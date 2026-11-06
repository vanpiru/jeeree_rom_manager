#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Оконный редактор таблицы ROM-файлов в бинарнике.

Формат бинарника:
  Таблица записей с адреса 0x64000, запись = 32 байта:
    0x00..0x13 (20 байт) - имя, дополнено 0xFF
    0x14..0x17 (4 байта) - сигнатура 00 00 FE CA
    0x18..0x1B (4 байта) - смещение данных (little-endian)
    0x1C..0x1F (4 байта) - размер данных (little-endian)
  Данные файлов начинаются с адреса 0x65000 и идут подряд.

При добавлении ROM:
  - принимаются только iNES 1.0 и NES 2.0;
  - заголовок NES 2.0 автоматически преобразуется в iNES 1.0;
  - игры с mapper больше 255 не поддерживаются.

Кнопки:
  Backup        - прочитать flash RP2040 через picotool (режим BOOTSEL)
  Открыть BIN   - загрузить бинарник и таблицу
  Распаковать ROM - извлечь все NES-файлы в папку ROM
  Добавить ROM  - добавить один или несколько ROM-файлов
  Очистить      - удалить все записи
  Собрать BIN   - записать таблицу и данные в новый бинарник
  Собрать UF2   - собрать текущий образ и сохранить его в UF2 для RP2040
  Записать игры - записать в RP2040 только таблицу игр и область ROM (BOOTSEL)
  Удалить       - удалить выбранную запись (клавиша Del)

Имя в списке редактируется двойным кликом (или клавишей F2).
"""

from __future__ import annotations

import os
import queue
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
from dataclasses import dataclass
from pathlib import Path
from tkinter import filedialog, messagebox, ttk
from typing import Callable

TABLE_OFFSET = 0x64000
DATA_OFFSET = 0x65000
TABLE_SIZE = DATA_OFFSET - TABLE_OFFSET
RECORD_SIZE = 32
NAME_SIZE = 20
MAGIC = 0xCAFE0000
MAGIC_BYTES = MAGIC.to_bytes(4, "little")
MAX_ENTRIES = TABLE_SIZE // RECORD_SIZE
FILL = b"\xff"
DEFAULT_FILE = Path.home() / "Desktop" / "file.bin"
NUMBER_PREFIX_RE = re.compile(r"^\d{1,3}\s+")
INVALID_FILENAME_CHARS = re.compile(r'[<>:"/\\|?*\x00-\x1f]')
WINDOWS_RESERVED_NAMES = {
    "CON", "PRN", "AUX", "NUL",
    *(f"COM{number}" for number in range(1, 10)),
    *(f"LPT{number}" for number in range(1, 10)),
}

# Параметры формата iNES / NES 2.0
INES_MAGIC = b"NES\x1a"
INES_HEADER_SIZE = 16
INES_TRAINER_SIZE = 512
INES_PRG_UNIT = 16 * 1024
INES_CHR_UNIT = 8 * 1024
MAX_INES_MAPPER = 0xFF

# Параметры UF2 (как в bin2uf2.py)
UF2_MAGIC0 = 0x0A324655
UF2_MAGIC1 = 0x9E5D5157
UF2_MAGIC_END = 0x0AB16F30
UF2_FLAG_FAMILY = 0x00002000
UF2_FAMILY_RP2040 = 0xE48BFF56
UF2_CHUNK = 256
UF2_BASE = 0x10000000
FLASH_SECTOR_SIZE = 4096
BOOTSEL_INFO_FILENAME = "INFO_UF2.TXT"

# Параметры чтения flash с RP2040 через picotool
RP2040_FLASH_BASE = 0x10000000
RP2040_FLASH_SIZE = 0x200000
RP2040_FLASH_END = RP2040_FLASH_BASE + RP2040_FLASH_SIZE
PICOTOOL_URL = "https://github.com/raspberrypi/pico-sdk-tools/releases"
BACKUP_TIMEOUT_SECONDS = 120


@dataclass
class RomEntry:
    """Одна запись таблицы: имя и содержимое файла."""

    name: str
    data: bytes

    @property
    def size(self) -> int:
        return len(self.data)


def sanitize_name(name: str) -> str:
    """Приводит имя к Latin-1 и обрезает до 20 байт."""
    raw = name.encode("latin-1", errors="replace")[:NAME_SIZE]
    return raw.decode("latin-1")


def strip_number_prefix(name: str) -> str:
    """Убирает автоматический номер вида «01 » из начала имени."""
    stripped = NUMBER_PREFIX_RE.sub("", name, count=1).strip()
    return stripped or name.strip()


def apply_numbering(entries: list[RomEntry]) -> bool:
    """Нумерует записи по порядку: 01, 02, ... Возвращает True, если что-то изменилось."""
    changed = False
    for index, entry in enumerate(entries, 1):
        new_name = sanitize_name(f"{index:02d} {strip_number_prefix(entry.name)}")
        if new_name != entry.name:
            entry.name = new_name
            changed = True
    return changed


def format_size(value: int) -> str:
    return f"{value:,}".replace(",", " ")


class RomValidationError(ValueError):
    """ROM не является iNES или не может быть приведён к iNES 1.0."""


def _nes2_size(low_byte: int, high_nibble: int, unit: int) -> int:
    """Размер PRG/CHR в NES 2.0 с учётом exponent-multiplier записи."""
    if high_nibble == 0x0F:
        exponent = low_byte >> 2
        multiplier = low_byte & 0x03
        return (1 << exponent) * (2 * multiplier + 1)
    return (low_byte | (high_nibble << 8)) * unit


def normalize_ines_rom(data: bytes) -> tuple[bytes, int, bool]:
    """Проверяет iNES/NES 2.0 и приводит заголовок к iNES 1.0.

    Возвращает (данные, номер mapper, был_ли_заголовок_NES_2.0).
    При ошибке выбрасывает RomValidationError.
    """
    if len(data) < INES_HEADER_SIZE:
        raise RomValidationError(
            f"файл слишком мал для iNES-заголовка ({format_size(len(data))} байт)"
        )
    if data[:4] != INES_MAGIC:
        if data[:4] == b"UNIF":
            raise RomValidationError("формат UNIF не поддерживается, нужен iNES")
        raise RomValidationError(
            "нет заголовка iNES (первые 4 байта должны быть NES\\x1A)"
        )

    header = data[:INES_HEADER_SIZE]
    flags6 = header[6]
    flags7 = header[7]
    flags8 = header[8]
    flags9 = header[9]
    identifier = flags7 & 0x0C

    if identifier == 0x08:
        # NES 2.0: mapper занимает 12 бит.
        mapper = (flags6 >> 4) | (flags7 & 0xF0) | ((flags8 & 0x0F) << 8)
        if mapper > MAX_INES_MAPPER:
            raise RomValidationError(
                f"mapper {mapper} не поддерживается: iNES 1.0 "
                f"допускает mapper 0–{MAX_INES_MAPPER}"
            )

        prg_bytes = _nes2_size(header[4], flags9 & 0x0F, INES_PRG_UNIT)
        chr_bytes = _nes2_size(header[5], flags9 >> 4, INES_CHR_UNIT)

        if prg_bytes <= 0:
            raise RomValidationError("в заголовке NES 2.0 указан нулевой размер PRG")
        if prg_bytes % INES_PRG_UNIT:
            raise RomValidationError(
                "размер PRG не кратен 16 КиБ — iNES 1.0 не может его сохранить"
            )
        if chr_bytes % INES_CHR_UNIT:
            raise RomValidationError(
                "размер CHR не кратен 8 КиБ — iNES 1.0 не может его сохранить"
            )

        prg_units = prg_bytes // INES_PRG_UNIT
        chr_units = chr_bytes // INES_CHR_UNIT
        if prg_units > 0xFF:
            raise RomValidationError(
                f"PRG {format_size(prg_bytes)} байт не помещается в iNES 1.0 "
                "(максимум 255 × 16 КиБ)"
            )
        if chr_units > 0xFF:
            raise RomValidationError(
                f"CHR {format_size(chr_bytes)} байт не помещается в iNES 1.0 "
                "(максимум 255 × 8 КиБ)"
            )

        required = INES_HEADER_SIZE + prg_bytes + chr_bytes
        if flags6 & 0x04:  # trainer
            required += INES_TRAINER_SIZE
        if len(data) < required:
            raise RomValidationError(
                f"файл обрезан: нужно минимум {format_size(required)} байт, "
                f"есть {format_size(len(data))}"
            )

        new_header = bytearray(INES_HEADER_SIZE)
        new_header[:4] = INES_MAGIC
        new_header[4] = prg_units
        new_header[5] = chr_units
        new_header[6] = (flags6 & 0x0F) | ((mapper & 0x0F) << 4)
        new_header[7] = (flags7 & 0x03) | (mapper & 0xF0)
        # Байты 8–15 в iNES 1.0: PRG RAM и резерв. 0 = совместимые 8 КиБ.
        return bytes(new_header) + data[INES_HEADER_SIZE:], mapper, True

    if identifier == 0x00:
        # iNES 1.0. Ноль в поле PRG в старых файлах означал 256 банков.
        prg_units = header[4] or 0x100
        chr_units = header[5]
        prg_bytes = prg_units * INES_PRG_UNIT
        chr_bytes = chr_units * INES_CHR_UNIT

        required = INES_HEADER_SIZE + prg_bytes + chr_bytes
        if flags6 & 0x04:  # trainer
            required += INES_TRAINER_SIZE
        if len(data) < required:
            raise RomValidationError(
                f"файл обрезан: нужно минимум {format_size(required)} байт, "
                f"есть {format_size(len(data))}"
            )

        mapper = (flags6 >> 4) | (flags7 & 0xF0)
        return data, mapper, False

    raise RomValidationError(
        "неизвестный вариант iNES-заголовка (биты 2–3 байта 7)"
    )


def safe_filename(name: str) -> str:
    """Делает имя пригодным для файловой системы Windows."""
    cleaned = INVALID_FILENAME_CHARS.sub("_", name).strip().rstrip(". ")
    if not cleaned:
        cleaned = "ROM"
    if cleaned.split(".", 1)[0].upper() in WINDOWS_RESERVED_NAMES:
        cleaned = "_" + cleaned
    return cleaned


def extract_nes_files(
    entries: list[RomEntry], target: Path, overwrite: bool = True
) -> tuple[list[Path], int]:
    """Извлекает NES-файлы в target. Возвращает (записанные пути, пропущено)."""
    target.mkdir(parents=True, exist_ok=True)
    written: list[Path] = []
    skipped = 0
    used: set[str] = set()

    for entry in entries:
        if not entry.data.startswith(b"NES\x1a"):
            skipped += 1
            continue

        filename = safe_filename(entry.name)
        if not filename.lower().endswith(".nes"):
            filename += ".nes"

        path = target / filename
        if path.name.lower() in used or (not overwrite and path.exists()):
            stem, suffix = path.stem, path.suffix
            counter = 2
            while True:
                candidate = target / f"{stem} ({counter}){suffix}"
                if candidate.name.lower() not in used and (overwrite or not candidate.exists()):
                    path = candidate
                    break
                counter += 1

        used.add(path.name.lower())
        path.write_bytes(entry.data)
        written.append(path)

    return written, skipped


def read_bin(path: Path) -> tuple[bytes, list[RomEntry], int]:
    """Читает бинарник. Возвращает (исходные байты, записи, конец данных)."""
    raw = path.read_bytes()
    if len(raw) < DATA_OFFSET:
        raise ValueError(
            f"Файл слишком мал ({len(raw)} байт), таблица должна быть до 0x{DATA_OFFSET:X}."
        )

    entries: list[RomEntry] = []
    data_end = DATA_OFFSET

    pos = TABLE_OFFSET
    while pos + RECORD_SIZE <= DATA_OFFSET:
        record = raw[pos:pos + RECORD_SIZE]
        if record == FILL * RECORD_SIZE:  # конец таблицы
            break

        magic = int.from_bytes(record[20:24], "little")
        if magic != MAGIC:
            raise ValueError(
                f"Некорректная сигнатура записи #{len(entries) + 1} "
                f"по адресу 0x{pos:X}: 0x{magic:08X}."
            )

        name = record[:NAME_SIZE].split(b"\x00", 1)[0].decode("latin-1")
        offset = int.from_bytes(record[24:28], "little")
        size = int.from_bytes(record[28:32], "little")

        if offset < DATA_OFFSET or offset + size > len(raw):
            raise ValueError(
                f"Запись «{name}» указывает за пределы файла "
                f"(смещение 0x{offset:X}, размер {size})."
            )

        entries.append(RomEntry(name, raw[offset:offset + size]))
        data_end = max(data_end, offset + size)
        pos += RECORD_SIZE

    return raw, entries, data_end


def build_bin(
    base: bytes | None,
    entries: list[RomEntry],
    min_size: int = 0,
    old_data_end: int = DATA_OFFSET,
) -> tuple[bytes, int]:
    """Собирает бинарник. Возвращает (байты, новый конец данных).

    Байты вне таблицы и области данных (например, код меню) сохраняются
    из исходного файла.
    """
    if len(entries) > MAX_ENTRIES:
        raise ValueError(
            f"Слишком много записей: {len(entries)}, максимум {MAX_ENTRIES}."
        )

    total_data = sum(entry.size for entry in entries)
    new_data_end = DATA_OFFSET + total_data
    if new_data_end > 0xFFFFFFFF:
        raise ValueError("Суммарный размер данных слишком велик.")

    size = max(len(base) if base else 0, min_size, new_data_end, DATA_OFFSET)
    out = bytearray(FILL * size)

    if base:
        out[:len(base)] = base

    # Чистим таблицу и старую область данных.
    out[TABLE_OFFSET:DATA_OFFSET] = FILL * TABLE_SIZE
    clear_end = max(old_data_end, new_data_end)
    if clear_end > DATA_OFFSET:
        out[DATA_OFFSET:clear_end] = FILL * (clear_end - DATA_OFFSET)

    # Пишем таблицу и данные подряд.
    offset = DATA_OFFSET
    for index, entry in enumerate(entries):
        record = bytearray(FILL * RECORD_SIZE)
        name_bytes = entry.name.encode("latin-1", errors="replace")[:NAME_SIZE]
        record[:len(name_bytes)] = name_bytes
        if len(name_bytes) < NAME_SIZE:  # завершающий ноль, как в исходном файле
            record[len(name_bytes)] = 0
        record[20:24] = MAGIC_BYTES
        record[24:28] = offset.to_bytes(4, "little")
        record[28:32] = entry.size.to_bytes(4, "little")

        start = TABLE_OFFSET + index * RECORD_SIZE
        out[start:start + RECORD_SIZE] = record

        out[offset:offset + entry.size] = entry.data
        offset += entry.size

    return bytes(out), new_data_end


def build_uf2(data: bytes, base: int = UF2_BASE) -> bytes:
    """Превращает образ flash в UF2 для RP2040 (как bin2uf2.py)."""
    blocks = (len(data) + UF2_CHUNK - 1) // UF2_CHUNK
    out = bytearray()

    for index in range(blocks):
        chunk = data[index * UF2_CHUNK:(index + 1) * UF2_CHUNK]
        chunk = chunk + b"\x00" * (UF2_CHUNK - len(chunk))
        header = struct.pack(
            "<8I",
            UF2_MAGIC0,
            UF2_MAGIC1,
            UF2_FLAG_FAMILY,
            base + index * UF2_CHUNK,
            UF2_CHUNK,
            index,
            blocks,
            UF2_FAMILY_RP2040,
        )
        out += header + chunk + b"\x00" * (476 - UF2_CHUNK)
        out += struct.pack("<I", UF2_MAGIC_END)

    return bytes(out)


def find_picotool() -> str | None:
    """Ищет picotool в PATH, в папке picotool и в типовых местах Pico SDK."""
    found = shutil.which("picotool")
    if found:
        return found

    app_dir = Path(__file__).resolve().parent
    cwd = Path.cwd()
    home = Path.home()
    drive_root = Path(cwd.anchor)

    direct_dirs = [app_dir, cwd, home]
    nested_dirs = [
        app_dir / "picotool",
        cwd / "picotool",
        home / "picotool",
        drive_root / "picotool",
        home / ".pico-sdk" / "picotool",
    ]

    env_dir = os.environ.get("PICOTOOL_DIR")
    if env_dir:
        nested_dirs.append(Path(env_dir))

    # Сначала проверяем ожидаемые имена файлов.
    for directory in direct_dirs + nested_dirs:
        for name in ("picotool.exe", "picotool"):
            candidate = directory / name
            if candidate.is_file():
                return str(candidate)

    # Затем — вложенные каталоги (например, picotool/picotool/picotool.exe).
    for directory in nested_dirs:
        if not directory.is_dir():
            continue
        for name in ("picotool.exe", "picotool"):
            for candidate in sorted(directory.rglob(name), reverse=True):
                if candidate.is_file():
                    return str(candidate)

    return None


def _windows_drive_roots() -> list[Path]:
    if os.name != "nt":
        return []
    try:
        import ctypes

        mask = ctypes.windll.kernel32.GetLogicalDrives()
    except Exception:  # noqa: BLE001
        return []
    return [Path(f"{chr(65 + index)}:\\") for index in range(26) if mask & (1 << index)]


def _unix_drive_roots() -> list[Path]:
    user = os.environ.get("USER", "")
    bases = [
        Path("/media") / user,
        Path("/run/media") / user,
        Path("/mnt"),
    ]
    roots: list[Path] = []
    for base in bases:
        try:
            roots.extend(path for path in base.iterdir() if path.is_dir())
        except OSError:
            continue
    return roots


def find_bootsel_drive() -> Path | None:
    """Ищет смонтированный диск BOOTSEL по файлу INFO_UF2.TXT."""
    roots = _windows_drive_roots() + _unix_drive_roots()
    for root in roots:
        try:
            if (root / BOOTSEL_INFO_FILENAME).is_file():
                return root
        except OSError:
            continue
    return None


def bootsel_drive_present(drive: Path) -> bool:
    """Проверяет, что диск BOOTSEL всё ещё смонтирован."""
    try:
        return (drive / BOOTSEL_INFO_FILENAME).is_file()
    except OSError:
        return False


class _WriteCancelled(Exception):
    """Внутренний сигнал отмены записи игр."""


class ProgressDialog(tk.Toplevel):
    """Модальное окно с индикатором загрузки и возможностью отмены."""

    def __init__(
        self,
        parent: tk.Misc,
        title: str,
        text: str,
        on_cancel: Callable[[], None] | None = None,
    ) -> None:
        super().__init__(parent)
        self.withdraw()
        self.title(title)
        self.resizable(False, False)
        self.transient(parent)
        self._on_cancel = on_cancel
        self._cancel_button: ttk.Button | None = None

        frame = ttk.Frame(self, padding=16)
        frame.pack(fill="both", expand=True)

        self.status_var = tk.StringVar(value=text)
        ttk.Label(frame, textvariable=self.status_var, justify="left").pack(anchor="w")

        self.progress = ttk.Progressbar(frame, mode="indeterminate", length=460)
        self.progress.pack(fill="x", pady=(12, 0))
        self.progress.start(15)

        if on_cancel is not None:
            self._cancel_button = ttk.Button(frame, text="Отмена", command=self._cancel)
            self._cancel_button.pack(anchor="e", pady=(12, 0))
            self.protocol("WM_DELETE_WINDOW", self._cancel)
        else:
            self.protocol("WM_DELETE_WINDOW", lambda: None)

        self.update_idletasks()
        try:
            parent.update_idletasks()
            x = parent.winfo_rootx() + max(
                0, (parent.winfo_width() - self.winfo_reqwidth()) // 2
            )
            y = parent.winfo_rooty() + max(
                0, (parent.winfo_height() - self.winfo_reqheight()) // 2
            )
            self.geometry(f"+{x}+{y}")
        except tk.TclError:
            pass

        self.deiconify()
        self.grab_set()
        self.focus_set()

    def set_status(self, text: str) -> None:
        self.status_var.set(text)

    def set_progress(self, percent: float | None) -> None:
        """Переключает индикатор между режимами ожидания и процентами."""
        if percent is None:
            if str(self.progress.cget("mode")) == "determinate":
                self.progress.stop()
                self.progress.configure(mode="indeterminate", value=0)
                self.progress.start(15)
            return

        if str(self.progress.cget("mode")) != "determinate":
            self.progress.stop()
            self.progress.configure(mode="determinate", maximum=100)
        self.progress["value"] = max(0.0, min(100.0, percent))

    def _cancel(self) -> None:
        if self._on_cancel is None:
            return
        callback = self._on_cancel
        self._on_cancel = None
        if self._cancel_button is not None:
            self._cancel_button.state(["disabled"])
        callback()

    def close(self) -> None:
        try:
            self.grab_release()
        except tk.TclError:
            pass
        try:
            self.progress.stop()
            self.destroy()
        except tk.TclError:
            pass


class RomManagerApp(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("ROM Manager")
        self.geometry("600x560")
        self.minsize(600, 460)

        self.bin_path: Path | None = None
        self.bin_base: bytes | None = None
        self.data_end = DATA_OFFSET
        self.entries: list[RomEntry] = []
        self.dirty = False
        self.picotool_path: str | None = None

        self._editor: ttk.Entry | None = None
        self._edit_index: int | None = None

        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.refresh()

    # ---------- Интерфейс ----------

    def _build_ui(self) -> None:
        style = ttk.Style(self)
        style.configure(
            "Memo.Treeview",
            background="#FFFFFF",
            fieldbackground="#FFFFFF",
            foreground="#000000",
            borderwidth=0,
            relief="flat",
            rowheight=23,
            font=("Segoe UI", 9),
        )
        style.map(
            "Memo.Treeview",
            background=[("selected", "#CCE8FF")],
            foreground=[("selected", "#000000")],
        )
        style.configure(
            "Memo.Treeview.Heading",
            background="#E8E8E8",
            foreground="#000000",
            font=("Segoe UI", 9),
            padding=(6, 3),
        )
        style.map(
            "Memo.Treeview.Heading",
            background=[("active", "#DCDCDC")],
        )

        toolbar = ttk.Frame(self, padding=(8, 8, 8, 2))
        toolbar.pack(side="top", fill="x")

        ttk.Button(toolbar, text="Backup", command=self._on_read_backup).pack(side="left")
        ttk.Button(toolbar, text="Открыть BIN", command=self._on_open).pack(
            side="left", padx=(6, 0)
        )
        ttk.Button(toolbar, text="Распаковать ROM", command=self._on_extract_rom).pack(
            side="left", padx=(6, 0)
        )
        ttk.Button(toolbar, text="Добавить ROM", command=self._on_add_rom).pack(
            side="left", padx=(6, 0)
        )
        ttk.Button(toolbar, text="Очистить", command=self._on_clear).pack(
            side="left", padx=(6, 0)
        )

        status_area = tk.Frame(self, relief="sunken", borderwidth=1)
        status_area.pack(side="bottom", fill="x", padx=8, pady=(0, 8))

        self.status_var = tk.StringVar()
        tk.Label(
            status_area,
            textvariable=self.status_var,
            anchor="w",
            padx=4,
            pady=2,
        ).pack(fill="x")

        self.capacity_var = tk.StringVar()
        self.capacity_label = tk.Label(
            status_area,
            textvariable=self.capacity_var,
            anchor="w",
            padx=4,
            foreground="#666666",
        )
        self.capacity_label.pack(fill="x")

        self.free_var = tk.StringVar()
        self.free_label = tk.Label(
            status_area,
            textvariable=self.free_var,
            anchor="w",
            padx=4,
        )
        self.free_label.pack(fill="x", pady=(0, 2))

        bottom = ttk.Frame(self, padding=(8, 2, 8, 6))
        bottom.pack(side="bottom", fill="x")

        ttk.Label(
            bottom,
            text="Двойной клик — переименовать. Del — удалить.",
            foreground="#666666",
        ).pack(side="left")

        ttk.Button(bottom, text="Записать игры", command=self._on_write_games).pack(
            side="right", padx=(0, 6)
        )
        ttk.Button(bottom, text="Собрать UF2", command=self._on_build_uf2).pack(side="right", padx=(0, 6))
        ttk.Button(bottom, text="Собрать BIN", command=self._on_save).pack(
            side="right", padx=(0, 6)
        )

        table_frame = tk.Frame(self, relief="sunken", borderwidth=1, background="#FFFFFF")
        table_frame.pack(side="top", fill="both", expand=True, padx=8, pady=(2, 2))
        table_frame.rowconfigure(0, weight=1)
        table_frame.columnconfigure(0, weight=1)

        columns = ("num", "name", "size", "kb", "offset")
        self.tree = ttk.Treeview(
            table_frame,
            columns=columns,
            show="headings",
            selectmode="browse",
            style="Memo.Treeview",
        )

        self.tree.heading("num", text="№", anchor="center")
        self.tree.heading("name", text="Имя", anchor="w")
        self.tree.heading("size", text="Размер, байт", anchor="e")
        self.tree.heading("kb", text="Размер, Кб", anchor="e")
        self.tree.heading("offset", text="Смещение", anchor="e")

        self.tree.column("num", width=48, minwidth=40, anchor="center", stretch=False)
        self.tree.column("name", width=120, minwidth=100, anchor="w", stretch=True)
        self.tree.column("size", width=100, minwidth=100, anchor="e", stretch=False)
        self.tree.column("kb", width=80, minwidth=60, anchor="e", stretch=False)
        self.tree.column("offset", width=100, minwidth=100, anchor="e", stretch=False)

        scrollbar = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.scrollbar = scrollbar
        self.tree.configure(yscrollcommand=self._on_tree_scroll)
        self.tree.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")

        self.context_menu = tk.Menu(self, tearoff=False)
        self.context_menu.add_command(label="Переименовать", command=self._edit_selected)
        self.context_menu.add_command(label="Удалить", command=self._on_delete)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Считать Backup", command=self._on_read_backup)

        self.tree.bind("<Double-1>", self._on_double_click)
        self.tree.bind("<Button-3>", self._on_right_click)
        self.tree.bind("<F2>", self._on_f2)
        self.tree.bind("<Delete>", lambda _event: self._on_delete())

        self.bind("<Control-o>", lambda _event: self._on_open())
        self.bind("<Control-s>", lambda _event: self._on_save())
        self.bind("<Insert>", lambda _event: self._on_add_rom())

    # ---------- Состояние ----------

    def refresh(self) -> None:
        self._cancel_edit()
        selected = self._selected_index()

        self.tree.delete(*self.tree.get_children())

        offset = DATA_OFFSET
        total = 0
        for index, entry in enumerate(self.entries):
            size = entry.size
            self.tree.insert(
                "",
                "end",
                iid=str(index),
                values=(
                    index + 1,
                    entry.name,
                    format_size(size),
                    f"{size / 1024:.1f}",
                    f"0x{offset:08X}",
                ),
            )
            offset += size
            total += size

        if selected is not None and self.entries:
            index = min(selected, len(self.entries) - 1)
            self.tree.selection_set(str(index))
            self.tree.focus(str(index))
            self.tree.see(str(index))

        path_text = str(self.bin_path) if self.bin_path else "файл не открыт"
        self.status_var.set(
            f"Записей: {len(self.entries)} | "
            f"Всего данных: {format_size(total)} байт | {path_text}"
        )
        self._update_capacity(total)
        self._update_title()
        self.after_idle(self._update_scrollbar_visibility)

    def _on_tree_scroll(self, first: str, last: str) -> None:
        self.scrollbar.set(first, last)
        if float(first) <= 0.0 and float(last) >= 1.0:
            self.scrollbar.grid_remove()
        else:
            self.scrollbar.grid()

    def _update_scrollbar_visibility(self) -> None:
        first, last = self.tree.yview()
        self._on_tree_scroll(first, last)

    def _update_capacity(self, used: int) -> None:
        """Показывает доступный объём и остаток до служебной области."""
        if self.bin_base is None:
            self.capacity_var.set(
                "Доступный объем: Откройте BIN, чтобы рассчитать место."
            )
            self.free_var.set("Свободно: -")
            self.free_label.configure(foreground="#666666")
            return

        tail_start = self._tail_start()
        if tail_start >= len(self.bin_base):
            self.capacity_var.set(
                "Доступный объем: не ограничен (служебная область не найдена)."
            )
            self.free_var.set("Свободно: не ограничено")
            self.free_label.configure(foreground="#1a7f37")
            return

        capacity = max(0, tail_start - DATA_OFFSET)
        free = capacity - used

        self.capacity_var.set(
            f"Доступный объем: {format_size(capacity)} байт "
            f"({capacity / 1024:.1f} Кб) — служебная область с 0x{tail_start:08X}"
        )

        if free >= 0:
            self.free_var.set(
                f"Свободно: {format_size(free)} байт ({free / 1024:.1f} Кб)"
            )
            self.free_label.configure(foreground="#1a7f37")
        else:
            self.free_var.set(
                f"Свободно: не хватает {format_size(-free)} байт ({-free / 1024:.1f} Кб) — "
                "данные перекроют служебную область!"
            )
            self.free_label.configure(foreground="#b00020")

    def _update_title(self) -> None:
        if self.bin_path is None:
            self.title("ROM Manager")
            return
        star = " *" if self.dirty else ""
        self.title(f"ROM Manager — {self.bin_path.name}{star}")

    def _mark_dirty(self) -> None:
        self.dirty = True
        self._update_title()

    def _renumber(self) -> bool:
        return apply_numbering(self.entries)

    def _selected_index(self) -> int | None:
        selection = self.tree.selection()
        if not selection:
            return None
        try:
            return int(selection[0])
        except ValueError:
            return None

    # ---------- Открытие / сохранение ----------

    def _on_open(self) -> None:
        if not self._confirm_save():
            return

        initial_dir = self.bin_path.parent if self.bin_path else DEFAULT_FILE.parent
        initial_file = self.bin_path.name if self.bin_path else DEFAULT_FILE.name
        filename = filedialog.askopenfilename(
            parent=self,
            title="Открыть BIN",
            initialdir=str(initial_dir),
            initialfile=initial_file,
            filetypes=[("BIN files", "*.bin"), ("All files", "*.*")],
        )
        if not filename:
            return

        try:
            base, entries, data_end = read_bin(Path(filename))
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Ошибка чтения", str(exc), parent=self)
            return

        self.bin_path = Path(filename)
        self.bin_base = base
        self.entries = entries
        self.data_end = data_end
        self.dirty = False
        self.refresh()

    def _can_build(self) -> bool:
        if self.bin_base is None and not self.entries:
            messagebox.showinfo(
                "Нечего собирать",
                "Сначала откройте BIN-файл или добавьте ROM.",
                parent=self,
            )
            return False
        return True

    def _build_current_bin(self) -> tuple[bytes, int] | None:
        """Собирает текущее состояние в образ; при отказе/ошибке возвращает None."""
        new_data_end = DATA_OFFSET + sum(entry.size for entry in self.entries)
        if self.bin_base:
            tail_start = self._tail_start()
            if new_data_end > tail_start:
                if not messagebox.askyesno(
                    "Перекрытие служебной области",
                    "Новые данные выйдут за пределы старой области файлов "
                    f"(0x{tail_start:X}) и перекроют служебные данные.\n\n"
                    "Продолжить?",
                    parent=self,
                ):
                    return None

        try:
            return build_bin(self.bin_base, self.entries, old_data_end=self.data_end)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Ошибка сборки", str(exc), parent=self)
            return None

    def _on_save(self) -> bool:
        if not self._can_build():
            return False

        initial_dir = self.bin_path.parent if self.bin_path else DEFAULT_FILE.parent
        initial_file = self.bin_path.name if self.bin_path else "output.bin"
        filename = filedialog.asksaveasfilename(
            parent=self,
            title="Собрать BIN",
            initialdir=str(initial_dir),
            initialfile=initial_file,
            defaultextension=".bin",
            filetypes=[("BIN files", "*.bin"), ("All files", "*.*")],
        )
        if not filename:
            return False

        built = self._build_current_bin()
        if built is None:
            return False
        output, new_data_end = built

        try:
            Path(filename).write_bytes(output)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Ошибка сохранения", str(exc), parent=self)
            return False

        self.bin_path = Path(filename)
        self.bin_base = output
        self.data_end = new_data_end
        self.dirty = False
        self.refresh()
        messagebox.showinfo(
            "Готово",
            f"Файл сохранён:\n{filename}\n\n"
            f"Записей: {len(self.entries)}, размер: {format_size(len(output))} байт.",
            parent=self,
        )
        return True

    def _on_build_uf2(self) -> bool:
        if not self._can_build():
            return False

        initial_dir = self.bin_path.parent if self.bin_path else DEFAULT_FILE.parent
        initial_file = (self.bin_path.stem if self.bin_path else "output") + ".uf2"
        filename = filedialog.asksaveasfilename(
            parent=self,
            title="Собрать UF2",
            initialdir=str(initial_dir),
            initialfile=initial_file,
            defaultextension=".uf2",
            filetypes=[("UF2 files", "*.uf2"), ("All files", "*.*")],
        )
        if not filename:
            return False

        built = self._build_current_bin()
        if built is None:
            return False
        output, _new_data_end = built

        try:
            uf2 = build_uf2(output)
            Path(filename).write_bytes(uf2)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Ошибка сохранения UF2", str(exc), parent=self)
            return False

        blocks = (len(output) + UF2_CHUNK - 1) // UF2_CHUNK
        messagebox.showinfo(
            "Готово",
            f"UF2 сохранён:\n{filename}\n\n"
            f"Блоков: {blocks}, размер: {format_size(len(uf2))} байт.\n"
            f"База: 0x{UF2_BASE:08X}.",
            parent=self,
        )
        return True

    def _build_games_uf2(self) -> tuple[bytes, int, int] | None:
        """Собирает UF2 только для таблицы игр и области ROM.

        Возвращает (uf2, начало области, конец области) в адресах flash.
        Код эмулятора и служебные настройки в образ не попадают.
        """
        new_data_end = DATA_OFFSET + sum(entry.size for entry in self.entries)
        tail_start: int | None = None
        if self.bin_base:
            tail_start = self._tail_start()
            if new_data_end > tail_start:
                messagebox.showerror(
                    "Перекрытие служебной области",
                    "Таблица и ROM выходят за пределы области игр "
                    f"(0x{tail_start:08X}).\n\n"
                    "Запись отменена, чтобы не повредить настройки.",
                    parent=self,
                )
                return None

        built = self._build_current_bin()
        if built is None:
            return None
        output, new_data_end = built

        end = max(new_data_end, DATA_OFFSET)
        end = min(end, len(output))
        end = ((end + FLASH_SECTOR_SIZE - 1) // FLASH_SECTOR_SIZE) * FLASH_SECTOR_SIZE

        if tail_start is not None and end > tail_start:
            messagebox.showerror(
                "Перекрытие служебной области",
                "Область игр не помещается перед служебными данными "
                f"(0x{tail_start:08X}).\n\n"
                "Запись отменена, чтобы не повредить настройки.",
                parent=self,
            )
            return None

        region = output[TABLE_OFFSET:end]
        region_size = end - TABLE_OFFSET
        if len(region) < region_size:
            region += FILL * (region_size - len(region))
        if not region:
            messagebox.showerror(
                "Ошибка сборки",
                "Не удалось получить область игр.",
                parent=self,
            )
            return None

        uf2 = build_uf2(region, base=UF2_BASE + TABLE_OFFSET)
        return uf2, UF2_BASE + TABLE_OFFSET, UF2_BASE + end

    def _on_write_games(self) -> bool:
        if not self._can_build():
            return False

        prepared = self._build_games_uf2()
        if prepared is None:
            return False
        uf2, region_start, region_end = prepared
        region_size = region_end - region_start

        if not messagebox.askokcancel(
            "Запись игр через BOOTSEL",
            "Переведите приставку в режим BOOTSEL:\n\n"
            "1. Выключите приставку долгим нажатием Start.\n"
            "2. Подключите приставку к компьютеру по USB.\n"
            "3. Нажмите и удерживайте Menu.\n"
            "4. Удерживая Menu, нажмите Start.\n"
            "5. Отпустите Menu, но продолжайте удерживать Start.\n\n"
            "Будет записана только таблица игр и область ROM:\n"
            f"0x{region_start:08X}–0x{region_end:08X} "
            f"({format_size(region_size)} байт).\n"
            "Код эмулятора и настройки не изменятся.\n\n"
            "Нажмите OK и дождитесь появления диска BOOTSEL.",
            parent=self,
        ):
            return False

        temp_dir: Path | None = None
        temp_path: Path | None = None

        def cleanup_temp() -> None:
            if temp_path is not None:
                try:
                    temp_path.unlink(missing_ok=True)
                except OSError:
                    pass
            if temp_dir is not None:
                try:
                    temp_dir.rmdir()
                except OSError:
                    pass

        try:
            temp_dir = Path(tempfile.mkdtemp(prefix="rom_manager_games_"))
            temp_path = temp_dir / "temp.uf2"
            temp_path.write_bytes(uf2)
        except Exception as exc:  # noqa: BLE001
            cleanup_temp()
            messagebox.showerror(
                "Ошибка записи",
                f"Не удалось создать временный temp.uf2:\n{exc}",
                parent=self,
            )
            return False

        results: queue.Queue[tuple] = queue.Queue()
        cancel_event = threading.Event()

        def worker() -> None:
            try:
                results.put(("status", "Ожидание диска BOOTSEL..."))
                drive: Path | None = None
                while drive is None:
                    if cancel_event.is_set():
                        raise _WriteCancelled
                    drive = find_bootsel_drive()
                    if drive is None:
                        cancel_event.wait(0.4)

                results.put(
                    ("status", f"Найден диск {drive}. Копирование temp.uf2...")
                )
                destination = drive / "temp.uf2"
                total = temp_path.stat().st_size
                copied = 0
                with temp_path.open("rb") as source, destination.open(
                    "wb"
                ) as target_file:
                    while True:
                        if cancel_event.is_set():
                            raise _WriteCancelled
                        chunk = source.read(64 * 1024)
                        if not chunk:
                            break
                        target_file.write(chunk)
                        copied += len(chunk)
                        results.put(("progress", copied, total))

                results.put(
                    (
                        "status",
                        "Копирование завершено. Ожидание исчезновения диска...",
                    )
                )
                while bootsel_drive_present(drive):
                    if cancel_event.is_set():
                        raise _WriteCancelled
                    cancel_event.wait(0.4)
                results.put(("done", str(drive)))
            except _WriteCancelled:
                results.put(("cancelled",))
            except Exception as exc:  # noqa: BLE001
                results.put(("error", str(exc)))

        dialog = ProgressDialog(
            self,
            "Запись игр",
            "Ожидание диска BOOTSEL...",
            on_cancel=cancel_event.set,
        )
        finish: tuple | None = None
        threading.Thread(target=worker, daemon=True).start()

        def poll() -> None:
            nonlocal finish
            try:
                while True:
                    message = results.get_nowait()
                    kind = message[0]
                    if kind == "status":
                        dialog.set_status(message[1])
                        if message[1].startswith("Копирование завершено"):
                            dialog.set_progress(None)
                    elif kind == "progress":
                        copied, total = message[1], message[2]
                        percent = copied * 100 / total if total else 100.0
                        dialog.set_status(
                            "Копирование temp.uf2...\n"
                            f"{format_size(copied)} из {format_size(total)} байт "
                            f"({percent:.0f}%)"
                        )
                        dialog.set_progress(percent)
                    else:
                        finish = message
                        dialog.close()
                        return
            except queue.Empty:
                pass

            self.after(100, poll)

        self.after(50, poll)
        try:
            dialog.wait_window(dialog)
        finally:
            if dialog.winfo_exists():
                dialog.close()
            cleanup_temp()

        if finish is None:
            finish = ("error", "Не удалось получить результат записи.")
        kind = finish[0]

        if kind == "cancelled":
            messagebox.showinfo(
                "Запись игр",
                "Запись отменена.\n\n"
                "Если копирование уже началось, не отключайте приставку "
                "до исчезновения диска BOOTSEL.",
                parent=self,
            )
            return False

        if kind == "error":
            messagebox.showerror(
                "Ошибка записи",
                f"{finish[1]}\n\n"
                "Проверьте, что приставка подключена в режиме BOOTSEL.",
                parent=self,
            )
            return False

        messagebox.showinfo(
            "Готово",
            "Игры записаны в RP2040.\n\n"
            f"Записей: {len(self.entries)}\n"
            f"Область: 0x{region_start:08X}–0x{region_end:08X} "
            f"({format_size(region_size)} байт).\n"
            "Код эмулятора и настройки не изменены.",
            parent=self,
        )
        return True

    def _ensure_picotool(self) -> str | None:
        if self.picotool_path and Path(self.picotool_path).is_file():
            return self.picotool_path

        self.picotool_path = find_picotool()
        if self.picotool_path:
            return self.picotool_path

        if not messagebox.askyesno(
            "picotool не найден",
            "Для чтения backup с RP2040 нужен picotool "
            "(протокол PICOBOOT).\n\n"
            f"Скачать: {PICOTOOL_URL}\n\n"
            "Указать путь к picotool.exe вручную?",
            parent=self,
        ):
            return None

        filename = filedialog.askopenfilename(
            parent=self,
            title="Укажите picotool.exe",
            filetypes=[("picotool", "picotool.exe"), ("All files", "*.*")],
        )
        if not filename:
            return None

        self.picotool_path = filename
        return filename

    def _on_read_backup(self) -> bool:
        if not self._confirm_save():
            return False

        picotool = self._ensure_picotool()
        if not picotool:
            return False

        if not messagebox.askokcancel(
            "Чтение Backup с RP2040",
            "Выключите приставку долгим нажатием Start.\n\n"
            "Подключите приставку к компьютеру по USB.\n\n "
            "Нажмите и удерживайте Menu.\n\n"
            "Удерживая Menu, нажмите Start.\n\n"
            "Отпустите Menu, но продолжайте удерживать Start.\n\n"
            "Будет прочитан диапазон "
            f"0x{RP2040_FLASH_BASE:08X}–0x{RP2040_FLASH_END:08X} "
            f"({format_size(RP2040_FLASH_SIZE)} байт).\n\nНачать чтение?",
            parent=self,
        ):
            return False

        initial_dir = self.bin_path.parent if self.bin_path else DEFAULT_FILE.parent
        initial_file = (self.bin_path.stem if self.bin_path else "backup") + "_backup.bin"
        filename = filedialog.asksaveasfilename(
            parent=self,
            title="Сохранить Backup из RP2040",
            initialdir=str(initial_dir),
            initialfile=initial_file,
            defaultextension=".bin",
            filetypes=[("BIN files", "*.bin"), ("All files", "*.*")],
        )
        if not filename:
            return False

        command = [
            picotool,
            "save",
            "-r",
            f"0x{RP2040_FLASH_BASE:08X}",
            f"0x{RP2040_FLASH_END:08X}",
            filename,
            "-t",
            "bin",
        ]

        creationflags = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0
        try:
            process = subprocess.Popen(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
                creationflags=creationflags,
            )
        except OSError as exc:
            self.picotool_path = None
            messagebox.showerror(
                "Ошибка запуска picotool",
                f"{exc}\n\nПроверьте путь к picotool.",
                parent=self,
            )
            return False

        status_text = (
            "Чтение flash RP2040...\n"
            f"Диапазон: 0x{RP2040_FLASH_BASE:08X}–0x{RP2040_FLASH_END:08X}\n"
            f"picotool: {picotool}"
        )

        results: queue.Queue[tuple[int, str, str]] = queue.Queue()

        def reader() -> None:
            try:
                out, err = process.communicate()
                results.put((process.returncode, out, err))
            except Exception as exc:  # noqa: BLE001
                results.put((-1, "", str(exc)))

        # Читаем stdout/stderr в отдельном потоке, чтобы не переполнить pipe
        # и не заблокировать picotool на большом объёме вывода.
        threading.Thread(target=reader, daemon=True).start()

        cancelled = False
        timed_out = False
        result: tuple[int, str, str] | None = None

        def cancel() -> None:
            nonlocal cancelled
            cancelled = True
            if process.poll() is None:
                process.kill()

        dialog = ProgressDialog(self, "Чтение Backup", status_text, on_cancel=cancel)
        started = time.monotonic()

        def poll() -> None:
            nonlocal result, timed_out

            if result is None:
                try:
                    result = results.get_nowait()
                except queue.Empty:
                    pass

            if result is not None:
                dialog.close()
                return

            elapsed = time.monotonic() - started
            if elapsed > BACKUP_TIMEOUT_SECONDS and not timed_out:
                timed_out = True
                if process.poll() is None:
                    process.kill()
                dialog.set_status(
                    f"{status_text}\nПревышено время ожидания. Останавливаю picotool..."
                )
            elif cancelled:
                dialog.set_status(f"{status_text}\nОстановка picotool...")
            else:
                dialog.set_status(f"{status_text}\nПрошло: {elapsed:.0f} с")

            self.after(100, poll)

        self.after(50, poll)
        try:
            dialog.wait_window(dialog)
        finally:
            if dialog.winfo_exists():
                dialog.close()

        if result is None:
            result = (-1, "", "picotool не вернул результат")
        returncode, stdout, stderr = result

        if cancelled:
            try:
                Path(filename).unlink(missing_ok=True)
            except OSError:
                pass
            messagebox.showinfo(
                "Отменено",
                "Чтение backup отменено.",
                parent=self,
            )
            return False

        if timed_out:
            messagebox.showerror(
                "Ошибка чтения backup",
                f"picotool не ответил за {BACKUP_TIMEOUT_SECONDS} секунд.\n\n"
                "Проверьте подключение платы и режим BOOTSEL.",
                parent=self,
            )
            return False

        if returncode != 0:
            details = (stderr or stdout or "").strip()
            messagebox.showerror(
                "Ошибка чтения backup",
                f"picotool завершился с кодом {returncode}.\n\n"
                f"{details}\n\n"
                "Проверьте, что плата подключена в режиме BOOTSEL.",
                parent=self,
            )
            return False

        path = Path(filename)
        try:
            size = path.stat().st_size
        except OSError as exc:
            messagebox.showerror("Ошибка чтения backup", str(exc), parent=self)
            return False

        if size < DATA_OFFSET:
            messagebox.showerror(
                "Ошибка чтения backup",
                f"Файл слишком мал: {format_size(size)} байт.\n"
                f"Ожидалось не менее {format_size(DATA_OFFSET)} байт.",
                parent=self,
            )
            return False

        try:
            base, entries, data_end = read_bin(path)
        except Exception as exc:  # noqa: BLE001
            messagebox.showwarning(
                "Backup прочитан",
                f"Файл сохранён:\n{path}\n\n"
                f"Но открыть таблицу не удалось:\n{exc}",
                parent=self,
            )
            return False

        self.bin_path = path
        self.bin_base = base
        self.entries = entries
        self.data_end = data_end
        self.dirty = False
        self.refresh()
        messagebox.showinfo(
            "Готово",
            f"Backup прочитан с RP2040:\n{path}\n\n"
            f"Размер: {format_size(size)} байт.\n"
            f"Записей: {len(entries)}.",
            parent=self,
        )
        return True

    def _tail_start(self) -> int:
        """Первый не-0xFF байт после области данных (начало служебных данных)."""
        if not self.bin_base:
            return DATA_OFFSET
        pos = self.data_end
        while pos < len(self.bin_base) and self.bin_base[pos] == 0xFF:
            pos += 1
        return pos

    def _confirm_save(self) -> bool:
        if not self.dirty:
            return True
        answer = messagebox.askyesnocancel(
            "Несохранённые изменения",
            "В таблице есть несохранённые изменения.\n\nСохранить их?",
            parent=self,
        )
        if answer is None:
            return False
        if answer:
            return self._on_save()
        return True

    def _on_close(self) -> None:
        if self._confirm_save():
            self.destroy()

    # ---------- Удаление / добавление ----------

    def _on_delete(self) -> None:
        index = self._selected_index()
        if index is None:
            messagebox.showinfo("Удаление", "Сначала выберите запись в списке.", parent=self)
            return

        entry = self.entries[index]
        if not messagebox.askyesno(
            "Удаление",
            f"Удалить запись «{entry.name}»?",
            parent=self,
        ):
            return

        del self.entries[index]
        self._renumber()
        self._mark_dirty()
        self.refresh()

    def _on_clear(self) -> None:
        if not self.entries:
            messagebox.showinfo("Очистить", "Таблица уже пуста.", parent=self)
            return

        if not messagebox.askyesno(
            "Очистить",
            f"Удалить все записи ({len(self.entries)})?",
            parent=self,
        ):
            return

        self.entries.clear()
        self._mark_dirty()
        self.refresh()

    def _on_add_rom(self) -> None:
        filenames = filedialog.askopenfilenames(
            parent=self,
            title="Добавить ROM",
            initialdir=str(DEFAULT_FILE.parent),
            filetypes=[
                ("NES ROM", "*.nes"),
                ("Все файлы", "*.*"),
            ],
        )
        if not filenames:
            return

        loaded: list[tuple[str, bytes]] = []
        errors: list[str] = []
        converted: list[str] = []
        for filename in filenames:
            path = Path(filename)
            try:
                data = path.read_bytes()
            except OSError as exc:
                errors.append(f"{path.name}: {exc}")
                continue

            try:
                normalized, mapper, was_nes2 = normalize_ines_rom(data)
            except RomValidationError as exc:
                errors.append(f"{path.name}: {exc}")
                continue

            loaded.append((path.stem, normalized))
            if was_nes2:
                converted.append(f"{path.name} (mapper {mapper})")

        if errors:
            details = "\n".join(errors[:15])
            if len(errors) > 15:
                details += f"\n… и ещё {len(errors) - 15}"
            messagebox.showerror(
                "Ошибка добавления ROM",
                "Эти файлы не добавлены:\n\n" + details,
                parent=self,
            )

        if not loaded:
            return

        if len(self.entries) + len(loaded) > MAX_ENTRIES:
            messagebox.showerror(
                "Слишком много записей",
                f"В таблицу помещается не более {MAX_ENTRIES} записей.",
                parent=self,
            )
            return

        for name, data in loaded:
            name = strip_number_prefix(name)
            self.entries.append(RomEntry(sanitize_name(name), data))

        self._renumber()

        self._mark_dirty()
        self.refresh()

        last = len(self.entries) - 1
        self.tree.selection_set(str(last))
        self.tree.focus(str(last))
        self.tree.see(str(last))

        if converted:
            details = "\n".join(converted[:15])
            if len(converted) > 15:
                details += f"\n… и ещё {len(converted) - 15}"
            messagebox.showinfo(
                "NES 2.0 → iNES 1.0",
                "Заголовок NES 2.0 преобразован в iNES 1.0.\n"
                f"Файлов: {len(converted)}\n\n{details}",
                parent=self,
            )

    def _on_extract_rom(self) -> None:
        if not self.entries:
            messagebox.showinfo(
                "Распаковать ROM",
                "Таблица пуста — нечего распаковывать.",
                parent=self,
            )
            return

        base_dir = self.bin_path.parent if self.bin_path else DEFAULT_FILE.parent
        target = base_dir / "ROM"

        if target.exists():
            if not target.is_dir():
                messagebox.showerror(
                    "Распаковать ROM",
                    f"Путь занят файлом:\n{target}",
                    parent=self,
                )
                return
            if any(target.iterdir()) and not messagebox.askyesno(
                "Папка ROM",
                f"Папка уже существует:\n{target}\n\n"
                "Заменить файлы с совпадающими именами?",
                parent=self,
            ):
                return

        try:
            written, skipped = extract_nes_files(self.entries, target)
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror("Ошибка распаковки", str(exc), parent=self)
            return

        if not written:
            messagebox.showinfo(
                "Распаковать ROM",
                "В таблице не найдено ни одного NES-файла.",
                parent=self,
            )
            return

        text = f"Распаковано NES-файлов: {len(written)}\n\nПапка:\n{target}"
        if skipped:
            text += f"\n\nПропущено (не NES): {skipped}"
        messagebox.showinfo("Готово", text, parent=self)

    # ---------- Редактирование имени ----------

    def _on_double_click(self, event: tk.Event) -> None:
        row = self.tree.identify_row(event.y)
        if not row:
            return
        self.tree.selection_set(row)
        self.tree.focus(row)
        self._start_edit(row)

    def _on_right_click(self, event: tk.Event) -> str:
        row = self.tree.identify_row(event.y)
        if row:
            self.tree.selection_set(row)
            self.tree.focus(row)
            self.context_menu.tk_popup(event.x_root, event.y_root)
        return "break"

    def _edit_selected(self) -> None:
        index = self._selected_index()
        if index is not None:
            self._start_edit(str(index))

    def _on_f2(self, _event: tk.Event) -> None:
        self._edit_selected()

    def _start_edit(self, row: str) -> None:
        self._cancel_edit()
        try:
            index = int(row)
        except ValueError:
            return
        if not 0 <= index < len(self.entries):
            return

        bbox = self.tree.bbox(row, "name")
        if not bbox:
            return

        x, y, width, height = bbox
        editor = ttk.Entry(self.tree)
        editor.insert(0, self.entries[index].name)
        editor.select_range(0, "end")
        editor.place(x=x, y=y, width=width, height=height)
        editor.focus_set()

        self._editor = editor
        self._edit_index = index

        editor.bind("<Return>", self._commit_edit)
        editor.bind("<KP_Enter>", self._commit_edit)
        editor.bind("<Escape>", self._cancel_edit)
        editor.bind("<FocusOut>", self._commit_edit)

    def _commit_edit(self, _event: tk.Event | None = None) -> None:
        if self._editor is None:
            return

        editor = self._editor
        index = self._edit_index
        self._editor = None
        self._edit_index = None

        value = editor.get().strip()
        editor.destroy()

        if index is None:
            return

        try:
            raw = value.encode("latin-1")
        except UnicodeEncodeError:
            messagebox.showerror(
                "Недопустимое имя",
                "Имя должно содержать только символы Latin-1 "
                "(латиница, цифры, знаки препинания).",
                parent=self,
            )
            return

        if not raw:
            messagebox.showerror(
                "Недопустимое имя",
                "Имя не может быть пустым.",
                parent=self,
            )
            return

        if len(raw) > NAME_SIZE:
            raw = raw[:NAME_SIZE]

        self.entries[index].name = raw.decode("latin-1")
        self._renumber()
        self._mark_dirty()
        self.refresh()
        self.tree.selection_set(str(index))
        self.tree.focus(str(index))

    def _cancel_edit(self, _event: tk.Event | None = None) -> None:
        if self._editor is not None:
            self._editor.destroy()
            self._editor = None
            self._edit_index = None


def main() -> int:
    app = RomManagerApp()
    app.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
