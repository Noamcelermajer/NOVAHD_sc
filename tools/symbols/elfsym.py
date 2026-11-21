"""Minimal 32-bit little-endian ELF reader: sections, symbols, memory image (no third-party dependency)."""
from __future__ import annotations

import struct
from dataclasses import dataclass
from pathlib import Path


@dataclass
class Sym:
    name: str
    value: int
    size: int
    kind: int      # STT_*
    bind: int      # STB_*
    shndx: int


class Elf:
    def __init__(self, path: Path):
        self.raw = Path(path).read_bytes()
        raw = self.raw
        if raw[:4] != b"\x7fELF" or raw[4] != 1:
            raise ValueError("not a 32-bit ELF")
        shoff, = struct.unpack_from("<I", raw, 0x20)
        shentsize, shnum, shstrndx = struct.unpack_from("<HHH", raw, 0x2E)
        secs = []
        for k in range(shnum):
            secs.append(struct.unpack_from("<10I", raw, shoff + k * shentsize))
        names = secs[shstrndx]
        self.sections = {}
        for nm, ty, fl, addr, off, size, link, info, al, es in secs:
            end = raw.index(b"\0", names[4] + nm)
            self.sections[raw[names[4] + nm:end].decode()] = dict(type=ty, flags=fl, addr=addr, off=off, size=size,
                                                                   link=link, entsize=es)
        # load image
        top = max(s["addr"] + s["size"] for s in self.sections.values() if s["flags"] & 2)
        self.memory = bytearray(top)
        for s in self.sections.values():
            if s["flags"] & 2 and s["type"] != 8:
                self.memory[s["addr"]:s["addr"] + s["size"]] = raw[s["off"]:s["off"] + s["size"]]
        self.symbols = []
        sym, st = self.sections[".symtab"], self.sections[".strtab"]
        for k in range(sym["size"] // 16):
            nm, val, size, info, other, shndx = struct.unpack_from("<IIIBBH", raw, sym["off"] + 16 * k)
            end = raw.index(b"\0", st["off"] + nm)
            self.symbols.append(Sym(raw[st["off"] + nm:end].decode("latin1"), val, size, info & 15, info >> 4, shndx))

    def u32(self, a: int) -> int:
        return struct.unpack_from("<I", self.memory, a)[0]

    def cstring(self, a: int, limit: int = 512):
        if not 0 < a < len(self.memory):
            return None
        end = self.memory.find(b"\0", a, a + limit)
        if end < 0:
            return None
        return bytes(self.memory[a:end])
