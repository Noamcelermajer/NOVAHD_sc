"""Load the iOS Mach-O and the Android ELF into the same shape: {address: Fn}, names, memory, vtables."""
from __future__ import annotations

import pickle
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "recomp"))

from elfsym import Elf  # noqa: E402
from features import Fn, extract  # noqa: E402

N_SECT, N_TYPE = 0x0E, 0x0E


class Bin:
    def __init__(self):
        self.funcs = {}   # address (no thumb bit) -> Fn
        self.names = {}   # address -> symbol name (mangled, as in the C++ ABI)
        self.mem = b""
        self.vtables = {}  # vtable address (of the first slot) -> list of slot addresses
        self.vtable_names = {}  # class vtable symbol (_ZTV...) -> slot-0 address
        self.text = (0, 0)


def _vtable_slots(mem, a, in_text, limit=400):
    out = []
    for k in range(limit):
        p = a + 4 * k
        if p + 4 > len(mem):
            break
        v = int.from_bytes(mem[p:p + 4], "little")
        if v == 0 and k:
            break
        if not in_text(v & ~1):
            break
        out.append(v & ~1)
    return out


def load_ios(exe: Path, cache: Path | None) -> Bin:
    newest = max(Path(exe).stat().st_mtime, (HERE.parent / "recomp" / "macho.py").stat().st_mtime,
                 (HERE / "features.py").stat().st_mtime)
    if cache and cache.exists() and cache.stat().st_mtime > newest:
        return pickle.loads(cache.read_bytes())
    from macho import Image
    im = Image(exe)
    b = Bin()
    b.mem = bytes(im.memory)
    t = im.text
    b.text = (t.addr, t.addr + t.size)
    cs = im.section("__TEXT", "__cstring")
    str_range = (cs.addr, cs.addr + cs.size)
    ds = [s for s in im.segments if s[5] == "__DATA"][0]
    data_range = (ds[0], ds[1])
    in_text = lambda a: b.text[0] <= a < b.text[1]
    for name, ty, sect, desc, va in im.symbols:
        if (ty & N_TYPE) == N_SECT:
            if in_text(va & ~1) and name.startswith("_"):
                b.names[va & ~1] = name[1:]
            elif name.startswith("__ZTV"):
                b.vtable_names[name[1:]] = va
    mem = b.mem
    fset = {f.address for f in im.functions}
    plt, stubs = im.plt, im.local_stubs

    def call_target(a):
        if a in plt:
            return ("i", plt[a][0])
        if a in stubs:
            return ("f", stubs[a] & ~1)
        if a in fset:
            return ("f", a)
        return None

    def vtable_ok(a):
        if not (data_range[0] + 8 <= a < data_range[1]):
            return False
        if int.from_bytes(mem[a - 8:a - 4], "little") != 0:
            return False
        v = int.from_bytes(mem[a:a + 4], "little")
        return in_text(v & ~1) and data_range[0] <= int.from_bytes(mem[a - 4:a], "little") < data_range[1]

    for f in im.functions:
        fn = Fn(f.address, f.size, f.thumb, b.names.get(f.address, ""))
        extract(mem, fn, f.data_ranges, str_range, call_target, vtable_ok)
        b.funcs[f.address] = fn
    for fn in b.funcs.values():
        for a in fn.vtables:
            b.vtables.setdefault(a, _vtable_slots(mem, a, in_text))
    for n, a in b.vtable_names.items():
        b.vtables.setdefault(a + 8, _vtable_slots(mem, a + 8, in_text))
    if cache:
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(pickle.dumps(b))
    return b


def load_android(so: Path, cache: Path | None) -> Bin:
    newest = max(Path(so).stat().st_mtime, (HERE / "features.py").stat().st_mtime)
    if cache and cache.exists() and cache.stat().st_mtime > newest:
        return pickle.loads(cache.read_bytes())
    e = Elf(so)
    b = Bin()
    b.mem = bytes(e.memory)
    mem = b.mem
    t = e.sections[".text"]
    b.text = (t["addr"], t["addr"] + t["size"])
    in_text = lambda a: b.text[0] <= a < b.text[1]
    ro = e.sections[".rodata"]
    str_range = (ro["addr"], ro["addr"] + ro["size"])
    dr = e.sections[".data.rel.ro"]
    data_range = (dr["addr"], dr["addr"] + dr["size"])

    # PLT: 20-byte header, then 12-byte entries in .rel.plt order
    plt = {}
    pl, rp, dyn = e.sections[".plt"], e.sections[".rel.plt"], e.sections[".dynsym"]
    dstr = e.sections[".dynstr"]
    for k in range(rp["size"] // 8):
        off, info = struct.unpack_from("<II", e.raw, rp["off"] + 8 * k)
        sidx = info >> 8
        nm = struct.unpack_from("<I", e.raw, dyn["off"] + 16 * sidx)[0]
        end = e.raw.index(b"\0", dstr["off"] + nm)
        plt[pl["addr"] + 20 + 12 * k] = e.raw[dstr["off"] + nm:end].decode()
    funcs = [s for s in e.symbols if s.kind == 2 and s.shndx and s.value and in_text(s.value & ~1)]
    fset = {s.value & ~1 for s in funcs}
    for s in funcs:
        b.names.setdefault(s.value & ~1, s.name)
    for s in e.symbols:
        if s.name.startswith("_ZTV") and s.value:
            b.vtable_names[s.name] = s.value

    def call_target(a):
        if a in plt:
            return ("i", plt[a])
        if a in fset:
            return ("f", a)
        return None

    def vtable_ok(a):
        if not (data_range[0] + 8 <= a < data_range[1]):
            return False
        if int.from_bytes(mem[a - 8:a - 4], "little") != 0:
            return False
        v = int.from_bytes(mem[a:a + 4], "little")
        return in_text(v & ~1)

    seen = set()
    for s in funcs:
        a = s.value & ~1
        if a in seen or s.size < 2:
            continue
        seen.add(a)
        fn = Fn(a, s.size, bool(s.value & 1), s.name)
        extract(mem, fn, [], str_range, call_target, vtable_ok)
        b.funcs[a] = fn
    for fn in b.funcs.values():
        for a in fn.vtables:
            b.vtables.setdefault(a, _vtable_slots(mem, a, in_text))
    for n, a in b.vtable_names.items():
        b.vtables.setdefault(a + 8, _vtable_slots(mem, a + 8, in_text))
    if cache:
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(pickle.dumps(b))
    return b
