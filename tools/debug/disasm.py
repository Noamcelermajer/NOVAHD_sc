"""Disassemble the executable with import, symbol and selector names: py -3 tools/debug/disasm.py EXE ADDR [COUNT] [t]"""
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parents[1] / "recomp"))
from capstone import CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB, Cs
from macho import Image

image = Image(Path(sys.argv[1]))
addr, count = int(sys.argv[2], 16), int(sys.argv[3]) if len(sys.argv) > 3 else 40
thumb = len(sys.argv) > 4 or bool(addr & 1)
stubs = {a: n for a, (n, _) in image.plt.items()}
syms = {f.address: f.name for f in image.functions}
imports = {v: k for k, v in image.imports.items()}


def cstr(a):
    try:
        e = image.memory.index(b"\0", a, a + 200)
        s = image.memory[a:e].decode()
        return s if s.isprintable() else None
    except (ValueError, UnicodeDecodeError):
        return None


def note(v):
    if v in stubs: return stubs[v]
    if v in syms: return syms[v]
    if v in imports: return "&" + imports[v]
    if 0x1000 <= v < image.size:
        w = image.u32(v)
        if w in imports: return "-> " + imports[w]
        s = cstr(w) if 0x1000 <= w < image.size else None
        if s: return f'-> "{s}"'
        s = cstr(v)
        if s and len(s) > 1: return f'"{s}"'
    return ""


md = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
a = addr & ~1
for i in md.disasm(bytes(image.memory[a:a + 4 * count]), a):
    extra = []
    for h in re.findall(r"#(0x[0-9a-f]+)", i.op_str):
        n = note(int(h, 16))
        if n: extra.append(n)
    m = re.search(r"\[pc, #(-?0x[0-9a-f]+|-?\d+)\]", i.op_str)
    if m and i.mnemonic.startswith("ldr"):
        lit = ((i.address + (4 if thumb else 8)) & ~3) + int(m.group(1), 0)
        v = image.u32(lit)
        extra.append(f"=0x{v:x} {note(v)}")
    print(f"  {i.address:7x}  {i.mnemonic:8s} {i.op_str:32s} {'; '.join(extra)}")
