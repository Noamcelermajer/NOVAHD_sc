"""Re-run one difftest case with a trace of the original's path: py -3 tools/debug/onerun.py EXE ADDR RUN"""
import ctypes, random, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parents[1] / "recomp"))
import difftest as D
from macho import Image
from lift import entries
from unicorn import UC_HOOK_CODE
from unicorn import arm_const as U

exe, addr, run = sys.argv[1], int(sys.argv[2], 16), int(sys.argv[3])
image = Image(Path(exe))
ents = entries(image)
dll = ctypes.CDLL(str(Path("build/recomp/recomp.dll").resolve()))
h = D.Harness(image, dll, 1)
path = []
h.uc.hook_add(UC_HOOK_CODE, lambda uc, a, s, _: path.append(a) if len(path) < 400 else None)
f = ents[addr]
rng = random.Random(addr * 1000 + run)
mem = h.snapshot(run % 8)
regs, flags, fpscr, d = h.state(rng)
print("regs", [hex(x) for x in regs], "flags", flags)
u, why = h.run_unicorn(addr, mem, regs, flags, fpscr, d, bool(f.thumb))
print("unicorn:", why or [hex(x) for x in u["r"]])
blocks = []
for a in path:
    if not blocks or a != blocks[-1][1] + 4:
        blocks.append([a, a])
    else:
        blocks[-1][1] = a
print("path:", " ".join(f"{s:x}-{e:x}" for s, e in blocks[:60]))
hh = h.run_host(addr, mem, regs, flags, fpscr, d)
print("host fault", hh["fault"], [hex(x) for x in hh["r"]])
print("diff:", D.compare(u, hh) if u else None)
