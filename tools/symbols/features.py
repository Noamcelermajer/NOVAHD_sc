"""Per-function features for both binaries: ordered direct callees, string literals, rare constants.

The two binaries are different ISAs/compilers (iOS: mostly ARM mode, non-PIC; Android: Thumb, PIC), so only what survives
a recompile is kept: who a function calls and in what order, which string literals it references, which unusual 32-bit
constants it loads, and a rough size.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

from capstone import CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB, Cs

_LDR_PC = re.compile(r"^(ldr|ldr\.w)\s+(\w+),\s*\[pc(?:,\s*#(-?)(0x[0-9a-f]+|\d+))?\]$")
_ADD_PC = re.compile(r"^add(?:\.w)?\s+(\w+),\s*(?:(\w+),\s*)?(\w+)(?:,\s*(\w+))?$")
_BRANCH = re.compile(r"^#(0x[0-9a-f]+)$")
_MOVW = re.compile(r"^(movw|movt)\s+(\w+),\s*#(0x[0-9a-f]+|\d+)$")
_MOV_IMM = re.compile(r"^mov(?:s|\.w)?\s+(\w+),\s*#(0x[0-9a-f]+|\d+)$")


@dataclass
class Fn:
    addr: int
    size: int
    thumb: bool
    name: str = ""
    calls: list = field(default_factory=list)    # ordered: ("f", addr) | ("i", import name)
    strings: list = field(default_factory=list)  # ordered, with repeats removed
    consts: set = field(default_factory=set)
    insns: int = 0
    nums: set = field(default_factory=set)       # structure offsets and small literal constants (>= 8, < 0x10000)
    vtables: list = field(default_factory=list)  # data addresses that look like a vtable start (+8 form), in code order


def printable_string(mem, a: int, lo: int, hi: int, minlen: int = 4):
    if not lo <= a < hi:
        return None
    end = mem.find(b"\0", a, min(hi, a + 400))
    if end < 0 or end - a < minlen:
        return None
    s = bytes(mem[a:end])
    if all(32 <= c < 127 or c in (9, 10, 13) for c in s):
        return s.decode("ascii")
    return None


_REG = {"sb": "r9", "sl": "r10", "fp": "r11", "ip": "r12"}
_NO_DEST = {"cmp", "cmn", "tst", "teq", "str", "strb", "strh", "push", "stm", "stmia", "stmdb", "stmfd", "b", "bx",
            "bl", "blx", "nop", "cbz", "cbnz", "vstr", "vpush", "vstm", "svc", "bkpt", "it", "ite", "itt", "pld"}
_IS_REG = re.compile(r"^(r\d+|sb|sl|fp|ip|sp|lr|pc)$")
_CLOBBER_ON_CALL = ("r0", "r1", "r2", "r3", "r12")


def _split(ops: str):
    out, depth, cur = [], 0, ""
    for ch in ops:
        if ch == "[" or ch == "{":
            depth += 1
        elif ch == "]" or ch == "}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def _reg(x):
    x = x.strip()
    x = _REG.get(x, x)
    return x if _IS_REG.match(x) else None


def _imm(x):
    x = x.strip()
    if x.startswith("#"):
        try:
            return int(x[1:], 0)
        except ValueError:
            return None
    return None


def extract(mem, fn: Fn, data_ranges, str_range, call_target, vtable_ok):
    """Fill fn from its code. call_target(addr) -> ("f", a) / ("i", name) / None.

    A small forward value tracker follows registers that hold a known constant: literal-pool loads, PC-relative adds
    (Thumb PIC), the GOT base plus an offset literal (Android), loads from the GOT. Whatever such a register is set to
    is classified: string literal, vtable, or a rare constant.
    """
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB if fn.thumb else CS_MODE_ARM)
    start, end = fn.addr, fn.addr + fn.size
    pc_off = 4 if fn.thumb else 8
    insns = list(md.disasm(bytes(mem[start:end]), start))
    fn.insns = len(insns)
    known = {}
    seen = set()
    M32 = 0xFFFFFFFF
    memlen = len(mem)

    def note(v, from_lit):
        s = printable_string(mem, v, *str_range)
        if s is not None:
            if s not in seen:
                seen.add(s)
                fn.strings.append(s)
            return
        if vtable_ok(v):
            if v not in fn.vtables:
                fn.vtables.append(v)
            return
        if from_lit and v > 0xFFFF and v != M32 and not (0x1000 < v < memlen and v < 0x10000000):
            fn.consts.add(v)

    def val(x, a):
        r = _reg(x)
        if r == "pc":
            return (a + pc_off) & M32
        if r:
            return known.get(r)
        return _imm(x)

    for k, i in enumerate(insns):
        m, a = i.mnemonic, i.address
        if any(s <= a < e for s, e in data_ranges):
            known.clear()
            continue
        ops = _split(i.op_str)
        if m in ("bl", "blx", "b", "b.w") and len(ops) == 1:
            mt = _BRANCH.match(ops[0])
            if mt:
                t = int(mt.group(1), 16)
                if m in ("bl", "blx") or not (start <= t < end):
                    r = call_target(t)
                    if r:
                        fn.calls.append(r)
            if m in ("bl", "blx"):
                for r in _CLOBBER_ON_CALL:
                    known.pop(r, None)
            continue
        if m[:3] in ("ldr", "str") or m[:4] in ("vldr", "vstr"):
            for o in ops[1:]:
                if o.startswith("["):
                    inner = _split(o.strip("[]!"))
                    b0 = _reg(inner[0]) if inner else None
                    if b0 in (None, "sp", "pc") or len(inner) < 2:
                        break
                    off = _imm(inner[1])
                    if off is None and _reg(inner[1]):
                        off = known.get(_reg(inner[1]))
                    if off is not None and 8 <= off < 0x10000:
                        fn.nums.add(off)
                    break
        if m in _NO_DEST or not ops:
            if m in ("bx", "blx"):
                for r in _CLOBBER_ON_CALL:
                    known.pop(r, None)
            continue
        d = _reg(ops[0])
        if d is None:
            continue
        newv = None
        lit = False
        if m in ("ldr", "ldr.w") and len(ops) >= 2 and ops[1].startswith("["):
            inner = _split(ops[1].strip("[]!"))
            if (inner and not ops[1].endswith("!") and len(ops) == 2 and _reg(inner[0]) == "pc"
                    and (len(inner) == 1 or _imm(inner[1]) is not None)):
                off = _imm(inner[1]) if len(inner) == 2 else 0
                la = (((a + pc_off) & ~3) if fn.thumb else a + pc_off) + off
                if 0 <= la and la + 4 <= memlen:
                    newv, lit = int.from_bytes(mem[la:la + 4], "little"), True
            elif len(ops) == 2 and "!" not in ops[1]:
                base = val(inner[0], a) if inner else None
                if base is not None:
                    if len(inner) == 1:
                        off = 0
                    elif _imm(inner[1]) is not None:
                        off = _imm(inner[1])
                    else:
                        off = val(inner[1], a) if len(inner) == 2 else None
                    if off is not None and 0 <= (base + off) & M32 and ((base + off) & M32) + 4 <= memlen:
                        newv = int.from_bytes(mem[(base + off) & M32:((base + off) & M32) + 4], "little")
                        if newv < 0x1000:
                            newv = None
        elif m in ("add", "adds", "add.w", "addw") and len(ops) in (2, 3):
            srcs = ops[1:] if len(ops) == 3 else [ops[0], ops[1]]
            vs = [val(x, a) for x in srcs]
            if all(v is not None for v in vs):
                newv = sum(vs) & M32
        elif m in ("sub", "subs", "sub.w", "subw") and len(ops) in (2, 3):
            srcs = ops[1:] if len(ops) == 3 else [ops[0], ops[1]]
            vs = [val(x, a) for x in srcs]
            if all(v is not None for v in vs):
                newv = (vs[0] - vs[1]) & M32
        elif m in ("mov", "movs", "mov.w", "movw") and len(ops) == 2:
            v = val(ops[1], a)
            if v is not None:
                newv = v & M32
                if m == "movw":
                    known[d] = newv
                    continue
        elif m == "movt" and len(ops) == 2 and d in known and _imm(ops[1]) is not None:
            newv = (known[d] & 0xFFFF) | (_imm(ops[1]) << 16)
            lit = True
        if newv is None:
            known.pop(d, None)
            continue
        known[d] = newv
        if lit and 0x40 <= newv < 0x10000:
            fn.nums.add(newv)
        if newv > 0xFFF:
            note(newv, lit)
