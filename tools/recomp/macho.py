"""The original iOS executable (32-bit ARM Mach-O) as game memory, with its imports and its functions.

An MH_EXECUTE image is not position independent, so it is loaded at its link addresses: game address == link
address, IMAGE_BASE is 0. __PAGEZERO (0x0-0xfff) stays unmapped, so a null pointer still faults.

Game memory layout (32-bit addresses):
  0x00001000 ...        __TEXT, __DATA, __LINKEDIT at their link addresses
  IMPORT_STUB_BASE      one 4-byte slot per import; lazy and non-lazy pointers and external relocations point here
  0x01000000 ...        free for the runtime (heap, stacks)

The executable keeps only its exported symbols, so most function starts are found by recursive descent
(`discover`): from the symbols, the entry point, the static constructors, Objective-C method implementations and
every word in the data segment or in a literal pool that points into __text, follow branches and calls in the
mode the reference implies (ARM, or Thumb when the low bit is set or the call is a BLX). Words of __text that no
descent reaches are data (literal pools, jump tables); the lifter skips them.

Interface used by lift.py and difftest.py (the same as image.py in NOVA3_sc): memory, size, segments, writable,
imports (name -> slot address, in slot order), plt (stub address -> (name, pointer address)), functions,
by_address, code().
"""
from __future__ import annotations

import bisect
import struct
from dataclasses import dataclass, field
from pathlib import Path

from capstone import CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB, Cs
from capstone import arm as A

IMAGE_BASE = 0
IMPORT_STUB_BASE = 0x00F00000

LC_SEGMENT, LC_SYMTAB, LC_UNIXTHREAD, LC_DYSYMTAB, LC_ENCRYPTION_INFO = 0x1, 0x2, 0x5, 0xB, 0x21
LC_DYLD_INFO, LC_DYLD_INFO_ONLY = 0x22, 0x80000022
S_NON_LAZY_SYMBOL_POINTERS, S_LAZY_SYMBOL_POINTERS, S_SYMBOL_STUBS = 6, 7, 8
INDIRECT_SYMBOL_LOCAL, INDIRECT_SYMBOL_ABS = 0x80000000, 0x40000000
N_TYPE, N_SECT, N_ARM_THUMB_DEF = 0x0E, 0x0E, 0x0008


@dataclass
class Function:
    address: int
    size: int
    name: str
    data_ranges: list = field(default_factory=list)
    thumb: bool = False

    def is_data(self, addr: int) -> bool:
        return any(s <= addr < e for s, e in self.data_ranges)


@dataclass
class Section:
    segment: str
    name: str
    addr: int
    size: int
    offset: int
    flags: int
    reserved1: int
    reserved2: int


def import_name(macho_name: str) -> str:
    """C-level name of a Mach-O symbol (the compiler's leading underscore removed): `_memcpy` -> `memcpy`."""
    return macho_name[1:] if macho_name.startswith("_") else macho_name


class Image:
    def __init__(self, path: Path, discover_functions: bool = True):
        self.path = Path(path)
        raw = self.path.read_bytes()
        magic, cputype, _, filetype, ncmds = struct.unpack_from("<5I", raw, 0)
        if magic != 0xFEEDFACE or cputype != 12:
            raise ValueError("not a thin 32-bit ARM Mach-O (extract one architecture with lipo first)")
        self.segments, self.sections = [], []
        self.all_segments = []  # every LC_SEGMENT in order (bind opcodes index this list), as (vmaddr, name)
        self.entry = None
        self.dyld_info = None
        symtab = dysymtab = None
        off = 28
        for _ in range(ncmds):
            cmd, size = struct.unpack_from("<II", raw, off)
            if cmd == LC_SEGMENT:
                name = raw[off + 8:off + 24].rstrip(b"\0").decode()
                va, vs, fo, fs, _, initprot, nsect, _ = struct.unpack_from("<8I", raw, off + 24)
                self.all_segments.append((va, name))
                if name != "__PAGEZERO":
                    self.segments.append((va, va + vs, initprot, fo, fs, name))
                for k in range(nsect):
                    so = off + 56 + 68 * k
                    sect = raw[so:so + 16].rstrip(b"\0").decode()
                    a, z, o, _, _, _, fl, r1, r2 = struct.unpack_from("<9I", raw, so + 32)
                    self.sections.append(Section(name, sect, a, z, o, fl, r1, r2))
            elif cmd == LC_SYMTAB:
                symtab = struct.unpack_from("<4I", raw, off + 8)
            elif cmd == LC_DYSYMTAB:
                dysymtab = struct.unpack_from("<18I", raw, off + 8)
            elif cmd == LC_UNIXTHREAD:
                flavor, count = struct.unpack_from("<II", raw, off + 8)
                self.entry = struct.unpack_from("<I", raw, off + 16 + 15 * 4)[0]  # r0-r12, sp, lr, pc
            elif cmd in (LC_DYLD_INFO, LC_DYLD_INFO_ONLY):
                self.dyld_info = struct.unpack_from("<10I", raw, off + 8)
            elif cmd == LC_ENCRYPTION_INFO and struct.unpack_from("<I", raw, off + 16)[0]:
                raise ValueError("the executable is encrypted (cryptid != 0): use a decrypted dump")
            off += size
        self.size = (max(e for _, e, *_ in self.segments) + 0xFFFF) & ~0xFFFF
        self.memory = bytearray(self.size)
        for va, _, _, fo, fs, _ in self.segments:
            self.memory[va:va + fs] = raw[fo:fo + fs]

        # symbols
        symoff, nsyms, stroff, _ = symtab
        self.symbols = []  # (name, n_type, n_sect, n_desc, value)
        for k in range(nsyms):
            sx, ty, se, de, va = struct.unpack_from("<IBBhI", raw, symoff + 12 * k)
            end = raw.index(b"\0", stroff + sx)
            self.symbols.append((raw[stroff + sx:end].decode("latin1"), ty, se, de & 0xFFFF, va))

        # imports: every undefined symbol gets a slot, in symbol table order
        iundef, nundef = dysymtab[4], dysymtab[5]
        self.imports = {}
        for name, *_ in self.symbols[iundef:iundef + nundef]:
            self.imports[import_name(name)] = IMPORT_STUB_BASE + 4 * len(self.imports)
        self.import_at = {v: k for k, v in self.imports.items()}

        # indirect symbols: stubs, lazy and non-lazy pointers
        indoff = dysymtab[12]
        self.plt = {}
        self.pointer_imports = {}  # pointer slot address -> import name
        self.local_stubs = {}  # stub address -> defined function it binds to (low bit: Thumb)
        for s in self.sections:
            kind = s.flags & 0xFF
            if kind not in (S_NON_LAZY_SYMBOL_POINTERS, S_LAZY_SYMBOL_POINTERS, S_SYMBOL_STUBS):
                continue
            step = s.reserved2 if kind == S_SYMBOL_STUBS else 4
            for j in range(s.size // step):
                sym = struct.unpack_from("<I", raw, indoff + 4 * (s.reserved1 + j))[0]
                if sym & (INDIRECT_SYMBOL_LOCAL | INDIRECT_SYMBOL_ABS):
                    continue
                sname, sty, _, sdesc, sval = self.symbols[sym]
                name = import_name(sname)
                at = s.addr + step * j
                if (sty & N_TYPE) == N_SECT:  # a defined (weak, coalesced) symbol: bound to itself
                    if kind == S_SYMBOL_STUBS:
                        self.local_stubs[at] = sval | (1 if sdesc & N_ARM_THUMB_DEF else 0)
                    else:
                        self.memory[at:at + 4] = (sval | (1 if sdesc & N_ARM_THUMB_DEF else 0)).to_bytes(4, "little")
                    continue
                if kind == S_SYMBOL_STUBS:
                    self.plt[at] = (name, self._stub_pointer(at, step))
                else:
                    self.pointer_imports[at] = name
                    self.memory[at:at + 4] = self.imports[name].to_bytes(4, "little")

        # external relocations: data words that hold the address of an import (+ addend)
        extreloff, nextrel = dysymtab[14], dysymtab[15]
        self.reloc_imports = {}
        self.bound = {}  # word address -> import (or weak symbol) bound there by LC_DYLD_INFO
        for k in range(nextrel):
            addr, info = struct.unpack_from("<iI", raw, extreloff + 8 * k)
            symnum, pcrel, length, ext = info & 0xFFFFFF, (info >> 24) & 1, (info >> 25) & 3, (info >> 27) & 1
            if addr < 0 or not ext or pcrel or length != 2:
                raise ValueError(f"unhandled external relocation at {addr:#x} ({info:#x})")
            name = import_name(self.symbols[symnum][0])
            word = int.from_bytes(self.memory[addr:addr + 4], "little")
            self.memory[addr:addr + 4] = ((word + self.imports[name]) & 0xFFFFFFFF).to_bytes(4, "little")
            self.reloc_imports[addr] = name

        # compressed binding (LC_DYLD_INFO): data words bound to imports (Objective-C superclasses, class
        # references, the isa of constant strings, C++ type-info vtables, ...)
        if self.dyld_info:
            bind_off, bind_size, _, _, lazy_off, lazy_size = self.dyld_info[2:8]
            self._bind(raw[bind_off:bind_off + bind_size], lazy=False)
            self._bind(raw[lazy_off:lazy_off + lazy_size], lazy=True)

        self.text = self.section("__TEXT", "__text")
        self.functions = discover(self) if discover_functions else []
        self.by_address = {f.address: f for f in self.functions}

    def _bind(self, ops: bytes, lazy: bool):
        """Run dyld's bind opcodes: each bound word becomes the import's slot address plus the addend."""
        pos, seg_addr, addr, sym, addend = 0, 0, 0, None, 0

        def uleb():
            nonlocal pos
            v = sh = 0
            while True:
                b = ops[pos]
                pos += 1
                v |= (b & 0x7F) << sh
                sh += 7
                if b < 0x80:
                    return v

        def sleb():
            nonlocal pos
            v = sh = 0
            while True:
                b = ops[pos]
                pos += 1
                v |= (b & 0x7F) << sh
                sh += 7
                if b < 0x80:
                    return v - (1 << sh) if b & 0x40 else v

        def bind():
            name = import_name(sym)
            if name in self.imports:
                target = self.imports[name]
            else:  # a weak definition inside the image
                target = next(va for n, ty, _, _, va in self.symbols if n == sym and (ty & N_TYPE) == N_SECT)
            self.memory[addr:addr + 4] = ((target + addend) & 0xFFFFFFFF).to_bytes(4, "little")
            self.bound[addr] = name

        while pos < len(ops):
            b = ops[pos]
            pos += 1
            op, imm = b & 0xF0, b & 0x0F
            if op == 0x00:  # DONE (separates entries in the lazy stream)
                if not lazy:
                    break
            elif op in (0x10, 0x30, 0x50):  # dylib ordinal / special ordinal / type
                pass
            elif op == 0x20:
                uleb()
            elif op == 0x40:  # symbol name
                end = ops.index(b"\0", pos)
                sym = ops[pos:end].decode("latin1")
                pos = end + 1
            elif op == 0x60:
                addend = sleb()
            elif op == 0x70:
                addr = self.all_segments[imm][0] + uleb()
            elif op == 0x80:
                addr = (addr + uleb()) & 0xFFFFFFFF
            elif op == 0x90:
                bind()
                addr += 4
            elif op == 0xA0:
                bind()
                addr = (addr + 4 + uleb()) & 0xFFFFFFFF
            elif op == 0xB0:
                bind()
                addr += 4 + 4 * imm
            elif op == 0xC0:
                count, skip = uleb(), uleb()
                for _ in range(count):
                    bind()
                    addr += 4 + skip
            else:
                raise ValueError(f"unknown bind opcode {b:#x}")

    def _stub_pointer(self, at: int, step: int) -> int:
        """Pointer slot a symbol stub jumps through. armv6 4-byte stub: `ldr pc, [pc, #imm]`."""
        w = int.from_bytes(self.memory[at:at + 4], "little")
        if step == 4 and (w & 0xFFFFF000) == 0xE59FF000:
            return at + 8 + (w & 0xFFF)
        if step == 4 and (w & 0xFFFFF000) == 0xE51FF000:
            return at + 8 - (w & 0xFFF)
        raise ValueError(f"unexpected symbol stub at {at:#x}: {w:#010x}")

    def section(self, seg: str, name: str) -> Section | None:
        return next((s for s in self.sections if s.segment == seg and s.name == name), None)

    @property
    def writable(self):
        return [(a, b) for a, b, prot, *_ in self.segments if prot & 2]

    def u32(self, a: int) -> int:
        return int.from_bytes(self.memory[a:a + 4], "little")

    def in_text(self, a: int) -> bool:
        return self.text.addr <= a < self.text.addr + self.text.size

    def code(self, f: Function) -> bytes:
        return bytes(self.memory[f.address:f.address + f.size])


# ---- function discovery ----------------------------------------------------------------------------------------
def _is(i, *names):
    return i.insn_name() in names


def _uncond(i):
    return i.cc in (A.ARM_CC_AL, A.ARM_CC_INVALID)


def _writes_pc(md, i) -> bool:
    ops = i.operands
    name = i.insn_name()
    if name in ("pop", "ldm", "ldmib", "ldmda", "ldmdb"):
        return any(o.type == A.ARM_OP_REG and md.reg_name(o.reg) == "pc" for o in ops)
    if name == "bx":
        return True
    return bool(ops) and ops[0].type == A.ARM_OP_REG and md.reg_name(ops[0].reg) == "pc" and name not in (
        "str", "strb", "strh", "stm", "push", "cmp", "cmn", "tst", "teq")


class _Descent:
    def __init__(self, image: Image):
        self.image = image
        self.md = {False: Cs(CS_ARCH_ARM, CS_MODE_ARM), True: Cs(CS_ARCH_ARM, CS_MODE_THUMB)}
        for md in self.md.values():
            md.detail = True
        self.cache = {}

    def decode(self, a: int, thumb: bool):
        key = (a, thumb)
        if key not in self.cache:
            n = 4
            got = next(self.md[thumb].disasm(bytes(self.image.memory[a:a + n]), a, 1), None)
            self.cache[key] = got
        return self.cache[key]

    def walk(self, start: int, thumb: bool):
        """Instructions reachable from start without calls: (reached {address: size}, calls {(target, thumb)},
        literal words read with PC-relative loads, ok). Calls and tail branches are followed by the caller."""
        img, md = self.image, self.md[thumb]
        reached, calls, literals = {}, set(), set()
        todo = [start]
        while todo:
            pc = todo.pop()
            while img.in_text(pc) and pc not in reached:
                i = self.decode(pc, thumb)
                if i is None:
                    return reached, calls, literals, False
                reached[pc] = i.size
                name, ops, nxt = i.insn_name(), i.operands, pc + i.size
                # PC-relative literal loads: the loaded word is data, and may be a function pointer
                if name in ("ldr", "vldr") and len(ops) > 1 and ops[1].type == A.ARM_OP_MEM \
                        and md.reg_name(ops[1].mem.base) == "pc" and not ops[1].mem.index:
                    base = (pc + (4 if thumb else 8)) & ~3
                    lit = base + ops[1].mem.disp
                    literals.add(lit)
                    if name == "vldr" and md.reg_name(ops[0].reg).startswith("d"):
                        literals.add(lit + 4)
                if name in ("bl", "blx") and ops and ops[0].type == A.ARM_OP_IMM:
                    t = ops[0].imm & 0xFFFFFFFF
                    calls.add((t & ~1, (not thumb) if name == "blx" else thumb))
                    pc = nxt
                    continue
                if name == "b" or (name in ("cbz", "cbnz")):
                    t = ops[-1].imm & 0xFFFFFFFF
                    if t < start and not thumb:  # backwards out of the function: a tail call (static initializer helpers)
                        calls.add((t, thumb))
                    else:
                        todo.append(t)
                    if name == "b" and _uncond(i):
                        break
                    pc = nxt
                    continue
                if _writes_pc(md, i):
                    for t in self.table(i, thumb, reached):
                        todo.append(t)
                    # `mov lr, pc` then a write to PC is an indirect call (GCC 4.x): execution continues after it
                    prev = self.decode(pc - 4, False) if not thumb and pc - 4 in reached else None
                    is_call = prev is not None and prev.insn_name() == "mov" and len(prev.operands) == 2 \
                        and md.reg_name(prev.operands[0].reg) == "lr" and prev.operands[1].type == A.ARM_OP_REG \
                        and md.reg_name(prev.operands[1].reg) == "pc"
                    if _uncond(i) and not is_call:
                        break
                pc = nxt
        return reached, calls, literals, True

    def table(self, i, thumb, reached):
        """Targets of an ARM jump table at i: `add pc, pc, rX, lsl #2` + a row of B, or `ldr pc, [pc, rX, lsl #2]`
        + absolute addresses."""
        if thumb:
            return []
        img, md, ops, name = self.image, self.md[False], i.operands, i.insn_name()
        out = []
        if name == "add" and len(ops) == 3 and ops[1].type == A.ARM_OP_REG and md.reg_name(ops[1].reg) == "pc":
            t = i.address + 8
            out.append(i.address + 4)
            while img.in_text(t) and (img.u32(t) >> 24) == 0xEA:
                out.append(t)
                t += 4
        elif name == "ldr" and len(ops) > 1 and ops[1].type == A.ARM_OP_MEM \
                and md.reg_name(ops[1].mem.base) == "pc" and ops[1].mem.index:
            t = i.address + 8
            # a conditional ldr is followed by the default-case branch, then the table
            if not _uncond(i):
                out.append(i.address + 4)
            while True:
                v = img.u32(t)
                if not img.in_text(v) or v & 3:
                    break
                out.append(v)
                reached[t] = 0  # table word: data, but part of the function
                t += 4
        return out


def _data_pointers(image: Image):
    """Words in the writable segments and in the read-only data sections that point into __text."""
    out = set()
    ranges = list(image.writable)
    for s in image.sections:
        if s.segment == "__TEXT" and s.name in ("__const", "__constructor", "__destructor"):
            ranges.append((s.addr, s.addr + s.size))
    for lo, hi in ranges:
        for a in range(lo & ~3, hi, 4):
            v = image.u32(a)
            if image.in_text(v & ~1) and not (v & 2):
                out.add((v & ~1, bool(v & 1)))
    return out


def discover(image: Image) -> list:
    d = _Descent(image)
    seeds = {}  # address -> (thumb, name, trusted)
    for name, ty, sect, desc, va in image.symbols:
        if (ty & N_TYPE) == N_SECT and image.in_text(va):
            seeds[va & ~1] = (bool(desc & N_ARM_THUMB_DEF) or bool(va & 1), name.lstrip("_") or name, True)
    if image.entry is not None:
        seeds.setdefault(image.entry & ~1, (bool(image.entry & 1), "start", True))
    init = image.section("__DATA", "__mod_init_func")
    if init:
        for a in range(init.addr, init.addr + init.size, 4):
            v = image.u32(a)
            seeds.setdefault(v & ~1, (bool(v & 1), f"init_{v & ~1:x}", True))
    weak = _data_pointers(image)

    funcs = {}  # address -> (thumb, name, reached)
    literals = set()
    work = [(a, t, n, True) for a, (t, n, _) in seeds.items()] + [(a, t, f"sub_{a:x}", False) for a, t in weak]
    rejected = 0
    while work:
        a, thumb, name, trusted = work.pop()
        if a in funcs or not image.in_text(a) or (thumb is False and a & 3):
            continue
        if not trusted and not thumb:  # compiled ARM functions start unconditionally
            first = d.decode(a, False)
            if first is None or not _uncond(first):
                rejected += 1
                continue
        reached, calls, lits, ok = d.walk(a, thumb)
        if not ok and not trusted:
            rejected += 1
            continue
        funcs[a] = (thumb, name, reached)
        literals |= lits
        for t, th in calls:
            work.append((t, th, f"sub_{t:x}", True))
        # literal words that point into __text: function pointers passed as arguments
        for lit in lits:
            if image.in_text(lit):
                v = image.u32(lit)
                if image.in_text(v & ~1) and not v & 2:
                    work.append((v & ~1, bool(v & 1), f"sub_{v & ~1:x}", False))
    # a weak seed that lands in the middle of a code word reached in the other mode or inside a literal is noise
    code_at = {}
    for a, (thumb, _, reached) in funcs.items():
        for pc, n in reached.items():
            code_at.setdefault(pc, thumb)
    for a in list(funcs):
        thumb, name, _ = funcs[a]
        if name.startswith("sub_") and (a in literals or code_at.get(a, thumb) != thumb):
            del funcs[a]
            rejected += 1

    # entries: branches into another function's range make the target an entry of its own
    starts = sorted(funcs)
    text_end = image.text.addr + image.text.size
    reached_all = {}
    for a, (thumb, _, reached) in funcs.items():
        for pc, n in reached.items():
            reached_all.setdefault(pc, n)

    out = []
    for k, a in enumerate(starts):
        thumb, name, _ = funcs[a]
        end = starts[k + 1] if k + 1 < len(starts) else text_end
        step = 2 if thumb else 4
        data, run = [], None
        pc = a
        while pc < end:
            n = reached_all.get(pc)
            if n:  # an instruction
                if run is not None:
                    data.append((run, pc))
                    run = None
                pc += n
            else:
                if run is None:
                    run = pc
                pc += step
        if run is not None:
            data.append((run, end))
        out.append(Function(a, end - a, name, data, thumb))
    image.discovery = {"functions": len(out), "thumb": sum(f.thumb for f in out), "rejected_weak_seeds": rejected,
                       "symbols": sum(1 for v in seeds.values() if v[2]), "data_pointer_seeds": len(weak)}
    return out
