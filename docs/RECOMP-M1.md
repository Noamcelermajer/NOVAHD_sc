# Milestone 1: the iOS executable translated and checked

Goal: every function of `NovaHD` (armv6 Mach-O) translated to C and checked against Unicorn running the original,
reusing NOVA3_sc's lifter and differential test.

## What changed relative to NOVA3_sc

| File | Change |
|---|---|
| `tools/recomp/macho.py` (new) | Mach-O loader with the same interface as NOVA3_sc's `image.py`. Loads at link addresses (`IMAGE_BASE = 0`); imports get slots at `0x00f00000`; symbol stubs become the "PLT"; lazy/non-lazy pointers and `LC_DYLD_INFO` bind opcodes are resolved to import slots (or to the weak definition inside the image). Function discovery by recursive descent (see `ASSESSMENT.md`). |
| `tools/recomp/lift.py` | Imports from `macho`; iOS stubs do not set `ip`; `blx #imm` calls Thumb functions; `rev`/`rev16`/`revsh`/`uxtb16`/`uxtab16`; `ThumbLifter` for Thumb-1 (PC + 4, aligned PC for literals and ADR, flags from the S suffix, unrotated immediates, no writeback on single transfers, return addresses with the Thumb bit). `entries` follows Thumb branches too. |
| `tools/recomp/difftest.py` | `--exe`; Thumb functions start in Unicorn with the Thumb bit; the dispatcher ignores the Thumb bit; the translation runs first and the original stops where the translation returned (see below); the host image is restored before every run; imports without a model end a run as "not covered" on both sides. |
| `tools/recomp/models.py` | Darwin additions: `__divsi3`/`__udivsi3`/`__modsi3`/`__umodsi3` (imported from libgcc_s), `bzero`, `__error`, single-precision math, `__tolower`. |
| `tools/recomp/survey.py` (new) | Translates everything and groups the failures. |
| `tools/debug/onerun.py` (new) | Re-runs one test case with the original's path printed. |

## Results

- Discovery: 16,697 functions (402 Thumb) from 667 symbols; 3.52 MB of the 3.75 MB `__text` reached as code.
- Entries (after splitting at branches into other functions): 25,719; **25,689 translate**. The 30 that do not are
  data words that a pointer in the data segment made look like code (`vrhadd`, `ldrsbt`, undecodable words).
  They fault with `RC_FAULT_UNLIFTED` if ever entered, which the runtime will report.
- Differential test, 1,500 random entries x 16 runs (`recovered/recomp/m1/`): **432 pass, 0 fail** (205 leaf, 227
  with calls; 415 ARM, 17 Thumb). 1,068 have too few complete runs from random inputs (mostly invalid memory reads
  and imports without a model: `printf`, `objc_msgSend`, `_Unwind_SjLj_Register`); real coverage comes from
  running the game.
- Mutation checks (the checker checked): see the table below.

| Mutation | Effect |
|---|---|
| `cf = co;` -> `cf = !co;` (wrong carry after add/sub) | 45 of 300 sampled leaf functions fail (155 pass: they use no add/sub carry that reaches the result) |
| `c->vfp.s[` -> `c->vfp.s[1+` (wrong VFP register) | 24 of 300 fail (175 pass: no single-precision register in them, or none that reaches the result) |

## Bugs found on the way

1. **Indirect calls ended functions.** GCC 4.2 calls through a pointer with `mov lr, pc` + `ldr pc, [rX, #n]`.
   Discovery took the write to PC as the end of the function, so everything after the first virtual call was
   marked as data: 2.37 MB of code found instead of 3.52 MB, and the first test run had 12 failures. Discovery
   now continues after such a pair, as the lifter already did.
2. **Returns to a code address.** An entry in the middle of a function, run with random registers, can pop a real
   code address as its return address. The translation returns there; Unicorn went on executing the code at that
   address until it happened to reach the sentinel. The harness now runs the translation first and stops Unicorn at
   the address the translation returned to. A wrong translation still fails: the original does not reach that
   address, or reaches it with other state.
3. **Host memory leaking between runs.** With the translation first, a run that Unicorn then rejects (a write to
   code) left its writes in the host's read-only regions. The host image is now restored before every run.
4. **Missing import models looked like failures.** An import without a model on the host side reported a fault
   after Unicorn had completed. Such runs are now "not covered" on both sides.

## Next

M2, the Objective-C runtime: see `PLAN.md`.
