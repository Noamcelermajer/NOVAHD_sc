# M2 verification: the translation re-checked after the Thumb and discovery changes

Re-run of the differential test (original in Unicorn, translation in a host DLL, same memory and registers,
every register, flag, VFP register and writable byte compared) after: the Thumb-1 lifter, the bx-return heuristics
(`rc_is_entry`), inline `__switch32` tables, PIC pointer discovery and the mutually exclusive data/code decisions.

## Numbers

| Pass | Tested | Pass | Fail | No coverage |
|---|---|---|---|---|
| First run, before any change today (3000 random entries x 16 runs, seed 1) | 3000 | 863 | 4 | 2133 |
| Final run, 3000 random entries x 16 runs, seed 1 (`recovered/recomp/m2/`) | 3000 | 1015 (985 ARM, 30 Thumb) | **0** | 1985 |
| All Thumb entries x 16 runs (`recovered/recomp/m2-thumb/`) | 433 (every one) | 244 | **0** | 189 |
| Every entry with an inline `__switch32` site, x 600 runs (`recovered/recomp/m2-switch/`) | 3 (every one) | 2 | **0** | 1 |
| Unmutated leaf control, 300 leaf entries (`recovered/recomp/m2-unmutated/`) | 300 | 281 | 0 | 19 |

"No coverage" means fewer than 4 of the 16 runs completed on both sides (random state hits an invalid read, an
import without a model, a computed jump to a non-entry, and so on). It is not a pass. Of the 1015 passing entries,
457 are leaf functions and 558 make calls.

Discovery after the fix below: 12,059 functions (429 Thumb), 21,230 entries (433 Thumb), all 21,230 translate.
Before the fix: 26,277 entries.

## Mutation checks (the checker checked)

Same two mutations as in `RECOMP-M1.md`, on 300 sampled leaf entries x 16 runs each. These runs use the new
`--picked-only` option (a DLL of only the tested entries), so they compile in a few minutes.

| Mutation | Result | M1 |
|---|---|---|
| `cf = co;` -> `cf = !co;` (wrong carry after add/sub) | **57 of 300 fail** (229 pass, 14 no coverage) | 45 of 300 |
| `c->vfp.s[` -> `c->vfp.s[1+` (wrong VFP register) | **16 of 300 fail** (270 pass, 14 no coverage) | 24 of 300 |
| none (control, same 300 entries) | 0 fail, 281 pass, 19 no coverage | |

The checker detects both. The pass counts under mutation are functions where the mutated statement does not reach
the result or never occurs (no VFP single-precision register in most leaf functions).

## Bugs found

### 1. Real bug: false function starts split loops into mutually recursive C functions (fixed in `macho.py`, `lift.py`)

Four failures in the first run (`sub_493e8`, `sub_4940c`, `sub_b7760`, `sub_b778c`), all "host fault 6" (call depth
limit). Cause: a word in a literal pool or data that looks like a code address (here `0x49418` at `0x378e7c`, and
`0xb778c` at `0x30c16c`) became a weak function seed. Its walk then branches backwards, out of its own range, into the
real function (`bne 0x4940c`): the backwards-branch rule ("a tail call out of the function") made that a second function.
The loop `4940c -> 49418 -> 4940c` became two C functions that call each other: every iteration nests two C frames
(translated code ends a function with `RC_SAVE(); f_next(c, m); RC_TAIL();`, which the compiler cannot turn into a jump
because of the `depth--` after the call). In the test the depth limit fires after 2000 iterations; in the game the
same code would overflow the stack on a long loop, or be slow (a save and a load of all registers per iteration).
The translation was functionally right, so this was found by the depth fault, not by a wrong value.

Fix: in `discover` (`macho.py`), a function found only through a data word or literal (never a symbol, never a call
target of trusted code) whose whole reach lies inside the reach of another, larger function of the same mode is a
label inside that function. It is dropped as a function (`image.inner_labels`; `discovery["inner_labels"]` = 6,690)
and `entries()` (`lift.py`) adds it back as an entry, so a computed jump or call to that address still works, but
the code around it is one function and its loops are `goto`s. Entries 26,277 -> 21,230, thumb unchanged (433). This changes
the translated source of about 5,000 entries: **every runner build recompiles those**, and any cached image built before this
change is stale.

Not verified: that the 6,690 dropped starts include no real function that is only called through a pointer. The
rule keeps them as entries, so a call through the pointer still reaches the right code; what is lost is only the
separate function boundary. No test or game run shows a difference, but I only reasoned about this, I did not
run the game on it.

### 2. Harness artifacts (not translation bugs), handled in `difftest.py`

- `sub_2eca8` run 1 and `sub_1db5ec` run 14: "host fault 4" (computed jump to an address that is no entry).
  - `sub_2eca8`: random state made `ldr pc, [r3, #0x30]` read a jump table word inside `sub_cfb94` (the object's
    "vtable" pointer is the address of that function). The original jumps to the table's label `0xcfeb0`.
  - `sub_1db5ec`: a virtual call through a pointer into the scratch heap (`0x20008f0`); Unicorn executes the random
    bytes there as code and happens to come back, the translation (correctly) refuses to jump into data.
  In both the original is doing something the translation intentionally does not support (computed jumps go to entries
  only). The harness now counts such runs as "dispatch to a non-entry, original continued" (not covered), and only
  when Unicorn completed; when Unicorn itself fails first, the usual reason is counted. 
- Leaf/call classification: every translated block ends with a dead "falls through" call to the next entry, so
  textual detection of calls cannot be used to build a minimal DLL. `--picked-only` adds fault stubs for the
  entries a pick mentions instead.

## Models added (`models.py`)

`printf`, `sprintf`, `snprintf` (shared formatter on both sides: flags, width, precision, `h/hh/l/ll`, `d i u x X o c s p f e g`, doubles in
two argument words, no alignment), `puts`, `_Unwind_SjLj_Register`/`_Unwind_SjLj_Unregister` (no effect on the
compared state), `__cxa_guard_acquire/release/abort`, and every `glXxx` call as returning 0. `objc_msgSend` stays unmodelled.
Effect: leaf entries without coverage in the 3000 sample: 229 -> 26; first run no-coverage 2133 -> 1985. The most frequent remaining
reasons in the final run: Unicorn invalid memory read (9,836 runs), write to write-protected memory (5,244), invalid instruction (5,164),
invalid write (2,746), memset (1,287: the model refuses a write to read-only memory, as the original would fault), memcpy (557),
`objc_msgSend` (556), `std::string` constructors/destructors (`_ZNSsC1ERKSs` 301, `_ZNSsC1EPKcRKSaIcE` 232, `_ZNSsD2Ev` 231), strcmp (232).
Most of those are random pointers that are invalid; they will not be covered by random inputs.

## Harness options added (`difftest.py`)

- `--select thumb|switch` restricts the pool; `--sample 0` tests every entry of the pool.
- `--picked-only` (with `--kind leaf`) builds the DLL of the tested entries only (for mutation runs).
- `tools/debug/onerun.py` prints the tail of the original's path (20,000 instructions) and the host's call trace.

## What remains uncovered

- About 2/3 of random entries have fewer than 4 completed runs. Entries entered with random registers rarely get valid
  object pointers: methods, anything behind `objc_msgSend`, and everything built on `std::string`. Their translation
  is the same lifter as the covered ones; real coverage comes from running the game (the runner passes frames).
- The third `__switch32` function, `sub_2f8740`, never completed a run in 600 (it starts with `strlen` on a random pointer).
  The other two (`sub_2f3fd0`, 502 runs; `sub_2fc2f8`, 12 runs) pass. I did not check that those runs
  reached each case of the table; only the site's translation is tested at all if random `r0` selects it.
- Only 30 of 433 Thumb entries completed in the 3000 sample; the dedicated Thumb pass completes 244 of 433. The other 189 call
  unmodelled imports (`std::string`, sockets, `fopen`, `gethostbyname`) or hit invalid memory. Thumb instruction forms are
  therefore tested only as far as these 244 functions use them.
- Imports are compared through their models, not the real libc/Foundation; the runtime's own implementations are not checked
  here.
- Self-modifying code, `__kuser` helpers and exceptions (SjLj landing pads) are not exercised.
