# N.O.V.A. HD (iOS), recompiled for Android

Gameloft's **N.O.V.A. – Near Orbit Vanguard Alliance HD** (iPad, 1.0.6, iOS 3.2, 2011) shipped as a 32-bit ARM
(armv6) iOS executable. This project translates that executable's machine code into C by static recompilation,
checks the translation against an emulator running the original, and is building a runtime that stands in for
iOS (Objective-C runtime, a small UIKit, OpenGL ES 1.1, OpenAL), so the game runs natively on 64-bit Android
phones and on Windows.

It reuses the method and the translator of [`NOVA3_sc`](https://github.com/Noamcelermajer/NOVA3_sc) (N.O.V.A. 3,
Android). What is new here is the iOS side: a Mach-O loader with function discovery for a stripped executable,
Thumb-1 translation, and the iOS platform layer.

## Status

| Part | State |
|---|---|
| Mach-O loader (`tools/recomp/macho.py`) | done: segments at their link addresses, imports through stubs, lazy/non-lazy pointers and `LC_DYLD_INFO` binds |
| Function discovery | done: 16,697 functions from 667 symbols by recursive descent; 3.52 of 3.75 MB of code reached |
| Lifter (`tools/recomp/lift.py`) | ARM + VFP from NOVA3_sc, plus Thumb-1: 25,689 of 25,719 entries translate (the rest are data mistaken for code) |
| Differential test (`tools/recomp/difftest.py`) | 1,500 sampled entries: 432 pass, 0 fail, the rest not covered by random inputs ([`docs/RECOMP-M1.md`](docs/RECOMP-M1.md)) |
| iOS runtime | not started; see [`docs/PLAN.md`](docs/PLAN.md) |
| Android APK | not started (front end comes from NOVA3_sc) |

See [`docs/ASSESSMENT.md`](docs/ASSESSMENT.md) for the numbers behind these choices.

## Running the tools

You need your own copy of the game (the `.ipa`); neither the executable nor the data is in this repository.
Python 3 with `capstone`, `unicorn` and `ziglang` (`pip install capstone unicorn ziglang`).

```
# unzip the .ipa; the executable is Payload/NovaHD.app/NovaHD
py -3 tools/recomp/survey.py   --exe <NovaHD>                    # what translates and what does not
py -3 tools/recomp/difftest.py --exe <NovaHD> --sample 600 --out recovered/recomp/m1
```

## Rights

The game's code and data belong to Gameloft. This repository holds tools and a runtime, plus analysis data derived
from the binary. Builds contain the game's code and are for your own copy only; do not redistribute them.

Branches: work on feature branches off `development`; never push directly to `main` or `development`.
