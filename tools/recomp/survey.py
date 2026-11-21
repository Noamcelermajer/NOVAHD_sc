#!/usr/bin/env python3
"""Translate every function of the executable and count what the lifter cannot handle yet.

  py -3 tools/recomp/survey.py --exe NovaHD [--out recovered/recomp/survey.json]
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from macho import Image  # noqa: E402
from lift import Lifter, Unsupported, entries  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--exe", required=True)
    ap.add_argument("--out")
    args = ap.parse_args()
    image = Image(Path(args.exe))
    ents = entries(image)
    lifter = Lifter(image, ents)
    reasons, examples, ok, sizes = collections.Counter(), {}, {"arm": 0, "thumb": 0}, collections.Counter()
    for a, f in sorted(ents.items()):
        mode = "thumb" if getattr(f, "thumb", False) else "arm"
        try:
            lifter.lift(f)
            ok[mode] += 1
        except Unsupported as e:
            key = re.sub(r"0x[0-9a-f]+", "X", f"{mode}: {e}")
            reasons[key] += 1
            examples.setdefault(key, hex(a))
            sizes[mode] += 1
    summary = {"discovery": image.discovery, "entries": len(ents), "translated": ok, "failed": dict(sizes),
               "reasons": [(k, v, examples[k]) for k, v in reasons.most_common()]}
    print(json.dumps(summary, indent=1))
    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(json.dumps(summary, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
