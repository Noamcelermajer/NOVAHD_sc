#!/usr/bin/env python3
"""Precision check: hide half of the name anchors, run the matcher, and score the matches on the hidden half
(truth: the same demangled name on both sides)."""
import collections
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import transfer  # noqa: E402
from binaries import load_android, load_ios  # noqa: E402

SP = Path(sys.argv[1])
A = load_android(SP / "apk/lib/armeabi/libnova.so", HERE.parent.parent / "build/symcache/android.pkl")
I = load_ios(SP / "ipa/Payload/NovaHD.app/NovaHD", HERE.parent.parent / "build/symcache/ios.pkl")
m = transfer.Matcher(A, I)
m.stage_names()
truth = dict(m.ai)
tinfo = dict(m.info)
hidden = {a for a in truth if (a // 2) % 2 == 0}
for a in hidden:
    i = m.ai.pop(a)
    del m.ia[i]
    del m.info[a]
m.stage_strings()
m.propagate(lambda *x: None, "p")
m.stage_consts()
m.stage_fingerprint()
m.propagate(lambda *x: None, "p")
res = collections.defaultdict(lambda: [0, 0])
for a, i in m.ai.items():
    if a in hidden or truth.get(a) is not None and a not in hidden:
        pass
    if a in hidden:
        meth = m.info[a][1]
        res[meth][0] += 1
        res[meth][1] += truth[a] == i
    elif a in truth:
        pass
print("hidden anchors:", len(hidden), "recovered:", sum(v[0] for v in res.values()))
for k, (n, ok) in res.items():
    print(f"  {k:12s} {n:5d} correct {ok:5d}  {100 * ok / n:.1f}%")
# wrongly matching a hidden anchor to something else, or other truth-known pairs
bad = [(a, i) for a, i in m.ai.items() if a in truth and truth[a] != i]
print("known-name functions matched to a wrong partner:", len(bad), "of", len([a for a in m.ai if a in truth]))
