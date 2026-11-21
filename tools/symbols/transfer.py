#!/usr/bin/env python3
"""Give the stripped iOS executable function names by matching it to the Android build of the same game.

  py -3 -I tools/symbols/transfer.py --ios NovaHD --android libnova.so [--out recovered/symbols/names.csv]

The binaries differ in ISA (ARM vs Thumb), compiler and version, so code bytes are useless. What survives is structure:
  names      symbols both binaries export (exact, then demangled with `unsigned long` read as `unsigned int`)
  strings    a string literal (or a set of them) referenced by one function on each side
  callgap    in a matched pair the callee sequences are aligned on already-matched callees; the unmatched callees
             between the same two anchors pair up in order
  vtable     matched classes (same _ZTV symbol, or the vtable a matched constructor installs): slot i <-> slot i
  signature  unmatched functions that call the same matched callees in the same order (and use the same strings)
  caller     the only unmatched caller of a matched callee on each side
  consts     the same rare 32-bit constants and no other candidate
Every match is one-to-one; a pair is accepted only when each side's best candidate is the other. Confidence is the
product of the confidence of what it was derived from and a per-method factor. Output columns:
ios_address,name,demangled,confidence,method
"""
from __future__ import annotations

import argparse
import collections
import csv
import glob
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from binaries import load_android, load_ios  # noqa: E402

FACTOR = {"names": 1.0, "names-demangled": 0.95, "strings": 0.9, "string-set": 0.95, "callgap": 0.9, "vtable": 0.9,
          "signature": 0.85, "caller": 0.75, "consts": 0.6, "vote": 0.8, "fingerprint": 0.7}
# imports that exist on one platform only (soft-float helpers, logging, stack protector, ObjC runtime ...)
PLATFORM_ONLY = re.compile(r"^(__aeabi_|__android|__stack_chk|__gnu_|__cxa_(atexit|finalize)|objc_|_objc|__cxa_guard|"
                           r"__dso_handle|__divsi3|__udivsi3|__modsi3|__umodsi3|__fixsfsi|__floatsi|__eabi)")


def norm_import(n: str) -> str:
    n = n.split("$")[0].lstrip("_")
    return {"Znwj": "Znwm", "Znaj": "Znam"}.get(n, n)


def find_cxxfilt():
    for pat in (os.path.expandvars("%LOCALAPPDATA%/Android/Sdk/ndk/*/toolchains/llvm/prebuilt/*/bin/llvm-cxxfilt*"),
                os.path.expanduser("~/Library/Android/sdk/ndk/*/toolchains/llvm/prebuilt/*/bin/llvm-cxxfilt")):
        hits = glob.glob(pat)
        if hits:
            return hits[0]
    for n in ("c++filt", "llvm-cxxfilt"):
        for d in os.environ.get("PATH", "").split(os.pathsep):
            for ext in ("", ".exe"):
                if os.path.exists(os.path.join(d, n + ext)):
                    return os.path.join(d, n + ext)
    return None


def demangle_all(names):
    names = sorted(set(names))
    exe = find_cxxfilt()
    if not exe:
        return {}
    out = {}
    for k in range(0, len(names), 4000):
        chunk = names[k:k + 4000]
        r = subprocess.run([exe], input="\n".join(chunk), capture_output=True, text=True)
        for n, d in zip(chunk, r.stdout.split("\n")):
            out[n] = d
    return out


def dnorm(d: str) -> str:
    return d.replace("unsigned long", "unsigned int")


class Matcher:
    def __init__(self, A, I):
        self.A, self.I = A, I
        self.ai, self.ia, self.info = {}, {}, {}
        shared = ({norm_import(c[1]) for f in A.funcs.values() for c in f.calls if c[0] == "i"} &
                  {norm_import(c[1]) for f in I.funcs.values() for c in f.calls if c[0] == "i"})
        self.shared = {n for n in shared if not PLATFORM_ONLY.match(n)}
        self.callers_a = collections.defaultdict(set)
        self.callers_i = collections.defaultdict(set)
        for f in A.funcs.values():
            for c in f.calls:
                if c[0] == "f" and c[1] != f.addr:
                    self.callers_a[c[1]].add(f.addr)
        for f in I.funcs.values():
            for c in f.calls:
                if c[0] == "f" and c[1] != f.addr:
                    self.callers_i[c[1]].add(f.addr)

    STRICT = {"callgap", "caller", "signature", "vote", "consts", "fingerprint"}

    def sane(self, a, i, method):
        """Size plausibility (ARM vs Thumb code differ by 1.2-2x in instruction count, smoothed for tiny ones)."""
        fa, fi = self.A.funcs.get(a), self.I.funcs.get(i)
        if not fa or not fi:
            return False
        r = (fa.insns + 6) / (fi.insns + 6)
        lo, hi = (0.45, 3.2) if method in self.STRICT else (0.25, 5.0)
        if method == "caller":
            lo, hi = 0.6, 2.2
        if method in self.STRICT and fa.insns > 12 and fi.insns > 12:
            # a function that calls things on one side and nothing on the other is not the same function
            if bool(self.seq_a(fa)) != bool(self.seq_i(fi)):
                return False
        return lo < r < hi

    def add(self, a, i, conf, method):
        if a in self.ai or i in self.ia:
            return False
        self.ai[a], self.ia[i] = i, a
        self.info[a] = (conf, method)
        return True

    def commit(self, props):
        """props: {(a, i): (conf, method)}. Accept pairs that are each other's best (and unrivalled) candidate."""
        by_a, by_i = collections.defaultdict(list), collections.defaultdict(list)
        for (a, i), (c, m) in props.items():
            if a in self.ai or i in self.ia or not self.sane(a, i, m):
                continue
            by_a[a].append((c, i, m))
            by_i[i].append((c, a, m))
        n = collections.Counter()
        for a, cands in by_a.items():
            cands.sort(reverse=True)
            c, i, m = cands[0]
            if len(cands) > 1 and cands[1][0] >= c:
                continue
            rivals = sorted(by_i[i], reverse=True)
            if rivals[0][1] != a or (len(rivals) > 1 and rivals[1][0] >= c):
                continue
            if self.add(a, i, c, m):
                n[m] += 1
        return n

    # identity of a callee, in iOS address space: matched functions and shared imports compare equal across sides
    def seq_a(self, f):
        out = []
        for c in f.calls:
            if c[0] == "i":
                n = norm_import(c[1])
                if n in self.shared:
                    out.append(("i", n))
            else:
                out.append(("f", self.ai[c[1]]) if c[1] in self.ai else ("u", c[1]))
        return out

    def seq_i(self, f):
        out = []
        for c in f.calls:
            if c[0] == "i":
                n = norm_import(c[1])
                if n in self.shared:
                    out.append(("i", n))
            else:
                out.append(("f", c[1]) if c[1] in self.ia else ("v", c[1]))
        return out

    def stage_names(self):
        A, I = self.A, self.I
        an = {}
        for a, n in A.names.items():
            an.setdefault(n, a)
        for i, n in I.names.items():
            if n in an and an[n] in A.funcs and i in I.funcs:
                self.add(an[n], i, 1.0, "names")
        dm = demangle_all([n for n in list(A.names.values()) + list(I.names.values()) if n.startswith("_Z")])
        ga, gi = collections.defaultdict(set), collections.defaultdict(set)
        for a, n in A.names.items():
            if a not in self.ai and n in dm and a in A.funcs:
                ga[dnorm(dm[n])].add(a)
        for i, n in I.names.items():
            if i not in self.ia and n in dm and i in I.funcs:
                gi[dnorm(dm[n])].add(i)
        for d, s in ga.items():
            if len(s) == 1 and len(gi.get(d, ())) == 1:
                self.add(next(iter(s)), next(iter(gi[d])), FACTOR["names-demangled"], "names-demangled")

    def stage_strings(self):
        A, I = self.A, self.I
        sa, si = collections.defaultdict(set), collections.defaultdict(set)
        for f in A.funcs.values():
            for s in f.strings:
                sa[s].add(f.addr)
        for f in I.funcs.values():
            for s in f.strings:
                si[s].add(f.addr)
        props = {}
        ka, ki = collections.defaultdict(list), collections.defaultdict(list)
        for f in A.funcs.values():
            if f.strings and f.addr not in self.ai:
                ka[frozenset(f.strings)].append(f.addr)
        for f in I.funcs.values():
            if f.strings and f.addr not in self.ia:
                ki[frozenset(f.strings)].append(f.addr)
        for k, v in ka.items():
            if len(v) == 1 and len(ki.get(k, ())) == 1:
                props[(v[0], ki[k][0])] = (FACTOR["string-set"] if len(k) > 1 else FACTOR["strings"] * 0.97,
                                           "string-set")
        votes = collections.defaultdict(set)
        for s, fa in sa.items():
            if len(fa) == 1 and len(si.get(s, ())) == 1:
                a, i = next(iter(fa)), next(iter(si[s]))
                if a not in self.ai and i not in self.ia:
                    votes[a].add(i)
        for a, targets in votes.items():
            if len(targets) == 1:
                i = next(iter(targets))
                if (a, i) not in props:
                    props[(a, i)] = (FACTOR["strings"], "strings")
        self.commit(props)

    def gap_pairs(self, fa, fi):
        """Align the callee sequences on matched callees; pair the unmatched ones between the same anchors."""
        sa, si = self.seq_a(fa), self.seq_i(fi)
        if len(sa) > 150 or len(si) > 150:
            return []
        n, m = len(sa), len(si)
        L = [[0] * (m + 1) for _ in range(n + 1)]
        for x in range(n - 1, -1, -1):
            for y in range(m - 1, -1, -1):
                if sa[x] == si[y] and sa[x][0] in ("f", "i"):
                    L[x][y] = L[x + 1][y + 1] + 1
                else:
                    L[x][y] = max(L[x + 1][y], L[x][y + 1])
        x = y = 0
        gx, gy, gaps, anchors = [], [], [], 0
        while x < n and y < m:
            if sa[x] == si[y] and sa[x][0] in ("f", "i"):
                gaps.append((gx, gy))
                gx, gy = [], []
                anchors += 1
                x += 1
                y += 1
            elif L[x + 1][y] >= L[x][y + 1]:
                gx.append(sa[x])
                x += 1
            else:
                gy.append(si[y])
                y += 1
        gaps.append((gx + sa[x:], gy + si[y:]))
        out = []
        for ga, gi in gaps:
            ua = list(dict.fromkeys(c[1] for c in ga if c[0] == "u"))
            ui = list(dict.fromkeys(c[1] for c in gi if c[0] == "v"))
            if ua and len(ua) == len(ui) and len(ua) <= 3 and len(ga) == len(gi):
                out.extend((a, i, len(ua), anchors) for a, i in zip(ua, ui))
        return out

    def stage_callgap(self):
        props = {}
        for a, i in list(self.ai.items()):
            fa, fi = self.A.funcs.get(a), self.I.funcs.get(i)
            if not fa or not fi:
                continue
            pc = self.info[a][0]
            for ca, ci, k, anchors in self.gap_pairs(fa, fi):
                if ca in self.ai or ci in self.ia:
                    continue
                c = pc * FACTOR["callgap"] * (1.0 if k == 1 else 0.9) * (1.0 if anchors else 0.8)
                if props.get((ca, ci), (0,))[0] < c:
                    props[(ca, ci)] = (c, "callgap")
        return self.commit(props)

    def vtable_pairs(self):
        A, I = self.A, self.I
        pairs = {}
        for n, va in A.vtable_names.items():
            vi = I.vtable_names.get(n)
            if vi is None:
                vi = I.vtable_names.get("_" + n)
            if vi is not None:
                pairs[va + 8] = (vi + 8, 0.95)
        for a, i in self.ai.items():
            fa, fi = A.funcs[a], I.funcs[i]
            if fa.vtables and fi.vtables and len(fa.vtables) == len(fi.vtables):
                pairs.setdefault(fa.vtables[-1], (fi.vtables[-1], self.info[a][0] * FACTOR["vtable"]))
        return pairs

    def stage_vtable(self):
        props = {}
        for va, (vi, conf) in self.vtable_pairs().items():
            sa, si = self.A.vtables.get(va, []), self.I.vtables.get(vi, [])
            if not sa or not si:
                continue
            agree = sum(1 for x, y in zip(sa, si) if self.ai.get(x) == y)
            clash = sum(1 for x, y in zip(sa, si)
                        if (x in self.ai and self.ai[x] != y) or (y in self.ia and self.ia[y] != x))
            if len(sa) == len(si):
                if clash > max(1, len(sa) // 4):
                    continue
                c = conf
            else:
                if agree < 1 or clash:
                    continue
                c = conf * 0.8
            for x, y in zip(sa, si):
                if x in self.A.funcs and y in self.I.funcs:
                    props[(x, y)] = (c, "vtable")
        return self.commit(props)

    def stage_signature(self):
        ka, ki = collections.defaultdict(list), collections.defaultdict(list)
        for f in self.A.funcs.values():
            if f.addr not in self.ai:
                seq = tuple(c for c in self.seq_a(f) if c[0] == "f")
                if len(seq) + len(f.strings) >= 2:
                    ka[(seq, tuple(sorted(f.strings)))].append(f.addr)
        for f in self.I.funcs.values():
            if f.addr not in self.ia:
                seq = tuple(c for c in self.seq_i(f) if c[0] == "f")
                if len(seq) + len(f.strings) >= 2:
                    ki[(seq, tuple(sorted(f.strings)))].append(f.addr)
        props = {}
        for k, v in ka.items():
            if len(v) == 1 and len(ki.get(k, ())) == 1:
                props[(v[0], ki[k][0])] = (0.8 * FACTOR["signature"], "signature")
        return self.commit(props)

    def stage_callers(self):
        props = {}
        for a, i in list(self.ai.items()):
            ua = [x for x in self.callers_a.get(a, ()) if x not in self.ai]
            ui = [x for x in self.callers_i.get(i, ()) if x not in self.ia]
            if len(ua) == 1 and len(ui) == 1 and len(self.callers_a[a]) <= 3 and len(self.callers_i[i]) <= 3:
                c = self.info[a][0] * FACTOR["caller"]
                props[(ua[0], ui[0])] = (max(c, props.get((ua[0], ui[0]), (0,))[0]), "caller")
        return self.commit(props)

    def stage_consts(self):
        ca, ci = collections.defaultdict(set), collections.defaultdict(set)
        for f in self.A.funcs.values():
            if f.addr not in self.ai:
                for v in f.consts:
                    ca[v].add(f.addr)
        for f in self.I.funcs.values():
            if f.addr not in self.ia:
                for v in f.consts:
                    ci[v].add(f.addr)
        votes = collections.defaultdict(collections.Counter)
        for v, s in ca.items():
            if len(s) == 1 and len(ci.get(v, ())) == 1:
                votes[next(iter(s))][next(iter(ci[v]))] += 1
        props = {}
        for a, cnt in votes.items():
            (i, n), = cnt.most_common(1)
            if len(cnt) == 1 and (n >= 2 or (len(self.A.funcs[a].consts) <= 3 and len(self.I.funcs[i].consts) <= 3)):
                props[(a, i)] = (FACTOR["consts"] if n >= 2 else FACTOR["consts"] * 0.8, "consts")
        return self.commit(props)

    def stage_vote(self):
        """Candidates from shared evidence (strings, matched callees, constants), scored; accept clear winners."""
        A, I = self.A, self.I
        cnt_sa, cnt_si = collections.Counter(), collections.Counter()
        for f in A.funcs.values():
            cnt_sa.update(f.strings)
        for f in I.funcs.values():
            cnt_si.update(f.strings)
        by_str = collections.defaultdict(list)
        for f in I.funcs.values():
            if f.addr not in self.ia:
                for s in f.strings:
                    by_str[s].append(f.addr)
        cands = collections.defaultdict(set)
        for f in A.funcs.values():
            if f.addr in self.ai:
                continue
            for s in f.strings:
                if len(by_str.get(s, ())) <= 8:
                    cands[f.addr].update(by_str[s])
            for c in f.calls:
                if c[0] == "f" and c[1] in self.ai:
                    ci = self.ai[c[1]]
                    cs = self.callers_i.get(ci, ())
                    if len(cs) <= 25:
                        cands[f.addr].update(y for y in cs if y not in self.ia)
        scored = {}
        for a, ys in cands.items():
            fa = A.funcs[a]
            sa = self.seq_a(fa)
            fset_a = {c for c in sa if c[0] == "f"}
            iset_a = {c for c in sa if c[0] == "i"}
            for y in ys:
                fi = I.funcs[y]
                si = self.seq_i(fi)
                fset_i = {c for c in si if c[0] == "f"}
                iset_i = {c for c in si if c[0] == "i"}
                shared_s = set(fa.strings) & set(fi.strings)
                score = sum(1.0 + 2.0 / (cnt_sa[s] * cnt_si[s]) ** 0.5 for s in shared_s)
                score -= 0.7 * (len(set(fa.strings) - shared_s) + len(set(fi.strings) - shared_s))
                both = fset_a & fset_i
                score += 1.5 * len(both) - 0.7 * len(fset_a ^ fset_i)
                score += 0.2 * min(len(iset_a & iset_i), 4) - 0.1 * min(len(iset_a ^ iset_i), 4)
                score += 1.0 * len(fa.consts & fi.consts)
                if score >= 2.0:
                    scored[(a, y)] = score
        by_a, by_i = collections.defaultdict(list), collections.defaultdict(list)
        for (a, y), sc in scored.items():
            by_a[a].append((sc, y))
            by_i[y].append((sc, a))
        props = {}
        for a, l in by_a.items():
            l.sort(reverse=True)
            sc, y = l[0]
            r = sorted(by_i[y], reverse=True)
            if r[0][1] != a:
                continue
            if (len(l) > 1 and l[1][0] > sc - 1.0) or (len(r) > 1 and r[1][0] > sc - 1.0):
                continue
            props[(a, y)] = (min(0.85, 0.6 + 0.04 * sc), "vote")
        return self.commit(props)

    def stage_fingerprint(self):
        """Structure offsets and small literals (field offsets, vtable slots, flags) survive the recompile."""
        import math
        A, I = self.A, self.I
        df = collections.Counter()
        for f in list(A.funcs.values()) + list(I.funcs.values()):
            df.update(f.nums)
        n_all = len(A.funcs) + len(I.funcs)
        idf = {v: math.log(n_all / c) for v, c in df.items()}
        ua = [f for f in A.funcs.values() if f.addr not in self.ai and len(f.nums) >= 3]
        index = collections.defaultdict(list)
        for f in I.funcs.values():
            if f.addr not in self.ia and len(f.nums) >= 3:
                for v in f.nums:
                    if df[v] <= 60:
                        index[v].append(f.addr)
        norm = {}

        def nrm(f):
            if f.addr not in norm:
                norm[f.addr] = math.sqrt(sum(idf[v] ** 2 for v in f.nums))
            return norm[f.addr]
        scored = {}
        for fa in ua:
            cand = collections.Counter()
            for v in fa.nums:
                if df[v] <= 60:
                    cand.update(index.get(v, ()))
            for y, k in cand.items():
                if k < 3:
                    continue
                fi = I.funcs[y]
                shared = fa.nums & fi.nums
                dot = sum(idf[v] ** 2 for v in shared)
                cos = dot / (nrm(fa) * nrm(fi))
                if cos >= 0.6:
                    scored[(fa.addr, y)] = cos
        by_a, by_i = collections.defaultdict(list), collections.defaultdict(list)
        for (a, y), sc in scored.items():
            by_a[a].append((sc, y))
            by_i[y].append((sc, a))
        props = {}
        for a, l in by_a.items():
            l.sort(reverse=True)
            sc, y = l[0]
            r = sorted(by_i[y], reverse=True)
            if r[0][1] != a:
                continue
            if (len(l) > 1 and l[1][0] > sc - 0.12) or (len(r) > 1 and r[1][0] > sc - 0.12):
                continue
            props[(a, y)] = (min(0.8, 0.45 + 0.4 * sc), "fingerprint")
        return self.commit(props)

    def propagate(self, log, label):
        for rnd in range(40):
            before = len(self.ai)
            tot = collections.Counter()
            for st in (self.stage_callgap, self.stage_vtable, self.stage_signature, self.stage_callers,
                       self.stage_vote):
                tot += st()
            log(f"{label} round {rnd}: +{len(self.ai) - before} {dict(tot)} total {len(self.ai)}")
            if len(self.ai) == before:
                break

    def run(self, log=print):
        self.stage_names()
        log(f"names: {len(self.ai)}")
        self.stage_strings()
        log(f"after strings: {len(self.ai)}")
        self.propagate(log, "propagate")
        self.stage_consts()
        log(f"after consts: {len(self.ai)}")
        self.stage_fingerprint()
        log(f"after fingerprint: {len(self.ai)}")
        self.propagate(log, "propagate2")
        log(f"final: {len(self.ai)}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ios", type=Path, required=True)
    ap.add_argument("--android", type=Path, required=True)
    ap.add_argument("--out", type=Path, default=HERE.parent.parent / "recovered/symbols/names.csv")
    ap.add_argument("--cache", type=Path, default=HERE.parent.parent / "build/symcache")
    ap.add_argument("--min-confidence", type=float, default=0.5)
    args = ap.parse_args()
    A = load_android(args.android, args.cache / "android.pkl")
    I = load_ios(args.ios, args.cache / "ios.pkl")
    print(f"android {len(A.funcs)} functions ({len(A.names)} names), ios {len(I.funcs)} functions "
          f"({len(I.names)} named)")
    m = Matcher(A, I)
    m.run()
    rows = []
    for a, i in m.ai.items():
        c, method = m.info[a]
        if c >= args.min_confidence and i not in I.names:
            rows.append((i, A.names[a], c, method))
    for i, n in I.names.items():
        if i in I.funcs and n:
            rows.append((i, n, 1.0, "macho"))
    rows.sort()
    dm = demangle_all([r[1] for r in rows if r[1].startswith("_Z")])
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["ios_address", "name", "demangled", "confidence", "method"])
        for i, n, c, method in rows:
            w.writerow([f"0x{i:x}", n, dm.get(n, ""), f"{c:.2f}", method])
    print(f"wrote {len(rows)} names to {args.out}")
    for k, v in collections.Counter(r[3] for r in rows).most_common():
        print(f"  {k:16s} {v}")
    print(f"  confidence >= 0.8: {sum(1 for r in rows if r[2] >= 0.8)}")


if __name__ == "__main__":
    main()
