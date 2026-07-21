#!/usr/bin/env python3
"""Fertonani-Duman marker-genie lower bounds on deletion-channel capacity with
first-order Markov block inputs.

Extends 2026-07-19-claude-fable-5-finite-n-baseline (code: exact_mi.py).  The
genie bound (baseline Claim 3, = Fertonani-Duman eq. (39) / Cheraghchi-Ribeiro
survey eq. (16)) holds for ANY fixed distribution p on {0,1}^n used i.i.d.
across blocks:

    C(d) >= [ I_p(X^n; Y) - H(Bin(n, 1-d)) ] / n .

Here p = symmetric first-order Markov path measure with flip probability gamma
(stationary start, gamma = 0.5 recovers i.i.d. Bern(1/2)).  I_p(X^n;Y) is
computed EXACTLY (full enumeration, float64) with the same embedding-count DP
as exact_mi.py, but a single pass over inputs x accumulates ALL gammas at once:
the O(n 4^n) DP cost is shared, each extra gamma costs only O(4^n) accumulation,
so a G-point gamma sweep at length n costs ~ (n+G)/n of a single run.

Usage:
    python3 markov_genie.py N g1,g2,...     e.g.  python3 markov_genie.py 14 0.2,0.3,0.5

ds are fixed to [0.05, 0.1, 0.2, 0.3].  Results are merged into
markov_genie_results.json next to this file (key "n=N", per-gamma exact I in
bits, plus the genie bound per d).  Cross-checks (run every time):
  * analyze_multi vs exact_mi.brute_force_I for n in {3,6}, iid and Markov;
  * analyze_multi(gamma=0.5) vs exact_mi.analyze uniform for n=10;
  * H(Bin) against direct formula.
"""

import json
import sys
from math import comb, log2
from pathlib import Path
import time

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from exact_mi import (xlog2x_table, embedding_counts, uniform_weight,
                      markov_weight, brute_force_I, analyze)

DS = [0.05, 0.1, 0.2, 0.3]


def analyze_multi(n, weight_fns, ds):
    """Exact I(X^n;Y) in bits for each (weight_fn, d); one pass over inputs.

    Each weight_fn must be complement-symmetric and sum to 1 over {0,1}^n.
    Returns list (per weight_fn) of {d: I}.
    """
    G = len(weight_fns)
    T = xlog2x_table(comb(n, n // 2) + 1)
    Sw = [[np.zeros(1 << m) for m in range(n + 1)] for _ in range(G)]
    wS2 = np.zeros((G, n + 1))
    half = 1 << (n - 1) if n > 1 else 1
    for x in range(half):
        xbits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
        A = embedding_counts(xbits, n)
        s2 = np.array([T[A[m]].sum() for m in range(n + 1)])
        sym = [A[m] + A[m][::-1] for m in range(n + 1)]
        ws = np.array([wf(x) for wf in weight_fns])
        wS2 += 2.0 * ws[:, None] * s2[None, :]
        for g in range(G):
            w = ws[g]
            Swg = Sw[g]
            for m in range(n + 1):
                Swg[m] += w * sym[m]
    out = []
    for g in range(G):
        for m in range(n + 1):
            s = Sw[g][m].sum()
            assert abs(s - comb(n, m)) < 1e-6 * comb(n, m) + 1e-12, (n, m, g, s)
        T2w = np.array([
            np.sum(np.where(s > 0, s * np.log2(np.where(s > 0, s, 1.0)), 0.0))
            for s in Sw[g]
        ])
        res = {}
        for d in ds:
            c = np.array([d ** (n - m) * (1 - d) ** m for m in range(n + 1)])
            res[d] = float(np.dot(c, wS2[g] - T2w))
        out.append(res)
    return out


def h_binomial(n, p):
    """H(Bin(n, p)) in bits, exact float64 sum."""
    return -sum(
        (lambda q: q * log2(q) if q > 0 else 0.0)(comb(n, k) * p ** k * (1 - p) ** (n - k))
        for k in range(n + 1)
    )


def cross_checks():
    # multi-pass vs brute force, iid and Markov
    for n in (3, 6):
        wfs = [uniform_weight(n), markov_weight(n, 0.25)]
        got = analyze_multi(n, wfs, [0.05, 0.3])
        for wf, res in zip(wfs, got):
            for d, v in res.items():
                bf = brute_force_I(n, d, wf)
                assert abs(v - bf) < 1e-10, (n, d, v, bf)
    # gamma=0.5 Markov == uniform, vs exact_mi.analyze, n=10
    a = analyze_multi(10, [markov_weight(10, 0.5)], DS)[0]
    b = analyze(10, uniform_weight(10), DS)
    for d in DS:
        assert abs(a[d] - b[d]) < 1e-9, (d, a[d], b[d])
    # binomial entropy sanity: H(Bin(1,p)) = h2(p)
    for p in (0.7, 0.9):
        h2 = -p * log2(p) - (1 - p) * log2(1 - p)
        assert abs(h_binomial(1, p) - h2) < 1e-12
    print("cross-checks passed")


def main():
    n = int(sys.argv[1])
    gammas = [float(g) for g in sys.argv[2].split(",")]
    cross_checks()

    t0 = time.time()
    wfs = [markov_weight(n, g) if g != 0.5 else uniform_weight(n) for g in gammas]
    res = analyze_multi(n, wfs, DS)
    dt = time.time() - t0

    hb = {d: h_binomial(n, 1 - d) for d in DS}
    outpath = Path(__file__).parent / "markov_genie_results.json"
    data = json.loads(outpath.read_text()) if outpath.exists() else {}
    key = f"n={n}"
    entry = data.setdefault(key, {"H_bin": {str(d): hb[d] for d in DS},
                                  "I_bits": {}, "genie_bound": {}})
    for g, r in zip(gammas, res):
        entry["I_bits"][str(g)] = {str(d): r[d] for d in DS}
        entry["genie_bound"][str(g)] = {str(d): (r[d] - hb[d]) / n for d in DS}
        print(f"n={n} gamma={g}: " + "  ".join(
            f"d={d}: I/n={r[d]/n:.6f} bound={(r[d]-hb[d])/n:+.6f}" for d in DS))
    entry["timing_sec"] = round(dt, 2)
    outpath.write_text(json.dumps(data, indent=1))
    print(f"({dt:.1f}s)  wrote {outpath}")


if __name__ == "__main__":
    main()
