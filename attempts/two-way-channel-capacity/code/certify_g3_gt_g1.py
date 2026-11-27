#!/usr/bin/env python3
"""Certificate: G_1(BMC) is a strict subset of G_3(BMC) (equal-rate point).

Part A (lower bound on sym(G_3)).  Load the k = 3 optimiser found by
`bmc_gk.py 3 1500 300 2` (bmc_gk_k3_seed2.npz), round it to an exact rational
distribution with denominator 10^9, and evaluate
    R_sym = [H(Y^3|S2) + H(Y^3|S1)] / 6
in mpmath INTERVAL arithmetic (mp.iv, 50 digits).  Every reduced strategy is a genuine
element of CausalStrat 3 Bool Bool (unreachable histories filled with 0), and the
time-shared pair {(p1,p2), (p2,p1)} with Q uniform on 2 values puts (R_sym, R_sym) in
G_3 as defined in lean/InfoTheory/Problems/TwoWayChannelCapacity.lean.

Part B (upper bound on sym(G_1)).  sym(G_1) = max_{x,y} [y h(x) + x h(y)]/2
(time sharing + swapping users; attempt file, Claim 3).  On each cell
[x0,x1] x [y0,y1] of a uniform N x N grid,
    y h(x) + x h(y) <= y1 * max_{[x0,x1]} h + x1 * max_{[y0,y1]} h,
and max of h on an interval is h at the point nearest to 1/2.  h is evaluated with
mpmath interval arithmetic at the (few hundred) distinct grid points needed per axis, so
the bound is rigorous.

Prints both bounds and checks lower(A) > upper(B).
"""
from fractions import Fraction
import numpy as np
import mpmath as mp
from mpmath import iv

iv.dps = 50
mp.mp.dps = 50


def iv_negxlogx(p):
    """-p log2 p for an exact rational p >= 0, as an mpmath interval."""
    if p == 0:
        return iv.mpf(0)
    P = iv.mpf(p.numerator) / iv.mpf(p.denominator)
    return -P * iv.log(P) / iv.log(iv.mpf(2))


def part_A():
    d = np.load("bmc_gk_k3_seed2.npz")
    T = d["T"]
    D = 10 ** 9

    def rationalise(p):
        q = np.floor(np.asarray(p) * D).astype(np.int64)
        q[np.argmax(q)] += D - q.sum()          # exact normalisation
        assert q.min() >= 0 and q.sum() == D
        return [Fraction(int(v), D) for v in q]

    p1, p2 = rationalise(d["p1"]), rationalise(d["p2"])
    n1, n2 = T.shape
    # H(Y|S2) = sum_s2 p2(s2) H(Y | S2=s2) with P(Y=y|s2) = sum_s1 p1(s1)[T=y]
    HY_S2 = iv.mpf(0)
    for s2 in range(n2):
        if p2[s2] == 0:
            continue
        dist = {}
        for s1 in range(n1):
            dist[T[s1, s2]] = dist.get(T[s1, s2], Fraction(0)) + p1[s1]
        Hs = sum((iv_negxlogx(v) for v in dist.values()), iv.mpf(0))
        HY_S2 += iv.mpf(p2[s2].numerator) / iv.mpf(p2[s2].denominator) * Hs
    HY_S1 = iv.mpf(0)
    for s1 in range(n1):
        if p1[s1] == 0:
            continue
        dist = {}
        for s2 in range(n2):
            dist[T[s1, s2]] = dist.get(T[s1, s2], Fraction(0)) + p2[s2]
        Hs = sum((iv_negxlogx(v) for v in dist.values()), iv.mpf(0))
        HY_S1 += iv.mpf(p1[s1].numerator) / iv.mpf(p1[s1].denominator) * Hs
    R = (HY_S2 + HY_S1) / 6
    return R, HY_S2 / 3, HY_S1 / 3


def part_B(N=4000):
    # interval h at grid points j/N, j = 0..N
    hv = []
    two = iv.mpf(2)
    for j in range(N + 1):
        x = iv.mpf(j) / N
        if j == 0 or j == N:
            hv.append(iv.mpf(0))
        else:
            hv.append(-(x * iv.log(x) + (1 - x) * iv.log(1 - x)) / iv.log(two))
    hi = np.array([float(mp.mpf(v.b)) for v in hv])     # upper endpoints (rounded up below)
    hi = np.nextafter(hi, np.inf)
    # max of h on [j/N, (j+1)/N]: endpoint closest to 1/2, or 1 if the cell contains 1/2
    cell_max = np.maximum(hi[:-1], hi[1:])
    half = N // 2
    if N % 2 == 0:
        cell_max[half - 1] = max(cell_max[half - 1], 1.0)
        cell_max[half] = max(cell_max[half], 1.0)
    x1 = (np.arange(N) + 1) / N                          # exact in binary? add margin below
    x1 = np.nextafter(x1, np.inf)
    # bound(i,j) = y1[j]*Hx[i] + x1[i]*Hy[j]; maximise over the grid
    best = 0.0
    for i in range(N):
        b = x1 * cell_max[i] + x1[i] * cell_max
        best = max(best, b.max())
    ub = best / 2
    return np.nextafter(ub * (1 + 1e-12), np.inf)


if __name__ == "__main__":
    R, R1, R2 = part_A()
    print("Part A: rational k=3 product distribution (denominator 1e9)")
    print("  R1 = H(Y^3|S2)/3 in", R1)
    print("  R2 = H(Y^3|S1)/3 in", R2)
    print("  sym rate (time-shared) in", R)
    lowA = float(mp.mpf(R.a))
    ub = part_B()
    print(f"Part B: rigorous upper bound sym(G_1) <= {ub:.6f} (grid 4000x4000)")
    print("certified sym(G_3) > sym(G_1):", lowA > ub, f"(margin {lowA - ub:.6f})")
