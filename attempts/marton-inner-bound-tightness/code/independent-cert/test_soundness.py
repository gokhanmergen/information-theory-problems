#!/usr/bin/env python3
"""Sanity tests for bnb_rigorous.py (not part of the proof; the proof is the soundness argument
in the module docstring).  Checks, on random boxes of many sizes (including boxes touching the
simplex boundary), that box_upper(box) >= G(p) for random points p in box ∩ simplex, with G
evaluated independently by mpmath at 50 digits straight from the entropy formula
  G = -alpha H(Y) - abar H(Z) + I(U;Y) + I(V;Z) - I(U;V) + a.p_X
(not from the h/g decomposition used by the bound).  Also checks the decomposition itself and
G(19) against HLL (18).

Usage: python -I test_soundness.py [n_boxes]
"""
import random
import sys
from fractions import Fraction as Fr

import os
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bnb_rigorous as B
import model as M

mp.mp.dps = 50


def H(ps):
    return -sum(p * mp.log(p) for p in ps if p > 0)


def G_direct(f, P):
    """P: 4 mpf (cells 00,01,10,11), X = f(U,V)."""
    al = mp.mpf(M.ALPHA_S)
    ty = [[mp.mpf(x) for x in r] for r in M.TY_S]
    tz = [[mp.mpf(x) for x in r] for r in M.TZ_S]
    a = [mp.mpf(x) for x in M.AVEC_S]
    cells = [(0, 0), (0, 1), (1, 0), (1, 1)]
    px = [sum(P[i] for i in range(4) if f[i] == x) for x in range(3)]
    pY = [sum(px[x] * ty[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(px[x] * tz[x][z] for x in range(3)) for z in range(3)]
    pu = [P[0] + P[1], P[2] + P[3]]
    pv = [P[0] + P[2], P[1] + P[3]]
    pUY = [sum(P[i] * ty[f[i]][y] for i in range(4) if cells[i][0] == u) for u in range(2) for y in range(3)]
    pVZ = [sum(P[i] * tz[f[i]][z] for i in range(4) if cells[i][1] == v) for v in range(2) for z in range(3)]
    IUY = H(pu) + H(pY) - H(pUY)
    IVZ = H(pv) + H(pZ) - H(pVZ)
    IUV = H(pu) + H(pv) - H(P)
    return -al * H(pY) - (1 - al) * H(pZ) + IUY + IVZ - IUV + sum(a[x] * px[x] for x in range(3))


def G_sup_direct(side, px):
    al = mp.mpf(M.ALPHA_S)
    ty = [[mp.mpf(x) for x in r] for r in M.TY_S]
    tz = [[mp.mpf(x) for x in r] for r in M.TZ_S]
    a = [mp.mpf(x) for x in M.AVEC_S]
    pY = [sum(px[x] * ty[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(px[x] * tz[x][z] for x in range(3)) for z in range(3)]
    if side == "u":   # U = X, V const: I(U;Y) = I(X;Y)
        extra = H(pY) - sum(px[x] * H(ty[x]) for x in range(3))
    else:
        extra = H(pZ) - sum(px[x] * H(tz[x]) for x in range(3))
    return -al * H(pY) - (1 - al) * H(pZ) + extra + sum(a[x] * px[x] for x in range(3))


def rand_box(n, rng):
    ONE = B.ONE
    while True:
        k = rng.choice([1, 2, 4, 8, 16, 30, 45])
        w = ONE >> k
        center = [rng.random() for _ in range(n)]
        s = sum(center)
        center = [c / s for c in center]
        if rng.random() < 0.3:                      # push to the boundary
            center[rng.randrange(n)] = 0.0
            s = sum(center)
            center = [c / s for c in center]
        lo = [max(0, int(c * ONE) - rng.randrange(w + 1)) for c in center]
        hi = [min(ONE, l + w) for l in lo]
        t = B.tighten(lo, hi)
        if t:
            return t


def rand_point(lo, hi, rng):
    """random exact point in box ∩ simplex (rejection on a random corner-ish mix)."""
    ONE = B.ONE
    n = len(lo)
    for _ in range(200):
        p = [lo[i] + int(rng.random() * (hi[i] - lo[i])) for i in range(n)]
        j = rng.randrange(n)
        p[j] = ONE - (sum(p) - p[j])
        if lo[j] <= p[j] <= hi[j]:
            return p
    # fall back to an LP vertex
    p = list(lo)
    cap = ONE - sum(p)
    for i in rng.sample(range(n), n):
        inc = min(hi[i] - p[i], cap)
        p[i] += inc
        cap -= inc
    return p


def main():
    nbox = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(20261127)
    # decomposition check + G(19)
    P19 = [mp.mpf(x) for x in M.P19_S]
    g19 = G_direct(M.F19, P19)
    print("G(19) direct mpmath:", mp.nstr(g19, 30), " (HLL (18): -1.06471340944277385029433493729...)")
    print("G(19) arb (decomposition):", B.g_at_point_lower(M.F19, M.P19))
    worst = mp.mpf(-1)
    nfail = 0
    import itertools
    maps = list(itertools.product(range(3), repeat=4))
    for b in range(nbox):
        if b % 10 == 9:
            side = rng.choice("uv")
            cm = B.Compiled(M.superposition_model(side))
            n = 3
        else:
            f = rng.choice(maps)
            cm = B.Compiled(M.map_model(f))
            n = 4
        lo, hi = rand_box(n, rng)
        ub = mp.mpf(B.box_upper(cm, lo, hi).str(45, radius=False))
        for _ in range(20):
            p = rand_point(lo, hi, rng)
            P = [mp.mpf(x) / mp.mpf(B.ONE) for x in p]
            g = G_direct(f, P) if n == 4 else G_sup_direct(side, P)
            gap = ub - g
            if gap < 0:
                nfail += 1
                print("FAIL", cm.name, lo, hi, p, ub, g)
            worst = min(worst, gap) if worst != -1 else gap
    print("boxes tested:", nbox, "x 20 points; failures:", nfail, "; min(bound - G) =", mp.nstr(worst, 6))


if __name__ == "__main__":
    main()
