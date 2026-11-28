#!/usr/bin/env python3
"""
BSSC: two-letter vs one-letter Marton dual functional.

  mode 'center' : (alpha, a) = (1/2, (0,0)), the dual point that certifies the BSSC Marton sum
                  rate (UB(1/2) = 0.3616428844 bits = one-letter Marton sum rate).  If
                  B_2(1/2,0) = 2 B_1(1/2,0) then the two-letter Marton sum rate of the BSSC equals
                  twice the one-letter one (Claim 3 of the attempt file).  Heavy multistart over
                  all 430 + 430 canonical maps, L-BFGS polish of the 25 best classes per family, report of the
                  best non-product local optimum.
  mode 'scan'   : grid over (alpha, a1) (a0 = 0), lighter multistart; B_2 - 2 B_1 per point.

Usage: python bssc_two_letter.py center [B] [iters] [seed]
       python bssc_two_letter.py scan   [B] [iters] [seed] [alphas a1s]   (comma lists)
"""
import sys
import time
import numpy as np
from ml_core import (bssc, B1, canonical_maps, TwoLetterDual, mirror_ascent, polish,
                     full_x_branches, B2_search)


def center(B, iters, seed):
    TY, TZ = bssc()
    b1, q1, br = B1(TY, TZ, 0.5, [0, 0], return_arg=True)
    target = 2 * b1
    print("B_1(1/2,0) = %.15f at q = %.10f (%s);  2 B_1 = %.15f" % (b1, q1, br, target))
    rng = np.random.default_rng(seed)
    rows = []
    for tag in ("23", "32"):
        nu, nv = (2, 3) if tag == "23" else (3, 2)
        maps = canonical_maps(nu, nv)
        D = TwoLetterDual(TY, TZ, 0.5, [0, 0], maps)
        t = time.time()
        G, P = mirror_ascent(D, B, iters, rng)
        gm = G.max(1)
        # L-BFGS polish (best start) for the 25 best map classes; mirror-ascent value otherwise
        top = set(np.argsort(-gm)[:25].tolist())
        for m in range(len(maps)):
            vbest = gm[m]
            if m in top:
                v, p = polish(D, m, P[m, int(np.argmax(G[m]))])
                vbest = max(vbest, v)
            rows.append((vbest, tag, maps[m].ravel().tolist()))
        print("  maps %s: %d maps x %d starts x %d iters in %.0fs" % (tag, len(maps), B, iters, time.time() - t),
              flush=True)
    fb = full_x_branches(TY, TZ, 0.5, [0, 0], rng, starts=100)
    for k, v in fb.items():
        rows.append((v, k, None))
    rows.sort(key=lambda r: -r[0])
    print("best value found  B_2 >= %.15f   (B_2 - 2B_1 = %.3e)" % (rows[0][0], rows[0][0] - target))
    tol = 1e-10
    attain = [r for r in rows if r[0] > target - tol]
    print("map classes attaining 2B_1 (within 1e-10): %d of %d" % (len(attain), len(rows)))
    non = [r for r in rows if r[0] <= target - tol]
    print("best map classes NOT attaining 2B_1:")
    for r in non[:5]:
        print("   %s f=%s  value - 2B_1 = %.6e" % (r[1], r[2], r[0] - target))
    print("largest value over all map classes - 2B_1 = %.3e" % (rows[0][0] - target))


def scan(B, iters, seed, alphas=(0.1, 0.25, 0.4, 0.5, 0.6, 0.75, 0.9),
         a1s=(-1.0, -0.5, -0.2, 0.0, 0.2, 0.5, 1.0)):
    TY, TZ = bssc()
    rng = np.random.default_rng(seed)
    m23, m32 = canonical_maps(2, 3), canonical_maps(3, 2)
    worst = -np.inf
    print(" alpha     a1       B_1              B_2(found)        B_2-2B_1")
    for al in alphas:
        for a1 in a1s:
            b1 = B1(TY, TZ, al, [0, a1])
            v, arg, info = B2_search(TY, TZ, al, [0, a1], rng, m23, m32, B=B, iters=iters, npolish=4)
            d = v - 2 * b1
            worst = max(worst, d)
            print("%5.2f  %6.2f  %.12f  %.12f  %+.3e" % (al, a1, b1, v, d), flush=True)
    print("max over scan of (B_2 found - 2 B_1) = %.3e" % worst)


if __name__ == "__main__":
    mode = sys.argv[1]
    B = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    if mode == "scan" and len(sys.argv) > 6:
        al = tuple(float(x) for x in sys.argv[5].split(","))
        a1 = tuple(float(x) for x in sys.argv[6].split(","))
        scan(B, iters, seed, al, a1)
    else:
        {"center": center, "scan": scan}[mode](B, iters, seed)
