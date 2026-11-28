#!/usr/bin/env python3
"""
Random binary-input BCs: search for dual non-additivity  B_2(alpha,a) > 2 B_1(alpha,a).

For each trial: random marginals TY (2 x kY), TZ (2 x kZ), kY,kZ in {2,3}; rows are Dirichlet
with a random concentration, and with probability 1/3 one entry of a row is zeroed (Z-channel
like / partially deterministic rows, as in the BSSC).  alpha ~ U(0.05, 0.95).
  * with prob. 1/2, a1 ~ N(0, 1)  ('free' dual point);
  * with prob. 1/2, a1 is tuned by bisection so that the two one-letter branches tie,
    max_q psi_Y = max_q psi_Z  ('tied' point: the randomized-time-division regime, which is
    where the BSSC's Marton optimum lives).
Then B_2 is searched (ml_core.B2_search) and B_2 - 2 B_1 recorded.  Any value above 1e-9 is
re-polished and flagged.

Usage: python random_search.py n_trials seed [B] [iters] [tied]  > out.txt
   ('tied' as 5th argument: only tied dual points; trials without a tie are skipped)
Note: the first runs (seeds 11, 12, 21, 22) used a bracket-bisection tie finder that almost always
failed (both branch maxima coincide as a1 -> +-inf), so they are essentially all 'free' points.
"""
import sys
import time
import numpy as np
from ml_core import B1, B2_search, canonical_maps, psi_branches


def rand_channel(rng, k):
    T = np.zeros((2, k))
    c = rng.choice([0.3, 1.0, 3.0])
    for x in range(2):
        r = rng.gamma(c, size=k)
        if rng.random() < 1 / 3:
            r[rng.integers(k)] = 0.0
        if r.sum() == 0:
            r[0] = 1.0
        T[x] = r / r.sum()
    return T


def branch_max(TY, TZ, al, a1):
    qs = np.linspace(0, 1, 20001)
    vY, vZ = psi_branches(qs, TY, TZ, al, [0, a1])
    return vY.max(), vZ.max()


def tie_a1(TY, TZ, al, rng):
    """a1 at which both one-letter branches attain B_1 (an interior sign change of
    max psi_Y - max psi_Z; both maxima coincide trivially as a1 -> +-inf, so scan a grid)."""
    grid = np.linspace(-6, 6, 121)
    d = np.array([np.subtract(*branch_max(TY, TZ, al, g)) for g in grid])
    idx = [i for i in range(len(grid) - 1)
           if np.sign(d[i]) * np.sign(d[i + 1]) < 0 and min(abs(d[i]), abs(d[i + 1])) > 1e-12]
    if not idx:
        return None
    i = idx[rng.integers(len(idx))]
    lo, hi, dlo = grid[i], grid[i + 1], d[i]
    for _ in range(60):
        mid = (lo + hi) / 2
        dm = np.subtract(*branch_max(TY, TZ, al, mid))
        if np.sign(dm) == np.sign(dlo):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


TIED_ONLY = False


def main():
    global TIED_ONLY
    TIED_ONLY = len(sys.argv) > 5 and sys.argv[5] == "tied"
    n = int(sys.argv[1])
    seed = int(sys.argv[2])
    B = int(sys.argv[3]) if len(sys.argv) > 3 else 24
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 1000
    rng = np.random.default_rng(seed)
    m23, m32 = canonical_maps(2, 3), canonical_maps(3, 2)
    worst = -np.inf
    t0 = time.time()
    for t in range(n):
        kY, kZ = rng.integers(2, 4), rng.integers(2, 4)
        TY, TZ = rand_channel(rng, kY), rand_channel(rng, kZ)
        al = rng.uniform(0.05, 0.95)
        kind = "free"
        a1 = rng.normal()
        if TIED_ONLY:      # resample (channel, alpha) until a tied dual point exists
            for _ in range(400):
                a1t = tie_a1(TY, TZ, al, rng)
                if a1t is not None:
                    break
                kY, kZ = rng.integers(2, 4), rng.integers(2, 4)
                TY, TZ = rand_channel(rng, kY), rand_channel(rng, kZ)
                al = rng.uniform(0.05, 0.95)
            if a1t is not None:
                a1, kind = a1t, "tied"
            else:
                print("trial %4d seed %d: no tie found, skipped" % (t, seed), flush=True)
                continue
        elif rng.random() < 0.5:
            a1t = tie_a1(TY, TZ, al, rng)
            if a1t is not None:
                a1, kind = a1t, "tied"

        b1 = B1(TY, TZ, al, [0, a1])
        v, arg, info = B2_search(TY, TZ, al, [0, a1], rng, m23, m32, B=B, iters=iters, npolish=1)
        d = v - 2 * b1
        worst = max(worst, d)
        flag = "  <== FLAG" if d > 1e-9 else ""
        print("trial %4d seed %d kind %s kY %d kZ %d alpha %.4f a1 %+.6f  B1 %.10f  B2-2B1 %+.3e%s"
              % (t, seed, kind, kY, kZ, al, a1, b1, d, flag), flush=True)
        if flag:
            print("   TY =", TY.tolist(), " TZ =", TZ.tolist())
            print("   witness:", arg)
    print("done %d trials in %.0fs; max(B2 found - 2B1) = %.3e" % (n, time.time() - t0, worst))


if __name__ == "__main__":
    main()
