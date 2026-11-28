#!/usr/bin/env python3
"""
Sanity check of the one-letter reduction used in ml_core.B1 (binary input: the dual functional
is maximised with U = X, V const or U const, V = X; GJNW 2013 Thm 1 / AGN 2019 Thm 3):
brute-force multistart over fully stochastic P_{UVX} with |U| = |V| = 3 must never exceed B1.

Usage: python check_one_letter.py n_channels seed
"""
import sys
import numpy as np
from scipy.optimize import minimize
from ml_core import B1, ent
from random_search import rand_channel


def G(P, TY, TZ, al, a):
    PUY = np.einsum('uvx,xy->uy', P, TY)
    PVZ = np.einsum('uvx,xz->vz', P, TZ)
    return ((1 - al) * ent(PUY.sum(0)) + al * ent(PVZ.sum(0)) - ent(PUY.ravel())
            - ent(PVZ.ravel()) + ent(P.sum(2).ravel()) + P.sum((0, 1)) @ a)


def main():
    n, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = np.random.default_rng(seed)
    worst = -np.inf
    for t in range(n):
        TY, TZ = rand_channel(rng, rng.integers(2, 4)), rand_channel(rng, rng.integers(2, 4))
        al, a = rng.uniform(0.05, 0.95), np.array([0.0, rng.normal()])
        b1 = B1(TY, TZ, al, a)
        best = -np.inf
        for s in range(40):
            f = lambda th: -G((lambda e: e / e.sum())(np.exp(th - th.max())).reshape(3, 3, 2), TY, TZ, al, a)
            r = minimize(f, rng.normal(size=18) * 3, method='L-BFGS-B', options={'maxiter': 5000, 'ftol': 1e-15})
            best = max(best, -r.fun)
        worst = max(worst, best - b1)
        print("channel %3d: brute max - B1 = %+.3e" % (t, best - b1), flush=True)
    print("max over %d channels of (brute - B1) = %+.3e  (must be <= ~1e-9)" % (n, worst))


if __name__ == "__main__":
    main()
