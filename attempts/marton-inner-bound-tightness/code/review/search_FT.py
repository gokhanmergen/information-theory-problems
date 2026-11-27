#!/usr/bin/env python3
# Reviewer search (2026-11-27, non-rigorous) for F_T = max G_T: all 81 deterministic maps on a
# step-1/n simplex grid plus polish, the two one-sided branches, and random stochastic-X starts (seed 12345).
# Run: python3 search_FT.py [n [nrand]]   (defaults n = 120, nrand = 600: the run in search_FT_120.out)
# Runtime: about 2.5-4 min. Needs numpy, scipy.
"""Reviewer's independent falsification search for HLL's one-letter dual max F_T (eq. (18)).

G(P_UVX) = -a H(Y) - (1-a) H(Z) + I(U;Y) + I(V;Z) - I(U;V) + sum_x p(x) a_x   (nats)
Target: G(19) = -1.0647134094427738503; HLL certify max G <= G(19) + 5e-7.
Not a proof: grid + local polish. Usage: python -I search_FT.py <grid_n> <n_random>
"""
import itertools
import sys
import time
import numpy as np
from scipy.optimize import minimize

TY = np.array([[0.385361043864, 0.358548005177, 0.256090950959],
               [0.790302113033, 0.091025394735, 0.118672492232],
               [0.113168779849, 0.520687239901, 0.366143980250]])
TZ = np.array([[0.390396602690, 0.207292393713, 0.402311003597],
               [0.293627666338, 0.040944965497, 0.665427368165],
               [0.396880111705, 0.507497881167, 0.095622007128]])
AL = 0.546388044486
AV = np.array([0.0, -0.393210549796, -0.149290191142])
G19 = -1.0647134094427738503


def xlogx(q):
    with np.errstate(divide='ignore', invalid='ignore'):
        return np.where(q > 0, q * np.log(np.where(q > 0, q, 1.0)), 0.0)


def G_general(P):
    """P: (..., nu, nv, 3) joint pmf of (U,V,X)."""
    pUY = np.einsum('...uvx,xy->...uy', P, TY)
    pVZ = np.einsum('...uvx,xz->...vz', P, TZ)
    puv = P.sum(-1)
    py, pz = pUY.sum(-2), pVZ.sum(-2)
    px = P.sum((-3, -2))
    # (1-a)H(Y) + a H(Z) + sum g(p_uy) + sum g(p_vz) + H(UV) + <p,a>
    s = lambda q, ax: xlogx(q).sum(ax)
    return (-(1 - AL) * s(py, -1) - AL * s(pz, -1) + s(pUY, (-2, -1)) + s(pVZ, (-2, -1))
            - s(puv, (-2, -1)) + px @ AV)


def det_P(puv, f):
    """puv: (B,4) over (u,v) in order 00,01,10,11; f: map tuple -> (B,2,2,3)."""
    B = puv.shape[0]
    P = np.zeros((B, 2, 2, 3))
    for i, (u, v) in enumerate([(0, 0), (0, 1), (1, 0), (1, 1)]):
        P[:, u, v, f[i]] = puv[:, i]
    return P


def simplex_grid(k, n):
    pts = [c + (n - sum(c),) for c in itertools.product(range(n + 1), repeat=k - 1) if sum(c) <= n]
    return np.array(pts, float) / n


def polish_det(f, p0):
    def obj(z):
        w = np.exp(z - z.max()); w /= w.sum()
        return -G_general(det_P(w[None, :], f))[0]
    z0 = np.log(np.maximum(p0, 1e-12))
    r = minimize(obj, z0, method='L-BFGS-B', options={'maxiter': 3000, 'ftol': 1e-16, 'gtol': 1e-12})
    r2 = minimize(obj, r.x, method='Nelder-Mead', options={'maxiter': 3000, 'xatol': 1e-12, 'fatol': 1e-17})
    return -min(r.fun, r2.fun)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    nrand = int(sys.argv[2]) if len(sys.argv) > 2 else 600
    t0 = time.time()
    grid = simplex_grid(4, n)
    results = []
    for f in itertools.product(range(3), repeat=4):
        Gv = G_general(det_P(grid, f))
        order = np.argsort(-Gv)
        # polish the best grid point and up to 5 further well-separated candidates
        cands = []
        for i in order[:5000]:
            if all(np.abs(grid[i] - grid[j]).sum() > 0.05 for j in cands):
                cands.append(i)
            if len(cands) >= 10:
                break
        best = max(polish_det(f, grid[i]) for i in cands)
        results.append((best, f, Gv[order[0]]))
    results.sort(reverse=True)
    print("grid n=%d (%d pts/map), time %.0fs" % (n, len(grid), time.time() - t0))
    for b, f, g in results[:6]:
        print("  map %s: polished max G = %.15f  (max - G19 = %+.3e; raw grid best %.9f)" % (f, b, b - G19, g))
    # one-sided superposition branches (U=X,V const), (U const,V=X): over p_X
    g3 = simplex_grid(3, 2000)
    HYx = -xlogx(TY).sum(1); HZx = -xlogx(TZ).sum(1)
    Hs = lambda q: -xlogx(q).sum(-1)
    for name, val in [("U=X,V const", lambda p: -AL * Hs(p @ TY) - (1 - AL) * Hs(p @ TZ) + Hs(p @ TY) - p @ HYx + p @ AV),
                      ("U const,V=X", lambda p: -AL * Hs(p @ TY) - (1 - AL) * Hs(p @ TZ) + Hs(p @ TZ) - p @ HZx + p @ AV)]:
        v = val(g3); i = int(np.argmax(v))
        obj = lambda z: -val((lambda w: w / w.sum())(np.exp(z - z.max())))
        r = minimize(obj, np.log(np.maximum(g3[i], 1e-12)), method='Nelder-Mead', options={'xatol': 1e-13, 'fatol': 1e-17, 'maxiter': 20000})
        print("  %s: max G = %.15f (max - G19 = %+.3e)" % (name, -r.fun, -r.fun - G19))
    # random stochastic-X multistart for (|U|,|V|) in {(2,2),(3,3)}
    rng = np.random.default_rng(12345)
    for (nu, nv, ns) in [(2, 2, nrand), (3, 3, nrand // 3)]:
        bestv = -np.inf
        for s in range(ns):
            th0 = rng.normal(size=nu * nv * 3) * rng.choice([1.0, 3.0, 6.0])
            def obj(th):
                w = np.exp(th - th.max()); w /= w.sum()
                return -G_general(w.reshape(1, nu, nv, 3))[0]
            r = minimize(obj, th0, method='L-BFGS-B', options={'maxiter': 4000, 'ftol': 1e-16, 'gtol': 1e-11})
            bestv = max(bestv, -r.fun)
        print("  random stochastic X, |U|=%d |V|=%d, %d starts: best G = %.15f (best - G19 = %+.3e)" % (nu, nv, ns, bestv, bestv - G19))
    # stochastic-X starts seeded at the (19) witness with perturbations (does the stochastic
    # neighbourhood of the witness contain anything higher?)
    f19 = (0, 1, 2, 0)
    P19 = det_P(np.array([[0.013502132210, 0.172563088231, 0.122932075846, 0.691002703713]]), f19)[0]
    bestv = -np.inf
    for s in range(200):
        th0 = np.log(np.maximum(P19, 1e-12)).ravel() + rng.normal(size=12) * 0.5
        obj = lambda th: -G_general((lambda w: (w / w.sum()).reshape(1, 2, 2, 3))(np.exp(th - th.max())))[0]
        r = minimize(obj, th0, method='L-BFGS-B', options={'maxiter': 4000, 'ftol': 1e-16, 'gtol': 1e-11})
        bestv = max(bestv, -r.fun)
    print("  stochastic X seeded near (19), 200 starts: best G = %.15f (best - G19 = %+.3e)" % (bestv, bestv - G19))
    print("total time %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
