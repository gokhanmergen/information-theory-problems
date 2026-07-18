#!/usr/bin/env python3
"""El Gamal-Gohari-Nair strengthened cutset bound (arXiv:2101.11139, Prop. 1)
evaluated on the BSC primitive relay channel.

Bound: C <= max over p(x), p(v|x,z), |V| <= |X||Z|+1 = 5, of
    min{ I(X;Y,V) - I(V;X|Z),  I(X;Y) + C0 - I(V;Z|X) }
(second term uses I(V;Z|X,Y) = I(V;Z|X), since (V,Z) independent of Y given X).
Compress-forward is the same expression restricted to p(v|z) — Remark 9 of the
paper — so the search space strictly contains CF's.

CAUTION: the bound is a MAX over auxiliaries, so any numerically found optimum
is a LOWER ESTIMATE of the bound's true value. Confidence in global optimality
comes from many random restarts (reported). Requires scipy (Nelder-Mead).

Usage: python3 egn_bound.py <d1> <d2> <R0> [restarts]
"""
import math
import sys

import numpy as np
from scipy.optimize import minimize

NV = 5


def entropy(p):
    p = p[p > 1e-15]
    return float(-(p * np.log2(p)).sum())


def build_joint(d1, d2, px1, cond_v):
    """p[x,z,y,v] from P(X=1)=px1 and p(v|x,z) as a (2,2,NV) array."""
    p = np.zeros((2, 2, 2, NV))
    for x in (0, 1):
        pxv = px1 if x else 1 - px1
        for z in (0, 1):
            pz = d1 if z != x else 1 - d1
            for y in (0, 1):
                py = d2 if y != x else 1 - d2
                p[x, z, y, :] = pxv * pz * py * cond_v[x, z, :]
    return p


def objective_terms(p, r0):
    pxy = p.sum(axis=(1, 3))          # (x,y)
    pxyv = p.sum(axis=1)              # (x,y,v)
    pxz = p.sum(axis=(2, 3))          # (x,z)
    pxzv = p.sum(axis=2)              # (x,z,v)
    px = pxy.sum(axis=1)
    # I(X;Y,V)
    ixyv = entropy(px) + entropy(pxyv.sum(axis=0).ravel()) - entropy(pxyv.ravel())
    # I(V;X|Z) = H(X|Z) - H(X|Z,V)
    ivx_z = (entropy(pxz.ravel()) - entropy(pxz.sum(axis=0))) \
        - (entropy(pxzv.ravel()) - entropy(pxzv.sum(axis=0).ravel()))
    # I(V;Z|X) = H(Z|X) - H(Z|X,V)
    ivz_x = (entropy(pxz.ravel()) - entropy(px)) \
        - (entropy(pxzv.ravel()) - entropy(pxzv.sum(axis=1).ravel()))
    ixy = entropy(px) + entropy(pxy.sum(axis=0)) - entropy(pxy.ravel())
    return ixyv - ivx_z, ixy + r0 - ivz_x


def bound_estimate(d1, d2, r0, restarts=200, seed=0):
    rng = np.random.default_rng(seed)

    def neg_min(theta):
        px1 = 1 / (1 + math.exp(-theta[0]))
        logits = theta[1:].reshape(2, 2, NV)
        cond_v = np.exp(logits - logits.max(axis=2, keepdims=True))
        cond_v /= cond_v.sum(axis=2, keepdims=True)
        p = build_joint(d1, d2, px1, cond_v)
        a, b = objective_terms(p, r0)
        return -min(a, b)

    vals, best, best_theta = [], -1.0, None
    for k in range(restarts):
        theta0 = np.concatenate([[0.0], rng.normal(0, 3, 2 * 2 * NV)])
        res = minimize(neg_min, theta0, method="Nelder-Mead",
                       options={"maxiter": 20000, "xatol": 1e-9, "fatol": 1e-12})
        vals.append(-res.fun)
        if -res.fun > best:
            best, best_theta = -res.fun, res.x
    near = sum(1 for v in vals if v > best - 1e-4)
    return best, best_theta, near


if __name__ == "__main__":
    d1, d2, r0 = (float(a) for a in sys.argv[1:4])
    restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    val, theta, near = bound_estimate(d1, d2, r0, restarts)
    print(f"d1={d1} d2={d2} R0={r0} restarts={restarts}: "
          f"EGN bound estimate (lower estimate of the bound) = {val:.6f}  "
          f"[P(X=1)={1/(1+math.exp(-theta[0])):.4f}, "
          f"{near}/{restarts} restarts within 1e-4 of best]")
