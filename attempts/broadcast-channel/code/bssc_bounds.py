#!/usr/bin/env python3
"""Marton inner bound vs Nair-El Gamal (UV) outer bound sum rates for the
binary skew-symmetric broadcast channel (BSSC).

Channel: X in {0,1};  p(y1|x) = [[1, 0], [1/2, 1/2]],  p(y2|x) = [[1/2, 1/2], [0, 1]].

Marton sum rate (private messages, X = f(U,V) relaxed to p(x|u,v)):
    max  I(U;Y1) + I(V;Y2) - I(U;V)         over p(u,v) p(x|u,v)
    Known exact value: 0.3616428 bits, achieved by randomized time division
    (Nair-Wang-Geng's information inequality proves RTD optimal for all
    binary-input broadcast channels).

UV outer bound sum rate:
    max  min{ I(U;Y1)+I(V;Y2),
              I(U;Y1)+I(X;Y2|U),
              I(V;Y2)+I(X;Y1|V) }           over p(u,v,x)
    Literature: strictly larger than Marton's sum rate for the BSSC.

CAUTION: both are maxima over auxiliaries. A numerical optimum certifies a
LOWER estimate: for Marton that is a true achievable rate; for the UV bound it
only estimates the bound's value (global optimality by restart evidence).

Usage: python3 bssc_bounds.py [restarts] ; requires numpy + scipy.
"""
import sys

import numpy as np
from scipy.optimize import minimize
from scipy.special import expit

W1 = np.array([[1.0, 0.0], [0.5, 0.5]])   # p(y1|x)
W2 = np.array([[0.5, 0.5], [0.0, 1.0]])   # p(y2|x)


def entropy(p):
    p = p[p > 1e-15]
    return float(-(p * np.log2(p)).sum())


def mi_from_joint(pab):
    return entropy(pab.sum(axis=1)) + entropy(pab.sum(axis=0)) - entropy(pab.ravel())


def softmax(v):
    e = np.exp(v - v.max())
    return e / e.sum()


def marton_sum(theta, nw, nu=2, nv=2):
    """Marton sum rate with common auxiliary W:
        min{I(W;Y1), I(W;Y2)} + sum_w p(w) [I(U;Y1|w) + I(V;Y2|w) - I(U;V|w)]
    from logits: p(w), then per-w p(u,v|w) and p(x=1|u,v,w).
    nw = 1 recovers the W-less form I(U;Y1)+I(V;Y2)-I(U;V)."""
    k = nu * nv
    pw = softmax(theta[:nw])
    inner = 0.0
    pwy1 = np.zeros((nw, 2))
    pwy2 = np.zeros((nw, 2))
    off = nw
    for w in range(nw):
        puv = softmax(theta[off:off + k]).reshape(nu, nv)
        px1 = expit(theta[off + k:off + 2 * k].reshape(nu, nv))
        off += 2 * k
        puvx = np.stack([puv * (1 - px1), puv * px1], axis=2)   # (u,v,x) given w
        puy1 = np.einsum('uvx,xy->uy', puvx, W1)
        pvy2 = np.einsum('uvx,xy->vy', puvx, W2)
        inner += pw[w] * (mi_from_joint(puy1) + mi_from_joint(pvy2)
                          - mi_from_joint(puv))
        px = puvx.sum(axis=(0, 1))
        pwy1[w] = pw[w] * (px @ W1)
        pwy2[w] = pw[w] * (px @ W2)
    return min(mi_from_joint(pwy1), mi_from_joint(pwy2)) + inner


def uv_sum(theta, nu, nv):
    """min of the three sum-rate constraints of the UV outer bound."""
    puvx = softmax(theta).reshape(nu, nv, 2)
    puy1 = np.einsum('uvx,xy->uy', puvx, W1)
    pvy2 = np.einsum('uvx,xy->vy', puvx, W2)
    iuy1, ivy2 = mi_from_joint(puy1), mi_from_joint(pvy2)
    # I(X;Y2|U) and I(X;Y1|V)
    ixy2_u = 0.0
    for u in range(nu):
        pu = puvx[u].sum()
        if pu < 1e-12:
            continue
        pxg = puvx[u].sum(axis=0) / pu                        # p(x|u)
        ixy2_u += pu * mi_from_joint((pxg[:, None] * W2))
    ixy1_v = 0.0
    for v in range(nv):
        pv = puvx[:, v, :].sum()
        if pv < 1e-12:
            continue
        pxg = puvx[:, v, :].sum(axis=0) / pv                  # p(x|v)
        ixy1_v += pv * mi_from_joint((pxg[:, None] * W1))
    return min(iuy1 + ivy2, iuy1 + ixy2_u, ivy2 + ixy1_v)


def maximize(f, nparams, restarts, seed=0):
    rng = np.random.default_rng(seed)
    vals, best, arg = [], -1.0, None
    for _ in range(restarts):
        res = minimize(lambda t: -f(t), rng.normal(0, 3, nparams),
                       method="Nelder-Mead",
                       options={"maxiter": 40000, "xatol": 1e-10, "fatol": 1e-13})
        vals.append(-res.fun)
        if -res.fun > best:
            best, arg = -res.fun, res.x
    near = sum(1 for v in vals if v > best - 1e-5)
    return best, near, arg


if __name__ == "__main__":
    restarts = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    for nw in (1, 2, 3):
        m, near_m, _ = maximize(lambda t: marton_sum(t, nw), nw + nw * 16, restarts)
        print(f"Marton sum rate (|W|={nw}, |U|=|V|=2): {m:.7f} bits "
              f"[{near_m}/{restarts} restarts within 1e-5]  (published: 0.3616428)")
    for nu, nv in ((2, 2), (3, 3)):
        u, near_u, _ = maximize(lambda t: uv_sum(t, nu, nv), nu * nv * 2, restarts)
        print(f"UV outer bound sum rate (|U|=|V|={nu}): {u:.7f} bits "
              f"[{near_u}/{restarts} restarts within 1e-5]")
