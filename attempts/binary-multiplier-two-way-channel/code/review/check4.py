# Reviewer check (2026-11-27, Claim 5): the Lagrangian dual D(lam, t0) at the printed rounded
# (lam, t0) = (0.2906, 0.6635), grid max plus local refinement of the inner max.
# Run: python3 check4.py
# Runtime: about 1 s. Needs numpy, scipy.
# Reviewer's own evaluation of the Lagrangian dual D(lam,t0) at the author's (lam,t0), with
# continuous local refinement of the inner max over (alpha,beta) from the best grid points.
import numpy as np
from scipy.optimize import minimize


def h(x):
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    m = (x > 0) & (x < 1)
    xm = x[m]
    out[m] = -xm * np.log2(xm) - (1 - xm) * np.log2(1 - xm)
    return out


def p_hw(a, b):
    d = (1 - a) * b + a * (1 - b)
    return np.where(d > 0, a * (1 - b) / np.where(d > 0, d, 1), 0.0)


def F(a, b, lam, t0):
    p = p_hw(a, b)
    r1 = b * h(a) + (1 - b) * (h((1 - a) * (1 - p)) - (1 - a) * h(p))
    r2 = a * h(b) + (1 - a) * (h((1 - b) * p) - (1 - b) * h(p))
    c1, c2 = -np.log2(1 - t0), np.log2((1 - t0) / t0)
    L = c1 * (a + b) / 2 + c2 * a * b
    return lam * (r1 + r2) / 2 + (1 - lam) * L


for lam, t0 in [(0.2906, 0.6635)]:
    g = np.linspace(0, 1, 2001)
    A, B = np.meshgrid(g, g, indexing="ij")
    V = F(A, B, lam, t0)
    gm = V.max()
    idx = np.argsort(V.ravel())[-40:]
    best = gm
    for i in idx:
        a0, b0 = A.ravel()[i], B.ravel()[i]
        r = minimize(lambda z: -float(F(np.array([np.clip(z[0], 0, 1)]), np.array([np.clip(z[1], 0, 1)]), lam, t0)[0]),
                     [a0, b0], method="Nelder-Mead", options={"xatol": 1e-12, "fatol": 1e-15})
        best = max(best, -r.fun)
    print(f"lam={lam}, t0={t0}: grid max {gm:.8f}, refined max {best:.8f}")
