# Reviewer check (2026-11-27, Claim 7): lower estimates of the EGN Thm 6 bound B(R0) at rho = 0.1 from
# two-point mixtures of arbitrary cube points (differential evolution, seed 11; pieces at 50 digits).
# Run: python3 egn_check.py   (output in egn_check.out)
# Runtime: about 1 min. Needs numpy, scipy, mpmath.
"""Independent lower estimate of the EGN Theorem 6 bound B(R0) at rho=0.1 (Claim 7).
B(R0) = min_{lam in [0,1]} [1 - 2h(rho) + lam R0 + Env g_lam (rho)].
Lower bound Env g_lam(rho) >= w f_lam(P) + (1-w) f_lam(P') with w c(P) + (1-w) c(P') = rho,
for two arbitrary cube points P, P' (generalises the author's (P, symmetric point) pairs).
Each pair gives an affine function of lam; min over lam of max of finitely many affine
functions is computed at all breakpoints, pieces evaluated in mpmath (50 digits)."""
import numpy as np
from itertools import combinations
from scipy.optimize import minimize, differential_evolution
from mpmath import mp, mpf, log
mp.dps = 50
rho = 0.1


def hf(q):
    q = np.clip(q, 1e-15, 1 - 1e-15)
    return -(q * np.log2(q) + (1 - q) * np.log2(1 - q))


def parts(a, u, v):
    y = rho + (1 - 2 * rho) * a
    z = (1 - a) * u + a * (1 - v)
    c = (1 - a) * u + a * v
    return hf(y) - hf(z), (1 - a) * hf(u) + a * hf(v), c


def val(x, lam):
    a, u, v, a2, u2, v2 = x
    D1, E1, c1 = parts(a, u, v)
    D2, E2, c2 = parts(a2, u2, v2)
    if abs(c1 - c2) < 1e-12:
        return -1e3
    w = (rho - c2) / (c1 - c2)
    if not (0 <= w <= 1):
        return -1e3 - abs(w)
    return w * ((1 - lam) * D1 + E1) + (1 - w) * ((1 - lam) * D2 + E2)


def hb(x):
    x = mpf(x)
    if x <= 0 or x >= 1:
        return mpf(0)
    return -(x * log(x, 2) + (1 - x) * log(1 - x, 2))


def piece(x):
    rr = mpf(rho)
    a, u, v, a2, u2, v2 = (mpf(repr(float(q))) for q in x)
    def P(a, u, v):
        y = rr + (1 - 2 * rr) * a
        z = (1 - a) * u + a * (1 - v)
        return hb(y) - hb(z), (1 - a) * hb(u) + a * hb(v), (1 - a) * u + a * v
    D1, E1, c1 = P(a, u, v)
    D2, E2, c2 = P(a2, u2, v2)
    w = (rr - c2) / (c1 - c2)
    assert 0 <= w <= 1
    alpha = w * (D1 + E1) + (1 - w) * (D2 + E2)
    beta = -(w * D1 + (1 - w) * D2)
    return alpha, beta


rng = np.random.default_rng(11)
pieces = [(hb(rho), mpf(0))]
lams = list(np.linspace(0, 0.9, 19)) + list(1 - np.logspace(-1, -3.5, 16))
for lam in lams:
    res = differential_evolution(lambda x: -val(x, lam), [(0, 1)] * 6, seed=int(rng.integers(1e6)),
                                 tol=1e-12, maxiter=3000, polish=True)
    x = np.clip(res.x, 1e-12, 1 - 1e-12)
    try:
        pieces.append(piece(x))
    except AssertionError:
        pass
print(len(pieces), 'pieces')
base = 1 - 2 * hb(rho)
for R0 in ('0.005', '0.01', '0.05', '0.2'):
    R0 = mpf(R0)
    lines = [(base + al, be + R0) for al, be in pieces]
    cand = {mpf(0), mpf(1)}
    for (A1, B1), (A2, B2) in combinations(lines, 2):
        if B1 != B2:
            xx = (A2 - A1) / (B1 - B2)
            if 0 < xx < 1:
                cand.add(xx)
    lower = min(max(A + B * xx for A, B in lines) for xx in cand)
    print('R0', R0, ' B(R0) >=', mp.nstr(lower, 10), ' cutset', mp.nstr(min(1 - hb(rho) + R0, 1 + hb(2 * rho * (1 - rho)) - 2 * hb(rho)), 10))
