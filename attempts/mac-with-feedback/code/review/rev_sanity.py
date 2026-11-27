# Reviewer sanity checks (2026-11-27, items 5 and 8): closed-form psi vs ../cert_cl1.py psi_float,
# multi-start k = 1 CL optimisation with |U| <= 5, and 2*10^5 random CL laws (seed 1); log rev_sanity.log.
# Run: python3 rev_sanity.py   (imports the author's ../cert_cl1.py)
# Runtime: about 90 s. Needs numpy, scipy, mpmath.
"""Reviewer sanity checks: (1) closed form psi vs author's psi_float; (2) independent k=1 CL
sum-rate optimisation for W_{1/2} (multi-start, |U| = 2..5); (3) random CL distributions never
exceed UB1 (weak duality sanity)."""
import os
import sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))  # author's code dir (read-only use of psi_float)
from cert_cl1 import psi_float

W = np.zeros((2, 2, 2))
for x1 in range(2):
    for x2 in range(2):
        W[x1, x2] = [1 - (x1 + x2) / 2, (x1 + x2) / 2]

def h(x):
    x = np.clip(x, 0, 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        return np.nan_to_num(-x * np.log2(x)) + np.nan_to_num(-(1 - x) * np.log2(1 - x))
g = lambda s: h(s / 2) - s
psi = lambda a, b: b * g(1 - a) + (1 - b) * g(a) + a * g(1 - b) + (1 - a) * g(b)
rng = np.random.default_rng(1)
A, B = rng.random(10000), rng.random(10000)
print("max |closed form - psi_float| =", np.max(np.abs(psi(A, B) - psi_float(W, A, B))))

def H(p):
    p = p[p > 0]; return -(p * np.log2(p)).sum()

def quantities(pu, a, b):
    # a[u] = P(X1=0|u), b[u] = P(X2=0|u)
    Asum = float(np.sum(pu * psi(a, b)))
    pbar = np.zeros(4)
    for u in range(len(pu)):
        pbar += pu[u] * np.outer([a[u], 1 - a[u]], [b[u], 1 - b[u]]).ravel()
    py = pbar @ W.reshape(4, 2)
    Bv = H(py) - sum(pbar[i] * H(W.reshape(4, 2)[i]) for i in range(4))
    return Asum, Bv

def neg(z, nu):
    pu = np.exp(z[:nu] - z[:nu].max()); pu /= pu.sum()
    a = 1 / (1 + np.exp(-z[nu:2 * nu])); b = 1 / (1 + np.exp(-z[2 * nu:]))
    Asum, Bv = quantities(pu, a, b)
    return -min(Asum, Bv)

best = 0
for nu in (1, 2, 3, 4, 5):
    for s in range(30):
        z0 = rng.normal(scale=2, size=3 * nu)
        res = minimize(neg, z0, args=(nu,), method="Nelder-Mead",
                       options=dict(maxiter=40000, xatol=1e-10, fatol=1e-13))
        best = max(best, -res.fun)
    print(f"|U|<={nu}: best k=1 sum-rate found so far {best:.8f}")

UB1 = 0.578949078927
mx = 0
for _ in range(200000):
    nu = rng.integers(1, 6)
    pu = rng.dirichlet(np.ones(nu)); a = rng.random(nu); b = rng.random(nu)
    mx = max(mx, min(*quantities(pu, a, b)))
print(f"random CL distributions: max min(A,B) = {mx:.6f} (UB1 = {UB1})")
