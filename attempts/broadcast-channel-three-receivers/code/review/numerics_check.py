# Reviewer check (2026-11-27, Claim 2, non-rigorous): multi-start optimisation of S_alpha with
# a general random p(u,v,x), |U| = |V| = 2, 3, at alpha = 2.35 and 2.4 (60 starts, seed 1).
# Run: python3 numerics_check.py   (output in numerics.txt; overflow warnings are harmless)
# Runtime: about 40 s. Needs numpy, scipy.
"""Reviewer numerics (non-rigorous): estimate S_alpha with general (non-deterministic)
p(u,v,x), |U|=|V|=3, to sanity-check Claim 2 and the S_alpha ~ alpha*C_Z claim."""
import numpy as np
from scipy.optimize import minimize
WY1 = np.array([[0.7, 0.3], [0.3, 0.7]])
K = np.array([[0.6, 0.4], [0.0, 1.0]])
WY2 = WY1 @ K
def H(q):
    q = q[q > 1e-300]; return -np.sum(q * np.log2(q))
def G(puvx, alpha):
    # puvx shape (nu, nv, 2)
    puy = np.einsum('uvx,xy->uy', puvx, WY1)
    pvz = np.einsum('uvx,xz->vz', puvx, WY2)
    pu = puvx.sum((1, 2)); pv = puvx.sum((0, 2)); puv = puvx.sum(2)
    py = puy.sum(0); pz = pvz.sum(0)
    IUY = H(pu) + H(py) - H(puy.ravel())
    IVZ = H(pv) + H(pz) - H(pvz.ravel())
    IUV = H(pu) + H(pv) - H(puv.ravel())
    return IUY + alpha * IVZ - IUV
def est(alpha, nu, nv, starts, seed=1):
    rng = np.random.default_rng(seed); best = -1
    n = nu * nv * 2
    for _ in range(starts):
        obj = lambda z: -G((np.exp(z) / np.exp(z).sum()).reshape(nu, nv, 2), alpha)
        r = minimize(obj, rng.normal(size=n) * 3, method='L-BFGS-B')
        r = minimize(obj, r.x, method='Nelder-Mead', options=dict(maxiter=20000, xatol=1e-10, fatol=1e-14))
        best = max(best, -r.fun)
    return best
for alpha in (2.35, 2.4):
    for nu, nv in ((2, 2), (3, 3)):
        print(alpha, (nu, nv), f'{est(alpha, nu, nv, 60):.7f}', flush=True)
