"""
NON-RIGOROUS companion to marton_noW_gap.py (attempt Claim 8).  Nothing labelled
[proved] depends on this file.

For alpha in {2.35, 2.4}: multi-start Nelder-Mead estimate of
    S_alpha = max_{p(u,v), f} I(U;Y1) + alpha I(V;Y2) - I(U;V)
over the 7 orbit representatives f (binary U, V; X = f(U,V) -- sufficient by Claim 2),
and the capacity-side value F_alpha, to compare with GEA's reported 0.1215 / 0.1229 at 2.4.
"""
import sys, numpy as np
from scipy.optimize import minimize
sys.argv = sys.argv[:1]
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import marton_noW_gap as M

def estimate_S(alpha, starts=40, seed=0):
    rng = np.random.default_rng(seed)
    out = {}
    for name, f in M.ORBIT_REPS.items():
        best, arg = -np.inf, None
        obj = lambda z: -M.G_value(np.exp(z)/np.exp(z).sum(), f, alpha)
        for _ in range(starts):
            r = minimize(obj, rng.normal(size=4)*3, method='Nelder-Mead',
                         options=dict(xatol=1e-10, fatol=1e-13, maxiter=4000))
            if -r.fun > best:
                best = -r.fun; w = np.exp(r.x); arg = (w/w.sum()).round(4)
        out[name] = (best, arg)
    return out

if __name__ == '__main__':
    s = np.linspace(0, 1, 1000001)
    IZ = M.h2(0.58 + 0.24*s) - ((1-s)*M.h2(0.58) + s*M.h2(0.82))
    CY, CZ = 1 - float(M.h2(0.3)), float(IZ.max())
    for alpha in (2.35, 2.4):
        F, _ = M.cap_functional(alpha)
        est = estimate_S(alpha)
        S = max(v[0] for v in est.values())
        print(f'alpha={alpha}: F_alpha={F:.7f}, C_Y={CY:.7f}, alpha*C_Z={alpha*CZ:.7f}, '
              f'S_alpha (estimate)={S:.7f}, gap F-S={F-S:.7f}')
        for k, (v, p) in est.items():
            print(f'    {k:6s} max G ~= {v:.7f}  at p(u,v)={p}')
