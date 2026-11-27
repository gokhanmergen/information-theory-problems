# Reviewer check (2026-11-27, Claim 8): Nelder-Mead over general binary J (free gamma) and
# over skew-mirror (G, K), using indep_check's float64 hull evaluator at N = 2*10^4.
# Run: python3 opt_check.py
# Runtime: about 100 s. Needs numpy, scipy, mpmath (importing indep_check first prints its checks 1-2).
import os, sys, numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep_check as ic
T = ic.grid(20000); i = int(np.argmin(abs(T - .5)))
Y, Z = ic.IYn(T), ic.IZn(T)
C = lambda f: ic.hull_vals(T, f)
def FJ_gen(p):
    a0, a1, gam = p
    if not (0 < a0 < 1 and 0 < a1 < 1 and 0 <= gam <= 1): return 1.0
    J = ic.I_Jn(T, a0, a1)
    F = (1 - gam) * Y + gam * Z + C(C(J - Y) + gam * (Y - J)) + C(C(J - Z) + (1 - gam) * (Z - J))
    return F[i]          # value at t=1/2 (min_J at fixed uniform p)
def FJ_gen_max(p):
    a0, a1, gam = p
    if not (0 < a0 < 1 and 0 < a1 < 1 and 0 <= gam <= 1): return 1.0
    J = ic.I_Jn(T, a0, a1)
    F = (1 - gam) * Y + gam * Z + C(C(J - Y) + gam * (Y - J)) + C(C(J - Z) + (1 - gam) * (Z - J))
    return F.max()        # max over t for this fixed J (valid bound without minimax swap)
best = None
for x0 in [(0.81, 0.19, .5), (0.78, 0.17, .45), (0.85, 0.22, .55), (0.9, 0.3, 0.5), (0.7, 0.1, 0.5)]:
    r = minimize(FJ_gen, x0, method='Nelder-Mead', options=dict(xatol=1e-7, fatol=1e-12, maxiter=3000))
    print("J general, F(1/2): start", x0, "->", np.round(r.x, 6), "%.12f" % r.fun)
    if best is None or r.fun < best.fun: best = r
print("same J, max_t F =", "%.12f" % FJ_gen_max(best.x))
def FGK(p):
    g0, g1 = p
    if not (0 < g0 < 1 and 0 < g1 < 1): return 1.0
    G = ic.I_Jn(T, g0, g1); K = ic.I_Jn(T, 1 - g1, 1 - g0)
    F = .5*Y + .5*Z + C(.5*(Y - G) + C(G - Y)) + C(.5*(Z - K) + C(K - Z)) + .5*C(G - K) + .5*C(K - G)
    return F[i]
for x0 in [(0.17, 0.79), (0.2, 0.8), (0.15, 0.75), (0.1, 0.7)]:
    r = minimize(FGK, x0, method='Nelder-Mead', options=dict(xatol=1e-8, fatol=1e-13, maxiter=3000))
    print("GK skew-mirror: start", x0, "->", np.round(r.x, 7), "%.12f" % r.fun)
