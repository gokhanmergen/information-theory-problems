# Reviewer checks (2026-11-27): exact Lean value on W* (sympy), the 3/2 converse pieces (grid, multistart,
# 1200 random codes, seed 3), CEG79 (83a-c) at the Claim-3 points, and the Ponniah BSC instance. Section 4's
# C-CF optimiser is superseded by ccf_opt.py. Run: python3 review_check.py   (output in review_check_out.txt)
# Runtime: about 2-3 min. Needs sympy, numpy, scipy.
"""Independent reviewer checks for attempts/relay-channel/...thm7-transcription-catalog-error.md.

Written from scratch (does not import the author's code).
Variables in dict form: a joint law is a dict {tuple: prob}; entropies computed exactly
with sympy for part 1, floats elsewhere.
"""
import itertools, math, random
from fractions import Fraction as F
import sympy as sp
import numpy as np
from scipy.optimize import minimize

# ---------------------------------------------------------------- helpers
def H_exact(dist):
    """exact entropy (sympy) of dict {key: Fraction}"""
    tot = 0
    for p in dist.values():
        if p > 0:
            tot -= sp.Rational(p.numerator, p.denominator) * sp.log(sp.Rational(p.numerator, p.denominator), 2)
    return tot

def marg(J, idx):
    out = {}
    for k, p in J.items():
        kk = tuple(k[i] for i in idx)
        out[kk] = out.get(kk, 0) + p
    return out

def cmi_exact(J, A, B, C):
    return H_exact(marg(J, A + C)) + H_exact(marg(J, B + C)) - H_exact(marg(J, A + B + C)) - (H_exact(marg(J, C)) if C else 0)

# W*: x=(x1,x2), xr, y=(y1,y2), yr
def Wstar(x, xr):
    x1, x2 = x
    out = {}
    for z in (0, 1):
        y = (x1 ^ z, x2 + xr)
        out[(y, z)] = out.get((y, z), 0) + F(1, 2)
    return out

# ------------------------------------------------- 1. Lean functional, exact
# t = (u, x, xr, y, yr, yh) ; Lean index map:
# r1 = I(U;Yr|Xr) + I(X;(Y,Yh)|(U,Xr)) ; r2 = I((X,Xr);Y) - I(Yr;Yh|(U,X,Xr,Y))
pair = {(0, 0): F(1, 3), (0, 1): F(1, 6), (1, 0): F(1, 6), (1, 1): F(1, 3)}
J = {}
for x1 in (0, 1):
    for (x2, xr), pp in pair.items():
        for (y, yr), w in Wstar((x1, x2), xr).items():
            yh = yr
            J[(0, (x1, x2), xr, y, yr, yh)] = J.get((0, (x1, x2), xr, y, yr, yh), 0) + F(1, 2) * pp * w
assert sum(J.values()) == 1
U, X, XR, Y, YR, YH = range(6)
r1 = cmi_exact(J, [U], [YR], [XR]) + cmi_exact(J, [X], [Y, YH], [U, XR])
r2 = cmi_exact(J, [X, XR], [Y], []) - cmi_exact(J, [YR], [YH], [U, X, XR, Y])
r1s, r2s = sp.nsimplify(sp.simplify(r1)), sp.simplify(r2)
print("1. Lean point on W*: r1 =", sp.simplify(r1), "=", float(r1), "; r2 =", r2s, "=", float(r2))
print("   r2 - log2(3) simplifies to", sp.simplify(r2 - sp.log(3, 2)))

# ---------------------------------- 2. converse constant max H(B1+B2) = 3/2
# (i) 1-D reduction G(t) for t = 2*alpha*beta > 0 (see review note)
def h(p):
    return 0.0 if p <= 0 or p >= 1 else -p * math.log2(p) - (1 - p) * math.log2(1 - p)
ts = np.linspace(1e-9, 0.5, 2_000_001)
G = np.array([0.0])
hv = np.vectorize(h)
Gt = hv(0.5 - ts) + (0.5 + ts) * hv(0.5 + np.sqrt(2 * ts) / (1 + 2 * ts))
print("2. max_t G(t) on (0,1/2] grid =", Gt.max(), " (must be <= 1.5)")
# (ii) direct multi-start optimisation of H(Bern(p)+Bern(q))
def negHS(v):
    p, q = np.clip(v, 0, 1)
    d = [(1 - p) * (1 - q), p * (1 - q) + q * (1 - p), p * q]
    return -sum(-a * math.log2(a) for a in d if a > 0)
best = max(-minimize(negHS, np.random.rand(2), bounds=[(0, 1)] * 2).fun for _ in range(200))
print("   multistart max H(B1+B2) =", best)

# (iii) exact I(M;Y^n) for random codes with strictly causal relay, n=3
def code_MI(n, Mn, rng):
    enc = [[(rng.randrange(2), rng.randrange(2)) for _ in range(n)] for _ in range(Mn)]
    relay = [{zz: rng.randrange(2) for zz in itertools.product((0, 1), repeat=i)} for i in range(n)]
    PY, PMY = {}, {}
    for m in range(Mn):
        for z in itertools.product((0, 1), repeat=n):
            y = tuple((enc[m][i][0] ^ z[i], enc[m][i][1] + relay[i][z[:i]]) for i in range(n))
            p = 1.0 / Mn / 2 ** n
            PY[y] = PY.get(y, 0) + p
            PMY[(m, y)] = PMY.get((m, y), 0) + p
    Hf = lambda d: -sum(v * math.log2(v) for v in d.values() if v > 0)
    return math.log2(Mn) + Hf(PY) - Hf(PMY)
rng = random.Random(3)
worst = max(code_MI(3, Mn, rng) for Mn in (8, 16, 32, 64) for _ in range(300))
print("   max I(M;Y^3) over 1200 random codes (relay strictly causal) =", worst, " bound 4.5")
# structured attempt: x2 fresh bits, relay forwards previous Z
def structured(n):
    Mn = 2 ** (2 * n)
    PY, PMY = {}, {}
    for m in range(Mn):
        bits = [(m >> (2 * i)) & 3 for i in range(n)]
        for z in itertools.product((0, 1), repeat=n):
            y = tuple(((bits[i] >> 1) ^ z[i], (bits[i] & 1) + (z[i - 1] if i > 0 else 0)) for i in range(n))
            p = 1.0 / Mn / 2 ** n
            PY[y] = PY.get(y, 0) + p
            PMY[(m, y)] = PMY.get((m, y), 0) + p
    Hf = lambda d: -sum(v * math.log2(v) for v in d.values() if v > 0)
    return math.log2(Mn) + Hf(PY) - Hf(PMY)
print("   structured (uncoded X, relay forwards Z_{i-1}) I(M;Y^n)/n for n=1..4:",
      [round(structured(n) / n, 6) for n in range(1, 5)])

# ----------------------- 3. ORIGINAL CEG79 Theorem 7 (83a-c) evaluated on W*
# variables (v,u,x,xr,y,yr,yh); p(v)p(u|v)p(x|u)p(xr|v)W p(yh|xr,yr,u)
def Hf_np(d):
    return -sum(v * math.log2(v) for v in d.values() if v > 1e-300)
def cmi_f(J, A, B, C):
    return Hf_np(marg(J, A + C)) + Hf_np(marg(J, B + C)) - Hf_np(marg(J, A + B + C)) - (Hf_np(marg(J, C)) if C else 0)
def thm7_orig(pv, pu_v, px_u, pxr_v, pyh):
    J = {}
    for v, a in pv.items():
        for u, b in pu_v[v].items():
            for x, c in px_u[u].items():
                for xr, d in pxr_v[v].items():
                    for (y, yr), w in Wstar(x, xr).items():
                        for yh, e in pyh(xr, yr, u).items():
                            k = (v, u, x, xr, y, yr, yh)
                            J[k] = J.get(k, 0) + a * b * c * d * float(w) * e
    V_, U_, X_, XR_, Y_, YR_, YH_ = range(7)
    t1 = cmi_f(J, [X_], [Y_, YH_], [XR_, U_]) + cmi_f(J, [U_], [YR_], [XR_, V_])
    t2 = cmi_f(J, [X_, XR_], [Y_], []) - cmi_f(J, [YH_], [YR_], [XR_, X_, U_, Y_])
    lhs = cmi_f(J, [YH_], [YR_], [Y_, XR_, U_])
    rhs = cmi_f(J, [XR_], [Y_], [V_])
    return min(t1, t2), t1, t2, lhs, rhs
unifX = {(a, b): 0.25 for a in (0, 1) for b in (0, 1)}
# author's point V=U=const, Yh=Yr: violates (83c)
r = thm7_orig({0: 1.0}, {0: {0: 1.0}}, {0: unifX}, {0: {0: .5, 1: .5}}, lambda xr, yr, u: {yr: 1.0})
print("3. CEG79 (83) at author's point (Yh=Yr): min=%.6f t1=%.6f t2=%.6f  constraint %.6f <= %.6f ?" % r)
# repaired point: Yh = Yr xor Bern(delta), h(delta)=1/2
lo, hi = 0.0, 0.5
for _ in range(200):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if h(mid) < 0.5 else (lo, mid)
dl = (lo + hi) / 2
r = thm7_orig({0: 1.0}, {0: {0: 1.0}}, {0: unifX}, {0: {0: .5, 1: .5}},
              lambda xr, yr, u: {yr: 1 - dl, 1 - yr: dl})
print("   CEG79 (83) with Yh=Yr xor Bern(%.6f): min=%.6f t1=%.6f t2=%.6f  constraint %.6f <= %.6f" % ((dl,) + r))
# drop (83c) but KEEP factorisation (83b): V uniform on {0,1}, U=V,
# V=0: Xr=0, X2~Bern(1/3); V=1: Xr=1, X2~Bern(2/3); X1 uniform; Yh=Yr
px_u = {0: {(a, b): 0.5 * (2 / 3 if b == 0 else 1 / 3) for a in (0, 1) for b in (0, 1)},
        1: {(a, b): 0.5 * (1 / 3 if b == 0 else 2 / 3) for a in (0, 1) for b in (0, 1)}}
r = thm7_orig({0: .5, 1: .5}, {0: {0: 1.0}, 1: {1: 1.0}}, px_u, {0: {0: 1.0}, 1: {1: 1.0}},
              lambda xr, yr, u: {yr: 1.0})
print("   (83a) with (83b) kept but (83c) dropped: min=%.6f t1=%.6f t2=%.6f  [(83c): %.6f <= %.6f violated]" % r)
print("   log2 3 =", math.log2(3))

# ---------------------------------------------- 4. Claim 6/7 numbers
hb = h
q = None
lo, hi = 0.0, 0.5
for _ in range(200):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if hb(mid) < 0.7 else (lo, mid)
q = (lo + hi) / 2
IXY1Yr = 1 + hb(0.26) - hb(0.2) - hb(0.1)
DF = 1 - hb(0.1)
L1 = lambda lam: 1 - hb(0.2) + 0.3 - lam * hb(0.1)
L2 = lambda lam: (1 - lam) * DF + lam * IXY1Yr
L3 = lambda lam: L2(lam) + 0.3 - lam * hb(0.26)
lam = (1 - hb(0.2) + 0.3 - DF) / (IXY1Yr - DF + hb(0.1))
print("4. q=%.6f  1-h(.1)=%.6f  I(X;Y1,Yr)=%.6f  cutset=min(%.6f,%.6f)" % (q, DF, IXY1Yr, IXY1Yr, 1 - hb(0.2) + 0.3))
print("   Thm7 time-sharing: lam=%.6f  rate=%.6f  (line3=%.6f slack)" % (lam, L1(lam), L3(lam)))
print("   Ponniah U-CF/C-CF analytic bound 1-h(.2)+0.8*0.3 = %.6f" % (1 - hb(0.2) + 0.24))

# local optimisation of Ponniah-type C-CF rate I(X;Yh,Y|Xr) s.t. I(Yh;Yr|Xr) <= I(Yh,Xr;Y)
# (same-law reading; arbitrary p(x,xr); |Yh|=3 >= |Xr|; penalty method)
def chanBSC():
    Wt = np.zeros((2, 2, 2, 2, 2))  # x, xr, y1, y2, yr
    for x, xr, y1, y2, yr in itertools.product((0, 1), repeat=5):
        Wt[x, xr, y1, y2, yr] = (0.8 if y1 == x else 0.2) * ((1 - q) if y2 == xr else q) * (0.9 if yr == x else 0.1)
    return Wt
Wt = chanBSC()
def Hn(a):
    a = a[a > 1e-15]
    return float(-(a * np.log2(a)).sum())
def ccf(params, kh=3):
    pxx = np.exp(params[:4]); pxx /= pxx.sum(); pxx = pxx.reshape(2, 2)
    T = np.exp(params[4:].reshape(2, 2, kh)); T /= T.sum(-1, keepdims=True)  # T[xr,yr,yh]
    J = pxx[:, :, None, None, None, None] * Wt[:, :, :, :, :, None] * T[None, :, None, None, :, :]
    # axes x, xr, y1, y2, yr, yh
    def Hm(keep):
        drop = tuple(i for i in range(6) if i not in keep)
        return Hn(J.sum(axis=drop).ravel())
    def I(A, B, C):
        return Hm(A | C) + Hm(B | C) - Hm(A | B | C) - (Hm(C) if C else 0.0)
    rate = I({0}, {5, 2, 3}, {1})
    slack = I({5, 1}, {2, 3}, set()) - I({5}, {4}, {1})
    return rate, slack
nprng = np.random.default_rng(11)
bestr = 0
for s in range(150):
    x0 = nprng.normal(size=4 + 12) * 2
    for pen in (10.0, 100.0, 1000.0):
        f = lambda v: -ccf(v)[0] + pen * max(0.0, -ccf(v)[1]) ** 2
        res = minimize(f, x0, method="Nelder-Mead", options={"maxiter": 3000, "xatol": 1e-7, "fatol": 1e-10})
        x0 = res.x
    rt, sl = ccf(x0)
    if sl >= -1e-6:
        bestr = max(bestr, rt)
print("   optimised feasible C-CF rate (150 starts) = %.6f  (analytic bound %.6f, DF %.6f)" % (bestr, 1 - hb(0.2) + 0.24, DF))
