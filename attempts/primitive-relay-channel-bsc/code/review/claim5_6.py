# Reviewer check (2026-11-27, Claims 5, 6, 9): sympy factorisation, a(theta)/b(theta) closed forms vs
# direct joint enumeration (random U, seed 3), and the EGN Thm 6 witness Phi (50 digits).
# Run: python3 claim5_6.py
# Runtime: about 2 s. Needs numpy, sympy, mpmath.
"""Reviewer checks for Claims 5, 6, 9 (symmetric case)."""
import numpy as np
import sympy as sp
from mpmath import mp, mpf, log
mp.dps = 50

# --- Claim 5: power-series coefficient identity
k, m = sp.symbols('k m', positive=True)
expr = k**(4*m) + k**2 - (1 + k**2) * k**(2*m)
print('factorisation check:', sp.simplify(sp.expand(expr - (k**(2*m) - k**2) * (k**(2*m) - 1))) == 0)

# psi(t) = 1 - h(1/2+t) series check numerically
def hb(x):
    x = mpf(x)
    return -(x * log(x, 2) + (1 - x) * log(1 - x, 2))
t = mpf('0.13')
ser = sum((2 * t) ** (2 * j) / (2 * j * (2 * j - 1)) for j in range(1, 200)) / log(2)
print('psi series check:', mp.nstr(1 - hb(mpf(1) / 2 + t) - ser, 5))

# --- Claim 5: a(theta), b(theta) vs direct joint computation, uniform X, random U
rng = np.random.default_rng(3)
def Hn(P):
    P = P.ravel(); P = P[P > 0]
    return float(-(P * np.log2(P)).sum())
worst = 0
for rho in (0.05, 0.1, 0.2, 0.3, 0.45):
    W = np.array([[1 - rho, rho], [rho, 1 - rho]])
    s = (1 - 2 * rho) ** 2 / (1 + (1 - 2 * rho) ** 2)
    hf = lambda q: -(q * np.log2(q) + (1 - q) * np.log2(1 - q))
    st = lambda a, b: a * (1 - b) + (1 - a) * b
    for trial in range(3000):
        kU = rng.integers(2, 6)
        T = rng.dirichlet(np.full(kU, 0.5), size=2)  # [yr,u]
        J = 0.5 * W[:, :, None, None] * W[:, None, :, None] * T[None, None, :, :]  # x,y,yr,u
        a = Hn(J.sum((2, 3))) + Hn(J.sum((0, 2))) - Hn(J.sum(2)) - Hn(J.sum((0, 2, 3)))
        b = Hn(J.sum((0, 3))) + Hn(J.sum((0, 2))) - Hn(J.sum(0)) - Hn(J.sum((0, 2, 3)))
        # closed form
        Pu = J.sum((0, 1, 2)); Pyr_u = J.sum((0, 1)) / Pu[None, :]
        th = Pyr_u[1]
        a_cf = float((Pu * (hf(st(st(th, rho), rho)) - hf(st(th, rho)))).sum())
        b_cf = float((Pu * (hf(st(st(th, rho), rho)) - hf(th))).sum())
        assert abs(a - a_cf) < 1e-9 and abs(b - b_cf) < 1e-9, (a, a_cf, b, b_cf)
        if b > 1e-8:
            worst = max(worst, a / b / s)
print('closed forms a,b match direct computation; max (a/b)/s over random U =', worst)

# --- Claim 5: s = corr^2(X,Yr|Y)
rho = mpf('0.1'); kk = 1 - 2 * rho
print('s_0.1 =', mp.nstr(kk**2 / (1 + kk**2), 10))

# --- Claim 6: witness Phi > 0 at lambda=0.99, a=0.25, t=0.000775, rho=0.1
def dkl(u, r):
    return u * log(u / r, 2) + (1 - u) * log((1 - u) / (1 - r), 2)
lam, a, t = mpf('0.99'), mpf('0.25'), mpf('0.000775')
y = rho + (1 - 2 * rho) * a
u, v = rho - t, rho + t
z = (1 - a) * u + a * (1 - v)
Phi = (1 - lam) * (hb(y) - hb(z)) - (1 - a) * dkl(u, rho) - a * dkl(v, rho)
# also directly: f_lambda - tangent line at c
c = (1 - a) * u + a * v
f = (1 - lam) * (hb(y) - hb(z)) + (1 - a) * hb(u) + a * hb(v)
tang = hb(rho) + log((1 - rho) / rho, 2) * (c - rho)
print('Phi =', mp.nstr(Phi, 8), '  f - tangent =', mp.nstr(f - tang, 8))

# --- Claim 6 for many lambda: max over (a,t) of Phi > 0 ?
for lam in ('0.5', '0.9', '0.999', '0.99999'):
    lam = mpf(lam)
    best = max(((1 - lam) * (hb(rho + (1 - 2 * rho) * a) - hb(rho + (1 - 2 * rho) * a - t))
                - (1 - a) * dkl(rho - t, rho) - a * dkl(rho + t, rho), a, t)
               for a in (mpf('0.1'), mpf('0.25'), mpf('0.4'))
               for t in [(1 - lam) * mpf(j) / 50 for j in range(1, 60)] if t < rho)
    print('lambda', mp.nstr(lam, 6), 'max Phi on small grid', mp.nstr(best[0], 6))

# --- Claim 8: c_alpha asymptotics, alpha = 2(1-rho)  (formula as transcribed in the attempt)
from mpmath import findroot, exp, sqrt
alpha = 2 * (1 - rho)
def c_alpha(hh):
    g = lambda tt: (alpha - 1) * tt + hh / (1 - exp(-tt))
    # minimise over t>0 by golden search
    from mpmath import mpf as F
    lo, hi = F('1e-12'), F(50)
    for _ in range(300):
        m1 = lo + (hi - lo) * F('0.382'); m2 = lo + (hi - lo) * F('0.618')
        if g(m1) < g(m2): hi = m2
        else: lo = m1
    return g((lo + hi) / 2)
for hh in ('1e-2', '1e-4', '1e-6'):
    hh = mpf(hh)
    print('h=', hh, ' c_alpha(h)/(2 sqrt((alpha-1) h)) =', mp.nstr(c_alpha(hh) / (2 * sqrt((alpha - 1) * hh)), 8))
