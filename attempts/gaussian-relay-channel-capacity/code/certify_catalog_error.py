#!/usr/bin/env python3
"""Rigorous certificates for attempts/gaussian-relay-channel-capacity/
2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md

Every inequality that the attempt labels [proved] and that needs a number is
checked here, either with exact integer arithmetic (fractions) or with
mpmath interval arithmetic (mpmath.iv, outward rounding).  Floating-point
values are printed only for the reader; no conclusion depends on them.

Notation: C(s) = (1/2) log2(1+s), unit noise variances,
s12 = g12^2 P1, s13 = g13^2 P1, s23 = g23^2 P2,
R_CF(s12,s13,s23) = C(s13 + s12*s23/(1+s12+s13+s23))   (Gaussian CF, closed form).
Lemma 1 of the attempt: if g12^2 <= g13^2 then the Lean quantity
gaussianHybridDFCFRate equals ofReal(R_CF).

Run:  python3 certify_catalog_error.py      (about 1 s; prints PASS/FAIL lines)
"""
from fractions import Fraction as F
import mpmath
from mpmath import iv, mp

mp.dps = 50
iv.dps = 60

ok_all = True


def report(name, ok):
    global ok_all
    ok_all &= bool(ok)
    print(("PASS  " if ok else "FAIL  ") + name)


def cf_arg(s12, s13, s23):
    """1 + s13 + s12*s23/(1+s12+s13+s23), exact if inputs are Fractions."""
    return 1 + s13 + s12 * s23 / (1 + s12 + s13 + s23)


def log2mp(x):
    return mpmath.log(x, 2)


# ---------------------------------------------------------------------------
# Certificate A: bursty compress-forward (EMZ 2006 eq. (8)) beats
# gaussianHybridDFCFRate.  Exact integer comparisons.
# ---------------------------------------------------------------------------
print("== Certificate A: bursty CF vs hybrid rate (exact integer arithmetic) ==")

# A1. Headline point: g = (1,1,1), P1 = 1/1000, P2 = 1/10, burst fraction lambda = 1/100.
P1, P2, lam = F(1, 1000), F(1, 10), F(1, 100)
Fh = cf_arg(P1, P1, P2)                   # R_hyb = (1/2) log2 Fh   (Lemma 1, g12 = g13)
Fb = cf_arg(P1 / lam, P1 / lam, P2 / lam)  # R_CF at the burst powers
print("  R_hyb argument  Fh =", Fh, " burst argument Fb =", Fb)
assert Fh == F(551601, 551000) and Fb == F(333, 280)
# lam*(1/2)log2 Fb > (1/2)log2 Fh  <=>  Fb > Fh^(1/lam) = Fh^100
lhs = Fb.numerator * Fh.denominator ** 100
rhs = Fb.denominator * Fh.numerator ** 100
report("A1: (333/280) > (551601/551000)^100, i.e. (1/100)C-burst > R_hyb at (1,1,1,1e-3,1e-1)", lhs > rhs)
Rh = log2mp(mpmath.mpf(Fh.numerator) / Fh.denominator) / 2
Rb = mpmath.mpf(lam.numerator) / lam.denominator * log2mp(mpmath.mpf(Fb.numerator) / Fb.denominator) / 2
print("  R_hyb = %s  bursty-CF = %s  ratio = %s" % (mpmath.nstr(Rh, 12), mpmath.nstr(Rb, 12), mpmath.nstr(Rb / Rh, 8)))

# A2. Coordinator's point: g = (1,1,3), P1 = P2 = 1/20, lambda = 3/10.
g12, g13, g23 = 1, 1, 3
P1, P2, lam = F(1, 20), F(1, 20), F(3, 10)
Fh = cf_arg(g12**2 * P1, g13**2 * P1, g23**2 * P2)
Fb = cf_arg(g12**2 * P1 / lam, g13**2 * P1 / lam, g23**2 * P2 / lam)
# (3/10) log Fb > log Fh  <=>  Fb^3 > Fh^10
lhs = Fb.numerator ** 3 * Fh.denominator ** 10
rhs = Fb.denominator ** 3 * Fh.numerator ** 10
report("A2: Fb^3 > Fh^10 at (1,1,3,1/20,1/20), lambda=3/10", lhs > rhs)
Rh = log2mp(mpmath.mpf(Fh.numerator) / Fh.denominator) / 2
Rb = mpmath.mpf(3) / 10 * log2mp(mpmath.mpf(Fb.numerator) / Fb.denominator) / 2
print("  Fh =", Fh, " Fb =", Fb)
print("  R_hyb = %s  bursty-CF = %s  ratio = %s" % (mpmath.nstr(Rh, 12), mpmath.nstr(Rb, 12), mpmath.nstr(Rb / Rh, 8)))

# ---------------------------------------------------------------------------
# Certificate B: EMZ Example 1 (block-length-2 linear relaying) at unit gains,
# P1 = P2 = 1/10, beta = 2/3, versus (i) R_hyb and (ii) the supporting line
# R_CF(x1,x2) <= x1/(2 ln 2) + x2/20 that bounds the concave envelope.
# Interval arithmetic.
# ---------------------------------------------------------------------------
print("== Certificate B: EMZ Example 1 linear relaying (interval arithmetic) ==")


def rL_iv(x1, x2, beta):
    """Rate of EMZ Example 1, unit gains, unit noise, per channel use (interval).
    SNR = 2*beta*x1*(1 + (sqrt((1-beta)/beta) + d)^2/(1+d^2)), d^2 = 2*x2/(2*beta*x1+1),
    rate = (1/4) log2(1+SNR)."""
    x1, x2, beta = iv.mpf(x1), iv.mpf(x2), iv.mpf(beta)
    d2 = 2 * x2 / (2 * beta * x1 + 1)
    c = iv.sqrt((1 - beta) / beta) + iv.sqrt(d2)
    snr = 2 * beta * x1 * (1 + c * c / (1 + d2))
    return iv.log(1 + snr) / (4 * iv.log(2)), snr


rL, snr = rL_iv(iv.mpf(1) / 10, iv.mpf(1) / 10, iv.mpf(2) / 3)
print("  r_L(1/10,1/10; beta=2/3) in", rL, "  SNR in", snr)
# (i) versus R_hyb(1/10,1/10) = (1/2)log2(72/65)
Fh = cf_arg(F(1, 10), F(1, 10), F(1, 10))
assert Fh == F(72, 65)
# r_L > R_hyb  <=>  1 + SNR > (72/65)^2
report("B1: 1+SNR_L > (72/65)^2, i.e. r_L > R_hyb at (1,1,1,1/10,1/10)",
       (1 + snr).a > iv.mpf(72 * 72) / (65 * 65))
Rh = log2mp(mpmath.mpf(72) / 65) / 2
print("  R_hyb(1/10,1/10) = %s" % mpmath.nstr(Rh, 12))

# (ii) Supporting-line lemma: for all x1, x2 >= 0,
#   R_CF(x1,x1,x2) <= m*x1 + mu2*x2,  m = 1/(2 ln 2), mu2 = 1/20.
# Reduction (proved in the attempt): it suffices that for all x >= 0
#   Phi(x) = (sqrt(K) - sqrt(mu2*D))_+^2 - m*(x - ln(1+x)) <= 0,
#   K = m*x/(1+x), D = 1 + 2x.
# (sqrt K - sqrt(mu2 D))_+ = 0 iff q(x) = 2 mu2 x^2 + (3 mu2 - m) x + mu2 >= 0.
mu2 = iv.mpf(1) / 20
m_iv = 1 / (2 * iv.log(2))


def q_iv(x):
    x = iv.mpf(x)
    return 2 * mu2 * x * x + (3 * mu2 - m_iv) * x + mu2


xlo, xhi = F(2, 25), F(6)   # 0.08 and 6
# q is a convex quadratic with vertex (m - 3 mu2)/(4 mu2) in (0.08, 6); so q >= min(q(0.08), q(6)) > 0
# on [0, 0.08] U [6, inf) once we check q(0.08) > 0, q(6) > 0 and the vertex lies in between.
vertex = (m_iv - 3 * mu2) / (4 * mu2)
report("B2a: q(0.08) > 0, q(6) > 0, vertex in (0.08, 6)  => Phi = -m(x-ln(1+x)) <= 0 off [0.08, 6]",
       q_iv(iv.mpf(2) / 25).a > 0 and q_iv(6).a > 0 and vertex.a > iv.mpf(2) / 25 and vertex.b < 6)


def phi_upper(l, u):
    """Rigorous upper bound of Phi on [l,u] (0 < l < u): K increasing, D increasing,
    x - ln(1+x) increasing."""
    l, u = iv.mpf(l), iv.mpf(u)
    Ku = m_iv * u / (1 + u)
    Dl = 1 + 2 * l
    t = iv.sqrt(Ku) - iv.sqrt(mu2 * Dl)
    pos = t.b if t.b > 0 else mpmath.mpf(0)
    pos_sq = iv.mpf(pos) * iv.mpf(pos)
    gain = m_iv * (l - iv.log(1 + l))
    return (pos_sq - gain).b


def bnb(l, u, depth=0, stats=None):
    if stats is None:
        stats = {"boxes": 0, "maxub": -mpmath.inf}
    ub = phi_upper(l, u)
    if ub <= 0:
        stats["boxes"] += 1
        stats["maxub"] = max(stats["maxub"], ub)
        return True, stats
    if depth > 40:
        return False, stats
    mid = (iv.mpf(l) + iv.mpf(u)) / 2
    mid = mid.a  # any split point is fine
    ok1, _ = bnb(l, mid, depth + 1, stats)
    ok2, _ = bnb(mid, u, depth + 1, stats)
    return ok1 and ok2, stats


ok, stats = bnb(mpmath.mpf(2) / 25, mpmath.mpf(6))
report("B2b: Phi(x) <= 0 on [0.08, 6] (interval branch-and-bound, %d leaf intervals, max leaf UB %s)"
       % (stats["boxes"], mpmath.nstr(stats["maxub"], 5)), ok)

# (iii) Slope comparison: bursting Example 1 from (1/10,1/10) gives, for 0 < t <= 1/10,
#   C_Gauss(1,1,1,t,t) >= 10*t*r_L(1/10,1/10) ; concave envelope of R_hyb along (t,t) <= (m + 1/20) t.
slope_L = 10 * rL
slope_env = m_iv + mu2
print("  bursty-linear slope in", slope_L, "  envelope slope bound", slope_env)
report("B3: 10*r_L(1/10,1/10) > 1/(2 ln 2) + 1/20  (strict, for every t in (0,1/10])",
       slope_L.a > slope_env.b)

# ---------------------------------------------------------------------------
# Certificate C: second-derivative constant of Theorem 2 (symbolic; checked here numerically
# only as an illustration):  d^2/dt^2 R_CF(t p) at 0 = (2 b d - a^2)/(2 ln 2),
# a = g13^2 p1, b = g12^2 p1, d = g23^2 p2.
# ---------------------------------------------------------------------------
print("== Illustration of Theorem 2 constant (finite differences, not a proof) ==")
a, b, d = mpmath.mpf(1), mpmath.mpf(1), mpmath.mpf(1)
Rt = lambda t: mpmath.log(1 + a * t + b * d * t * t / (1 + (a + b + d) * t)) / (2 * mpmath.log(2))
h = mpmath.mpf("1e-12")
fd = (Rt(2 * h) - 2 * Rt(h) + Rt(0)) / h**2
print("  finite-difference R''(0) =", mpmath.nstr(fd, 10), "  formula =", mpmath.nstr((2 * b * d - a * a) / (2 * mpmath.log(2)), 10))

print()
print("ALL CERTIFICATES PASS" if ok_all else "SOME CERTIFICATE FAILED")
