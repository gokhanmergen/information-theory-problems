# Reviewer check (2026-11-27, Claims 3, 5, 6, 7): certificate inequalities A1, A2, B1, B3 and the
# Phi <= 0 box check on [0.08, 6], in exact Fraction arithmetic (artanh-series ln, integer isqrt).
# Run: python3 exact_checks.py
# Runtime: under 1 s; prints ALL OK. Standard library only.
"""Independent reviewer checks, exact rational arithmetic only (no floats in any decision).
Gaussian relay, unit noise.  C(s) = 1/2 log2(1+s).
"""
from fractions import Fraction as F
from math import isqrt


def ln_bounds(x, K=40):
    """Rigorous rational bounds lo <= ln(x) <= hi for rational x >= 1, via
    ln x = 2 artanh(y), y=(x-1)/(x+1), tail <= y^(2K+1)/((2K+1)(1-y^2))."""
    x = F(x)
    assert x >= 1
    y = (x - 1) / (x + 1)
    s = F(0)
    p = y
    for k in range(K):
        s += p / (2 * k + 1)
        p *= y * y
    tail = p / ((2 * K + 1) * (1 - y * y))
    return 2 * s, 2 * (s + tail)


def sqrt_lo(q, prec=10**30):
    q = F(q)
    assert q >= 0
    return F(isqrt(q.numerator * prec * prec // q.denominator), prec)


def sqrt_hi(q, prec=10**30):
    r = sqrt_lo(q, prec)
    while r * r < q:
        r += F(1, prec)
    return r


LN2_LO, LN2_HI = ln_bounds(2)
M_LO, M_HI = 1 / (2 * LN2_HI), 1 / (2 * LN2_LO)   # m = 1/(2 ln 2)
print("ln2 in [%.15f, %.15f]" % (LN2_LO, LN2_HI))


def cfarg(s12, s13, s23):
    return 1 + s13 + s12 * s23 / (1 + s12 + s13 + s23)


ok = True
# ---- A1: (1,1,1, 1e-3, 1e-1), lambda = 1/100
P1, P2, lam = F(1, 1000), F(1, 10), F(1, 100)
Fh = cfarg(P1, P1, P2)
Fb = cfarg(P1 / lam, P1 / lam, P2 / lam)
print("A1 Fh =", Fh, " Fb =", Fb)
a1 = Fb > Fh ** 100           # lam*log Fb > log Fh  <=>  Fb > Fh^(1/lam)
print("A1 Fb > Fh^100:", a1)
ok &= a1
lo_b, hi_b = ln_bounds(Fb)
lo_h, hi_h = ln_bounds(Fh)
print("  bursty CF rate in [%.10f, %.10f]" % (lam * lo_b / (2 * LN2_HI), lam * hi_b / (2 * LN2_LO)))
print("  R_hyb        in [%.10f, %.10f]" % (lo_h / (2 * LN2_HI), hi_h / (2 * LN2_LO)))
# ---- A2: (1,1,3, 1/20, 1/20), lambda = 3/10
P1, P2, lam = F(1, 20), F(1, 20), F(3, 10)
Fh = cfarg(P1, P1, 9 * P2)
Fb = cfarg(P1 / lam, P1 / lam, 9 * P2 / lam)
print("A2 Fh =", Fh, " Fb =", Fb)
a2 = Fb ** 3 > Fh ** 10
print("A2 Fb^3 > Fh^10:", a2)
ok &= a2
lo_b, hi_b = ln_bounds(Fb)
lo_h, hi_h = ln_bounds(Fh)
print("  bursty CF rate in [%.10f, %.10f]" % (lam * lo_b / (2 * LN2_HI), lam * hi_b / (2 * LN2_LO)))
print("  R_hyb        in [%.10f, %.10f]" % (lo_h / (2 * LN2_HI), hi_h / (2 * LN2_LO)))

# ---- B1: EMZ Example 1, unit gains, P1=P2=1/10, beta=2/3.
# SNR = 2 beta P1 (1 + c^2/(1+d^2)), c = sqrt((1-beta)/beta) + d, d^2 = 2P2/(2 beta P1 + 1)
beta, P1, P2 = F(2, 3), F(1, 10), F(1, 10)
d2 = 2 * P2 / (2 * beta * P1 + 1)
assert d2 == F(3, 17)
r1 = (1 - beta) / beta          # = 1/2
# c^2 = r1 + d2 + 2 sqrt(r1*d2)
cross_lo = sqrt_lo(r1 * d2)
cross_hi = sqrt_hi(r1 * d2)
snr_lo = 2 * beta * P1 * (1 + (r1 + d2 + 2 * cross_lo) / (1 + d2))
snr_hi = 2 * beta * P1 * (1 + (r1 + d2 + 2 * cross_hi) / (1 + d2))
print("B1 SNR in [%.15f, %.15f]" % (snr_lo, snr_hi))
assert cfarg(P1, P1, P2) == F(72, 65)
b1 = 1 + snr_lo > F(72, 65) ** 2
print("B1 1+SNR > (72/65)^2 :", b1)
ok &= b1
lnL, _ = ln_bounds(1 + snr_lo)
_, lnH = ln_bounds(1 + snr_hi)
rL_lo, rL_hi = lnL / (4 * LN2_HI), lnH / (4 * LN2_LO)
print("  r_L in [%.13f, %.13f]" % (rL_lo, rL_hi))
# ---- B3: 10 r_L > m + 1/20
b3 = 10 * rL_lo > M_HI + F(1, 20)
print("B3 10 r_L >= %.10f > m+1/20 <= %.10f : %s" % (10 * rL_lo, M_HI + F(1, 20), b3))
ok &= b3

# ---- B2: Phi(x) = (sqrt K - sqrt(mu D))_+^2 - m (x - ln(1+x)) <= 0 for all x >= 0,
# K = m x/(1+x), D = 1+2x, mu = 1/20.  Independent proof: exact rationals, uniform grid.
mu = F(1, 20)
xl, xr = F(2, 25), F(6)


def qlo(x):
    # q(x) = 2mu x^2 + (3mu - m) x + mu >= qlo(x) for x >= 0, since m <= M_HI
    return 2 * mu * x * x + (3 * mu - M_HI) * x + mu


vert_hi = (M_HI - 3 * mu) / (4 * mu)   # vertex of qlo
b2a = qlo(xl) > 0 and qlo(xr) > 0 and xl < vert_hi < xr
print("B2a qlo(0.08)=%.6f qlo(6)=%.6f vertex(qlo)=%.4f : %s" % (qlo(xl), qlo(xr), vert_hi, b2a))
ok &= b2a


def phi_ub(l, u):
    Khi = M_HI * u / (1 + u)
    muD = mu * (1 + 2 * l)
    if Khi <= muD:
        pos2 = F(0)
    else:
        pos2 = Khi + muD - 2 * sqrt_lo(Khi * muD)
    _, lnhi = ln_bounds(1 + l, K=25)
    gap = l - lnhi
    gain = M_LO * gap if gap > 0 else F(0)
    return pos2 - gain


NBOX = 600
worst = None
b2b = True
for i in range(NBOX):
    l = xl + (xr - xl) * i / NBOX
    u = xl + (xr - xl) * (i + 1) / NBOX
    v = phi_ub(l, u)
    if worst is None or v > worst[0]:
        worst = (v, l, u)
    if v > 0:
        b2b = False
        print("   box FAILS", float(l), float(u), float(v))
print("B2b Phi <= 0 on [0.08,6] with %d uniform boxes: %s ; worst box UB %.6e on [%.4f,%.4f]"
      % (NBOX, b2b, worst[0], worst[1], worst[2]))
ok &= b2b
print("ALL OK" if ok else "SOME CHECK FAILED")
