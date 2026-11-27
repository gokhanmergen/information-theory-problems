# Reviewer check (2026-11-27, Claims 8, 10): interval enclosure (40 digits) of the 3-letter
# scheme's 2R1+R2, and a numerical re-check of the Claim-8 outer-bound value ~1.2290392.
# Run: python3 iv_k3_and_outer.py
# Runtime: about 1 s. Needs mpmath, numpy, scipy.
"""(1) Interval-arithmetic enclosure of (1/3)[2 I(X1^3;Y1^3) + H(X2^3)] for the attempt's 3-letter scheme.
(2) Numerical check of the Claim-8 single-letter outer-bound value (~1.229039)."""
import itertools
import mpmath as mp
from mpmath import iv
import numpy as np
from scipy.optimize import minimize

iv.dps = 40
LN2 = iv.log(2)
HALF = iv.mpf(1) / 2
P0 = {(0, 0): iv.mpf(1), (0, 1): HALF, (1, 0): iv.mpf(1), (1, 1): iv.mpf(0)}


def w1(y, a, b):
    return P0[(a, b)] if y == 0 else 1 - P0[(a, b)]


def negplogp(x):  # x is an interval known to contain a value in [0,1]; x either exactly 0 or > 0
    if x.b == 0:
        return iv.mpf(0)
    assert x.a > 0
    return -x * iv.log(x) / LN2


k = 3
words = list(itertools.product((0, 1), repeat=k))
a = iv.mpf("0.434823"); b = iv.mpf("0.136205"); c = iv.mpf("0.154298"); d = 1 - 3 * b - 3 * c
p1 = {w: iv.mpf(0) for w in words}; p1[(0, 0, 0)] = a; p1[(1, 1, 1)] = 1 - a
p2 = {w: (iv.mpf(0) if sum(w) == 0 else b if sum(w) == 1 else c if sum(w) == 2 else d) for w in words}
# p(y | x1) = sum_x2 p2(x2) prod_i w1(y_i | x1_i, x2_i)
pyx = {}
for x1 in [(0, 0, 0), (1, 1, 1)]:
    for y in words:
        s = iv.mpf(0)
        for x2 in words:
            t = p2[x2]
            for i in range(k):
                t = t * w1(y[i], x1[i], x2[i])
            s = s + t
        pyx[(x1, y)] = s
py = {y: p1[(0, 0, 0)] * pyx[((0, 0, 0), y)] + p1[(1, 1, 1)] * pyx[((1, 1, 1), y)] for y in words}
HY = sum((negplogp(py[y]) for y in words), iv.mpf(0))
HYgX1 = sum((p1[x1] * sum((negplogp(pyx[(x1, y)]) for y in words), iv.mpf(0)) for x1 in [(0, 0, 0), (1, 1, 1)]),
            iv.mpf(0))
I1 = HY - HYgX1
H2 = sum((negplogp(p2[w]) for w in words), iv.mpf(0))
val = (2 * I1 + H2) / 3
print("interval enclosure of 2R1+R2 (3-letter scheme):", val)
print("  lower end > 1.1102045 ?", val.a > mp.mpf("1.1102045"))
print("  R1 in", I1 / 3, "\n  R2 in", H2 / 3)


# (2) Claim 8 outer bound numeric
def hb(x):
    x = np.clip(x, 1e-300, 1 - 1e-16)
    return -x * np.log2(x) - (1 - x) * np.log2(1 - x)


def phi(p, q):  # I(X1X2;Y1) + H(X2|Y1,X1) + I(X1;Y1|X2), p=P(X1=0), q=P(X2=0)
    s = q + (1 - q) * p / 2
    IXY = hb(s) - p * (1 - q)
    I2gx1 = p * hb((1 + q) / 2) + (1 - p) * hb(q) - p * (1 - q)
    return IXY + (hb(q) - I2gx1) + (1 - q) * (hb(p / 2) - p)


G = np.linspace(0, 1, 2001)
PP, QQ = np.meshgrid(G, G, indexing="ij")
V = phi(PP, QQ)
i, j = np.unravel_index(np.argmax(V), V.shape)
r = minimize(lambda z: -phi(*np.clip(z, 0, 1)), [G[i], G[j]], method="Nelder-Mead",
             options=dict(xatol=1e-13, fatol=1e-15))
print("Claim 8 outer bound value ~", -r.fun, "at", r.x)
