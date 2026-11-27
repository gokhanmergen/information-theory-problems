#!/usr/bin/env python3
"""The plain Hekstra-Willems dependence-balance (DB) functional is vacuous for the BMC.

Evaluates the four conditional mutual informations of the Lean definition
`bmcDependenceBalanceBound` (lean/InfoTheory/Problems/BinaryMultiplierTwoWayChannel.lean)
with exactly the Lean formula
    condMutualInfo P = H(X,Z) + H(Y,Z) - H(X,Y,Z) - H(Z)
at kZ = 1 and Shannon's outer-bound optimiser
    p*(x1,x2):  p00 = 0,  p01 = p10 = (5 - sqrt5)/10,  p11 = 1/sqrt5,
in 60-digit arithmetic.  Expected output:
    I(X1;X2|Z)   = 0.1564...  <=  I(X1;X2|Y,Z) = 0.5527...   (DB constraint holds)
    I(X1;Y|X2,Z) = I(X2;Y|X1,Z) = log2((1+sqrt5)/2) = 0.694241913...
so bmcDependenceBalanceBound >= log2(phi) (and in fact = log2(phi), see the attempt file).

It also scans a grid of joint laws p(x1,x2) to confirm numerically that
max_p (H(Y|X1) + H(Y|X2))/2 = log2(phi) (Shannon 1961), the upper half of the claim.
"""
from itertools import product
from collections import defaultdict
import mpmath as mp

mp.mp.dps = 60


def H(dist):
    return -mp.fsum(p * mp.log(p, 2) for p in dist.values() if p > 0)


def marg(J, f):
    out = defaultdict(lambda: mp.mpf(0))
    for t, p in J.items():
        out[f(t)] += p
    return out


def cmi(J, fx, fy, fz):
    """I(X;Y|Z) = H(X,Z) + H(Y,Z) - H(X,Y,Z) - H(Z), as in Lean's condMutualInfo."""
    return (H(marg(J, lambda t: (fx(t), fz(t)))) + H(marg(J, lambda t: (fy(t), fz(t))))
            - H(marg(J, lambda t: (fx(t), fy(t), fz(t)))) - H(marg(J, fz)))


s5 = mp.sqrt(5)
P = {(0, 0, 0): mp.mpf(0), (0, 0, 1): (5 - s5) / 10, (0, 1, 0): (5 - s5) / 10, (0, 1, 1): 1 / s5}
assert abs(mp.fsum(P.values()) - 1) < mp.mpf(10) ** -50
# J on (z, x1, x2, y) with y = x1 AND x2, as in the Lean `let J := P.map ...`
J = {(z, a, b, a & b): p for (z, a, b), p in P.items()}
z = lambda t: t[0]
x1 = lambda t: t[1]
x2 = lambda t: t[2]
y = lambda t: t[3]
I12_Z = cmi(J, x1, x2, z)
I12_YZ = cmi(J, x1, x2, lambda t: (y(t), z(t)))
I1Y = cmi(J, x1, y, lambda t: (x2(t), z(t)))
I2Y = cmi(J, x2, y, lambda t: (x1(t), z(t)))
logphi = mp.log((1 + s5) / 2, 2)
print("I(X1;X2|Z)    =", mp.nstr(I12_Z, 20))
print("I(X1;X2|Y,Z)  =", mp.nstr(I12_YZ, 20))
print("DB constraint holds:", I12_Z <= I12_YZ)
print("I(X1;Y|X2,Z)  =", mp.nstr(I1Y, 30))
print("I(X2;Y|X1,Z)  =", mp.nstr(I2Y, 30))
print("log2(phi)     =", mp.nstr(logphi, 30))
print("|min - log2 phi| =", mp.nstr(abs(min(I1Y, I2Y) - logphi), 5))

# Grid check of Shannon's outer bound value (double precision; not a proof).
import numpy as np


def h(x):
    x = np.clip(x, 1e-300, 1.0)
    y_ = np.clip(1 - x, 1e-300, 1.0)
    return -(x * np.log2(x) + y_ * np.log2(y_))


N = 400
g = np.arange(N + 1) / N
best = 0.0
for i in range(N + 1):          # p11 = i/N
    p11 = g[i]
    a = g[:, None]               # P(X1=1)
    b = g[None, :]               # P(X2=1)
    ok = (a >= p11) & (b >= p11) & (a + b - p11 <= 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        A = np.where(a > 0, a * h(p11 / np.where(a > 0, a, 1)), 0.0)  # H(Y|X1)
        B = np.where(b > 0, b * h(p11 / np.where(b > 0, b, 1)), 0.0)  # H(Y|X2)
    v = np.where(ok, 0.5 * (A + B), -1).max()
    best = max(best, v)
print(f"grid max of (H(Y|X1)+H(Y|X2))/2 over p(x1,x2), step 1/{N}: {best:.6f} (log2 phi = {float(logphi):.6f})")
