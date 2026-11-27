# Reviewer check (2026-11-27, item 7): LB2 recomputed from the Lean definition on the author's saved
# k = 2 law (exact-rational renormalisation, entropies at 60 digits); output in rev_k2_exact.log.
# Run: python3 rev_k2_exact.py [law.npz]   (default ../opt_q0.5.npz, the law used in the note)
# Runtime: under 1 s. Needs numpy, mpmath.
"""Reviewer's independent evaluation of the k=2 point, written from the Lean definition of
coverLeungKLetterRegion (not from mac_cl.py).

Strategy for k=2, binary X, binary Y: s = (x0, f) with s(0)() = x0, s(1)(y0) = f(y0).
Index convention of the saved arrays (read off mac_cl.strategies): a = 4*x0 + 2*f(0) + f(1).
Distribution is renormalised EXACTLY (Fractions); the joint J(u,s1,s2,y0,y1) is an exact rational;
entropies are then evaluated with mpmath at 60 digits, using Lean's formulas
  condMutualInfo(X;Y|Z) = H(X,Z) + H(Y,Z) - H(X,Y,Z) - H(Z),  mutualInfo = H(X)+H(Y)-H(X,Y).
"""
import os
import sys
from fractions import Fraction as F
from collections import defaultdict
import numpy as np
import mpmath as mp

mp.mp.dps = 60
npz = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), '..', 'opt_q0.5.npz')
q = F(1, 2)
D = np.load(npz)

def exact(v):
    v = [F(float(x)) for x in v]
    s = sum(v)
    return [x / s for x in v]

pu = exact(D["pu2"]); P1 = [exact(r) for r in D["P12"]]; P2 = [exact(r) for r in D["P22"]]
nu = len(pu)
strat = [(a >> 2, ((a >> 1) & 1, a & 1)) for a in range(8)]    # (x0, (f(0), f(1)))

def W(x1, x2, y):
    p1 = q * (x1 + x2)
    return p1 if y == 1 else 1 - p1

J = {}
for u in range(nu):
    for a, (x10, f1) in enumerate(strat):
        for b, (x20, f2) in enumerate(strat):
            base = pu[u] * P1[u][a] * P2[u][b]
            if base == 0:
                continue
            for y0 in (0, 1):
                for y1 in (0, 1):
                    pr = W(x10, x20, y0) * W(f1[y0], f2[y0], y1)
                    if pr:
                        J[(u, a, b, (y0, y1))] = base * pr
assert sum(J.values()) == 1, "joint is not exactly normalised"

def H(keyf):
    m = defaultdict(F)
    for k, v in J.items():
        m[keyf(k)] += v
    return -mp.fsum([mp.mpf(v.numerator) / v.denominator * mp.log(mp.mpf(v.numerator) / v.denominator, 2)
                     for v in m.values() if v > 0])

# J key = (u, s1, s2, y)
I1 = H(lambda k: (k[1], k[2], k[0])) + H(lambda k: (k[3], k[2], k[0])) - H(lambda k: k) - H(lambda k: (k[2], k[0]))
I2 = H(lambda k: (k[2], k[1], k[0])) + H(lambda k: (k[3], k[1], k[0])) - H(lambda k: k) - H(lambda k: (k[1], k[0]))
I12 = H(lambda k: (k[1], k[2])) + H(lambda k: k[3]) - H(lambda k: (k[1], k[2], k[3]))
r1, r2, s = I1 / 2, I2 / 2, I12 / 2
print("I(S1;Y^2|S2,U)/2 =", mp.nstr(r1, 20))
print("I(S2;Y^2|S1,U)/2 =", mp.nstr(r2, 20))
print("I(S1S2;Y^2)/2    =", mp.nstr(s, 20))
print("point (r1,r2) feasible (r1+r2 <= sum bound):", r1 + r2 <= s, " r1+r2 =", mp.nstr(r1 + r2, 20))
print("LB2 = min(r1+r2, I12/2) =", mp.nstr(min(r1 + r2, s), 20))
