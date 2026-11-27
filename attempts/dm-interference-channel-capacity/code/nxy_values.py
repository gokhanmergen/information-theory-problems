"""(a) max_{p,q} F(p,q) = max_{R_HK}(2R1+R2) for the NXY binary CZI channel (float, for orientation);
(b) exact re-evaluation of NXY's 2-letter TIN point;
(c) exact check of the polynomial identity behind NXY eq. (15) (sign of d^2 f / dq^2).
"""
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import minimize
import mpmath as mp
from czi_common import F, tin_value

# (a) grid + local refinement of F
best = (-1, None)
for p in np.linspace(0, 1, 401):
    for q in np.linspace(0, 1, 401):
        v = F(p, q)
        if v > best[0]:
            best = (v, (p, q))
res = minimize(lambda z: -F(np.clip(z[0], 0, 1), np.clip(z[1], 0, 1)), best[1], method="Nelder-Mead",
               options=dict(xatol=1e-12, fatol=1e-15, maxiter=20000))
print("max F (single-letter HK, 2R1+R2) ~", -res.fun, "at (p,q) =", res.x)

# (b) NXY 2-letter point, exact arithmetic in mpmath (50 digits)
mp.mp.dps = 50
p0 = mp.mpf("0.507829413"); q0 = mp.mpf("0.436538150")
px1 = [p0, 0, 0, 1 - p0]                       # (x11,x12) in {00,01,10,11}; repetition code
px2 = [mp.mpf("0.36") * q0, mp.mpf("0.64") * q0, mp.mpf("0.64") * q0, 1 - mp.mpf("1.64") * q0]
W = {(0, 0): [1, 0], (0, 1): [mp.mpf(1) / 2, mp.mpf(1) / 2], (1, 0): [1, 0], (1, 1): [0, 1]}
bits = [(0, 0), (0, 1), (1, 0), (1, 1)]
def Hm(v):
    return -mp.fsum([x * mp.log(x, 2) for x in v if x > 0])
J = {}
for a in range(4):
    for b in range(4):
        for c in range(4):
            pr = px1[a] * px2[b]
            for i in range(2):
                pr *= W[(bits[a][i], bits[b][i])][bits[c][i]]
            J[(a, b, c)] = pr
py = [mp.fsum(J[(a, b, c)] for a in range(4) for b in range(4)) for c in range(4)]
px1y = [mp.fsum(J[(a, b, c)] for b in range(4)) for a in range(4) for c in range(4)]
I1 = Hm(py) + Hm(px1) - Hm(px1y)
val = I1 + Hm(px2) / 2          # 2*R1 + R2 with R1 = I/2, R2 = H/2
print("NXY 2-letter point: R1 =", mp.nstr(I1 / 2, 12), " R2 =", mp.nstr(Hm(px2) / 2, 12),
      " 2R1+R2 =", mp.nstr(val, 15))
v_np, r1, r2 = tin_value(np.array([float(x) for x in px1]), np.array([float(x) for x in px2]), 2)
print("   (numpy cross-check:", v_np, ")")

# (c) exact polynomial identity: T(p,q) := -(2p-1)(1+q)(2q+p qb) + 2pq(2q+p qb) - (2-p) q (1+q)
#     equals p(1 - 3q - 2p qb), where qb = 1-q.  Both sides have degree <= 2 in p and <= 3 in q,
#     so agreement on a 4 x 5 grid of rationals proves the identity.
ok = True
for i in range(4):
    for j in range(5):
        p = Fr(i + 1, 7); q = Fr(j + 1, 11); qb = 1 - q
        T = -(2 * p - 1) * (1 + q) * (2 * q + p * qb) + 2 * p * q * (2 * q + p * qb) - (2 - p) * q * (1 + q)
        ok &= (T == p * (1 - 3 * q - 2 * p * qb))
print("polynomial identity for f_qq numerator holds on 4x5 rational grid (=> identically):", ok)
