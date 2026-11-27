"""A simple explicit 3-letter TIN scheme on the NXY binary CZI channel, evaluated in 40-digit arithmetic.

X1^3: repetition code, P(000) = a, P(111) = 1-a.
X2^3: never 000 (X2 = 0 forces Y1 = 0, which would erase the repeated X1 symbol);
      each weight-1 word w.p. b, each weight-2 word w.p. c, 111 w.p. d = 1 - 3b - 3c.
Value: (1/3)[2 I(X1^3;Y1^3) + H(X2^3)] = 2R1 + R2 with R1 = I/3, R2 = H/3; a point of HK^(3)(W)
(U1 = U2 = Q = const).  Parameters optimised in floating point, then rounded to 6 decimals and
re-evaluated exactly (any rounding gives a valid distribution, so the value is a rigorous lower bound).
"""
import itertools
import numpy as np
from scipy.optimize import minimize
import mpmath as mp
from czi_common import joint_k, tin_value

k = 3
_, Wk = joint_k(np.ones(8) / 8, np.ones(8) / 8, k)
wt = [bin(s).count("1") for s in range(8)]


def dists(a, b, c):
    p1 = np.zeros(8); p1[0] = a; p1[7] = 1 - a
    p2 = np.array([0.0 if w == 0 else b if w == 1 else c if w == 2 else 1 - 3 * b - 3 * c for w in wt])
    return p1, p2


def obj(z):
    a, b, c = z
    if not (0 < a < 1 and b > 0 and c > 0 and 3 * b + 3 * c < 1):
        return 10.0
    p1, p2 = dists(a, b, c)
    return -tin_value(p1, p2, k, Wk=Wk)[0]


res = minimize(obj, [0.435, 0.136, 0.154], method="Nelder-Mead", options=dict(xatol=1e-12, fatol=1e-15))
a, b, c = res.x
print(f"float optimum of the 3-parameter family: {-res.fun:.10f} at a={a:.8f}, b={b:.8f}, c={c:.8f}")

mp.mp.dps = 40
A, B, Cc = (mp.mpf(str(round(x, 6))) for x in (a, b, c))
D = 1 - 3 * B - 3 * Cc
P1 = [A] + [mp.mpf(0)] * 6 + [1 - A]
P2 = [mp.mpf(0) if w == 0 else B if w == 1 else Cc if w == 2 else D for w in wt]
Wm = {(0, 0): [1, 0], (0, 1): [mp.mpf(1) / 2, mp.mpf(1) / 2], (1, 0): [1, 0], (1, 1): [0, 1]}
bits = [tuple((s >> (k - 1 - i)) & 1 for i in range(k)) for s in range(8)]


def Hm(v):
    return -mp.fsum([x * mp.log(x, 2) for x in v if x > 0])


J = {}
for s1 in range(8):
    for s2 in range(8):
        for y in range(8):
            pr = P1[s1] * P2[s2]
            for i in range(k):
                pr *= Wm[(bits[s1][i], bits[s2][i])][bits[y][i]]
            J[(s1, s2, y)] = pr
py = [mp.fsum(J[(s1, s2, y)] for s1 in range(8) for s2 in range(8)) for y in range(8)]
pxy = [mp.fsum(J[(s1, s2, y)] for s2 in range(8)) for s1 in range(8) for y in range(8)]
I = Hm(py) + Hm(P1) - Hm(pxy)
val = (2 * I + Hm(P2)) / 3
print(f"rounded parameters a={A}, b={B}, c={Cc}, d={D}")
print(f"exact (40-digit): R1 = {mp.nstr(I/3, 12)}, R2 = {mp.nstr(Hm(P2)/3, 12)}, 2R1+R2 = {mp.nstr(val, 15)}")
