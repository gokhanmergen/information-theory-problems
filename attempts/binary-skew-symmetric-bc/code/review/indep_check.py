#!/usr/bin/env python3
# Reviewer check (2026-11-27): Marton RTD point and Lean constraints at 50 digits, exact UV
# value via the tangent at t = 4/5, and float64 grid-hull values of F_J(1/2), F_GK(1/2).
# Run: python3 indep_check.py [N ...]   (default N = 2000 20000 200000; output in indep_out.txt)
# Runtime: about 6 s. Needs numpy and mpmath.
"""Independent reviewer check (not derived from the author's code).

1. Marton RTD sum rate at the author's exact rational a, mpmath 50 digits; and the max over a.
2. UV envelope form (GLN eq. 18) at t=1/2: exact via the two-point chord maximisation in mpmath.
3. F_J(1/2), F_GK(1/2) via dense-grid upper hulls (float64), several grid sizes.
Conventions: t = P(X=1); Y: 0->0, 1->Unif;  Z: 1->1, 0->Unif.
"""
import sys
import numpy as np
import mpmath as mp
from fractions import Fraction as Fr

mp.mp.dps = 50


def hb(p):
    p = mp.mpf(p)
    if p == 0 or p == 1:
        return mp.mpf(0)
    return -(p * mp.log(p, 2) + (1 - p) * mp.log(1 - p, 2))


# ---------------- 1. Marton ----------------
a_rat = Fr(2854123837928735, 18014398509481984)
a = mp.mpf(a_rat.numerator) / a_rat.denominator
S = lambda a: hb(mp.mpf(1) / 4) + hb(a / 2) / 2 - hb((1 - a) / 2) / 2 - a
print("a (author rational) =", mp.nstr(a, 20))
print("S(a) at author's a   =", mp.nstr(S(a), 25))
amax = mp.findroot(lambda x: mp.diff(S, x), 0.158)
print("argmax a* =", mp.nstr(amax, 25), " S(a*) =", mp.nstr(S(amax), 25))

# direct check of Lean-region constraints for the RTD point (W uniform; W=0: X~Bern(a),U=X,V=0;
# W=1: X~Bern(1-a),U=0,V=X); Y1 Z-channel (x=1 -> Unif), Y2 reversed
IY = lambda t: hb(t / 2) - t           # I(X;Y1) at P(X=1)=t
IZ = lambda t: hb((1 - t) / 2) - (1 - t)
I_WU_Y1 = hb(mp.mpf(1) / 4) - (a / 2 + hb((1 - a) / 2) / 2)
I_WV_Y2 = hb(mp.mpf(1) / 4) - (hb((1 - a) / 2) / 2 + a / 2)
I_U_Y1_W = IY(a) / 2
I_V_Y2_W = IZ(1 - a) / 2
s1 = I_WU_Y1 + I_V_Y2_W
s2 = I_U_Y1_W + I_WV_Y2
print("Lean constraints: I(WU;Y1)=%s I(WV;Y2)=%s sum1=%s sum2=%s  R=S/2=%s" % tuple(
    mp.nstr(v, 15) for v in (I_WU_Y1, I_WV_Y2, s1, s2, S(a) / 2)))

# ---------------- 2. UV exact ----------------
# (18) at 1/2 = I_Y(1/2) + C[I_Z - I_Y](1/2) by symmetry.  C at 1/2 = max over chords.
f = lambda t: IZ(t) - IY(t)


def chord(t1, t2):
    return ((t2 - mp.mpf(1) / 2) * f(t1) + (mp.mpf(1) / 2 - t1) * f(t2)) / (t2 - t1)


# scan
best = None
for t1 in [mp.mpf(i) / 400 for i in range(0, 200)]:
    for t2 in [mp.mpf(j) / 400 for j in range(201, 401)]:
        v = chord(t1, t2)
        if best is None or v > best[0]:
            best = (v, t1, t2)
print("UV chord scan best:", mp.nstr(best[0], 12), "at", mp.nstr(best[1], 6), mp.nstr(best[2], 6))
# refine: one end is an endpoint (t=0 or 1) per scan; tangent condition at the interior end
v0, t1b, t2b = best
if t1b == 0:
    # line from (0,f(0)) tangent at t2: f(t2) - f(0) = t2 f'(t2)
    hp = lambda p: mp.log((1 - p) / p, 2)
    fp = lambda t: -hp((1 - t) / 2) / 2 + 1 - hp(t / 2) / 2 + 1
    tt = mp.findroot(lambda x: f(x) - f(0) - x * fp(x), (mp.mpf('0.7'), mp.mpf('0.9')), solver='anderson')
    print("tangent residual at 4/5:", mp.nstr(f(mp.mpf(4)/5) - f(0) - mp.mpf(4)/5 * fp(mp.mpf(4)/5), 5))
    val = chord(mp.mpf(0), tt)
    print("UV tangent point t =", mp.nstr(tt, 25))
else:
    tt = mp.findroot(lambda x: f(x) - f(1) - (x - 1) * mp.diff(f, x), t1b)
    val = chord(tt, mp.mpf(1))
    print("UV tangent point t =", mp.nstr(tt, 25))
UV = IY(mp.mpf(1) / 2) + val
print("UV (18) at 1/2 exact =", mp.nstr(UV, 25))

# ---------------- 3. grid hulls ----------------


def hn(p):
    p = np.clip(p, 0, 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        r = -(p * np.log2(p) + (1 - p) * np.log2(1 - p))
    return np.nan_to_num(r)


def grid(N):
    u = np.linspace(0, 1, N + 1)
    g = np.sin(np.pi * u / 2) ** 2
    geo = g[1] * 2.0 ** (-np.arange(1, 50))
    return np.unique(np.concatenate([g, geo, 1 - geo, [0.5]]))


def hull_vals(T, V):
    H = []
    for i in range(len(T)):
        while len(H) >= 2:
            i1, i2 = H[-2], H[-1]
            if (T[i2] - T[i1]) * (V[i] - V[i1]) >= (V[i2] - V[i1]) * (T[i] - T[i1]):
                H.pop()
            else:
                break
        H.append(i)
    H = np.array(H)
    return np.interp(T, T[H], V[H])


def I_Jn(T, a0, a1):
    return hn(a0 + (a1 - a0) * T) - (1 - T) * hn(np.array(a0)) - T * hn(np.array(a1))


def IYn(T):
    return hn(T / 2) - T


def IZn(T):
    return hn((1 - T) / 2) - (1 - T)


def FJ(T, a0, a1):
    Y, Z, J = IYn(T), IZn(T), I_Jn(T, a0, a1)
    A = hull_vals(T, hull_vals(T, J - Y) + 0.5 * (Y - J))
    B = hull_vals(T, hull_vals(T, J - Z) + 0.5 * (Z - J))
    F = 0.5 * Y + 0.5 * Z + A + B
    return F


def FGK(T, g0, g1):
    Y, Z = IYn(T), IZn(T)
    G = I_Jn(T, g0, g1)
    K = I_Jn(T, 1 - g1, 1 - g0)
    A = hull_vals(T, 0.5 * (Y - G) + hull_vals(T, G - Y))
    B = hull_vals(T, 0.5 * (Z - K) + hull_vals(T, K - Z))
    c = 0.5 * hull_vals(T, G - K) + 0.5 * hull_vals(T, K - G)
    return 0.5 * Y + 0.5 * Z + A + B + c


def UVn(T):
    Y, Z = IYn(T), IZn(T)
    return 0.5 * Y + 0.5 * Z + 0.5 * hull_vals(T, Y - Z) + 0.5 * hull_vals(T, Z - Y)


if __name__ == "__main__":
    Ns = [int(x) for x in sys.argv[1:]] or [2000, 20000, 200000]
    for N in Ns:
        T = grid(N)
        i = int(np.argmin(np.abs(T - 0.5)))
        assert T[i] == 0.5
        uv = UVn(T)
        fj = FJ(T, 1 - 0.189953475893, 0.189953475893)
        fjp = FJ(T, 1 - 0.189986556858845, 0.189986556858845)
        fgk = FGK(T, 0.17311456, 0.79310944)
        fgkp = FGK(T, 0.173670782688446, 0.793595839081043)
        # also check symmetry / argmax at 1/2 on the grid
        print("N=%7d nodes=%7d  UV=%.12f  FJ(author)=%.12f  FJ(Geng)=%.12f  FGK(author)=%.12f  FGK(GLN)=%.12f"
              % (N, len(T), uv[i], fj[i], fjp[i], fgk[i], fgkp[i]))
        print("    argmax_t FJ = %.6f, argmax_t FGK = %.6f, max-F(1/2): FJ %.2e FGK %.2e"
              % (T[np.argmax(fj)], T[np.argmax(fgk)], fj.max() - fj[i], fgk.max() - fgk[i]))
