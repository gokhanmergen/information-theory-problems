# Reviewer check (2026-11-27): black-box test that the author's certified PL majorants
# (../bssc_certify.py) dominate their targets at random points, evaluated at 60 digits.
# Run: python3 majorant_test.py [K]   (default K = 400, the value quoted in the note)
# Runtime: about 2 s at K = 400. Needs mpmath.
# Black-box test of the author's majorant construction: the PL function through the certified
# node values must dominate the target function at random points (evaluated in mpmath, 60 digits).
import os, sys, random
from fractions import Fraction as Fr
import mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))  # author's code/
import bssc_certify as bc
mp.mp.dps = 60
random.seed(7)

def hb(p):
    p = mp.mpf(p)
    return mp.mpf(0) if p <= 0 or p >= 1 else -(p*mp.log(p, 2) + (1-p)*mp.log(1-p, 2))

def ev(fn, t):  # high-precision evaluation of an Fn at rational/float t
    t = mp.mpf(t.numerator) / t.denominator if isinstance(t, Fr) else mp.mpf(t)
    v = mp.make_mpf(fn.const._mpi_[0]) + mp.make_mpf(fn.lin._mpi_[0]) * t
    for (c, a, b) in fn.terms:
        v += mp.mpf(c.numerator)/c.denominator * hb(mp.mpf(a.numerator)/a.denominator + mp.mpf(b.numerator)/b.denominator * t)
    return v

def pl(T, V, t):
    import bisect
    k = max(0, min(len(T)-2, bisect.bisect_right(T, t) - 1))
    tl, tr = T[k], T[k+1]
    lam = (t - tl) / (tr - tl)
    return (1-lam)*V[k] + lam*V[k+1]

K = int(sys.argv[1]) if len(sys.argv) > 1 else 400
T = bc.make_grid(K)
Y, Z = bc.I_Y(), bc.I_Z()
g0, g1 = Fr(0.17311456).limit_denominator(10**12), Fr(0.79310944).limit_denominator(10**12)
G, Kc = bc.I_J(g0, g1), bc.I_J(1 - g1, 1 - g0)
worst = {}
def test(name, vals, target):
    w = None
    for k in range(len(T)-1):
        for _ in range(6):
            u = Fr(random.random())
            t = T[k] + u * (T[k+1] - T[k])
            m = mp.mpf(pl(T, vals, t).numerator) / pl(T, vals, t).denominator - target(t)
            if w is None or m < w[0]:
                w = (m, float(t))
    print("%-28s min(majorant - f) over %d samples = %s at t=%.3e" % (name, 6*(len(T)-1), mp.nstr(w[0], 5), w[1]))

inA, _ = bc.certified_env(T, G - Y)
test("C[G-Y] majorant", inA, lambda t: ev(G - Y, t))
outA, _ = bc.certified_env(T, None, outer_g=(Y - G).scale(Fr(1, 2)), inner_vals=inA)
test("C[C[G-Y]+(Y-G)/2] majorant", outA, lambda t: mp.mpf(pl(T, inA, t).numerator)/pl(T, inA, t).denominator + ev((Y - G).scale(Fr(1,2)), t))
c1, _ = bc.certified_env(T, G - Kc)
test("C[G-K] majorant", c1, lambda t: ev(G - Kc, t))
v1, _ = bc.certified_env(T, Y - Z)
test("C[Y-Z] majorant", v1, lambda t: ev(Y - Z, t))
# concavity of the certified hull output (not needed for soundness, informative)
def concave_violations(V):
    n = 0
    for k in range(1, len(T)-1):
        s1 = (V[k]-V[k-1])/(T[k]-T[k-1]); s2 = (V[k+1]-V[k])/(T[k+1]-T[k])
        if s2 > s1: n += 1
    return n
print("concavity violations after round-up of hull values: C[G-Y]:", concave_violations(inA), " outer:", concave_violations(outA))
