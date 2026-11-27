#!/usr/bin/env python3
"""
Rigorous (interval-arithmetic + exact-rational) certificates for sum-rate bounds on the
binary skew-symmetric broadcast channel (BSSC).

Attempt file: attempts/binary-skew-symmetric-bc/2026-11-26-claude-opus-5-5-certified-bounds.md

Conventions (bits).  t = P(X = 1).  Receiver 1 ("Y") is the Z-channel 0 -> 0, 1 -> Unif{0,1};
receiver 2 ("Z") is the mirrored Z-channel 1 -> 1, 0 -> Unif{0,1}  (the catalog's W_BSSC):
    I_Y(t) = h(t/2) - t,          I_Z(t) = h((1-t)/2) - (1-t).
A binary auxiliary receiver J is given by a0 = P(J=0|X=0), a1 = P(J=0|X=1):
    I_J(t) = h(a0 + (a1-a0) t) - (1-t) h(a0) - t h(a1).
C[.] denotes the upper concave envelope on [0,1].

Certified quantities (all evaluated at t = 1/2, which is the global max over t by
concavity + skew symmetry, see the attempt file):
  UV  :  1/2 I_Y + 1/2 I_Z + 1/2 C[I_Y - I_Z] + 1/2 C[I_Z - I_Y]
  J   :  1/2 I_Y + 1/2 I_Z + C[ C[I_J - I_Y] + 1/2 (I_Y - I_J) ] + C[ C[I_J - I_Z] + 1/2 (I_Z - I_J) ]
         (sigma = 1, gamma = 1/2 in Geng's Theorem 1; J a BSC so the expression is symmetric)
  GK  :  1/2 I_Y + 1/2 I_Z + C[ 1/2 (I_Y - I_G) + C[I_G - I_Y] ] + C[ 1/2 (I_Z - I_K) + C[I_K - I_Z] ]
         + 1/2 C[I_G - I_K] + 1/2 C[I_K - I_G]      (K = skew mirror of G)
  Marton (lower bound, explicit randomized-time-division distribution):
         h(1/4) + 1/2 h(a/2) - 1/2 h((1-a)/2) - a      at a rational a.

Method for an upper bound on C[f] (f a combination of binary entropies of affine maps):
  * rational grid t_0 = 0 < ... < t_M = 1 (symmetric, refined near the end points);
  * at each node an outward-rounded interval enclosure of f(t_k) (mpmath.iv, 120-bit);
  * on each cell either (a) the interpolation error bound  f - interp <= w^2/8 * max(0, -inf f'')
    with inf f'' from an interval enclosure of f'' on the cell, or (b) a crude bound
    sup_cell f <= sup of an interval enclosure of f on the cell (monotone pieces of h);
  * node values are raised so that the piecewise-linear interpolant dominates f on every cell;
  * the upper concave hull of the raised nodes is computed EXACTLY in rational arithmetic;
    it is a concave majorant of f, hence majorizes C[f].
  For nested envelopes C[C[f] + g] the inner hull H1 is linear on every cell (its vertices
  are grid nodes), so (H1 + g)'' = g'' inside cells and the same method applies.
  All node values are rounded UP to a dyadic grid of 2^-140 to keep denominators small.

Usage:   python bssc_certify.py [K] [modes...]   (K = grid parameter, default 8000;
         modes among marton uv j gk jlow gklow; env BSSC_ALPHA, BSSC_G0, BSSC_G1 set the
         auxiliary channels, see the attempt file for the values used)
"""
import sys
import time
from fractions import Fraction as Fr
import math

from mpmath import iv, mpf
from mpmath.libmp import to_rational

iv.prec = 120
LN2 = iv.log(iv.mpf(2))
ROUND = Fr(1, 2 ** 140)          # dyadic resolution for rounding stored values up
MARGIN = Fr(1, 10 ** 30)         # extra absolute safety margin added to every enclosure


# ----------------------------------------------------------------------------------------
# interval helpers
# ----------------------------------------------------------------------------------------
def ivq(q):
    """Thin interval enclosing the rational q."""
    q = Fr(q)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _raw_to_fr(raw):
    p, q = to_rational(raw)
    return Fr(p, q)


def up(x):
    """Rational upper bound (rounded up to ROUND) of an interval x, plus MARGIN."""
    b = _raw_to_fr(x._mpi_[1]) + MARGIN
    return roundup(b)


def lo(x):
    """Rational lower bound (rounded down to ROUND) of an interval x, minus MARGIN."""
    a = _raw_to_fr(x._mpi_[0]) - MARGIN
    return rounddown(a)


def roundup(q):
    return Fr(math.ceil(q / ROUND)) * ROUND


def rounddown(q):
    return Fr(math.floor(q / ROUND)) * ROUND


def h_point(s):
    """Interval enclosure of the binary entropy (bits) at rational s in [0,1]."""
    s = Fr(s)
    if s == 0 or s == 1:
        return iv.mpf(0)
    S = ivq(s)
    T = ivq(1 - s)
    return -(S * iv.log(S) + T * iv.log(T)) / LN2


def h_range(slo, shi):
    """Interval enclosure of {h(s): s in [slo, shi]} using monotonicity of h."""
    slo, shi = Fr(slo), Fr(shi)
    a, b = h_point(slo), h_point(shi)
    if shi <= Fr(1, 2):
        return iv.mpf([a.a, b.b])
    if slo >= Fr(1, 2):
        return iv.mpf([b.a, a.b])
    m = iv.mpf([min(a.a, b.a), 1])
    return m


def hpp_range(slo, shi):
    """Interval enclosure of h''(s) = -1/(ln2 s(1-s)) for s in [slo, shi]; None if unbounded."""
    slo, shi = Fr(slo), Fr(shi)
    if slo <= 0 or shi >= 1:
        return None
    qmin = min(slo * (1 - slo), shi * (1 - shi))
    qmax = Fr(1, 4) if (slo <= Fr(1, 2) <= shi) else max(slo * (1 - slo), shi * (1 - shi))
    # h'' in [-1/(ln2 qmin), -1/(ln2 qmax)]
    lower = -(iv.mpf(1) / (LN2 * ivq(qmin)))
    upper = -(iv.mpf(1) / (LN2 * ivq(qmax)))
    return iv.mpf([lower.a, upper.b])


# ----------------------------------------------------------------------------------------
# functions of t: const + lin*t + sum c * h(alpha + beta t)
# const, lin: intervals; c, alpha, beta: rationals
# ----------------------------------------------------------------------------------------
class Fn:
    def __init__(self, const=None, lin=None, terms=None):
        self.const = const if const is not None else iv.mpf(0)
        self.lin = lin if lin is not None else iv.mpf(0)
        self.terms = list(terms) if terms else []

    def __add__(self, o):
        return Fn(self.const + o.const, self.lin + o.lin, self.terms + o.terms)

    def scale(self, c):
        c = Fr(c)
        C = ivq(c)
        return Fn(self.const * C, self.lin * C, [(tc * c, a, b) for (tc, a, b) in self.terms])

    def __sub__(self, o):
        return self + o.scale(-1)

    def at(self, t):
        t = Fr(t)
        v = self.const + self.lin * ivq(t)
        for (c, a, b) in self.terms:
            v = v + ivq(c) * h_point(a + b * t)
        return v

    def on(self, tl, tr):
        tl, tr = Fr(tl), Fr(tr)
        v = self.const + self.lin * iv.mpf([ivq(tl).a, ivq(tr).b])
        for (c, a, b) in self.terms:
            s1, s2 = a + b * tl, a + b * tr
            v = v + ivq(c) * h_range(min(s1, s2), max(s1, s2))
        return v

    def d2on(self, tl, tr):
        tl, tr = Fr(tl), Fr(tr)
        v = iv.mpf(0)
        for (c, a, b) in self.terms:
            if b == 0:
                continue
            s1, s2 = a + b * tl, a + b * tr
            r = hpp_range(min(s1, s2), max(s1, s2))
            if r is None:
                return None
            v = v + ivq(c * b * b) * r
        return v


def I_Y():
    return Fn(lin=iv.mpf(-1), terms=[(Fr(1), Fr(0), Fr(1, 2))])


def I_Z():
    return Fn(const=iv.mpf(-1), lin=iv.mpf(1), terms=[(Fr(1), Fr(1, 2), Fr(-1, 2))])


def I_J(a0, a1):
    a0, a1 = Fr(a0), Fr(a1)
    h0, h1 = h_point(a0), h_point(a1)
    return Fn(const=-h0, lin=h0 - h1, terms=[(Fr(1), a0, a1 - a0)])


# ----------------------------------------------------------------------------------------
# grid
# ----------------------------------------------------------------------------------------
def make_grid(K, J=60):
    """Symmetric rational grid on [0,1]: t = sin^2(pi k / 2K) rounded to 2^-64, plus geometric
    refinement t_1 2^-j (j=1..J) next to 0 and 1."""
    assert K % 2 == 0
    half = []
    for k in range(K // 2 + 1):
        x = math.sin(math.pi * k / (2 * K)) ** 2
        q = Fr(round(x * 2 ** 64), 2 ** 64)
        half.append(q)
    half[0] = Fr(0)
    half[-1] = Fr(1, 2)
    # strictly increasing
    for i in range(1, len(half)):
        assert half[i] > half[i - 1]
    t1 = half[1]
    geo = [t1 / 2 ** j for j in range(J, 0, -1)]
    left = [Fr(0)] + geo + half[1:]
    right = [1 - q for q in reversed(left[:-1])]
    return left + right


# ----------------------------------------------------------------------------------------
# certified concave-majorant construction
# ----------------------------------------------------------------------------------------
def upper_hull(T, V):
    H = []
    for i in range(len(T)):
        while len(H) >= 2:
            i1, i2 = H[-2], H[-1]
            if (T[i2] - T[i1]) * (V[i] - V[i1]) >= (V[i2] - V[i1]) * (T[i] - T[i1]):
                H.pop()
            else:
                break
        H.append(i)
    return H


def hull_values(T, V):
    """Values at every node of the exact upper concave hull of (T, V), rounded up."""
    H = upper_hull(T, V)
    out = [None] * len(T)
    for j in range(len(H) - 1):
        i1, i2 = H[j], H[j + 1]
        slope = (V[i2] - V[i1]) / (T[i2] - T[i1])
        for i in range(i1, i2 + 1):
            out[i] = roundup(V[i1] + slope * (T[i] - T[i1]))
    out[H[-1]] = V[H[-1]]
    return out, H


def raised_nodes(T, base_vals, cell_e, cell_U):
    """Given node upper values base_vals (rationals) and per-cell options
    (a) curvature error e (rational or None) and (b) crude cell sup U (rational),
    return node values such that the PL interpolant dominates the function on each cell."""
    n = len(T)
    req = list(base_vals)
    for k in range(n - 1):
        e, U = cell_e[k], cell_U[k]
        opt_a = None if e is None else max(base_vals[k] + e, base_vals[k + 1] + e)
        if opt_a is not None and (U is None or opt_a <= U):
            req[k] = max(req[k], base_vals[k] + e)
            req[k + 1] = max(req[k + 1], base_vals[k + 1] + e)
        else:
            req[k] = max(req[k], U)
            req[k + 1] = max(req[k + 1], U)
    return req


def certified_env(T, f, outer_g=None, inner_vals=None):
    """If inner_vals is None: certified majorant (node values) of C[f].
    Else: certified majorant of C[P + outer_g] where P is the PL function through inner_vals
    (which must be linear on each cell, i.e. inner_vals come from hull_values on T)."""
    n = len(T)
    if inner_vals is None:
        fn = f
        base = [up(fn.at(t)) for t in T]
        cell_e, cell_U = [], []
        for k in range(n - 1):
            w = T[k + 1] - T[k]
            d2 = fn.d2on(T[k], T[k + 1])
            if d2 is None:
                cell_e.append(None)
            else:
                m = max(Fr(0), -lo(d2))
                cell_e.append(roundup(w * w / 8 * m))
            cell_U.append(up(fn.on(T[k], T[k + 1])))
    else:
        g = outer_g
        base = [inner_vals[i] + up(g.at(T[i])) for i in range(n)]
        cell_e, cell_U = [], []
        for k in range(n - 1):
            w = T[k + 1] - T[k]
            d2 = g.d2on(T[k], T[k + 1])
            if d2 is None:
                cell_e.append(None)
            else:
                m = max(Fr(0), -lo(d2))
                cell_e.append(roundup(w * w / 8 * m))
            cell_U.append(max(inner_vals[k], inner_vals[k + 1]) + up(g.on(T[k], T[k + 1])))
    V = raised_nodes(T, base, cell_e, cell_U)
    vals, H = hull_values(T, V)
    return vals, H


def hull_values_down(T, V):
    """Values at every node of the exact upper concave hull of (T, V), rounded DOWN."""
    H = upper_hull(T, V)
    out = [None] * len(T)
    for j in range(len(H) - 1):
        i1, i2 = H[j], H[j + 1]
        slope = (V[i2] - V[i1]) / (T[i2] - T[i1])
        for i in range(i1, i2 + 1):
            out[i] = rounddown(V[i1] + slope * (T[i] - T[i1]))
    out[H[-1]] = V[H[-1]]
    return out


def lower_env(T, f, outer_g=None, inner_vals=None):
    """Rigorous LOWER bounds at the nodes for C[f] (inner_vals None) or for C[P + g] with
    P <= C[f] given by inner_vals.  The hull of points lying on or below the graph of a
    function is a minorant of its concave envelope."""
    if inner_vals is None:
        V = [lo(f.at(t)) for t in T]
    else:
        V = [inner_vals[i] + lo(outer_g.at(T[i])) for i in range(len(T))]
    return hull_values_down(T, V)


def lower_J(T, a0, a1, sigma=Fr(1), gamma=Fr(1, 2)):
    Y, Z, J = I_Y(), I_Z(), I_J(a0, a1)
    in1 = lower_env(T, J.scale(sigma) - Y)
    out1 = lower_env(T, None, (Y - J).scale(sigma * gamma), in1)
    in2 = lower_env(T, J.scale(sigma) - Z)
    out2 = lower_env(T, None, (Z - J).scale(sigma * (1 - gamma)), in2)
    lin = lo(Y.at(HALF) * ivq(1 - sigma * gamma) + Z.at(HALF) * ivq(1 - sigma * (1 - gamma)))
    return lin + value_at(T, out1, HALF) + value_at(T, out2, HALF)


def lower_GK(T, g0, g1):
    g0, g1 = Fr(g0), Fr(g1)
    Y, Z = I_Y(), I_Z()
    G, K = I_J(g0, g1), I_J(1 - g1, 1 - g0)
    inA = lower_env(T, G - Y)
    outA = lower_env(T, None, (Y - G).scale(HALF), inA)
    inB = lower_env(T, K - Z)
    outB = lower_env(T, None, (Z - K).scale(HALF), inB)
    c1 = lower_env(T, G - K)
    c2 = lower_env(T, K - G)
    lin = lo((Y.at(HALF) + Z.at(HALF)) * ivq(HALF))
    return (lin + value_at(T, outA, HALF) + value_at(T, outB, HALF)
            + (value_at(T, c1, HALF) + value_at(T, c2, HALF)) / 2)


def value_at(T, vals, p):
    i = T.index(Fr(p))
    return vals[i]


def fmt(q, digits=12):
    """Decimal string rounded UP."""
    s = math.ceil(q * 10 ** digits)
    return "%d.%0*d" % (s // 10 ** digits, digits, s % 10 ** digits)


def fmt_down(q, digits=12):
    s = math.floor(q * 10 ** digits)
    return "%d.%0*d" % (s // 10 ** digits, digits, s % 10 ** digits)


HALF = Fr(1, 2)


def cert_UV(T):
    Y, Z = I_Y(), I_Z()
    v1, _ = certified_env(T, Y - Z)
    v2, _ = certified_env(T, Z - Y)
    lin = up((Y.at(HALF) + Z.at(HALF)) * ivq(HALF))
    return lin + (value_at(T, v1, HALF) + value_at(T, v2, HALF)) / 2


def cert_J(T, a0, a1, sigma=Fr(1), gamma=Fr(1, 2)):
    Y, Z, J = I_Y(), I_Z(), I_J(a0, a1)
    f1 = J.scale(sigma) - Y
    g1 = (Y - J).scale(sigma * gamma)
    f2 = J.scale(sigma) - Z
    g2 = (Z - J).scale(sigma * (1 - gamma))
    in1, _ = certified_env(T, f1)
    out1, H1 = certified_env(T, None, outer_g=g1, inner_vals=in1)
    in2, _ = certified_env(T, f2)
    out2, H2 = certified_env(T, None, outer_g=g2, inner_vals=in2)
    lin = up(Y.at(HALF) * ivq(1 - sigma * gamma) + Z.at(HALF) * ivq(1 - sigma * (1 - gamma)))
    return lin + value_at(T, out1, HALF) + value_at(T, out2, HALF)


def cert_GK(T, g0, g1):
    """G = (g0, g1) paired with receiver Y (= I_Y); K = skew mirror (1-g1, 1-g0) paired with Z."""
    g0, g1 = Fr(g0), Fr(g1)
    Y, Z = I_Y(), I_Z()
    G, K = I_J(g0, g1), I_J(1 - g1, 1 - g0)
    inA, _ = certified_env(T, G - Y)
    outA, _ = certified_env(T, None, outer_g=(Y - G).scale(HALF), inner_vals=inA)
    inB, _ = certified_env(T, K - Z)
    outB, _ = certified_env(T, None, outer_g=(Z - K).scale(HALF), inner_vals=inB)
    c1, _ = certified_env(T, G - K)
    c2, _ = certified_env(T, K - G)
    lin = up((Y.at(HALF) + Z.at(HALF)) * ivq(HALF))
    return (lin + value_at(T, outA, HALF) + value_at(T, outB, HALF)
            + (value_at(T, c1, HALF) + value_at(T, c2, HALF)) / 2)


def cert_marton_lower(a):
    """Rigorous lower bound on the RTD sum rate h(1/4) + h(a/2)/2 - h((1-a)/2)/2 - a."""
    a = Fr(a)
    v = h_point(Fr(1, 4)) + h_point(a / 2) * ivq(HALF) - h_point((1 - a) / 2) * ivq(HALF) - ivq(a)
    return lo(v), v


def frac_of(x, bits=64):
    return Fr(round(x * 2 ** bits), 2 ** bits)


if __name__ == "__main__":
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    which = sys.argv[2:] if len(sys.argv) > 2 else ["marton", "uv", "j", "gk"]
    T = make_grid(K)
    print("grid nodes:", len(T), flush=True)
    t0 = time.time()
    if "marton" in which:
        import numpy as np
        xs = np.linspace(0.01, 0.99, 400001)
        hh = lambda p: -(p * np.log2(p) + (1 - p) * np.log2(1 - p))
        vals = hh(np.array([0.25]))[0] + hh(xs / 2) / 2 - hh((1 - xs) / 2) / 2 - xs
        a = frac_of(float(xs[np.argmax(vals)]))
        lb, enc = cert_marton_lower(a)
        print("Marton RTD sum rate at a = %.9f (exact rational %s):  >= %s"
              % (float(a), a, fmt_down(lb, 12)), flush=True)
    if "uv" in which:
        b = cert_UV(T)
        print("UV  sum-rate envelope form (18):  <= %s   [%.0fs]" % (fmt(b), time.time() - t0), flush=True)
    if "j" in which:
        import os
        alpha = frac_of(float(os.environ.get("BSSC_ALPHA", "0.189986556858845")))
        b = cert_J(T, 1 - alpha, alpha)
        print("J-bound (Geng Thm 1, sigma=1,gamma=1/2), J=BSC(%.15f): <= %s   [%.0fs]"
              % (float(alpha), fmt(b), time.time() - t0), flush=True)
    if "jlow" in which:
        alpha = frac_of(0.189986556858845)
        b = lower_J(T, 1 - alpha, alpha)
        print("J-bound value at Geng's published J=BSC(0.189986556858845) is >= %s   [%.0fs]"
              % (fmt_down(b), time.time() - t0), flush=True)
    if "gklow" in which:
        g0, g1 = frac_of(0.173670782688446), frac_of(0.793595839081043)
        b = lower_GK(T, g0, g1)
        print("GK-bound value at GLN's published (G,K) is >= %s   [%.0fs]"
              % (fmt_down(b), time.time() - t0), flush=True)
    if "gk" in which:
        import os
        g0 = frac_of(float(os.environ.get("BSSC_G0", "0.173670782688446")))
        g1 = frac_of(float(os.environ.get("BSSC_G1", "0.793595839081043")))
        b = cert_GK(T, g0, g1)
        print("GK-bound (16), G=(%.15f, %.15f), K=mirror: <= %s   [%.0fs]"
              % (float(g0), float(g1), fmt(b), time.time() - t0), flush=True)
