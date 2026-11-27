"""
Independent reviewer re-implementation (not derived from the author's code).

Channel (GEA arXiv:1006.5166v2, proof of Claim 1): X->Y1 BSC(0.3); Y1->Y2 with
K(0|0)=0.6, K(1|0)=0.4, K(0|1)=0, K(1|1)=1.  All channel entries and alpha are exact
Fractions; the X->Y2 marginal is computed here by composition.

(1) capacity side: exact-rational superposition point, mpmath interval value of
    I(X;Y1|V) + alpha I(V;Y2) at 120 bits.
(2) Marton-without-W side: rigorous upper bound of
       G(p,f) = I(U;Y1) + alpha I(V;Y2) - I(U;V),  (U,V) ~ p on {0,1}^2, X = f(U,V)
    for ALL 16 maps f (no orbit reduction), over the whole 3-simplex, by simplicial
    branch-and-bound with the DC bound (tangent cross-entropy for concave entropy terms,
    vertex max for convex terms).  Vertices are exact Fractions; every accepted leaf is
    evaluated in mpmath interval arithmetic.  Threshold tau chosen by the reviewer.
"""
import sys, itertools, time
from fractions import Fraction as Fr
from mpmath import iv, mpf
import numpy as np

ALPHA = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(47, 20)
TAU = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(1201, 10000)
iv.prec = 100

WY1 = {(x, y): (Fr(7, 10) if x == y else Fr(3, 10)) for x in (0, 1) for y in (0, 1)}
K = {(0, 0): Fr(6, 10), (0, 1): Fr(4, 10), (1, 0): Fr(0), (1, 1): Fr(1)}
WY2 = {(x, z): sum(WY1[(x, y)] * K[(y, z)] for y in (0, 1)) for x in (0, 1) for z in (0, 1)}
assert WY2[(0, 0)] == Fr(42, 100) and WY2[(1, 0)] == Fr(18, 100)

def ivf(q):  # rigorous enclosure of a Fraction
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)

LN2 = iv.log(iv.mpf(2))

def iv_ent(qs):
    s = iv.mpf(0)
    for q in qs:
        if q == 0:
            continue
        t = ivf(q)
        s -= t * iv.log(t)
    return s / LN2

def iv_xent(qs, rs):
    s = iv.mpf(0)
    for q, r in zip(qs, rs):
        if q == 0:
            continue
        assert r != 0
        s -= ivf(q) * iv.log(ivf(r))
    return s / LN2

# ---------------------------------------------------------------- capacity side
def cap_point(a, s0, s1, alpha):
    """P(V=1)=a, P(X=1|V=v)=s_v (Fractions). Returns intervals R1, R2, R1+alpha R2."""
    def py1(s):  # law of Y1 given X~Bern(s)
        return [sum(((1 - s) if x == 0 else s) * WY1[(x, y)] for x in (0, 1)) for y in (0, 1)]
    def py2(s):
        return [sum(((1 - s) if x == 0 else s) * WY2[(x, z)] for x in (0, 1)) for z in (0, 1)]
    HY1gX = iv_ent([WY1[(0, 0)], WY1[(0, 1)]])
    R1 = ivf(1 - a) * iv_ent(py1(s0)) + ivf(a) * iv_ent(py1(s1)) - HY1gX
    sbar = (1 - a) * s0 + a * s1
    R2 = iv_ent(py2(sbar)) - (ivf(1 - a) * iv_ent(py2(s0)) + ivf(a) * iv_ent(py2(s1)))
    return R1, R2, R1 + ivf(alpha) * R2

# ---------------------------------------------------------------- Marton side
def marginals(p, f):
    """p: dict (u,v)->Fraction (or float). Returns the six distributions as lists."""
    puy = [[0, 0], [0, 0]]; pvz = [[0, 0], [0, 0]]
    for (u, v), w in p.items():
        x = f[(u, v)]
        for y in (0, 1):
            puy[u][y] += w * WY1[(x, y)]
            pvz[v][y] += w * WY2[(x, y)]
    Y1 = [puy[0][y] + puy[1][y] for y in (0, 1)]
    Y2 = [pvz[0][z] + pvz[1][z] for z in (0, 1)]
    V = [p[(0, v)] + p[(1, v)] for v in (0, 1)]
    UV = [p[(u, v)] for u in (0, 1) for v in (0, 1)]
    UY = [puy[u][y] for u in (0, 1) for y in (0, 1)]
    VZ = [pvz[v][z] for v in (0, 1) for z in (0, 1)]
    return dict(Y1=Y1, Y2=Y2, V=V, UV=UV, UY=UY, VZ=VZ)

CELLS = [(0, 0), (0, 1), (1, 0), (1, 1)]

def coeffs(alpha):
    # G = H(Y1) + a H(Y2) + (a-1) H(V) + H(UV) - H(UY1) - a H(VY2)
    conc = [(Fr(1), 'Y1'), (alpha, 'Y2'), (alpha - 1, 'V'), (Fr(1), 'UV')]
    conv = [(Fr(1), 'UY'), (alpha, 'VZ')]
    assert all(c >= 0 for c, _ in conc)
    return conc, conv

def float_bound(verts, f, alpha):
    conc, conv = coeffs(alpha)
    fl = lambda d: {k: [float(t) for t in v] for k, v in d.items()}
    c = {cell: sum(float(w[cell]) for w in verts) / len(verts) for cell in CELLS}
    mc = fl(marginals(c, f))
    best = -1e9
    for w in verts:
        mw = fl(marginals({k: float(v) for k, v in w.items()}, f))
        tot = 0.0
        for a, key in conc:
            tot += float(a) * -sum(q * np.log2(r) for q, r in zip(mw[key], mc[key]) if q > 0)
        for a, key in conv:
            tot -= float(a) * -sum(q * np.log2(q) for q in mw[key] if q > 0)
        best = max(best, tot)
    return best

def iv_bound(verts, f, alpha):
    conc, conv = coeffs(alpha)
    n = len(verts)
    c = {cell: sum(w[cell] for w in verts) / n for cell in CELLS}   # exact Fractions
    mc = marginals(c, f)
    ub = None
    for w in verts:
        mw = marginals(w, f)
        tot = iv.mpf(0)
        for a, key in conc:
            tot += ivf(a) * iv_xent(mw[key], mc[key])
        for a, key in conv:
            tot -= ivf(a) * iv_ent(mw[key])
        ub = tot.b if ub is None else max(ub, tot.b)
    return ub

def certify(f, alpha, tau):
    root = [{cell: Fr(int(cell == e)) for cell in CELLS} for e in CELLS]
    stack = [root]; leaves = 0; worst = mpf('-inf'); visited = 0
    tau_f = float(tau)
    while stack:
        S = stack.pop(); visited += 1
        b = float_bound(S, f, alpha)
        if b <= tau_f - 1e-6:
            ub = iv_bound(S, f, alpha)          # rigorous
            if ub <= ivf(tau).a:
                leaves += 1; worst = max(worst, ub); continue
        # bisect the longest edge (L1)
        bi, bj, bd = None, None, Fr(-1)
        for i in range(len(S)):
            for j in range(i + 1, len(S)):
                d = sum(abs(S[i][k] - S[j][k]) for k in CELLS)
                if d > bd:
                    bi, bj, bd = i, j, d
        if bd < Fr(1, 2**30):
            raise RuntimeError(f'cannot certify f={f}')
        m = {k: (S[bi][k] + S[bj][k]) / 2 for k in CELLS}
        S1 = list(S); S1[bi] = m
        S2 = list(S); S2[bj] = m
        stack.append(S1); stack.append(S2)
    return leaves, visited, worst

if __name__ == '__main__':
    alpha, tau = ALPHA, TAU
    print(f'alpha = {alpha} = {float(alpha)}, tau = {tau} = {float(tau)}')
    print('WY2 =', {k: str(v) for k, v in WY2.items()})
    t0 = time.time()
    for bits in itertools.product((0, 1), repeat=4):
        f = dict(zip(CELLS, bits))
        L, V, w = certify(f, alpha, tau)
        print(f'  f={bits}: {L} leaves, {V} visited, max interval UB {float(mpf(w)):.9f} <= tau  [{time.time()-t0:.0f}s]',
              flush=True)
    print(f'ALL 16 MAPS CERTIFIED: S_alpha <= {float(tau)}')
