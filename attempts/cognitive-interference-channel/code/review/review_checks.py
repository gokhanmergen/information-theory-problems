# Reviewer checks R1-R4 (2026-11-27): literal Lean projections vs the author's lean_terms, both
# Claim-2 Fourier-Motzkin branches, and the Claim-7b configuration; seed 271127 (fixed below).
# Run: python3 review_checks.py [path/to/lean_region_checks.py]   (default ../lean_region_checks.py)
# Runtime: about 1 s; prints ALL PASS (output in review_checks.out). Needs numpy, scipy.
"""Independent reviewer checks for cognitive-interference-channel (commit 17947f8).

R1  Mechanical transcription: evaluate every condMutualInfo of `rtdInnerBound` by
    applying the Lean projections literally (nested right-associated tuples,
    z.2.1.2.2.1 etc.) and Lean's condMutualInfo formula on pushforward pmfs; compare
    with the author's hand-decoded `lean_terms`.
R2  Claim 2, branch K > I1+I2 (skipped by the author's T2): Marton polytope for p is
    inside the frozen polytope of the embedding U1p = U2p = const, U2c = W.
R3  Claim 2, branch K <= I1+I2, re-done with my own LP over (x, y, a, b) of the
    reduced system (not the author's LP): Marton polytope vertices are feasible.
R4  Claim 7b (semi-deterministic, Y2 = f(X1,X2)) with the attempt's own config
    (U0=U2c=const, U1p=U, U2p=Y2): both corners of the capacity pentagon for the same
    p(u,x1,x2) are frozen-feasible (author's T3 used a different config).
"""
import itertools, math, os, sys, importlib.util
import numpy as np
from scipy.optimize import linprog

CODE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), '..', 'lean_region_checks.py')
spec = importlib.util.spec_from_file_location("author", CODE)
author = importlib.util.module_from_spec(spec); spec.loader.exec_module(author)

# ---------- generic Lean-style evaluator over an explicit list of (z, prob) ----------
def ent(d):
    return -sum(v * math.log2(v) for v in d.values() if v > 0)

def pushforward(items, f):
    d = {}
    for z, pr in items:
        k = f(z); d[k] = d.get(k, 0.0) + pr
    return d

def lean_cmi(items, f):
    """InfoTheory.condMutualInfo (P.map f) with P = items, f z = (a, (b, c))."""
    P = pushforward(items, f)
    Pxz = {}; Pyz = {}; Pz = {}
    for (a, (b, c)), v in P.items():
        Pxz[(a, c)] = Pxz.get((a, c), 0) + v
        Pyz[(b, c)] = Pyz.get((b, c), 0) + v
        Pz[c] = Pz.get(c, 0) + v
    return ent(Pxz) + ent(Pyz) - ent(P) - ent(Pz)

# Lean projections; z = (q, ((u0, (u1p, (u2c, (u2p, (x1, x2))))), (y1, y2)))
fst = lambda t: t[0]; snd = lambda t: t[1]
def P(path):
    """path like '2.1.2.2.1' -> composition of .1/.2 projections (Lean semantics)."""
    def g(z):
        for s in path.split('.'):
            z = z[0] if s == '1' else z[1]
        return z
    return g
T = lambda a, b, c: (lambda z: (a(z), (b(z), c(z))))
tup = lambda *fs: (lambda z: tuple(f(z) for f in fs)) if len(fs) > 1 else fs[0]
def tupr(*fs):  # Lean (a, b, c) = (a, (b, c)) : right-nested
    if len(fs) == 1: return fs[0]
    return lambda z: (fs[0](z), tupr(*fs[1:])(z))

def lean_terms_literal(items):
    p = P
    t = {}
    t['bin2c'] = lean_cmi(items, T(p('2.1.2.2.1'), p('2.1.2.2.2.2.1'), tupr(p('2.1.1'), p('1'))))
    t['bin2p'] = lean_cmi(items, T(p('2.1.2.2.2.1'), p('2.1.2.2.2.2.1'), tupr(p('2.1.1'), p('2.1.2.2.1'), p('1'))))
    t['bin12p'] = lean_cmi(items, T(p('2.1.2.1'), p('2.1.2.2.2.1'),
                                    tupr(p('2.1.1'), p('2.1.2.2.2.2.1'), p('2.1.2.2.1'), p('1'))))
    t['bin2cp'] = lean_cmi(items, T(tupr(p('2.1.2.2.1'), p('2.1.2.2.2.1')), p('2.1.2.2.2.2.1'), tupr(p('2.1.1'), p('1'))))
    t['bin12cp'] = lean_cmi(items, T(p('2.1.2.1'), tupr(p('2.1.2.2.1'), p('2.1.2.2.2.1')),
                                     tupr(p('2.1.1'), p('2.1.2.2.2.2.1'), p('1'))))
    t['pen1'] = lean_cmi(items, T(tupr(p('2.1.2.2.2.2.1'), p('2.1.2.1')), p('2.1.2.2.1'), tupr(p('2.1.1'), p('1'))))
    t['c6'] = lean_cmi(items, T(tupr(p('2.1.2.2.2.2.1'), p('2.1.2.1')), p('2.2.1'),
                                tupr(p('2.1.1'), p('2.1.2.2.1'), p('1')))) + t['pen1']
    t['c7'] = lean_cmi(items, T(tupr(p('2.1.2.2.2.2.1'), p('2.1.2.1'), p('2.1.2.2.1')), p('2.2.1'),
                                tupr(p('2.1.1'), p('1')))) + t['pen1']
    t['c8'] = lean_cmi(items, T(tupr(p('2.1.1'), p('2.1.2.2.2.2.1'), p('2.1.2.1'), p('2.1.2.2.1')), p('2.2.1'),
                                p('1'))) + t['pen1']
    t['c9'] = lean_cmi(items, T(p('2.1.2.2.2.1'), p('2.2.2'), tupr(p('2.1.1'), p('2.1.2.2.1'), p('1'))))
    t['c10'] = lean_cmi(items, T(tupr(p('2.1.2.2.1'), p('2.1.2.2.2.1')), p('2.2.2'), tupr(p('2.1.1'), p('1'))))
    t['c11'] = lean_cmi(items, T(tupr(p('2.1.1'), p('2.1.2.2.1'), p('2.1.2.2.2.1')), p('2.2.2'), p('1')))
    return t

def items_from_array(parr):
    """author array axes (Q,U0,U1p,U2c,U2p,X1,X2,Y1,Y2) -> Lean nested tuples."""
    out = []
    for idx in zip(*np.nonzero(parr > 0)):
        q, u0, u1p, u2c, u2p, x1, x2, y1, y2 = map(int, idx)
        z = (q, ((u0, (u1p, (u2c, (u2p, (x1, x2))))), (y1, y2)))
        out.append((z, float(parr[idx])))
    return out

def R1(rng, trials=40):
    worst = 0.0
    for _ in range(trials):
        kQ, k0, k1, kc, k2 = rng.integers(1, 3, size=5)
        nx1, nx2, ny1, ny2 = rng.integers(1, 3, size=4) + 1
        paux = author.rand_simplex(rng, (kQ, k0, k1, kc, k2, nx1, nx2))
        W = author.rand_channel(rng, nx1, nx2, ny1, ny2)
        p = author.joint(paux, W)
        ta = author.lean_terms(p); tl = lean_terms_literal(items_from_array(p))
        worst = max(worst, max(abs(ta[k] - tl[k]) for k in ta))
    print(f"R1 literal-Lean vs author lean_terms: max |diff| over {trials} instances = {worst:.2e}")
    return worst < 1e-9

# ---------- Claim 2 checks ----------
def marton_quants(pw, Wbc):
    """pw over (W,U,V,X); Wbc over (X,Y1,Y2). returns J1,J2,I1,I2,K,IWY1,IWY2"""
    pj = pw[..., None, None] * Wbc[None, None, None, :, :, :]  # W U V X Y1 Y2
    def Hm(ax):
        other = tuple(i for i in range(6) if i not in ax)
        m = pj.sum(axis=other) if other else pj
        m = m[m > 0]; return float(-(m * np.log2(m)).sum())
    def I(A, B, C=()):
        return Hm(sorted(set(A + C))) + Hm(sorted(set(B + C))) - Hm(sorted(set(A + B + C))) - (Hm(sorted(set(C))) if C else 0.0)
    Wv, U, V, Y1, Y2 = (0,), (1,), (2,), (4,), (5,)
    return dict(J1=I(Wv + U, Y1), J2=I(Wv + V, Y2), I1=I(U, Y1, Wv), I2=I(V, Y2, Wv),
                K=I(U, V, Wv), IW1=I(Wv, Y1), IW2=I(Wv, Y2))

def marton_vertices(m):
    cons = [(1, 0, m['J1']), (0, 1, m['J2']), (1, 1, m['J1'] + m['I2'] - m['K']), (1, 1, m['I1'] + m['J2'] - m['K'])]
    cons += [(-1, 0, 0), (0, -1, 0)]
    V = []
    for (a1, b1, c1), (a2, b2, c2) in itertools.combinations(cons, 2):
        d = a1 * b2 - a2 * b1
        if abs(d) < 1e-12: continue
        x = (c1 * b2 - c2 * b1) / d; y = (a1 * c2 - a2 * c1) / d
        if all(a * x + b * y <= c + 1e-9 for a, b, c in cons):
            V.append((max(x, 0.0), max(y, 0.0)))
    return V

def frozen_feasible_from_pw(pw, Wbc, R, mode):
    kw, ku, kv, nx = pw.shape
    W = Wbc[None, :, :, :]  # X1 = Fin 1
    paux = np.zeros((1, 1, ku if mode == 'embed' else 1, kw, kv if mode == 'embed' else 1, 1, nx))
    for w, u, v, x in itertools.product(range(kw), range(ku), range(kv), range(nx)):
        if mode == 'embed':
            paux[0, 0, u, w, v, 0, x] += pw[w, u, v, x]
        else:  # U1p = U2p = const, U2c = W
            paux[0, 0, 0, w, 0, 0, x] += pw[w, u, v, x]
    t = author.lean_terms(author.joint(paux, W))
    return author.lean_feasible(t, *R)

def R2(rng, trials=400):
    n_hit, bad = 0, 0
    for _ in range(trials):
        kw, ku, kv, nx = 2, 2, 2, 2
        # make U,V strongly correlated given W, channel noisy, so K > I1 + I2
        pw = np.zeros((kw, ku, kv, nx))
        for w in range(kw):
            pwm = rng.random() * 0.5 + 0.25
            for u in range(ku):
                v = u  # V = U
                for x in range(nx):
                    pw[w, u, v, x] = 0.5 * pwm * (0.5 if w == 0 else 1) * rng.random()
        pw /= pw.sum()
        Wbc = author.rand_channel(rng, 1, nx, 2, 2)[0]
        Wbc = 0.6 * Wbc + 0.4 * 0.25  # extra noise
        m = marton_quants(pw, Wbc)
        if m['K'] <= m['I1'] + m['I2'] + 1e-9:
            continue
        n_hit += 1
        for R in marton_vertices(m):
            if not frozen_feasible_from_pw(pw, Wbc, (R[0] * (1 - 1e-9), R[1] * (1 - 1e-9)), 'alt'):
                bad += 1
            if R[0] + R[1] > min(m['IW1'], m['IW2']) + 1e-12:
                bad += 1
    print(f"R2 K>I1+I2 branch: {n_hit} instances, Marton vertices not covered by alt embedding = {bad}")
    return bad == 0 and n_hit > 0

def R3(rng, trials=150):
    n, bad = 0, 0
    for _ in range(trials):
        kw, ku, kv, nx = rng.integers(1, 4, size=3).tolist() + [int(rng.integers(2, 4))]
        pw = author.rand_simplex(rng, (kw, ku, kv, nx))
        Wbc = author.rand_channel(rng, 1, nx, int(rng.integers(2, 4)), int(rng.integers(2, 4)))[0]
        m = marton_quants(pw, Wbc)
        if m['K'] > m['I1'] + m['I2']:
            continue
        n += 1
        for R in marton_vertices(m):
            R = (R[0] * (1 - 1e-9), R[1] * (1 - 1e-9))
            # my own reduced system in (x, y, a, b) from the review derivation
            A = [[-1, 0, 1, 0], [0, 1, 1, 0], [0, -1, 0, 1], [1, 0, 0, 1], [0, 0, -1, -1], [1, 0, 0, 0], [0, 1, 0, 0]]
            b = [m['I1'] - R[0], m['J1'] - R[0], m['I2'] - R[1], m['J2'] - R[1], -m['K'], R[0], R[1]]
            res = linprog(np.zeros(4), A_ub=A, b_ub=b, bounds=[(0, None)] * 4, method='highs')
            ok_mine = res.status == 0
            ok_lean = frozen_feasible_from_pw(pw, Wbc, R, 'embed')
            bad += (not ok_mine) + (not ok_lean)
    print(f"R3 K<=I1+I2 branch: {n} instances, infeasible Marton vertices (my FM system / Lean LP) = {bad}")
    return bad == 0

# ---------- Claim 7b ----------
def R4(rng, trials=60):
    bad = 0
    for _ in range(trials):
        nx1, nx2, nu = int(rng.integers(2, 4)), int(rng.integers(2, 4)), int(rng.integers(2, 4))
        ny2 = int(rng.integers(2, 4)); ny1 = int(rng.integers(2, 4))
        f = rng.integers(0, ny2, size=(nx1, nx2))
        W = np.zeros((nx1, nx2, ny1, ny2))
        Wy1 = author.rand_channel(rng, nx1, nx2, ny1, 1)[..., 0]
        for a, c in itertools.product(range(nx1), range(nx2)):
            W[a, c, :, f[a, c]] = Wy1[a, c]
        pux = author.rand_simplex(rng, (nu, nx1, nx2))
        # quantities of the semi-deterministic capacity pentagon
        p0 = np.zeros((1, nu, 1, 1, 1, nx1, nx2)); p0[0, :, 0, 0, 0] = pux
        pj = author.joint(p0, W)
        Q, U0, U1p, U2c, U2p, X1, X2, Y1, Y2 = range(9)
        HY2_X1 = author.cmi(pj, [Y2], [Y2], [X1]); HY2_UX1 = author.cmi(pj, [Y2], [Y2], [X1, U0])
        IUX1_Y1 = author.cmi(pj, [U0, X1], [Y1], [])
        c_ = IUX1_Y1 + HY2_UX1
        corners = [(IUX1_Y1, HY2_UX1), (c_ - HY2_X1, HY2_X1) if c_ >= HY2_X1 else (0.0, c_)]
        # attempt's config: U0=U2c=const, U1p=U, U2p=Y2=f(X1,X2)
        paux = np.zeros((1, 1, nu, 1, ny2, nx1, nx2))
        for u, a, c in itertools.product(range(nu), range(nx1), range(nx2)):
            paux[0, 0, u, 0, f[a, c], a, c] += pux[u, a, c]
        t = author.lean_terms(author.joint(paux, W))
        for R in corners:
            if not author.lean_feasible(t, R[0] * (1 - 1e-9), R[1] * (1 - 1e-9)):
                bad += 1
    print(f"R4 semi-deterministic, attempt's config: infeasible capacity corners = {bad} over {trials} p")
    return bad == 0

if __name__ == '__main__':
    rng = np.random.default_rng(271127)
    res = dict(R1=R1(rng), R2=R2(rng), R3=R3(rng), R4=R4(rng))
    print("ALL PASS" if all(res.values()) else f"FAIL {res}")
