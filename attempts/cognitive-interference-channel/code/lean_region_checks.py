#!/usr/bin/env python3
"""Numerical checks of the frozen Lean region `rtdInnerBound`
(lean/InfoTheory/Problems/CognitiveInterferenceChannel.lean).

The constraint list below is a *literal* transcription of the Lean definition.
The joint pmf is an array with axes

    0:Q  1:U0  2:U1p  3:U2c  4:U2p  5:X1  6:X2  7:Y1  8:Y2

which is the Lean tuple
    z.1, z.2.1.1, z.2.1.2.1, z.2.1.2.2.1, z.2.1.2.2.2.1,
    z.2.1.2.2.2.2.1, z.2.1.2.2.2.2.2, z.2.2.1, z.2.2.2.
`cmi(A, B, C)` is `condMutualInfo` of the Lean triple map (A, B, C), computed as
H(A,C) + H(B,C) - H(A,B,C) - H(C), exactly as in `InfoTheory.condMutualInfo`.

Checks (all with fixed seeds; run: python3 lean_region_checks.py):
  T1  |X1| = 1: the Lean polytope is inside Marton's 4-inequality polytope with
      common auxiliary W = (U0, U2c, Q)  (Claim 2a of the attempt).
  T2  |X1| = 1: the embedding U0 = const, U2c = W, U1p = U1, U2p = U2 reproduces
      Marton's 4-inequality polytope (when I(U1;U2|W) <= I(U1;Y1|W)+I(U2;Y2|W))
      (Claim 2b).
  T3  the 'asymmetric clipper' deterministic cognitive IC of Rini-Tuninetti-Devroye
      Sec. X-A (indices swapped to the Lean convention): the capacity corner points
      (R1,R2) = (3,1) and (2,2) are in the Lean region (Claim 4).
  T4  Y1 = Y2 (very strong interference holds with equality): Lean region with
      U0 = X1, U2c = X2 attains the capacity region (Claim 4).
  T5  Y1 a degraded version of Y2, or Y1 = Y2 (better-cognitive-decoding regime):
      the corner points A, B of region (1) are dominated by Lean-feasible points
      (Claim 4).
  T6  general random instances: the Lean polytope lies inside the one-auxiliary
      outer bound with U = (U0, U1p, U2c, Q) (Claim 5).
"""
import itertools
import numpy as np
from scipy.optimize import linprog

AX = dict(Q=0, U0=1, U1p=2, U2c=3, U2p=4, X1=5, X2=6, Y1=7, Y2=8)
TOL = 1e-8


def H(p, axes):
    """Entropy (bits) of the marginal of p on the given axes."""
    axes = sorted(set(axes))
    other = tuple(i for i in range(p.ndim) if i not in axes)
    m = p.sum(axis=other) if other else p
    m = m[m > 0]
    return float(-(m * np.log2(m)).sum())


def cmi(p, A, B, C):
    return H(p, A + C) + H(p, B + C) - H(p, A + B + C) - H(p, C)


def lean_terms(p):
    """Every information term of `rtdInnerBound`, transcribed literally."""
    Q, U0, U1p, U2c, U2p, X1, X2, Y1, Y2 = range(9)
    t = {}
    t['bin2c'] = cmi(p, [U2c], [X1], [U0, Q])
    t['bin2p'] = cmi(p, [U2p], [X1], [U0, U2c, Q])
    t['bin12p'] = cmi(p, [U1p], [U2p], [U0, X1, U2c, Q])
    t['bin2cp'] = cmi(p, [U2c, U2p], [X1], [U0, Q])
    t['bin12cp'] = cmi(p, [U1p], [U2c, U2p], [U0, X1, Q])
    t['pen1'] = cmi(p, [X1, U1p], [U2c], [U0, Q])
    t['c6'] = cmi(p, [X1, U1p], [Y1], [U0, U2c, Q]) + t['pen1']
    t['c7'] = cmi(p, [X1, U1p, U2c], [Y1], [U0, Q]) + t['pen1']
    t['c8'] = cmi(p, [U0, X1, U1p, U2c], [Y1], [Q]) + t['pen1']
    t['c9'] = cmi(p, [U2p], [Y2], [U0, U2c, Q])
    t['c10'] = cmi(p, [U2c, U2p], [Y2], [U0, Q])
    t['c11'] = cmi(p, [U0, U2c, U2p], [Y2], [Q])
    return t


# LP variables: r1c r1p r2c r2p rp1p rp2c rp2p
def lean_lp(t):
    A, b = [], []
    def le(coef, rhs):
        A.append(coef); b.append(rhs)
    def ge(coef, rhs):
        A.append([-c for c in coef]); b.append(-rhs)
    ge([0, 0, 0, 0, 0, 1, 0], t['bin2c'])
    ge([0, 0, 0, 0, 0, 0, 1], t['bin2p'])
    ge([0, 0, 0, 0, 1, 1, 0], t['pen1'])
    ge([0, 0, 0, 0, 1, 0, 1], t['bin2p'] + t['bin12p'])
    ge([0, 0, 0, 0, 1, 1, 1], t['bin2cp'] + t['bin12cp'])
    le([0, 1, 0, 0, 1, 0, 0], t['c6'])
    le([0, 1, 1, 0, 1, 1, 0], t['c7'])
    le([1, 1, 1, 0, 1, 1, 0], t['c8'])
    le([0, 0, 0, 1, 0, 0, 1], t['c9'])
    le([0, 0, 1, 1, 0, 1, 1], t['c10'])
    le([1, 0, 1, 1, 0, 1, 1], t['c11'])
    return np.array(A, float), np.array(b, float)


def lean_support(t, lam):
    A, b = lean_lp(t)
    c = -np.array([lam, lam, 1 - lam, 1 - lam, 0, 0, 0])
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * 7, method='highs')
    return -res.fun if res.status == 0 else -np.inf


def lean_feasible(t, R1, R2):
    A, b = lean_lp(t)
    Aeq = np.array([[1, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0]], float)
    res = linprog(np.zeros(7), A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[R1, R2],
                  bounds=[(0, None)] * 7, method='highs')
    return res.status == 0


def poly_support(cons, lam):
    """support of {R >= 0 : a1 R1 + a2 R2 <= c for (a1, a2, c) in cons}"""
    A = np.array([[a1, a2] for a1, a2, _ in cons], float)
    b = np.array([c for _, _, c in cons], float)
    res = linprog(-np.array([lam, 1 - lam]), A_ub=A, b_ub=b,
                  bounds=[(0, None)] * 2, method='highs')
    return -res.fun if res.status == 0 else -np.inf


def joint(paux, W):
    """paux: array over (Q,U0,U1p,U2c,U2p,X1,X2); W: array (X1,X2,Y1,Y2)."""
    return paux[..., None, None] * W[None, None, None, None, None, :, :, :, :]


def rand_simplex(rng, shape):
    a = rng.exponential(size=shape)
    return a / a.sum()


def rand_channel(rng, nx1, nx2, ny1, ny2, sparse=0.0):
    W = rng.exponential(size=(nx1, nx2, ny1, ny2))
    if sparse:
        W *= (rng.random(W.shape) > sparse)
        W += 1e-12
    return W / W.sum(axis=(2, 3), keepdims=True)


LAMS = np.linspace(0.0, 1.0, 21)


def marton4(p):
    """Marton 4-inequality polytope with W = (U0,U2c,Q), U1 = U1p, U2 = U2p."""
    Q, U0, U1p, U2c, U2p, X1, X2, Y1, Y2 = range(9)
    Wv = [U0, U2c, Q]
    J1 = cmi(p, Wv + [U1p], [Y1], [])
    J2 = cmi(p, Wv + [U2p], [Y2], [])
    I1 = cmi(p, [U1p], [Y1], Wv)
    I2 = cmi(p, [U2p], [Y2], Wv)
    K = cmi(p, [U1p], [U2p], Wv)
    return [(1, 0, J1), (0, 1, J2), (1, 1, J1 + I2 - K), (1, 1, I1 + J2 - K)], (I1, I2, K)


def T1(rng, trials=60):
    worst = -np.inf
    for _ in range(trials):
        kQ, k0, k1, kc, k2 = rng.integers(1, 3), *rng.integers(1, 4, size=4)
        nx2, ny1, ny2 = rng.integers(2, 4, size=3)
        paux = rand_simplex(rng, (kQ, k0, k1, kc, k2, 1, nx2))
        W = rand_channel(rng, 1, nx2, ny1, ny2, sparse=0.3)
        p = joint(paux, W)
        t = lean_terms(p)
        cons, _ = marton4(p)
        for lam in LAMS:
            worst = max(worst, lean_support(t, lam) - poly_support(cons, lam))
    print(f"T1 |X1|=1: max over trials of [Lean support - Marton(W=(U0,U2c,Q)) support] = {worst:.2e} (expect <= 0)")
    return worst <= 1e-7


def embed_marton(pw, W):
    """pw over (W,U1,U2,X2) -> Lean aux array with Q=U0=const, U2c=W, U1p=U1, U2p=U2, X1 const."""
    kw, k1, k2, nx2 = pw.shape
    paux = np.zeros((1, 1, k1, kw, k2, 1, nx2))
    paux[0, 0, :, :, :, 0, :] = np.transpose(pw, (1, 0, 2, 3))
    return joint(paux, W)


def T2(rng, trials=60):
    worst, nk = 0.0, 0
    for _ in range(trials):
        kw, k1, k2 = rng.integers(1, 4, size=3)
        nx2, ny1, ny2 = rng.integers(2, 4, size=3)
        pw = rand_simplex(rng, (kw, k1, k2, nx2))
        W = rand_channel(rng, 1, nx2, ny1, ny2, sparse=0.3)
        p = embed_marton(pw, W)
        t = lean_terms(p)
        cons, (I1, I2, K) = marton4(p)
        if K > I1 + I2:
            continue
        nk += 1
        for lam in LAMS:
            worst = max(worst, abs(lean_support(t, lam) - poly_support(cons, lam)))
    print(f"T2 |X1|=1 embedding: {nk} instances with K<=I1+I2, max |Lean - Marton4| support gap = {worst:.2e} (expect 0)")
    return worst <= 1e-7


def T3():
    # RTD Sec. X-A in RTD indexing: X1c in Z4 (cognitive), X2p in Z8 (primary),
    # Ycog = X1c + X2p mod 4, Yprim = 1{2,3}(X1c) + X2p mod 8.
    # Lean indexing: X1 = X2p (primary, 8), X2 = X1c (cognitive, 4),
    # Y1 = Yprim (8 values), Y2 = Ycog (4 values).
    nx1, nx2, ny1, ny2 = 8, 4, 8, 4
    W = np.zeros((nx1, nx2, ny1, ny2))
    for x1 in range(nx1):
        for x2 in range(nx2):
            y1 = ((1 if x2 in (2, 3) else 0) + x1) % 8
            y2 = (x2 + x1) % 4
            W[x1, x2, y1, y2] = 1.0
    ok = True
    for name, px2, target in [("(3,1)", [0.5, 0.5, 0, 0], (3.0, 1.0)),
                              ("(2,2)", [0.25] * 4, (2.0, 2.0))]:
        # semi-deterministic embedding: U0 = U2c = const, U1p = Y1 (copy), U2p = Y2 (copy)
        paux = np.zeros((1, 1, ny1, 1, ny2, nx1, nx2))
        for x1 in range(nx1):
            for x2 in range(nx2):
                pr = (1 / 8) * px2[x2]
                if pr == 0:
                    continue
                y1 = int(np.nonzero(W[x1, x2].sum(axis=1))[0][0])
                y2 = int(np.nonzero(W[x1, x2].sum(axis=0))[0][0])
                paux[0, 0, y1, 0, y2, x1, x2] += pr
        t = lean_terms(joint(paux, W))
        f = lean_feasible(t, *target)
        f_out = lean_feasible(t, target[0] + 0.01, target[1] + 0.01)
        print(f"T3 clipper: capacity corner {name} Lean-feasible: {f}; (+0.01,+0.01) feasible: {f_out}")
        ok &= f and not f_out
    return ok


def T4(rng, trials=30):
    worst = 0.0
    for _ in range(trials):
        nx1, nx2, ny = rng.integers(2, 4, size=3)
        Wm = rng.exponential(size=(nx1, nx2, ny)); Wm /= Wm.sum(axis=2, keepdims=True)
        W = np.zeros((nx1, nx2, ny, ny))
        for y in range(ny):
            W[:, :, y, y] = Wm[:, :, y]
        px = rand_simplex(rng, (nx1, nx2))
        # Lean config: U0 = X1 (copy), U2c = X2 (copy)
        paux = np.zeros((1, nx1, 1, nx2, 1, nx1, nx2))
        for a in range(nx1):
            for c in range(nx2):
                paux[0, a, 0, c, 0, a, c] = px[a, c]
        p = joint(paux, W)
        t = lean_terms(p)
        Q, U0, U1p, U2c, U2p, X1, X2, Y1, Y2 = range(9)
        cap = [(0, 1, cmi(p, [X2], [Y2], [X1])), (1, 1, cmi(p, [X1, X2], [Y1], []))]
        for lam in LAMS:
            worst = max(worst, abs(lean_support(t, lam) - poly_support(cap, lam)))
    print(f"T4 Y1=Y2: max |Lean(U0=X1,U2c=X2) - capacity polytope| support gap = {worst:.2e} (expect 0)")
    return worst <= 1e-7


def T5(rng, trials=40):
    """Y1 = degraded(Y2) or Y1 = Y2 (both in the BCD regime): corners of region (1)
    are dominated by Lean points."""
    bad = 0
    nA_direct = 0
    for _ in range(trials):
        nx1, nx2, nu, ny2, ny1 = 2, 2, 2, 3, 2
        W2 = rng.exponential(size=(nx1, nx2, ny2)); W2 /= W2.sum(axis=2, keepdims=True)
        if _ % 2 == 0:   # Y1 a physically degraded version of Y2
            D = rng.exponential(size=(ny2, ny1)); D /= D.sum(axis=1, keepdims=True)
        else:            # Y1 = Y2 (BCD holds with equality; exercises the direct branch)
            ny1 = ny2; D = np.eye(ny2)
        W = W2[:, :, None, :] * D.T[None, None, :, :]      # (x1,x2,y1,y2)
        pux = rand_simplex(rng, (nu, nx1, nx2))
        # quantities of region (1) for this p(u,x1,x2)
        paux0 = np.zeros((1, nu, 1, 1, 1, nx1, nx2)); paux0[0, :, 0, 0, 0] = pux
        p0 = joint(paux0, W)  # U0 slot holds U here, used only to evaluate (1)
        Q, U0, U1p, U2c, U2p, X1, X2, Y1, Y2 = range(9)
        IX1U_Y1 = cmi(p0, [X1, U0], [Y1], [])
        IX2_Y2_X1 = cmi(p0, [X2], [Y2], [X1])
        IX2_Y2_X1U = cmi(p0, [X2], [Y2], [X1, U0])
        IU_Y2_X1 = cmi(p0, [U0], [Y2], [X1])
        IU_Y1_X1 = cmi(p0, [U0], [Y1], [X1])
        IX1_Y1 = cmi(p0, [X1], [Y1], [])
        B = (IX1U_Y1, IX2_Y2_X1U)
        A = (IX1U_Y1 - IU_Y2_X1, IX2_Y2_X1)
        # Config B: U0 = (X1,U), U2p = X2
        pB = np.zeros((1, nu * nx1, 1, 1, nx2, nx1, nx2))
        # Config A: U0 = X1, U2c = U, U2p = X2
        pA = np.zeros((1, nx1, 1, nu, nx2, nx1, nx2))
        # Config A0: U0 = X1, U2p = X2
        pA0 = np.zeros((1, nx1, 1, 1, nx2, nx1, nx2))
        for u, a, c in itertools.product(range(nu), range(nx1), range(nx2)):
            pB[0, u * nx1 + a, 0, 0, c, a, c] += pux[u, a, c]
            pA[0, a, 0, u, c, a, c] += pux[u, a, c]
            pA0[0, a, 0, 0, c, a, c] += pux[u, a, c]
        tB, tA, tA0 = (lean_terms(joint(x, W)) for x in (pB, pA, pA0))
        okB = lean_feasible(tB, *B)
        if IU_Y1_X1 >= IU_Y2_X1 - 1e-12 and A[0] >= 0:
            okA = lean_feasible(tA, *A); nA_direct += 1
        else:
            okA = lean_feasible(tA0, IX1_Y1, IX2_Y2_X1) and (A[0] <= IX1_Y1 + 1e-12)
        bad += (not okB) + (not okA)
    print(f"T5 degraded Y1 / Y1=Y2: corner failures = {bad} over {trials} distributions "
          f"(corner A reached directly in {nA_direct} cases, otherwise via A0) (expect 0)")
    return bad == 0


def T6(rng, trials=60):
    worst = -np.inf
    for _ in range(trials):
        kQ = rng.integers(1, 3)
        k0, k1, kc, k2 = rng.integers(1, 3, size=4)
        nx1, nx2, ny1, ny2 = rng.integers(2, 3, size=4)
        paux = rand_simplex(rng, (kQ, k0, k1, kc, k2, nx1, nx2))
        W = rand_channel(rng, nx1, nx2, ny1, ny2, sparse=0.3)
        p = joint(paux, W)
        t = lean_terms(p)
        Q, U0, U1p, U2c, U2p, X1, X2, Y1, Y2 = range(9)
        U = [Q, U0, U1p, U2c]
        ob = [(1, 0, cmi(p, U + [X1], [Y1], [])),
              (0, 1, cmi(p, [X2], [Y2], [X1])),
              (1, 1, cmi(p, U + [X1], [Y1], []) + cmi(p, [X2], [Y2], U + [X1]))]
        for lam in LAMS:
            worst = max(worst, lean_support(t, lam) - poly_support(ob, lam))
    print(f"T6 general: max [Lean support - one-aux outer bound support] = {worst:.2e} (expect <= 0)")
    return worst <= 1e-7


if __name__ == '__main__':
    rng = np.random.default_rng(20261126)
    results = dict(T1=T1(rng), T2=T2(rng), T3=T3(), T4=T4(rng), T5=T5(rng), T6=T6(rng))
    print("ALL PASS" if all(results.values()) else f"FAILURES: {results}")
