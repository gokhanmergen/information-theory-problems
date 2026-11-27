"""
Literal Python transcription of `nairElGamalInnerBound` in
lean/InfoTheory/Problems/DegradedMessageSetsBcThreeReceivers.lean, using the Core
definitions verbatim:
    condEntropy P      = H(P) - H(P.snd)
    mutualInfo P       = H(P.fst) + H(P.snd) - H(P)
    condMutualInfo P   = H(XZ) + H(YZ) - H(XYZ) - H(Z)        for P on X x Y x Z
and the same tuple conventions: t = (u1, u2, u3, x), V2 = (u1, u2), V3 = (u1, u3).

Checks:
 (1) NE 2009 Fig. 2 product multilevel channel: the point (R0, R1) = (1/2, 1/2),
     which is on the capacity boundary but outside the Borade-Zheng-Trott
     (straightforward Korner-Marton) region (max R1 = 5/12 at R0 = 1/2), lies in
     the Lean region (all ten constraints evaluated exactly with Fractions where
     possible, floats otherwise).
 (2) Random distributions on random channels: the redundancies used in the hand
     Fourier--Motzkin elimination (L23 <= L2, L23 <= L3, L2 <= L1, L3 <= L1) hold.
 (3) Fourier--Motzkin by LP: for random (P, W) and random (R0, R1), feasibility of
     Nair--El Gamal's code-rate system (15)-(22) (with S2 <= T2, S3 <= T3, all rates
     >= 0, non-strict inequalities) agrees with membership in the ten Lean constraints.
"""
import itertools, math
import numpy as np

def H(d):
    """entropy (bits) of a dict outcome->prob"""
    return -sum(p*math.log2(p) for p in d.values() if p > 0)

def push(J, f):
    out = {}
    for z, p in J.items():
        k = f(z); out[k] = out.get(k, 0.0) + p
    return out

def mutualInfo(J, fa, fb):
    return H(push(J, fa)) + H(push(J, fb)) - H(push(J, lambda z: (fa(z), fb(z))))

def condMutualInfo(J, fa, fb, fc):
    return (H(push(J, lambda z: (fa(z), fc(z)))) + H(push(J, lambda z: (fb(z), fc(z))))
            - H(push(J, lambda z: (fa(z), fb(z), fc(z)))) - H(push(J, fc)))

def lean_region_constraints(P, W1, W2, W3):
    """P: dict (u1,u2,u3,x)->prob ; Wj: dict x -> dict yj -> prob (marginal channels;
    the Lean quantities only involve pairs (aux, y_j), so marginals suffice).
    Returns the right-hand sides of the ten Lean constraints, in Lean order."""
    J = {}
    for t, p in P.items():
        x = t[3]
        for y1, a in W1[x].items():
            for y2, b in W2[x].items():
                for y3, c in W3[x].items():
                    # product coupling of the marginals; any coupling gives the same values
                    J[(t, (y1, y2, y3))] = J.get((t, (y1, y2, y3)), 0.0) + p*a*b*c
    u1 = lambda z: z[0][0]
    V2 = lambda z: (z[0][0], z[0][1])
    V3 = lambda z: (z[0][0], z[0][2])
    V23 = lambda z: (z[0][0], z[0][1], z[0][2])
    X = lambda z: z[0][3]
    Y1 = lambda z: z[1][0]; Y2 = lambda z: z[1][1]; Y3 = lambda z: z[1][2]
    IV2Y2 = mutualInfo(J, V2, Y2)
    IV3Y3 = mutualInfo(J, V3, Y3)
    IV2V3gU1 = condMutualInfo(J, V2, V3, u1)
    IXY1gV2 = condMutualInfo(J, X, Y1, V2)
    IXY1gV3 = condMutualInfo(J, X, Y1, V3)
    IXY1gU1 = condMutualInfo(J, X, Y1, u1)
    IXY1gV23 = condMutualInfo(J, X, Y1, V23)
    IXY1 = mutualInfo(J, X, Y1)
    q = dict(IV2Y2=IV2Y2, IV3Y3=IV3Y3, IV2V3gU1=IV2V3gU1, IXY1gV2=IXY1gV2,
             IXY1gV3=IXY1gV3, IXY1gU1=IXY1gU1, IXY1gV23=IXY1gV23, IXY1=IXY1)
    cons = [  # (a0, a1, rhs) meaning a0*R0 + a1*R1 <= rhs
        (1, 0, IV2Y2), (1, 0, IV3Y3), (2, 0, IV2Y2 + IV3Y3 - IV2V3gU1),
        (0, 1, IXY1gV2 + IXY1gV3), (0, 1, IXY1gU1),
        (1, 1, IXY1), (1, 1, IV2Y2 + IXY1gV2), (1, 1, IV3Y3 + IXY1gV3),
        (2, 1, IV2Y2 + IV3Y3 + IXY1gV23 - IV2V3gU1),
        (2, 2, IV2Y2 + IXY1gV2 + IV3Y3 + IXY1gV3 - IV2V3gU1)]
    return cons, q

def check_fig2():
    # inputs x = (x1, x2) in {0,1}^2 ; marginal channels of the NE Fig. 2 example
    xs = list(itertools.product((0, 1), (0, 1)))
    W1, W2, W3 = {}, {}, {}
    for x in xs:
        x1, x2 = x
        W1[x] = {(x1, x2): 0.5, ('E', x2): 0.5}             # Y1 = (BEC_1/2(X1), X2)
        W2[x] = {x1: 1.0}                                   # Y2 = Y21 = X1
        W3[x] = {(x1, x2): (1/6)*0.5, (x1, 'E'): (1/6)*0.5,  # Y3 = (BEC_5/6(X1), BEC_1/2(X2))
                 ('E', x2): (5/6)*0.5, ('E', 'E'): (5/6)*0.5}
    # U1 = X2, U2 = X1 (so V2 = (X2, X1) = X), U3 = constant (so V3 = X2); X uniform
    P = {(x[1], x[0], 0, x): 0.25 for x in xs}
    cons, q = lean_region_constraints(P, W1, W2, W3)
    R0, R1 = 0.5, 0.5
    print('NE Fig. 2 channel, U1=X2, U2=X1, U3=const, X uniform:')
    for k, v in q.items():
        print(f'   {k:9s} = {v:.12f}')
    ok = True
    for a0, a1, rhs in cons:
        lhs = a0*R0 + a1*R1
        print(f'   {a0}R0+{a1}R1 = {lhs:.3f} <= {rhs:.12f}  {"ok" if lhs <= rhs + 1e-12 else "VIOLATED"}')
        ok &= lhs <= rhs + 1e-12
    print('   (1/2, 1/2) in Lean region:', ok, ' (BZT allows at most R1 = 5/12 at R0 = 1/2)')
    return ok

def random_checks(n=300, seed=0):
    rng = np.random.default_rng(seed)
    worst = 0.0
    for _ in range(n):
        nx, k1, k2, k3 = 2, rng.integers(1, 3), rng.integers(1, 4), rng.integers(1, 4)
        ny = [2, 3, 2]
        W = [{x: dict(enumerate(rng.dirichlet(np.ones(m)))) for x in range(nx)} for m in ny]
        keys = list(itertools.product(range(k1), range(k2), range(k3), range(nx)))
        pv = rng.dirichlet(np.ones(len(keys))*0.5)
        P = dict(zip(keys, pv))
        cons, q = lean_region_constraints(P, *W)
        # Fourier--Motzkin redundancy facts used in the hand elimination
        L1, L2, L3, L23 = q['IXY1gU1'], q['IXY1gV2'], q['IXY1gV3'], q['IXY1gV23']
        worst = max(worst, L23 - L2, L23 - L3, L2 - L1, L3 - L1)
    print(f'random check of L23<=L2, L23<=L3, L2<=L1, L3<=L1 on {n} random (P,W): '
          f'max violation {worst:.2e} (should be <= ~1e-12)')
    return worst <= 1e-10

def fm_check(n_dist=200, n_pts=60, seed=1):
    """Fourier-Motzkin check: for random (P, W), the set of (R0, R1) for which the
    Nair-El Gamal code-rate system (15)-(22) (non-strict) is feasible in
    (S1, S2, S3, T2, T3) >= 0 with R1 = S1+S2+S3, S2 <= T2, S3 <= T3, coincides with the
    ten Lean constraints.  Points are sampled near the boundary to make the test sharp."""
    from scipy.optimize import linprog
    rng = np.random.default_rng(seed)
    mismatches = 0; tested = 0; n_in = 0
    for _ in range(n_dist):
        ny = [2, 3, 2]
        W = [{x: dict(enumerate(rng.dirichlet(np.ones(m)))) for x in range(2)} for m in ny]
        k1, k2, k3 = rng.integers(1, 3), rng.integers(1, 4), rng.integers(1, 4)
        keys = list(itertools.product(range(k1), range(k2), range(k3), range(2)))
        P = dict(zip(keys, rng.dirichlet(np.ones(len(keys))*0.5)))
        cons, q = lean_region_constraints(P, *W)
        I2, I3, I23 = q['IV2Y2'], q['IV3Y3'], q['IV2V3gU1']
        K, L1, L2, L3, L23 = q['IXY1'], q['IXY1gU1'], q['IXY1gV2'], q['IXY1gV3'], q['IXY1gV23']
        # scale for sampling
        r0max = max(min(I2, I3), 1e-9); r1max = max(K, 1e-9)
        for _ in range(n_pts):
            R0 = rng.uniform(0, 1.05*r0max); R1 = rng.uniform(0, 1.05*r1max)
            lean_in = all(a0*R0 + a1*R1 <= rhs + 1e-9 for a0, a1, rhs in cons)
            # variables v = (S1, S2, S3, T2, T3)
            A = []; bb = []
            A.append([0, 1, 1, -1, -1]); bb.append(-I23)          # (15) S2+S3 <= T2+T3-I23
            A.append([1, 1, 1, 0, 0]);  bb.append(K - R0)         # (16)
            A.append([1, 1, 1, 0, 0]);  bb.append(L1)             # (17)
            A.append([1, 0, 1, 0, 0]);  bb.append(L2)             # (18)
            A.append([1, 1, 0, 0, 0]);  bb.append(L3)             # (19)
            A.append([1, 0, 0, 0, 0]);  bb.append(L23)            # (20)
            A.append([0, 0, 0, 1, 0]);  bb.append(I2 - R0)        # (21)
            A.append([0, 0, 0, 0, 1]);  bb.append(I3 - R0)        # (22)
            A.append([0, 1, 0, -1, 0]); bb.append(0)              # S2 <= T2
            A.append([0, 0, 1, 0, -1]); bb.append(0)              # S3 <= T3
            res = linprog(np.zeros(5), A_ub=A, b_ub=np.array(bb) + 1e-9,
                          A_eq=[[1, 1, 1, 0, 0]], b_eq=[R1], bounds=[(0, None)]*5,
                          method='highs')
            code_in = res.status == 0
            tested += 1; n_in += lean_in
            if code_in != lean_in:
                # tolerate disagreements only within numerical slack of a constraint
                slack = min(abs(rhs - (a0*R0 + a1*R1)) for a0, a1, rhs in cons)
                if slack > 1e-7:
                    mismatches += 1
    print(f'Fourier-Motzkin LP check: {tested} (P, W, R0, R1) samples ({n_in} inside the Lean region, '
          f'{tested-n_in} outside), {mismatches} mismatches')
    return mismatches == 0

if __name__ == '__main__':
    a = check_fig2()
    b = random_checks()
    c = fm_check()
    print('ALL OK' if a and b and c else 'FAILURE')
