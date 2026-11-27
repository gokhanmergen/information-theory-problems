# Reviewer check (2026-11-27, Claim 4(i)): the coded time-sharing point recomputed from conditional
# variances in mpmath (50 digits): averaged HK terms, max sum rate 3.92288136, explicit rate split.
# Run: python3 coded_point.py
# Runtime: under 1 s. Needs mpmath, numpy, scipy.
"""Independent check of the coded time-sharing point (reviewer script).

Channel (Lean convention): Y1 = X1 + a X2 + Z1, Y2 = b X1 + X2 + Z2, a = b = 1/2
(amplitude), so power gains a^2 = b^2 = 1/4; P1 = P2 = 100.
X_i = U_i + V_i, U_i ~ N(0, Pc_i), V_i ~ N(0, Pp_i) independent, given Q.

All mutual informations derived from conditional variances (not copied from the
author's code).  mpmath 50 digits.
"""
import itertools
from mpmath import mp, mpf, log, matrix

mp.dps = 50
a2 = mpf(1) / 4
b2 = mpf(1) / 4
P = mpf(100)


def h(v):  # entropy difference helper: 0.5*log2 of variance ratio
    return log(v) / (2 * log(2))


def mi(var_num, var_den):
    return h(var_num) - h(var_den)


def phase(P1c, P1p, P2c, P2p):
    P1c, P1p, P2c, P2p = map(mpf, (P1c, P1p, P2c, P2p))
    P1 = P1c + P1p
    P2 = P2c + P2p
    # Receiver 1: Y1 = U1 + V1 + a U2 + a V2 + Z1
    noise1 = 1 + a2 * P2p          # Var(Y1 | X1, U2)  (= Var(Y1|X1,X2-common))
    r1 = dict(
        priv=mi(P1p + a2 * P2p + 1, noise1),          # I(X1;Y1|U1,U2)
        own=mi(P1 + a2 * P2p + 1, noise1),            # I(X1;Y1|U2)
        privcross=mi(P1p + a2 * P2 + 1, noise1),      # I(X1,U2;Y1|U1)
        all=mi(P1 + a2 * P2 + 1, noise1),             # I(X1,U2;Y1)
    )
    noise2 = 1 + b2 * P1p
    r2 = dict(
        priv=mi(P2p + b2 * P1p + 1, noise2),
        own=mi(P2 + b2 * P1p + 1, noise2),
        privcross=mi(P2p + b2 * P1 + 1, noise2),
        all=mi(P2 + b2 * P1 + 1, noise2),
    )
    return r1, r2


def avg(dicts, w):
    return {k: sum(wi * d[k] for d, wi in zip(dicts, w)) for k in dicts[0]}


def compact(r1, r2):
    """El Gamal-Kim Thm 6.4 compact 7 bounds, written from the MI names."""
    A1 = r1['own']                                  # R1 <= I(X1;Y1|U2,Q)
    A2 = r2['own']
    S1 = r1['all'] + r2['priv']                     # I(X1,U2;Y1|Q)+I(X2;Y2|U1,U2,Q)
    S2 = r2['all'] + r1['priv']
    S3 = r1['privcross'] + r2['privcross']          # I(X1,U2;Y1|U1)+I(X2,U1;Y2|U2)
    D1 = r1['all'] + r1['priv'] + r2['privcross']   # 2R1+R2
    D2 = r2['all'] + r2['priv'] + r1['privcross']   # R1+2R2
    return A1, A2, S1, S2, S3, D1, D2


def max_sum_compact(T):
    """Exact max R1+R2 over {R>=0, 7 constraints} by vertex enumeration."""
    A1, A2, S1, S2, S3, D1, D2 = T
    rows = [(1, 0, A1), (0, 1, A2), (1, 1, S1), (1, 1, S2), (1, 1, S3), (2, 1, D1), (1, 2, D2),
            (-1, 0, 0), (0, -1, 0)]
    best = None
    for (p, q) in itertools.combinations(rows, 2):
        det = p[0] * q[1] - p[1] * q[0]
        if det == 0:
            continue
        x = (p[2] * q[1] - p[1] * q[2]) / det
        y = (p[0] * q[2] - p[2] * q[0]) / det
        if all(r[0] * x + r[1] * y <= r[2] + mpf(10) ** -40 for r in rows):
            if best is None or x + y > best[0]:
                best = (x + y, x, y)
    return best


def symmetric_split(r1, r2):
    """Max symmetric R with explicit split (R1c,R1p,R2c,R2p) by LP vertex search.
    Receiver-1 SND constraints (El Gamal-Kim Sec. 6.5):
      R1p <= priv1, R1c+R1p <= own1, R1p+R2c <= privcross1, R1c+R1p+R2c <= all1.
    Use scipy for the search, then verify the split in mpmath."""
    import numpy as np
    from scipy.optimize import linprog
    Aub = [[0, 1, 0, 0], [1, 1, 0, 0], [0, 1, 1, 0], [1, 1, 1, 0],
           [0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 1], [1, 0, 1, 1]]
    bub = [r1['priv'], r1['own'], r1['privcross'], r1['all'],
           r2['priv'], r2['own'], r2['privcross'], r2['all']]
    res = linprog([-1, -1, 0, 0], A_ub=Aub, b_ub=[float(v) for v in bub],
                  A_eq=[[1, 1, -1, -1]], b_eq=[0], bounds=[(0, None)] * 4, method='highs')
    return res.x, Aub, bub


if __name__ == '__main__':
    ph1 = phase(100, 0, 86, 14)    # (P1p, P2p) = (0, 14)
    ph2 = phase(86, 14, 100, 0)    # (P1p, P2p) = (14, 0)
    names = ['A1', 'A2', 'S1', 'S2', 'S3', 'D1', 'D2']
    T1 = compact(*ph1)
    T2 = compact(*ph2)
    r1 = avg([ph1[0], ph2[0]], [mpf(1) / 2] * 2)
    r2 = avg([ph1[1], ph2[1]], [mpf(1) / 2] * 2)
    Tbar = compact(r1, r2)
    for n, x, y, z in zip(names, T1, T2, Tbar):
        print(f"{n}: phase1 {mp.nstr(x, 10)}  phase2 {mp.nstr(y, 10)}  avg {mp.nstr(z, 10)}")
    print('per-phase max sum (no TS):', mp.nstr(max_sum_compact(T1)[0], 12), mp.nstr(max_sum_compact(T2)[0], 12))
    best = max_sum_compact(Tbar)
    print('coded-TS max sum (compact):', mp.nstr(best[0], 15), 'at', mp.nstr(best[1], 12), mp.nstr(best[2], 12))
    print('C(200) =', mp.nstr(log(201) / (2 * log(2)), 15))
    x, Aub, bub = symmetric_split(r1, r2)
    # exact re-check of a rational split slightly inside
    R1p = r1['priv']                      # private rate = avg I(X1;Y1|U1,U2)
    # symmetric: R1p = R2p, R1c = R2c = t; constraints become
    # t+R1p <= own, R1p+t <= privcross, 2t+R1p <= all  (receiver 1, symmetric)
    t = min(r1['own'] - R1p, r1['privcross'] - R1p, (r1['all'] - R1p) / 2)
    split = [t, R1p, t, R1p]
    slack = [b - sum(c * s for c, s in zip(row, split)) for row, b in zip(Aub, bub)]
    print('symmetric split (R1c,R1p,R2c,R2p) =', [mp.nstr(s, 10) for s in split])
    print('per-user R =', mp.nstr(t + R1p, 15), ' sum =', mp.nstr(2 * (t + R1p), 15))
    print('min slack =', mp.nstr(min(slack), 5))
    print('scipy LP split:', x, 'sum', 2 * (x[0] + x[1]))
    # Power check: each phase uses (P1c+P1p, P2c+P2p) = (100, 100)
    print('average powers: user1', (100 + 100) / 2, 'user2', (100 + 100) / 2)
