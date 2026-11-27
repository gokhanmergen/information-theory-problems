# Reviewer check (2026-11-27, Claim 2): exact Fourier-Motzkin elimination (Fractions) of NE
# code system (15)-(22), then LP tests of both inclusions against Lean (14), with and without
# the side facts L23 <= L2, L23 <= L3.  Run: python3 fm_exact.py
# Runtime: under 1 s. Needs numpy, scipy.
"""Independent exact Fourier-Motzkin check of NE Prop. 5 (14) from code constraints (15)-(22).
Variables (all >= 0): R0 R1 I2 I3 I23 K L1 L2 L3 L23 | S1 S2 S3 T2 T3.
Homogeneous cone; FM eliminates T2,T3,S1,S2,S3 exactly (Fractions). Then the two inclusions
(Lean(14) & side  <=>  FM projection & side) are checked inequality by inequality by LP over
the cone intersected with the unit box."""
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

names = ['R0', 'R1', 'I2', 'I3', 'I23', 'K', 'L1', 'L2', 'L3', 'L23', 'S1', 'S2', 'S3', 'T2', 'T3']
idx = {n: i for i, n in enumerate(names)}


def row(**kw):
    r = [F(0)] * len(names)
    for k, v in kw.items():
        r[idx[k]] = F(v)
    return r  # meaning r.z <= 0


cons = []
cons.append(row(R1=1, S1=-1, S2=-1, S3=-1))
cons.append(row(R1=-1, S1=1, S2=1, S3=1))
cons.append(row(S2=1, S3=1, T2=-1, T3=-1, I23=1))   # (15)
cons.append(row(R0=1, S1=1, S2=1, S3=1, K=-1))      # (16)
cons.append(row(S1=1, S2=1, S3=1, L1=-1))           # (17)
cons.append(row(S1=1, S3=1, L2=-1))                 # (18)
cons.append(row(S1=1, S2=1, L3=-1))                 # (19)
cons.append(row(S1=1, L23=-1))                      # (20)
cons.append(row(R0=1, T2=1, I2=-1))                 # (21)
cons.append(row(R0=1, T3=1, I3=-1))                 # (22)
cons.append(row(S2=1, T2=-1))
cons.append(row(S3=1, T3=-1))
for n in ['S1', 'S2', 'S3', 'T2', 'T3']:
    cons.append(row(**{n: -1}))


def fm(cons, var):
    j = idx[var]
    P = [c for c in cons if c[j] > 0]
    N = [c for c in cons if c[j] < 0]
    out = [c for c in cons if c[j] == 0]
    for p in P:
        for q in N:
            a, b = p[j], -q[j]
            out.append([b * x + a * y for x, y in zip(p, q)])
    seen, res = set(), []
    for c in out:
        g = max(abs(x) for x in c) or F(1)
        cc = tuple(x / g for x in c)
        if cc not in seen and any(cc):
            seen.add(cc)
            res.append(list(cc))
    return res


C = cons
for v in ['T2', 'T3', 'S1', 'S2', 'S3']:
    C = fm(C, v)
print('FM output inequalities:', len(C))
base = ['R0', 'R1', 'I2', 'I3', 'I23', 'K', 'L1', 'L2', 'L3', 'L23']
nb = len(base)


def vec(c):
    return np.array([float(c[idx[n]]) for n in base])


def lrow(**kw):
    r = np.zeros(nb)
    for k, v in kw.items():
        r[base.index(k)] = v
    return r


L = [lrow(R0=1, I2=-1), lrow(R0=1, I3=-1), lrow(R0=2, I2=-1, I3=-1, I23=1),
     lrow(R1=1, L2=-1, L3=-1), lrow(R1=1, L1=-1), lrow(R0=1, R1=1, K=-1),
     lrow(R0=1, R1=1, I2=-1, L2=-1), lrow(R0=1, R1=1, I3=-1, L3=-1),
     lrow(R0=2, R1=1, I2=-1, I3=-1, L23=-1, I23=1),
     lrow(R0=2, R1=2, I2=-1, L2=-1, I3=-1, L3=-1, I23=1)]
side_sets = {
    'nonneg only': [],
    'nonneg + L23<=L2, L23<=L3': [lrow(L23=1, L2=-1), lrow(L23=1, L3=-1)],
}


def implied(target, A):
    res = linprog(-target, A_ub=np.array(A) if len(A) else None,
                  b_ub=np.zeros(len(A)) if len(A) else None,
                  bounds=[(0, 1)] * nb, method='highs')
    return -res.fun <= 1e-9, -res.fun


FMv = [vec(c) for c in C]
for nm, side in side_sets.items():
    a_bad = [c for f, c in zip(FMv, C) if not implied(f, L + side)[0]]
    b_bad = [i for i, l in enumerate(L) if not implied(l, FMv + side)[0]]
    print(f'[{nm}] Lean&side subset FM: {len(a_bad) == 0};  FM&side subset Lean: {len(b_bad) == 0} '
          f'(Lean rows not implied: {b_bad})')
    for c in a_bad:
        print('   FM ineq not implied by Lean:', {n: str(c[idx[n]]) for n in base if c[idx[n]] != 0})
