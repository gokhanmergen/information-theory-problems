# Reviewer check (2026-11-27, Claims 1-2): Lean DB terms at Shannon's optimiser, the Claim-1
# identity on 60 000 random laws (kZ <= 4, seed 12345), and penalised Nelder-Mead at kZ = 2.
# Run: python3 check.py
# Runtime: about 10 s. Needs numpy, scipy.
# Independent reviewer check (not the author's code).
import math
import numpy as np
from collections import defaultdict
from scipy.optimize import minimize

rng = np.random.default_rng(12345)


def H(d):
    return -sum(p * math.log2(p) for p in d.values() if p > 0)


def marg(J, f):
    o = defaultdict(float)
    for t, p in J.items():
        o[f(t)] += p
    return o


def cmi(J, fa, fb, fc):
    # Lean condMutualInfo: H(A,C)+H(B,C)-H(A,B,C)-H(C)
    return (H(marg(J, lambda t: (fa(t), fc(t)))) + H(marg(J, lambda t: (fb(t), fc(t))))
            - H(marg(J, lambda t: (fa(t), fb(t), fc(t)))) - H(marg(J, fc)))


def lean_terms(P):  # P: dict (z,x1,x2)->prob ; Lean J = (z, x1, x2, x1 && x2)
    J = {(z, a, b, a & b): p for (z, a, b), p in P.items()}
    z = lambda t: t[0]
    x1 = lambda t: t[1]
    x2 = lambda t: t[2]
    y = lambda t: t[3]
    return (cmi(J, x1, x2, z), cmi(J, x1, x2, lambda t: (y(t), z(t))),
            cmi(J, x1, y, lambda t: (x2(t), z(t))), cmi(J, x2, y, lambda t: (x1(t), z(t))))


phi = (1 + 5 ** .5) / 2
L = math.log2(phi)
a = 1 / 5 ** .5
b = (5 - 5 ** .5) / 10
P = {(0, 0, 0): 0.0, (0, 0, 1): b, (0, 1, 0): b, (0, 1, 1): a}
print("Shannon point (I12|Z, I12|YZ, r1, r2):", lean_terms(P), "log2phi", L)

best_f = 0
best_u = 0
viol = 0
for trial in range(60000):
    k = int(rng.integers(1, 5))
    w = rng.dirichlet(np.ones(4 * k) * rng.choice([0.2, 1, 5]))
    P = {(z, x1, x2): w[4 * z + 2 * x1 + x2] for z in range(k) for x1 in (0, 1) for x2 in (0, 1)}
    i12z, i12yz, r1, r2 = lean_terms(P)
    m = min(r1, r2)
    best_u = max(best_u, m)
    if i12z <= i12yz + 1e-15:
        best_f = max(best_f, m)
    J = {(z, x1, x2, x1 & x2): p for (z, x1, x2), p in P.items()}
    HYZ = H(marg(J, lambda t: (t[3], t[0]))) - H(marg(J, lambda t: t[0]))
    HYX1Z = H(marg(J, lambda t: (t[3], t[1], t[0]))) - H(marg(J, lambda t: (t[1], t[0])))
    HYX2Z = H(marg(J, lambda t: (t[3], t[2], t[0]))) - H(marg(J, lambda t: (t[2], t[0])))
    viol = max(viol, abs((i12z - i12yz) - (HYZ - HYX1Z - HYX2Z)))
print("random search: best feasible min", best_f, " best unconstrained", best_u,
      " max |Claim-1 identity error|", viol)


def neg(x, k):
    w = np.abs(x)
    w = w / w.sum()
    P = {(z, x1, x2): w[4 * z + 2 * x1 + x2] for z in range(k) for x1 in (0, 1) for x2 in (0, 1)}
    i12z, i12yz, r1, r2 = lean_terms(P)
    pen = max(0, i12z - i12yz) * 100
    return -(min(r1, r2)) + pen


bb = 0
for s in range(20):
    k = 2
    x0 = rng.random(4 * k)
    r = minimize(neg, x0, args=(k,), method="Nelder-Mead",
                 options={"maxiter": 6000, "xatol": 1e-11, "fatol": 1e-13})
    bb = max(bb, -r.fun)
print("Nelder-Mead kZ=2 best penalised value:", bb, " log2phi - best:", L - bb)
