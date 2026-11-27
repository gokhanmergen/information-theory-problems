# Reviewer check (2026-11-27, Claim 5): Nelder-Mead polish of the printed |U|=3 point and
# 40-start Nelder-Mead at |U| = 3, 4 (seed 99), with the attempt's p rule.
# Run: python3 check3.py
# Runtime: about 10 s. Needs numpy, scipy.
# Local polish of the reported |U|=3 point and multi-start Nelder-Mead on the objective
# min(r1,r2,O1,O2), |U| = 3, 4 (reviewer's own optimiser; attained values = lower bounds only).
import math
import numpy as np
from scipy.optimize import minimize


def h(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def p_hw(a, b):
    d = (1 - a) * b + a * (1 - b)
    return a * (1 - b) / d if d > 0 else 0.0


def closed(w, al, be):
    r1 = r2 = 0.0
    for wu, a, b in zip(w, al, be):
        p = p_hw(a, b)
        r1 += wu * (b * h(a) + (1 - b) * (h((1 - a) * (1 - p)) - (1 - a) * h(p)))
        r2 += wu * (a * h(b) + (1 - a) * (h((1 - b) * p) - (1 - b) * h(p)))
    P1 = sum(wu * a for wu, a in zip(w, al))
    P2 = sum(wu * b for wu, b in zip(w, be))
    P11 = sum(wu * a * b for wu, a, b in zip(w, al, be))
    return r1, r2, P2 * h(P11 / P2), P1 * h(P11 / P1)


def negmin(x, k):
    w = np.abs(x[:k]) + 1e-15
    w = w / w.sum()
    al = np.clip(x[k:2 * k], 0, 1)
    be = np.clip(x[2 * k:3 * k], 0, 1)
    return -min(closed(w, al, be))


x0 = np.array([0.16437, 0.67127, 0.16437, 0.96851, 0.71026, 0.39818, 0.39818, 0.71026, 0.96851])
r = minimize(negmin, x0, args=(3,), method="Nelder-Mead",
             options={"maxiter": 40000, "maxfev": 40000, "xatol": 1e-12, "fatol": 1e-14})
print("polished |U|=3 from reported point:", -r.fun, flush=True)
rng = np.random.default_rng(99)
for k in (3, 4):
    best = 0
    for s in range(40):
        x = np.concatenate([rng.dirichlet(np.ones(k)), rng.uniform(0.3, 1, 2 * k)])
        rr = minimize(negmin, x, args=(k,), method="Nelder-Mead",
                      options={"maxiter": 30000, "maxfev": 30000, "xatol": 1e-11, "fatol": 1e-13})
        best = max(best, -rr.fun)
    print(f"multistart NM |U|={k}: {best:.7f}", flush=True)
