# Reviewer check (2026-11-27, Ponniah C-CF): SLSQP maximisation of I(X;Yh,Y1,Y2|Xr) subject to the
# same-law reading of (93), |Yh| = 2, 3, 4, 60 starts each (180 total, seed 5); the note quotes 0.431412.
# Run: python3 ccf_opt.py
# Runtime: about 1 min. Needs numpy, scipy.
"""SLSQP maximisation of Ponniah-type C-CF rate I(X;Yh,Y1,Y2|Xr) subject to
I(Yh;Yr|Xr) <= I(Yh,Xr;Y1,Y2) (same-law reading of (93)), arbitrary p(x,xr), |Yh| = kh."""
import itertools, math
import numpy as np
from scipy.optimize import minimize


def h(p):
    return 0.0 if p <= 0 or p >= 1 else -p * math.log2(p) - (1 - p) * math.log2(1 - p)


lo, hi = 0.0, 0.5
for _ in range(200):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if h(mid) < 0.7 else (lo, mid)
q = (lo + hi) / 2
Wt = np.zeros((2, 2, 2, 2, 2))
for x, xr, y1, y2, yr in itertools.product((0, 1), repeat=5):
    Wt[x, xr, y1, y2, yr] = (0.8 if y1 == x else 0.2) * ((1 - q) if y2 == xr else q) * (0.9 if yr == x else 0.1)


def Hn(a):
    a = a[a > 1e-300]
    return float(-(a * np.log2(a)).sum())


def ev(v, kh):
    pxx = np.exp(v[:4] - v[:4].max()); pxx /= pxx.sum(); pxx = pxx.reshape(2, 2)
    T = v[4:].reshape(2, 2, kh); T = np.exp(T - T.max(-1, keepdims=True)); T /= T.sum(-1, keepdims=True)
    J = pxx[:, :, None, None, None, None] * Wt[:, :, :, :, :, None] * T[None, :, None, None, :, :]

    def Hm(keep):
        drop = tuple(i for i in range(6) if i not in keep)
        return Hn(J.sum(axis=drop).ravel())

    def I(A, B, C):
        return Hm(A | C) + Hm(B | C) - Hm(A | B | C) - (Hm(C) if C else 0.0)
    # axes: 0 x, 1 xr, 2 y1, 3 y2, 4 yr, 5 yh
    return I({0}, {5, 2, 3}, {1}), I({5, 1}, {2, 3}, set()) - I({5}, {4}, {1})


rng = np.random.default_rng(5)
best = (0, None, None)
for kh in (2, 3, 4):
    for s in range(60):
        v0 = rng.normal(size=4 + 4 * kh) * 2
        res = minimize(lambda v: -ev(v, kh)[0], v0, method="SLSQP",
                       constraints=[{"type": "ineq", "fun": lambda v: ev(v, kh)[1]}],
                       options={"maxiter": 500, "ftol": 1e-12})
        r, sl = ev(res.x, kh)
        if sl >= -1e-9 and r > best[0]:
            best = (r, kh, sl)
print("max feasible C-CF rate found: %.6f (|Yh|=%d, slack %.2e); analytic bound %.6f; DF bound %.6f"
      % (best[0], best[1], best[2], 1 - h(0.2) + 0.24, 1 - h(0.1)))
