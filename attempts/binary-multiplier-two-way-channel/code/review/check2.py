# Reviewer check (2026-11-27, Claims 4-5): brute-force HW parallel-channel terms vs the closed
# form (3000 + 2000 random laws, seed 7), the printed |U|=3 point, and differential evolution.
# Run: python3 check2.py
# Runtime: about 100 s (mostly the DE runs). Needs numpy, scipy.
# Independent reviewer check of Claims 4-5 (HW parallel-channel bound for the BMC).
# (1) Brute-force the information terms of Bloemen Thm 6.3 from the full joint law
#     p(u,x1,x2) p(y|x1,x2) p_B(b|x1,x2,y) with Table 6.2, and compare to the closed form.
# (2) Evaluate at the |U|=3 point reported in the attempt.
# (3) Own optimisation (differential evolution, different method from the author's SLSQP).
import math
import numpy as np
from collections import defaultdict
from scipy.optimize import differential_evolution

rng = np.random.default_rng(7)


def H(d):
    return -sum(p * math.log2(p) for p in d.values() if p > 1e-300)


def marg(J, f):
    o = defaultdict(float)
    for t, p in J.items():
        o[f(t)] += p
    return o


def cmi(J, fa, fb, fc):
    return (H(marg(J, lambda t: (fa(t), fc(t)))) + H(marg(J, lambda t: (fb(t), fc(t))))
            - H(marg(J, lambda t: (fa(t), fb(t), fc(t)))) - H(marg(J, fc)))


def h(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def joint(w, Pu, prule):
    """Pu[u] = 2x2 array p(x1,x2|u) (general, not nec. independent); prule(u) -> p."""
    J = defaultdict(float)
    for u in range(len(w)):
        p = prule(u)
        for x1 in (0, 1):
            for x2 in (0, 1):
                q = w[u] * Pu[u][x1][x2]
                y = x1 & x2
                if (x1, x2) == (0, 0):
                    J[(u, x1, x2, y, 0)] += q * p
                    J[(u, x1, x2, y, 1)] += q * (1 - p)
                elif (x1, x2) == (0, 1):
                    J[(u, x1, x2, y, 1)] += q
                elif (x1, x2) == (1, 0):
                    J[(u, x1, x2, y, 0)] += q
                else:
                    J[(u, x1, x2, y, 2)] += q   # '*'
    return J


U_ = lambda t: t[0]
X1 = lambda t: t[1]
X2 = lambda t: t[2]
Y = lambda t: t[3]
B = lambda t: t[4]


def brute_terms(J):
    r1 = cmi(J, X1, lambda t: (Y(t), B(t)), lambda t: (X2(t), U_(t)))
    r2 = cmi(J, X2, lambda t: (Y(t), B(t)), lambda t: (X1(t), U_(t)))
    o1 = cmi(J, X1, Y, X2)
    o2 = cmi(J, X2, Y, X1)
    db_prod = cmi(J, X1, X2, lambda t: (Y(t), B(t), U_(t)))
    db_cons = cmi(J, X1, X2, U_)
    return r1, r2, o1, o2, db_prod, db_cons


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


# (1) closed form vs brute force on random independent-given-u laws, random p rule = HW rule
maxerr = 0
maxprod = 0
for trial in range(3000):
    k = int(rng.integers(1, 5))
    w = rng.dirichlet(np.ones(k))
    al = rng.random(k)
    be = rng.random(k)
    Pu = [[[(1 - a) * (1 - b), (1 - a) * b], [a * (1 - b), a * b]] for a, b in zip(al, be)]
    J = joint(w, Pu, lambda u: p_hw(al[u], be[u]))
    bt = brute_terms(J)
    ct = closed(w, al, be)
    maxerr = max(maxerr, max(abs(x - y) for x, y in zip(bt[:4], ct)))
    maxprod = max(maxprod, abs(bt[4]))
# also: I(X1;X2|Y,B,U) = 0 for arbitrary (dependent) p(x1,x2|u) and arbitrary p
for trial in range(2000):
    k = int(rng.integers(1, 4))
    w = rng.dirichlet(np.ones(k))
    Pu = [rng.dirichlet(np.ones(4)).reshape(2, 2).tolist() for _ in range(k)]
    ps = rng.random(k)
    J = joint(w, Pu, lambda u: ps[u])
    maxprod = max(maxprod, abs(brute_terms(J)[4]))
print("closed form vs brute force: max abs diff", maxerr)
print("max |I(X1;X2|Y,B,U)| over random laws (should be 0):", maxprod)

# leak minimiser check: numerically minimise leak sum over p, compare with p_hw
maxdp = 0
for trial in range(500):
    a, b = rng.random(2)
    f = lambda p: ((1 - b) * (h((1 - a) * (1 - p)) - (1 - a) * h(p))
                   + (1 - a) * (h((1 - b) * p) - (1 - b) * h(p)))
    grid = np.linspace(1e-6, 1 - 1e-6, 200001)
    vals = np.array([0.0])
    pv = min(grid[::50], key=f)
    fine = np.linspace(max(1e-9, pv - 1e-4), min(1 - 1e-9, pv + 1e-4), 2001)
    pv = min(fine, key=f)
    maxdp = max(maxdp, abs(pv - p_hw(a, b)))
print("max |numerical leak argmin - p_hw| :", maxdp)

# (2) reported |U|=3 point
w = [0.16437, 0.67127, 0.16437]
al = [0.96851, 0.71026, 0.39818]
be = [0.39818, 0.71026, 0.96851]
s = sum(w)
w = [x / s for x in w]
print("reported |U|=3 point terms:", closed(w, al, be), " min:", min(closed(w, al, be)))


# (3) own optimiser: differential evolution, |U|=3, symmetric and free
def negmin(x, k):
    ww = np.abs(x[:k]) + 1e-12
    ww = ww / ww.sum()
    return -min(closed(ww, x[k:2 * k], x[2 * k:3 * k]))


for k in (2, 3, 4):
    r = differential_evolution(negmin, [(0, 1)] * (3 * k), args=(k,), seed=3, tol=1e-12,
                               maxiter=4000, popsize=40, polish=True)
    print(f"DE |U|={k}: {-r.fun:.7f}")
