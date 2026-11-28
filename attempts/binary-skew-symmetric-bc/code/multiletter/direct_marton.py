#!/usr/bin/env python3
"""
Direct cross-check on BSSC (x) BSSC (4-ary input), independent of the cardinality reduction and
of the minimax/dual argument: multistart maximisation of the two-letter affine Marton form

   L_{1/2}(P) = 1/2 I(W;Y^2) + 1/2 I(W;Z^2) + I(U;Y^2|W) + I(V;Z^2|W) - I(U;V|W)

over fully stochastic P_{W U V X1 X2} (softmax parametrisation) with |W| = 2, |U| = |V| = 4
(HLL's two-letter witness sizes).  Since M_{T(x)2}(P) = min_t L_t(P) <= L_{1/2}(P), any value
of L_{1/2} above 2 * 0.36164288442 bits would be a candidate two-letter gain; the reported
min{L_0, L_1} is the actual Marton value of the best distribution found.  NUMERICAL only.

Usage: python direct_marton.py n_starts seed [nW nU nV]
       python direct_marton.py seeded n_per_scale seed
          (|W|=|U|=|V|=4; starts = product of the two one-letter RTD optimisers, a = 0.15843497,
           perturbed in softmax coordinates by N(0, sigma^2), sigma in {0.05,0.2,0.5,1,2})
"""
import sys
import numpy as np
from scipy.optimize import minimize
from ml_core import bssc, product2, ent

M1 = 0.36164288442195   # one-letter BSSC Marton sum rate (bits)


def forms(P, TY2, TZ2):
    """P: (nW,nU,nV,4). Returns I(W;Y2), I(W;Z2), J = I(U;Y|W)+I(V;Z|W)-I(U;V|W)."""
    PW = P.sum((1, 2, 3))
    PWUY = np.einsum('wuvx,xy->wuy', P, TY2)
    PWVZ = np.einsum('wuvx,xz->wvz', P, TZ2)
    PWY, PWZ = PWUY.sum(1), PWVZ.sum(1)
    PY, PZ = PWY.sum(0), PWZ.sum(0)
    PWU, PWV, PWUV = P.sum((2, 3)), P.sum((1, 3)), P.sum(3)
    HW = ent(PW)
    IWY = ent(PY) + HW - ent(PWY.ravel())
    IWZ = ent(PZ) + HW - ent(PWZ.ravel())
    IUYgW = ent(PWU.ravel()) + ent(PWY.ravel()) - ent(PWUY.ravel()) - HW
    IVZgW = ent(PWV.ravel()) + ent(PWZ.ravel()) - ent(PWVZ.ravel()) - HW
    IUVgW = ent(PWU.ravel()) + ent(PWV.ravel()) - ent(PWUV.ravel()) - HW
    return IWY, IWZ, IUYgW + IVZgW - IUVgW


def product_rtd(a=0.15843497):
    """Two-letter product of the one-letter RTD optimiser, as P[w,u,v,x] with 4-ary alphabets."""
    one = np.zeros((2, 2, 2, 2))            # (w, u, v, x)
    one[0, 0, 0, 0], one[0, 1, 0, 1] = 0.5 * (1 - a), 0.5 * a      # W=0: X~Bern(a), U=X, V=0
    one[1, 0, 0, 0], one[1, 0, 1, 1] = 0.5 * a, 0.5 * (1 - a)      # W=1: X~Bern(1-a), U=0, V=X
    P = np.einsum('abcd,efgh->aebfcgdh', one, one).reshape(4, 4, 4, 4)
    return P


def seeded(n, seed):
    rng = np.random.default_rng(seed)
    TY, TZ = bssc()
    TY2, TZ2 = product2(TY), product2(TZ)
    P0 = product_rtd()
    a, b, J = forms(P0, TY2, TZ2)
    print("product RTD: L_1/2 = %.12f, Marton = %.12f, 2 M1 = %.12f" % (0.5 * a + 0.5 * b + J, min(a, b) + J, 2 * M1))

    def obj(th):
        e = np.exp(th - th.max())
        P = (e / e.sum()).reshape(P0.shape)
        a, b, J = forms(P, TY2, TZ2)
        return -(0.5 * a + 0.5 * b + J)
    th0 = np.log(P0.ravel() + 1e-12)
    overall = -np.inf
    for sig in (0.05, 0.2, 0.5, 1.0, 2.0):
        vals = []
        for s in range(n):
            r = minimize(obj, th0 + sig * rng.normal(size=th0.size), method='L-BFGS-B',
                         options={'maxiter': 20000, 'ftol': 1e-15, 'gtol': 1e-10})
            vals.append(-r.fun)
        vals = np.array(vals)
        overall = max(overall, vals.max())
        print("  sigma %.2f: max L_1/2 - 2M1 = %+.3e ; fraction returning within 1e-6 of 2M1: %.2f ; min %+.3e"
              % (sig, vals.max() - 2 * M1, np.mean(vals > 2 * M1 - 1e-6), vals.min() - 2 * M1), flush=True)
    print("  overall max L_1/2 - 2M1 = %+.3e" % (overall - 2 * M1))


def main():
    if sys.argv[1] == "seeded":
        return seeded(int(sys.argv[2]), int(sys.argv[3]))
    n = int(sys.argv[1])
    seed = int(sys.argv[2])
    nW, nU, nV = (int(x) for x in sys.argv[3:6]) if len(sys.argv) > 5 else (2, 4, 4)
    rng = np.random.default_rng(seed)
    TY, TZ = bssc()
    TY2, TZ2 = product2(TY), product2(TZ)
    shape = (nW, nU, nV, 4)

    def obj(th):
        e = np.exp(th - th.max())
        P = (e / e.sum()).reshape(shape)
        a, b, J = forms(P, TY2, TZ2)
        return -(0.5 * a + 0.5 * b + J)
    best = (-np.inf, None)
    vals = []
    for s in range(n):
        th0 = rng.normal(size=int(np.prod(shape))) * rng.choice([1.0, 3.0, 6.0])
        r = minimize(obj, th0, method='L-BFGS-B', options={'maxiter': 20000, 'ftol': 1e-15, 'gtol': 1e-10})
        vals.append(-r.fun)
        if -r.fun > best[0]:
            best = (-r.fun, r.x)
    e = np.exp(best[1] - best[1].max())
    P = (e / e.sum()).reshape(shape)
    a, b, J = forms(P, TY2, TZ2)
    vals = np.sort(vals)[::-1]
    print("BSSC^2, |W|,|U|,|V| = %d,%d,%d, %d starts (seed %d)" % (nW, nU, nV, n, seed))
    print("  best L_1/2 found      = %.12f bits" % best[0])
    print("  2 x one-letter Marton = %.12f bits;  difference = %+.3e" % (2 * M1, best[0] - 2 * M1))
    print("  Marton value min{L_0,L_1} at best = %.12f" % (min(a, b) + J))
    print("  top-5 local values:", " ".join("%.9f" % v for v in vals[:5]))
    print("  fraction of starts within 1e-6 of 2M1: %.3f" % np.mean(vals > 2 * M1 - 1e-6))


if __name__ == "__main__":
    main()
