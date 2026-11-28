#!/usr/bin/env python3
"""
Black-box test of the DC simplex bound used in bnb_dc.py: for random sub-simplices S of the
probability simplex (random size, including ones touching faces) and random points x in S,
check G(x) <= UB(S) (no margin).  Also checks the concave/convex split numerically
(c concave and k convex along random segments).

Usage: python bnb_validity_test.py n_simplices seed
"""
import sys
import numpy as np
from bnb_dc import MapProblem, BranchProblem, canonical_maps


def ub(prob, S):
    x0 = S.mean(1)
    c0, g0 = prob.c_and_grad(x0)
    lin = c0[:, None] + np.einsum('mn,mvn->mv', g0, S - x0[:, None, :])
    return (lin + prob.k(S)).max(1)


def main():
    n, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = np.random.default_rng(seed)
    maps = canonical_maps(2, 3)[::37] + canonical_maps(3, 2)[::41]
    probs = [MapProblem(F) for F in maps] + [BranchProblem("V=X"), BranchProblem("U=X")]
    worst = -np.inf
    worst_conc = -np.inf
    for pr in probs:
        d = pr.n
        # random simplices: centre c on the simplex, vertices c + r * (dirichlet - c), some snapped to faces
        C = rng.dirichlet(np.ones(d) * rng.choice([0.3, 1, 3]), size=n)
        r = 10 ** rng.uniform(-4, 0, size=(n, 1, 1))
        Vt = rng.dirichlet(np.ones(d) * 0.5, size=(n, d))
        S = C[:, None, :] + r * (Vt - C[:, None, :])
        lam = rng.dirichlet(np.ones(d), size=(n, 4))
        X = np.einsum('mkv,mvn->mkn', lam, S)
        u = ub(pr, S)
        g = pr.G(X)
        worst = max(worst, (g - u[:, None]).max())
        # concavity of c / convexity of k along segments
        A, B = rng.dirichlet(np.ones(d), size=n), rng.dirichlet(np.ones(d), size=n)
        t = rng.uniform(size=(n, 1))
        M = t * A + (1 - t) * B
        cA = pr.c_and_grad(A)[0]; cB = pr.c_and_grad(B)[0]; cM = pr.c_and_grad(M)[0]
        kA, kB, kM = pr.k(A), pr.k(B), pr.k(M)
        tt = t[:, 0]
        worst_conc = max(worst_conc, (tt * cA + (1 - tt) * cB - cM).max(), (kM - tt * kA - (1 - tt) * kB).max())
    print("problems tested: %d, simplices per problem: %d, points per simplex: 4" % (len(probs), n))
    print("max over samples of G(x) - UB(S)  = %.3e   (must be <= 0)" % worst)
    print("max concavity/convexity violation = %.3e   (must be <= ~1e-15)" % worst_conc)


if __name__ == "__main__":
    main()
