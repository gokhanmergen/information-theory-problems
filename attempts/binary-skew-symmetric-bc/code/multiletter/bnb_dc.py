#!/usr/bin/env python3
"""
Simplicial branch-and-bound UPPER bound on the two-letter BSSC dual
    B_2(1/2, 0) = max_{P_UVX}  G(P),   G = 1/2 H(Y^2) + 1/2 H(Z^2) - H(U,Y^2) - H(V,Z^2) + H(U,V)
over the cardinality-reduced family (Anantharam-Gohari-Nair 2019, Thm 3): X = f(U,V),
(|U|,|V|) in {(2,3),(3,2)} for every map f, plus the branches (U const, V = X) and
(U = X, V const) on the 4-ary product input.

DC bound.  G = c + k with c = 1/2 H(Y^2) + 1/2 H(Z^2) + H(U,V) concave and k = -H(U,Y^2) - H(V,Z^2)
convex in P (entropies of linear images of P).  On a simplex S = conv{v_0..v_d} with centroid x0
(interior to the probability simplex, so c is differentiable there):
    c(x) <= c(x0) + grad c(x0).(x - x0) =: l(x)            (concavity)
    k(x) <= sum_i lam_i k(v_i)  for x = sum_i lam_i v_i    (convexity)
hence  G(x) <= sum_i lam_i [l(v_i) + k(v_i)] <= max_i [l(v_i) + k(v_i)] =: UB(S).
A simplex is discarded when UB(S) <= target; otherwise it is bisected along its longest edge.
The branches (1,4)/(4,1) use the same bound on the 3-simplex of P_X.

Arithmetic: float64 numpy.  Every entropy is a sum of at most 64 terms |p log2 p| <= 0.531, and
gradients involve log2 of probabilities >= 1e-300; the absolute rounding error of each UB(S)
is far below 1e-10.  We discard only when UB(S) <= target - MARGIN... no: we use
    discard  iff  UB(S) + MARGIN <= target,   MARGIN = 1e-9,
so the reported statement 'max G <= target' is robust to rounding errors of that size.  This
is NOT outward-rounded interval arithmetic; see the attempt file for the status of the claim.

Usage: python bnb_dc.py eps [maxleaves] [a:b | k/n]   (problem range, or interleaved shard k of n)
   proves (if it terminates) B_2(1/2,0) <= 2 B_1(1/2,0) + eps, map by map.
       python bnb_dc.py proto
   the feasibility prototype quoted in the attempt file (three problems, eps in {0.1,0.03,0.01},
   cap 3e6 simplices).
       python bnb_dc.py negctl
   negative controls (targets below attained values must abort, never 'PROVED').
"""
import sys
import time
import numpy as np
from ml_core import bssc, product2, canonical_maps, B1

MARGIN = 1e-9
TY, TZ = bssc()
TY2, TZ2 = product2(TY), product2(TZ)


def xlog(p):
    return np.where(p > 0, p * np.log2(np.where(p > 0, p, 1.0)), 0.0)


class MapProblem:
    """X = f(U,V); P is a vector of length nu*nv (row-major (u,v))."""

    def __init__(self, F):
        F = np.asarray(F)
        self.nu, self.nv = F.shape
        n = self.nu * self.nv
        self.n = n
        # linear maps P -> P_Y2 (4), P_Z2 (4), P_{U,Y2} (nu*4), P_{V,Z2} (nv*4), P_UV (n)
        uu, vv = np.divmod(np.arange(n), self.nv)
        fx = F.ravel()
        self.AY = TY2[fx].T                       # (4, n)
        self.AZ = TZ2[fx].T
        AUY = np.zeros((self.nu * 4, n))
        AVZ = np.zeros((self.nv * 4, n))
        for j in range(n):
            AUY[uu[j] * 4:(uu[j] + 1) * 4, j] = TY2[fx[j]]
            AVZ[vv[j] * 4:(vv[j] + 1) * 4, j] = TZ2[fx[j]]
        self.AUY, self.AVZ = AUY, AVZ

    def c_and_grad(self, X):
        """X: (m, n) interior points -> c (m,), grad (m, n)."""
        pY, pZ = X @ self.AY.T, X @ self.AZ.T
        c = -0.5 * xlog(pY).sum(1) - 0.5 * xlog(pZ).sum(1) - xlog(X).sum(1)
        lg = lambda p: np.log2(np.maximum(p, 1e-300))
        g = (-0.5 * lg(pY) @ self.AY - 0.5 * lg(pZ) @ self.AZ - lg(X))
        # constant parts of the gradient (-1/ln2 per unit mass) cancel on the simplex: drop
        return c, g

    def k(self, V):
        """V: (..., n) points (may lie on faces)."""
        return xlog(V @ self.AUY.T).sum(-1) + xlog(V @ self.AVZ.T).sum(-1)

    def G(self, V):
        pY, pZ = V @ self.AY.T, V @ self.AZ.T
        return (-0.5 * xlog(pY).sum(-1) - 0.5 * xlog(pZ).sum(-1) - xlog(V).sum(-1) + self.k(V))


class BranchProblem:
    """(U const, V = X): G = -1/2 H(Y2) + 1/2 H(Z2) - sum p(x) H(Z2|x); mirror for U = X."""

    def __init__(self, which):
        self.n = 4
        HY2x = -xlog(TY2).sum(1)
        HZ2x = -xlog(TZ2).sum(1)
        if which == "V=X":
            self.Ac, self.Ak, self.lin = TZ2.T, TY2.T, -HZ2x   # concave +1/2 H(Z), convex -1/2 H(Y)
        else:
            self.Ac, self.Ak, self.lin = TY2.T, TZ2.T, -HY2x

    def c_and_grad(self, X):
        p = X @ self.Ac.T
        c = -0.5 * xlog(p).sum(1) + X @ self.lin
        g = -0.5 * np.log2(np.maximum(p, 1e-300)) @ self.Ac + self.lin
        return c, g

    def k(self, V):
        return 0.5 * xlog(V @ self.Ak.T).sum(-1)

    def G(self, V):
        return -0.5 * xlog(V @ self.Ac.T).sum(-1) + V @ self.lin + self.k(V)


def bnb(prob, target, maxleaves=10 ** 8, batch=20000):
    """Returns (status, n_processed, best_lower_value_seen)."""
    n = prob.n
    stack = [np.eye(n)[None]]                       # list of arrays (m, n_vertices=n, n)
    processed = 0
    best_low = -np.inf
    while stack:
        S = stack.pop()
        if S.shape[0] > batch:
            stack.append(S[batch:])
            S = S[:batch]
        processed += S.shape[0]
        if processed > maxleaves:
            return "ABORT", processed, best_low
        x0 = S.mean(1)
        c0, g0 = prob.c_and_grad(x0)
        lin = c0[:, None] + np.einsum('mn,mvn->mv', g0, S - x0[:, None, :])
        kv = prob.k(S)
        ub = (lin + kv).max(1)
        gv = prob.G(S).max(1)
        best_low = max(best_low, gv.max(), prob.G(x0).max())
        keep = ub + MARGIN > target
        if not keep.any():
            continue
        S = S[keep]
        # bisect longest edge
        d = np.linalg.norm(S[:, :, None, :] - S[:, None, :, :], axis=-1)
        m = d.reshape(S.shape[0], -1).argmax(1)
        i, j = np.divmod(m, n)
        mid = 0.5 * (S[np.arange(len(S)), i] + S[np.arange(len(S)), j])
        A = S.copy()
        Bm = S.copy()
        A[np.arange(len(S)), i] = mid
        Bm[np.arange(len(S)), j] = mid
        stack.append(np.concatenate([A, Bm]))
    return "PROVED", processed, best_low


def proto():
    b1 = B1(TY, TZ, 0.5, [0, 0])
    for eps in (1e-1, 3e-2, 1e-2):
        for name, p in (("V=X branch", BranchProblem("V=X")),
                        ("f=[[0,2,2],[1,3,3]] (product optimum)", MapProblem([[0, 2, 2], [1, 3, 3]])),
                        ("f=[[0,1,2],[3,0,1]] (generic)", MapProblem([[0, 1, 2], [3, 0, 1]]))):
            t = time.time()
            st, k, low = bnb(p, 2 * b1 + eps, maxleaves=3e6)
            print("eps %.0e  %-40s %-7s simplices %8d  [%.1fs]" % (eps, name, st, k, time.time() - t), flush=True)


def negctl():
    """Negative controls: targets below a known attained value must never be PROVED."""
    b1 = B1(TY, TZ, 0.5, [0, 0])
    st, k, low = bnb(MapProblem([[0, 2, 2], [1, 3, 3]]), 2 * b1 - 1e-3, maxleaves=2e6)
    print('product map, target 2B1-1e-3:', st, k, 'best sampled-2B1=%.2e' % (low - 2 * b1))
    st, k, low = bnb(BranchProblem('V=X'), 2 * b1 + 0.01, maxleaves=2e6)
    print('V=X branch at 2B1+0.01:', st, k, 'best sampled-2B1=%.4e' % (low - 2 * b1))
    st, k, _ = bnb(BranchProblem('V=X'), low - 1e-4, maxleaves=2e6)
    print('V=X branch, target = its sampled max - 1e-4:', st, k)


if __name__ == "__main__":
    if sys.argv[1] in ("proto", "negctl"):
        {"proto": proto, "negctl": negctl}[sys.argv[1]]()
        sys.exit()
    eps = float(sys.argv[1])
    maxleaves = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10 ** 7
    rng_spec = sys.argv[3] if len(sys.argv) > 3 else None
    b1 = B1(TY, TZ, 0.5, [0, 0])
    target = 2 * b1 + eps
    print("2 B_1(1/2,0) = %.12f ; target = 2B_1 + %.1e" % (2 * b1, eps), flush=True)
    probs = [("V=X", BranchProblem("V=X")), ("U=X", BranchProblem("U=X"))]
    for tag, (nu, nv) in (("23", (2, 3)), ("32", (3, 2))):
        for F in canonical_maps(nu, nv):
            probs.append((tag + ":" + "".join(map(str, F.ravel())), MapProblem(F)))
    if rng_spec:
        if "/" in rng_spec:          # interleaved shard k/n
            k, nsh = map(int, rng_spec.split("/"))
            probs = probs[k::nsh]
        else:
            a, b = map(int, rng_spec.split(":"))
            probs = probs[a:b]
    t0 = time.time()
    tot = 0
    all_ok = True
    for name, pr in probs:
        st, k, low = bnb(pr, target, maxleaves)
        tot += k
        all_ok = all_ok and st == "PROVED"
        print("%-12s %-7s simplices %10d  best sampled G - 2B1 = %+.3e  [%.0fs]"
              % (name, st, k, low - 2 * b1, time.time() - t0), flush=True)
    print("total simplices", tot)
    print("SHARD RESULT:", "ALL PROVED" if all_ok else "NOT ALL PROVED", "(%d problems)" % len(probs))
