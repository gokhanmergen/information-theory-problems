#!/usr/bin/env python3
"""Symmetric rate of Shannon's k-letter strategy inner bound G_k for Blackwell's BMC.

Channel: Y1 = Y2 = Y = X1 AND X2.  A k-letter strategy S_i maps the past outputs
Y^{j-1} to X_{i,j}.  Since Y^k is a deterministic function of (S1, S2),

    I(S1; Y^k | S2) = H(Y^k | S2),     I(S2; Y^k | S1) = H(Y^k | S1).

Symmetric rate of G_k (time sharing included, as in the Lean definition):

    sym(G_k) = max_{p1, p2}  [H(Y^k|S2) + H(Y^k|S1)] / (2k)

(the max of the average equals the sup of min(R1,R2) over time-shared product
distributions: swap the roles of the users and time-share 1/2-1/2).

Exact reduction.  For the BMC, if a user sends 0 the output is 0 whatever the other
user does, so a strategy's values on output histories inconsistent with its own past
inputs are irrelevant.  Reduced strategies are trees: N(0)=1, N(k)=N(k-1)+N(k-1)^2,
i.e. 2, 6, 42, 1806 for k = 1..4.  Merging strategies with identical outcome rows is
exact for both H(Y|S2) and H(Y|S1).

Optimisation.  F(p1,p2) = H(Y|S2) + H(Y|S1) is concave in p1 for fixed p2 (and vice
versa): H(Y|S2) = I(S1; (Y,S2)) for the DMC s1 -> (y,s2) with law p2(s2)[y=f(s1,s2)],
and H(Y|S1) = sum_s1 p1(s1) c(s1) is linear.  Each half-step is therefore a
Blahut-Arimoto iteration with linear "cost" c (monotone ascent):
    p1(s1) <- p1(s1) * 2^{D(s1) + c(s1)} / Z,
    D(s1)  = sum_s2 p2(s2) log2 1/P_{s2}(f(s1,s2)),  P_{s2}(y) = sum_s1 p1(s1)[f(s1,s2)=y].
Alternating these is a block-coordinate ascent on a biconcave function: it finds
partial optima only, so many random restarts are used.  Results are LOWER bounds on
sym(G_k) (each returned value is exactly evaluated at an explicit distribution);
they are not certified global maxima.

Usage:  python bmc_gk.py K RESTARTS ITERS SEED
"""
import sys
import json
import numpy as np


def reduced_trees(k):
    """Reduced k-step BMC strategies as nested tuples (x, children)."""
    if k == 0:
        return [None]
    sub = reduced_trees(k - 1)
    out = []
    for c in sub:              # send 0: output is 0, one continuation
        out.append((0, (c,)))
    for c0 in sub:             # send 1: output reveals the other input
        for c1 in sub:
            out.append((1, (c0, c1)))
    return out


def outcome_table(trees, k):
    n = len(trees)
    T = np.zeros((n, n), dtype=np.int64)
    for a, t1 in enumerate(trees):
        for b, t2 in enumerate(trees):
            u, v, code = t1, t2, 0
            for j in range(k):
                x1, x2 = u[0], v[0]
                y = x1 & x2
                code |= y << j
                u = u[1][y] if x1 == 1 else u[1][0]
                v = v[1][y] if x2 == 1 else v[1][0]
            T[a, b] = code
    return T


def dedup(T):
    """Merge strategies of user 1 with identical rows and of user 2 with identical
    columns (exact for the objective)."""
    _, r_idx = np.unique(T, axis=0, return_index=True)
    T = T[np.sort(r_idx)]
    _, c_idx = np.unique(T, axis=1, return_index=True)
    T = T[:, np.sort(c_idx)]
    return T


def H2(P, axis):
    with np.errstate(divide="ignore", invalid="ignore"):
        L = np.where(P > 0, -P * np.log2(P), 0.0)
    return L.sum(axis=axis)


class Problem:
    def __init__(self, T, ny):
        self.T = T                      # n1 x n2 outcome codes
        self.ny = ny
        self.n1, self.n2 = T.shape

    def cond_dists(self, p1, p2):
        """A[y, s2] = P(Y=y | S2=s2);  B[s1, y] = P(Y=y | S1=s1)."""
        n1, n2, ny, T = self.n1, self.n2, self.ny, self.T
        A = np.bincount((T * n2 + np.arange(n2)[None, :]).ravel(),
                        weights=np.repeat(p1, n2), minlength=ny * n2).reshape(ny, n2)
        B = np.bincount((np.arange(n1)[:, None] * ny + T).ravel(),
                        weights=np.tile(p2, n1), minlength=n1 * ny).reshape(n1, ny)
        return A, B

    def value(self, p1, p2):
        A, B = self.cond_dists(p1, p2)
        HY_S2 = np.dot(p2, H2(A, axis=0))
        HY_S1 = np.dot(p1, H2(B, axis=1))
        return HY_S2, HY_S1

    def step1(self, p1, p2):
        A, B = self.cond_dists(p1, p2)
        c = H2(B, axis=1)
        with np.errstate(divide="ignore"):
            LA = np.where(A > 0, -np.log2(np.maximum(A, 1e-300)), 0.0)
        D = (LA[self.T, np.arange(self.n2)[None, :]] * p2[None, :]).sum(axis=1)
        e = D + c
        w = p1 * np.exp2(e - e.max())
        return w / w.sum()

    def transpose(self):
        return Problem(self.T.T.copy(), self.ny)


def optimise(prob, probT, rng, iters, init=None):
    n1, n2 = prob.n1, prob.n2
    if init is None:
        p1 = rng.dirichlet(np.full(n1, rng.choice([0.2, 1.0, 3.0])))
        p2 = rng.dirichlet(np.full(n2, rng.choice([0.2, 1.0, 3.0])))
    else:
        p1, p2 = init
    for it in range(iters):
        for _ in range(3):
            p1 = prob.step1(p1, p2)
        for _ in range(3):
            p2 = probT.step1(p2, p1)
    a, b = prob.value(p1, p2)
    return (a + b), p1, p2


def main():
    k = int(sys.argv[1])
    restarts = int(sys.argv[2])
    iters = int(sys.argv[3])
    seed = int(sys.argv[4])
    rng = np.random.default_rng(seed)
    trees = reduced_trees(k)
    T = outcome_table(trees, k)
    n_red = len(trees)
    Td = dedup(T)
    prob = Problem(Td, 2 ** k)
    probT = prob.transpose()
    best = (-1, None, None)
    vals = []
    for r in range(restarts):
        v, p1, p2 = optimise(prob, probT, rng, iters)
        vals.append(v / (2 * k))
        if v > best[0]:
            best = (v, p1, p2)
    v, p1, p2 = best
    # polish
    v, p1, p2 = optimise(prob, probT, rng, 20 * iters, init=(p1, p2))
    a, b = prob.value(p1, p2)
    res = {
        "k": k, "reduced_strategies": n_red, "after_dedup": list(Td.shape),
        "restarts": restarts, "iters": iters, "seed": seed,
        "sym_rate": (a + b) / (2 * k), "R1_no_timeshare": a / k, "R2_no_timeshare": b / k,
        "restart_values_top5": sorted(vals)[-5:],
        "support_p1": int((p1 > 1e-6).sum()), "support_p2": int((p2 > 1e-6).sum()),
    }
    print(json.dumps(res, indent=1))
    np.savez(f"bmc_gk_k{k}_seed{seed}.npz", p1=p1, p2=p2, T=Td)


if __name__ == "__main__":
    main()
