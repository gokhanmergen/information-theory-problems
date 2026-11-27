# Reviewer library (2026-11-27): behavioural evaluator of the BMC k-letter objective
# F = H(Y^k|S2) + H(Y^k|S1), imported by the other scripts in this folder. Not run on its own.
"""Behavioural (per-node) evaluation of the BMC k-letter objective
    F = H(Y^k | S2) + H(Y^k | S1),     sym(G_k) >= F / (2k)   (swap + time-share),
for strategies given as P(x=1 | own history v), v = ((x_1,y_1),...,(x_{t-1},y_{t-1})).
Any behavioural strategy is a product distribution over reduced trees, i.e. a genuine
Ps on CausalStrat k Bool Bool, so every value is a valid LOWER bound on sym(G_k).
Chain rule: H(Y^k|S2) = sum_t E[ 1{x2_t=1} h(P(x1_t=1 | v2_t)) ]  (S1, S2 cond. independent
given user-2's own history v2_t, which is all S2 and Y^{t-1} reveal about S1).
All 4^k joint input sequences are enumerated exactly.
"""
import itertools
import numpy as np


def own_nodes(k):
    """All own histories of length < k with y <= x (reachable), in a fixed order."""
    nodes = []
    for t in range(k):
        for h in itertools.product([(0, 0), (1, 0), (1, 1)], repeat=t):
            nodes.append(h)
    return nodes


def h2(p):
    p = np.clip(p, 0, 1)
    with np.errstate(divide='ignore', invalid='ignore'):
        r = -(p * np.log2(p) + (1 - p) * np.log2(1 - p))
    return np.where((p > 0) & (p < 1), r, 0.0)


class Evaluator:
    def __init__(self, k):
        self.k = k
        self.nodes = own_nodes(k)
        self.nidx = {v: i for i, v in enumerate(self.nodes)}
        seqs = list(itertools.product((0, 1), repeat=2 * k))
        X1 = np.array([s[:k] for s in seqs]); X2 = np.array([s[k:] for s in seqs])
        Y = X1 & X2
        self.X1, self.X2, self.Y = X1, X2, Y
        n = len(seqs)
        self.v1 = np.zeros((n, k), int); self.v2 = np.zeros((n, k), int)
        for r in range(n):
            for t in range(k):
                self.v1[r, t] = self.nidx[tuple((int(X1[r, j]), int(Y[r, j])) for j in range(t))]
                self.v2[r, t] = self.nidx[tuple((int(X2[r, j]), int(Y[r, j])) for j in range(t))]

    def F(self, b1, b2):
        k = self.k
        P1 = np.where(self.X1 == 1, b1[self.v1], 1 - b1[self.v1])   # per-step prob of user 1 action
        P2 = np.where(self.X2 == 1, b2[self.v2], 1 - b2[self.v2])
        # probability of the prefix up to (not incl.) step t
        pre1 = np.cumprod(np.hstack([np.ones((len(P1), 1)), P1[:, :-1]]), axis=1)
        pre2 = np.cumprod(np.hstack([np.ones((len(P2), 1)), P2[:, :-1]]), axis=1)
        pre = pre1 * pre2
        tot = 0.0
        nn = len(self.nodes)
        for t in range(k):
            # mass of prefix, split by own node of user 2 (for H(Y|S2)) and user 1 (for H(Y|S1))
            # sequences sharing the same first t joint pairs are duplicated 4^(k-t) times: use
            # only representatives with all later inputs = 0 to avoid double counting.
            rep = (self.X1[:, t:].sum(1) == 0) & (self.X2[:, t:].sum(1) == 0)
            w = pre[rep, t]
            # user 2 view: P(v2), P(x1_t=1 and v2)
            m2 = np.bincount(self.v2[rep, t], weights=w, minlength=nn)
            a2 = np.bincount(self.v2[rep, t], weights=w * b1[self.v1[rep, t]], minlength=nn)
            m1 = np.bincount(self.v1[rep, t], weights=w, minlength=nn)
            a1 = np.bincount(self.v1[rep, t], weights=w * b2[self.v2[rep, t]], minlength=nn)
            with np.errstate(invalid='ignore', divide='ignore'):
                q1 = np.where(m2 > 0, a2 / np.maximum(m2, 1e-300), 0)
                q2 = np.where(m1 > 0, a1 / np.maximum(m1, 1e-300), 0)
            tot += np.sum(m2 * b2 * h2(q1)) + np.sum(m1 * b1 * h2(q2))
        return tot
