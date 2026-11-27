# Reviewer certificate (2026-11-27, Claim 8): interval lower bound on sym(G_4(BMC)) from a behavioural
# strategy pair rounded to multiples of 1/D, as a product law on the 1806 reduced 4-trees.
# Run: python3 certify_k4.py kort_k4_asym.npz 1000000   (quoted 0.6214031128; also kort_k4_sym.npz,
# k4_lift.npz, k4_behav_best_seed3_sym.npz; logs certify_*.out). Runtime: about 5 s per run. Needs numpy, mpmath.
"""Interval certificate of a lower bound on sym(G_4(BMC)) from a behavioural strategy pair.

1. Round behavioural parameters b(v) to rationals c(v)/D.
2. Enumerate reduced 4-trees (own action at every reachable own node; sending 0 forces y=0),
   each with exact probability prod_v b(v)^{x}(1-b(v))^{1-x} over its reachable nodes
   (a product distribution over trees = a genuine Ps on CausalStrat 4 Bool Bool after
   filling unreachable histories).
3. Simulate the outcome Y^4 for every tree pair, and evaluate
       sym >= [H(Y^4|S2) + H(Y^4|S1)] / 8      (swap + uniform time sharing, Claim 4)
   with exact integer probabilities and mpmath interval logs.
Usage: certify_k4.py file.npz D
"""
import itertools, os, sys
from fractions import Fraction
import numpy as np
from mpmath import iv
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import own_nodes

iv.dps = 40
K = 4
nodes = own_nodes(K)
nidx = {v: i for i, v in enumerate(nodes)}


def trees(t, hist):
    """All reduced subtrees from own history `hist` at time t: list of dict node->action."""
    if t == K:
        return [{}]
    out = []
    for c in trees(t + 1, hist + ((0, 0),)):
        d = dict(c); d[hist] = 0; out.append(d)
    for c0 in trees(t + 1, hist + ((1, 0),)):
        for c1 in trees(t + 1, hist + ((1, 1),)):
            d = dict(c0); d.update(c1); d[hist] = 1; out.append(d)
    return out


def main(path, D):
    z = np.load(path)
    T = trees(0, ())
    print("reduced 4-trees:", len(T))
    res = []
    for b in (z["b1"], z["b2"]):
        c = [int(round(float(x) * D)) for x in b]
        num = []
        for tr in T:
            p = 1
            for v, a in tr.items():
                p *= c[nidx[v]] if a == 1 else D - c[nidx[v]]
            num.append(p)
        L = max(len(tr) for tr in T)
        probs = [p * D ** (L - len(tr)) for p, tr in zip(num, T)]   # numerators over D**L
        assert sum(probs) == D ** L
        res.append(probs)
    p1, p2 = res
    n = len(T)
    acts = [[tr for tr in T]]

    def play(a, b):
        ha, hb, code = (), (), 0
        for t in range(K):
            x1, x2 = a[ha], b[hb]
            y = x1 & x2
            code |= y << t
            ha += ((x1, y),); hb += ((x2, y),)
        return code
    tab = [[play(T[i], T[j]) for j in range(n)] for i in range(n)]
    ln2 = iv.log(iv.mpf(2))

    L = max(len(tr) for tr in T)
    DEN = iv.mpf(D) ** L

    def H(dist):
        s = iv.mpf(0)
        for v in dist.values():
            if v:
                P = iv.mpf(v) / DEN
                s += -P * iv.log(P) / ln2
        return s
    HY_S2 = iv.mpf(0)
    for j in range(n):
        if not p2[j]:
            continue
        dist = {}
        for i in range(n):
            if p1[i]:
                dist[tab[i][j]] = dist.get(tab[i][j], 0) + p1[i]
        HY_S2 += iv.mpf(p2[j]) / DEN * H(dist)
    HY_S1 = iv.mpf(0)
    for i in range(n):
        if not p1[i]:
            continue
        dist = {}
        for j in range(n):
            if p2[j]:
                dist[tab[i][j]] = dist.get(tab[i][j], 0) + p2[j]
        HY_S1 += iv.mpf(p1[i]) / DEN * H(dist)
    print("R1 = H(Y^4|S2)/4 in", HY_S2 / 4)
    print("R2 = H(Y^4|S1)/4 in", HY_S1 / 4)
    print("sym (time-shared) in", (HY_S2 + HY_S1) / 8)


if __name__ == "__main__":
    main(os.path.join(os.path.dirname(os.path.abspath(__file__)), sys.argv[1]), int(sys.argv[2]))
