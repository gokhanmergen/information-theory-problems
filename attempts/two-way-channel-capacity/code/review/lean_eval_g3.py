# Reviewer check (2026-11-27, Claim 7): evaluates the Lean twcKLetterInnerBound 3 formula at the author's
# rational k = 3 law (g3_rational.json) with exact Fractions and mpmath.iv; compares the outcome table.
# Run: python3 lean_eval_g3.py [g3_rational.json]   (output in lean_eval_g3.out)
# Runtime: a few seconds. Needs mpmath.
"""Independent evaluator of the Lean definition `twcKLetterInnerBound 3 binaryMultiplyingChannel`
at an explicit (Pq, Ps1, Ps2).

* Strategies are FULL elements of CausalStrat 3 Bool Bool: a value for every i in Fin 3 and
  every own-output history in Bool^i (1 + 2 + 4 = 7 bits).  A reduced tree is turned into a
  full strategy by following the tree along the history; histories that are inconsistent with
  the tree's own inputs (it sent 0 but saw 1) get the value 0.
* J(q, s1, s2, y) = Pq(q) Ps1_q(s1) Ps2_q(s2) prod_i W.trans((s1 i y1^{<i}, s2 i y2^{<i}), y_i)
  with y : Fin 3 -> Bool x Bool, W.trans(x, y) = [y = (x1&&x2, x1&&x2)].  All 64 y are enumerated
  (no use of determinism), probabilities are exact Fractions.
* rate1 = (1/3) condMutualInfo(map t -> (s1, (y_i.2)_i, (s2, q)))
        = (1/3) [H(S1,S2,Q) + H(Y2,S2,Q) - H(S1,Y2,S2,Q) - H(S2,Q)]       (Core/Entropy.lean)
  rate2 symmetric with Y1.  Entropies in mpmath interval arithmetic.
Design: Q uniform on {0,1}; q=0: (Ps1,Ps2)=(p1,p2); q=1: (p2,p1).
"""
import itertools, json, os, sys
from fractions import Fraction
from collections import defaultdict
from mpmath import iv

iv.dps = 60
K = 3


def tree_to_full(tree):
    """Return dict (i, hist) -> bit for all i < K, hist in {0,1}^i."""
    f = {}
    for i in range(K):
        for hist in itertools.product((0, 1), repeat=i):
            node, ok = tree, True
            for j in range(i):
                x, ch = node
                if x == 1:
                    node = ch[hist[j]]
                else:
                    if hist[j] == 1:      # impossible: own input 0 forces output 0
                        ok = False
                        break
                    node = ch[0]
            f[(i, hist)] = node[0] if ok else 0
    return tuple(f[(i, h)] for i in range(K) for h in itertools.product((0, 1), repeat=i))


IDX = {(i, h): n for n, (i, h) in enumerate(
    (i, h) for i in range(K) for h in itertools.product((0, 1), repeat=i))}


def W(x1, x2, y):
    return 1 if y == (x1 & x2, x1 & x2) else 0


def ent(dist):
    tot = iv.mpf(0)
    ln2 = iv.log(iv.mpf(2))
    for p in dist.values():
        if p == 0:
            continue
        P = iv.mpf(p.numerator) / p.denominator
        tot += -P * iv.log(P) / ln2
    return tot


def main(path):
    d = json.load(open(path))
    D = d["D"]
    full = [tree_to_full(t) for t in d["trees"]]
    assert len(set(full)) == len(full), "two trees map to the same full strategy"
    p1 = {full[a]: Fraction(v, D) for a, v in enumerate(d["p1"]) if v}
    p2 = {full[a]: Fraction(v, D) for a, v in enumerate(d["p2"]) if v}
    assert sum(p1.values()) == 1 and sum(p2.values()) == 1
    ys = list(itertools.product(itertools.product((0, 1), repeat=2), repeat=K))
    J = defaultdict(Fraction)
    # also rebuild the outcome table to compare with the author's T
    mine_T = {}
    for q, (P1, P2) in enumerate([(p1, p2), (p2, p1)]):
        for s1, a in P1.items():
            for s2, b in P2.items():
                tot = Fraction(0)
                for y in ys:
                    pr = 1
                    for i in range(K):
                        h1 = tuple(y[j][0] for j in range(i))
                        h2 = tuple(y[j][1] for j in range(i))
                        x1 = s1[IDX[(i, h1)]]
                        x2 = s2[IDX[(i, h2)]]
                        pr *= W(x1, x2, y[i])
                        if pr == 0:
                            break
                    if pr:
                        J[(q, s1, s2, y)] += Fraction(1, 2) * a * b * pr
                        tot += pr
                assert tot == 1
    assert sum(J.values()) == 1

    def marg(fn):
        m = defaultdict(Fraction)
        for t, p in J.items():
            m[fn(t)] += p
        return m
    # rate 1: (S1 ; Y2 | (S2,Q))
    y2 = lambda t: tuple(yy[1] for yy in t[3])
    y1 = lambda t: tuple(yy[0] for yy in t[3])
    I1 = (ent(marg(lambda t: (t[1], (t[2], t[0])))) + ent(marg(lambda t: (y2(t), (t[2], t[0]))))
          - ent(marg(lambda t: (t[1], y2(t), (t[2], t[0])))) - ent(marg(lambda t: (t[2], t[0]))))
    I2 = (ent(marg(lambda t: (t[2], (t[1], t[0])))) + ent(marg(lambda t: (y1(t), (t[1], t[0]))))
          - ent(marg(lambda t: (t[2], y1(t), (t[1], t[0])))) - ent(marg(lambda t: (t[1], t[0]))))
    R1, R2 = I1 / K, I2 / K
    print("support sizes:", len(p1), len(p2), " |supp J| =", len(J))
    print("rate1 = I(S1;Y2^3|S2,Q)/3 in", R1)
    print("rate2 = I(S2;Y1^3|S1,Q)/3 in", R2)
    print("min lower endpoint:", min(R1.a, R2.a))
    # per-q check (no time sharing)
    for q in (0, 1):
        Jq = {t: p * 2 for t, p in J.items() if t[0] == q}
        def mq(fn):
            m = defaultdict(Fraction)
            for t, p in Jq.items():
                m[fn(t)] += p
            return m
        a = (ent(mq(lambda t: (t[1], t[2]))) + ent(mq(lambda t: (y2(t), t[2])))
             - ent(mq(lambda t: (t[1], y2(t), t[2]))) - ent(mq(lambda t: t[2]))) / K
        print(f"  q={q}: I(S1;Y2|S2)/3 in", a)
    # compare the author's outcome table T[a][b] (code = sum y_j 2^j) with my simulation
    bad = 0
    for a, ta in enumerate(full):
        for b, tb in enumerate(full):
            yy = []
            for i in range(K):
                h = tuple(yy)
                x1, x2 = ta[IDX[(i, h)]], tb[IDX[(i, h)]]
                yy.append(x1 & x2)
            code = sum(v << j for j, v in enumerate(yy))
            bad += code != d["T"][a][b]
    print("outcome-table mismatches vs author's T:", bad)
    rows = {tuple(r) for r in d["T"]}
    print("distinct rows in T:", len(rows), "of", len(d["T"]))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else
         os.path.join(os.path.dirname(os.path.abspath(__file__)), "g3_rational.json"))
