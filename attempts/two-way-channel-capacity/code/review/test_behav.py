# Reviewer check (2026-11-27): behavioural projection of the author's k = 3 optimum (g3_rational.json)
# reproduces 0.6196448091917556; writes g3_behav.npz next to this script.
# Run: python3 test_behav.py
# Runtime: about 1 s. Needs numpy.
import json, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import Evaluator

here = os.path.dirname(os.path.abspath(__file__))
E1 = Evaluator(1)
print("k=1 at 0.703506:", E1.F(np.array([0.703506]), np.array([0.703506])) / 2)
d = json.load(open(os.path.join(here, "g3_rational.json")))
E = Evaluator(3)


def action(tree, v):
    node = tree
    for (x, y) in v:
        if node[0] != x:
            return None
        node = node[1][y] if x == 1 else node[1][0]
    return node[0]


def behav(p):
    b = np.zeros(len(E.nodes))
    for i, v in enumerate(E.nodes):
        num = den = 0
        for t, w in zip(d["trees"], p):
            a = action(t, v)
            if a is None:
                continue
            den += w
            num += w * a
        b[i] = num / den if den > 0 else 0.5
    return b


b1, b2 = behav(d["p1"]), behav(d["p2"])
print("k=3 behavioural projection of author's rational optimum: sym =", E.F(b1, b2) / 6)
np.savez(os.path.join(here, "g3_behav.npz"), b1=b1, b2=b2)
for v, x, y in zip(E.nodes, b1, b2):
    print(v, round(x, 5), round(y, 5))
