# Reviewer search (2026-11-27, Claim 8, numerical): k = 4 behavioural search from structured starts
# built on g3_behav.npz. Logged run: 30 7 -> k4_struct.out, k4_struct_best_seed7.npz.
# Run: python3 opt_k4_struct.py N SEED
# Runtime: about 85 s for N = 30. Needs numpy, scipy.
"""k=4 behavioural search from structured starts (Kort 1997 hint: after a first output y=1 the
remaining 3 letters face a fresh K3 problem, so copy the K3 optimum there); other nodes are
random or copied from the K3 optimum shifted by one letter.  Usage: opt_k4_struct.py N SEED"""
import os, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import Evaluator, own_nodes

here = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]); seed = int(sys.argv[2])
E = Evaluator(4); nodes = E.nodes; n = len(nodes)
g3 = np.load(os.path.join(here, "g3_behav.npz"))
n3 = own_nodes(3); i3 = {v: i for i, v in enumerate(n3)}
rng = np.random.default_rng(seed)


def start(bb3, noise):
    b = np.empty(n)
    for i, v in enumerate(nodes):
        if len(v) >= 1 and v[0] == (1, 1):
            b[i] = bb3[i3[v[1:]]]                     # fresh K3 after y=1
        elif len(v) <= 2:
            b[i] = bb3[i3[v]]                          # first letters as K3 optimum
        else:
            b[i] = rng.uniform(0, 1)
        b[i] = np.clip(b[i] + rng.normal(0, noise), 0, 1)
    return b


def obj(z):
    return -E.F(z[:n], z[n:]) / 8


best = (-1, None); vals = []
for r in range(N):
    noise = [0.0, 0.05, 0.15][r % 3]
    z0 = np.concatenate([start(g3["b1"], noise), start(g3["b2"], noise)])
    res = minimize(obj, z0, method="L-BFGS-B", bounds=[(0, 1)] * (2 * n),
                   options={"maxiter": 5000, "ftol": 1e-15, "gtol": 1e-10, "eps": 1e-8})
    vals.append(-res.fun)
    if -res.fun > best[0]:
        best = (-res.fun, res.x.copy())
v, z = best
print(f"k=4 structured starts N={N}: best half-sum {v:.8f}; top: {np.round(np.sort(vals)[-6:], 6)}")
print("R1-ish split: H(Y|S2)/4, H(Y|S1)/4 not separated here")
np.savez(os.path.join(here, f"k4_struct_best_seed{seed}.npz"), b1=z[:n], b2=z[n:], val=v)
