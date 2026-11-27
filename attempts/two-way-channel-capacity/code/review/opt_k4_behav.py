# Reviewer search (2026-11-27, Claim 8, numerical): L-BFGS-B over behavioural strategies (40 params per
# user at k = 4). Logged runs: 4 150 4 -> k4_asym.out (0.62085593, the note's 0.62086), 4 150 3 symmetric
# -> k4_sym.out. Writes k{K}_behav_best_seed{SEED}[_sym].npz here. Run: python3 opt_k4_behav.py K RESTARTS SEED
# [symmetric]. Runtime: 5-8 min for 150 restarts (about 3 s per restart). Needs numpy, scipy.
"""Search sym(G_k(BMC)) over behavioural strategies (40 parameters per user for k = 4),
L-BFGS-B on [0,1]^80 with central finite differences, random + structured starts.
Usage: opt_k4_behav.py K RESTARTS SEED [symmetric]"""
import os, sys, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import Evaluator

k = int(sys.argv[1]); R = int(sys.argv[2]); seed = int(sys.argv[3])
sym_only = len(sys.argv) > 4 and sys.argv[4] == "symmetric"
E = Evaluator(k); n = len(E.nodes)
here = os.path.dirname(os.path.abspath(__file__))


def obj(z):
    b1 = z[:n]; b2 = z[:n] if sym_only else z[n:]
    return -E.F(b1, b2) / (2 * k)


dim = n if sym_only else 2 * n
rng = np.random.default_rng(seed)
best = (-1, None); vals = []
starts = []
# structured start: after first (1,1) play the k-1 optimum found so far is unknown; use 0.7035
for r in range(R):
    mode = r % 3
    if mode == 0:
        z0 = rng.uniform(0, 1, dim)
    elif mode == 1:
        z0 = np.clip(0.70351 + rng.normal(0, 0.25, dim), 0, 1)
    else:
        z0 = rng.beta(0.5, 0.5, dim)
    res = minimize(obj, z0, method="L-BFGS-B", bounds=[(0, 1)] * dim,
                   options={"maxiter": 3000, "ftol": 1e-15, "gtol": 1e-10, "eps": 1e-8})
    v = -res.fun; vals.append(v)
    if v > best[0]:
        best = (v, res.x.copy())
vals = np.sort(vals)
v, z = best
b1 = z[:n]; b2 = z[:n] if sym_only else z[n:]
R1 = None
print(f"k={k} sym_only={sym_only} restarts={R}: best half-sum rate {v:.8f}")
print("top 8:", np.round(vals[-8:], 6))
np.savez(os.path.join(here, f"k{k}_behav_best_seed{seed}{'_sym' if sym_only else ''}.npz"), b1=b1, b2=b2, val=v)
