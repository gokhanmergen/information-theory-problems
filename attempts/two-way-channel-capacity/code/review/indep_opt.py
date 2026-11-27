# Reviewer search (2026-11-27, Claims 6-7, numerical): full CausalStrat k enumeration and L-BFGS over
# softmax logits. Logged runs: (k, restarts, seed) = (1,50,11), (2,300,11) in indep_opt_k12.out;
# (3,400,12) in indep_opt_k3.out; (3,2000,13) in indep_opt_k3_2000.out.
# Run: python3 indep_opt.py K RESTARTS SEED   Runtime: 1 s (k <= 2), 30 s (3,400), about 3 min (3,2000).
"""Independent numerical search for sym(G_k(BMC)), k = 2, 3 (not using the author's code).
Full CausalStrat k Bool Bool strategies (2^(2^k-1) of them) are enumerated, the outcome table
Y^k = f(s1, s2) is simulated directly, strategies with identical outcome rows are merged
(exact), and F = H(Y|S2) + H(Y|S1) is maximised by L-BFGS on softmax logits, many restarts.
sym(G_k) = max F / (2k)."""
import itertools, sys
import numpy as np
from scipy.optimize import minimize

k = int(sys.argv[1]); restarts = int(sys.argv[2]); seed = int(sys.argv[3])
hists = [(i, h) for i in range(k) for h in itertools.product((0, 1), repeat=i)]
idx = {x: n for n, x in enumerate(hists)}
strats = list(itertools.product((0, 1), repeat=len(hists)))


def play(s1, s2):
    y = []
    for i in range(k):
        h = tuple(y)
        y.append(s1[idx[(i, h)]] & s2[idx[(i, h)]])
    return sum(v << j for j, v in enumerate(y))


Tfull = np.array([[play(a, b) for b in strats] for a in strats])
_, ri = np.unique(Tfull, axis=0, return_index=True)
T = Tfull[np.sort(ri)][:, np.sort(ri)]   # symmetric channel: same classes for both users
n, ny = T.shape[0], 2 ** k
print(f"k={k}: full strategies {len(strats)}, outcome classes {n}")
LN2 = np.log(2)
onehot = np.zeros((n, n, ny)); onehot[np.arange(n)[:, None], np.arange(n)[None, :], T] = 1


def F_and_grad(z):
    u1, u2 = z[:n], z[n:]
    p1 = np.exp(u1 - u1.max()); p1 /= p1.sum()
    p2 = np.exp(u2 - u2.max()); p2 /= p2.sum()
    A = np.einsum('a,aby->by', p1, onehot)       # P(y|s2)
    B = np.einsum('b,aby->ay', p2, onehot)       # P(y|s1)
    lA = np.where(A > 0, np.log2(np.maximum(A, 1e-300)), 0)
    lB = np.where(B > 0, np.log2(np.maximum(B, 1e-300)), 0)
    HA = -(A * lA).sum(1); HB = -(B * lB).sum(1)
    F = p2 @ HA + p1 @ HB
    # dF/dp1(a) = sum_b p2(b) (-log2 A[b,T[a,b]] - 1/ln2) + HB[a]
    g1 = (p2[None, :] * (-lA[np.arange(n)[None, :], T] - 1 / LN2)).sum(1) + HB
    g2 = HA + (p1[:, None] * (-lB[np.arange(n)[:, None], T] - 1 / LN2)).sum(0)
    gu1 = p1 * (g1 - p1 @ g1); gu2 = p2 * (g2 - p2 @ g2)
    return -F, -np.concatenate([gu1, gu2])


rng = np.random.default_rng(seed)
best = -1; vals = []
for r in range(restarts):
    z0 = rng.normal(0, rng.choice([0.5, 2, 5]), 2 * n)
    res = minimize(F_and_grad, z0, jac=True, method='L-BFGS-B', options={'maxiter': 5000, 'gtol': 1e-12, 'ftol': 1e-15})
    v = -res.fun / (2 * k); vals.append(v)
    best = max(best, v)
vals = np.sort(vals)
print(f"best sym rate {best:.10f}; top5 {vals[-5:]}; fraction within 1e-7 of best {(vals > best - 1e-7).mean():.3f}")
