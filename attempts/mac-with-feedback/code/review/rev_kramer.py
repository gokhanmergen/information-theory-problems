# Reviewer side-check (2026-11-27, Found (d), uncertified floats): Kramer's noisy adder MAC with the
# author's ../mac_cl.py: k = 1 CL max sum vs 2*0.43621, then the k = 2 optimiser (seed 7); log rev_kramer.log.
# Run: python3 rev_kramer.py [STARTS]   (default 4 random k = 2 starts, as in the note's run)
# Runtime: about 3-4.5 min with 4 starts (about 1 min per start). Needs numpy, scipy.
"""Reviewer side-check: Kramer's binary additive noisy MAC Y = X1 + X2 + N, N ~ Bern(1/2), Y in {0,1,2,3}
(Kramer 1998/2003 as reported by Tandon-Ulukus 2009: CL symmetric rate 0.43621, code-tree scheme 0.43879).
(1) validates the author's k=1 machinery against the published CL value (max sum = 2*0.43621);
(2) tries the author's k=2 optimiser (random starts) to see whether R^(2) (Lean sense) beats CL here."""
import os
import sys
import time
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))  # author's code/
from mac_cl import super_channel, cl_quantities, unpack

W = np.zeros((2, 2, 4))
for x1 in range(2):
    for x2 in range(2):
        for n in range(2):
            W[x1, x2, x1 + x2 + n] += 0.5

def smin(a, b, beta):
    m = min(a, b)
    return m - np.log(np.exp(-beta * (a - m)) + np.exp(-beta * (b - m))) / beta

def run(V, k, nu, z0, betas=(1e2, 1e3, 1e4), maxiter=3000):
    n1, n2, _ = V.shape
    z = z0
    for beta in betas:
        def obj(zz):
            pu, P1, P2 = unpack(zz, nu, n1, n2)
            A1, A2, B = cl_quantities(pu, P1, P2, V)
            return -smin(A1 + A2, B, beta) / k
        z = minimize(obj, z, method="L-BFGS-B", options=dict(maxiter=maxiter, maxfun=10 ** 6)).x
    pu, P1, P2 = unpack(z, nu, n1, n2)
    A1, A2, B = cl_quantities(pu, P1, P2, V)
    return min(A1 + A2, B) / k

rng = np.random.default_rng(7)
t0 = time.time()
_, _, V1 = super_channel(W, 1)
v1 = max(run(V1, 1, 3, rng.normal(scale=2, size=3 * 5)) for _ in range(10))
print(f"k=1 CL max sum-rate (numerical) = {v1:.6f}  vs 2*0.43621 = 0.87242  [{time.time()-t0:.0f}s]", flush=True)
_, _, V2 = super_channel(W, 2)
n = V2.shape[0]
best = 0
for s in range(int(sys.argv[1]) if len(sys.argv) > 1 else 4):
    v = run(V2, 2, 3, rng.normal(scale=2, size=3 * (1 + 2 * n)), maxiter=1500)
    best = max(best, v)
    print(f"  k=2 start {s}: {v:.6f} (best {best:.6f})  [{time.time()-t0:.0f}s]", flush=True)
print(f"k=2 best found {best:.6f} vs k=1 {v1:.6f}: gain {best - v1:.2e}")
