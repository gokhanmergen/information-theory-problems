"""Exploration: no-FB sum capacity, CL k=1 and k=2 sum-rates (numerical lower bounds), cooperative bound,
for a few small binary-input MACs outside Willems' class.  Usage: python explore.py [restarts]"""
import sys
import time
import numpy as np
from mac_cl import (super_channel, optimize_weighted, nofb_sum_rate, coop_sum_rate,
                    bross_lapidoth_mac)

restarts = int(sys.argv[1]) if len(sys.argv) > 1 else 8


def noisy_adder(eps):
    """Y = X1 + X2 in {0,1,2}, then with prob eps replaced by a uniform symbol."""
    W = np.zeros((2, 2, 3))
    for a in range(2):
        for b in range(2):
            W[a, b] = eps / 3
            W[a, b, a + b] += 1 - eps
    return W


def noisy_and(eps):
    """Y = X1 AND X2 through BSC(eps)."""
    W = np.zeros((2, 2, 2))
    for a in range(2):
        for b in range(2):
            y = a & b
            W[a, b, y] = 1 - eps; W[a, b, 1 - y] = eps
    return W


channels = {
    "BL q=0.10": bross_lapidoth_mac(0.10),
    "BL q=0.25": bross_lapidoth_mac(0.25),
    "BL q=0.40": bross_lapidoth_mac(0.40),
    "BL q=0.50": bross_lapidoth_mac(0.50),
    "noisy adder eps=0.1": noisy_adder(0.1),
    "noisy adder eps=0.3": noisy_adder(0.3),
}

for name, W in channels.items():
    t0 = time.time()
    nofb = nofb_sum_rate(W, grid=201)
    coop_lo, coop_hi = coop_sum_rate(W)
    _, _, V1 = super_channel(W, 1)
    r1 = optimize_weighted(V1, 1, nu=4, restarts=restarts, seed=1)
    _, _, V2 = super_channel(W, 2)
    r2 = optimize_weighted(V2, 2, nu=3, restarts=restarts, seed=2)
    print(f"{name:22s} noFB={nofb:.6f}  CL1={r1['sum_rate']:.6f}  CL2>={r2['sum_rate']:.6f}  "
          f"coop={coop_lo:.6f}  (A1+A2,B)_2=({(r2['A1']+r2['A2'])/2:.6f},{r2['B']/2:.6f})  "
          f"[{time.time()-t0:.0f}s]", flush=True)
