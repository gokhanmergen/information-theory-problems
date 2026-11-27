#!/usr/bin/env python3
"""Continue the k = 4 alternating Blahut-Arimoto ascent from a saved point.

Usage: python bmc_g4_continue.py IN.npz OUT.npz SWEEPS REPORT_EVERY
(each sweep = 3 + 3 BA half-steps, as in bmc_gk.optimise).  Reported in the attempt file:
  python bmc_g4_continue.py bmc_gk_k4_seed6.npz bmc_gk_k4_seed6_cont.npz 2000 250
  (log: g4_continue_seed6.log)
"""
import sys
import json
import time
import numpy as np
import bmc_gk as G

d = np.load(sys.argv[1])
T, p1, p2 = d["T"], d["p1"], d["p2"]
sweeps, every = int(sys.argv[3]), int(sys.argv[4])
prob = G.Problem(T, 16)
probT = prob.transpose()
t0 = time.time()
for s in range(1, sweeps + 1):
    for _ in range(3):
        p1 = prob.step1(p1, p2)
    for _ in range(3):
        p2 = probT.step1(p2, p1)
    if s % every == 0:
        a, b = prob.value(p1, p2)
        print(json.dumps({"sweep": s, "sym_rate": (a + b) / 8, "t": round(time.time() - t0)}), flush=True)
        np.savez(sys.argv[2], p1=p1, p2=p2, T=T)
