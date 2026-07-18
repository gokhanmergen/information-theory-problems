#!/usr/bin/env python3
"""Derive the tables reported in the attempt file from results.json and
ba_results.json.  Literature values hard-coded from:

  [FD]  Fertonani & Duman, IEEE T-IT 2010 (arXiv:0810.0785), Table IV
        (upper bounds via genie-aided finite-length channels).
  [DM]  Drinea & Mitzenmacher lower bounds as tabulated in Diggavi,
        Mitzenmacher & Pfister, ISIT 2007, Table I.
  [RC]  Rubinstein & Con, arXiv:2305.07156: C > 0.1221(1-d);
        C < 0.3745(1-d) for d >= 0.68.
  [MD]  Mitzenmacher & Drinea: C > (1-d)/9.
"""

import json
from math import comb, log2
from pathlib import Path

import numpy as np

HERE = Path(__file__).parent
R = json.loads((HERE / "results.json").read_text())
BA = json.loads((HERE / "ba_results.json").read_text())

DS = [0.1, 0.3, 0.5, 0.7, 0.9]
FD_UPPER = {0.1: 0.689, 0.3: 0.362, 0.5: 0.212, 0.7: 0.126, 0.9: 0.049}
DM_LOWER = {0.1: 0.5620, 0.3: 0.2224, 0.5: 0.1019, 0.7: 0.04532, 0.9: 0.01238}


def H_bin(n, p):
    pr = np.array([comb(n, k) * p ** k * (1 - p) ** (n - k) for k in range(n + 1)])
    pr = pr[pr > 0]
    return float(-(pr * np.log2(pr)).sum())


iid = {int(n): {float(d): v for d, v in row.items()} for n, row in R["iid"].items()}
ns = sorted(iid)

print("=== (1/n) I(X^n;Y), i.i.d. Bern(1/2) inputs (exact, bits) ===")
print("n    " + "".join(f"d={d:<10}" for d in DS))
for n in ns:
    print(f"{n:<4d} " + "".join(f"{iid[n][d]/n:<12.6f}"[:12] for d in DS))

print("\n=== monotonicity check: is (1/n) I strictly decreasing in n? ===")
for d in DS:
    seq = [iid[n][d] / n for n in ns]
    dec = all(seq[i + 1] < seq[i] for i in range(len(seq) - 1))
    print(f"d={d}: strictly decreasing over n=1..{ns[-1]}: {dec}")

print("\n=== subadditivity spot check: I_{n+m} <= I_n + I_m ===")
viol = 0
for d in DS:
    for n in ns:
        for m in ns:
            if n + m in iid and iid[n + m][d] > iid[n][d] + iid[m][d] + 1e-9:
                viol += 1
print(f"violations over all computed (n, m, d): {viol}")

print("\n=== rigorous genie (marker) lower bounds on C:  (I_n - H(Bin(n,1-d)))/n ===")
print("(i.i.d. inputs; best n shown; Fertonani-Duman style)")
for d in DS:
    best = max(ns, key=lambda n: (iid[n][d] - H_bin(n, 1 - d)) / n)
    val = (iid[best][d] - H_bin(best, 1 - d)) / best
    print(f"d={d}: best n={best}:  C >= {val:.4f}   "
          f"(H(Bin({best},{1-d:.1f})) = {H_bin(best, 1-d):.4f})")

print("\n=== Blahut-Arimoto on C_n: rigorous upper bounds C <= C_n and "
      "optimized-input genie lower bounds ===")
bans = sorted(int(n) for n in BA["Cn"])
for d in DS:
    print(f"d={d}:")
    for n in bans:
        e = BA["Cn"][str(n)][str(d)]
        hb = BA["H_bin"][str(n)][str(d)]
        up = e["maxD_ub"] / n
        lo = (e["I_lb"] - hb) / n
        gap = (e["maxD_ub"] - e["I_lb"]) / n
        if n == bans[-1] or n in (8, 10):
            print(f"  n={n:2d}:  C <= {up:.4f}   C >= {lo:+.4f}   "
                  f"(BA gap {gap:.2e}, iters {e['iters']})")

print("\n=== comparison with literature at the computed d ===")
print("d     ourC>=(iid,n=18)  ourC>=(BA opt)  ourC<= (BA C_n)  "
      "DM-lower  FD-upper  0.1221(1-d)  (1-d)/9")
nlast = ns[-1]
for d in DS:
    our_lo_iid = (iid[nlast][d] - H_bin(nlast, 1 - d)) / nlast
    nb = bans[-1]
    e = BA["Cn"][str(nb)][str(d)]
    our_lo_opt = (e["I_lb"] - BA["H_bin"][str(nb)][str(d)]) / nb
    our_up = e["maxD_ub"] / nb
    print(f"{d}  {our_lo_iid:+.4f}          {our_lo_opt:+.4f}         "
          f"{our_up:.4f}          {DM_LOWER[d]:.4f}   {FD_UPPER[d]:.3f}    "
          f"{0.1221*(1-d):.4f}      {(1-d)/9:.4f}")

print("\n=== Markov inputs at d=0.5 ===")
mk = {int(n): {float(g): v for g, v in row.items()}
      for n, row in R["markov_d0.5"].items()}
for n in sorted(mk):
    row = mk[n]
    print(f"n={n:2d}: " + "  ".join(f"g={g}: {row[g]/n:.4f}" for g in sorted(row)))
