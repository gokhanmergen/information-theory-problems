#!/usr/bin/env python3
"""Minimum energy per bit at unit gains: cutset vs first-order EGN 2022 lower bounds, and EMZ
Example 1 (with bursting) as an upper bound.  Non-rigorous (grid + local refinement).

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

By EMZ 2006 Thm. 1, E* = inf over the power ratio kappa = P2/P1 of lim_{t->0} (1+kappa) t / C(t, kappa t).
A first-order upper bound F(kappa) on C (units t/2 nats) gives E*/(2 ln 2) >= inf_kappa (1+kappa)/F(kappa).
With g12 = g13 = g23 = 1 and direction (p1, p2) = (1, kappa): a12 = a13 = 1, a23 = kappa.
Prints, for each kappa, the normalised energies E/(2 ln 2) of
  cutset (lower bound), first-order EGN (lower bound), EMZ Example 1 + bursting (upper bound).
Expected (2026-11-27 run): cutset min 0.75 at kappa ~ 0.2;  EGN min ~0.934 at kappa ~ 0.07-0.1;
Example 1 never below 1 (direct transmission).

Run:  python3 egn_energy_per_bit.py    (a few minutes)
Requires numpy.
"""
import numpy as np
from egn2 import egn_first
from egn_lowsnr import cutset_first, ex1_rate

LN2 = np.log(2)

if __name__ == "__main__":
    best_cs, best_eg = np.inf, np.inf
    for kappa in [0.001, 0.003, 0.01, 0.02, 0.03, 0.05, 0.07, 0.1, 0.15, 0.2, 0.3, 0.5, 1.0, 1.5]:
        cs = cutset_first(1.0, 1.0, kappa)
        eg, _ = egn_first(1.0, 1.0, kappa, 1.0, kappa, n=161)
        ex = max(ex1_rate(1, 1, 1, P, kappa * P) / P for P in np.geomspace(0.01, 10, 80))  # nats/t
        e_cs, e_eg = (1 + kappa) / cs, (1 + kappa) / eg
        e_ex = (1 + kappa) / (2 * ex)
        best_cs, best_eg = min(best_cs, e_cs), min(best_eg, e_eg)
        print(f"kappa={kappa:6.3f}: E/2ln2  cutset >= {e_cs:.4f}   EGN >= {e_eg:.4f}   "
              f"Ex.1+burst <= {e_ex:.4f}", flush=True)
    print(f"min over kappa: cutset {best_cs:.4f} (exact 3/4), EGN {best_eg:.4f}")
