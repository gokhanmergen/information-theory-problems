#!/usr/bin/env python3
"""Lagrangian upper bound for the HW parallel-channel functional (companion to
hw_parallel_bound.py).  For lam in [0,1] and any tangent point t0,
  min(R1,R2,O1,O2) <= lam/2 (R1+R2) + (1-lam)/2 (O1+O2)
and O1 = P2 h(P11/P2) is concave and 1-homogeneous in (P2,P11), hence
  O1 <= -log2(1-t0) P2 + log2((1-t0)/t0) P11   (tangent plane through the origin),
which is linear in the mixing measure; same for O2.  So
  HW <= D(lam,t0) := max_{alpha,beta in [0,1]} [lam/2 (r1+r2) + (1-lam)/2 (L1+L2)](alpha,beta).
The max over (alpha,beta) is evaluated on a uniform grid (NOT a rigorous bound: no
interval/Lipschitz control of the grid error), so this is a numerical cross-check only.
"""
import numpy as np
from scipy.optimize import minimize_scalar
import hw_parallel_bound as H

N = 2001
g = np.linspace(0, 1, N)
AL, BE = np.meshgrid(g, g, indexing="ij")
P = H.p_hw(AL, BE)
r1 = BE * H.h(AL) + (1 - BE) * (H.h((1 - AL) * (1 - P)) - (1 - AL) * H.h(P))
r2 = AL * H.h(BE) + (1 - AL) * (H.h((1 - BE) * P) - (1 - BE) * H.h(P))

def D(lam, t0):
    c1, c2 = -np.log2(1 - t0), np.log2((1 - t0) / t0)
    L = c1 * (AL + BE) / 2 + c2 * AL * BE
    return (lam * (r1 + r2) / 2 + (1 - lam) * L).max()

best = None
for t0 in np.linspace(0.60, 0.72, 61):
    r = minimize_scalar(lambda l: D(l, t0), bounds=(0, 1), method="bounded", options={"xatol": 1e-7})
    if best is None or r.fun < best[0]:
        best = (r.fun, r.x, t0)
# refine t0
r2_ = minimize_scalar(lambda t: minimize_scalar(lambda l: D(l, t), bounds=(0, 1), method="bounded",
                      options={"xatol": 1e-8}).fun, bounds=(best[2] - 0.005, best[2] + 0.005),
                      method="bounded", options={"xatol": 1e-8})
lam = minimize_scalar(lambda l: D(l, r2_.x), bounds=(0, 1), method="bounded", options={"xatol": 1e-9}).x
print(f"grid {N}x{N}: min dual value = {r2_.fun:.7f} at lam = {lam:.6f}, t0 = {r2_.x:.6f}")
