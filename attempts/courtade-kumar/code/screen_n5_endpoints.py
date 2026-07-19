#!/usr/bin/env python3
"""Screen all 616,126 NPN class representatives of 5-variable Boolean functions
against the n=5 analogues of the endpoint lemmas from the n=4 theorem
(float screening; any near-threshold class would get exact re-checking).

Low-noise criterion (alpha0 = 1e-3, gamma = (1-1e-3)^4, t0 = log2(1000)):
  balanced (k=16):   t0*(gamma*c1 - 1) >= log2(e) + c2
  unbalanced:        1e-3*(t0*max(0, 1-gamma*c1) + log2(e) + c2) <= 1 - H(k/32)
  c1 = (1/32) sum_y b_y,  c2 = (1/32) sum_y b_y log2 b_y.

High-noise criterion (rho0 = 1e-2):
  eps = rho0*A/qmin <= 1/2  and  (W1t + rho0^2*(1-W1t))*(1 + (4/3)*eps) <= 1.

Usage: python3 screen_n5_endpoints.py npn5_reps.bin
"""
import sys

import numpy as np

N, SIZE = 5, 32
ALPHA0, RHO0 = 1e-3, 1e-2
T0 = np.log2(1000.0)
GAMMA = (1 - ALPHA0) ** 4
LOG2E = np.log2(np.e)

reps = np.fromfile(sys.argv[1], dtype=np.uint32)
print(f"loaded {len(reps)} class representatives")

# truth table bits: (nreps, 32)
bits = ((reps[:, None] >> np.arange(SIZE, dtype=np.uint32)[None, :]) & 1).astype(np.int8)
k = bits.sum(axis=1)
nonconst = (k > 0) & (k < SIZE)

# boundary degree b_y: count of neighbors differing
b = np.zeros((len(reps), SIZE), dtype=np.int8)
for i in range(N):
    nb = np.arange(SIZE) ^ (1 << i)
    b += (bits != bits[:, nb]).astype(np.int8)
c1 = b.sum(axis=1) / SIZE
blog = np.where(b > 0, np.log2(np.maximum(b, 1)), 0.0)
c2 = (b * blog).sum(axis=1) / SIZE

q1 = k / SIZE
with np.errstate(divide="ignore", invalid="ignore"):
    Hq = np.where(nonconst, -(q1 * np.log2(np.where(q1 > 0, q1, 1)) +
                              (1 - q1) * np.log2(np.where(q1 < 1, 1 - q1, 1))), 0.0)
m0 = 1 - Hq

# Fourier of indicator via Walsh-Hadamard on the 32-point truth table
H1 = np.array([[1, 1], [1, -1]], dtype=np.float64)
W = H1
for _ in range(N - 1):
    W = np.kron(W, H1)
hat = bits.astype(np.float64) @ W.T / SIZE      # (nreps, 32), hat[:,0] = q1
w1_ind = (hat[:, [1 << i for i in range(N)]] ** 2).sum(axis=1)
q0q1 = q1 * (1 - q1)
with np.errstate(divide="ignore", invalid="ignore"):
    W1t = np.where(nonconst, w1_ind / np.where(q0q1 > 0, q0q1, 1), 0.0)
A = np.abs(hat[:, 1:]).sum(axis=1)
qmin = np.minimum(q1, 1 - q1)

dictator = nonconst & np.isclose(W1t, 1.0, atol=1e-12)
target = nonconst & ~dictator
print(f"non-constant non-dictator classes: {target.sum()} "
      f"(dictator classes: {dictator.sum()})")

balanced = target & (k == SIZE // 2)
low_bal_ok = T0 * (GAMMA * c1 - 1) >= LOG2E + c2
low_unb_ok = ALPHA0 * (T0 * np.maximum(0, 1 - GAMMA * c1) + LOG2E + c2) <= m0
low_fail = target & ~np.where(balanced, low_bal_ok, low_unb_ok)

eps = RHO0 * A / np.where(qmin > 0, qmin, 1)
val = (W1t + RHO0 ** 2 * (1 - W1t)) * (1 + 4 / 3 * eps)
high_fail = target & ~((eps <= 0.5) & (val <= 1))

print(f"low-noise  lemma failures: {low_fail.sum()}")
print(f"high-noise lemma failures: {high_fail.sum()}")
print(f"balanced non-dictator min boundary edges: "
      f"{(b.sum(axis=1)[balanced].min() // 2) if balanced.any() else 'n/a'} "
      f"(dictator has 16)")
print(f"max W1t among targets: {W1t[target].max():.6f}; "
      f"max eps: {eps[target].max():.4f}; max val: {val[target].max():.6f}")
if low_fail.any():
    idx = np.where(low_fail)[0][:5]
    print("low-noise failing examples:", [hex(int(reps[i])) for i in idx],
          "k:", k[idx].tolist(), "c1:", c1[idx].round(3).tolist())
if high_fail.any():
    idx = np.where(high_fail)[0][:5]
    print("high-noise failing examples:", [hex(int(reps[i])) for i in idx],
          "k:", k[idx].tolist(), "W1t:", W1t[idx].round(4).tolist(),
          "eps:", eps[idx].round(3).tolist())
