#!/usr/bin/env python3
"""Verify both low-noise and high-noise endpoint lemmas exactly over all
616,126 class representatives for n=5, using exact rational arithmetic
for any class near the boundary (margin filter method).
"""
import sys
import os
from fractions import Fraction as F
import numpy as np

N, SIZE = 5, 32

# Rational bounds: LO[x] <= log2(x) <= HI[x]
LOG2_LO = {3: F(15849, 10000), 5: F(23219, 10000), 7: F(28073, 10000),
           11: F(34594, 10000), 13: F(37004, 10000)}
LOG2_HI = {3: F(15850, 10000), 5: F(23220, 10000), 7: F(28074, 10000),
           11: F(34595, 10000), 13: F(37005, 10000)}
LOG2E_HI = F(14427, 10000)          # log2(e) <= 1.4427
LOG2E_LO = F(14426, 10000)

# Cutover alpha0 = 10^-4.
ALPHA0 = F(1, 10000)
T0_LO = 4 * (1 + LOG2_LO[5])         # log2(10000) = 4*(1 + log2(5))
T0_HI = 4 * (1 + LOG2_HI[5])
GAMMA = (F(9999, 10000)) ** 4

RHO0 = F(1, 100)

def log2_bounds(n):
    """(lower, upper) rational bounds for log2(n), n = 1..SIZE."""
    if n == 0:
        return F(0), F(0)
    lo = hi = F(0)
    m = n
    for p in (2, 3, 5, 7, 11, 13):
        while m % p == 0:
            m //= p
            if p == 2:
                lo += 1
                hi += 1
            else:
                lo += LOG2_LO[p]
                hi += LOG2_HI[p]
    assert m == 1
    return lo, hi

def H_upper(k):
    """Rational upper bound on H(k/SIZE)."""
    lo_k, _ = log2_bounds(k) if k else (F(0), F(0))
    lo_j, _ = log2_bounds(SIZE - k) if SIZE - k else (F(0), F(0))
    return 5 - (k * lo_k + (SIZE - k) * lo_j) / SIZE

def fourier_ind(f):
    """Exact Fourier coefficients of 1_f, hat(S) for S=0..31."""
    return [F(sum((1 if (f >> x) & 1 else 0) *
                  (-1) ** bin(x & S).count('1') for x in range(SIZE)), SIZE)
            for S in range(SIZE)]

def low_noise_exact(k, b):
    c1 = F(sum(b), SIZE)
    c2 = sum(F(by, SIZE) * log2_bounds(by)[1] for by in b if by)
    if k == SIZE // 2:
        return T0_LO * (GAMMA * c1 - 1) >= LOG2E_HI + c2
    m0 = 1 - H_upper(k)
    tcoef = 1 - GAMMA * c1
    dmax = ALPHA0 * ((T0_HI * tcoef if tcoef > 0 else F(0)) + LOG2E_HI + c2)
    return dmax <= m0

def high_noise_exact(k, f):
    q1, q0 = F(k, SIZE), F(SIZE - k, SIZE)
    hat = fourier_ind(f)
    w1 = sum(hat[1 << i] ** 2 for i in range(N)) / (q0 * q1)
    A = sum(abs(hat[S]) for S in range(1, SIZE))
    eps = RHO0 * A / min(q0, q1)
    if eps > F(1, 2):
        return False
    val = (w1 + RHO0 ** 2 * (1 - w1)) * (1 + F(4, 3) * eps)
    return val <= 1

def main():
    bin_path = "attempts/courtade-kumar/code/npn5_reps.bin"
    if not os.path.exists(bin_path):
        print(f"Error: {bin_path} not found. Please run npn5 first.")
        sys.exit(1)
        
    reps = np.fromfile(bin_path, dtype=np.uint32)
    n_reps = len(reps)
    print(f"Loaded {n_reps} representatives.")
    
    # We do a fast float screening to find any potential failures or close calls.
    # Float constants:
    alpha0_f = 1e-4
    rho0_f = 0.01
    gamma_f = (1 - alpha0_f) ** 4
    t0_f = np.log2(10000.0)
    log2e_f = np.log2(np.e)
    
    # Unpack truth tables to bits
    bits = ((reps[:, None] >> np.arange(SIZE, dtype=np.uint32)[None, :]) & 1).astype(np.int8)
    k = bits.sum(axis=1)
    nonconst = (k > 0) & (k < SIZE)
    
    # Calculate boundary degrees
    b = np.zeros((n_reps, SIZE), dtype=np.int8)
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
    
    # Walsh-Hadamard Fourier coefficients
    H1 = np.array([[1, 1], [1, -1]], dtype=np.float64)
    W = H1
    for _ in range(N - 1):
        W = np.kron(W, H1)
    hat = bits.astype(np.float64) @ W.T / SIZE
    w1_ind = (hat[:, [1 << i for i in range(N)]] ** 2).sum(axis=1)
    q0q1 = q1 * (1 - q1)
    with np.errstate(divide="ignore", invalid="ignore"):
        W1t = np.where(nonconst, w1_ind / np.where(q0q1 > 0, q0q1, 1), 0.0)
    A = np.abs(hat[:, 1:]).sum(axis=1)
    qmin = np.minimum(q1, 1 - q1)
    
    dictator = nonconst & np.isclose(W1t, 1.0, atol=1e-12)
    target = nonconst & ~dictator
    
    # Float margins
    balanced = target & (k == SIZE // 2)
    low_bal_margin = t0_f * (gamma_f * c1 - 1) - (log2e_f + c2)
    low_unb_margin = m0 - alpha0_f * (t0_f * np.maximum(0, 1 - gamma_f * c1) + log2e_f + c2)
    low_margin = np.where(balanced, low_bal_margin, low_unb_margin)
    
    eps = rho0_f * A / np.where(qmin > 0, qmin, 1)
    high_margin = 1.0 - (W1t + rho0_f ** 2 * (1 - W1t)) * (1 + 4/3 * eps)
    
    # We check in exact rational arithmetic if float margin is small (say < 1e-4)
    exact_low_check = target & (low_margin < 1e-4)
    exact_high_check = target & (high_margin < 1e-4)
    
    print(f"Float screening done.")
    print(f"Classes requiring exact low-noise check: {exact_low_check.sum()}")
    print(f"Classes requiring exact high-noise check: {exact_high_check.sum()}")
    
    # Exact verification
    fail_low, fail_high = [], []
    
    # Verify low-noise
    low_indices = np.where(exact_low_check)[0]
    for idx in low_indices:
        f = int(reps[idx])
        bk = int(k[idx])
        by = b[idx].tolist()
        if not low_noise_ok_f(bk, by) and not low_noise_exact(bk, by):
            fail_low.append(f)
            
    # Verify high-noise
    high_indices = np.where(exact_high_check)[0]
    for idx in high_indices:
        f = int(reps[idx])
        bk = int(k[idx])
        if not high_noise_exact(bk, f):
            fail_high.append(f)
            
    # As a sanity check, also check if any float margins were negative (which should fail)
    float_low_fail = target & (low_margin < 0.0)
    float_high_fail = target & (high_margin < 0.0)
    
    print(f"Float low-noise fails: {float_low_fail.sum()}")
    print(f"Float high-noise fails: {float_high_fail.sum()}")
    
    if fail_low or fail_high:
        print("FAILURES FOUND!")
        print("Low failures:", [hex(f) for f in fail_low])
        print("High failures:", [hex(f) for f in fail_high])
        sys.exit(1)
    else:
        print("ALL CLASSES PASSED EXACTLY!")
        sys.exit(0)

def low_noise_ok_f(k, b):
    # exact rational checks helper
    return False

if __name__ == "__main__":
    main()
