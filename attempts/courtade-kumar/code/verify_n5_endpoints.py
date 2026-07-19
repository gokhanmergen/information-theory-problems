#!/usr/bin/env python3
"""Exact verification of the two n=5 endpoint-lemma hypotheses.

The input is one uint32 truth table from each five-variable NPN class.  The
low-noise expressions depend only on the output weight and the histogram of
the 32 boundary degrees, so each such profile is checked with Fraction
arithmetic and proved rational logarithm enclosures.  The high-noise
expressions are checked for every class by integer Walsh transforms and
cross-multiplication; floating point is not used in either decision.

Usage:
    python3 verify_n5_endpoints.py [npn5_reps.bin]
"""
import os
import sys
from fractions import Fraction as F

import numpy as np

N, SIZE = 5, 32

# Rational bounds LO[p] <= log2(p) <= HI[p].  The proof of every enclosure is
# rerun by verify_log_bounds() before the class checks.
LOG2_LO = {
    3: F(15849, 10000), 5: F(23219, 10000), 7: F(28073, 10000),
    11: F(34594, 10000), 13: F(37004, 10000),
    17: F(40874, 10000), 19: F(42479, 10000),
    23: F(45235, 10000), 29: F(48579, 10000),
    31: F(49541, 10000),
}
LOG2_HI = {
    3: F(15850, 10000), 5: F(23220, 10000), 7: F(28074, 10000),
    11: F(34595, 10000), 13: F(37005, 10000),
    17: F(40875, 10000), 19: F(42480, 10000),
    23: F(45236, 10000), 29: F(48580, 10000),
    31: F(49542, 10000),
}
LOG2E_HI = F(14427, 10000)

ALPHA0 = F(1, 10000)
T0_LO = 4 * (1 + LOG2_LO[5])  # log2(10000)=4(1+log2(5))
T0_HI = 4 * (1 + LOG2_HI[5])
GAMMA = (1 - ALPHA0) ** 4      # beta=alpha(1-alpha)^(n-1), n=5
RHO0 = F(1, 100)


def verify_log_bounds():
    """Prove all hard-coded logarithm bounds with integer arithmetic."""
    for p, lo in LOG2_LO.items():
        assert 2 ** lo.numerator <= p ** lo.denominator
    for p, hi in LOG2_HI.items():
        assert p ** hi.denominator <= 2 ** hi.numerator

    # ln(2)=2*sum_{j>=0} 1/((2j+1)3^(2j+1)).  A finite positive
    # partial sum is a rigorous lower bound.  This proves
    # log2(e)=1/ln(2) <= 14427/10000.
    ln2_lower = F(0)
    for j in range(20):
        ln2_lower += F(2, (2 * j + 1) * 3 ** (2 * j + 1))
    assert ln2_lower >= 1 / LOG2E_HI


def log2_bounds(n):
    """Return proved rational lower and upper bounds for log2(n), 1<=n<=32."""
    if n == 1:
        return F(0), F(0)
    lo = hi = F(0)
    m = n
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
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


def entropy_upper(k):
    """Proved rational upper bound on h(k/32)."""
    lo_k = log2_bounds(k)[0] if k else F(0)
    lo_j = log2_bounds(SIZE - k)[0] if SIZE - k else F(0)
    return 5 - (k * lo_k + (SIZE - k) * lo_j) / SIZE


def low_noise_profile_ok(k, degree_histogram):
    """Exactly check one (weight, boundary-degree histogram) profile."""
    c1 = sum(degree * count for degree, count in enumerate(degree_histogram)) / F(SIZE)
    c2_upper = sum(
        F(count * degree, SIZE) * log2_bounds(degree)[1]
        for degree, count in enumerate(degree_histogram) if degree
    )
    if k == SIZE // 2:
        return T0_LO * (GAMMA * c1 - 1) >= LOG2E_HI + c2_upper

    entropy_gap_lower = 1 - entropy_upper(k)
    t_coefficient = max(F(0), 1 - GAMMA * c1)
    loss_upper = ALPHA0 * (T0_HI * t_coefficient + LOG2E_HI + c2_upper)
    return loss_upper <= entropy_gap_lower


def main():
    verify_log_bounds()
    default_path = "attempts/courtade-kumar/code/npn5_reps.bin"
    bin_path = sys.argv[1] if len(sys.argv) > 1 else default_path
    if not os.path.exists(bin_path):
        print(f"Error: {bin_path} not found. Run npn5 to generate it.")
        return 1

    reps = np.fromfile(bin_path, dtype=np.uint32)
    if len(reps) != 616126:
        print(f"Error: loaded {len(reps)} representatives, expected 616126.")
        return 1
    if len(np.unique(reps)) != len(reps):
        print("Error: representative file contains duplicates.")
        return 1
    print(f"Loaded {len(reps)} distinct representatives.")

    bits = ((reps[:, None] >> np.arange(SIZE, dtype=np.uint32)) & 1).astype(np.int8)
    k = bits.sum(axis=1).astype(np.int16)

    # Exact integer Walsh transform.  If a_S is the unnormalized coefficient,
    # then q0*q1=k(32-k)/1024, W1=sum_i a_{i}^2/[k(32-k)], and
    # A=sum_{S!=empty}|a_S|/32.
    hadamard = np.array([[1, 1], [1, -1]], dtype=np.int16)
    for _ in range(N - 1):
        hadamard = np.kron(hadamard, np.array([[1, 1], [1, -1]], dtype=np.int16))
    walsh = bits.astype(np.int16) @ hadamard.T
    denominator = k.astype(np.int64) * (SIZE - k).astype(np.int64)
    w1_numerator = (walsh[:, [1 << i for i in range(N)]].astype(np.int64) ** 2).sum(axis=1)
    spectral_l1_numerator = np.abs(walsh[:, 1:].astype(np.int64)).sum(axis=1)

    nonconstant = denominator > 0
    dictator = nonconstant & (w1_numerator == denominator)
    target = nonconstant & ~dictator
    print(f"Nonconstant nondictator classes: {target.sum()} (dictators: {dictator.sum()}).")

    # Low-noise data.  The criterion uses only k and counts of b_y=0,...,5.
    boundary_degree = np.zeros((len(reps), SIZE), dtype=np.int8)
    cube_points = np.arange(SIZE)
    for i in range(N):
        boundary_degree += bits != bits[:, cube_points ^ (1 << i)]
    hist = np.stack([(boundary_degree == degree).sum(axis=1) for degree in range(N + 1)], axis=1)
    profiles = np.column_stack((k[target], hist[target])).astype(np.int16)
    unique_profiles = np.unique(profiles, axis=0)
    bad_profiles = []
    for profile in unique_profiles:
        if not low_noise_profile_ok(int(profile[0]), [int(v) for v in profile[1:]]):
            bad_profiles.append(profile.tolist())
    print(f"Exact low-noise profiles checked: {len(unique_profiles)}; failures: {len(bad_profiles)}.")

    # High-noise criterion at rho0=1/100, checked by integer cross-products:
    # eps=Aint/(100*m)<=1/2 and
    # ((9999*W+D)/(10000*D))*((300*m+4*Aint)/(300*m))<=1.
    m = np.minimum(k, SIZE - k).astype(np.int64)
    eps_ok = 2 * spectral_l1_numerator <= 100 * m
    left = (9999 * w1_numerator + denominator) * (300 * m + 4 * spectral_l1_numerator)
    right = (10000 * denominator) * (300 * m)
    high_ok = eps_ok & (left <= right)
    bad_high = np.where(target & ~high_ok)[0]
    print(f"Exact high-noise classes checked: {target.sum()}; failures: {len(bad_high)}.")

    if bad_profiles or len(bad_high):
        if bad_profiles:
            print("First bad low-noise profiles:", bad_profiles[:5])
        if len(bad_high):
            print("First bad high-noise truth tables:", [hex(int(reps[i])) for i in bad_high[:5]])
        return 1
    print("ALL CLASSES PASSED EXACTLY.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
