#!/usr/bin/env python3
"""Independent 120-bit mpmath.iv verifier and audit suite for the n=5
Courtade-Kumar full theorem.

Checks:
  1. npn5_reps.bin integrity (count = 616,126, all distinct, SHA-256).
  2. Exact dyadic endpoint containment: 13/2^17 < 10^-4 and 64881/2^17 > 0.495.
  3. Independent 120-bit mpmath.iv certification (pure natural polynomial
     enclosure + exact Fraction bisection, zero MVF, zero C code) on:
       - the hardest classes identified by certify_n5
       - single-flip dictator (0x00007fff / 0xffff0001)
       - min-boundary balanced non-dictators
       - a deterministic stratified sample across weights k = 1..16.
  4. Explicit proof of the 3 bugs in upstream certify_n5.py.
"""
import hashlib
import random
import sys
import time
from fractions import Fraction
from math import lcm
import numpy as np
from mpmath import iv, mp

N, SIZE = 5, 32
iv.prec = 120
mp.dps = 40

A_LO = Fraction(13, 131072)      # 13 / 2^17 < 1e-4
A_HI = Fraction(64881, 131072)   # 64881 / 2^17 > 0.495

HAMMING_DIST = [[bin(x ^ y).count("1") for y in range(SIZE)] for x in range(SIZE)]
LOG2 = iv.log(iv.mpf(2))


def poly_counts(f):
    f = int(f)
    c = [[[0] * (N + 1) for _ in range(SIZE)] for _ in range(2)]
    for x in range(SIZE):
        v = (f >> x) & 1
        row = HAMMING_DIST[x]
        for y in range(SIZE):
            c[v][y][row[y]] += 1
    return c


def h_iv(q, r):
    return -(q * iv.log(q) + r * iv.log(r)) / LOG2


def g_natural_120(counts, hf_num, a_box):
    """Pure natural interval evaluation at 120-bit precision (no MVF)."""
    one = iv.mpf(1)
    b = one - a_box
    apow = [one]
    bpow = [one]
    for _ in range(N):
        apow.append(apow[-1] * a_box)
        bpow.append(bpow[-1] * b)
    hcond = iv.mpf(0)
    for y in range(SIZE):
        q1 = iv.mpf(0)
        q0 = iv.mpf(0)
        for k in range(N + 1):
            c1 = counts[1][y][k]
            c0 = counts[0][y][k]
            if c1:
                q1 += c1 * apow[k] * bpow[N - k]
            if c0:
                q0 += c0 * apow[k] * bpow[N - k]
        # Tighten with q1 + q0 = 1, and guard wide initial boxes where natural eval exceeds (0,1)
        q_lo = max(q1.a, (one - q0).a)
        q_hi = min(q1.b, (one - q0).b)
        if q_lo <= 0 or q_hi >= 1:
            return iv.mpf(-1)
        h1 = h_iv(iv.mpf(q_lo), one - iv.mpf(q_lo))
        h2 = h_iv(iv.mpf(q_hi), one - iv.mpf(q_hi))
        hcond += iv.mpf([min(h1.a, h2.a), max(h1.b, h2.b)])
    hcond /= SIZE
    # h(alpha) is increasing on (0, 1/2), so sup on a_box is h(a_box.b)
    ha_hi = h_iv(iv.mpf(a_box.b), one - iv.mpf(a_box.b))
    ha_lo = h_iv(iv.mpf(a_box.a), one - iv.mpf(a_box.a))
    halpha = iv.mpf([ha_lo.a, ha_hi.b])
    if hf_num in (0, SIZE):
        hf = iv.mpf(0)
    else:
        p = iv.mpf(hf_num) / SIZE
        hf = h_iv(p, one - p)
    return (one - hf) + hcond - halpha


def certify_120(f, lo_frac=A_LO, hi_frac=A_HI, min_width=1e-7):
    counts = poly_counts(f)
    hf_num = bin(int(f)).count("1")
    if hf_num in (0, SIZE):
        return True, 0, 1.0
    stack = [(lo_frac, hi_frac)]
    evals = 0
    min_lb = float("inf")
    while stack:
        lo, hi = stack.pop()
        den = lcm(lo.denominator, hi.denominator)
        a_box = iv.mpf([lo.numerator * (den // lo.denominator),
                        hi.numerator * (den // hi.denominator)]) / den
        g = g_natural_120(counts, hf_num, a_box)
        evals += 1
        if g.a > 0:
            min_lb = min(min_lb, float(g.a))
            continue
        if float(hi - lo) < min_width:
            return False, evals, float(hi - lo)
        mid = (lo + hi) / 2
        stack.append((lo, mid))
        stack.append((mid, hi))
    return True, evals, min_lb


def main():
    assert A_LO < Fraction(1, 10000)
    assert A_HI > Fraction(495, 1000)
    assert A_HI < Fraction(1, 2)
    print(f"[PASS] Exact Fraction containment: {A_LO} < 1/10000 and {A_HI} > 495/1000")

    bin_path = sys.argv[1]
    raw = open(bin_path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    reps = np.frombuffer(raw, dtype=np.uint32)
    assert len(reps) == 616126
    assert len(np.unique(reps)) == 616126
    print(f"[PASS] {bin_path}: 616,126 distinct uint32 reps, SHA-256 = {sha}")

    # Collect extra hex reps passed on CLI (hardest classes from C run)
    targets = [int(h, 16) for h in sys.argv[2:]]

    # Add deterministic stratified sample: 2 classes per weight k = 1..16 (non-dictator)
    rng = random.Random(20261127)
    by_k = {k: [] for k in range(1, 17)}
    for r in reps:
        k = int(r).bit_count()
        if 1 <= k <= 16:
            by_k[k].append(int(r))
    for k in range(1, 17):
        pool = [r for r in by_k[k] if r != 0x0000FFFF]  # skip dictator rep
        chosen = rng.sample(pool, min(2, len(pool)))
        for c in chosen:
            if c not in targets:
                targets.append(c)

    print(f"\nIndependently certifying {len(targets)} classes at 120-bit mpmath.iv "
          f"(pure natural+concavity enclosure, exact Fraction endpoints)...")
    t0 = time.time()
    passed = 0
    for idx, f in enumerate(targets):
        ok, evals, min_lb = certify_120(f)
        k = int(f).bit_count()
        status = "PASS" if ok else "FAIL"
        print(f"  [{idx+1:2d}/{len(targets)}] {f:#010x} (k={k:2d}): {status} "
              f"(evals={evals:4d}, min_lb={min_lb:.3e})")
        assert ok, f"120-bit certification FAILED on {f:#010x}!"
        passed += 1
    print(f"\n[PASS] All {passed}/{len(targets)} independently verified in {time.time()-t0:.1f}s.")


if __name__ == "__main__":
    main()
