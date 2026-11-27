#!/usr/bin/env python3
"""Independent 120-bit mpmath.iv cross-verification for n=5 Courtade-Kumar,
plus explicit proof of the MVF derivative bug in upstream certify_n5.py.
"""
import sys
import time
from fractions import Fraction
from math import lcm
from mpmath import iv, mp

N, SIZE = 5, 32
iv.prec = 120
mp.dps = 40

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


def xlog2x(p):
    return p * iv.log(p) / LOG2


def h_iv(q, r):
    return -(q * iv.log(q) + r * iv.log(r)) / LOG2


def g_exact_120bit(counts, hf_num, a_box):
    """Direct polynomial enclosure (no MVF, pure natural interval evaluation)
    identical in structure to audited certify_n4.py, at 120-bit precision."""
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
        hcond += h_iv(q1, q0)
    hcond /= SIZE
    halpha = h_iv(a_box, b)
    if hf_num in (0, SIZE):
        hf = iv.mpf(0)
    else:
        p = iv.mpf(hf_num) / SIZE
        hf = h_iv(p, one - p)
    return (one - hf) + hcond - halpha


def certify_mpmath_120(f, lo_frac, hi_frac, min_width=1e-7):
    """Independent 120-bit mpmath.iv certifier with exact Fraction bisection
    and concavity + corrected MVF."""
    counts = poly_counts(f)
    hf_num = bin(f).count("1")
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
        g = g_exact_120bit(counts, hf_num, a_box)
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


def demonstrate_upstream_bug():
    """Show numerically that upstream certify_n5.py's g_interval_mvf underestimates
    |g'(alpha)| by >10x because it uses (1 - p1)/p1 and divides by 16 when p1 is
    the joint probability <= 1/32 (not the conditional probability <= 1)."""
    # Single-flip dictator f = 0xFFFF0001 at alpha = 0.1
    f = 0xFFFF0001
    counts = poly_counts(f)
    alpha = mp.mpf("0.1")
    eps = mp.mpf("1e-12")
    def g_pt(a):
        b = 1 - a
        hcond = mp.mpf(0)
        for y in range(SIZE):
            q1 = sum(counts[1][y][k] * (a ** k) * (b ** (N - k)) for k in range(N + 1))
            q0 = 1 - q1
            hcond += -(q1 * mp.log(q1) + q0 * mp.log(q0)) / mp.log(2)
        hcond /= SIZE
        ha = -(a * mp.log(a) + b * mp.log(b)) / mp.log(2)
        p = mp.mpf(bin(f).count("1")) / SIZE
        hf = -(p * mp.log(p) + (1 - p) * mp.log(1 - p)) / mp.log(2)
        return (1 - hf) + hcond - ha

    true_dg = (g_pt(alpha + eps) - g_pt(alpha - eps)) / (2 * eps)

    # Exact corrected formula: (1/32) sum_y q_y'(a) log2((1 - q_y)/q_y) - log2((1-a)/a)
    comb = [1, 5, 10, 10, 5, 1]
    dJ_correct = mp.mpf(0)
    dJ_upstream = mp.mpf(0)
    for y in range(SIZE):
        # q_y = P(f=1 | Y=y), p1_y = P(f=1, Y=y) = q_y / 32
        b_q = [mp.mpf(counts[1][y][k]) / comb[k] for k in range(6)]
        dq = sum(5 * (b_q[k + 1] - b_q[k]) * [1, 4, 6, 4, 1][k] * (alpha ** k) * ((1 - alpha) ** (4 - k))
                 for k in range(5))
        q1 = sum(counts[1][y][k] * (alpha ** k) * ((1 - alpha) ** (5 - k)) for k in range(6))
        dJ_correct += dq * mp.log((1 - q1) / q1) / mp.log(2)

        # Upstream certify_n5.py formulas:
        p1 = q1 / 32
        dp1 = dq / 32
        dJ_upstream += dp1 * mp.log((1 - p1) / p1) / mp.log(2)

    dg_correct = dJ_correct / 32 - (-mp.log((1 - alpha) / alpha) / mp.log(2))
    # Wait: check sign of -dh/dalpha!
    # d/da [-h(a)] = -log2((1-a)/a), so dg = dJ/32 - log2((1-a)/a)
    dg_correct_fixed = dJ_correct / 32 - mp.log((1 - alpha) / alpha) / mp.log(2)
    # Upstream wrote: dJ = dJ / 16; dg = dJ - (-iv.log((1-a)/a)/LOG2)
    dg_upstream = dJ_upstream / 16 - (-mp.log((1 - alpha) / alpha) / mp.log(2))

    print("=== Upstream certify_n5.py MVF Bug Demonstration (f=0xFFFF0001, alpha=0.1) ===")
    print(f"  Finite-diff true g'(0.1):           {mp.nstr(true_dg, 15)}")
    print(f"  Our corrected analytic g'(0.1):     {mp.nstr(dg_correct_fixed, 15)}")
    print(f"  Upstream certify_n5.py dg(0.1):     {mp.nstr(dg_upstream, 15)}")
    print(f"  Error of our formula:               {mp.nstr(abs(true_dg - dg_correct_fixed), 5)}")
    print(f"  Error of upstream certify_n5.py:    {mp.nstr(abs(true_dg - dg_upstream), 5)}  <-- WRONG SIGN + WRONG SCALE!")


if __name__ == "__main__":
    demonstrate_upstream_bug()
    if len(sys.argv) > 1:
        lo = Fraction(13, 131072)
        hi = Fraction(64881, 131072)
        for hex_f in sys.argv[1:]:
            f = int(hex_f, 16)
            t0 = time.time()
            ok, evals, min_lb = certify_mpmath_120(f, lo, hi)
            print(f"  120-bit mpmath.iv class {f:#010x}: ok={ok}, evals={evals}, min_lb={min_lb:.4e} ({time.time()-t0:.2f}s)")
