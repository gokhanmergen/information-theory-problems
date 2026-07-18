#!/usr/bin/env python3
"""Certified verification of the Courtade-Kumar conjecture at n=4 over a
closed noise interval, for ALL Boolean functions (not a grid).

For each NPN equivalence class of f: {0,1}^4 -> {0,1} (input permutations x
input flips x output complement; MI is invariant under all three), certifies

    g_f(alpha) = 1 - h(alpha) - I(f(X);Y) > 0

for all alpha in [A_LO, A_HI], by adaptive bisection with outward-rounded
interval arithmetic (mpmath.iv). Uses that Y is uniform and P(f(X)=v) is
constant in alpha, so
    g(alpha) = H(f(X),Y)(alpha) - h(alpha) - (n-1) - H(f(X)),
with the 2 x 16 joint entries exact integer-coefficient polynomials
    p_{v,y}(alpha) = 2^-4 sum_k c_{v,y,k} alpha^k (1-alpha)^{4-k},
    c_{v,y,k} = #{x : f(x)=v, d(x,y)=k}.

The dictator class (g == 0) is excluded and reported separately; every other
class must certify strictly positive. Output: per-class status + summary.

Requires mpmath. Run: .venv/bin/python certify_n4.py [A_LO A_HI]
"""
import sys
import time
from itertools import permutations

from mpmath import iv, mp

N, SIZE, FULL = 4, 16, 0xFFFF
iv.prec = 90


# ---------------------------------------------------------------- NPN classes

def npn_classes():
    maps = []
    for perm in permutations(range(N)):
        for flips in range(SIZE):
            m = []
            for x in range(SIZE):
                y = x ^ flips
                m.append(sum(((y >> perm[i]) & 1) << i for i in range(N)))
            maps.append(m)
    seen = bytearray(1 << SIZE)
    reps = []
    for f in range(1 << SIZE):
        if seen[f]:
            continue
        orbit = set()
        for m in maps:
            g = 0
            for x in range(SIZE):
                if (f >> m[x]) & 1:
                    g |= 1 << x
            orbit.add(g)
            orbit.add(g ^ FULL)
        for g in orbit:
            seen[g] = 1
        reps.append((min(orbit), len(orbit)))
    return reps


# ---------------------------------------------------------------- g_f interval

def poly_counts(f):
    """c[v][y][k] and P(f=1) numerator."""
    c = [[[0] * (N + 1) for _ in range(SIZE)] for _ in range(2)]
    for x in range(SIZE):
        v = (f >> x) & 1
        for y in range(SIZE):
            c[v][y][bin(x ^ y).count('1')] += 1
    return c


LOG2 = iv.log(iv.mpf(2))


def xlog2x(p):
    """p*log2(p) for interval p with inf(p) > 0."""
    return p * iv.log(p) / LOG2


def g_interval(counts, hf_num, a):
    """Interval enclosure of g(alpha) for alpha-interval a."""
    one = iv.mpf(1)
    b = one - a
    apow = [one, a, a * a, a * a * a, a * a * a * a]
    bpow = [one, b, b * b, b * b * b, b * b * b * b]
    hjoint = iv.mpf(0)
    for v in (0, 1):
        for y in range(SIZE):
            ck = counts[v][y]
            s = iv.mpf(0)
            nonzero = False
            for k in range(N + 1):
                if ck[k]:
                    s += ck[k] * apow[k] * bpow[N - k]
                    nonzero = True
            if nonzero:
                hjoint -= xlog2x(s / SIZE)
    halpha = -xlog2x(a) - xlog2x(b)
    # H(f(X)) exact: hf_num ones out of 16
    if hf_num in (0, SIZE):
        hf = iv.mpf(0)
    else:
        p = iv.mpf(hf_num) / SIZE
        hf = -xlog2x(p) - xlog2x(1 - p)
    return hjoint - halpha - (N - 1) - hf


def certify(f, a_lo, a_hi, min_width=1e-7):
    counts = poly_counts(f)
    hf_num = bin(f).count('1')
    stack = [(mp.mpf(a_lo), mp.mpf(a_hi))]
    evals, worst = 0, None
    while stack:
        lo, hi = stack.pop()
        g = g_interval(counts, hf_num, iv.mpf([lo, hi]))
        evals += 1
        if g.a > 0:      # certified positive on this subinterval (inf > 0)
            continue
        width = float(hi - lo)
        if worst is None or width < worst:
            worst = width
        if width < min_width:
            return False, evals, width
        mid = (lo + hi) / 2
        stack.append((lo, mid))
        stack.append((mid, hi))
    return True, evals, worst


# ---------------------------------------------------------------- fourier data

def w1(f):
    """Level-1 Fourier weight of (-1)^f, exact rational as float."""
    tot = 0
    for i in range(N):
        s = sum((1 - 2 * ((f >> x) & 1)) * (1 - 2 * ((x >> i) & 1))
                for x in range(SIZE))
        tot += s * s
    return tot / SIZE ** 2


def boundary_edges(f):
    return sum(1 for x in range(SIZE) for i in range(N)
               if x < x ^ (1 << i) and ((f >> x) & 1) != ((f >> (x ^ (1 << i))) & 1))


DICTATOR_CLASS = min  # placeholder; computed below


if __name__ == "__main__":
    a_lo, a_hi = (sys.argv[1], sys.argv[2]) if len(sys.argv) > 2 else ("0.005", "0.495")
    t0 = time.time()
    reps = npn_classes()
    print(f"NPN classes: {len(reps)} (expected 222); "
          f"orbit sizes sum = {sum(s for _, s in reps)} (expected 65536)")
    dict_rep = min({sum(1 << x for x in range(SIZE) if (x >> i) & 1)
                    for i in range(N)} | {0xFFFF ^ sum(1 << x for x in range(SIZE)
                                                       if (x >> 0) & 1)})
    # canonical rep of the dictator class = min over its orbit; find it:
    dict_class = None
    for rep, size in reps:
        # class contains a dictator iff some orbit member is one; check via w1 == 1
        if abs(w1(rep) - 1.0) < 1e-12:
            dict_class = rep
    ok, failed = 0, []
    max_w1_nondict, min_bnd_balanced = 0.0, 999
    for rep, size in reps:
        if rep == dict_class:
            print(f"class {rep:#06x} (dictators, orbit {size}): excluded (g == 0)")
            continue
        max_w1_nondict = max(max_w1_nondict, w1(rep))
        if bin(rep).count('1') == 8:
            min_bnd_balanced = min(min_bnd_balanced, boundary_edges(rep))
        good, evals, worst = certify(rep, a_lo, a_hi)
        if good:
            ok += 1
        else:
            failed.append((rep, worst))
            print(f"class {rep:#06x}: FAILED to certify (worst width {worst})")
    print(f"\ncertified g > 0 on [{a_lo}, {a_hi}] for {ok} of {len(reps) - 1} "
          f"non-dictator classes; failures: {len(failed)}")
    print(f"max level-1 Fourier weight among non-dictator classes: "
          f"{max_w1_nondict:.6f} (dictators have 1)")
    print(f"min boundary edges among balanced non-dictator classes: "
          f"{min_bnd_balanced} (dictators have 8)")
    print(f"elapsed {time.time() - t0:.1f}s, iv.prec = {iv.prec}")
