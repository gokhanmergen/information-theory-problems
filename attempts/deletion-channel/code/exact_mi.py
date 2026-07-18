#!/usr/bin/env python3
"""Exact finite-blocklength mutual information for the binary deletion channel.

For input length n and deletion probability d, the channel deletes each bit of
x in {0,1}^n independently with probability d; the output y is the subsequence
of surviving bits (no side information about positions). Then

    P(y | x) = N(x, y) * d^(n-|y|) * (1-d)^|y|,

where N(x, y) = number of deletion patterns (subsets of positions of x) whose
removal leaves exactly y, i.e. the number of embeddings of y into x as a
subsequence. N is computed exactly by the standard DP

    f(i, y) = f(i-1, y) + [y ends in x_i] * f(i-1, y minus last symbol),

vectorized over all 2^(m) strings y of each length m simultaneously (y encoded
as an integer with bits appended at the LSB: appending bit b maps y -> 2y+b).

Everything is an exact enumeration over all inputs x and all outputs y (float64
arithmetic, no sampling). Mutual information in bits:

    I(X^n; Y) = sum_m c_m * [ sum_x w(x) S2_m(x) - sum_y Sw_m[y] log2 Sw_m[y] ]

with c_m = d^(n-m)(1-d)^m,  S2_m(x) = sum_y N(x,y) log2 N(x,y)  (over length-m y),
Sw_m[y] = sum_x w(x) N(x,y),  w an input distribution. (The log2(c_m) terms of
H(Y) and H(Y|X) cancel; derivation in the attempt file.)

Input distributions supported:
  * i.i.d. Bernoulli(1/2)  (w(x) = 2^-n)
  * symmetric first-order Markov with flip probability gamma
    (w(x) = (1/2) gamma^t (1-gamma)^(n-1-t), t = # transitions in x)

Both are invariant under bitwise complement, and N(xbar, ybar) = N(x, y), so
the loop runs over the 2^(n-1) inputs with leading bit 0 and adds the
complement's contribution via the index map y -> (2^m - 1) - y  (= reversal of
the length-m count array).

A brute-force cross-check (explicit enumeration of all 2^n deletion subsets)
is run for small n.

Usage:  python3 exact_mi.py [nmax]        (default nmax = 14)
Writes results.json next to this file.
"""

import json
import sys
import time
from math import comb, log2
from pathlib import Path

import numpy as np


def xlog2x_table(maxval):
    """T[k] = k*log2(k) for integer k, T[0] = 0."""
    t = np.zeros(maxval + 1)
    k = np.arange(1, maxval + 1, dtype=float)
    t[1:] = k * np.log2(k)
    return t


def embedding_counts(xbits, n):
    """A[m][y] = N(x, y) for all y in {0,1}^m, m = 0..n (y as int, MSB first)."""
    A = [np.zeros(1 << m, dtype=np.int64) for m in range(n + 1)]
    A[0][0] = 1
    for i, b in enumerate(xbits):
        # descending m so A[m-1] is the pre-update value
        for m in range(min(i + 1, n), 0, -1):
            A[m][b::2] += A[m - 1]
    return A


def analyze(n, weight_fn, ds):
    """Exact I(X^n; Y) in bits for each d in ds, input distribution weight_fn.

    weight_fn(x) must satisfy weight_fn(x) == weight_fn(~x) (complement
    symmetry); the sum of weights over all 2^n inputs must be 1.
    """
    T = xlog2x_table(comb(n, n // 2) + 1)
    Sw = [np.zeros(1 << m) for m in range(n + 1)]        # sum_x w(x) N(x,y)
    wS2 = np.zeros(n + 1)                                # sum_x w(x) S2_m(x)
    half = 1 << (n - 1) if n > 1 else 1
    for x in range(half):
        xbits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
        A = embedding_counts(xbits, n)
        w = weight_fn(x)
        for m in range(n + 1):
            Am = A[m]
            wS2[m] += 2.0 * w * T[Am].sum()
            # complement input: counts are the reversed array (y -> mask - y)
            Sw[m] += w * (Am + Am[::-1])
    if n == 1:  # x=0 loop above covered x=0 and its complement x=1 already
        pass
    # sanity: sum_y Sw_m[y] must equal C(n, m)
    for m in range(n + 1):
        assert abs(Sw[m].sum() - comb(n, m)) < 1e-6 * comb(n, m) + 1e-12, (n, m)
    T2w = np.array([
        np.sum(np.where(s > 0, s * np.log2(np.where(s > 0, s, 1.0)), 0.0))
        for s in Sw
    ])
    out = {}
    for d in ds:
        c = np.array([d ** (n - m) * (1 - d) ** m for m in range(n + 1)])
        out[d] = float(np.dot(c, wS2 - T2w))
    return out


def uniform_weight(n):
    w = 2.0 ** (-n)
    return lambda x: w


def markov_weight(n, gamma):
    def w(x):
        t = bin((x ^ (x >> 1)) & ((1 << (n - 1)) - 1)).count("1")
        return 0.5 * gamma ** t * (1 - gamma) ** (n - 1 - t)
    return w


# ---------------------------------------------------------------- brute force

def brute_force_I(n, d, weight_fn):
    """Direct enumeration of all 2^n deletion subsets for every input."""
    py = {}
    hyx = 0.0
    for x in range(1 << n):
        xbits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
        dist = {}
        for mask in range(1 << n):  # bit i of mask set => position i survives
            y = tuple(xbits[i] for i in range(n) if (mask >> (n - 1 - i)) & 1)
            k = len(y)
            p = (1 - d) ** k * d ** (n - k)
            dist[y] = dist.get(y, 0.0) + p
        w = weight_fn(x)
        for y, p in dist.items():
            py[y] = py.get(y, 0.0) + w * p
            hyx -= w * p * log2(p)
    hy = -sum(p * log2(p) for p in py.values() if p > 0)
    return hy - hyx


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    ds = [0.1, 0.3, 0.5, 0.7, 0.9]
    results = {"ds": ds, "iid": {}, "markov_d0.5": {}, "timing_sec": {}}

    # cross-check exact DP vs brute force for small n
    for n in (2, 3, 5, 6):
        for d in (0.1, 0.5, 0.9):
            a = analyze(n, uniform_weight(n), [d])[d]
            b = brute_force_I(n, d, uniform_weight(n))
            assert abs(a - b) < 1e-10, (n, d, a, b)
        g = 0.3
        a = analyze(n, markov_weight(n, g), [0.5])[0.5]
        b = brute_force_I(n, 0.5, markov_weight(n, g))
        assert abs(a - b) < 1e-10, ("markov", n, a, b)
    print("brute-force cross-checks passed (n in {2,3,5,6})")

    # analytic check n=1: I = 1-d
    for d in ds:
        assert abs(analyze(1, uniform_weight(1), [d])[d] - (1 - d)) < 1e-12

    for n in range(1, nmax + 1):
        t0 = time.time()
        r = analyze(n, uniform_weight(n), ds)
        dt = time.time() - t0
        results["iid"][n] = r
        results["timing_sec"][n] = round(dt, 2)
        print(f"n={n:2d}  " + "  ".join(
            f"d={d}: I/n={r[d]/n:.6f}" for d in ds) + f"   ({dt:.1f}s)")

    # first-order Markov inputs at d = 0.5
    gammas = [0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5]
    for n in (8, 10, 12, min(nmax, 14)):
        row = {}
        for g in gammas:
            row[g] = analyze(n, markov_weight(n, g), [0.5])[0.5]
        results["markov_d0.5"][n] = row
        print(f"Markov d=0.5 n={n:2d}  " + "  ".join(
            f"g={g}: I/n={row[g]/n:.6f}" for g in gammas))

    out = Path(__file__).parent / "results.json"
    out.write_text(json.dumps(results, indent=1))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
