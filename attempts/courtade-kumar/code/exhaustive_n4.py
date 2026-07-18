#!/usr/bin/env python3
"""Exhaustive check of the Courtade-Kumar conjecture at n=4.

For each alpha in a grid, computes I(f(X);Y) exactly for ALL 2^16 Boolean
functions f: {0,1}^4 -> {0,1} (X uniform, Y = BSC(alpha) output), using a
Gray-code sweep so each function costs O(2^n) instead of O(4^n).

Reports: max MI, whether the maximizer set is exactly the dictators and
anti-dictators, the runner-up value, and the gap. Stdlib only.
"""
import math
from collections import defaultdict

N = 4
SIZE = 1 << N          # 16 inputs
NF = 1 << SIZE         # 65536 functions


def hamming(a, b):
    return bin(a ^ b).count("1")


def run(alpha):
    # channel matrix W[x][y] = P(y|x), and marginal py (uniform input)
    W = [[alpha ** hamming(x, y) * (1 - alpha) ** (N - hamming(x, y))
          for y in range(SIZE)] for x in range(SIZE)]
    px = 1.0 / SIZE
    py = [sum(W[x][y] for x in range(SIZE)) * px for y in range(SIZE)]

    p1 = [0.0] * SIZE          # p1[y] = P(f(X)=1, Y=y), starts at f == 0
    mask = 0
    counts = defaultdict(int)    # rounded MI -> exact number of functions
    results = defaultdict(list)  # rounded MI -> example masks (capped)

    for i in range(NF):
        if i:
            b = (i & -i).bit_length() - 1   # bit flipped between gray(i-1), gray(i)
            sign = -1.0 if (mask >> b) & 1 else 1.0
            mask ^= 1 << b
            row = W[b]
            for y in range(SIZE):
                p1[y] += sign * px * row[y]
        pf1 = sum(p1)
        if pf1 <= 0.0 or pf1 >= 1.0:        # constant function, MI = 0
            mi = 0.0
        else:
            mi = 0.0
            for y in range(SIZE):
                q, r = p1[y], py[y] - p1[y]
                if q > 0:
                    mi += q * math.log2(q / (pf1 * py[y]))
                if r > 0:
                    mi += r * math.log2(r / ((1 - pf1) * py[y]))
        key = round(mi, 9)
        counts[key] += 1
        bucket = results[key]
        if len(bucket) < 256:
            bucket.append(mask)

    vals = sorted(results, reverse=True)
    best, second = vals[0], vals[1]
    dictators = {sum(1 << x for x in range(SIZE) if (x >> i) & 1) for i in range(N)}
    dictators |= {m ^ (NF - 1) for m in dictators}   # anti-dictators
    # single-flip perturbations of (anti-)dictators: flip f on exactly one input
    single_flip = {m ^ (1 << x) for m in dictators for x in range(SIZE)}
    top_masks = set(results[best])
    return {
        "alpha": alpha,
        "bound": 1 - (-alpha * math.log2(alpha) - (1 - alpha) * math.log2(1 - alpha)),
        "max": best,
        "max_is_dictators_only": top_masks == dictators and counts[best] == 8,
        "second": second,
        "n_second": counts[second],
        "second_is_single_flip": set(results[second]) == single_flip
                                 and counts[second] == len(single_flip),
    }


if __name__ == "__main__":
    for alpha in (0.01, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45):
        r = run(alpha)
        print(f"alpha={r['alpha']:.2f}  bound={r['bound']:.9f}  max={r['max']:.9f}  "
              f"dictators_only={r['max_is_dictators_only']}  "
              f"second={r['second']:.9f} (x{r['n_second']}, "
              f"single_flip_class={r['second_is_single_flip']})  "
              f"gap={r['max'] - r['second']:.6f}")
