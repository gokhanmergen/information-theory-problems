#!/usr/bin/env python3
"""I(maj(X); Y) for odd n via the symmetric-function reduction.

For symmetric f, P(f(X)=1, Y=y) depends on y only through wt(y), so
  P(f=1, wt(Y)=u) = 2^-n * C(n,u) * sum_{w: f_w=1} sum_k C(u,k) C(n-u,w-k)
                    * a^(u+w-2k) * (1-a)^(n-u-w+2k),
where k is the overlap of 1-positions. O(n^3) total. Stdlib only.
"""
import math
from math import comb


def mi_symmetric(weight_set, n, a):
    pf1u = []  # P(f=1, wt(Y)=u)
    pu = [comb(n, u) * 0.0 for u in range(n + 1)]
    for u in range(n + 1):
        s = 0.0
        for w in range(n + 1):
            if w not in weight_set:
                continue
            for k in range(max(0, u + w - n), min(u, w) + 1):
                s += (comb(u, k) * comb(n - u, w - k)
                      * a ** (u + w - 2 * k) * (1 - a) ** (n - u - w + 2 * k))
        pf1u.append(2.0 ** -n * comb(n, u) * s)
        # P(wt(Y)=u): Y is uniform too (uniform input through BSC)
        pu[u] = comb(n, u) * 2.0 ** -n
    pf1 = sum(pf1u)
    mi = 0.0
    for u in range(n + 1):
        q, r = pf1u[u], pu[u] - pf1u[u]
        if q > 0:
            mi += q * math.log2(q / (pf1 * pu[u]))
        if r > 0:
            mi += r * math.log2(r / ((1 - pf1) * pu[u]))
    return mi


if __name__ == "__main__":
    selected = {3, 5, 9, 15, 25, 41, 61}
    for a in (0.05, 0.10, 0.20, 0.30, 0.40):
        bound = 1 - (-a * math.log2(a) - (1 - a) * math.log2(1 - a))
        values = []
        for n in range(3, 62, 2):
            value = mi_symmetric(set(range(n // 2 + 1, n + 1)), n, a)
            values.append((n, value))
        decreases = [left - right for (_, left), (_, right)
                     in zip(values, values[1:])]
        row = [f"n={n}:{value:.6f}" for n, value in values if n in selected]
        print(f"alpha={a:.2f} bound={bound:.6f} "
              f"all_adjacent_decrease={all(gap > 0 for gap in decreases)} "
              f"min_decrease={min(decreases):.9f}  " + "  ".join(row))
