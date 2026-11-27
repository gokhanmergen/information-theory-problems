# Reviewer check (2026-11-27, Claim 5): rigorous rational-box B&B upper bound on sym(G_1(BMC)).
# Run: python3 g1_bnb.py TARGET   (the note quotes TARGET = 0.61700 and 0.61696; output in g1_bnb.out)
# Runtime: about 12 s at 0.61696. Needs mpmath.
"""Independent rigorous upper bound on sym(G1(BMC)) = max_{x,y in [0,1]} [y h(x) + x h(y)]/2.

Adaptive branch and bound on boxes with exact rational corners.  On a box B=[x0,x1]x[y0,y1]:
    y h(x) + x h(y) <= y1 * Hx + x1 * Hy,   Hx = max_{[x0,x1]} h,
(h >= 0, x,y >= 0).  h is concave with peak at 1/2, so Hx = h(endpoint nearest 1/2) or 1 if
1/2 in [x0,x1]; h evaluated in mpmath interval arithmetic (upper endpoint used).
A box is discarded if its bound <= 2*TARGET; otherwise split into 4.  Every discarded box is
rigorously below the target, and the boxes partition [0,1]^2, so the max is <= TARGET.
"""
import sys, heapq
from fractions import Fraction as F
from mpmath import iv, mpf

iv.dps = 40
LN2 = iv.log(iv.mpf(2))
cache = {}


def h_up(x):
    if x in cache:
        return cache[x]
    if x == 0 or x == 1:
        v = mpf(0)
    else:
        X = iv.mpf(x.numerator) / x.denominator
        v = (-(X * iv.log(X) + (1 - X) * iv.log(1 - X)) / LN2).b
    cache[x] = v
    return v


def hmax(a, b):
    if a <= F(1, 2) <= b:
        return mpf(1)
    return max(h_up(a), h_up(b))


def bound(x0, x1, y0, y1):
    X1 = iv.mpf(x1.numerator) / x1.denominator
    Y1 = iv.mpf(y1.numerator) / y1.denominator
    return (Y1 * hmax(x0, x1) + X1 * hmax(y0, y1)).b


def main(target_str):
    target2 = 2 * iv.mpf(target_str)
    t2 = target2.a  # lower end of 2*target: discarding requires bound <= this
    stack = [(F(0), F(1), F(0), F(1))]
    n_boxes = 0
    min_w = F(1)
    while stack:
        x0, x1, y0, y1 = stack.pop()
        n_boxes += 1
        if bound(x0, x1, y0, y1) <= t2:
            continue
        if x1 - x0 < F(1, 2 ** 30):
            print("FAILED: cannot certify near", float(x0), float(y0))
            return
        xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
        min_w = min(min_w, xm - x0)
        stack += [(x0, xm, y0, ym), (xm, x1, y0, ym), (x0, xm, ym, y1), (xm, x1, ym, y1)]
    print(f"certified: sym(G1) <= {target_str}; boxes visited {n_boxes}, min width {min_w}")


if __name__ == "__main__":
    main(sys.argv[1])
