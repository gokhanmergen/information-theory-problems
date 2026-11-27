# Reviewer probe (2026-11-27, Claim 7 code audit): mpmath.iv behaviours that the author's
# ../certify_hk1_bound.py relies on (.a/.b, undecidable comparisons, exactness of 1 - x).
# Run: python3 iv_semantics.py
# Runtime: about 1 s. Needs mpmath.
"""Probe mpmath.iv semantics that certify_hk1_bound.py relies on."""
import mpmath as mp
from mpmath import iv

iv.dps = 30
mp.mp.dps = 30
x = iv.mpf(1) / 3
print("type(x.a):", type(x.a), "x.a == x.b?", x.a == x.b, " x.a < x.b?", x.a < x.b)
print("x =", x, " x.a =", x.a, " x.b =", x.b)
# iv.mpf([A.a, B.b]) built from degenerate intervals
y = iv.mpf([x.a, x.b])
print("iv.mpf([x.a, x.b]) =", y, " contains 1/3 exactly (rational check):",
      mp.mpf(y.a) <= mp.mpf(1) / 3 <= mp.mpf(y.b))
# comparisons of degenerate intervals with mpf
t = mp.mpf("1.10803")
print("x.b < t:", x.b < t, type(x.b < t))
z = iv.mpf([1, 2])
print("[1,2] < 3:", z < 3, " [1,2] < 1.5:", z < 1.5, " [1,2] >= 1.5:", z >= 1.5)
# 1 - mpf with many bits: exact?
u = mp.mpf(1) / 3      # 30-digit mpf ~ 103 bits
w = 1 - u
print("1 - u exact? ", (w + u) == 1, " prec bits", mp.mp.prec)
# 1 - ivmpf (degenerate) -> interval?
v = 1 - x.a
print("1 - x.a =", v, " width:", v.delta)
# log of interval and product signs
P = iv.mpf([mp.mpf("0.25"), mp.mpf("0.5")])
print("log2(1-P) =", iv.log(1 - P) / iv.log(2))
print("(P-1)*log2(1-P) =", (P - 1) * iv.log(1 - P) / iv.log(2))
# max/min mixing mpf and ivmpf
print("max(mpf(0), x.a) ->", max(mp.mpf(0), x.a), type(max(mp.mpf(0), x.a)))
print("min(mpf(1), x.b) ->", min(mp.mpf(1), x.b), type(min(mp.mpf(1), x.b)))
# heapq tuple comparison with degenerate intervals equal
import heapq
h = []
heapq.heappush(h, (-(x.b), mp.mpf(0), mp.mpf(1)))
heapq.heappush(h, (-(x.b), mp.mpf(0.5), mp.mpf(1)))
print("heap ok:", heapq.heappop(h))
