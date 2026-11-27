"""Reviewer's rigorous (IEEE basic ops only, no libm) branch-and-bound.

Claim to certify, a^2 = b^2 = 1/4, P1 = P2 = 100:
  for every x = (u1, v1, u2, v2) in R_+^4:
     g(x) <= L(x) := C(200) + c (sum x - 200) + DELTA,   c = 1/(2 ln2 * 201),
  where g(x) = max{R1+R2 : InGaussianHKBasic constraints at split x}.

Weak duality: g(x) <= f_k(x) for the seven forms
  A1+A2, S1, S2, S3, (A1+D2)/2, (D1+A2)/2, (D1+D2)/3.
Each form is (1/m) * sum_j C(r_j) with C(r) = 0.5 log2(1+r), so
  f_k <= L   <=>   prod_j (1 + r_j)  <=  E(s)^m,   E(s) := 2^{2L} = 201 * exp((s-200)/201) * 4^DELTA
(using 2 c ln 2 = 1/201).  On a box, each r_j = n_j/d_j with n_j, d_j affine with
nonnegative coefficients in disjoint coordinates, so r_j <= n_j(hi)/d_j(lo).  E is
increasing in s, so E(s) >= E(s_lo).

Rounding: products / sums / quotients on the LHS rounded up (nextafter after each
IEEE op, which is correctly rounded), RHS rounded down.  exp(t) is bounded below by
(1 + t/2^K)^(2^K) (valid because log(1+y) <= y, and 1 + t/2^K > 0 for t >= -1),
computed by K downward-rounded squarings.  201 * 4^DELTA is a scalar lower bound
computed once by mpmath interval arithmetic.  No libm call enters the box test.

Tail (sum x >= SMAX) is checked separately with mpmath interval arithmetic.
"""
import sys
import time
import numpy as np
from mpmath import iv, mp, mpf

DELTA = float(sys.argv[1]) if len(sys.argv) > 1 else 0.05
SMAX_EXTRA = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
K = 24
INF = np.inf
up = lambda x: np.nextafter(x, INF)
dn = lambda x: np.nextafter(x, -INF)
s2 = 0.25  # exact

iv.dps = 50
mp.dps = 50
# scalar constant 201 * 4^DELTA, rounded down
K0 = iv.mpf(201) * iv.power(4, iv.mpf(DELTA))
K0_lo = float(mpf(K0.a))
K0_lo = np.nextafter(K0_lo, -INF)
K0_lo = np.nextafter(K0_lo, -INF)


def exp_lo(t):
    """Rigorous lower bound of exp(t) for t >= -1 (array)."""
    y = dn(1.0 + dn(t / 2.0 ** K))  # t/2^K is exact unless underflow; dn anyway
    assert (y > 0).all()
    for _ in range(K):
        y = dn(y * y)
    return y


def E_lo(slo):
    t = dn(dn(slo - 200.0) / 201.0)
    return dn(K0_lo * exp_lo(t))


def fac(num_hi, den_lo):
    """upper bound of 1 + num/den"""
    return up(1.0 + up(num_hi / den_lo))


def box_ok(lo, hi):
    u1l, v1l, u2l, v2l = lo.T
    u1h, v1h, u2h, v2h = hi.T
    N1 = dn(1.0 + s2 * v2l)
    N2 = dn(1.0 + s2 * v1l)
    p1h = up(u1h + v1h)
    p2h = up(u2h + v2h)
    A1 = fac(p1h, N1)
    A2 = fac(p2h, N2)
    all1 = fac(up(p1h + s2 * u2h), N1)
    all2 = fac(up(p2h + s2 * u1h), N2)
    priv1 = fac(v1h, N1)
    priv2 = fac(v2h, N2)
    pc1 = fac(up(v1h + s2 * u2h), N1)
    pc2 = fac(up(v2h + s2 * u1h), N2)
    m = lambda *a: _prod(a)
    E = E_lo(dn(dn(u1l + v1l) + dn(u2l + v2l)))
    E2 = dn(E * E)
    E3 = dn(E2 * E)
    ok = (m(A1, A2) <= E)
    ok |= (m(all1, priv2) <= E)                      # S1
    ok |= (m(all2, priv1) <= E)                      # S2
    ok |= (m(pc1, pc2) <= E)                         # S3
    ok |= (m(A1, all2, priv2, pc1) <= E2)            # (A1 + D2)/2
    ok |= (m(all1, priv1, pc2, A2) <= E2)            # (D1 + A2)/2
    ok |= (m(all1, priv1, pc2, all2, priv2, pc1) <= E3)  # (D1 + D2)/3
    return ok


def _prod(arrs):
    r = arrs[0]
    for x in arrs[1:]:
        r = up(r * x)
    return r


def tail_smax():
    # smallest integer s >= 401 with 2C(s/2) < L(s) rigorously (interval arithmetic).
    s = 401
    c = 1 / (2 * iv.log(2) * 201)
    while True:
        lhs = iv.log(1 + iv.mpf(s) / 2) / iv.log(2)
        rhs = iv.log(201) / (2 * iv.log(2)) + c * (s - 200) + iv.mpf(DELTA)
        if lhs.b < rhs.a:
            s = s + SMAX_EXTRA
            lhs = iv.log(1 + iv.mpf(s) / 2) / iv.log(2)
            rhs = iv.log(201) / (2 * iv.log(2)) + c * (s - 200) + iv.mpf(DELTA)
            assert lhs.b < rhs.a
            return float(s), mpf(rhs.a) - mpf(lhs.b)
        s += 1


def run():
    smax, margin = tail_smax()
    print(f"DELTA={DELTA} K={K} SMAX={smax} rigorous tail margin >= {mp.nstr(margin, 6)}")
    stack = [(np.zeros((1, 4)), np.full((1, 4), smax))]
    n = 0
    t0 = time.time()
    while stack:
        lo, hi = stack.pop()
        keep = dn(dn(lo[:, 0] + lo[:, 1]) + dn(lo[:, 2] + lo[:, 3])) <= smax
        # boxes with lower-corner sum > smax lie in the tail region: rigorous since
        # we compare a downward-rounded sum (if dn(sum) > smax then sum > smax).
        lo, hi = lo[keep], hi[keep]
        if not len(lo):
            continue
        ok = box_ok(lo, hi)
        n += len(lo)
        lo, hi = lo[~ok], hi[~ok]
        if not len(lo):
            continue
        w = hi - lo
        if w.max() < 1e-7:
            raise SystemExit(f"FAIL near {lo[0]}, {hi[0]}")
        k = np.argmax(w, axis=1)
        idx = np.arange(len(lo))
        mid = lo[idx, k] + 0.5 * w[idx, k]   # dyadic midpoint; exact for these grids
        hi1 = hi.copy(); hi1[idx, k] = mid
        lo2 = lo.copy(); lo2[idx, k] = mid
        nlo = np.vstack([lo, lo2]); nhi = np.vstack([hi1, hi])
        for i in range(0, len(nlo), 500_000):
            stack.append((nlo[i:i + 500_000], nhi[i:i + 500_000]))
    print(f"CERTIFIED g <= L on {{x>=0, sum x <= {smax}}}: {n} boxes, {time.time() - t0:.1f}s")
    C200 = iv.log(201) / (2 * iv.log(2))
    bound = C200 + iv.mpf(DELTA)
    print(f"=> Lean-region sum rate <= C(200) + DELTA <= {mp.nstr(mpf(bound.b), 12)}")


if __name__ == "__main__":
    run()
