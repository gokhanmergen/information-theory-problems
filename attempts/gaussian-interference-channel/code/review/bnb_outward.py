# Reviewer's first B&B (2026-11-27): sum-form test g <= L with ulp-pushed floats; it assumes libm
# log2 is accurate to < 4 ulp, so it is superseded by ../reviewer_bnb_rigorous.py (product form, no libm).
# Run: python3 bnb_outward.py [DELTA [leaves.npz]]   (default DELTA = 0.05; the leaf dump is optional
# and hundreds of MB, so none is committed.) Runtime: about 3 s at DELTA = 0.05. Needs numpy, mpmath.
"""Reviewer's independent branch-and-bound with outward rounding.

Goal: for x = (u1, v1, u2, v2) >= 0 (common/private powers of user 1, user 2),
  g(x) := max{R1+R2 : InGaussianHKBasic constraints with these powers}
       <= min of 7 weak-duality forms  (A1+A2, S1, S2, S3, (A1+D2)/2, (D1+A2)/2, (D1+D2)/3)
show  g(x) <= L(x) := C(200) + c*(sum(x) - 200) + DELTA,  c = C'(200) = 1/(2 ln2 * 201).

Rounding: every basic float op on the "upper" side is pushed up by one ulp with
nextafter (IEEE +,*,/ are correctly rounded, so one ulp suffices); log2 results are
pushed up by 4 ulps (macOS libm log2 is faithfully rounded, < 1 ulp).  The lower
side L is computed with C(200), c from mpmath and pushed down.  So a box passing the
test satisfies the inequality in exact arithmetic, modulo the libm log2 accuracy
assumption (< 4 ulp).

The leaves are dumped so they can be re-verified with mpmath interval arithmetic.
"""
import sys
import time
import numpy as np
from mpmath import mp, mpf, log

mp.dps = 40
DELTA = float(sys.argv[1]) if len(sys.argv) > 1 else 0.05
DUMP = sys.argv[2] if len(sys.argv) > 2 else None
s2 = 0.25

INF = np.inf
up = lambda x: np.nextafter(x, INF)
dn = lambda x: np.nextafter(x, -INF)

C200 = log(201) / (2 * log(2))
cc = 1 / (2 * log(2) * 201)
C200_lo = float(C200) ; C200_lo = np.nextafter(C200_lo, -INF)
c_lo = np.nextafter(float(cc), -INF)
c_hi = np.nextafter(float(cc), INF)


def Cup(num_hi, den_lo):
    r = up(num_hi / den_lo)
    y = np.log2(up(1.0 + r))
    for _ in range(4):
        y = up(y)
    return up(0.5 * y)  # 0.5*y exact anyway


def box_ub(lo, hi):
    u1l, v1l, u2l, v2l = lo.T
    u1h, v1h, u2h, v2h = hi.T
    N1 = dn(1.0 + s2 * v2l)
    N2 = dn(1.0 + s2 * v1l)
    p1h = up(u1h + v1h)
    p2h = up(u2h + v2h)
    A1 = Cup(p1h, N1)                         # I(X1;Y1|U2)
    A2 = Cup(p2h, N2)
    all1 = Cup(up(p1h + s2 * u2h), N1)        # I(X1,U2;Y1)   (num: P1 + a2*(P2c) over N1 after
    #  noting Var(Y1)/Var(Y1|X1,U2) = 1 + (P1 + a2 P2c)/N1)
    all2 = Cup(up(p2h + s2 * u1h), N2)
    priv1 = Cup(v1h, N1)                      # I(X1;Y1|U1,U2)
    priv2 = Cup(v2h, N2)
    pc1 = Cup(up(v1h + s2 * u2h), N1)         # I(X1,U2;Y1|U1)
    pc2 = Cup(up(v2h + s2 * u1h), N2)
    S1 = up(all1 + priv2)
    S2 = up(all2 + priv1)
    S3 = up(pc1 + pc2)
    D1 = up(up(all1 + priv1) + pc2)
    D2 = up(up(all2 + priv2) + pc1)
    f = [up(A1 + A2), S1, S2, S3, up(up(A1 + D2) / 2), up(up(D1 + A2) / 2), up(up(D1 + D2) / 3)]
    return np.minimum.reduce(f)


def L_lo(slo):
    t = slo - 200.0  # slo multiple-of-dyadic; t may be inexact -> push down
    t = dn(t)
    term = np.where(t >= 0, dn(c_lo * t), dn(c_hi * t))
    return dn(dn(C200_lo + term) + DELTA)


def tail_smax():
    # smallest integer s >= 400 with 2C(s/2) <= L(s) - 1e-12 (mpmath); then for all s'>=s
    # since d/ds 2C(s/2) = 1/(ln2 (2+s)) < c for s > 400.
    s = 400
    while True:
        lhs = log(1 + mpf(s) / 2) / log(2)
        rhs = C200 + cc * (s - 200) + mpf(DELTA)
        if lhs <= rhs - mpf(10) ** -12:
            return s, rhs - lhs
        s += 1


def run():
    smax, margin = tail_smax()
    print(f"DELTA={DELTA}  SMAX={smax}  tail margin at SMAX = {mp.nstr(margin, 6)}")
    stack = [(np.zeros((1, 4)), np.full((1, 4), float(smax)))]
    nproc = 0
    leaves_lo, leaves_hi = [], []
    worst = -np.inf
    t0 = time.time()
    while stack:
        lo, hi = stack.pop()
        keep = dn(lo.sum(axis=1)) <= smax  # boxes with lo-sum > smax: tail region
        lo, hi = lo[keep], hi[keep]
        if not len(lo):
            continue
        ub = box_ub(lo, hi)
        Ll = L_lo(dn(lo.sum(axis=1)))
        ok = ub <= Ll
        nproc += len(lo)
        if DUMP is not None and ok.any():
            leaves_lo.append(lo[ok]); leaves_hi.append(hi[ok])
        lo, hi = lo[~ok], hi[~ok]
        if not len(lo):
            continue
        w = hi - lo
        if w.max() < 1e-7:
            raise SystemExit(f"FAIL: cannot certify near {lo[np.argmax(w.max(axis=1)*0)]} ub={ub[~ok][:3]}")
        k = np.argmax(w, axis=1)
        idx = np.arange(len(lo))
        mid = lo[idx, k] + 0.5 * w[idx, k]
        hi1 = hi.copy(); hi1[idx, k] = mid
        lo2 = lo.copy(); lo2[idx, k] = mid
        nlo = np.vstack([lo, lo2]); nhi = np.vstack([hi1, hi])
        for i in range(0, len(nlo), 500_000):
            stack.append((nlo[i:i + 500_000], nhi[i:i + 500_000]))
        if nproc > 400_000_000:
            raise SystemExit("budget")
    print(f"certified: {nproc} boxes, {time.time() - t0:.1f}s; bound C(200)+DELTA = {mp.nstr(C200 + DELTA, 10)}")
    if DUMP is not None:
        np.savez(DUMP, lo=np.vstack(leaves_lo), hi=np.vstack(leaves_hi), smax=smax, delta=DELTA)
        print("leaves:", sum(len(x) for x in leaves_lo))


if __name__ == "__main__":
    run()
