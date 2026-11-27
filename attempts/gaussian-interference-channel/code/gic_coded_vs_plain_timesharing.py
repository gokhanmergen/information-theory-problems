#!/usr/bin/env python3
"""Coded time-sharing of Gaussian Han-Kobayashi beats the Lean convex hull.

Channel: a = b = 1/2, P1 = P2 = 100 (real, unit noise).

PART 1 (achievable point, exact closed forms).  HK with a time-sharing variable
Q in {1,2}, P(Q=1)=P(Q=2)=1/2, full power P in both phases (no power control),
Gaussian superposition X_i = U_i + V_i with private powers
    phase 1: (P1p, P2p) = (0, 14),    phase 2: (P1p, P2p) = (14, 0).
Every HK mutual-information term is the average over Q of the per-phase
Gaussian value ("coded time-sharing", El Gamal-Kim Thm 6.4).  We exhibit an
explicit rate split (R1c, R1p, R2c, R2p) satisfying the eight receiver-side
decoding constraints (simultaneous non-unique decoding) at the symmetric rate
R = 1.9614 per user, i.e. sum rate 3.9228.

PART 2 (certificate).  Every point of the Lean set InGaussianHKRegion 0.5 0.5
100 100 (finite convex combinations of InGaussianHKBasic points with averaged
phase powers) has R1 + R2 <= L(P,P) where
    L(p1,p2) = C(200) + c (p1 + p2 - 200) + DELTA,  c = 1/(2 ln2 * 201),
provided  g(x) <= L(x) for every power vector x = (P1c,P1p,P2c,P2p) >= 0,
where g(x) = max{R1+R2 : the 7 Basic constraints at x}.  We verify
g <= L on {x >= 0, sum x <= SMAX} by interval branch-and-bound (each Basic
term is C(n/d) with n, d affine in disjoint coordinates with nonnegative
coefficients, so exact box bounds come from box corners), and beyond SMAX by
the analytic tail bound g <= C(p1)+C(p2) <= 2C(s/2) <= L.
With DELTA = 0.01: Lean sum rate <= C(200) + 0.01 = 3.8355 < 3.9228.
(Sanity: the same branch-and-bound FAILS for DELTA = -0.005, near the TDM
phase (p1,p2) ~ (200,0), as it must since g = L - DELTA there.)

Floating point: IEEE double; every box test demands a 1e-9 margin, far above
the accumulated rounding error of the closed-form bounds (values <= ~12 bits,
a handful of log2/divisions per term, relative error ~1e-15).

Relation to Motahari-Khandani (IEEE TIT 2009, Thm 7): their region "G" puts
psi3 = min{psi31,psi32,psi33} inside the time-sharing average (average of
mins).  The HK region with a time-sharing variable (El Gamal-Kim Thm 6.4)
averages the three sum bounds separately (min of averages).  The point of
PART 1 lies in the latter but not in the convex hull, so "time-sharing =
convexification" fails for the true coded-time-sharing Gaussian HK region.

Reproduce:  python3 gic_coded_vs_plain_timesharing.py     (numpy+scipy, minutes)
"""
import math
import sys
import time

import numpy as np
from scipy.optimize import linprog

LN2 = math.log(2.0)
A = 0.5
P = 100.0
S2 = A * A  # a^2 = b^2


def C(x):
    return 0.5 * np.log2(1.0 + x)


# ------------------------------------------------------------- PART 1
def phase_terms(P1p, P2p, P1=P, P2=P, s=S2):
    """Per-phase Gaussian HK quantities for receiver 1 and receiver 2."""
    P1c, P2c = P1 - P1p, P2 - P2p
    N1, N2 = 1 + s * P2p, 1 + s * P1p
    rx1 = dict(a=C(P1p / N1), b=C(P1 / N1), c=C((P1p + s * P2c) / N1), d=C((P1 + s * P2c) / N1))
    rx2 = dict(a=C(P2p / N2), b=C(P2 / N2), c=C((P2p + s * P1c) / N2), d=C((P2 + s * P1c) / N2))
    compact = np.array([
        C(P1 / N1), C(P2 / N2),
        C((P1 + s * P2c) / N1) + C(P2p / N2),
        C(P1p / N1) + C((P2 + s * P1c) / N2),
        C((P1p + s * P2c) / N1) + C((P2p + s * P1c) / N2),
        C((P1 + s * P2c) / N1) + C(P1p / N1) + C((P2p + s * P1c) / N2),
        C((P2 + s * P1c) / N2) + C(P2p / N2) + C((P1p + s * P2c) / N1)])
    return rx1, rx2, compact


def part1():
    r1a, r2a, Ta = phase_terms(0.0, 14.0)
    r1b, r2b, Tb = phase_terms(14.0, 0.0)
    avg = lambda u, v: {k: 0.5 * (u[k] + v[k]) for k in u}
    rx1, rx2 = avg(r1a, r1b), avg(r2a, r2b)
    Tbar = 0.5 * (Ta + Tb)
    # compact-form max sum rate (dual forms of the 2-variable LP)
    A1, A2, s1, s2, s3, D1, D2 = Tbar
    coded_sum = min(A1 + A2, s1, s2, s3, (A1 + D2) / 2, (D1 + A2) / 2, (D1 + D2) / 3)
    plain_a = min(Ta[0] + Ta[1], *Ta[2:5], (Ta[0] + Ta[6]) / 2, (Ta[5] + Ta[1]) / 2, (Ta[5] + Ta[6]) / 3)
    print("PART 1: coded time-sharing of swapped Gaussian HK splits, a=b=0.5, P=100")
    print(f"  averaged compact HK terms: {np.round(Tbar, 6)}")
    print(f"  coded-TS max sum rate (compact form) = {coded_sum:.9f}")
    print(f"  plain TS of the same two phases       = {plain_a:.9f}")
    # explicit rate split: variables (R1c, R1p, R2c, R2p); maximise symmetric R
    # receiver 1: R1p<=a1, R1c+R1p<=b1, R1p+R2c<=c1, R1c+R1p+R2c<=d1 ; receiver 2 symmetric
    Aub = [[0, 1, 0, 0], [1, 1, 0, 0], [0, 1, 1, 0], [1, 1, 1, 0],
           [0, 0, 0, 1], [0, 0, 1, 1], [1, 0, 0, 1], [1, 0, 1, 1]]
    bub = [rx1["a"], rx1["b"], rx1["c"], rx1["d"], rx2["a"], rx2["b"], rx2["c"], rx2["d"]]
    # maximise R1c+R1p subject to R1c+R1p = R2c+R2p
    res = linprog([-1, -1, 0, 0], A_ub=Aub, b_ub=bub, A_eq=[[1, 1, -1, -1]], b_eq=[0],
                  bounds=[(0, None)] * 4, method="highs")
    split = res.x
    R = split[0] + split[1]
    print(f"  best symmetric rate via explicit split: R = {R:.9f} per user, sum = {2 * R:.9f}")
    print(f"  split (R1c,R1p,R2c,R2p) = {np.round(split, 6)}")
    slack = np.array(bub) - np.array(Aub) @ split
    print(f"  min slack of the 8 decoding constraints = {slack.min():.2e} (>= 0 means feasible)")
    assert slack.min() >= -1e-9
    assert abs(2 * R - coded_sum) < 1e-6
    return 2 * R


# ------------------------------------------------------------- PART 2
DELTA = 0.01
CSL = 1.0 / (2 * LN2 * (1 + 2 * P))     # slope of C at 2P
C2P = float(C(2 * P))


def L_of(psum):
    return C2P + CSL * (psum - 2 * P) + DELTA


def tail_smax():
    """Smallest SMAX (on a grid, >= 4P) s.t. 2C(s/2) <= L(s) at s=SMAX; then it
    holds for all s >= SMAX because d/ds[2C(s/2)] < CSL for s > 4P."""
    s = 4 * P
    while 2 * C(s / 2) > L_of(s):
        s += 1.0
    return s


def box_upper_sum(lo, hi):
    """Upper bound of g over boxes. lo, hi: arrays (n,4) of (u1,v1,u2,v2)."""
    u1l, v1l, u2l, v2l = lo.T
    u1h, v1h, u2h, v2h = hi.T
    s = S2
    # each term C(n/d) bounded above by C(n(hi)/d(lo))
    A1 = C((u1h + v1h) / (1 + s * v2l))
    A2 = C((u2h + v2h) / (1 + s * v1l))
    t1 = C((u1h + v1h + s * u2h) / (1 + s * v2l))      # I(X1,U2;Y1)
    t2 = C(v2h / (1 + s * v1l))                       # I(X2;Y2|U1,U2)
    t3 = C(v1h / (1 + s * v2l))                       # I(X1;Y1|U1,U2)
    t4 = C((u2h + v2h + s * u1h) / (1 + s * v1l))      # I(X2,U1;Y2)
    t5 = C((v1h + s * u2h) / (1 + s * v2l))            # I(X1,U2;Y1|U1)
    t6 = C((v2h + s * u1h) / (1 + s * v1l))            # I(X2,U1;Y2|U2)
    S1 = t1 + t2
    S2_ = t3 + t4
    S3 = t5 + t6
    D1 = t1 + t3 + t6
    D2 = t4 + t2 + t5
    return np.minimum.reduce([A1 + A2, S1, S2_, S3, (A1 + D2) / 2, (D1 + A2) / 2, (D1 + D2) / 3])


def certify(smax, max_boxes=60_000_000, batch=400_000):
    lo = np.zeros((1, 4))
    hi = np.full((1, 4), smax)
    queue = [(lo, hi)]
    processed = 0
    t0 = time.time()
    while queue:
        lo, hi = queue.pop()
        # discard boxes entirely outside the simplex {sum <= smax} (tail bound covers them)
        keep = lo.sum(axis=1) <= smax
        lo, hi = lo[keep], hi[keep]
        if len(lo) == 0:
            continue
        ub = box_upper_sum(lo, hi)
        Llow = L_of(lo.sum(axis=1))
        bad = ub > Llow - 1e-9
        processed += len(lo)
        if processed > max_boxes:
            raise RuntimeError("box budget exceeded")
        lo, hi = lo[bad], hi[bad]
        if len(lo) == 0:
            continue
        w = hi - lo
        if w.max() < 1e-6:
            raise RuntimeError(f"cannot certify near {lo[0]}")
        # bisect each bad box along its widest coordinate
        k = np.argmax(w, axis=1)
        mid = lo[np.arange(len(lo)), k] + 0.5 * w[np.arange(len(lo)), k]
        hi1 = hi.copy(); hi1[np.arange(len(lo)), k] = mid
        lo2 = lo.copy(); lo2[np.arange(len(lo)), k] = mid
        nlo = np.vstack([lo, lo2]); nhi = np.vstack([hi1, hi])
        for i in range(0, len(nlo), batch):
            queue.append((nlo[i:i + batch], nhi[i:i + batch]))
    return processed, time.time() - t0


def part2(coded_sum):
    smax = tail_smax()
    print(f"\nPART 2: certificate that the Lean region's sum rate is <= C(200)+DELTA")
    print(f"  C(200) = {C2P:.9f}, slope c = {CSL:.9e}, DELTA = {DELTA}, SMAX = {smax:g}")
    n, dt = certify(smax)
    bound = C2P + DELTA
    print(f"  branch-and-bound: {n} boxes checked in {dt:.1f}s: g(x) <= L(x) on sum(x) <= SMAX")
    print(f"  => every point of InGaussianHKRegion 0.5 0.5 100 100 has R1+R2 <= {bound:.6f}")
    print(f"  coded-TS achievable sum rate {coded_sum:.6f} exceeds it by {coded_sum - bound:.6f} bits")
    assert coded_sum > bound


if __name__ == "__main__":
    s = part1()
    if "--skip-certificate" not in sys.argv:
        part2(s)


# ------------------------------------------------------------- PART 3 (optional, heuristic)
def part3_scan():
    """Heuristic scan (python3 gic_coded_vs_plain_timesharing.py --scan):
    best coded time-sharing of two swapped splits (alpha,beta)/(beta,alpha)
    at full power vs the numerically computed Lean envelope (plain TS + power
    control, grid search; a lower estimate of the Lean sum rate)."""
    import gic_lean_region_sumrate as LR

    def compact(a, p, f1, f2):
        s = a * a
        P1p, P2p = f1 * p, f2 * p
        P1c, P2c = p - P1p, p - P2p
        N1, N2 = 1 + s * P2p, 1 + s * P1p
        return np.stack([
            C(p / N1), C(p / N2),
            C((p + s * P2c) / N1) + C(P2p / N2),
            C(P1p / N1) + C((p + s * P1c) / N2),
            C((P1p + s * P2c) / N1) + C((P2p + s * P1c) / N2),
            C((p + s * P2c) / N1) + C(P1p / N1) + C((P2p + s * P1c) / N2),
            C((p + s * P1c) / N2) + C(P2p / N2) + C((P1p + s * P2c) / N1)])

    def summax(T):
        A1, A2, s1, s2, s3, D1, D2 = T
        return np.minimum.reduce([A1 + A2, s1, s2, s3, (A1 + D2) / 2, (D1 + A2) / 2, (D1 + D2) / 3])

    print("\nPART 3 (heuristic): | P | a | coded swap TS (alpha,beta) | Lean envelope (grid) | excess |")
    f = np.linspace(0, 1, 401)
    F1, F2 = np.meshgrid(f, f, indexing="ij")
    for p in (30.0, 100.0, 1000.0):
        for a in (0.4, 0.5, 0.6, math.sqrt(0.5), 0.8):
            coded = summax(0.5 * (compact(a, p, F1, F2) + compact(a, p, F2, F1)))
            i, j = np.unravel_index(np.argmax(coded), coded.shape)
            env = LR.lean_sum_rate(a, a, p, p)[0]
            print(f"  | {p:g} | {a:.4f} | {coded[i, j]:.4f} ({f[i]:.3f},{f[j]:.3f}) | {env:.4f} "
                  f"| {coded[i, j] - env:+.4f} |", flush=True)


if __name__ == "__main__" and "--scan" in sys.argv:
    part3_scan()
