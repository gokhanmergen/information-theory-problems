#!/usr/bin/env python3
"""Weak-interference (p1 > p2) baseline for the binary symmetric Z-interference
channel (BS-ZIC):

    Y1 = X1 xor X2 xor N1,   N1 ~ Bern(p1)   (interfered link)
    Y2 = X2 xor N2,          N2 ~ Bern(p2)   (interference-free link)

Everything here is exact enumeration over binary alphabets (stdlib only, IEEE
double arithmetic; no sampling, no iterative optimization other than grids and
a concave 1-D maximization).

Computed objects, for several (p1, p2) with p1 > p2:

INNER BOUNDS (all standard, hence rigorous up to floating point):
  * TIN-u : treat interference as noise, uniform inputs  -> (0, 1-h(p2)).
  * TIN(t): treat interference as noise, X2 ~ Bern(b) with t = b*p2 (b optimized,
            X1 uniform):  R1 = 1 - h(q * t), R2 = h(t) - h(p2),
            where q = (p1-p2)/(1-2 p2) and a*b := a(1-b)+b(1-a).
  * TD    : time division between the two single-user corners.
  * HK    : Han-Kobayashi-style split for user 2 (common U, private satellite
            X2 | U), user 1 all-private with uniform X1; grid over
            P(U=1)=alpha and P(X2=1|U=u)=b_u; exact small LP per weight vector.

OUTER BOUNDS:
  * Trivial: R1 <= 1-h(p1), R2 <= 1-h(p2).
  * MGL outer bound (derived in the accompanying attempt file via Mrs. Gerber's
    Lemma):  R1 <= 1 - h( q * hinv( h(p2) + R2 ) ).
    This curve coincides analytically with the optimized-bias TIN curve.
  * Reference (NOT valid for p1 > p2): strong-regime sum bound R1+R2 <= 1-h(p1).

CONSISTENCY CHECKS:
  * every HK / TD / TIN point must satisfy the MGL outer bound (min slack >= 0
    up to 1e-9), otherwise the converse derivation would be refuted;
  * TIN curve minus MGL curve == 0 to machine precision;
  * gap profiles of TD and HK-grid inner bounds against the MGL outer curve.

Run:  python3 weak_regime_bounds.py
"""

import math
from itertools import product

LOG2 = math.log(2.0)


def h(p):
    """Binary entropy in bits."""
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -(p * math.log(p) + (1.0 - p) * math.log(1.0 - p)) / LOG2


def hinv(y):
    """Inverse of h on [0, 1/2], by bisection (60 iters ~ 1e-18)."""
    if y <= 0.0:
        return 0.0
    if y >= 1.0:
        return 0.5
    lo, hi = 0.0, 0.5
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if h(mid) < y:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def star(a, b):
    """Binary convolution a*b = a(1-b) + b(1-a)."""
    return a * (1.0 - b) + b * (1.0 - a)


# ------------------------------------------------------------------ entropies
def entropy(dist):
    s = 0.0
    for p in dist.values():
        if p > 0.0:
            s -= p * math.log(p)
    return s / LOG2


def marginal(joint, idx):
    out = {}
    for k, p in joint.items():
        kk = tuple(k[i] for i in idx)
        out[kk] = out.get(kk, 0.0) + p
    return out


def H(joint, idx):
    return entropy(marginal(joint, idx))


# ------------------------------------------------------- HK joint enumeration
def hk_quantities(p1, p2, alpha, b0, b1, a=0.5):
    """Exact info quantities for the HK-style superposition scheme.

    X1 ~ Bern(a); U ~ Bern(alpha); X2 | U=u ~ Bern(b_u);
    Y1 = X1^X2^N1, Y2 = X2^N2.  Variable order: (x1, u, x2, y1, y2).
    Returns (A1, B1, S1, P2, T2) =
      (I(X1;Y1|U), I(U;Y1|X1), I(X1,U;Y1), I(X2;Y2|U), I(X2;Y2)).
    """
    joint = {}
    for x1, u, x2, n1, n2 in product((0, 1), repeat=5):
        p = (a if x1 else 1 - a)
        p *= (alpha if u else 1 - alpha)
        bb = b1 if u else b0
        p *= (bb if x2 else 1 - bb)
        p *= (p1 if n1 else 1 - p1)
        p *= (p2 if n2 else 1 - p2)
        if p == 0.0:
            continue
        y1 = x1 ^ x2 ^ n1
        y2 = x2 ^ n2
        k = (x1, u, x2, y1, y2)
        joint[k] = joint.get(k, 0.0) + p
    X1, U, X2, Y1, Y2 = 0, 1, 2, 3, 4
    A1 = H(joint, (X1, U)) + H(joint, (Y1, U)) - H(joint, (U,)) - H(joint, (X1, Y1, U))
    B1 = H(joint, (U, X1)) + H(joint, (Y1, X1)) - H(joint, (X1,)) - H(joint, (U, Y1, X1))
    S1 = H(joint, (X1, U)) + H(joint, (Y1,)) - H(joint, (X1, U, Y1))
    P2 = H(joint, (X2, U)) + H(joint, (Y2, U)) - H(joint, (U,)) - H(joint, (X2, Y2, U))
    T2 = H(joint, (X2,)) + H(joint, (Y2,)) - H(joint, (X2, Y2))
    return A1, B1, S1, P2, T2


def hk_lp(quants, mu1, mu2):
    """Exact LP max of mu1*R1 + mu2*(R2c+R2p) over the HK polytope

       R1 <= A1, R2c <= B1, R1 + R2c <= S1, R2p <= P2, R2c + R2p <= T2, all >= 0.

    For fixed R2c the optimum is R1 = min(A1, S1-R2c), R2p = min(P2, T2-R2c);
    the objective is piecewise linear in R2c, so evaluating at the breakpoints
    {0, S1-A1, T2-P2, cmax} (clipped) is exact.  Returns (value, R1, R2)."""
    A1, B1, S1, P2, T2 = quants
    cmax = max(0.0, min(B1, S1, T2))
    cands = {0.0, cmax}
    for c in (S1 - A1, T2 - P2):
        if 0.0 < c < cmax:
            cands.add(c)
    best = (-1.0, 0.0, 0.0)
    for c in cands:
        r1 = max(0.0, min(A1, S1 - c))
        r2 = c + max(0.0, min(P2, T2 - c))
        val = mu1 * r1 + mu2 * r2
        if val > best[0]:
            best = (val, r1, r2)
    return best


# ------------------------------------------------------------ outer/inner curves
def outer_r1_of_r2(r2, p1, p2):
    """MGL outer bound: R1 <= 1 - h(q * hinv(h(p2)+R2)), q=(p1-p2)/(1-2p2)."""
    q = (p1 - p2) / (1.0 - 2.0 * p2)
    v = h(p2) + r2
    if v >= 1.0:
        return 0.0 if v > 1.0 + 1e-12 else 1.0 - h(star(q, 0.5))
    return 1.0 - h(star(q, hinv(v)))


def tin_point(t, p1, p2):
    """Optimized-bias TIN point at parameter t = b*p2 in [p2, 1/2]."""
    q = (p1 - p2) / (1.0 - 2.0 * p2)
    return 1.0 - h(star(q, t)), h(t) - h(p2)


def outer_support(mu1, mu2, p1, p2, n=200000):
    """max mu1*R1(t) + mu2*R2(t) along the MGL curve (fine grid; curve concave)."""
    best = -1.0
    arg = None
    for i in range(n + 1):
        t = p2 + (0.5 - p2) * i / n
        r1, r2 = tin_point(t, p1, p2)
        val = mu1 * r1 + mu2 * r2
        if val > best:
            best, arg = val, (t, r1, r2)
    return best, arg


# ---------------------------------------------------------------------- main
WEIGHTS = [(1, 0), (4, 1), (2, 1), (1, 1), (1, 2), (1, 4), (0, 1)]


def analyze(p1, p2, alpha_grid, b_grid, fine=False):
    assert p1 > p2
    C1, C2 = 1.0 - h(p1), 1.0 - h(p2)
    q = (p1 - p2) / (1.0 - 2.0 * p2)
    print("=" * 78)
    print(f"(p1, p2) = ({p1}, {p2})   [weak regime p1 > p2]")
    print(f"C1 = 1-h(p1) = {C1:.6f}   C2 = 1-h(p2) = {C2:.6f}   q = {q:.6f}")
    print(f"strong-regime sum bound 1-h(p1) = {C1:.6f}  (INVALID here, reference only)")
    print(f"  -> violated by achievable TIN-u point (0, {C2:.6f}): sum {C2:.6f} > {C1:.6f}")

    # --- consistency: TIN curve vs MGL outer curve (analytically identical)
    max_dev = 0.0
    N = 2000
    for i in range(N + 1):
        t = p2 + (0.5 - p2) * i / N
        r1, r2 = tin_point(t, p1, p2)
        max_dev = max(max_dev, abs(outer_r1_of_r2(r2, p1, p2) - r1))
    print(f"max |TIN curve - MGL outer curve| over {N+1} pts: {max_dev:.3e}")

    # --- HK grid
    hk_points = []
    for alpha in alpha_grid:
        for b0 in b_grid:
            for b1 in b_grid:
                qs = hk_quantities(p1, p2, alpha, b0, b1)
                for mu1, mu2 in WEIGHTS:
                    _, r1, r2 = hk_lp(qs, mu1, mu2)
                    hk_points.append((r1, r2))
    # dedupe (coarse)
    hk_points = sorted(set((round(r1, 12), round(r2, 12)) for r1, r2 in hk_points))
    print(f"HK grid: {len(alpha_grid)}x{len(b_grid)}x{len(b_grid)} configs, "
          f"{len(hk_points)} distinct optimal vertices collected")

    # --- validation: no achievable point above the MGL curve
    min_slack = float("inf")
    worst = None
    for r1, r2 in hk_points:
        s = outer_r1_of_r2(r2, p1, p2) - r1
        if s < min_slack:
            min_slack, worst = s, (r1, r2)
    lam_checks = [i / 50 for i in range(51)]
    for lam in lam_checks:  # TD points
        r1, r2 = lam * C1, (1 - lam) * C2
        s = outer_r1_of_r2(r2, p1, p2) - r1
        if s < min_slack:
            min_slack, worst = s, (r1, r2)
    print(f"min slack (outer R1 - achieved R1) over all HK+TD points: "
          f"{min_slack:.3e} at point ({worst[0]:.6f}, {worst[1]:.6f})")
    if min_slack < -1e-9:
        print("*** CONSISTENCY FAILURE: an achievable point exceeds the MGL outer "
              "bound -- the converse derivation would be refuted. ***")

    # --- does HK ever beat TIN?  (should not, since TIN curve = outer curve)
    max_hk_gain = -float("inf")
    for r1, r2 in hk_points:
        max_hk_gain = max(max_hk_gain, r1 - outer_r1_of_r2(r2, p1, p2))
    print(f"max (HK R1 - TIN/outer R1 at same R2): {max_hk_gain:.3e}  "
          f"(<=0 means rate splitting adds nothing beyond optimized TIN)")

    # --- weighted sum-rate table
    print(f"\n{'weights':>10} | {'MGL outer':>10} | {'TIN opt':>10} | "
          f"{'HK grid':>10} | {'TD':>10} | {'trivial':>10}")
    for mu1, mu2 in WEIGHTS:
        outer, _ = outer_support(mu1, mu2, p1, p2, n=100000 if fine else 20000)
        tin = outer  # identical curves
        hk = max(mu1 * r1 + mu2 * r2 for r1, r2 in hk_points)
        td = max(mu1 * lam * C1 + mu2 * (1 - lam) * C2 for lam in
                 [i / 1000 for i in range(1001)])
        triv = mu1 * C1 + mu2 * C2
        print(f"  mu=({mu1},{mu2}) | {outer:10.6f} | {tin:10.6f} | {hk:10.6f} | "
              f"{td:10.6f} | {triv:10.6f}")

    # --- sum rate specifically
    outer_sum, arg = outer_support(1, 1, p1, p2, n=200000)
    print(f"\nsum rate: MGL outer max = {outer_sum:.6f} at t = {arg[0]:.6f} "
          f"(corner: t=1/2 gives R=(0,{C2:.6f}))")
    print(f"          -> sum capacity = 1-h(p2) = {C2:.6f}, "
          f"achieved only at the (0, C2) corner")

    # --- boundary table at fixed R2 fractions
    print(f"\n{'R2/C2':>6} {'R2':>9} | {'outer=TIN R1':>12} | {'HK-hull R1':>11} | "
          f"{'TD R1':>9} | {'trivial R1':>10}")
    # upper concave envelope of HK points via support functions is overkill;
    # report best single HK point with R2 >= target (conservative for HK).
    for frac in (0.0, 0.25, 0.5, 0.75, 0.95, 1.0):
        r2t = frac * C2
        out_r1 = outer_r1_of_r2(r2t, p1, p2)
        hk_r1 = max([r1 for r1, r2 in hk_points if r2 >= r2t - 1e-9], default=0.0)
        td_r1 = (1 - r2t / C2) * C1
        print(f"{frac:6.2f} {r2t:9.6f} | {out_r1:12.6f} | {hk_r1:11.6f} | "
              f"{td_r1:9.6f} | {C1:10.6f}")

    # --- gap profiles vs the MGL outer curve
    def max_gap(inner_r1_fn):
        gmax, at = -1.0, None
        M = 400
        for i in range(M + 1):
            r2t = C2 * i / M
            g = outer_r1_of_r2(r2t, p1, p2) - inner_r1_fn(r2t)
            if g > gmax:
                gmax, at = g, r2t
        return gmax, at

    g_td, at_td = max_gap(lambda r2t: (1 - r2t / C2) * C1)
    g_hk, at_hk = max_gap(
        lambda r2t: max([r1 for r1, r2 in hk_points if r2 >= r2t - 1e-9],
                        default=0.0))
    print(f"\nlargest gap, MGL outer vs TD           : {g_td:.6f} bits at R2 = "
          f"{at_td:.6f} (R2/C2 = {at_td/C2:.3f})")
    print(f"largest gap, MGL outer vs HK grid pts  : {g_hk:.6f} bits at R2 = "
          f"{at_hk:.6f}  (grid-resolution artifact)")
    print(f"largest gap, trivial outer vs capacity : {C1:.6f} bits at R2 = C2 "
          f"(trivial box corner (C1, C2) vs true (0, C2))")
    return min_slack, max_hk_gain


def spot_check_x1_bias(p1, p2):
    """Numerical confirmation that X1 uniform (a = 1/2) dominates in the HK LP."""
    print("\nspot check: X1 bias a in {0.30, 0.40, 0.50}, best sum rate over a "
          "small (alpha,b0,b1) grid:")
    grid = [i / 10 for i in range(6)]
    for a in (0.30, 0.40, 0.50):
        best = 0.0
        for alpha in grid:
            for b0 in grid:
                for b1 in grid:
                    v, _, _ = hk_lp(hk_quantities(p1, p2, alpha, b0, b1, a=a), 1, 1)
                    best = max(best, v)
        print(f"  a = {a:.2f}: best sum rate = {best:.6f}")


def main():
    alpha_grid = [i / 20 for i in range(11)]          # 0, 0.05, ..., 0.5
    b_grid = [i / 25 for i in range(26)]              # 0, 0.04, ..., 1.0
    overall_ok = True
    for (p1, p2) in [(0.2, 0.05), (0.3, 0.1), (0.15, 0.1)]:
        ms, mg = analyze(p1, p2, alpha_grid, b_grid)
        overall_ok &= (ms > -1e-9)
        print()
    spot_check_x1_bias(0.2, 0.05)
    print("\nOVERALL:", "all achievable points consistent with the MGL outer bound"
          if overall_ok else "*** INCONSISTENCY FOUND ***")


if __name__ == "__main__":
    main()
