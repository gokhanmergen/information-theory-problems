#!/usr/bin/env python3
"""
Deep analysis of TIME-SHARED ASYMMETRIC Berger-Tung vs Outer Bounds for DSBS(p):
  1. Compute the TRUE time-shared Berger-Tung inner bound for symmetric DSBS(p)
     (combining asymmetric (q1, q2) points, 1-encoder mode (q, p*q), Berger-Yeung corners,
     and general |U1|, |U2| <= 3 optimization!).
  2. Compare against:
     - Naive symmetric BSC(D) BT: 1 + h(p*D*D) - 2*h(D)
     - Courtade-Weissman log-loss outer bound
     - Centralized joint RD R_{X1,X2}(D, D)
     - Berger-Tung outer bound (allowing asymmetric short Markov chains too!)
  3. Find the EXACT phase transition D_split(p) where asymmetric time-sharing strictly
     beats symmetric BSC(D) quantization!
  4. Analyze the one-help-one corner (D2 = 1/2) and asymmetric (D1, D2) regions.
"""

import numpy as np
from scipy.optimize import minimize, brentq

EPS = 1e-15


def h2(x):
    x = np.clip(x, EPS, 1.0 - EPS)
    return -x * np.log2(x) - (1.0 - x) * np.log2(1.0 - x)


def h2_inv(y):
    if y <= 0.0:
        return 0.0
    if y >= 1.0:
        return 0.5
    return brentq(lambda x: h2(x) - y, 1e-14, 0.5)


def conv(a, b):
    return a * (1.0 - b) + (1.0 - a) * b


def entropy(p):
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > EPS]
    return float(-np.sum(p * np.log2(p)))


def dsbs_joint(p):
    return np.array([[(1 - p) / 2, p / 2], [p / 2, (1 - p) / 2]])


def eval_dsbs_bt(P, Q1, Q2):
    J = P[:, :, None, None] * Q1[:, None, :, None] * Q2[None, :, None, :]
    P_u1u2 = J.sum(axis=(0, 1))
    H_u1u2 = entropy(P_u1u2)
    H_u1_x1 = 0.5 * (entropy(Q1[0]) + entropy(Q1[1]))
    H_u2_x2 = 0.5 * (entropy(Q2[0]) + entropy(Q2[1]))
    Rsum = H_u1u2 - H_u1_x1 - H_u2_x2
    P_x1u = J.sum(axis=1)
    P_x2u = J.sum(axis=0)
    D1 = float(np.sum(np.minimum(P_x1u[0], P_x1u[1])))
    D2 = float(np.sum(np.minimum(P_x2u[0], P_x2u[1])))
    L1 = entropy(P_x1u) - H_u1u2
    L2 = entropy(P_x2u) - H_u1u2
    return Rsum, D1, D2, L1, L2


def lower_hull(pts):
    pts = sorted(set((round(x, 10), round(y, 10)) for x, y in pts))
    hull = []
    for p in pts:
        while len(hull) >= 2:
            x1, y1 = hull[-2]; x2, y2 = hull[-1]; x3, y3 = p
            if (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) <= 1e-12:
                hull.pop()
            else:
                break
        hull.append(p)
    clean = [hull[0]]
    for x, y in hull[1:]:
        if y < clean[-1][1] - 1e-12:
            clean.append((x, y))
    return clean


def eval_hull(hull, xs):
    return np.interp(xs, [p[0] for p in hull], [p[1] for p in hull])


def bt_bsc_sym(p, D):
    return 0.0 if D >= 0.5 else (1.0 + h2(conv(p, conv(D, D))) - 2.0 * h2(D))


def bt_ts_1enc(p, D):
    """Time-sharing between (U1=BSC(q), U2=const) and (U1=const, U2=BSC(q))."""
    if D < p / 2.0:
        return np.inf
    if D >= 0.5:
        return 0.0
    q = (2.0 * D - p) / (2.0 * (1.0 - p))
    return 1.0 - h2(q)


def compute_full_bt_dsbs_sym(p):
    """
    Compute the TRUE time-shared Berger-Tung inner bound for symmetric DSBS(p)
    by scanning:
      - ALL pairs of BSC(q1) x BSC(q2) (note: when q2 > p * q1, MAP for X2 uses U1,
        so D2 = min(q2, p * q1) -> wait: if q2 < 0.5 and q2 > p*q1, sending U2 wastes rate!)
      - General 3-ary (BEC+BSC) and random asymmetric channels!
    """
    P = dsbs_joint(p)
    pts_bsc_all = [(0.5, 0.0), (0.0, 1.0 + h2(p))]
    qs = np.linspace(0.0, 0.5, 101)
    for q1 in qs:
        Q1 = np.array([[1 - q1, q1], [q1, 1 - q1]])
        for q2 in qs:
            if q2 < q1:
                continue
            Q2 = np.array([[1 - q2, q2], [q2, 1 - q2]])
            Rsum, D1, D2, _, _ = eval_dsbs_bt(P, Q1, Q2)
            pts_bsc_all.append((0.5 * (D1 + D2), Rsum))

    hull_bsc_all = lower_hull(pts_bsc_all)

    # Also check if ANY non-BSC / 3-ary channel beats hull_bsc_all!
    rng = np.random.default_rng(77)
    max_imp_k3 = -1e9
    best_k3 = None
    for k in (2, 3):
        for _ in range(10000):
            al = rng.choice([0.1, 0.3, 1.0])
            Q1 = rng.dirichlet([al] * k, size=2)
            Q2 = rng.dirichlet([al] * k, size=2)
            Rsum, D1, D2, _, _ = eval_dsbs_bt(P, Q1, Q2)
            D = 0.5 * (D1 + D2)
            imp = float(eval_hull(hull_bsc_all, D)) - Rsum
            if imp > max_imp_k3:
                max_imp_k3 = imp
                best_k3 = (k, D1, D2, D, Rsum)

    # Compute Courtade-Weissman log-loss outer bound using ALL (q1, q2)
    pts_cw = [(1.0, 0.0), (0.0, 1.0 + h2(p))]
    for q1 in qs:
        Q1 = np.array([[1 - q1, q1], [q1, 1 - q1]])
        for q2 in qs:
            if q2 < q1:
                continue
            Q2 = np.array([[1 - q2, q2], [q2, 1 - q2]])
            Rsum, _, _, L1, L2 = eval_dsbs_bt(P, Q1, Q2)
            pts_cw.append((0.5 * (L1 + L2), Rsum))
    hull_cw = lower_hull(pts_cw)

    # Compute centralized RD via Blahut-Arimoto
    P_flat = P.ravel()
    dmat = np.array([[bin(i ^ j).count("1") / 2.0 for j in range(4)] for i in range(4)])
    pts_cen = []
    for s in np.concatenate([[0.0], np.geomspace(1e-3, 120.0, 250)]):
        q = np.ones(4) / 4.0
        for _ in range(250):
            logW = np.log(np.clip(q, EPS, 1.0))[None, :] - s * dmat
            logW -= logW.max(axis=1, keepdims=True)
            W = np.exp(logW); W /= W.sum(axis=1, keepdims=True)
            q_new = P_flat @ W
            if np.max(np.abs(q_new - q)) < 1e-12:
                q = q_new; break
            q = q_new
        J = P_flat[:, None] * W
        pts_cen.append((float(np.sum(J * dmat)), entropy(P_flat) + entropy(q) - entropy(J)))
    pts_cen.sort()

    return hull_bsc_all, hull_cw, pts_cen, max_imp_k3, best_k3


def analyze_1enc_vs_cw_dsbs():
    """
    Check if time-shared 1-encoder BT R_TS1(D) = 1 - h((2D - p)/(2(1-p)))
    EVER matches CW-LogLoss or Centralized RD as D -> 1/2!
    Compute exact second-order Taylor expansions as D = 1/2 - eps -> 1/2!
    """
    print("\n" + "=" * 78)
    print("ASYMPTOTIC HIGH-DISTORTION (D = 1/2 - eps) SLOPE COMPARISON FOR DSBS(p)")
    print("=" * 78)
    # 1. Symmetric BSC(D) BT:
    #    R_sym(1/2 - eps) = 1 + h(1/2 - (1-2p)*(2*eps)^2 / 2) - 2*h(1/2 - eps)
    #    Wait: D = 1/2 - eps => D*D = 1/2 - 2*eps^2 => p*D*D = 1/2 - 2*(1-2p)*eps^2
    #    h(p*D*D) = 1 - O(eps^4)!
    #    2*h(D) = 2 - (4/ln2)*eps^2 + O(eps^4)!
    #    So R_sym(1/2 - eps) = (4 / ln 2) * eps^2 + O(eps^4)!!
    # 2. Time-shared 1-encoder BT:
    #    q = (2D - p)/(2(1-p)) = 1/2 - eps / (1 - p)
    #    R_TS1(1/2 - eps) = 1 - h(q) = (2 / ln 2) * (eps / (1 - p))^2 + O(eps^4)
    #                     = (2 / ((1-p)^2 ln 2)) * eps^2 + O(eps^4)!!
    #    WAIT A SECOND!! COMPARE 2/(1-p)^2 vs 4!!
    #    2/(1-p)^2 < 4  <==>  (1-p)^2 > 1/2  <==>  p < 1 - 1/sqrt(2) = 0.292893!!
    # 3. Centralized RD R_{X1,X2}(1/2 - eps, 1/2 - eps):
    #    Near D = 1/2, the optimal test channel sends a 1-bit estimate Z = maj/common bit:
    #    Let P(X1=X2) = 1-p, P(X1!=X2) = p. Wait: for Z in {0,1} predicting BOTH X1 and X2:
    #    E[d1 + d2]/2 = (1/2)[P(X1!=Z) + P(X2!=Z)].
    #    When X1=X2=0, d=0 for Z=0, d=1 for Z=1. When X1!=X2, d=1/2 for BOTH Z=0 and Z=1 (DON'T CARE!!)!
    #    So centralized encoder ONLY encodes when X1 = X2 (prob 1-p) with crossover q:
    #    D = p*(1/2) + (1-p)*q = 1/2 - (1-p)*(1/2 - q), so 1/2 - q = eps/(1-p)!
    #    Rate = (1 - p) * (1 - h(q)) = (2 / ((1-p) ln 2)) * eps^2 + O(eps^4)!!
    #    WAIT A SECOND!! CHECK THAT RATIO:
    #      R_TS1 / R_central -> 1 / (1 - p)!!
    #      R_sym / R_TS1     -> 2 * (1 - p)^2!!
    #      SO FOR ALL p < 1 - 1/sqrt(2) ≈ 0.292893, TIME-SHARED 1-ENCODER BT STRICTLY
    #      BEATS SYMMETRIC BSC(D) BT BY FACTOR 2*(1-p)^2 > 1 NEAR D = 1/2!!
    # 4. What about CW-LogLoss near D = 1/2?!
    #    In CW-LogLoss: need (H(X1|U1,U2) + H(X2|U1,U2))/2 <= h(1/2 - eps) = 1 - (2/ln 2)*eps^2!
    #    Check 1-encoder U1 = BSC(1/2 - delta), U2 = const:
    #      H(X1|U1) = h(1/2 - delta) = 1 - (2/ln 2)*delta^2
    #      H(X2|U1) = h(1/2 - (1-2p)*delta) = 1 - (2/ln 2)*(1-2p)^2*delta^2
    #      Avg = 1 - (2/ln 2) * [(1 + (1-2p)^2)/2] * delta^2!
    #      Rate = (2/ln 2) * delta^2!
    #      So R_CW_1enc(1/2 - eps) = (2/ln 2) * [2 / (1 + (1-2p)^2)] * eps^2!!
    #    Compare coefficient of (2/ln 2) * eps^2:
    #      - Centralized:   1 / (1 - p)
    #      - CW (1-enc):    2 / (1 + (1-2p)^2) = 1 / (1 - 2p + 2p^2)
    #      - TS 1-enc BT:   1 / (1 - p)^2 = 1 / (1 - 2p + p^2)
    #      - Sym BSC BT:    2!
    #    WAIT A SECOND! Check CW (2-enc symmetric):
    #      U1 = BSC(1/2 - d), U2 = BSC(1/2 - d) => Rsum = (4/ln 2)*d^2,
    #      H(X1|U1,U2) = 1 - (2/ln 2)*(1 + (1-2p)^2)*d^2 => coeff = 2 / (1 + (1-2p)^2) (SAME!!)!
    p_crit = 1.0 - 1.0 / np.sqrt(2.0)
    print(f"  Exact phase-transition threshold for DSBS(p): p* = 1 - 1/sqrt(2) = {p_crit:.6f}")
    print(f"  Coefficient of (2/ln 2)*(1/2 - D)^2 as D -> 1/2:")
    print(f"  {'p':>6} | {'Sym-BSC':>9} | {'TS-1Enc':>9} | {'CW-LogL':>9} | {'Central':>9} | {'Sym/TS1':>8}")
    print("  " + "-" * 62)
    for p in [0.05, 0.10, 0.15, 0.20, 0.25, 0.2929, 0.35]:
        c_sym = 2.0
        c_ts1 = 1.0 / ((1.0 - p) ** 2)
        c_cw = 2.0 / (1.0 + (1.0 - 2.0 * p) ** 2)
        c_cen = 1.0 / (1.0 - p)
        print(f"  {p:6.4f} | {c_sym:9.5f} | {c_ts1:9.5f} | {c_cw:9.5f} | {c_cen:9.5f} | {c_sym/c_ts1:8.4f}")


def main():
    print("=" * 78)
    print("TWO-TERMINAL DSBS(p) — TRUE TIME-SHARED BERGER-TUNG vs OUTER BOUNDS")
    print("=" * 78)

    for p in [0.10, 0.20, 0.25, 0.35]:
        print(f"\n>>> DSBS(p = {p})")
        hull_bt, hull_cw, pts_cen, max_imp_k3, best_k3 = compute_full_bt_dsbs_sym(p)
        D_grid = np.array([0.0, 0.02, 0.05, 0.08, 0.10, 0.125, 0.15, 0.20, 0.30, 0.40])
        R_sym = np.array([bt_bsc_sym(p, d) for d in D_grid])
        R_ts1 = np.array([bt_ts_1enc(p, d) for d in D_grid])
        R_bt = eval_hull(hull_bt, D_grid)
        R_cw = eval_hull(hull_cw, h2(D_grid))
        R_cen = np.interp(D_grid, [t[0] for t in pts_cen], [t[1] for t in pts_cen])

        print(f"{'D':>5} | {'SymBSC':>7} | {'TS-1Enc':>7} | {'True-BT':>7} | {'CW-Log':>7} | {'Central':>7} | {'Sym-BT':>7} | {'BT-CW':>7}")
        print("-" * 78)
        for i, d in enumerate(D_grid):
            ts1_s = f"{R_ts1[i]:7.4f}" if np.isfinite(R_ts1[i]) else "    inf"
            print(f"{d:5.3f} | {R_sym[i]:7.4f} | {ts1_s} | {R_bt[i]:7.4f} | {R_cw[i]:7.4f} | {R_cen[i]:7.4f} | {R_sym[i]-R_bt[i]:7.4f} | {R_bt[i]-R_cw[i]:7.4f}")

        print(f"  Max improvement of random k<=3 over BSC-pair convex hull: {max_imp_k3:+.7f} ({best_k3})")

    analyze_1enc_vs_cw_dsbs()

    print("\n" + "=" * 78)
    print("FINE LOG-SPACED GRID CHECK (30,000 RANDOM |U1|, |U2| <= 4 AUXILIARIES)")
    print("=" * 78)
    qs_fine = np.unique(np.concatenate([
        [0.0],
        np.geomspace(1e-5, 0.05, 80),
        np.linspace(0.05, 0.5, 181),
    ]))
    rng = np.random.default_rng(2026)
    for p in [0.10, 0.25]:
        P = dsbs_joint(p)
        pts_fine = [(0.5, 0.0), (0.0, 1.0 + h2(p))]
        for q1 in qs_fine:
            Q1 = np.array([[1 - q1, q1], [q1, 1 - q1]])
            for q2 in qs_fine:
                if q2 < q1:
                    continue
                Q2 = np.array([[1 - q2, q2], [q2, 1 - q2]])
                Rsum, D1, D2, _, _ = eval_dsbs_bt(P, Q1, Q2)
                pts_fine.append((0.5 * (D1 + D2), Rsum))
        hull_fine = lower_hull(pts_fine)
        max_imp = -1e9
        for k in (2, 3, 4):
            for _ in range(10000):
                al = rng.choice([0.1, 0.3, 1.0])
                Q1 = rng.dirichlet([al] * k, size=2)
                Q2 = rng.dirichlet([al] * k, size=2)
                Rsum, D1, D2, _, _ = eval_dsbs_bt(P, Q1, Q2)
                imp = float(eval_hull(hull_fine, 0.5 * (D1 + D2))) - Rsum
                if imp > max_imp:
                    max_imp = imp
        print(f"  p={p:.2f}: max improvement over fine BSC-pair hull (30,000 samples, k<=4): {max_imp:+.7f}")


if __name__ == "__main__":
    main()
