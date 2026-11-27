#!/usr/bin/env python3
"""
Fast, high-precision analysis of Two-Terminal DSBS(p) Multiterminal Source Coding:
  (X1, X2) ~ DSBS(p), separate Hamming distortions (D1, D2) in [0, 1/2]^2.
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
    # P: (2,2), Q1: (2,k1), Q2: (2,k2)
    J = P[:, :, None, None] * Q1[:, None, :, None] * Q2[None, :, None, :]
    P_u1u2 = J.sum(axis=(0, 1))
    H_u1u2 = entropy(P_u1u2)
    H_u1_x1 = 0.5 * (entropy(Q1[0]) + entropy(Q1[1]))
    H_u2_x2 = 0.5 * (entropy(Q2[0]) + entropy(Q2[1]))
    Rsum = H_u1u2 - H_u1_x1 - H_u2_x2
    R1 = H_u1u2 - entropy(P_u1u2.sum(axis=0)) - H_u1_x1
    R2 = H_u1u2 - entropy(P_u1u2.sum(axis=1)) - H_u2_x2
    P_x1u = J.sum(axis=1)
    P_x2u = J.sum(axis=0)
    D1 = float(np.sum(np.minimum(P_x1u[0], P_x1u[1])))
    D2 = float(np.sum(np.minimum(P_x2u[0], P_x2u[1])))
    L1 = entropy(P_x1u) - H_u1u2
    L2 = entropy(P_x2u) - H_u1u2
    return R1, R2, Rsum, D1, D2, L1, L2


def bt_bsc_sym(p, D):
    if D >= 0.5:
        return 0.0
    return 1.0 + h2(conv(p, conv(D, D))) - 2.0 * h2(D)


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


def centralized_dsbs_sym_rd(p, D_list):
    P = dsbs_joint(p).ravel()
    dmat = np.array([[bin(i ^ j).count("1") / 2.0 for j in range(4)] for i in range(4)])
    pts = []
    for s in np.concatenate([[0.0], np.geomspace(1e-3, 100.0, 250)]):
        q = np.ones(4) / 4.0
        for _ in range(250):
            logW = np.log(np.clip(q, EPS, 1.0))[None, :] - s * dmat
            logW -= logW.max(axis=1, keepdims=True)
            W = np.exp(logW); W /= W.sum(axis=1, keepdims=True)
            q_new = P @ W
            if np.max(np.abs(q_new - q)) < 1e-12:
                q = q_new; break
            q = q_new
        J = P[:, None] * W
        pts.append((float(np.sum(J * dmat)), entropy(P) + entropy(q) - entropy(J)))
    pts.sort()
    return np.interp(D_list, [t[0] for t in pts], [t[1] for t in pts])


def cw_logloss_dsbs_sym(p, D_list):
    """Courtade-Weissman log-loss outer bound for symmetric DSBS(p) at D_log = h2(D)."""
    P = dsbs_joint(p)
    pts = [(1.0, 0.0), (0.0, 1.0 + h2(p))]
    # Dense BSC(q1) x BSC(q2) grid
    qs = np.linspace(0.0, 0.5, 51)
    for q1 in qs:
        Q1 = np.array([[1 - q1, q1], [q1, 1 - q1]])
        for q2 in qs:
            Q2 = np.array([[1 - q2, q2], [q2, 1 - q2]])
            _, _, Rsum, _, _, L1, L2 = eval_dsbs_bt(P, Q1, Q2)
            pts.append((0.5 * (L1 + L2), Rsum))
    # Also random ternary check
    rng = np.random.default_rng(12)
    for _ in range(3000):
        Q1 = rng.dirichlet([0.5, 0.5, 0.5], size=2)
        Q2 = rng.dirichlet([0.5, 0.5, 0.5], size=2)
        _, _, Rsum, _, _, L1, L2 = eval_dsbs_bt(P, Q1, Q2)
        pts.append((0.5 * (L1 + L2), Rsum))
    hull = lower_hull(pts)
    return eval_hull(hull, h2(D_list))


def bt_outer_dsbs_sym(p, D_list):
    """
    Berger-Tung OUTER bound (short Markov chains U1-X1-X2, U2-X2-X1) for symmetric DSBS(p).
    Symmetric binary coupling: P(U1=1|X1=0)=q, P(U1=1|X1=1)=1-q, same for U2,
    plus free correlation parameter c00 = P(U1=1,U2=1|0,0), c01 = P(U1=1,U2=1|0,1)!
    Check exact achievable short-Markov-chain sum-rate!
    """
    P = dsbs_joint(p)
    pts = [(0.5, 0.0), (0.0, 1.0 + h2(p))]
    for q in np.linspace(0.01, 0.49, 49):
        # Symmetric constraints: a0=q, a1=1-q, b0=q, b1=1-q
        # On (0,0): lo=max(0, 2q-1)=0, hi=q. Set p11(0,0) = t_eq * q
        # On (1,1): symmetric => p00(1,1) = t_eq * q => p11(1,1) = 1 - 2q + t_eq * q
        # On (0,1): lo=0, hi=q. Set p10(0,1) = ... wait: a0=q, b1=1-q => lo=0, hi=q => p11(0,1) in [0, q]
        for t_eq in np.linspace(0.0, 1.0, 11):
            for t_neq in np.linspace(0.0, 1.0, 11):
                J = np.zeros((2, 2, 2, 2))
                # (0,0)
                p11 = t_eq * q
                J[0, 0] = P[0, 0] * np.array([[1 - 2 * q + p11, q - p11], [q - p11, p11]])
                # (1,1)
                J[1, 1] = P[1, 1] * np.array([[p11, q - p11], [q - p11, 1 - 2 * q + p11]])
                # (0,1): a=q, b=1-q
                p11n = t_neq * q
                J[0, 1] = P[0, 1] * np.array([[p11n, 1 - q - p11n], [q - p11n, p11n]])
                # Wait: check marginals of J[0,1]!
                # row sum u1=0: p11n + 1 - q - p11n = 1 - q = 1 - a0 OK!
                # row sum u1=1: q - p11n + p11n = q = a0 OK!
                # col sum u2=0: p11n + q - p11n = q = 1 - b1 OK!
                # col sum u2=1: 1 - q - p11n + p11n = 1 - q = b1 OK!
                # nonnegativity: p11n >= 0, q - p11n >= 0, 1 - q - p11n >= 0 (since q <= 0.5 => q <= 1-q) OK!
                J[1, 0] = P[1, 0] * J[0, 1].T / P[0, 1]  # by symmetry swap u1,u2
                P_u1u2 = J.sum(axis=(0, 1))
                P_u1 = P_u1u2.sum(axis=1)
                P_u2 = P_u1u2.sum(axis=0)
                Rsum_I = entropy(P) + entropy(P_u1u2) - entropy(J)
                P_x1u = J.sum(axis=1)
                P_x1u2 = P_x1u.sum(axis=1)
                R1 = (entropy(P_u1u2) - entropy(P_u2)) - (entropy(P_x1u) - entropy(P_x1u2))
                P_x2u = J.sum(axis=0)
                P_x2u1 = P_x2u.sum(axis=2)
                R2 = (entropy(P_u1u2) - entropy(P_u1)) - (entropy(P_x2u) - entropy(P_x2u1))
                Rsum = max(Rsum_I, R1 + R2)
                D1 = float(np.sum(np.minimum(P_x1u[0], P_x1u[1])))
                D2 = float(np.sum(np.minimum(P_x2u[0], P_x2u[1])))
                pts.append((0.5 * (D1 + D2), Rsum))
    hull = lower_hull(pts)
    return eval_hull(hull, D_list)


def search_bt_beat_bsc_dsbs(p, n_samples=15000, seed=0):
    """
    Test whether ANY Berger-Tung (Q1, Q2) with |U1|, |U2| in {2, 3, 4}
    EVER beats the lower convex hull of binary symmetric BSC(D) Berger-Tung!
    """
    P = dsbs_joint(p)
    bsc_dense = [(d, bt_bsc_sym(p, d)) for d in np.linspace(0.0, 0.5, 1001)]
    bsc_hull = lower_hull(bsc_dense)

    best_margin = -1e9
    best_info = None

    def check(Q1, Q2, label):
        nonlocal best_margin, best_info
        R1, R2, Rsum, D1, D2, _, _ = eval_dsbs_bt(P, Q1, Q2)
        D = 0.5 * (D1 + D2)
        Rbsc = float(eval_hull(bsc_hull, D))
        margin = Rbsc - Rsum
        if margin > best_margin:
            best_margin = margin
            best_info = (label, D1, D2, D, Rsum, Rbsc, Q1.copy(), Q2.copy())

    # 1. Check asymmetric BSC(q1) x BSC(q2) (different distortions D1 != D2 whose average is D!)
    qs = np.linspace(0.0, 0.5, 51)
    for q1 in qs:
        Q1 = np.array([[1 - q1, q1], [q1, 1 - q1]])
        for q2 in qs:
            Q2 = np.array([[1 - q2, q2], [q2, 1 - q2]])
            check(Q1, Q2, "Asym-BSC")

    # 2. Check Z-channel and symmetric 3-ary (BEC+BSC)
    for a in np.linspace(0.0, 0.9, 19):
        for b in np.linspace(0.0, (1 - a) / 2, 15):
            Q = np.array([[1 - a - b, b, a], [b, 1 - a - b, a]])
            check(Q, Q, "Sym-3ary")

    # 3. Random Dirichlet search over k=2,3,4
    rng = np.random.default_rng(seed)
    for k in (2, 3, 4):
        for _ in range(n_samples // 3):
            al = rng.choice([0.1, 0.3, 1.0, 3.0])
            Q1 = rng.dirichlet([al] * k, size=2)
            Q2 = rng.dirichlet([al] * k, size=2)
            check(Q1, Q2, f"Rand-k{k}")

    # 4. Nelder-Mead local optimization directly maximizing (R_bsc_hull(D) - Rsum)
    for k in (2, 3, 4):
        dim = 4 * (k - 1)
        def unpack(th):
            m = 2 * (k - 1)
            L1 = np.zeros((2, k)); L1[:, :k - 1] = th[:m].reshape(2, k - 1)
            L1 -= L1.max(axis=1, keepdims=True)
            Q1 = np.exp(L1); Q1 /= Q1.sum(axis=1, keepdims=True)
            L2 = np.zeros((2, k)); L2[:, :k - 1] = th[m:].reshape(2, k - 1)
            L2 -= L2.max(axis=1, keepdims=True)
            Q2 = np.exp(L2); Q2 /= Q2.sum(axis=1, keepdims=True)
            return Q1, Q2

        def neg_margin(th):
            Q1, Q2 = unpack(th)
            _, _, Rsum, D1, D2, _, _ = eval_dsbs_bt(P, Q1, Q2)
            D = 0.5 * (D1 + D2)
            return Rsum - float(eval_hull(bsc_hull, D))

        for _ in range(25):
            x0 = rng.normal(0, 2.0, size=dim)
            res = minimize(neg_margin, x0, method="Nelder-Mead", options={"maxiter": 500})
            Q1, Q2 = unpack(res.x)
            check(Q1, Q2, f"Opt-k{k}")

    return bsc_hull, best_margin, best_info


def test_structured_codes_dsbs(p):
    """
    Test exact finite-blocklength structured quantize-and-bin codes on DSBS(p):
      - 3-bit, 5-bit, 7-bit repetition (majority) code
      - [7,4] Hamming code quantizer (D = 1/8 = 0.125!)
    Compare (1/k) H(U1^k, U2^k) against BT-BSC hull!
    """
    bsc_dense = [(d, bt_bsc_sym(p, d)) for d in np.linspace(0.0, 0.5, 1001)]
    bsc_hull = lower_hull(bsc_dense)
    results = []

    # 1. k-bit majority vote
    for k in (3, 5, 7):
        # Exact joint P(X1_0, U1, U2) where U1 = maj(X1^k), U2 = maj(X2^k)
        dp = np.zeros((1, 1)); dp[0, 0] = 1.0
        P_x = dsbs_joint(p)
        for _ in range(k - 1):
            ndp = np.zeros((dp.shape[0] + 1, dp.shape[1] + 1))
            for x1 in (0, 1):
                for x2 in (0, 1):
                    ndp[x1:x1 + dp.shape[0], x2:x2 + dp.shape[1]] += dp * P_x[x1, x2]
            dp = ndp
        thr = k // 2 + 1
        P_u_x10 = np.zeros((2, 2))
        for a in range(k):
            for b in range(k):
                w = dp[a, b]
                for x2 in (0, 1):
                    u1 = 1 if a >= thr else 0
                    u2 = 1 if (b + x2) >= thr else 0
                    P_u_x10[u1, u2] += w * P_x[0, x2]
        P_u_x11 = P_u_x10[::-1, ::-1]
        P_u = P_u_x10 + P_u_x11
        Rsum = entropy(P_u) / k
        D = float(np.sum(np.minimum(P_u_x10, P_u_x11)))
        Rbsc = float(eval_hull(bsc_hull, D))
        results.append((f"Maj-{k}", D, Rsum, Rbsc, Rbsc - Rsum))

    # 2. [7,4] Hamming code quantizer
    H = np.array([[int(b) for b in f"{i:03b}"] for i in range(1, 8)]).T
    codewords = [y for y in range(128) if np.all((H @ np.array([(y >> j) & 1 for j in range(7)])) % 2 == 0)]
    cw_idx = {c: i for i, c in enumerate(codewords)}
    quant = np.zeros(128, dtype=int)
    for y in range(128):
        v = np.array([(y >> j) & 1 for j in range(7)])
        syn = (H @ v) % 2
        s = syn[0] * 4 + syn[1] * 2 + syn[2]
        c = y if s == 0 else (y ^ (1 << (s - 1)))
        quant[y] = cw_idx[c]

    pop = np.array([bin(i).count("1") for i in range(128)])
    wt_mat = pop[np.bitwise_xor.outer(np.arange(128), np.arange(128))]
    P_x1x2 = (1.0 / 128.0) * (p ** wt_mat) * ((1.0 - p) ** (7 - wt_mat))
    Qmat = np.zeros((128, 16))
    Qmat[np.arange(128), quant] = 1.0
    P_u1u2 = Qmat.T @ P_x1x2 @ Qmat
    Rsum_h74 = entropy(P_u1u2) / 7.0
    # Distortion of X1_0 given (U1, U2):
    mask0 = (np.arange(128) & 1) == 0
    P_x10_u = Qmat[mask0].T @ P_x1x2[mask0] @ Qmat
    P_x11_u = Qmat[~mask0].T @ P_x1x2[~mask0] @ Qmat
    D_h74 = float(np.sum(np.minimum(P_x10_u, P_x11_u)))
    Rbsc_h74 = float(eval_hull(bsc_hull, D_h74))
    results.append(("Hamming-[7,4]", D_h74, Rsum_h74, Rbsc_h74, Rbsc_h74 - Rsum_h74))

    return results


def main():
    print("=" * 78)
    print("TWO-TERMINAL DSBS(p) MULTITERMINAL SOURCE CODING — DEEP ANALYSIS")
    print("=" * 78)

    for p in [0.1, 0.25]:
        print(f"\n>>> DSBS(p = {p}), Symmetric Distortion D1 = D2 = D")
        D_grid = np.array([0.0, 0.02, 0.05, 0.10, 0.125, 0.15, 0.20, 0.30, 0.40])
        R_bsc = np.array([bt_bsc_sym(p, d) for d in D_grid])
        bsc_hull, margin, info = search_bt_beat_bsc_dsbs(p, n_samples=15000, seed=7)
        R_bsc_h = eval_hull(bsc_hull, D_grid)
        R_bt_out = bt_outer_dsbs_sym(p, D_grid)
        R_cw = cw_logloss_dsbs_sym(p, D_grid)
        R_cent = centralized_dsbs_sym_rd(p, D_grid)
        R_km = np.array([2 * h2(p) + 1.0 - h2(d) for d in D_grid])

        print(f"{'D':>5} | {'BT-BSC':>7} | {'BT-BSCh':>7} | {'BT-Out':>7} | {'CW-Log':>7} | {'Central':>7} | {'KM-hyb':>7} | {'Gap(BT-CW)':>10}")
        print("-" * 78)
        for i, d in enumerate(D_grid):
            print(f"{d:5.3f} | {R_bsc[i]:7.4f} | {R_bsc_h[i]:7.4f} | {R_bt_out[i]:7.4f} | {R_cw[i]:7.4f} | {R_cent[i]:7.4f} | {R_km[i]:7.4f} | {R_bsc_h[i]-R_cw[i]:10.4f}")

        print(f"\n  [Non-convexity of BT-BSC & General |U|<=4 Check]:")
        print(f"    Max (BT-BSC - BT-BSC_hull) = {np.max(R_bsc - R_bsc_h):.6f}")
        print(f"    Max (BT-BSC_hull - General BT |U|<=4) = {margin:+.7f}  (via {info[0]}, D1={info[1]:.4f}, D2={info[2]:.4f}, R={info[4]:.5f} vs {info[5]:.5f})")

        print(f"\n  [Structured k-bit Quantize-and-Bin (Majority & Hamming [7,4])]:")
        for name, D, Rsum, Rbsc, diff in test_structured_codes_dsbs(p):
            print(f"    {name:14s}: D={D:.5f}, R_sum={Rsum:.5f}, R_BSCh(D)={Rbsc:.5f}, (BT - Struct)={diff:+.5f}")

        # One-help-one check (D2 = 1/2, R2 = 0.5)
        beta = h2_inv(0.5)
        q_eff = conv(p, beta)
        wz_pts = [(q_eff, 0.0)] + [(d, h2(conv(q_eff, d)) - h2(d)) for d in np.linspace(0, q_eff, 300)]
        wz_hull = lower_hull(wz_pts)
        print(f"\n  [One-Help-One: DSBS({p}), D2=0.5, R2=0.5 => beta={beta:.4f}, q_eff={q_eff:.4f}]")
        for d1 in np.linspace(0.0, q_eff, 6):
            rwz = float(eval_hull(wz_hull, d1))
            rmgl = max(0.0, h2(q_eff) - h2(d1))
            print(f"    D1={d1:.4f}: R1(WZ/BT)={rwz:.5f}, R1(MGL-Fano outer)={rmgl:.5f}, gap={rwz-rmgl:.5f}")


if __name__ == "__main__":
    main()
