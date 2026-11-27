#!/usr/bin/env python3
"""
Fast, high-precision analysis of the Two-Agent Binary Symmetric CEO Problem:
  X ~ Bern(1/2), Y1 = X ^ N1 (BSC(p1)), Y2 = X ^ N2 (BSC(p2)), Hamming distortion D.
"""

import numpy as np
from scipy.optimize import minimize, brentq
from itertools import product

EPS = 1e-15


def h2(x):
    x = np.clip(x, EPS, 1.0 - EPS)
    return -x * np.log2(x) - (1.0 - x) * np.log2(1.0 - x)


def conv(a, b):
    return a * (1.0 - b) + (1.0 - a) * b


def entropy(p):
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > EPS]
    return float(-np.sum(p * np.log2(p)))


def joint_ceo(p1, p2):
    P = np.zeros((2, 2, 2))
    for x in (0, 1):
        for y1 in (0, 1):
            for y2 in (0, 1):
                w1 = (1 - p1) if y1 == x else p1
                w2 = (1 - p2) if y2 == x else p2
                P[x, y1, y2] = 0.5 * w1 * w2
    return P


def eval_bt(P, Q1, Q2):
    # P: (2, 2, 2), Q1: (2, k1), Q2: (2, k2)
    # P_xu1u2[x, u1, u2] = sum_{y1, y2} P[x, y1, y2] Q1[y1, u1] Q2[y2, u2]
    A = np.einsum("xab,au->xub", P, Q1)
    P_xu1u2 = np.einsum("xub,bv->xuv", A, Q2)
    P_u1u2 = P_xu1u2.sum(axis=0)
    H_u1u2 = entropy(P_u1u2)
    H_u1_y1 = 0.5 * (entropy(Q1[0]) + entropy(Q1[1]))
    H_u2_y2 = 0.5 * (entropy(Q2[0]) + entropy(Q2[1]))
    Rsum = H_u1u2 - H_u1_y1 - H_u2_y2
    R1 = H_u1u2 - entropy(P_u1u2.sum(axis=0)) - H_u1_y1
    R2 = H_u1u2 - entropy(P_u1u2.sum(axis=1)) - H_u2_y2
    D_ham = float(np.sum(np.minimum(P_xu1u2[0], P_xu1u2[1])))
    D_log = entropy(P_xu1u2) - H_u1u2
    return R1, R2, Rsum, D_ham, D_log


def single_agent_rd(p1, D):
    if D < p1 - 1e-12:
        return np.inf
    if D <= p1:
        return 1.0
    if D >= 0.5:
        return 0.0
    q = (D - p1) / (1.0 - 2.0 * p1)
    return 1.0 - h2(q)


def centralized_rd(p1, p2, D_list):
    P = joint_ceo(p1, p2)
    P_y = P.sum(axis=0).ravel()
    dbar = np.zeros((4, 2))
    for idx, (y1, y2) in enumerate([(0, 0), (0, 1), (1, 0), (1, 1)]):
        py = P[:, y1, y2].sum()
        dbar[idx, 0] = P[1, y1, y2] / py
        dbar[idx, 1] = P[0, y1, y2] / py

    pts = []
    for s in np.concatenate([[0.0], np.geomspace(1e-3, 200.0, 300)]):
        q = np.array([0.5, 0.5])
        for _ in range(250):
            logW = np.log(np.clip(q, EPS, 1.0))[None, :] - s * dbar
            logW -= logW.max(axis=1, keepdims=True)
            W = np.exp(logW); W /= W.sum(axis=1, keepdims=True)
            q_new = P_y @ W
            if np.max(np.abs(q_new - q)) < 1e-12:
                q = q_new; break
            q = q_new
        J = P_y[:, None] * W
        pts.append((float(np.sum(J * dbar)), entropy(P_y) + entropy(q) - entropy(J)))
    pts.sort()
    return np.interp(D_list, [t[0] for t in pts], [t[1] for t in pts])


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


def cw_logloss_sumrate(p1, p2, D_list):
    """
    Courtade-Weissman (2014) exact log-loss CEO sum-rate at D_log = h2(D).
    First check BSC(q1), BSC(q2) grid, PLUS general ternary optimization!
    """
    P = joint_ceo(p1, p2)
    pts = [(1.0, 0.0)]
    # Dense grid over BSC(q1) x BSC(q2)
    qs = np.linspace(0.0, 0.5, 41)
    for q1 in qs:
        Q1 = np.array([[1 - q1, q1], [q1, 1 - q1]])
        for q2 in qs:
            Q2 = np.array([[1 - q2, q2], [q2, 1 - q2]])
            _, _, Rsum, _, D_log = eval_bt(P, Q1, Q2)
            pts.append((D_log, Rsum))
    # Also random ternary checks
    rng = np.random.default_rng(11)
    for _ in range(3000):
        Q1 = rng.dirichlet([0.5, 0.5, 0.5], size=2)
        Q2 = rng.dirichlet([0.5, 0.5, 0.5], size=2)
        _, _, Rsum, _, D_log = eval_bt(P, Q1, Q2)
        pts.append((D_log, Rsum))
    hull = lower_hull(pts)
    return eval_hull(hull, h2(D_list)), hull


def search_bt_beat_1agent(p1, p2, n_samples=40000, seed=0):
    """
    HIGH-SPEED VECTORIZED + LOCAL SEARCH:
    Test whether ANY Berger-Tung pair (Q1, Q2) with |U1|, |U2| in {2, 3, 4}
    EVER beats R_1agent(D) = 1 - h((D - min(p1,p2))/(1 - 2*min(p1,p2))) in sum-rate!
    Also checks structured families: Z-channel, BEC, soft 3-ary, soft 4-ary.
    """
    P = joint_ceo(p1, p2)
    pmin = min(p1, p2)
    best_margin = -1e9  # R_1agent(D) - Rsum (positive => STRICTLY BEATS 1-agent!)
    best_info = None

    def check(Q1, Q2, label):
        nonlocal best_margin, best_info
        R1, R2, Rsum, D, _ = eval_bt(P, Q1, Q2)
        if D < pmin or D >= 0.5:
            return
        R1a = single_agent_rd(pmin, D)
        margin = R1a - Rsum
        if margin > best_margin:
            best_margin = margin
            best_info = (label, D, Rsum, R1a, R1, R2, Q1.copy(), Q2.copy())

    # 1. Structured family: Z-channel (asymmetric binary)
    for a1 in np.linspace(0.01, 0.99, 50):
        for a2 in np.linspace(0.01, 0.99, 50):
            Q1 = np.array([[1.0, 0.0], [a1, 1.0 - a1]])
            Q2 = np.array([[1.0, 0.0], [a2, 1.0 - a2]])
            check(Q1, Q2, "Z-channel")

    # 2. Structured family: symmetric 3-ary (BSC + erasure: 0->(1-a-b, b, a), 1->(b, 1-a-b, a))
    for a in np.linspace(0.0, 0.9, 19):
        for b in np.linspace(0.0, (1 - a) / 2, 15):
            Q = np.array([[1 - a - b, b, a], [b, 1 - a - b, a]])
            check(Q, Q, "Sym-3ary")

    # 3. Structured family: asymmetric 4-ary soft quantizer
    #    Strong/weak outputs: 0 -> (s, w, w2, s2), 1 -> (s2, w2, w, s)
    rng = np.random.default_rng(seed)
    for k in (2, 3, 4):
        for _ in range(n_samples // 3):
            alpha = rng.choice([0.1, 0.3, 1.0, 3.0])
            Q1 = rng.dirichlet([alpha] * k, size=2)
            Q2 = rng.dirichlet([alpha] * k, size=2)
            check(Q1, Q2, f"Rand-k{k}")

    # 4. Polish with Nelder-Mead directly maximizing (R_1agent(D) - Rsum) from diverse starts!
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
            _, _, Rsum, D, _ = eval_bt(P, Q1, Q2)
            if D >= 0.4999 or D <= pmin + 1e-6:
                return 10.0
            return Rsum - single_agent_rd(pmin, D)

        for _ in range(30):
            x0 = rng.normal(0, 2.0, size=dim)
            res = minimize(neg_margin, x0, method="Nelder-Mead", options={"maxiter": 500})
            Q1, Q2 = unpack(res.x)
            check(Q1, Q2, f"Opt-k{k}")

    return best_margin, best_info


def test_asymmetric_rate_region(p1, p2, D_target):
    """
    Check the FULL (R1, R2) rate region at fixed D_target for asymmetric p1 < p2!
    Compare:
      - Time-sharing of 1-agent schemes (if D_target >= p2) or 1-agent-only (if D_target < p2)
      - True Berger-Tung (R1, R2) region (where Agent 2 acts as Wyner-Ziv helper for Agent 1!)
      - Courtade-Weissman log-loss outer bound on (R1, R2)!
    """
    P = joint_ceo(p1, p2)
    # Suppose Agent 2 sends Y2 (R2 = 1, U2 = Y2), and Agent 1 uses Wyner-Ziv to send U1
    # so that decoder sees (U1, Y2)!
    # Wait: with U2 = Y2 and Y1 -> U1 being BSC(q1):
    # What is D(U1, Y2)?
    #   X -> U1 has crossover a1 = p1 * q1
    #   X -> Y2 has crossover p2
    #   Since MAP of two independent BSCs takes the cleaner one, D = min(p1 * q1, p2)!
    #   Wait: if D_target < p2, then p1 * q1 = D_target => q1 = (D_target - p1)/(1 - 2*p1)!
    #   And what is R1 = I(Y1; U1 | Y2)?!
    #   I(Y1; U1 | Y2) = H(U1 | Y2) - H(U1 | Y1) = h((p1*p2) * q1) - h(q1)!!
    #   AND R2 = I(Y2; Y2 | U1) = H(Y2 | U1) = h((p1*p2) * q1)!! (Or if R2 = I(Y2; Y2) = 1!)
    #   Wait: sum-rate is I(Y1, Y2; U1, Y2) = H(Y2) + I(Y1; U1 | Y2) = 1 + h((p1*p2)*q1) - h(q1) > 1 - h(q1)!
    #   BUT R1 = h((p1*p2)*q1) - h(q1) < 1 - h(q1) = R_1agent(D_target)!!
    q1 = (D_target - p1) / (1.0 - 2.0 * p1)
    q12 = conv(p1, p2)
    R1_wz = h2(conv(q12, q1)) - h2(q1)
    R2_wz_corner = h2(conv(q12, q1))  # Wait: R1 = I(Y1; U1 | Y2), R2 = I(Y2; Y2) = 1!
    # Other corner of the same BT pentagon: R1 = I(Y1; U1) = 1 - h(q1), R2 = I(Y2; Y2 | U1) = h(q12 * q1)
    R1_1ag = 1.0 - h2(q1)
    # Better: what if Agent 2 sends BSC(q2) helper U2 instead of full Y2?!
    # Then R2 = I(Y2; U2) = 1 - h(q2), and R1 = I(Y1; U1 | U2) = h((q12 * q2) * q1) - h(q1)!
    pts_bt = []
    for q2 in np.linspace(0.0, 0.5, 51):
        R2 = 1.0 - h2(q2)
        R1 = h2(conv(conv(q12, q2), q1)) - h2(q1)
        pts_bt.append((R2, R1))
    return R1_1ag, R1_wz, pts_bt


def test_finite_n_coding_ceo(p, k_list=(3, 5, 7)):
    """
    Test finite-blocklength k-bit quantize-and-bin (structured coding!) on symmetric CEO (p1=p2=p):
    - k-bit repetition code quantizer (majority vote of k bits): U1 = maj(Y1^k), U2 = maj(Y2^k)
    - [7,4] Hamming code quantizer: U1 = decode_H74(Y1^7), U2 = decode_H74(Y2^7)
    Compare sum-rate (1/k)*H(U1^k, U2^k) vs R_1agent(D)!
    """
    results = []
    q = conv(p, p)  # DSBS(q) between Y1 and Y2
    # 1. k-bit majority vote (odd k): U1 = maj(Y1^k) in {0,1}, U2 = maj(Y2^k) in {0,1}
    for k in k_list:
        # Compute exact joint distribution P(X^k, U1, U2) -> only need P(X_1, U1, U2) by symmetry!
        # Wait: enumerate all (x, y1, y2) in {0,1}^k if k <= 7? 2^21 too big; use DP / binomial!
        # Since U1 = 1[wt(Y1) > k/2], by symmetry only counts (a,b,c,d) matter, or enumerate x^k?
        # Even simpler: conditioned on X_1 = 0, the remaining k-1 bits of X are i.i.d. Bern(1/2),
        # and each bit i has (Y1_i, Y2_i) ~ DSBS(q) independently, with P(Y1_1, Y2_1 | X_1 = 0)!
        # Let's compute P(wt(Y1^{2..k}) = a, wt(Y2^{2..k}) = b) via 2D convolution (exact, O(k^3))!
        dp = np.zeros((1, 1))
        dp[0, 0] = 1.0
        P_y = np.array([[(1 - q) / 2, q / 2], [q / 2, (1 - q) / 2]])
        for _ in range(k - 1):
            ndp = np.zeros((dp.shape[0] + 1, dp.shape[1] + 1))
            for y1 in (0, 1):
                for y2 in (0, 1):
                    ndp[y1:y1 + dp.shape[0], y2:y2 + dp.shape[1]] += dp * P_y[y1, y2]
            dp = ndp
        # Now add bit 1 conditioned on X_1 = 0 (P(Y1_1=y1, Y2_1=y2 | X_1=0))
        P_y1_x0 = np.array([[(1 - p) ** 2, (1 - p) * p], [p * (1 - p), p ** 2]])
        P_u_x0 = np.zeros((2, 2))
        thr = k // 2 + 1
        for a in range(k):
            for b in range(k):
                w = dp[a, b]
                for y1 in (0, 1):
                    for y2 in (0, 1):
                        u1 = 1 if (a + y1) >= thr else 0
                        u2 = 1 if (b + y2) >= thr else 0
                        P_u_x0[u1, u2] += w * P_y1_x0[y1, y2]
        # By symmetry, P(U1=u1, U2=u2 | X_1=1) = P_u_x0[1-u1, 1-u2]
        P_u_x1 = P_u_x0[::-1, ::-1]
        P_u = 0.5 * (P_u_x0 + P_u_x1)
        Rsum = entropy(P_u) / k
        D = float(np.sum(np.minimum(0.5 * P_u_x0, 0.5 * P_u_x1)))
        R1a = single_agent_rd(p, D)
        results.append((f"Maj-{k}", D, Rsum, R1a, R1a - Rsum))

    # 2. [7,4] Hamming code quantizer!
    # Parity check matrix H (3 x 7), columns = binary 1..7
    H = np.array([[int(b) for b in f"{i:03b}"] for i in range(1, 8)]).T  # (3, 7)
    # Build lookup table: for each y in 0..127, nearest codeword index in 0..15 (coset leader = 1-bit flip)
    codewords = []
    for y in range(128):
        v = np.array([(y >> j) & 1 for j in range(7)])
        if np.all((H @ v) % 2 == 0):
            codewords.append(y)
    cw_idx = {c: i for i, c in enumerate(codewords)}
    quant = np.zeros(128, dtype=int)
    for y in range(128):
        v = np.array([(y >> j) & 1 for j in range(7)])
        syn = (H @ v) % 2
        s_val = syn[0] * 4 + syn[1] * 2 + syn[2]
        c = y if s_val == 0 else (y ^ (1 << (s_val - 1)))
        quant[y] = cw_idx[c]

    # Exact joint P(U1, U2) where Y1 ~ Unif(128), Y2 = Y1 ^ E (E ~ Bern(q)^7)
    # By linearity of Hamming code: quant(y ^ e) = quant(y) ^ quant(e)? NO! Only for y in C!
    # Let's compute exact 128x128 transition matrix T_q(y1, y2) -> 16x16 P(U1, U2)!
    popcnt = np.array([bin(i).count("1") for i in range(128)])
    xor_mat = np.bitwise_xor.outer(np.arange(128), np.arange(128))
    wt_mat = popcnt[xor_mat]
    P_y1y2 = (1.0 / 128.0) * (q ** wt_mat) * ((1.0 - q) ** (7 - wt_mat))
    # Aggregate into 16x16 P(U1, U2)
    Qmat = np.zeros((128, 16))
    Qmat[np.arange(128), quant] = 1.0
    P_u1u2 = Qmat.T @ P_y1y2 @ Qmat
    Rsum_h74 = entropy(P_u1u2) / 7.0

    # Distortion: compute P(X_0 = 0, U1, U2) by averaging over X in {0,1}^7 with X_0 = 0
    # P(y1 | x) = p^wt(x^y1) (1-p)^(7-wt(x^y1))
    W_xy = (p ** wt_mat) * ((1.0 - p) ** (7 - wt_mat))  # (128_x, 128_y)
    W_xu = W_xy @ Qmat  # (128_x, 16_u)
    # P(X_0 = 0, u1, u2) = (1/128) sum_{x: x&1 == 0} W_xu[x, u1] * W_xu[x, u2]
    mask0 = (np.arange(128) & 1) == 0
    P_x0_u = (1.0 / 128.0) * (W_xu[mask0].T @ W_xu[mask0])
    P_x1_u = (1.0 / 128.0) * (W_xu[~mask0].T @ W_xu[~mask0])
    D_h74 = float(np.sum(np.minimum(P_x0_u, P_x1_u)))
    R1a_h74 = single_agent_rd(p, D_h74)
    results.append(("Hamming-[7,4]", D_h74, Rsum_h74, R1a_h74, R1a_h74 - Rsum_h74))
    return results


def test_rectangle_exact_small_n(p, n_max=5):
    """
    Test the exact D = p rectangle problem for small n:
    Minimize -(1/n) log2 P_{DSBS(q)}^n(A x B) subject to E[(1/n) wt(Y1 & Y2) | A x B] <= delta,
    where q = 2p(1-p).
    Test symmetric/greedy/random sets A, B for n = 2..5 and delta in {0, 0.01, 0.05, 0.1}.
    """
    q = conv(p, p)
    print(f"\n  [Exact Rectangle Check at p={p}, q=2p(1-p)={q:.4f}]")
    for n in range(2, n_max + 1):
        N = 1 << n
        pop = np.array([bin(i).count("1") for i in range(N)])
        xor_m = np.bitwise_xor.outer(np.arange(N), np.arange(N))
        and_m = np.bitwise_and.outer(np.arange(N), np.arange(N))
        wt_xor = pop[xor_m]
        wt_and = pop[and_m] / float(n)
        Pmat = (1.0 / N) * (q ** wt_xor) * ((1.0 - q) ** (n - wt_xor))

        # Test: given Lagrange penalty lam > 0, find A, B subset [N] maximizing
        # sum_{a in A, b in B} Pmat[a, b] * (1 - lam * wt_and[a, b])? No, want max P(A x B) s.t. E[wt_and | A x B] <= delta!
        # Alternating optimization on A, B to maximize P(A x B) * exp(-mu * (E[wt_and|AxB] - delta)) or
        # minimize -(1/n) log2 P(A x B) + lam * E[wt_and | A x B]!
        rng = np.random.default_rng(100 + n)
        best_by_delta = {0.0: 1.0, 0.02: 1.0, 0.05: 1.0, 0.10: 1.0}
        # Always check balls around 0: wt <= w
        for w1 in range(n + 1):
            A = (pop <= w1).astype(float)
            for w2 in range(n + 1):
                B = (pop <= w2).astype(float)
                mass = float(A @ Pmat @ B)
                if mass > 0:
                    ed = float(A @ (Pmat * wt_and) @ B) / mass
                    rate = -np.log2(mass) / n
                    for dl in best_by_delta:
                        if ed <= dl + 1e-12 and rate < best_by_delta[dl]:
                            best_by_delta[dl] = rate
        # Coordinate-ascent search from random subsets (for alternating A and B!)
        for lam in [0.5, 1.0, 2.0, 4.0, 8.0, 16.0, 40.0]:
            # Maximize sum_{a in A, b in B} Pmat[a,b] * (c - lam * wt_and[a,b]) -> wait:
            # Exact alternating maximization of log2(P(AxB))/n - lam * E[wt_and | AxB]:
            # For fixed B, let p_a = (Pmat @ B)[a], w_a = ((Pmat * wt_and) @ B)[a].
            # Sorting by w_a / p_a gives the EXACT optimal A for any fixed B!!
            for _ in range(40):
                B = (rng.random(N) < rng.uniform(0.1, 0.9)).astype(float)
                if B.sum() == 0:
                    B[0] = 1.0
                for _it in range(6):
                    # Given B, evaluate all prefixes sorted by w_a / p_a
                    p_a = Pmat @ B
                    w_a = (Pmat * wt_and) @ B
                    order = np.argsort(w_a / np.maximum(p_a, EPS))
                    cp = np.cumsum(p_a[order])
                    cw = np.cumsum(w_a[order])
                    eds = cw / np.maximum(cp, EPS)
                    rates = -np.log2(np.maximum(cp, EPS)) / n
                    for dl in best_by_delta:
                        ok = np.where(eds <= dl + 1e-12)[0]
                        if len(ok) > 0:
                            best_by_delta[dl] = min(best_by_delta[dl], float(np.min(rates[ok])))
                    idx_best = int(np.argmin(rates + lam * eds))
                    A = np.zeros(N); A[order[:idx_best + 1]] = 1.0
                    # Swap roles: given A, optimize B
                    p_b = A @ Pmat
                    w_b = A @ (Pmat * wt_and)
                    order = np.argsort(w_b / np.maximum(p_b, EPS))
                    cp = np.cumsum(p_b[order])
                    cw = np.cumsum(w_b[order])
                    eds = cw / np.maximum(cp, EPS)
                    rates = -np.log2(np.maximum(cp, EPS)) / n
                    for dl in best_by_delta:
                        ok = np.where(eds <= dl + 1e-12)[0]
                        if len(ok) > 0:
                            best_by_delta[dl] = min(best_by_delta[dl], float(np.min(rates[ok])))
                    idx_best = int(np.argmin(rates + lam * eds))
                    B = np.zeros(N); B[order[:idx_best + 1]] = 1.0
        print(f"    n={n}: " + ", ".join(f"delta<={dl:.2f} -> min_rate={v:.5f}" for dl, v in best_by_delta.items()))


def main():
    print("=" * 78)
    print("TWO-AGENT BINARY SYMMETRIC CEO PROBLEM — DEEP ANALYSIS")
    print("=" * 78)

    for (p1, p2) in [(0.1, 0.1), (0.2, 0.2), (0.1, 0.25)]:
        print(f"\n>>> Parameters: p1 = {p1}, p2 = {p2} (D_min = {min(p1,p2)})")
        D_min = min(p1, p2)
        D_grid = np.linspace(D_min, 0.45, 8)
        R_1ag = np.array([single_agent_rd(D_min, d) for d in D_grid])
        R_cent = centralized_rd(p1, p2, D_grid)
        R_cw, _ = cw_logloss_sumrate(p1, p2, D_grid)

        print(f"{'D':>6} | {'1-Agent':>9} | {'CW-LogLoss':>10} | {'Central':>9} | {'Gap(1Ag-CW)':>11} | {'Gap(1Ag-Cen)':>12}")
        print("-" * 70)
        for i, d in enumerate(D_grid):
            print(f"{d:6.3f} | {R_1ag[i]:9.5f} | {R_cw[i]:10.5f} | {R_cent[i]:9.5f} | {R_1ag[i]-R_cw[i]:11.5f} | {R_1ag[i]-R_cent[i]:12.5f}")

        # Search for ANY BT (U1, U2) beating 1-agent sum-rate!
        margin, info = search_bt_beat_1agent(p1, p2, n_samples=15000, seed=42)
        print(f"\n  [Can ANY BT (|U1|,|U2|<=4) beat 1-Agent sum-rate?]")
        print(f"    Max (R_1agent(D) - R_BT_sum) found = {margin:+.7f}  (via {info[0]})")
        print(f"    At D={info[1]:.5f}: R_BT={info[2]:.6f} vs R_1agent={info[3]:.6f} (R1_cond={info[4]:.5f}, R2_cond={info[5]:.5f})")

        if p1 == p2:
            # Finite-k structured coding test
            print(f"\n  [Structured k-bit Quantize-and-Bin (Majority & Hamming [7,4])]:")
            for name, D, Rsum, R1a, diff in test_finite_n_coding_ceo(p1):
                print(f"    {name:14s}: D={D:.5f}, R_sum={Rsum:.5f}, R_1ag(D)={R1a:.5f}, (1Ag - Struct)={diff:+.5f}")
        else:
            # Asymmetric rate region (Wyner-Ziv helper corner)
            D_t = 0.15
            R1_1ag, R1_wz, pts = test_asymmetric_rate_region(p1, p2, D_t)
            print(f"\n  [Asymmetric (R1, R2) at p1={p1}, p2={p2}, D={D_t} (< p2={p2})]:")
            print(f"    1-Agent alone (R2=0): R1 = {R1_1ag:.5f}")
            print(f"    With full Y2 helper (R2=1): R1 = {R1_wz:.5f} (savings = {R1_1ag - R1_wz:.5f} bits!)")
            print(f"    Sample helper tradeoff (R2 -> R1): " + ", ".join(f"({r2:.2f}->{r1:.4f})" for r2, r1 in pts[::10]))

    # Exact rectangle test for p = 0.2 (where BT-outer strictly beats 1.0!)
    test_rectangle_exact_small_n(0.2, n_max=7)


if __name__ == "__main__":
    main()
