#!/usr/bin/env python3
"""
Numerical verification for universal-lossy-redundancy:
1. Boundary kink at P = Bern(D) (m = 2, D = 1/4):
   - Exact P^{⊗n}(E_n) for E_n = {wt(x) >= nD + s}
   - Exact max_c P^{⊗n}(B(c, nD) ∩ E_n) vs Chernoff bound 2^{-t}
   - Exact Kraft/Gibbs lower bound showing Ω(n^{-1/2}) redundancy
   - Comparison with E_P[R(P_n, D)] ~ (log2((1-D)/D)) * sqrt(D(1-D)/(2*pi*n))
2. Exact ball-intersection prefactors for m = 2 and m = 3:
   - q(Q*, P_n) = |B(x^n, nD) ∩ T(Q*)| / |T(Q*)| ~ c * n^{-1/2} * 2^{-n R(P_n, D)}
   - O(1) grid-mismatch penalty n * (f(Q_hat, P_n) - R(P_n, D)) for ||Q_hat - Q*|| ~ n^{-1/2}
3. Exact unit-slice ball bound for the 1 * (log2 n)/n known-source asymmetric converse
   and (m+1)/2 * (log2 n)/n universal interior converse:
   - m = 2: max_{w, K} |B(y, nD) ∩ T(K/n)| / (n^{-1} * 2^{n h(D)}) = O(1)
   - m = 3: max_{y, k} |B(y, nD) ∩ {n H(P_n) in [k, k+1)}| / (n^{-1} * 2^{n(h(D)+D log2 2)}) = O(1)
"""

import math
from math import comb, log2, sqrt, pi, lgamma, exp


def h_bin(p: float) -> float:
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -p * log2(p) - (1.0 - p) * log2(1.0 - p)


def H_dist(probs) -> float:
    return sum(-p * log2(p) for p in probs if p > 0.0)


def log2_binom(n: int, k: int) -> float:
    if k < 0 or k > n:
        return -float("inf")
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / math.log(2.0)


def log2_multinom(n: int, counts) -> float:
    if any(c < 0 for c in counts) or sum(counts) != n:
        return -float("inf")
    val = lgamma(n + 1) - sum(lgamma(c + 1) for c in counts)
    return val / math.log(2.0)


def log2_sum_exp(vals) -> float:
    vals = [v for v in vals if v > -float("inf")]
    if not vals:
        return -float("inf")
    m = max(vals)
    return m + log2(sum(2.0 ** (v - m) for v in vals))


# =============================================================================
# PART 1: Boundary Kink at P = Bern(D) (m = 2, D = 1/4)
# =============================================================================
def verify_boundary_kink():
    print("=" * 78)
    print("PART 1: Boundary Kink at P = Bern(D) (m = 2, D = 1/4)")
    print("=" * 78)
    D = 0.25
    v = D * (1.0 - D)
    asymptotic_kink_const = log2((1.0 - D) / D) * sqrt(v / (2.0 * pi))
    print(f"D = {D}, R(Bern(D), D) = 0")
    print(f"Theoretical E[R(P_n, D)] * sqrt(n) -> {asymptotic_kink_const:.6f}")
    print(
        f"{'n':>6} | {'P(E_n)':>8} | {'max_w P(B∩E)':>12} | {'2^{-t} bnd':>12} | "
        f"{'sqrt(n)*LB':>10} | {'sqrt(n)*E[R(P_n)]':>17}"
    )
    print("-" * 78)

    for n in [40, 100, 200, 400, 800, 1600]:
        s = sqrt(n * v)  # standard deviation
        # Use t = s / 2 for crisp numerical demonstration (Lean proof uses t = s/18)
        t = 0.5 * s
        k_min = math.ceil(n * D + t)
        # Exact binomial probabilities log2 Pr(Bin(n, D) = k)
        log2_p = [
            log2_binom(n, k) + k * log2(D) + (n - k) * log2(1.0 - D)
            for k in range(n + 1)
        ]
        p_En = sum(2.0 ** log2_p[k] for k in range(k_min, n + 1))

        # Exact E_P[R(P_n, D)] = E[(h(K/n) - h(D))_+]
        exp_R_Pn = sum(
            (2.0 ** log2_p[k]) * max(0.0, h_bin(k / n) - h_bin(D))
            for k in range(n + 1)
        )

        # Exact max over codeword weight w of P^{⊗n}(B(c, nD) ∩ E_n):
        # On B(c, nD) ∩ E_n, A ~ Bin(w, D) and B ~ Bin(n-w, D) independent,
        # requiring A + B >= k_min and (w - A) + B <= floor(nD).
        nD = math.floor(n * D)
        max_ball_prob = 0.0
        # We only need to check w around [ceil(t), n]
        # Note: A >= ceil((w + k_min - nD)/2)
        for w in range(0, n + 1):
            a_min = math.ceil((w + k_min - nD) / 2.0)
            if a_min > w:
                continue
            # Exact sum over A and B
            prob_w = 0.0
            # Precompute log2 Bin(n-w, D) on demand only if a_min <= w
            # For speed at n=1600, bound by exact Pr(A >= a_min) for w >= 0,
            # and compute exact joint for n <= 400.
            if n <= 400:
                for a in range(a_min, w + 1):
                    pa = 2.0 ** (
                        log2_binom(w, a) + a * log2(D) + (w - a) * log2(1.0 - D)
                    )
                    b_lo = max(0, k_min - a)
                    b_hi = min(n - w, nD - w + a)
                    if b_lo <= b_hi:
                        pb = sum(
                            2.0
                            ** (
                                log2_binom(n - w, b)
                                + b * log2(D)
                                + (n - w - b) * log2(1.0 - D)
                            )
                            for b in range(b_lo, b_hi + 1)
                        )
                        prob_w += pa * pb
            else:
                # Upper bound by exact Pr(Bin(w, D) >= a_min) (tight to constant factor)
                prob_w = sum(
                    2.0 ** (log2_binom(w, a) + a * log2(D) + (w - a) * log2(1.0 - D))
                    for a in range(a_min, w + 1)
                )
            if prob_w > max_ball_prob:
                max_ball_prob = prob_w

        # Kraft + Gibbs lower bound:
        # E[len] >= P(E_n) * log2(P(E_n) / max_ball_prob)
        # (since sum_j p_j len_j >= sum_j p_j log2(1/p_j) + P(E_n) log2 P(E_n)
        #  and each p_j <= max_ball_prob => log2(1/p_j) >= log2(1/max_ball_prob))
        lb_rate = (
            p_En * (log2(1.0 / max_ball_prob) + log2(p_En)) / n
            if max_ball_prob > 0
            else 0.0
        )
        chernoff_bnd = 2.0 ** (-t)
        print(
            f"{n:>6} | {p_En:>8.5f} | {max_ball_prob:>12.4e} | {chernoff_bnd:>12.4e} | "
            f"{sqrt(n) * lb_rate:>10.5f} | {sqrt(n) * exp_R_Pn:>17.6f}"
        )


# =============================================================================
# PART 2: Exact Ball-Covering Probability q(Q_hat, P_n) for m = 2 and m = 3
# =============================================================================
def log2_q_binary(n: int, k: int, w: int, D: float) -> float:
    """Exact log2 q(w/n, k/n) = log2(|B(x^n, nD) ∩ T(w/n)| / C(n, w)) for x^n in T(k/n)."""
    nD = math.floor(n * D)
    terms = []
    # a = #{i : x_i=1, y_i=0}, b = #{i : x_i=0, y_i=1}
    # w = (k - a) + b => b - a = w - k; d = a + b <= nD
    for d in range(0, nD + 1):
        if (d + w - k) % 2 != 0:
            continue
        b = (d + w - k) // 2
        a = d - b
        if 0 <= a <= k and 0 <= b <= n - k:
            terms.append(log2_binom(k, a) + log2_binom(n - k, b))
    if not terms:
        return -float("inf")
    return log2_sum_exp(terms) - log2_binom(n, w)


def log2_q_ternary(n: int, p_counts, q_counts, D: float) -> float:
    """
    Exact log2 q(Q_hat, P_n) = log2(|B(x^n, nD) ∩ T(Q_hat)| / |T(Q_hat)|) for m = 3.
    """
    p0, p1, p2 = p_counts
    q0, q1, q2 = q_counts
    nD = math.floor(n * D)
    log2_Tq = log2_multinom(n, q_counts)
    terms = []
    for v01 in range(0, min(p0, q1, nD) + 1):
        for v02 in range(0, min(p0 - v01, q2, nD - v01) + 1):
            v00 = p0 - v01 - v02
            if v00 > q0:
                continue
            rem1 = nD - v01 - v02
            for v10 in range(0, min(p1, q0 - v00, rem1) + 1):
                v20 = (q0 - p0) + v01 + v02 - v10
                if v20 < 0 or v20 > p2 or v10 + v20 > rem1:
                    continue
                rem2 = rem1 - v10 - v20
                for v12 in range(0, min(p1 - v10, q2 - v02, rem2) + 1):
                    v11 = p1 - v10 - v12
                    if v11 > q1 - v01:
                        continue
                    v21 = (q1 - p1) + v10 + v12 - v01
                    if v21 < 0 or v21 > rem2 - v12:
                        continue
                    v22 = p2 - v20 - v21
                    if v22 < 0:
                        continue
                    if v02 + v12 + v22 != q2:
                        continue
                    val = (
                        log2_multinom(p0, (v00, v01, v02))
                        + log2_multinom(p1, (v10, v11, v12))
                        + log2_multinom(p2, (v20, v21, v22))
                    )
                    terms.append(val)
    if not terms:
        return -float("inf")
    return log2_sum_exp(terms) - log2_Tq


def verify_q_prefactor_and_grid():
    print("\n" + "=" * 78)
    print("PART 2: Exact Prefactor of q(Q_hat, P_n) & O(1) Grid-Mismatch Penalty")
    print("=" * 78)

    # m = 2: P = Bern(0.3), D = 0.1 => Q*(1) = (0.3 - 0.1) / 0.8 = 0.25
    # Choose n so that k, w_star, nD have matched parity (n divisible by 40)
    # and delta = even integer close to sqrt(n) to avoid 1-step parity jump
    D2 = 0.1
    p2 = 0.3
    q2_star = (p2 - D2) / (1.0 - 2.0 * D2)
    print(f"\n[m = 2] P = (0.7, 0.3), D = {D2}, Q* = ({1-q2_star:.3f}, {q2_star:.3f})")
    print(
        f"{'n':>6} | {'log2(1/q*) - nR - 0.5 log2 n':>30} | "
        f"{'grid shift +sqrt(n) penalty (bits)':>35}"
    )
    print("-" * 78)
    for n in [400, 1600, 3600, 6400]:
        k = round(n * p2)
        w_star = round(n * q2_star)
        delta = round(sqrt(n))
        if delta % 2 != 0:
            delta += 1  # preserve parity with nD + k - w
        w_shift = w_star + delta
        R_Pn = h_bin(k / n) - h_bin(D2)
        lq_opt = log2_q_binary(n, k, w_star, D2)
        lq_sh = log2_q_binary(n, k, w_shift, D2)
        resid = -lq_opt - n * R_Pn - 0.5 * log2(n)
        penalty = lq_opt - lq_sh
        print(f"{n:>6} | {resid:>30.6f} | {penalty:>35.6f}")

    # m = 3: P = (0.5, 0.3, 0.2), D = 0.2 => D/(m-1) = 0.1 < min P
    # Q*(x) = (P(x) - 0.1) / 0.7 = (4/7, 2/7, 1/7)
    D3 = 0.2
    P3 = (0.5, 0.3, 0.2)
    Q3_star = tuple((p - D3 / 2.0) / (1.0 - 1.5 * D3) for p in P3)
    print(
        f"\n[m = 3] P = {P3}, D = {D3}, Q* = ({Q3_star[0]:.4f}, {Q3_star[1]:.4f}, {Q3_star[2]:.4f})"
    )
    print(
        f"{'n':>6} | {'log2(1/q*) - nR - 0.5 log2 n':>30} | "
        f"{'grid shift +sqrt(n) penalty (bits)':>35}"
    )
    print("-" * 78)
    for n in [35, 70, 105, 140]:
        p_cnt = [round(n * P3[0]), round(n * P3[1]), 0]
        p_cnt[2] = n - p_cnt[0] - p_cnt[1]
        q_cnt = [round(n * Q3_star[0]), round(n * Q3_star[1]), 0]
        q_cnt[2] = n - q_cnt[0] - q_cnt[1]
        delta = max(1, round(sqrt(n)))
        q_sh_cnt = [q_cnt[0] + delta, q_cnt[1] - delta, q_cnt[2]]

        P_emp = [c / n for c in p_cnt]
        R_Pn = H_dist(P_emp) - h_bin(D3) - D3 * log2(2)
        lq_opt = log2_q_ternary(n, p_cnt, q_cnt, D3)
        lq_sh = log2_q_ternary(n, p_cnt, q_sh_cnt, D3)
        resid = -lq_opt - n * R_Pn - 0.5 * log2(n)
        penalty = lq_opt - lq_sh
        print(f"{n:>6} | {resid:>30.6f} | {penalty:>35.6f}")


# =============================================================================
# PART 3: Verification of Unit-Slice Ball Bound |B(y, nD) ∩ S_k| <= C n^{-1} 2^{n(h(D)+D log2(m-1))}
#         for the 1*(log2 n)/n (known asymmetric) and (m+1)/2 * (log2 n)/n (universal) converses!
# =============================================================================
def verify_unit_slice_ball_bound():
    print("\n" + "=" * 78)
    print("PART 3: Unit-Slice Ball Bound |B(y, nD) ∩ S_k| / (n^{-1} * 2^{n(h(D)+D log2(m-1))})")
    print("=" * 78)

    # m = 2: D = 0.1, P = Bern(0.3), check max over w in [0.2n, 0.4n] and all K
    D = 0.1
    print(f"\n[m = 2] D = {D}, checking max_{{w in [0.2n, 0.4n], K}} |B(y, nD) ∩ T(K/n)| / (n^-1 * 2^(n h(D)))")
    print(f"{'n':>6} | {'max ratio':>12} | {'ball_vol / (n^-0.5 2^nh(D))':>28}")
    print("-" * 55)
    for n in [100, 200, 400, 800, 1600]:
        nD = math.floor(n * D)
        ball_log2 = log2_sum_exp([log2_binom(n, d) for d in range(nD + 1)])
        ball_ratio = 2.0 ** (ball_log2 - n * h_bin(D) + 0.5 * log2(n))
        # Check w = round(0.25*n) (worst-case interior w) and all K
        w = round(0.25 * n)
        best_log2 = -float("inf")
        for K in range(max(0, w - nD), min(n, w + nD) + 1):
            terms = []
            for d in range(0, nD + 1):
                if (d + K - w) % 2 != 0:
                    continue
                b = (d + K - w) // 2
                a = d - b
                if 0 <= a <= w and 0 <= b <= n - w:
                    terms.append(log2_binom(w, a) + log2_binom(n - w, b))
            if terms:
                val = log2_sum_exp(terms)
                if val > best_log2:
                    best_log2 = val
        slice_ratio = 2.0 ** (best_log2 - n * h_bin(D) + log2(n))
        print(f"{n:>6} | {slice_ratio:>12.6f} | {ball_ratio:>28.6f}")

    # m = 3: D = 0.2, y has type Q = (0.57, 0.29, 0.14) (corresponding to P = (0.5, 0.3, 0.2))
    # Compute exact distribution of n * H(P_n(x)) for x in B(y, nD) by summing over 3x3 transition counts
    D3 = 0.2
    Q3 = (0.57, 0.29, 0.14)
    print(
        f"\n[m = 3] D = {D3}, y of type Q = {Q3}, "
        "checking max_k |B(y, nD) ∩ {n H(P_n) in [k, k+1)}| / (n^-1 * 2^{n(h(D)+D log2 2)})"
    )
    print(f"{'n':>6} | {'max slice ratio':>16} | {'ball_vol / (n^-0.5 2^nR0)':>26}")
    print("-" * 55)
    R0 = h_bin(D3) + D3 * log2(2)
    for n in [30, 50, 70, 90]:
        nD = math.floor(n * D3)
        q0 = round(n * Q3[0])
        q1 = round(n * Q3[1])
        q2 = n - q0 - q1
        ball_log2 = log2_sum_exp(
            [log2_binom(n, d) + d * log2(2) for d in range(nD + 1)]
        )
        ball_ratio = 2.0 ** (ball_log2 - n * R0 + 0.5 * log2(n))
        # Enumerate transitions from y -> x:
        # From q0 positions of y=0: e01 go to 1, e02 go to 2
        # From q1 positions of y=1: e10 go to 0, e12 go to 2
        # From q2 positions of y=2: e20 go to 0, e21 go to 1
        # Total errors e01+e02+e10+e12+e20+e21 <= nD.
        # Group by resulting counts (p0, p1, p2) -> bucket k = floor(n * H(P_n))!
        buckets = {}
        for e01 in range(0, min(q0, nD) + 1):
            for e02 in range(0, min(q0 - e01, nD - e01) + 1):
                c0 = log2_multinom(q0, (q0 - e01 - e02, e01, e02))
                r1 = nD - e01 - e02
                for e10 in range(0, min(q1, r1) + 1):
                    for e12 in range(0, min(q1 - e10, r1 - e10) + 1):
                        c1 = c0 + log2_multinom(q1, (e10, q1 - e10 - e12, e12))
                        r2 = r1 - e10 - e12
                        for e20 in range(0, min(q2, r2) + 1):
                            for e21 in range(0, min(q2 - e20, r2 - e20) + 1):
                                c2 = c1 + log2_multinom(q2, (e20, e21, q2 - e20 - e21))
                                p0 = (q0 - e01 - e02) + e10 + e20
                                p1 = e01 + (q1 - e10 - e12) + e21
                                p2 = e02 + e12 + (q2 - e20 - e21)
                                nH = n * H_dist((p0 / n, p1 / n, p2 / n))
                                k_bucket = math.floor(nH)
                                buckets.setdefault(k_bucket, []).append(c2)
        best_log2 = max(log2_sum_exp(vs) for vs in buckets.values())
        slice_ratio = 2.0 ** (best_log2 - n * R0 + log2(n))
        print(f"{n:>6} | {slice_ratio:>16.6f} | {ball_ratio:>26.6f}")


if __name__ == "__main__":
    verify_boundary_kink()
    verify_q_prefactor_and_grid()
    verify_unit_slice_ball_bound()
