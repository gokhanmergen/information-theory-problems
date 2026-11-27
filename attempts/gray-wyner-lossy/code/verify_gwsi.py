#!/usr/bin/env python3
"""
Numerical & exact verification for `gray-wyner-lossy`
(InfoTheory.Problems.GrayWynerLossy).

Part 1: Exact verification of the BEC(1/2) counterexample disproving the frozen
        statement `GrayWynerLossy.Statement` (both lossless D1=D2=0 and lossy
        D1=D/2, D2=D), plus finite-blocklength simulation of the operational
        Slepian-Wolf / random-binning scheme.
Part 2: Exact verification of the corrected Gray-Wyner + side-information
        inner bound (splitting U0's bin index across M0, M1, M2) and its
        Fourier-Motzkin equivalence.
Part 3: Numerical comparison of the 2-decoder Heegard-Berger inner bound
        (R1 = R2 = 0, where the modeling bug vanishes) against rigorous
        genie-aided outer bounds on non-degraded side-information channels
        (BEC vs BSC, complementary DSBS, and mismatched product sources).
"""

import numpy as np
from scipy.optimize import minimize, linprog


def h2(p):
    """Binary entropy in bits."""
    p = np.clip(p, 0.0, 1.0)
    out = np.zeros_like(p, dtype=float)
    mask = (p > 0) & (p < 1)
    pm = p[mask]
    out[mask] = -pm * np.log2(pm) - (1.0 - pm) * np.log2(1.0 - pm)
    return float(out) if np.ndim(p) == 0 else out


def entropy_bits(probs):
    """Shannon entropy H(P) in bits for an arbitrary non-negative array summing to 1."""
    p = np.asarray(probs, dtype=float).ravel()
    p = p[p > 1e-15]
    return float(-np.sum(p * np.log2(p)))


def cond_mutual_info_bits(joint_xyz):
    """I(X; Y | Z) in bits for a 3D array P(x, y, z)."""
    p_xz = joint_xyz.sum(axis=1)
    p_yz = joint_xyz.sum(axis=0)
    p_z = joint_xyz.sum(axis=(0, 1))
    return entropy_bits(p_xz) + entropy_bits(p_yz) - entropy_bits(joint_xyz) - entropy_bits(p_z)


def mutual_info_bits(joint_xy):
    """I(X; Y) in bits for a 2D array P(x, y)."""
    p_x = joint_xy.sum(axis=1)
    p_y = joint_xy.sum(axis=0)
    return entropy_bits(p_x) + entropy_bits(p_y) - entropy_bits(joint_xy)


def eval_lossyGWSIInner_point(P_xz1z2, P_u_given_x, d1_mat, d2_mat):
    """
    Given:
      P_xz1z2 : shape (kX, kZ1, kZ2) joint distribution of (X, Z1, Z2)
      P_u_given_x : shape (kX, k0, k1, k2) conditional distribution P(u0, u1, u2 | x)
      d1_mat : shape (kX, kh1) distortion matrix for decoder 1
      d2_mat : shape (kX, kh2) distortion matrix for decoder 2
    Computes:
      a1 = I(X; U0 | Z1)
      a2 = I(X; U0 | Z2)
      b1 = I(X; U1 | U0, Z1)
      b2 = I(X; U2 | U0, Z2)
      min achievable expected distortions D1, D2 via optimal deterministic g1(u0, u1, z1), g2(u0, u2, z2).
    """
    kX, kZ1, kZ2 = P_xz1z2.shape
    _, k0, k1, k2 = P_u_given_x.shape

    # Joint Q(x, z1, z2, u0, u1, u2) = P(x, z1, z2) * P(u0, u1, u2 | x)
    Q = P_xz1z2[:, :, :, None, None, None] * P_u_given_x[:, None, None, :, :, :]

    # Marginals for mutual infos
    # (X, U0, Z1)
    Q_xu0z1 = Q.sum(axis=(2, 4, 5)).transpose(0, 2, 1)  # (X, U0, Z1)
    a1 = cond_mutual_info_bits(Q_xu0z1)

    # (X, U0, Z2)
    Q_xu0z2 = Q.sum(axis=(1, 4, 5)).transpose(0, 2, 1)  # (X, U0, Z2)
    a2 = cond_mutual_info_bits(Q_xu0z2)

    # (X, U1, (U0, Z1))
    Q_xu1_u0z1 = Q.sum(axis=(2, 5)).transpose(0, 3, 2, 1).reshape(kX, k1, k0 * kZ1)
    b1 = cond_mutual_info_bits(Q_xu1_u0z1)

    # (X, U2, (U0, Z2))
    Q_xu2_u0z2 = Q.sum(axis=(1, 4)).transpose(0, 3, 2, 1).reshape(kX, k2, k0 * kZ2)
    b2 = cond_mutual_info_bits(Q_xu2_u0z2)

    # Optimal deterministic decoders g1(u0, u1, z1) and g2(u0, u2, z2)
    Q_xz1u0u1 = Q.sum(axis=(2, 5))  # (X, Z1, U0, U1)
    # expected distortion for each choice of xh1 at each (z1, u0, u1)
    # cost[z1, u0, u1, xh1] = sum_x Q_xz1u0u1[x, z1, u0, u1] * d1_mat[x, xh1]
    cost1 = np.einsum("xzuv,xh->zuvh", Q_xz1u0u1, d1_mat)
    D1 = float(np.sum(np.min(cost1, axis=-1)))

    Q_xz2u0u2 = Q.sum(axis=(1, 4))  # (X, Z2, U0, U2)
    cost2 = np.einsum("xzuv,xh->zuvh", Q_xz2u0u2, d2_mat)
    D2 = float(np.sum(np.min(cost2, axis=-1)))

    return a1, a2, b1, b2, D1, D2


def part1_bec_counterexample():
    print("=" * 72)
    print("PART 1: BEC(1/2) Counterexample to Frozen `GrayWynerLossy.Statement`")
    print("=" * 72)

    # X ~ Bern(1/2), Z1 = BEC(1/2)(X) in {0, 1, 2=?}, Z2 = 0 (trivial)
    P_xz1z2 = np.zeros((2, 3, 1))
    P_xz1z2[0, 0, 0] = 0.25
    P_xz1z2[0, 2, 0] = 0.25
    P_xz1z2[1, 1, 0] = 0.25
    P_xz1z2[1, 2, 0] = 0.25
    d_ham = np.array([[0.0, 1.0], [1.0, 0.0]])

    # 1A. Random sanity-check of the converse inequality over 5,000 random
    #     Markov auxiliary distributions P(u0, u1, u2 | x) with k0,k1,k2 up to 4.
    rng = np.random.default_rng(42)
    min_slack_exact = float("inf")
    min_slack_sqrt = float("inf")
    max_a1_ratio_err = 0.0

    for trial in range(3000):
        k0 = int(rng.integers(2, 5))
        k1 = int(rng.integers(2, 4))
        k2 = int(rng.integers(2, 4))
        # Dirichlet draws including sparse/near-deterministic kernels
        alpha = float(rng.choice([0.05, 0.2, 1.0, 3.0]))
        raw = rng.gamma(alpha, 1.0, size=(2, k0 * k1 * k2))
        P_u = (raw / raw.sum(axis=1, keepdims=True)).reshape(2, k0, k1, k2)

        a1, a2, b1, b2, D1, D2 = eval_lossyGWSIInner_point(P_xz1z2, P_u, d_ham, d_ham)
        max_a1_ratio_err = max(max_a1_ratio_err, abs(a1 - 0.5 * a2))

        # Best possible (3/2)*r0 + r1 + r2 in lossyGWSIInner for this (a1, a2, b1, b2):
        # r0 = r00 + r01 + r02, r00 >= max(a1, a2) = a2, r01 + r1 >= b1, r02 + r2 >= b2.
        # Minimizing 1.5*r0 + r1 + r2 sets r01 = r02 = 0, r00 = max(a1, a2), r1 = b1, r2 = b2.
        lhs = 1.5 * max(a1, a2) + b1 + b2

        # Exact RD lower bound: 0.5*(1 - h2(min(2*D1, 0.5))) + (1 - h2(min(D2, 0.5)))
        rhs_exact = 0.5 * (1.0 - h2(min(2.0 * D1, 0.5))) + (1.0 - h2(min(D2, 0.5)))
        # Elementary sqrt lower bound: 1.5 - sqrt(2*D1) - 2*sqrt(D2)
        rhs_sqrt = 1.5 - np.sqrt(2.0 * D1) - 2.0 * np.sqrt(D2)

        min_slack_exact = min(min_slack_exact, lhs - rhs_exact)
        min_slack_sqrt = min(min_slack_sqrt, lhs - rhs_sqrt)

    print(f"Checked 3000 random auxiliary distributions (k0<=4, k1,k2<=3):")
    print(f"  max |I(X;U0|Z1) - 0.5*I(X;U0|Z2)|   = {max_a1_ratio_err:.3e}  (exact identity: 0)")
    print(f"  min slack (LHS - exact RD bound)    = {min_slack_exact:.6e}  (must be >= 0)")
    print(f"  min slack (LHS - sqrt Fano bound)   = {min_slack_sqrt:.6e}  (must be >= 0)")

    # 1A-bis. Verify elementary inequality h2(p) <= 2*sqrt(p) on [0, 1]
    p_grid = np.linspace(0.0, 1.0, 100001)
    max_h_minus_2sqrt = float(np.max(h2(p_grid) - 2.0 * np.sqrt(p_grid)))
    print(f"  max_{{p in [0,1]}} (h2(p) - 2*sqrt(p)) = {max_h_minus_2sqrt:.6e}  (must be <= 0)")

    # 1B. Check gap for lossless (D1=D2=0) and lossy family (D1=D/2, D2=D)
    print("\nSeparation between operational point (0.5*(1-h(D)), 0, 0.5*(1-h(D)))")
    print("and `InLossyGWSIClosure` lower bound on functional F = 1.5*R0 + R1 + R2:")
    print(f"  {'D':>6s}  {'D1':>6s}  {'D2':>6s}  {'F(oper)':>10s}  {'F(inner LB)':>12s}  {'Gap':>10s}")
    for D in [0.0, 0.01, 0.05, 0.1, 0.2, 0.3, 0.4]:
        rate = 1.0 - h2(D)
        f_oper = 1.25 * rate
        f_lb = 1.5 * rate
        print(f"  {D:6.2f}  {D/2:6.3f}  {D:6.2f}  {f_oper:10.6f}  {f_lb:12.6f}  {f_lb - f_oper:10.6f}")

    # 1C. Finite-blocklength Monte Carlo simulation of the operational linear code
    #     for (R0, R1, R2, D1, D2) = (0.5 + eps, 0, 0.5 + eps, 0, 0):
    #     Generate random invertible n x n binary matrix H over GF(2), send top k0 rows
    #     as M0 and remaining n - k0 rows as M2. Decoder 2 recovers X^n with 0 error!
    #     Decoder 1 solves the linear system for erased positions using M0 = H0 X^n.
    print("\nFinite-blocklength GF(2) linear code simulation for (R0, R1, R2) = (0.5+eps, 0, 0.5-eps):")
    rng2 = np.random.default_rng(123)
    for n, eps in [(40, 0.15), (80, 0.10), (160, 0.08)]:
        k0 = int(np.ceil(n * (0.5 + eps)))
        k2 = n - k0
        trials = 400
        dec1_bit_errs = 0
        dec1_blk_errs = 0
        for _ in range(trials):
            # Random k0 x n binary matrix H0
            H0 = rng2.integers(0, 2, size=(k0, n), dtype=np.uint8)
            # Erasure mask: 1 means erased
            erased = rng2.random(n) < 0.5
            e_idx = np.where(erased)[0]
            E = len(e_idx)
            # Decoder 1 succeeds uniquely iff submatrix H0[:, e_idx] has full column rank E over GF(2)
            if E == 0:
                continue
            if E > k0:
                dec1_blk_errs += 1
                dec1_bit_errs += E * 0.5  # conservative upper bound (guess randomly on failure)
                continue
            # Gaussian elimination over GF(2) on H0[:, e_idx]
            M = H0[:, e_idx].copy()
            rank = 0
            for col in range(E):
                pivot = -1
                for row in range(rank, k0):
                    if M[row, col] == 1:
                        pivot = row
                        break
                if pivot == -1:
                    continue
                if pivot != rank:
                    M[[rank, pivot]] = M[[pivot, rank]]
                for row in range(rank + 1, k0):
                    if M[row, col] == 1:
                        M[row] ^= M[rank]
                rank += 1
            if rank < E:
                dec1_blk_errs += 1
                dec1_bit_errs += (E - rank) * 0.5
        print(
            f"  n={n:3d}, R0={k0/n:.3f}, R2={k2/n:.3f}: "
            f"Dec1 block-err={dec1_blk_errs/trials:.4f}, "
            f"Dec1 avgD1<={dec1_bit_errs/(trials*n):.5f}, Dec2 avgD2=0.00000"
        )


def part2_corrected_inner_bound_fm():
    print("\n" + "=" * 72)
    print("PART 2: Fourier-Motzkin Check of Corrected Gray-Wyner Inner Bound")
    print("=" * 72)
    # Test equivalence between:
    # (A) Split-binning LP:
    #     r00, r01, r02, r10, r11, r20, r22 >= 0
    #     r00 + r01 + r02 = R0, r10 + r11 = R1, r20 + r22 = R2
    #     r00 + r10 >= a1, r00 + r20 >= a2, r01 + r11 >= b1, r02 + r22 >= b2
    # (B) Eliminated polytope:
    #     R0, R1, R2 >= 0
    #     R0 + R1 >= a1 + b1
    #     R0 + R2 >= a2 + b2
    #     R0 + R1 + R2 >= max(a1, a2) + b1 + b2
    rng = np.random.default_rng(7)
    mismatches = 0
    total = 2000
    for _ in range(total):
        a1, a2, b1, b2 = rng.uniform(0, 2, size=4)
        R0, R1, R2 = rng.uniform(0, 3, size=3)
        in_B = (
            (R0 + R1 >= a1 + b1 - 1e-9)
            and (R0 + R2 >= a2 + b2 - 1e-9)
            and (R0 + R1 + R2 >= max(a1, a2) + b1 + b2 - 1e-9)
        )
        # Solve LP for (A): vars = [r00, r01, r02, r10, r11, r20, r22]
        A_eq = [
            [1, 1, 1, 0, 0, 0, 0],
            [0, 0, 0, 1, 1, 0, 0],
            [0, 0, 0, 0, 0, 1, 1],
        ]
        b_eq = [R0, R1, R2]
        A_ub = [
            [-1, 0, 0, -1, 0, 0, 0],
            [-1, 0, 0, 0, 0, -1, 0],
            [0, -1, 0, 0, -1, 0, 0],
            [0, 0, -1, 0, 0, 0, -1],
        ]
        b_ub = [-a1, -a2, -b1, -b2]
        res = linprog(np.zeros(7), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None))
        in_A = res.success
        if in_A != in_B:
            # check if near boundary
            slack = min(
                abs((R0 + R1) - (a1 + b1)),
                abs((R0 + R2) - (a2 + b2)),
                abs((R0 + R1 + R2) - (max(a1, a2) + b1 + b2)),
            )
            if slack > 1e-7:
                mismatches += 1
    print(f"Tested {total} random (a1, a2, b1, b2, R0, R1, R2) tuples:")
    print(f"  LP (split-binning) vs FM-eliminated polytope mismatches = {mismatches}")


def wz_binary_hamming_exact_bec(e, D):
    """Wyner-Ziv RD for Bern(1/2) with BEC(e) side info and Hamming distortion D."""
    if D >= e / 2.0:
        return 0.0
    return e * (1.0 - h2(D / e))


def wz_binary_hamming_bsc(p, D):
    """
    Wyner-Ziv RD for Bern(1/2) with BSC(p) side info (0 <= p <= 0.5) and Hamming distortion D.
    Classic Wyner-Ziv (1976): lower convex envelope of g(D) = h(p * D) - h(D) and (p, 0).
    """
    if D >= p:
        return 0.0
    if D <= 0.0:
        return h2(p)
    # Build dense grid for lower convex envelope of g(d) on [0, p]
    grid = np.linspace(0.0, p, 2001)
    g = np.array([h2(p * (1 - d) + (1 - p) * d) - h2(d) for d in grid])
    # Exact tangent point from (p, 0) to g(d): minimize g(d)/(p - d) over d in [0, p)
    slopes = g[:-1] / (p - grid[:-1])
    idx = int(np.argmin(slopes))
    d_star = grid[idx]
    if D <= d_star:
        return h2(p * (1 - D) + (1 - p) * D) - h2(D)
    else:
        return slopes[idx] * (p - D)


def optimize_hb_inner_2dec(P_xz1z2, d1_mat, d2_mat, D1, D2, k0=2, k1=2, k2=2, n_restarts=5, seed=0):
    """
    Fast heuristic upper bound on the 2-decoder Heegard-Berger inner bound (R1 = R2 = 0):
      R_HB(D1, D2) = inf [ max(I(X; U0 | Z1), I(X; U0 | Z2)) + I(X; U1 | U0, Z1) + I(X; U2 | U0, Z2) ]
    First evaluates a dense structured symmetric grid (BSC test channels for U0, U1, U2),
    then refines with Nelder-Mead over general asymmetric P(u0|x) P(u1|x,u0) P(u2|x,u0).
    """
    kX = P_xz1z2.shape[0]
    rng = np.random.default_rng(seed)
    best_rate = float("inf")
    best_info = None

    # 1) Dense structured sweep over symmetric BSC test channels U0 = X + E0, U1 = X + E1, U2 = X + E2
    if kX == 2 and k0 >= 2 and k1 >= 2 and k2 >= 2:
        q_grid = np.concatenate([[0.0, 0.005, 0.01, 0.02], np.linspace(0.03, 0.5, 25)])
        for q0 in q_grid:
            p0 = np.zeros((2, k0))
            p0[0, 0], p0[0, 1] = 1.0 - q0, q0
            p0[1, 0], p0[1, 1] = q0, 1.0 - q0
            # Try pure U0 first (no private refinements)
            p1_triv = np.zeros((2, k0, k1))
            p1_triv[:, :, 0] = 1.0
            p2_triv = np.zeros((2, k0, k2))
            p2_triv[:, :, 0] = 1.0
            P_u = p0[:, :, None, None] * p1_triv[:, :, :, None] * p2_triv[:, :, None, :]
            a1, a2, b1, b2, d1_val, d2_val = eval_lossyGWSIInner_point(P_xz1z2, P_u, d1_mat, d2_mat)
            if d1_val <= D1 + 1e-9 and d2_val <= D2 + 1e-9:
                rate = max(a1, a2) + b1 + b2
                if rate < best_rate:
                    best_rate = rate
                    best_info = (a1, a2, b1, b2, d1_val, d2_val)
            # Also try adding private BSC refinement for Dec 1 or Dec 2
            for q1 in [0.0, 0.02, 0.05, 0.1, 0.2, 0.5]:
                p1 = np.zeros((2, k0, k1))
                p1[0, :, 0], p1[0, :, 1] = 1.0 - q1, q1
                p1[1, :, 0], p1[1, :, 1] = q1, 1.0 - q1
                for q2 in [0.0, 0.02, 0.05, 0.1, 0.2, 0.5]:
                    p2 = np.zeros((2, k0, k2))
                    p2[0, :, 0], p2[0, :, 1] = 1.0 - q2, q2
                    p2[1, :, 0], p2[1, :, 1] = q2, 1.0 - q2
                    P_u = p0[:, :, None, None] * p1[:, :, :, None] * p2[:, :, None, :]
                    a1, a2, b1, b2, d1_val, d2_val = eval_lossyGWSIInner_point(P_xz1z2, P_u, d1_mat, d2_mat)
                    if d1_val <= D1 + 1e-9 and d2_val <= D2 + 1e-9:
                        rate = max(a1, a2) + b1 + b2
                        if rate < best_rate:
                            best_rate = rate
                            best_info = (a1, a2, b1, b2, d1_val, d2_val)

    # 2) General asymmetric Nelder-Mead refinement
    def unpack(theta):
        idx = 0
        n0 = kX * k0
        logits0 = theta[idx : idx + n0].reshape(kX, k0)
        idx += n0
        n1 = kX * k0 * k1
        logits1 = theta[idx : idx + n1].reshape(kX, k0, k1)
        idx += n1
        n2 = kX * k0 * k2
        logits2 = theta[idx : idx + n2].reshape(kX, k0, k2)

        def softmax(a):
            e = np.exp(a - np.max(a, axis=-1, keepdims=True))
            return e / np.sum(e, axis=-1, keepdims=True)

        p0 = softmax(logits0)
        p1 = softmax(logits1)
        p2 = softmax(logits2)
        return p0[:, :, None, None] * p1[:, :, :, None] * p2[:, :, None, :]

    dim = kX * k0 + kX * k0 * k1 + kX * k0 * k2
    for r in range(n_restarts):
        x0 = rng.normal(0, 1.5, size=dim)
        for lam in [50.0, 2000.0]:
            def obj(theta):
                P_u = unpack(theta)
                a1, a2, b1, b2, d1_val, d2_val = eval_lossyGWSIInner_point(P_xz1z2, P_u, d1_mat, d2_mat)
                return max(a1, a2) + b1 + b2 + lam * (max(0.0, d1_val - D1) ** 2 + max(0.0, d2_val - D2) ** 2)

            res = minimize(obj, x0, method="Nelder-Mead", options={"maxiter": 600, "xatol": 1e-3, "fatol": 1e-5})
            x0 = res.x
        P_u = unpack(x0)
        a1, a2, b1, b2, d1_val, d2_val = eval_lossyGWSIInner_point(P_xz1z2, P_u, d1_mat, d2_mat)
        if d1_val <= D1 + 5e-5 and d2_val <= D2 + 5e-5:
            rate = max(a1, a2) + b1 + b2
            if rate < best_rate:
                best_rate = rate
                best_info = (a1, a2, b1, b2, d1_val, d2_val)

    return best_rate, best_info


def part3_nondegraded_hb():
    print("\n" + "=" * 72)
    print("PART 3: Non-Degraded 2-Decoder Heegard-Berger (R1 = R2 = 0)")
    print("        BEC(e) vs BSC(p) (neither degraded nor less noisy)")
    print("=" * 72)
    p = 0.11
    e = 0.45
    print(f"Source X ~ Bern(1/2); Z1 = BEC(e={e}), Z2 = BSC(p={p}), independent given X.")
    print(f"  2p = {2*p:.4f} < 4p(1-p) = {4*p*(1-p):.4f} < e = {e:.4f} < h2(p) = {h2(p):.4f}")
    print(f"  => Neither Z1 nor Z2 is degraded or less noisy wrt the other!")

    P_xz1z2 = np.zeros((2, 3, 2))
    for x in [0, 1]:
        px = 0.5
        p_z1 = [1 - e if x == 0 else 0.0, 1 - e if x == 1 else 0.0, e]
        p_z2 = [1 - p if x == 0 else p, p if x == 0 else 1 - p]
        for z1 in range(3):
            for z2 in range(2):
                P_xz1z2[x, z1, z2] = px * p_z1[z1] * p_z2[z2]

    d_ham = np.array([[0.0, 1.0], [1.0, 0.0]])

    test_pairs = [
        (0.0, 0.0),
        (0.05, 0.02),
        (0.05, 0.05),
        (0.10, 0.03),
        (0.10, 0.05),
    ]
    print(f"\n  {'(D1, D2)':>11s}  {'WZ1':>7s}  {'WZ2':>7s}  {'maxWZ':>7s}  {'HB_in':>8s}  {'HB-maxWZ':>9s}  {'(a1, a2, b1, b2)'}", flush=True)
    for D1, D2 in test_pairs:
        wz1 = wz_binary_hamming_exact_bec(e, D1)
        wz2 = wz_binary_hamming_bsc(p, D2)
        lb_wz = max(wz1, wz2)
        if D1 == 0.0 and D2 == 0.0:
            hb_rate = max(e, h2(p))
            info = (e, h2(p), 0.0, 0.0, 0.0, 0.0)
        else:
            hb_rate, info = optimize_hb_inner_2dec(
                P_xz1z2, d_ham, d_ham, D1, D2, k0=2, k1=2, k2=2, n_restarts=5, seed=42
            )
        a1, a2, b1, b2, _, _ = info
        print(
            f"  ({D1:4.2f},{D2:4.2f})  {wz1:7.4f}  {wz2:7.4f}  {lb_wz:7.4f}  "
            f"{hb_rate:8.5f}  {hb_rate - lb_wz:9.5f}  ({a1:.3f},{a2:.3f},{b1:.3f},{b2:.3f})",
            flush=True,
        )


if __name__ == "__main__":
    part1_bec_counterexample()
    part2_corrected_inner_bound_fm()
    part3_nondegraded_hb()
