"""Find the smallest-K explicit finite-alphabet counterexample to
InfoTheory.Problems.CascadeRateDistortionSideInfo.Statement
and also compute the Cuff-Su-El Gamal inner vs outer bound gap on
Binary Erasure Side Information.

Uses BOTH:
1. Basic (non-EPI) continuous Gaussian operational converse:
     R2 >= 0.5 * log2( v0^2 / (sigma_N^2 * (D_G - v0)) )
   where v0 = sigma_{X|Y}^2 * 2^(-2 R1).
2. EPI-sharpened continuous Gaussian operational converse:
     R2 >= 0.5 * log2( (sigma_N^2 + 2^(-2 R1)) * v0^2 / (sigma_N^4 * (D_G - v0)) ).
3. Lloyd-Max optimal MSE quantizer for X ~ N(0, 1) to minimize eta_X!
"""
import math
import numpy as np
from scipy.stats import norm


def lloyd_max_gaussian(K: int, n_iter: int = 80):
    """Compute K-level Lloyd-Max quantizer for X ~ N(0, 1).
    Returns (edges, centroids, mse_quant_X) where:
      edges has length K+1 with edges[0]=-inf, edges[-1]=+inf,
      centroids[i] = E[X | edges[i] <= X < edges[i+1]],
      mse_quant_X = E[(X - Q(X))^2] = 1 - sum_i p_i * centroids[i]^2 (EXACT).
    """
    # Initialize with uniform grid on [-L, L]
    L = min(5.5, 1.5 + 0.7 * math.log(K))
    interior = np.linspace(-L, L, K - 1)
    edges = np.concatenate(([-np.inf], interior, [np.inf]))
    for _ in range(n_iter):
        p = np.diff(norm.cdf(edges))
        p = np.maximum(p, 1e-300)
        centroids = -np.diff(norm.pdf(edges)) / p
        new_interior = 0.5 * (centroids[:-1] + centroids[1:])
        edges = np.concatenate(([-np.inf], new_interior, [np.inf]))
    p = np.diff(norm.cdf(edges))
    centroids = -np.diff(norm.pdf(edges)) / p
    mse_quant_X = 1.0 - float(np.sum(p * centroids**2))
    return edges, centroids, mse_quant_X


def build_exact_pxy(edges_X, edges_Y, sigma_N: float, gl_order: int = 96):
    """Exact joint PMF P(X in bin_i, Y in bin_j) via high-order Gauss-Legendre."""
    K_X = len(edges_X) - 1
    K_Y = len(edges_Y) - 1
    P_XY = np.zeros((K_X, K_Y))
    gl_nodes, gl_weights = np.polynomial.legendre.leggauss(gl_order)
    for i in range(K_X):
        a = -14.0 if np.isneginf(edges_X[i]) else edges_X[i]
        b = 14.0 if np.isposinf(edges_X[i + 1]) else edges_X[i + 1]
        mid = 0.5 * (a + b)
        half = 0.5 * (b - a)
        xs = mid + half * gl_nodes
        ws = half * gl_weights * norm.pdf(xs)
        z = (edges_Y[None, :] - xs[:, None]) / sigma_N
        prob_Y = np.diff(norm.cdf(z), axis=1)
        P_XY[i, :] = ws @ prob_Y
    P_XY = np.maximum(P_XY, 0.0)
    P_XY /= P_XY.sum()
    return P_XY


def entropy_bits(p):
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > 0]
    return float(-np.sum(p * np.log2(p)))


def eval_outer_bound_exact(P_XY, x_vals, edges_U, sigma_W, xh_grid):
    """Exact evaluation of a valid witness (U, Xhat) in cascadeOuterBound.
    U - X - Y holds identically (P(U|X,Y) = P(U|X)).
    X - (U, Y) - Xhat holds identically (Xhat is a deterministic function of (U, Y)).
    """
    K_X, K_Y = P_XY.shape
    K_U = len(edges_U) - 1
    M_xh = len(xh_grid)

    z = (edges_U[None, :] - x_vals[:, None]) / sigma_W
    P_U_given_X = np.diff(norm.cdf(z), axis=1)
    P_U_given_X = np.maximum(P_U_given_X, 0.0)
    P_U_given_X /= P_U_given_X.sum(axis=1, keepdims=True)

    P_X = P_XY.sum(axis=1)
    P_Y = P_XY.sum(axis=0)
    P_YU = P_XY.T @ P_U_given_X  # (K_Y, K_U)
    P_XU = P_X[:, None] * P_U_given_X

    R1 = (entropy_bits(P_YU) - entropy_bits(P_Y)) - (entropy_bits(P_XU) - entropy_bits(P_X))

    num = (P_XY * x_vals[:, None]).T @ P_U_given_X  # (K_Y, K_U)
    post_mean = np.where(P_YU > 0, num / np.maximum(P_YU, 1e-300), 0.0)
    idx_xh = np.argmin(np.abs(post_mean[:, :, None] - xh_grid[None, None, :]), axis=2)
    xh_vals = xh_grid[idx_xh]

    D_Delta = float(
        np.sum(P_X * x_vals**2)
        - 2.0 * np.sum(num * xh_vals)
        + np.sum(P_YU * xh_vals**2)
    )

    H_Xh_given_XY = 0.0
    P_Xh = np.zeros(M_xh)
    for y in range(K_Y):
        M_xm = np.zeros((K_X, M_xh))
        np.add.at(M_xm.T, idx_xh[y], P_U_given_X.T)
        P_xm = P_XY[:, y:y+1] * M_xm
        P_Xh += P_xm.sum(axis=0)
        mask = M_xm > 0
        ent_x = -np.sum(np.where(mask, M_xm * np.log2(np.where(mask, M_xm, 1.0)), 0.0), axis=1)
        H_Xh_given_XY += float(np.sum(P_XY[:, y] * ent_x))

    R2 = entropy_bits(P_Xh) - H_Xh_given_XY
    return R1, R2, D_Delta


def operational_converse_R2(R1_bits, D_G, sigma_N):
    sigma_XY_sq = (sigma_N**2) / (1.0 + sigma_N**2)
    v0 = sigma_XY_sq * (2.0 ** (-2.0 * R1_bits))
    slack = D_G - v0
    if slack <= 0:
        return float("inf"), float("inf"), v0, slack
    R2_basic = 0.5 * math.log2((v0**2) / ((sigma_N**2) * slack))
    epi_factor = 1.0 + (2.0 ** (-2.0 * R1_bits)) / (sigma_N**2)
    R2_epi = R2_basic + 0.5 * math.log2(epi_factor)
    return R2_basic, R2_epi, v0, slack


def binary_erasure_analysis():
    """Compare cascadeOuterBound vs Cuff-Su-El Gamal inner bound on Binary Erasure Side Info:
    X ~ Bern(1/2), Y = X w.p. 1-eps, Y = e w.p. eps, Hamming distortion.
    """
    print("\n=== Binary Erasure Side Info: Outer Bound vs Cuff-Su-El Gamal Inner Bound ===")
    def h2(p):
        if p <= 0 or p >= 1:
            return 0.0
        return -p * math.log2(p) - (1 - p) * math.log2(1 - p)

    for eps, D in [(0.5, 0.125), (0.5, 0.05), (0.4, 0.1), (0.8, 0.2)]:
        d_e = D / eps  # distortion on erased bits at WZ corner
        R1_wz = eps * (1.0 - h2(d_e))
        R2_outer = 1.0 - eps * h2(d_e)
        R2_recomp = 1.0  # pure recompression (V=empty, U=X+W)
        # Pure relaying (U=empty, V=X+W): R2 = I(X;V) + I(Y;Xhat|V) = 1 - h2(d_e) + h2((1-eps)*d_e)
        R2_relay = (1.0 - h2(d_e)) + h2((1.0 - eps) * d_e)
        # Hybrid (V = U + W2 degraded version of U, where U = X + W1, W1 ~ Bern(d_e), W2 ~ Bern(alpha)):
        # P(V != X) = d_e * (1-alpha) + (1-d_e) * alpha =: q
        # I(X; V) = 1 - h2(q)
        # I(U, Y; Xhat | V) = H(Xhat | V) - H(Xhat | U, Y, V) = H(Xhat | V)
        # P(Xhat != V) = (1-eps)*P(X != V) + eps*P(U != V) = (1-eps)*q + eps*alpha
        best_hybrid = 1e9
        best_alpha = 0.0
        for alpha in np.linspace(0.0, 0.5, 501):
            q = d_e * (1.0 - alpha) + (1.0 - d_e) * alpha
            p_diff = (1.0 - eps) * q + eps * alpha
            r2_h = (1.0 - h2(q)) + h2(p_diff)
            if r2_h < best_hybrid:
                best_hybrid = r2_h
                best_alpha = alpha
        print(f"eps={eps:.2f}, D={D:.3f} (D/eps={d_e:.3f}) | R1_WZ={R1_wz:.5f} | "
              f"R2_outer={R2_outer:.5f} | R2_relay={R2_relay:.5f}, R2_recomp={R2_recomp:.5f}, "
              f"R2_hybrid={best_hybrid:.5f} (alpha={best_alpha:.3f}) | CSE_gap={best_hybrid - R2_outer:+.5f}")


def main():
    print("=== Lloyd-Max Finite-Alphabet Counterexample Search ===")
    for K in [32, 48, 64, 80, 96, 128, 200]:
        edges_X, x_vals, mse_q = lloyd_max_gaussian(K, n_iter=60)
        eta_X = math.sqrt(mse_q)
        best_basic = (-1e9, None)
        best_epi = (-1e9, None)
        for sigma_N in [0.8, 1.0, 1.2, 1.5, 1.8]:
            sigma_Y = math.sqrt(1.0 + sigma_N**2)
            edges_Y = edges_X * sigma_Y
            P_XY = build_exact_pxy(edges_X, edges_Y, sigma_N, gl_order=80)
            sigma_XY_sq = sigma_N**2 / (1.0 + sigma_N**2)
            for ratio in [0.5, 0.65, 0.72, 0.78, 0.84]:
                sigma_W = math.sqrt(sigma_XY_sq / (1.0 / ratio - 1.0))
                sigma_U = math.sqrt(1.0 + sigma_W**2)
                edges_U = edges_X * sigma_U
                # Reconstruction grid scaled to std(Xhat) = sqrt(1 - D_cont)
                D_cont = ratio * sigma_XY_sq
                xh_grid = x_vals * math.sqrt(1.0 - D_cont)
                R1, R2, D_Delta = eval_outer_bound_exact(P_XY, x_vals, edges_U, sigma_W, xh_grid)
                D_G = (math.sqrt(D_Delta) + eta_X) ** 2
                R2_b, R2_e, v0, slack = operational_converse_R2(R1, D_G, sigma_N)
                if R2_b - R2 > best_basic[0]:
                    best_basic = (R2_b - R2, (sigma_N, ratio, R1, R2, R2_b, R2_e, D_Delta, D_G, v0, eta_X))
                if R2_e - R2 > best_epi[0]:
                    best_epi = (R2_e - R2, (sigma_N, ratio, R1, R2, R2_b, R2_e, D_Delta, D_G, v0, eta_X))
        gb, tb = best_basic
        ge, te = best_epi
        print(f"K={K:3d} (eta={eta_X:.5f}) | BASIC gap={gb:+.5f} [sN={tb[0]}, rat={tb[1]}, R1={tb[2]:.4f}, R2_out={tb[3]:.4f}, R2_b={tb[4]:.4f}] "
              f"| EPI gap={ge:+.5f} [sN={te[0]}, rat={te[1]}, R1={te[2]:.4f}, R2_out={te[3]:.4f}, R2_e={te[5]:.4f}]")

    binary_erasure_analysis()


if __name__ == "__main__":
    main()
