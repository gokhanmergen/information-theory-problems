"""Verify the purely analytical (zero-quadrature!) explicit bounds for the
disproof of InfoTheory.Problems.CascadeRateDistortionSideInfo.Statement!

Source: X_G ~ N(0, 1), N ~ N(0, 1) indep., Y_G = X_G + N (sigma_N = 1, sigma_{X|Y}^2 = 1/2).
Auxiliary noise: W ~ N(0, 1/2) indep. of (X_G, Y_G).
Target: D_cont = 1/4, R1_cont = 1/2 bit, R2_cont = 0.5*log2(6) ~ 1.29248 bits.

All inequalities below are 100% rigorous analytical upper/lower bounds
requiring ZERO numerical integration!
"""
import math
from scipy.stats import norm


def tail_l2_bound(sigma: float, L: float) -> float:
    """Exact E[Z^2 * 1_{|Z| > L}] for Z ~ N(0, sigma^2)."""
    t = L / sigma
    return 2.0 * (sigma**2) * (t * norm.pdf(t) + norm.sf(t))


def analytical_check(Delta: float, L: float):
    """Check purely analytical proof at grid step Delta and truncation L (M = ceil(L/Delta), K = 2M + 1).
    We take delta -> 0+ for U_Delta = Q_delta(X_Delta + W), so eta_U -> 0 and continuity margin -> 0.
    """
    M = math.ceil(L / Delta)
    L_eff = M * Delta
    K = 2 * M + 1

    # Exact upper bounds on quantization L2 errors:
    # E[(Z - Q_Delta(Z))^2] <= Delta^2 / 4 + E[Z^2 * 1_{|Z| > L_eff}]
    eta_X = math.sqrt((Delta**2) / 4.0 + tail_l2_bound(1.0, L_eff))
    eta_Y = math.sqrt((Delta**2) / 4.0 + tail_l2_bound(math.sqrt(2.0), L_eff))
    # For Z_hat = 0.5*(X_Delta + W) + 0.25*Y_Delta:
    # Note |Z_hat| <= 0.5*L_eff + 0.25*L_eff + 0.5*|W| = 0.75*L_eff + 0.5*|W|,
    # so |Z_hat| > L_eff implies |W| > 0.5*L_eff!
    # And on |Z_hat| > L_eff, (|Z_hat| - L_eff)^2 <= (0.5*|W| - 0.25*L_eff)^2 <= 0.25*W^2.
    eta_Xh = math.sqrt((Delta**2) / 4.0 + 0.25 * tail_l2_bound(math.sqrt(0.5), 0.5 * L_eff))

    # Analytical upper bound on D_Delta = E[(X_Delta - Xhat_Delta)^2] (as delta -> 0):
    sqrt_D_Delta_ub = 0.5 + 0.5 * eta_X + 0.25 * eta_Y + eta_Xh
    D_Delta_ub = sqrt_D_Delta_ub ** 2

    # Analytical upper bound on R1^* = I(X_Delta; U_Delta | Y_Delta):
    norm_res_ub = (1.0 / math.sqrt(2.0)) + eta_X + 0.5 * eta_Y
    R1_ub = 0.5 * math.log2(1.0 + 2.0 * (norm_res_ub ** 2))

    # Analytical upper bound on R2^* = I(X_Delta, Y_Delta; Xhat_Delta) (as delta -> 0):
    norm_lin_ub = math.sqrt(5.0 / 8.0) + 0.5 * eta_X + 0.25 * eta_Y
    R2_ub = 0.5 * math.log2(1.0 + 8.0 * (norm_lin_ub ** 2))

    # Pullback to continuous Gaussian (as eps -> 0):
    D_G_ub = (math.sqrt(D_Delta_ub) + eta_X) ** 2

    # Lower bound on v0 = 0.5 * 2^(-2 R1^*) >= 0.5 * 2^(-2 R1_ub):
    v0_lb = 0.5 * (2.0 ** (-2.0 * R1_ub))
    slack_ub = D_G_ub - v0_lb

    # Operational converse lower bound on R2 (basic, NO EPI needed!):
    R2_conv_basic = 0.5 * math.log2((v0_lb ** 2) / (1.0 * slack_ub))
    # EPI-sharpened:
    R2_conv_epi = R2_conv_basic + 0.5 * math.log2(1.0 + 2.0 ** (-2.0 * R1_ub))

    return {
        "Delta": Delta, "L": L_eff, "K": K,
        "eta_X": eta_X, "eta_Y": eta_Y, "eta_Xh": eta_Xh,
        "D_Delta_ub": D_Delta_ub, "D_G_ub": D_G_ub,
        "R1_ub": R1_ub, "v0_lb": v0_lb, "slack_ub": slack_ub,
        "R2_ub": R2_ub, "R2_conv_basic": R2_conv_basic, "R2_conv_epi": R2_conv_epi,
        "gap_basic": R2_conv_basic - R2_ub, "gap_epi": R2_conv_epi - R2_ub,
    }


def main():
    print("=== Purely Analytical Zero-Quadrature Proof Verification ===")
    for Delta, L in [
        (1e-2, 8.0),
        (5e-3, 9.0),
        (2e-3, 10.0),
        (1e-3, 10.0),
        (5e-4, 11.0),
        (1e-4, 12.0),
    ]:
        r = analytical_check(Delta, L)
        print(f"Delta={r['Delta']:.0e}, L={r['L']:4.1f}, K={r['K']:7d} | "
              f"R1<={r['R1_ub']:.5f}, D_G<={r['D_G_ub']:.5f}, v0>={r['v0_lb']:.5f}, slack<={r['slack_ub']:.5f} | "
              f"R2_out<={r['R2_ub']:.5f} | R2_basic>={r['R2_conv_basic']:.5f} (gap={r['gap_basic']:+.5f}) | "
              f"R2_epi>={r['R2_conv_epi']:.5f} (gap={r['gap_epi']:+.5f})")


if __name__ == "__main__":
    main()
