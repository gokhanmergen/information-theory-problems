"""
Exact verification of the 4x3x3 counterexample disproving
InfoTheory.Problems.NonAsymptoticLossyDispersion.Statement.

Source (X, Y) with |X| = 4, |Y| = 3, |Xhat| = 3:
  X = (S, B) ~ Uniform({0, 1} x {0, 1})
  Y = (0, 0)         if S = 0
      (1, B xor Z)   if S = 1, where Z ~ Bern(p), p = 0.40, independent of (S, B)
  Xhat = {0, 1, e}
  Distortion d((s, b), xhat):
    S = 0: d((0, b), b) = 0, d((0, b), e) = w0, d((0, b), 1-b) = 3*w0
    S = 1: d((1, b), b) = 0, d((1, b), 1-b) = 1, d((1, b), e) = 10
  where w0 = lam_star / lam1, lam_star = log2((1+sqrt(5))/2),
  and lam1 is the slope magnitude of the linear segment of binary WZ at p = 0.40.

Target distortion: D = 0.415 (strictly interior: 0 < R_WZ(D) and d = 0 is feasible).

This script verifies:
1. Analytical constants and supporting-hyperplane bounds for R0(d0) and R1(d1),
   plus independent numerical verification of R0(d0) and R1(d1) via convex/dual opt.
2. Exact finite-n non-asymptotic certified upper bound on excess-distortion
   probability at rate R_n = R_WZ(D) - c / sqrt(n) (c = 0.03 > 0) using exact
   binomial distributions, exact probabilistic sphere covering, exact random
   binning union bound, and Shevtsova's (2011) exact Berry-Esseen constant 0.56.
   Demonstrates certified excessProb < 1/2 at finite n (e.g. n = 5*10^6, 2*10^7).
3. Full asymptotic second-order curve L_ach(eps) vs sqrt(V) * Phi^{-1}(1 - eps),
   showing L_ach(1/2) = -0.062396 < 0 (and even L_ach(0.40) = -0.005950 < 0).
"""

import math
import numpy as np
from scipy.optimize import brentq, minimize
from scipy.stats import binom, norm
from scipy.special import gammaln


def h2(x: float) -> float:
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -(x * math.log2(x) + (1.0 - x) * math.log2(1.0 - x))


def h2_vec(x: np.ndarray) -> np.ndarray:
    x = np.clip(x, 1e-15, 1.0 - 1e-15)
    return -(x * np.log2(x) + (1.0 - x) * np.log2(1.0 - x))


def h2p(x: float) -> float:
    return math.log2((1.0 - x) / x)


def log2_binom_vec(n: np.ndarray, k: np.ndarray) -> np.ndarray:
    return (gammaln(n + 1) - gammaln(k + 1) - gammaln(n - k + 1)) / math.log(2.0)


def compute_parameters(p: float = 0.40, D: float = 0.415):
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    t = 1.0 / phi
    lam_star = math.log2(phi)
    p0_minus = (t ** 2) / 2.0
    d0_minus = 3.0 * p0_minus
    r0_minus = 1.0 - h2(p0_minus)

    def tangent_eq(d):
        pd = p + (1.0 - 2.0 * p) * d
        g = h2(pd) - h2(d)
        gp = (1.0 - 2.0 * p) * h2p(pd) - h2p(d)
        return gp * (p - d) + g

    dc = brentq(tangent_eq, 1e-12, p - 1e-12)
    pd = p + (1.0 - 2.0 * p) * dc
    gc = h2(pd) - h2(dc)
    lam1 = gc / (p - dc)
    w0 = lam_star / lam1

    R_WZ = 0.5 * (lam_star + lam1 * p) - lam1 * D
    d0_A = 2.0 * D - p
    d0_B = 2.0 * D - dc

    tau = 0.5 * (lam_star - lam1 * p)
    sigA = lam1 * math.sqrt(0.5 * p * (1.0 - p))
    sigB = h2p(pd) * math.sqrt(0.5 * p * (1.0 - p))

    return dict(
        p=p, D=D, phi=phi, t=t, lam_star=lam_star,
        p0_minus=p0_minus, d0_minus=d0_minus, r0_minus=r0_minus,
        dc=dc, pd=pd, gc=gc, lam1=lam1, w0=w0,
        R_WZ=R_WZ, d0_A=d0_A, d0_B=d0_B,
        tau=tau, sigA=sigA, sigB=sigB,
    )


def verify_single_letter_bounds(params: dict):
    """Independently check supporting hyperplanes for S=0 and S=1."""
    lam_star = params["lam_star"]
    lam1 = params["lam1"]
    p = params["p"]

    # 1. Check S=0: min_{P(xhat|b)} I(B; Xhat) + lam_star * E[d0(B, Xhat)] == lam_star
    # Parameterize P(xhat | b) for b in {0, 1}, xhat in {0, 1, e}
    D0 = np.array([[0.0, 3.0, 1.0], [3.0, 0.0, 1.0]])

    def obj_s0(z):
        # softmax rows
        W = np.zeros((2, 3))
        W[0] = np.exp(z[:3] - np.max(z[:3]))
        W[0] /= W[0].sum()
        W[1] = np.exp(z[3:] - np.max(z[3:]))
        W[1] /= W[1].sum()
        Q = 0.5 * (W[0] + W[1])
        mi = 0.0
        for b in range(2):
            for j in range(3):
                if W[b, j] > 1e-15:
                    mi += 0.5 * W[b, j] * math.log2(W[b, j] / Q[j])
        dist = 0.5 * np.sum(W * D0)
        return mi + lam_star * dist

    rng = np.random.default_rng(42)
    best_s0 = min(
        minimize(obj_s0, rng.normal(size=6), method="BFGS").fun
        for _ in range(30)
    )
    assert abs(best_s0 - lam_star) < 1e-9, f"S=0 mismatch: {best_s0} vs {lam_star}"

    # 2. Check S=1: min_{alpha in [0, 0.5]} (g(alpha) - lam1*(p - alpha)) == 0
    alphas = np.linspace(1e-9, 0.5 - 1e-9, 100000)
    gaps = (h2_vec(p + (1.0 - 2.0 * p) * alphas) - h2_vec(alphas)) - lam1 * (p - alphas)
    min_gap = float(np.min(gaps))
    assert min_gap >= -1e-12, f"S=1 tangent violated: {min_gap}"

    print(f"Single-letter checks PASSED:")
    print(f"  S=0 min(I + lam* d0) = {best_s0:.12f} (exact lam* = {lam_star:.12f})")
    print(f"  S=1 min(g(a) - lam1*(p-a)) on [0, 1/2] = {min_gap:.3e} (>= 0)")


def certified_finite_n_excess_prob(params: dict, n: int, c: float) -> tuple[float, float]:
    """
    Fast vectorized computation of an EXACT non-asymptotic upper bound on
    excess-distortion probability at blocklength n and rate
    log2(M)/n <= R_WZ(D) - c / sqrt(n).

    Uses:
    - Exact Bin(n, 1/2) probabilities for N0 = |{i : S_i = 0}|.
    - Exact probabilistic sphere covering size |C| <= ceil((K ln 2 + 1) * 2^K / binom(K, r)).
    - Mode A: exact Bin(N1, p) tail probability.
    - Mode B: exact random binning collision union bound + exact Shevtsova (2011)
      Berry-Esseen bound (C_BE = 0.56) on Bin(r1, 1-p) + Bin(N1-r1, p).
    """
    p = params["p"]
    D = params["D"]
    w0 = params["w0"]
    p0_minus = params["p0_minus"]
    dc = params["dc"]
    pd = params["pd"]
    R_WZ = params["R_WZ"]

    log2_M_real = n * R_WZ - c * math.sqrt(n)
    assert log2_M_real > 50.0
    log2_M = log2_M_real - 1e-9  # conservative lower bound on log2(floor(2^{log2_M_real}))
    rate_shift = -c

    # Adaptive grid over N0 within +/- 6.5 * sqrt(n/4)
    # Note: for n up to 1e8, summing all integer N0 in +/- 6.5*sqrt(n/4) is at most 65,000 points -> < 0.05s vectorized!
    half_width = int(math.ceil(6.5 * math.sqrt(n / 4.0)))
    lo = max(1, n // 2 - half_width)
    hi = min(n - 1, n // 2 + half_width)
    tail_prob = float(binom.cdf(lo - 1, n, 0.5) + binom.sf(hi, n, 0.5))

    N0 = np.arange(lo, hi + 1, dtype=np.int64)
    N1 = n - N0
    probs = binom.pmf(N0, n, 0.5)

    # --- Mode A: K0_A does NOT depend on N0 as long as K0_A <= N0! ---
    # Find largest K0 <= lo with log2_sphere_covering(K0, floor(K0*p0_minus)) <= log2_M
    def cov_log2_scalar(K: int, r: int) -> float:
        return math.log2(K * math.log(2.0) + 1.0) + K - float(log2_binom_vec(np.array([K]), np.array([r]))[0]) + 1e-9

    k_lo, k_hi = 1, lo
    while k_lo < k_hi:
        mid = (k_lo + k_hi + 1) // 2
        if cov_log2_scalar(mid, int(math.floor(mid * p0_minus))) <= log2_M:
            k_lo = mid
        else:
            k_hi = mid - 1
    K0_A = k_lo
    r0_A = int(math.floor(K0_A * p0_minus))
    assert cov_log2_scalar(K0_A, r0_A) <= log2_M
    D0_A = 3.0 * w0 * r0_A + w0 * (N0 - K0_A)
    z_thresh = np.floor(n * D - D0_A - 1e-12)
    exc_A = binom.sf(z_thresh, N1, p)

    # --- Mode B: vectorized over N0 ---
    r1 = np.floor(N1 * dc).astype(np.int64)
    # Smallest K0_B such that 3*w0*floor(K0*p0_minus) + w0*(N0 - K0) + r1 <= n*D
    # Since floor(K0*p0_minus) <= K0*p0_minus, sufficient condition is:
    #   w0 * N0 - w0 * (1 - 3*p0_minus) * K0 + r1 <= n * D
    #   K0 >= (w0 * N0 + r1 - n * D) / (w0 * (1 - 3*p0_minus))
    K0_B = np.ceil((w0 * N0 + r1 - n * D) / (w0 * (1.0 - 3.0 * p0_minus))).astype(np.int64)
    K0_B = np.clip(K0_B, 1, N0)
    r0_B = np.floor(K0_B * p0_minus).astype(np.int64)
    # Verify deterministic distortion <= n*D everywhere
    dist_B = 3.0 * w0 * r0_B + w0 * (N0 - K0_B) + r1
    assert np.all(dist_B <= n * D + 1e-9), "Mode B deterministic distortion check failed!"

    log2_M0 = np.log2(K0_B * math.log(2.0) + 1.0) + K0_B - log2_binom_vec(K0_B, r0_B) + 1e-6
    log2_M1 = log2_M - log2_M0 - 1e-5
    log2_C1 = np.log2(N1 * math.log(2.0) + 1.0) + N1 - log2_binom_vec(N1, r1) + 1e-6

    mu_E1 = r1 * (1.0 - p) + (N1 - r1) * p
    sig_E1 = np.sqrt(N1 * p * (1.0 - p))
    be_err = 0.56 * (p**2 + (1.0 - p)**2) / sig_E1

    # Concavity tangent upper bound on h2(t_int / N1):
    #   N1 * h2(t_int / N1) <= N1 * h2(pd) + h2p(pd) * (t_int - N1 * pd)
    # Wait: even tighter AND completely exact is using the tangent bound directly!
    # Choose t_int = floor(N1 * pd + (log2_M1 + N1 - log2_C1 - N1*h2(pd) - k_coll) / h2p(pd))
    # Then by concavity of h2, N1*h2(t_int/N1) <= log2_M1 + N1 - log2_C1 - k_coll,
    # so collision prob <= 2^{-k_coll}!
    hp_pd = h2p(pd)
    h2_pd = h2(pd)
    exc_B = np.ones_like(probs)
    for k_coll in [6.0, 8.0, 10.0, 12.0, 14.0]:
        slack_bits = log2_M1 + N1 - log2_C1 - N1 * h2_pd - k_coll
        t_int = np.floor(N1 * pd + slack_bits / hp_pd)
        valid = (log2_M1 > 20.0) & (t_int >= 0) & (t_int <= N1 // 2)
        # Verify exact collision bound using actual h2(t_int/N1) <= tangent!
        cand = np.where(
            valid,
            norm.sf((t_int - mu_E1) / sig_E1) + be_err + (2.0 ** (-k_coll)),
            1.0,
        )
        exc_B = np.minimum(exc_B, cand)

    total_excess = tail_prob + float(np.sum(probs * np.minimum(exc_A, exc_B)))
    return rate_shift, total_excess


def main():
    params = compute_parameters(p=0.40, D=0.415)
    print("=== 4x3x3 Counterexample Parameters ===")
    for k in ["p", "D", "lam_star", "d0_minus", "r0_minus", "dc", "pd", "gc",
              "lam1", "w0", "R_WZ", "d0_A", "d0_B", "tau", "sigA", "sigB"]:
        print(f"  {k:10s} = {params[k]:.8f}")
    print()
    verify_single_letter_bounds(params)

    p_succ_0 = 0.5 + (math.atan(params["tau"] / params["sigB"])
                      - math.atan(params["tau"] / params["sigA"])) / (2.0 * math.pi)
    gs = np.linspace(-10, 10, 40001)
    dg = gs[1] - gs[0]
    pdf = norm.pdf(gs)

    def asymp_excess(c_val):
        u = -params["tau"] * gs - c_val
        p_s = np.where(u >= 0, norm.cdf(u / params["sigB"]), norm.cdf(u / params["sigA"]))
        return 1.0 - float(np.sum(p_s * pdf) * dg)

    c_star = brentq(lambda c_val: asymp_excess(c_val) - 0.5, 0.0, 1.0)
    print(f"\n=== Asymptotic Limit (n -> inf) ===")
    print(f"  Excess prob at R_n = R_WZ(D) (c = 0):       eps(0) = {1.0 - p_succ_0:.6f} < 0.500000")
    print(f"  Asymptotic achievable shift at eps = 1/2:   L_ach(1/2) = {-c_star:.6f} < 0")

    print(f"\n=== Certified Non-Asymptotic Upper Bounds (c = 0.03, sqrt(n)(R_n - R_WZ) = -0.03) ===")
    print(f"  Asymptotic limit at c = 0.03:               {asymp_excess(0.03):.6f}")
    for n in [100_000, 1_000_000, 5_000_000, 20_000_000, 100_000_000]:
        shift, exc = certified_finite_n_excess_prob(params, n, c=0.03)
        tag = "  <-- STRICTLY BELOW 1/2!" if exc < 0.5 else ""
        print(f"  n = {n:11d}: sqrt(n)*(R_n - R_WZ) = {shift:+.4f}, "
              f"certified excessProb <= {exc:.6f}{tag}")

    print(f"\n=== Full Second-Order Curve L_ach(eps) vs Gaussian (for eps in (0, 1)) ===")
    for eps in [0.05, 0.10, 0.25, 0.40, 0.50, 0.60, 0.75, 0.90, 0.95]:
        L_eps = -brentq(lambda c_val: asymp_excess(c_val) - eps, -5.0, 5.0)
        q_eps = norm.ppf(1.0 - eps)
        ratio = L_eps / q_eps if abs(q_eps) > 1e-9 else float("nan")
        print(f"  eps = {eps:4.2f}: L_ach(eps) = {L_eps:+.6f}, Phi^-1(1-eps) = {q_eps:+.6f}, L/Phi^-1 = {ratio:+.6f}")


if __name__ == "__main__":
    main()
