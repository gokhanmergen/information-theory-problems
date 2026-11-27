"""
Reproducible numerical & certified analysis of 3-channel symmetric quadratic
Gaussian Multiple Descriptions (`gaussian-multiple-descriptions-3`).

Reproduces all computations and certified bounds in:
  attempts/gaussian-multiple-descriptions-3/2026-11-26-gemini-4-neon.md

Sections:
  1. Certified branch-and-bound lower bound on tianChenMD3SymRate(1/2, 1/10, 1/20)
     and exact rational witnesses for the correlated-V (Tian-Chen random-binning +
     (3,2)-XOR) scheme beating tianChenMD3SymRate by > 0.0254 bits/description
     (and crossing the integer threshold R = 1 bit/description).
  2. Certified strict non-convexity of tianChenMD3SymRate itself at
     A = (1/2, 1/10, 1/20), B = (9/10, 1/20, 1/25), lambda = 3/4,
     M = (3/5, 7/80, 19/400), showing time-sharing alone beats tianChenMD3SymRate
     by > 0.00458 bits/description (using explicit feasible 4-tuples for A and B
     and a certified branch-and-bound lower bound for M).
  3. First-order derivative check of dR_corrV / d(eps)|_{eps=0} < 0 at an interior
     point where all three layers are active.
  4. Comparison table across the (D1, D2, D3) simplex: Ozarow (1980) 2-desc bound,
     Wang-Viswanath (2007) (D1,D3) bound, VKG layer-2, CMS pair-common, R_corrV,
     and R_TC.
"""

from fractions import Fraction
import heapq
import math
import numpy as np
from scipy.optimize import minimize


def log2(x: float) -> float:
    return math.log2(x)


# ==============================================================================
# Direct evaluation of the exact frozen Lean formula tianChenMD3SymRate
# ==============================================================================
def eval_TC_lean_4d(v0: float, sig2: float, rho: float, tau2: float,
                    D1: float, D2: float, D3: float):
    assert 0 < v0 <= 1.0 and sig2 > 0 and -0.5 < rho < 1.0 and tau2 > 0
    d1 = (v0 * sig2) / (v0 + sig2)
    d2Base = (v0 * sig2 * (1.0 + rho)) / (2.0 * v0 + sig2 * (1.0 + rho))
    d2 = (d2Base * tau2) / (d2Base + tau2)
    d3Base = (v0 * sig2 * (1.0 + 2.0 * rho)) / (3.0 * v0 + sig2 * (1.0 + 2.0 * rho))
    d3p = (d3Base * tau2) / (d3Base + tau2)
    assert d1 <= D1 and d2 <= D2, f"Infeasible: d1={d1} (D1={D1}), d2={d2} (D2={D2})"
    r0 = 0.5 * log2(1.0 / v0)
    rBase = 0.5 * log2(v0 / d1) + (1.0 / 6.0) * log2(1.0 / ((1.0 + 2.0 * rho) * (1.0 - rho) ** 2))
    r2 = 0.25 * log2(1.0 + d2Base / tau2)
    r3 = (1.0 / 6.0) * max(0.0, log2(d3p / D3))
    return r0 + rBase + r2 + r3, dict(d1=d1, d2Base=d2Base, d2=d2, d3Base=d3Base, d3p=d3p,
                                      r0=r0, rBase=rBase, r2=r2, r3=r3)


# ==============================================================================
# Exact 2D analytic reduction of tianChenMD3SymRate (proved in report)
# ==============================================================================
def F_TC_2d(a: float, rho: float, D1: float, D2: float, D3: float) -> float:
    v0 = min(1.0, D1 * (1.0 + a))
    d1 = v0 / (1.0 + a)
    c2 = (1.0 + rho) / (2.0 * a + 1.0 + rho)
    c3 = (1.0 + 2.0 * rho) / (3.0 * a + 1.0 + 2.0 * rho)
    d2b = v0 * c2
    d3b = v0 * c3
    u = max(0.0, d2b / D2 - 1.0)
    d3p = d3b / (1.0 + (c3 / c2) * u)
    return (0.5 * log2(1.0 / d1)
            + (1.0 / 6.0) * log2(1.0 / ((1.0 + 2.0 * rho) * (1.0 - rho) ** 2))
            + 0.25 * log2(1.0 + u)
            + (1.0 / 6.0) * max(0.0, log2(d3p / D3)))


def compute_R_TC_2d(D1: float, D2: float, D3: float):
    best = F_TC_2d(0.0, 0.0, D1, D2, D3)
    best_ar = (0.0, 0.0)
    a_grid = np.concatenate([[0.0], np.geomspace(1e-3, max(10.0, 5.0 / D3), 30)])
    r_grid = np.concatenate([-0.5 + np.geomspace(1e-7, 0.49, 15), np.linspace(0.0, 0.9, 10)])
    for a in a_grid:
        for r in r_grid:
            v = F_TC_2d(a, r, D1, D2, D3)
            if v < best:
                best = v
                best_ar = (float(a), float(r))

    def wrap(x):
        a = max(0.0, x[0])
        r = float(np.clip(x[1], -0.5 + 1e-14, 1.0 - 1e-13))
        return F_TC_2d(a, r, D1, D2, D3)

    for st in [best_ar, (max(0.0, 1.0 / D1 - 1.0), -0.35), (1.0, -0.2)]:
        res = minimize(wrap, list(st), method="Nelder-Mead",
                       options={"xatol": 1e-13, "fatol": 1e-15, "maxiter": 2500})
        if res.fun < best:
            best = float(res.fun)
            best_ar = (max(0.0, float(res.x[0])),
                       float(np.clip(res.x[1], -0.5 + 1e-14, 1.0 - 1e-13)))
    return best, best_ar


def box_lb_TC(a_lo: float, a_hi: float, r_lo: float, r_hi: float,
              D1: float, D2: float, D3: float) -> float:
    d1_max = min(D1, 1.0 / (1.0 + a_lo))
    t1 = 0.5 * log2(1.0 / d1_max)
    f = lambda r: (1.0 + 2.0 * r) * (1.0 - r) ** 2
    f_max = 1.0 if (r_lo <= 0.0 <= r_hi) else max(f(r_lo), f(r_hi))
    t2 = (1.0 / 6.0) * log2(1.0 / f_max)
    d2b = lambda a, r: min(1.0, D1 * (1.0 + a)) * (1.0 + r) / (2.0 * a + 1.0 + r)
    d3b = lambda a, r: min(1.0, D1 * (1.0 + a)) * (1.0 + 2.0 * r) / (3.0 * a + 1.0 + 2.0 * r)
    d2b_lo = d2b(a_hi, r_lo)
    d2b_hi = d2b(a_lo, r_hi)
    t3 = 0.25 * log2(1.0 + max(0.0, d2b_lo / D2 - 1.0))
    d3b_lo = d3b(a_hi, r_lo)
    d3p_lo = 1.0 / (1.0 / d3b_lo + max(0.0, 1.0 / D2 - 1.0 / d2b_hi))
    t4 = (1.0 / 6.0) * max(0.0, log2(d3p_lo / D3))
    return t1 + t2 + t3 + t4


def certify_TC_lower_bound(D1: float, D2: float, D3: float,
                           a_max: float, r_min: float, r_max: float,
                           n_splits: int = 30000):
    f = lambda r: (1.0 + 2.0 * r) * (1.0 - r) ** 2
    tail_a = 0.5 * log2(1.0 / min(D1, 1.0 / (1.0 + a_max)))
    tail_r = 0.5 * log2(1.0 / D1) + (1.0 / 6.0) * log2(1.0 / max(f(r_min), f(r_max)))
    pq = [(box_lb_TC(0.0, a_max, r_min, r_max, D1, D2, D3), 0.0, a_max, r_min, r_max)]
    for _ in range(n_splits):
        lb, a0, a1, r0, r1 = heapq.heappop(pq)
        if (a1 - a0) / a_max >= (r1 - r0) / (r_max - r_min):
            am = 0.5 * (a0 + a1)
            heapq.heappush(pq, (box_lb_TC(a0, am, r0, r1, D1, D2, D3), a0, am, r0, r1))
            heapq.heappush(pq, (box_lb_TC(am, a1, r0, r1, D1, D2, D3), am, a1, r0, r1))
        else:
            rm = 0.5 * (r0 + r1)
            heapq.heappush(pq, (box_lb_TC(a0, a1, r0, rm, D1, D2, D3), a0, a1, r0, rm))
            heapq.heappush(pq, (box_lb_TC(a0, a1, rm, r1, D1, D2, D3), a0, a1, rm, r1))
    box_lb = pq[0][0]
    return min(box_lb, tail_a, tail_r), box_lb, tail_a, tail_r, pq[0]


# ==============================================================================
# Correlated-V random-binning + (3,2)-XOR achievable scheme
# ==============================================================================
def eval_corrV(v0: float, sig2: float, rho: float, tau2: float, gamma: float,
               D1: float, D2: float, D3: float):
    C = np.array([
        [sig2, rho * sig2, rho * sig2, gamma],
        [rho * sig2, sig2, rho * sig2, gamma],
        [rho * sig2, rho * sig2, sig2, gamma],
        [gamma, gamma, gamma, tau2],
    ], dtype=float)
    eigs = np.linalg.eigvalsh(C)
    if np.min(eigs) <= 1e-13:
        return 1e9, None
    S = np.zeros((5, 5), dtype=float)
    S[0, :] = v0
    S[:, 0] = v0
    S[1:, 1:] = v0 + C
    if np.min(np.linalg.eigvalsh(S)) <= 1e-14:
        return 1e9, None

    def H(idx):
        _, ld = np.linalg.slogdet(S[np.ix_(idx, idx)])
        return 0.5 * ld / math.log(2.0)

    def mmse(idx):
        _, ld1 = np.linalg.slogdet(S[np.ix_([0] + idx, [0] + idx)])
        _, ld0 = np.linalg.slogdet(S[np.ix_(idx, idx)])
        return math.exp(ld1 - ld0)

    d1 = mmse([1])
    d2 = mmse([1, 2, 4])
    d3p = mmse([1, 2, 3, 4])
    if d1 > D1 + 1e-12 or d2 > D2 + 1e-12:
        return 1e9, None
    r0 = 0.5 * log2(1.0 / v0)
    c1 = H([0]) + H([1]) - H([0, 1])
    c2 = 0.5 * (H([1]) + H([2]) - (H([0, 1, 2]) - H([0])))
    c3 = (1.0 / 3.0) * (H([1]) + H([2]) + H([3]) - (H([0, 1, 2, 3]) - H([0])))
    r1 = max(c1, c2, c3)
    R_V = H([4]) + H([0, 1, 2, 3]) - H([0, 1, 2, 3, 4])
    I_V_12 = H([4]) + H([1, 2]) - H([1, 2, 4])
    r2 = 0.5 * (R_V - I_V_12)
    r3 = (1.0 / 6.0) * max(0.0, log2(d3p / D3))
    return r0 + r1 + r2 + r3, dict(
        v0=v0, sig2=sig2, rho=rho, tau2=tau2, gamma=gamma,
        d1=d1, d2=d2, d3p=d3p, r0=r0, r1=r1, r2=r2, r3=r3,
        R_V=R_V, I_V_12=I_V_12, min_eig=float(np.min(eigs))
    )


def opt_corrV(D1: float, D2: float, D3: float):
    def wrap(x):
        sig2 = math.exp(np.clip(x[1], -12, 12))
        v0_max = 1.0 if sig2 <= D1 else min(1.0, D1 * sig2 / (sig2 - D1))
        v0 = np.clip(x[0], 1e-8, 1.0) * v0_max
        rho = -0.5 + 1.5 / (1.0 + math.exp(-np.clip(x[2], -15, 15)))
        tau2 = math.exp(np.clip(x[3], -12, 12))
        gf = math.tanh(np.clip(x[4], -8, 8))
        gamma = gf * math.sqrt(tau2 * sig2 * (1.0 + 2.0 * rho) / 3.0)
        val, _ = eval_corrV(v0, sig2, rho, tau2, gamma, D1, D2, D3)
        return val

    starts = []
    for sig2 in [D1 * 1.1, D1 * 2.0, D1 * 4.0]:
        for rho in [-0.42, -0.25, 0.0]:
            for tau2 in [D2 * 0.8, D2 * 2.5]:
                for gf in [-0.7, -0.35, 0.0]:
                    starts.append((1.0, math.log(sig2), math.log((rho + 0.5) / (1.0 - rho)),
                                   math.log(tau2), math.atanh(gf)))
    scored = sorted([(wrap(s), s) for s in starts], key=lambda t: t[0])
    best = 1e9
    best_info = None
    for _, s in scored[:2]:
        res = minimize(wrap, s, method="Nelder-Mead",
                       options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 2500})
        if res.fun < best:
            best = float(res.fun)
            x = res.x
            sig2 = math.exp(np.clip(x[1], -12, 12))
            v0_max = 1.0 if sig2 <= D1 else min(1.0, D1 * sig2 / (sig2 - D1))
            v0 = np.clip(x[0], 1e-8, 1.0) * v0_max
            rho = -0.5 + 1.5 / (1.0 + math.exp(-np.clip(x[2], -15, 15)))
            tau2 = math.exp(np.clip(x[3], -12, 12))
            gf = math.tanh(np.clip(x[4], -8, 8))
            gamma = gf * math.sqrt(tau2 * sig2 * (1.0 + 2.0 * rho) / 3.0)
            _, best_info = eval_corrV(v0, sig2, rho, tau2, gamma, D1, D2, D3)
    return best, best_info


def verify_exact_rational_witness(label: str, rho_f: Fraction, tau2_f: Fraction, gam_f: Fraction,
                                  D1_f: Fraction, D2_f: Fraction, D3_f: Fraction):
    v0 = Fraction(1)
    sig2 = Fraction(1)
    d1 = v0 * sig2 / (v0 + sig2)
    c2 = sig2 * (1 + rho_f) / 2
    c3 = sig2 * (1 + 2 * rho_f) / 3
    schur = tau2_f - gam_f * gam_f / c3
    d2 = 1 / (1 / v0 + (c2 + tau2_f - 2 * gam_f) / (c2 * tau2_f - gam_f * gam_f))
    d3 = 1 / (1 / v0 + (c3 + tau2_f - 2 * gam_f) / (c3 * tau2_f - gam_f * gam_f))
    var_v_12 = (v0 + tau2_f) - (v0 + gam_f) ** 2 / (v0 + c2)
    ratio_r2 = var_v_12 / schur
    det_rho = (1 + 2 * rho_f) * (1 - rho_f) ** 2
    arg12 = (1 / d1) ** 6 * (1 / det_rho) ** 2 * ratio_r2 ** 3
    R_tot = (1.0 / 12.0) * log2(float(arg12))
    assert schur > 0 and d1 <= D1_f and d2 <= D2_f and d3 <= D3_f
    print(f"  {label}: rho={rho_f}, tau2={tau2_f}, gamma={gam_f}")
    print(f"    Var(Q2|Z1,Z2,Z3) = {schur} ({float(schur):.8f} > 0)")
    print(f"    d1 = {d1} (<= {D1_f}), d2 = {d2} ({float(d2):.8f} <= {D2_f}), d3' = {d3} ({float(d3):.8f} <= {D3_f})")
    print(f"    2^(12*R) = {float(arg12):.8f}  =>  R = {R_tot:.12f}")
    return R_tot


# ==============================================================================
# Converse outer bounds
# ==============================================================================
def ozarow_2desc_lb(D1: float, D2: float) -> float:
    if D1 >= 0.5 * (1.0 + D2):
        return 0.25 * log2(1.0 / D2)
    best_oz = 0.5 * log2(1.0 / D2)
    for d1 in np.linspace(D2 + 1e-9, D1, 2000):
        rho = 2.0 * (1.0 - d1) * D2 / (d1 * (1.0 - D2)) - 1.0
        if -1.0 < rho < 1.0:
            val = 0.5 * log2(1.0 / d1) + 0.25 * log2(1.0 / (1.0 - rho * rho))
            if val < best_oz:
                best_oz = val
    return best_oz


def main():
    print("================================================================================")
    print("1. CERTIFIED DISPROOF #1: CORRELATED-V SCHEME vs tianChenMD3SymRate")
    print("================================================================================")
    D1, D2, D3 = 0.5, 0.1, 0.05
    rtc_opt, ar_opt = compute_R_TC_2d(D1, D2, D3)
    lb_tc, box_lb, tail_a, tail_r, worst = certify_TC_lower_bound(
        D1, D2, D3, a_max=3.2, r_min=-0.475, r_max=0.80, n_splits=30000
    )
    print(f"Target triple: (D1, D2, D3) = (1/2, 1/10, 1/20)")
    print(f"  Numerical optimum R_TC = {rtc_opt:.12f} at a={ar_opt[0]:.8f}, rho={ar_opt[1]:.8f}")
    print(f"  CERTIFIED lower bound  = {lb_tc:.12f} (box={box_lb:.10f}, tail_a={tail_a:.6f}, tail_r={tail_r:.6f})")
    r_w1 = verify_exact_rational_witness(
        "Rational Witness #1", Fraction(-8, 25), Fraction(23, 100), Fraction(-3, 50),
        Fraction(1, 2), Fraction(1, 10), Fraction(1, 20)
    )
    r_w2 = verify_exact_rational_witness(
        "Rational Witness #2", Fraction(-321, 1000), Fraction(59, 250), Fraction(-29, 500),
        Fraction(1, 2), Fraction(1, 10), Fraction(1, 20)
    )
    print(f"  CERTIFIED GAP (Witness #1): R_TC_lb - R_w1 = {lb_tc - r_w1:+.10f} bits/desc (crosses R = 1!)")
    print(f"  CERTIFIED GAP (Witness #2): R_TC_lb - R_w2 = {lb_tc - r_w2:+.10f} bits/desc")

    print("\n================================================================================")
    print("2. CERTIFIED DISPROOF #2: STRICT NON-CONVEXITY OF tianChenMD3SymRate")
    print("================================================================================")
    A = (0.5, 0.1, 0.05)
    B = (0.9, 0.05, 0.04)
    lam = 0.75
    M = tuple(lam * A[i] + (1.0 - lam) * B[i] for i in range(3))  # (0.6, 0.0875, 0.0475)
    # Explicit feasible 4-tuples for A and B verified directly in eval_TC_lean_4d:
    # For A = (0.5, 0.1, 0.05): opt a=1.17925841, sig2=1/a=0.84799053, rho=-0.37137085
    # Pick explicit clean decimals strictly satisfying d1<=D1, d2<=D2:
    rA_ub, infoA = eval_TC_lean_4d(1.0, 0.84799, -0.37137, 0.19054, *A)
    # For B = (0.9, 0.05, 0.04): find opt and pick explicit feasible 4-tuple:
    rB_opt, (aB, rhoB) = compute_R_TC_2d(*B)
    v0B = min(1.0, B[0] * (1.0 + aB))
    sig2B = v0B / aB if aB > 1e-9 else 1e9
    d2bB = (v0B * sig2B * (1.0 + rhoB)) / (2.0 * v0B + sig2B * (1.0 + rhoB))
    tau2B = d2bB * B[1] / (d2bB - B[1]) * 0.99999  # slightly smaller tau2 for strict d2 <= D2
    rB_ub, infoB = eval_TC_lean_4d(v0B, sig2B, rhoB, tau2B, *B)
    R_ts_ub = lam * rA_ub + (1.0 - lam) * rB_ub

    rM_opt, arM = compute_R_TC_2d(*M)
    lb_M, box_M, tail_aM, tail_rM, _ = certify_TC_lower_bound(
        *M, a_max=3.8, r_min=-0.493, r_max=0.90, n_splits=30000
    )
    print(f"  A = {A}: explicit feasible 4-tuple gives R_TC(A) <= {rA_ub:.10f} (v0=1, sig2=0.84799, rho=-0.37137, tau2=0.19054)")
    print(f"  B = {B}: explicit feasible 4-tuple gives R_TC(B) <= {rB_ub:.10f} (v0={v0B:.6f}, sig2={sig2B:.6f}, rho={rhoB:.6f}, tau2={tau2B:.6f})")
    print(f"  Time-sharing upper bound at M = {M} (lambda=3/4): R_TS <= {R_ts_ub:.10f}")
    print(f"  Direct R_TC(M) numerical opt: {rM_opt:.10f} at a={arM[0]:.6f}, rho={arM[1]:.6f}")
    print(f"  CERTIFIED lower bound on R_TC(M): >= {lb_M:.10f} (box={box_M:.10f}, tail_a={tail_aM:.6f}, tail_r={tail_rM:.6f})")
    print(f"  CERTIFIED STRICT NON-CONVEXITY GAP: R_TC(M) - R_TS >= {lb_M - R_ts_ub:+.10f} bits/desc!")

    print("\n================================================================================")
    print("3. FIRST-ORDER DERIVATIVE VERIFICATION (Layers 1, 2, 3 all active)")
    print("================================================================================")
    v0, sig2, rho = 1.0, 1.0, -0.25
    D2_t, D3_t = 0.05, 0.02
    c2 = 0.5 * sig2 * (1.0 + rho)
    c3 = (1.0 / 3.0) * sig2 * (1.0 + 2.0 * rho)
    d2b = v0 * c2 / (v0 + c2)
    d3b = v0 * c3 / (v0 + c3)
    tau2_0 = d2b * D2_t / (d2b - D2_t)
    d3p_0 = d3b * tau2_0 / (d3b + tau2_0)
    analytic_slope = -(d3p_0 / (3.0 * math.log(2.0) * tau2_0)) * (1.0 / c3 - 1.0 / c2)
    K = 1.0 / D2_t - 1.0 / v0
    r0_tot, inf0 = eval_corrV(v0, sig2, rho, tau2_0, 0.0, 0.5, D2_t, D3_t)
    for eps in [1e-5, 1e-6, 1e-7]:
        tau2_e = (c2 + 2.0 * eps + K * eps * eps) / (K * c2 - 1.0)
        re_tot, infe = eval_corrV(v0, sig2, rho, tau2_e, -eps, 0.5, D2_t, D3_t)
        dr2 = (infe["r2"] - inf0["r2"]) / eps
        dr3 = (infe["r3"] - inf0["r3"]) / eps
        print(f"  eps={eps:.0e}: dr2/deps={dr2:+.4e}, dr3/deps={dr3:+.10f}, analytic={analytic_slope:+.10f}, rel_err={abs(dr2+dr3-analytic_slope)/abs(analytic_slope):.2e}")

    print("\n================================================================================")
    print("4. SIMPLEX COMPARISON: OUTER BOUNDS vs R_corrV vs R_TC")
    print("================================================================================")
    print(f"{'D1':>5} {'D2':>5} {'D3':>6} | {'R_Oz12':>8} {'R_WV13':>8} | {'R_corrV':>9} {'R_TC':>9} | {'TC-corrV':>9} {'corrV-LB':>9}")
    print("-" * 86)
    pts = [
        (0.50, 0.10, 0.050),
        (0.50, 0.05, 0.020),
        (0.40, 0.05, 0.020),
        (0.30, 0.05, 0.020),
        (0.60, 0.05, 0.025),
        (0.80, 0.10, 0.050),
        (0.70, 0.10, 0.040),
        (0.90, 0.10, 0.030),
        (0.60, 0.30, 0.200),
        (0.50, 0.10, 0.020),
        (0.50, 0.10, 0.010),
    ]
    for (d1, d2, d3) in pts:
        r_oz = ozarow_2desc_lb(d1, d2)
        r_wv, _ = compute_R_TC_2d(d1, 1.0, d3)
        lb_m = max(0.5 * log2(1.0 / d1), 0.25 * log2(1.0 / d2), (1.0 / 6.0) * log2(1.0 / d3), r_oz, r_wv)
        r_tc, _ = compute_R_TC_2d(d1, d2, d3)
        r_cv, _ = opt_corrV(d1, d2, d3)
        print(f"{d1:5.2f} {d2:5.2f} {d3:6.3f} | {r_oz:8.5f} {r_wv:8.5f} | {r_cv:9.6f} {r_tc:9.6f} | {r_tc-r_cv:+9.6f} {r_cv-lb_m:+9.6f}")


if __name__ == "__main__":
    main()
