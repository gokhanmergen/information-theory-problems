#!/usr/bin/env python3
"""Global (dense grid + multistart) maximisation of the EGN 2022 Corollary 1 Gaussian bound at
unit gains and equal powers, over the FULL feasible set of (rho, alpha, beta, sigma).

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

Purpose: a local optimiser can under-estimate a bound written as a maximum.  Here we
  G1  evaluate the exact finite-P bound on a dense 4-D grid covering the whole feasible set
      rho in [-1, 1], alpha in [0, 1], beta in (0, 1], sigma in (-1, 1)  (beta and |sigma| on
      logarithmic grids so that every scaling 1-beta ~ P^c, sigma ~ P^c is represented), keep
      the best feasible grid points, and polish the best 40 with Nelder-Mead;
      P in {1e-2, 1e-3, 1e-4, 1e-5};
  G2  do the same for the first-order (P -> 0) problem in its original variables
      (rho, alpha, b, s) WITHOUT eliminating b or s (cross-check of egn2.py's closed form).
Output is in units of P/2 nats (cutset = 2).  The first-order optimum from egn2.py is 1.539601.

Run:  python3 egn_global_check.py     (about 5-10 min on one core)
Requires numpy, scipy.
"""
import numpy as np
from scipy.optimize import minimize
from egn_lowsnr import exact_terms, first_order, lam_plus


def maxU_scalar(P, rho):
    return exact_terms(1, 1, 1, P, P, rho, 0.5, 1.0, 0.0)[3]


def exact_grid_rho(P, rho, A, Bm, S, mU):
    """Vectorised exact bound at unit gains for one rho; A, Bm (=1-beta), S arrays (broadcast)."""
    alpha, beta, sigma = A, 1 - Bm, S
    Q = (1 - rho ** 2) * P
    c = sigma * np.sqrt(Q * alpha * beta)
    A1 = 0.5 * np.log1p(2 * Q)
    VarYr_V = Q * alpha + beta + 2 * c
    VarY_V = Q * alpha + 1
    Cov_V = Q * alpha + c
    VarY_Yr = Q + 1 - Q ** 2 / (Q + 1)
    with np.errstate(divide="ignore", invalid="ignore"):
        VarY_VYr = VarY_V - Cov_V ** 2 / VarYr_V
        A2 = 0.5 * np.log(VarY_Yr / VarY_VYr)
        VarYr_VY = VarYr_V - Cov_V ** 2 / VarY_V
        A3 = 0.5 * np.log(VarYr_VY / (beta * (1 - sigma ** 2)))
        R = A1 - A2 - A3
        IVYr = 0.5 * np.log((Q + 1) / VarYr_V)
        IVY = 0.5 * np.log((Q + 1) / VarY_V)
    IXrYr = 0.5 * np.log1p(P) - 0.5 * np.log1p(Q)
    mac = 2 * P + 2 * rho * P
    IXrY = 0.5 * np.log1p(mac) - 0.5 * np.log1p(Q)
    lhs = (IXrYr + IVYr) - (IXrY + IVY)
    rhs = min(IXrYr, mU)
    psd = (1 - alpha) * (1 - beta) - sigma ** 2 * alpha * beta
    ok = (rhs - lhs >= 0) & (psd >= 0) & np.isfinite(R) & (beta > 0)
    return np.where(ok, R, -np.inf)


def G1(P, n_rho=201, n_alpha=101, n_beta=91, n_sig=71, polish=40):
    rhos = np.linspace(-1, 1, n_rho)
    alphas = np.linspace(0, 1, n_alpha)
    bms = np.concatenate([[0.0], 10.0 ** np.linspace(-10, 0, n_beta)[:-1]])  # 1 - beta
    sv = 10.0 ** np.linspace(-8, -1e-6, n_sig)
    sigmas = np.concatenate([-sv[::-1], [0.0], sv])
    A, Bm, S = np.meshgrid(alphas, bms, sigmas, indexing="ij")
    cand = []
    for rho in rhos:
        mU = maxU_scalar(P, rho)
        R = exact_grid_rho(P, rho, A, Bm, S, mU)
        idx = np.argsort(R, axis=None)[-5:]
        for i in idx:
            a, b, s = np.unravel_index(i, R.shape)
            if np.isfinite(R[a, b, s]):
                cand.append((R[a, b, s], rho, alphas[a], bms[b], sigmas[s]))
    cand.sort(reverse=True)
    grid_best = cand[0][0]

    def obj(x):
        rho, alpha, lbm, sigma = x
        if not (-1 <= rho <= 1 and 0 <= alpha <= 1 and abs(sigma) < 1 and lbm <= 0):
            return 1e3
        bm = 10 ** lbm
        R, sl, psd, _ = exact_terms(1, 1, 1, P, P, rho, alpha, 1 - bm, sigma)
        if not np.isfinite(R) or 1 - bm <= 0:
            return 1e3
        pen = (1e4 * (-sl) / P if sl < 0 else 0) + (1e4 * (-psd) / P if psd < 0 else 0)
        return -R / P + pen

    best = grid_best
    arg = cand[0][1:]
    for (_, rho, alpha, bm, sigma) in cand[:polish]:
        x0 = np.array([rho, alpha, np.log10(max(bm, 1e-12)), sigma])
        r = minimize(obj, x0, method="Nelder-Mead",
                     options={"xatol": 1e-12, "fatol": 1e-15, "maxiter": 20000})
        rho, alpha, lbm, sigma = r.x
        if -1 <= rho <= 1 and 0 <= alpha <= 1 and abs(sigma) < 1 and lbm <= 0:
            R, sl, psd, _ = exact_terms(1, 1, 1, P, P, rho, alpha, 1 - 10 ** lbm, sigma)
            if sl >= -1e-9 * P and psd >= -1e-9 * P and R > best:
                best, arg = R, (rho, alpha, 10 ** lbm, sigma)
    return 2 * grid_best / P, 2 * best / P, arg


def G2(n_rho=201, n_alpha=201, n_b=81, n_s=161, polish=40):
    """First-order problem, variables (rho, alpha, b, s); b >= 0, s real, PSD (1-alpha) b >= s^2 alpha."""
    rhos = np.linspace(-1, 1, n_rho)
    alphas = np.linspace(0, 1, n_alpha)
    bs = np.concatenate([[0.0], 10.0 ** np.linspace(-4, 3, n_b)])
    sv = 10.0 ** np.linspace(-4, 1.5, (n_s - 1) // 2)
    ss = np.concatenate([-sv[::-1], [0.0], sv])
    A, Bb, S = np.meshgrid(alphas, bs, ss, indexing="ij")
    cand = []
    for rho in rhos:
        q = 1 - rho ** 2
        w = np.sqrt(q * A)
        F = q + q * A - (w + S) ** 2
        lhs = q - w ** 2 + Bb - 2 * S * w - q * (1 - A)
        Bc = min(rho ** 2, lam_plus(1, 1, 1, 1, 1, rho)) - rho ** 2 + (rho + 1) ** 2
        ok = (lhs <= Bc) & ((1 - A) * Bb >= S ** 2 * A)
        F = np.where(ok, F, -np.inf)
        i = np.argmax(F)
        a, b, s = np.unravel_index(i, F.shape)
        cand.append((F[a, b, s], rho, alphas[a], bs[b], ss[s]))
    cand.sort(reverse=True)
    grid_best = cand[0][0]

    def obj(x):
        rho, alpha, b, s = x
        if not (-1 <= rho <= 1 and 0 <= alpha < 1 and b >= 0) or (1 - alpha) * b < s ** 2 * alpha:
            return 1e3
        F, sl = first_order(1, 1, 1, 1, 1, rho, alpha, s, b=b)
        return -F + (1e4 * (-sl) if sl < 0 else 0)

    best = grid_best
    for (_, rho, alpha, b, s) in cand[:polish]:
        r = minimize(obj, np.array([rho, alpha, b, s]), method="Nelder-Mead",
                     options={"xatol": 1e-12, "fatol": 1e-15, "maxiter": 20000})
        rho, alpha, b, s = r.x
        if -1 <= rho <= 1 and 0 <= alpha < 1 and b >= 0 and (1 - alpha) * b >= s ** 2 * alpha:
            F, sl = first_order(1, 1, 1, 1, 1, rho, alpha, s, b=b)
            if sl >= -1e-12 and F > best:
                best = F
    return grid_best, best


if __name__ == "__main__":
    print("G1: exact bound, full 4-D grid + 40 polished starts; units P/2 nats (cutset 2)")
    for P in [1e-2, 1e-3, 1e-4, 1e-5]:
        g, b, arg = G1(P)
        print(f"  P={P:g}: grid max {g:.6f}, polished max {b:.6f} at "
              f"(rho, alpha, 1-beta, sigma) = ({arg[0]:.5f}, {arg[1]:.5f}, {arg[2]:.3e}, {arg[3]:.5f})",
              flush=True)
    g, b = G2()
    print(f"G2: first-order problem in (rho, alpha, b, s): grid max {g:.6f}, polished max {b:.6f}")
