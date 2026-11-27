#!/usr/bin/env python3
"""Exact (finite-power) Gaussian evaluation of the EGN 2022 Corollary 1 bound: validation runs.

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

Sections:
  V1  Reproduction of EGN 2022 Fig. 4 (S13 = 3.7585, S12 = 1.2139, P = 1, S23 in {0.1, 0.25}).
      Values read off the published figure: new upper bound ~1.131 / ~1.140 bits, CF lower bound
      ~1.128 / ~1.1325, cutset ~1.204 / ~1.238.
  V2  Sanity: at random gains and powers, the evaluated bound must lie between the best of
      (DF, CF, EMZ Example 1) and the cutset bound.
  V3  Unit gains, P1 = P2 = P: (2/P) * EGN(P) in nats for P = 1, 0.1, 1e-2, 1e-3, compared with
      the first-order value 1.5396 (egn2.py) and the cutset value 2.

Optimisation: scipy differential_evolution over (rho, alpha, log10(1-beta), sigma) with a
penalty for constraint violation, 4 seeds, polished.  This is a heuristic global optimiser; the
dense-grid / multistart / interval checks are in egn_global_check.py and egn_interval_cert.py.

Run:  python3 egn_exact.py     (a few minutes)
Requires numpy, scipy.
"""
import numpy as np
from scipy.optimize import differential_evolution
from egn_lowsnr import exact_terms, df_rate, cf_rate, cutset_rate, ex1_rate

LN2 = np.log(2)


def egn_exact(g12, g13, g23, P1, P2, seeds=(1, 2, 3, 4)):
    """Max over (rho, alpha, beta, sigma) of EGN Corollary 1 (nats) by differential evolution."""
    scale = max(P1, 1e-300)

    def unpack(x):
        return x[0], x[1], 1 - 10 ** x[2], x[3]

    def obj(x):
        rho, alpha, beta, sigma = unpack(x)
        if beta <= 0 or abs(sigma) >= 1:
            return 1e3
        R, sl, psd, _ = exact_terms(g12, g13, g23, P1, P2, rho, alpha, beta, sigma)
        if not np.isfinite(R):
            return 1e3
        pen = 0.0
        if sl < 0:
            pen += 1e4 * (-sl) / scale
        if psd < 0:
            pen += 1e4 * (-psd)
        return -R / scale + pen

    bounds = [(-0.999, 0.999), (0, 0.99999), (-12, -0.0001), (-0.999, 0.999)]
    best = None
    for sd in seeds:
        r = differential_evolution(obj, bounds, seed=sd, tol=1e-12, maxiter=3000, popsize=40,
                                   polish=True)
        if best is None or r.fun < best.fun:
            best = r
    rho, alpha, beta, sigma = unpack(best.x)
    R, sl, psd, _ = exact_terms(g12, g13, g23, P1, P2, rho, alpha, beta, sigma)
    return R, (rho, alpha, beta, sigma, sl, psd)


def V1():
    print("V1: EGN 2022 Fig. 4 reproduction (bits)")
    for S23 in [0.1, 0.25]:
        g = (np.sqrt(1.2139), np.sqrt(3.7585), np.sqrt(S23))
        R, _ = egn_exact(*g, 1.0, 1.0)
        print(f"  S23={S23}: EGN {R / LN2:.4f}  CF {cf_rate(*g, 1, 1) / LN2:.4f}  "
              f"cutset {cutset_rate(*g, 1, 1) / LN2:.4f}")


def V2():
    print("V2: achievable <= EGN <= cutset at random points (nats)")
    rng = np.random.default_rng(5)
    for _ in range(8):
        g = tuple(np.exp(rng.normal(size=3) * 0.8))
        P = float(np.exp(rng.normal() * 1.5))
        R, _ = egn_exact(*g, P, P)
        ach = max(df_rate(*g, P, P), cf_rate(*g, P, P), ex1_rate(*g, P, P))
        cut = cutset_rate(*g, P, P)
        flag = "ok" if ach - 1e-6 <= R <= cut + 1e-9 else "VIOLATION"
        print(f"  g={np.round(g, 3)} P={P:.4f}: achievable {ach:.6f} EGN {R:.6f} cutset {cut:.6f} {flag}")


def V3():
    print("V3: unit gains, P1 = P2 = P: (2/P) EGN(P) [nats]; first-order 1.5396, cutset 2")
    for P in [1.0, 0.1, 1e-2, 1e-3]:
        R, info = egn_exact(1, 1, 1, P, P)
        print(f"  P={P:g}: {2 * R / P:.6f}   (rho, alpha, beta, sigma) = "
              f"({info[0]:.5f}, {info[1]:.5f}, {info[2]:.8f}, {info[3]:.6f})")


if __name__ == "__main__":
    V1()
    V2()
    V3()
