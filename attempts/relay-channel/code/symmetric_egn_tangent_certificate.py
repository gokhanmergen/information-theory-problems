#!/usr/bin/env python3
"""Fixed-bias concavity certificate for the symmetric binary EGN relay bound.

This improves ``symmetric_egn_certificate.py`` by proving that, at fixed input
bias a, the inner objective is quantitatively concave in the two conditional
crossover probabilities (u,v). A tangent point therefore upper-bounds the
complete (u,v)-square. Only the remaining a interval is bisected.

Usage:
  python3 symmetric_egn_tangent_certificate.py solve <rho> <R0>
  python3 symmetric_egn_tangent_certificate.py certify \
      <rho> <R0> <lambda> <slope> [tolerance]
  python3 symmetric_egn_tangent_certificate.py selftest
"""
from __future__ import annotations

import argparse
import heapq
import math
import random
from decimal import Decimal
from functools import lru_cache

from scipy.optimize import minimize, root

import symmetric_egn_certificate as base


# This is deliberately much larger than the inherited 60-digit arithmetic's
# roundoff. For the certified specialization, y is in [0.1,0.9], the optimizer
# clips u and v to [1e-12,1-1e-12], all intermediate magnitudes are below 2e12,
# and fewer than 100 Decimal operations enter any reported interval bound.
PAD = Decimal("1e-30")


def h_prime_float(x: float) -> float:
    return math.log2((1.0 - x) / x)


@lru_cache(maxsize=None)
def h_prime_decimal(x: Decimal) -> Decimal:
    if not (0 < x < 1):
        raise ValueError("entropy derivative requires x in (0,1)")
    return ((1 - x) / x).ln() / Decimal(2).ln()


def optimize_slice_float(a: float, rho: float, lam: float, slope: float):
    """Find a useful tangent point; optimality is not needed for validity."""
    def negative(x):
        return -base.objective_float((a, x[0], x[1]), rho, lam, slope)

    def gradient(x):
        u, v = x
        z = (1.0 - a) * u + a * (1.0 - v)
        gu = ((1.0 - a)
              * (h_prime_float(u) - (1.0 - lam) * h_prime_float(z) - slope))
        gv = (a * ((1.0 - lam) * h_prime_float(z)
                   + h_prime_float(v) - slope))
        return (-gu, -gv)

    # The negative objective is convex by the fixed-a concavity lemma, so one
    # gradient-based solve suffices for a sharp tangent point.
    result = minimize(negative, (0.5, 0.5), jac=gradient, method="L-BFGS-B",
                      bounds=((1e-12, 1 - 1e-12),) * 2,
                      options={"ftol": 1e-15, "gtol": 1e-12, "maxiter": 500})
    return tuple(float(x) for x in result.x)


def tangent_upper(alo: Decimal, ahi: Decimal,
                  rho: Decimal, lam: Decimal, slope: Decimal):
    """Upper-bound max F on [alo,ahi] x [0,1]^2 using slice concavity."""
    amid = (alo + ahi) / 2
    u_float, v_float = optimize_slice_float(
        float(amid), float(rho), float(lam), float(slope))
    # Decimal(str(float)) makes the tangent point an exact feasible decimal pair.
    u0, v0 = Decimal(str(u_float)), Decimal(str(v_float))

    def z_at(a):
        return (1 - a) * u0 + a * (1 - v0)

    ymid = rho + (1 - 2 * rho) * amid
    zmid = z_at(amid)
    f0_mid = (base.objective_decimal((amid, u0, v0), rho, lam, slope)
              + Decimal(8) * PAD)

    k = 1 - 2 * rho
    dz = 1 - v0 - u0
    f0_prime = ((1 - lam)
                * (k * h_prime_decimal(ymid) - dz * h_prime_decimal(zmid))
                + base.h_decimal(v0) - base.h_decimal(u0)
                - slope * (v0 - u0))

    radius = (ahi - alo) / 2
    ylo, yhi = sorted((rho + k * alo, rho + k * ahi))
    zlo, zhi = sorted((z_at(alo), z_at(ahi)))
    min_y_variance = min(ylo * (1 - ylo), yhi * (1 - yhi))
    min_z_variance = min(zlo * (1 - zlo), zhi * (1 - zhi))
    ln2 = Decimal(2).ln()
    second_derivative_bound = ((1 - lam) / ln2
                               * (k * k / min_y_variance
                                  + dz * dz / min_z_variance)
                               + PAD)
    f0_upper = (f0_mid + abs(f0_prime) * radius
                + second_derivative_bound * radius * radius / 2
                + Decimal(8) * PAD)

    hpz_lo = h_prime_decimal(zhi) - PAD
    hpz_hi = h_prime_decimal(zlo) + PAD
    hpu_lo = h_prime_decimal(u0) - PAD
    hpu_hi = h_prime_decimal(u0) + PAD
    hpv_lo = h_prime_decimal(v0) - PAD
    hpv_hi = h_prime_decimal(v0) + PAD

    # dF/du = (1-a) [h'(u0) - (1-lambda)h'(z0(a)) - slope].
    bu_lo = hpu_lo - (1 - lam) * hpz_hi - slope - PAD
    bu_hi = hpu_hi - (1 - lam) * hpz_lo - slope + PAD
    # dF/dv = a [(1-lambda)h'(z0(a)) + h'(v0) - slope].
    bv_lo = (1 - lam) * hpz_lo + hpv_lo - slope - PAD
    bv_hi = (1 - lam) * hpz_hi + hpv_hi - slope + PAD

    max_bu_sq = max(bu_lo * bu_lo, bu_hi * bu_hi)
    max_bv_sq = max(bv_lo * bv_lo, bv_hi * bv_hi)
    # Fixed-a strong concavity gives
    #   max_{u,v} F <= F(u0,v0)
    #     + ln(2)/(8*lambda) [(1-a) B_u^2 + a B_v^2].
    concavity_correction = (ln2 / (8 * lam)
                            * ((1 - alo) * max_bu_sq + ahi * max_bv_sq)
                            + Decimal(8) * PAD)

    return f0_upper + concavity_correction + Decimal(8) * PAD, (u0, v0)


def certify(rho_text: str, r0_text: str, lam_text: str, slope_text: str,
            tolerance_text: str):
    rho, r0 = map(base.d, (rho_text, r0_text))
    lam, slope = map(base.d, (lam_text, slope_text))
    tolerance = base.d(tolerance_text)
    if not (0 < rho < Decimal("0.5")):
        raise ValueError("certificate requires 0 < rho < 0.5")
    if not (0 < lam <= 1):
        raise ValueError("curvature certificate requires 0 < lambda <= 1")
    if tolerance <= 0:
        raise ValueError("tolerance must be positive")

    feasible_value, feasible_point = base.maximize_float(
        float(rho), float(lam), float(slope), seed=4)
    rational_point = tuple(Decimal(str(x)) for x in feasible_point)
    lower = (base.objective_decimal(rational_point, rho, lam, slope)
             - Decimal(10) * PAD)

    counter = 0
    initial_upper, _ = tangent_upper(Decimal(0), Decimal(1),
                                     rho, lam, slope)
    heap = [(-initial_upper, counter, Decimal(0), Decimal(1))]
    pruned_upper = lower
    processed = 0
    while heap:
        neg_upper, _, alo, ahi = heapq.heappop(heap)
        upper = -neg_upper
        if upper - lower <= tolerance:
            pruned_upper = max(pruned_upper, upper)
            break
        amid = (alo + ahi) / 2
        for child_lo, child_hi in ((alo, amid), (amid, ahi)):
            child_upper, _ = tangent_upper(child_lo, child_hi,
                                           rho, lam, slope)
            if child_upper - lower > tolerance:
                counter += 1
                heapq.heappush(heap, (-child_upper, counter,
                                      child_lo, child_hi))
            else:
                pruned_upper = max(pruned_upper, child_upper)
        processed += 1
        if processed % 1000 == 0:
            print(f"processed={processed} active={len(heap)} "
                  f"lower={lower} upper={-heap[0][0] if heap else pruned_upper}")

    inner_upper = max(lower, pruned_upper,
                      -heap[0][0] if heap else lower) + PAD
    constant = 1 - 2 * base.h_decimal(rho) + lam * r0 + slope * rho
    capacity_upper = constant + inner_upper + Decimal(10) * PAD
    print(f"rho={rho} R0={r0} lambda={lam} slope={slope}")
    print(f"optimizer_feasible={feasible_value:.15f} point={feasible_point}")
    print(f"processed_intervals={processed} active_intervals={len(heap)}")
    print(f"inner_lower={lower}")
    print(f"inner_upper={inner_upper}")
    print(f"inner_width={inner_upper - lower}")
    print(f"certified_EGN_upper={capacity_upper}")


def solve_parameters(rho: float, r0: float):
    """Heuristically solve the two-active-branch minimax equations."""
    k = 1.0 - 2.0 * rho

    def equations(x):
        a, u, v, lam, slope, theta = x
        linear = 1.0 - lam
        y = rho + k * a
        z = (1.0 - a) * u + a * (1.0 - v)
        mismatch = (1.0 - a) * u + a * v
        entropy_difference = base.h_float(y) - base.h_float(z)
        asymmetric = base.objective_float((a, u, v), rho, lam, slope)
        symmetric_error = 1.0 / (1.0 + 2.0 ** slope)
        symmetric = math.log2(1.0 + 2.0 ** (-slope))
        return (
            linear * (k * h_prime_float(y)
                      - (1.0 - v - u) * h_prime_float(z))
            + base.h_float(v) - base.h_float(u) - slope * (v - u),
            h_prime_float(u) - linear * h_prime_float(z) - slope,
            linear * h_prime_float(z) + h_prime_float(v) - slope,
            theta * entropy_difference - r0,
            theta * mismatch + (1.0 - theta) * symmetric_error - rho,
            asymmetric - symmetric,
        )

    initial = (0.998, 0.82, 0.014, 0.32, 1.98, 0.55)
    result = root(equations, initial, tol=1e-12)
    print(f"success={result.success} residual={max(abs(x) for x in result.fun):.3e}")
    names = ("a", "u", "v", "lambda", "slope", "theta")
    for name, value in zip(names, result.x):
        print(f"{name}={value:.15f}")


def selftest():
    rng = random.Random(1)
    rho, lam, slope = map(base.d, ("0.1", "0.318749787402", "1.981497952611"))
    for _ in range(1000):
        alo = Decimal(str(rng.random()))
        ahi = alo + (1 - alo) * Decimal(str(rng.random()))
        upper, _ = tangent_upper(alo, ahi, rho, lam, slope)
        for _sample in range(20):
            point = (alo + (ahi - alo) * Decimal(str(rng.random())),
                     Decimal(str(rng.random())),
                     Decimal(str(rng.random())))
            value = base.objective_decimal(point, rho, lam, slope)
            if value > upper:
                raise AssertionError((alo, ahi, point, value, upper))
    print("selftest passed: 20000 sampled points below tangent interval bounds")


def main():
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    solve = subparsers.add_parser("solve")
    solve.add_argument("rho", type=float)
    solve.add_argument("r0", type=float)
    cert = subparsers.add_parser("certify")
    cert.add_argument("rho")
    cert.add_argument("r0")
    cert.add_argument("lam")
    cert.add_argument("slope")
    cert.add_argument("tolerance", nargs="?", default="0.000001")
    subparsers.add_parser("selftest")
    args = parser.parse_args()
    if args.command == "solve":
        solve_parameters(args.rho, args.r0)
    elif args.command == "certify":
        certify(args.rho, args.r0, args.lam, args.slope, args.tolerance)
    else:
        selftest()


if __name__ == "__main__":
    main()
