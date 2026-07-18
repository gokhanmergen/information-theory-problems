#!/usr/bin/env python3
"""Evaluate the EGN Theorem 6 bound for the symmetric binary relay channel.

For X~Bern(a), let
    u = P(Z=1 | X=0),  v = P(Z=0 | X=1).
For fixed channel crossover rho, Lagrange multiplier lam in [0,1], and supporting
line slope s, the inner dual objective is

  F(a,u,v) = (1-lam)[h(rho+(1-2rho)a)-h(P(Z=1))]
             +(1-a)h(u)+a h(v)-s P(X != Z).

Theorem 6 and the supporting-line representation of a concave envelope give

  C <= 1-2h(rho)+lam*R0+s*rho+max_{[0,1]^3} F.

The ``search`` command finds useful (lam,s) candidates. The ``certify`` command
uses analytic entropy ranges on axis-aligned boxes to upper-bound the cube maximum.
The branch-and-bound arithmetic is high-precision Decimal arithmetic; every entropy
range is enlarged by ROUNDING_PAD.

Usage:
  python3 symmetric_egn_certificate.py search <rho> <R0>
  python3 symmetric_egn_certificate.py certify <rho> <R0> <lam> <s> [tol]
  python3 symmetric_egn_certificate.py baseline <rho> <R0> <q>
  python3 symmetric_egn_certificate.py selftest
"""
from __future__ import annotations

import argparse
import heapq
import math
import random
from dataclasses import dataclass
from decimal import Decimal, getcontext, localcontext
from functools import lru_cache

from scipy.optimize import differential_evolution, minimize


ROUNDING_PAD = Decimal("1e-45")
DECIMAL_PRECISION = 60
getcontext().prec = DECIMAL_PRECISION


def h_float(x: float) -> float:
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x * math.log2(x) - (1.0 - x) * math.log2(1.0 - x)


def objective_float(point, rho: float, lam: float, slope: float) -> float:
    a, u, v = point
    py = rho + (1.0 - 2.0 * rho) * a
    pz = (1.0 - a) * u + a * (1.0 - v)
    mismatch = (1.0 - a) * u + a * v
    return ((1.0 - lam) * (h_float(py) - h_float(pz))
            + (1.0 - a) * h_float(u) + a * h_float(v)
            - slope * mismatch)


def maximize_float(rho: float, lam: float, slope: float, seed: int = 0):
    result = differential_evolution(
        lambda x: -objective_float(x, rho, lam, slope),
        bounds=[(0.0, 1.0)] * 3,
        seed=seed,
        tol=1e-11,
        polish=True,
        workers=1,
        updating="immediate",
    )
    return -result.fun, result.x


def search(rho: float, r0: float):
    cache = {}

    def bound(params):
        lam, slope = params
        key = (round(float(lam), 10), round(float(slope), 10))
        if key not in cache:
            cache[key] = maximize_float(rho, float(lam), float(slope))[0]
        inner = cache[key]
        return 1.0 - 2.0 * h_float(rho) + lam * r0 + slope * rho + inner

    # The dual objective is convex. Powell is used only to locate a convenient
    # rational-decimal certificate point; certify() supplies the upper bound.
    best = None
    for start in ((0.25, 0.0), (0.5, 0.0), (0.75, 0.0), (0.5, 1.0), (0.5, -1.0)):
        result = minimize(
            bound,
            x0=start,
            method="Powell",
            bounds=((0.0, 1.0), (-10.0, 10.0)),
            options={"xtol": 2e-7, "ftol": 2e-9, "maxiter": 100},
        )
        if best is None or result.fun < best.fun:
            best = result
    assert best is not None
    inner, point = maximize_float(rho, best.x[0], best.x[1], seed=1)
    print(f"rho={rho:.12g} R0={r0:.12g}")
    print(f"candidate lambda={best.x[0]:.12f} slope={best.x[1]:.12f}")
    print(f"candidate inner maximum={inner:.12f} at "
          f"a={point[0]:.12f}, u={point[1]:.12f}, v={point[2]:.12f}")
    print(f"candidate EGN upper-bound value={bound(best.x):.12f}")


def d(value) -> Decimal:
    return value if isinstance(value, Decimal) else Decimal(str(value))


@lru_cache(maxsize=None)
def h_decimal(x: Decimal) -> Decimal:
    if x <= 0 or x >= 1:
        return Decimal(0)
    with localcontext() as ctx:
        ctx.prec = DECIMAL_PRECISION
        ln2 = Decimal(2).ln()
        return -(x * x.ln() + (1 - x) * (1 - x).ln()) / ln2


def entropy_range(lo: Decimal, hi: Decimal):
    values = [h_decimal(lo), h_decimal(hi)]
    minimum = max(Decimal(0), min(values) - ROUNDING_PAD)
    if lo <= Decimal("0.5") <= hi:
        maximum = Decimal(1)
    else:
        maximum = min(Decimal(1), max(values) + ROUNDING_PAD)
    return minimum, maximum


def multilinear_range(corners):
    return min(corners), max(corners)


@dataclass(frozen=True)
class Box:
    alo: Decimal
    ahi: Decimal
    ulo: Decimal
    uhi: Decimal
    vlo: Decimal
    vhi: Decimal

    def widest_axis(self):
        widths = (self.ahi - self.alo, self.uhi - self.ulo, self.vhi - self.vlo)
        return max(range(3), key=widths.__getitem__)

    def split(self):
        axis = self.widest_axis()
        bounds = [[self.alo, self.ahi], [self.ulo, self.uhi], [self.vlo, self.vhi]]
        mid = sum(bounds[axis]) / 2
        left = [pair[:] for pair in bounds]
        right = [pair[:] for pair in bounds]
        left[axis][1] = mid
        right[axis][0] = mid
        return Box(*sum(left, [])), Box(*sum(right, []))

    def center(self):
        return ((self.alo + self.ahi) / 2,
                (self.ulo + self.uhi) / 2,
                (self.vlo + self.vhi) / 2)


def affine_probability_range(box: Box, kind: str):
    values = []
    for a in (box.alo, box.ahi):
        for u in (box.ulo, box.uhi):
            for v in (box.vlo, box.vhi):
                if kind == "z":
                    value = (1 - a) * u + a * (1 - v)
                elif kind == "mismatch":
                    value = (1 - a) * u + a * v
                else:
                    raise ValueError(kind)
                values.append(value)
    return multilinear_range(values)


def conditional_entropy_upper(box: Box):
    _, hu = entropy_range(box.ulo, box.uhi)
    _, hv = entropy_range(box.vlo, box.vhi)
    values = [(1 - a) * eu + a * ev
              for a in (box.alo, box.ahi)
              for eu in (Decimal(0), hu)
              for ev in (Decimal(0), hv)]
    return max(values) + ROUNDING_PAD


def objective_upper(box: Box, rho: Decimal, lam: Decimal, slope: Decimal):
    pylo = rho + (1 - 2 * rho) * box.alo
    pyhi = rho + (1 - 2 * rho) * box.ahi
    _, hy_upper = entropy_range(min(pylo, pyhi), max(pylo, pyhi))
    pzlo, pzhi = affine_probability_range(box, "z")
    hz_lower, _ = entropy_range(pzlo, pzhi)
    clo, chi = affine_probability_range(box, "mismatch")
    linear_upper = -slope * (clo if slope >= 0 else chi)
    return ((1 - lam) * (hy_upper - hz_lower)
            + conditional_entropy_upper(box) + linear_upper
            + Decimal(6) * ROUNDING_PAD)


def objective_decimal(point, rho: Decimal, lam: Decimal, slope: Decimal):
    a, u, v = point
    py = rho + (1 - 2 * rho) * a
    pz = (1 - a) * u + a * (1 - v)
    mismatch = (1 - a) * u + a * v
    return ((1 - lam) * (h_decimal(py) - h_decimal(pz))
            + (1 - a) * h_decimal(u) + a * h_decimal(v)
            - slope * mismatch)


def binary_convolution(x: Decimal, y: Decimal):
    return x * (1 - y) + (1 - x) * y


def baseline(rho_text: str, r0_text: str, q_text: str):
    rho, r0, q = d(rho_text), d(r0_text), d(q_text)
    relay_destination_error = binary_convolution(rho, rho)
    compressed_error = binary_convolution(rho, q)
    output_disagreement = binary_convolution(rho, compressed_error)
    compression_rate = (h_decimal(binary_convolution(relay_destination_error, q))
                        - h_decimal(q))
    achievable_rate = (1 + h_decimal(output_disagreement)
                       - h_decimal(rho) - h_decimal(compressed_error))
    cutset_broadcast = (1 + h_decimal(relay_destination_error)
                        - 2 * h_decimal(rho))
    cutset_pipe = 1 - h_decimal(rho) + r0
    print(f"rho={rho} R0={r0} q={q}")
    print(f"compression_rate={compression_rate}")
    print(f"compression_feasible={compression_rate <= r0}")
    print(f"compress_forward_rate={achievable_rate}")
    print(f"cutset={min(cutset_broadcast, cutset_pipe)}")


def selftest():
    rng = random.Random(0)
    rho, lam, slope = d("0.1"), d("0.29518"), d("1.93807")
    for _ in range(1000):
        bounds = []
        for _axis in range(3):
            lo = Decimal(str(rng.random()))
            hi = lo + (1 - lo) * Decimal(str(rng.random()))
            bounds.extend((lo, hi))
        box = Box(*bounds)
        upper = objective_upper(box, rho, lam, slope)
        for _sample in range(10):
            point = tuple(lo + (hi - lo) * Decimal(str(rng.random()))
                          for lo, hi in ((box.alo, box.ahi),
                                         (box.ulo, box.uhi),
                                         (box.vlo, box.vhi)))
            value = objective_decimal(point, rho, lam, slope)
            if value > upper:
                raise AssertionError((box, point, value, upper))
    print("selftest passed: 10000 sampled points below their analytic box bounds")


def certify(rho_text: str, r0_text: str, lam_text: str, slope_text: str,
            tolerance_text: str):
    rho, r0 = d(rho_text), d(r0_text)
    lam, slope = d(lam_text), d(slope_text)
    tolerance = d(tolerance_text)
    if not (0 <= rho <= Decimal("0.5") and 0 <= lam <= 1):
        raise ValueError("require rho in [0,1/2] and lambda in [0,1]")

    initial = Box(*(Decimal(x) for x in (0, 1, 0, 1, 0, 1)))
    # A high-quality feasible point accelerates pruning. It is used only as a lower
    # bound on the maximum, so numerical global optimality is neither assumed nor
    # needed for the certificate.
    _, float_point = maximize_float(float(rho), float(lam), float(slope), seed=2)
    rational_point = tuple(Decimal(str(x)) for x in float_point)
    best_lower = (objective_decimal(rational_point, rho, lam, slope)
                  - Decimal(10) * ROUNDING_PAD)
    counter = 0
    heap = [(-objective_upper(initial, rho, lam, slope), counter, initial)]
    pruned_upper = best_lower
    processed = 0
    while heap:
        neg_upper, _, box = heapq.heappop(heap)
        upper = -neg_upper
        if upper - best_lower <= tolerance:
            # This is the largest remaining upper bound, so every box is certified.
            pruned_upper = max(pruned_upper, upper)
            break
        for child in box.split():
            child_upper = objective_upper(child, rho, lam, slope)
            if child_upper - best_lower > tolerance:
                counter += 1
                heapq.heappush(heap, (-child_upper, counter, child))
            else:
                pruned_upper = max(pruned_upper, child_upper)
        processed += 1
        if processed % 100000 == 0:
            print(f"processed={processed} active={len(heap)} "
                  f"lower={best_lower} upper={-heap[0][0] if heap else best_lower}")

    inner_upper = max(best_lower, pruned_upper,
                      -heap[0][0] if heap else best_lower) + ROUNDING_PAD
    with localcontext() as ctx:
        ctx.prec = DECIMAL_PRECISION
        constant = 1 - 2 * h_decimal(rho) + lam * r0 + slope * rho
        capacity_upper = constant + inner_upper + Decimal(10) * ROUNDING_PAD
    print(f"rho={rho} R0={r0} lambda={lam} slope={slope}")
    print(f"processed_boxes={processed} active_boxes={len(heap)}")
    print(f"inner_lower={best_lower}")
    print(f"inner_upper={inner_upper}")
    print(f"inner_width={inner_upper - best_lower}")
    print(f"certified_EGN_upper={capacity_upper}")


def main():
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    search_parser = subparsers.add_parser("search")
    search_parser.add_argument("rho", type=float)
    search_parser.add_argument("r0", type=float)
    certify_parser = subparsers.add_parser("certify")
    certify_parser.add_argument("rho")
    certify_parser.add_argument("r0")
    certify_parser.add_argument("lam")
    certify_parser.add_argument("slope")
    certify_parser.add_argument("tolerance", nargs="?", default="0.00001")
    baseline_parser = subparsers.add_parser("baseline")
    baseline_parser.add_argument("rho")
    baseline_parser.add_argument("r0")
    baseline_parser.add_argument("q")
    subparsers.add_parser("selftest")
    args = parser.parse_args()
    if args.command == "search":
        search(args.rho, args.r0)
    elif args.command == "certify":
        certify(args.rho, args.r0, args.lam, args.slope, args.tolerance)
    elif args.command == "baseline":
        baseline(args.rho, args.r0, args.q)
    else:
        selftest()


if __name__ == "__main__":
    main()
