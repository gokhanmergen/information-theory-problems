#!/usr/bin/env python3
"""Rigorous interval bound on the FIRST-ORDER EGN functional at unit gains, P1 = P2 = P -> 0.

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

What is certified (mpmath interval arithmetic, outward rounding, branch and bound):
    max over (rho, alpha) in [-1, 1] x [0, 1] of G(rho, alpha)  <=  T = 1.5400,
where G is the closed form of the first-order problem after the exact eliminations of
egn2.py, specialised to a12 = a13 = a23 = 1 (p1 = p2 = 1):
    q = 1 - rho^2,  w = sqrt(q alpha),  k = alpha / (1 - alpha),
    lam = (sqrt(5 + 4 rho) - (1 + 2 rho)) / 2          (= lam_plus at unit gains, >= 0),
    B = min(rho^2, lam) - rho^2 + (1 + rho)^2          (>= 0),
    the constraint is k s^2 - 2 w s <= B (the constant term vanishes at unit gains),
    s* = max(-w, s_minus),  s_minus = -B / (w + sqrt(w^2 + k B)),
    G = q (1 + alpha) - max(0, w + s_minus)^2.
In units of P/2 nats the cutset value is 2, so T/2 = 0.7700 of the cutset slope, i.e.
    first-order EGN slope <= 0.7700 / ln 2 = 1.1109 bits per unit power  <  1/ln 2 = 1.4427.

What is NOT certified here (see the attempt): that G is the correct first-order limit of the
exact EGN bound (a [sketch] derivation, checked numerically by egn_global_check.py), and EGN's
own theorems (Corollary 1, Lemma 7 Gaussian optimality, eq. (52)), which are cited.

Domain handling:
  alpha in [0, d]:      G <= q (1 + alpha) <= 1 + d.
  alpha in [1 - d, 1]:  w + sqrt(w^2 + kB) >= sqrt(kB) gives w + s_minus >= w - sqrt(B/k), and
                        1/k <= d/(1-d), B <= 4, so G <= 2q - max(0, sqrt(q(1-d)) - sqrt(4d/(1-d)))^2.
  alpha in [d, 1 - d]:  interval evaluation of the exact closed form on boxes, bisection until the
                        upper bound is <= T.
Run:  python3 egn_interval_cert.py    (prints PASS/FAIL; about 1-5 min)
Requires mpmath (and numpy for the float cross-check).
"""
import numpy as np
from mpmath import iv, mpf

iv.dps = 30
T = mpf("1.5400")
D = mpf("1e-6")


def imin(x, y):
    return iv.mpf([min(x.a, y.a), min(x.b, y.b)])


def imax0(x):
    return iv.mpf([max(mpf(0), x.a), max(mpf(0), x.b)])


def B_of(r):
    lam = (iv.sqrt(5 + 4 * r) - (1 + 2 * r)) / 2
    lam = imax0(lam)
    return imax0(imin(r * r, lam) - r * r + (1 + r) ** 2)


def G_upper(r, a):
    """Upper bound of G over the box r x a (intervals), a within [D, 1-D]."""
    q = imax0(1 - r * r)
    w = iv.sqrt(q * a)
    k = a / (1 - a)
    B = B_of(r)
    root = iv.sqrt(w * w + k * B)
    num = imax0(w * w + w * root - B)      # = (w + s_minus) * (w + root), clipped at 0
    den = w + root
    if den.a <= 0:                          # cannot happen for a >= D, q > 0; be safe
        X = iv.mpf([0, 0])
    else:
        X = num / den
    G = q * (1 + a) - X * X
    return G.b


def sliver_upper(r):
    """Upper bound on G for alpha in [1-D, 1] and rho in the interval r."""
    q = imax0(1 - r * r)
    lowX = imax0(iv.sqrt(q * (1 - D)) - iv.sqrt(4 * D / (1 - D)))
    return (2 * q - lowX * lowX).b


def bnb():
    boxes = [((mpf(-1), mpf(1)), (D, 1 - D))]
    done = 0
    maxleaf = mpf("-inf")
    while boxes:
        (r0, r1), (a0, a1) = boxes.pop()
        ub = G_upper(iv.mpf([r0, r1]), iv.mpf([a0, a1]))
        if ub <= T:
            done += 1
            maxleaf = max(maxleaf, ub)
            continue
        if (r1 - r0) < mpf("1e-9") and (a1 - a0) < mpf("1e-9"):
            return False, done, (r0, r1, a0, a1, ub)
        if (r1 - r0) / 2 >= (a1 - a0):
            m = (r0 + r1) / 2
            boxes.append(((r0, m), (a0, a1)))
            boxes.append(((m, r1), (a0, a1)))
        else:
            m = (a0 + a1) / 2
            boxes.append(((r0, r1), (a0, m)))
            boxes.append(((r0, r1), (m, a1)))
    return True, done, maxleaf


def G_float(rho, alpha):
    q = 1 - rho ** 2
    w = np.sqrt(q * alpha)
    k = alpha / (1 - alpha)
    lam = (np.sqrt(5 + 4 * rho) - (1 + 2 * rho)) / 2
    B = min(rho ** 2, lam) - rho ** 2 + (1 + rho) ** 2
    sm = -B / (w + np.sqrt(w * w + k * B)) if w + np.sqrt(w * w + k * B) > 0 else -np.inf
    return q * (1 + alpha) - max(0.0, w + sm) ** 2


if __name__ == "__main__":
    # float cross-check of the closed form against egn2.best_s (non-rigorous)
    from egn2 import best_s
    from egn_lowsnr import lam_plus
    err = 0.0
    for rho in np.linspace(-0.99, 0.99, 37):
        assert abs(lam_plus(1, 1, 1, 1, 1, rho) - max(0, (np.sqrt(5 + 4 * rho) - 1 - 2 * rho) / 2)) < 1e-12
        for alpha in np.linspace(0.01, 0.99, 37):
            F, _ = best_s(1, 1, 1, 1, 1, rho, alpha)
            err = max(err, abs(F - G_float(rho, alpha)))
    print(f"float cross-check closed form vs egn2.best_s: max |diff| = {err:.2e}")
    grid = max(G_float(r, a) for r in np.linspace(-1, 1, 801) for a in np.linspace(0, 1 - 1e-9, 801))
    print(f"float grid max of G: {grid:.6f}")
    ok_lo = (1 + D) <= T
    ok_hi = all(sliver_upper(iv.mpf([mpf(-1) + mpf(i) / 50, mpf(-1) + mpf(i + 1) / 50])) <= T
                for i in range(100))
    ok, n, info = bnb()
    print(("PASS" if ok_lo else "FAIL") + f"  alpha in [0, 1e-6]: G <= 1 + 1e-6 <= {T}")
    print(("PASS" if ok_hi else "FAIL") + f"  alpha in [1-1e-6, 1]: sliver bound <= {T}")
    if ok:
        print(f"PASS  alpha in [1e-6, 1-1e-6]: G <= {T} on all {n} leaf boxes "
              f"(largest leaf upper bound {float(info):.6f})")
    else:
        print(f"FAIL  box not resolved: {info}")
    print("OVERALL " + ("PASS" if (ok and ok_lo and ok_hi) else "FAIL")
          + f": first-order EGN <= {T} (units P/2 nats); cutset = 2; ratio <= {float(T) / 2:.4f}")
