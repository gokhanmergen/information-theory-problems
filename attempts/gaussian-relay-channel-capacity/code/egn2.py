#!/usr/bin/env python3
"""First-order (P -> 0) EGN bound with the variables b and s eliminated in closed form.

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

The first-order problem (see egn_lowsnr.py) has variables (rho, alpha, b, s).  The rate does not
depend on b and b enters the constraint with a plus sign, so the smallest PSD-feasible
b = s^2 alpha/(1-alpha) is optimal.  For fixed (rho, alpha), with w = sqrt(a12 q alpha) and
k = alpha/(1-alpha), the constraint becomes the convex quadratic
    k s^2 - 2 w s + const <= B,   const = q a12 - w^2 - a13 q (1 - alpha),
and the rate q a12 + q a13 alpha - (w + s)^2 is maximised by the feasible s closest to -w.
So the first-order bound is  max over (rho, alpha) in [-1,1] x [0,1) of a closed-form G(rho, alpha),
evaluated here on a grid with local refinement (a 2-D problem: no multistart issue).

Units: t/2 nats (cutset at unit gains, equal powers = 2).  Divide by 2 and by ln 2 to get bits
per unit power;  multiply the ratio EGN/cutset by 1/ln 2 = 1.4427 for the slope in bits.

Run:  python3 egn2.py      (about 1 min)
Requires numpy.
"""
import numpy as np
from egn_lowsnr import lam_plus, cutset_first


def best_s(a12, a13, a23, p1, p2, rho, alpha):
    """Return (G(rho, alpha), s*) or (None, None) if infeasible."""
    q = 1 - rho ** 2
    w = np.sqrt(a12 * q * alpha)
    B = (min(a12 * rho ** 2, lam_plus(a12, a13, a23, p1, p2, rho)) - a12 * rho ** 2
         + (rho * np.sqrt(a13) + np.sqrt(a23)) ** 2)
    k = alpha / (1 - alpha)
    const = q * a12 - w ** 2 - a13 * q * (1 - alpha)
    if k == 0:
        if w == 0:
            return (q * a12, 0.0) if const <= B else (None, None)
        s = max(-w, (const - B) / (2 * w))
    else:
        disc = w * w - k * (const - B)
        if disc < 0:
            return None, None
        sm = (w - np.sqrt(disc)) / k
        sp = (w + np.sqrt(disc)) / k
        s = min(max(-w, sm), sp)
    return q * a12 + q * a13 * alpha - (w + s) ** 2, s


def egn_first(a12, a13, a23, p1=1.0, p2=1.0, n=401, refine=4):
    best, arg = -1.0, None
    for rho in np.linspace(-1.0, 1.0, n):
        for alpha in np.linspace(0.0, 1 - 1e-9, n):
            F, s = best_s(a12, a13, a23, p1, p2, rho, alpha)
            if F is not None and F > best:
                best, arg = F, (rho, alpha, s)
    r0, al0, _ = arg
    h1, h2 = 2.0 / n, 1.0 / n
    for _ in range(refine):
        for rho in np.linspace(max(-1.0, r0 - h1), min(1.0, r0 + h1), 61):
            for alpha in np.linspace(max(0.0, al0 - h2), min(1 - 1e-12, al0 + h2), 61):
                F, s = best_s(a12, a13, a23, p1, p2, rho, alpha)
                if F is not None and F > best:
                    best, arg = F, (rho, alpha, s)
        r0, al0, _ = arg
        h1 /= 10
        h2 /= 10
    return best, arg


if __name__ == "__main__":
    LN2 = np.log(2)
    print("first-order EGN vs cutset (units t/2 nats), directions p1 = p2 = 1")
    for a in [(1, 1, 1), (4, 1, 1), (1, 1, 4), (0.25, 1, 1), (10, 1, 10), (1, 1, 0.25), (2, 1, 1), (1, 2, 1)]:
        cs = cutset_first(*a)
        eg, arg = egn_first(*a)
        print(f"a={a}: cutset {cs:.6f}  EGN {eg:.6f}  ratio {eg / cs:.6f}  "
              f"argmax rho={arg[0]:.6f} alpha={arg[1]:.6f} s={arg[2]:.6f}")
    eg, _ = egn_first(1, 1, 1)
    print(f"unit gains, P1 = P2 = P -> 0:  C/P <= {eg / 2 / LN2:.5f} bits per unit power "
          f"(cutset 1/ln 2 = {1 / LN2:.5f})")
