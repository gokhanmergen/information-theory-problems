#!/usr/bin/env python3
"""Is G_2(BMC) = G_1(BMC) as regions?  Compare support functions.

Both regions are closed, convex and down-closed in the nonnegative orthant, so each is
determined by its support function s(lam) = max{lam R1 + (1-lam) R2}, lam in [0,1]:
  s_1(lam) = max_{x,y} lam*y*h(x) + (1-lam)*x*h(y),
  s_2(lam) = max_{v in [0,1]^8} [lam*H(Y^2|S2) + (1-lam)*H(Y^2|S1)] / 2,
with H(Y^2|S2), H(Y^2|S1) in the closed form of bmc_g2_closed_form.py (exact; verified
against brute force there).  Multistart L-BFGS-B; numerical evidence only.
"""
import numpy as np
from scipy.optimize import minimize


def h(x):
    x = np.clip(x, 1e-300, 1.0)
    y = np.clip(1 - x, 1e-300, 1.0)
    return -(x * np.log2(x) + y * np.log2(y))


def parts(v):
    a, g1, f0, f1, b, g2, e0, e1 = v
    c = (1 - a) * g1 + a * f0
    cp = (1 - b) * g2 + b * e0
    HY_S2 = b * h(a) + (1 - b) * g2 * h(c) + b * (1 - a) * e0 * h(g1) + a * b * e1 * h(f1)
    HY_S1 = a * h(b) + (1 - a) * g1 * h(cp) + a * (1 - b) * f0 * h(g2) + a * b * f1 * h(e1)
    return HY_S2, HY_S1


def main():
    rng = np.random.default_rng(3)
    print(" lam     s_1(lam)      s_2(lam)      s_2 - s_1")
    worst = -1.0
    for lam in np.linspace(0, 1, 21):
        b1 = 0.0
        for _ in range(400):
            r = minimize(lambda z: -(lam * z[1] * h(z[0]) + (1 - lam) * z[0] * h(z[1])),
                         rng.uniform(0, 1, 2), method="L-BFGS-B", bounds=[(0, 1)] * 2)
            b1 = max(b1, -r.fun)
        b2 = 0.0
        for _ in range(1500):
            def f(v):
                A, B = parts(v)
                return -(lam * A + (1 - lam) * B) / 2
            r = minimize(f, rng.uniform(0, 1, 8), method="L-BFGS-B", bounds=[(0, 1)] * 8)
            b2 = max(b2, -r.fun)
        worst = max(worst, b2 - b1)
        print(f"{lam:4.2f}  {b1:.10f}  {b2:.10f}  {b2 - b1:+.2e}", flush=True)
    print(f"max over lam of s_2 - s_1 = {worst:+.2e}")


if __name__ == "__main__":
    main()
