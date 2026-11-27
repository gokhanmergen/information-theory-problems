#!/usr/bin/env python3
"""k = 2 for the BMC: closed form of F = H(Y^2|S2) + H(Y^2|S1) and its reduction.

Reduced 2-step strategy of user 1: first input A ~ Bern(a); if A = 0 it sends g at
time 2; if A = 1 it sends f_{Y1}.  Only these marginals matter (attempt file, Claim 4):
  a = P(A=1), g1 = P(g=1|A=0), f0 = P(f_0=1|A=1), f1 = P(f_1=1|A=1),
and likewise (b, g2, e0, e1) for user 2.  Then
  F = b h(a) + a h(b)
      + (1-b) g2 h(c)  + a(1-b) f0 h(g2)      c  = (1-a) g1 + a f0
      + (1-a) g1 h(c') + b(1-a) e0 h(g1)      c' = (1-b) g2 + b e0
      + a b [e1 h(f1) + f1 h(e1)].
Checks done here:
 (1) the closed form agrees with the brute-force strategy computation of bmc_gk.py
     at random product distributions on the 6 reduced strategies;
 (2) multistart maximisation of F over [0,1]^8 returns 4 g*, g* = max_x x h(x);
 (3) the 4-variable majorant
     Phi(a,b,g1,g2) = b h(a) + a h(b) + 2 g* a b + (1-b) psi(g2) + (1-a) psi(g1)
                      - (1-a)(1-b) [g1 h(g2) + g2 h(g1)],
     psi(g) = max_c [g h(c) + c h(g)], has grid maximum 4 g* (grid, not interval-certified).
"""
import numpy as np
from scipy.optimize import minimize, minimize_scalar
import bmc_gk as G


def h(x):
    x = np.clip(x, 1e-300, 1.0)
    y = np.clip(1 - x, 1e-300, 1.0)
    return -(x * np.log2(x) + y * np.log2(y))


def F_closed(v):
    a, g1, f0, f1, b, g2, e0, e1 = v
    c = (1 - a) * g1 + a * f0
    cp = (1 - b) * g2 + b * e0
    return (b * h(a) + a * h(b) + (1 - b) * g2 * h(c) + a * (1 - b) * f0 * h(g2)
            + (1 - a) * g1 * h(cp) + b * (1 - a) * e0 * h(g1) + a * b * (e1 * h(f1) + f1 * h(e1)))


def strat_dist(a, g, f0, f1, trees):
    """Product-form distribution on reduced trees with the given marginals."""
    p = np.zeros(len(trees))
    for i, t in enumerate(trees):
        x, ch = t
        if x == 0:
            p[i] = (1 - a) * (g if ch[0][0] == 1 else 1 - g)
        else:
            p[i] = a * (f0 if ch[0][0] == 1 else 1 - f0) * (f1 if ch[1][0] == 1 else 1 - f1)
    return p


def main():
    rng = np.random.default_rng(0)
    trees = G.reduced_trees(2)
    T = G.outcome_table(trees, 2)
    prob = G.Problem(T, 4)
    err = 0.0
    for _ in range(1000):
        v = rng.uniform(0, 1, 8)
        p1 = strat_dist(*v[:4], trees)
        p2 = strat_dist(*v[4:], trees)
        A, B = prob.value(p1, p2)
        err = max(err, abs(A + B - F_closed(v)))
    print(f"(1) max |brute force - closed form| over 1000 random points: {err:.2e}")

    gstar = -minimize_scalar(lambda x: -x * h(x), bounds=(0, 1), method="bounded",
                             options={"xatol": 1e-12}).fun
    print(f"g* = max x h(x) = {gstar:.10f}")
    best = 0
    for _ in range(3000):
        r = minimize(lambda v: -F_closed(v), rng.uniform(0, 1, 8), method="L-BFGS-B",
                     bounds=[(0, 1)] * 8)
        best = max(best, -r.fun)
    print(f"(2) multistart max F = {best:.10f};  4 g* = {4 * gstar:.10f};  diff = {best - 4 * gstar:.2e}")

    # psi(g) = max_c [g h(c) + c h(g)]: stationary at log2((1-c)/c) = -h(g)/g
    def psi(g):
        g = np.asarray(g, float)
        with np.errstate(divide="ignore", over="ignore"):
            c = 1.0 / (1.0 + np.exp2(np.where(g > 0, -h(g) / np.maximum(g, 1e-300), -np.inf)))
        return g * h(c) + c * h(g)

    N = 61
    x = np.linspace(0, 1, N)
    a, b, g1, g2 = np.meshgrid(x, x, x, x, indexing="ij", sparse=True)
    Phi = (b * h(a) + a * h(b) + 2 * gstar * a * b + (1 - b) * psi(g2) + (1 - a) * psi(g1)
           - (1 - a) * (1 - b) * (g1 * h(g2) + g2 * h(g1)))
    i = np.unravel_index(np.argmax(Phi), Phi.shape)
    print(f"(3) grid {N}^4 max Phi = {Phi.max():.8f} at (a,b,g1,g2) = {[x[j] for j in i]};"
          f" 4 g* = {4 * gstar:.8f}")
    best = 0
    for _ in range(3000):
        f = lambda v: -float(v[1] * h(v[0]) + v[0] * h(v[1]) + 2 * gstar * v[0] * v[1]
                             + (1 - v[1]) * psi(v[3]) + (1 - v[0]) * psi(v[2])
                             - (1 - v[0]) * (1 - v[1]) * (v[2] * h(v[3]) + v[3] * h(v[2])))
        r = minimize(f, rng.uniform(0, 1, 4), method="L-BFGS-B", bounds=[(0, 1)] * 4)
        best = max(best, -r.fun)
    print(f"(3') multistart max Phi = {best:.10f}; diff to 4 g* = {best - 4 * gstar:.2e}")


if __name__ == "__main__":
    main()
