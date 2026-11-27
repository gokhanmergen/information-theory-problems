#!/usr/bin/env python3
"""Sum rate of the *Lean* Gaussian Han-Kobayashi region (with time-sharing and
power control) at the four open grid points of the earlier baseline attempt,
plus a probe with non-Gaussian (discrete / Bernoulli-Gaussian) TIN schemes.

Lean objects (lean/InfoTheory/Problems/GaussianInterferenceChannel.lean):
  InGaussianHKBasic a b P1 P2 R1 R2  -- 7 linear constraints, Gaussian
      common/private powers P1c+P1p <= P1, P2c+P2p <= P2
  InGaussianHKRegion                 -- finite convex combinations of Basic
      points with per-phase powers (p1_i, p2_i) whose *averages* are <= (P1,P2)

For a linear objective the Region's support value is the upper concave envelope
of g(p1,p2) := max_{splits} max{R1+R2 : Basic(p1,p2)} evaluated at (P1,P2):
    S_Lean(P1,P2) = sup { sum_j l_j g(q_j) : l in simplex, sum_j l_j q_j <= (P1,P2) }.
We compute g on a grid of phase powers q_j in [0, PMAX]^2 (inner optimisation
over private-power fractions by grid + zoom), then solve the envelope LP exactly
(HiGHS).  Every reported number is a valid point of the Lean region, hence an
achievable sum rate (lower bound on S_Lean); optimality of the grid/zoom search
is NOT certified (heuristic upper side).

Closed form for fixed powers (2-variable LP, derived in the attempt file):
    max R1+R2 = min{ S, A1+A2, (A1+D2)/2, (D1+A2)/2, (D1+D2)/3 }
with A_i the single-rate bounds, S the min of the three sum bounds, D1, D2 the
2R1+R2 and R1+2R2 bounds.

Reproduce:  python3 gic_lean_region_sumrate.py     (numpy + scipy, ~1-3 min)
"""
import math

import numpy as np
from scipy.optimize import linprog

LOG2 = math.log(2.0)


def cap(x):
    return 0.5 * np.log2(1.0 + x)


def basic_maxsum(a, b, p1, p2, f1, f2):
    """Max R1+R2 over InGaussianHKBasic with full phase powers (p1,p2) and
    private fractions f1, f2 (arrays broadcast)."""
    P1p, P2p = f1 * p1, f2 * p2
    P1c, P2c = p1 - P1p, p2 - P2p
    a2, b2 = a * a, b * b
    N1 = 1 + a2 * P2p
    N2 = 1 + b2 * P1p
    A1 = cap((P1c + P1p) / N1)
    A2 = cap((P2c + P2p) / N2)
    s1 = cap((P1c + P1p + a2 * P2c) / N1) + cap(P2p / N2)
    s2 = cap(P1p / N1) + cap((P2c + P2p + b2 * P1c) / N2)
    s3 = cap((P1p + a2 * P2c) / N1) + cap((P2p + b2 * P1c) / N2)
    D1 = cap((P1c + P1p + a2 * P2c) / N1) + cap(P1p / N1) + cap((P2p + b2 * P1c) / N2)
    D2 = cap((P2c + P2p + b2 * P1c) / N2) + cap(P2p / N2) + cap((P1p + a2 * P2c) / N1)
    S = np.minimum(np.minimum(s1, s2), s3)
    return np.minimum.reduce([S, A1 + A2, (A1 + D2) / 2, (D1 + A2) / 2, (D1 + D2) / 3])


def g_full(a, b, p1, p2, n0=41, zooms=4):
    """max over private fractions of basic_maxsum (grid + zoom)."""
    lo1, hi1, lo2, hi2 = 0.0, 1.0, 0.0, 1.0
    best, bf = -1.0, (1.0, 1.0)
    for _ in range(zooms + 1):
        f1 = np.linspace(lo1, hi1, n0)
        f2 = np.linspace(lo2, hi2, n0)
        F1, F2 = np.meshgrid(f1, f2, indexing="ij")
        V = basic_maxsum(a, b, p1, p2, F1, F2)
        i, j = np.unravel_index(np.argmax(V), V.shape)
        if V[i, j] > best:
            best, bf = float(V[i, j]), (f1[i], f2[j])
        w1, w2 = (hi1 - lo1) / 4, (hi2 - lo2) / 4
        lo1, hi1 = max(0.0, bf[0] - w1), min(1.0, bf[0] + w1)
        lo2, hi2 = max(0.0, bf[1] - w2), min(1.0, bf[1] + w2)
    return best, bf


def lean_sum_rate(a, b, P1, P2, pmax_factor=4.0, ngrid=33):
    q1 = np.linspace(0.0, pmax_factor * P1, ngrid)
    q2 = np.linspace(0.0, pmax_factor * P2, ngrid)
    pts, vals, fr = [], [], []
    for x in q1:
        for y in q2:
            v, f = g_full(a, b, x, y)
            pts.append((x, y)); vals.append(v); fr.append(f)
    pts = np.array(pts); vals = np.array(vals)
    res = linprog(-vals, A_ub=pts.T, b_ub=[P1, P2],
                  A_eq=np.ones((1, len(vals))), b_eq=[1.0],
                  bounds=(0, None), method="highs")
    lam = res.x
    support = [(tuple(pts[k]), lam[k], vals[k], fr[k]) for k in np.argsort(-lam) if lam[k] > 1e-9]
    no_ts, f0 = g_full(a, b, P1, P2, n0=81, zooms=6)
    return -res.fun, support, no_ts, f0


# ------------------------------------------------------- reference values
def etw_outer_sym(P, a):
    INR = a * a * P
    C = lambda x: 0.5 * math.log2(1 + x)
    return min(2 * C(P), C(P) + C(P / (1 + INR)), 2 * C(INR + P / (1 + INR)),
               (2 / 3) * (C(P + INR) + C(P / (1 + INR)) + C(INR + P / (1 + INR))))


# --------------------------------------------- non-Gaussian TIN probes
def mixture_entropy_bits(atoms, weights, var, ngrid=20001):
    """Differential entropy (bits) of sum_k w_k N(atoms_k, var), by quadrature."""
    atoms = np.asarray(atoms, float); weights = np.asarray(weights, float)
    sd = math.sqrt(var)
    lo, hi = atoms.min() - 12 * sd, atoms.max() + 12 * sd
    y = np.linspace(lo, hi, ngrid)
    dens = (weights[None, :] * np.exp(-(y[:, None] - atoms[None, :]) ** 2 / (2 * var))
            ).sum(axis=1) / math.sqrt(2 * math.pi * var)
    with np.errstate(divide="ignore"):
        integrand = np.where(dens > 0, -dens * np.log(dens), 0.0)
    return float(np.trapezoid(integrand, y)) / LOG2


def pam(M, P):
    pts = np.arange(M) - (M - 1) / 2
    pts = pts * math.sqrt(P / np.mean(pts ** 2))
    return pts, np.full(M, 1.0 / M)


def tin_discrete_sym(P, a, M):
    """TIN sum rate, both users uniform M-PAM at power P (symmetric channel):
    2 [ h(X1 + a X2 + Z) - h(a X2 + Z) ]."""
    x, w = pam(M, P)
    y_atoms = (x[:, None] + a * x[None, :]).ravel()
    y_w = (w[:, None] * w[None, :]).ravel()
    i_atoms = a * x
    return 2 * (mixture_entropy_bits(y_atoms, y_w, 1.0)
                - mixture_entropy_bits(i_atoms, w, 1.0))


def gauss_var_mix_entropy_bits(vars_, weights, ngrid=40001):
    vars_ = np.asarray(vars_, float); weights = np.asarray(weights, float)
    sd = math.sqrt(vars_.max())
    y = np.linspace(-14 * sd, 14 * sd, ngrid)
    dens = (weights[None, :] * np.exp(-y[:, None] ** 2 / (2 * vars_[None, :]))
            / np.sqrt(2 * math.pi * vars_[None, :])).sum(axis=1)
    with np.errstate(divide="ignore"):
        integrand = np.where(dens > 0, -dens * np.log(dens), 0.0)
    return float(np.trapezoid(integrand, y)) / LOG2


def tin_onoff_sym(P, a, t):
    """TIN sum rate with independent randomized on-off Gaussian inputs:
    X_i = B_i G_i, B_i ~ Bern(t), G_i ~ N(0, P/t), B_1, B_2 unknown to receivers.
    Y1 = X1 + a X2 + Z is a 4-component zero-mean Gaussian variance mixture."""
    Q = P / t
    v = [1.0, 1.0 + Q, 1.0 + a * a * Q, 1.0 + Q + a * a * Q]
    w = [(1 - t) ** 2, t * (1 - t), (1 - t) * t, t * t]
    hy = gauss_var_mix_entropy_bits(v, w)
    hi = gauss_var_mix_entropy_bits([1.0, 1.0 + a * a * Q], [1 - t, t])
    return 2 * (hy - hi)


def main():
    pts = [(1.0, 0.5), (1.0, math.sqrt(0.5)), (10.0, 0.5), (10.0, math.sqrt(0.5))]
    prev_inner = {(1.0, 0.5): 0.8480, (1.0, math.sqrt(0.5)): 0.7925,
                  (10.0, 0.5): 2.1962, (10.0, math.sqrt(0.5)): 2.1962}
    print("| P | a | earlier inner best | Lean Basic, no TS (f1,f2) | Lean Region (TS+PC) "
          "| ETW outer | gap to outer | best TIN-PAM (M) | best TIN on-off (t) |")
    print("|---|---|---|---|---|---|---|---|---|")
    for P, a in pts:
        S, support, nots, f0 = lean_sum_rate(a, a, P, P)
        outer = etw_outer_sym(P, a)
        pam_best = max((tin_discrete_sym(P, a, M), M) for M in (2, 3, 4, 6, 8, 16))
        onoff_best = max((tin_onoff_sym(P, a, t), t) for t in np.linspace(0.05, 1.0, 39))
        al = "0.5" if abs(a - 0.5) < 1e-12 else "sqrt(1/2)"
        print(f"| {P:g} | {al} | {prev_inner[(P, a)]:.4f} | {nots:.4f} ({f0[0]:.3f},{f0[1]:.3f}) "
              f"| {S:.4f} | {outer:.4f} | {outer - S:.4f} | {pam_best[0]:.4f} ({pam_best[1]}) "
              f"| {onoff_best[0]:.4f} ({onoff_best[1]:.3f}) |")
        for (q, lam, v, fr) in support:
            print(f"      phase: weight {lam:.4f}, powers ({q[0]:.3f},{q[1]:.3f}), "
                  f"basic sum {v:.4f}, private fractions ({fr[0]:.3f},{fr[1]:.3f})")
    # Consistency of the Lean region with known exact sum capacities: the
    # region's sum rate (TS+PC envelope) must EQUAL the known sum capacity
    # (it cannot exceed it if InGaussianHKRegion is sound, and must reach it if
    # the region reproduces the known result).
    C = lambda x: 0.5 * math.log2(1 + x)
    cases = [
        ("noisy (SKC/MK/AV), P=1,a=b=0.2", 0.2, 0.2, 1.0, 1.0,
         2 * C(1.0 / (1 + 0.04))),
        ("strong (Sato/HK), P=10,a=b=1.5", 1.5, 1.5, 10.0, 10.0,
         min(2 * C(10.0), C(10.0 + 2.25 * 10.0))),
        ("very strong (Carleial), P=1,a=b=3", 3.0, 3.0, 1.0, 1.0, 2 * C(1.0)),
        ("weak Z (Costa/Sason), P1=P2=10,a=0.5,b=0", 0.5, 0.0, 10.0, 10.0,
         C(10.0) + C(10.0 / (1 + 0.25 * 10.0))),
        ("mixed (Motahari-Khandani), P=10,a=1.5,b=0.5", 1.5, 0.5, 10.0, 10.0,
         min(C(10.0) + C(10.0 / (1 + 0.25 * 10.0)), C(10.0 + 2.25 * 10.0))),
    ]
    print()
    print("| case | known sum capacity | Lean Region sum (TS+PC) | difference |")
    print("|---|---|---|---|")
    for name, a_, b_, P1_, P2_, known in cases:
        S_, _, _, _ = lean_sum_rate(a_, b_, P1_, P2_)
        print(f"| {name} | {known:.6f} | {S_:.6f} | {S_ - known:+.2e} |")
        assert S_ <= known + 1e-9, ("Lean region exceeds a known sum capacity", name)
        assert known - S_ < 1e-6, ("Lean region misses a known sum capacity", name)
    # sanity checks: Basic reproduces TIN and the strong-interference sum capacity
    P = 10.0
    t = float(basic_maxsum(0.5, 0.5, P, P, 1.0, 1.0))
    assert abs(t - 2 * 0.5 * math.log2(1 + P / (1 + 0.25 * P))) < 1e-12
    s = float(basic_maxsum(1.5, 1.5, P, P, 0.0, 0.0))
    assert abs(s - min(math.log2(1 + P), 0.5 * math.log2(1 + P + 2.25 * P))) < 1e-12
    print("sanity: Basic(all private)=TIN and Basic(all common, strong)=MAC-intersection sum: OK")


if __name__ == "__main__":
    main()
