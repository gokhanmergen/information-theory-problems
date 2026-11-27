#!/usr/bin/env python3
"""Time-sharing counterexample to  C = max(R_PDF, R_CF)  for the asymmetric
primitive BSC relay channel (attempt 2026-11-26-claude-opus-5-5-time-sharing-
and-first-order.md, Claims 2-4).

Part A (the proved instance, 50-digit mpmath arithmetic; every number printed
is a closed-form expression in binary entropies evaluated at rational points):
  p1 = 0.2 (destination), p2 = 0.1 (relay), R0 = 0.3.
  * lower bound on C(0.3) by time-sharing DF at pipe rate 0.2530 with CF
    (U = Yr, Slepian-Wolf) at pipe rate 0.8270;
  * upper bounds R_PDF <= 1-h(p2), R_CF <= 1-h(p1) + (1-2 p2) R0.
Part B (sanity checks of the two analytic lemmas, floating point):
  * Dobrushin coefficient of the reverse channel Yr -> X given Y=y is <= 1-2 p2
    for every input bias;
  * I(U;X|Y) <= (1-2p2) I(U;Yr|Y) on random test channels.
Part C (HEURISTIC): numerical CF curve via cf_dual.py and the size of the gap
  between max(R_PDF,R_CF) and its upper concave envelope.

Usage:  python3 lead1_time_sharing_counterexample.py [--skip-heuristic]
"""
from __future__ import annotations

import sys

import numpy as np
from mpmath import mp, mpf, log

mp.dps = 50


def hb(x):
    x = mpf(x)
    return -(x * log(x, 2) + (1 - x) * log(1 - x, 2))


def star(a, b):
    a, b = mpf(a), mpf(b)
    return a * (1 - b) + (1 - a) * b


def part_a():
    p1, p2, R0 = mpf("0.2"), mpf("0.1"), mpf("0.3")
    Ra_pipe, Rb_pipe, R_used = mpf("0.2530"), mpf("0.8270"), mpf("0.2999")
    df_threshold = hb(p1) - hb(p2)                 # h(p1)-h(p2)
    sw_threshold = hb(star(p1, p2))                # H(Yr|Y) = h(p1*p2)
    rate_df = 1 - hb(p2)                           # DF rate (all R < this)
    rate_cf = 1 + hb(star(p1, p2)) - hb(p1) - hb(p2)   # I(X;Y,Yr)
    lam = (Rb_pipe - R_used) / (Rb_pipe - Ra_pipe)
    ts_rate = lam * rate_df + (1 - lam) * rate_cf
    ub_pdf = 1 - hb(p2)
    ub_cf = 1 - hb(p1) + (1 - 2 * p2) * R0
    print("Part A: proved instance (p1,p2,R0) = (0.2,0.1,0.3)")
    print(f"  h(p1)-h(p2)          = {mp.nstr(df_threshold, 20)}  (< 0.2530: {df_threshold < Ra_pipe})")
    print(f"  h(p1*p2)=H(Yr|Y)     = {mp.nstr(sw_threshold, 20)}  (< 0.8270: {sw_threshold < Rb_pipe})")
    print(f"  DF rate 1-h(p2)      = {mp.nstr(rate_df, 20)}")
    print(f"  CF rate I(X;Y,Yr)    = {mp.nstr(rate_cf, 20)}")
    print(f"  lambda               = {mp.nstr(lam, 20)};  lambda*0.2530+(1-lambda)*0.8270 = "
          f"{mp.nstr(lam * Ra_pipe + (1 - lam) * Rb_pipe, 20)} < 0.3")
    print(f"  time-shared rate     = {mp.nstr(ts_rate, 20)}")
    print(f"  UB on R_PDF(0.3)     = {mp.nstr(ub_pdf, 20)}")
    print(f"  UB on R_CF(0.3)      = {mp.nstr(ub_cf, 20)}")
    gap = ts_rate - max(ub_pdf, ub_cf)
    print(f"  certified gap        = {mp.nstr(gap, 20)}  (positive: {gap > 0})")
    # Range of R0 on which the Dobrushin argument alone proves C > max(PDF,CF),
    # using the exact time-sharing line through (h(p1)-h(p2), 1-h(p2)) and
    # (h(p1*p2), I(X;Y,Yr)).
    slope = (rate_cf - rate_df) / (sw_threshold - df_threshold)
    r_star = (rate_df - slope * df_threshold - (1 - hb(p1))) / ((1 - 2 * p2) - slope)
    print(f"  Dobrushin argument works for R0 in ({mp.nstr(df_threshold, 8)}, {mp.nstr(r_star, 8)})")
    assert df_threshold < Ra_pipe and sw_threshold < Rb_pipe and gap > 0


def _h(x):
    x = np.clip(x, 1e-300, 1 - 1e-16)
    return -(x * np.log2(x) + (1 - x) * np.log2(1 - x))


def part_b(seed=1, trials=20000):
    rng = np.random.default_rng(seed)
    p1, p2 = 0.2, 0.1
    # Dobrushin coefficient of Yr -> X given Y = y, over a grid of input biases.
    worst_tv = 0.0
    for pi in np.linspace(1e-6, 1 - 1e-6, 20001):
        px = np.array([1 - pi, pi])
        for y in (0, 1):
            py_x = np.array([1 - p1, p1]) if y == 0 else np.array([p1, 1 - p1])
            rows = []
            for r in (0, 1):
                pr_x = np.array([1 - p2, p2]) if r == 0 else np.array([p2, 1 - p2])
                w = px * py_x * pr_x
                rows.append(w / w.sum())
            worst_tv = max(worst_tv, abs(rows[0][0] - rows[1][0]))
    print(f"Part B: max Dobrushin coefficient over grid = {worst_tv:.12f}  (1-2p2 = {1 - 2 * p2})")
    # Random test channels: I(U;X|Y) <= (1-2p2) I(U;Yr|Y).
    worst_ratio = 0.0
    for _ in range(trials):
        pi = rng.uniform(0.001, 0.999)
        k = rng.integers(2, 5)
        T = rng.dirichlet(np.full(k, 0.3), size=2)          # T[yr, u]
        px = np.array([1 - pi, pi])
        W1 = np.array([[1 - p1, p1], [p1, 1 - p1]])
        W2 = np.array([[1 - p2, p2], [p2, 1 - p2]])
        J = px[:, None, None, None] * W1[:, :, None, None] * W2[:, None, :, None] * T[None, None, :, :]
        J = np.clip(J, 1e-300, None)

        def H(P):
            P = P[P > 1e-300]
            return -(P * np.log2(P)).sum()
        Pxyu = J.sum(2); Pyu = Pxyu.sum(0); Pxy = Pxyu.sum(2); Py = Pxy.sum(0)
        Pyru = J.sum(0); Pyr_y = J.sum((0, 3))
        a = H(Pxy) + H(Pyu) - H(Pxyu) - H(Py)          # I(U;X|Y)
        b = H(Pyr_y) + H(Pyu) - H(Pyru) - H(Py)        # I(U;Yr|Y)
        if b > 1e-9:
            worst_ratio = max(worst_ratio, a / b)
    print(f"        max I(U;X|Y)/I(U;Yr|Y) over {trials} random test channels = {worst_ratio:.6f}"
          f"  (<= 1-2p2 = {1 - 2 * p2})")


def part_c():
    sys.path.insert(0, __file__.rsplit("/", 1)[0])
    import cf_dual
    p1, p2 = 0.2, 0.1
    D = float(hb(p1) - hb(p2))
    top = float(1 - hb(p2))
    print("Part C (heuristic): numerical CF and the concave envelope of max(PDF,CF)")
    # Tangent from the DF corner (D, top) to the CF curve.
    best = (-1.0, None, None)
    for R in np.concatenate([np.linspace(0.40, 0.83, 44), np.linspace(0.81, 0.83, 41)]):
        v = cf_dual.cf_rate(0.5, p1, p2, R)
        s = (v - top) / (R - D)
        if s > best[0]:
            best = (s, R, v)
    s, Rt, vt = best
    print(f"  tangent point R0~{Rt:.4f}, CF={vt:.6f}, envelope slope {s:.6f}")
    for R in (0.3, 0.4, 0.5, 0.6, 0.7, 0.8):
        cfu, pi_star = cf_dual.cf_rate_opt(p1, p2, R)
        df = min(1 - float(hb(p1)) + R, top)
        env = top + s * (R - D)
        print(f"  R0={R:.2f}: DF={df:.6f} CF={cfu:.6f} (pi*={pi_star:.3f}) "
              f"envelope={env:.6f} gap={env - max(df, cfu):.6f}")


if __name__ == "__main__":
    part_a()
    part_b()
    if "--skip-heuristic" not in sys.argv:
        part_c()
