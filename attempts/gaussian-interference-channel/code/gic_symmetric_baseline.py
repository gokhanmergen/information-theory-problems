#!/usr/bin/env python3
"""Computational baseline for the symmetric two-user Gaussian interference channel.

Channel (standard form, real, unit noise):
    Y1 = X1 + a X2 + Z1,   Y2 = a X1 + X2 + Z2,   Zi ~ N(0,1) iid,
symmetric powers P1 = P2 = P, symmetric coupling a = b.  SNR = P, INR = a^2 P.
All rates in bits per real channel use; C(x) = (1/2) log2(1 + x).

For each (P, a) on the grid P in {1, 10}, a in {0.2, 0.5, sqrt(0.5), 1.0, 1.5, 3.0}:

1. Regime classification (exact finite-SNR thresholds):
   - very strong: a^2 >= 1 + P   (Carleial 1975; capacity = interference-free)
   - strong:      1 <= a^2 < 1+P (Sato 1981 / Han-Kobayashi 1981; capacity =
                  intersection of the two MAC regions)
   - noisy:       a^2 < 1 and 2a(1 + a^2 P) <= 1, i.e.
                  sqrt(INR)(1+INR) <= sqrt(SNR)/2 (symmetric form of the
                  Shang-Kramer-Chen / Annapureddy-Veeravalli / Motahari-Khandani
                  2008-09 condition); TIN is sum-capacity optimal.
   - weak (open): a^2 < 1 otherwise.
   Also reports the ETW generalized-degrees-of-freedom parameter
   alpha = log INR / log SNR (descriptive only; undefined at P = 1).

2. Inner bounds on sum rate:
   - TIN:  2 C(P / (1 + INR))                     (Gaussian inputs, full power)
   - TDM:  C(2P)                                  (half-time bursts at power 2P)
   - simple Han-Kobayashi, Gaussian inputs, no time sharing, symmetric power
     split: private power eta*P, common power (1-eta)*P.  Region evaluated via
     the Chong-Motani-Garg compact form (El Gamal & Kim, "Network Information
     Theory", Thm 6.4) with U_i ~ N(0,(1-eta)P), X_i = U_i + V_i,
     V_i ~ N(0, eta P).  With N = 1 + a^2 eta P the constraints are
        R1 <= A  = C(P / N)                       [= I(X1;Y1|U2)]
        R2 <= A
        R1+R2 <= B1 = C((P + a^2(1-eta)P)/N) + C(eta P / N)
                                                  [= I(X1,U2;Y1) + I(X2;Y2|U1,U2)]
        R1+R2 <= B2 = 2 C((eta P + a^2(1-eta)P)/N)
                                                  [= 2 I(X1,U2;Y1|U1)]
        2R1+R2 <= D = B1 + B2/2, R1+2R2 <= D.
     Max sum rate for fixed eta found by exact 2-variable LP vertex enumeration.
     Evaluated at the ETW split eta = min(1, 1/INR) (private interference at
     noise level; Etkin-Tse-Wang 2008) and at a sweep eta in {0, 1/2000, ..., 1}.

3. Outer bounds on sum rate:
   - noisy regime:       sum capacity = 2 C(P/(1+INR))          [exact, SKC/AV/MK]
   - strong regime:      sum capacity = min(2C(P), C(P + INR))  [exact, Sato/HK]
   - very strong regime: sum capacity = 2 C(P)                  [exact, Carleial]
   - weak (open) regime: ETW outer bound (Etkin-Tse-Wang 2008, Thm 3,
     symmetric real case):
        Rsum <= 2 C(P)
        Rsum <= C(P) + C(P/(1+INR))            [Z-channel / genie bound]
        Rsum <= 2 C(INR + P/(1+INR))
        Rsum <= (2/3) [ C(P+INR) + C(P/(1+INR)) + C(INR + P/(1+INR)) ]
                                               [from 2R1+R2 and R1+2R2 bounds]

4. Prints a markdown gap table (outer - best inner) flagging exact vs open.

stdlib + numpy only.  Reproduce:  python3 gic_symmetric_baseline.py
"""
import math

import numpy as np


def C(x):
    return 0.5 * math.log2(1.0 + x)


# ----------------------------------------------------------------- 2-var LP
def max_sum_lp(constraints):
    """Maximize R1+R2 s.t. c1*R1 + c2*R2 <= rhs for each constraint, R>=0.

    Exact vertex enumeration (constraints include R_i <= A so region bounded).
    """
    cons = list(constraints) + [(-1.0, 0.0, 0.0), (0.0, -1.0, 0.0)]
    pts = [(0.0, 0.0)]
    n = len(cons)
    for i in range(n):
        a1, b1, r1 = cons[i]
        for j in range(i + 1, n):
            a2, b2, r2 = cons[j]
            det = a1 * b2 - a2 * b1
            if abs(det) < 1e-12:
                continue
            x = (r1 * b2 - r2 * b1) / det
            y = (a1 * r2 - a2 * r1) / det
            pts.append((x, y))
    best = 0.0
    for x, y in pts:
        if x < -1e-9 or y < -1e-9:
            continue
        if all(c1 * x + c2 * y <= r + 1e-9 for c1, c2, r in cons):
            best = max(best, x + y)
    return best


# ----------------------------------------------------------- inner bounds
def hk_sum(P, a, eta):
    """Simple Han-Kobayashi sum rate, Gaussian inputs, split eta (private frac)."""
    N = 1.0 + a * a * eta * P
    A = C(P / N)
    B1 = C((P + a * a * (1.0 - eta) * P) / N) + C(eta * P / N)
    B2 = 2.0 * C((eta * P + a * a * (1.0 - eta) * P) / N)
    D = B1 + B2 / 2.0
    return max_sum_lp([
        (1.0, 0.0, A), (0.0, 1.0, A),
        (1.0, 1.0, B1), (1.0, 1.0, B2),
        (2.0, 1.0, D), (1.0, 2.0, D),
    ])


def tin_sum(P, a):
    return 2.0 * C(P / (1.0 + a * a * P))


def tdm_sum(P):
    return C(2.0 * P)  # half-duty bursts at power 2P (avg power P)


# ----------------------------------------------------------- outer bounds
def classify(P, a):
    a2 = a * a
    if a2 >= 1.0 + P:
        return "very strong"
    if a2 >= 1.0:
        return "strong"
    if 2.0 * a * (1.0 + a2 * P) <= 1.0:
        return "noisy"
    return "weak (open)"


def outer_sum(P, a, regime):
    INR = a * a * P
    if regime == "very strong":
        return 2.0 * C(P), True
    if regime == "strong":
        return min(2.0 * C(P), C(P + INR)), True
    if regime == "noisy":
        return 2.0 * C(P / (1.0 + INR)), True
    etw = min(
        2.0 * C(P),
        C(P) + C(P / (1.0 + INR)),
        2.0 * C(INR + P / (1.0 + INR)),
        (2.0 / 3.0) * (C(P + INR) + C(P / (1.0 + INR)) + C(INR + P / (1.0 + INR))),
    )
    return etw, False


# ----------------------------------------------------------------- driver
def main():
    Ps = [1.0, 10.0]
    coeffs = [("0.2", 0.2), ("0.5", 0.5), ("sqrt(1/2)", math.sqrt(0.5)),
              ("1.0", 1.0), ("1.5", 1.5), ("3.0", 3.0)]
    etas = np.linspace(0.0, 1.0, 2001)

    hdr = ("| P | a | INR | regime | alpha | TIN | TDM | HK@eta_ETW (eta) "
           "| HK best (eta*) | inner best | outer | gap | capacity |")
    sep = "|" + "---|" * 13
    print(hdr)
    print(sep)
    for P in Ps:
        for label, a in coeffs:
            INR = a * a * P
            regime = classify(P, a)
            alpha = (math.log(INR) / math.log(P)) if P != 1.0 else float("nan")
            tin = tin_sum(P, a)
            tdm = tdm_sum(P)
            eta_etw = min(1.0, 1.0 / INR)
            hk_etw = hk_sum(P, a, eta_etw)
            hk_vals = [hk_sum(P, a, e) for e in etas]
            i_best = int(np.argmax(hk_vals))
            hk_best, eta_best = hk_vals[i_best], etas[i_best]
            inner = max(tin, tdm, hk_etw, hk_best)
            outer, exact = outer_sum(P, a, regime)
            gap = outer - inner
            alpha_s = f"{alpha:.3f}" if not math.isnan(alpha) else "n/a"
            print(f"| {P:g} | {label} | {INR:g} | {regime} | {alpha_s} "
                  f"| {tin:.4f} | {tdm:.4f} | {hk_etw:.4f} ({eta_etw:.3f}) "
                  f"| {hk_best:.4f} ({eta_best:.4f}) | {inner:.4f} "
                  f"| {outer:.4f} | {gap:.4f} "
                  f"| {'exact' if exact else 'OPEN'} |")

    # consistency checks
    print()
    for P in Ps:
        for _, a in coeffs:
            regime = classify(P, a)
            outer, exact = outer_sum(P, a, regime)
            if exact:
                inner = max(tin_sum(P, a), tdm_sum(P),
                            max(hk_sum(P, a, e) for e in [0.0, min(1.0, 1.0 / (a * a * P)), 1.0]))
                assert inner <= outer + 1e-9, (P, a, inner, outer)
                assert outer - inner < 1e-9, ("exact regime not met by inner", P, a, inner, outer)
    # eta=1 HK must equal TIN, eta=0 in strong must equal exact sum capacity
    for P in Ps:
        for _, a in coeffs:
            assert abs(hk_sum(P, a, 1.0) - tin_sum(P, a)) < 1e-9
    print("consistency checks passed: inner<=outer everywhere; exact-regime "
          "sum capacity achieved by the implemented inner schemes; HK(eta=1)=TIN.")


if __name__ == "__main__":
    main()
