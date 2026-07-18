#!/usr/bin/env python3
"""Endpoint lemmas for the full n=4 Courtade-Kumar theorem, verified in exact
rational arithmetic (stdlib fractions only; no floating point in any check).

Together with interval certification on [1/1000, 0.495] (certify_n4.py), these
prove: for n=4 and ALL alpha in (0, 1/2), every Boolean f satisfies
I(f(X);Y) <= 1 - h(alpha).

LOW-NOISE LEMMA, alpha in (0, 1/1000].
  Let k = |f^{-1}(1)|, q = k/16, b_y = #{neighbors x of y with f(x) != f(y)},
  c1 = (1/16) sum_y b_y = 2B/16, c2 = (1/16) sum_y b_y log2(b_y).
  Chain (each step proved in the attempt write-up):
    (i)   H(f(X)|Y) >= (1/16) sum_y h(b_y beta),  beta = alpha(1-alpha)^3
          [P(f(X) != f(y) | Y=y) >= b_y beta, both sides <= 1/2, h increasing]
    (ii)  h(u) >= u log2(1/u)
    (iii) h(alpha) <= alpha (log2(1/alpha) + log2 e)
  give, with t = log2(1/alpha) and gamma = (999/1000)^3 <= ((1-alpha)^3/1):
    D(alpha) := h(alpha) - (1/16) sum_y h(b_y beta)
              <= alpha [ t (1 - gamma c1) + log2 e + c2 ].
  Since g = (1 - h) - H(q) + H(f|Y) = m0 - D with m0 = 1 - H(q):
    * balanced (k=8, m0=0):  need t0 (gamma c1 - 1) >= log2 e + c2
      at t0 = lower bound on log2(1000)  [t-coefficient negative, t >= t0]
    * unbalanced: D <= (1/1000)[ t0' max(0, 1-gamma c1) + log2 e + c2 ] <= m0
      at t0' = upper bound on log2(1000)  [alpha*t increasing on (0, 1/e)]
  Constants k in {0,16} (f constant) are trivial: I = 0.

HIGH-NOISE LEMMA, rho = 1-2alpha in (0, 1/100].
  With hat(S) the Fourier coefficients of the indicator 1_f:
    chi^2 = (sum_{S != 0} hat(S)^2 rho^{2|S|}) / (q0 q1)
         <= rho^2 [ W1t + rho^2 (1 - W1t) ],   W1t = sum_{|S|=1} hat(S)^2/(q0 q1)
  (uses sum_{S != 0} hat(S)^2 = q0 q1 exactly), and
    |eps_{v,y}| = |p(v,y)/(q_v p_y) - 1| <= rho A / qmin,  A = sum_{S!=0}|hat(S)|.
  Scalar inequality (proved by series in the write-up): for |eps| <= 1/2,
    (1+eps) ln(1+eps) <= eps + eps^2/2 + (2/3)|eps|^3.
  Summing against q_v p_y (the linear terms cancel exactly):
    I(f;Y) ln 2 <= (chi^2/2)(1 + (4/3) eps_max).
  Against 1 - h(alpha) >= rho^2/(2 ln 2) (exact positive series), suffices:
    [ W1t + rho0^2 (1 - W1t) ] (1 + (4/3) rho0 A / qmin) <= 1   at rho0 = 1/100
  (monotone in rho), plus the check rho0 A / qmin <= 1/2.

Every non-dictator NPN class must pass; dictators have I = 1-h exactly.
"""
import sys
from fractions import Fraction as F
from itertools import permutations

N, SIZE = 4, 16

# rational bounds: LO[x] <= log2(x) <= HI[x]
LOG2_LO = {3: F(15849, 10000), 5: F(23219, 10000), 7: F(28073, 10000),
           11: F(34594, 10000), 13: F(37004, 10000)}
LOG2_HI = {3: F(15850, 10000), 5: F(23220, 10000), 7: F(28074, 10000),
           11: F(34595, 10000), 13: F(37005, 10000)}
LOG2E_HI = F(14427, 10000)          # log2(e) <= 1.4427
T0_LO = F(99657, 10000)             # log2(1000) >= 9.9657
T0_HI = F(99658, 10000)             # log2(1000) <= 9.9658
ALPHA0 = F(1, 1000)
RHO0 = F(1, 100)
GAMMA = (F(999, 1000)) ** 3


def verify_log_bounds():
    """Prove every hard-coded logarithm enclosure using integer arithmetic."""
    for n in LOG2_LO:
        lo, hi = LOG2_LO[n], LOG2_HI[n]
        # lo <= log2(n) <= hi, after raising 2 and n to integer powers.
        assert 2 ** lo.numerator <= n ** lo.denominator
        assert n ** hi.denominator <= 2 ** hi.numerator
    assert 2 ** T0_LO.numerator <= 1000 ** T0_LO.denominator
    assert 1000 ** T0_HI.denominator <= 2 ** T0_HI.numerator
    # ln(2) = 2 * sum_{j>=0} 1/((2j+1)3^(2j+1)).  A partial sum is a
    # rigorous lower bound; ln(2) >= 1/LOG2E_HI proves log2(e) <= LOG2E_HI.
    ln2_lower = sum((F(2, (2*j + 1) * 3 ** (2*j + 1))
                     for j in range(20)), F(0))
    assert ln2_lower >= 1 / LOG2E_HI


def log2_bounds(n):
    """(lower, upper) rational bounds for log2(n), n = 1..16."""
    lo = hi = F(0)
    m = n
    for p in (2, 3, 5, 7, 11, 13):
        while m % p == 0:
            m //= p
            if p == 2:
                lo += 1
                hi += 1
            else:
                lo += LOG2_LO[p]
                hi += LOG2_HI[p]
    assert m == 1
    return lo, hi


def npn_classes():
    maps = []
    for perm in permutations(range(N)):
        for flips in range(SIZE):
            maps.append([sum((((x ^ flips) >> perm[i]) & 1) << i
                             for i in range(N)) for x in range(SIZE)])
    seen = bytearray(1 << SIZE)
    reps = []
    for f in range(1 << SIZE):
        if seen[f]:
            continue
        orbit = set()
        for m in maps:
            g = 0
            for x in range(SIZE):
                if (f >> m[x]) & 1:
                    g |= 1 << x
            orbit.add(g)
            orbit.add(g ^ 0xFFFF)
        for g in orbit:
            seen[g] = 1
        reps.append(min(orbit))
    return reps


def profile(f):
    """(k, b_y list) for the class representative."""
    b = [sum(1 for i in range(N)
             if ((f >> y) & 1) != ((f >> (y ^ (1 << i))) & 1))
         for y in range(SIZE)]
    return bin(f).count('1'), b


def H_upper(k):
    """Rational upper bound on H(k/16) = 4 - (k log2 k + (16-k) log2(16-k))/16."""
    lo_k, _ = log2_bounds(k) if k else (F(0), F(0))
    lo_j, _ = log2_bounds(16 - k) if 16 - k else (F(0), F(0))
    return 4 - (k * lo_k + (16 - k) * lo_j) / 16


def low_noise_ok(k, b):
    c1 = F(sum(b), 16)
    c2 = sum(F(by, 16) * log2_bounds(by)[1] for by in b if by)
    if k == 8:
        return T0_LO * (GAMMA * c1 - 1) >= LOG2E_HI + c2
    m0 = 1 - H_upper(k)
    tcoef = 1 - GAMMA * c1
    dmax = ALPHA0 * ((T0_HI * tcoef if tcoef > 0 else F(0)) + LOG2E_HI + c2)
    return dmax <= m0


def fourier_ind(f):
    """Exact Fourier coefficients of 1_f over {0,1}^4, hat(S) for S=0..15."""
    return [F(sum((1 if (f >> x) & 1 else 0) *
                  (-1) ** bin(x & S).count('1') for x in range(SIZE)), SIZE)
            for S in range(SIZE)]


def high_noise_ok(k, f):
    q1, q0 = F(k, 16), F(16 - k, 16)
    hat = fourier_ind(f)
    w1 = sum(hat[1 << i] ** 2 for i in range(N)) / (q0 * q1)
    A = sum(abs(hat[S]) for S in range(1, SIZE))
    eps = RHO0 * A / min(q0, q1)
    if eps > F(1, 2):
        return False
    val = (w1 + RHO0 ** 2 * (1 - w1)) * (1 + F(4, 3) * eps)
    return val <= 1


if __name__ == "__main__":
    verify_log_bounds()
    print("hard-coded logarithm bounds: ALL VERIFIED by exact integers/rationals")
    reps = npn_classes()
    print(f"NPN classes: {len(reps)}")
    fail_low, fail_high, checked = [], [], 0
    for f in reps:
        k, b = profile(f)
        if k in (0, 16):
            continue                       # constants: I = 0, trivial
        hat = fourier_ind(f)
        w1n = sum(hat[1 << i] ** 2 for i in range(N)) / (F(k, 16) * F(16 - k, 16))
        if w1n == 1:
            print(f"class {f:#06x}: dictator (equality case), excluded")
            continue
        checked += 1
        if not low_noise_ok(k, b):
            fail_low.append(f)
        if not high_noise_ok(k, f):
            fail_high.append(f)
    print(f"checked {checked} non-constant non-dictator classes")
    print(f"low-noise lemma  (alpha in (0, 1/1000]) : "
          f"{'ALL PASS' if not fail_low else 'FAILURES: ' + str([hex(x) for x in fail_low])}")
    print(f"high-noise lemma (rho in (0, 1/100])    : "
          f"{'ALL PASS' if not fail_high else 'FAILURES: ' + str([hex(x) for x in fail_high])}")
    sys.exit(1 if (fail_low or fail_high) else 0)
