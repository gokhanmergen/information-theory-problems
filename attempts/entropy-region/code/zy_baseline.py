#!/usr/bin/env python3
"""Computational baseline for the entropy region Gamma*_4.

What this script does:

1. Exact entropy-vector computation: given an arbitrary finite joint pmf of
   four random variables (a 4-dimensional probability array), compute all 15
   subset entropies H(X_S), 0 != S subseteq {1,2,3,4}, in bits.

2. Zhang-Yeung (ZY98) non-Shannon inequality. Canonical form
   (Zhang-Yeung, IEEE Trans. IT 1998, Theorem 3; Yeung, "Information Theory
   and Network Coding", 2008, Theorem 15.7):

       2 I(X3;X4) <= I(X1;X2) + I(X1;X3,X4) + 3 I(X3;X4|X1) + I(X3;X4|X2).

   An LP over the Shannon cone Gamma_4 (28 elemental inequalities, normalized
   by H(X1X2X3X4) = 1) maximizes the ZY violation LHS - RHS.  The optimum is
   strictly positive; the optimizer is rounded to rationals and re-verified
   with exact fractions arithmetic, giving an exact certificate that ZY98 is
   NOT implied by the Shannon inequalities.

   A frequently misquoted variant,
       I(X3;X4) <= 2 I(X3;X4|X1) + I(X3;X4|X2) + I(X1;X2) + I(X1;X3,X4),
   is ALSO tested by LP: its optimum is 0, i.e. that variant IS
   Shannon-implied (a short proof is in the attempt file), so it is not the
   ZY inequality.

3. Sanity: ZY98 (and all 28 elemental inequalities) are checked on many
   random small joint distributions, and the entropy code is unit-tested on
   distributions with known entropy vectors.

Only numpy + scipy.optimize.linprog + stdlib fractions are used.
Run:  python3 zy_baseline.py
"""

import itertools
import random
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

N = 4
# Canonical order of the 15 nonempty subsets of {0,1,2,3} (0-indexed variables).
SUBSETS = [frozenset(c)
           for k in range(1, N + 1)
           for c in itertools.combinations(range(N), k)]
IDX = {s: i for i, s in enumerate(SUBSETS)}
FULL = frozenset(range(N))


def subset_name(s):
    return "H(" + "".join(str(i + 1) for i in sorted(s)) + ")"


# ---------------------------------------------------------------------------
# 1. Entropy vectors of arbitrary finite joint distributions of 4 variables
# ---------------------------------------------------------------------------

def entropy_vector(p):
    """All 15 subset entropies (bits) of a joint pmf given as a 4-d array."""
    p = np.asarray(p, dtype=float)
    assert p.ndim == N, "need a 4-dimensional array"
    assert abs(p.sum() - 1.0) < 1e-9 and (p >= -1e-12).all(), "not a pmf"
    h = np.zeros(len(SUBSETS))
    for s, i in IDX.items():
        axes = tuple(a for a in range(N) if a not in s)
        m = p.sum(axis=axes) if axes else p
        m = m[m > 0]
        h[i] = float(-(m * np.log2(m)).sum())
    return h


# ---------------------------------------------------------------------------
# Linear functionals on R^15 (convention H(emptyset) = 0)
# ---------------------------------------------------------------------------

def mi_vec(A, B, C=frozenset()):
    """Coefficient vector of I(X_A; X_B | X_C) as a functional of the h_S."""
    r = np.zeros(len(SUBSETS))

    def add(S, c):
        S = frozenset(S)
        if S:
            r[IDX[S]] += c

    A, B, C = frozenset(A), frozenset(B), frozenset(C)
    add(A | C, 1)
    add(B | C, 1)
    add(A | B | C, -1)
    add(C, -1)
    return r


def elemental_inequalities():
    """The 28 elemental Shannon inequalities for n=4 as rows r with r.h >= 0.

    (a) H(X_i | X_{[4]\\{i}}) >= 0                       -- 4 rows
    (b) I(X_i; X_j | X_K) >= 0,  i<j, K subseteq [4]\\{i,j} -- 6*4 = 24 rows
    These generate the full Shannon cone Gamma_4 (Yeung 2008, Sec. 14.2).
    """
    rows, labels = [], []
    for i in range(N):
        r = np.zeros(len(SUBSETS))
        r[IDX[FULL]] += 1
        r[IDX[FULL - {i}]] -= 1
        rows.append(r)
        labels.append(f"H(X{i+1}|rest)")
    for i, j in itertools.combinations(range(N), 2):
        rest = [k for k in range(N) if k not in (i, j)]
        for kk in range(len(rest) + 1):
            for K in itertools.combinations(rest, kk):
                rows.append(mi_vec({i}, {j}, frozenset(K)))
                cond = "".join(str(k + 1) for k in K)
                labels.append(f"I(X{i+1};X{j+1}" + (f"|X{cond})" if cond else ")"))
    return np.array(rows), labels


# Violation functionals: v.h > 0  <=>  the inequality is violated at h.
# Canonical ZY98:  v = 2I(3;4) - I(1;2) - I(1;34) - 3I(3;4|1) - I(3;4|2).
ZY_CANONICAL = (2 * mi_vec({2}, {3})
                - mi_vec({0}, {1})
                - mi_vec({0}, {2, 3})
                - 3 * mi_vec({2}, {3}, {0})
                - mi_vec({2}, {3}, {1}))

# Misquoted variant: v' = I(3;4) - 2I(3;4|1) - I(3;4|2) - I(1;2) - I(1;34).
ZY_VARIANT = (mi_vec({2}, {3})
              - 2 * mi_vec({2}, {3}, {0})
              - mi_vec({2}, {3}, {1})
              - mi_vec({0}, {1})
              - mi_vec({0}, {2, 3}))


# ---------------------------------------------------------------------------
# 2. LP over the Shannon cone + exact rational certificate
# ---------------------------------------------------------------------------

def maximize_violation(v, name):
    """max v.h  s.t.  E h >= 0 (28 elemental), h_{1234} = 1, 0 <= h <= 4."""
    E, _ = elemental_inequalities()
    A_ub = -E                      # E h >= 0  <=>  -E h <= 0
    b_ub = np.zeros(E.shape[0])
    A_eq = np.zeros((1, len(SUBSETS)))
    A_eq[0, IDX[FULL]] = 1.0
    b_eq = [1.0]
    res = linprog(-v, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, 4)] * len(SUBSETS), method="highs")
    assert res.status == 0, res.message
    print(f"LP max of ({name}) violation over Gamma_4, H(X1X2X3X4)=1: "
          f"{-res.fun:.10f}")
    return res, res.x, -res.fun


def certify_dual_exact(res, v, bound):
    """Exact dual certificate: rationals y >= 0 with
           v + sum_i y_i * E_i = bound * delta_{1234}.
    Then for every h with E h >= 0 and h_{1234} = 1:  v.h <= bound.
    Duals are read from the HiGHS marginals and re-verified from scratch in
    exact fractions arithmetic (the float LP is only used as a guess).
    """
    E, _ = elemental_inequalities()
    for sgn in (1, -1):
        y = [Fraction(float(sgn * m)).limit_denominator(64)
             for m in res.ineqlin.marginals]
        if any(t < 0 for t in y):
            continue
        resid = [Fraction(x).limit_denominator(1) for x in v]
        for yi, row in zip(y, E):
            for k, c in enumerate(row):
                resid[k] += yi * Fraction(c).limit_denominator(1)
        target = [Fraction(0)] * len(SUBSETS)
        target[IDX[FULL]] = bound
        if resid == target:
            print(f"  exact dual certificate found: v + sum y_i E_i = "
                  f"{bound} * delta_{{1234}}, all y_i >= 0  =>  "
                  f"max violation <= {bound} exactly")
            return True
    print("  no exact dual certificate recovered from marginals")
    return False


def certify_exact(h_rat, label):
    """Exact check with fractions: h_rat in Gamma_4 and its ZY98 violation."""
    E, labels = elemental_inequalities()
    E_rat = [[Fraction(x).limit_denominator(1) for x in row] for row in E]
    ok = True
    for row, lab in zip(E_rat, labels):
        val = sum(c * x for c, x in zip(row, h_rat))
        if val < 0:
            print(f"  ELEMENTAL VIOLATED: {lab} = {val}")
            ok = False
    v_rat = [Fraction(x).limit_denominator(1) for x in ZY_CANONICAL]
    viol = sum(c * x for c, x in zip(v_rat, h_rat))
    print(f"[{label}] all 28 elemental inequalities hold exactly: {ok}; "
          f"exact ZY98 violation LHS-RHS = {viol} "
          f"({'>0: ZY VIOLATED at this Gamma_4 point' if viol > 0 else '<=0'})")
    return ok and viol > 0


def rationalize(h, max_den=64):
    return [Fraction(x).limit_denominator(max_den) for x in h]


# ---------------------------------------------------------------------------
# 3. Sanity checks
# ---------------------------------------------------------------------------

def unit_tests():
    # (a) four independent uniform bits: H_S = |S|.
    p = np.full((2, 2, 2, 2), 1 / 16)
    h = entropy_vector(p)
    for s, i in IDX.items():
        assert abs(h[i] - len(s)) < 1e-12, (s, h[i])
    # (b) four identical copies of a uniform bit: H_S = 1 for all S.
    p = np.zeros((2, 2, 2, 2))
    p[0, 0, 0, 0] = p[1, 1, 1, 1] = 0.5
    h = entropy_vector(p)
    assert np.allclose(h, 1.0)
    # (c) X4 = X1 xor X2 xor X3, X1,X2,X3 iid uniform bits:
    #     H_S = min(|S|, 3) for all S.
    p = np.zeros((2, 2, 2, 2))
    for a, b, c in itertools.product(range(2), repeat=3):
        p[a, b, c, a ^ b ^ c] = 1 / 8
    h = entropy_vector(p)
    for s, i in IDX.items():
        assert abs(h[i] - min(len(s), 3)) < 1e-12, (s, h[i])
    print("unit tests on known entropy vectors: PASS")


def random_sanity(n_trials=400, seed=20260718):
    """Random joint pmfs: elemental and ZY98 must hold (both are theorems)."""
    rng = np.random.default_rng(seed)
    pyrng = random.Random(seed)
    E, _ = elemental_inequalities()
    worst_elem, worst_zy = np.inf, -np.inf
    for _ in range(n_trials):
        shape = tuple(pyrng.choice([2, 3]) for _ in range(N))
        alpha = pyrng.choice([0.05, 0.3, 1.0])
        p = rng.dirichlet(np.full(int(np.prod(shape)), alpha)).reshape(shape)
        if pyrng.random() < 0.3:   # sparsify to hit low-dimensional faces
            mask = rng.random(shape) < 0.5
            if (p * mask).sum() > 0:
                p = p * mask / (p * mask).sum()
        h = entropy_vector(p)
        worst_elem = min(worst_elem, float((E @ h).min()))
        worst_zy = max(worst_zy, float(ZY_CANONICAL @ h))
    print(f"random sanity ({n_trials} pmfs): min elemental slack = "
          f"{worst_elem:.3e} (>= -1e-9 expected), max ZY98 violation = "
          f"{worst_zy:.3e} (<= 1e-9 expected)")
    assert worst_elem >= -1e-9 and worst_zy <= 1e-9


# ---------------------------------------------------------------------------

def main():
    print("=== entropy-region baseline: Zhang-Yeung vs the Shannon cone ===\n")
    unit_tests()
    random_sanity()
    print()

    # LP for the canonical ZY98 inequality.
    res, x, opt = maximize_violation(ZY_CANONICAL, "canonical ZY98")
    assert opt > 1e-6, "expected a strictly positive gap"
    ok_dual = certify_dual_exact(res, ZY_CANONICAL, Fraction(1, 4))
    h_rat = rationalize(x)
    print("LP optimizer, rounded to rationals (order "
          + ", ".join(subset_name(s) for s in SUBSETS) + "):")
    print("  h = [" + ", ".join(str(f) for f in h_rat) + "]")
    ok_lp = certify_exact(h_rat, "LP point")
    print()

    # Independent hand-written certificate: the Ingleton/Vamos-type
    # polymatroid, scaled to H(X1X2X3X4)=1:
    #   h_i = 1/2, h_12 = 1, other pairs 3/4, all triples and the quad = 1.
    h_star = [Fraction(0)] * len(SUBSETS)
    for s, i in IDX.items():
        if len(s) == 1:
            h_star[i] = Fraction(1, 2)
        elif len(s) == 2:
            h_star[i] = Fraction(1) if s == frozenset({0, 1}) else Fraction(3, 4)
        else:
            h_star[i] = Fraction(1)
    print("Hand-written certificate point h* (same subset order):")
    print("  h* = [" + ", ".join(str(f) for f in h_star) + "]")
    ok_star = certify_exact(h_star, "h*")
    print()

    # LP for the misquoted variant: optimum should be 0 (Shannon-implied).
    res_var, _, opt_var = maximize_violation(ZY_VARIANT, "misquoted variant")
    certify_dual_exact(res_var, ZY_VARIANT, Fraction(0))
    print(f"  -> variant optimum {opt_var:.3e}: the variant is implied by "
          "the Shannon inequalities (gap 0), so it is NOT the ZY inequality.")
    print()

    if ok_lp and ok_star and opt > 1e-6:
        print("CONCLUSION [exact]: a rational point of Gamma_4 violating "
              "ZY98 has been certified with exact arithmetic; ZY98 is not "
              "implied by the Shannon inequalities."
              + (" The LP optimum 1/4 is also certified exactly via the "
                 "dual." if ok_dual else ""))
    else:
        print("CONCLUSION: certification FAILED; see messages above.")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
