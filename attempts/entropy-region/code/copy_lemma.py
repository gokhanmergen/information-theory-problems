#!/usr/bin/env python3
"""Copy-lemma LP machinery for the entropy region Gamma*_4.

Extends attempts/entropy-region/code/zy_baseline.py (same entropy-vector and
LP conventions, generalized from n=4 to arbitrary n).

The Copy Lemma (Dougherty-Freiling-Zeger, arXiv:1104.3602, Lemma 2; essentially
Zhang-Yeung 1998): for jointly distributed (X_V) and disjoint Y, Z subseteq V,
there exists a new random variable R ("a copy of X_Y over X_Z") with

    C1:  (X_Z, R) ~ (X_Z, X_Y)      (identical joint marginal distribution)
    C2:  I(R ; X_{V \\ Z} | X_Z) = 0.

(DFZ state it for Y a single group C over Z = (A,B) with C2 = I(CD;R|AB)=0;
applying their lemma to the grouped variable X_Y gives exactly this form.)

Entropy consequences of C1/C2 are LINEAR equalities on the (2^{n+1}-1)-dim
entropy vector after adjoining R:

    h(T u {R}) = h(T u Y)   for all T subseteq Z          (from C1)
    h(Z u {R}) + h(V) - h(V u {R}) - h(Z) = 0             (C2)

Hence: for any candidate 4-variable inequality  v . h <= 0,  if

    max { v.h : h in Gamma_n (Shannon cone, n = 4 + #copies),
                copy equalities C h = 0 }  =  0,

then v.h <= 0 holds on all of Gamma*_4 (every entropic 4-vector extends, by
the Copy Lemma, to an entropic n-vector satisfying C h = 0, and Gamma*_n is
inside the Shannon cone).  The LP dual gives the proof object: rationals
y >= 0 (one per elemental Shannon inequality) and mu (free, one per copy
equality) with

    v + sum_i y_i E_i + sum_j mu_j C_j = 0        (identity in R^{2^n - 1})

which is verified here in EXACT Fraction arithmetic (floats are only used
inside the LP solver as a guess generator, exactly as in zy_baseline.py).

What main() does:

 1. Re-checks the baseline: max ZY98 violation over Gamma_4 alone is 1/4.
 2. Re-derives ZY98 with ONE copy (R = a copy of A over (C,D); this is
    DFZ's Section III derivation transported to the canonical Theorem-1
    form by the swap C<->A, B<->D): LP optimum 0, exact certificate.
 3. Negative control: the (false) Ingleton inequality must NOT be certified
    by any single-copy spec, and is not certified by the two-copy specs used
    below (a bug that "proved" Ingleton would be caught here).
 4. Certifies three of the six DFZ-2006 two-copy inequalities
    (arXiv:1104.3602 Section V, eqs (37), (40), (42)) exactly, with two
    copy variables; also screens the other three.
 5. Confirms (float LP + exact rational primal witnesses where rounding
    succeeds) that none of the six DFZ inequalities is provable with a
    single copy variable, matching DFZ's statement that ZY98 is the only
    one-copy inequality.
 6. Small search over the DFZ coefficient family for candidates not implied
    by Shannon + one copy; results (whatever they are) are printed.

Run:  nice -n 19 python3 copy_lemma.py        (a few minutes)
"""

import itertools
import random
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

# ---------------------------------------------------------------------------
# Entropy-space worlds (generalization of the n=4 machinery in zy_baseline.py)
# ---------------------------------------------------------------------------

VARNAMES = "ABCDRS"  # 0=A,1=B,2=C,3=D, 4=first copy R, 5=second copy S


def _subsets(n):
    return [frozenset(c)
            for k in range(1, n + 1)
            for c in itertools.combinations(range(n), k)]


class World:
    """Entropy space of n jointly distributed variables: R^{2^n - 1}."""

    def __init__(self, n):
        self.n = n
        self.subs = _subsets(n)
        self.idx = {s: i for i, s in enumerate(self.subs)}
        self.full = frozenset(range(n))
        self.dim = len(self.subs)
        self._elem = None

    def name(self, s):
        return "".join(VARNAMES[i] for i in sorted(s))

    def mi(self, A, B, C=()):
        """Coefficient vector of I(X_A; X_B | X_C) (convention h(empty)=0)."""
        r = np.zeros(self.dim)
        A, B, C = frozenset(A), frozenset(B), frozenset(C)
        for S, c in ((A | C, 1), (B | C, 1), (A | B | C, -1), (C, -1)):
            if S:
                r[self.idx[S]] += c
        return r

    def elemental(self):
        """Elemental Shannon inequalities: rows r with r.h >= 0.

        n + C(n,2)*2^(n-2) rows (28 for n=4, 85 for n=5, 246 for n=6);
        they generate the full Shannon cone Gamma_n (Yeung 2008, Sec. 14.2).
        """
        if self._elem is not None:
            return self._elem
        rows, labels = [], []
        for i in range(self.n):
            r = np.zeros(self.dim)
            r[self.idx[self.full]] += 1
            r[self.idx[self.full - {i}]] -= 1
            rows.append(r)
            labels.append(f"H({VARNAMES[i]}|rest)")
        for i, j in itertools.combinations(range(self.n), 2):
            rest = [k for k in range(self.n) if k not in (i, j)]
            for kk in range(len(rest) + 1):
                for K in itertools.combinations(rest, kk):
                    rows.append(self.mi({i}, {j}, K))
                    cond = self.name(K)
                    labels.append(f"I({VARNAMES[i]};{VARNAMES[j]}"
                                  + (f"|{cond})" if cond else ")"))
        self._elem = (np.array(rows), labels)
        return self._elem

    def lift(self, v_small, small):
        """Embed a functional on a sub-world (vars 0..small.n-1) into self."""
        r = np.zeros(self.dim)
        for s, i in small.idx.items():
            r[self.idx[s]] = v_small[i]
        return r


W4, W5, W6 = World(4), World(5), World(6)


def copy_rows(world, old_vars, new, Y, Z):
    """Entropy equalities for: new variable `new` is a copy of X_Y over X_Z.

    old_vars = variables existing before this step; Y, Z disjoint subsets of
    old_vars, Y nonempty.  Returns rows r (in `world` coordinates) with
    r.h = 0, plus labels.
    """
    old_vars, Y, Z = frozenset(old_vars), frozenset(Y), frozenset(Z)
    assert Y and not (Y & Z) and (Y | Z) <= old_vars and new not in old_vars
    rows, labels = [], []
    for k in range(len(Z) + 1):
        for T in itertools.combinations(sorted(Z), k):
            T = frozenset(T)
            r = np.zeros(world.dim)
            r[world.idx[T | {new}]] += 1
            r[world.idx[T | Y]] -= 1
            rows.append(r)
            labels.append(f"H({world.name(T | {new})})=H({world.name(T | Y)})")
    # C2: I(new ; old_vars \ Z | Z) = 0
    r = np.zeros(world.dim)
    r[world.idx[Z | {new}]] += 1
    r[world.idx[old_vars]] += 1
    r[world.idx[old_vars | {new}]] -= 1
    if Z:
        r[world.idx[Z]] -= 1
    rows.append(r)
    labels.append(f"I({VARNAMES[new]};{world.name(old_vars - Z)}"
                  + (f"|{world.name(Z)})=0" if Z else ")=0"))
    return np.array(rows), labels


# ---------------------------------------------------------------------------
# The inequalities (violation functionals: v.h > 0 <=> violated at h)
# ---------------------------------------------------------------------------

A_, B_, C_, D_ = {0}, {1}, {2}, {3}

# Canonical ZY98 (DFZ Theorem 1): 2I(C;D) <= I(A;B)+I(A;CD)+3I(C;D|A)+I(C;D|B)
# Same functional as zy_baseline.py's ZY_CANONICAL under (X1..X4)=(A,B,C,D).
ZY = (2 * W4.mi(C_, D_) - W4.mi(A_, B_) - W4.mi(A_, C_ | D_)
      - 3 * W4.mi(C_, D_, A_) - W4.mi(C_, D_, B_))

# Ingleton (FALSE as an information inequality; negative control):
# I(C;D) <= I(C;D|A) + I(C;D|B) + I(A;B).
INGLETON = (W4.mi(C_, D_) - W4.mi(C_, D_, A_) - W4.mi(C_, D_, B_)
            - W4.mi(A_, B_))


def dfz_family(a, b, c, d, e, f, g):
    """2I(A;B) <= a I(A;B|C)+b I(A;C|B)+c I(B;C|A)+d I(A;B|D)+e I(A;D|B)
                 +f I(B;D|A)+g I(C;D)   (DFZ 2011, Section V family)."""
    return (2 * W4.mi(A_, B_)
            - a * W4.mi(A_, B_, C_) - b * W4.mi(A_, C_, B_)
            - c * W4.mi(B_, C_, A_) - d * W4.mi(A_, B_, D_)
            - e * W4.mi(A_, D_, B_) - f * W4.mi(B_, D_, A_)
            - g * W4.mi(C_, D_))


# The six DFZ-2006 two-copy inequalities, arXiv:1104.3602 eqs (37)-(42):
DFZ_SIX = {
    "DFZ(37)": (5, 3, 1, 2, 0, 0, 2),
    "DFZ(38)": (4, 2, 1, 3, 1, 0, 2),
    "DFZ(39)": (4, 4, 1, 2, 1, 1, 2),
    "DFZ(40)": (3, 3, 3, 2, 0, 0, 2),
    "DFZ(41)": (3, 4, 2, 3, 1, 0, 2),
    "DFZ(42)": (3, 2, 2, 2, 1, 1, 2),
}


# ---------------------------------------------------------------------------
# LP: screen (float) and certify (exact rationals)
# ---------------------------------------------------------------------------

NORM_4 = frozenset(range(4))  # normalize by H(ABCD) = 1


def screen(v4, world, eq_rows, extra_ineq=None):
    """Float LP:  max v.h  over  {h in Gamma_world : eq_rows h = 0, H(ABCD)=1}.

    extra_ineq: optional additional rows r with r.h >= 0 (instances of
    already-certified valid inequalities).  Returns (opt, x).
    opt ~ 0 => candidate for exact certification;
    opt > 0 => this copy spec cannot prove v.h <= 0.
    """
    E, _ = world.elemental()
    if extra_ineq is not None and len(extra_ineq):
        E = np.vstack([E, extra_ineq])
    v = world.lift(v4, W4)
    A_eq = [np.zeros(world.dim)]
    A_eq[0][world.idx[NORM_4]] = 1.0
    b_eq = [1.0]
    if len(eq_rows):
        A_eq = np.vstack([A_eq, eq_rows])
        b_eq = b_eq + [0.0] * len(eq_rows)
    res = linprog(-v, A_ub=-E, b_ub=np.zeros(E.shape[0]),
                  A_eq=np.asarray(A_eq), b_eq=b_eq,
                  bounds=[(0, 16)] * world.dim, method="highs")
    assert res.status == 0, res.message
    return -res.fun, res.x


def _to_int_matrix(M):
    Mi = np.rint(M).astype(int)
    assert M.size == 0 or np.abs(M - Mi).max() < 1e-9
    return Mi


DENOM_LADDER = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256,
                384, 512, 1024, 4096, 65536, 2**20]


def verify_certificate(v_int, E_int, C_int, y, mu):
    """Exact check: y >= 0 and v + sum y_i E_i + sum mu_j C_j = 0 (all coords)."""
    if any(t < 0 for t in y):
        return False
    dim = len(v_int)
    resid = [Fraction(int(v_int[k])) for k in range(dim)]
    for yi, row in zip(y, E_int):
        if yi:
            for k in range(dim):
                if row[k]:
                    resid[k] += yi * int(row[k])
    for mj, row in zip(mu, C_int):
        if mj:
            for k in range(dim):
                if row[k]:
                    resid[k] += mj * int(row[k])
    return all(t == 0 for t in resid)


def _exact_solve(cols, b):
    """Solve (columns) x = b exactly over Fractions; free vars set to 0.

    cols: list of length-dim integer vectors; b: length-dim Fractions.
    Returns list of Fractions x with sum x_k cols[k] = b, or None.
    """
    dim, K = len(b), len(cols)
    M = [[Fraction(int(cols[k][r])) for k in range(K)] + [b[r]]
         for r in range(dim)]
    piv_col_of_row, r = {}, 0
    for c in range(K):
        piv = next((i for i in range(r, dim) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = 1 / M[r][c]
        M[r] = [t * inv for t in M[r]]
        for i in range(dim):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [ti - f * tr for ti, tr in zip(M[i], M[r])]
        piv_col_of_row[r] = c
        r += 1
        if r == dim:
            break
    for i in range(r, dim):
        if M[i][K] != 0:
            return None  # inconsistent
    x = [Fraction(0)] * K
    for row, c in piv_col_of_row.items():
        x[c] = M[row][K]
    return x


def certify(v4, world, eq_rows, label, verbose=True, extra=None):
    """Exact rational certificate that v4.h <= 0 on {Gamma_world, eq_rows h=0}.

    extra: optional (rows, labels) of additional valid inequality rows
    (r.h >= 0; instances of already-certified inequalities) that may be used
    with nonnegative multipliers -- the certificate is then *relative* to
    those inequalities.  Solves the dual-form LP
    min sum(y) s.t. E^T y + C^T mu = -v, y >= 0, then makes it exact:
    (a) round duals over a denominator ladder, or (b) exact Fraction
    Gaussian elimination on the float solution's support.
    Returns (y, mu) as Fractions on success, None on failure.
    """
    E, elab = world.elemental()
    elab = list(elab)
    if extra is not None and len(extra[0]):
        E = np.vstack([E, extra[0]])
        elab = elab + list(extra[1])
    C = np.asarray(eq_rows)
    v = world.lift(v4, W4)
    v_int, E_int = _to_int_matrix(v), _to_int_matrix(E)
    C_int = _to_int_matrix(C)
    mE, mC = E.shape[0], C.shape[0]
    A_eq = np.hstack([E.T, C.T])           # dim x (mE + mC)
    b_eq = -v
    cost = np.concatenate([np.ones(mE), np.zeros(mC)])
    res = linprog(cost, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(0, None)] * mE + [(None, None)] * mC,
                  method="highs")
    if res.status != 0:
        if verbose:
            print(f"  [{label}] no dual certificate (LP status {res.status}:"
                  f" {res.message.splitlines()[0]})")
        return None
    yf, mf = res.x[:mE], res.x[mE:]
    # (a) rounding ladder
    for den in DENOM_LADDER:
        y = [Fraction(t).limit_denominator(den) for t in yf]
        mu = [Fraction(t).limit_denominator(den) for t in mf]
        if verify_certificate(v_int, E_int, C_int, y, mu):
            return _report(label, elab, y, mu, verbose)
    # (b) exact solve on the support of the float solution
    supp = [i for i in range(mE) if yf[i] > 1e-9]
    cols = [E_int[i] for i in supp] + [C_int[j] for j in range(mC)]
    b = [Fraction(-int(v_int[k])) for k in range(world.dim)]
    x = _exact_solve(cols, b)
    if x is not None:
        y = [Fraction(0)] * mE
        for i, s in enumerate(supp):
            y[s] = x[i]
        mu = x[len(supp):]
        if verify_certificate(v_int, E_int, C_int, y, mu):
            return _report(label, elab, y, mu, verbose)
    if verbose:
        print(f"  [{label}] float dual found but exact reconstruction FAILED")
    return None


def _report(label, elab, y, mu, verbose):
    if verbose:
        nz = [(elab[i], y[i]) for i in range(len(y)) if y[i] != 0]
        print(f"  [{label}] EXACT certificate: v + sum y_i E_i + sum mu_j C_j"
              f" = 0 verified in Fraction arithmetic;"
              f" {len(nz)} nonzero Shannon multipliers, "
              f"{sum(1 for m in mu if m != 0)} nonzero copy multipliers")
        print("    y: " + ", ".join(f"{l}:{q}" for l, q in nz))
        print("    mu: " + ", ".join(str(q) for q in mu))
    return y, mu


def exact_positive_witness(v4, world, eq_rows, opt, x):
    """Try to certify (exactly) that a copy spec canNOT prove v4: exhibit a
    rational h with E h >= 0, C h = 0 exactly and v.h > 0."""
    E, _ = world.elemental()
    C = np.asarray(eq_rows)
    v = world.lift(v4, W4)
    E_int, C_int, v_int = _to_int_matrix(E), _to_int_matrix(C), _to_int_matrix(v)
    for den in DENOM_LADDER[:14]:
        h = [Fraction(t).limit_denominator(den) for t in x]
        if (all(sum(int(r[k]) * h[k] for k in range(world.dim)) >= 0
                for r in E_int)
                and all(sum(int(r[k]) * h[k] for k in range(world.dim)) == 0
                        for r in C_int)
                and sum(int(v_int[k]) * h[k] for k in range(world.dim)) > 0):
            return h
    return None


# ---------------------------------------------------------------------------
# Copy-spec enumeration
# ---------------------------------------------------------------------------

def one_copy_specs():
    """All (Y, Z): new var 4 is a copy of X_Y over X_Z, Y,Z disjoint in [4]."""
    out = []
    varset = range(4)
    for ky in (1, 2, 3):
        for Y in itertools.combinations(varset, ky):
            rest = [t for t in varset if t not in Y]
            for kz in range(len(rest) + 1):
                for Z in itertools.combinations(rest, kz):
                    out.append((frozenset(Y), frozenset(Z)))
    return out


def spec_name(Y, Z, new):
    return (f"{VARNAMES[new]}=copy({''.join(VARNAMES[i] for i in sorted(Y))}"
            f"|{''.join(VARNAMES[i] for i in sorted(Z)) or '-'})")


def second_copy_specs():
    """(Y, Z) subsets of {A,B,C,D,R}={0..4} for the second copy variable S."""
    out = []
    varset = range(5)
    for ky in (1, 2):
        for Y in itertools.combinations(varset, ky):
            rest = [t for t in varset if t not in Y]
            for kz in range(1, len(rest) + 1):
                for Z in itertools.combinations(rest, kz):
                    out.append((frozenset(Y), frozenset(Z)))
    return out


# Copy specs. DFZ prove their Theorem-3 form of ZY with "R = D-copy of C over
# (A,B)"; our ZY functional is the canonical Theorem-1 form, related by the
# swap C<->A, B<->D (DFZ Sec. III), so the corresponding copy is A over (C,D).
ZY_COPY = (frozenset({0}), frozenset({2, 3}))     # R = copy of A over (C,D)
# The DFZ-2006 six are stated in Theorem-3-style variables, first copy:
C_OVER_AB = (frozenset({2}), frozenset({0, 1}))   # R = copy of C over (A,B)


def two_copy_rows(spec1, spec2):
    r1, _ = copy_rows(W6, range(4), 4, *spec1)
    r2, _ = copy_rows(W6, range(5), 5, *spec2)
    return np.vstack([r1, r2])


# ---------------------------------------------------------------------------
# Random-distribution sanity (validity screening for candidate inequalities)
# ---------------------------------------------------------------------------

def entropy_vector4(p):
    p = np.asarray(p, dtype=float)
    h = np.zeros(W4.dim)
    for s, i in W4.idx.items():
        axes = tuple(a for a in range(4) if a not in s)
        m = p.sum(axis=axes) if axes else p
        m = m[m > 0]
        h[i] = float(-(m * np.log2(m)).sum())
    return h


def random_pmfs(n_trials, seed):
    rng = np.random.default_rng(seed)
    pyrng = random.Random(seed)
    for _ in range(n_trials):
        shape = tuple(pyrng.choice([2, 3]) for _ in range(4))
        alpha = pyrng.choice([0.05, 0.3, 1.0])
        p = rng.dirichlet(np.full(int(np.prod(shape)), alpha)).reshape(shape)
        if pyrng.random() < 0.3:
            mask = rng.random(shape) < 0.5
            if (p * mask).sum() > 0:
                p = p * mask / (p * mask).sum()
        yield p


def max_violation_on_random(v4, n_trials=600, seed=20260722):
    worst = -np.inf
    for p in random_pmfs(n_trials, seed):
        worst = max(worst, float(v4 @ entropy_vector4(p)))
    return worst


# ---------------------------------------------------------------------------

def part1_baseline():
    print("== 1. Baseline re-check: ZY98 over Gamma_4 alone ==")
    opt, x = screen(ZY, W4, np.zeros((0, W4.dim)))
    print(f"  max ZY violation over Gamma_4, H(ABCD)=1: {opt:.10f} "
          "(baseline attempt certified 1/4 exactly)")
    assert abs(opt - 0.25) < 1e-8
    cert = certify(ZY, W4, np.zeros((0, W4.dim)), "ZY over Gamma_4 alone",
                   verbose=False)
    assert cert is None, "ZY must NOT be provable from Shannon alone"
    print("  and (as expected) no Shannon-only dual certificate exists.")


def part2_zy_one_copy():
    print("\n== 2. ZY98 from ONE copy variable (R = copy of A over (C,D)) ==")
    rows, labels = copy_rows(W5, range(4), 4, *ZY_COPY)
    print("  copy constraints: " + "; ".join(labels))
    opt, _ = screen(ZY, W5, rows)
    print(f"  LP max ZY violation over Gamma_5 + copy constraints: {opt:.2e}")
    cert = certify(ZY, W5, rows, "ZY98, one copy")
    assert cert is not None and abs(opt) < 1e-8, "ZY98 certification failed"
    return cert


def part3_negative_control(two_copy_specs_used):
    print("\n== 3. Negative control: Ingleton (false inequality) ==")
    worst = np.inf
    for Y, Z in one_copy_specs():
        rows, _ = copy_rows(W5, range(4), 4, Y, Z)
        opt, _ = screen(INGLETON, W5, rows)
        worst = min(worst, opt)
        assert certify(INGLETON, W5, rows, "", verbose=False) is None, \
            f"BUG: certified the false Ingleton inequality via {spec_name(Y, Z, 4)}"
    print(f"  one-copy specs tried: {len(one_copy_specs())}; min LP optimum "
          f"{worst:.6f} > 0 and no exact certificate exists for any -> "
          "Ingleton (correctly) not provable")
    for spec1, spec2 in two_copy_specs_used:
        rows = two_copy_rows(spec1, spec2)
        assert certify(INGLETON, W6, rows, "", verbose=False) is None, \
            "BUG: certified Ingleton with two copies"
    print(f"  also not provable via the {len(two_copy_specs_used)} two-copy "
          "specs used in part 4")


def part4_dfz_six():
    print("\n== 4. DFZ-2006 two-copy inequalities (arXiv:1104.3602 Sec. V) ==")
    # Second-copy specs named by DFZ (p.8) tried first, then a search.
    named = [(frozenset({0}), frozenset({2, 3, 4})),   # S = copy of A over CDR
             (frozenset({2}), frozenset({0, 3, 4}))]   # S = copy of C over ADR
    # First-copy specs to try: C-over-AB (the ZY one); then A-over-BC, which a
    # widened pass over all 64 x 145 first/second specs (2026-07-23 run) found
    # to certify (39) and (41) ABSOLUTELY with second copy S=copy(A|BDR),
    # making the relative pass in part4b unnecessary; then the other one-step
    # specs DFZ list on p.5 (codes 27,36,39,66,75) for stragglers.
    first_specs = [C_OVER_AB,
                   (frozenset({0}), frozenset({1, 2})),
                   (frozenset({3}), frozenset({0, 1, 2})),
                   (frozenset({2, 3}), frozenset({0, 1})),
                   (frozenset({1, 2, 3}), frozenset({0})),
                   (frozenset({1, 2}), frozenset({0})),
                   (frozenset({1}), frozenset({0}))]
    results, specs_used = {}, []
    for label, coeffs in DFZ_SIX.items():
        v = dfz_family(*coeffs)
        found = None
        all2 = named + [s for s in second_copy_specs() if s not in named]
        for spec1 in first_specs:
            for spec2 in all2:
                rows = two_copy_rows(spec1, spec2)
                opt, _ = screen(v, W6, rows)
                if opt < 1e-7:
                    cert = certify(v, W6, rows,
                                   f"{label} via {spec_name(*spec1, 4)}, "
                                   f"{spec_name(*spec2, 5)}")
                    if cert is not None:
                        found = ((spec1, spec2), cert)
                        specs_used.append((spec1, spec2))
                        break
            if found:
                break
        results[label] = found
        if found is None:
            print(f"  [{label}] NOT certified with (any of {len(first_specs)} "
                  "first copies + any single second copy) -- honest failure, "
                  "see attempt file")
    ok = [l for l, r in results.items() if r]
    print(f"  certified exactly: {', '.join(ok) if ok else 'none'}")
    return results, specs_used


# The 15 two-copy-variable two-step specs from arXiv:1104.3602 p.8 (codes
# decoded: bits 1=A,2=B,4=C,8=D,16=R; all have first copy "C over AB").
def _dec(bits):
    return frozenset(i for i in range(5) if bits >> i & 1)


DFZ_15_SECOND = [(_dec(y), _dec(z)) for y, z in
                 [(1, 28), (4, 25), (2, 25), (1, 24), (8, 21), (8, 19),
                  (8, 17), (2, 21), (1, 20), (4, 19), (4, 17), (16, 9),
                  (24, 3), (16, 5), (20, 3)]]


def instance_rows(world, cited):
    """All instances of already-certified 4-variable inequalities under
    injective role maps [4] -> world variables, as rows r with r.h >= 0.

    cited: list of (name, v4) with v4.h <= 0 valid for ALL random variables
    (so every instance on any 4 of the world's variables is a valid row).
    """
    rows, labels, seen = [], [], set()
    for name, v4 in cited:
        for perm in itertools.permutations(range(world.n), 4):
            r = np.zeros(world.dim)
            for s, i in W4.idx.items():
                if v4[i]:
                    r[world.idx[frozenset(perm[t] for t in s)]] -= v4[i]
            key = tuple(np.rint(r).astype(int))
            if key not in seen:
                seen.add(key)
                rows.append(r)
                labels.append(f"{name}[{''.join(VARNAMES[p] for p in perm)}]")
    return np.array(rows), labels


def part4b_relative(results):
    """For DFZ inequalities not certified absolutely: certify RELATIVE to
    Shannon + one two-step copy spec + instances of the already-certified
    inequalities (ZY + the absolutely-certified DFZ ones).  This mirrors
    DFZ's iteration; the resulting proof tree is complete because each cited
    inequality carries its own exact certificate from parts 2 and 4."""
    failing = [l for l, r in results.items() if r is None]
    if not failing:
        return results
    print("\n== 4b. Relative certification for " + ", ".join(failing)
          + " (copy spec + already-certified inequalities as lemmas) ==")
    cited = [("ZY", ZY)] + [(l, dfz_family(*DFZ_SIX[l]))
                            for l, r in results.items() if r is not None]
    K6 = instance_rows(W6, cited)
    for label in failing:
        v = dfz_family(*DFZ_SIX[label])
        found = None
        for spec2 in DFZ_15_SECOND:
            rows = two_copy_rows(C_OVER_AB, spec2)
            opt, _ = screen(v, W6, rows, extra_ineq=K6[0])
            if opt < 1e-7:
                cert = certify(v, W6, rows,
                               f"{label} via {spec_name(*C_OVER_AB, 4)}, "
                               f"{spec_name(*spec2, 5)} + cited lemmas",
                               extra=K6)
                if cert is not None:
                    found = ((C_OVER_AB, spec2), cert)
                    break
        results[label] = found
        if found is None:
            print(f"  [{label}] still NOT certified (relative pass failed) "
                  "-- honest failure, recorded in the attempt file")
    return results


def part5_dfz_need_two_copies():
    print("\n== 5. One copy does NOT suffice for the DFZ six (cf. DFZ's "
          "uniqueness claim for ZY) ==")
    specs = one_copy_specs()
    for label, coeffs in DFZ_SIX.items():
        v = dfz_family(*coeffs)
        min_opt, exact_wit = np.inf, 0
        for Y, Z in specs:
            rows, _ = copy_rows(W5, range(4), 4, Y, Z)
            opt, x = screen(v, W5, rows)
            min_opt = min(min_opt, opt)
            if opt > 1e-7 and exact_positive_witness(v, W5, rows, opt, x) is not None:
                exact_wit += 1
        print(f"  [{label}] min LP optimum over {len(specs)} one-copy specs: "
              f"{min_opt:.6f} (>0 => unprovable with one copy); exact "
              f"rational positive witnesses for {exact_wit}/{len(specs)} specs")


def part6_search(seed=20260722, n_samples=220):
    print("\n== 6. Search: DFZ-family candidates not implied by Shannon + one "
          "copy ==")
    rng = random.Random(seed)
    seen, cands = set(), []
    while len(cands) < n_samples:
        t = tuple(rng.randint(0, 4) for _ in range(7))
        if t not in seen:
            seen.add(t)
            cands.append(t)
    one_copy_row_sets = [copy_rows(W5, range(4), 4, *s)[0]
                         for s in (C_OVER_AB, ZY_COPY)]
    named2 = [(frozenset({0}), frozenset({2, 3, 4})),
              (frozenset({2}), frozenset({0, 3, 4}))]
    counts = {"shannon": 0, "one-copy": 0, "violated": 0, "two-copy": 0,
              "unresolved": 0}
    unresolved, twocopy_new = [], []
    for t in cands:
        v = dfz_family(*t)
        opt4, _ = screen(v, W4, np.zeros((0, W4.dim)))
        if opt4 < 1e-7 and certify(v, W4, np.zeros((0, W4.dim)), "",
                                   verbose=False) is not None:
            counts["shannon"] += 1
            continue
        if any(screen(v, W5, rows)[0] < 1e-7
               and certify(v, W5, rows, "", verbose=False) is not None
               for rows in one_copy_row_sets):
            counts["one-copy"] += 1
            continue
        if max_violation_on_random(v, n_trials=250, seed=seed) > 1e-7:
            counts["violated"] += 1        # false inequality: entropic witness
            continue
        done = False
        for spec2 in named2:
            rows = two_copy_rows(C_OVER_AB, spec2)
            opt6, _ = screen(v, W6, rows)
            if opt6 < 1e-7 and certify(v, W6, rows, "", verbose=False) is not None:
                counts["two-copy"] += 1
                twocopy_new.append(t)
                done = True
                break
        if not done:
            counts["unresolved"] += 1
            unresolved.append(t)
    print(f"  {n_samples} random (a..g) in {{0..4}}^7, seed {seed}: {counts}")
    if twocopy_new:
        print(f"  two-copy-certified (valid, non-Shannon, not one-copy): "
              f"{twocopy_new[:10]}{' ...' if len(twocopy_new) > 10 else ''}")
    if unresolved:
        print(f"  unresolved (no violation found, no certificate with our "
              f"specs): {unresolved[:10]}"
              f"{' ...' if len(unresolved) > 10 else ''}")
    return counts, unresolved, twocopy_new


def main():
    print("=== entropy-region: copy-lemma frontier machinery ===\n")
    part1_baseline()
    part2_zy_one_copy()
    results, specs_used = part4_dfz_six()
    results = part4b_relative(results)
    part3_negative_control(specs_used or
                           [(C_OVER_AB, (frozenset({0}), frozenset({2, 3, 4})))])
    part5_dfz_need_two_copies()
    part6_search()

    n_certified = sum(1 for r in results.values() if r)
    if n_certified >= 2:
        print(f"\nCONCLUSION [exact]: ZY98 certified via one copy; "
              f"{n_certified}/6 DFZ-2006 inequalities certified via two "
              "copies; every certificate verified in exact Fraction "
              "arithmetic (identity v + sum y_i E_i + sum mu_j C_j = 0, "
              "y >= 0).")
    else:
        print("\nCONCLUSION: fewer than 2 DFZ inequalities certified; "
              "see messages above.")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
