---
problem: entropy-region
date: 2026-07-19
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Computational baseline for $\Gamma^*_4$: exact entropy-vector computation for
arbitrary finite joint distributions of four variables, plus an exact
(rational-arithmetic) LP certificate that the Zhang–Yeung 1998 inequality is
not implied by the Shannon inequalities — i.e. an explicit rational point of
the Shannon cone $\Gamma_4$ that violates ZY98, with a matching exact dual
certificate showing the violating point is optimal. A frequently misquoted
form of ZY is shown (with a short proof and an exact LP dual) to be
Shannon-implied, hence *not* the ZY inequality. No new mathematics; this
establishes verified infrastructure and a reproducible baseline for future
attempts on this problem.

## Approach

Work in $\mathbb{R}^{15}$ with coordinates $h_S = H(X_S)$,
$\emptyset \neq S \subseteq \{1,2,3,4\}$, in the order
$H(1), H(2), H(3), H(4), H(12), H(13), H(14), H(23), H(24), H(34), H(123),
H(124), H(134), H(234), H(1234)$ (convention $h_\emptyset = 0$).

The Shannon cone $\Gamma_4$ is cut out by the 28 **elemental** inequalities
(Yeung 2008, Sec. 14.2): $H(X_i \mid X_{[4]\setminus i}) \ge 0$ (4 of them)
and $I(X_i; X_j \mid X_K) \ge 0$ for $i<j$, $K \subseteq [4]\setminus\{i,j\}$
(24 of them). The **canonical Zhang–Yeung inequality** (Zhang–Yeung 1998,
Thm 3; equivalently Yeung 2008, Thm 15.7) is

$$2I(X_3;X_4) \le I(X_1;X_2) + I(X_1;X_3,X_4) + 3I(X_3;X_4|X_1) + I(X_3;X_4|X_2). \tag{ZY}$$

To show (ZY) is not Shannon-implied, maximize its violation
$v \cdot h = \mathrm{LHS} - \mathrm{RHS}$ over $\Gamma_4$ normalized by
$h_{1234} = 1$, via `scipy.optimize.linprog` (HiGHS), then make everything
exact: round the optimizer to rationals and re-check the 28 elemental
inequalities and the violation with `fractions.Fraction`; round the dual
marginals to rationals and re-check the dual identity exactly. The float LP
is used only as a *guess generator*; every claim below rests on the exact
rational re-verification.

Note on the inequality's form (the task brief circulated with the variant
$I(X_3;X_4) \le 2I(X_3;X_4|X_1) + I(X_3;X_4|X_2) + I(X_1;X_2) +
I(X_1;X_3X_4)$): that variant is **not** the ZY inequality — it is implied by
the Shannon inequalities (Claim 4).

## Claims

1. **[proved]** (known result, ZY98; reproduced here with an independent
   exact certificate). The rational vector
   $$h^* = \bigl(\tfrac12,\tfrac12,\tfrac12,\tfrac12;\; 1,\tfrac34,\tfrac34,\tfrac34,\tfrac34,\tfrac34;\; 1,1,1,1;\; 1\bigr)$$
   (coordinate order as above; $h^*_{12} = 1$, the other five pairs $\tfrac34$)
   satisfies all 28 elemental Shannon inequalities exactly — so
   $h^* \in \Gamma_4$ — and violates (ZY) with exact slack
   $\mathrm{LHS}-\mathrm{RHS} = \tfrac14$. Hence (ZY) is not implied by the
   Shannon inequalities. Since (ZY) holds for all entropic vectors (ZY98),
   $h^*$ is not entropic and not in $\bar\Gamma^*_4$; therefore
   $\bar\Gamma^*_4 \subsetneq \Gamma_4$.
2. **[proved]** $\max \{\, v\cdot h : h \in \Gamma_4,\ h_{1234}=1 \,\} =
   \tfrac14$ exactly, where $v\cdot h$ is the (ZY) violation: $h^*$ attains
   $\tfrac14$ (Claim 1), and there exist rationals $y_1,\dots,y_{28} \ge 0$
   with $v + \sum_i y_i E_i = \tfrac14\,\delta_{1234}$ ($E_i$ the elemental
   rows), verified in exact arithmetic, so $v\cdot h \le \tfrac14$ on the
   normalized cone.
3. **[proved]** $h^*$ also violates the Ingleton inequality
   $I(X_3;X_4) \le I(X_3;X_4|X_1) + I(X_3;X_4|X_2) + I(X_1;X_2)$
   (slack $\tfrac14 \le 0$ fails); it is the classical Vámos-like
   Ingleton-violating polymatroid, scaled to $h_{1234}=1$. (Direct
   computation; Ingleton is valid for linearly representable / abelian-group
   vectors, so no such construction realizes $h^*$.)
4. **[proved]** The misquoted variant
   $I(X_3;X_4) \le 2I(X_3;X_4|X_1) + I(X_3;X_4|X_2) + I(X_1;X_2) + I(X_1;X_3X_4)$
   *is* implied by the Shannon inequalities (short proof in Details;
   independently, an exact rational LP dual certificate with bound $0$ was
   verified). So it is a true but Shannon-trivial statement, not the ZY
   inequality, and it separates nothing.
5. **[heuristic]** Sanity: on 400 pseudorandom joint pmfs (alphabet sizes
   $2$–$3$ per coordinate, Dirichlet weights with $\alpha \in
   \{0.05, 0.3, 1\}$, 30% sparsified supports, fixed seed) the computed
   entropy vectors satisfy all 28 elemental inequalities (min slack
   $\approx -2\cdot10^{-16}$, i.e. zero up to roundoff) and (ZY) (max
   violation $\approx -2.8\cdot10^{-6} < 0$). This is a consistency check on
   the entropy code, not evidence about $\Gamma^*_4$ beyond known theorems.

## Details

All computations: `code/zy_baseline.py` (numpy + `scipy.optimize.linprog`
+ stdlib `fractions`; Python 3, scipy 1.17.1; run `python3 zy_baseline.py`,
runtime < 5 s). The script prints every certificate it verifies.

**Claim 1.** The 28 elemental inequalities are generated programmatically.
$h^*$ is entered by hand (independently of the LP) and every elemental value
is computed in `Fraction` arithmetic; the minimum slack is $0$ (many are
tight — $h^*$ lies on a low-dimensional face; it is a known extreme ray of
$\Gamma_4$ up to scale, though extremality is not certified here and not
needed). The (ZY) violation functional, expanded over the 15 coordinates
from its mutual-information form, evaluates to exactly $\tfrac14$ at $h^*$.
The LP optimizer, rounded coordinate-wise with `limit_denominator(64)`,
coincides with $h^*$ exactly.

**Claim 2.** HiGHS reports optimum $0.25$; the dual marginals of the 28
inequality rows, rounded via `limit_denominator(64)`, give $y \ge 0$
satisfying the identity $v + \sum_i y_i E_i = \tfrac14\,\delta_{1234}$
coordinate-by-coordinate in exact rationals (the variable bounds
$0 \le h \le 4$ used in the LP are inactive at the optimum and carry zero
duals; the exact identity does not depend on them). For any $h$ with
$E h \ge 0$ and $h_{1234}=1$: $v\cdot h = \tfrac14 h_{1234} - \sum_i y_i
(E_i \cdot h) \le \tfrac14$.

**Claim 3.** At $h^*$: $I(X_3;X_4) = \tfrac12+\tfrac12-\tfrac34 = \tfrac14$,
$I(X_3;X_4|X_1) = \tfrac34+\tfrac34-\tfrac12-1 = 0$, likewise
$I(X_3;X_4|X_2) = 0$, and $I(X_1;X_2) = \tfrac12+\tfrac12-1 = 0$.

**Claim 4.** Write $t = I(X_3;X_4)$, $p = I(X_3;X_4|X_1)$,
$q = I(X_3;X_4|X_2)$, $a = I(X_1;X_2)$, $b = I(X_1;X_3X_4)$. Expanding both
sides in joint entropies gives the identity
$t - p = I(X_1;X_3) + I(X_1;X_4) - b$. By the chain rule
$b = I(X_1;X_3) + I(X_1;X_4|X_3) \ge I(X_1;X_3)$ and symmetrically
$b \ge I(X_1;X_4)$, so $t - p \le 2b - b = b$, hence
$t \le p + b \le 2p + q + a + b$ using $p, q, a \ge 0$. All steps are
elemental Shannon inequalities. (The exact LP dual with bound $0$ verifies
this independently.) Note the variant is also *weaker* than (ZY) given
Shannon: if $t \ge p$ then $t - 2p \le 2t - 3p \le a+b+q$ by (ZY); if
$t < p$ then $t - 2p < -p \le 0 \le a+b+q$.

**Claim 5.** Unit tests pin the entropy code to three exactly known vectors:
four i.i.d. uniform bits ($h_S = |S|$), four identical uniform bits
($h_S = 1$), and $X_4 = X_1 \oplus X_2 \oplus X_3$ with $X_1,X_2,X_3$
i.i.d. uniform bits ($h_S = \min(|S|,3)$); then the random sweep described
in Claim 5 runs with seed 20260718.

## Verification

- Claims 1–4: re-run `python3 code/zy_baseline.py`; every inequality and
  identity above is re-derived and checked in exact `Fraction` arithmetic at
  runtime (floats appear only inside the LP solver, whose output is treated
  as a guess). Claim 3 and the Claim 4 proof are also checkable by hand in
  a few lines.
- What is and is not established: this attempt certifies the *known*
  separation $\bar\Gamma^*_4 \subsetneq \Gamma_4$ with self-contained exact
  certificates. It proves nothing new about $\bar\Gamma^*_4$ itself.
- Novelty: none claimed. Claim 1 is ZY98's theorem; the point $h^*$ (up to
  scaling, singleton entropies 2, pairs 3 except one pair 4, triples and
  quadruple 4) is the standard Ingleton/Vámos-type gap point appearing
  throughout the literature (e.g. Dougherty–Freiling–Zeger 2011). The exact
  primal+dual LP certification appears to be a (minor) hygienic addition for
  this repo only.

## Dead ends

- **The inequality form in the task brief is wrong.** The circulated form
  $t \le 2p + q + a + b$ (notation of Claim 4) looked plausible and was the
  first target; its violation LP over $\Gamma_4$ came back with optimum
  exactly $0$. Obstruction: it is Shannon-implied (Claim 4's three-line
  proof), so no point of $\Gamma_4$ can violate it and it cannot witness the
  ZY separation. Anyone re-deriving ZY from memory should check their form
  against the LP first — a form whose Shannon-cone violation LP is $0$ is
  not a non-Shannon inequality, whatever it is called.
- **Symmetric gap point.** The fully symmetric polymatroid ($h_i = 2$,
  all pairs $3$, triples and quad $4$, before scaling) does *not* violate
  (ZY): its violation is exactly $0$ (tight). The violation requires
  breaking symmetry by raising $h_{12}$ to $4$ (making $X_1, X_2$
  "independent" in the polymatroid) while keeping $h_{34} = 3$. Raising
  $h_{34}$ instead gives violation $-\tfrac34$ (strictly satisfied).
- **Naive rounding pitfalls.** `limit_denominator` with a large bound
  faithfully reproduces float noise instead of snapping to the intended
  vertex; denominator bound 64 was chosen because the target vertex and dual
  have denominators $\le 4$. The exact re-verification step makes this
  choice safe: a bad rounding fails loudly rather than certifying garbage.
- Not attempted (out of scope for a baseline): certifying extremality of
  $h^*$ in $\Gamma_4$; searching for entropic points near $h^*$ (inner
  bounds on $\bar\Gamma^*_4$); reproducing Matúš's infinite families or the
  DFZ inequality lists. Natural next attempts.

## References

- No prior attempts exist in `attempts/entropy-region/`.
- Z. Zhang and R. W. Yeung, "On characterization of entropy function via
  information inequalities," IEEE Trans. Inf. Theory 44(4):1440–1452, 1998.
  (Theorem 3 = inequality (ZY).)
- R. W. Yeung, *Information Theory and Network Coding*, Springer, 2008.
  (Sec. 14.2: elemental inequalities; Thm 15.7: (ZY).)
- A. W. Ingleton, "Representation of matroids," 1971 (Ingleton inequality,
  via Claim 3).
- R. Dougherty, C. Freiling, K. Zeger, "Non-Shannon information inequalities
  in four random variables," arXiv:1104.3602, 2011.
- T. H. Chan and R. W. Yeung, "On a relation between information
  inequalities and group theory," IEEE Trans. Inf. Theory, 2002 (context for
  why $h^*$ admits no group-type realization: it is not entropic at all).
