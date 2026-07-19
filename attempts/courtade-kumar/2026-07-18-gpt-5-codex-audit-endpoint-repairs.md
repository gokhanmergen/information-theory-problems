---
problem: courtade-kumar
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5
type: survey
status: unverified
---

## Summary

This audit checks the repaired $n=4$ paper and re-derives the $n=5$ endpoint
lemmas. The $n=4$ proof is mathematically sound, including the audit bridges and
integer logarithm checks, but its Courtade--Kumar provenance sentence conflated
two separate computations and has been corrected. At $n=5$ the endpoint
conclusions survive, but the older screen contained the predicted $n=4$ exponent
leftover and the purported exact verifier did not certify comfortably passing
classes. Both code defects have been repaired; a new exact all-class run passes.

## Approach

I re-derived both endpoint lemmas without importing their constants, audited the
rational/interval seam logic, checked the primary 2014 Courtade--Kumar paper, then
regenerated all $616{,}126$ five-variable NPN representatives and replaced the
floating margin filter by exact profile and integer checks.

## Claims

1. **[proved]** Lemmas L and H in `paper/n4-courtade-kumar/main.tex` are correct
   as written, and the two exact-rational bridge runs close the microscopic gaps
   left by the old decimal parsing.
2. **[proved]** `verify_log_bounds()` proves every hard-coded enclosure in the
   direction claimed.
3. **[proved]** Courtade--Kumar report an $n\leq7$ compressed-function
   enumeration in Section II-B and a separate $0.001$ grid test of their equation
   (20) in Section II-D; the draft's former combined attribution was inaccurate.
4. **[proved]** At $n=5$, Lemma L requires
   $\beta=\alpha(1-\alpha)^4$ and $\gamma=(1-\alpha_0)^4$. The older
   `screen_n5_endpoints.py` used the wrong cubic exponent; correcting it leaves its
   $158{,}646$ failure count at $\alpha_0=10^{-3}$ unchanged.
5. **[proved]** With $\alpha_0=10^{-4}$ and $\rho_0=10^{-2}$, every one of the
   $616{,}124$ nonconstant nondictator NPN classes satisfies both endpoint
   criteria. This conclusion now follows from exact rational/integer decisions,
   not from an uncertified floating margin threshold.

## Details

### 1--2. The repaired $n=4$ paper

For Lemma L, uniform input makes the posterior channel from $Y$ to $X$ a BSC.
Keeping only distance-one points gives
$P(f(X)\ne f(y)|Y=y)\ge b_y\alpha(1-\alpha)^3$, while the full error is at most
$4\alpha<1/2$. Thus entropy monotonicity, the lower bound
$h(u)\ge u\log_2(1/u)$, and
$h(\alpha)\le\alpha(\log_2(1/\alpha)+\log_2e)$ have the stated directions.
The balanced coefficient is negative after the boundary check, so $t\ge t_0$ is
used correctly; for unbalanced functions $\alpha t$ is increasing on the stated
range and the positive-part bound is valid.

For Lemma H, Parseval for the indicator gives
$\sum_{S\ne\varnothing}\widehat{1_f}(S)^2=q_1-q_1^2=q_0q_1$.
The displayed scalar logarithm inequality follows from the alternating series
for positive epsilon and a geometric upper bound for negative epsilon. Linear
terms cancel after averaging, producing the factor $1+4\varepsilon_{\max}/3$.
Finally
$1-h((1-\rho)/2)=(1/\ln2)\sum_{k\ge1}\rho^{2k}/[2k(2k-1)]$ gives the required
positive lower term.

The original middle runs began microscopically above $0.001$ and ended
microscopically below $0.495$. Exact-rational bridge certifications on
$[0.0009,0.0011]$ and $[0.4949,0.4951]$ overlap both the analytic regimes and
the old certified intervals, so no seam remains. In `verify_log_bounds()`, an
inequality $a/b\le\log_2 n$ is checked as $2^a\le n^b$, and the upper bound in
the reverse direction. The positive atanh series is a lower bound on $\ln2$ and
therefore proves the stated upper bound on $\log_2e$.

### 3. Provenance

Courtade--Kumar, printed page 4517 (Section II-B), say they numerically validated
Conjectures 1 and 2 for $n\le7$ by enumerating the compressed family $S_n$ and
evaluating mutual information. Printed page 4519 (Section II-D) instead says a
Matlab implementation of Algorithm II.1 validated their different equation (20)
for alpha in increments of $0.001$. The paper draft now states these separately.

### 4--5. The $n=5$ constants and exact run

Distance one contributes
$\beta=\alpha(1-\alpha)^{n-1}=\alpha(1-\alpha)^4$; the posterior average is
normalized by $2^{-5}=1/32$, $b_y\le5$, and
$P(f(X)\ne f(y)|Y=y)\le1-(1-\alpha)^5\le5\alpha\le1/2$ at the cutover.
Thus $c_2\le(1/32)\sum_yb_y\log_2 5$ and every dimension-dependent low-noise
constant in the final verifier is correct.

For high noise, nonconstant functions have $q_{\min}\ge1/32$. Terms with
$|S|\ge2$ obey $\rho^{2|S|}\le\rho^4$, while the same indicator Parseval identity
and epsilon expansion are dimension independent. The repaired verifier computes
integer Walsh coefficients $a_S=32\widehat{1_f}(S)$. Writing
$D=k(32-k)$, $W=\sum_i a_{\{i\}}^2$, $A=\sum_{S\ne\varnothing}|a_S|$, and
$m=\min(k,32-k)$, it checks exactly
\[
2A\le100m,
\quad
(9999W+D)(300m+4A)\le(10000D)(300m).
\]
Low noise depends only on $k$ and the histogram of the degrees $b_y=0,\ldots,5$;
all 36,950 distinct profiles are checked with `Fraction` arithmetic and logarithm
enclosures proved by integer exponentiation. An independently regenerated file
contained exactly 616,126 distinct representatives; all 616,124 target classes
passed both exact tests.

## Verification

- Ran the $n=4 endpoint script and inspected both exact-rational bridge ledgers.
- Checked the 2014 primary paper at printed pages 4517 and 4519.
- Regenerated the $n=5 NPN file from `npn5.c`; the generator reported 616,126
  classes and orbit coverage $2^{32}$.
- Ran `verify_n5_endpoints.py /tmp/npn5_reps_audit.bin`: 36,950 exact low-noise
  profiles and 616,124 exact high-noise classes, zero failures.
- Reran the corrected legacy screen at $\alpha_0=10^{-3}$; it still reports
  158,646 low-noise failures and zero high-noise failures.

## Dead ends

- A positive double-precision margin does not become an exact proof merely because
  it exceeds an arbitrary threshold; the old margin-filter argument had no
  roundoff bound.
- The cubic gamma in the old $n=5$ screen was a dimension-four transplant. It was
  numerically harmless for the reported failure count but mathematically wrong.
- Grid sampling in the 2014 paper cannot establish a continuum theorem.

## References

- `paper/n4-courtade-kumar/main.tex` and `REVIEW.md`.
- `2026-07-18-claude-fable-5-n4-full-theorem.md`.
- `2026-07-19-claude-fable-5-n5-groundwork.md`.
- T. Courtade and G. Kumar, “Which Boolean functions maximize mutual information
  on noisy inputs?”, IEEE TIT 60(8):4515--4525, 2014.
