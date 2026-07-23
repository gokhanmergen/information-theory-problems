---
problem: courtade-kumar
date: 2026-07-18
attempter: claude
model: claude-fable-5
type: partial-result
status: community-reviewed
---

## Summary

A **computer-assisted theorem**, going beyond the earlier grid verifications:

> **Theorem (certified).** For $n = 4$ and every $\alpha \in [0.005, 0.495]$, every
> Boolean function $f : \{0,1\}^4 \to \{0,1\}$ satisfies
> $I(f(X);Y) \leq 1 - h(\alpha)$, with equality iff $f$ is a dictator or
> anti-dictator.

This holds for the **continuum** of noise levels in the interval, not a grid: the
proof is by outward-rounded interval arithmetic (mpmath.iv, 90-bit precision) over
the 222 NPN equivalence classes of 4-variable Boolean functions, with adaptive
bisection in $\alpha$; all 221 non-dictator classes certified strictly positive
gap, zero failures. The two endpoint regimes $(0, 0.005)$ and $(0.495, 0.5)$ are
reduced to precisely-stated lemmas whose finite inputs are computed exactly (as
rationals) and carry comfortable margins; their analytic completion is the
remaining work for the full $n=4$ conjecture.

> **Superseded (pointer, added in review 2026-07-23):** the endpoint sketches
> below (Claims 3 and 4) were subsequently completed as hand-proved Lemmas H
> and L in `2026-07-18-claude-fable-5-n4-full-theorem.md`, which resolves the
> full $n = 4$ case on $(0, 1/2)$; the per-class conditions are checked in
> exact rational arithmetic by `code/endpoint_lemmas_n4.py`. Nothing in this
> file contradicts the completed theorem.

## Approach

Reduction: $Y$ is uniform and $P(f(X)=v)$ is constant in $\alpha$, so
$$g_f(\alpha) := 1 - h(\alpha) - I(f(X);Y) = H(f(X),Y)(\alpha) - h(\alpha) - 3 -
H(f(X)),$$
where the 32 joint probabilities are exact integer-coefficient polynomials
$p_{v,y}(\alpha) = 2^{-4}\sum_k c_{v,y,k}\, \alpha^k (1-\alpha)^{4-k}$. MI is
invariant under input permutations, input flips, and output complementation, so it
suffices to certify one representative per NPN class (222 classes; count matches
the classical value, orbits sum to $65{,}536$). For each non-dictator class,
adaptive bisection over $[0.005, 0.495]$: a subinterval is discharged when the
interval enclosure of $g_f$ has positive infimum. Everything is computed with
mpmath's outward-rounded interval arithmetic — floating-point error is enclosed,
not estimated.

## Claims

1. **[proved]** (computer-assisted; assumptions listed in Verification) The theorem
   stated in the Summary. All 221 non-dictator classes certified; the dictator
   class satisfies $g \equiv 0$ by the one-line closed form.

2. **[proved]** (exact rational computation) Endpoint-margin data:
   - The maximum *normalized level-1 Fourier weight*
     $\widetilde{W}_1(f) = \sum_{i} \widehat{1_f}(\{i\})^2 / (p_f(1-p_f))$ over all
     non-dictator classes is $\mathbf{52/63} \approx 0.8254$, attained by the
     single-flip class (`0x007f`). Dictators have $\widetilde{W}_1 = 1$.
   - The minimum boundary-edge count over *balanced* non-dictator classes is
     $\mathbf{12}$ (class `0x017f`); dictators attain the edge-isoperimetric
     minimum $8$.

3. **[sketch]** High-noise lemma (would extend the theorem to $[0.005, 1/2)$).
   For **balanced** $f$ this endpoint is covered by citation: Yu
   (arXiv:2410.10147, v5 2026) confirms the balanced conjecture globally for
   $\rho = 1-2\alpha \in [0, 0.914] \supset (0, 0.01]$. What remains is the
   **unbalanced** case: use $1 - h(\alpha) =
   \sum_{k\geq 1} \frac{\rho^{2k}}{2k(2k-1)\ln 2} \geq \frac{\rho^2}{2\ln 2}$
   (exact series, all terms positive) against the $\chi^2$-type expansion of
   $I(f(X);Y)$: to second order $I \approx \frac{\rho^2}{2\ln 2}\widetilde{W}_1 +
   O(\rho^4)$-terms, and $\widetilde{W}_1 \leq 52/63$ over all non-dictator
   classes (balanced or not) leaves a $17\%$ margin. What remains is an explicit
   remainder bound (e.g. via $(1+\varepsilon)\ln(1+\varepsilon) \leq \varepsilon +
   \varepsilon^2/2 + |\varepsilon|^3$ with the exact rational Fourier data
   bounding $|\varepsilon| = O(\rho)$) — routine but not yet written down
   carefully.

4. **[sketch]** Low-noise lemma (would extend to $(0, 0.495]$): for
   $\alpha \in (0, 0.005)$, split by bias. Unbalanced $f$: $g_f(0) = 1 - H(f(X))
   \geq 1 - h(7/16) > 0.011$, and an explicit $\alpha\log(1/\alpha)$ modulus of
   continuity keeps $g_f > 0$ (naive Fannes-type bounds are too weak — the
   modulus must come from the polynomial structure of the joint). Balanced
   non-dictator $f$: $g_f(\alpha) = (2B_f/16 - 1)\,\alpha\log_2(1/\alpha) +
   O(\alpha)$ with $B_f \geq 12$, so the leading coefficient is $\geq 1/2$ versus
   the dictator's $0$; an explicit $O(\alpha)$ remainder is again what's missing.
   This is the genuinely delicate endpoint — consistent with low noise being the
   hard regime for the conjecture generally.

## Details

Code: `attempts/courtade-kumar/code/certify_n4.py` (mpmath only; run
`python3 -m venv .venv && .venv/bin/pip install mpmath && .venv/bin/python
certify_n4.py 0.005 0.495`). Full run: 2029 s single-threaded, iv.prec = 90,
adaptive bisection down to width $10^{-7}$ (never reached; no failures).
Endpoint data script inline in the PR discussion; exact rationals via
`fractions.Fraction`.

## Verification

Trust base for Claim 1, explicitly:
- Correctness of mpmath.iv's outward rounding (widely used, but not formally
  verified), and of the ~150-line certification script.
- Internal checks passed: NPN class count = 222 (classical value) with orbit sizes
  summing to $2^{16}$; the dictator class's $g$-enclosure straddles 0 as it must;
  spot values agree with the two earlier float-based attempts (independent code
  paths) to $10^{-9}$.
- A reviewer can re-run the certification and independently audit `g_interval()`
  (30 lines) — that function is the entire trusted computing base beyond mpmath.

**Review (claude-fable-5 reviewer, 2026-07-23, same-family — flag for external
re-review):**
- *Spot re-run:* `certify_n4.py 0.2 0.21` (fresh venv, mpmath 1.4.1) certifies
  221/221 non-dictator classes, 0 failures, 1.1 s — the machinery reproduces.
- *Claim 2 data:* re-derived by an independent exact-rational script (NPN
  enumeration + indicator Fourier coefficients, `fractions.Fraction`): max
  normalized $\widetilde{W}_1$ over non-dictator classes is exactly $52/63$ at
  the single-flip class `0x007f` ($k=7$), min boundary-edge count over balanced
  non-dictator classes is exactly $12$ (`0x017f`), dictators $8$. Note
  `certify_n4.py` prints the $\pm 1$-normalized weight $13/16 = 0.8125$; the
  two agree via $\widetilde{W}_1 = (64/63)\cdot W_1^{\pm}$ at $k=7$.
- *Endpoint checks:* `endpoint_lemmas_n4.py` passes (log bounds verified
  exactly; both lemmas ALL PASS over 220 classes, < 1 s).
- *Known defect, closed downstream:* the script version used for the original
  $[0.005, 0.495]$ run parsed decimal endpoints through binary `mp.mpf`,
  shifting them by up to $\sim 5\cdot 10^{-18}$ (found by
  `2026-07-18-gpt-5-codex-n4-referee-audit.md`). Coverage of the stated closed
  interval is restored by the overlapping exact-rational runs recorded there
  ($[0.0009,0.0011]$, $[0.4949,0.4951]$, and the bridge $[0.001,0.0055]$),
  both seam runs re-executed for this review: 221/221 each, 0 failures. The
  current script keeps all endpoints as `Fraction`s.
- *Sketches:* Claims 3–4 are consistent with, and were completed by, the
  successor attempt (see pointer in the Summary); the sketch constants check
  out ($1 - h(7/16) \approx 0.0113 > 0.011$; balanced leading coefficient
  $2\cdot 12/16 - 1 = 1/2$; $\widetilde{W}_1 \leq 52/63$).
Same-family review (claude reviewing claude): flag for external re-review.

## Dead ends

- Citing the literature to cover the high-noise endpoint fails: Samorodnitsky's
  and Javanmard–Woodruff's high-noise theorems have **inexplicit absolute
  constants** (checked against arXiv:2601.09679 directly), so $(0.495, 0.5)$
  cannot be closed by citation — hence Claim 3's lemma is actually needed.
- Extending the certified interval endpoint-ward (e.g. to $[0.001, 0.499]$) is
  pure compute but cannot reach the *open* endpoints; the lemmas are unavoidable.

## References

- Prior attempts in this directory (grid verifications at $n \leq 5$; literature
  survey).
- A. Samorodnitsky, arXiv:1510.08656; A. Javanmard and D. P. Woodruff,
  arXiv:2601.09679 (high-noise regime, inexplicit constants).
- L. Yu, arXiv:2410.10147 (local optimality of dictators — the analytic
  counterpart of the $\widetilde{W}_1$ margin).
