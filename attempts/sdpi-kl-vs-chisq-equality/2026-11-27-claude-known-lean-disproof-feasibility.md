---
problem: sdpi-kl-vs-chisq-equality
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: full-solution-claim
status: unverified
---

## Summary

This attempt turns the counterexample in `2026-11-27-antigravity-counterexample.md` into a
**kernel-checked Lean disproof**:

```
theorem InfoTheory.Solutions.SdpiKlVsChisqEquality.disproof :
    ¬ InfoTheory.Problems.SdpiKlVsChisqEquality.Statement
```

It lives in `lean/InfoTheory/Solutions/SdpiKlVsChisqEquality.lean` and delegates to
`statement_false` in `lean/InfoTheory/Known/Certificates/SdpiKlVsChisqEquality.lean`.

The first version of this attempt proved everything except one global inequality. It reduced
the problem to `not_statement_of_sdpiKLAt_ex_le : sdpiKLAt exQ exW ≤ 9/100 → ¬ Statement`, with
the global inequality `D(PW‖Q) ≤ (9/100)·D(P‖Q)` over the whole 2-simplex left open. That
inequality is now proved as well (`kl_ex_global`, claim 6 below), so `s_KL = s_χ² = 9/100`
holds exactly.

The statement is a catalog formulation, not a published conjecture (see the provenance note in
the problem file). Under the AGENTS.md convention, the refutation is therefore recorded as
`statement_false` in the certificate.

## Approach

`Statement` has these hypotheses: full support, reversibility `QX·W = (QY·Wrev)ᵀ`, the
**two-sided equalities** `sdpiKLAt QX W = sdpiChiSqAt QX W` and `sdpiKLAt QY Wrev = sdpiChiSqAt QY Wrev`,
and `sdpiChiSqAt QX W ≤ (p-1)/(q-1)`. The conclusion is `inNairRibbon (W.joint QX) p q`. The
equalities really are hypotheses (they are not weakened to one direction). Each `sdpiKLAt` is a
real `sSup` over a set that is nonempty and bounded (`sdpiKLAt_le_one` is already certified), so
no junk-value shortcut exists. Degenerate instances do not help either:
- `kX = 1`: the sets are empty, both constants are 0, and the ribbon holds by data processing.
- `ρ = 1`: this forces `p = q`, and `nair_diag` covers that case.
- `ρ = 0`: the source is independent and the ribbon holds.

Structured alternatives (BSC/DSBS, products) do not give counterexamples either; see Dead ends.
So the 3×3 instance of the earlier attempt is the natural target. Its joint distribution is
symmetric, so `Wrev = W` and `QY = QX` and the two equalities collapse into one.

## Claims

Instance: `exQ = (1/4, 1/4, 1/2)` and
`exW = [[9/20, 3/20, 2/5], [3/20, 9/20, 2/5], [1/5, 1/5, 3/5]]` on `Fin 3`.

1. **[proved]** (Lean: `exQ_pos`, `ex_reversible`) `exQ` has full support and
   `exQ x · exW x y = exQ y · exW y x`. So `(QX, QY, W, Wrev) = (exQ, exQ, exW, exW)` satisfies the
   support and reversibility hypotheses of `Statement`.
2. **[proved]** (Lean: `sdpiChiSqAt_ex`) `sdpiChiSqAt exQ exW = 9/100`. In coordinates
   `s = (P₀ + P₁) - 1/2` and `d = P₀ - P₁` we have `χ²(P‖Q) = 4s² + 2d²` and
   `χ²(PW‖Q) = 4(1/25)s² + 2(9/100)d²`. The value is attained at `P = (1/2, 0, 1/2)`.
3. **[proved]** (Lean: `sdpiKLAt_ex_ge`) `9/100 ≤ sdpiKLAt exQ exW`. The proof uses
   `P_z = ((1+z)/4, (1-z)/4, 1/2)`, which gives `D(P_z W‖Q)/D(P_z‖Q) = g(3z/10)/g(z)`, where
   `g(w) = (1+w)ln(1+w) + (1-w)ln(1-w)`. It then uses `|g(w) - w²| ≤ 2w³/(1-w)` (from Mathlib's
   `Real.abs_log_sub_add_sum_range_le`) to get a ratio `≥ 9/100 - 3z/10` for `0 < z ≤ 1/10`.
4. **[proved]** (Lean: `ex_not_ribbon`) `¬ inNairRibbon (exW.joint exQ) (127/100) 4`. At this
   point `(p-1)/(q-1) = 9/100`. The witness is
   `R = (1/200)·[[2, 4, 3], [6, 111, 27], [4, 24, 19]]`. This is a coarser rounding of a numerical
   optimum, not the attempt's `R`. It gives
   `(1/p)·D(R_X‖Q) + (3/4)·D(R_Y‖Q) - D(R‖P_XY) ≈ +0.00296` bits. The proof uses certified
   two-sided bounds on the 15 needed `log2` values: each `x` is written as `2^k·y` with
   `y ∈ [0.7, 1.4]`, and a truncated log series is used with error `< 1e-10`, plus
   `Real.log_two_gt_d9` and `Real.log_two_lt_d9`. Each bound has width `≤ 1e-6`, against a
   margin of `3e-3`.
5. **[proved]** (Lean: `not_statement_of_sdpiKLAt_ex_le`, `sdpiKLAt_ex_le_of`)
   `sdpiKLAt exQ exW ≤ 9/100 → ¬ Statement`. It is enough to show
   `∀ P : ProbDist (Fin 3), D((exW.joint P).snd ‖ (exW.joint exQ).snd) ≤ (9/100)·D(P ‖ exQ)`.
   All of these depend only on `propext`, `Classical.choice` and `Quot.sound`
   (checked with `#print axioms`).
6. **[proved]** (Lean: `kl_ex_global`, `sdpiKLAt_ex_le`, `sdpiKLAt_ex`) For every
   `P ∈ Δ₃`, `D(P·exW ‖ exQ) ≤ (9/100)·D(P ‖ exQ)`. Hence `sdpiKLAt exQ exW = 9/100`. Together
   with claims 1–5 this gives `statement_false : ¬ Statement`. The proof is in Details below.
   (The earlier numerical check stands: a grid search with step `1/1500` gives a maximum ratio
   of `0.0899999…`.)

## Details

**Proof of claim 6.** Write `g(z) = (1+z)ln(1+z) + (1-z)ln(1-z)`, which is `gSym` in Lean.
Fix `P = (a, b, c)` and set:
- `s = a + b`;
- `x = 2s - 1`;
- `y = (a - b)/s`, with `y = 0` when `s = 0`.

*Step 1: grouping identity* (`group_id`). Splitting the alphabet as `{0,1} | {2}` gives, in
nats,

    2·D(P‖Q) = g(x) + s·g(y).

This includes the boundary cases `s = 0` and `|y| = 1`, because Lean has `0·log 0 = 0`. The
channel sends `s ↦ s' = (5+x)/10`, `x ↦ x/5` and `a - b ↦ (3/10)(a - b)`, so

    2·D(PW‖Q) = g(x/5) + s'·g(u),  where u = 3(1+x)y / (2(5+x)).

*Step 2: series* (`gSym_hasSum`, `gSym_le_partial`, `gSym_ge4`). For `|z| < 1`,

    g(z) = Σ_{k≥0} z^{2k+2} / ((2k+1)(k+1)).

This follows from Mathlib's `hasSum_log_sub_log_of_abs_lt_one` and
`hasSum_pow_div_log_of_abs_lt_one`, using `log(1+z) + log(1-z) = log(1-z²)`. Two consequences:
- *Lower bound.* Truncation gives `g(z) ≥ z² + z⁴/6 + z⁶/15 + z⁸/28` for `|z| ≤ 1`. At `|z| = 1`
  this is the numeric fact `2 ln 2 > 1.27`.
- *Upper bound.* The tail is bounded by a geometric series:
  `g(z) ≤ Σ_{k<n} a_k z^{2k+2} + a_n z^{2n+2}/(1-z²)`.

*Step 3: reduction to a polynomial* (`gSym_x5_le`, `gSym_out_le`, `poly_step`, `core_ineq`).
Set `t = y²` and `U = u² = 9(1+x)²t / (4(5+x)²)`. Then `U ≤ t/4`, so `|u| ≤ 1/2`, and
`s'U ≤ (3/20)·s·t`. Four bounds feed the inequality:
- `g(x) ≥ x²`;
- `g(y) ≥ t + t²/6 + t³/15 + t⁴/28`;
- `g(x/5) ≤ x²/25 + x⁴/3600`;
- `s'·g(u) ≤ s'U + s'U²/6 + (3/20)·s·t·(t²/240 + t³/1792 + t⁴/8640)`.

With these, the target `9/100·(g(x) + s·g(y)) - g(x/5) - s'·g(u) ≥ 0` reduces to
`Gpoly(x, t)/(5+x)³ ≥ 0`. Here `Gpoly` is an explicit polynomial in `(x, t)` of degree 7 in `x`
and 5 in `t`, and the reduction is checked by `field_simp; ring`.

*Step 4: positivity certificate* (`Gpoly_pos`, `Gpoly_neg`). On `x ∈ [0,1]` and on `x ∈ [-1,0]`
separately, `Gpoly` is written as an exact nonnegative rational combination of terms
`B·X^a(1-X)^b t^c(1-t)^d`, where `B` is one of `X²`, `t²`, `X·t` or `(X - κt)²` with
`κ ∈ {1/5, …, 14/25}`. The two pieces use 33 and 37 terms. The combinations were found with an
LP (scipy/HiGHS) and then solved exactly over ℚ with sympy. Lean checks them with
`linear_combination`, which is a `ring` identity, so neither the LP nor sympy is trusted.

The zero at `(x, t) = (0, 0)` is non-degenerate in the `(x, t)` coordinates. Its leading form
`25/8·x² - 9/4·xt + 273/640·t²` has discriminant `-0.27 < 0`. This is the weighted
`(x, y²)` form that the earlier attempt and this attempt's first version identified as the
obstacle. Once it is written in the variable `t = y²`, it becomes an ordinary positive-definite
quadratic.

Two parameter choices matter:
- Four terms of the `g(y)` series are needed. With fewer, the truncation loses too much at
  `|y| = 1`: the series for `g(1) = 2 ln 2` converges slowly.
- For `x`, one term `x²` suffices.

The previous version of this section listed obstacles (a)–(d). They were resolved as follows:
- (a) is `group_id`.
- (b), the binary contraction `h(z/5) ≤ h(z)/25`, is not needed separately. It is subsumed by
  the series bounds in Step 3.
- (c) is `gSym_ge4` and `gSym_le_partial`.
- (d) is the certificate in Step 4.

**Ribbon witness generation.** I searched for witnesses with smooth entries, so that only
`log 2, 3, 5, 7` would be needed, and found none. I switched to the generic `2^k·y` series bounds
instead, which work for any rational. The Python generator for the `exLog2_bd*` lemmas and the
numerical scripts are in the session scratch directory and are not part of the repo. The bounds
are re-proved by `norm_num` inside the certificate, so they do not need to be trusted.
The same holds for the LP/sympy scripts that produced `Gpoly` and its certificate: Lean re-checks
the final identities with `ring`.

## Verification

- `lake build InfoTheory.Known.Certificates.SdpiKlVsChisqEquality` succeeds, with no warnings in
  the new code.
- `#print axioms statement_false` gives `[propext, Classical.choice, Quot.sound]`.
- `python3 scripts/verify_proof.py --verify sdpi-kl-vs-chisq-equality` prints:
  `VERIFIED sdpi-kl-vs-chisq-equality: OK disproof of InfoTheory.Problems.SdpiKlVsChisqEquality.Statement; axioms: #[propext, Quot.sound, Classical.choice] (leanchecker + CheckSolution passed)`.
- Numerics (numpy) re-confirm:
  - the eigenvalues `{1, 0.3, 0.2}` of `diag(√Q) W diag(1/√Q)`;
  - the earlier attempt's ribbon violation, `+0.002504` bits;
  - the max violation over all `R` at `(1.27, 4)`, `≈ 0.00223` nats;
  - the grid supremum of claim 6.

## Dead ends

- **Symmetric or product instances with structurally provable equality.**
  - DSBS / BSC with uniform input satisfies the conclusion (Bonami–Beckner).
  - Products of DSBS's: `s_KL` and `s_χ²` tensorize as `max`, and the ribbon tensorizes as an
    intersection. The product therefore again satisfies the conclusion.
  - A product of a "bad-ribbon" component (with `s_KL₁ < ρ₂²`) and a DSBS(ρ₂) might break the
    conclusion while keeping two-sided equality. But it would need three things: Lean
    tensorization of `s_KL` (a chain-rule argument not in `Bridge/`), the DSBS equality
    `s_KL = ρ²` (Ahlswede–Gács, uncertified), and a component whose ribbon fails at ratio `ρ₂²`.
    That is not easier than claim 6.
- **Erasure channels.** Forward `D(PW‖QW) = (1-ε)·D(P‖Q)` holds exactly, so the forward equality
  is free. But the reverse constant satisfies `s_KL(QY, Wrev) > ρ²` in general: point masses on
  non-erased outputs give ratios `log(1/Q(x)) / (log(1/Q(x)) + log(1/(1-ε)))`. So the two-sided
  hypothesis fails.
- **Junk-value shortcuts.** All `sSup` sets are nonempty and bounded for full-support inputs
  (certified by `sdpiKLAt_le_one` and `sdpiChiSqAt_le_one`), and the KL/χ² definitions have no
  `log 0` junk under `AbsCont`. No degenerate instance satisfies the hypotheses and violates the
  conclusion.

## References

- `attempts/sdpi-kl-vs-chisq-equality/2026-11-27-antigravity-counterexample.md`: the instance
  and the `[sketch]` of claim 6, which this attempt extends.
- `lean/InfoTheory/Known/Certificates/SdpiKlVsChisqEquality.lean`:
  - first version: `exQ`, `exW`, `sdpiChiSqAt_ex`, `sdpiKLAt_ex_ge`, `ex_not_ribbon`,
    `sdpiKLAt_ex_le_of`, `not_statement_of_sdpiKLAt_ex_le`;
  - this version: `gSym_hasSum`, `gSym_le_partial`, `gSym_ge4`, `Gpoly`, `Gpoly_pos`,
    `Gpoly_neg`, `poly_step`, `gSym_x5_le`, `gSym_out_le`, `core_ineq`, `group_id`,
    `kl_ex_global`, `sdpiKLAt_ex_le`, `sdpiKLAt_ex`, `statement_false`.
- `lean/InfoTheory/Solutions/SdpiKlVsChisqEquality.lean`: `disproof`.
- R. Ahlswede, P. Gács, "Spreading of sets in product spaces and hypercontraction of the Markov
  operator", Ann. Probab. 4 (1976).
- C. Nair, "Equivalent formulations of hypercontractivity using information measures", IZS 2014
  (the KL form of the ribbon used in `inNairRibbon`).
