---
problem: sdpi-kl-vs-chisq-equality
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

I checked whether the counterexample in `2026-11-27-antigravity-counterexample.md` can be turned
into a Lean `theorem disproof : ¬ Statement`. Everything except one global inequality is now
machine-checked in `lean/InfoTheory/Known/Certificates/SdpiKlVsChisqEquality.lean`. That
includes the conditional reduction
`not_statement_of_sdpiKLAt_ex_le : sdpiKLAt exQ exW ≤ 9/100 → ¬ Statement`. The step still open
is the upper bound `s_KL(Q, W) ≤ 9/100`. It says `D(PW‖Q) ≤ (9/100)·D(P‖Q)` for **every** `P` in
the 2-simplex, with equality reached only in the limit `P → Q`. That attempt itself labels this
step `[sketch]`, and it is the only thing blocking a formal disproof. No `Solutions/` file was
written: a disproof cannot be completed without this inequality.

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
6. **[heuristic]** (numerical, consistent with the earlier attempt's claim 2)
   `sup_P D(PW‖Q)/D(P‖Q) = 9/100`. A grid search over `P ∈ Δ₃` with step `1/1500`, boundary
   included, gives a maximum ratio of `0.0899999…` at the grid point nearest `Q`. It is never above
   `9/100`. This is evidence, not proof.

## Details

**Why claim 6 blocks a formal disproof.** The inequality is global and transcendental in two
variables. It is tight to second order at `P = Q` along the eigendirection `d` (eigenvalue
`3/10`). Along that direction the slack is only fourth order:
`(9/100)·h(y) - h(3y/10) = Θ(y⁴)`. The sketch in the earlier attempt has the right shape, but
proving it in Lean needs four pieces:

- (a) The KL grouping identity in the `(x, y)` parametrisation, including the boundary cases
  `s = 0` and `d = ±s` (Lean's `log 0 = 0` convention makes these separate cases).
- (b) The binary contraction `h(z/5) ≤ (1/25)·h(z)` on `[-1, 1]`. This is Ahlswede–Gács for
  BSC(2/5) at uniform input. The certificate header lists it as *not* certified.
- (c) Polynomial upper and lower bounds on `h`, valid all the way to `|z| = 1`.
- (d) Positivity of a degree-8 bivariate polynomial on a box. Its leading part is a *weighted*
  homogeneous form in `(x, y²)`, `-0.025x² + 0.018xy² - 0.0034y⁴`. That is the regime where
  `nlinarith` and `positivity` need a hand-built SOS or Positivstellensatz certificate.

Also, the earlier attempt's derivation of `u ≤ 1/2` and the reduction to `(x, y)` with `y = |d|/s`
were not re-derived here. I estimate (a)–(d) at well over the ~90-minute budget of this session.
The other ingredients (claims 1–5) took about an hour in total.

**Ribbon witness generation.** I searched for witnesses with smooth entries, so that only
`log 2, 3, 5, 7` would be needed, and found none. I switched to the generic `2^k·y` series bounds
instead, which work for any rational. The Python generator for the `exLog2_bd*` lemmas and the
numerical scripts are in the session scratch directory and are not part of the repo. The bounds
are re-proved by `norm_num` inside the certificate, so they do not need to be trusted.

## Verification

- `lake build InfoTheory.Known.Certificates.SdpiKlVsChisqEquality` succeeds, with only
  deprecation and lint warnings.
- `#print axioms` on `not_statement_of_sdpiKLAt_ex_le` and on `sdpiKLAt_ex_le_of` gives
  `[propext, Classical.choice, Quot.sound]`.
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
- `lean/InfoTheory/Known/Certificates/SdpiKlVsChisqEquality.lean`: new lemmas `exQ`, `exW`,
  `sdpiChiSqAt_ex`, `sdpiKLAt_ex_ge`, `ex_not_ribbon`, `sdpiKLAt_ex_le_of`, and
  `not_statement_of_sdpiKLAt_ex_le`.
- R. Ahlswede, P. Gács, "Spreading of sets in product spaces and hypercontraction of the Markov
  operator", Ann. Probab. 4 (1976).
- C. Nair, "Equivalent formulations of hypercontractivity using information measures", IZS 2014
  (the KL form of the ribbon used in `inNairRibbon`).
