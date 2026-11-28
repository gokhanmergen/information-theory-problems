---
id: hypercontractivity-ribbon-discrete
title: Computable Characterization and Two-Valued Extremizers of the Discrete Hypercontractivity Ribbon
status: open
category: statistical-info-theory
posed_by: Venkat Anantharam, Amin Gohari, Sudeep Kamath, and Chandra Nair
posed_year: 2013
tags: [hypercontractivity, strong-data-processing, discrete-sources, functional-inequalities]
lean_module: InfoTheory.Problems.HypercontractivityRibbonDiscrete
lean_file: lean/InfoTheory/Problems/HypercontractivityRibbonDiscrete.lean
---

## Statement

For a finite discrete bipartite source $(X, Y) \sim P_{XY}$ over $\mathcal{X} \times \mathcal{Y}$, the (forward) **hypercontractivity ribbon** $\mathcal{R}(P_{XY})$ is the set of exponent pairs $(p, q)$ with $1 \le p \le q$ such that for all nonnegative functions $f : \mathcal{X} \to \mathbb{R}_{\ge 0}$ and $g : \mathcal{Y} \to \mathbb{R}_{\ge 0}$,
$$
\mathbb{E}_{P_{XY}}[f(X) g(Y)] \le \|f(X)\|_p \, \|g(Y)\|_{q'}, \qquad \frac{1}{q} + \frac{1}{q'} = 1.
$$
Nair (2014) proved the exact information-theoretic equivalence: $(p, q) \in \mathcal{R}(P_{XY})$ if and only if for every joint distribution $Q_{XY} \ll P_{XY}$,
$$
\frac{1}{p} D_{\mathrm{KL}}(Q_X \mathbin{\|} P_X) + \left(1 - \frac{1}{q}\right) D_{\mathrm{KL}}(Q_Y \mathbin{\|} P_Y) \le D_{\mathrm{KL}}(Q_{XY} \mathbin{\|} P_{XY}).
$$

**Determine a tractable, explicitly computable characterization of the boundary of $\mathcal{R}(P_{XY})$ for general discrete bipartite sources — and in particular, for the canonical symmetric non-binary test case of the $q$-ary symmetric channel $\mathrm{QSC}(q, \alpha)$ with uniform input ($q \ge 3$), resolve the Two-Valued Extremizer Conjecture (formalized in Lean):**

Does $(p, q_2) \in \mathcal{R}(P_{XY})$ hold for the uniform-input $q$-ary symmetric channel whenever the hypercontractive norm inequality $\mathbb{E}[f(X) g(Y)] \le \|f\|_p \|g\|_{q_2'}$ holds for all **two-valued** nonnegative functions $f, g : \mathrm{Fin}\, q \to \mathbb{R}_{\ge 0}$?

## Background

Hypercontractivity inequalities (Bonami 1970; Beckner 1975; Borell 1982) are among the most powerful tools in discrete analysis, coding theory, and statistical information theory, underlying sharp reverse-Brascamp–Lieb bounds, noise stability, non-interactive correlation distillation, and strong converses. Anantharam, Gohari, Kamath, and Nair (2013) and Nair (2014) reformulated hypercontractivity purely in terms of mutual information and KL divergence, proving tensorization and unifying forward and reverse hypercontractivity with strong data processing inequalities.

Yet checking Nair's KL inequality requires minimizing a *non-convex* difference of KL divergences over $\Delta(\mathcal{X} \times \mathcal{Y})$, and even for the simplest symmetric channel beyond the binary symmetric channel — the $q$-ary symmetric channel for $q \ge 3$ — the exact hypercontractivity ribbon is unknown across general $(p, q_2)$!

## What is known

- **Exact solved ribbons:**
  - **Doubly symmetric binary source ($\mathrm{BSC}(\alpha)$ with uniform input):** $\mathcal{R}(P_{XY}) = \{(p, q) : \frac{p-1}{q-1} \ge (1 - 2\alpha)^2\}$ (Bonami 1970; Beckner 1975).
  - **Bivariate Gaussian source:** $\mathcal{R}(P_{XY}) = \{(p, q) : \frac{p-1}{q-1} \ge \rho^2\}$ (Nelson 1973; Borell 1982).
  - **Binary erasure source ($\mathrm{BEC}(\varepsilon)$):** $\mathcal{R}(P_{XY})$ has been determined explicitly (Nair 2014; Polyanskiy–Wu 2017).
- **Information-theoretic equivalences and tensorization:** Nair (2014) and Beigi–Gohari (2015) proved equivalence of the functional, KL-divergence, and concave-envelope formulations, as well as exact tensorization $\mathcal{R}(P_{XY}^{\otimes n}) = \mathcal{R}(P_{XY})$.
- **Partial results on the $q$-ary symmetric channel ($q \ge 3$):**
  - The continuous-time log-Sobolev constant of the complete graph $K_q$ was computed exactly by Diaconis and Saloff-Coste (1996), with a **two-valued** extremizer; this determines the tangent slope of the ribbon at $p = 2$ in the continuous-time limit.
  - Polyanskiy and Samorodnitsky (2019) and Kamath–Anantharam / Nair–Wang established sharp bounds and studied extremal functions for the discrete-time $q$-ary symmetric channel; however, whether two-valued functions are globally extremal across all $(p, q_2)$ and $\alpha \in (0, 1)$ — and how to efficiently compute $\mathcal{R}(P_{XY})$ for general discrete sources — remains open.

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful.** `inFullHypercontractivityRibbon` is Nair's KL form of `E[f(X)g(Y)] ≤ ‖f‖_p ‖g‖_{q'}`. All `rpow`s act on nonnegative bases with `q' = q/(q-1)` finite. Since `m ≥ 3`, the two-valued test is a genuine restriction. A literature search (2026-11) found no resolution.
- **Certificate** `lean/InfoTheory/Known/Certificates/HypercontractivityRibbonDiscrete.lean` (kernel-checked, standard axioms only) proves:
  - marginal KL data processing;
  - every `(p, p)` is in every ribbon;
  - **regression at `α = 0`** (`ρ = 1`): the ribbon is exactly `p = q` (`identity_ribbon_iff`), and for `p < q` the two-valued test already fails (`identity_twoValued_fails`), so the implication holds there;
  - **regression at `α = (m-1)/m`** (independent `X`, `Y`): the ribbon is all of `1 < p ≤ q` (`independent_ribbon`).
- Not certified: the doubly-symmetric binary ribbon for `0 < α < 1/2`, and Nair's functional/KL equivalence.

## References

- W. Beckner, "Inequalities in Fourier analysis," *Ann. of Math.* **102**(1), 159–182 (1975).
- P. Diaconis and L. Saloff-Coste, "Logarithmic Sobolev inequalities for finite Markov chains," *Ann. Appl. Probab.* **6**(3), 695–750 (1996).
- V. Anantharam, A. Gohari, S. Kamath, and C. Nair, "On maximal correlation, hypercontractivity, and the data processing inequality studied by Erkip and Cover," *arXiv:1304.2333* (2013).
- E. Mossel, K. Oleszkiewicz, and A. Sen, "On reverse hypercontractivity," *Geom. Funct. Anal.* **23**, 1062–1097 (2013).
- C. Nair, "Equivalent formulations of hypercontractivity using information measures," *Proc. Int. Zurich Seminar on Communications (IZS)* (2014).
- S. Beigi and A. Gohari, "On the duality of additivity and tensorization," *Proc. IEEE ISIT*, 2381–2385 (2015).
- Y. Polyanskiy and A. Samorodnitsky, "Improved log-Sobolev inequalities, hypercontractivity and uncertainty principle on the hypercube," *J. Funct. Anal.* **277**(11), 108280 (2019).
