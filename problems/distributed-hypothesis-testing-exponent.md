---
id: distributed-hypothesis-testing-exponent
title: Optimal Type-II Error Exponent for General Two-Terminal Distributed Hypothesis Testing
status: open
category: statistical-info-theory
posed_by: Rudolf Ahlswede and Imre Csiszár
posed_year: 1986
tags: [hypothesis-testing, error-exponents, multiterminal, binning, single-letterization]
lean_module: InfoTheory.Problems.DistributedHypothesisTestingExponent
lean_file: lean/InfoTheory/Problems/DistributedHypothesisTestingExponent.lean
---

## Statement

Two distributed terminals observe i.i.d. sequences $X^n$ and $Y^n$ drawn jointly from either $P_{XY}$ (null hypothesis $H_0$) or $Q_{XY}$ (alternative hypothesis $H_1$, with $P_{XY} \ll Q_{XY}$) over finite alphabets $\mathcal{X} \times \mathcal{Y}$. The encoder observes $X^n$ and sends a message $M = f_n(X^n) \in \{1, \dots, \lfloor 2^{n R} \rfloor\}$ at rate $R > 0$ to the decoder, which observes $(M, Y^n)$ and chooses an acceptance region $\mathcal{A}_n$ for $H_0$. Let $\beta_n^*(R, \varepsilon)$ denote the minimum type-II error probability $Q_{XY}^{\otimes n}((f_n(X^n), Y^n) \in \mathcal{A}_n)$ subject to type-I error probability $P_{XY}^{\otimes n}((f_n(X^n), Y^n) \notin \mathcal{A}_n) \le \varepsilon$. The **optimal type-II error exponent** (in the Stein's lemma regime) is
$$
E^*(R, P, Q) := \lim_{\varepsilon \to 0^+} \limsup_{n \to \infty} -\frac{1}{n} \log_2 \beta_n^*(R, \varepsilon).
$$

**Determine a single-letter characterization of $E^*(R, P, Q)$ for general pairs $(P_{XY}, Q_{XY})$ and rates $R > 0$.**

In particular, while Watanabe (2022) and Kochman–Wang (2023) proved that the **Shimokawa–Han–Amari (1994) single-letter inner bound** $E_{\mathrm{SHA}}(R, P, Q)$ is strictly suboptimal for general (larger-alphabet) pairs $(P_{XY}, Q_{XY})$, the accompanying Lean statement formalizes whether $E_{\mathrm{SHA}}(R, P, Q)$ equals $E^*(R, P, Q)$ for all full-support **binary-alphabet** sources ($\mathcal{X} = \mathcal{Y} = \{0, 1\}$).

## Background

Posed by Ahlswede and Csiszár (1986) as the multiterminal generalization of the Chernoff–Stein lemma, distributed hypothesis testing under communication constraints sits at the intersection of statistical inference and multiterminal source coding. While Ahlswede and Csiszár completely solved **testing against independence** ($Q_{XY} = P_X \times P_Y$), moving to arbitrary alternative distributions $Q_{XY}$ introduces a subtle coupling between quantization, Wyner–Ziv binning, and large-deviations error events that has resisted a matching converse for four decades.

## What is known

- **Testing against independence ($Q_{XY} = P_X \times P_Y$):** Ahlswede and Csiszár (1986) proved
  $$
  E^*(R, P, P_X \times P_Y) = \max_{U - X - Y,\; I(U; X) \le R} I(U; Y),
  $$
  and also established the zero-rate exponent $E^*(0^+, P, Q)$ for general $(P, Q)$ (Han 1987; Shalaby–Papamarcou 1992).
- **Han and Shimokawa–Han–Amari inner bounds:** Han (1987) proved a quantization-only single-letter lower bound; Shimokawa, Han, and Amari (1994) strengthened it via Wyner–Ziv binning to $E_{\mathrm{SHA}}(R, P, Q) \le E^*(R, P, Q)$.
- **Testing against conditional independence:** Rahman and Wagner (2012) proved that the Shimokawa–Han–Amari inner bound is **tight** when testing against conditional independence ($Q_{X, (Y, Z)} = P_{XZ} P_{Y|Z}$, where $(Y, Z)$ is observed at the decoder and $X \perp Y \mid Z$ under $H_1$), demonstrating that Wyner–Ziv binning is genuinely optimal in a broad non-trivial class.
- **Improved converses and open gap:** Watanabe (2022) and Weinberger–Kochman / Rahman–Wagner developed stronger outer bounds and second-order analyses, yet for general positive-rate pairs $(P_{XY}, Q_{XY})$ beyond conditional independence, whether $E^*(R, P, Q) = E_{\mathrm{SHA}}(R, P, Q)$ holds in general remains open.

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful.**
  - `shaInnerBoundRaw` matches the SHA exponent: Markov chain `U - X - Y`, `Q̃ = P_{U|X} Q`, binning rate `I(U;X|Y) ≤ R`, the binning term `D + R - I(U;X|Y)` under `H_P(U|Y) ≤ H_{P̃}(U|Y)`, and no binning term when `I(U;X) ≤ R`.
  - The absolute-continuity guards rule out `log 0` junk, and full support makes every set nonempty and bounded.
  - The known counterexamples to SHA optimality use non-binary alphabets: Watanabe (arXiv:2201.13005) uses a product of two DSBSs, and Kochman–Wang (arXiv:2306.14499, Example 3) use ternary `X`. The binary case is still open as of 2026-11; Girish–Cung–Telatar (arXiv:2601.10526) study only linear codes.
- **Certificate** `lean/InfoTheory/Known/Certificates/DistributedHypothesisTestingExponent.lean` (kernel-checked, standard axioms only) proves:
  - `E* ≥ 0`, because exponent `0` is always achievable;
  - **regression:** `E*(R, P, P) = 0` (`dhtOptimalExponent_self`), the Stein value `D(P‖P) = 0`;
  - `E_SHA ≥ 0`, together with its raw version.
- Not certified: SHA achievability, the Ahlswede–Csiszár testing-against-independence formula, and `E_SHA(R, P, P) = 0`.

## References

- R. Ahlswede and I. Csiszár, "Hypothesis testing with communication constraints," *IEEE Trans. Inf. Theory* **32**(4), 533–542 (1986).
- T. S. Han, "Hypothesis testing with multiterminal data compression," *IEEE Trans. Inf. Theory* **33**(6), 759–772 (1987).
- H. Shimokawa, T. S. Han, and S. Amari, "Error bound of hypothesis testing with data compression," *Proc. IEEE ISIT*, 114 (1994).
- M. S. Rahman and A. B. Wagner, "On the optimality of binning for distributed hypothesis testing," *IEEE Trans. Inf. Theory* **58**(10), 6282–6303 (2012).
- S. Watanabe, "Neyman–Pearson test for zero-rate multiterminal hypothesis testing," *IEEE Trans. Inf. Theory* **64**(7), 4923–4939 (2018).
- S. Watanabe, "A converse bound on the error exponent of distributed hypothesis testing," *IEEE Trans. Inf. Theory* **68**(1), 2022.
