---
id: dmc-zero-rate-error-exponent
title: Tightness of the Expurgated and Random-Coding Exponents for Binary-Input DMCs
status: open
category: channel-capacity
posed_by: Claude E. Shannon, Robert G. Gallager, and Elwyn R. Berlekamp; Marco Dalai
posed_year: 1967
tags: [channel-capacity, error-exponent, expurgated-bound, dmc, reliability-function]
lean_module: InfoTheory.Problems.DmcZeroRateErrorExponent
lean_file: lean/InfoTheory/Problems/DmcZeroRateErrorExponent.lean
---

## Statement

Let $W : \{0, 1\} \to \mathcal{Y}$ be a binary-input Discrete Memoryless Channel (DMC) over a finite output alphabet $\mathcal{Y}$ with Shannon capacity $C(W) > 0$. For $R \in (0, C(W))$, let $E(W, R)$ be its reliability function, $E_r(W, R)$ Gallager's random-coding exponent, and $E_{\mathrm{ex}}(W, R)$ Gallager's expurgated exponent.

**Conjecture (Low-Rate Tightness for Binary-Input DMCs).** For every finite output alphabet $\mathcal{Y}$, every binary-input DMC $W : \{0, 1\} \to \mathcal{Y}$, and every rate $R \in (0, C(W))$,
$$E(W, R) \;=\; \max\!\big(E_r(W, R),\; E_{\mathrm{ex}}(W, R)\big).$$

## Background

In their classic 1967 papers, Shannon, Gallager, and Berlekamp (SGB) established the sphere-packing upper bound $E_{\mathrm{sp}}(W, R)$, the straight-line upper bound, and the exact zero-rate error exponent $E(W, 0^+) = E_{\mathrm{ex}}(W, 0^+)$ for every DMC with zero-error capacity $C_0(W) = 0$. For general DMCs at low positive rates $0 < R < R_{\mathrm{crit}}(W)$, a strict gap separates the random-coding/expurgated lower bound $\max(E_r(W, R), E_{\mathrm{ex}}(W, R))$ from the sphere-packing and straight-line upper bounds.

SGB originally asked whether Gallager's expurgated bound (or its multi-letter version) is tight at low rates for general DMCs. For large input alphabets ($|\mathcal{X}| \ge 49$), Katsman, Tsfasman, and Vlăduţ (1984) disproved tightness via algebraic-geometric codes over $q$-ary symmetric channels, and Dalai and Polyanskiy (2018) gave elementary counterexamples to even the multi-letter expurgated bound on small-alphabet ($|\mathcal{X}| \in \{4, 5\}$) typewriter channels. For **binary-input DMCs** ($|\mathcal{X}| = 2$), however — including both symmetric and asymmetric binary-input channels — no counterexample is known and the exact low-rate reliability function between $0$ and $R_{\mathrm{crit}}(W)$ remains completely open.

## What is known

- **High rates $R \ge R_{\mathrm{crit}}(W)$ (Gallager, 1965; SGB, 1967):** $E(W, R) = E_r(W, R) = E_{\mathrm{sp}}(W, R)$ for every DMC $W$.
- **Zero-rate limit (SGB, 1967):** Whenever $C_0(W) = 0$ (which holds for every binary-input DMC whose two output distributions have overlapping support), $\lim_{R \to 0^+} E(W, R) = E_{\mathrm{ex}}(W, 0^+)$ exactly.
- **Refutation for $|\mathcal{X}| \ge 4$ (Katsman–Tsfasman–Vlăduţ, 1984; Dalai–Polyanskiy, 2018):** Both the single-letter and multi-letter expurgated bounds can be strictly loose for DMCs with $|\mathcal{X}| \ge 4$ inputs (e.g., $49$-ary symmetric channels and $4$- or $5$-input typewriter channels).
- **Lovász-theta and linear-programming upper bounds (Dalai, 2013; Dalai–Polyanskiy, 2018):** Dalai generalized Lovász's $\vartheta$ function to channel reliability, yielding sharpened upper bounds on $E(W, R)$ near $C_0(W)$ for channels with zero-probability transitions.
- **Binary-input DMCs ($|\mathcal{X}| = 2$) at $0 < R < R_{\mathrm{crit}}(W)$:** Whether $E(W, R) = \max(E_r(W, R), E_{\mathrm{ex}}(W, R))$ holds for every binary-input DMC (and even for asymmetric binary-input channels such as the Z-channel or binary erasure-error channels) remains open.

## References

- C. E. Shannon, R. G. Gallager, and E. R. Berlekamp, "Lower bounds to error probability for coding on discrete memoryless channels I & II," *Information and Control*, 10(1):65–103 and 10(5):522–552, 1967.
- G. L. Katsman, M. A. Tsfasman, and S. G. Vlăduţ, "Modular curves and codes with a polynomial construction," *IEEE Trans. Inf. Theory*, 30(2):353–355, 1984.
- M. Dalai, "Lower bounds on the probability of error for classical and classical-quantum channels," *IEEE Trans. Inf. Theory*, 59(12):8027–8056, 2013.
- M. Dalai and Y. Polyanskiy, "Bounds on the reliability of a typewriter channel," *Proc. IEEE Int. Symp. Information Theory (ISIT)*, pp. 1728–1732, 2018.
- I. Csiszár and J. Körner, *Information Theory: Coding Theorems for Discrete Memoryless Systems*, 2nd ed., Cambridge University Press, 2011.
