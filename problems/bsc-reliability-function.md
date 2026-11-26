---
id: bsc-reliability-function
title: Exact Reliability Function of the Binary Symmetric Channel Below the Critical Rate
status: open
category: channel-capacity
posed_by: Claude E. Shannon, Robert G. Gallager, and Elwyn R. Berlekamp
posed_year: 1967
tags: [channel-capacity, error-exponent, bsc, reliability-function, coding-theory]
lean_module: InfoTheory.Problems.BscReliabilityFunction
lean_file: lean/InfoTheory/Problems/BscReliabilityFunction.lean
---

## Statement

Fix a crossover probability $p \in (0, 1/2)$ and consider the Binary Symmetric Channel $\mathsf{BSC}(p)$, whose Shannon capacity is $C(p) = 1 - h(p)$ bits per channel use. For any rate $R \in (0, C(p))$, let
$$E(\mathsf{BSC}(p), R) := \limsup_{n \to \infty} -\frac{1}{n} \log_2 P_e^*\!\left(\mathsf{BSC}(p), n, \lceil 2^{nR} \rceil\right)$$
be its reliability function (optimal error exponent, in bits), where $P_e^*(\mathsf{BSC}(p), n, M)$ is the minimum average block error probability over all $(n, M)$ block codes. Let $E_r(\mathsf{BSC}(p), R)$ and $E_{\mathrm{ex}}(\mathsf{BSC}(p), R)$ denote Gallager's random-coding and expurgated error exponents, respectively.

**Conjecture (Tightness of the Random-Coding and Expurgated Bounds for the BSC).** For every crossover probability $p \in (0, 1/2)$ and every rate $R \in (0, 1 - h(p))$,
$$E(\mathsf{BSC}(p), R) \;=\; \max\!\big(E_r(\mathsf{BSC}(p), R),\; E_{\mathrm{ex}}(\mathsf{BSC}(p), R)\big).$$

## Background

For rates above the critical rate $R_{\mathrm{crit}}(p) = 1 - h\!\big(\frac{\sqrt{p}}{\sqrt{p} + \sqrt{1-p}}\big)$, the reliability function of the BSC is known exactly: Gallager's random-coding lower bound $E_r(R)$ matches the Shannon–Gallager–Berlekamp sphere-packing upper bound $E_{\mathrm{sp}}(R)$. In the zero-rate limit $R \to 0^+$, Shannon, Gallager, and Berlekamp (1967) likewise proved $E(0^+) = E_{\mathrm{ex}}(0^+) = -\frac{1}{2}\log_2(2\sqrt{p(1-p)})$.

For **every** strictly intermediate rate $0 < R < R_{\mathrm{crit}}(p)$, however, the exact value of $E(\mathsf{BSC}(p), R)$ has remained unknown for nearly sixty years. On $(0, R_{\mathrm{crit}}(p))$, the best known lower bound is $\max(E_r(R), E_{\mathrm{ex}}(R))$ — where $E_{\mathrm{ex}}(R) = -\delta_{\mathrm{GV}}(R)\log_2(2\sqrt{p(1-p)})$ directly reflects the Gilbert–Varshamov minimum distance $\delta_{\mathrm{GV}}(R) = h^{-1}(1 - R)$ — while the best known upper bounds come from combining sphere-packing with minimum-distance / linear-programming (JPL) bounds (McEliece–Rodemich–Rumsey–Welch 1977; Litsyn 1999; Barg–McGregor 2005). Notably, disproving the conjecture at sufficiently small $R$ via a high-distance binary code family would resolve the Gilbert–Varshamov conjecture in the negative, whereas proving it would establish the asymptotic optimality of random/expurgated binary coding across all rates.

## What is known

- **High rates $R_{\mathrm{crit}}(p) \le R < 1 - h(p)$ (Elias, 1955; Gallager, 1965; Shannon–Gallager–Berlekamp, 1967):** $E(R) = E_r(R) = E_{\mathrm{sp}}(R)$ exactly.
- **Zero-rate limit (Shannon–Gallager–Berlekamp, 1967):** $\lim_{R \to 0^+} E(R) = E_{\mathrm{ex}}(0^+) = -\frac{1}{2}\log_2(2\sqrt{p(1-p)})$.
- **Lower bounds for $0 < R < R_{\mathrm{crit}}(p)$ (Gallager, 1965):** $E(R) \ge \max(E_r(R), E_{\mathrm{ex}}(R))$, where $E_{\mathrm{ex}}(R)$ dominates on $(0, R_{\mathrm{ex}}(p))$ and $E_r(R)$ dominates on $(R_{\mathrm{ex}}(p), R_{\mathrm{crit}}(p))$. No code sequence is known to beat this lower bound for any $p \in (0, 1/2)$ and $R \in (0, R_{\mathrm{crit}}(p))$.
- **Upper bounds for $0 < R < R_{\mathrm{crit}}(p)$ (Shannon–Gallager–Berlekamp, 1967; McEliece–Omura, 1977; Litsyn, 1999; Barg–McGregor, 2005):** The straight-line bound of SGB, minimum-distance bounds via MRRW, and Litsyn's / Barg–McGregor's distance-distribution bounds strictly improve upon $E_{\mathrm{sp}}(R)$ below $R_{\mathrm{crit}}(p)$, yet a strict gap to $\max(E_r(R), E_{\mathrm{ex}}(R))$ persists at every $0 < R < R_{\mathrm{crit}}(p)$.
- **Contrast with large-$q$ channels:** For $q$-ary symmetric channels with $q \ge 49$, algebraic-geometric codes beat the $q$-ary Gilbert–Varshamov bound and strictly surpass $E_{\mathrm{ex}}(R)$ (Katsman–Tsfasman–Vlăduţ 1984), whereas for $q = 2$ (the BSC) no improvement over $\max(E_r, E_{\mathrm{ex}})$ is known.

## References

- C. E. Shannon, R. G. Gallager, and E. R. Berlekamp, "Lower bounds to error probability for coding on discrete memoryless channels I & II," *Information and Control*, 10(1):65–103 and 10(5):522–552, 1967.
- R. G. Gallager, "A simple derivation of the coding theorem and some applications," *IEEE Trans. Inf. Theory*, 11(1):3–18, 1965.
- R. J. McEliece, E. R. Rodemich, H. Rumsey Jr., and L. R. Welch, "New upper bounds on the rate of a code via the Delsarte–MacWilliams inequalities," *IEEE Trans. Inf. Theory*, 23(2):157–166, 1977.
- S. Litsyn, "New upper bounds on error exponents," *IEEE Trans. Inf. Theory*, 45(2):385–398, 1999.
- A. Barg and A. McGregor, "Distance distribution of binary codes and the error probability of decoding," *IEEE Trans. Inf. Theory*, 51(12):4237–4246, 2005.
