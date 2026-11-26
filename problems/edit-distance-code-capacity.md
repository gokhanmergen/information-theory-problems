---
id: edit-distance-code-capacity
title: Zero-Rate Threshold and Capacity of Binary Adversarial Deletion Codes
status: partially-solved
category: coding-theory
posed_by: Vladimir I. Levenshtein; Boris Bukh, Venkatesan Guruswami, and Johan Håstad
posed_year: 1966
tags: [coding-theory, deletion-codes, edit-distance, zero-rate-threshold]
lean_module: InfoTheory.Problems.EditDistanceCodeCapacity
lean_file: lean/InfoTheory/Problems/EditDistanceCodeCapacity.lean
---

## Statement

For binary strings $x, y \in \{0, 1\}^n$, their **deletion distance** is $d_{\mathrm{del}}(x, y) = n - \mathrm{LCS}(x, y)$ (half their edit/indel distance), where $\mathrm{LCS}(x, y)$ is the length of the longest common subsequence of $x$ and $y$. A binary code $C \subseteq \{0, 1\}^n$ corrects $t$ adversarial deletions if and only if $d_{\mathrm{del}}(x, y) > t$ for all distinct $x, y \in C$. Let $M_{\mathrm{del}}(n, t)$ be the maximum cardinality of such a code, and for $\delta \in (0, 1)$, define the asymptotic binary adversarial deletion code capacity
$$R_{\mathrm{del}}(\delta) = \limsup_{n \to \infty} \frac{1}{n} \log_2 M_{\mathrm{del}}(n, \lfloor \delta n \rfloor).$$
The **zero-rate threshold** is $\delta^* = \sup \{ \delta \in (0, 1) \mid R_{\mathrm{del}}(\delta) > 0 \}$.

Bukh, Guruswami, and Håstad (2017) proved that positive-rate binary codes exist for every deletion fraction $\delta < \sqrt{2} - 1 \approx 0.4142$, establishing $\delta^* \ge \sqrt{2} - 1$. Guruswami, He, and Li (2021) proved that $\delta^* < 1/2 - \varepsilon_0$ for a strictly positive absolute constant $\varepsilon_0 > 0$, disproving the long-standing hope that $\delta^* = 1/2$.

**Open Problem:** Determine the exact zero-rate threshold $\delta^*$ and the exact capacity curve $R_{\mathrm{del}}(\delta)$ for binary adversarial deletion codes. In particular, **does the zero-rate threshold strictly exceed the Bukh–Guruswami–Håstad bound $\sqrt{2} - 1$**, i.e., does there exist $\delta > \sqrt{2} - 1$ with $R_{\mathrm{del}}(\delta) > 0$?

## Background

Adversarial deletion (and insertion-deletion / edit-distance) codes were pioneered by Levenshtein (1966), who showed that Varshamov–Tenengolts codes are asymptotically optimal for a single deletion and bounded the maximum size of codes correcting a fixed number $t$ of deletions. For a constant fraction $\delta$ of worst-case deletions, however, the geometry of the deletion ball is notoriously non-uniform and non-transitive, defeating standard Hamming-space packing and linear-programming methods.

For decades, even the zero-rate threshold $\delta^*$ for binary deletion codes was unknown: while the Plotkin-type argument (every two strings among $\{0^n, 1^n, (01)^{n/2}\}$ share a common subsequence of length at least $n/2$) trivially forces $R_{\mathrm{del}}(1/2) = 0$, the best positive-rate constructions stalled far below $1/2$ until Bukh–Guruswami–Håstad (2017) reached $\sqrt{2} - 1$, and Guruswami–He–Li (2021) proved that $\delta^*$ is strictly bounded away from $1/2$. Closing the gap $\sqrt{2} - 1 \le \delta^* < 1/2$ and determining $R_{\mathrm{del}}(\delta)$ remain central open problems in coding theory and extremal combinatorics.

## What is known

- **Zero-rate threshold bounds:**
  - **Lower bound:** Schulman and Zuckerman (1999) constructed the first asymptotically good binary deletion codes (correcting a small constant fraction of deletions). Kash, Mitzenmacher, Thaler, and Ullman (2011) proved $\delta^* > 0.17$ via random codes. Bukh, Guruswami, and Håstad (2017) proved $\delta^* \ge \sqrt{2} - 1 \approx 0.41421$ using spans of carefully chosen periodic/oscillating patterns (and $1 - \frac{2}{q + \sqrt{q}}$ for $q$-ary alphabets).
  - **Upper bound:** Trivial $\delta^* \le 1/2$ (any 3 binary strings have a pair with $\mathrm{LCS} \ge n/2$, Bukh–Ma 2014). Guruswami, He, and Li (FOCS 2021 / IEEE TIT 2023) proved $\delta^* \le 1/2 - \varepsilon_0$ for an explicit constant $\varepsilon_0 > 0$ (specifically $\delta^* < 1/2 - 10^{-40}$), establishing that positive-rate binary deletion codes cannot approach $1/2$.
- **Small deletion fraction ($\delta \to 0^+$):**
  - The redundancy $1 - R_{\mathrm{del}}(\delta)$ satisfies $\Omega(\delta \log(1/\delta)) \le 1 - R_{\mathrm{del}}(\delta) \le O(\delta \log(1/\delta))$ (Levenshtein 1966; Haeupler–Shahrasbi 2017; Cheng–Jin–Li–Wu 2018), though the exact leading constant in front of $\delta \log_2(1/\delta)$ is not yet determined.
- **Large alphabets ($q \to \infty$):** Over large alphabets (growing with $1/\varepsilon$), Haeupler and Shahrasbi (2017) constructed explicit synchronization-string codes achieving rate $1 - \delta - \varepsilon$ for every $\delta < 1$, matching the Singleton bound.
- **Explicit binary codes:** Guruswami and Wang (2017), Haeupler (2019), and Con–Shpilka–Tamo (2022) constructed explicit polynomial-time encodable/decodable binary deletion codes in both the low-noise and high-noise regimes (up to $\sqrt{2} - 1 - \varepsilon$).

## References

- V. I. Levenshtein, "Binary codes capable of correcting deletions, insertions, and reversals," *Soviet Physics Doklady*, 10(8):707–710, 1966.
- L. J. Schulman and D. Zuckerman, "Asymptotically good codes correcting insertions, deletions, and transpositions," *IEEE Trans. Inf. Theory*, 45(7):2552–2557, 1999.
- I. Kash, M. Mitzenmacher, J. Thaler, and J. Ullman, "On the zero-error capacity threshold for deletion channels," *Proc. 49th Allerton Conf.*, pp. 1111–1118, 2011.
- B. Bukh and J. Ma, "Longest common subsequences in sets of words," *SIAM J. Discrete Math.*, 28(4):2042–2049, 2014.
- B. Bukh, V. Guruswami, and J. Håstad, "An improved bound on the fraction of correctable deletions," *IEEE Trans. Inf. Theory*, 63(1):93–103, 2017.
- B. Haeupler and A. Shahrasbi, "Synchronization strings: Codes for insertions and deletions approaching the Singleton bound," *Proc. 49th ACM STOC*, pp. 33–46, 2017.
- V. Guruswami, X. He, and R. Li, "The zero-rate threshold for adversarial bit-deletions is less than $1/2$," *IEEE Trans. Inf. Theory*, 69(4):2218–2239, 2023 (FOCS 2021).
