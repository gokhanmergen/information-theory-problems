---
id: deletion-channel-small-d-asymptotics
title: Small-Deletion-Probability Asymptotic Expansion of the Binary Deletion Channel
status: partially-solved
category: channel-capacity
posed_by: Yashodhan Kanoria and Andrea Montanari
posed_year: 2013
tags: [channel-capacity, deletion-channel, asymptotics, synchronization]
lean_module: InfoTheory.Problems.DeletionChannelSmallDAsymptotics
lean_file: lean/InfoTheory/Problems/DeletionChannelSmallDAsymptotics.lean
---

## Statement

Let $C(d)$ denote the Shannon capacity (in bits per channel use) of the i.i.d. binary deletion channel with deletion probability $d \in (0, 1)$, and let $h(d) = -d \log_2 d - (1 - d) \log_2(1 - d)$ be the binary entropy function. Define the Kanoria–Montanari first-order correction constant
$$c_1 := \left(\sum_{\ell = 1}^{\infty} 2^{-\ell - 1} \ell \log_2 \ell\right) - 1 \;\approx\; 0.2885.$$

Kanoria and Montanari (2013) proved that as $d \to 0^+$,
$$C(d) = 1 - h(d) + c_1\, d + c_2\, d^2 + O(d^{3 - \varepsilon})$$
for every $\varepsilon > 0$ (equivalently $C(d) = 1 + d \log_2 d - A_1 d + O(d^{2 - \varepsilon})$ with $A_1 = \log_2(2e) - \sum_{\ell=1}^\infty 2^{-\ell-1}\ell\log_2 \ell \approx 1.1542$).

**Open Problem (All-Orders Expansion / Real-Analyticity at $d = 0^+$).** Does the excess capacity $C(d) - (1 - h(d))$ admit a convergent power-series expansion in a right neighborhood of $d = 0$ — i.e., do there exist $\delta > 0$ and real coefficients $(c_k)_{k \ge 1}$ with $c_1 = (\sum_{\ell=1}^\infty 2^{-\ell-1} \ell \log_2 \ell) - 1$ such that
$$C(d) = 1 - h(d) + \sum_{k=1}^{\infty} c_k\, d^k \qquad \text{for all } d \in (0, \delta)?$$

## Background

In the small-deletion regime $d \to 0^+$, the binary deletion channel behaves to leading order like a binary erasure channel minus the position entropy $h(d)$ of the deleted bits, plus a positive correction $c_1 d$ reflecting the fact that deleting any bit inside a run of length $\ell$ yields the same output string (saving $\log_2 \ell$ bits of location uncertainty, offset by run mergers when length-1 runs vanish).

Kanoria and Montanari (2013) achieved a landmark breakthrough by turning this intuition into a rigorous cluster expansion up to order $O(d^{3-\varepsilon})$, proving that i.i.d. $\mathrm{Bern}(1/2)$ inputs are optimal to order $d$ and that a perturbed renewal (Markov) input process achieves capacity up to $O(d^{3-\varepsilon})$. However, their perturbation analysis encounters rapidly growing combinatorial complexity from multi-deletion clusters and does not establish whether the expansion continues to all orders without higher-order logarithmic singularities (such as $d^k \log d$ terms for $k \ge 3$), nor whether $C(d) - (1 - h(d))$ is real-analytic on $(0, \delta)$.

## What is known

- **First-order expansion (Kalai–Mitzenmacher–Sudan, 2010; Kanoria–Montanari, 2010/2013):** Kalai, Mitzenmacher, and Sudan proved $C(d) \ge 1 - h(d) + \Omega(d)$, showing the deletion channel strictly exceeds $1 - h(d)$ for small $d$. Kanoria and Montanari determined the exact linear coefficient $c_1 = (\sum_{\ell=1}^\infty 2^{-\ell-1}\ell\log_2\ell) - 1$ (equivalently $A_1 = \log_2(2e) - \sum_{\ell=1}^\infty 2^{-\ell-1}\ell\log_2\ell \approx 1.1542$).
- **Second-order expansion (Kanoria–Montanari, 2013):** Extended the rigorous expansion to $C(d) = 1 + d\log_2 d - A_1 d + A_2 d^2 + O(d^{3-\varepsilon})$ with an explicit formula for $A_2$ achieved by a perturbed renewal input distribution.
- **Higher orders ($k \ge 3$) and analyticity:** Whether the remainder is $O(d^3)$ (without $d^3 \log d$ terms), whether all higher-order coefficients exist, and whether $C(d) - (1 - h(d))$ is real-analytic near $d = 0^+$ remain open.

## References

- A. Kalai, M. Mitzenmacher, and M. Sudan, "Tight asymptotic bounds for the deletion channel with small deletion probabilities," *Proc. IEEE Int. Symp. Information Theory (ISIT)*, pp. 997–1001, 2010.
- Y. Kanoria and A. Montanari, "Optimal coding for the binary deletion channel with small deletion probability," *IEEE Trans. Inf. Theory*, 59(10):6192–6219, 2013 (arXiv:1104.5546).
- M. Mitzenmacher, "A survey of results for deletion channels and related synchronization channels," *Probability Surveys*, 6:1–33, 2009.
