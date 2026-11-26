---
id: network-coding-capacity-decidability
title: Decidability of the Asymptotic Multi-Source Network Coding Capacity Region
status: partially-solved
category: network-coding
posed_by: X. Yan, Raymond W. Yeung, and Zhen Zhang
posed_year: 2007
tags: [network-coding, decidability, entropy-region, multi-source]
lean_module: InfoTheory.Problems.NetworkCodingCapacityDecidability
lean_file: lean/InfoTheory/Problems/NetworkCodingCapacityDecidability.lean
---

## Statement

Consider a finite directed acyclic multi-source network $\mathcal{N}$ on $V$ vertices with unit-capacity directed edges, $K$ independent sources located at vertices $s_1, \dots, s_K$, and arbitrary sink demands specifying which subset of sources each vertex must reconstruct. Let $C_{\mathrm{asymp}}(\mathcal{N})$ denote its **asymptotic (vanishing-error) symmetric network coding capacity**: the supremum of rates $R \ge 0$ such that for every $\varepsilon > 0$ there exist a blocklength $t \ge 1$ and local causal edge encoders transmitting $t$ bits per edge so that all sinks simultaneously recover their demanded messages (each of size $\lfloor 2^{t R} \rfloor$) with average error probability at most $\varepsilon$.

Yan, Yeung, and Zhang (2007) characterized the asymptotic multi-source network coding capacity region implicitly as a linear projection of the intersection of the closed almost-entropic cone $\overline{\Gamma^*_n}$ with network-induced linear constraints. In 2022–2023, Cheuk Ting Li proved that **exact zero-error solvability** of general network coding instances is algorithmically **undecidable**. However, the reduction to exact finite-alphabet zero-error solvability does not determine whether the **asymptotic** (vanishing-error / $\overline{\Gamma^*_n}$) capacity is algorithmically computable.

**Open Problem:** Is the asymptotic multi-source network coding capacity $C_{\mathrm{asymp}}(\mathcal{N})$ algorithmically **computable** (approximable to arbitrary rational precision $1/k$ by a halting Turing machine)? Equivalently, is membership in the asymptotic capacity region (up to an arbitrary tolerance $\varepsilon > 0$) decidable?

## Background

A central goal of network information theory is to compute the capacity region of an arbitrary multi-source, multi-sink acyclic communication network. For single-source multicast, the Ahlswede–Cai–Li–Yeung (2000) max-flow/min-cut theorem yields a polynomial-time computable characterization. For general multi-source networks, Yan, Yeung, and Zhang (2007, 2012) proved an exact inner-and-outer characterization in terms of the almost-entropic cone $\overline{\Gamma^*_n}$, establishing a deep equivalence between multi-source network coding capacity and the complete characterization of entropy vectors (and hence non-Shannon information inequalities).

Because $\overline{\Gamma^*_n}$ is non-polyhedral for $n \ge 4$ (Matúš 2007), even the basic question of algorithmic decidability—whether any Turing machine can decide network solvability or compute network capacity—remained open for decades. Cheuk Ting Li (2023) settled the **zero-error exact solvability** question negatively via a reduction from the uniform word problem for finite groups, leaving the computability of the **asymptotic** capacity region (and the decidability of unconstrained linear information inequalities over $\overline{\Gamma^*_n}$) as a major remaining open problem.

## What is known

- **Exact characterization via $\overline{\Gamma^*_n}$:** Yan, Yeung, and Zhang (2007, 2012) expressed the exact multi-source network coding capacity region in terms of $\Gamma^*_n$ and its closure $\overline{\Gamma^*_n}$. Chan and Grant (2008) showed a converse duality: characterizing $\overline{\Gamma^*_n}$ is equivalent to determining the capacity regions of all multi-source networks.
- **Shannon-type LP outer bound is computable but not tight:** Replacing $\overline{\Gamma^*_n}$ by the Shannon polymatroid cone $\Gamma_n$ gives a computable linear-programming outer bound, which is strictly loose for general networks (Dougherty–Freiling–Zeger 2007).
- **Undecidability of exact zero-error solvability (settled 2022–2023):** Cheuk Ting Li (IEEE TIT 2023, arXiv:2205.11461) proved that deciding whether a given network admits an exact zero-error scalar/vector network code of rate $1$ is **undecidable** (along with conditional information inequalities and conditional independence implication).
- **Asymptotic / vanishing-error capacity remains open:** As explicitly noted by Li (2023), the undecidability proof for exact zero-error solvability uses exact conditional independence / group-homomorphism constraints that break down under vanishing $\varepsilon$-error approximations; whether $C_{\mathrm{asymp}}(\mathcal{N})$ is computable (approximable to within any rational $\varepsilon > 0$) remains **open**.

## References

- X. Yan, R. W. Yeung, and Z. Zhang, "The capacity region for multi-source multi-sink network coding," *Proc. IEEE ISIT*, pp. 116–120, 2007.
- X. Yan, R. W. Yeung, and Z. Zhang, "An implicit characterization of the achievable rate region for acyclic multisource multisink network coding," *IEEE Trans. Inf. Theory*, 58(9):5625–5639, 2012.
- F. Matúš, "Infinitely many information inequalities," *Proc. IEEE ISIT*, pp. 41–44, 2007.
- T. H. Chan and A. Grant, "Dualities between entropy functions and network codes," *IEEE Trans. Inf. Theory*, 54(10):4470–4487, 2008.
- C. T. Li, "Undecidability of network coding, conditional information inequalities, and conditional independence implication," *IEEE Trans. Inf. Theory*, 69(6):3493–3510, 2023 (arXiv:2205.11461, 2022).
