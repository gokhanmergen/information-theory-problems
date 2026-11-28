---
id: trace-reconstruction-worst-case
title: Sample Complexity of Worst-Case Binary Trace Reconstruction
status: open
category: coding-theory
posed_by: Tugkan Batu, Sampath Kannan, Sanjeev Khanna, and Andrew McGregor
posed_year: 2004
tags: [coding-theory, trace-reconstruction, deletion-channel, sample-complexity]
lean_module: InfoTheory.Problems.TraceReconstructionWorstCase
lean_file: lean/InfoTheory/Problems/TraceReconstructionWorstCase.lean
---

## Statement

An unknown binary string $x \in \{0, 1\}^n$ is passed independently $T$ times through the i.i.d. binary deletion channel $\mathrm{Del}_d$ with deletion probability $d = 1/2$, producing $T$ independent **traces** $Y^{(1)}, \dots, Y^{(T)} \in \{0, 1\}^{\le n}$. Let $T_{\mathrm{wc}}(n, 1/2)$ denote the minimum number of traces needed to distinguish any two distinct strings $x \neq y \in \{0, 1\}^n$ with total error probability at most $2/3$ (by standard tournament / maximum-likelihood reductions, distinguishing any pair with constant error is within an $O(n)$ factor of reconstructing an arbitrary worst-case $x \in \{0, 1\}^n$ with probability at least $2/3$).

**Open Problem:** Does worst-case binary trace reconstruction at deletion probability $d = 1/2$ have **polynomial** sample complexity, i.e., does there exist a constant $c \in \mathbb{N}$ such that
$$T_{\mathrm{wc}}(n, 1/2) = O(n^c),$$
or is $T_{\mathrm{wc}}(n, 1/2)$ super-polynomial in $n$?

## Background

Introduced by Batu, Kannan, Khanna, and McGregor (2004) (following earlier work by Levenshtein 2001 on combinatorial sequence reconstruction), trace reconstruction is one of the cleanest and most stubborn open problems in probability, information theory, and theoretical computer science. It models consensus-sequence recovery in DNA data storage and bioinformatics, where many independent noisy reads (traces) of a single unknown molecule are observed.

Despite two decades of sustained progress, there remains an exponential chasm between the best known upper bound $\exp(\tilde{O}(n^{1/5}))$ and the best known lower bound $\tilde{\Omega}(n^{3/2})$—not even the question of polynomial vs. sub-exponential sample complexity is resolved!

## What is known

- **Upper bounds:**
  - Holenstein, Mitzenmacher, Panigrahy, and Wieder (2008): $\exp(\tilde{O}(n^{1/2}))$ traces for any constant $d < 1$.
  - Nazarov and Peres (2017) and De, O'Donnell, and Servedio (2017), independently: $\exp(O(n^{1/3}))$ traces using **mean-based algorithms** (looking only at the single-bit marginals $\mathbb{E}[Y_j]$) via complex-analytic Littlewood polynomial estimates on the unit disk. Both papers also proved that $\exp(\Omega(n^{1/3}))$ is **tight** for all mean-based algorithms.
  - Chase (2021, STOC 2021): $\exp(\tilde{O}(n^{1/5}))$ traces by analyzing $k$-mer subsequence statistics and connecting them to complex analysis and the separating-words problem.
  - **Burudgunte, Valiant, and Wang (July 2026, `arXiv:2607.04073`):** **Quasipolynomial** upper bound $\exp(p^{-7/3} (\log_2 n)^c)$ for all retention probabilities $p \ge 1/\mathrm{polylog}(n)$, bypassing the local statistical-query barrier via global triple-product statistics and inductive zoom-out. Whether polynomial sample complexity $O(n^c)$ is achievable remains open.
- **Lower bounds:**
  - Batu et al. (2004): $\Omega(\log n)$.
  - Holden and Lyons (2020): $\tilde{\Omega}(n^{5/4})$ traces.
  - Chase (2021, Ann. Probab.): $\tilde{\Omega}(n^{3/2})$ traces, currently the best known lower bound for worst-case binary trace reconstruction at $d = 1/2$.
- **Barriers for $k$-mer / local statistical query algorithms:** Chen, De, Lee, Servedio, and Sinha (2024) and Mazooji–Shomorony (2024) proved that $k$-mer / $O(n^{1/5})$-local statistical query algorithms cannot beat $\exp(\tilde{\Omega}(n^{1/5}))$, indicating that breaking the $n^{1/5}$ barrier requires fundamentally non-local techniques.

## References

- V. I. Levenshtein, "Efficient reconstruction of sequences from their subsequences or supersequences," *J. Combin. Theory Ser. A*, 93(2):310–332, 2001.
- T. Batu, S. Kannan, S. Khanna, and A. McGregor, "Reconstructing strings from random traces," *Proc. 15th ACM–SIAM SODA*, pp. 910–918, 2004.
- T. Holenstein, M. Mitzenmacher, R. Panigrahy, and U. Wieder, "Trace reconstruction with constant deletion probability and related results," *Proc. 19th ACM–SIAM SODA*, pp. 389–398, 2008.
- F. Nazarov and Y. Peres, "Trace reconstruction with $\exp(O(n^{1/3}))$ samples," *Proc. 49th ACM STOC*, pp. 1042–1046, 2017.
- A. De, R. O'Donnell, and R. A. Servedio, "Optimal mean-based algorithms for trace reconstruction," *Annals of Applied Probability*, 29(2):851–874, 2019 (STOC 2017).
- N. Holden and R. Lyons, "Lower bounds for trace reconstruction," *Annals of Applied Probability*, 30(2):503–525, 2020.
- Z. Chase, "New lower bounds for trace reconstruction," *Annales de l'Institut Henri Poincaré, Probabilités et Statistiques*, 57(2):627–643, 2021.
- Z. Chase, "Separating words and trace reconstruction," *Proc. 53rd ACM STOC*, pp. 21–31, 2021.
