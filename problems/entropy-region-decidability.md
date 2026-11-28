---
id: entropy-region-decidability
title: Decidability of Membership in the Four-Variable Almost-Entropic Cone
status: open
category: entropy-inequalities
posed_by: Terence H. Chan and Raymond W. Yeung; František Matúš
posed_year: 2002
tags: [entropy-inequalities, entropy-region, decidability, computability, non-shannon]
lean_module: InfoTheory.Problems.EntropyRegionDecidability
lean_file: lean/InfoTheory/Problems/EntropyRegionDecidability.lean
---

## Statement

Let $\Gamma^*_4 \subset \mathbb{R}^{2^4}$ be the set of joint Shannon entropy vectors $h(S) = H(X_S)$ ($S \subseteq \{0, 1, 2, 3\}$) of four discrete random variables, and let $\overline{\Gamma^*_4}$ denote its topological closure (the **4-variable almost-entropic cone**).

**Problem (Decidability of $\overline{\Gamma^*_4}$).** Is membership of nonnegative rational vectors $h : 2^{[4]} \to \mathbb{Q}_{\ge 0}$ in the closed almost-entropic cone $\overline{\Gamma^*_4}$ Turing-decidable? That is, does there exist an algorithm (e.g., a halting register machine / Turing machine) that, given any rational vector $h : 2^{[4]} \to \mathbb{Q}_{\ge 0}$, halts in finite time and correctly outputs whether $h \in \overline{\Gamma^*_4}$?

## Background

Characterizing the set of entropic vectors $\Gamma^*_n$ and its closure $\overline{\Gamma^*_n}$ is one of the grand unifying problems of information theory (Pippenger 1986; Yeung 1997). For $n \le 3$, $\overline{\Gamma^*_n}$ coincides with the polyhedral Shannon polymatroid cone $\Gamma_n$, so membership is trivially decidable by checking finitely many linear inequalities. For $n = 4$, Zhang and Yeung (1998) discovered the first non-Shannon linear information inequality, proving $\overline{\Gamma^*_4} \subsetneq \Gamma_4$, and Matúš (2007) proved that $\overline{\Gamma^*_4}$ is **not polyhedral** — no finite list of linear inequalities can cut it out.

Because $\overline{\Gamma^*_4}$ is non-polyhedral, the algorithmic question becomes central: can a computer even *decide* whether a given rational vector lies in $\overline{\Gamma^*_4}$ (or, dually, whether a given rational linear information inequality on 4 random variables is valid)? Notably, Chan and Yeung (2002) linked $\overline{\Gamma^*_n}$ to subgroup-index vectors of finite groups, while subsequent work on group-characterizable cones and network coding has shown deep ties between membership in $\overline{\Gamma^*_n}$ and algorithmic undecidability phenomena in algebra and combinatorics (such as Slofstra's undecidability results in quantum correlations and Kühne–Yashfe's undecidability results for polymatroid/network-coding variants at larger $n$). For $n = 4$, the decidability of $\overline{\Gamma^*_4}$ remains wide open.

## What is known

- **$n \le 3$:** $\overline{\Gamma^*_n} = \Gamma_n$ is a finite rational polyhedral cone, hence membership is decidable in $O(1)$ arithmetic operations.
- **Non-polyhedrality at $n = 4$ (Matúš, 2007):** Matúš constructed an infinite family of independent non-Shannon inequalities on 4 variables, proving $\overline{\Gamma^*_4}$ has infinitely many extreme rays/facets.
- **Semi-decidability / approximation:** One can enumerate finite distributions to approximate $\overline{\Gamma^*_4}$ from the inside, and enumerate Copy-Lemma / Ahlswede–Körner-type linear inequalities (Dougherty–Freiling–Zeger 2011; Gurpinar–Romashchenko 2019) to bound $\overline{\Gamma^*_4}$ from the outside, but neither procedure is known to yield a halting decision procedure for arbitrary rational points on or near the boundary.
- **Undecidability for related problems at large $n$:** Recent breakthroughs (e.g., Li 2023 on conditional independence implication; Kühne–Yashfe 2022 on linear/entropic representability of matroids and network coding solvability) show undecidability for certain multi-variable information-theoretic problems when $n$ is unbounded, while the exact threshold in $n$ — and in particular the case $n = 4$ — remains open.

## Formal statement and certificate

Adversarial check (2026-11-27): **faithful and open**; the Lean `Statement` was not changed. It asks
for one register machine that, given 16 nonnegative rationals (numerator, positive denominator per
subset, loaded into registers `0..31`), halts and decides `InAlmostEntropicCone 4 h`. Li (2023) and
Kühne–Yashfe prove undecidability only with an unbounded number of variables and for
conditional/affine or linear-representability questions, so membership in the fixed cone
$\overline{\Gamma^*_4}$ is still open.

Certificate `lean/InfoTheory/Known/Certificates/EntropyRegionDecidability.lean`:
- `subsetOfMask_surjective` / `subsetOfMask_injective`: the masks `0..15` enumerate all 16 subsets, so
  every coordinate is loaded exactly once (`initRegs_num`, `initRegs_den`).
- YES instances: the zero vector (`query_zero_mem`), and $h(S) = 1$ for $S \ne \emptyset$, the entropy
  vector of four copies of a fair bit, computed from scratch (`query_diag_mem`).
- NO instances: $h(\emptyset) = 1$ (`query_ones_not_mem`) and a monotonicity violator
  (`query_nonmono_not_mem`).
- `exists_yes_and_no_instances`: on encodable inputs the predicate takes both values, so no
  constant machine satisfies the `Statement`.

## References

- Z. Zhang and R. W. Yeung, "On characterization of entropy function via information inequalities," *IEEE Trans. Inf. Theory*, 44(4):1440–1452, 1998.
- T. H. Chan and R. W. Yeung, "On a relation between information inequalities and group theory," *IEEE Trans. Inf. Theory*, 48(7):1992–1995, 2002.
- F. Matúš, "Infinitely many information inequalities," *Proc. IEEE Int. Symp. Information Theory (ISIT)*, pp. 41–44, 2007.
- R. Dougherty, C. Freiling, and K. Zeger, "Non-Shannon information inequalities in four random variables," arXiv:1104.3602, 2011.
- R. W. Yeung, *Information Theory and Network Coding*, Springer, 2008.
- C. Li, "Undecidability of network coding, conditional information inequalities, and conditional independence implication," *IEEE Trans. Inf. Theory*, 69(6):3493–3510, 2023.
