---
id: entropy-region
title: Characterize the Entropy Region for Four or More Random Variables
status: open
posed_by: Zhang and Yeung (explicitly); implicit in Pippenger
posed_year: 1998
tags: [entropy-inequalities, network-coding, foundations]
---

## Statement

For jointly distributed discrete random variables $X_1, \dots, X_n$, list the $2^n - 1$
joint entropies $H(X_S)$, $\emptyset \neq S \subseteq [n]$, as a vector in
$\mathbb{R}^{2^n - 1}$. Let $\Gamma^*_n$ be the set of all such *entropic vectors*, and
$\bar{\Gamma}^*_n$ its closure.

**Give a characterization (an explicit description, e.g. by inequalities or an
algorithm) of $\bar{\Gamma}^*_n$ for $n \geq 4$.**

## Background

This asks, literally: *what are all the laws of information?* Every constraint that
Shannon entropy places on subsets of random variables lives in this region. For
$n \leq 3$ the answer is exactly the Shannon inequalities (submodularity and
monotonicity). At $n = 4$ the question turns out to be deep: the region is not what the
Shannon inequalities say, and characterizing it is *equivalent* to determining the
capacity of general network coding — so this single geometry problem is the bottleneck
for a whole class of network capacity questions. It also has known equivalences to open
problems in group theory (via group-characterizable vectors) and to conditional
independence axioms.

## What is known

- $\bar{\Gamma}^*_2 = \Gamma_2$, $\bar{\Gamma}^*_3 = \Gamma_3$: Shannon inequalities
  suffice for $n \leq 3$ (Zhang–Yeung 1997 for the closure statement at $n=3$).
- Zhang–Yeung (1998): a *non-Shannon* linear information inequality in $n = 4$
  variables — so $\bar{\Gamma}^*_4 \subsetneq \Gamma_4$.
- Matúš (2007): $\bar{\Gamma}^*_4$ is **not a polyhedron** — no finite list of linear
  inequalities characterizes it. Infinitely many independent non-Shannon inequalities
  exist (see also Dougherty–Freiling–Zeger's large computer-generated families).
- $\bar{\Gamma}^*_n$ is always a closed convex cone (Yeung); entropic vectors are
  asymptotically equivalent to group-characterizable vectors (Chan–Yeung 2002).
- Equivalence with network coding capacity regions (Yan–Yeung–Zhang implicit
  characterization) and consequences for secret sharing rates are well developed; the
  *explicit* characterization is open even for $n = 4$, and it is open whether
  membership in $\bar{\Gamma}^*_4$ is decidable.

## References

- Z. Zhang and R. W. Yeung, "On characterization of entropy function via information
  inequalities," IEEE Trans. Inf. Theory, 1998.
- F. Matúš, "Infinitely many information inequalities," Proc. IEEE ISIT, 2007.
- R. Dougherty, C. Freiling, and K. Zeger, "Non-Shannon information inequalities in
  four random variables," arXiv:1104.3602, 2011.
- T. H. Chan and R. W. Yeung, "On a relation between information inequalities and
  group theory," IEEE Trans. Inf. Theory, 2002.
- R. W. Yeung, *Information Theory and Network Coding*, Springer, 2008.
