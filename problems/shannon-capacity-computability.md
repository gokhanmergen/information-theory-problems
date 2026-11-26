---
id: shannon-capacity-computability
title: Computability of the Shannon Capacity of Finite Graphs
status: open
category: zero-error
posed_by: Claude Shannon; Noga Alon, Eyal Lubetzky
posed_year: 1956
tags: [zero-error, shannon-capacity, graph-theory, computability]
lean_module: InfoTheory.Problems.ShannonCapacityComputability
lean_file: lean/InfoTheory/Problems/ShannonCapacityComputability.lean
---

## Statement

For a finite simple graph $G$, its Shannon (zero-error) capacity is
$$\Theta(G) = \lim_{k \to \infty} \alpha(G^{\boxtimes k})^{1/k} = \sup_{k \ge 1} \alpha(G^{\boxtimes k})^{1/k} ,$$
where $\alpha(\cdot)$ is the independence number and $G^{\boxtimes k}$ is the $k$-fold strong
graph product.

**Is $\Theta(G)$ computable?** Equivalently, does there exist an algorithm (halting Turing
machine / register machine) that, given any finite simple graph $G$ on $n \ge 1$ vertices and
any positive integer precision $m \ge 1$, halts and outputs a rational number $p/q$ satisfying
$$\left|\Theta(G) - \frac{p}{q}\right| \le \frac{1}{m} ?$$

## Background

Because $\Theta(G) = \sup_{k \ge 1} \alpha(G^{\boxtimes k})^{1/k}$ is the supremum of a
computable sequence of algebraic numbers, $\Theta(G)$ is automatically **lower-semicomputable**:
an algorithm can enumerate $k = 1, 2, \dots$ and compute $\alpha(G^{\boxtimes k})^{1/k}$,
producing a monotonically nondecreasing sequence of lower bounds converging to $\Theta(G)$.
However, no general algorithm is known to certify converging **upper** bounds on $\Theta(G)$,
and computability of $\Theta(G)$ is equivalent to upper-semicomputability.

Even on a single 7-vertex graph ($C_7$), seventy years of algebraic, spectral, and semidefinite
programming methods (Lovász's $\vartheta$, Haemers's minrank, Schrijver's $\vartheta'$, and
asymptotic spectrum duals) have failed to close the gap between the best known lower and upper
bounds. Establishing whether $\Theta(G)$ is computable — or proving that it is uncomputable
(analogous to undecidability results in quantum nonlocal games and network coding) — is one of
the deepest foundational questions in zero-error information theory.

## What is known

- **Lower-semicomputability:** $\Theta(G)$ is lower-semicomputable for all finite graphs $G$.
- **Exact values and tractable classes:** $\Theta(G) = \alpha(G)$ for perfect graphs;
  $\Theta(C_5) = \sqrt{5}$ (Lovász 1979); $\Theta(G) = \vartheta(G)$ whenever $\alpha(G)$ or a
  finite-power independent set matches $\vartheta(G)$ (such as Kneser graphs and self-complementary
  vertex-transitive graphs).
- **Asymptotic spectrum duality:** Zuiddam (2019) proved a dual characterization
  $\Theta(G) = \min_{\phi \in \Delta(\mathcal{G})} \phi(G)$ over the asymptotic spectrum of
  graphs (multiplicative, additive, monotone graph invariants), generalizing $\vartheta$,
  Haemers's bound, and fractional clique cover, but the spectrum $\Delta(\mathcal{G})$ itself is
  not known to be effectively enumerable.
- **No convergence rate bound:** Alon and Lubetzky (2006) showed that $\alpha(G^{\boxtimes k})^{1/k}$
  can exhibit arbitrarily delayed jumps as $k$ grows, demonstrating that no simple function of
  $|V(G)|$ bounds the blocklength $k$ at which near-capacity behavior emerges.

## References

- C. E. Shannon, "The zero error capacity of a noisy channel,"
  IRE Trans. Inf. Theory, 1956.
- L. Lovász, "On the Shannon capacity of a graph,"
  IEEE Trans. Inf. Theory, 1979.
- N. Alon and E. Lubetzky, "The Shannon capacity of a graph and the independence numbers of
  its powers," IEEE Trans. Inf. Theory, 2006.
- J. Zuiddam, "The asymptotic spectrum of graphs and the Shannon capacity,"
  Combinatorica, 2019.
- A. Wigderson and J. Zuiddam, "Asymptotic spectra: theory, applications and extensions,"
  Survey, 2023.
