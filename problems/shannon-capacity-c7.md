---
id: shannon-capacity-c7
title: The Shannon Capacity of the 7-Cycle
status: open
posed_by: Claude Shannon
posed_year: 1956
tags: [zero-error, combinatorics, graph-theory]
---

## Statement

For a graph $G$, let $\alpha(G)$ be its independence number and $G^{\boxtimes k}$ its
$k$-fold strong product. The Shannon (zero-error) capacity of $G$ is
$$\Theta(G) = \lim_{k \to \infty} \alpha(G^{\boxtimes k})^{1/k} .$$
$\Theta(G)$ is the effective alphabet size per symbol for zero-error communication over
a channel whose confusability graph is $G$.

**Determine $\Theta(C_7)$, the Shannon capacity of the 7-cycle** — and more generally
$\Theta(C_{2k+1})$ for all odd cycles with $2k+1 \geq 7$.

## Background

Shannon introduced zero-error capacity in 1956 and could not determine $\Theta(C_5)$.
Lovász resolved it in 1979 — $\Theta(C_5) = \sqrt{5}$ — by inventing the theta function
$\vartheta(G)$, one of the most influential ideas connecting information theory,
combinatorics, and semidefinite programming. The very next case, $C_7$, has resisted
every technique since: the Lovász bound is not tight for it (as far as anyone can tell),
and no construction meets any known upper bound. The problem is a clean, finite,
combinatorial question that has been open for nearly seventy years.

## What is known

- $\Theta(C_5) = \sqrt{5}$ (Lovász 1979). For all graphs, $\Theta(G) \leq \vartheta(G)$.
- Upper bound: $\Theta(C_7) \leq \vartheta(C_7) = \dfrac{7\cos(\pi/7)}{1+\cos(\pi/7)}
  \approx 3.3177$.
- Lower bounds come from explicit independent sets in small powers $C_7^{\boxtimes k}$;
  the record has crept upward over the years (Baumert et al.; Vesel–Žerovnik;
  Polak–Schrijver 2019, via $\alpha(C_7^{\boxtimes 5}) \geq 367$, giving
  $\Theta(C_7) \geq 367^{1/5} \approx 3.2578$). A gap to the $\vartheta$ bound remains.
- Fractional relaxations, Haemers' rank bound, and known SDP hierarchies have not
  closed the gap; it is not even known whether $\Theta(C_7)$ is achieved by
  $\alpha(C_7^{\boxtimes k})^{1/k}$ at any finite $k$, nor whether $\Theta$ is in
  general computable.

## References

- C. E. Shannon, "The zero error capacity of a noisy channel," IRE Trans. Inf. Theory,
  1956.
- L. Lovász, "On the Shannon capacity of a graph," IEEE Trans. Inf. Theory, 1979.
- W. Haemers, "On some problems of Lovász concerning the Shannon capacity of a graph,"
  IEEE Trans. Inf. Theory, 1979.
- A. Vesel and J. Žerovnik, "Improved lower bound on the Shannon capacity of C7,"
  Inf. Process. Lett., 2002.
- S. C. Polak and A. Schrijver, "New lower bound on the Shannon capacity of C7 from
  circular graphs," Inf. Process. Lett., 2019.
