---
id: shannon-capacity-union-product
title: Boundedness of Shannon Capacity under Disjoint Union and Strong Product
status: open
category: zero-error
posed_by: Claude Shannon; Noga Alon
posed_year: 1998
tags: [zero-error, shannon-capacity, graph-products, combinatorics]
lean_module: InfoTheory.Problems.ShannonCapacityUnionProduct
lean_file: lean/InfoTheory/Problems/ShannonCapacityUnionProduct.lean
---

## Statement

For finite simple graphs $G$ and $H$, let $G + H$ denote their disjoint union, $G \boxtimes H$
their strong product, and $\Theta(\cdot)$ the Shannon (zero-error) capacity. It is always true
that $\Theta(G + H) \ge \Theta(G) + \Theta(H)$ and $\Theta(G \boxtimes H) \ge \Theta(G)\Theta(H)$,
and both inequalities can be strict (Haemers 1979; Alon 1998).

**Is $\Theta(G + H)$ bounded by a function of $\Theta(G)$ and $\Theta(H)$?** Equivalently,
does there exist a function $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ such that for all
nonempty finite simple graphs $G$ and $H$,
$$\Theta(G + H) \le f(\Theta(G), \Theta(H)) ?$$
(Equivalently, is $\Theta(G \boxtimes H)$ bounded by a function of $\Theta(G)$ and $\Theta(H)$?)

## Background

In 1956, Shannon proved $\Theta(G + H) \ge \Theta(G) + \Theta(H)$ and
$\Theta(G \boxtimes H) \ge \Theta(G)\Theta(H)$ and conjectured that equality holds for the
disjoint union (the zero-error capacity of a sum of two channels). Haemers (1979) disproved
multiplicativity for the strong product using his linear-algebraic minrank bound on the
Schläfli graph. Nearly twenty years later, Alon (1998) stunned the field by disproving
Shannon's additivity conjecture for the disjoint union as well: constructing pairs of graphs
$(G, H)$ via finite-field polynomial spaces of distinct characteristics, Alon proved that
$\Theta(G + H)$ can exceed $\Theta(G) + \Theta(H)$ by a superpolynomial factor — specifically
$\Theta(G), \Theta(H) \le t$ with $\Theta(G + H) \ge t^{\Omega(\log t / \log \log t)}$.

Crucially, in Alon's construction, $\Theta(G)$ and $\Theta(H)$ grow to infinity alongside
$\Theta(G + H)$. Alon (1998) posed the striking question of whether $\Theta(G + H)$ can be
**arbitrarily large** even while $\Theta(G)$ and $\Theta(H)$ remain bounded by a fixed constant
(for example, $\Theta(G), \Theta(H) \le 3$). Because $\Theta(G + H)$ and $\Theta(G \boxtimes H)$
mutually bound each other up to elementary transformations, this question equivalently asks
whether the strong-product capacity $\Theta(G \boxtimes H)$ is bounded by any function of
$\Theta(G)$ and $\Theta(H)$.

## What is known

- **Supermultiplicativity:** Haemers (1979) gave the first counterexample to
  $\Theta(G \boxtimes H) = \Theta(G)\Theta(H)$ using the 27-vertex Schläfli graph and its
  complement ($\Theta(G) \le 7$, $\Theta(\bar{G}) = 3$, yet $\Theta(G \boxtimes \bar{G}) \ge 27 > 21$).
- **Superadditivity:** Alon (1998) disproved $\Theta(G + H) = \Theta(G) + \Theta(H)$ and showed
  that there exist graphs with $\Theta(G), \Theta(H) \le t$ and
  $\Theta(G + H) \ge t^{\Omega(\log t / \log \log t)}$ (and $\Theta(G \boxtimes H) \ge t^{\Omega(\log t / \log \log t)}$).
- **Trivial small cases:** If $\Theta(G) < 2$, then $\alpha(G) = 1$, so $G$ is a complete graph,
  $\Theta(G) = 1$, and $\Theta(G + H) = 1 + \Theta(H)$ and $\Theta(G \boxtimes H) = \Theta(H)$
  for every graph $H$.
- **Open for bounded capacity:** It is unknown whether $\sup \{ \Theta(G + H) : \Theta(G) \le C, \, \Theta(H) \le C \}$
  is finite even for $C = 3$ (or even $C = 2$ with $\alpha(G) = 2$ and $\Theta(G) = 2$? Note:
  if $\Theta(G) = 2$, is $\Theta(G + H)$ always bounded by a function of $\Theta(H)$? Even that
  remains open for general $C$).

## References

- C. E. Shannon, "The zero error capacity of a noisy channel,"
  IRE Trans. Inf. Theory, 1956.
- W. Haemers, "On some problems of Lovász concerning the Shannon capacity of a graph,"
  IEEE Trans. Inf. Theory, 1979.
- N. Alon, "The Shannon capacity of a union,"
  Combinatorica, 1998.
- N. Alon and E. Lubetzky, "The Shannon capacity of a graph and the independence numbers of
  its powers," IEEE Trans. Inf. Theory, 2006.
- A. Wigderson and J. Zuiddam, "Asymptotic spectra: theory, applications and extensions,"
  Survey, 2023.
