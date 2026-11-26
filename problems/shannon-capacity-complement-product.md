---
id: shannon-capacity-complement-product
title: Minimum Product of Shannon Capacities of a Graph and Its Complement
status: open
category: zero-error
posed_by: László Lovász; Willem Haemers; Noga Alon
posed_year: 1998
tags: [zero-error, shannon-capacity, ramsey-theory, graph-complements]
lean_module: InfoTheory.Problems.ShannonCapacityComplementProduct
lean_file: lean/InfoTheory/Problems/ShannonCapacityComplementProduct.lean
---

## Statement

For a finite simple graph $G$ on $n$ vertices and its complement $\bar{G}$, the diagonal
$\{(v, v) : v \in V(G)\}$ is an independent set of size $n$ in $G \boxtimes \bar{G}$, so
$$\Theta(G \boxtimes \bar{G}) \ge n \quad \text{and} \quad \vartheta(G)\,\vartheta(\bar{G}) \ge n .$$
In contrast, the product $\Theta(G)\,\Theta(\bar{G})$ can be dramatically smaller than $n$:
Alon (1998) constructed $n$-vertex graphs with
$\Theta(G)\,\Theta(\bar{G}) \le 2^{O(\sqrt{\log n \log \log n})} = n^{o(1)}$, whereas
Ramsey's theorem implies $\max(\Theta(G), \Theta(\bar{G})) \ge \max(\alpha(G), \omega(G)) \ge \frac{1}{2}\log_2 n$.

**Can $\Theta(G)\,\Theta(\bar{G})$ be made polylogarithmic in $n$?** Equivalently, does there
exist a constant $c > 0$ such that for every sufficiently large $n$, there is an $n$-vertex
simple graph $G$ satisfying
$$\Theta(G) \cdot \Theta(\bar{G}) \le (\log_2 n)^c ?$$

## Background

Lovász (1979) proved that his theta function satisfies $\vartheta(G)\,\vartheta(\bar{G}) \ge n$
for every $n$-vertex graph (with equality for vertex-transitive graphs, giving
$\Theta(G) = \sqrt{n}$ for self-complementary vertex-transitive graphs like $C_5$). The same
year, Haemers (1979) disproved the analogous lower bound $\Theta(G)\,\Theta(\bar{G}) \ge n$
for Shannon capacity using the 27-vertex Schläfli graph, where $\Theta(G)\,\Theta(\bar{G}) \le 7 \cdot 3 = 21 < 27$.

Alon (1998) pushed this failure of complementarity to an extreme: using graphs whose
non-adjacency is governed by modular intersection conditions over distinct primes, he
constructed $n$-vertex graphs $G$ for which *both* $\Theta(G)$ and $\Theta(\bar{G})$ are
bounded by $2^{O(\sqrt{\log n \log \log n})}$, leaving an exponential gap between this
subpolynomial upper bound and the Ramsey-theoretic lower bound $\Omega(\log n)$ (which gives
$\Theta(G)\,\Theta(\bar{G}) = \Omega(\log n)$ since $\Theta \ge 1$). Determining whether
random graphs (or any explicit graphs) achieve polylogarithmic $\Theta(G)\,\Theta(\bar{G})$ —
in particular, whether the Erdős–Rényi random graph $G(n, 1/2)$ has $\Theta(G(n, 1/2)) = O(\log n)$
or $(\log n)^{O(1)}$ — remains a celebrated open problem bridging zero-error information theory
and Ramsey theory.

## What is known

- **Strong-product and Lovász lower bounds:** $\Theta(G \boxtimes \bar{G}) \ge n$ and
  $\vartheta(G)\,\vartheta(\bar{G}) \ge n$ for every $n$-vertex graph $G$ (Lovász 1979).
- **First counterexample to $\Theta(G)\Theta(\bar{G}) \ge n$:** Haemers (1979) showed
  $\Theta(G)\,\Theta(\bar{G}) \le 21 < 27$ for the Schläfli graph.
- **Subpolynomial upper bound:** Alon (1998) proved that there exist $n$-vertex graphs $G$ with
  $\max(\Theta(G), \Theta(\bar{G})) \le 2^{O(\sqrt{\log n \log \log n})}$, hence
  $\Theta(G)\,\Theta(\bar{G}) = n^{o(1)}$.
- **Ramsey lower bound:** For every $n$-vertex graph $G$,
  $\max(\Theta(G), \Theta(\bar{G})) \ge \max(\alpha(G), \omega(G)) \ge \frac{1}{2}\log_2 n$.
- **Random graphs:** For $G \sim G(n, 1/2)$, $\alpha(G) = (2 + o(1))\log_2 n$ and
  $\vartheta(G) = (2 + o(1))\sqrt{n}$ w.h.p., while the true order of $\Theta(G(n, 1/2))$ is
  completely unknown (even whether $\Theta(G(n, 1/2)) \le n^{1/2 - \varepsilon}$ is open!).

## References

- L. Lovász, "On the Shannon capacity of a graph,"
  IEEE Trans. Inf. Theory, 1979.
- W. Haemers, "On some problems of Lovász concerning the Shannon capacity of a graph,"
  IEEE Trans. Inf. Theory, 1979.
- N. Alon, "The Shannon capacity of a union,"
  Combinatorica, 1998.
- N. Alon and E. Lubetzky, "The Shannon capacity of a graph and the independence numbers of
  its powers," IEEE Trans. Inf. Theory, 2006.
- B. Bukh and C. Cox, "On a fractional version of Haemers' bound,"
  IEEE Trans. Inf. Theory, 2019.
