---
id: zero-error-source-coding-side-info
title: Computability of Witsenhausen's Zero-Error Source Coding Rate with Side Information
status: open
category: source-coding
posed_by: Hans S. Witsenhausen
posed_year: 1976
tags: [source-coding, zero-error, side-information, graph-coloring, computability]
lean_module: InfoTheory.Problems.ZeroErrorSourceCodingSideInfo
lean_file: lean/InfoTheory/Problems/ZeroErrorSourceCodingSideInfo.lean
---

## Statement

Let $(X, Y)$ be a pair of correlated discrete random variables on finite alphabets
$\mathcal{X} \times \mathcal{Y}$. Its characteristic (confusability) graph $G$ on vertex set
$\mathcal{X}$ connects distinct $x, x' \in \mathcal{X}$ whenever there exists $y \in \mathcal{Y}$
with $P(x, y) > 0$ and $P(x', y) > 0$. Witsenhausen (1976) proved that the minimum asymptotic
fixed-length rate for zero-error source coding of $X^k$ with decoder side information $Y^k$ is
$$R_0(G) = \lim_{k \to \infty} \frac{1}{k} \log_2 \chi(G^{\boxtimes k}) = \inf_{k \ge 1} \frac{1}{k} \log_2 \chi(G^{\boxtimes k}) ,$$
where $\chi(\cdot)$ is the chromatic number and $G^{\boxtimes k}$ is the $k$-fold strong graph
product.

**Is Witsenhausen's zero-error rate $R_0(G)$ computable?** Equivalently, does there exist an
algorithm that, given any finite simple graph $G$ and positive integer precision $m$, halts
and outputs a rational number within $1/m$ of $R_0(G)$?

## Background

In his foundational 1976 paper, Witsenhausen formulated zero-error source coding with decoder
side information as the source-coding dual of Shannon's (1956) zero-error channel capacity
$\Theta(G) = \sup_{k \ge 1} \alpha(G^{\boxtimes k})^{1/k}$. Because $R_0(G)$ is defined as an
infimum over all blocklengths $k \ge 1$ of the computable quantities
$\frac{1}{k} \log_2 \chi(G^{\boxtimes k})$, $R_0(G)$ is automatically upper-semicomputable.
However, no general algorithm is known to produce converging lower bounds. For vertex-transitive
graphs, $R_0(G) = \log_2(|V(G)| / \Theta(G))$, linking $R_0(G)$ directly to $\Theta(G)$ (for
example, $R_0(C_7) = \log_2(7 / \Theta(C_7))$ is unknown); for general non-vertex-transitive
graphs, $R_0(G)$ and $\Theta(G)$ are not even known to be mutually reducible.

The probabilistic variable-length counterpart — Alon and Orlitsky's (1996) complementary graph
entropy $\bar{H}(G, P) = \inf_{k \ge 1} \frac{1}{k} H_\chi(G^{\boxtimes k}, P^k)$ — faces the
same multiletter barrier and likewise lacks a general single-letter or computable formula.

## What is known

- **Bounds:** For every finite graph $G$ on $n$ vertices,
  $$\max\!\left(\log_2 \omega(G), \; \log_2 \frac{n}{\Theta(G)}\right) \le R_0(G) \le \log_2 \chi_f(G) \le \log_2 \chi(G) ,$$
  and via Lovász's theta function, $\log_2(n / \vartheta(G)) \le R_0(G)$ when $G$ is
  vertex-transitive (and $\log_2 \vartheta(\bar{G}) \le R_0(G)$ in general).
- **Exact values for special classes:** $R_0(G) = \log_2 \omega(G)$ for perfect graphs;
  $R_0(C_5) = \log_2 \sqrt{5} \approx 1.1610$; exact rates are also known for odd cycles
  whenever $\Theta$ is known (currently only $C_5$).
- **Variable-length / type-based version:** Körner–Longo (1973), Marton (1993), Alon–Orlitsky
  (1996), and Koulgi–Tuncel–Regunathan–Rose (2003) studied complementary graph entropy
  $\bar{H}(G, P)$ and established Marton's duality $R_W(G, P) + C(\bar{G}, P) = H(P)$ within a
  type class, leaving single-letterization and computability open in general.
- **Non-additivity:** Strong-product subadditivity $R_0(G \boxtimes H) \le R_0(G) + R_0(H)$ can
  be strict (via Haemers's and Alon's counterexamples to multiplicativity of $\Theta$).

## References

- H. S. Witsenhausen, "The zero-error side information problem and chromatic numbers,"
  IEEE Trans. Inf. Theory, 1976.
- N. Alon and A. Orlitsky, "Source coding and graph entropies,"
  IEEE Trans. Inf. Theory, 1996.
- J. Körner and A. Orlitsky, "Zero-error information theory,"
  IEEE Trans. Inf. Theory, 1998.
- P. Koulgi, E. Tuncel, S. L. Regunathan, and K. Rose, "On zero-error source coding with
  decoder side information," IEEE Trans. Inf. Theory, 2003.
- K. Marton, "On the Shannon capacity of probabilistic graphs,"
  J. Combin. Theory Ser. B, 1993.
