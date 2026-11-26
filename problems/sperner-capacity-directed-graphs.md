---
id: sperner-capacity-directed-graphs
title: Sperner Capacity of Directed Odd Cycles and Orientation Separation on C₇
status: open
category: zero-error
posed_by: Luisa Gargano, János Körner, Ugo Vaccaro
posed_year: 1992
tags: [zero-error, sperner-capacity, directed-graphs, extremal-combinatorics]
lean_module: InfoTheory.Problems.SpernerCapacityDirectedGraphs
lean_file: lean/InfoTheory/Problems/SpernerCapacityDirectedGraphs.lean
---

## Statement

For a finite directed graph $D = (V, E)$, a subset $C \subseteq V^k$ is a **$D$-qualitatively
independent (Sperner) code** if for every ordered pair of distinct codewords $x, y \in C$,
there exists a coordinate $i \in \{1, \dots, k\}$ such that $(x_i, y_i) \in E$. The
**Sperner capacity** of $D$ (Gargano–Körner–Vaccaro 1992) is
$$\Sigma(D) = \sup_{k \ge 1} \frac{1}{k} \log_2 \max \{ |C| : C \subseteq V^k \text{ is a } D\text{-Sperner code} \} .$$
When $D$ is an orientation of an undirected graph $G$, every $D$-Sperner code in $V^k$ is an
independent set in $\bar{G}^{\boxtimes k}$, so always
$$\Sigma(D) \le \log_2 \Theta(\bar{G}) .$$

For the cyclically oriented $m$-cycle $\vec{C}_m$ on $\mathbb{Z}/m\mathbb{Z}$ (with edges
$x \to x + 1 \pmod m$), Alon's out-degree bound (1998) gives $\Sigma(\vec{C}_m) \le \log_2(\Delta^+(\vec{C}_m) + 1) = 1$ bit for all $m \ge 3$, with equality $\Sigma(\vec{C}_3) = 1$ (Calderbank et al. 1993; Blokhuis 1993). **Determine $\Sigma(\vec{C}_5)$** (and $\Sigma(\vec{C}_{2r+1})$ for $r \ge 2$) — and in particular, whether $\Sigma(\vec{C}_5) < 1$.

## Background

Gargano, Körner, and Vaccaro (1992, 1993) introduced Sperner capacity as the directed-graph
generalization of Shannon's zero-error capacity, motivated by extremal set theory (qualitative
independence, Sperner families of partitions) and compound/asymmetric zero-error channels.
They asked whether the Sperner capacity of an oriented graph genuinely depends on its
orientation.

Calderbank, Frankl, Graham, Li, and Shepp (1993) and Blokhuis (1993) settled this for the
cyclic triangle $\vec{C}_3$: whereas the undirected triangle $K_3$ has symmetric capacity
$\log_2 \Theta(\overline{K_3}) = \log_2 3 \approx 1.5850$, the cyclic orientation $\vec{C}_3$
has strictly smaller Sperner capacity $\Sigma(\vec{C}_3) = \log_2 2 = 1$ (and linear codes do
not suffice to attain it). Alon (1998) proved the general out-degree upper bound
$\Sigma(D) \le \log_2(\Delta^+(D) + 1)$, which gives $\Sigma(\vec{C}_m) \le 1$ for every
directed cycle (and combines with Bohman–Holzman 2003, $\Theta(\overline{C_7}) > 2$, to
immediately yield $\Sigma(\vec{C}_7) < \log_2 \Theta(\overline{C_7})$). Determining the exact
value of $\Sigma(\vec{C}_5)$ — and whether it is strictly smaller than $1$ — remains open.

## What is known

- **Cyclic triangle ($\vec{C}_3$):** $\Sigma(\vec{C}_3) = \log_2 2 = 1 < \log_2 3 = \log_2 \Theta(\overline{K_3})$
  (Calderbank–Frankl–Graham–Li–Shepp 1993; Blokhuis 1993), establishing strict orientation
  dependence and demonstrating that nonlinear codes strictly beat linear codes.
- **Alon's out-degree bound (1998):** For every directed graph $D$ of maximum out-degree $\Delta^+$,
  $\Sigma(D) \le \log_2(\Delta^+ + 1)$; in particular $\Sigma(\vec{C}_m) \le 1$ for all $m \ge 3$.
- **Separation from undirected complement on $C_7$:** Since $\Sigma(\vec{C}_7) \le 1$ (Alon 1998)
  and $\Theta(\overline{C_7}) > 2$ (Bohman–Holzman 2003), $\Sigma(\vec{C}_7) < \log_2 \Theta(\overline{C_7})$
  is already known.
- **Directed odd cycles $\vec{C}_5, \vec{C}_7, \dots$:** Computing the exact value of
  $\Sigma(\vec{C}_5)$ (and deciding whether $\Sigma(\vec{C}_5) < 1$) remains open.

## References

- L. Gargano, J. Körner, and U. Vaccaro, "Sperner capacities,"
  Graphs and Combinatorics, 1993.
- L. Gargano, J. Körner, and U. Vaccaro, "Capacities: from information theory to extremal set
  theory," J. Combin. Theory Ser. A, 1994.
- A. R. Calderbank, P. Frankl, R. L. Graham, W.-C. W. Li, and L. A. Shepp, "The Sperner
  capacity of linear and nonlinear codes for the cyclic triangle,"
  J. Algebraic Combin., 1993.
- A. Blokhuis, "On the Sperner capacity of the cyclic triangle,"
  J. Algebraic Combin., 1993.
- L. Kiviluoto, P. R. J. Östergård, and V. P. Vaskelainen, "Sperner capacity of small
  digraphs," Adv. Math. Commun., 2010.
