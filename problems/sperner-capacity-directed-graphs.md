---
id: sperner-capacity-directed-graphs
title: Sperner Capacity of Random Tournaments and Directed Graphs
status: open
category: zero-error
posed_by: Noga Alon; Luisa Gargano, János Körner, Ugo Vaccaro
posed_year: 1998
tags: [zero-error, sperner-capacity, directed-graphs, tournaments, extremal-combinatorics]
lean_module: InfoTheory.Problems.SpernerCapacityDirectedGraphs
lean_file: lean/InfoTheory/Problems/SpernerCapacityDirectedGraphs.lean
---

## Statement

For a finite directed graph $D = (V, E)$, a subset $C \subseteq V^k$ is a **$D$-qualitatively
independent (Sperner) code** if for every ordered pair of distinct codewords $x, y \in C$,
there exists a coordinate $i \in \{1, \dots, k\}$ such that $(x_i, y_i) \in E$. The
**Sperner capacity** of $D$ (Gargano–Körner–Vaccaro 1992) is
$$\Sigma(D) = \sup_{k \ge 1} \frac{1}{k} \log_2 \max \{ |C| : C \subseteq V^k \text{ is a } D\text{-Sperner code} \} .$$

Let $T_n$ be a uniformly random tournament on $n$ vertices (each unordered pair $\{u, v\}$ oriented
independently with probability $1/2$). **Alon's Random Tournament Conjecture (1998):** Does there
exist an absolute constant $c > 0$ such that
$$\Pr\!\left[2^{\Sigma(T_n)} \le c \log_2 n\right] \longrightarrow 1 \qquad \text{as } n \to \infty ?$$

## Background

Gargano, Körner, and Vaccaro (1992, 1993) introduced Sperner capacity as the directed-graph
generalization of Shannon's zero-error capacity, motivated by extremal set theory and compound
zero-error channels. For any tournament $T$, the size $t(T)$ of its largest transitive
subtournament always satisfies $t(T) \le 2^{\Sigma(T)}$.

Körner and Simonyi conjectured that $2^{\Sigma(T)} = t(T)$ for every tournament $T$. In 1998,
Noga Alon famously disproved this conjecture by constructing tournaments on $2n$ vertices with
$2^{\Sigma(T)} \ge n$ despite having $t(T) = O(\log n)$, and proved the general out-degree upper
bound $2^{\Sigma(D)} \le \Delta^+(D) + 1$ (which together with Sperner's theorem immediately gives
$\Sigma(\vec{C}_m) = 1$ for every directed cycle $\vec{C}_m$, $m \ge 2$). Alon simultaneously asked
for the typical Sperner capacity of a uniformly random tournament $T_n$: since $t(T_n) = \Theta(\log n)$
with high probability (Erdős–Moser 1964), does $2^{\Sigma(T_n)} = O(\log n)$ still hold for almost
all tournaments?

## What is known

- **Cyclic triangle & directed cycles:** $\Sigma(\vec{C}_3) = 1$ (Calderbank–Frankl–Graham–Li–Shepp
  1993; Blokhuis 1993), and more generally $\Sigma(\vec{C}_m) = 1$ for every $m \ge 2$ (upper bound
  via Alon 1998, $\Delta^+ + 1 = 2$; lower bound via Sperner's theorem on a single edge).
- **Small tournaments & digraphs:** Every tournament on at most $6$ vertices satisfies
  $2^{\Sigma(T)} = t(T)$, while separation begins at $7$ vertices; Kiviluoto–Östergård–Vaskelainen
  (2009) determined $\Sigma(D)$ for all but $8$ of the $9{,}846$ digraphs on $\le 5$ vertices.
- **Extremal tournaments (Alon 1998):** There exist tournaments on $2n$ vertices with
  $2^{\Sigma(T)} \ge n$ and $t(T) = O(\log n)$, showing $2^{\Sigma(T)} / t(T)$ can be as large as
  $\Omega(n / \log n)$ (and $\Omega(\sqrt{n}/\log n)$ for Paley tournaments).
- **Random tournaments:** For $T_n \sim \mathrm{Unif}(\text{tournaments on } [n])$,
  $t(T_n) = (2 - o(1)) \log_2 n$ w.h.p. gives $2^{\Sigma(T_n)} = \Omega(\log n)$, while Alon's
  out-degree bound gives $2^{\Sigma(T_n)} \le (1/2 + o(1)) n$. Whether $2^{\Sigma(T_n)} = O(\log n)$
  w.h.p. remains open.

## References

- N. Alon, "On the capacity of digraphs," *European Journal of Combinatorics* 19(1), 1–5, 1998.
- L. Gargano, J. Körner, and U. Vaccaro, "Sperner capacities," *Graphs and Combinatorics*, 1993.
- A. R. Calderbank, P. Frankl, R. L. Graham, W.-C. W. Li, and L. A. Shepp, "The Sperner capacity
  of linear and nonlinear codes for the cyclic triangle," *J. Algebraic Combin.*, 1993.
- L. Kiviluoto, P. R. J. Östergård, and V. P. Vaskelainen, "Sperner capacity of small digraphs,"
  *Adv. Math. Commun.*, 2009.
