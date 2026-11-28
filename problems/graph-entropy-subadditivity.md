---
id: graph-entropy-subadditivity
title: Subadditivity of Complementary Graph Entropy under Graph Union
status: open
category: zero-error
posed_by: János Körner (as recorded by Gábor Simonyi)
posed_year: 2001
tags: [zero-error, graph-entropy, subadditivity, witsenhausen-rate, graph-coloring]
lean_module: InfoTheory.Problems.GraphEntropySubadditivity
lean_file: lean/InfoTheory/Problems/GraphEntropySubadditivity.lean
---

## Statement

For a finite simple graph $G = (V, E)$, recall two fundamental graph-theoretic rate
functionals:

1. **Körner's graph entropy (1973):** $H(G, P) = \min_{X \in W \in \mathcal{I}(G)} I(X; W)$,
   whose maximum over all probability distributions $P$ on $V$ is $\log_2 \chi_f(G)$, the
   asymptotic chromatic number of the **OR-product** (co-normal) powers $G^{\vee k}$.
   Körner proved that $H(G, P)$ is **subadditive** under graph union: for all graphs $F, G$ on
   the same vertex set $V$ and all distributions $P$,
   $$H(F \cup G, P) \le H(F, P) + H(G, P) .$$
2. **Witsenhausen's rate (1976):** the distribution-free zero-error **AND-product**
   (strong-product) counterpart
   $$R_0(G) = \lim_{k \to \infty} \frac{1}{k} \log_2 \chi(G^{\boxtimes k}) = \inf_{k \ge 1} \frac{1}{k} \log_2 \chi(G^{\boxtimes k}) .$$

**Körner's question.** Is the complementary graph entropy subadditive under graph union?
That is, for every pair of simple graphs $F, G$ on a common finite vertex set $V$ and every
probability distribution $P$ on $V$, does
$$\bar H(F \cup G, P) \le \bar H(F, P) + \bar H(G, P)$$
hold? Here (Körner–Longo 1973; Simonyi 2001, Definition 32)
$$\bar H(G, P) = \lim_{\varepsilon \to 0} \limsup_{t \to \infty} \min_{U \subseteq V^t,\ P^t(U) > 1 - \varepsilon} \frac{1}{t} \log_2 \chi\big(G^{\boxtimes t}[U]\big),$$
with $G^{\boxtimes t}$ the strong (normal / AND) power.

**Provenance (verified 2026-11-27).** G. Simonyi, "Perfect graphs and graph entropy. An updated
survey," in *Perfect Graphs* (J. L. Ramírez-Alfonsín and B. A. Reed, eds.), Wiley, 2001,
pp. 293–328, §7.4 "Co-entropy" (author copy: https://www.renyi.hu/~simonyi/perfhgp.pdf, p. 36):

> "It is an old and still open question of Körner whether $\bar H(G, P)$ is also sub-additive
> like graph entropy. It should be clear from the above facts that
> $\bar H(F, P) + \bar H(G, P) \ge \bar H(F \cup G, P)$ is true if $F$ and $G$ are perfect. […]
> Marton [69] proved that the above inequality holds in another case. This case is,
> surprisingly, just a kind of counterpart of the previous one: it is when the graph
> $F \cup G$ is perfect."

(The bar over $H$ is lost in plain-text extraction of the PDF; in context, the section defines
$\bar H$, the co-entropy.)

*Statement-fix (2026-11-27).* Before this fix the catalog asked the distribution-free version,
"$R_0(F \cup G) \le R_0(F) + R_0(G)$" for Witsenhausen's rate
$R_0(G) = \lim_k \frac1k \log_2 \chi(G^{\boxtimes k})$. No source poses that version. The
Lean `Statement` now formalizes Körner's question about $\bar H(\cdot, P)$ exactly as quoted.
The $R_0$ version remains a natural relative: by a type-class covering argument (not proved here)
one expects $R_0(G) = \max_P \bar H(G, P)$, in which case a positive answer to Körner's question
would imply it.

## Background

Subadditivity of Körner's graph entropy $H(F \cup G, P) \le H(F, P) + H(G, P)$ is one of the
most versatile tools in combinatorics and information theory: it yields short information-theoretic
proofs of lower bounds on graph coverings (such as Fredman–Komlós / Körner–Marton hashing bounds)
and led Csiszár, Körner, Lovász, Marton, and Simonyi (1990) to their celebrated entropy-splitting
characterization of perfect graphs ($H(G, P) + H(\bar{G}, P) = H(P)$ for all $P$).

The reason subadditivity is elementary for Körner's graph entropy is that the OR-product
distributes over graph union: $(F \cup G)^{\vee k} = F^{\vee k} \cup G^{\vee k}$, so the
product of proper colorings of $F^{\vee k}$ and $G^{\vee k}$ properly colors $(F \cup G)^{\vee k}$.
For the **strong (AND) product** governing zero-error coding, however,
$(F \cup G)^{\boxtimes k}$ strictly contains $F^{\boxtimes k} \cup G^{\boxtimes k}$ whenever
$k \ge 2$ (two $k$-tuples can be adjacent via an $F$-edge in one coordinate and a $G$-edge in
another). Consequently, taking product colorings fails to certify subadditivity of $R_0$ or of
$\bar H$. Subadditivity of $\bar H(\cdot, P)$ under arbitrary graph union is Körner's open
question quoted above. For $R_0$ we found no source that poses it.

## What is known

- **Körner graph entropy subadditivity:** $H(F \cup G, P) \le H(F, P) + H(G, P)$ holds for
  all graphs $F, G$ on $V$ and all $P$ (Körner 1973; Simonyi 1995). Equality for all $P$
  characterizes perfect graphs when $G = \bar{F}$ (CKLMS 1990) and *perfect couples* in
  general (Körner–Simonyi–Tuza 1992); characterizing *normal couples* (equality for some
  strictly positive $P$) also remains open.
- **Marton's two cases (Marton 1993; Simonyi 2001, §7.4):** the inequality
  $\bar H(F \cup G, P) \le \bar H(F, P) + \bar H(G, P)$ holds when $F$ and $G$ are both perfect
  (then $\bar H = H$ for both, and $H$ is subadditive), and when $F \cup G$ is perfect. In Simonyi's account the
  second case uses Marton's duality $\bar H(G, P) + C(\bar G, P) = H(P)$ and
  $\mu(G, P) \le \bar H(G, P)$. It includes the complementary case $F \cup G = K_n$.
- **Relaxed subadditivity:** Tuncel, Nayak, Koulgi and Rose (2009) prove subadditivity-type
  inequalities for $\bar H$ under the AND product and disjoint union. Charpenay, Le Treust and
  Roumy (2023, arXiv:2305.01459) note that $\bar H$ "has no single-letter formula, except for
  perfect graphs, for the pentagon graph with uniform distribution $G_5$, and for their disjoint
  union", and that characterizing the cases of equality in those inequalities "is an open problem".
- **General case:** open. A literature search (2026-11: Simonyi 1995/2001, Tuncel et al. 2009,
  Charpenay–Le Treust–Roumy 2023) found no resolution of Körner's question.

## References

- J. Körner, "Coding of an information source having ambiguous alphabet and the entropy of
  graphs," Trans. 6th Prague Conf. Inf. Theory, 1973.
- H. S. Witsenhausen, "The zero-error side information problem and chromatic numbers,"
  IEEE Trans. Inf. Theory, 1976.
- I. Csiszár, J. Körner, L. Lovász, K. Marton, and G. Simonyi, "Entropy splitting for
  antiblocking corners and perfect graphs," Combinatorica, 1990.
- J. Körner, G. Simonyi, and Z. Tuza, "Perfect couples of graphs,"
  Combinatorica, 1992.
- K. Marton, "On the Shannon capacity of probabilistic graphs,"
  J. Combin. Theory Ser. B, 1993.
- G. Simonyi, "Graph entropy: a survey,"
  DIMACS Series in Discrete Mathematics and Theoretical Computer Science, 1995.
- G. Simonyi, "Perfect graphs and graph entropy. An updated survey," in *Perfect Graphs*
  (J. L. Ramírez-Alfonsín and B. A. Reed, eds.), Wiley, 2001, pp. 293–328.
- J. Körner and G. Longo, "Two-step encoding for finite sources," IEEE Trans. Inf. Theory
  19 (1973), 778–782.
- E. Tuncel, J. Nayak, P. Koulgi, and K. Rose, "On complementary graph entropy," IEEE Trans.
  Inf. Theory 55(6) (2009), 2537–2546.
- M. Charpenay, M. Le Treust, and A. Roumy, "Complementary graph entropy, AND product, and
  disjoint union of graphs," arXiv:2305.01459 (ISIT 2023).

## Formal statement and certificate

- **Statement (after the 2026-11-27 fix).** `complementaryGraphEntropy G P` is
  `sup_{ε∈(0,1)} inf_N sup_{t≥N, t>0} coEntropyBlock G P ε t`. Here `coEntropyBlock` is the
  `sInf` of `log₂ m / t` over sets `U ⊆ (Fin t → V)` with `P^t(U) > 1 - ε` and colourings that
  are proper on `G^{⊠t}` restricted to `U`. Since the block value does not increase in `ε`, the
  `sup` over `ε` is the limit `ε → 0`. There are **no junk values**: every set is non-empty
  (`U = univ`) and lies in `[0, log₂ |V|]`. `Statement` quantifies over `n`, all `F, G` on
  `Fin n` and all `P : ProbDist (Fin n)`. `ProbDist (Fin 0)` is empty, so `n = 0` is vacuous.
- **Certificate** `lean/InfoTheory/Known/Certificates/GraphEntropySubadditivity.lean`:
  - non-junk bounds `coEntropy_nonneg` and `coEntropy_le_log2_card`;
  - `coEntropy_le_log2_of_coloring`, giving `H̄(G, P) ≤ log₂ χ(G)`;
  - regressions `coEntropy_bot` (`H̄(\bar K_n, P) = 0`) and `coEntropy_top_uniform`
    (`H̄(K_n, Unif) = log₂ n = H(Unif)`, which uses the full `lim/limsup` structure);
  - instances `coEntropy_subadditive_bot_left` and `coEntropy_union_compl_uniform` (the left
    side in the complementary case);
  - the earlier Witsenhausen-rate facts (`log₂ ω ≤ R₀ ≤ log₂ χ`, product-colouring bound),
    kept as related results.
- **Not certified:** `H̄(G, P) = H(G, P)` for perfect graphs, and Marton's cases.
