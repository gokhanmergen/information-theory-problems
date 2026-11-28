---
id: graph-entropy-subadditivity
title: Subadditivity of Witsenhausen's Rate and Complementary Graph Entropy under Graph Union
status: open
category: zero-error
posed_by: János Körner, Katalin Marton; Gábor Simonyi
posed_year: 1988
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
2. **Witsenhausen's rate (1976) / complementary graph entropy (Körner–Longo 1973; Marton 1993):**
   the zero-error **AND-product** (strong-product) counterpart
   $$R_0(G) = \lim_{k \to \infty} \frac{1}{k} \log_2 \chi(G^{\boxtimes k}) = \inf_{k \ge 1} \frac{1}{k} \log_2 \chi(G^{\boxtimes k}) .$$

**Is Witsenhausen's zero-error rate subadditive under graph union?** That is, for every
$n \ge 1$ and every pair of simple graphs $F, G$ on the same vertex set $\{1, \dots, n\}$,
does
$$R_0(F \cup G) \le R_0(F) + R_0(G)$$
hold? (And analogously for the probabilistic complementary graph entropy
$\bar{H}(F \cup G, P) \le \bar{H}(F, P) + \bar{H}(G, P)$.)

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
another). Consequently, taking product colorings fails to certify subadditivity of $R_0$, and
the subadditivity of Witsenhausen's rate (and complementary graph entropy) under arbitrary
graph union remains open.

## What is known

- **Körner graph entropy subadditivity:** $H(F \cup G, P) \le H(F, P) + H(G, P)$ holds for
  all graphs $F, G$ on $V$ and all $P$ (Körner 1973; Simonyi 1995). Equality for all $P$
  characterizes perfect graphs when $G = \bar{F}$ (CKLMS 1990) and *perfect couples* in
  general (Körner–Simonyi–Tuza 1992); characterizing *normal couples* (equality for some
  strictly positive $P$) also remains open.
- **Complementary special case ($F \cup G = K_n$):** When $G = \bar{F}$, subadditivity
  $R_0(K_n) = \log_2 n \le R_0(F) + R_0(\bar{F})$ **does** hold for all finite graphs $F$,
  because Lovász's sandwich theorem gives $R_0(F) \ge \log_2 \vartheta(\bar{F})$ and
  $\vartheta(F)\,\vartheta(\bar{F}) \ge n$.
- **Perfect graphs:** If $F$ and $G$ are perfect (or more generally whenever $R_0 = \log_2 \chi_f$
  for $F$ and $G$), $R_0(F \cup G) \le \log_2 \chi_f(F \cup G) \le \log_2 \chi_f(F) + \log_2 \chi_f(G) = R_0(F) + R_0(G)$.
- **General graph unions:** When $F \cup G \ne K_n$ and $F, G$ are non-perfect (so
  $R_0 < \log_2 \chi_f$), it is open whether $R_0(F \cup G) \le R_0(F) + R_0(G)$ holds
  universally.

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

## Formal statement and certificate

- **Adversarial check (2026-11-27): the mathematics of the Statement is sound; its provenance is
  unverified.** `witsenhausenRate` is `inf_k (1/k) log₂ χ(G^{⊠k})`, the strong-product
  (Witsenhausen 1976) rate. By Fekete this infimum equals the limit, and there are no junk
  values: the set is nonempty and bounded below by `0`. `graphUnion` is the edge union. We
  checked two cheap routes and neither settles the question. (i) The asymptotic-spectrum
  duality (Zuiddam) controls `χ̄(G^{⊠k})`, which tends to the fractional clique-cover number, not
  `χ(G^{⊠k})`, so it does not apply. (ii) Fractional chromatic number is **not** multiplicative
  under the strong product (`χ_f(C₅ ⊠ C₅) = 5 < 25/4`), so `R₀ = log₂ χ_f` fails (`R₀(C₅) = log₂ √5`)
  and the OR-product argument does not transfer. The question therefore looks genuinely
  nontrivial. **Doubt:** we could not locate a sentence in Körner–Marton (1988), Simonyi
  (1995) or Tuncel–Nayak–Koulgi–Rose (2009) that explicitly poses union-subadditivity of
  `R₀` or of `H̄` as open. Charpenay–Le Treust–Roumy (arXiv:2305.01459) mention only that edge
  union "is already studied in the literature". Treat the attribution as unconfirmed until a
  quotation is found.
- **Certificate** `lean/InfoTheory/Known/Certificates/GraphEntropySubadditivity.lean`:
  Witsenhausen's bounds `log₂ ω ≤ R₀ ≤ log₂ χ` and the exact values for `K_n` and `\bar K_n`;
  `graphUnion` sanity lemmas (`graphUnion_compl : F ∪ Fᶜ = K_n`, `rate_union_compl`); the
  one-shot product-colouring bound `rate_union_le_log2_mul : R₀(F ∪ G) ≤ log₂ a + log₂ b`; and
  the regression `subadditive_of_rate_eq_log2_coloring`: the inequality holds whenever
  `R₀ = log₂ χ` for both graphs (perfect graphs). Concrete instances: `subadditive_top_top`,
  `subadditive_bot_left`.
