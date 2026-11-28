---
id: undirected-network-coding-li-li
title: The Li–Li Conjecture for Undirected Multiple-Unicast Network Coding
status: open
category: network-coding
posed_by: Zongpeng Li and Baochun Li
posed_year: 2004
tags: [network-coding, undirected-networks, multiple-unicast, li-li-conjecture]
lean_module: InfoTheory.Problems.UndirectedNetworkCodingLiLi
lean_file: lean/InfoTheory/Problems/UndirectedNetworkCodingLiLi.lean
---

## Statement

Let $G = (V, E, c)$ be a finite **undirected** graph with symmetric nonnegative integer edge capacities $c(u, v) = c(v, u)$, together with $k \ge 1$ source–destination pairs $(s_1, t_1), \dots, (s_k, t_k)$ with $s_i \neq t_i$. In an undirected network, each edge $\{u, v\}$ of capacity $c(u, v)$ may be split arbitrarily between traffic flowing from $u$ to $v$ and from $v$ to $u$ (subject to total rate $\le c(u, v)$).

Let $\lambda_{\mathrm{route}}(G)$ denote the maximum symmetric fractional **multicommodity routing throughput** (the supremum $\lambda \ge 0$ such that $k$ concurrent flows of rate $\lambda$ from $s_i$ to $t_i$ can be routed simultaneously without exceeding edge capacities), and let $\lambda_{\mathrm{code}}(G)$ denote the maximum symmetric **network coding throughput** (allowing arbitrary coding at internal nodes). Clearly $\lambda_{\mathrm{code}}(G) \ge \lambda_{\mathrm{route}}(G)$.

**Li–Li Conjecture (2004):** For **every** undirected multiple-unicast network, network coding provides **zero** throughput advantage over fractional multicommodity routing:
$$\lambda_{\mathrm{code}}(G) = \lambda_{\mathrm{route}}(G).$$

## Background

In **directed** networks, network coding can dramatically outperform routing even for two unicast sessions (as demonstrated by the famous butterfly network, where coding achieves throughput $1$ vs. routing throughput $1/2$, and more generally the coding advantage can grow as $\Omega(|V|)$). In **undirected** networks, however, Li and Li (2004) observed that every undirected multiple-unicast example they examined had coding throughput equal to multicommodity flow throughput—unlike undirected *multicast* networks, where coding can achieve a constant-factor advantage up to $2$ (Agarwal–Charikar 2004).

The Li–Li conjecture (also widely known as the **undirected multiple-unicast conjecture**) is arguably the most famous open problem in network coding theory. Its validity would imply deep structural consequences beyond networking: Adler, Harvey, Jain, Kleinberg, and Lehman (2006) showed that a refutation with a large gap would connect to non-trivial circuit/communication lower bounds, while Braverman, Garg, and Schvartzman (2017) linked the conjecture to external information complexity and graph-cut metrics.

## What is known

- **Solved special cases (confirming $\lambda_{\mathrm{code}} = \lambda_{\mathrm{route}}$):**
  - $k = 1$ (single unicast): max-flow/min-cut.
  - $k = 2$ (two unicast pairs): Hu's two-commodity flow theorem (1963) implies the cut-set bound equals fractional routing throughput, so coding cannot improve upon routing.
  - All networks where the sparsest-cut / multicommodity flow-cut gap is $1$ (e.g., planar graphs with all terminals on the outer face, Okamura–Seymour networks, $K_{2,3}$-minor-free graphs).
  - **Bipartite graphs and graphs with small terminals / symmetric instances:** Harvey, Kleinberg, and Lehman (2006) proved $\lambda_{\mathrm{code}} = \lambda_{\mathrm{route}}$ on several structured classes (such as the Okamura–Seymour graph and certain symmetric bipartite graphs) using the **information dominance / PdE (partition-based) outer bound** rather than cuts alone.
  - **Linear network coding and $k$-pairs on small graphs:** Extensive computer searches using Shannon-type information inequalities (and Matúš/Zhang–Yeung inequalities) have failed to produce any counterexample, even on the smallest graph with a strict flow-cut gap (the $K_{3,3}$-like Okamura–Seymour / $K_{2,3}$-containing instances, where the flow-cut gap is $> 1$ yet the Shannon-type coding bound still matches routing!).
- **Known upper bounds on the possible coding advantage:**
  - By Leighton–Rao (1999) and Linial–London–Rabinovich (1995) / Aumann–Rabani (1998), the multicommodity flow-cut gap in any undirected graph with $k$ terminal pairs is $O(\log k)$. Since network coding is bounded above by the cut-set (sparsest-cut) bound, $\lambda_{\mathrm{code}}(G) / \lambda_{\mathrm{route}}(G) = O(\log k)$ always holds.
- **Undirected multicast contrast:** For undirected single-source multicast, Li and Li (2004) and Agarwal and Charikar (2004) proved that coding can outperform routing (fractional Steiner tree packing), with advantage at most $2$ (matching the integrality gap of the bidirected cut relaxation).

## Formal statement and certificate

- The Lean statement (`Problems/UndirectedNetworkCodingLiLi.lean`, Core
  `undirectedRoutingThroughput` / `undirectedCodingThroughput`) was checked on 2026-11-27 and
  left unchanged. Both models match the text: undirected capacity shared across the two
  directions and across rounds, causal local encoding, and zero-error decoding at each sink.
- **Certificate** (`lean/InfoTheory/Known/Certificates/UndirectedNetworkCodingLiLi.lean`): no
  junk. Both sets contain `0` and are bounded by elementary cuts: `routing_le_srcCut`
  (`λ_route ≤ Σ_u cap(s₁,u)`) and `coding_le_dstCut` (`λ_code ≤ Σ_w cap(w,t₁)`, a counting
  argument on the exact code model). Regression ($k = 1$): on a single unit edge,
  `λ_route = λ_code = 1` (`liLi_singleEdge`). The inequality `λ_route ≤ λ_code` is not
  certified in general.

## References

- Z. Li and B. Li, "Network coding: The case of multiple unicast sessions," *Proc. 42nd Allerton Conf. on Communication, Control, and Computing*, 2004.
- M. Adler, N. J. A. Harvey, K. Jain, R. Kleinberg, and A. R. Lehman, "On the capacity of information networks," *Proc. 17th ACM–SIAM SODA*, pp. 241–250, 2006.
- N. J. A. Harvey, R. Kleinberg, and A. R. Lehman, "On the capacity of information networks," *IEEE Trans. Inf. Theory*, 52(6):2345–2364, 2006.
- A. Agarwal and M. Charikar, "On the advantage of network coding for improving network throughput," *Proc. IEEE Information Theory Workshop (ITW)*, pp. 247–249, 2004.
- S. Jalali, M. Effros, and T. Ho, "On the impact of a single edge on the network coding capacity," *Proc. Information Theory and Applications Workshop (ITA)*, 2011.
- M. Braverman, A. Garg, and A. Schvartzman, "Coding in undirected graphs is either very helpful or not helpful at all," *Proc. 8th ITCS*, pp. 18:1–18:18, 2017.
