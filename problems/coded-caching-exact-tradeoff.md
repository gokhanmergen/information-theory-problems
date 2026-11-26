---
id: coded-caching-exact-tradeoff
title: Exact Rate–Memory Tradeoff of Centralized Coded Caching with Coded Placement
status: partially-solved
category: network-coding
posed_by: Mohammad Ali Maddah-Ali and Urs Niesen
posed_year: 2014
tags: [network-coding, coded-caching, rate-memory-tradeoff, broadcast]
lean_module: InfoTheory.Problems.CodedCachingExactTradeoff
lean_file: lean/InfoTheory/Problems/CodedCachingExactTradeoff.lean
---

## Statement

Consider the centralized $(N, K)$ **coded caching** network: a server holds $N$ independent files of $F$ bits each and connects via a shared noiseless broadcast link to $K$ users, each equipped with a local cache of capacity $M F$ bits ($0 \le M \le N$). In the **placement phase** (before user demands are revealed), the server populates each user's cache using an arbitrary (possibly **coded**) function of the $N$ files. In the **delivery phase**, each user $k \in \{1, \dots, K\}$ requests a single file $d_k \in \{1, \dots, N\}$, and the server broadcasts a message of at most $R F$ bits so that every user recovers its requested file with zero error from the broadcast and its local cache.

Let $R^*(N, K, M)$ denote the infimum achievable worst-case broadcast rate $R$ (over all file sizes $F \ge 1$ and arbitrary coded placement and delivery schemes). For integer $t \in \{0, 1, \dots, K\}$ and cache memory $M = t N / K$, the Maddah-Ali–Niesen (2014) uncoded-placement scheme achieves rate $R_{\mathrm{MAN}}(t N / K) = \frac{K - t}{t + 1}$ whenever $N \ge K$.

**Open Problem:** Determine the exact optimal rate–memory tradeoff $R^*(N, K, M)$ under arbitrary (coded) cache placement for all $(N, K, M)$. In particular, **when $N \ge K \ge 2$ and $M = t N / K$ for an integer $t \in \{1, \dots, K\}$, is uncoded Maddah-Ali–Niesen placement optimal**, i.e., does
$$R^*\!\left(N, K, \frac{t N}{K}\right) = \frac{K - t}{t + 1}$$
hold for all $N \ge K \ge 2$ and all $1 \le t \le K$?

## Background

Maddah-Ali and Niesen (2014) showed that carefully designing cache placement to enable coded multicast transmissions during delivery yields a global caching gain of $(1 + K M / N)^{-1}$—a multiplicative reduction in broadcast traffic scaling with the *aggregate* cache memory across all users, rather than only each user's local memory.

Yu, Maddah-Ali, and Avestimehr (2018) completely settled the exact optimal rate–memory tradeoff $R^*_{\mathrm{uncoded}}(N, K, M)$ when placement is restricted to **uncoded** prefetching (storing raw subfiles without cross-file coding), and proved that $R^*_{\mathrm{uncoded}}(N, K, M) \le 2 R^*(N, K, M)$ universally. However, coded cache placement is known to strictly outperform uncoded prefetching in the small-memory regime ($M < N/K$, e.g., Chen–Fan–Letaief 2016; Tian–Chen 2018; Gómez-Vilardebó 2018). For general $(N, K)$ and arbitrary coded placement—including whether coded placement can ever improve on the Maddah-Ali–Niesen corner points $M = t N / K$ ($t \ge 1$) when $N \ge K \ge 4$—the exact optimal rate–memory tradeoff remains open.

## What is known

- **Exact tradeoff for uncoded prefetching (Yu–Maddah-Ali–Avestimehr 2018):** Completely characterized $R^*_{\mathrm{uncoded}}(N, K, M)$ for all $(N, K, M)$, improving on the original Maddah-Ali–Niesen rate when $N < K$ or for redundant demands, and matching $\frac{K - t}{t + 1}$ at $M = t N / K$ whenever $N \ge K$.
- **Factor-2 optimality (Yu–Maddah-Ali–Avestimehr 2018):** Proved $R^*_{\mathrm{uncoded}}(N, K, M) \le 2 R^*(N, K, M)$ for all $(N, K, M)$ (improving earlier factor-12 and factor-4 bounds of Maddah-Ali–Niesen 2014 and Ghasemi–Ramamoorthy 2017).
- **Coded placement beats uncoded placement for small $M$:**
  - Chen, Fan, and Letaief (2016): achieved $(M, R) = (1/K, N(K - 1)/K)$ when $N \le K$, strictly beating uncoded prefetching.
  - Tian and Chen (2018) and Gómez-Vilardebó (2018) constructed further coded-placement schemes strictly improving on uncoded prefetching for small $M$.
- **Solved small cases with coded placement:**
  - $N = 2$, arbitrary $K$: exact $R^*(2, K, M)$ determined (Tian 2018).
  - $(N, K) = (3, 3)$: exact $R^*(3, 3, M)$ completely determined by Tian (2018) via computer-aided Shannon-type information inequalities, proving that coded placement strictly helps only for $M < 1$ and that $R^*(3, 3, 1) = 1 = (3 - 1)/(1 + 1)$ and $R^*(3, 3, 2) = 1/3$ are exact!
  - Large memory $M = N(K - 1)/K$ ($t = K - 1$): $R^* = 1/K$ is exact by the cut-set bound.
- **Open cases:** General $(N, K)$ with $K \ge 4$ (even $(N, K) = (4, 4)$ at $M = 1$, where $R_{\mathrm{MAN}} = 3/2$ vs. best known converse!).

## References

- M. A. Maddah-Ali and U. Niesen, "Fundamental limits of caching," *IEEE Trans. Inf. Theory*, 60(5):2856–2867, 2014.
- Z. Chen, P. Fan, and K. B. Letaief, "Fundamental limits of caching: Improved bounds for users with small buffers," *IET Communications*, 10(17):2315–2318, 2016.
- H. Ghasemi and A. Ramamoorthy, "Improved lower bounds for coded caching," *IEEE Trans. Inf. Theory*, 63(7):4388–4413, 2017.
- Q. Yu, M. A. Maddah-Ali, and A. S. Avestimehr, "The exact rate-memory tradeoff for caching with uncoded prefetching," *IEEE Trans. Inf. Theory*, 64(2):1281–1296, 2018.
- Q. Yu, M. A. Maddah-Ali, and A. S. Avestimehr, "Characterizing the rate-memory tradeoff in cache networks within a factor of 2," *IEEE Trans. Inf. Theory*, 65(1):647–663, 2019 (arXiv:1702.04563, 2017).
- C. Tian, "Symmetry, outer bounds, and code constructions: A computer-aided investigation on the fundamental limits of caching," *Entropy*, 20(8):603, 2018.
- C. Tian and J. Chen, "Caching and delivery via interference elimination," *IEEE Trans. Inf. Theory*, 64(3):1548–1560, 2018.
- J. Gómez-Vilardebó, "Fundamental limits of caching: Improved rate-memory tradeoff with coded prefetching," *IEEE Trans. Communications*, 66(10):4488–4497, 2018.
