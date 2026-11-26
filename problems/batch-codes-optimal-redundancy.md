---
id: batch-codes-optimal-redundancy
title: Optimal Redundancy of Primitive Multiset Batch Codes
status: open
category: network-coding
posed_by: Yuval Ishai, Eyal Kushilevitz, Rafail Ostrovsky, and Amit Sahai; Hilal Asi and Eitan Yaakobi
posed_year: 2004
tags: [network-coding, batch-codes, distributed-storage, redundancy]
lean_module: InfoTheory.Problems.BatchCodesOptimalRedundancy
lean_file: lean/InfoTheory/Problems/BatchCodesOptimalRedundancy.lean
---

## Statement

A binary linear **primitive multiset $k$-batch code** of dimension $n$ and blocklength $N$ is a linear encoding map $E : \mathbb{F}_2^n \to \mathbb{F}_2^N$ such that for *every* multiset request of $k$ information indices $(i_1, \dots, i_k) \in \{1, \dots, n\}^k$ (repetitions allowed), there exist $k$ pairwise disjoint recovery subsets $R_1, \dots, R_k \subseteq \{1, \dots, N\}$ such that each requested symbol $x_{i_t}$ ($1 \le t \le k$) can be recovered from the codeword symbols $(E(x)_j)_{j \in R_t}$.

Let $N_{\min}(n, k)$ be the minimum blocklength of such a code, and let $r_B(n, k) = N_{\min}(n, k) - n$ denote its **minimum redundancy**. For every fixed $k \ge 3$, it is known that $\Omega(\sqrt{n}) \le r_B(n, k) \le O(\sqrt{n} \log n)$, whereas for the weaker notion of $k$-PIR codes (where all $k$ requests ask for the *same* symbol), the optimal redundancy is tightly $r_{\mathrm{PIR}}(n, k) = \Theta(\sqrt{n})$.

**Open Problem (Asi–Yaakobi 2019):** For every fixed constant batch size $k \ge 3$, does the optimal redundancy of binary linear primitive multiset $k$-batch codes satisfy
$$r_B(n, k) = O_k(\sqrt{n})$$
(matching the $\Omega(\sqrt{n})$ lower bound and the optimal redundancy of $k$-PIR codes by eliminating the logarithmic overhead)?

## Background

Batch codes were introduced by Ishai, Kushilevitz, Ostrovsky, and Sahai (2004) for load balancing in distributed storage systems and amortizing the server-computation cost of multi-query Private Information Retrieval. In the **primitive** setting (one coded symbol per server), a $k$-batch code guarantees that any $k$ simultaneous user requests—even with arbitrary hot-spot duplicates—can be served in parallel with each server read at most once.

Determining the exact optimal redundancy $r_B(n, k)$ as a function of $n$ and $k$ is the central extremal question for batch codes. While $r_B(n, k) = \Theta(\sqrt{n})$ is settled for $k \in \{3, 4\}$ (Vardy–Yaakobi 2016) and for the weaker $k$-PIR code problem for all constant $k$ (Fazeli–Vardy–Yaakobi 2015), a persistent $\log n$ factor separates the best known upper and lower bounds for general constant $k \ge 5$, and an even wider gap remains when $k$ grows polynomially with $n$.

## What is known

- **Small batch sizes $k \le 4$:**
  - $k = 2$: $r_B(n, 2) = 1$ (single parity bit).
  - $k = 3, 4$: Vardy and Yaakobi (2016) and Rao and Vardy (2016) proved $r_B(n, 3) = \Theta(\sqrt{n})$ and $r_B(n, 4) = \Theta(\sqrt{n})$ (with exact leading constants determined in subsequent work).
- **Lower bounds:**
  - Rao and Vardy (2016) and Woo–Lim proved $r_B(n, k) = \Omega(\sqrt{n})$ for all $k \ge 3$ (even for PIR codes).
  - Zhang, Etzion, and Yaakobi (2020) and Li and Wootters (2021) proved stronger lower bounds jointly in $n$ and $k$, including $r_B(n, k) = \Omega(\sqrt{n k})$ (and for systematic/linear codes, tensor-rank and dual-code bounds ruling out $r_B(n, n^\alpha) = o(n)$ for $\alpha \ge 1/2$).
- **Upper bounds:**
  - Ishai et al. (2004) introduced subcube and Reed–Muller-based batch codes.
  - Vardy and Yaakobi (2016) and Asi and Yaakobi (2019) constructed primitive multiset batch codes via multiplicity codes, Reed–Muller codes, and array/graph constructions achieving $r_B(n, k) = O(\sqrt{n} \log n)$ for every constant $k$, and $r_B(n, n^\varepsilon) = o(n)$ for every $\varepsilon < 1/2$ (contrasting with PIR codes, which achieve $r_{\mathrm{PIR}}(n, n^\varepsilon) = o(n)$ for all $\varepsilon < 1$).
  - Polyanskii and Vorobyev (2019) and Hollmann–Khathuria–Kuzmin–Skachek studied constructions via combinatorial designs and incidence geometries, narrowing constants without yet proving $r_B(n, k) = O_k(\sqrt{n})$ for general constant $k \ge 5$.

## References

- Y. Ishai, E. Kushilevitz, R. Ostrovsky, and A. Sahai, "Batch codes and their applications," *Proc. 36th ACM STOC*, pp. 262–271, 2004.
- A. Fazeli, A. Vardy, and E. Yaakobi, "PIR with low storage overhead: Coding instead of replication," *arXiv:1505.06241*, 2015.
- A. Vardy and E. Yaakobi, "Constructions of batch codes with near-optimal redundancy," *Proc. IEEE ISIT*, pp. 1197–1201, 2016.
- S. Rao and A. Vardy, "Lower bound on the redundancy of PIR codes," *arXiv:1605.01869*, 2016.
- H. Asi and E. Yaakobi, "Nearly optimal constructions of PIR and batch codes," *IEEE Trans. Inf. Theory*, 65(2):947–964, 2019.
- R. Li and M. Wootters, "Improved lower bounds for primitive batch codes," *IEEE Trans. Inf. Theory*, 67(10):6476–6485, 2021.
