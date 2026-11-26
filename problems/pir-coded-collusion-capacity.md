---
id: pir-coded-collusion-capacity
title: Capacity of T-Colluding Private Information Retrieval from MDS-Coded Databases
status: open
category: network-coding
posed_by: Ragnar Freij-Hollanti, Oliver W. Gnilke, Camilla Hollanti, and David A. Karpuk; Hua Sun and Syed A. Jafar
posed_year: 2017
tags: [network-coding, private-information-retrieval, mds-codes, collusion]
lean_module: InfoTheory.Problems.PirCodedCollusionCapacity
lean_file: lean/InfoTheory/Problems/PirCodedCollusionCapacity.lean
---

## Statement

Consider a distributed storage system of $N$ servers storing $M$ independent files encoded using an $[N, K]$ Maximum Distance Separable (MDS) code over a finite field $\mathbb{F}_q$ (so any $K$ servers suffice to reconstruct all $M$ files). A user wishes to retrieve a single file $W_\theta$ ($\theta \in \{1, \dots, M\}$) while preserving information-theoretic **$T$-privacy**: any subset of up to $T$ colluding servers learns zero information about the requested index $\theta$ from their joint queries.

Let $C(N, K, T, M)$ denote the supremum achievable PIR download rate (bits of desired file retrieved per total bits downloaded from all $N$ servers), and let
$$C_\infty(N, K, T) = \inf_{M \ge 1} C(N, K, T, M) = \lim_{M \to \infty} C(N, K, T, M)$$
be the asymptotic MDS-TPIR capacity as the number of files grows large.

Freij-Hollanti, Gnilke, Hollanti, and Karpuk (2017) constructed star-product schemes achieving rate $\left(1 + \frac{K+T-1}{N} + \dots + \left(\frac{K+T-1}{N}\right)^{M-1}\right)^{-1}$ for $K + T - 1 < N$ (approaching $1 - \frac{K+T-1}{N}$ as $M \to \infty$) and conjectured this formula equals $C(N, K, T, M)$. Sun and Jafar (2018) **disproved** the finite-$M$ conjecture by achieving rate $3/5 > 4/7$ at $(N, K, T, M) = (4, 2, 2, 2)$.

**Open Problem:** Determine the exact MDS-TPIR capacity $C(N, K, T, M)$ for general $(N, K, T, M)$—and in particular settle the **Asymptotic MDS-TPIR Capacity Conjecture**: does
$$C_\infty(N, K, T) = 1 - \frac{K + T - 1}{N}$$
hold for all integers $1 \le K, T$ with $K + T - 1 < N$?

## Background

Private Information Retrieval (Chor, Goldreich, Kushilevitz, and Sudan 1995) studies how to query replicated or coded databases without leaking which record is sought. Sun and Jafar (2017) revolutionized the area by determining the exact capacity of replicated PIR ($K = 1, T = 1$) and $T$-colluding replicated PIR ($K = 1$, general $T$), and Banawan and Ulukus (2018) settled MDS-coded PIR without collusion ($T = 1$, general $K$).

Combining MDS-coded storage ($K > 1$) with server collusion ($T > 1$)—known as **MDS-TPIR**—revealed surprising algebraic subtlety: the naive unification replacing $K$ or $T$ by $K + T - 1$ was refuted by Sun and Jafar (2018) for finite $M$, showing that the interaction between MDS storage redundancy and collusion-resistant query spaces is strictly richer than either special case alone.

## What is known

- **Replicated $T$-colluding PIR ($K = 1$, Sun–Jafar 2017):** Exact capacity is
  $$C(N, 1, T, M) = \left(1 + \frac{T}{N} + \left(\frac{T}{N}\right)^2 + \dots + \left(\frac{T}{N}\right)^{M-1}\right)^{-1}, \qquad C_\infty(N, 1, T) = 1 - \frac{T}{N}.$$
- **MDS-coded non-colluding PIR ($T = 1$, Banawan–Ulukus 2018):** Exact capacity is
  $$C(N, K, 1, M) = \left(1 + \frac{K}{N} + \left(\frac{K}{N}\right)^2 + \dots + \left(\frac{K}{N}\right)^{M-1}\right)^{-1}, \qquad C_\infty(N, K, 1) = 1 - \frac{K}{N}.$$
- **Star-product achievability (Freij-Hollanti et al. 2017; Tajeddine–Gnilke–El Rouayheb 2018):** Using star products of Generalized Reed–Solomon codes, rate $\left(\sum_{i=0}^{M-1} \left(\frac{K+T-1}{N}\right)^i\right)^{-1}$ is achievable whenever $K + T - 1 < N$, giving $C_\infty(N, K, T) \ge 1 - \frac{K+T-1}{N}$.
- **Disproof of the finite-$M$ conjecture (Sun–Jafar 2018):** For $(N, K, T, M) = (4, 2, 2, 2)$, Sun and Jafar constructed a scheme achieving rate $3/5 = 0.6$, strictly exceeding the conjectured value $(1 + 3/4)^{-1} = 4/7 \approx 0.5714$.
- **Restricted converses (Holzbaur–Freij-Hollanti–Li–Hollanti 2021):** Proved that the Freij-Hollanti formula *is* exact when restricted to **linear, full support-rank** MDS-TPIR schemes, while also showing that relaxing full support-rank allows strictly higher rates for small $M$.
- **General converse / asymptotic limit $M \to \infty$:** Remains open for general $(N, K, T)$ with $K \ge 2$ and $T \ge 2$.

## References

- H. Sun and S. A. Jafar, "The capacity of private information retrieval," *IEEE Trans. Inf. Theory*, 63(7):4075–4088, 2017.
- H. Sun and S. A. Jafar, "The capacity of private information retrieval with colluding databases," *IEEE Trans. Inf. Theory*, 64(4):2361–2378, 2018 (arXiv:1605.00635, 2016).
- K. Banawan and S. Ulukus, "The capacity of private information retrieval from coded databases," *IEEE Trans. Inf. Theory*, 64(3):1945–1956, 2018.
- R. Freij-Hollanti, O. W. Gnilke, C. Hollanti, and D. A. Karpuk, "Private information retrieval from coded databases with colluding servers," *SIAM J. Applied Algebra and Geometry*, 1(1):647–664, 2017.
- R. Tajeddine, O. W. Gnilke, and S. El Rouayheb, "Private information retrieval from MDS coded data in distributed storage systems," *IEEE Trans. Inf. Theory*, 64(11):7081–7093, 2018.
- H. Sun and S. A. Jafar, "Private information retrieval from MDS coded data with colluding servers: Settling a conjecture by Freij-Hollanti et al.," *IEEE Trans. Inf. Theory*, 64(2):1000–1022, 2018.
- L. Holzbaur, R. Freij-Hollanti, J. Li, and C. Hollanti, "Towards the capacity of private information retrieval from coded and colluding servers," *IEEE Trans. Inf. Theory*, 68(1):517–537, 2022 (arXiv:1903.12552, 2019/2021).
