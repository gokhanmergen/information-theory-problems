---
id: reed-muller-capacity-general-dmc
title: Capacity Achievement of Reed–Muller Codes on General Binary-Input DMCs
status: partially-solved
category: coding-theory
posed_by: D. J. Costello; G. D. Forney; E. Abbe; A. Shpilka; A. Wigderson (folklore)
posed_year: 1994
tags: [coding-theory, reed-muller-codes, channel-capacity, map-decoding]
lean_module: InfoTheory.Problems.ReedMullerCapacityGeneralDmc
lean_file: lean/InfoTheory/Problems/ReedMullerCapacityGeneralDmc.lean
---

## Statement

For integers $0 \le r \le m$, the binary **Reed–Muller code** $\mathrm{RM}(m, r)$ of blocklength $N = 2^m$ is the $\mathbb{F}_2$-linear subspace of functions $f : \mathbb{F}_2^m \to \mathbb{F}_2$ spanned by all multilinear monomials $\prod_{j \in S} x_j$ with $|S| \le r$; its dimension is $k(m, r) = \sum_{i=0}^{r} \binom{m}{i}$ and its rate is $R(m, r) = k(m, r) / 2^m$.

Let $W : \{0, 1\} \to \mathcal{Y}$ be an arbitrary (not necessarily symmetric) binary-input discrete memoryless channel (DMC) with finite output alphabet $\mathcal{Y}$, and let $I_{\mathrm{unif}}(W) = I(U; Y)$ be its symmetric (uniform-input) mutual information when $U \sim \mathrm{Unif}(\{0, 1\})$. Since $\mathrm{RM}(m, r)$ is linear and contains the all-ones codeword, $I_{\mathrm{unif}}(W)$ is the largest rate any sequence of Reed–Muller codes can achieve over $W$ (and equals the Shannon capacity $C(W)$ whenever $W$ is a binary-input memoryless symmetric (BMS) channel).

**Open Problem:** Do Reed–Muller codes achieve the uniform-input mutual information $I_{\mathrm{unif}}(W)$ under block-MAP decoding on **every** binary-input DMC $W$ (including asymmetric channels such as the Z-channel)? That is, for every binary-input DMC $W$, every $R \in [0, I_{\mathrm{unif}}(W))$, and every $\varepsilon > 0$, does there exist $m_0$ such that for every $m \ge m_0$, some $r \le m$ yields $R(m, r) \ge R$ and block-MAP decoding error at most $\varepsilon$ over $W^{\otimes 2^m}$?

*(A closely related major open problem is whether Reed–Muller codes can be decoded in **polynomial time** up to capacity on BMS channels such as the BSC.)*

## Background

Introduced by Muller (1954) and Reed (1954), Reed–Muller codes are among the oldest and most symmetric algebraic codes, invariant under the entire general affine group $\mathrm{GA}(m, 2)$. For decades it was conjectured that Reed–Muller codes achieve Shannon capacity on every BMS channel (including the BEC and BSC) under MAP decoding.

This conjecture saw a sequence of landmark breakthroughs over the past decade, culminating in the full resolution of the **BMS case**: Kudekar et al. (2017) proved capacity achievement on the BEC via sharp thresholds of symmetric monotone Boolean functions; Reeves and Pfister (2021) proved bit-MAP capacity on all BMS channels; and Abbe and Sandon (2023) proved block-MAP capacity on all BMS channels. However, all existing proofs depend crucially on BMS channel symmetry (specifically, symmetry of log-likelihood ratios and BMS degradation/polarization orderings). Extending capacity achievement to **general asymmetric binary-input DMCs**—as well as finding **efficient polynomial-time decoders** achieving capacity on the BSC—remains open.

## What is known

- **Binary Erasure Channel (BEC):** Kudekar, Kumar, Mondelli, Pfister, Şaşoğlu, and Urbanke (2017) proved that Reed–Muller codes achieve capacity on the $\mathrm{BEC}(p)$ under bit-MAP and block-MAP decoding by exploiting the doubly transitive automorphism group of $\mathrm{RM}(m, r)$ and the Bourgain–Kalai / Friedgut–Kalai sharp-threshold theorem.
- **Bit-MAP on all BMS channels:** Reeves and Pfister (2021, IEEE TIT 2024) proved that Reed–Muller codes achieve capacity on every BMS channel under **bit-MAP** decoding, using nested codechains, generalized EXIT (GEXIT) relations, and the symmetry of BMS channels.
- **Block-MAP on all BMS channels:** Abbe and Sandon (STOC 2023) proved that Reed–Muller codes achieve capacity on every BMS channel under **block-MAP** decoding, via a novel polarization/boosting argument on the conditional entropy of syndrome projections that still requires BMS channel symmetry.
- **High-rate / low-rate regimes and weight enumerators:** Abbe, Shpilka, and Wigderson (2015) and Samorodnitsky (2020) obtained bounds on weight distributions and capacity in extreme rate regimes.
- **What remains open:**
  1. Block-MAP (and even bit-MAP) achievement of $I_{\mathrm{unif}}(W)$ on **arbitrary asymmetric binary-input DMCs** $W$ (such as the binary Z-channel).
  2. **Polynomial-time decoding** of Reed–Muller codes at rates approaching capacity on BMS channels (even on $\mathrm{BSC}(p)$); current efficient decoders (e.g., recursive projection-aggregation, Ye–Abbe 2020) are not known to achieve capacity asymptotically.

## References

- D. E. Muller, "Application of Boolean algebra to switching circuit design and to error detection," *IRE Trans. Electronic Computers*, EC-3(3):6–12, 1954.
- I. S. Reed, "A class of multiple-error-correcting codes and the decoding scheme," *Trans. IRE Professional Group on Information Theory*, 4(4):38–49, 1954.
- E. Abbe, A. Shpilka, and A. Wigderson, "Reed–Muller codes for random erasures and errors," *IEEE Trans. Inf. Theory*, 61(10):5229–5252, 2015.
- S. Kudekar, S. Kumar, M. Mondelli, H. D. Pfister, E. Şaşoğlu, and R. L. Urbanke, "Reed–Muller codes achieve capacity on erasure channels," *IEEE Trans. Inf. Theory*, 63(7):4298–4316, 2017.
- G. Reeves and H. D. Pfister, "Reed–Muller codes on BMS channels achieve vanishing bit-error probability for all rates below capacity," *IEEE Trans. Inf. Theory*, 70(2):920–949, 2024 (arXiv:2110.14631, 2021).
- E. Abbe and C. Sandon, "A proof that Reed–Muller codes achieve Shannon capacity on symmetric channels," *Proc. 55th ACM STOC* / *IEEE FOCS*, 2023 (arXiv:2304.02409).
- M. Ye and E. Abbe, "Recursive projection-aggregation decoding of Reed–Muller codes," *IEEE Trans. Inf. Theory*, 66(8):4948–4965, 2020.
