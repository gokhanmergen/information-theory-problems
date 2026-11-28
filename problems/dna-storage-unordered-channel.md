---
id: dna-storage-unordered-channel
title: Capacity of the Shuffled Noisy-Draws DNA Storage Channel with Deletion Noise
status: partially-solved
category: network-coding
posed_by: Ilan Shomorony and Reinhard Heckel; Nir Weinberger and Neri Merhav
posed_year: 2021
tags: [network-coding, dna-storage, shuffling-channel, deletion-channel]
lean_module: InfoTheory.Problems.DnaStorageUnorderedChannel
lean_file: lean/InfoTheory/Problems/DnaStorageUnorderedChannel.lean
---

## Statement

Consider the **noisy shuffling channel** for DNA-based data storage with i.i.d. deletion noise $\mathrm{Del}_d$ ($d \in (0, 1)$) in the logarithmic molecule-length regime: an encoder stores a message by writing $M$ binary strands $x_1, \dots, x_M \in \{0, 1\}^L$ of length $L = \lfloor \beta \log_2 M \rfloor$ (where $\beta > 1$ is a fixed scaling parameter). Each strand passes independently through the binary deletion channel $\mathrm{Del}_d$, and the receiver observes only the **unordered multiset** of the $M$ resulting noisy strands (equivalently, the decoder must be invariant under arbitrary permutations of the $M$ output traces).

A storage rate $R \ge 0$ (bits per stored symbol) is achievable if for every $\varepsilon > 0$ and all sufficiently large $M$, there exist an encoder and a permutation-invariant decoder transmitting $\lfloor 2^{M L R} \rfloor$ messages with average block error probability at most $\varepsilon$. Let $C_{\mathrm{shuf\text{-}del}}(d, \beta)$ denote the supremum achievable rate, and let $C_{\mathrm{del}}(d)$ denote the Shannon capacity of the standard (ordered) binary deletion channel $\mathrm{Del}_d$.

**Open Problem:** Determine the exact capacity of the shuffled noisy-draws DNA storage channel under deletion (and insertion–deletion) noise for arbitrary molecule-length scaling $\beta > 1$ and coverage depth. In particular, **does the Shomorony–Heckel shuffling-penalty law hold for the binary deletion channel at sufficiently large $\beta$**—i.e., for every $d \in (0, 1)$, does there exist $\beta_0 > 1$ such that for all $\beta \ge \beta_0$,
$$C_{\mathrm{shuf\text{-}del}}(d, \beta) = C_{\mathrm{del}}(d) - \frac{1}{\beta}?$$

## Background

In DNA data storage, information is synthesized onto millions of short DNA molecules stored together in a pool, losing all spatial ordering, and read via random sampling (PCR amplification and shotgun sequencing) accompanied by substitution, insertion, and deletion errors. Heckel, Shomorony, Ramchandran, and Tse (2017) and Shomorony and Heckel (2021) introduced the **noisy shuffling** and **shuffling-sampling** channel models to capture the fundamental storage density limits of this architecture.

For **noiseless** shuffling and for **memoryless substitution channels** (such as $\mathrm{BSC}(p)$ and general DMCs), Shomorony–Heckel (2021) and Weinberger–Merhav (2022) established exact capacity characterizations: in the noiseless case $C(\beta) = 1 - 1/\beta$ (where $1/\beta$ is the exact rate penalty of indexing unordered strands), and for $\mathrm{BSC}(p)$ at sufficiently large $\beta$, $C_{\mathrm{shuf\text{-}BSC}}(p, \beta) = 1 - h(p) - 1/\beta$. However, when the per-molecule channel has **synchronization noise** (deletions or insertions), the lack of a single-letter capacity formula and tight error-exponent bounds for $\mathrm{Del}_d$ leaves both the exact capacity and even the separation law $C_{\mathrm{shuf\text{-}del}}(d, \beta) = C_{\mathrm{del}}(d) - 1/\beta$ open.

## What is known

- **Noiseless shuffling and shuffling-sampling (Heckel–Shomorony–Ramchandran–Tse 2017; Shomorony–Heckel 2021):**
  - Pure noiseless shuffling ($M$ strands, $L = \beta \log_2 M$): $C(\beta) = (1 - 1/\beta)^+$.
  - Noiseless random sampling with coverage $c$ ($N = c M$ i.i.d. draws with replacement): $C(c, \beta) = (1 - e^{-c})(1 - 1/\beta)^+$ for $\beta > 1$.
- **Substitution noise ($\mathrm{BSC}(p)$ and general DMCs):**
  - Shomorony and Heckel (2021) proved $C_{\mathrm{shuf\text{-}BSC}}(p, \beta) \le 1 - h(p) - 1/\beta$ and showed equality $C_{\mathrm{shuf\text{-}BSC}}(p, \beta) = 1 - h(p) - 1/\beta$ holds whenever $p < 1/4$ and $\beta > \frac{2}{-\log_2(1 - 2p(1-p))}$ (sufficiently large $\beta$), while also showing that for smaller $\beta$ / higher noise, index errors prevent naive index separation.
  - Weinberger and Merhav (2022) derived exact capacity characterizations and error-exponent bounds for the shuffled-sampling DNA storage channel over **arbitrary memoryless substitution DMCs** in the $L = \beta \log_2 M$ regime, using multi-draw mutual information and Poissonized coverage analysis.
- **Deletion / indel noise (open):**
  - Lenz, Siegel, Wachter-Zeh, and Yaakobi (2019, 2020) constructed explicit coding schemes and derived bounds for unordered sets of strings under substitutions and deletions.
  - Exact capacity of the shuffled-noisy-draws channel with $\mathrm{Del}_d$ (or general insertion–deletion) noise remains **open**—both because $C_{\mathrm{del}}(d)$ itself is unknown and because proving the exact $1/\beta$ shuffling-penalty identity $C_{\mathrm{shuf\text{-}del}}(d, \beta) = C_{\mathrm{del}}(d) - 1/\beta$ for large $\beta$ requires controlling finite-blocklength error exponents of $\mathrm{Del}_d$ at logarithmic strand length $L = \beta \log_2 M$.

## Formal statement and certificate

Adversarial audit (2026-11-27): the Lean `Statement` is faithful to the open question, though it
covers the shuffling channel without sampling (each strand is read exactly once).
- The noiseless (`1 - 1/β`) and BSC (`1 - h(p) - 1/β`, large β) laws are proved results
  (Shomorony–Heckel 2021).
- A search found no 2024–2026 result for deletion noise.

Certificate `lean/InfoTheory/Known/Certificates/DnaStorageUnorderedChannel.lean` proves the following:
- Rate 0 is achievable, so the capacity set is non-empty and the capacity is `≥ 0`.
- At `d = 0` strands are received intact, and the conjectured formula reduces to the proven
  noiseless law `1 - 1/β`, using `C_del(0) = 1`.
- The right-hand side is `≤ 1 - d - 1/β`.

Not certified: that the set of achievable rates is bounded above, which is needed to rule out the
`sSup` junk value.

## References

- R. Heckel, I. Shomorony, K. Ramchandran, and D. N. C. Tse, "Fundamental limits of DNA storage systems," *Proc. IEEE ISIT*, pp. 3130–3134, 2017.
- A. Lenz, P. H. Siegel, A. Wachter-Zeh, and E. Yaakobi, "Anchor-based correction of substitutions in indexed sets," *Proc. IEEE ISIT*, pp. 757–761, 2019 (and "Coding over sets for DNA storage," *IEEE Trans. Inf. Theory*, 66(4):2331–2351, 2020).
- I. Shomorony and R. Heckel, "DNA-based storage: Models and fundamental limits," *IEEE Trans. Inf. Theory*, 67(6):3675–3689, 2021.
- N. Weinberger and N. Merhav, "The DNA storage channel: Capacity and error probability bounds," *IEEE Trans. Inf. Theory*, 68(9):5657–5700, 2022.
