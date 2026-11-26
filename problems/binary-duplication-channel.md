---
id: binary-duplication-channel
title: Capacity and Optimal Input Support of the Geometric Binary Duplication Channel
status: open
category: channel-capacity
posed_by: Michael Mitzenmacher; Noam Kirshner and Farzad Farnoud
posed_year: 2008
tags: [channel-capacity, synchronization, duplication-channel, sticky-channel]
lean_module: InfoTheory.Problems.BinaryDuplicationChannel
lean_file: lean/InfoTheory/Problems/BinaryDuplicationChannel.lean
---

## Statement

Fix a duplication parameter $p \in (0, 1)$. In the **i.i.d. geometric binary duplication channel** (also called the *geometric sticky channel*), each input bit $x_j \in \{0, 1\}$ is independently replaced by $K_j \ge 1$ consecutive copies of $x_j$, where $K_j \sim \mathrm{Geom}(1 - p)$ has distribution $\Pr[K_j = k] = (1 - p) p^{k - 1}$ for $k \ge 1$.

Because every bit produces at least one output copy, the number of alternating runs is preserved and each input run of length $r \ge 1$ independently maps to an output run of length $s \ge r$ with Negative Binomial transition probability
$$W_p(s \mid r) = \binom{s - 1}{r - 1} (1 - p)^r p^{s - r}, \qquad s \ge r \ge 1.$$
By Mitzenmacher (2008), i.i.d. input run lengths are capacity-achieving, so the channel capacity (in bits per input bit) admits the renewal-reward variational characterization
$$C_{\mathrm{dup}}(p) = \sup_{P_R} \frac{I(R; S)}{\mathbb{E}[R]},$$
where the supremum is over all probability distributions $P_R$ on $\mathbb{Z}_{\ge 1}$ with finite mean $\mathbb{E}[R] < \infty$, and $S \mid (R = r) \sim W_p(\cdot \mid r)$.

**Problem (Capacity and Convexity of the Geometric Binary Duplication Channel).** Determine the exact capacity $C_{\mathrm{dup}}(p)$ for $p \in (0, 1)$, and in particular decide whether $p \mapsto C_{\mathrm{dup}}(p)$ is **convex** on $(0, 1)$.

## Background

The i.i.d. geometric binary duplication channel is the cleanest synchronization channel without deletions, arising in clock-drift modeling, DNA storage / tandem duplication systems, and variable-rate sampling. Unlike the binary deletion channel, the absence of deletions preserves run boundaries, reducing the multi-letter capacity to the single-run ratio optimization $\sup_{P_R} I(R; S)/\mathbb{E}[R]$ over positive integer run lengths $R$.

Despite this dramatic simplification, no closed-form expression for $C_{\mathrm{dup}}(p)$ is known for any $p \in (0, 1)$. Even more intriguingly, numerical Blahut–Arimoto optimizations (Mitzenmacher 2008; Cheraghchi 2019; Kirshner–Farnoud 2020) reveal that the capacity-achieving run-length distribution $P_R^*$ is *not* geometric (and does not even have contiguous support — it places zero mass on intermediate integers, exhibiting "gaps" analogous to the discrete-time Poisson channel). Determining whether $P_R^*$ has finite support (as opposed to infinite discrete support with gaps) for every $p \in (0, 1)$ remains open.

## What is known

- **Single-run characterization (Mitzenmacher, 2008):** Proved $C_{\mathrm{dup}}(p) = \sup_{P_R} I(R; S)/\mathbb{E}[R]$ and derived tight numerical lower and upper bounds using finite-support run-length distributions and duality.
- **Analytical upper bounds (Cheraghchi, 2019; Kovačević, 2020):** Cheraghchi derived general capacity upper bounds for sticky/duplication channels via convex duality; Kovačević studied exact properties and dominance criteria for $q$-ary sticky channels.
- **High-duplication asymptotics ($p \to 1^-$) and small-$p$ regime ($p \to 0^+$):** Asymptotic expansions have been analyzed by Mitzenmacher (2008), Mercier–Tarokh–Labeau, and Kirshner–Farnoud (2020), who also studied capacity bounds for general noisy duplication channels motivated by DNA storage.
- **Finite-support optimality:** Numerical computations over truncated alphabets $\{1, \dots, M\}$ show rapidly decaying or vanishing mass at large run lengths for small-to-moderate $p$, but whether the exact optimizer $P_R^*$ has finite support for every $p \in (0, 1)$ remains open.

## References

- M. Mitzenmacher, "Capacity bounds for sticky channels," *IEEE Trans. Inf. Theory*, 54(1):72–77, 2008.
- M. Cheraghchi, "Capacity upper bounds for deletion-type channels," *J. ACM*, 66(2):Article 9, 2019.
- N. Kirshner and F. Farnoud, "Capacity bounds for the noisy tandem duplication channel," *Proc. IEEE Int. Symp. Information Theory (ISIT)*, 2020.
- M. Kovačević, "Runlength-limited sequences and shift-correcting codes: Asymptotic analysis," *IEEE Trans. Inf. Theory*, 65(8):4804–4814, 2019.
- R. L. Dobrushin, "Shannon's theorems for channels with synchronization errors," *Problems of Information Transmission*, 3(4):11–26, 1967.
