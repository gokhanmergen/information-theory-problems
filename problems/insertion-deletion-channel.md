---
id: insertion-deletion-channel
title: Capacity and Convexity of the Binary Insertion–Deletion Channel
status: open
category: channel-capacity
posed_by: Robert G. Gallager; Michael Mitzenmacher
posed_year: 1961
tags: [channel-capacity, synchronization, insertion-deletion, convexity]
lean_module: InfoTheory.Problems.InsertionDeletionChannel
lean_file: lean/InfoTheory/Problems/InsertionDeletionChannel.lean
---

## Statement

Consider Gallager's (1961) memoryless binary insertion–deletion channel $\mathsf{IDS}(p_d, p_i)$ parameterized by $(p_d, p_i)$ in the simplex $\Delta = \{(p_d, p_i) \in \mathbb{R}_{\ge 0}^2 : p_d + p_i \le 1\}$. Each input bit $x_j \in \{0, 1\}$ is processed independently:
- with probability $p_d$, the bit is deleted (producing the empty string);
- with probability $1 - p_d - p_i$, the bit is transmitted unchanged (producing $x_j$);
- with probability $p_i$, the bit is replaced by two independent uniform random bits (each of the four pairs in $\{0, 1\}^2$ occurring with probability $p_i / 4$).

The output is the concatenation of all surviving/inserted strings with no position markers. By Dobrushin's (1967) coding theorem for synchronization channels, the Shannon capacity exists and equals
$$C_{\mathrm{IDS}}(p_d, p_i) = \lim_{n \to \infty} \frac{1}{n} \max_{P_{X^n}} I(X^n; Y) = \sup_{n \ge 1} \frac{1}{n} \max_{P_{X^n}} I(X^n; Y).$$

**Conjecture (Joint Convexity of the Insertion–Deletion Capacity).** The capacity function $(p_d, p_i) \mapsto C_{\mathrm{IDS}}(p_d, p_i)$ is jointly convex on the parameter simplex $\Delta$: for all $(p_d, p_i), (q_d, q_i) \in \Delta$ and $\lambda \in [0, 1]$,
$$C_{\mathrm{IDS}}\big(\lambda p_d + (1-\lambda) q_d,\; \lambda p_i + (1-\lambda) q_i\big) \;\le\; \lambda\, C_{\mathrm{IDS}}(p_d, p_i) + (1-\lambda)\, C_{\mathrm{IDS}}(q_d, q_i).$$

In particular, setting $p_i = q_i = 0$ yields the famous open conjecture that the binary deletion channel capacity $d \mapsto C(d)$ is convex on $[0, 1]$.

## Background

Gallager introduced the binary insertion–deletion channel in 1961 alongside sequential decoding methods for synchronization errors. Like the pure binary deletion channel ($p_i = 0$), its exact capacity $C_{\mathrm{IDS}}(p_d, p_i)$ is unknown at every interior point $(p_d, p_i)$ with $p_d + p_i > 0$ and $p_d + p_i < 1$. Because the channel destroys symbol alignment without side information, the mutual information per symbol does not single-letterize.

Beyond determining exact capacity values, even the basic global **convexity** of $C_{\mathrm{IDS}}(p_d, p_i)$ — and even of the one-parameter deletion capacity $C(d)$ — remains an open structural problem (highlighted by Mitzenmacher 2009 and Dalai 2011). Convexity is mathematically natural (the capacity of any DMC is convex in the transition matrix, and $C(d)$ is strictly convex near $d = 0$ since $C''(d) \sim \frac{1}{d\ln 2} > 0$), yet the synchronization memory breaks the standard symbol-by-symbol convexity proof. Proving convexity would immediately tighten upper bounds across all intermediate parameters via chord interpolation between known endpoint asymptotics and numerical bounds.

## What is known

- **Existence of capacity (Dobrushin, 1967):** Capacity equals $\lim_{n \to \infty} \frac{1}{n} \max_{P_{X^n}} I(X^n; Y)$ and is achieved by stationary ergodic inputs.
- **Lower bounds (Gallager, 1961; Davey–MacKay, 2001; Mitzenmacher–Drinea, 2006; Rahmati–Duman, 2015):** Gallager derived the classical lower bound $C_{\mathrm{IDS}}(p_d, p_i) \ge 1 - h(p_d, p_i, 1 - p_d - p_i)$ for small error rates; subsequent Markov/renewal input optimizations (Kirsch–Drinea; Rahmati–Duman) substantially improved achievable rates across the parameter simplex.
- **Upper bounds (Fertonani–Duman, 2010; Dalai, 2011; Rahmati–Duman, 2015; Cheraghchi, 2019):** Genie-aided decoders (revealing synchronization markers at periodic intervals) and convex-duality / mean-limited channel upper bounds (Cheraghchi 2019) yield the sharpest known upper bounds on $C_{\mathrm{IDS}}(p_d, p_i)$, though substantial gaps to lower bounds remain at moderate $p_d, p_i$.
- **Sub-multiplicativity for deletions (Dalai, 2011):** For $p_i = 0$, composing two deletion channels shows $C(d_1 + d_2 - d_1 d_2) \le (1 - d_1) C(d_2)$, which implies $d \mapsto C(d)/(1 - d)$ is non-increasing, consistent with convexity, while global convexity itself remains open.

## References

- R. G. Gallager, "Sequential decoding for binary channels with noise and synchronization errors," *MIT Lincoln Lab. Group Report*, 1961.
- R. L. Dobrushin, "Shannon's theorems for channels with synchronization errors," *Problems of Information Transmission*, 3(4):11–26, 1967.
- M. Mitzenmacher, "A survey of results for deletion channels and related synchronization channels," *Probability Surveys*, 6:1–33, 2009.
- D. Fertonani and T. M. Duman, "Novel bounds on the capacity of the binary deletion channel," *IEEE Trans. Inf. Theory*, 56(6):2753–2765, 2010.
- M. Dalai, "A new bound on the capacity of the binary deletion channel with high deletion probabilities," *Proc. IEEE ISIT*, pp. 499–502, 2011.
- M. Rahmati and T. M. Duman, "Upper bounds on the capacity of deletion channels using channel fragmentation," *IEEE Trans. Inf. Theory*, 61(1):146–156, 2015.
- M. Cheraghchi, "Capacity upper bounds for deletion-type channels," *J. ACM*, 66(2):Article 9, 2019.
