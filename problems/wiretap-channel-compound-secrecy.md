---
id: wiretap-channel-compound-secrecy
title: Single-Letter Secrecy Capacity of the Compound Discrete Memoryless Wiretap Channel
status: open
category: security-privacy
posed_by: Yingbin Liang, Gerhard Kramer, H. Vincent Poor, and Shlomo Shamai (Shitz)
posed_year: 2009
tags: [information-theoretic-security, wiretap-channel, compound-channel, single-letterization]
lean_module: InfoTheory.Problems.WiretapChannelCompoundSecrecy
lean_file: lean/InfoTheory/Problems/WiretapChannelCompoundSecrecy.lean
---

## Statement

A finite-state **compound discrete memoryless wiretap channel** is a finite family $\{W_s(y, z \mid x)\}_{s \in \mathcal{S}}$ of discrete memoryless wiretap channels sharing common finite alphabets $\mathcal{X}, \mathcal{Y}, \mathcal{Z}$. The transmitter and legitimate receiver do not know which state $s \in \mathcal{S}$ governs the channel and must simultaneously achieve vanishing decoding error and vanishing information leakage $\max_{s \in \mathcal{S}} \frac{1}{n} I(M; Z_s^n) \to 0$ across every state $s \in \mathcal{S}$.

Bjelaković, Boche, and Sommerfeld (2013) established the multi-letter regularized secrecy capacity formula
$$
C_s(\{W_s\}) = \sup_{n \ge 1} \frac{1}{n} \sup_{V - X^n - (Y_s^n, Z_s^n)} \Big( \min_{s \in \mathcal{S}} I(V; Y_s^n) - \max_{s \in \mathcal{S}} I(V; Z_s^n) \Big).
$$
Meanwhile, Liang, Kramer, Poor, and Shamai (2009) established the single-letter inner bound
$$
R_{\mathrm{LKPS}}(\{W_s\}) = \sup_{U - V - X - (Y_s, Z_s)} \Big( \min_{s \in \mathcal{S}} I(V; Y_s \mid U) - \max_{s \in \mathcal{S}} I(V; Z_s \mid U) \Big).
$$

**Determine a single-letter characterization of $C_s(\{W_s\})$ for general finite-state compound DM wiretap channels — and specifically determine whether the single-letter inner bound $R_{\mathrm{LKPS}}(\{W_s\})$ equals the multi-letter compound secrecy capacity $C_s(\{W_s\})$ for all finite-state compound DM wiretap channels.**

## Background

For a single-state discrete memoryless wiretap channel ($|\mathcal{S}| = 1$), Csiszár and Körner (1978) proved the celebrated single-letter formula $C_s(W) = \max_{V - X - YZ} [I(V; Y) - I(V; Z)]$. For an ordinary (non-wiretap) compound DMC $\{W_s\}_{s \in \mathcal{S}}$, Blackwell, Breiman, and Thomasian (1959) likewise obtained the single-letter capacity $\max_{P_X} \min_{s} I(X; Y_s)$.

When secrecy and channel uncertainty are combined, however, the standard Csiszár–Körner telescoping identity breaks down because the minimizing legitimate-receiver state $s_1$ and maximizing eavesdropper state $s_2$ can differ and can vary across coordinates $i \in \{1, \dots, n\}$. As a result, single-letterizing the compound wiretap secrecy capacity has remained open for over fifteen years.

## What is known

- **Multi-letter characterization:** Bjelaković, Boche, and Sommerfeld (2013) proved that the regularized formula $\lim_{n \to \infty} \frac{1}{n} \sup_{V - X^n} [\min_s I(V; Y_s^n) - \max_s I(V; Z_s^n)]$ equals the compound secrecy capacity under both weak and strong secrecy for general finite-state (and arbitrary) compound DM wiretap channels.
- **Single-letter inner bound:** Liang, Kramer, Poor, and Shamai (2009) proved achievability of $R_{\mathrm{LKPS}}(\{W_s\})$ and established tightness for degraded compound wiretap channels (where every eavesdropper channel is degraded with respect to every legitimate channel, or under certain stochastic-degradation orderings), as well as for parallel and Gaussian degraded compound wiretap channels.
- **Tightness for special structured classes:** Khisti (2011) and Schaefer (Wyrembelski) and Boche (2013) obtained exact single-letter capacities for MIMO Gaussian and certain symmetric/semi-deterministic compound wiretap channels.
- **General finite-state DM case remains open:** Even for $|\mathcal{S}| = 2$ non-degraded binary-input wiretap channels, it is unknown whether $R_{\mathrm{LKPS}}(\{W_s\}) = C_s(\{W_s\})$ always holds or whether multi-letter prefix coding is strictly necessary.

## References

- I. Csiszár and J. Körner, "Broadcast channels with confidential messages," *IEEE Trans. Inf. Theory* **24**(3), 339–348 (1978).
- Y. Liang, G. Kramer, H. V. Poor, and S. Shamai (Shitz), "Compound wiretap channels," *EURASIP J. Wireless Commun. Netw.*, Article ID 142374 (2009).
- A. Khisti, "Interference alignment for the multiantenna compound wiretap channel," *IEEE Trans. Inf. Theory* **57**(5), 2976–2993 (2011).
- I. Bjelaković, H. Boche, and J. Sommerfeld, "Secrecy results for compound wiretap channels," *Probl. Inf. Transm.* **49**(1), 73–98 (2013).
- R. F. Wyrembelski and H. Boche, "Strong secrecy in compound broadcast channels with confidential messages," *IEEE Trans. Inf. Theory* **59**(4), 2059–2071 (2013).
