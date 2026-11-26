---
id: sbm-multi-community-threshold
title: Exact Information-Theoretic Weak Recovery Threshold for the q-Community Stochastic Block Model (q ≥ 5)
status: open
category: statistical-info-theory
posed_by: Aurelien Decelle, Florent Krzakala, Cristopher Moore, and Lenka Zdeborová
posed_year: 2011
tags: [stochastic-block-model, community-detection, phase-transitions, kesten-stigum]
lean_module: InfoTheory.Problems.SbmMultiCommunityThreshold
lean_file: lean/InfoTheory/Problems/SbmMultiCommunityThreshold.lean
---

## Statement

In the sparse symmetric $q$-community **Stochastic Block Model** $\mathrm{SBM}(n, q, a/n, b/n)$ (with $a > b > 0$ in the assortative regime), each vertex $v \in \{1, \dots, n\}$ is assigned an independent uniform community label $\sigma_v \in \{1, \dots, q\}$, and each unordered pair $\{u, v\}$ is connected by an edge independently with probability $a/n$ if $\sigma_u = \sigma_v$ and $b/n$ if $\sigma_u \ne \sigma_v$. The average degree is $d = \frac{a + (q - 1)b}{q}$ and the Kesten–Stigum signal-to-noise ratio is $\mathrm{SNR} = \frac{(a - b)^2}{q(a + (q-1)b)}$.

- **Weak recovery** is achievable if there exists $\delta > 0$ and a sequence of estimators $\hat{\sigma}_n(G)$ achieving strictly better-than-random overlap up to community relabeling:
  $$
  \liminf_{n \to \infty} \mathbb{E}\!\left[ \max_{\pi \in S_q} \frac{1}{n} \sum_{v=1}^n \mathbf{1}\{\hat{\sigma}_n(G)_v = \pi(\sigma_v)\} \right] \ge \frac{1}{q} + \delta.
  $$
- **Strong distinguishability** from the Erdős–Rényi null model $G(n, d/n)$ holds if $\lim_{n \to \infty} \mathrm{TV}\big(\mathrm{SBM}(n, q, a/n, b/n), G(n, d/n)\big) = 1$.

**Determine the exact information-theoretic weak recovery threshold for multi-community SBMs, and in particular (formalized in Lean) determine whether for $q = 4$ communities the Kesten–Stigum threshold $\mathrm{SNR} = \frac{(a - b)^2}{4(a + 3b)} = 1$ is tight across *all* assortative parameter pairs $a > b > 0$ (no weak recovery below Kesten–Stigum even at small average degree).**

## Background

Decelle, Krzakala, Moore, and Zdeborová (2011) used the cavity method of statistical physics to predict a rich phase diagram for sparse community detection: while polynomial-time algorithms should succeed down to the Kesten–Stigum (KS) threshold $\mathrm{SNR} = 1$, for $q \ge 5$ communities a **first-order phase transition** creates an information-theoretic–to–computational gap in which exponential-time weak recovery becomes possible strictly *below* the KS threshold.

This prediction catalyzed an enormous body of work in probability, statistical physics, and information theory, confirming the existence of the hard regime for $q \ge 5$ — yet pinning down the exact sharp threshold and proving equivalence between weak recovery and distinguishability across all sparse assortative $(q, a, b)$ for $q \ge 5$ remains open.

## What is known

- **Above the Kesten–Stigum threshold ($\mathrm{SNR} > 1$):** Efficient polynomial-time weak recovery is possible for all $q \ge 2$ (Massoulié 2014; Mossel–Neeman–Sly 2018; Bordenave–Lelarge–Massoulié 2015; Abbe–Sandon 2015, 2018).
- **$q = 2$ (complete resolution):** Mossel, Neeman, and Sly (2015) proved that $\mathrm{SNR} = 1$ is the exact information-theoretic weak recovery and distinguishability threshold (with mutual contiguity to $G(n, d/n)$ for all $\mathrm{SNR} < 1$).
- **Equivalence of weak recovery and distinguishability (Mossel–Sly–Sohn, STOC 2025, arXiv:2406.15957):** Proved that weak recovery and strong distinguishability share the exact same threshold away from the critical point, resolving the intermediate-phase question.
- **$q = 3, 4$ (Kesten–Stigum tightness):** Mossel, Sly, and Sohn (2023) proved tightness of the Kesten–Stigum threshold for $q = 3, 4$ in the sufficiently large average-degree regime, while tightness for $q = 4$ across *all* assortative degrees $a > b > 0$ remains open.
- **$q \ge 5$ (below Kesten–Stigum):**
  - Abbe and Sandon (2016) and Banks, Moore, Neeman, and Netrapalli (2016) rigorously proved that weak recovery IS possible strictly below the KS threshold for all $q \ge 5$, establishing the asymptotic scaling $\mathrm{SNR}_{\mathrm{IT}}(q) = \Theta\!\left(\frac{\log q}{q}\right)$ as $q \to \infty$.
  - Determining the exact closed-form / variational weak recovery threshold $d^*(q)$ for sparse assortative ($a > b$) SBMs with $q \ge 5$ remains open.

## References

- A. Decelle, F. Krzakala, C. Moore, and L. Zdeborová, "Asymptotic analysis of the stochastic block model for modular networks and its algorithmic applications," *Phys. Rev. E* **84**, 066106 (2011).
- E. Mossel, J. Neeman, and A. Sly, "Reconstruction and estimation in the planted partition model," *Probab. Theory Relat. Fields* **162**, 431–461 (2015).
- E. Abbe and C. Sandon, "Detection in the stochastic block model with multiple clusters: Proof of the achievability conjectures, acyclic BP, and the information-computation gap," *arXiv:1512.09080* (2015); *NeurIPS* (2016).
- J. Banks, C. Moore, J. Neeman, and P. Netrapalli, "Information-theoretic thresholds for community detection in sparse networks," *Proc. 29th COLT*, PMLR **49**, 383–416 (2016).
- A. Coja-Oghlan, F. Krzakala, W. Perkins, and L. Zdeborová, "Information-theoretic thresholds from the cavity method," *Adv. Math.* **333**, 694–795 (2018).
- E. Abbe, "Community detection and stochastic block models: Recent developments," *J. Mach. Learn. Res.* **18**(177), 1–86 (2018).
- E. Mossel, A. Sly, and Y. Sohn, "Exact phase transitions for stochastic block models and reconstruction on trees," *Proc. 55th ACM STOC* (2023).
