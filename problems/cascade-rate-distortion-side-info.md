---
id: cascade-rate-distortion-side-info
title: Cascade Rate-Distortion with Side Information at the Intermediate Node
status: open
category: source-coding
posed_by: Dinkar Vasudevan, Chao Tian, Suhas Diggavi; Paul Cuff, Han-I Su, Abbas El Gamal
posed_year: 2006
tags: [source-coding, rate-distortion, multiterminal, side-information]
lean_module: InfoTheory.Problems.CascadeRateDistortionSideInfo
lean_file: lean/InfoTheory/Problems/CascadeRateDistortionSideInfo.lean
---

## Statement

Consider a three-node cascade lossy source coding network for a discrete memoryless source
$(X_i, Y_i)_{i=1}^n \stackrel{\text{i.i.d.}}{\sim} P_{X,Y}$ over finite alphabets
$\mathcal{X} \times \mathcal{Y}$, with a single-letter distortion measure
$d : \mathcal{X} \times \hat{\mathcal{X}} \to \mathbb{R}_{\ge 0}$ and distortion threshold $D$:

- **Node 1** observes $X^n$ and sends a message $M_1 \in \{1, \dots, \lfloor 2^{n R_1} \rfloor\}$
  to Node 2.
- **Node 2** observes $(M_1, Y^n)$ and sends a message
  $M_2 \in \{1, \dots, \lfloor 2^{n R_2} \rfloor\}$ to Node 3.
- **Node 3** observes $M_2$ (with no side information) and produces a reconstruction $\hat{X}^n$
  satisfying $\frac{1}{n} \sum_{i=1}^n \mathbb{E}[d(X_i, \hat{X}_i)] \le D$.

A natural single-letter outer bound (Cuff–Su–El Gamal 2009) consists of all rate pairs
$(R_1, R_2)$ for which there exist a finite auxiliary random variable $U$ and reconstruction
$\hat{X}$ satisfying the Markov chains $U - X - Y$ and $X - (U, Y) - \hat{X}$, average
distortion $\mathbb{E}[d(X, \hat{X})] \le D$, and
$$R_1 \ge I(X; U \mid Y), \qquad R_2 \ge I(X, Y; \hat{X}) .$$

**Determine whether this single-letter outer bound is tight for all finite-alphabet discrete
memoryless sources and distortion measures** — and more generally, find a computable
single-letter characterization of the cascade rate-distortion region with side information
at the intermediate node (and optionally non-degraded side information at the final decoder).

## Background

Yamamoto (1981) established the rate-distortion region for the three-node cascade network
without side information. Adding correlated side information $Y$ at the intermediate relay
node (Node 2) — as arises in sensor networks, distributed storage, and multihop compression —
fundamentally changes the problem because Node 1 cannot directly match its description to
the realization of $Y$. While Node 1 can use Wyner–Ziv binning to deliver an auxiliary
description $U$ to Node 2 at rate $I(X; U \mid Y)$, a naive decode-and-recompress strategy
at Node 2 requires rate $R_2 \ge I(U, Y; \hat{X})$, which can strictly exceed the outer-bound
term $I(X, Y; \hat{X})$. Closing the gap between achievable binning/forwarding schemes and
converse bounds remains a central open problem in multiterminal rate-distortion theory.

## What is known

- **No side information:** Yamamoto (1981) gave a complete single-letter characterization.
- **Quadratic Gaussian case:** Vasudevan, Tian, and Diggavi (2006) solved the quadratic
  Gaussian cascade source coding problem with side information at the intermediate node,
  showing that jointly Gaussian auxiliary variables suffice.
- **Side information at Node 1 and Node 2 / lossless reconstruction:** Cuff, Su, and
  El Gamal (2009) and Gu and Effros (2009) obtained single-letter characterizations when
  $Y$ is also available at the source encoder, when Node 3 requires lossless reconstruction,
  or in special degraded regimes.
- **Triangular and causal/non-causal extensions:** Permuter and Weissman (2012) and
  Chia, Kramer, Mahajan, and Weissman (2012) resolved additional special cases (including
  degraded side information at Node 3 and certain triangular topologies), but the general
  discrete memoryless lossy cascade with side information only at Node 2 remains open.

## References

- H. Yamamoto, "Source coding theory for cascade and branching communication systems,"
  IEEE Trans. Inf. Theory, 1981.
- D. Vasudevan, C. Tian, and S. N. Diggavi, "Lossy source coding for a cascade
  communication system with side-informations," Proc. Allerton Conf., 2006.
- P. Cuff, H.-I. Su, and A. El Gamal, "Cascade multiterminal source coding,"
  Proc. IEEE ISIT, 2009.
- W. Gu and M. Effros, "A strong conditional typicality lemma and its applications to
  cascade source coding," Proc. IEEE ISIT, 2009.
- H. H. Permuter and T. Weissman, "Cascade and triangular source coding with side
  information at the first two nodes," IEEE Trans. Inf. Theory, 2012.
- Y.-K. Chia, G. Kramer, A. Mahajan, and T. Weissman, "Cascade and triangular source
  coding with side information," IEEE Trans. Inf. Theory, 2012.
