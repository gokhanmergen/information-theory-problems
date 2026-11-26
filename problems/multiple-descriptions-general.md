---
id: multiple-descriptions-general
title: Rate-Distortion Region for General Two-Channel Multiple Descriptions
status: open
category: source-coding
posed_by: Abbas El Gamal and Thomas Cover (and Zhang–Berger)
posed_year: 1982
tags: [source-coding, multiple-descriptions, rate-distortion, zhang-berger]
lean_module: InfoTheory.Problems.MultipleDescriptionsGeneral
lean_file: lean/InfoTheory/Problems/MultipleDescriptionsGeneral.lean
---

## Statement

Consider a discrete memoryless source $X \sim P(x)$ over a finite alphabet $\mathcal{X}$
with three distortion measures $d_j : \mathcal{X} \times \hat{\mathcal{X}}_j \to \mathbb{R}_{\ge 0}$
($j \in \{0, 1, 2\}$). An encoder produces two descriptions $M_1 \in \{1, \dots, 2^{n R_1}\}$
and $M_2 \in \{1, \dots, 2^{n R_2}\}$; side decoder $1$ observes $M_1$ to meet distortion
$D_1$, side decoder $2$ observes $M_2$ to meet distortion $D_2$, and the central decoder
observes $(M_1, M_2)$ to meet distortion $D_0$.

Because Zhang and Berger (1987) proved that the original El Gamal–Cover (1982) inner bound
is strictly suboptimal for the binary symmetric source with Hamming distortion, the
sharpest known general single-letter inner bound for two descriptions is the
**Zhang–Berger inner bound** (1987; El Gamal–Kim 2011, Theorem 13.4): the closed convex
hull of all 5-tuples $(R_1, R_2, D_0, D_1, D_2)$ admitting a finite-alphabet common
auxiliary $U_0$ and joint distribution $p(x, u_0, \hat{x}_0, \hat{x}_1, \hat{x}_2)$ with
$X$-marginal $P$, $\mathbb{E}[d_j(X, \hat{X}_j)] \le D_j$ ($j = 0, 1, 2$), and:
$$
\begin{aligned}
R_1 &\ge I(X; U_0, \hat{X}_1), \\
R_2 &\ge I(X; U_0, \hat{X}_2), \\
R_1 + R_2 &\ge 2 I(X; U_0) + I(X; \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid U_0)
  + I(\hat{X}_1; \hat{X}_2 \mid U_0).
\end{aligned}
$$

**Does the closed convex hull of the Zhang–Berger inner bound equal the exact operational
rate-distortion region for every finite-alphabet two-channel multiple descriptions problem?**

## Background

Posed at the 1979 IEEE Information Theory Workshop (motivated by packet-switched networks
and diversity communication over unreliable links), the multiple descriptions problem asks
how to split a source into two individually useful descriptions that combine synergistically
when both arrive. El Gamal and Cover (1982) gave a single-letter inner bound that Ozarow
(1980) proved tight for the quadratic Gaussian source. In a landmark 1987 paper, Zhang and
Berger showed that adding a shared base layer $U_0$ decoded by all three receivers strictly
enlarges the El Gamal–Cover region for the binary symmetric source with Hamming distortion.
Whether the Zhang–Berger inner bound itself is universally tight for all two-description
discrete memoryless sources remains open nearly forty years later.

## What is known

- **Quadratic Gaussian two-description source**: completely solved by Ozarow (1980), where
  even the El Gamal–Cover inner bound (without $U_0$) is tight.
- **No-excess-rate-sum regime** ($R_1 + R_2 = R(D_0)$): Ahlswede (1985) and Zhang–Berger
  (1987) characterized the exact region in the no-excess-rate regime (where El Gamal–Cover
  is tight).
- **Suboptimality of El Gamal–Cover**: Zhang and Berger (1987) proved that El Gamal–Cover
  is strictly smaller than the achievable region for the binary symmetric source with
  Hamming distortion in the excess-rate regime, motivating the common auxiliary $U_0$.
- **Successive refinement / one-sided special cases**: solved by Equitz–Cover (1991) and
  Rimoldi (1994).
- **Binary symmetric source with Hamming distortion**: even for this simplest discrete
  instance, the exact rate-distortion region in the general excess-rate regime remains
  open (Fu–Yeung 2002; Zhang–Berger 1987).
- **Three or more descriptions ($L \ge 3$)**: Venkataramani–Kramer–Goyal (2003) extended
  Zhang–Berger to combinatorial layers, and Tian–Chen (2009) showed that structured lattice
  coding can strictly beat random-codebook layering for $L \ge 3$; for $L = 2$, no scheme
  is known to outperform Zhang–Berger.

## References

- L. H. Ozarow, "On a source-coding problem with two channels and three receivers," *Bell
  Syst. Tech. J.*, vol. 59, no. 10, pp. 1909–1921, 1980.
- A. El Gamal and T. M. Cover, "Achievable rates for multiple descriptions," *IEEE Trans.
  Inf. Theory*, vol. 28, no. 6, pp. 851–857, 1982.
- R. Ahlswede, "The rate-distortion region for multiple descriptions without excess rate,"
  *IEEE Trans. Inf. Theory*, vol. 31, no. 6, pp. 721–726, 1985.
- Z. Zhang and T. Berger, "New results in binary multiple descriptions," *IEEE Trans. Inf.
  Theory*, vol. 33, no. 4, pp. 502–521, 1987.
- R. Venkataramani, G. Kramer, and V. K. Goyal, "Multiple description coding with many
  channels," *IEEE Trans. Inf. Theory*, vol. 49, no. 9, pp. 2106–2114, 2003.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 13.
