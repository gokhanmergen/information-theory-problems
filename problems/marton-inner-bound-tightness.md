---
id: marton-inner-bound-tightness
title: Tightness of Marton's Inner Bound with a Common Message
status: open
category: network-info-theory
posed_by: Katalin Marton
posed_year: 1979
tags: [network-information-theory, broadcast-channel, marton-inner-bound, multiuser]
lean_module: InfoTheory.Problems.MartonInnerBoundTightness
lean_file: lean/InfoTheory/Problems/MartonInnerBoundTightness.lean
---

## Statement

Consider a two-receiver discrete memoryless broadcast channel
$(\mathcal{X}, p(y_1, y_2 \mid x), \mathcal{Y}_1 \times \mathcal{Y}_2)$ with one common
message $M_0 \in \{1, \dots, 2^{n R_0}\}$ intended for both receivers and two independent
private messages $M_1 \in \{1, \dots, 2^{n R_1}\}$ and $M_2 \in \{1, \dots, 2^{n R_2}\}$
intended for receivers $1$ and $2$, respectively.

Marton's inner bound with a common message (Marton 1979; Liang–Kramer 2007; El Gamal–Kim
2011, Theorem 8.3) is the set $\mathcal{R}_{\mathrm{M}}(W)$ of nonnegative rate triples
$(R_0, R_1, R_2)$ for which there exist finite-alphabet auxiliary random variables
$(U_0, U_1, U_2)$ jointly distributed with $X$ such that $(U_0, U_1, U_2) - X - (Y_1, Y_2)$
and:
$$
\begin{aligned}
R_0 + R_1 &\le I(U_0, U_1; Y_1), \\
R_0 + R_2 &\le I(U_0, U_2; Y_2), \\
R_0 + R_1 + R_2 &\le I(U_0, U_1; Y_1) + I(U_2; Y_2 \mid U_0) - I(U_1; U_2 \mid U_0), \\
R_0 + R_1 + R_2 &\le I(U_1; Y_1 \mid U_0) + I(U_0, U_2; Y_2) - I(U_1; U_2 \mid U_0), \\
2 R_0 + R_1 + R_2 &\le I(U_0, U_1; Y_1) + I(U_0, U_2; Y_2) - I(U_1; U_2 \mid U_0).
\end{aligned}
$$

**Does $\mathcal{R}_{\mathrm{M}}(W)$ equal the full common-and-private-message capacity
region $\mathcal{C}_{\mathrm{com}}(W)$ for every finite-alphabet two-receiver discrete
memoryless broadcast channel $W$?**

## Background

Marton's 1979 coding theorem introduced correlated auxiliary codebooks (multicoding /
Gel'fand–Pinsker binning) to the broadcast channel, yielding the largest known single-letter
achievable region for general two-receiver discrete memoryless broadcast channels. When a
common message $M_0$ is present alongside private messages $(M_1, M_2)$, rate-splitting of
$M_0$ across the cloud center $U_0$ and the satellites $(U_1, U_2)$ produces the five-inequality
region above (Gelfand–Pinsker 1980; Liang–Kramer 2007). Determining whether Marton's inner
bound is universally tight — or finding a single counterexample channel where multi-letter
coding beats it — is one of the central unresolved questions of multiuser information theory.

## What is known

- Marton's inner bound with a common message is tight for every class of two-receiver
  broadcast channels whose capacity region is known, including degraded, less-noisy,
  more-capable, deterministic (Marton 1979; Pinsker 1978), semi-deterministic (Gel'fand–Pinsker
  1980), product of reversely degraded, and Gaussian MIMO broadcast channels
  (Weingarten–Steinberg–Shamai 2006).
- With private messages only ($R_0 = 0$), Marton's region coincides with the projection
  of $\mathcal{R}_{\mathrm{M}}(W)$ onto $R_0 = 0$, though the common auxiliary $U_0$ is
  essential even for private messages on non-binary channels.
- Gohari and Anantharam (2012) proved finite cardinality bounds on $(U_0, U_1, U_2)$ for
  evaluating $\mathcal{R}_{\mathrm{M}}(W)$, and showed that deterministic mappings
  $X = f(U_0, U_1, U_2)$ suffice on the boundary.
- The Nair–El Gamal (2007) UV outer bound strictly exceeds Marton's inner bound on the
  binary skew-symmetric broadcast channel (Nair–Wang–Geng 2010), and Gohari–Nair (2022)
  introduced an auxiliary-receiver outer bound that strictly tightens the UV bound; however,
  a positive gap between inner and outer bounds remains.
- Unlike the three-receiver case — where Nair and El Gamal (2009) proved that naive
  superposition is suboptimal even with degraded message sets — no counterexample to
  Marton's inner bound is known for any two-receiver DMBC.

## References

- K. Marton, "A coding theorem for the discrete memoryless broadcast channel," *IEEE Trans.
  Inf. Theory*, vol. 25, no. 3, pp. 306–311, 1979.
- S. I. Gel'fand and M. S. Pinsker, "Capacity of a broadcast channel with one deterministic
  component," *Probl. Inf. Transm.*, vol. 16, no. 1, pp. 17–25, 1980.
- Y. Liang and G. Kramer, "Rate regions for relay broadcast channels," *IEEE Trans. Inf.
  Theory*, vol. 53, no. 10, pp. 3517–3535, 2007.
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the broadcast channel,"
  *IEEE Trans. Inf. Theory*, vol. 53, no. 1, pp. 401–405, 2007.
- A. A. Gohari and V. Anantharam, "Evaluation of Marton's inner bound for the general
  broadcast channel," *IEEE Trans. Inf. Theory*, vol. 58, no. 2, pp. 608–619, 2012.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Theorem 8.3.
