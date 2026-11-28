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
formal_status: claimed-resolved
formal_status_note: "Huang–Liu–Liu arXiv:2608.19869 claim Marton (with W) is suboptimal; unrefereed; one-letter bound (25) independently certified, gradient-shaping theorems unchecked"
---

## Statement

Consider a two-receiver discrete memoryless broadcast channel
$(\mathcal{X}, p(y_1, y_2 \mid x), \mathcal{Y}_1 \times \mathcal{Y}_2)$ with one common
message $M_0 \in \{1, \dots, 2^{n R_0}\}$ intended for both receivers and two independent
private messages $M_1 \in \{1, \dots, 2^{n R_1}\}$ and $M_2 \in \{1, \dots, 2^{n R_2}\}$
intended for receivers $1$ and $2$, respectively.

Marton's inner bound with a common message (Marton 1979; Liang–Kramer 2007; El Gamal–Kim
2011, Theorem 8.4) is the set $\mathcal{R}_{\mathrm{M}}(W)$ of nonnegative rate triples
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
  of $\mathcal{R}_{\mathrm{M}}(W)$ onto $R_0 = 0$, and the common auxiliary $U_0$ is
  essential even for private messages: Gohari, El Gamal, and Anantharam (2014) show that
  Marton's scheme without it is suboptimal even for some degraded broadcast channels.
- Gohari and Anantharam (2012) proved finite cardinality bounds on $(U_0, U_1, U_2)$ for
  evaluating $\mathcal{R}_{\mathrm{M}}(W)$, and showed that deterministic mappings
  $X = f(U_0, U_1, U_2)$ suffice on the boundary.
- The Nair–El Gamal (2007) UV outer bound strictly exceeds Marton's inner bound on the
  binary skew-symmetric broadcast channel (Nair–Wang–Geng 2010). Gohari–Nair (2022)
  introduced auxiliary-receiver outer bounds that strictly tighten UV, with examples on the
  erasure Blackwell and product channels. On the BSSC, later auxiliary-receiver bounds,
  Geng (ISIT 2025) and Gohari–Liu–Nair (manuscript), narrow the sum-rate window. It is now
  certified as $[0.361642884, 0.369297201]$ bits (see the `binary-skew-symmetric-bc` attempt
  log); a positive gap remains.
- **Claimed counterexample (2026).** Huang, Liu, and Liu ("Sub-optimality of Marton's inner
  bound for the two-receiver broadcast channel", arXiv:2608.19869, Aug. 2026; not yet peer
  reviewed) claim a finite two-receiver DMBC $\tilde T$ whose two-letter Marton sum-rate
  strictly exceeds twice its one-letter Marton sum-rate (with the common auxiliary $W$).
  Hence the one-letter Marton region, with or without a common message, would be strictly
  inside the capacity region.
  - The construction starts from a ternary-input base channel with a certified fixed-input
    two-letter gain of about $3\times10^{-6}$ nats.
  - "Gradient shaping" and "constraint removal" then turn it into an unconstrained channel
    with input alphabet $\{0,1,2\}\times[2^{2\cdot 10^6}]$.
  - The numerics are certified with exact rationals and outward-rounded MPFR. The
    acknowledgments state that Nair and Gohari checked the non-numerical arguments.
  - An independent re-computation of the base-channel numbers is in the attempt log.
  - **Independent certificate (2026-11-27).** HLL's global one-letter bound (25) is now
    certified by a separate interval branch-and-bound that shares no numerical code with HLL.
    It uses exact integers plus Arb, and its reduction is the Anantharam–Gohari–Nair 2019
    Thm 3. The bound is sharpened to $\max G_T < G_T(19) + 10^{-12}$, so the fixed-input gain is
    $\ge 3.83\times10^{-6}$ nats. The certificate was re-run and adversarially reviewed.
    Still unchecked independently: HLL's Thms 2 and 4 (gradient shaping, constraint removal)
    and the lifted explicit instance. See
    `attempts/marton-inner-bound-tightness/2026-11-27-claude-opus-5-5-independent-certificate.md`.
- **Consequence for this entry.** If the claim is correct, the answer to the question above
  is **no**, and the frozen Lean `Statement` is false. The binary-input case remains open:
  Huang–Liu–Liu note that counterexamples appear to require non-binary inputs.
- Before this, the classical suboptimality example was for three receivers: Nair and
  El Gamal (2009) proved that naive superposition is suboptimal even with degraded message
  sets.

## References

- K. Marton, "A coding theorem for the discrete memoryless broadcast channel," *IEEE Trans.
  Inf. Theory*, vol. 25, no. 3, pp. 306–311, 1979.
- S. I. Gel'fand and M. S. Pinsker, "Capacity of a broadcast channel with one deterministic
  component," *Probl. Inf. Transm.*, vol. 16, no. 1, pp. 17–25, 1980.
- Y. Liang and G. Kramer, "Rate regions for relay broadcast channels," *IEEE Trans. Inf.
  Theory*, vol. 53, no. 10, pp. 3517–3535, 2007.
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the broadcast channel,"
  *IEEE Trans. Inf. Theory*, vol. 53, no. 1, pp. 350–355, 2007.
- A. Gohari, A. El Gamal, and V. Anantharam, "On Marton's inner bound for the general
  broadcast channel," *IEEE Trans. Inf. Theory*, vol. 60, no. 7, pp. 3748–3762, 2014.
- A. A. Gohari and V. Anantharam, "Evaluation of Marton's inner bound for the general
  broadcast channel," *IEEE Trans. Inf. Theory*, vol. 58, no. 2, pp. 608–619, 2012.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Theorem 8.4 (Marton's inner bound with a common message; Theorem 8.3 is the private-message
  version).
- Y. Liang, G. Kramer, and H. V. Poor, "On the equivalence of two achievable regions for the
  broadcast channel," *IEEE Trans. Inf. Theory*, vol. 57, no. 1, pp. 95–100, 2011.
- Y. Geng, "A simple auxiliary receiver outer bound for broadcast channels," *IEEE Int. Symp.
  Inf. Theory (ISIT)*, 2025.
- M. Huang, Y. Liu, and Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869, 2026.
