---
id: binary-skew-symmetric-bc
title: Sum-Rate Capacity of the Binary Skew-Symmetric Broadcast Channel
status: open
category: network-info-theory
posed_by: Bruce Hajek and Michael Pursley
posed_year: 1979
tags: [network-information-theory, broadcast-channel, marton-inner-bound, bssc]
lean_module: InfoTheory.Problems.BinarySkewSymmetricBc
lean_file: lean/InfoTheory/Problems/BinarySkewSymmetricBc.lean
---

## Statement

The **binary skew-symmetric broadcast channel** (BSSC) is the two-receiver discrete
memoryless broadcast channel $W_{\mathrm{BSSC}}$ with binary input $X \in \{0, 1\}$ and
conditionally independent binary outputs $Y_1, Y_2 \in \{0, 1\}$ defined by two opposite
Z-channels with crossover probability $1/2$:
$$
p(y_1 \mid x) = \begin{cases}
\mathbf{1}[y_1 = 0] & x = 0, \\
1/2 & x = 1,
\end{cases}
\qquad
p(y_2 \mid x) = \begin{cases}
1/2 & x = 0, \\
\mathbf{1}[y_2 = 1] & x = 1.
\end{cases}
$$

Let $C_{\mathrm{sum}}(W_{\mathrm{BSSC}}) = \sup \{ R_1 + R_2 : (R_1, R_2) \in \mathcal{C}(W_{\mathrm{BSSC}}) \}$
denote its private-message sum-rate capacity, and let
$R_{\mathrm{M,sum}}(W_{\mathrm{BSSC}}) = \sup \{ R_1 + R_2 : (R_1, R_2) \in \mathcal{R}_{\mathrm{M}}(W_{\mathrm{BSSC}}) \}$
denote the maximum sum-rate in Marton's inner bound.

**Does $C_{\mathrm{sum}}(W_{\mathrm{BSSC}}) = R_{\mathrm{M,sum}}(W_{\mathrm{BSSC}})$?**

## Background

Introduced by Hajek and Pursley (1979) as the simplest two-receiver broadcast channel that
falls outside every known capacity-characterized class (it is neither degraded, nor less
noisy, nor more capable, nor semi-deterministic), the BSSC has become the benchmark testbed
for the entire broadcast channel problem. Remarkably, the BSSC is the canonical example on
which the best known general inner bound (Marton 1979) and the classical Nair–El Gamal
(2007) UV outer bound strictly separate, concentrating the 50-year broadcast channel
capacity problem into a concrete gap of about $0.01$ bits on a binary-input, binary-output
channel. Since Marton's inner bound is now claimed to be strictly suboptimal for some
non-binary-input channel (Huang–Liu–Liu 2026, below), the binary-input case, and the BSSC
in particular, is where the optimality question remains genuinely open.

## What is known

- The single-user capacity of each marginal Z-channel is
  $C_Z = \max_{p \in [0, 1]} (h(p/2) - p) = \log_2(5/4) \approx 0.321928$ bits.
- Nair, Wang, and Geng (2010; journal version Geng–Jog–Nair–Wang 2013) proved an
  information inequality establishing that for *every* binary-input broadcast channel, the
  sum-rate of Marton's inner bound is achieved by randomized time division (binary auxiliary
  variables). For the BSSC, this evaluates precisely to
  $R_{\mathrm{M,sum}}(W_{\mathrm{BSSC}}) \approx 0.3616428$ bits, strictly beating time
  sharing ($0.321928$ bits). An explicit randomized-time-division distribution certifies
  $R_{\mathrm{M,sum}} \ge 0.361642884$ with interval arithmetic (attempt log).
- The Nair–El Gamal (2007) UV outer bound evaluates on the BSSC to $\approx 0.3725562$ bits.
  Jog and Nair (2009) derived this value analytically, correcting an earlier $0.3711$; the
  attempt log re-checks it with interval arithmetic ($\le 0.372556252$). It leaves a gap of
  roughly $0.0109$ bits above Marton's sum-rate.
- Gohari and Nair (2022) introduced the auxiliary-receiver framework. Their paper's strict
  improvements over UV are for other channels (the erasure Blackwell corner point and product
  channels); it contains no BSSC evaluation.
- The first improvement on the BSSC came from Geng (ISIT 2025), using a one-auxiliary-receiver
  concave-envelope bound that, for each fixed auxiliary receiver $J$, is implied by
  Gohari–Nair's Theorem 7. As quoted by Gohari–Liu–Nair, Geng reported $\approx 0.369316568803963$ at
  $J = \mathrm{BSC}(0.18999)$.
- Gohari, Liu, and Nair (manuscript, 2025 or later) gave a two-auxiliary-receiver bound with a
  reported value of $\approx 0.369296340638082$.
- A rigorous re-evaluation (attempt log) shows that both reported values are about $10^{-6}$
  below their own formulas at the stated parameters. It also certifies
  $C_{\mathrm{sum}}(W_{\mathrm{BSSC}}) \le 0.369297201$ bits.
- The best certified window is therefore $[0.361642884,\ 0.369297201]$, a gap of about
  $0.0077$ bits.
- Huang, Liu, and Liu (arXiv:2608.19869, 2026; not yet peer reviewed) claim that Marton's
  inner bound is strictly suboptimal for some finite two-receiver DMBC. Their construction
  starts from a ternary-input base channel. They note that counterexamples appear to require
  a non-binary input, and they leave the binary-input case, including the BSSC, open.
- Their paper also recounts the following history. Numerical comparisons of two-letter and
  one-letter Marton bounds for binary-input broadcast channels, following Geng, Gohari, Nair,
  and Yu (ITA 2011) and run in 2011–2012, found no strict two-letter improvement. Nair (ITA
  2020) proved *local* tensorization at the product optimizer for product channels with a
  binary component. Anantharam, Gohari, and Nair (IEEE TIT 2019, Sec. II-C, Lemma 2, Remarks
  9–10) give the dual two-letter test for products of binary-input channels, with a
  $|U|+|V|\le5$ reduction. They report "rather exhaustive" searches on binary-input,
  binary-output channels that found no gain.
- **Two-letter bound (computer-assisted, 2026-11-27).** The two-letter Marton sum rate of
  the BSSC is $\le 0.36664$ bits/letter, below the outer bound 0.369297. So two-letter Marton
  cannot close the window, and any two-letter gain is at most about 0.005 bits/letter.
  - It follows from the dual criterion $B_{T\otimes T}(\tfrac12,0)\le 2B_T(\tfrac12,0)+0.01$,
    certified by a branch-and-bound over all 862 reduced problems.
  - The run is float64 with a $10^{-9}$ margin, not interval arithmetic, so it is labelled
    `[sketch]`.
  - Multistart search finds the two-letter maximum equal to the one-letter value to
    $10^{-15}$.
  - See `attempts/binary-skew-symmetric-bc/2026-11-27-claude-opus-5-5-binary-input-multiletter.md`.
- No published global multi-letter result for the BSSC is known to us. The exactness of
  $R_{\mathrm{M,sum}}(W_{\mathrm{BSSC}})$ is supported by this evidence but remains unproven.

## References

- B. E. Hajek and M. B. Pursley, "Evaluation of an achievable rate region for the broadcast
  channel," *IEEE Trans. Inf. Theory*, vol. 25, no. 1, pp. 36–46, 1979.
- K. Marton, "A coding theorem for the discrete memoryless broadcast channel," *IEEE Trans.
  Inf. Theory*, vol. 25, no. 3, pp. 306–311, 1979.
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the broadcast channel,"
  *IEEE Trans. Inf. Theory*, vol. 53, no. 1, pp. 350–355, 2007.
- C. Nair, Z. V. Wang, and Y. Geng, "An information inequality and evaluation of Marton's
  inner bound for binary input broadcast channels," *IEEE Int. Symp. Inf. Theory (ISIT)*,
  2010; arXiv:1001.1468.
- V. Jog and C. Nair, "An information inequality for the BSSC channel," *Information Theory
  and Applications Workshop (ITA)*, 2010; arXiv:0901.1492 (Sec. 3.2.1 evaluates the UV sum-rate).
- Y. Geng, V. Jog, C. Nair, and Z. V. Wang, "An information inequality and evaluation of
  Marton's inner bound for binary input broadcast channels," *IEEE Trans. Inf. Theory*,
  vol. 59, no. 7, pp. 4095–4105, 2013.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
- Y. Geng, "A simple auxiliary receiver outer bound for broadcast channels," *IEEE Int. Symp.
  Inf. Theory (ISIT)*, 2025.
- A. Gohari, Y. Liu, and C. Nair, "A two auxiliary receiver outer bound to the capacity
  region of a two-receiver discrete memoryless broadcast channel," manuscript
  (chandra.ie.cuhk.edu.hk/pub/papers/BC/GK-outer.pdf).
- M. Huang, Y. Liu, and Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869, 2026.
- V. Anantharam, A. Gohari, and C. Nair, "On the evaluation of Marton's inner bound for
  two-receiver broadcast channels," *IEEE Trans. Inf. Theory*, 65(3), 2019.
- C. Nair, "On Marton's achievable region: local tensorization for product channels with a
  binary component," *Information Theory and Applications Workshop (ITA)*, 2020.
