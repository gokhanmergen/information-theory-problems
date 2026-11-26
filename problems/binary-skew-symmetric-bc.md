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
capacity problem into a concrete $0.01$-bit gap on a binary-input, binary-output channel.

## What is known

- The single-user capacity of each marginal Z-channel is
  $C_Z = \max_{p \in [0, 1]} (h(p/2) - p) = \log_2(5/4) \approx 0.321928$ bits.
- Nair, Wang, and Geng (2010) proved an information inequality establishing that for
  *every* binary-input broadcast channel, the sum-rate of Marton's inner bound is achieved
  by randomized time division (binary auxiliary variables). For the BSSC, this evaluates
  precisely to $R_{\mathrm{M,sum}}(W_{\mathrm{BSSC}}) \approx 0.3616428$ bits, strictly
  beating time sharing ($0.321928$ bits).
- The Nair–El Gamal (2007) UV outer bound evaluates on the BSSC to
  $\approx 0.37256$ bits, leaving a gap of roughly $0.0109$ bits above Marton's sum-rate.
- Gohari and Nair (2022) developed the auxiliary-receiver converse framework and proved a
  strictly tighter upper bound on the BSSC sum-rate than the UV outer bound, narrowing
  the gap but not closing it.
- Multi-letter (2-letter and higher) evaluations of Marton's inner bound on the BSSC have
  not yielded any improvement over single-letter Marton's bound, lending support to — but
  not proving — the conjecture that $R_{\mathrm{M,sum}}(W_{\mathrm{BSSC}})$ is exact.

## References

- B. E. Hajek and M. B. Pursley, "Evaluation of an achievable rate region for the broadcast
  channel," *IEEE Trans. Inf. Theory*, vol. 25, no. 1, pp. 36–46, 1979.
- K. Marton, "A coding theorem for the discrete memoryless broadcast channel," *IEEE Trans.
  Inf. Theory*, vol. 25, no. 3, pp. 306–311, 1979.
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the broadcast channel,"
  *IEEE Trans. Inf. Theory*, vol. 53, no. 1, pp. 401–405, 2007.
- C. Nair, Z. V. Wang, and Y. Geng, "An information inequality and evaluation of Marton's
  inner bound for binary input broadcast channels," *IEEE Int. Symp. Inf. Theory (ISIT)*,
  2010; arXiv:1001.1468.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
