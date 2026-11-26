---
id: gaussian-relay-channel-capacity
title: Exact Capacity of the Three-Node Gaussian Relay Channel
status: open
category: network-info-theory
posed_by: Thomas Cover and Abbas El Gamal
posed_year: 1979
tags: [network-information-theory, relay-channel, gaussian, cooperation]
lean_module: InfoTheory.Problems.GaussianRelayChannelCapacity
lean_file: lean/InfoTheory/Problems/GaussianRelayChannelCapacity.lean
---

## Statement

Consider the memoryless three-node AWGN relay channel with real channel gains
$(g_{12}, g_{13}, g_{23})$ and average power constraints $P_1, P_2 > 0$:
$$
Y_{r,i} = g_{12} X_i + Z_{r,i}, \qquad Y_i = g_{13} X_i + g_{23} X_{r,i} + Z_i,
$$
where $Z_{r,i}, Z_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$ are independent
standard Gaussian noises, the source codeword satisfies
$\frac{1}{n} \sum_{i=1}^n X_i^2 \le P_1$, and the causal relay outputs
$X_{r,i} = f_i(Y_r^{i-1})$ satisfy $\frac{1}{n} \sum_{i=1}^n \mathbb{E}[X_{r,i}^2] \le P_2$.

Writing $C(s) = \frac{1}{2} \log_2(1 + s)$, the Gaussian hybrid decode-and-forward /
compress-and-forward (Cover–El Gamal Theorem 7) achievable rate is
$$
R_{\mathrm{hyb}}(g_{12}, g_{13}, g_{23}, P_1, P_2) = \sup_{\substack{\alpha,\beta,\gamma \ge 0,\; \alpha+\beta+\gamma \le 1 \\ \theta \in [0, 1],\; \sigma^2 > 0}} \sup \{ R_1 + R_2 : R_1, R_2 \ge 0 \},
$$
subject to:
$$
\begin{aligned}
R_1 &\le C\!\left(\frac{g_{12}^2 \beta P_1}{1 + g_{12}^2 \gamma P_1}\right), \\
R_2 &\le \min\!\left(C\!\left(g_{13}^2 \gamma P_1 + \frac{g_{12}^2 \gamma P_1}{1 + \sigma^2}\right),\; C\!\big(g_{13}^2 \gamma P_1 + g_{23}^2 (1 - \theta) P_2\big) - C\!\left(\frac{1}{\sigma^2}\right)\right), \\
R_1 + R_2 &\le C\!\Big(g_{13}^2 P_1 + g_{23}^2 P_2 + 2 |g_{13} g_{23}| \sqrt{\alpha \theta P_1 P_2}\Big) - C\!\left(\frac{1}{\sigma^2}\right).
\end{aligned}
$$

**Does $R_{\mathrm{hyb}}$ equal the exact capacity $C_{\mathrm{Gauss}}(g_{12}, g_{13}, g_{23}, P_1, P_2)$
for all gains $(g_{12}, g_{13}, g_{23})$ and powers $P_1, P_2 > 0$?**

## Background

The AWGN relay channel is the canonical continuous-alphabet model of wireless cooperative
communication. Even though the channel is defined by three scalar gains and two power
constraints, its exact capacity has remained open since Cover and El Gamal (1979)
introduced decode-and-forward, compress-and-forward, and their hybrid combination. The
Gaussian cutset bound is closed-form and was long suspected to be loose, a fact finally
proved in full generality only recently. Determining whether a single-letter Gaussian
strategy (or a multi-letter / structured-lattice / linear-filtering scheme) achieves
capacity remains one of the flagship open problems in wireless information theory.

## What is known

- The Gaussian cutset bound is
  $C_{\mathrm{CS}} = \max_{\rho \in [0, 1]} \min\!\big(C((g_{12}^2 + g_{13}^2)(1 - \rho^2) P_1),\; C(g_{13}^2 P_1 + g_{23}^2 P_2 + 2 \rho |g_{13} g_{23}| \sqrt{P_1 P_2})\big)$.
- El Gamal, Gohari, and Nair (2022) proved that the capacity of the Gaussian relay channel
  is **strictly smaller** than the cutset bound whenever $g_{12}, g_{13}, g_{23} \ne 0$
  and $P_1, P_2 > 0$.
- For the *primitive* Gaussian relay channel (orthogonal noiseless relay-to-destination
  pipe of rate $C_0$), Wu, Barnes, and Özgür (2019) used spherical concentration of measure
  to prove that $C(C_0) < C(\infty)$ for every finite $C_0$, resolving Cover's 1987 open
  problem in the Gaussian case.
- Constant-gap capacity: compress-and-forward (and noisy network coding) achieves capacity
  to within $1/2$ bit per channel use for all channel gains and powers
  (Avestimehr–Diggavi–Tse 2011; Lim–Kim–El Gamal–Chung 2011).
- El Gamal, Mohseni, and Zahedi (2006) showed that multi-letter amplify-and-forward with
  colored Gaussian inputs can outperform both pure decode-and-forward and pure
  independent-input compress-and-forward in certain intermediate SNR regimes.
- Capacity is known exactly in the physically degraded limit ($g_{13} = 0$ or
  $g_{12} \to \infty$) and when the relay is very close to the source so that
  decode-and-forward meets the cutset bound.

## References

- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," *IEEE Trans. Inf.
  Theory*, vol. 25, no. 5, pp. 572–584, 1979.
- A. El Gamal, M. Mohseni, and S. Zahedi, "Bounds on capacity and minimum energy-per-bit
  for AWGN relay channels," *IEEE Trans. Inf. Theory*, vol. 52, no. 4, pp. 1545–1561, 2006.
- A. S. Avestimehr, S. N. Diggavi, and D. N. C. Tse, "Wireless network information flow:
  a deterministic approach," *IEEE Trans. Inf. Theory*, vol. 57, no. 4, pp. 1872–1905, 2011.
- X. Wu, L. P. Barnes, and A. Özgür, "'The capacity of the relay channel': solution to
  Cover's problem in the Gaussian case," *IEEE Trans. Inf. Theory*, vol. 65, no. 1,
  pp. 255–275, 2019.
- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the capacity
  of the relay channel and applications," *IEEE Trans. Inf. Theory*, vol. 68, no. 7,
  pp. 4247–4263, 2022.
