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

Let $C_{\mathrm{Gauss}}(g_{12}, g_{13}, g_{23}, P_1, P_2)$ be its operational capacity. It is
unknown for every choice of nonzero gains. The formal statement poses the sharpest open
first-order question at the standard benchmark of unit gains and equal powers
$P_1 = P_2 = P$: the cutset bound gives $C_{\mathrm{Gauss}}(1,1,1,P,P) \le \tfrac12\log_2(1+2P)
\le P/\ln 2$, so the capacity per unit power is at most $1/\ln 2$ bits.

**Is the cutset bound tight to first order at low SNR, i.e. does**
$$
\lim_{P \to 0^+} \frac{C_{\mathrm{Gauss}}(1, 1, 1, P, P)}{P} = \frac{1}{\ln 2}\ ?
$$
This is the minimum energy-per-bit question of El Gamal–Mohseni–Zahedi (2006) at this
benchmark, with per-node power normalization: does the minimum energy-per-bit equal the
cutset lower bound?

In Lean: `Statement : Filter.Tendsto (fun P => gaussianRelayCapacity 1 1 1 P P / ENNReal.ofReal P)
(nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (1 / Real.log 2)))`. The capacity is valued in
`ℝ≥0∞` (an unbounded achievable set gives `⊤`, never a junk `0`); the source constraint is per
codeword, the relay constraint is a per-message expectation over the relay noise, and the
error and power integrals are Lebesgue integrals in `ℝ≥0∞`.

> **Statement-fix (2026-11-27).** The previous statement asked whether $C_{\mathrm{Gauss}}$
> equals the Gaussian hybrid decode-forward/compress-forward rate $R_{\mathrm{hyb}}$ (Cover–El
> Gamal Theorem 7 with jointly Gaussian inputs) for all gains and powers. $R_{\mathrm{hyb}}$
> has no power time-sharing, while the model allows bursty signalling, so bursty
> compress-forward (El Gamal–Mohseni–Zahedi 2006, eq. (8)) beats it; their block-length-2
> linear relaying beats it and even its upper concave envelope. The old statement was
> therefore false by known results; see
> `attempts/gaussian-relay-channel-capacity/2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md`.
> Since every "capacity = single-letter Gaussian DF/CF/hybrid rate" re-posing is refuted or
> very likely refuted in the same way, the statement now asks about the low-SNR capacity
> slope, whose value is unknown.

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
- El Gamal, Mohseni, and Zahedi (2006) observed that the Gaussian compress-and-forward
  (side-information) rate is not concave in the power and improved it by bursty
  time-sharing (their eq. (8): transmit at powers $(P_1/\lambda, P_2/\lambda)$ a fraction
  $\lambda$ of the time). They also showed that a block-length-2 linear relaying scheme
  (their Example 1: the source repeats a scaled symbol, and the relay forwards a scaled copy
  of its previous received symbol) can beat both the generalized block-Markov
  (decode-and-forward) rate and the Gaussian compress-and-forward rate, notably at low SNR
  (their Fig. 3).
- Capacity is known exactly when $g_{13} = 0$: the channel is then physically degraded and
  decode-and-forward meets the cutset bound, giving
  $C = \min(C(g_{12}^2 P_1), C(g_{23}^2 P_2))$. As $g_{12} \to \infty$, decode-and-forward
  approaches the cutset bound. For this model (independent noises, all gains nonzero),
  however, the generalized block-Markov lower bound never meets the cutset bound
  (El Gamal–Mohseni–Zahedi 2006, Sec. 2), consistent with the strict gap of El Gamal–Gohari–Nair.
- Low-SNR bounds at unit gains and $P_1 = P_2 = P$: the direct link with a silent relay gives
  $C_{\mathrm{Gauss}} \ge \tfrac12\log_2(1+P)$, slope $\ge 1/(2\ln 2) \approx 0.7213$
  (certified in Lean); EMZ Example 1 with bursting gives $C_{\mathrm{Gauss}} \ge 0.88283\,P$
  for $P \in (0, 1/10]$ (see attempt log); the cutset slope is $1/\ln 2 \approx 1.4427$.
  Kosut–Effros–Langberg (arXiv:2401.15495, 2024) improve the achievable minimum
  energy-per-bit with rank-1 linear relaying and still compare against the cutset lower
  bound only.
- The Gaussian hybrid DF/CF rate (Cover–El Gamal Theorem 7 with jointly Gaussian inputs, no
  time-sharing) equals the closed-form Gaussian compress-forward rate when
  $g_{12}^2 \le g_{13}^2$, and is strictly beaten by bursty compress-forward and by EMZ
  Example 1 (e.g. $0.0883 > 0.0738$ at unit gains, $P_1 = P_2 = 1/10$); see attempt log.

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
- O. Kosut, M. Effros, and M. Langberg, "Nobody expects a differential equation: minimum
  energy-per-bit for the Gaussian relay channel with rank-1 linear relaying,"
  arXiv:2401.15495, 2024.
