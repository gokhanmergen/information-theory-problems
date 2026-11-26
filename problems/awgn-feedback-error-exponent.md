---
id: awgn-feedback-error-exponent
title: Reliability Function of the Peak-Energy-Constrained AWGN Channel with Feedback
status: open
category: channel-capacity
posed_by: Claude E. Shannon; Mark S. Pinsker
posed_year: 1968
tags: [channel-capacity, error-exponent, awgn, feedback, sphere-packing]
lean_module: InfoTheory.Problems.AwgnFeedbackErrorExponent
lean_file: lean/InfoTheory/Problems/AwgnFeedbackErrorExponent.lean
---

## Statement

Consider the discrete-time memoryless additive white Gaussian noise (AWGN) channel $Y_i = X_i + Z_i$ ($i = 1, \dots, n$) with $Z_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$, noiseless causal output feedback ($X_i = f_i(m, Y_1, \dots, Y_{i-1})$), and a **strict almost-sure codeword energy (peak-energy) constraint**
$$\sum_{i=1}^{n} X_i^2 \;\le\; n P \qquad \text{almost surely for every message } m \in \{1, \dots, M\}$$
for fixed SNR $P > 0$. The capacity is $C(P) = \frac{1}{2} \ln(1 + P)$ (in nats per channel use). Let $E_{\mathrm{fb}}^{\mathrm{peak}}(R, P)$ denote the reliability function (optimal exponential decay rate $-\lim_{n\to\infty} \frac{1}{n} \ln P_e^*(n, \lceil e^{nR} \rceil)$ in nats) over all fixed-blocklength feedback codes satisfying the strict codeword energy constraint $\sum_{i=1}^n X_i^2 \le n P$.

Let $E_{\mathrm{sp}}(R, P)$ denote Shannon's (1959) sphere-packing exponent (in nats) for $0 < R < C(P)$: writing $A = \sqrt{P}$, $\sin\theta = e^{-R}$, $\cos\theta = \sqrt{1 - e^{-2R}}$, and $g(\theta) = \frac{1}{2}\big(A \cos\theta + \sqrt{A^2 \cos^2\theta + 4}\big)$,
$$E_{\mathrm{sp}}(R, P) := \frac{P}{2} - \frac{A\, g(\theta) \cos\theta}{2} - \ln\big(g(\theta) \sin\theta\big).$$

**Problem (Tightness of the Sphere-Packing Bound with Feedback under Peak Energy).** Pinsker (1968) proved that $E_{\mathrm{fb}}^{\mathrm{peak}}(R, P) \le E_{\mathrm{sp}}(R, P)$ for all $R \in (0, C(P))$, and equality holds for all $R \in [R_{\mathrm{crit}}(P), C(P))$ as well as in the zero-rate limit $R \to 0^+$ ($E_{\mathrm{fb}}^{\mathrm{peak}}(0^+, P) = P/2 = E_{\mathrm{sp}}(0^+, P)$). Does equality
$$E_{\mathrm{fb}}^{\mathrm{peak}}(R, P) \;=\; E_{\mathrm{sp}}(R, P)$$
hold for **every** SNR $P > 0$ and **every** rate $0 < R < C(P)$ (including the low-rate regime $0 < R < R_{\mathrm{crit}}(P)$)?

## Background

The effect of noiseless feedback on the reliability function of the AWGN channel exhibits a dramatic dichotomy depending on the power constraint. Under an **expected (average) energy constraint** $\frac{1}{n} \sum_{i=1}^n \mathbb{E}[X_i^2] \le P$, Schalkwijk and Kailath (1966) demonstrated that linear feedback schemes achieve **doubly exponential** error decay (an infinite error exponent $E_{\mathrm{fb}}^{\mathrm{avg}}(R, P) = +\infty$ for all $0 < R < C(P)$) by using rare, arbitrarily large power bursts to correct atypical noise realizations.

When such power spikes are forbidden by an **almost-sure codeword energy constraint** $\sum_{i=1}^n X_i^2 \le n P$, Pinsker (1968) proved the striking converse that feedback *cannot* surpass Shannon's (1959) sphere-packing upper bound $E_{\mathrm{sp}}(R, P)$ at any rate $R \in (0, C(P))$. Without feedback, the reliability function drops strictly below $E_{\mathrm{sp}}(R, P)$ at low rates (reaching $E(0^+, P) = P/4$ at $R \to 0^+$ vs. $E_{\mathrm{sp}}(0^+, P) = P/2$). With feedback, however, the zero-rate exponent jumps all the way to $P/2 = E_{\mathrm{sp}}(0^+, P)$ (Zigangirov 1970; Schalkwijk 1971; Pinsker 1968). Whether causal feedback closes the entire low-rate gap between $0$ and $R_{\mathrm{crit}}(P)$ so that $E_{\mathrm{fb}}^{\mathrm{peak}}(R, P) = E_{\mathrm{sp}}(R, P)$ for all $R \in (0, C(P))$ remains a classic open problem.

## What is known

- **No-feedback AWGN reliability function (Shannon, 1959; Gallager, 1965):** $E(R, P) = E_{\mathrm{sp}}(R, P)$ for $R_{\mathrm{crit}}(P) \le R < C(P)$, while for $0 < R < R_{\mathrm{crit}}(P)$ only lower bounds (random coding, expurgated, straight-line) and upper bounds (sphere-packing, minimum-distance / Kabatyanskii–Levenshtein) are known, with $E(0^+, P) = P/4$.
- **Average-power feedback (Schalkwijk–Kailath, 1966):** Achieves $P_e \le \exp(-\exp(\Omega(n)))$, i.e., infinite reliability function for all $R < C(P)$.
- **Peak-energy feedback converse (Pinsker, 1968):** $E_{\mathrm{fb}}^{\mathrm{peak}}(R, P) \le E_{\mathrm{sp}}(R, P)$ for all $0 < R < C(P)$.
- **Zero-rate peak-energy feedback (Pinsker, 1968; Zigangirov, 1970):** $E_{\mathrm{fb}}^{\mathrm{peak}}(0^+, P) = P/2 = E_{\mathrm{sp}}(0^+, P)$, strictly beating the no-feedback exponent $P/4$.
- **Low positive rates $0 < R < R_{\mathrm{crit}}(P)$:** Exact value of $E_{\mathrm{fb}}^{\mathrm{peak}}(R, P)$ — and whether it equals $E_{\mathrm{sp}}(R, P)$ throughout $(0, R_{\mathrm{crit}}(P))$ — remains open.

## References

- C. E. Shannon, "Probability of error for optimal codes in a Gaussian channel," *Bell Syst. Tech. J.*, 38(3):611–656, 1959.
- J. P. M. Schalkwijk and T. Kailath, "A coding scheme for additive noise channels with feedback — Part I: No bandwidth constraint," *IEEE Trans. Inf. Theory*, 12(2):172–182, 1966.
- M. S. Pinsker, "The probability of error in block transmission in a memoryless Gaussian channel with feedback," *Problems of Information Transmission*, 4(4):3–19, 1968.
- K. S. Zigangirov, "Upper bounds for the error probability for channels with feedback," *Problems of Information Transmission*, 6(2):159–163, 1970.
- M. V. Burnashev, "Data transmission over a discrete channel with feedback: Random transmission time," *Problems of Information Transmission*, 12(4):250–265, 1976.
- Y. Xiang and Y.-H. Kim, "On the error exponent of Gaussian channels with noiseless feedback," *Proc. IEEE ISIT*, 2013.
