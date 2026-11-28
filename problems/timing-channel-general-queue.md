---
id: timing-channel-general-queue
title: Feedback Capacity Gain of the General Single-Server Queue Timing Channel
status: partially-solved
category: channel-capacity
posed_by: Venkat Anantharam and Sergio Verdú
posed_year: 1996
tags: [channel-capacity, timing-channel, queueing-theory, feedback]
lean_module: InfoTheory.Problems.TimingChannelGeneralQueue
lean_file: lean/InfoTheory/Problems/TimingChannelGeneralQueue.lean
---

## Statement

Consider a single-server first-in-first-out ($\cdot/G/1$) queue operating as a timing channel (Anantharam–Verdú, 1996). Packets arrive at epochs $0 \le A_1 \le A_2 \le \cdots \le A_n$ chosen by the encoder; a code operates at output rate $\lambda \in (0, \mu)$ if the $n$-th departure occurs on average no later than $n/\lambda$, i.e. $\mathbb{E}[D_n] \le n/\lambda$ (averaged over equiprobable messages and service times), and its rate is $\log M / (n/\lambda)$ (Anantharam–Verdú 1996; Sahasranand–Tchamkerten 2023). Packets experience i.i.d. positive service times $S_1, S_2, \dots$ drawn from a continuous density $f_S$ on $(0, \infty)$ with finite mean $\mathbb{E}[S_1] = 1/\mu > 0$. Departure times satisfy Lindley's recursion
$$D_0 = 0, \qquad D_k = \max(A_k, D_{k-1}) + S_k \qquad (k = 1, \dots, n).$$

Let $C(f_S, \lambda)$ denote the Shannon capacity (in nats per unit time) without feedback, and let $C_{\mathrm{fb}}(f_S, \lambda)$ denote the capacity with full causal departure-time feedback. Anantharam and Verdú (1996) proved that for any general service-time density $f_S$ of mean $1/\mu$,
$$C(f_S, \lambda) \;\le\; C_{\mathrm{fb}}(f_S, \lambda) \;=\; \lambda \cdot \sup_{\substack{W \ge 0 \\ \mathbb{E}[W] \le \frac{1}{\lambda} - \frac{1}{\mu}}} I(W; W + S),$$
with equality $C(f_S, \lambda) = C_{\mathrm{fb}}(f_S, \lambda) = \lambda \ln(\mu/\lambda)$ when $S \sim \mathrm{Exp}(\mu)$ is exponentially distributed.

**Conjecture (Anantharam–Verdú Feedback Conjecture, 1996).** For every continuous positive service-time density $f_S$ of finite mean $1/\mu$ that is **not** exponential, and every arrival rate $\lambda \in (0, \mu)$, full causal feedback strictly increases the FIFO timing-channel capacity:
$$C(f_S, \lambda) \;<\; C_{\mathrm{fb}}(f_S, \lambda).$$

> **Statement-fix (2026-11-27).** (1) The previous Lean no-feedback capacity constrained the *arrival* epochs to $[0, n/\lambda]$ instead of the expected *last departure* $\mathbb{E}[D_n] \le n/\lambda$. Under that relaxation an encoder can signal at any lower output rate $\lambda' < \lambda$ on part of the window and release the remaining packets at time $n/\lambda$ (they depart after the window and cost nothing), so the defined quantity is at least $\sup_{\lambda' \le \lambda} C(\lambda')$; since $C_{\mathrm{fb}}(f_S, \lambda) \to 0$ as $\lambda \uparrow \mu$ while $\sup_{\lambda' \le \lambda} C(\lambda')$ stays bounded away from $0$, the old statement was false as written for every service law (`[sketch]`). The code definition now uses the Anantharam–Verdú constraint $\mathbb{E}[D_n] \le n/\lambda$ (a Lebesgue `lintegral`, junk-free). (2) The excluded class was "shifted exponential $c + \mathrm{Exp}(\mu)$, $c \ge 0$"; the conjecture as posed excludes only the memoryless (exponential) service law, and the justification given for $c > 0$ (that a constant delay cancels in the Lindley recursion) is wrong because $c$ also occupies the server. The exclusion is now `IsExponential`.

## Formal statement (Lean)

`InfoTheory.Problems.TimingChannelGeneralQueue.Statement`: for every `ServiceDensity` $S$ (continuous density on $(0,\infty)$, finite positive mean, finite differential entropy) that is not exponential and every $0 < \lambda < 1/\mathbb{E}[S]$,
`queueNoFeedbackCapacity S λ < queueFeedbackCapacity S λ`, where the former is the operational capacity (nats/s) of $(n, M, n/\lambda, \varepsilon)$ codes with nondecreasing nonnegative arrivals, $\mathbb{E}[D_n] \le n/\lambda$, measurable decoders and average error $\le \varepsilon$, and the latter is $\lambda \sup \{h(W+S) - h(S) : W \text{ a service density}, \mathbb{E}[W] \le 1/\lambda - \mathbb{E}[S]\}$. Certificate: `lean/InfoTheory/Known/Certificates/TimingChannelGeneralQueue.lean` (Lindley recursion facts, back-to-back regression $D_n = \sum_i S_i$, $C \ge 0$).

## Background

In their landmark 1996 paper *"Bits Through Queues"*, Anantharam and Verdú modeled a single-server queue as a continuous-time timing channel in which information is carried solely in the inter-arrival times of identical packets and corrupted by random service delays. For the $\cdot/M/1$ queue (exponential service times), Burke's theorem implies that a Poisson arrival process produces a Poisson departure process, allowing them to determine the exact capacity $C = \lambda \ln(\mu/\lambda)$ nats/sec — and to show that noiseless feedback does *not* increase capacity in the exponential case.

For any non-exponential service time $S$ ($\cdot/G/1$ queue), however, the exact non-feedback capacity $C(f_S, \lambda)$ is unknown (even for deterministic or uniform service times!). While full causal feedback reduces the queue to an additive-noise channel with inter-departure shaping $W_k \ge 0$ (yielding the single-letter formula $C_{\mathrm{fb}}(f_S, \lambda)$), Anantharam and Verdú conjectured that the memoryless exponential distribution is the *unique* service law for which feedback provides zero capacity gain.

## What is known

- **Exponential service times (Anantharam–Verdú, 1996):** $C(\mathrm{Exp}(\mu), \lambda) = C_{\mathrm{fb}}(\mathrm{Exp}(\mu), \lambda) = \lambda \ln(\mu / \lambda)$ nats/sec (and maximizing over $\lambda \in (0, \mu)$ yields $\mu / e$ nats/sec).
- **General upper and lower bounds (Anantharam–Verdú, 1996; Sundaresan–Verdú, 2000; Prabhakar–Gallager, 2003):** $C(f_S, \lambda) \ge \lambda \ln(\mu/\lambda)$ when $S$ has a log-concave / increasing-failure-rate density or via exponential-queue comparison; exact capacity without feedback remains unknown for virtually every non-exponential $f_S$.
- **Sufficient conditions for feedback gain (Aptel–Tchamkerten, 2020):** Introduced "weak feedback" (service start times) and gave sufficient conditions under which feedback strictly increases capacity.
- **Bounded / finite-support service times (Sahasranand–Tchamkerten, 2024):** Proved the Anantharam–Verdú conjecture for **all** service-time distributions with bounded support (confirming $C(f_S, \lambda) < C_{\mathrm{fb}}(f_S, \lambda)$ whenever $\mathrm{supp}(f_S)$ is bounded).
- **Unbounded non-exponential service times:** The conjecture remains open for general unbounded-support non-exponential service-time densities (e.g., Gamma, Weibull, log-normal, or mixtures of exponentials).

## References

- V. Anantharam and S. Verdú, "Bits through queues," *IEEE Trans. Inf. Theory*, 42(1):4–18, 1996.
- R. Sundaresan and S. Verdú, "Robust decoding for timing channels," *IEEE Trans. Inf. Theory*, 46(2):405–419, 2000.
- B. Prabhakar and R. G. Gallager, "Entropy and the timing capacity of discrete queues," *IEEE Trans. Inf. Theory*, 49(2):357–370, 2003.
- O. Aptel and A. Tchamkerten, "Feedback increases the capacity of queues," *IEEE Trans. Inf. Theory*, 66(9):5561–5572, 2020.
- K. R. Sahasranand and A. Tchamkerten, "Feedback increases the capacity of queues with bounded service times," arXiv:2309.14145, 2023.
