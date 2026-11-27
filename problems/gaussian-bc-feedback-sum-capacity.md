---
id: gaussian-bc-feedback-sum-capacity
title: Sum-Capacity of the Symmetric Gaussian Broadcast Channel with Feedback
status: open
category: network-info-theory
posed_by: Lawrence H. Ozarow and S. K. Leung-Yan-Cheong; Belhadj Amor, Steinberg and Wigger
posed_year: 1984
tags: [network-information-theory, broadcast-channel, feedback, gaussian-channel, linear-feedback, lqg]
lean_module: InfoTheory.Problems.GaussianBcFeedbackSumCapacity
lean_file: lean/InfoTheory/Problems/GaussianBcFeedbackSumCapacity.lean
review: pending-expert
---

## Statement

The two-receiver scalar Gaussian broadcast channel is
$$
Y_{k,i} = h_k X_i + Z_{k,i}, \qquad k = 1, 2,
$$
where $Z_{1,i}, Z_{2,i}$ are independent i.i.d. $\mathcal{N}(0,1)$. The transmitter has
**perfect causal output feedback from both receivers**: $X_i = f_i(M_1, M_2, Y_1^{i-1}, Y_2^{i-1})$.
It must satisfy the expected block power constraint $\sum_{i=1}^n \mathbb{E}[X_i^2] \le nP$.
Receiver $k$ decodes $M_k$ from $Y_k^n$.

**Linear-feedback benchmark.** Belhadj Amor, Steinberg and Wigger (2015, Cor. 2) proved that the
linear-feedback capacity region equals the following region, obtained by MAC–BC duality
from Ozarow's MAC region. It is the set of $(R_1,R_2) \ge 0$ such that for some $P_1 + P_2 = P$
and some $\rho \in [0,1]$:
$$
R_1 \le \tfrac12\log_2\bigl(1 + h_1^2P_1(1-\rho^2)\bigr),\quad
R_2 \le \tfrac12\log_2\bigl(1 + h_2^2P_2(1-\rho^2)\bigr),\quad
R_1 + R_2 \le \tfrac12\log_2\bigl(1 + h_1^2P_1 + h_2^2P_2 + 2|h_1h_2|\sqrt{P_1P_2}\,\rho\bigr).
$$
Here a linear-feedback scheme sends a message-dependent term plus a linear function of past
outputs. Let $C_{\mathrm{LF}}(h_1,h_2,P)$ denote the maximum of $R_1 + R_2$ over this region.

**Question.** For the symmetric channel $h_1 = h_2 = h \ne 0$, is the feedback sum-capacity
$C_{\mathrm{FB,sum}}(h,h,P)$ equal to $C_{\mathrm{LF}}(h,h,P)$? Equivalently: do the
control-theoretic (LQG) schemes of Elia and Ardestanizadeh–Minero–Franceschetti achieve the
sum-capacity of the symmetric Gaussian BC with feedback?

A proof would need a feedback converse matching $C_{\mathrm{LF}}$. A disproof would need a
(necessarily non-linear) feedback scheme beating it.

## Background

El Gamal (1978) showed that feedback does not enlarge the capacity region of a *physically*
degraded broadcast channel. The Gaussian BC with independent noises is only stochastically
degraded. Ozarow and Leung (1984) showed that there feedback *does* enlarge the capacity
region, using a Schalkwijk–Kailath-type linear scheme. Since then:

- the best achievable sum rates have come from linear schemes, in particular control-theoretic
  (LQG / Kalman-filter) codes;
- with correlated noises, feedback can even raise the pre-log above 1 (Gastpar–Lapidoth–
  Steinberg–Wigger; Ardestanizadeh–Minero–Franceschetti).

Yet no converse beyond the cut-set / full-cooperation bound is known to be tight, even for two
users in the symmetric scalar case. Belhadj Amor–Steinberg–Wigger state that the capacity
region of the Gaussian BC with perfect feedback "is unknown even in the scalar case". Among the
open questions they list is "whether the control-theoretic schemes achieve the sum-capacity
with perfect feedback for symmetric BCs". This entry formalizes that question.

## What is known

- **Ozarow–Leung (1984):** an achievable region and an outer bound for the two-user Gaussian BC
  with feedback. Feedback strictly enlarges the region for independent noises.
- **Elia (2004):** a control-oriented (Bode-integral) linear feedback scheme with a better sum
  rate than Ozarow–Leung.
- **Ardestanizadeh–Minero–Franceschetti (2012):** an LQG code for $k$ receivers. For
  independent noises its sum rate is $\tfrac12\log(1 + P\phi)$ with a coherent-gain factor
  $\phi \in [1,k]$ determined by a discrete algebraic Riccati equation. For correlated noises of
  rank $r$ the sum-capacity pre-log is at most $k - r + 1$, and this is tight for some
  covariance.
- **Gastpar–Lapidoth–Steinberg–Wigger (2014):** schemes whose sum rate is asymptotically
  optimal at high SNR, for every noise correlation other than $\pm1$.
- **Belhadj Amor–Steinberg–Wigger (2015):** linear-feedback MAC–BC duality. It gives the
  single-letter linear-feedback capacity region above (two-user SISO). In the symmetric case
  the control-theoretic schemes are **sum-rate optimal among linear-feedback schemes**. The
  maximizing correlation $\rho^\star$ is the root in $[0,1]$ of a quartic.
- **Noisy / one-sided feedback** (Bhaskaran 2008; Pillai 2015; Venkataramanan–Pradhan 2013 for
  DM-BCs) address other settings and do not settle the perfect-feedback sum-capacity.
- We found no paper (searches up to Nov. 2026: the ASW / Wigger follow-ups, the LQG literature,
  "Gaussian broadcast channel feedback sum capacity") claiming a matching converse or a scheme
  beating $C_{\mathrm{LF}}$ in the symmetric case. **The expert should confirm this.**

## Notes on the formalization (for expert review)

- **Model.** Unit-variance independent noises and gains $h_1, h_2$, as in ASW. The statement
  uses $h_1 = h_2 = h \ne 0$ only, which is the published open question. The **region**
  version ("$\mathcal{C}_{\mathrm{FB}} = \mathcal{C}_{\mathrm{LF}}$ for all $h_1,h_2$") is
  strictly stronger and is not what is formalized.
- **Codes.** Encoders are functions of the messages and both full output blocks. They must be
  *causal*, i.e. depend only on times $t < i$, and jointly measurable in the outputs. Decoders
  are measurable. The received blocks are defined by $n$ passes of the channel equations
  starting from the noise. The certificate proves that this is the unique solution of the
  causal recursion and that it is measurable in the noise.
- **Power constraint (judgment call).** The constraint is *expected* power, averaged over
  uniform messages and noise. It is evaluated as an $\mathbb{R}_{\ge0}^\infty$-valued
  `lintegral`, so infinite power is $\top$, never $0$. This follows Ozarow–Leung and ASW.
  Linear feedback schemes have Gaussian-like inputs and cannot satisfy an almost-sure block
  power constraint, so an a.s. constraint would change the benchmark side.
- **Error.** Average over uniform message pairs. For each pair, the error is the noise measure
  of $\{\hat M_1 \ne M_1\} \cup \{\hat M_2 \ne M_2\}$.
- **`sSup` guards.** The operational sum-capacity is an `sSup` in $\mathbb{R}_{\ge0}^\infty$:
  an unbounded achievable set would give $\top$, making the equation false rather than
  vacuous. The linear-feedback sum rate is a real `sSup`. The certificate proves its set
  nonempty and bounded by $\tfrac12\log_2(1 + (|h_1|+|h_2|)^2P)$.
- **Certificate** (`Known/Certificates/GaussianBcFeedbackSumCapacity.lean`):
  - well-posedness of the causal recursion: existence, uniqueness, measurability;
  - $(0,0)$ is achievable;
  - every single-user rate $R < \tfrac12\log_2(1+h_1^2P)$ is achievable, via the operational
    AWGN coding theorem, so both sides of the equation are $\ge \tfrac12\log_2(1+h^2P)$;
  - the formula side is non-junk and bounded.
- **Not certified:** any feedback converse. Even finiteness of the operational sum-capacity is
  not certified, because it needs a change of measure through the causal output map, which is
  not yet in `Known`. Achievability of $C_{\mathrm{LF}}$ is not certified either.

## References

- A. El Gamal, "The feedback capacity of degraded broadcast channels," *IEEE Trans. Inf.
  Theory*, vol. 24, no. 3, pp. 379–381, 1978.
- L. H. Ozarow and S. K. Leung-Yan-Cheong, "An achievable region and outer bound for the Gaussian
  broadcast channel with feedback," *IEEE Trans. Inf. Theory*, vol. 30, no. 4, pp. 667–671, 1984.
- N. Elia, "When Bode meets Shannon: control-oriented feedback communication schemes," *IEEE
  Trans. Autom. Control*, vol. 49, no. 9, 2004.
- S. R. Bhaskaran, "Gaussian broadcast channel with feedback," *IEEE Trans. Inf. Theory*,
  vol. 54, no. 11, 2008.
- E. Ardestanizadeh, P. Minero, M. Franceschetti, "LQG control approach to Gaussian broadcast
  channels with feedback," *IEEE Trans. Inf. Theory*, vol. 58, no. 8, 2012
  (arXiv:1102.3214).
- R. Venkataramanan and S. S. Pradhan, "An achievable rate region for the broadcast channel
  with feedback," *IEEE Trans. Inf. Theory*, vol. 59, no. 10, 2013.
- M. Gastpar, A. Lapidoth, Y. Steinberg, M. Wigger, "Coding schemes and asymptotic capacity for
  the Gaussian broadcast and interference channels with feedback," *IEEE Trans. Inf. Theory*,
  vol. 60, no. 1, 2014 (arXiv:1003.6082).
- S. Belhadj Amor, Y. Steinberg, M. Wigger, "MIMO MAC-BC duality with linear-feedback coding
  schemes," *IEEE Trans. Inf. Theory*, vol. 61, no. 11, 2015 (arXiv:1404.2584).
- S. S. Pillai, "On the noisy feedback capacity of Gaussian broadcast channels,"
  arXiv:1502.04806, 2015.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011, Ch. 17.
