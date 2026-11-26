---
id: zero-error-broadcast-channel
title: Computability and Characterization of the Zero-Error Broadcast Channel Feedback Capacity
status: open
category: zero-error
posed_by: János Körner, Alon Orlitsky; Ofer Shayevitz, Michèle Wigger
posed_year: 1998
tags: [zero-error, broadcast-channel, feedback, multiterminal, computability]
lean_module: InfoTheory.Problems.ZeroErrorBroadcastChannel
lean_file: lean/InfoTheory/Problems/ZeroErrorBroadcastChannel.lean
---

## Statement

Consider a two-receiver discrete memoryless broadcast channel (DMBC) with finite alphabets
$\mathcal{X}, \mathcal{Y}_1, \mathcal{Y}_2$ and zero-error transition support relation
$S \subseteq \mathcal{X} \times \mathcal{Y}_1 \times \mathcal{Y}_2$ (where
$(x, y_1, y_2) \in S$ iff $W(y_1, y_2 \mid x) > 0$, with every $x$ having at least one
reachable output). With causal noiseless output feedback from both receivers, an
$(n, M_1, M_2)$ zero-error feedback code consists of adaptive encoding functions
$$f_i : \{1, \dots, M_1\} \times \{1, \dots, M_2\} \times (\mathcal{Y}_1 \times \mathcal{Y}_2)^{i-1} \to \mathcal{X} \qquad (i = 1, \dots, n)$$
and decoders $g_1 : \mathcal{Y}_1^n \to \{1, \dots, M_1\}$,
$g_2 : \mathcal{Y}_2^n \to \{1, \dots, M_2\}$ such that for every message pair $(m_1, m_2)$
and every feasible channel output sequence $(y_1^n, y_2^n)$ (satisfying
$(f_i(m_1, m_2, y_1^{i-1}, y_2^{i-1}), y_{1,i}, y_{2,i}) \in S$ for all $i$), we have
$g_1(y_1^n) = m_1$ and $g_2(y_2^n) = m_2$.

The **zero-error feedback sum capacity** of $S$ is
$$C_{0,f}^{\mathrm{sum}}(S) = \sup \left\{ \frac{\log_2 M_1 + \log_2 M_2}{n} : \exists \text{ zero-error feedback code of parameters } (n, M_1, M_2) \right\} .$$

**Is $C_{0,f}^{\mathrm{sum}}(S)$ computable** (and more generally, does the zero-error
feedback capacity region of a two-receiver DMBC admit a computable single-letter
characterization)? Equivalently, does there exist an algorithm that, given the finite
support table $S$ and precision $m \ge 1$, halts and outputs a rational approximation within
$1/m$ of $C_{0,f}^{\mathrm{sum}}(S)$?

## Background

For a **point-to-point** discrete memoryless channel with noiseless feedback, Shannon (1956)
completely solved the zero-error capacity problem, giving a clean single-letter minimax formula:
whenever $C_0(W) > 0$,
$$C_{0,f}(W) = \max_{P_X} \min_{y \in \mathcal{Y}} \log_2 \frac{1}{\sum_{x : W(y \mid x) > 0} P_X(x)} .$$
Thus, unlike zero-error capacity without feedback (where even $C_7$ is open), the single-user
zero-error feedback capacity is both single-letterizable and computable.

Remarkably, moving from one receiver to **two receivers** destroys this tractability even in
the presence of full noiseless feedback from both receivers. Feedback allows the transmitter
to track the joint knowledge state of both receivers and exploit past noise realizations for
common-message-like coordination (as in Dueck 1980 and Shayevitz–Wigger 2013 for vanishing
error), but tracking the exact set of surviving message pairs at each receiver creates a
combinatorial multi-graph refinement game for which no single-letter characterization — and no
general algorithm to compute the capacity region or sum capacity — is known.

## What is known

- **Single-user feedback case (Shannon 1956):** Completely solved by Shannon's single-letter
  formula when $C_0(W) > 0$ (and $C_{0,f}(W) = 0$ when $C_0(W) = 0$).
- **Deterministic broadcast channels:** For deterministic DMBCs ($Y_1 = f_1(X)$, $Y_2 = f_2(X)$),
  feedback has no effect and the zero-error capacity region coincides with the vanishing-error
  capacity region of Gelfand–Pinsker–Marton (with sum capacity $\log_2 |\operatorname{Im}(f_1, f_2)|$).
- **No-feedback zero-error BC:** Reduces to single-user Shannon capacity $\Theta(G_1)$ and
  $\Theta(G_2)$ on the two axes, inheriting all the obstructions of graph capacity.
- **Two-receiver feedback bounds:** Outer bounds follow from the single-user Shannon feedback
  capacities $C_{0,f}(W_1)$, $C_{0,f}(W_2)$ and the cooperative receiver bound $C_{0,f}(W)$, as
  well as vanishing-error feedback outer bounds (Shayevitz–Wigger 2013), but matching inner and
  outer characterizations and computability remain open in general.

## References

- C. E. Shannon, "The zero error capacity of a noisy channel,"
  IRE Trans. Inf. Theory, 1956.
- J. Körner and A. Orlitsky, "Zero-error information theory,"
  IEEE Trans. Inf. Theory, 1998.
- O. Shayevitz and M. Wigger, "On the capacity of the discrete memoryless broadcast channel
  with feedback," IEEE Trans. Inf. Theory, 2013.
- G. Dueck, "Partial feedback for two-way and broadcast channels,"
  Inf. Control, 1980.
- P. Vanroose and E. C. van der Meulen, "Uniquely decodable codes for deterministic relay
  channels," IEEE Trans. Inf. Theory, 1992.
