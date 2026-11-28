---
id: cognitive-interference-channel
title: Capacity Region of the Discrete Memoryless Cognitive Interference Channel
status: open
category: network-info-theory
posed_by: Natasha Devroye, Patrick Mitran, and Vahid Tarokh
posed_year: 2006
tags: [network-information-theory, interference-channel, cognitive-radio, broadcast-channel]
lean_module: InfoTheory.Problems.CognitiveInterferenceChannel
lean_file: lean/InfoTheory/Problems/CognitiveInterferenceChannel.lean
formal_status: claimed-resolved
formal_status_note: "Reduces to broadcast-channel at |X1|=1; false if Huang–Liu–Liu arXiv:2608.19869 holds (unverified)"
---

## Statement

A **discrete memoryless cognitive interference channel** (also called an interference
channel with unidirectional transmitter cooperation or degraded message sets) consists of a
channel $W(y_1, y_2 \mid x_1, x_2)$ on finite alphabets
$\mathcal{X}_1 \times \mathcal{X}_2 \to \mathcal{Y}_1 \times \mathcal{Y}_2$, where:
- Primary transmitter $1$ knows only message $M_1 \in \{1, \dots, 2^{n R_1}\}$ and sends
  $X_1^n(M_1)$;
- Cognitive transmitter $2$ knows **both** messages $(M_1, M_2)$ and sends
  $X_2^n(M_1, M_2)$;
- Receiver $1$ decodes $M_1$ from $Y_1^n$, and receiver $2$ decodes $M_2$ from $Y_2^n$.

The frozen region $\mathcal{R}_{\mathrm{RTD}}(W)$ is an **RTD-type inner bound** modelled
on Rini–Tuninetti–Devroye (2011, Theorem 7). It combines superposition, rate-splitting
$R_1 = R_{1c} + R_{1p}$, $R_2 = R_{2c} + R_{2p}$, and Gel'fand–Pinsker / Marton binning
across auxiliaries $(U_0, U_{1p}, U_{2c}, U_{2p})$, jointly distributed with $(X_1, X_2)$ via
$p(u_0, u_{1p}, u_{2c}, u_{2p}, x_1, x_2) W(y_1, y_2 \mid x_1, x_2)$, plus time sharing. The
binning rates $R'_{1p}, R'_{2c}, R'_{2p} \ge 0$ satisfy the mutual-covering constraints
$$
\begin{aligned}
R'_{2c} &\ge I(U_{2c}; X_1 \mid U_0), \\
R'_{2p} &\ge I(U_{2p}; X_1 \mid U_0, U_{2c}), \\
R'_{1p} + R'_{2c} &\ge I(X_1, U_{1p}; U_{2c} \mid U_0), \\
R'_{1p} + R'_{2p} &\ge I(U_{2p}; X_1 \mid U_0, U_{2c}) + I(U_{1p}; U_{2p} \mid U_0, X_1, U_{2c}), \\
R'_{1p} + R'_{2c} + R'_{2p} &\ge I(U_{2c}, U_{2p}; X_1 \mid U_0) + I(U_{1p}; U_{2c}, U_{2p} \mid U_0, X_1),
\end{aligned}
$$
and there are three decoding constraints at each receiver (see the Lean file).

The frozen region is *not* a literal transcription of RTD's Theorem 7. RTD split the
primary message into three parts, superpose the cognitive transmitter's codeword for the
primary private message on the cognitive common codeword, and drop error events in which
no intended message is wrong (their Remark V.2). The frozen region uses a two-part split,
bins $U_{1p}$ against $U_{2c}$, and keeps all constraints. It lies inside the WVA
one-auxiliary outer bound. It contains Marton's region with common auxiliary when $X_1$ is
degenerate. It contains the capacity region in the better-cognitive-decoding regime, which
includes the very weak and very strong interference regimes. It also contains it in the
semi-deterministic case, which includes the deterministic one. The Gaussian results below
are outside this finite-alphabet question. A constraint-by-constraint
audit is in
`attempts/cognitive-interference-channel/2026-11-26-claude-opus-5-5-audit-and-bc-reduction.md`.

**Does $\mathcal{R}_{\mathrm{RTD}}(W)$ equal the exact capacity region
$\mathcal{C}_{\mathrm{cog}}(W)$ for every finite-alphabet discrete memoryless cognitive
interference channel $W$?**

## Background

Introduced by Devroye, Mitran, and Tarokh (2006) to model cognitive radio systems in which
a secondary transmitter noncausally acquires the primary user's message, the cognitive
interference channel bridges the broadcast channel and the interference channel. Indeed,
when the primary input $X_1$ is absent (degenerate), the cognitive interference channel
reduces identically to the general two-receiver discrete memoryless broadcast channel,
showing that characterizing $\mathcal{C}_{\mathrm{cog}}(W)$ is at least as hard as the
general broadcast channel problem. Formally, at $|\mathcal{X}_1| = 1$ the frozen region
equals the Core `martonInnerBound` and the operational region equals `bcCapacityRegion`.
So this problem's Statement implies the `broadcast-channel` Statement, and it is
equivalent to it when restricted to $|\mathcal{X}_1| = 1$ (attempt cited above, Claims
1–3).

## What is known

- **Weak interference regime**: Wu, Vishwanath, and Arapostathis (2007) determined the
  capacity region for a class of weak-interference channels. RTD (2011) restate the
  result as the "very weak interference" regime. In this file's indexing (transmitter 1
  primary), it requires $I(U; Y_1 \mid X_1) \le I(U; Y_2 \mid X_1)$ and
  $I(X_1; Y_1) \le I(X_1; Y_2)$ for all $p(u, x_1, x_2)$. The capacity region is
  $R_1 \le I(U, X_1; Y_1)$, $R_2 \le I(X_2; Y_2 \mid U, X_1)$. The Gaussian
  weak-interference analogue is due to Jovičić–Viswanath 2009 and
  Wu–Vishwanath–Arapostathis 2007; there dirty-paper coding plus beamforming is optimal.
  RTD (2011, arXiv v1 Thm VII.1) extend capacity to the larger "better cognitive
  decoding" regime $I(U, X_1; Y_1) \le I(U, X_1; Y_2)$ for all $p(u, x_1, x_2)$. That
  regime contains both the very weak and the very strong interference regimes.
- **Strong / very strong interference regimes**: Maric, Yates, and Kramer (2007) and
  Rini, Tuninetti, and Devroye (2011) established the capacity region under strong
  interference conditions where both receivers decode both messages or primary decodes
  the cognitive message.
- **Semi-deterministic cognitive IC**: Rini, Tuninetti, and Devroye (2011) resolved the
  capacity region when $Y_2$ is a deterministic function of $(X_1, X_2)$ (and several
  related deterministic/primary-decodes-cognitive classes).
- **General inner and outer bounds**: Rini, Tuninetti, and Devroye (2011) established the
  unified inner bound of their Theorem 7 (which specializes to Marton's inner bound when
  $X_1$ is degenerate and recovers every known solved class) together with a general
  outer bound; whether it is universally tight remains open. For the *frozen* RTD-type
  region these properties are verified separately in the attempt cited above. That
  attempt shows the frozen region contains the capacity region in the better cognitive
  decoding regime and in the semi-deterministic case, by explicit choices of auxiliaries.
- **Gaussian cognitive IC**: capacity is known to within a constant gap (1 bit/s/Hz,
  Rini–Tuninetti–Devroye 2012) across all channel parameters, and exactly in the weak
  and very strong interference regimes, while the general intermediate-interference
  Gaussian cognitive IC remains open.

## References

- N. Devroye, P. Mitran, and V. Tarokh, "Achievable rates in cognitive radio channels,"
  *IEEE Trans. Inf. Theory*, vol. 52, no. 5, pp. 1813–1827, 2006.
- W. Wu, S. Vishwanath, and A. Arapostathis, "Capacity of a class of cognitive radio
  channels: interference channels with degraded message sets," *IEEE Trans. Inf. Theory*,
  vol. 53, no. 11, pp. 4391–4399, 2007.
- I. Maric, R. D. Yates, and G. Kramer, "Capacity of interference channels with partial
  transmitter cooperation," *IEEE Trans. Inf. Theory*, vol. 53, no. 10, pp. 3536–3548,
  2007.
- A. Jovičić and P. Viswanath, "Cognitive radio: an information-theoretic perspective,"
  *IEEE Trans. Inf. Theory*, vol. 55, no. 9, pp. 3945–3958, 2009.
- S. Rini, D. Tuninetti, and N. Devroye, "New inner and outer bounds for the memoryless
  cognitive interference channel and some new capacity results," *IEEE Trans. Inf. Theory*,
  vol. 57, no. 7, pp. 4087–4109, 2011.
- S. Rini, D. Tuninetti, and N. Devroye, "Inner and outer bounds for the Gaussian cognitive
  interference channel and new capacity results," *IEEE Trans. Inf. Theory*, vol. 58,
  no. 2, pp. 820–848, 2012.
