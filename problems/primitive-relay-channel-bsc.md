---
id: primitive-relay-channel-bsc
title: Capacity of the Primitive Relay Channel with BSC Components
status: open
category: network-info-theory
posed_by: Thomas Cover
posed_year: 1987
tags: [network-information-theory, relay-channel, bsc, compress-and-forward]
lean_module: InfoTheory.Problems.PrimitiveRelayChannelBsc
lean_file: lean/InfoTheory/Problems/PrimitiveRelayChannelBsc.lean
---

## Statement

Consider the **primitive discrete memoryless relay channel with BSC components**: a source
transmits a binary codeword $X^n \in \{0, 1\}^n$ simultaneously over two conditionally
independent binary symmetric channels — $Y_i = X_i \oplus N_{1,i}$ with
$N_{1,i} \sim \mathrm{Bern}(p_1)$ to the destination and $Y_{r,i} = X_i \oplus N_{2,i}$ with
$N_{2,i} \sim \mathrm{Bern}(p_2)$ to the relay — where $p_1, p_2 \in (0, 1/2)$. The relay
communicates to the destination over an orthogonal noiseless bit-pipe of rate $R_0 \ge 0$
(sending an index in $\{1, \dots, \lfloor 2^{n R_0} \rfloor\}$ as a function of $Y_r^n$).

Let $C_{\mathrm{BSC}}(p_1, p_2, R_0)$ denote the operational capacity of this channel.
The two classical Cover–El Gamal achievable rates specialize to:
- **Partial decode-and-forward**:
  $$R_{\mathrm{PDF}}(p_1, p_2, R_0) = \sup_{p(u, x)} \min\!\big(I(X; Y) + R_0,\; I(U; Y_r) + I(X; Y \mid U)\big).$$
- **Compress-and-forward / noisy network coding**:
  $$R_{\mathrm{CF}}(p_1, p_2, R_0) = \sup_{p(x) p(u \mid y_r)} \min\!\big(I(X; Y, U),\; I(X; Y) + R_0 - I(U; Y_r \mid X, Y)\big).$$

Capacity is concave in $R_0$: the relay's index can be split between sub-blocks
coded at different pipe rates. So the natural benchmark is the **time-shared
(concavified) compress-and-forward rate**
$$\overline{R}_{\mathrm{CF}}(p, R_0) = \sup\Big\{\textstyle\sum_i w_i\, R_{\mathrm{CF}}(p, p, R_i) \;:\; w_i \ge 0,\ \sum_i w_i = 1,\ R_i \ge 0,\ \sum_i w_i R_i \le R_0\Big\}.$$

**Symmetric question (formalized in the accompanying Lean statement).** For
$p_1 = p_2 = p \in (0, 1/2)$ and every $R_0 \ge 0$, does
$$C_{\mathrm{BSC}}(p, p, R_0) = \overline{R}_{\mathrm{CF}}(p, R_0)\ ?$$

*Why this form.* An earlier version of this file asked whether
$C_{\mathrm{BSC}} = \max(R_{\mathrm{PDF}}, R_{\mathrm{CF}})$ for **all** $p_1, p_2, R_0$.
That question has a negative answer. For $p_2 < p_1$, time-sharing decode-and-forward
(at $R_0 = h(p_1) - h(p_2)$) with compress-and-forward (at $R_0 = h(p_1 \star p_2)$)
strictly beats both schemes just above the decode-and-forward corner. At
$(p_1, p_2, R_0) = (0.2, 0.1, 0.3)$, one gets $C \ge 0.53957 > 0.53101 \ge \max(R_{\mathrm{PDF}}, R_{\mathrm{CF}})$.
The upper bound on CF comes from a strong data-processing inequality
(`attempts/primitive-relay-channel-bsc/2026-11-26-claude-opus-5-5-time-sharing-and-first-order.md`).
In the symmetric case, $R_{\mathrm{PDF}}(p, p, R_0) \le 1 - h(p) = R_{\mathrm{CF}}(p, p, 0)$,
so partial decode-and-forward is redundant and the only remaining candidate is
time-shared CF. Numerically, uniform input and a BSC test channel are optimal for CF
in the symmetric case, which makes $R_{\mathrm{CF}}(p, p, \cdot)$ already concave. If so,
the time-sharing in $\overline{R}_{\mathrm{CF}}$ is harmless but vacuous. That has not
been proved. For asymmetric $p_1 \ne p_2$, the analogous open question would compare
$C$ with the upper concave envelope of $\max(R_{\mathrm{PDF}}, R_{\mathrm{CF}})$ in
$R_0$; it is not formalized here.

## Background

Posed in its Gaussian and binary symmetric forms by Cover (1987) and studied extensively
by Kim (2008), the primitive relay channel strips away interference between the source and
relay transmissions by placing the relay-to-destination link on an orthogonal noiseless
pipe of rate $R_0$. Because the destination-side channel has no interference, this model
isolates the fundamental tension between **cooperation** (relaying) and **distributed source
coding** (Wyner–Ziv compression of $Y_r^n$ with side information $Y^n$ at the destination).
Even for the symmetric case $p_1 = p_2 = p$ (where decode-and-forward offers no gain over
direct transmission $1 - h(p)$), the exact capacity for $0 < R_0 < h(p \star p)$ remains
open.

## What is known

- The cutset bound gives
  $C_{\mathrm{CS}}(p_1, p_2, R_0) = \min\!\big(I(X; Y, Y_r), I(X; Y) + R_0\big)$ evaluated at
  $X \sim \mathrm{Bern}(1/2)$.
- Capacity is known in two boundary regimes:
  1. When $p_2 \le p_1$ and $R_0 \le I(X; Y_r) - I(X; Y) = h(p_1) - h(p_2)$, decode-and-forward
     meets the cutset bound $1 - h(p_1) + R_0$.
  2. When $R_0 \ge H(Y_r \mid Y) = h(p_1 \star p_2)$, compress-and-forward (forwarding $Y_r$
     losslessly via Slepian–Wolf binning) meets the cutset bound $I(X; Y, Y_r)$.
- For symmetric components $p_1 = p_2 = p$, the cutset bound is known to be loose in the
  interior regime $0 < R_0 < h(p \star p)$. Wu, Özgür and Xie (2017) and Barnes, Wu and Özgür (2017) gave explicit
  beyond-cutset bounds by geometric (blowing-up, rearrangement) arguments.
  Liu and Özgür (2020) recovered and sharpened the Wu–Özgür bounds via reverse
  hypercontractivity. Barnes–Wu–Özgür answer Cover's 1987 question (the smallest $R_0$
  with $C(R_0) = C(\infty)$) for symmetric BSC components: according to their abstract
  and later citations, $C(R_0) < C(\infty)$ for every $R_0 < h(p \star p)$, so the
  critical rate is the compress-and-forward threshold $h(p \star p)$. The Gaussian
  analogue, where the critical rate is infinite, is Wu–Barnes–Özgür (2019).
- For $p_2 < p_1$, capacity strictly exceeds $\max(R_{\mathrm{PDF}}, R_{\mathrm{CF}})$
  for $R_0$ slightly above $h(p_1) - h(p_2)$. It also exceeds each scheme's own
  time-shared version, because time-sharing *across* schemes is needed. See the
  Statement section and the 2026-11-26 attempt; numerically, for $(0.2, 0.1)$ the gap
  reaches about 0.045 bits near $R_0 = 0.5$.
- **First order at $R_0 = 0$ (symmetric case).** $C(R_0)$ is concave, so
  $C'(0^+)$ exists. Compress-and-forward with uniform input has slope exactly
  $s_p = (1-2p)^2/(1+(1-2p)^2)$, so $s_p \le C'(0^+) \le 1$ (at $p = 0.1$: $[0.390, 1]$).
  The El Gamal–Gohari–Nair Theorem 6 bound has slope 1 at $R_0 = 0$, i.e. it improves
  on cutset only at second order (proved in the 2026-11-26 attempt; a sketch there
  gives the same for the Liu–Özgür bound). No converse checked so far narrows this
  first-order gap.
- El Gamal, Gohari, and Nair (2022) proved a strengthened single-letter converse that
  strictly improves the cutset bound for the primitive BSC relay channel (for example, at
  $p_1 = p_2 = 0.1, R_0 = 0.2$, certifying $C < 0.6496$ versus the cutset bound $0.7310$,
  while compress-and-forward achieves $\approx 0.6064$).
- Whether compress-and-forward (with optimal test channel $p(u \mid y_r)$) is tight for
  the symmetric primitive BSC relay channel remains open.

## References

- T. M. Cover, "The capacity of the relay channel," in *Open Problems in Communication and
  Computation* (T. M. Cover and B. Gopinath, eds.), Springer, 1987, pp. 72–73.
- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," *IEEE Trans.
  Inf. Theory*, vol. 25, no. 5, pp. 572–584, 1979.
- X. Wu, A. Özgür, and L.-L. Xie, "Improving on the cut-set bound via geometric analysis
  of typical sets," *IEEE Trans. Inf. Theory*, vol. 63, no. 4, 2017.
- L. P. Barnes, X. Wu, and A. Özgür, "A solution to Cover's problem for the binary
  symmetric relay channel: Geometry of sets on the Hamming sphere," *55th Allerton
  Conf.*, 2017, pp. 844–851.
- Y.-H. Kim, "Coding techniques for primitive relay channels," *45th Annual Allerton Conf.
  Commun., Control, Comput.*, 2007.
- X. Wu, L. P. Barnes, and A. Özgür, "'The capacity of the relay channel': solution to
  Cover's problem in the Gaussian case," *IEEE Trans. Inf. Theory*, vol. 65, no. 1,
  pp. 255–275, 2019.
- J. Liu and A. Özgür, "Capacity upper bounds for the relay channel via reverse
  hypercontractivity," *IEEE Trans. Inf. Theory*, vol. 66, no. 9, pp. 5448–5455, 2020.
- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the capacity
  of the relay channel and applications," *IEEE Trans. Inf. Theory*, vol. 68, no. 7,
  pp. 4247–4263, 2022.
