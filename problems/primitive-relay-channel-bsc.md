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

**Does $C_{\mathrm{BSC}}(p_1, p_2, R_0) = \max\!\big(R_{\mathrm{PDF}}(p_1, p_2, R_0), R_{\mathrm{CF}}(p_1, p_2, R_0)\big)$
for all $p_1, p_2 \in (0, 1/2)$ and $R_0 \ge 0$?**

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
- In the interior regime $0 < R_0 < h(p_1 \star p_2)$ (especially for $p_1 = p_2$), Wu,
  Barnes, and Özgür (2019) and Liu and Özgür (2018) used concentration of measure /
  reverse hypercontractivity to prove that the cutset bound is strictly loose, resolving
  Cover's 1987 question about whether $C(R_0)$ reaches $C(\infty)$ at finite $R_0$
  (for the BSC case, $C(R_0) = C(\infty)$ if and only if $R_0 \ge h(p_1 \star p_2)$,
  or even strictly below $C(\infty)$ for $R_0 < h(p_1 \star p_2)$).
- El Gamal, Gohari, and Nair (2022) proved a strengthened single-letter converse that
  strictly improves the cutset bound for the primitive BSC relay channel (for example, at
  $p_1 = p_2 = 0.1, R_0 = 0.2$, certifying $C < 0.6496$ versus the cutset bound $0.7310$,
  while compress-and-forward achieves $\approx 0.6064$).
- Whether compress-and-forward (with optimal test channel $p(u \mid y_r)$) is tight for
  the symmetric primitive BSC relay channel remains open.

## References

- T. M. Cover, "The capacity of the relay channel," in *Open Problems in Communication and
  Computation* (T. M. Cover and B. Gopinath, eds.), Springer, 1987, pp. 72–73.
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
