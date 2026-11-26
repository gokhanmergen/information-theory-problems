---
id: broadcast-channel-three-receivers
title: Capacity Region of the Three-Receiver Broadcast Channel
status: open
category: network-info-theory
posed_by: Thomas Cover
posed_year: 1972
tags: [network-information-theory, broadcast-channel, three-receivers, multiuser]
lean_module: InfoTheory.Problems.BroadcastChannelThreeReceivers
lean_file: lean/InfoTheory/Problems/BroadcastChannelThreeReceivers.lean
---

## Statement

A three-receiver discrete memoryless broadcast channel (3-DMBC) is a channel
$W : \mathcal{X} \to \mathcal{Y}_1 \times \mathcal{Y}_2 \times \mathcal{Y}_3$ specified
by transition probabilities $p(y_1, y_2, y_3 \mid x)$. A single transmitter sends three
independent private messages $(M_1, M_2, M_3)$ at rates $(R_1, R_2, R_3)$ so that receiver
$j \in \{1, 2, 3\}$ reliably decodes $M_j$ from $Y_j^n$.

The natural three-receiver extension of Marton's inner bound (via a common cloud center $W_0$
and multivariate covering over auxiliary random variables $(U_1, U_2, U_3)$ with
$(W_0, U_1, U_2, U_3) - X - (Y_1, Y_2, Y_3)$) consists of all nonnegative triples
$(R_1, R_2, R_3)$ admitting a rate split $R_j = R_{j0} + R_{j1}$ ($R_{j0}, R_{j1} \ge 0$)
and auxiliary covering rates $R'_1, R'_2, R'_3 \ge 0$ such that:
$$
\begin{aligned}
R_{10} + R_{20} + R_{30} &\le \min_{j \in \{1,2,3\}} I(W_0; Y_j), \\
R_{j1} + R'_j &\le I(U_j; Y_j \mid W_0) \quad (j = 1, 2, 3), \\
R'_i + R'_j &\ge I(U_i; U_j \mid W_0) \quad (1 \le i < j \le 3), \\
R'_1 + R'_2 + R'_3 &\ge H(U_1 \mid W_0) + H(U_2 \mid W_0) + H(U_3 \mid W_0)
  - H(U_1, U_2, U_3 \mid W_0).
\end{aligned}
$$

**Does this three-receiver Marton inner bound equal the exact capacity region
$\mathcal{C}_3(W)$ for every finite-alphabet three-receiver discrete memoryless broadcast
channel $W$?**

## Background

Moving from two receivers to three introduces genuinely new network phenomena that do not
appear in the two-receiver setting. Even for **degraded message sets** — where all three
receivers demand a common message $M_0$ and only receiver $1$ demands a private message
$M_1$ — Nair and El Gamal (2009) proved that the natural generalization of Körner–Marton
superposition coding is strictly suboptimal, and that **indirect decoding** (where a
receiver decodes a satellite codeword without being required to output its message) strictly
enlarges the achievable region. For three private messages, pairwise clouds
$(W_{12}, W_{13}, W_{23})$, indirect decoding, and structured coding may all interact,
making the three-receiver broadcast channel substantially harder than the two-receiver case.

## What is known

- The capacity region is known for three-receiver *degraded* broadcast channels
  (Bergmans 1973; Gallager 1974) and *Gaussian MIMO* broadcast channels
  (Weingarten–Steinberg–Shamai 2006).
- For three-receiver broadcast channels with degraded message sets $(M_0, M_1)$, Körner–Marton
  superposition is strictly suboptimal (Nair–El Gamal 2009); Nair and El Gamal established
  capacity for the case where $Y_1$ is less noisy than $Y_2$ or $Y_3$ and introduced the
  indirect-decoding inner bound, whose optimality in general remains open.
- For three-receiver *deterministic* broadcast channels (unlike the two-receiver case solved
  by Marton 1979 / Pinsker 1978), even the capacity region with common and private messages
  is open in general, though special cases (e.g., degraded message sets or two-message
  deterministic channels) have been resolved (Nair–El Gamal 2009; Borade–Zheng–Trott 2007).
- Multivariate covering (El Gamal–Kim 2011, Lemma 8.2) yields the Marton inner bound stated
  above; further extensions incorporating pairwise common clouds $(W_{12}, W_{13}, W_{23})$
  and indirect decoding have been studied by Nair–Wang (2011) and Gohari–Nair (2022), yet
  no matching converse is known.

## References

- T. M. Cover, "Broadcast channels," *IEEE Trans. Inf. Theory*, vol. 18, no. 1, pp. 2–14,
  1972.
- C. Nair and A. El Gamal, "The capacity region of a class of three-receiver broadcast
  channels with degraded message sets," *IEEE Trans. Inf. Theory*, vol. 55, no. 10,
  pp. 4479–4493, 2009.
- C. Nair and Z. V. Wang, "The capacity region of the three receiver less noisy broadcast
  channel," *IEEE Trans. Inf. Theory*, vol. 57, no. 7, pp. 4058–4062, 2011.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 8.
