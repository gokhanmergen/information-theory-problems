---
id: relay-channel
title: Capacity of the Relay Channel
status: open
posed_by: van der Meulen
posed_year: 1971
tags: [network-information-theory, relaying, cooperation]
---

## Statement

A relay channel $(\mathcal{X} \times \mathcal{X}_r,\; p(y, y_r \mid x, x_r),\;
\mathcal{Y} \times \mathcal{Y}_r)$ has a sender $X$, a receiver observing $Y$, and a
relay that observes $Y_r$ and transmits $X_r$ (causally, with $X_{r,i}$ a function of
$Y_r^{i-1}$) to help.

**Determine the capacity $C$ — a single-letter characterization — of the general
discrete memoryless relay channel.** The Gaussian case with fixed channel gains is
already open.

## Background

The three-node relay channel is the smallest network in which *cooperation* appears,
and it is the building block of every multi-hop and cooperative scheme in modern
wireless systems. Cover and El Gamal's 1979 paper introduced decode-and-forward and
compress-and-forward, the two strategies that (with their descendants, including noisy
network coding) still bracket what is achievable. That a three-node memoryless network
has unknown capacity after fifty years is the cleanest illustration of how hard network
information theory is.

## What is known

- Capacity is known for degraded and reversely degraded relay channels, and with
  feedback (Cover–El Gamal 1979); for semideterministic relay channels
  (El Gamal–Aref 1982); and for some classes with orthogonal components
  (El Gamal–Zahedi).
- The cutset bound (Cover–El Gamal) is the standard upper bound; it is **not tight in
  general** — Zhang (1988) showed a gap for a class of channels, and Wu–Özgür and
  Wu–Barnes–Özgür (2017–2019) developed new converse techniques (rooted in measure
  concentration / hypercontractivity) giving the first quantitative improvements on
  the cutset bound for the Gaussian relay channel, resolving a 1987 question of Cover
  about the "critical" relay rate.
- Best general achievability: combinations of partial decode-forward and
  compress-forward; noisy network coding (Lim–Kim–El Gamal–Chung 2011) recovers and
  extends compress-forward to networks. None matches the best known converses in
  general.
- Approximate capacity: for Gaussian relay networks, capacity is known within a
  constant gap (Avestimehr–Diggavi–Tse deterministic-model program).

## References

- E. C. van der Meulen, "Three-terminal communication channels," Adv. Appl.
  Probability, 1971.
- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," IEEE Trans.
  Inf. Theory, 1979.
- Z. Zhang, "Partial converse for a relay channel," IEEE Trans. Inf. Theory, 1988.
- A. S. Avestimehr, S. N. Diggavi, and D. N. C. Tse, "Wireless network information
  flow: a deterministic approach," IEEE Trans. Inf. Theory, 2011.
- X. Wu and A. Özgür, "Cover's open problem: the capacity of the relay channel,"
  Proc. Allerton Conf., 2015 (and journal developments 2017–2019).
