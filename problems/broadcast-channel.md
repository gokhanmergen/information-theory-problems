---
id: broadcast-channel
title: Capacity Region of the General Two-Receiver Broadcast Channel
status: open
posed_by: Thomas Cover
posed_year: 1972
tags: [network-information-theory, multiuser]
---

## Statement

A two-receiver discrete memoryless broadcast channel is a triple
$(\mathcal{X}, p(y_1, y_2 \mid x), \mathcal{Y}_1 \times \mathcal{Y}_2)$: one sender
encodes two independent messages $M_1, M_2$ into a common input $X^n$, and receiver
$i$ must decode $M_i$ from $Y_i^n$.

**Determine the capacity region — a single-letter (computable) characterization of the
set of achievable rate pairs $(R_1, R_2)$ — for a general $p(y_1, y_2 \mid x)$.**

## Background

Posed by Cover in his 1972 paper that founded the subject, this is the oldest open
problem of network information theory and in a real sense *the* open problem of the
field: the broadcast channel is the simplest one-to-many setting, superposition coding
was invented for it, and dirty-paper coding — the basis of MIMO downlink transmission —
came out of its Gaussian special case. Yet the general region has been open for over
fifty years.

## What is known

- Solved for degraded channels (Bergmans achievability; Gallager / Ahlswede–Körner
  converse), and more generally for less-noisy and more-capable orderings (Körner–Marton,
  El Gamal).
- Solved when one message is required by both receivers in various senses (degraded
  message sets, Körner–Marton 1977).
- The Gaussian MIMO broadcast channel is solved: dirty-paper coding is optimal
  (Weingarten–Steinberg–Shamai 2006).
- Best general inner bound: Marton (1979). The Nair–El Gamal (2007) "UV outer bound"
  was long the best outer bound; Gohari–Nair (2022) strictly improved it via the
  auxiliary-receiver approach. The bounds coincide for every class where capacity is
  known, and Marton's bound is not known to be suboptimal for any channel — whether
  Marton's inner bound is the capacity region is itself a major open question.
- The canonical separating example is the **binary skew-symmetric channel**: Marton's
  sum rate is exactly $0.3616428$ bits (randomized time division, proven optimal
  within the inner bound by the Nair–Wang–Geng inequality for all binary-input
  channels), while the UV outer bound evaluates to $\approx 0.37256$ bits — the
  tightness question is, on this channel, a concrete $0.011$-bit window (see attempt
  log for reproducible evaluations).
- With only private messages, cardinality-bounded evaluation of Marton's bound is
  itself nontrivial (Gohari–Anantharam 2012).

## References

- T. M. Cover, "Broadcast channels," IEEE Trans. Inf. Theory, 1972.
- P. Bergmans, "Random coding theorem for broadcast channels with degraded
  components," IEEE Trans. Inf. Theory, 1973.
- K. Marton, "A coding theorem for the discrete memoryless broadcast channel,"
  IEEE Trans. Inf. Theory, 1979.
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the broadcast
  channel," IEEE Trans. Inf. Theory, 2007.
- C. Nair, Z. V. Wang, and Y. Geng, "An information inequality and evaluation of
  Marton's inner bound for binary input broadcast channels," arXiv:1001.1468.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," IEEE Trans. Inf. Theory, 2022.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011
  (Chs. 5, 8–9).
