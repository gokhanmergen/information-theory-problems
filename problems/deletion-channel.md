---
id: deletion-channel
title: Capacity of the Binary Deletion Channel
status: open
posed_by: folklore since Dobrushin
posed_year: 1967
tags: [channel-capacity, synchronization]
---

## Statement

Fix $d \in (0,1)$. The binary deletion channel takes an input string $x \in \{0,1\}^n$
and deletes each bit independently with probability $d$; the output is the concatenation
of the surviving bits, **with no indication of which positions were deleted**.
Dobrushin showed the Shannon capacity $C(d)$ exists for such synchronization channels.

**Determine $C(d)$ — or even a closed-form expression, a single-letter
characterization, or matching upper and lower bounds — for any $d \in (0,1)$.**

## Background

The deletion channel is the simplest channel with synchronization errors, and it is the
canonical embarrassment of channel coding: half a century after Shannon-type arguments
settled memoryless channels, the capacity of this innocent-looking channel is unknown
for every single deletion probability. The difficulty is that the channel has memory in
an essential way — the receiver does not know which positions survived — so the usual
single-letter techniques fail. The problem connects to trace reconstruction, DNA storage,
and edit-distance codes. A formula for $C(d)$ — even a variational, multi-letter but
computable one — or an exact answer at any interior $d$ would count as a solution.

## What is known

- Rubinstein–Con (2023), refining the run-length-distribution construction of
  Mitzenmacher–Drinea and Kirsch–Drinea, proved
  $C(d)>0.1221(1-d)$. In particular capacity is positive for every $d<1$.
- As $d \to 0$: $C(d) = 1 + d\log d - O(d)$ with explicit expansion terms
  (Kanoria–Montanari 2013); the channel behaves like an erasure channel to first order
  but the correction terms differ.
- As $d \to 1$: capacity is $\Theta(1-d)$. Current explicit bounds include
  $C(d)>0.1221(1-d)$ and, for every $d\geq0.68$,
  $C(d)<0.3745(1-d)$ (Rubinstein–Con 2023). A substantial constant-factor gap
  remains.
- Numerical upper bounds for intermediate $d$ via convex programming and channel
  comparison (Fertonani–Duman 2010; Cheraghchi 2019, who also gave the elegant bound
  family via "mean-limited" channels).
- Mitzenmacher's 2009 survey remains the standard entry point; the gap between upper
  and lower bounds is still wide at moderate $d$ (e.g. at $d = 0.5$).

## References

- R. L. Dobrushin, "Shannon's theorems for channels with synchronization errors,"
  Problems of Information Transmission, 1967.
- E. Drinea and M. Mitzenmacher, "On the capacity of channels with deletions,"
  IEEE Trans. Inf. Theory, 2006/2007.
- M. Mitzenmacher, "A survey of results for deletion channels and related
  synchronization channels," Probability Surveys, 2009.
- D. Fertonani and T. M. Duman, "Novel bounds on the capacity of the binary deletion
  channel," IEEE Trans. Inf. Theory, 2010.
- Y. Kanoria and A. Montanari, "Optimal coding for the binary deletion channel with
  small deletion probability," IEEE Trans. Inf. Theory, 2013.
- M. Cheraghchi, "Capacity upper bounds for deletion-type channels," J. ACM, 2019.
- I. Rubinstein and R. Con, "Improved upper and lower bounds on the capacity of the
  binary deletion channel," arXiv:2305.07156, 2023.
