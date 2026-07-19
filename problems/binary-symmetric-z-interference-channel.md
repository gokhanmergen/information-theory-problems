---
id: binary-symmetric-z-interference-channel
title: Capacity Region of the Binary Symmetric Z-Interference Channel
status: solved
posed_by: folklore
posed_year: 1980
tags: [channel-capacity, interference-channel, discrete-memoryless]
---

## Statement

Determine the exact capacity region $\mathcal{C}(p_1, p_2)$ of the two-user **Binary Symmetric Z-Interference Channel (BS-ZIC)** for all crossover probabilities $p_1, p_2 \in (0, 0.5)$.

The channel is defined by inputs $X_1, X_2 \in \{0,1\}$ and outputs:
$$Y_1 = X_1 \oplus X_2 \oplus N_1$$
$$Y_2 = X_2 \oplus N_2$$
where $N_1 \sim \operatorname{Bern}(p_1)$ and $N_2 \sim \operatorname{Bern}(p_2)$ are independent noise variables, and $\oplus$ denotes addition modulo 2. 

## Background

The Z-interference channel (also known as the one-sided interference channel) is a fundamental multi-user model where only one receiver (Receiver 1) experiences interference from the other user's transmitter. The binary symmetric case is the simplest noisy discrete memoryless instance of this model. This specialization is covered by classical interference-channel results once the two noise orderings are separated: the strong ordering uses the classical one-sided strong-interference argument, while the weak ordering has the same capacity region as Benzel's (1979) discrete additive degraded interference channel.

## What is known

- For the point-to-point links, the capacity of User 2's link in isolation is $1 - h(p_2)$, where $h(p) = -p \log_2 p - (1-p)\log_2(1-p)$ is the binary entropy function. The capacity of User 1's link in the absence of interference is $1 - h(p_1)$.
- In the limit of no noise ($p_1 = p_2 = 0$), the channel becomes a deterministic Z-interference channel, whose capacity region is a special case of the El Gamal–Costa (1982) capacity region for deterministic interference channels.
- When $p_1 \leq p_2$, Receiver 1's noise is less than or equal to Receiver 2's noise. In this regime, Receiver 1 can decode Receiver 2's message, and the capacity region is fully characterized: $\{R_1+R_2 \leq 1-h(p_1),\ R_2 \leq 1-h(p_2)\}$ (see attempts; reviewed). This is an instantiation of the classical strong-interference one-sided-IC machinery (Sato 1981; Costa–El Gamal 1987; El Gamal–Kim Ch. 6), so the regime should be considered essentially known.
- For $p_1 > p_2$ (the weak interference regime), relabeling users and writing $N_1\stackrel d=N_2\oplus Z$ gives the Z-channel form in Liu--Goldsmith (2009), which they state is capacity-region equivalent to Benzel's (1979) two-output discrete additive degraded interference channel. It is not literally Benzel's channel law: Benzel's reproduced model has both outputs equal to noisy versions of $X_1\oplus X_2$. The common capacity region equals the associated degraded BSC broadcast region: $R_2 \leq 1-h(p_2)$ and $R_1 \leq 1 - h(q \star h^{-1}(h(p_2) + R_2))$, where $q = (p_1-p_2)/(1-2p_2)$. Treating interference as noise with optimized input bias is optimal. The repository attempt gives a short independent MGL derivation; `2026-07-18-gpt-5-codex-audit-bs-zic.md` corrects the precise classical attribution.

- **Liu–Goldsmith containment, verified at the theorem level** (2026-07-19): with users
  relabeled to match their convention, the BS-ZIC satisfies both of their class
  conditions *exactly and in $n$-letter form* — Condition 1 ($H(Y_1^n \mid X_1^n = x_1^n)$
  independent of $x_1^n$ under any interfering input law) holds because conditioning
  makes $Y_1^n$ a bijective shift of $X_2^n \oplus N_1^n$; Condition 2 holds with
  $p^*(x_1) = \mathrm{Bern}(1/2)$, which makes $Y_1$ uniform ($\tau = 1$) irrespective
  of $p(x_2)$. Their capacity theorem therefore applies for **all** $(p_1, p_2)$, giving
  the region over $p(u)p(x_2|u)$, $X_1 \sim \mathrm{Bern}(1/2)$, $|\mathcal{U}| \leq 3$.
  Consistency: a degenerate $U$ reproduces the weak-regime TIN boundary; $U = X_2$
  reproduces the strong-regime polytope. The closed forms in this file thus evaluate
  Liu–Goldsmith's characterization, with the weak-regime closed form classical via
  the capacity-region equivalence to Benzel's (1979) channel that Liu–Goldsmith state
  (not literal membership in Benzel's class — see the audit attempt).

## References

- A. El Gamal and M. H. M. Costa, "The capacity region of a class of deterministic interference channels," IEEE Trans. Inf. Theory, 1982.
- R. Benzel, "The capacity region of a class of discrete additive degraded interference channels," IEEE Trans. Inf. Theory, 1979.
- N. Liu and S. Ulukus, "The capacity region of a class of discrete degraded interference channels," Allerton, 2006.
- N. Liu and A. J. Goldsmith, "Capacity regions and bounds for a class of Z-interference channels," IEEE Trans. Inf. Theory, 2009.
