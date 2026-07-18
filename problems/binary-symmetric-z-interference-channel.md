---
id: binary-symmetric-z-interference-channel
title: Capacity Region of the Binary Symmetric Z-Interference Channel
status: open
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

The Z-interference channel (also known as the one-sided interference channel) is a fundamental multi-user model where only one receiver (Receiver 1) experiences interference from the other user's transmitter. The binary symmetric case is the simplest noisy discrete memoryless instance of this model. While capacity results are well-known for Gaussian Z-interference channels and deterministic Z-interference channels, characterizing the exact capacity region for the binary symmetric case across all parameters remains an open problem.

## What is known

- For the point-to-point links, the capacity of User 2's link in isolation is $1 - h(p_2)$, where $h(p) = -p \log_2 p - (1-p)\log_2(1-p)$ is the binary entropy function. The capacity of User 1's link in the absence of interference is $1 - h(p_1)$.
- In the limit of no noise ($p_1 = p_2 = 0$), the channel becomes a deterministic Z-interference channel, whose capacity region is a special case of the El Gamal–Costa (1982) capacity region for deterministic interference channels.
- When $p_1 \leq p_2$, Receiver 1's noise is less than or equal to Receiver 2's noise. In this regime, Receiver 1 can decode Receiver 2's message, and the capacity region is fully characterized (see attempts).
- For $p_1 > p_2$, the channel exhibits very weak interference in some regimes. The general capacity region in this weak interference regime is open and the optimal trade-off involves public-private rate-splitting.

## References

- A. El Gamal and M. H. M. Costa, "The capacity region of a class of deterministic interference channels," IEEE Trans. Inf. Theory, 1982.
- N. Liu and A. J. Goldsmith, "Capacity of a class of Z-interference channels," IEEE Trans. Inf. Theory, 2009.
