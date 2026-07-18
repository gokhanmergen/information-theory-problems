---
id: gaussian-interference-channel
title: Exact Capacity Region of the Two-User Gaussian Interference Channel
status: partially-solved
posed_by: Ahlswede; Carleial
posed_year: 1974
tags: [network-information-theory, interference, gaussian]
---

## Statement

Two senders, two receivers, cross-coupled by interference:
$$Y_1 = X_1 + a\,X_2 + Z_1, \qquad Y_2 = b\,X_1 + X_2 + Z_2,$$
with $Z_i \sim \mathcal{N}(0,1)$, average power constraints $P_1, P_2$, receiver $i$
decoding only sender $i$'s message.

**Determine the exact capacity region for all coupling coefficients $(a, b)$ and powers
$(P_1, P_2)$.**

## Background

Interference — not noise — is the binding constraint in wireless networks, and this
two-user channel is its atomic model. The problem has been open since the 1970s and has
generated an outsized share of the field's ideas: rate splitting (Carleial),
Han–Kobayashi superposition, and the modern "capacity to within one bit" program of
approximate capacity results. Everything about interference management in practice
descends from partial answers to this question.

## What is known

- Strong interference ($a, b$ large enough): solved — both receivers can decode both
  messages, region given by Han–Kobayashi and Sato (1981). Very strong interference:
  interference costs nothing (Carleial 1975).
- Best general inner bound: Han–Kobayashi (1981). It is not known whether it is tight
  in general; for the *discrete memoryless* interference channel the Han–Kobayashi
  bound is known to be strictly suboptimal for some channels (Nair–Xia–Yazdanpanah).
- Approximate capacity: the simple Han–Kobayashi scheme achieves within 1 bit of
  capacity for all parameters (Etkin–Tse–Wang 2008), and the generalized
  degrees-of-freedom region is fully characterized, including the famous "W" curve.
- Noisy/weak-interference regime: sum-capacity is known where treating interference as
  noise is optimal (Shang–Kramer–Chen, Motahari–Khandani, Annapureddy–Veeravalli,
  2008–2009).
- Corner points of the region (one user at its single-user capacity) have been settled
  in later work (Polyanskiy, Sason and others), but the full region for general weak
  interference remains open.

## References

- A. B. Carleial, "A case where interference does not reduce capacity," IEEE Trans.
  Inf. Theory, 1975.
- T. S. Han and K. Kobayashi, "A new achievable rate region for the interference
  channel," IEEE Trans. Inf. Theory, 1981.
- H. Sato, "The capacity of the Gaussian interference channel under strong
  interference," IEEE Trans. Inf. Theory, 1981.
- R. Etkin, D. Tse, and H. Wang, "Gaussian interference channel capacity to within one
  bit," IEEE Trans. Inf. Theory, 2008.
- V. S. Annapureddy and V. V. Veeravalli, "Gaussian interference networks: sum
  capacity in the low-interference regime," IEEE Trans. Inf. Theory, 2009.
