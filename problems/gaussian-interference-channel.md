---
id: gaussian-interference-channel
title: Exact Capacity Region of the Two-User Gaussian Interference Channel
status: partially-solved
category: network-info-theory
posed_by: Ahlswede; Carleial
posed_year: 1974
tags: [network-information-theory, interference, gaussian]
lean_module: InfoTheory.Problems.GaussianInterferenceChannel
lean_file: lean/InfoTheory/Problems/GaussianInterferenceChannel.lean
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
- Corner points. Costa's "missing" corner point of the weak Gaussian Z-channel (the
  interfered user at its single-user capacity) was settled by Polyanskiy–Wu (IEEE Trans.
  Inf. Theory 62(7), 2016, via Wasserstein continuity of entropy). Rioul gave an
  alternative proof (arXiv:1607.02699, 2016). An I-MMSE proof by Bustin–Poor–Shamai
  (arXiv:1404.6690) carries an author-acknowledged error in its limit argument (arXiv v5
  comment). Sason (arXiv:1306.4934) bounds the corner points of the weak two-sided channel.
  The *slope* of the region at Costa's corner point is still open.
- Gaussian signaling inside Han–Kobayashi (HK).
  - Temporally correlated Gaussian inputs do not enlarge Gaussian HK (Nair–Ng, IEEE Trans.
    Inf. Theory 65(3), 2019).
  - Time-sharing between Gaussian HK schemes strictly helps (Costa, ITA 2011; Costa–Nair,
    ITA 2012).
  - Costa–Nair–Ng–Wang (ISIT 2020) conjectured an entropy inequality that would imply
    Gaussian optimality of HK for the Z-channel. Liu (arXiv:2209.00163, 2022) refuted it in
    some regimes and showed that Gaussian signaling is suboptimal for HK under *constant*
    power. The counterexamples do not reach HK with variable power control.
  - Costa–Gohari–Nair–Ng (ISIT 2023) proved Costa's noiseberg conjecture, which describes
    the Gaussian-signaling HK region with power control for the Z-channel, and refined the
    Gaussian-optimality conjecture. Whether Gaussian HK with time-sharing and power control
    equals capacity is open even for the Z-channel.
  - Non-Gaussian inputs are known to beat Gaussian ones only for weaker schemes: TIN with
    constant power (Abbe–Zheng 2012), and TIN without time-sharing using mixed inputs, which
    is constant-gap optimal (Dytso–Tuninetti–Devroye 2016).
  - Claimed full solutions are not accepted: Vaezi–Poor (arXiv:1509.02953) was withdrawn
    for a flawed outer bound, and Khandani's preprints (arXiv:2011.12981, arXiv:2501.14941)
    are unrefereed.
- Formalization note (2026-11). The frozen Lean statement compares capacity with the
  *convex hull* of Gaussian HK polytopes under power control, i.e. plain time-sharing.
  That set is strictly smaller than Gaussian HK with a coded time-sharing variable $Q$:
  at $a=b=1/2$, $P_1=P_2=100$, coded time-sharing achieves sum rate $3.9229$, while the
  convex hull is certified to stay at or below $3.8355$. So the Lean statement is false as
  written. A statement fix to the coded-time-sharing region is proposed; see
  `attempts/gaussian-interference-channel/2026-11-26-claude-opus-5-5-coded-time-sharing-catalog-error.md`.
  The mathematical problem, the exact region in the weak regime, remains open.

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
- A. S. Motahari and A. K. Khandani, "Capacity bounds for the Gaussian interference
  channel," IEEE Trans. Inf. Theory 55(2):620–643, 2009.
- Y. Polyanskiy and Y. Wu, "Wasserstein continuity of entropy and outer bounds for
  interference channels," IEEE Trans. Inf. Theory 62(7):3992–4002, 2016; arXiv:1504.04419.
- C. Nair and D. Ng, "Invariance of the Han–Kobayashi region with respect to
  temporally-correlated Gaussian inputs," IEEE Trans. Inf. Theory 65(3):1372–1374, 2019.
- M. Costa, C. Nair, D. Ng, and Y. N. Wang, "On the structure of certain non-convex
  functionals and the Gaussian Z-interference channel," ISIT 2020, pp. 1522–1527.
- J. Liu, "Stability of the Gaussian stationary point in the Han–Kobayashi region for
  Z-interference channels," arXiv:2209.00163, 2022.
- M. Costa, A. Gohari, C. Nair, and D. Ng, "A proof of the noiseberg conjecture for the
  Gaussian Z-interference channel," ISIT 2023.
- C. Nair, L. Xia, and M. Yazdanpanah, "Sub-optimality of Han–Kobayashi achievable region
  for interference channels," ISIT 2015, pp. 2416–2420; arXiv:1502.02589.
