---
id: zero-error-feedback-variable-length
title: Constant Additive Overhead for Zero-Error Variable-Length Feedback Coding
status: open
category: zero-error
posed_by: Mikhail V. Burnashev; Yury Polyanskiy, H. Vincent Poor, Sergio Verdú
posed_year: 2011
tags: [zero-error, feedback, variable-length, non-asymptotic, burnashev]
lean_module: InfoTheory.Problems.ZeroErrorFeedbackVariableLength
lean_file: lean/InfoTheory/Problems/ZeroErrorFeedbackVariableLength.lean
---

## Statement

Consider a discrete memoryless channel (DMC) $W(y \mid x)$ over finite alphabets
$\mathcal{X}, \mathcal{Y}$ with positive Shannon capacity $C(W) > 0$. Suppose $W$ admits
zero-error confirmation, meaning there exist inputs $x_1, x_2 \in \mathcal{X}$ and an output
$y \in \mathcal{Y}$ such that $W(y \mid x_1) > 0$ and $W(y \mid x_2) = 0$ (which is necessary
and sufficient for the zero-error variable-length feedback capacity to equal $C(W)$).

For $M \ge 2$ equiprobable messages, let $N_0^*(W, M)$ denote the minimum expected stopping
time $\mathbb{E}[\tau]$ over all causal **zero-error variable-length feedback (VLF)** codes
with noiseless output feedback (where the decoder stops at a causal stopping time $\tau$
adapted to $Y_1, Y_2, \dots$ and recovers the transmitted message $m$ with zero error on every
reachable stopping trajectory). By Wald's identity and zero-error Fano,
$$N_0^*(W, M) \ge \frac{\log_2 M}{C(W)} .$$

**Does every such DMC $W$ admit zero-error VLF codes with constant ($O(1)$) additive overhead
over $\frac{\log_2 M}{C(W)}$?** Equivalently, does there exist a constant $C_0(W) < \infty$
(depending only on $W$) such that for all $M \ge 2$,
$$N_0^*(W, M) \le \frac{\log_2 M}{C(W)} + C_0(W) ?$$

## Background

In fixed-length block coding without feedback, zero-error capacity $C_0(W)$ can be strictly
smaller than Shannon capacity $C(W)$ — or even $0$, as on the binary erasure channel
$\mathrm{BEC}(\varepsilon)$ and the binary Z-channel. Even with noiseless feedback under
fixed-length coding, Shannon's (1956) zero-error feedback capacity $C_{0,f}(W)$ remains $0$
whenever $C_0(W) = 0$.

Allowing **variable-length** transmission with noiseless feedback dramatically transforms the
picture: whenever $W$ has at least one zero transition probability $W(y \mid x_2) = 0 < W(y \mid x_1)$,
a two-slot confirmation trick (`(x_1, x_2)` vs. `(x_2, x_1)`) provides a zero-error ACK/NACK
in finite expected time, lifting the asymptotic zero-error VLF capacity all the way to the
ordinary Shannon capacity $C(W)$ (Burnashev 1976; Yamamoto–Itoh 1979; Polyanskiy–Poor–Verdú
2011).

In the non-asymptotic regime, Polyanskiy, Poor, and Verdú (2011) proved that for any fixed
target error probability $\varepsilon > 0$, VLF codes eliminate channel dispersion completely
and achieve $N^*(W, M, \varepsilon) = \frac{(1 - \varepsilon)\log_2 M}{C(W)} + O(1)$. On
$\mathrm{BEC}(\varepsilon)$, simple symbol-by-symbol ARQ achieves zero error with $O(1)$
additive overhead. For general zero-error-confirmable DMCs (such as the binary Z-channel,
where $C_0(W) = C_{0,f}(W) = 0$ yet $C_{0,\mathrm{vlf}}(W) = C(W)$), standard two-phase
VLF-plus-ACK/NACK schemes incur an $O(\log \log M)$ additive penalty, and whether $O(1)$
overhead is universally achievable with strict zero error remains open.

## What is known

- **First-order asymptotics:** Whenever $\exists x_1, x_2, y$ with $W(y \mid x_1) > 0$ and
  $W(y \mid x_2) = 0$, the zero-error VLF capacity equals $C(W)$ (Burnashev 1976;
  Polyanskiy–Poor–Verdú 2011); otherwise no zero-error VLF code exists for $M \ge 2$.
- **Converse:** $N_0^*(W, M) \ge \frac{\log_2 M}{C(W)}$ for all $M \ge 1$.
- **Binary erasure channel:** For $\mathrm{BEC}(\varepsilon)$ ($0 < \varepsilon < 1$),
  retransmission ARQ achieves $N_0^*(\mathrm{BEC}(\varepsilon), M) \le \frac{\log_2 M}{1 - \varepsilon} + \frac{1}{1 - \varepsilon}$,
  matching the converse up to an $O(1)$ constant.
- **General confirmable DMCs:** Two-phase schemes combining Polyanskiy–Poor–Verdú VLF codes
  (with $\varepsilon = 1 / \log_2 M$) and zero-error ACK/NACK confirmation achieve
  $N_0^*(W, M) \le \frac{\log_2 M}{C(W)} + O(\log \log M)$, while closing the gap between
  $O(1)$ and $O(\log \log M)$ remains open even for the binary Z-channel.

## References

- C. E. Shannon, "The zero error capacity of a noisy channel,"
  IRE Trans. Inf. Theory, 1956.
- M. V. Burnashev, "Data transmission over a discrete channel with feedback. Random
  transmission time," Probl. Peredachi Inf., 1976.
- Y. Polyanskiy, H. V. Poor, and S. Verdú, "Feedback in the non-asymptotic regime,"
  IEEE Trans. Inf. Theory, 2011.
- A. R. Williamson, T.-Y. Chen, and R. D. Wesel, "Variable-length convolutional coding for
  short blocklengths with decision feedback," IEEE Trans. Commun., 2015.
- B. Nakiboğlu and L. Zheng, "Errors-and-erasures decoding for block codes with feedback,"
  IEEE Trans. Inf. Theory, 2012.
