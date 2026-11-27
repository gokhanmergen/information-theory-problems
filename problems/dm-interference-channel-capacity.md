---
id: dm-interference-channel-capacity
title: Capacity Region of the General Discrete Memoryless Interference Channel
status: open
category: network-info-theory
posed_by: Rudolf Ahlswede
posed_year: 1974
tags: [network-information-theory, interference-channel, han-kobayashi, multiuser]
lean_module: InfoTheory.Problems.DmInterferenceChannelCapacity
lean_file: lean/InfoTheory/Problems/DmInterferenceChannelCapacity.lean
---

## Statement

A two-user discrete memoryless interference channel (DM-IC) is a channel
$W(y_1, y_2 \mid x_1, x_2)$ on finite alphabets
$\mathcal{X}_1 \times \mathcal{X}_2 \to \mathcal{Y}_1 \times \mathcal{Y}_2$. Sender $1$
transmits $M_1 \in \{1, \dots, 2^{n R_1}\}$ to receiver $1$, and sender $2$ independently
transmits $M_2 \in \{1, \dots, 2^{n R_2}\}$ to receiver $2$.

The **Han–Kobayashi inner bound** $\mathcal{R}_{\mathrm{HK}}(W)$ (Han–Kobayashi 1981;
simplified to an equivalent compact form by Chong–Motani–Garg–El Gamal 2008) consists of
all nonnegative rate pairs $(R_1, R_2)$ for which there exists a joint distribution
$p(q) p(u_1, x_1 \mid q) p(u_2, x_2 \mid q) W(y_1, y_2 \mid x_1, x_2)$ satisfying:
$$
\begin{aligned}
R_1 &\le I(X_1; Y_1 \mid U_2, Q), \\
R_2 &\le I(X_2; Y_2 \mid U_1, Q), \\
R_1 + R_2 &\le I(X_1, U_2; Y_1 \mid Q) + I(X_2; Y_2 \mid U_1, U_2, Q), \\
R_1 + R_2 &\le I(X_1; Y_1 \mid U_1, U_2, Q) + I(X_2, U_1; Y_2 \mid Q), \\
R_1 + R_2 &\le I(X_1, U_2; Y_1 \mid U_1, Q) + I(X_2, U_1; Y_2 \mid U_2, Q), \\
2 R_1 + R_2 &\le I(X_1, U_2; Y_1 \mid Q) + I(X_1; Y_1 \mid U_1, U_2, Q) + I(X_2, U_1; Y_2 \mid U_2, Q), \\
R_1 + 2 R_2 &\le I(X_2, U_1; Y_2 \mid Q) + I(X_2; Y_2 \mid U_1, U_2, Q) + I(X_1, U_2; Y_1 \mid U_1, Q).
\end{aligned}
$$
Because Nair, Xia, and Yazdanpanah (2015) proved that single-letter $\mathcal{R}_{\mathrm{HK}}(W)$
is strictly suboptimal for some DM-ICs, consider the **$k$-letter Han–Kobayashi hierarchy**
$\mathcal{R}_{\mathrm{HK}}^{(k)}(W) = \frac{1}{k} \mathcal{R}_{\mathrm{HK}}(W^{\otimes k})$,
whose closure as $k \to \infty$ equals the exact capacity region $\mathcal{C}(W)$.

**Does every finite-alphabet two-user DM-IC $W$ achieve its exact capacity region at some
finite blocklength $k \ge 1$, i.e., does there exist $k \ge 1$ such that
$\mathcal{C}(W) = \mathcal{R}_{\mathrm{HK}}^{(k)}(W)$?**

## Background

Introduced by Shannon (1961) and formally analyzed by Ahlswede (1974) and Carleial (1978),
the two-user discrete memoryless interference channel models two competing communication
links sharing a common medium without transmitter or receiver cooperation. For over three
decades, the Han–Kobayashi (1981) superposition-and-rate-splitting region was conjectured
to be tight for all DM-ICs. The 2015 discovery by Nair, Xia, and Yazdanpanah that
single-letter Han–Kobayashi can be strictly outperformed on a discrete memoryless channel
shattered that hope and showed that a general single-letter characterization — if one
exists at all — must go beyond Han–Kobayashi rate splitting.

## What is known

- **Solved special classes** (for the strong-interference and El Gamal–Costa classes the
  capacity region is the single-letter HK region, so the frozen statement holds there with
  $k = 1$; for the BS-ZIC the optimal schemes are TIN or $U_2 = X_2$, again special cases of
  HK):
  - Strong interference: Carleial (1975) and Sato (1981) for the Gaussian case; for DM-ICs,
    Costa–El Gamal (1987), whose region is HK with $U_j = X_j$.
  - A class of *deterministic* ICs satisfying an injectivity condition (El Gamal–Costa 1982).
    This does not cover general deterministic ICs.
  - Discrete additive degraded and Z-interference classes (Benzel 1979; Liu–Goldsmith 2009),
    including the binary symmetric Z-interference channel.
- **Compact Han–Kobayashi representation**: Chong, Motani, Garg, and El Gamal (2008) showed
  that the original Han–Kobayashi region (with four auxiliaries plus time-sharing) equals
  the seven-inequality region above using only $(Q, U_1, U_2)$.
- **Strict suboptimality of single-letter HK**: Nair, Xia, and Yazdanpanah (2015) studied
  *clean-Z-interference* (CZI) channels ($Y_2 = X_2$). For these they proved that HK, and
  indeed treating interference as noise, is optimal for $\max(\lambda R_1 + R_2)$ when
  $\lambda \le 1$. For $\lambda > 1$ they exhibited binary CZI channels on which a two-letter
  treating-interference-as-noise point of $\mathcal{R}_{\mathrm{HK}}^{(2)}(W)$ strictly beats
  $\max_{\mathcal{R}_{\mathrm{HK}}^{(1)}}(\lambda R_1 + R_2)$. Hence
  $\mathcal{R}_{\mathrm{HK}}^{(1)}(W) \subsetneq \mathcal{R}_{\mathrm{HK}}^{(2)}(W) \subseteq
  \mathcal{C}(W)$, so the frozen statement needs $k \ge 2$ for such $W$. Their rigorous
  argument covers one example ($\lambda = 2$: $1.107577$ vs $1.1080356$), with one
  "tedious" concavity step left unshown. A computer-assisted interval-arithmetic
  certificate for that example ($\max_{\mathcal{R}^{(1)}_{\mathrm{HK}}}(2R_1+R_2) \le
  1.1080300$) is in `attempts/dm-interference-channel-capacity/`. The same attempt gives an
  explicit three-letter scheme ($X_1^3$ a repetition code, $X_2^3 \ne 000$) with
  $2R_1+R_2 = 1.1102046$. Hence $\mathcal{R}_{\mathrm{HK}}^{(1)} \subsetneq
  \mathcal{R}_{\mathrm{HK}}^{(3)}$ with margin $2.2\cdot 10^{-3}$ for that channel.
- **Multi-letter HK.** $\mathcal{R}_{\mathrm{HK}}^{(k)} \subseteq \mathcal{R}_{\mathrm{HK}}^{(mk)}$
  (product distributions), and by Fano's inequality (with $U_1, U_2, Q$ constant)
  $\overline{\bigcup_k \mathcal{R}_{\mathrm{HK}}^{(k)}} = \mathcal{C}$. For the Gaussian IC,
  Nair–Ng (2019) proved that the $k$-letter HK region with temporally correlated Gaussian
  inputs equals the single-letter Gaussian-input HK region for every $k$. We found no result
  on whether the $k$-letter HK hierarchy stabilises at a finite $k$ for every DM-IC. That is
  exactly the frozen question.
- **Outer bounds**: for DM-ICs, Sato (1977), Carleial (1983), Telatar–Tse (2007), and
  Gohari–Nair (2022, auxiliary-receiver approach). Telatar–Tse give an outer bound for
  injective *semi-deterministic* ICs that recovers El Gamal–Costa and is within a bounded gap
  of HK; it is not a capacity result. Kramer (2004) and Etkin–Tse–Wang (2008) are
  Gaussian-specific. None of these matches achievability for general DM-ICs.

## References

- R. Ahlswede, "The capacity region of a channel with two senders and two receivers,"
  *Ann. Probab.*, vol. 2, no. 5, pp. 805–814, 1974.
- A. B. Carleial, "Interference channels," *IEEE Trans. Inf. Theory*, vol. 24, no. 1,
  pp. 60–70, 1978.
- T. S. Han and K. Kobayashi, "A new achievable rate region for the interference channel,"
  *IEEE Trans. Inf. Theory*, vol. 27, no. 1, pp. 49–60, 1981.
- A. El Gamal and M. H. M. Costa, "The capacity region of a class of deterministic
  interference channels," *IEEE Trans. Inf. Theory*, vol. 28, no. 2, pp. 343–346, 1982.
- H.-F. Chong, M. Motani, H. K. Garg, and H. El Gamal, "On the Han–Kobayashi region for
  the interference channel," *IEEE Trans. Inf. Theory*, vol. 54, no. 7, pp. 3188–3195,
  2008.
- C. Nair, L. Xia, and M. Yazdanpanah, "Sub-optimality of Han–Kobayashi achievable region
  for interference channels," *Proc. IEEE Int. Symp. Inf. Theory (ISIT)*, pp. 2416–2420,
  2015 (doi:10.1109/ISIT.2015.7282889; arXiv:1502.02589).
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 6.
- M. H. M. Costa and A. El Gamal, "The capacity region of the discrete memoryless
  interference channel with strong interference," *IEEE Trans. Inf. Theory*, vol. 33, no. 5,
  pp. 710–711, 1987.
- A. B. Carleial, "Outer bounds on the capacity of interference channels," *IEEE Trans. Inf.
  Theory*, vol. 29, no. 4, pp. 602–606, 1983.
- E. Telatar and D. Tse, "Bounds on the capacity region of a class of interference
  channels," *Proc. IEEE ISIT*, pp. 2871–2874, 2007.
- C. Nair and D. Ng, "Invariance of the Han–Kobayashi region with respect to
  temporally-correlated Gaussian inputs," *IEEE Trans. Inf. Theory*, vol. 65, no. 3,
  pp. 1372–1374, 2019.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
