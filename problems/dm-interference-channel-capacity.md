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

- **Solved special classes**:
  - Strong interference (Carleial 1975; Sato 1981; Han–Kobayashi 1981; Costa–El Gamal 1987).
  - Deterministic interference channels (El Gamal–Costa 1982).
  - Discrete additive degraded and Z-interference classes (Benzel 1979; Liu–Goldsmith 2009),
    including the binary symmetric Z-interference channel.
  - Injectively deterministic / semi-deterministic interference channels (Telatar–Tse 2007).
- **Compact Han–Kobayashi representation**: Chong, Motani, Garg, and El Gamal (2008) showed
  that the original Han–Kobayashi region (with four auxiliaries plus time-sharing) equals
  the seven-inequality region above using only $(Q, U_1, U_2)$.
- **Strict suboptimality of single-letter HK**: Nair, Xia, and Yazdanpanah (2015)
  constructed an explicit two-user DM-IC on which two-letter coding (or multi-letter
  Han–Kobayashi) strictly beats the single-letter Han–Kobayashi region, proving
  $\mathcal{R}_{\mathrm{HK}}^{(1)}(W) \subsetneq \mathcal{C}(W)$ in general.
- **Outer bounds**: Sato (1977), Carleial (1983), Kramer (2004), Etkin–Tse–Wang (2008),
  and Nair–Xia–Yazdanpanah provide progressively tighter outer bounds, none of which
  matches achievability for general DM-ICs.

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
  2015.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 6.
