---
id: two-way-channel-capacity
title: Capacity Region of Shannon's Discrete Memoryless Two-Way Channel
status: open
category: network-info-theory
posed_by: Claude E. Shannon
posed_year: 1961
tags: [network-information-theory, two-way-channel, feedback, directed-information]
lean_module: InfoTheory.Problems.TwoWayChannelCapacity
lean_file: lean/InfoTheory/Problems/TwoWayChannelCapacity.lean
---

## Statement

A discrete memoryless two-way channel (TWC) is specified by a transition probability kernel
$W(y_1, y_2 \mid x_1, x_2)$ on finite alphabets
$\mathcal{X}_1 \times \mathcal{X}_2 \to \mathcal{Y}_1 \times \mathcal{Y}_2$. Terminal $1$
wishes to send message $M_1 \in \{1, \dots, 2^{n R_1}\}$ to Terminal $2$, and Terminal $2$
wishes to send an independent message $M_2 \in \{1, \dots, 2^{n R_2}\}$ to Terminal $1$,
using causal adaptive encoders $X_{1,i} = f_{1,i}(M_1, Y_1^{i-1})$ and
$X_{2,i} = f_{2,i}(M_2, Y_2^{i-1})$.

In his 1961 founding paper, Shannon introduced the **$k$-block strategy inner bound**
$\mathcal{G}_k(W)$: treating $k$-step causal coding strategies
$S_1 \in \prod_{i=0}^{k-1} (\mathcal{Y}_1^i \to \mathcal{X}_1)$ and
$S_2 \in \prod_{i=0}^{k-1} (\mathcal{Y}_2^i \to \mathcal{X}_2)$ as independent super-letter
inputs conditioned on a time-sharing variable $Q$,
$$
\mathcal{G}_k(W) = \bigcup_{p(q)\, p(s_1 \mid q)\, p(s_2 \mid q)}
\left\{ (R_1, R_2) \ge 0 :
R_1 \le \frac{1}{k} I(S_1; Y_2^k \mid S_2, Q),\;
R_2 \le \frac{1}{k} I(S_2; Y_1^k \mid S_1, Q) \right\}.
$$
Shannon proved that $\mathcal{G}_1(W) \subseteq \mathcal{G}_2(W) \subseteq \dots \subseteq \mathcal{C}_{\mathrm{TWC}}(W)$
and $\mathcal{C}_{\mathrm{TWC}}(W) = \overline{\bigcup_{k=1}^\infty \mathcal{G}_k(W)}$.

**Does every finite-alphabet discrete memoryless two-way channel $W$ achieve its exact
capacity region at some finite strategy horizon $k \ge 1$, i.e., does there exist $k \ge 1$
(depending on $W$) such that $\mathcal{C}_{\mathrm{TWC}}(W) = \mathcal{G}_k(W)$?**

## Background

Shannon's 1961 paper on the two-way channel launched network information theory itself —
preceding the broadcast channel, multiple-access channel, and relay channel by a decade.
Unlike point-to-point channels, feedback in a two-way channel allows the two terminals to
correlate their future inputs adaptively based on past outputs, so Shannon's single-letter
inner bound $\mathcal{G}_1(W)$ (product inputs) and outer bound (arbitrarily correlated
inputs) do not coincide in general. Despite more than sixty years of work — including
directed information, dependence-balance bounds, and interactive coding schemes — no
single-letter or finite-horizon computable characterization of $\mathcal{C}_{\mathrm{TWC}}(W)$
is known.

## What is known

- **Shannon's bounds (1961)**: $\mathcal{G}_1(W) \subseteq \mathcal{C}_{\mathrm{TWC}}(W) \subseteq \mathcal{G}_{\mathrm{out}}(W)$,
  where $\mathcal{G}_{\mathrm{out}}(W)$ allows arbitrary joint distributions $p(x_1, x_2)$.
  Both bounds coincide for several symmetric classes (e.g., additive-noise / modulo-sum
  two-way channels, Gaussian two-way channels).
- **Suboptimality of $\mathcal{G}_1$**: Schalkwijk (1982, 1983) proved that $\mathcal{G}_1(W)$
  is strictly smaller than $\mathcal{C}_{\mathrm{TWC}}(W)$ for Blackwell's binary multiplying
  channel (BMC), achieving $0.61914$ bits at $k = 2$ and $0.63056$ bits via progressive
  adaptive subdivision, versus $\approx 0.61695$ bits for $\mathcal{G}_1$.
- **Suboptimality of $\mathcal{G}_{\mathrm{out}}$**: Zhang, Berger, and Schalkwijk (1986)
  and Hekstra and Willems (1989) proved via dependence-balance outer bounds that
  $\mathcal{G}_{\mathrm{out}}(W)$ is strictly larger than $\mathcal{C}_{\mathrm{TWC}}(W)$
  on Blackwell's BMC ($\le 0.64628$ vs. $\approx 0.69424$ bits).
- **Directed information**: Kramer (1998) reformulated the capacity region of general TWCs
  as a multi-letter limit of normalized directed information
  $\frac{1}{n} I(X_1^n \to Y_2^n \| X_2^n)$ and $\frac{1}{n} I(X_2^n \to Y_1^n \| X_1^n)$.
- **Single-letter extensions**: Han (1984) introduced a general single-letter coding scheme
  with auxiliary variables, and Sabag–Permuter–Kashyap studied dynamic programming /
  Q-graph characterizations, yet no general finite-letter converse is known.

## References

- C. E. Shannon, "Two-way communication channels," *Proc. 4th Berkeley Symp. Math. Statist.
  Probab.*, vol. 1, pp. 611–644, 1961.
- J. P. M. Schalkwijk, "The binary multiplying channel — a coding scheme that operates
  beyond Shannon's inner bound region," *IEEE Trans. Inf. Theory*, vol. 28, no. 1,
  pp. 107–110, 1982.
- T. S. Han, "A general coding scheme for the two-way channel," *IEEE Trans. Inf. Theory*,
  vol. 30, no. 1, pp. 35–44, 1984.
- A. P. Hekstra and F. M. J. Willems, "Dependence balance bounds for single-output two-way
  channels," *IEEE Trans. Inf. Theory*, vol. 35, no. 1, pp. 44–53, 1989.
- G. Kramer, *Directed Information for Channels with Feedback*, Ph.D. dissertation, ETH
  Zurich, 1998.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 17.
