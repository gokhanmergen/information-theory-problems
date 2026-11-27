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
Shannon proved that $\mathcal{G}_k(W) \subseteq \mathcal{C}_{\mathrm{TWC}}(W)$ for every $k$ and
$\mathcal{C}_{\mathrm{TWC}}(W) = \overline{\bigcup_{k=1}^\infty \mathcal{G}_k(W)}$. Concatenating
independent $k$-blocks gives the nesting $\mathcal{G}_k(W) \subseteq \mathcal{G}_{mk}(W)$. The
step-by-step chain $\mathcal{G}_k \subseteq \mathcal{G}_{k+1}$ is not automatic, and for
Blackwell's BMC the equal-rate point does not grow from $k=1$ to $k=2$ (see "What is known").

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
  channel (BMC). His unit-square coding schemes achieve the equal rates $0.61914$ (1982) and
  $0.63056$ (1983, bootstrapping), versus $\approx 0.61695$ bits for $\mathcal{G}_1$. These
  schemes use recursive subdivision with unbounded depth; they are not fixed-$k$ Shannon
  strategies. The best known equal rate is $0.63072$ (Schalkwijk–Meeuwissen–Bloemen 1995).
- **Equal-rate point of $\mathcal{G}_k$ for the BMC** (attempt
  `attempts/two-way-channel-capacity/2026-11-26-claude-opus-5-5-gk-audit-bmc-numerics.md`):
  $0.61695$ for $k=1$, and also $0.61695$ for $k=2$. For $k=2$ the reduction to a 4-variable
  inequality is proved and the inequality is checked numerically. For $k=3$ the value is
  $0.61964$, which beats both $\mathcal{G}_1$ and Schalkwijk's 1982 rate; the inclusion
  $\mathcal{G}_1 \subsetneq \mathcal{G}_3$ is certified in interval arithmetic. The $k=4$
  search was inconclusive. All these values are still about $0.011$ below the best known
  achievable rate.
- **Suboptimality of $\mathcal{G}_{\mathrm{out}}$**: Zhang, Berger, and Schalkwijk (1986)
  showed that $\mathcal{G}_{\mathrm{out}}(W)$ is strictly larger than
  $\mathcal{C}_{\mathrm{TWC}}(W)$ on Blackwell's BMC (equal rate $\le 0.64891$ vs.
  $\approx 0.69424$). Hekstra and Willems (1989) sharpened this to $\le 0.64628$ using the
  dependence-balance bound **with an adaptive parallel channel**. The plain dependence-balance
  bound coincides with Shannon's outer bound on the BMC.
- **Directed information**: Kramer (1998) reformulated the capacity region of general TWCs
  as a multi-letter limit of normalized directed information
  $\frac{1}{n} I(X_1^n \to Y_2^n \| X_2^n)$ and $\frac{1}{n} I(X_2^n \to Y_1^n \| X_1^n)$.
- **Single-letter extensions**: Han (1984) introduced a general single-letter coding scheme
  with auxiliary variables. Sabag and Permuter (Allerton 2018) gave a single-letter
  achievable region for common-output TWCs built on two auxiliary directed graphs. It reduces
  to Shannon's inner bound for single-node graphs and beats it on the BMC. No general
  finite-letter converse is known.
- **When adaptation is useless**: Weng, Song, Alajaji and Linder (2019) gave symmetry
  conditions under which Shannon's inner and outer bounds coincide, so $k=1$ suffices. Weng,
  Alajaji and Linder (arXiv:2004.03954) gave a simple outer bound that yields
  $\varepsilon$-approximations of the capacity region from the $\mathcal{G}_1$ computation.

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
- J. P. M. Schalkwijk, "On an extension of an achievable rate region for the binary
  multiplying channel," *IEEE Trans. Inf. Theory*, vol. 29, no. 3, pp. 445–448, 1983.
- Z. Zhang, T. Berger, and J. P. M. Schalkwijk, "New outer bounds to capacity regions of
  two-way channels," *IEEE Trans. Inf. Theory*, vol. 32, no. 3, pp. 383–386, 1986.
- A. H. A. Bloemen, *Discrete Coding Strategies for Two-Way Channels*, Ph.D. dissertation,
  Eindhoven University of Technology, 1996, doi:10.6100/IR463500.
- O. Sabag and H. H. Permuter, "An achievable rate region for the two-way channel with common
  output," *Proc. 56th Allerton Conf.*, pp. 527–531, 2018, doi:10.1109/ALLERTON.2018.8635930.
- J.-J. Weng, L. Song, F. Alajaji, and T. Linder, "Capacity of two-way channels with symmetry
  properties," *IEEE Trans. Inf. Theory*, vol. 65, no. 10, Oct. 2019.
- J.-J. Weng, F. Alajaji, and T. Linder, "A simple capacity outer bound for two-way channels
  and capacity approximation results," arXiv:2004.03954.
