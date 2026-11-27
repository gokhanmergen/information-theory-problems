---
id: mac-with-feedback
title: Capacity Region of the Multiple-Access Channel with Noiseless Feedback
status: open
category: network-info-theory
posed_by: N. Thomas Gaarder and Jack Keil Wolf
posed_year: 1975
tags: [network-information-theory, mac, feedback, directed-information]
lean_module: InfoTheory.Problems.MacWithFeedback
lean_file: lean/InfoTheory/Problems/MacWithFeedback.lean
---

## Statement

Consider a two-user discrete memoryless multiple-access channel (DM-MAC)
$W(y \mid x_1, x_2)$ on finite alphabets $\mathcal{X}_1 \times \mathcal{X}_2 \to \mathcal{Y}$
with noiseless causal output feedback to both encoders: at time $i$, transmitter $j \in \{1, 2\}$
selects $X_{j,i} = f_{j,i}(M_j, Y^{i-1})$ and the receiver decodes $(M_1, M_2)$ from $Y^n$.

Generalizing the Cover–Leung (1981) block-Markov superposition scheme to $k$-step causal
feedback strategies $S_j \in \prod_{i=0}^{k-1} (\mathcal{Y}^i \to \mathcal{X}_j)$, define
the **$k$-letter Cover–Leung inner bound** $\mathcal{R}_{\mathrm{CL}}^{(k)}(W)$ as the set
of all nonnegative rate pairs $(R_1, R_2)$ for which there exist a finite auxiliary $U$ and
conditionally independent strategy distributions $p(u) p(s_1 \mid u) p(s_2 \mid u)$ satisfying:
$$
\begin{aligned}
R_1 &\le \frac{1}{k} I(S_1; Y^k \mid S_2, U), \\
R_2 &\le \frac{1}{k} I(S_2; Y^k \mid S_1, U), \\
R_1 + R_2 &\le \frac{1}{k} I(S_1, S_2; Y^k).
\end{aligned}
$$
For $k = 1$, $\mathcal{R}_{\mathrm{CL}}^{(1)}(W)$ is precisely the Cover–Leung region, and
$\overline{\bigcup_{k=1}^\infty \mathcal{R}_{\mathrm{CL}}^{(k)}(W)} = \mathcal{C}_{\mathrm{MAC-FB}}(W)$
(Kramer 1998; the inclusion "$\supseteq$" also follows directly from Fano's inequality with
$U$ constant). $\mathcal{R}_{\mathrm{CL}}^{(k)}$ contains Kramer's *generalized Cover–Leung
region* with $M = k$ (Kramer 1998, §§5.3–5.4, written there with directed information; see
Venkataramanan–Pradhan 2011, §IV-B, Fact 2). In that restatement $U_1, \dots, U_M$ are i.i.d.
and the $i$-th inputs see $U_i$ but no other $U_j$, whereas here one $U$ serves the whole block, so
equality of the two regions has not been checked. The regions are nested along divisibility,
$\mathcal{R}_{\mathrm{CL}}^{(k)} \subseteq \mathcal{R}_{\mathrm{CL}}^{(mk)}$, so the
non-monotonicity in $k$ is harmless for the question below.

**Does every finite-alphabet two-user DM-MAC $W$ achieve its exact feedback capacity region
$\mathcal{C}_{\mathrm{MAC-FB}}(W)$ at some finite strategy horizon $k \ge 1$?**

## Background

In 1975, Gaarder and Wolf made the landmark discovery that — in sharp contrast to Shannon's
theorem for point-to-point memoryless channels — noiseless output feedback strictly
enlarges the capacity region of a discrete memoryless multiple-access channel (specifically
the binary erasure MAC), because feedback enables the two geographically separated
encoders to observe each other's interference and cooperatively resolve collisions in
subsequent rounds. While the capacity region is known for the Gaussian MAC with feedback
(Ozarow 1984) and for certain deterministic/semi-deterministic classes (Willems 1982), a
computable single-letter (or finite-letter) characterization for general DM-MACs remains
open after half a century.

## What is known

- **Without feedback**: the capacity region is completely solved by the Ahlswede–Liao
  single-letter formula (1971/1972).
- **Cover–Leung region (1981)**: $\mathcal{R}_{\mathrm{CL}}^{(1)}(W)$ uses block-Markov
  encoding to build cooperation through feedback. Willems (1982) proved that Cover–Leung
  is **tight** for the class of DM-MACs in which one input is a deterministic function of
  the output and the other input (including the binary adder channel $Y = X_1 + X_2$).
- **Gaussian MAC with feedback**: Ozarow (1984) determined the exact capacity region using
  a two-user extension of the Schalkwijk–Kailath linear feedback scheme, showing that
  Cover–Leung is strictly suboptimal in the Gaussian setting.
- **Suboptimality of Cover–Leung for general DM-MACs**: Bross and Lapidoth (2005) gave a
  region containing Cover–Leung (two-way exchange phase appended to each block) and evaluated
  it on the Poisson MAC via a binary DM-MAC ($P(Y{=}1|00)=0$, $P(Y{=}1|01)=P(Y{=}1|10)=q$,
  $P(Y{=}1|11)=2q$). Venkataramanan and Pradhan (2011) gave a single-letter region strictly
  containing Cover–Leung. Their numerical comparisons are on the AWGN MAC and on the same
  binary MAC as $q \to 0$ ($0.4994q$ vs $0.5132q$ nats symmetric sum-rate), and they report a
  likely calculation error in Bross–Lapidoth's number for that example (VP §IV-C). Earlier,
  Kramer (1998; 2003) gave the first improvement over Cover–Leung for a DM-MAC, using code trees
  on the binary additive noisy MAC $Y = X_1 + X_2 + N$, $N \sim \mathrm{Bern}(1/2)$: symmetric
  rate $0.43879$ vs Cover–Leung's $0.43621$ (as reported by Tandon–Ulukus 2009, who also
  evaluate that channel's Cover–Leung region analytically).
- **Finite-$k$ hierarchy**: Kramer's thesis evaluated the generalized CL region for $M = 2$ on
  a few examples. For the AWGN MAC at SNR 10 the equal-rate point is $1.2566$ (vs CL
  $1.2470$, VP $1.2709$, Ozarow capacity $1.2847$, as reported in VP §IV). That channel is not
  finite-alphabet. We know of no published result settling whether
  $\mathcal{R}_{\mathrm{CL}}^{(k)}$ stabilises for every finite-alphabet DM-MAC. A
  computer-assisted strict inclusion $\mathcal{R}_{\mathrm{CL}}^{(1)} \subsetneq
  \mathcal{R}_{\mathrm{CL}}^{(2)}$ for the binary MAC above at $q = 1/2$ (the endpoint of the
  family, which VP state for $0 < q < 1/2$; i.e. $Y = X_J$,
  $J \sim \mathrm{Unif}\{1,2\}$) is in `attempts/mac-with-feedback/`. The max sum-rate is
  $\le 0.57895$ at $k = 1$ (duality certificate) and $\ge 0.58432$ at $k = 2$ (explicit
  strategies). So for this channel the hierarchy does not stop at $k = 1$, and Cover–Leung is
  strictly suboptimal there. That some finite-alphabet MAC has
  $\mathcal{R}_{\mathrm{CL}}^{(1)} \neq \mathcal{C}_{\mathrm{MAC-FB}}$ already followed from
  Kramer's example above. What is new is an explicit, certified jump at $k = 2$.
- **Consistency of the frozen statement**: it holds with $k = 1$ for Willems' class, for
  channels where feedback does not enlarge the region, and in degenerate cases (silent user,
  empty alphabets). These are consistent with the catalog; no catalog error was found (see the
  2026-11-26 audit attempt).
- **Multi-letter characterization**: Kramer (1998, 2003) proved that the exact feedback
  capacity region is the multi-letter limit of normalized directed information regions (extended
  to finite-state MACs by Permuter–Weissman–Chen 2009). Anastasopoulos–Pradhan (2020) recast
  the multi-letter expression as a decentralized sequential active hypothesis testing /
  stochastic-control problem with time-invariant state space, and Vasal (arXiv:2202.02320)
  proposes a dynamic program for it. These are reformulations, not finite-letter
  characterizations. Dependence-balance
  outer bounds (Hekstra–Willems 1989; Tandon–Ulukus 2009) give the sharpest known
  single-letter converses, yet do not match achievability in general.

## References

- N. T. Gaarder and J. K. Wolf, "The capacity region of a multiple-access discrete
  memoryless channel can increase with feedback," *IEEE Trans. Inf. Theory*, vol. 21,
  no. 1, pp. 100–102, 1975.
- T. M. Cover and C. S. K. Leung, "An achievable rate region for the multiple-access
  channel with feedback," *IEEE Trans. Inf. Theory*, vol. 27, no. 3, pp. 292–298, 1981.
- F. M. J. Willems, "The feedback capacity region of a class of discrete memoryless
  multiple access channels," *IEEE Trans. Inf. Theory*, vol. 28, no. 1, pp. 93–95, 1982.
- L. H. Ozarow, "The capacity of the white Gaussian multiple access channel with feedback,"
  *IEEE Trans. Inf. Theory*, vol. 30, no. 4, pp. 623–629, 1984.
- G. Kramer, *Directed Information for Channels with Feedback*, Ph.D. dissertation, ETH
  Zurich, 1998.
- S. I. Bross and A. Lapidoth, "An improved achievable region for the discrete memoryless
  two-user multiple-access channel with noiseless feedback," *IEEE Trans. Inf. Theory*,
  vol. 51, no. 3, pp. 811–833, 2005.
- R. Venkataramanan and S. S. Pradhan, "A new achievable rate region for the
  multiple-access channel with noiseless feedback," *IEEE Trans. Inf. Theory*, vol. 57,
  no. 12, pp. 8038–8054, 2011 (arXiv:0901.1892).
- G. Kramer, "Capacity results for the discrete memoryless network," *IEEE Trans. Inf.
  Theory*, vol. 49, no. 1, pp. 4–21, 2003.
- A. P. Hekstra and F. M. J. Willems, "Dependence balance bounds for single-output two-way
  channels," *IEEE Trans. Inf. Theory*, vol. 35, no. 1, pp. 44–53, 1989.
- R. Tandon and S. Ulukus, "Outer bounds for multiple-access channels with feedback using
  dependence balance," *IEEE Trans. Inf. Theory*, vol. 55, no. 10, pp. 4494–4507, 2009.
- H. H. Permuter, T. Weissman, and J. Chen, "Capacity region of the finite-state
  multiple-access channel with and without feedback," *IEEE Trans. Inf. Theory*, vol. 55,
  no. 6, pp. 2455–2477, 2009.
- A. Anastasopoulos and S. S. Pradhan, "Decentralized sequential active hypothesis testing
  and the MAC feedback capacity," *Proc. IEEE ISIT*, pp. 2085–2090, 2020 (arXiv:2001.03807).
