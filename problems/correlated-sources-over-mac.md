---
id: correlated-sources-over-mac
title: Lossless Transmission of Correlated Sources over a Multiple-Access Channel
status: open
category: network-info-theory
posed_by: Thomas M. Cover, Abbas El Gamal, and Masoud Salehi
posed_year: 1980
tags: [network-information-theory, mac, joint-source-channel-coding, correlated-sources, single-letter-characterization, computability]
lean_module: InfoTheory.Problems.CorrelatedSourcesOverMac
lean_file: lean/InfoTheory/Problems/CorrelatedSourcesOverMac.lean
review: expert-approved (2026-11-26)
---

## Statement

Let $(U, V) \sim P_{UV}$ be a two-component discrete memoryless source (2-DMS) on finite
alphabets, and let $W(y \mid x_1, x_2)$ be a DM-MAC. Encoder 1 observes $U^k$ and encoder 2
observes $V^k$. Each maps its block into $n$ channel inputs, and the decoder must reproduce
$(U^k, V^k)$ from $Y^n$ with vanishing error probability. With $k = n$, the source is
*transmissible* over $W$ if such codes exist with $P_e \to 0$.

**Informal problem.** Find a single-letter (computable) necessary and sufficient condition for
$P_{UV}$ to be transmissible over $W$.

**Formal statement (Lean proxy).** To remove boundary effects, let codes send $\lfloor \rho n
\rfloor$ source symbols in $n$ channel uses, and let
$$\rho^*(P_{UV}, W) = \sup\{\rho \ge 0 : P_{UV} \text{ is losslessly transmissible over } W
\text{ at } \rho \text{ source symbols per channel use}\}.$$
A standard padding argument shows that $P_{UV}$ is transmissible with matched bandwidth if
$\rho^* > 1$, and it is not if $\rho^* < 1$. *Is $\rho^*$ computable from rational
data?* Precisely: is there a Turing machine that, given integer weights describing a rational
source $P_{UV}$ and a rational MAC $W$, and a query $(p, q, \mathrm{prec})$, always halts? It
should output `true` if $\rho^* \le p/q - 1/\mathrm{prec}$ and `false` if
$\rho^* \ge p/q + 1/\mathrm{prec}$. Sources concentrated on a single pair are excluded, since
for them $\rho^* = +\infty$.

A computable single-letter characterization would give a positive answer. A negative answer
would show that no computable single-letter characterization exists. A positive answer by
other means (e.g. converging computable inner and outer bounds) would not by itself give a
single-letter formula. The Lean statement is therefore a faithful *necessary condition* for
the informal problem, in the same spirit as `index-coding-single-letter` and
`shannon-capacity-computability`.

## Background

For a single source over a point-to-point channel, Shannon's separation theorem reduces
transmissibility to $H(U) < C$. In multiuser settings separation fails. Cover, El Gamal and
Salehi (CES, 1980) showed that the correlation between $U$ and $V$ can be preserved in the
channel inputs. In their example $(U,V)$ is uniform on $\{(0,0),(0,1),(1,1)\}$ and the
channel is the binary adder MAC $Y = X_1 + X_2$. Uncoded transmission $X_1 = U$, $X_2 = V$ is
error-free, yet $H(U,V) = \log_2 3 > 1.5 = C_\Sigma$, so Slepian–Wolf coding followed by
independent MAC coding must fail. CES gave a single-letter *sufficient* condition, which uses the Gács–Körner
common part $K$ of $(U,V)$ and auxiliaries $p(s)\,p(x_1 \mid u, s)\,p(x_2 \mid v, s)$:
$$H(U\mid V) < I(X_1;Y \mid X_2,V,S),\quad H(V\mid U) < I(X_2;Y\mid X_1,U,S),$$
$$H(U,V\mid K) < I(X_1,X_2;Y\mid K,S),\quad H(U,V) < I(X_1,X_2;Y).$$
CES (§IV, Theorems 2 and 4) also gave an exact but uncomputable $n$-letter characterization,
with both achievability and converse: $(U,V)$ is transmissible iff its entropy triple lies in
$\bigcup_k C_k$ for increasing $k$-letter regions $C_k$. Their Remark 2 notes that these inner
approximations converge but that no outer approximations are known. Dueck (1981) built an example
that is transmissible yet violates the CES condition, so the CES condition is not
necessary. A single-letter characterization has been open since then.

## What is known

- **Sufficient conditions.** CES (1980) gave the condition above. Pradhan, Choi and
  Ramchandran (2007) gave a graph-based framework that improves on CES for some sources.
  Heidari and Pradhan (arXiv:1905.04760) use structured (algebraic) mappings and "conferencing
  common information" to improve on CES-type schemes.
- **Necessary conditions.** CES's exact $n$-letter characterization (§IV) is approximated only
  from inside, so it yields no computable necessary condition. Kang and
  Ulukus (2011) used a new data-processing inequality to give a single-letter upper bound on
  the sum rate, i.e. a single-letter necessary condition. It does not close the gap to the CES
  region.
- **Not necessary.** Dueck (1981) showed that the CES sufficient condition is not necessary.
- **Solved special cases.** If $U$ and $V$ are independent, separation is optimal: Slepian–Wolf
  rates must lie in the MAC capacity region (Ahlswede–Liao). If one source is available to
  both encoders (the asymmetric MAC / "one source known at both encoders"), necessary and
  sufficient conditions are known (De Bruyn, Prelov, van der Meulen 1987). Ahlswede–Han (1983)
  treat source coding with side information over a MAC and related problems.
- **Status.** El Gamal–Kim (2011, Ch. 14) state that the optimal condition is unknown, and
  Heidari–Pradhan (2019) restate it as open. The searches done for this entry (Kang–Ulukus;
  Güler–Gündüz–Yener on the lossy version; Heidari–Pradhan; 2020–2026 literature) found no
  resolution and no result on computability of $\rho^*$.

## Notes on the formalization (for expert review)

- **Why a ratio $\rho^*$ rather than "decide transmissibility at $\rho = 1$".** An exact
  decision procedure would also have to decide boundary instances, e.g. $H(U) = C$ in
  degenerate cases. That is hard even for point-to-point channels, for arithmetic reasons that
  have nothing to do with the MAC. Approximating the real number $\rho^*$ with a promise gap
  avoids this. Transmissibility at $\rho = 1$ is recovered from $\rho^*$ except when
  $\rho^* = 1$. That exception includes CES's own motivating example. There the uncoded
  code is error-free, so $\rho^* \ge 1$, and the cooperative cut-set bound gives
  $\rho^* \le \log_2 3 / H(U,V) = 1$. So $\rho^* = 1$ exactly (attempt
  `2026-11-26-claude-opus-5-5-lower-semicomputability.md`, Claim 8).
- **Instances** are given by integer weights: $P(u,v) = w(u,v)/\sum w$ and
  $W(y \mid x_1,x_2) = v(x_1,x_2,y)/\sum_{y'} v(x_1,x_2,y')$. Every rational instance arises
  this way. The hypothesis $w(u,t) < \sum w$ for all $(u,t)$ is equivalent to $H(U,V) > 0$. The
  certificate shows that under it $\rho^*$ is a genuine finite supremum. The bound is
  $0 \le \rho^* \le (\log_2|\mathcal{Y}| + 1 + L)/L$ with $L = \log_2(1/p_{\max})$, proved by an
  elementary counting converse.
- **Monotonicity.** Transmissibility at $\rho$ implies it at all $\rho' < \rho$, by padding with
  a fixed, well-chosen tail of source symbols (an averaging argument). A written proof is in
  the attempt cited above (Claim 2); it is not yet certified in Lean. It is needed only to
  relate $\rho^*$ to $\rho = 1$, not for the frozen statement itself.
- **Lower semi-computability (attempt, reviewer-verified 2026-11-27).** The same attempt
  proves that $\rho^*$ is lower semi-computable, uniformly in the instance:
  $\{r \in \mathbb{Q} : r < \rho^*\}$ is recursively enumerable. The tool is a bootstrap
  theorem. When both single-user capacities $C_1, C_2$ are positive, one finite code with
  exact rational error $\varepsilon$ certifies every ratio below
  $k/(n + \varphi(\varepsilon)(1/C_1 + 1/C_2))$. This is essentially implicit in CES
  (1980, §IV). Their Theorems 2 and 4 characterize transmissibility by an increasing union
  of $n$-letter regions $C_n$. Their Remark 2 notes that these inner approximations
  converge but that no outer approximations are known. Consequently the frozen Statement is
  equivalent to uniform *upper* semi-computability of $\rho^*$, exactly as for
  `shannon-capacity-computability`. On instances where one encoder's input does not
  affect the output, $\rho^*$ has a closed form and is computable.

## References

- T. M. Cover, A. El Gamal, M. Salehi, "Multiple access channels with arbitrarily correlated
  sources," *IEEE Trans. Inf. Theory*, vol. 26, no. 6, pp. 648–657, 1980.
- G. Dueck, "A note on the multiple access channel with correlated sources," *IEEE Trans.
  Inf. Theory*, vol. 27, no. 2, pp. 232–235, 1981.
- D. Slepian and J. K. Wolf, "Noiseless coding of correlated information sources," *IEEE
  Trans. Inf. Theory*, vol. 19, no. 4, pp. 471–480, 1973.
- P. Gács and J. Körner, "Common information is far less than mutual information," *Problems
  of Control and Information Theory*, vol. 2, pp. 149–162, 1973.
- R. Ahlswede and T. S. Han, "On source coding with side information via a multiple-access
  channel and related problems in multi-user information theory," *IEEE Trans. Inf. Theory*,
  vol. 29, no. 3, pp. 396–412, 1983.
- K. de Bruyn, V. V. Prelov, E. C. van der Meulen, "Reliable transmission of two correlated
  sources over an asymmetric multiple-access channel," *IEEE Trans. Inf. Theory*, vol. 33,
  no. 5, pp. 716–718, 1987.
- S. S. Pradhan, S. Choi, K. Ramchandran, "A graph-based framework for transmission of
  correlated sources over multiple-access channels," *IEEE Trans. Inf. Theory*, vol. 53,
  no. 12, pp. 4583–4604, 2007.
- W. Kang and S. Ulukus, "A new data processing inequality and its applications in
  distributed source and channel coding," *IEEE Trans. Inf. Theory*, vol. 57, no. 1,
  pp. 56–69, 2011 (arXiv:cs/0611017; see also arXiv:cs/0511096).
- M. Heidari and S. S. Pradhan, "Structured mappings and conferencing common information for
  multiple-access channels," arXiv:1905.04760, 2019.
- Y. Güler, D. Gündüz, A. Yener, "Lossy coding of correlated sources over a multiple access
  channel: necessary conditions and separation results," arXiv:1612.05225, 2016.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011, Ch. 14.
