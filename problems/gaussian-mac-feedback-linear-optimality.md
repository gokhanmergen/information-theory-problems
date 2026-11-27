---
id: gaussian-mac-feedback-linear-optimality
title: Optimality of Linear Feedback for the Symmetric K-User Gaussian MAC with Feedback
status: open
category: network-info-theory
posed_by: Gerhard Kramer; Ardestanizadeh, Wigger, Kim and Javidi; Sula, Gastpar and Kramer
posed_year: 2002
tags: [network-information-theory, mac, feedback, gaussian-channel, linear-feedback, dependence-balance]
lean_module: InfoTheory.Problems.GaussianMacFeedbackLinearOptimality
lean_file: lean/InfoTheory/Problems/GaussianMacFeedbackLinearOptimality.lean
review: pending-expert
---

## Statement

The $K$-user Gaussian multiple-access channel (MAC) with feedback is
$$
Y_i = \sum_{j=1}^K X_{j,i} + Z_i, \qquad Z_i \text{ i.i.d. } \mathcal{N}(0, N),\ N > 0.
$$
The output is fed back noiselessly and causally to all senders:
$X_{j,i} = f_{j,i}(M_j, Y^{i-1})$. Each sender has the same expected block power constraint
$\sum_{i=1}^n \mathbb{E}[X_{j,i}^2] \le nP$. Let $\mathcal{C}_{\mathrm{FB}}(K,P,N)$ be the
capacity region.

A **linear-feedback code** (Ardestanizadeh–Wigger–Kim–Javidi 2012, Def. 1) has inputs of the form
$$
X_{j,i} = w_j(M_j)_i + \sum_{t < i} B_j(i,t)\, Y_t,
$$
where $w_j$ is an arbitrary (nonlinear) map from messages to $\mathbb{R}^n$ and $B_j$ is a
fixed strictly lower-triangular matrix. Let $\mathcal{C}_{\mathrm{LF}}(K,P,N)$ be the region
achievable with such codes. This class contains all non-feedback codes and the schemes of
Schalkwijk–Kailath, Ozarow and Kramer (Fourier-MEC).

**Question.** For $K \ge 3$ and equal powers, is
$$
\overline{\mathcal{C}_{\mathrm{FB}}(K,P,N)} = \overline{\mathcal{C}_{\mathrm{LF}}(K,P,N)}\ ?
$$
In words: is linear feedback capacity-achieving for the symmetric Gaussian MAC with feedback?
The inclusion $\supseteq$ is trivial and the open direction is $\subseteq$. A disproof needs a
rate vector achievable with feedback but not, even approximately, with linear feedback.

## Background

Gaarder and Wolf (1975) showed that feedback can enlarge the capacity region of a MAC. For the
two-user Gaussian MAC, Ozarow (1984) determined the feedback capacity region exactly. His
achievability scheme is a two-user Schalkwijk–Kailath scheme, i.e. a linear-feedback code, and
it is matched by a cut-set-type converse. So for $K = 2$, linear feedback is optimal and the
statement above holds.

For $K \ge 3$ the capacity region is open. Kramer (2002) generalized Ozarow's scheme to
"Fourier-modulated estimate correction" (Fourier-MEC). He showed it is sum-rate optimal for
equal powers above an SNR threshold that depends on $K$, where it meets the cut-set bound.
Kramer and Gastpar (2006) extended the dependence-balance bounds of Hekstra–Willems (1989) to
the Gaussian MAC with feedback. Sula–Gastpar–Kramer (2020) later showed that Fourier-MEC is
sum-rate optimal at *all* SNRs. AWKJ (2012, Cor. 1) note that at low SNR almost no cooperation is possible with linear
feedback. Our reading, which the expert should check, is that the cut-set bound is therefore
not tight for $K\ge3$ at low SNR.

Ardestanizadeh–Wigger–Kim–Javidi (2012) characterized the **linear-feedback** sum-capacity for
equal powers, showed that Kramer's code achieves it, and recalled the common belief that linear
feedback achieves the sum-capacity. Sula–Gastpar–Kramer (2020) proved this for the sum rate.
Fourier-MEC achieves the feedback sum-capacity of the symmetric $J$-user Gaussian MAC at all
SNRs:
$$
C_{\mathrm{sum}} = \tfrac12\log_2(1 + PJ\beta/N),\qquad (1 + PJ\beta/N)^{J-1} = (1 + P\beta(J-\beta)/N)^J,\ \beta \in [1,J].
$$
Their conclusion leaves open "whether Fourier MEC can achieve all rate points in the capacity
region of the symmetric GMAC with feedback". This entry formalizes the slightly weaker, and
scheme-independent, question of whether linear feedback suffices for the whole region. A
positive answer to Sula–Gastpar–Kramer's question implies a positive answer here.

## What is known

- **$K = 2$:** solved by Ozarow (1984). The region is the union over $\rho\in[0,1]$ of
  $R_j \le \tfrac12\log(1+P_j(1-\rho^2)/N)$ and
  $R_1+R_2 \le \tfrac12\log(1+(P_1+P_2+2\rho\sqrt{P_1P_2})/N)$. It is achieved by a linear
  scheme.
- **Outer bounds for $K \ge 3$:**
  - the cut-set / total-cooperation bound;
  - feedback can at most double the sum capacity (Thomas 1987). Ordentlich extended this to the
    whole region and to colored noise (as cited in AWKJ 2012);
  - the dependence-balance bounds of Hekstra–Willems (1989), as extended by Kramer–Gastpar
    (2006);
  - the Sula–Gastpar–Kramer refinement, combining dependence balance with a Geng–Nair-type
    convex-envelope argument.
- **Sum rate, equal powers:** solved at high SNR by Kramer (2002) and at all SNRs by
  Sula–Gastpar–Kramer (2020). The optimum is achieved by Fourier-MEC, a linear-feedback code.
  The linear-feedback sum-capacity was found earlier by Ardestanizadeh–Wigger–Kim–Javidi (2012).
- **Sum rate, unequal powers:** open. Sula–Gastpar–Kramer (Example 1) show that Fourier-MEC
  falls short of the dependence-balance bound for powers $(1,4,9)$: 1.6215 vs. 1.6427
  bits/use. They also note that Fourier-MEC can be improved by non-uniform modulation
  frequencies. (This regime is *not* part of the formal statement.)
- **Full region, $K \ge 3$:** open, even for equal powers. No non-linear scheme is known to beat
  linear feedback anywhere in the symmetric region. No converse matching linear-feedback rates
  off the sum-rate face is known either.
- Searches up to Nov. 2026 (Sula–Gastpar–Kramer follow-ups, "Gaussian multiple access channel
  feedback capacity region three users") found no resolution. **The expert should confirm.**
- For the *discrete memoryless* two-user MAC with feedback see the catalog entry
  `mac-with-feedback`.

## Notes on the formalization (for expert review)

- **Choice of question (judgment call).** No published conjecture gives a formula for the
  $K\ge3$ feedback region. We therefore formalize "linear feedback is optimal" as equality of
  two operational regions. This avoids writing down the Fourier-MEC region, which has no
  simple closed form in the literature we checked. Two caveats:
  - the linear-feedback region itself is not known in closed form for $K\ge3$;
  - the statement is implied by, but weaker than, Sula–Gastpar–Kramer's Fourier-MEC question.
  Restricting to equal powers matches the published open question. With unequal powers even
  the sum rate is open.
- **Linear-feedback class.** AWKJ's Def. 1 is $X_{ji} = L_{ji}(\theta_j(m_j), y^{i-1})$ with
  $\theta_j$ arbitrary and $L_{ji}$ linear. Since $\theta_j$ is arbitrary, the
  message-dependent part $A_j\theta_j(m_j)$ is an arbitrary map from messages to
  $\mathbb{R}^n$. So the class is exactly $x_j = w_j(m_j) + B_j y$ with $B_j$ strictly lower
  triangular, which is the form used in Lean.
- **Codes.** Encoders are functions of the own message and the full output block. They must be
  causal (depend only on $t < i$) and measurable. Decoders are measurable, one per sender.
  The received block is $n$ passes of $y = \sum_j x_j(y) + z$ starting from $z$. The
  certificate proves this is the unique solution of the causal recursion and is measurable.
- **Power (judgment call).** The constraint is expected block power per sender, averaged over
  uniform message tuples and noise. It is evaluated as an $\mathbb{R}_{\ge0}^\infty$
  `lintegral`, so infinite power is $\top$. This is as in Ozarow, AWKJ and SGK. An almost-sure
  constraint would exclude Schalkwijk–Kailath-type linear schemes outright, which have
  unbounded Gaussian inputs.
- **Error.** Average over uniform message tuples. For each tuple, the error is the noise
  measure of $\{\exists j: \hat M_j \ne M_j\}$.
- **Closures.** Both regions are compared through `closure` in $\mathbb{R}^K$, so boundary
  conventions are irrelevant. No `sSup` appears in the statement.
- **Certificate** (`Known/Certificates/GaussianMacFeedbackLinearOptimality.lean`):
  - well-posedness of the causal recursion;
  - $\mathcal{C}_{\mathrm{LF}} \subseteq \mathcal{C}_{\mathrm{FB}}$;
  - $0$ is achievable;
  - every single-user corner $R\,e_{j}$ with $R < \tfrac12\log_2(1+P/N)$ is achievable by
    (feedback-free, hence linear) codes, via the operational AWGN coding theorem. Hence both
    closures contain $[0,\tfrac12\log_2(1+P/N)]\,e_j$.
- **Not certified:** boundedness of $\mathcal{C}_{\mathrm{FB}}$ (any feedback converse), and
  achievability of Ozarow / Fourier-MEC rates. A feedback converse needs a change of measure
  through the causal output map, which `Known` does not yet provide.

## References

- N. T. Gaarder and J. K. Wolf, "The capacity region of a multiple-access discrete memoryless
  channel can increase with feedback," *IEEE Trans. Inf. Theory*, vol. 21, no. 1, 1975.
- L. H. Ozarow, "The capacity of the white Gaussian multiple access channel with feedback,"
  *IEEE Trans. Inf. Theory*, vol. 30, no. 4, pp. 623–629, 1984.
- J. A. Thomas, "Feedback can at most double Gaussian multiple access channel capacity,"
  *IEEE Trans. Inf. Theory*, vol. 33, no. 5, 1987.
- A. P. Hekstra and F. M. J. Willems, "Dependence balance bounds for single-output two-way
  channels," *IEEE Trans. Inf. Theory*, vol. 35, no. 1, 1989.
- G. Kramer, "Feedback strategies for white Gaussian interference networks," *IEEE Trans. Inf.
  Theory*, vol. 48, no. 6, 2002.
- G. Kramer and M. Gastpar, "Dependence balance and the Gaussian multiaccess channel with
  feedback," *Proc. IEEE Information Theory Workshop*, 2006.
- E. Ardestanizadeh, M. Wigger, Y.-H. Kim, T. Javidi, "Linear-feedback sum-capacity for Gaussian
  multiple access channels," *IEEE Trans. Inf. Theory*, vol. 58, no. 1, 2012 (arXiv:1002.1781).
- E. Sula, M. Gastpar, G. Kramer, "Sum-rate capacity for symmetric Gaussian multiple access
  channels with feedback," *IEEE Trans. Inf. Theory*, vol. 66, no. 5, pp. 2860–2871, 2020
  (arXiv:1811.09525; ISIT 2018).
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011, Ch. 17.
