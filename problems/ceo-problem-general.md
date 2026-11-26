---
id: ceo-problem-general
title: Rate-Distortion Region of the General Discrete Memoryless CEO Problem
status: open
category: source-coding
posed_by: Toby Berger, Zhen Zhang, and Harish Viswanathan
posed_year: 1996
tags: [source-coding, ceo-problem, rate-distortion, berger-tung, distributed-source-coding]
lean_module: InfoTheory.Problems.CeoProblemGeneral
lean_file: lean/InfoTheory/Problems/CeoProblemGeneral.lean
---

## Statement

In the two-agent **discrete memoryless CEO problem**, a hidden source $X \sim P_X$ over a
finite alphabet $\mathcal{X}$ is observed through two conditionally independent discrete
memoryless channels $W_1(y_1 \mid x)$ and $W_2(y_2 \mid x)$ (so $Y_1 - X - Y_2$). Two
non-communicating agents observe $Y_1^n$ and $Y_2^n$ and send descriptions at rates $R_1$
and $R_2$ to a Chief Executive Officer (CEO) decoder, which reconstructs $\hat{X}^n$ to
meet an expected single-letter distortion constraint
$\frac{1}{n} \sum_{i=1}^n \mathbb{E}[d(X_i, \hat{X}_i)] \le D$.

The **Berger–Tung inner bound** for the CEO problem (Berger–Zhang–Viswanathan 1996;
El Gamal–Kim 2011, Section 12.4) consists of the closure of all triples $(R_1, R_2, D)$
for which there exist a time-sharing variable $Q$, conditional distributions
$p(u_1 \mid y_1, q)$ and $p(u_2 \mid y_2, q)$ inducing
$p(q) P_X(x) W_1(y_1 \mid x) W_2(y_2 \mid x) p(u_1 \mid y_1, q) p(u_2 \mid y_2, q)$, and a
reconstruction function $g(u_1, u_2, q) \in \hat{\mathcal{X}}$ such that
$\mathbb{E}[d(X, g(U_1, U_2, Q))] \le D$ and:
$$
\begin{aligned}
R_1 &\ge I(Y_1; U_1 \mid U_2, Q), \\
R_2 &\ge I(Y_2; U_2 \mid U_1, Q), \\
R_1 + R_2 &\ge I(Y_1, Y_2; U_1, U_2 \mid Q).
\end{aligned}
$$

**Does this Berger–Tung inner bound characterize the exact operational rate-distortion
region for every discrete memoryless two-agent CEO source $(P_X, W_1, W_2)$ and every
single-letter distortion measure $d$?**

## Background

Introduced by Berger, Zhang, and Viswanathan (1996) to model distributed estimation and
sensor networks in which multiple noisy observers report to a fusion center without
inter-agent communication, the CEO problem is a structured specialization of multiterminal
source coding in which the observations are conditionally independent given the target
source ($Y_1 - X - Y_2$) and only the hidden source $X$ is reconstructed. Because
$Y_1 - X - Y_2$ rules out deterministic sum-source counterexamples like Körner–Marton's
modulo-2 sum, it has been a longstanding open question whether the Berger–Tung inner bound
is universally tight for all discrete memoryless CEO instances.

## What is known

- **Quadratic Gaussian CEO problem**: completely solved — Oohama (1998, 2005) established
  the sum-rate distortion function, and Prabhakaran, Tse, and Ramchandran (2004) and
  Oohama (2005) proved that the Berger–Tung inner bound is **tight** for the full
  $L$-agent quadratic Gaussian CEO rate-distortion region.
- **Logarithmic-loss CEO problem**: Courtade and Weissman (2014) proved that the
  Berger–Tung inner bound is **tight** for every discrete memoryless $L$-agent CEO problem
  under logarithmic-loss distortion.
- **Asymptotic large-$L$ behavior**: Berger, Zhang, and Viswanathan (1996) determined the
  error-exponent / distortion scaling as the number of agents $L \to \infty$ for general
  discrete sources under Hamming distortion.
- **General discrete memoryless CEO (finite $L$, e.g. $L = 2$)**: outside Gaussian
  squared-error and logarithmic loss, the rate-distortion region remains wide open — even
  for the binary symmetric CEO problem ($X \sim \mathrm{Bern}(1/2)$, $W_1 = W_2 = \mathrm{BSC}(p)$,
  Hamming distortion).

## References

- T. Berger, Z. Zhang, and H. Viswanathan, "The CEO problem," *IEEE Trans. Inf. Theory*,
  vol. 42, no. 3, pp. 887–902, 1996.
- Y. Oohama, "The rate-distortion function for the quadratic Gaussian CEO problem,"
  *IEEE Trans. Inf. Theory*, vol. 44, no. 3, pp. 1057–1070, 1998.
- V. Prabhakaran, D. Tse, and K. Ramchandran, "Rate region of the quadratic Gaussian CEO
  problem," *Proc. IEEE Int. Symp. Inf. Theory (ISIT)*, p. 119, 2004.
- Y. Oohama, "Rate-distortion theory for Gaussian multiterminal source coding systems with
  several side informations at the decoder," *IEEE Trans. Inf. Theory*, vol. 51, no. 7,
  pp. 2577–2593, 2005.
- T. A. Courtade and T. Weissman, "Multiterminal source coding under logarithmic loss,"
  *IEEE Trans. Inf. Theory*, vol. 60, no. 1, pp. 740–761, 2014.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Section 12.4.
