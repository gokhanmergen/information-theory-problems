---
id: minimax-kl-large-alphabet
title: Exact Leading Constant of Minimax KL Risk for Large-Alphabet Distribution Estimation
status: open
category: statistical-info-theory
posed_by: Dietrich Braess and Thomas Sauer; Sudeep Kamath, Alon Orlitsky, Dheeraj Pichapati, and Ananda Theertha Suresh
posed_year: 2004
tags: [minimax-risk, kl-divergence, large-alphabet, distribution-estimation, statistical-info-theory]
lean_module: InfoTheory.Problems.MinimaxKlLargeAlphabet
lean_file: lean/InfoTheory/Problems/MinimaxKlLargeAlphabet.lean
---

## Statement

Given $n$ i.i.d. samples $X_1, \dots, X_n$ from an unknown discrete distribution $P \in \Delta_k$ on an alphabet of size $k$, let
$$
r_{k, n} := \inf_{\hat{P}} \sup_{P \in \Delta_k} \mathbb{E}_{X^n \sim P^{\otimes n}} \big[ D_{\mathrm{KL}}(P \mathbin{\|} \hat{P}(X^n)) \big]
$$
denote the **minimax expected Kullback–Leibler risk** of discrete distribution estimation.

**Determine the exact limiting minimax KL risk constant**
$$
c(\alpha) := \lim_{n \to \infty} r_{\lfloor \alpha n \rfloor, n}
$$
**in the high-dimensional proportional regime $k / n \to \alpha \in (0, \infty)$.**

A sharp structural question — formalized in the accompanying Lean statement — asks whether the two-parameter **Braess–Sauer (2004) add-constant family** (which assigns weight $\beta_0 > 0$ to unseen symbols with count $N_a = 0$ and weight $N_a + \beta_1$ to seen symbols with count $N_a \ge 1$, proven asymptotically minimax-optimal in the classical regime $k = o(n)$) remains asymptotically minimax-optimal in the proportional regime $k / n \to \alpha \in (0, \infty)$, or whether estimators that depend non-trivially on higher-order frequency counts ($N_a = 1, 2, \dots$) achieve a strictly smaller limiting constant $c(\alpha)$.

## Background

Estimating a discrete probability distribution under KL divergence (equivalently, expected universal-compression redundancy / worst-case regret of predictive probability assignments) is one of the oldest problems in statistical information theory. In the classical low-dimensional regime ($k$ fixed, $n \to \infty$), Krichevsky and Trofimov (1981) and Braess and Sauer (2004) showed that the minimax KL risk is $\frac{k-1}{2n}(1 + o(1))$ (in nats), achieved by a simple add-$\beta$ estimator with boundary adjustment ($\beta_0 = 3/4, \beta_1 = 1/2$).

When the alphabet size $k$ grows proportionally with the sample size $n$ ($k / n \to \alpha \in (0, \infty)$), a constant fraction of symbols appear $0, 1, 2, \dots$ times (the Poissonized Good–Turing regime). In this regime, the classical $\frac{k-1}{2n}$ approximation breaks down, and pinning down the exact minimax constant $c(\alpha)$ and optimal estimator remains open.

## What is known

- **Small-alphabet regime ($k = o(n)$):** Braess and Sauer (2004) proved $r_{k, n} = \frac{k - 1}{2 n} + o(k/n)$ (in nats), achieved by the two-parameter Braess–Sauer estimator ($\beta_0 = 3/4$ for unseen symbols, $\beta_1 = 1/2$ for seen symbols), improving on the standard Krichevsky–Trofimov add-$1/2$ estimator whose worst-case risk at the simplex boundary is slightly larger ($\approx 0.509 \cdot k/n$).
- **Ultra-large-alphabet regime ($k \gg n$):** Paninski (2004) and Kamath, Orlitsky, Pichapati, and Suresh (2015) proved $r_{k, n} = \ln(k / n) + o(1)$ (in nats), with sharp lower-order asymptotics.
- **Proportional regime ($k / n \to \alpha \in (0, \infty)$):**
  - Kamath, Orlitsky, Pichapati, and Suresh (2015) proved sharp upper and lower bounds for every $\alpha > 0$, showing e.g. that for $\alpha = 1$ ($k = n$), $r_{n, n}$ lies in a narrow interval strictly below $1/2$ nat ($\approx 0.42$ to $0.50$ nats), and that single-parameter add-$\beta$ estimators are strictly suboptimal compared to estimators that treat unseen symbols separately.
  - Orlitsky and Suresh (2015) showed that modified Good–Turing estimators are competitive against the best *natural* (label-invariant) estimator on every distribution, yet the exact minimax value $c(\alpha)$ and the exact asymptotic minimax-optimal estimator in the proportional regime $k / n \to \alpha \in (0, \infty)$ remain open.

## References

- R. E. Krichevsky and V. K. Trofimov, "The performance of universal encoding," *IEEE Trans. Inf. Theory* **27**(2), 199–207 (1981).
- D. Braess and T. Sauer, "Bernstein polynomials and learning theory," *J. Approx. Theory* **128**(2), 187–206 (2004).
- L. Paninski, "Variational minimax estimation of discrete distributions under KL loss," *Advances in Neural Information Processing Systems (NeurIPS)* **17** (2004).
- S. Kamath, A. Orlitsky, D. Pichapati, and A. T. Suresh, "On learning distributions from their samples," *Proc. 28th COLT*, PMLR **40**, 1066–1100 (2015).
- A. Orlitsky and A. T. Suresh, "Competitive distribution estimation: Why is Good–Turing good," *Advances in Neural Information Processing Systems (NeurIPS)* **28** (2015).
