---
id: discrete-entropy-power-inequality
title: Discrete Entropy Power Inequality on the Integers
status: open
category: entropy-inequalities
posed_by: Terence Tao; Peter Harremoës and Christophe Vignat; Mokshay Madiman
posed_year: 2010
tags: [entropy-inequalities, entropy-power-inequality, discrete-entropy, additive-combinatorics]
lean_module: InfoTheory.Problems.DiscreteEntropyPowerInequality
lean_file: lean/InfoTheory/Problems/DiscreteEntropyPowerInequality.lean
---

## Statement

Let $X_1, X_2, \dots$ be independent and identically distributed random variables taking values in $\mathbb{Z}$ with finite Shannon entropy $H(X_1) = -\sum_{k \in \mathbb{Z}} P(k) \ln P(k)$ (in nats).

**Conjecture (Tao's Discrete Entropy Power Inequality, 2010).** For every integer $n \ge 1$ and every $\varepsilon > 0$, there exists $M > 0$ such that whenever $X_1, \dots, X_{n+1}$ are i.i.d. integer-valued random variables with $H(X_1) \ge M$,
$$H(X_1 + \cdots + X_{n+1}) \;\ge\; H(X_1 + \cdots + X_n) + \frac{1}{2} \ln\!\left(\frac{n+1}{n}\right) - \varepsilon.$$

In particular, for $n = 1$ (two i.i.d. copies $X_1, X_2$ on $\mathbb{Z}$),
$$H(X_1 + X_2) \;\ge\; H(X_1) + \frac{1}{2}\ln 2 - o_{H(X_1) \to \infty}(1).$$

## Background

Shannon's continuous Entropy Power Inequality (EPI) asserts that $e^{2h(X+Y)} \ge e^{2h(X)} + e^{2h(Y)}$ for independent real-valued random variables, which for i.i.d. sums implies $h(X_1 + \cdots + X_{n+1}) \ge h(X_1 + \cdots + X_n) + \frac{1}{2}\ln\frac{n+1}{n}$ (Artstein–Ball–Barthe–Naor 2004), with equality for Gaussians. On the integers $\mathbb{Z}$, a literal constant-free EPI fails at small entropies (e.g., for deterministic variables $H(X) = 0$ or highly biased Bernoulli variables). However, because $\mathbb{Z}$ is torsion-free and contains no nontrivial finite subgroups, it is conjectured that in the high-entropy regime $H(X_1) \to \infty$, discrete Gaussians are asymptotically extremal and the continuous entropy increment $\frac{1}{2}\ln\frac{n+1}{n}$ is recovered up to $o(1)$.

## What is known

- **Unconditional constant-gap bounds (Tao, 2010; Madiman–Marcus–Tetali, 2012):** Tao (2010) proved $H(X_1 + X_2) \ge H(X_1) + \frac{1}{2}\ln 2 - o(1)$ cannot be beaten by discrete Gaussians, and posed the general $n$-fold discrete EPI as Conjecture 2.9; Madiman, Marcus, and Tetali established general submodularity and Plünnecke–Ruzsa-type inequalities for discrete entropy on $\mathbb{Z}$.
- **Log-concave integer random variables (Woo–Madiman, 2015; Bobkov–Marsiglietti–Melbourne, 2022; Gavalakis, 2023):**
  - Woo and Madiman (2015) proved discrete EPIs for symmetric unimodal / uniform-like distributions via rearrangement and majorization.
  - Bobkov, Marsiglietti, and Melbourne (2022) established explicit universal-constant discrete EPIs $e^{2H(X+Y)} \ge c\,(e^{2H(X)} + e^{2H(Y)})$ for all independent discrete log-concave distributions on $\mathbb{Z}$.
  - Gavalakis (2023) proved Tao's conjecture $H(X_1 + \cdots + X_{n+1}) \ge H(X_1 + \cdots + X_n) + \frac{1}{2}\ln\frac{n+1}{n} - o(1)$ completely under the assumption that $X_1$ is **log-concave** on $\mathbb{Z}$.
- **Binomial / Poisson regimes (Harremoës–Vignat, 2003; Johnson–Yu, 2010):** Exact discrete EPIs hold for restricted families such as binomial sums and ultra-log-concave (ULC) distributions.
- **General integer distributions:** Removing the log-concavity assumption — even for the two-summand case $n = 1$ — remains completely open.

## References

- T. Tao, "Sumset and inverse sumset theory for Shannon entropy," *Combin. Probab. Comput.*, 19(4):603–639, 2010.
- P. Harremoës and C. Vignat, "An entropy power inequality for the binomial family," *J. Inequal. Pure Appl. Math.*, 4(5):Article 93, 2003.
- J. O. Woo and M. Madiman, "A discrete entropy power inequality for uniform distributions," *Proc. IEEE ISIT*, pp. 1625–1629, 2015.
- S. G. Bobkov, A. Marsiglietti, and J. Melbourne, "Concentration functions and entropy bounds for discrete log-concave distributions," *Combin. Probab. Comput.*, 31(1):54–72, 2022.
- L. Gavalakis, "Entropy power inequality for discrete log-concave random variables," *IEEE Trans. Inf. Theory*, 69(10):6181–6190, 2023.
- M. Madiman, A. W. Marcus, and P. Tetali, "Entropy and set cardinality inequalities for partition-determined functions," *Random Structures Algorithms*, 40(4):399–424, 2012.
