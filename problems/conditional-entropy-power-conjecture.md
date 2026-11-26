---
id: conditional-entropy-power-conjecture
title: Unconstrained Strong Conditional Entropy Power Inequality
status: open
category: entropy-inequalities
posed_by: Thomas A. Courtade; Mokshay Madiman and Ioannis Kontoyiannis; Ram Zamir and Meir Feder
posed_year: 2016
tags: [entropy-inequalities, entropy-power-inequality, differential-entropy, submodularity]
lean_module: InfoTheory.Problems.ConditionalEntropyPowerConjecture
lean_file: lean/InfoTheory/Problems/ConditionalEntropyPowerConjecture.lean
---

## Statement

For a continuous random vector $X$ on $\mathbb{R}^d$ ($d \ge 1$) with probability density $f_X$, let $h(X) = -\int_{\mathbb{R}^d} f_X(x) \ln f_X(x)\, dx$ be its differential entropy (in nats) and let
$$N(X) := \frac{1}{2\pi e} \exp\!\left(\frac{2}{d}\, h(X)\right)$$
be its entropy power.

**Conjecture (Unconstrained Strong / Conditional Entropy Power Inequality).** For every dimension $d \ge 1$ and every triple of mutually independent continuous random vectors $X, Y, W$ in $\mathbb{R}^d$ with finite differential entropies,
$$N(X + W)\, N(Y + W) \;\ge\; N(X + Y + W)\, N(W) + N(X)\, N(Y).$$

Equivalently, setting $V = X + Y + W$ (so that $X - (X + W) - V$ forms a Markov chain),
$$N(X + W)\, e^{-\frac{2}{d} I(X; V)} \;\ge\; N(X)\, e^{-\frac{2}{d} I(X + W; V)} + N(W).$$

## Background

Shannon's Entropy Power Inequality (EPI), $N(X + Y) \ge N(X) + N(Y)$, is one of the cornerstones of continuous information theory. Over the past three decades, a deep program led by Zamir and Feder (1993), Artstein, Ball, Barthe, and Naor (2004), Madiman and Barron (2007), Madiman and Kontoyiannis (2010), and Courtade (2016/2018) has sought to understand the complete set of inequalities governing entropy powers of sums of three or more independent random vectors (the *Stam region*).

Madiman (2008) proved that differential entropy of independent sums is submodular,
$$h(X + Y + W) + h(W) \;\le\; h(X + W) + h(Y + W),$$
which in entropy-power form reads $N(X + W) N(Y + W) \ge N(X + Y + W) N(W)$. On the other hand, Madiman and Barron (2007) showed that entropy power itself is *not* supermodular for $d \ge 2$ (and Costa's concavity of $t \mapsto N(X + \sqrt{t} Z)$ shows supermodularity fails in $d = 1$ as well), establishing instead fractional superadditivity.

In 2016/2018, Courtade proved a striking **Strong Entropy Power Inequality** that simultaneously strengthens both Shannon's EPI and Madiman's submodularity inequality whenever the common summand $W$ is **Gaussian**:
$$N(X + W)\, N(Y + W) \;\ge\; N(X + Y + W)\, N(W) + N(X)\, N(Y).$$
Equality holds whenever $X, Y, W$ are Gaussian with proportional covariance matrices (and for all 1D Gaussians). Whether this inequality remains valid when $W$ is an **arbitrary** (non-Gaussian) independent random vector — or whether a non-Gaussian counterexample exists — remains open.

## What is known

- **Gaussian common summand $W$ (Courtade, 2018):** Proved for all $d \ge 1$ and arbitrary independent $X, Y$ when $W$ is Gaussian, via an information-theoretic / data-processing proof (and later linked to forward–reverse Brascamp–Lieb inequalities by Liu, Courtade, Cuff, and Verdú).
- **All Gaussians in $\mathbb{R}^d$:** Holds with equality in $d = 1$ for arbitrary Gaussian variances $\sigma_X^2, \sigma_Y^2, \sigma_W^2$ via $(a+c)(b+c) = (a+b+c)c + ab$, and holds in all $d \ge 1$ for arbitrary positive-definite covariances via Minkowski's determinant inequality.
- **Weakened form without $+ N(X) N(Y)$ (Madiman, 2008; Kontoyiannis–Madiman, 2014):** $N(X + W) N(Y + W) \ge N(X + Y + W) N(W)$ holds unconditionally for all independent continuous random vectors $X, Y, W$ in $\mathbb{R}^d$.
- **Boundary limits:** Holds identically as $N(W) \to 0$, $N(X) \to 0$, or $N(Y) \to 0$, and holds to second order when $X, Y$ are small independent Gaussian perturbations of an arbitrary non-Gaussian $W$ (by Stam's inequality and Costa's concavity of entropy power).
- **General non-Gaussian $W$:** Neither a proof nor a counterexample is known for unconstrained independent $X, Y, W$.

## References

- T. A. Courtade, "A strong entropy power inequality," *IEEE Trans. Inf. Theory*, 64(4):2173–2192, 2018.
- M. Madiman and A. Barron, "Generalized entropy power inequalities and monotonicity properties of information," *IEEE Trans. Inf. Theory*, 53(7):2317–2329, 2007.
- M. Madiman, "On the entropy of sums," *Proc. IEEE Information Theory Workshop (ITW)*, pp. 303–307, 2008.
- I. Kontoyiannis and M. Madiman, "Sumset and inverse sumset inequalities for differential entropy and mutual information," *IEEE Trans. Inf. Theory*, 60(8):4503–4514, 2014.
- R. Zamir and M. Feder, "A generalization of the entropy power inequality with applications," *IEEE Trans. Inf. Theory*, 39(5):1723–1728, 1993.
- M. H. M. Costa, "A new entropy power inequality," *IEEE Trans. Inf. Theory*, 31(6):751–760, 1985.
