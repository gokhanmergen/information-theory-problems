---
id: renyi-entropy-power-sharp
title: Sharp Constant in the Rényi Entropy Power Inequality for Order α > 1
status: open
category: entropy-inequalities
posed_by: Sergey G. Bobkov and Gennadiy P. Chistyakov; Jiange Li
posed_year: 2015
tags: [entropy-inequalities, renyi-entropy, entropy-power-inequality, young-inequality]
lean_module: InfoTheory.Problems.RenyiEntropyPowerSharp
lean_file: lean/InfoTheory/Problems/RenyiEntropyPowerSharp.lean
---

## Statement

For a continuous random vector $X$ on $\mathbb{R}^d$ ($d \ge 1$) with density $f$ and Rényi order $\alpha > 1$, let
$$h_\alpha(X) := \frac{1}{1 - \alpha} \ln \int_{\mathbb{R}^d} f(x)^\alpha\, dx$$
be its Rényi differential entropy of order $\alpha$, and define its **Rényi entropy power**
$$N_\alpha(X) := \exp\!\left(\frac{2}{d}\, h_\alpha(X)\right) = \|f\|_\alpha^{-\frac{2\alpha}{d(\alpha - 1)}}.$$
Define the dimension-free constant
$$c_*(\alpha) := \frac{(\alpha + 1)^{\frac{\alpha + 1}{\alpha - 1}}}{2 \cdot 4^{\frac{1}{\alpha - 1}} \alpha^{\frac{\alpha}{\alpha - 1}}} \;\in\; \left(\frac{1}{2}, 1\right).$$

**Conjecture (Sharp Linear Rényi Entropy Power Inequality for $\alpha > 1$).** For every order $\alpha > 1$, every dimension $d \ge 1$, and every pair of independent continuous random vectors $X, Y$ on $\mathbb{R}^d$,
$$N_\alpha(X + Y) \;\ge\; c_*(\alpha)\,\big(N_\alpha(X) + N_\alpha(Y)\big).$$

## Background

Shannon's classical Entropy Power Inequality ($\alpha \to 1^+$) gives $N_1(X + Y) \ge N_1(X) + N_1(Y)$ with constant $1$, independent of dimension $d$. In 2015, Bobkov and Chistyakov initiated the systematic study of Rényi Entropy Power Inequalities for $\alpha > 1$, proving via sharp Young convolution inequalities that a dimension-free constant $c(\alpha) > 0$ exists with $N_\alpha(X + Y) \ge c(\alpha)(N_\alpha(X) + N_\alpha(Y))$. Unlike the Shannon case ($\alpha = 1$), the sharp constant $c(\alpha)$ is strictly less than $1$ for every $\alpha > 1$: taking $X, Y$ i.i.d. uniform on the Euclidean unit ball $B_2^d$ and letting $d \to \infty$ gives
$$\lim_{d \to \infty} \frac{N_\alpha(X + Y)}{N_\alpha(X) + N_\alpha(Y)} = c_*(\alpha),$$
with $c_*(1^+) = 1$, $c_*(2) = 27/32$, and $c_*(\infty) = 1/2$.

When $N_\alpha(X) = N_\alpha(Y)$, combining Beckner–Brascamp–Lieb's sharp Young inequality with Hölder interpolation already yields the geometric-mean bound $N_\alpha(X + Y) \ge 2 c_*(\alpha) \sqrt{N_\alpha(X) N_\alpha(Y)}$, matching $c_*(\alpha)(N_\alpha(X) + N_\alpha(Y))$ on the diagonal. For unequal entropy powers $N_\alpha(X) \ne N_\alpha(Y)$, however, the geometric mean falls strictly below the arithmetic mean, and determining whether the exact sharp constant $c_*(\alpha)$ holds universally for all $X, Y$ and all $d \ge 1$ remains open.

## What is known

- **Dimension-free constant $c = 1/e$ (Bobkov–Chistyakov, 2015):** Proved $N_\alpha(X + Y) \ge \frac{1}{e}(N_\alpha(X) + N_\alpha(Y))$ for all $\alpha > 1$ and all $d \ge 1$, and $c(\infty) = 1/2$ (exact at $\alpha = \infty$ since $\|f * g\|_\infty \le \min(\|f\|_\infty, \|g\|_\infty)$).
- **Improved $\alpha$-dependent constants (Ram–Sason, 2016; Li, 2018):** Sharpened the Young-inequality optimization to obtain improved explicit constants $c(\alpha) > 1/e$ approaching $1$ as $\alpha \to 1^+$ and $1/2$ as $\alpha \to \infty$, still strictly below $c_*(\alpha)$ for general unequal summands.
- **Power-sum Rényi EPI (Bobkov–Marsiglietti, 2017; Li, 2018):** Proved $N_\alpha(X + Y)^\beta \ge N_\alpha(X)^\beta + N_\alpha(Y)^\beta$ for $\beta \ge \frac{\alpha + 1}{2}$, and refined the exponent range via sharp Young inequalities.
- **Regime $\alpha \in (0, 1)$ (Li–Marsiglietti–Melbourne, 2019):** Proved that an unrestricted linear Rényi EPI fails for general densities when $\alpha \in (0, 1)$, while recovering sharp Rényi EPIs for log-concave and $s$-concave densities.
- **Sharp linear constant $c_*(\alpha)$ for $\alpha > 1$:** Proved when $N_\alpha(X) = N_\alpha(Y)$ and in the limits $\alpha \to 1^+$ and $\alpha \to \infty$; open for general unequal $N_\alpha(X) \ne N_\alpha(Y)$ at every finite $\alpha > 1$.

## References

- S. G. Bobkov and G. P. Chistyakov, "Entropy power inequality for the Rényi entropy," *IEEE Trans. Inf. Theory*, 61(2):708–714, 2015.
- E. Ram and I. Sason, "On Rényi entropy power inequalities," *IEEE Trans. Inf. Theory*, 62(12):6800–6815, 2016.
- S. G. Bobkov and A. Marsiglietti, "Variants of the entropy power inequality," *IEEE Trans. Inf. Theory*, 63(12):7747–7752, 2017.
- J. Li, "Rényi entropy power inequality and a reverse," *Studia Math.*, 242(3):303–319, 2018.
- J. Li, A. Marsiglietti, and J. Melbourne, "Further investigations of Rényi entropy power inequalities and an entropic characterization of $s$-concave densities," in *Geometric Aspects of Functional Analysis*, Lecture Notes in Math. 2266, Springer, pp. 95–123, 2020.
