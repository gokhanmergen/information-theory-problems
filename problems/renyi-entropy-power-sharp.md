---
id: renyi-entropy-power-sharp
title: Sharp Constant in the Rényi Entropy Power Inequality for Order α > 1
status: solved
formal_status: statement-true
formal_status_note: "Statement = Ram–Sason (IEEE TIT 2016) Thm 1 with n = 2; c_* is sharp via uniform balls, d → ∞"
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

> **Audit (2026-11-27): this problem is solved; the inequality above is a published theorem.**
> The constant $c_*(\alpha)$ is identically the two-summand constant of Ram and Sason,
> $c_\alpha^{(2)} = \alpha^{\frac{1}{\alpha-1}}\bigl(1 - \frac{1}{2\alpha'}\bigr)^{2\alpha'-1}$ with
> $\alpha' = \frac{\alpha}{\alpha-1}$ (since $1 - \frac{1}{2\alpha'} = \frac{\alpha+1}{2\alpha}$ and
> $2\alpha' - 1 = \frac{\alpha+1}{\alpha-1}$). Ram–Sason (IEEE TIT 2016, arXiv:1601.06555), Theorem 1:
> "Let $\{X_k\}_{k=1}^n$ be independent random vectors with densities defined on $\mathbb{R}^d$ …
> Then, the following R-EPI holds: $N_\alpha(S_n) \ge c_\alpha^{(n)} \sum_{k=1}^n N_\alpha(X_k)$",
> valid for **all** independent summands, equal or unequal entropy powers, in every dimension.
> The earlier claim in this file that the unequal case was open was a catalog error (the
> geometric-mean step is not needed: Ram–Sason optimize the Young exponents directly). Combined
> with the ball computation below, $c_*(\alpha)$ is exactly the optimal dimension-free constant.
>
> *Sharpness (Laplace method).* For $X, Y$ i.i.d. uniform on the unit ball $B \subset \mathbb{R}^d$,
> $N_\alpha(X) = |B|^{2/d}$, and $f * f(z) = |B \cap (B+z)|/|B|^2$ with
> $|B \cap (B+z)|/|B| = (1 - |z|^2/4)^{d/2 + O(\log d)}$. Hence
> $\int (f*f)^\alpha = |B|^{1-\alpha} \exp\bigl(d \max_\rho [\tfrac{\alpha}{2}\ln(1-\rho^2/4) + \ln\rho] + o(d)\bigr)$,
> the maximum being at $\rho^2 = 4/(\alpha+1)$, which gives
> $N_\alpha(X+Y)/(2N_\alpha(X)) \to \frac{(\alpha+1)^{(\alpha+1)/(\alpha-1)}}{2\cdot 4^{1/(\alpha-1)}\alpha^{\alpha/(\alpha-1)}} = c_*(\alpha)$.
> (Our own computation, `[sketch]`. Ram–Sason's Remark 2 says their inequality is never attained
> for finite $\alpha$; it is approached only as $d \to \infty$.)

## What is known

- **Dimension-free constant $c = 1/e$ (Bobkov–Chistyakov, 2015):** Proved $N_\alpha(X + Y) \ge \frac{1}{e}(N_\alpha(X) + N_\alpha(Y))$ for all $\alpha > 1$ and all $d \ge 1$, and $c(\infty) = 1/2$ (exact at $\alpha = \infty$ since $\|f * g\|_\infty \le \min(\|f\|_\infty, \|g\|_\infty)$).
- **Ram–Sason (2016), Theorem 1 with $n = 2$:** $N_\alpha(X+Y) \ge c_*(\alpha)(N_\alpha(X)+N_\alpha(Y))$ for all independent $X, Y$ on $\mathbb{R}^d$, every $d$; this *is* the conjecture as stated above. Their Theorem 2 / Corollary 3 improve on it when $N_\alpha(X) \ne N_\alpha(Y)$ and agree with it when the entropy powers are equal.
- **Power-sum Rényi EPI (Bobkov–Marsiglietti, 2017; Li, 2018):** Proved $N_\alpha(X + Y)^\beta \ge N_\alpha(X)^\beta + N_\alpha(Y)^\beta$ for $\beta \ge \frac{\alpha + 1}{2}$, and refined the exponent range via sharp Young inequalities.
- **Regime $\alpha \in (0, 1)$ (Li–Marsiglietti–Melbourne, 2019):** Proved that an unrestricted linear Rényi EPI fails for general densities when $\alpha \in (0, 1)$, while recovering sharp Rényi EPIs for log-concave and $s$-concave densities.
- **Sharp linear constant $c_*(\alpha)$ for $\alpha > 1$:** settled: the lower bound is Ram–Sason's Theorem 1 and the matching upper bound comes from uniform balls as $d \to \infty$ (see the audit note above).

## References

- S. G. Bobkov and G. P. Chistyakov, "Entropy power inequality for the Rényi entropy," *IEEE Trans. Inf. Theory*, 61(2):708–714, 2015.
- E. Ram and I. Sason, "On Rényi entropy power inequalities," *IEEE Trans. Inf. Theory*, 62(12):6800–6815, 2016.
- S. G. Bobkov and A. Marsiglietti, "Variants of the entropy power inequality," *IEEE Trans. Inf. Theory*, 63(12):7747–7752, 2017.
- J. Li, "Rényi entropy power inequality and a reverse," *Studia Math.*, 242(3):303–319, 2018.
- J. Li, A. Marsiglietti, and J. Melbourne, "Further investigations of Rényi entropy power inequalities and an entropic characterization of $s$-concave densities," in *Geometric Aspects of Functional Analysis*, Lecture Notes in Math. 2266, Springer, pp. 95–123, 2020.

## Formal statement and certificate

- **Adversarial check (2026-11-27): the Lean `Statement` is a known theorem (catalog error).**
  `sharpRenyiConst α` equals Ram–Sason's `c_α^{(2)}` (machine-checked identity
  `sharpRenyiConst_eq_ramSason`), so `Statement` is Theorem 1 of Ram–Sason (2016) for `n = 2`.
  No faithful open retarget was found: with sharpness via uniform balls the optimal
  two-summand constant is determined, and the `n`-summand analogue appears to be settled by
  the same pair of arguments. The frozen Lean is left unchanged and the problem is marked
  `status: solved` / `formal_status: statement-true`. A formal proof would need the sharp
  Young inequality (Beckner; Brascamp–Lieb), which is not in Mathlib.
- **Certificate** `lean/InfoTheory/Known/Certificates/RenyiEntropyPowerSharp.lean`:
  `sharpRenyiConst_eq_ramSason`, `sharpRenyiConst_eq_ramSason'` (the Ram–Sason form with
  `α' = α/(α-1)`), the regression `sharpRenyiConst_two : c_*(2) = 27/32`, `sharpRenyiConst_pos`,
  `renyiEntropyPower_pos`.
