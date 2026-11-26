---
id: gaussian-optimality-mutual-information
title: Gaussian Optimality for Multi-Branch Vector Information Bottleneck Functionals
status: open
category: entropy-inequalities
posed_by: Venkat Anantharam, Varun Jog, and Chandra Nair; Thomas A. Courtade
posed_year: 2016
tags: [entropy-inequalities, gaussian-optimality, information-bottleneck, brascamp-lieb]
lean_module: InfoTheory.Problems.GaussianOptimalityMutualInformation
lean_file: lean/InfoTheory/Problems/GaussianOptimalityMutualInformation.lean
---

## Statement

Let $d \ge 1$, let $g_1, g_2$ be two centered non-degenerate multivariate Gaussian densities on $\mathbb{R}^d$, let $K \in \mathbb{R}^{d \times d}$ be a symmetric positive-definite covariance bound, and let $\beta \in (1, 2)$. Consider the constrained differential-entropy functional
$$\Phi_{\beta, g_1, g_2}(f) := \beta\, h(f) - h(f * g_1) - h(f * g_2)$$
over all probability densities $f$ on $\mathbb{R}^d$ satisfying the covariance constraint $\mathrm{Cov}(f) \preceq K$ (i.e., $\mathbb{E}_{X \sim f}[\langle v, X \rangle^2] \le v^\top K v$ for all $v \in \mathbb{R}^d$).

**Conjecture (Multi-Branch Gaussian Optimality).** For every dimension $d \ge 1$, every pair of centered Gaussian densities $g_1, g_2$ on $\mathbb{R}^d$, every positive-definite covariance bound $K$, and every $\beta \in (1, 2)$, the supremum of $\Phi_{\beta, g_1, g_2}(f)$ over all densities $f$ with $\mathrm{Cov}(f) \preceq K$ is achieved by a centered Gaussian density $f^*$ with $\mathrm{Cov}(f^*) \preceq K$:
$$\sup_{\mathrm{Cov}(f) \preceq K} \big(\beta\, h(f) - h(f * g_1) - h(f * g_2)\big) \;=\; \sup_{\substack{f^* \text{ centered Gaussian} \\ \mathrm{Cov}(f^*) \preceq K}} \big(\beta\, h(f^*) - h(f^* * g_1) - h(f^* * g_2)\big).$$

## Background

A central theme of continuous network information theory and geometric functional analysis is **Gaussian optimality**: identifying which linear combinations of differential entropies (or mutual informations) subject to covariance constraints are extremized by Gaussian distributions. For single-branch functionals of the form $h(f * g_1) - \beta h(f)$ (or equivalently $\sup_{U - X - Y} [I(U; Y) - \beta I(U; X)]$, the Gaussian Information Bottleneck of Chechik–Globerson–Tishby–Weiss 2005) and two-receiver Gaussian broadcast / wiretap differences $h(f * g_1) - h(f * g_2)$, Geng and Nair (2014) established Gaussian optimality via the **doubling trick** (inspired by Lieb's 1990 proof of Gaussian extremizability for Brascamp–Lieb inequalities).

Liu, Courtade, Cuff, and Verdú (2018) and Anantharam, Jog, and Nair (2022) embedded these results into a unified **entropic forward–reverse Brascamp–Lieb** framework. However, once a functional combines *two* negative-sign convolutions against a single positive-sign entropy — as in $\beta h(f) - h(f * g_1) - h(f * g_2)$ with $\beta \in (1, 2)$, which arises directly in the two-target vector Information Bottleneck, Gray–Wyner networks, and common-message Gaussian broadcast channels — the standard doubling argument fails to preserve the required subadditivity when the noise covariances of $g_1$ and $g_2$ do not commute. Settling Gaussian optimality for such multi-branch functionals is a major open frontier of the Brascamp–Lieb / Geng–Nair program.

## What is known

- **Single-branch Gaussian Information Bottleneck (Chechik–Globerson–Tishby–Weiss, 2005; Geng–Nair, 2014):** For $\sup_{\mathrm{Cov}(f) \preceq K} (\beta h(f) - h(f * g_1))$ with $\beta \ge 1$ (and for $h(f * g_1) - h(f * g_2)$), Gaussian optimality is completely proved via Lieb's doubling method and channel-enhancement arguments (Weingarten–Steinberg–Shamai 2006; Liu–Viswanath 2007).
- **Forward–reverse Brascamp–Lieb duality (Liu–Courtade–Cuff–Verdú, 2018; Anantharam–Jog–Nair, 2022):** Establishes Gaussian optimality for unconstrained Brascamp–Lieb data satisfying the Bennett–Carbery–Christ–Tao scaling and finiteness conditions, and clarifies when doubling arguments succeed or fail under covariance constraints.
- **Scalar and commuting cases:** In $d = 1$ or when the covariances of $g_1, g_2, K$ are simultaneously diagonalizable, the problem simplifies via scalar EPI / Costa-type arguments in certain parameter regimes, whereas general non-commuting vector covariances in $d \ge 2$ remain open.
- **Related multi-terminal problems:** Counterexamples to naive Gaussian optimality are known for some *non-convex* multi-terminal functionals (such as certain three-receiver broadcast or interference regions), making the exact boundary between Gaussian-optimal and non-Gaussian-optimal mutual-information functionals a subtle open question.

## References

- Y. Geng and C. Nair, "The capacity region of the two-receiver Gaussian vector broadcast channel with private and common messages," *IEEE Trans. Inf. Theory*, 60(4):2087–2104, 2014.
- J. Liu, T. A. Courtade, P. W. Cuff, and S. Verdú, "Information-theoretic perspectives on Brascamp–Lieb inequality," *IEEE Trans. Inf. Theory*, 64(4):2429–2447, 2018.
- V. Anantharam, V. Jog, and C. Nair, "Unifying the Brascamp–Lieb inequality and the entropy power inequality," *IEEE Trans. Inf. Theory*, 68(12):7665–7684, 2022.
- G. Chechik, A. Globerson, N. Tishby, and Y. Weiss, "Information bottleneck for Gaussian variables," *J. Mach. Learn. Res.*, 6:165–188, 2005.
- T. Liu and P. Viswanath, "An extremal inequality motivated by multiterminal information-theoretic problems," *IEEE Trans. Inf. Theory*, 53(5):1839–1851, 2007.
- E. H. Lieb, "Gaussian kernels have only Gaussian maximizers," *Invent. Math.*, 102:179–208, 1990.
