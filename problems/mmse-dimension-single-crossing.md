---
id: mmse-dimension-single-crossing
title: Matrix-SNR Single-Crossing Inequality and MMSE Dimension for Non-Gaussian Vectors
status: solved
category: statistical-info-theory
posed_by: Dongning Guo, Shlomo Shamai (Shitz), and Sergio Verdú; Yihong Wu and Sergio Verdú
posed_year: 2005
tags: [i-mmse, mmse-dimension, single-crossing, gaussian-channels, estimation-theory]
lean_module: InfoTheory.Problems.MmseDimensionSingleCrossing
lean_file: lean/InfoTheory/Problems/MmseDimensionSingleCrossing.lean
---

## Statement

Consider estimating a $d$-dimensional random vector $X \in \mathbb{R}^d$ (with finite second moment) observed through a linear additive Gaussian noise channel $Y = H X + Z$, where $H \in \mathbb{R}^{d \times d}$ has matrix SNR $S = H^\top H \succeq 0$ and $Z \sim \mathcal{N}(0, I_d)$ is independent standard Gaussian noise. Let
$$
\mathbf{E}_X(S) := \mathbb{E}\big[(X - \mathbb{E}[X \mid H X + Z])(X - \mathbb{E}[X \mid H X + Z])^\top\big]
$$
denote the $d \times d$ MMSE covariance matrix. For a Gaussian reference vector $X_G \sim \mathcal{N}(0, J^{-1})$ with positive definite precision matrix $J \succ 0$, $\mathbf{E}_{X_G}(S) = (J + S)^{-1}$.

Two closely linked estimation-theoretic problems arising from the I-MMSE framework remain open:

1. **Matrix-SNR Single-Crossing Conjecture (Bustin–Payaró–Palomar–Shamai 2013; formalized in Lean):** For any dimension $d \ge 2$, any non-Gaussian vector input $X \in \mathbb{R}^d$, any Gaussian reference precision matrix $J \succ 0$, and any pair of SNR matrices $S_1 \succeq S_0 \succeq 0$ in the Loewner positive-semidefinite order, does
$$
\mathbf{E}_X(S_0) \preceq (J + S_0)^{-1} \implies \mathbf{E}_X(S_1) \preceq (J + S_1)^{-1} \quad ?
$$
2. **MMSE Dimension Existence and Equality with Rényi Information Dimension (Wu–Verdú 2011):** For a general scalar or vector distribution $X$ (such as the singular middle-thirds Cantor distribution), determine whether the MMSE dimension $D(X) := \lim_{\gamma \to \infty} \gamma \, \operatorname{mmse}(X, \gamma)$ exists whenever the Rényi information dimension $d_R(X)$ exists, and characterize when $\underline{D}(X) = \overline{D}(X) = d_R(X)$.

## Background

Guo, Shamai, and Verdú (2005) discovered the fundamental I-MMSE identity $\frac{d}{d\gamma} I(X; \sqrt{\gamma} X + Z) = \frac{1}{2} \operatorname{mmse}(X, \gamma)$, forging a deep bridge between Shannon theory and Bayesian estimation. In scalar Gaussian channels, Guo, Wu, Shamai, and Verdú (2011) proved the celebrated **single-crossing property**: the MMSE curve of any non-Gaussian input $X$ can cross the MMSE curve of a Gaussian input at most once, from above to below, yielding short, conceptual proofs of the Entropy Power Inequality and Gaussian broadcast converses.

Extending single-crossing to general vector channels with non-commuting matrix SNRs $S_1 \succeq S_0$ — and resolving the high-SNR MMSE dimension of singular distributions (Wu–Verdú 2011) — are key open questions for MIMO Gaussian network information theory and high-SNR estimation theory.

## What is known

- **Scalar single-crossing ($d = 1$):** Guo, Wu, Shamai, and Verdú (2011) proved that $\gamma \mapsto \frac{1}{\operatorname{mmse}(X, \gamma)} - \gamma$ is nondecreasing for all scalar inputs $X$, establishing the exact scalar single-crossing property.
- **Ray-wise vector single-crossing:** Bustin, Payaró, Palomar, and Shamai (2013) proved the Loewner-order matrix single-crossing property along one-parameter scalar SNR scalings $S(\gamma) = \gamma I_d$ (using $-\frac{d}{d\gamma}\mathbf{E}_X(\gamma I_d) = \mathbb{E}[\operatorname{Cov}(X \mid Y)^2] \succeq \mathbf{E}_X(\gamma I_d)^2$), and conjectured the general matrix-SNR version for arbitrary $S_1 \succeq S_0$.
- **MMSE dimension bounds (Wu–Verdú 2011):**
  - Always $\underline{D}(X) \le \underline{d}_R(X) \le \overline{d}_R(X) \le \overline{D}(X)$ via I-MMSE and Cesàro averaging.
  - For discrete-continuous mixtures $(1 - \alpha)\mu_{\mathrm{disc}} + \alpha \mu_{\mathrm{ac}}$ on $\mathbb{R}^d$, $D(X) = d_R(X) = \alpha d$.
  - For the middle-thirds Cantor distribution the limit does **not** exist: $\gamma \, \operatorname{mmse}(X, \gamma)$ is asymptotically periodic in $\log \gamma$ (Wu–Verdú 2011, Theorem 16) and oscillates between $\underline{D}(X) \approx 0.62$ and $\overline{D}(X) \approx 0.64$ around $d_R(X) = \log_3 2$ (restated by Wu–Verdú, arXiv:1111.6822, §II: "It is possible that the MMSE dimension does not exist … consider the Cantor distribution"). The numerical oscillation range comes from computation. *(Catalog correction 2026-11-27: earlier versions said this was open.)* So "does $D(X)$ exist whenever $d_R(X)$ exists?" has a negative answer.

## Catalog note (2026-11-27): the formal statement is a theorem

The frozen Lean `Statement` (subproblem 1, matrix-SNR single crossing for finite-support inputs)
is **true by a short known argument**, so this entry is marked `solved`:

1. Along $S(t) = S_0 + t\Delta$ ($\Delta = S_1 - S_0 \succeq 0$) the MMSE matrix satisfies
   $-\tfrac{d}{dt}\mathbf{E}_X(S(t)) = \mathbb{E}[C\,\Delta\,C]$ with $C = \mathrm{Cov}(X \mid Y_t)$
   (Payaró–Palomar 2009 Jacobian / Hessian formulas for the linear vector Gaussian channel).
2. $C \mapsto C\Delta C$ is matrix-convex ($v^\top C\Delta C v = \|\Delta^{1/2} C v\|^2$), so
   $\mathbb{E}[C\Delta C] \succeq \mathbf{E}\,\Delta\,\mathbf{E}$, hence
   $\tfrac{d}{dt}\mathbf{E}^{-1} = \mathbf{E}^{-1}\mathbb{E}[C\Delta C]\mathbf{E}^{-1} \succeq \Delta$.
3. Therefore $t \mapsto \mathbf{E}(S(t))^{-1} - (J + S(t))$ is Loewner-nondecreasing; the hypothesis
   says it is $\succeq 0$ at $t = 0$, so it is $\succeq 0$ at $t = 1$, which is the conclusion
   (operator antitonicity of inversion). If $\mathbf{E}$ is singular, smooth $X \mapsto X + \sqrt{\delta}W$
   and let $\delta \to 0^+$.

This is the general-path version of the Bustin–Payaró–Palomar–Shamai ray-wise result (also
flagged by gemini-neon's audit, AGENT-BOARD 2026-11-27, with 0/276 numerical violations). Subproblem 2
in the form "does the Cantor MMSE dimension exist?" is also answered (negatively, see above), so no
faithful *open* replacement was available within this entry; retargeting the Lean statement to a
different open problem is left as a separate catalog decision. The Lean file is unchanged; a formal
proof (`theorem proof : Statement`) would be a welcome contribution.
Certificate: `lean/InfoTheory/Known/Certificates/MmseDimensionSingleCrossing.lean` (positivity of the
kernel; `E_X(H) = 0` for deterministic inputs).

## References

- D. Guo, S. Shamai (Shitz), and S. Verdú, "Mutual information and minimum mean-square error in Gaussian channels," *IEEE Trans. Inf. Theory* **51**(4), 1261–1282 (2005).
- D. Guo, Y. Wu, S. Shamai (Shitz), and S. Verdú, "Estimation in Gaussian noise: Properties of the minimum mean-square error," *IEEE Trans. Inf. Theory* **57**(4), 2371–2385 (2011).
- Y. Wu and S. Verdú, "MMSE dimension," *IEEE Trans. Inf. Theory* **57**(8), 4857–4879 (2011).
- R. Bustin, M. Payaró, D. P. Palomar, and S. Shamai (Shitz), "On MMSE properties and I-MMSE implications in parallel Gaussian broadcast channels," *IEEE Trans. Inf. Theory* **59**(2), 792–816 (2013).
- Y. Wu and S. Verdú, "Optimal phase transitions in compressed sensing," *IEEE Trans. Inf. Theory* **58**(10), 6241–6263 (2012); arXiv:1111.6822.
- M. Payaró and D. P. Palomar, "Hessian and concavity of mutual information, differential entropy, and entropy power in linear vector Gaussian channels," *IEEE Trans. Inf. Theory* **55**(8), 3613–3628 (2009).
