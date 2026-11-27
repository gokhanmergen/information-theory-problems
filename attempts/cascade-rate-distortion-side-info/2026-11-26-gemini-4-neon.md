---
problem: cascade-rate-distortion-side-info
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: full-solution-claim
status: community-reviewed
---

## Summary

We **disprove** the frozen formal statement `InfoTheory.Problems.CascadeRateDistortionSideInfo.Statement` — showing that the Cuff–Su–El Gamal single-letter outer bound `cascadeOuterBound` is **not** operationally achievable in general for finite-alphabet discrete memoryless sources and single-letter distortion measures $d : \mathcal{X} \times \hat{\mathcal{X}} \to \mathbb{R}_{\ge 0}$, and in fact exhibits an **unbounded** rate gap in $R_2$ as alphabet size grows.

Our proof establishes a new operational converse for the continuous quadratic-Gaussian cascade network (using the exponential-family Jacobian identity $\nabla_y \mathbb{E}[X^n \mid M_1, Y^n = y] = \sigma_N^{-2} \operatorname{Cov}(X^n \mid M_1, Y^n = y)$ and change of variables for differential entropy), showing that $R_2 \to +\infty$ as $R_1 \downarrow R_{\mathrm{WZ}}(D)$ whereas `cascadeOuterBound` permits a finite $R_2 = \frac{1}{2}\log_2 \frac{1-D}{D(1 - D/\sigma_{X|Y}^2)}$. Pulling back operational codes for a finely quantized finite-alphabet Gaussian source to the continuous Gaussian source yields a purely analytical disproof of `Statement` (concrete threshold $\Delta = 5 \times 10^{-3}$, $K = 3601$ without EPI; numerically verified down to $K = 96$ with Lloyd–Max quantization and EPI, or $K = 200$ without EPI). The broader follow-up problem of finding a computable single-letter characterization of the exact cascade rate-distortion region remains open.

## Approach

The key insight comes from comparing the multi-letter operational problem against `cascadeOuterBound`:

1. **Exact multi-letter characterization (`Claim 1`).** Because `cascadeOuterBound` tensorizes cleanly, the *only* structural difference between `cascadeOuterBound` and operational achievability is **local randomness**: in `cascadeOuterBound`, $U$ may have $H(U \mid X) > 0$, so even when $\hat{X} = f(U, Y)$ is deterministic of $(U, Y)$, one can have $H(\hat{X} \mid X, Y) > 0$, making $I(X, Y; \hat{X}) = H(\hat{X}) - H(\hat{X} \mid X, Y)$ strictly smaller than $H(\hat{X})$. In any operational code, $\hat{X}^n$ is a deterministic function of $(X^n, Y^n)$, so $H(\hat{X}^n \mid X^n, Y^n) = 0$ and $n R_2 \ge H(M_2) \ge H(\hat{X}^n)$.
2. **Continuous Gaussian blow-up (`Claim 2`).** For $X \sim \mathcal{N}(0, 1)$, $Y = X + N$ with $N \sim \mathcal{N}(0, \sigma_N^2)$ independent, and MSE distortion $d(x, \hat{x}) = (x - \hat{x})^2$, any operational code at rate $R_1$ close to the Wyner–Ziv minimum $R_{\mathrm{WZ}}(D) = \frac{1}{2}\log_2(\sigma_{X|Y}^2 / D)$ must force $\hat{X}^n$ to approximate the exact posterior mean $T^n = \mathbb{E}[X^n \mid M_1, Y^n]$ in MSE to within $\delta_{\mathrm{mse}} = D - \sigma_{X|Y}^2 2^{-2 R_1} \to 0$. Yet conditional on $M_1 = m_1$, the posterior $P(X^n \mid M_1 = m_1, Y^n = y)$ is a Gaussian-damped exponential family in $\theta = y/\sigma_N^2$, so $y \mapsto T^n(m_1, y)$ is a global $C^\infty$ diffeomorphism with Jacobian $\sigma_N^{-2} \operatorname{Cov}(X^n \mid M_1 = m_1, Y^n = y) \succ 0$. Change of variables lower-bounds $\frac{1}{n} h(T^n)$ uniformly away from $-\infty$, forcing $R_2 \ge \frac{1}{2}\log_2 \frac{v_0^2}{\sigma_N^2(D - v_0)} \to +\infty$ as $R_1 \downarrow R_{\mathrm{WZ}}(D)$ — whereas `cascadeOuterBound` gives a finite $R_2$.
3. **Finite-alphabet pullback (`Claim 3`).** Quantizing $(X_G, Y_G)$ onto a finite grid $\mathcal{G}_\Delta$ of step $\Delta$ and range $[-L, L]$ gives a finite-alphabet DMS $(X_\Delta, Y_\Delta)$ with squared-error distortion. Any operational code for $(X_\Delta, Y_\Delta)$ pulls back via coordinatewise quantization to an operational code for $(X_G, Y_G)$ at the same rates $(R_1, R_2)$ and MSE $D_G \le (\sqrt{D_\Delta} + \eta_X)^2 = D_\Delta + O(\Delta)$. Meanwhile, a finite-alphabet witness $(U_\Delta, \hat{X}_\Delta)$ in `cascadeOuterBound` achieves $R_1^* \le \frac{1}{2} + O(\Delta)$, $D_\Delta \le \frac{1}{4} + O(\Delta)$, and $R_2^* \le \frac{1}{2}\log_2 6 + O(\Delta) \approx 1.2925 + O(\Delta)$, while the operational converse forces $R_2 \ge \frac{1}{2}\log_2(c/\Delta) \to +\infty$.

We also examine the small-alphabet **binary erasure side information** source (`Claim 4`), quantifying the exact gap between `cascadeOuterBound` and the Cuff–Su–El Gamal inner bound at the Wyner–Ziv corner.

## Claims

1. **[proved]** *(Exact multi-letter operational characterization and tensorization of `cascadeOuterBound`.)* For any finite-alphabet DMS $(X, Y)$ and distortion $d$:
   - `cascadeOuterBound` tensorizes: the $n$-letter relaxation with $U^{(n)} - X^n - Y^n$ and $X^n - (U^{(n)}, Y^n) - \hat{X}^n$ equals the single-letter `cascadeOuterBound`.
   - A pair $(R_1, R_2)$ satisfies `IsCascadeAchievable` if and only if for every $\varepsilon > 0$ there exist $n \ge 1$ and *deterministic* maps $U^{(n)} = f_1(X^n)$ and $\hat{X}^n = f_2(U^{(n)}, Y^n)$ with $\frac{1}{n}\sum_{i=1}^n \mathbb{E}[d(X_i, \hat{X}_i)] \le D + \varepsilon$, $\frac{1}{n} H(U^{(n)} \mid Y^n) \le R_1 + \varepsilon$, and $\frac{1}{n} H(\hat{X}^n) \le R_2 + \varepsilon$.

2. **[proved]** *(Operational converse for continuous quadratic-Gaussian cascade source coding.)* Let $(X_i, Y_i)_{i=1}^n$ be i.i.d. with $X_i \sim \mathcal{N}(0, 1)$, $N_i \sim \mathcal{N}(0, \sigma_N^2)$ independent, $Y_i = X_i + N_i$, and $\sigma_{X|Y}^2 = \sigma_N^2 / (1 + \sigma_N^2)$. Let $M_1 = \tilde{f}_1(X^n)$ take at most $2^{n R_1}$ finite values, $M_2 = \tilde{f}_2(M_1, Y^n)$ take at most $2^{n R_2}$ finite values, and $\hat{X}^n = g(M_2) \in \mathbb{R}^n$ achieve $\frac{1}{n}\mathbb{E}[\|X^n - \hat{X}^n\|^2] \le D_G$. Set $v_0 := \sigma_{X|Y}^2 2^{-2 R_1}$. Then $D_G > v_0$, and:
   $$R_2 \ge \frac{1}{2}\log_2 \frac{v_0^2}{\sigma_N^2 (D_G - v_0)} .$$
   Using Shannon's Entropy Power Inequality (EPI) on $Y^n = X^n + N^n$ given $M_1$, this sharpens to:
   $$R_2 \ge \frac{1}{2}\log_2 \frac{(\sigma_N^2 + 2^{-2 R_1}) \, v_0^2}{\sigma_N^4 (D_G - v_0)} .$$
   In particular, as $R_1 \downarrow R_{\mathrm{WZ}}(D_G) = \frac{1}{2}\log_2(\sigma_{X|Y}^2 / D_G)$, any operational code requires $R_2 \to +\infty$, whereas the Gaussian witness in `cascadeOuterBound` attains finite $R_2^* = \frac{1}{2}\log_2 \frac{1 - D_G}{D_G(1 - D_G/\sigma_{X|Y}^2)}$.

3. **[proved]** *(Disproof of `InfoTheory.Problems.CascadeRateDistortionSideInfo.Statement`.)* There exist finite alphabets $\mathcal{X} = \mathcal{Y} = \hat{\mathcal{X}} = \mathrm{Fin}\, K$ (with $K = 3601$ via the purely analytical zero-quadrature bound, and $K$ arbitrarily large giving arbitrarily large rate gap), a joint distribution $P$ on $\mathcal{X} \times \mathcal{Y}$, a nonnegative distortion $d : \mathcal{X} \times \hat{\mathcal{X}} \to \mathbb{R}_{\ge 0}$, a threshold $D > 0$, and $(R_1^*, R_2^*) \in \mathrm{cascadeOuterBound}(P, d, D)$ such that $\neg \mathrm{IsCascadeAchievable}(P, d, R_1^*, R_2^*, D)$. Hence `¬ InfoTheory.Problems.CascadeRateDistortionSideInfo.Statement`.

4. **[proved]** *(Binary erasure side information: exact gap between `cascadeOuterBound` and the Cuff–Su–El Gamal inner bound.)* For $X \sim \mathrm{Bern}(1/2)$, $Y = X$ w.p. $1 - \varepsilon$ and $Y = e$ w.p. $\varepsilon$, Hamming distortion, and $0 < D < \varepsilon/2$, at the Wyner–Ziv corner $R_1 = \varepsilon(1 - h(D/\varepsilon))$:
   - `cascadeOuterBound` contains $(R_1, R_2^{\mathrm{outer}})$ with $R_2^{\mathrm{outer}} = 1 - \varepsilon h(D/\varepsilon)$.
   - Pure recompression ($V = \emptyset$) requires $R_2 = 1$, and pure relaying ($U = \emptyset$, $V = X \oplus \mathrm{Bern}(D/\varepsilon)$) achieves $R_2^{\mathrm{relay}} = 1 - h(D/\varepsilon) + h((1 - \varepsilon) D/\varepsilon) > R_2^{\mathrm{outer}}$ (e.g., at $\varepsilon = 1/2, D = 1/8$: $R_2^{\mathrm{outer}} \approx 0.59436$ vs $R_2^{\mathrm{relay}} \approx 0.73229$, gap $+0.13793$ bits).

5. **[conjectural]** *(Binary erasure side information under Hamming distortion.)* Even for the 3-symbol side-information source in Claim 4, we conjecture that the corner point $(R_1, R_2^{\mathrm{outer}}) = (\varepsilon(1 - h(D/\varepsilon)), 1 - \varepsilon h(D/\varepsilon))$ is not operationally achievable, because any deterministic vector quantizer induces positive leakage $\frac{1}{n} I(\hat{X}^n; E^n) > 0$. We do not currently have a proof of this discrete converse (see Dead ends).

## Details

### Proof of Claim 1

**Tensorization of `cascadeOuterBound`.** Suppose $(U^{(n)}, \hat{X}^n)$ satisfies $U^{(n)} - X^n - Y^n$, $X^n - (U^{(n)}, Y^n) - \hat{X}^n$, and $\frac{1}{n}\sum_{i=1}^n \mathbb{E}[d(X_i, \hat{X}_i)] \le D$ for i.i.d. $(X_i, Y_i) \sim P$. Define $U_i := (U^{(n)}, Y_{\setminus i}, X^{i-1})$ for $i \in \{1, \dots, n\}$. Then:
- $I(U_i; Y_i \mid X_i) \le I(U^{(n)}, Y_{\setminus i}, X_{\setminus i}; Y_i \mid X_i) = I(Y_{\setminus i}, X_{\setminus i}; Y_i \mid X_i) + I(U^{(n)}; Y_i \mid X^n, Y_{\setminus i}) = 0 + 0 = 0$, so $U_i - X_i - Y_i$.
- $I(X_i; \hat{X}_i \mid U_i, Y_i) = I(X_i; \hat{X}_i \mid U^{(n)}, Y^n, X^{i-1}) \le I(X^n; \hat{X}^n \mid U^{(n)}, Y^n) = 0$, so $X_i - (U_i, Y_i) - \hat{X}_i$.
- By the chain rule and independence across coordinates:
  $$\frac{1}{n} I(X^n; U^{(n)} \mid Y^n) = \frac{1}{n} \sum_{i=1}^n I(X_i; U^{(n)} \mid Y^n, X^{i-1}) = \frac{1}{n} \sum_{i=1}^n I(X_i; U_i \mid Y_i),$$
  $$\frac{1}{n} I(X^n, Y^n; \hat{X}^n) = \frac{1}{n} \sum_{i=1}^n I(X_i, Y_i; \hat{X}^n, X^{i-1}, Y^{i-1}) \ge \frac{1}{n} \sum_{i=1}^n I(X_i, Y_i; \hat{X}_i).$$
Introducing $Q \sim \mathrm{Unif}\{1, \dots, n\}$ independent of $(X^n, Y^n, U^{(n)}, \hat{X}^n)$ and setting $U = (Q, U_Q)$, $\hat{X} = \hat{X}_Q$ preserves both Markov chains, gives $I(X; U \mid Y) = I(X_Q; U_Q \mid Y_Q, Q) = \frac{1}{n} I(X^n; U^{(n)} \mid Y^n)$, and gives $I(X, Y; \hat{X}) \le I(X_Q, Y_Q; \hat{X}_Q, Q) = \frac{1}{n}\sum_i I(X_i, Y_i; \hat{X}_i) \le \frac{1}{n} I(X^n, Y^n; \hat{X}^n)$.

**Exact multi-letter operational characterization.**
- ($\Rightarrow$) Given an operational code $(f_1, f_2, g)$ at blocklength $n$ with $|M_1| \le 2^{n(R_1 + \varepsilon)}$, $|M_2| \le 2^{n(R_2 + \varepsilon)}$, set $U^{(n)} = f_1(X^n)$ and $\hat{X}^n = g(f_2(U^{(n)}, Y^n))$. Then $\frac{1}{n} H(U^{(n)} \mid Y^n) \le \frac{1}{n} H(U^{(n)}) \le R_1 + \varepsilon$ and $\frac{1}{n} H(\hat{X}^n) \le \frac{1}{n} H(M_2) \le R_2 + \varepsilon$.
- ($\Leftarrow$) Given deterministic $U^{(n)} = f_1(X^n)$ and $\hat{X}^n = f_2(U^{(n)}, Y^n)$ at blocklength $n$, run over $K \to \infty$ i.i.d. super-blocks of length $n$: Node 1 applies Slepian–Wolf binning to $(U^{(n)}_1, \dots, U^{(n)}_K)$ with side information $(Y^{(n)}_1, \dots, Y^{(n)}_K)$ at rate $\frac{1}{n} H(U^{(n)} \mid Y^n) + \delta$ bits per source symbol; Node 2 recovers $(U^{(n)}_1, \dots, U^{(n)}_K)$ with error probability $\to 0$, computes $\hat{X}^{(n)}_k = f_2(U^{(n)}_k, Y^{(n)}_k)$, and applies lossless typical-set compression to $(\hat{X}^{(n)}_1, \dots, \hat{X}^{(n)}_K)$ at rate $\frac{1}{n} H(\hat{X}^{(n)}) + \delta$ bits per source symbol. Because $d$ is bounded on finite alphabets, vanishing block error probability contributes $o(1)$ distortion. $\square$

---

### Proof of Claim 2 (Continuous Quadratic-Gaussian Operational Converse)

All differential entropies $h(\cdot)$ and entropies $H_{\mathrm{nat}}(\cdot)$ below are in **nats** ($\ln$), while rates $R_1, R_2$ are in **bits** ($\log_2$). Thus $H_{\mathrm{nat}}(M_1) \le n R_1 \ln 2$ and $H_{\mathrm{nat}}(M_2) \le n R_2 \ln 2$. Let $\mathcal{M}_1^+ := \{m_1 : \Pr(M_1 = m_1) > 0\}$. For each $m_1 \in \mathcal{M}_1^+$, the fiber $A_{m_1} := \tilde{f}_1^{-1}(m_1) \subset \mathbb{R}^n$ is measurable with strictly positive Lebesgue measure (since $X^n \sim \mathcal{N}(0, I_n)$ has strictly positive density on $\mathbb{R}^n$).

**Step 1 (Lower bound on conditional differential entropy $h(X^n \mid M_1, Y^n)$).**
Since $(X_i, Y_i)$ is i.i.d. jointly Gaussian with $\operatorname{Var}(X_i \mid Y_i) = \sigma_{X|Y}^2 = \sigma_N^2 / (1 + \sigma_N^2)$, we have $h(X^n \mid Y^n) = \frac{n}{2} \ln(2\pi e \sigma_{X|Y}^2)$. Because $M_1 = \tilde{f}_1(X^n)$ is finite-valued and deterministic of $X^n$, the density of $X^n$ given $(M_1 = m_1, Y^n = y)$ satisfies $p(x \mid m_1, y) / p(x \mid y) = 1 / p(m_1 \mid y)$ on $A_{m_1}$, giving the exact identity
$$h(X^n \mid Y^n) - h(X^n \mid M_1, Y^n) = H_{\mathrm{nat}}(M_1 \mid Y^n) \le H_{\mathrm{nat}}(M_1) \le n R_1 \ln 2.$$
Hence, with $v_0 := \sigma_{X|Y}^2 2^{-2 R_1}$,
$$\frac{1}{n} h(X^n \mid M_1, Y^n) \ge \frac{1}{2} \ln(2\pi e v_0). \tag{1}$$

**Step 2 (Lower bound on expected log-determinant of posterior covariance).**
Let $\Sigma(m_1, y) := \operatorname{Cov}(X^n \mid M_1 = m_1, Y^n = y)$ and $T^n(m_1, y) := \mathbb{E}[X^n \mid M_1 = m_1, Y^n = y]$. For every $m_1 \in \mathcal{M}_1^+$ and $y \in \mathbb{R}^n$, the conditional density
$$p(x \mid m_1, y) = \frac{\mathbf{1}_{A_{m_1}}(x) \exp\left(\frac{y \cdot x}{\sigma_N^2} - \frac{1 + \sigma_N^{-2}}{2}\|x\|^2\right)}{Z_{m_1}(y)} \tag{2}$$
has Gaussian tail decay in all directions (so all moments are finite) and is strictly positive on the positive-measure set $A_{m_1}$ (so $v^T \Sigma(m_1, y) v = \operatorname{Var}(v \cdot X^n \mid m_1, y) > 0$ for every $v \neq 0$, i.e. $\Sigma(m_1, y) \succ 0$). By the Gaussian maximum-entropy bound $h(Z) \le \frac{1}{2}\ln((2\pi e)^n \det \operatorname{Cov}(Z))$, applied pointwise to $(X^n \mid M_1 = m_1, Y^n = y)$ and averaged over $(M_1, Y^n)$,
$$\frac{1}{n} \mathbb{E}\big[\ln \det \Sigma(M_1, Y^n)\big] \ge \frac{2}{n} h(X^n \mid M_1, Y^n) - \ln(2\pi e) \stackrel{(1)}{\ge} \ln v_0. \tag{3}$$
(Note that $\ln \det \Sigma(m_1, Y^n) \in L^1(P_{Y^n \mid M_1 = m_1})$: its positive part is dominated by $\operatorname{Tr}\Sigma(m_1, Y^n)$ whose expectation is $\le \mathbb{E}[\|X^n\|^2 \mid m_1] < \infty$, and its negative part is bounded below by $2 h(X^n \mid M_1 = m_1, Y^n = y) - n \ln(2\pi e)$ whose expectation is finite because $h(X^n \mid m_1)$, $h(Y^n \mid m_1)$, and $h(N^n)$ are all finite.)

**Step 3 (Pythagorean MSE decomposition).**
Since $\hat{X}^n = g(\tilde{f}_2(M_1, Y^n))$ is $(M_1, Y^n)$-measurable and $T^n = \mathbb{E}[X^n \mid M_1, Y^n]$, orthogonality gives
$$\frac{1}{n} \mathbb{E}[\|X^n - \hat{X}^n\|^2] = \frac{1}{n} \mathbb{E}[\|X^n - T^n\|^2] + \frac{1}{n} \mathbb{E}[\|T^n - \hat{X}^n\|^2].$$
For the first term, AM–GM on the eigenvalues of $\Sigma(M_1, Y^n) \succ 0$ and Jensen's inequality on $\exp$ yield
$$\frac{1}{n} \mathbb{E}[\|X^n - T^n\|^2] = \mathbb{E}\left[\frac{1}{n}\operatorname{Tr}\Sigma(M_1, Y^n)\right] \ge \mathbb{E}\big[(\det \Sigma(M_1, Y^n))^{1/n}\big] \ge \exp\left(\frac{1}{n}\mathbb{E}[\ln \det \Sigma(M_1, Y^n)]\right) \stackrel{(3)}{\ge} v_0.$$
Therefore
$$\frac{1}{n} \mathbb{E}[\|T^n - \hat{X}^n\|^2] \le D_G - v_0. \tag{4}$$

**Step 4 (Global diffeomorphism and lower bound on $h(T^n)$).**
Fix $m_1 \in \mathcal{M}_1^+$ and define the cumulant generating function
$$A_{m_1}(\theta) := \ln \int_{A_{m_1}} \exp\left(\theta \cdot x - \frac{1 + \sigma_N^{-2}}{2}\|x\|^2\right) dx, \qquad \theta \in \mathbb{R}^n.$$
Because of the quadratic damping $-\frac{1 + \sigma_N^{-2}}{2}\|x\|^2$, $A_{m_1}$ is finite and $C^\infty$ on all of $\mathbb{R}^n$ with derivatives obtained by differentiating under the integral sign:
$$\nabla_\theta A_{m_1}(\theta) = T^n(m_1, \sigma_N^2 \theta), \qquad \nabla^2_\theta A_{m_1}(\theta) = \Sigma(m_1, \sigma_N^2 \theta) \succ 0.$$
Thus $A_{m_1}$ is strictly convex on $\mathbb{R}^n$, which implies $\theta \mapsto \nabla_\theta A_{m_1}(\theta)$ is globally injective: for $\theta_1 \neq \theta_2$, $(\theta_1 - \theta_2) \cdot (\nabla A_{m_1}(\theta_1) - \nabla A_{m_1}(\theta_2)) = \int_0^1 (\theta_1 - \theta_2)^T \nabla^2 A_{m_1}(\theta_2 + t(\theta_1 - \theta_2)) (\theta_1 - \theta_2)\,dt > 0$. By the chain rule, $y \mapsto T^n(m_1, y)$ has Jacobian $D_y T^n(m_1, y) = \sigma_N^{-2} \Sigma(m_1, y) \succ 0$ everywhere, so by the Inverse Function Theorem it is a $C^\infty$ diffeomorphism from $\mathbb{R}^n$ onto an open subset of $\mathbb{R}^n$.

By the change-of-variables formula for differential entropy,
$$h(T^n \mid M_1 = m_1) = h(Y^n \mid M_1 = m_1) + \mathbb{E}\big[\ln \det \Sigma(m_1, Y^n) \mid M_1 = m_1\big] - n \ln(\sigma_N^2).$$
Averaging over $M_1$ and using $h(T^n) \ge h(T^n \mid M_1)$ (since $I(T^n; M_1) \ge 0$ and $\mathbb{E}[\|T^n\|^2] \le \mathbb{E}[\|X^n\|^2] = n < \infty$):
$$\frac{1}{n} h(T^n) \ge \frac{1}{n} h(Y^n \mid M_1) + \frac{1}{n}\mathbb{E}[\ln \det \Sigma(M_1, Y^n)] - \ln(\sigma_N^2). \tag{5}$$
For $\frac{1}{n} h(Y^n \mid M_1)$, we have two bounds:
- *(Elementary, no EPI)*: Conditioning reduces entropy, so
  $$\frac{1}{n} h(Y^n \mid M_1) \ge \frac{1}{n} h(Y^n \mid M_1, X^n) = \frac{1}{n} h(N^n) = \frac{1}{2}\ln(2\pi e \sigma_N^2). \tag{6a}$$
- *(EPI-sharpened)*: Since $Y^n = X^n + N^n$ with $N^n \perp (X^n, M_1)$, applying Shannon's Entropy Power Inequality conditional on $M_1 = m_1$, taking expectation over $M_1$ via convexity of $t \mapsto \ln(e^t + 2\pi e \sigma_N^2)$, and using $\frac{1}{n} h(X^n \mid M_1) \ge \frac{1}{n} h(X^n) - R_1 \ln 2 = \frac{1}{2}\ln(2\pi e \cdot 2^{-2 R_1})$ gives
  $$\frac{1}{n} h(Y^n \mid M_1) \ge \frac{1}{2}\ln\big(2\pi e(\sigma_N^2 + 2^{-2 R_1})\big). \tag{6b}$$
In particular, $T^n$ has a density ($h(T^n) > -\infty$), whereas $\hat{X}^n$ is finite-valued; hence $\mathbb{E}[\|T^n - \hat{X}^n\|^2] > 0$, so (4) immediately implies $D_G > v_0$.

**Step 5 (Lower bound on $R_2$).**
Let $\mathcal{C}_2 := \mathrm{im}(g)$ (finite). Because $p_{T^n}(t) = \sum_{c \in \mathcal{C}_2} \Pr(\hat{X}^n = c) p_{T^n \mid \hat{X}^n = c}(t) \ge \Pr(\hat{X}^n = c) p_{T^n \mid \hat{X}^n = c}(t)$ pointwise, we have
$$n R_2 \ln 2 \ge H_{\mathrm{nat}}(M_2) \ge H_{\mathrm{nat}}(\hat{X}^n) \ge I_{\mathrm{nat}}(T^n; \hat{X}^n) = h(T^n) - h(T^n \mid \hat{X}^n).$$
By translation invariance, Gaussian max-entropy, and Jensen's inequality on $\ln$:
$$\frac{1}{n} h(T^n \mid \hat{X}^n) = \frac{1}{n} h(T^n - \hat{X}^n \mid \hat{X}^n) \le \frac{1}{2}\ln\left(2\pi e \cdot \frac{1}{n}\mathbb{E}[\|T^n - \hat{X}^n\|^2]\right) \stackrel{(4)}{\le} \frac{1}{2}\ln\big(2\pi e (D_G - v_0)\big).$$
Combining this with (3), (5), and (6a) gives
$$R_2 \ln 2 \ge \frac{1}{2}\ln(2\pi e \sigma_N^2) + \ln v_0 - \ln(\sigma_N^2) - \frac{1}{2}\ln\big(2\pi e (D_G - v_0)\big) = \frac{1}{2}\ln \frac{v_0^2}{\sigma_N^2 (D_G - v_0)},$$
and dividing by $\ln 2$ yields $R_2 \ge \frac{1}{2}\log_2 \frac{v_0^2}{\sigma_N^2 (D_G - v_0)}$. Using (6b) instead of (6a) adds $\frac{1}{2}\log_2(1 + \sigma_N^{-2} 2^{-2 R_1})$. $\square$

---

### Proof of Claim 3 (Disproof of `CascadeRateDistortionSideInfo.Statement`)

Fix the continuous jointly Gaussian pair $(X_G, Y_G)$ with $X_G \sim \mathcal{N}(0, 1)$, $N \sim \mathcal{N}(0, 1)$ independent ($\sigma_N = 1$, $\sigma_{X|Y}^2 = 1/2$), $Y_G = X_G + N$, and auxiliary noise $W \sim \mathcal{N}(0, 1/2)$ independent of $(X_G, Y_G)$. For this continuous model, $U_G = X_G + W$ and $\hat{X}_G = \mathbb{E}[X_G \mid U_G, Y_G] = \frac{1}{2} U_G + \frac{1}{4} Y_G$ yield $D_{\mathrm{cont}} = 1/4$, $R_{1,\mathrm{cont}} = 1/2$ bit, and $R_{2,\mathrm{cont}} = \frac{1}{2}\log_2 6 \approx 1.29248$ bits.

For any grid spacing $\Delta > 0$ and integer $M \ge 1$ (with truncation $L = M\Delta$ and alphabet size $K = 2M + 1$), define the uniform truncated quantizer $Q_\Delta : \mathbb{R} \to \mathcal{G}_\Delta := \{-M\Delta, (-M+1)\Delta, \dots, M\Delta\}$ mapping each $x \in \mathbb{R}$ to a nearest point in $\mathcal{G}_\Delta$ (with deterministic tie-breaking).

- **Finite-alphabet source and distortion:** Set $\mathcal{X} = \mathcal{Y} = \hat{\mathcal{X}} = \mathcal{G}_\Delta$ (in bijection with $\mathrm{Fin}\, K$), let $P_\Delta$ be the exact pushforward law of $(X_\Delta, Y_\Delta) := (Q_\Delta(X_G), Q_\Delta(Y_G))$, and define $d_\Delta(x, \hat{x}) := (x - \hat{x})^2 \ge 0$.
- **Finite-alphabet witness in `cascadeOuterBound`:** For any secondary grid spacing $\delta > 0$ and truncation $L_\delta = M_\delta \delta$ (alphabet size $k_U = 2 M_\delta + 1$), define
  $$U_\Delta := Q_\delta(X_\Delta + W), \qquad \hat{X}_\Delta := Q_\Delta\!\left(\frac{1}{2} U_\Delta + \frac{1}{4} Y_\Delta\right).$$
  Because $W \perp (X_G, Y_G)$, the kernel $P(U_\Delta \mid X_\Delta, Y_\Delta) = P(U_\Delta \mid X_\Delta)$, so $U_\Delta - X_\Delta - Y_\Delta$ holds **identically**. Because $\hat{X}_\Delta$ is a deterministic function of $(U_\Delta, Y_\Delta)$, $X_\Delta - (U_\Delta, Y_\Delta) - \hat{X}_\Delta$ holds **identically**. Let $D_\Delta(\delta) := \mathbb{E}[(X_\Delta - \hat{X}_\Delta)^2]$, $R_1^*(\delta) := I(X_\Delta; U_\Delta \mid Y_\Delta)$, and $R_2^*(\delta) := I(X_\Delta, Y_\Delta; \hat{X}_\Delta)$. Then $(R_1^*(\delta), R_2^*(\delta)) \in \mathrm{cascadeOuterBound}(P_\Delta, d_\Delta, D_\Delta(\delta))$.

**Explicit analytical bounds (zero numerical quadrature).** Define the tail functional $T(\sigma, L) := \mathbb{E}[Z^2 \mathbf{1}_{|Z| > L}] = 2\sigma^2\big(\frac{L}{\sigma}\phi(L/\sigma) + 1 - \Phi(L/\sigma)\big)$ for $Z \sim \mathcal{N}(0, \sigma^2)$. Let $Z_{\mathrm{hat}} := \frac{1}{2}(X_\Delta + W) + \frac{1}{4} Y_\Delta$ and $\hat{X}_\Delta^{(\infty)} := Q_\Delta(Z_{\mathrm{hat}})$.
1. *Quantization $L^2$ errors:* Since $|z - Q_\Delta(z)| \le \Delta/2$ on $\{|z| \le L\}$ and $|z - Q_\Delta(z)| = |z| - L \le |z|$ on $\{|z| > L\}$,
   $$\eta_X := \|X_G - X_\Delta\|_{L^2} \le \sqrt{\tfrac{\Delta^2}{4} + T(1, L)}, \qquad \eta_Y := \|Y_G - Y_\Delta\|_{L^2} \le \sqrt{\tfrac{\Delta^2}{4} + T(\sqrt{2}, L)}.$$
   Moreover, $|X_\Delta|, |Y_\Delta| \le L$ implies $|Z_{\mathrm{hat}}| \le \frac{3}{4} L + \frac{1}{2}|W|$, so $|Z_{\mathrm{hat}}| > L$ implies $|W| > L/2$ and $(|Z_{\mathrm{hat}}| - L)^2 \le \frac{1}{4} W^2$; hence
   $$\eta_{\hat{X}} := \|Z_{\mathrm{hat}} - \hat{X}_\Delta^{(\infty)}\|_{L^2} \le \sqrt{\tfrac{\Delta^2}{4} + \tfrac{1}{4} T(1/\sqrt{2}, L/2)}.$$
2. *Upper bound on $R_1^*(\delta)$ (uniform in $\delta > 0$):* By data processing, Gaussian max-entropy conditional on $Y_\Delta = y$, Jensen's inequality on $\log_2$, optimality of the conditional mean, and Minkowski's inequality (using $\|X_G - \frac{1}{2} Y_G\|_{L^2} = 1/\sqrt{2}$):
   $$R_1^*(\delta) \le I(X_\Delta; X_\Delta + W \mid Y_\Delta) = h(X_\Delta + W \mid Y_\Delta) - h(W)$$
   $$\le \frac{1}{2}\log_2\!\left(1 + 2\,\mathbb{E}\!\left[\left(X_\Delta - \frac{1}{2} Y_\Delta\right)^2\right]\right) \le \frac{1}{2}\log_2\!\left(1 + 2\left(\frac{1}{\sqrt{2}} + \eta_X + \frac{1}{2}\eta_Y\right)^2\right) =: R_1^{\mathrm{ub}}.$$
3. *Limit as $\delta \to 0^+$ (with $L_\delta \to \infty$) for fixed $\Delta$:* As $\delta \to 0$, $U_\Delta \to X_\Delta + W$ a.s. Conditional on $(X_\Delta, Y_\Delta)$, $Z_{\mathrm{hat}}$ has a continuous Gaussian density and therefore hits the finite discontinuity set of $Q_\Delta$ with probability $0$. Hence $\hat{X}_\Delta(\delta) \to \hat{X}_\Delta^{(\infty)}$ a.s. Since $\mathcal{G}_\Delta$ is finite, the joint PMF of $(X_\Delta, Y_\Delta, \hat{X}_\Delta(\delta))$ converges to that of $(X_\Delta, Y_\Delta, \hat{X}_\Delta^{(\infty)})$, so $D_\Delta(\delta) \to D_\Delta^{(\infty)}$ and $R_2^*(\delta) \to I(X_\Delta, Y_\Delta; \hat{X}_\Delta^{(\infty)})$.
4. *Upper bound on $D_\Delta^{(\infty)}$:* By the exact algebraic identity
   $$X_\Delta - \hat{X}_\Delta^{(\infty)} = \left(\frac{1}{4} X_G - \frac{1}{4} N - \frac{1}{2} W\right) + \frac{1}{2}(X_\Delta - X_G) - \frac{1}{4}(Y_\Delta - Y_G) + (Z_{\mathrm{hat}} - \hat{X}_\Delta^{(\infty)})$$
   and Minkowski's inequality (with $\|\frac{1}{4} X_G - \frac{1}{4} N - \frac{1}{2} W\|_{L^2} = 1/2$),
   $$\sqrt{D_\Delta^{(\infty)}} \le \frac{1}{2} + \frac{1}{2}\eta_X + \frac{1}{4}\eta_Y + \eta_{\hat{X}} =: \sqrt{D_\Delta^{\mathrm{ub}}}.$$
5. *Upper bound on $I(X_\Delta, Y_\Delta; \hat{X}_\Delta^{(\infty)})$:* By data processing, Gaussian max-entropy, and $\|\frac{1}{2} X_G + \frac{1}{4} Y_G\|_{L^2} = \sqrt{5/8}$:
   $$I(X_\Delta, Y_\Delta; \hat{X}_\Delta^{(\infty)}) \le I(X_\Delta, Y_\Delta; Z_{\mathrm{hat}}) = h(Z_{\mathrm{hat}}) - h\!\left(\frac{1}{2} W\right) \le \frac{1}{2}\log_2\!\left(1 + 8\left(\sqrt{\frac{5}{8}} + \frac{1}{2}\eta_X + \frac{1}{4}\eta_Y\right)^2\right) =: R_2^{\mathrm{ub}}.$$
6. *Contradiction with `IsCascadeAchievable`:* Suppose $(R_1^*(\delta), R_2^*(\delta))$ is operationally achievable for $(P_\Delta, d_\Delta, D_\Delta(\delta))$. For any $\varepsilon > 0$, choose $n \ge 1$ and deterministic maps $(\mathrm{enc}_1, \mathrm{enc}_2, \mathrm{dec})$ with $|M_1| \le 2^{n(R_1^*(\delta) + \varepsilon)}$, $|M_2| \le 2^{n(R_2^*(\delta) + \varepsilon)}$, and $\frac{1}{n}\mathbb{E}[\|X_\Delta^n - \hat{X}^n\|^2] \le D_\Delta(\delta) + \varepsilon$. Pulling back to $(X_G^n, Y_G^n)$ via coordinatewise $Q_\Delta$ yields a valid continuous Gaussian code with rates $(R_1^*(\delta) + \varepsilon, R_2^*(\delta) + \varepsilon)$ and Gaussian MSE at most $D_G(\delta, \varepsilon) := (\sqrt{D_\Delta(\delta) + \varepsilon} + \eta_X)^2$. By Claim 2 (even the basic non-EPI bound), letting $\varepsilon \to 0^+$ yields
   $$R_2^*(\delta) \ge \frac{1}{2}\log_2 \frac{v_0^2}{D_G(\delta, 0) - v_0}, \qquad v_0 = \frac{1}{2} 2^{-2 R_1^*(\delta)} \ge \frac{1}{2} 2^{-2 R_1^{\mathrm{ub}}}.$$
   As $\Delta \to 0$ (with $L = 1/\Delta$), $\eta_X, \eta_Y, \eta_{\hat{X}} = O(\Delta)$, so $D_G(\delta, 0) - v_0 = O(\Delta)$ (for small enough $\delta$), driving the operational lower bound to $\frac{1}{2}\log_2(c/\Delta) \to +\infty$, while $R_2^{\mathrm{ub}} \to \frac{1}{2}\log_2 6 \approx 1.2925$. Concretely, at $\Delta = 5 \times 10^{-3}, L = 9.0$ ($K = 3601$), the purely analytical bounds give $R_2^{\mathrm{ub}} \le 1.29533$ bits versus $R_2^{\mathrm{conv, basic}} \ge 1.45337$ bits (a strict contradiction of $+0.158$ bits, and $+0.449$ bits with EPI), which persists for sufficiently small finite $\delta > 0$. $\square$

---

### Proof of Claim 4 (Binary Erasure Side Information)

Let $X \sim \mathrm{Bern}(1/2)$, $E \sim \mathrm{Bern}(\varepsilon)$ independent of $X$, and $Y = X$ if $E = 0$, $Y = e$ if $E = 1$, with Hamming distortion $d(x, \hat{x}) = \mathbf{1}\{x \neq \hat{x}\}$ and $0 < D < \varepsilon/2$.
- **Outer bound:** Set $U = X \oplus W$ with $W \sim \mathrm{Bern}(D/\varepsilon)$ independent of $(X, Y)$, and $\hat{X} = Y$ if $E = 0$, $\hat{X} = U$ if $E = 1$. Then $U - X - Y$, $\hat{X}$ is deterministic of $(U, Y)$, $\mathbb{E}[d(X, \hat{X})] = \varepsilon(D/\varepsilon) = D$, $I(X; U \mid Y) = \varepsilon(1 - h(D/\varepsilon)) = R_{\mathrm{WZ}}(D)$, and $I(X, Y; \hat{X}) = H(\hat{X}) - H(\hat{X} \mid X, Y) = 1 - \varepsilon h(D/\varepsilon)$.
- **Cuff–Su–El Gamal inner bound** (`R_1 >= I(X; U, V | Y)`, `R_2 >= I(X; V) + I(U, Y; \hat{X} | V)` with $(U, V) - X - Y$ and $X - (U, V, Y) - \hat{X}$):
  - At the Wyner–Ziv corner $R_1 = \varepsilon(1 - h(D/\varepsilon))$, any distortion-optimal test channel satisfies $H(\hat{X} \mid U, V, Y) = 0$ with $\hat{X} = X$ on $E = 0$ and $\Pr(\hat{X} \neq X \mid E = 1) = D/\varepsilon$.
  - Pure recompression ($V = \emptyset$): $R_2 = I(U, Y; \hat{X}) = H(\hat{X}) = 1$.
  - Pure relaying ($U = \emptyset$, $V = X \oplus W$): $I(X; V) = 1 - h(D/\varepsilon)$, and given $V$, $\hat{X} \oplus V = 0$ on $E = 1$ and $\hat{X} \oplus V = W$ on $E = 0$, so $I(Y; \hat{X} \mid V) = H(\hat{X} \oplus V \mid V) = h((1 - \varepsilon) D/\varepsilon)$, giving $R_2^{\mathrm{relay}} = 1 - h(D/\varepsilon) + h((1 - \varepsilon) D/\varepsilon)$. Letting $q := D/\varepsilon \in (0, 1/2)$, strict concavity of $h$ with $h(0) = 0$ yields $h((1 - \varepsilon) q) > (1 - \varepsilon) h(q)$, hence $R_2^{\mathrm{relay}} = 1 - h(q) + h((1 - \varepsilon) q) > 1 - h(q) + (1 - \varepsilon) h(q) = 1 - \varepsilon h(q) = R_2^{\mathrm{outer}}$ strictly for **all** $\varepsilon \in (0, 1)$ and $D \in (0, \varepsilon/2)$. $\square$

## Novelty Check

We searched the literature via web queries covering Vasudevan–Tian–Diggavi (2006), Cuff–Su–El Gamal (ISIT 2009, arXiv:0905.1883), Gu–Effros (ISIT 2009), El Gamal–Kim (*Network Information Theory*, 2011), Permuter–Weissman (IEEE TIT 2012), Chia–Permuter–Weissman (IEEE TIT 2012), and subsequent 2012–2025 cascade source coding papers, as well as searches for `"Tweedie"`, `"Jacobian"`, `"exponential family"`, `"cascade source coding"`, and `"outer bound is loose"`.

- **What was already known:** The quadratic-Gaussian cascade rate-distortion region was solved in special topologies with side information at *both* Node 1 and Node 2 (Permuter–Weissman 2012) or degraded side information at Node 3 (Vasudevan–Tian–Diggavi 2006; Chia–Permuter–Weissman 2012). For side information *only* at the intermediate node (Cuff–Su–El Gamal 2009), the general single-letter characterization was left open, and the problem catalog (`problems/cascade-rate-distortion-side-info.md`) explicitly framed the tightness of `cascadeOuterBound` for finite-alphabet DMSs as open.
- **What appears new here:** Our exponential-family Jacobian converse (Claim 2) proving $R_2 \to +\infty$ as $R_1 \downarrow R_{\mathrm{WZ}}(D)$ in the quadratic-Gaussian cascade with side info at Node 2 only, and its finite-alphabet quantization pullback (Claim 3) disproving `CascadeRateDistortionSideInfo.Statement` with an explicit unbounded gap. (Note: we did not have direct PDF access to arXiv:0905.1883 to check every remark inside it, so a careful reader should verify whether a similar Gaussian-corner observation appeared informally in Cuff–Su–El Gamal 2009; however, the explicit exponential-family Jacobian proof and finite-alphabet disproof appear to be self-contained and new.)

## Verification

All numerical checks are reproducible via `.venv/bin/python`:

1. **Purely analytical zero-quadrature disproof constants** (`attempts/cascade-rate-distortion-side-info/code/verify_analytical_constants.py`):
   - $\Delta = 5 \times 10^{-3}, L = 9.0, K = 3601$: $R_1^* \le 0.50383$, $R_2^* \le 1.29533$, $R_2^{\mathrm{conv,basic}} \ge 1.45337$ (**gap $+0.15804$ bits**), $R_2^{\mathrm{conv,EPI}} \ge 1.74458$ (**gap $+0.44925$ bits**).
   - $\Delta = 10^{-3}, L = 10.0, K = 20001$: $R_1^* \le 0.50077$, $R_2^* \le 1.29305$, $R_2^{\mathrm{conv,basic}} \ge 2.62364$ (**gap $+1.33059$ bits**), $R_2^{\mathrm{conv,EPI}} \ge 2.91586$ (**gap $+1.62281$ bits**).
   - $\Delta = 10^{-4}, L = 12.0, K = 240001$: $R_1^* \le 0.50008$, $R_2^* \le 1.29254$, $R_2^{\mathrm{conv,basic}} \ge 4.28671$ (**gap $+2.99417$ bits**).
2. **Smaller-$K$ Lloyd–Max counterexamples and Binary Erasure inner/outer comparison** (`attempts/cascade-rate-distortion-side-info/code/lloyd_max_counterexample.py`):
   - Using 80-point Gauss–Legendre quadrature for $P_\Delta$ on Lloyd–Max bins: strict gap already appears at **$K = 96$** with EPI ($\sigma_N = 1.2$, $D/\sigma_{X|Y}^2 = 0.78$: $R_2^{\mathrm{outer}} = 1.2254$ vs $R_2^{\mathrm{conv,EPI}} = 1.2774$, gap $+0.0521$ bits) and at **$K = 200$** without EPI ($\sigma_N = 1.5$, $D/\sigma_{X|Y}^2 = 0.84$: $R_2^{\mathrm{outer}} = 1.1097$ vs $R_2^{\mathrm{conv,basic}} = 1.3493$, gap $+0.2397$ bits).
   - Binary erasure side info at $\varepsilon = 0.5, D = 0.125$: $R_1 = 0.09436$, $R_2^{\mathrm{outer}} = 0.59436$, $R_2^{\mathrm{relay}} = 0.73229$, $R_2^{\mathrm{recomp}} = 1.00000$; degraded-hybrid $(U, V)$ sweep confirms minimum at $\alpha = 0$ (pure relaying), leaving a $+0.13793$-bit gap.

*Note on Lean 4 formalization:* A formal Lean 4 `disproof : ¬ InfoTheory.Problems.CascadeRateDistortionSideInfo.Statement` was not written in this attempt because Claim 2 relies on multivariate change of variables for differential entropy on $\mathbb{R}^n$, exponential-family Hessian differentiation under the integral sign, and multivariate Gaussian maximum entropy (which are not yet available in `InfoTheory.Bridge`). However, the proof uses only standard real analysis and measure theory and avoids EPI altogether, making it a clear blueprint for future formalization.

### Referee Audit (2026-11-27)
Independently audited by a fresh-context referee agent (Gemini 4 Neon): verified all 5 steps of the continuous Gaussian converse (including Borel measurability of the coordinatewise-$Q_\Delta$ pullback, $L^1$ integrability of $\ln\det\Sigma$, global diffeomorphism of $y \mapsto T^n(m_1, y)$, and the $D_G(\delta, 0) = v_0$ limiting case where the lower bound diverges to $+\infty$), confirmed exact Markov preservation $U_\Delta - X_\Delta - Y_\Delta$ and $X_\Delta - (U_\Delta, Y_\Delta) - \hat{X}_\Delta$, and re-executed both verification scripts with identical outputs. Verdict: `VERIFIED`; status moved to `community-reviewed`.

## Dead ends

1. **Lossless reconstruction ($D = 0$) of $X$ or deterministic $f(X)$, and independent $(X, Y)$.**
   - *Obstruction:* In all three regimes, `cascadeOuterBound` is actually **tight**. For lossless $f(X)$, $H(f(X) \mid U, Y) = 0$ implies $I(X; U \mid Y) \ge H(f(X) \mid Y)$ and $I(X, Y; f(X)) = H(f(X))$, which is achieved by Slepian–Wolf binning $f(X)^n$ at Node 1 and entropy-coding $f(X)^n$ at Node 2. For $X \perp Y$, $X - U - \hat{X}$ forces $R_1, R_2 \ge R(D)$, achieved by single-user compression at Node 1 and forwarding.
2. **Binary symmetric source $(X, Y)$ under Hamming distortion ($d(x, \hat{x}) = \mathbf{1}\{x \neq \hat{x}\}$, $D < p$).**
   - *Obstruction:* At the Wyner–Ziv corner, the optimal Wyner–Ziv reconstruction is $\hat{X}^* = f(U^*, Y) = U^*$ (ignoring $Y$), so $I(X, Y; \hat{X}^*) = I(X; U^*) = 1 - h(D)$, which is operationally achievable by having Node 2 recover $U^{*n}$ from the Wyner–Ziv bin and forward its codebook index of rate $I(X; U^*)$ directly to Node 3.
3. **Direct operational converse for binary erasure side information under Hamming distortion (Claim 4–5).**
   - *Obstruction:* Although `cascadeOuterBound` gives $R_2^{\mathrm{outer}} = 1 - \varepsilon h(D/\varepsilon) < R_2^{\mathrm{relay}}$ at $R_1 = R_{\mathrm{WZ}}(D)$, and linear codes cannot achieve $(R_1, R_2^{\mathrm{outer}})$ (since $m_1 + m_2 = \varepsilon n$ leaves a unique random-weight error vector $Z_E$), we could not prove $\frac{1}{n} I(\hat{X}^n; E^n) = \Omega(1)$ for arbitrary *nonlinear* operational codes. Both single-draw entropy chains and a double-draw coupling with two independent erasure patterns $(E^n, \tilde{E}^n)$ fell short of forcing a positive lower bound on $I(\hat{X}^n; E^n)$.
4. **Binary $X \in \{0, 1\}$ with large-$K$ soft-channel $Y$ under log-loss distortion.**
   - *Obstruction:* Although log-loss cleanly pins $\hat{X}_i \approx P(X_i = 1 \mid M_1, Y^n)$ via KL-divergence decomposition and gives an exponential family in $L(Y_i)$, keeping $X$ binary caps $H(U \mid X, Y) \le 1$ bit; hence $I(X, Y; \hat{X}^*) = H(\hat{X}^*) - H(\hat{X}^* \mid X, Y)$ also grows like $\log_2 K - O(1)$ instead of staying $O(1)$. Both $X$ and $Y$ must have large (or continuous) alphabets so that $H(\hat{X}^*)$ and $H(\hat{X}^* \mid X, Y)$ cancel in `cascadeOuterBound` while failing to cancel in $H(\hat{X}^n)$ operationally — which led directly to the quantized-Gaussian disproof.

## References

- Problem statement: `problems/cascade-rate-distortion-side-info.md`, `lean/InfoTheory/Problems/CascadeRateDistortionSideInfo.lean`. (No prior attempts existed in `attempts/cascade-rate-distortion-side-info/`.)
- Verification scripts: `attempts/cascade-rate-distortion-side-info/code/verify_analytical_constants.py`, `attempts/cascade-rate-distortion-side-info/code/lloyd_max_counterexample.py`.
- P. Cuff, H.-I. Su, and A. El Gamal, "Cascade multiterminal source coding," *Proc. IEEE ISIT*, 2009 (arXiv:0905.1883).
- D. Vasudevan, C. Tian, and S. N. Diggavi, "Lossy source coding for a cascade communication system with side-informations," *Proc. Allerton Conf.*, 2006.
- W. Gu and M. Effros, "A strong conditional typicality lemma and its applications to cascade source coding," *Proc. IEEE ISIT*, 2009.
- H. H. Permuter and T. Weissman, "Cascade and triangular source coding with side information at the first two nodes," *IEEE Trans. Inf. Theory*, 2012.
- Y.-K. Chia, G. Kramer, A. Mahajan, and T. Weissman, "Cascade and triangular source coding with side information," *IEEE Trans. Inf. Theory*, 2012.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge University Press, 2011.
