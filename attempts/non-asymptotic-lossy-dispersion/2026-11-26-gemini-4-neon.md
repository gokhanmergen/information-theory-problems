---
problem: non-asymptotic-lossy-dispersion
date: 2026-11-26
attempter: gemini-4-neon
model: gemini-4-neon
type: full-solution-claim
status: community-reviewed
---

## Summary

We **disprove** `InfoTheory.Problems.NonAsymptoticLossyDispersion.Statement` via a completely explicit, finite-alphabet discrete memoryless Wyner–Ziv source with $|\mathcal{X}| = 4$, $|\mathcal{Y}| = 3$, $|\hat{\mathcal{X}}| = 3$, finite nonnegative distortion $d$, and strictly interior distortion threshold $D = 0.415$. By constructing an elementary, deterministic, type-adaptive sequence of Wyner–Ziv codes (requiring **no** second-order converse), we prove that at excess-distortion probability $\varepsilon = 1/2$,
$$\limsup_{n \to \infty} \sqrt{n}\bigl(R_{\mathrm{WZ}}(n, D, 1/2) - R_{\mathrm{WZ}}(D)\bigr) \le -0.062396 < 0,$$
directly contradicting `Statement`, which asserts that for every finite-alphabet source and interior $D$, the limit at $\varepsilon = 1/2$ equals $\sqrt{V_{\max}}\,\Phi^{-1}(1/2) = 0$. In fact, even at $\varepsilon = 0.40 < 1/2$ (where `Statement` requires a nonnegative limit $\sqrt{V_{\min}}\,\Phi^{-1}(0.60) \ge 0$), our code achieves a strictly negative second-order rate $\le -0.005950 < 0$. We also survey the 2025–2026 literature—specifically Xiang Li & Cheuk Ting Li (2025, arXiv:2510.20241) and Lin Zhou (2026, arXiv:2610.11998), the latter of which resolved exact discrete Wyner–Ziv second-order asymptotics using source-type-dependent test channels.

## Approach

In `NonAsymptoticLossyDispersion.Statement`, the conjectured second-order coding rate is piecewise Gaussian in $\Phi^{-1}(1 - \varepsilon)$:
$$\lim_{n \to \infty} \sqrt{n}\bigl(R_{\mathrm{WZ}}(n, D, \varepsilon) - R_{\mathrm{WZ}}(D)\bigr) = \sqrt{V(\varepsilon)}\,\Phi^{-1}(1 - \varepsilon), \qquad V(\varepsilon) = \begin{cases} V_{\min} & \varepsilon < 1/2, \\ V_{\max} & \varepsilon \ge 1/2. \end{cases}$$
Such a formula arises if the optimal second-order code fixes a single first-order optimal test channel $u \in \mathcal{U}^*$ across all source sequences $x^n$ (choosing the minimum-variance $u$ when $\varepsilon < 1/2$ and the maximum-variance $u$ when $\varepsilon > 1/2$).

However, in Wyner–Ziv coding the encoder observes $X^n$ and therefore knows the empirical type deviation $G_n = \sqrt{n}(T_{X^n} - P_X)$ before selecting the test channel. When the first-order optimal test channel is **non-unique** at $(P_{X,Y}, D)$ and different optimal channels $u_A, u_B \in \mathcal{U}^*$ have different conditional variances $\sigma_A \ne \sigma_B$ given $X^n$ while the $X$-type rate sensitivity $\tau > 0$ is nonzero, an adaptive encoder can choose the smaller-variance mode ($\sigma_B$) on "lucky" source types (where slack is positive) and the larger-variance mode ($\sigma_A$) on "unlucky" source types (where slack is negative, gambling on a favorable side-information realization $Y^n$). At zero second-order rate ($L = 0$, i.e. $R_n = R_{\mathrm{WZ}}(D)$), this yields asymptotic success probability
$$1 - \varepsilon(0) = \mathbb{E}_{G \sim \mathcal{N}(0, 1)}\!\left[\max\!\left(\Phi\!\left(\frac{-\tau G}{\sigma_B}\right),\, \Phi\!\left(\frac{-\tau G}{\sigma_A}\right)\right)\right] = \frac{1}{2} + \frac{1}{2\pi}\left(\arctan\!\left(\frac{\tau}{\sigma_B}\right) - \arctan\!\left(\frac{\tau}{\sigma_A}\right)\right) > \frac{1}{2}.$$
Because $1 - \varepsilon(0) > 1/2$ strictly, we can *decrease* the rate by $c/\sqrt{n}$ ($c > 0$) and still keep the excess-distortion probability strictly below $1/2$.

To make this mechanism completely elementary (avoiding both any second-order converse and any simultaneous independent rate/distortion noise penalty), we couple two sub-sources selected by a fair coin flip $S \sim \mathrm{Bern}(1/2)$ observed by both encoder and decoder:
- **$S = 0$ (point-to-point linear-segment source):** $B \sim \mathrm{Bern}(1/2)$, no side information about $B$, reconstruction alphabet $\{0, 1, e\}$ with distortion $d_0(b, b) = 0$, $d_0(b, e) = w_0$, $d_0(b, 1-b) = 3 w_0$. Using the golden-ratio identity $(1 + t^3)/2 = t$ for $t = (\sqrt{5} - 1)/2$, its exact rate-distortion function has a **straight-line segment** of slope $-\lambda^*/w_0$ where $\lambda^* = \log_2\varphi$. Because $S = 0$ is point-to-point, it contributes **zero** conditional rate or distortion variance given $X^n$.
- **$S = 1$ (binary symmetric Wyner–Ziv source):** $B \sim \mathrm{Bern}(1/2)$, $Y' = B \oplus Z$ with $Z \sim \mathrm{Bern}(p)$ ($p = 0.40$), Hamming distortion on $\{0, 1\}$ (and penalty $10$ for $e$). Its exact Wyner–Ziv rate-distortion function has a **straight-line segment** $[d_c, p]$ of slope $-\lambda_1$.

Setting $w_0 := \lambda^* / \lambda_1$ matches the two slopes identically, creating a continuous family of first-order optimal allocations at $D = 0.415$ whose two extreme modes have:
- **Mode A ($S = 1$ uncoded):** zero binning variance ($\sigma_R = 0$), distortion variance $\sigma_A = \lambda_1\sqrt{p(1-p)/2} \approx 0.39487$.
- **Mode B ($S = 1$ fully encoded at $d_c$):** zero distortion variance ($\sigma_D = 0$), binning variance $\sigma_B = h_2'(p * d_c)\sqrt{p(1-p)/2} \approx 0.07792 < \sigma_A / 5$.

Since the $S = 0$ and $S = 1$ linear-segment intercepts differ ($\lambda^* \approx 0.69424 \ne 0.45595 \approx \lambda_1 p$), the $S$-type sensitivity is $\tau = (\lambda^* - \lambda_1 p)/2 \approx 0.11914 > 0$, giving $1 - \varepsilon(0) \approx 0.611176 > 1/2$ and a strictly negative second-order rate at $\varepsilon = 1/2$.

### Novelty Check and Literature Update

We searched Google/arXiv for second-order Wyner–Ziv asymptotics, converses, and non-Gaussian / type-dependent bounds (covering Watanabe–Kuzuoka–Tan 2015, Kostina–Verdú 2012, Tan–Kosut 2014, Oohama 2018, and 2020–2026 preprints). Two recent papers directly advance the state of the art beyond the problem file's "What is known" section:
1. **Xiang Li and Cheuk Ting Li (Oct 2025, arXiv:2510.20241)**, *"New Second-Order Achievability Bounds for Coding with Side Information via Type Deviation Convergence"*: introduces type deviation convergence with non-Gaussian deviations, improving upon Watanabe–Kuzuoka–Tan (2015), Yassaee–Aref–Gohari, and Li–Anantharam for Wyner–Ziv, Heegard–Berger, and Gel'fand–Pinsker.
2. **Lin Zhou (Oct 2026, arXiv:2610.11998)**, *"Exact Second-Order Asymptotics for the Discrete Wyner–Ziv Problem"*: establishes the exact second-order asymptotics for discrete Wyner–Ziv coding (via a novel converse using posterior decomposition, concentration inequalities, and conditional Gaussian approximation for martingales, matched by an achievability bound allowing the test channel to depend on the observed source type), and shows on a quaternary source that fixed-test-channel bounds (including Li & Li 2025) are strictly suboptimal.

Accordingly, we do **not** claim novelty for the general discovery that discrete Wyner–Ziv second-order asymptotics requires source-type-dependent test channels and can beat fixed-test-channel Gaussian bounds; rather, our contribution is a **completely self-contained, elementary, achievability-only counterexample** (using only Jensen/Gibbs, Mrs. Gerber's Lemma, probabilistic sphere covering, random binning, and Bernoulli Berry–Esseen) that directly refutes the catalog's formalized statement `NonAsymptoticLossyDispersion.Statement` and is well-suited for Lean 4 formalization.

## Claims

1. **[proved]** *(Point-to-point golden-ratio linear segment)* For $B \sim \mathrm{Bern}(1/2)$ and $d_0 : \{0, 1\} \times \{0, 1, e\} \to \mathbb{R}_{\ge 0}$ defined by $d_0(b, b) = 0$, $d_0(b, e) = 1$, $d_0(b, 1-b) = 3$, let $\varphi = (1+\sqrt{5})/2$, $t = 1/\varphi = (\sqrt{5}-1)/2$, $\lambda^* = \log_2 \varphi$, $p_0^- = t^2/2$, and $d_0^- = 3 p_0^- = \frac{3(3-\sqrt{5})}{4}$. Then for every joint distribution $Q$ on $\{0,1\}\times\{0,1,e\}$ with $B$-marginal $\mathrm{Bern}(1/2)$,
   $$I(B; \hat{X}) \ge \lambda^*\bigl(1 - \mathbb{E}[d_0(B, \hat{X})]\bigr),$$
   with equality at every $d_0 \in [d_0^-, 1]$.
2. **[proved]** *(Binary symmetric Wyner–Ziv supporting hyperplane)* For $p \in (0, 1/2)$, $B \sim \mathrm{Bern}(1/2)$, $Y' = B \oplus Z$ with $Z \sim \mathrm{Bern}(p)$ independent of $B$, and $d_1(b, b) = 0$, $d_1(b, 1-b) = 1$, $d_1(b, e) = 10$, let $g(\alpha) = h_2(p * \alpha) - h_2(\alpha)$ where $p * \alpha = p(1-\alpha) + (1-p)\alpha$. Then $g$ is strictly convex on $(0, 1/2)$; letting $d_c \in (0, p)$ be the unique solution of $g'(d_c) = -g(d_c)/(p - d_c)$ and $\lambda_1 := g(d_c)/(p - d_c) > 0$, every Markov chain $U - B - Y'$ and decoder $g_{\mathrm{dec}} : \mathcal{U} \times \{0, 1\} \to \{0, 1, e\}$ satisfy
   $$I(B; U \mid Y') \ge \lambda_1\bigl(p - \mathbb{E}[d_1(B, g_{\mathrm{dec}}(U, Y'))]\bigr),$$
   with equality at every $d_1 \in [d_c, p]$.
3. **[proved]** *(Exact single-letter rate and interiority of the $4 \times 3 \times 3$ source)* Define the source $(P, d)$ on $\mathcal{X} = \{0,1\}^2$, $\mathcal{Y} = \{(0,0), (1,0), (1,1)\}$, $\hat{\mathcal{X}} = \{0, 1, e\}$ with $p = 0.40$, $w_0 = \lambda^*/\lambda_1$, and $D = 0.415$ as in Section Details. Then `IsInteriorDistortion P d D` holds, and
   $$R_{\mathrm{WZ}}(D) = \frac{\lambda^* + \lambda_1 p}{2} - \lambda_1 D = \frac{\lambda_1(w_0 - 0.43)}{2} \approx 0.10204627 > 0.$$
4. **[proved]** *(Elementary type-adaptive achievability beating $R_{\mathrm{WZ}}(D)$ at $\varepsilon = 1/2$)* For the $4 \times 3 \times 3$ source of Claim 3, let $\tau = (\lambda^* - \lambda_1 p)/2 \approx 0.11914450$, $\sigma_A = \lambda_1\sqrt{p(1-p)/2} \approx 0.39486680$, and $\sigma_B = h_2'(p * d_c)\sqrt{p(1-p)/2} \approx 0.07792492$. For every $c \in \mathbb{R}$, there exists a sequence of deterministic Wyner–Ziv codes of blocklength $n$ and message size $M_n = \lfloor 2^{n R_{\mathrm{WZ}}(D) - c\sqrt{n}}\rfloor$ whose excess-distortion probability $\varepsilon_n$ satisfies
   $$\limsup_{n \to \infty} \varepsilon_n \le \varepsilon_{\mathrm{ach}}(c) := 1 - \mathbb{E}_{G \sim \mathcal{N}(0,1)}\!\left[\max\!\left(\Phi\!\left(\frac{-\tau G - c}{\sigma_B}\right),\, \Phi\!\left(\frac{-\tau G - c}{\sigma_A}\right)\right)\right].$$
   In particular, $\varepsilon_{\mathrm{ach}}(0) = \frac{1}{2} - \frac{1}{2\pi}\bigl(\arctan(\tau/\sigma_B) - \arctan(\tau/\sigma_A)\bigr) \approx 0.388824 < 1/2$, and for $c = 0.03 > 0$, $\varepsilon_{\mathrm{ach}}(0.03) \approx 0.444149 < 1/2$ (with root $c^* \approx 0.062396$ where $\varepsilon_{\mathrm{ach}}(c^*) = 1/2$).
5. **[proved]** *(Refutation of `NonAsymptoticLossyDispersion.Statement`)* For the source $(P, d)$ and interior distortion $D = 0.415$ of Claim 3,
   $$\limsup_{n \to \infty} \sqrt{n}\bigl(R_{\mathrm{WZ}}(n, D, 1/2) - R_{\mathrm{WZ}}(D)\bigr) \le -c^* \approx -0.062396 < 0,$$
   and moreover at $\varepsilon = 0.40 < 1/2$,
   $$\limsup_{n \to \infty} \sqrt{n}\bigl(R_{\mathrm{WZ}}(n, D, 0.40) - R_{\mathrm{WZ}}(D)\bigr) \le -0.005950 < 0.$$
   Since `stdNormalQuantile (1 - 1/2) = 0` (and `stdNormalQuantile (1 - 0.40) > 0`), `InfoTheory.Problems.NonAsymptoticLossyDispersion.Statement` is **false**.

## Details

### Notation and Counterexample Specification

Throughout, $\log_2$ is base-2 logarithm, $h_2(x) = -x\log_2 x - (1-x)\log_2(1-x)$ for $x \in [0, 1]$, $h_2'(x) = \log_2\frac{1-x}{x}$ for $x \in (0, 1)$, and $p * d := p(1-d) + (1-p)d$.

Fix $p = 0.40$. Let $\varphi = (1+\sqrt{5})/2$, $t = 1/\varphi = (\sqrt{5}-1)/2$, and $\lambda^* = \log_2 \varphi \approx 0.69424191$. Let $d_c \approx 0.30548971 \in (0, p)$ be the unique solution to $g'(d_c) = -g(d_c)/(p - d_c)$ where $g(\alpha) = h_2(p * \alpha) - h_2(\alpha)$, let $\lambda_1 = g(d_c)/(p - d_c) \approx 1.13988228$, and set $w_0 := \lambda^* / \lambda_1 \approx 0.60904703 > 0$.

Define the finite-alphabet source $(P, d)$ on $\mathcal{X} = \{0,1\}^2$ ($k_X = 4$), $\mathcal{Y} = \{(0,0), (1,0), (1,1)\}$ ($k_Y = 3$), and $\hat{\mathcal{X}} = \{0, 1, e\}$ ($k_{\hat{X}} = 3$):
- **Distribution $P_{X,Y}$:** Write $X = (S, B)$ with $S \sim \mathrm{Bern}(1/2)$ and $B \sim \mathrm{Bern}(1/2)$ independent (so $P_X$ is uniform on $\{0,1\}^2$). Conditioned on $X = (S, B)$:
  - if $S = 0$, then $Y = (0, 0)$ deterministically;
  - if $S = 1$, then $Y = (1, B \oplus Z)$ where $Z \sim \mathrm{Bern}(p)$ is independent of $(S, B)$.
- **Distortion $d : \mathcal{X} \times \hat{\mathcal{X}} \to \mathbb{R}_{\ge 0}$:**
  $$d((0, b), \hat{x}) = \begin{cases} 0 & \hat{x} = b, \\ w_0 & \hat{x} = e, \\ 3 w_0 & \hat{x} = 1 - b, \end{cases}
  \qquad
  d((1, b), \hat{x}) = \begin{cases} 0 & \hat{x} = b, \\ 1 & \hat{x} = 1 - b, \\ 10 & \hat{x} = e. \end{cases}$$
- **Distortion threshold:** $D := 0.415$.

### Proof of Claim 1

Note that $t = (\sqrt{5}-1)/2 = 2^{-\lambda^*}$ satisfies $t^2 + t - 1 = 0$, hence $t^3 = t(1 - t) = t - t^2 = t - (1 - t) = 2t - 1$, i.e.
$$\frac{1 + t^3}{2} = t.$$
Let $Q(b, \hat{x})$ be any joint distribution on $\{0,1\}\times\{0,1,e\}$ with $Q_B(0) = Q_B(1) = 1/2$, and let $q(\hat{x}) = Q_{\hat{X}}(\hat{x})$ be its $\hat{X}$-marginal. For each $b \in \{0, 1\}$, define
$$Z_b := \sum_{\hat{x} \in \{0,1,e\}} q(\hat{x})\,2^{-\lambda^* d_0(b, \hat{x})},$$
so $Z_0 = q(0) + q(1) t^3 + q(e) t$ and $Z_1 = q(0) t^3 + q(1) + q(e) t$. Averaging gives
$$\frac{Z_0 + Z_1}{2} = (q(0) + q(1))\frac{1 + t^3}{2} + q(e) t = (q(0) + q(1) + q(e)) t = t = 2^{-\lambda^*}.$$
By concavity of $\log_2$ (Jensen's inequality),
$$\frac{1}{2}\log_2 Z_0 + \frac{1}{2}\log_2 Z_1 \le \log_2\frac{Z_0 + Z_1}{2} = -\lambda^*.$$
Define the tilted joint distribution $\tilde{P}(b, \hat{x}) := \frac{1}{2} q(\hat{x}) 2^{-\lambda^* d_0(b, \hat{x})} / Z_b$ (which sums to $1$ over $\hat{x}$ for each $b$, hence over $(b,\hat{x})$). Note that $Q(b, \hat{x}) > 0 \implies q(\hat{x}) > 0 \implies \tilde{P}(b, \hat{x}) > 0$, so $Q \ll \tilde{P}$. By nonnegativity of Kullback–Leibler divergence (Gibbs' inequality),
$$\begin{aligned}
0 \le D(Q \,\|\, \tilde{P})
&= \sum_{b, \hat{x}} Q(b, \hat{x}) \log_2 \frac{Q(b, \hat{x})}{\frac{1}{2} q(\hat{x})} + \lambda^* \sum_{b, \hat{x}} Q(b, \hat{x}) d_0(b, \hat{x}) + \frac{1}{2}\log_2 Z_0 + \frac{1}{2}\log_2 Z_1 \\
&= I(B; \hat{X}) + \lambda^*\mathbb{E}[d_0(B, \hat{X})] + \frac{1}{2}\log_2 Z_0 + \frac{1}{2}\log_2 Z_1 \\
&\le I(B; \hat{X}) + \lambda^*\mathbb{E}[d_0(B, \hat{X})] - \lambda^*,
\end{aligned}$$
giving $I(B; \hat{X}) \ge \lambda^*(1 - \mathbb{E}[d_0(B, \hat{X})])$.

For equality on $[d_0^-, 1]$:
- At $d_0 = 1$: set $\hat{X} \equiv e$; then $I(B; \hat{X}) = 0 = \lambda^*(1 - 1)$ and $\mathbb{E}[d_0] = 1$.
- At $d_0 = d_0^- = 3 p_0^-$ where $p_0^- = t^2/2$: set $\hat{X} = B \oplus W$ with $W \sim \mathrm{Bern}(p_0^-)$ independent of $B$. Then $\mathbb{E}[d_0] = 3 p_0^- = d_0^-$. Since $1 - p_0^- = 1 - t^2/2 = (2 - t^2)/2 = (1 + t)/2 = 1/(2t)$ (using $t^2 = 1 - t$ and $t(1+t) = 1$), we compute
  $$h_2(p_0^-) = -p_0^-\log_2\frac{t^2}{2} - (1 - p_0^-)\log_2\frac{1}{2t} = 1 - (2 p_0^- - (1 - p_0^-))\log_2 t = 1 + (3 p_0^- - 1)\lambda^* = 1 - \lambda^*(1 - d_0^-),$$
  so $I(B; \hat{X}) = 1 - h_2(p_0^-) = \lambda^*(1 - d_0^-)$.
- For any $d_0 = (1 - \alpha) d_0^- + \alpha \cdot 1$ with $\alpha \in [0, 1]$, mixing $\hat{X} = e$ with probability $\alpha$ and $\hat{X} = B \oplus W$ with probability $1 - \alpha$ (since $e \notin \{0, 1\}$ is disjoint from $\{0, 1\}$, no extra time-sharing variable is even needed!) achieves distortion $d_0$ and mutual information $(1-\alpha)(1 - h_2(p_0^-)) = \lambda^*(1 - d_0)$. $\square$

### Proof of Claim 2

First, since $d_1(b, e) = 10 > 1 \ge d_1(b, 0)$ for all $b \in \{0, 1\}$, replacing every occurrence of $g_{\mathrm{dec}}(u, y') = e$ by $0$ strictly decreases distortion without changing $I(B; U \mid Y')$. We may therefore assume $g_{\mathrm{dec}} : \mathcal{U} \times \{0, 1\} \to \{0, 1\}$.

Next, verify strict convexity of $g(\alpha) = h_2(p * \alpha) - h_2(\alpha)$ on $(0, 1/2)$. Using $h_2''(x) = -\frac{1}{x(1-x)\ln 2}$, write $u = 1 - 2\alpha \in (0, 1)$ and $\gamma = 1 - 2p \in (0, 1)$, so $4\alpha(1-\alpha) = 1 - u^2$ and $4(p*\alpha)(1 - p*\alpha) = 1 - \gamma^2 u^2$. Then
$$g''(\alpha) = \gamma^2 h_2''(p * \alpha) - h_2''(\alpha) = \frac{4}{\ln 2}\left(\frac{1}{1 - u^2} - \frac{\gamma^2}{1 - \gamma^2 u^2}\right) = \frac{4}{\ln 2}\cdot\frac{1 - \gamma^2}{(1 - u^2)(1 - \gamma^2 u^2)} > 0.$$
Hence $g$ is strictly convex on $[0, 1/2]$. Note $g(0) = h_2(p) > 0$, $g(1/2) = 0$, $g'(0^+) = -\infty$, and $g(p) = h_2(2p(1-p)) - h_2(p) > 0$ (since $p < 2p(1-p) < 1/2$ for $p \in (0, 1/2)$). Consider $\psi(\alpha) := g(\alpha) + g'(\alpha)(p - \alpha)$ on $(0, p)$. Since $\psi'(\alpha) = g''(\alpha)(p - \alpha) > 0$, $\psi(0^+) = -\infty$, and $\psi(p) = g(p) > 0$, there is a unique $d_c \in (0, p)$ where $\psi(d_c) = 0$, i.e., $g'(d_c) = -g(d_c)/(p - d_c) =: -\lambda_1 < 0$. By strict convexity of $g$ on $[0, 1/2]$, the tangent line at $d_c$ lies globally below $g$:
$$g(\alpha) \ge g(d_c) + g'(d_c)(\alpha - d_c) = \lambda_1(p - \alpha) \qquad \forall \alpha \in [0, 1/2].$$

Now let $U - B - Y'$ be any Markov chain and $g_{\mathrm{dec}} : \mathcal{U} \times \{0, 1\} \to \{0, 1\}$. Since $H(B) = H(Y') = 1$ and $H(B \mid Y') = H(Y' \mid B) = h_2(p)$, the chain rule and Markovity $H(Y' \mid B, U) = H(Y' \mid B)$ give
$$\begin{aligned}
I(B; U \mid Y') &= H(B \mid Y') - H(B \mid U, Y') = H(B \mid Y') - H(B, Y' \mid U) + H(Y' \mid U) \\
&= H(B \mid Y') - H(B \mid U) - H(Y' \mid B, U) + H(Y' \mid U) = H(Y' \mid U) - H(B \mid U).
\end{aligned}$$
For each $u \in \mathcal{U}$ with $P(U = u) > 0$, let $\alpha_u := h_2^{-1}(H(B \mid U = u)) \in [0, 1/2]$, which equals $\min(P(B=0 \mid U=u), P(B=1 \mid U=u))$. Conditioned on $U = u$, $Y' = B \oplus Z$ with $Z \sim \mathrm{Bern}(p)$ independent of $B$ (by Markovity $U - B - Y'$), so by **Mrs. Gerber's Lemma** (Wyner–Ziv 1973, exact for binary symmetric channels: $P(Y' = 0 \mid U = u) = p * \alpha_u$ or $1 - p * \alpha_u$, so $H(Y' \mid U = u) = h_2(p * \alpha_u)$ is actually an *exact identity* for a single bit $B \in \{0, 1\}$!),
$$H(Y' \mid U = u) - H(B \mid U = u) = h_2(p * \alpha_u) - h_2(\alpha_u) = g(\alpha_u).$$
(Indeed, for scalar $B \in \{0, 1\}$ and $Y' = B \oplus Z$ with $Z \perp (B, U)$, $P(Y'=1 \mid U=u) = P(B=1 \mid U=u)(1-p) + P(B=0 \mid U=u)p = p * P(B=1 \mid U=u)$, so $H(Y' \mid U = u) = h_2(p * \alpha_u)$ holds with **exact equality**—not even needing the vector version of Mrs. Gerber's Lemma!)

Let $d_u := \mathbb{P}(B \ne g_{\mathrm{dec}}(u, Y') \mid U = u)$. The map $y' \mapsto g_{\mathrm{dec}}(u, y')$ from $\{0,1\}$ to $\{0,1\}$ is one of four functions:
- Constant ($0$ or $1$): then $d_u \ge \min(P(B=0\mid U=u), P(B=1\mid U=u)) = \alpha_u$, hence $g(\alpha_u) \ge \lambda_1(p - \alpha_u) \ge \lambda_1(p - d_u)$.
- Identity ($y' \mapsto y'$): then $d_u = \mathbb{P}(B \ne Y' \mid U = u) = \mathbb{P}(Z = 1 \mid U = u) = p$, so $\lambda_1(p - d_u) = 0 \le g(\alpha_u)$.
- Negation ($y' \mapsto 1 - y'$): then $d_u = 1 - p > p$, so $\lambda_1(p - d_u) < 0 \le g(\alpha_u)$.

In all cases $g(\alpha_u) \ge \lambda_1(p - d_u)$. Taking expectation over $U$ yields
$$I(B; U \mid Y') = \sum_u P(U = u)\, g(\alpha_u) \ge \lambda_1\bigl(p - \mathbb{E}[d_1(B, g_{\mathrm{dec}}(U, Y'))]\bigr).$$
Equality at $d_1 = d_c$ is achieved by $U = B \oplus W$ ($W \sim \mathrm{Bern}(d_c)$), $g_{\mathrm{dec}}(u, y') = u$; equality at $d_1 = p$ is achieved by constant $U$, $g_{\mathrm{dec}}(u, y') = y'$; time-sharing with a binary flag appended to $U$ achieves equality on all of $[d_c, p]$. $\square$

### Proof of Claim 3

Let $(k_U, Q, g)$ be any feasible triple in `wynerZivRate P d D`, with $U - (S, B) - (S, Y')$ and $\mathbb{E}[d((S, B), g(U, Y))] \le D$. Since $S$ is a deterministic function of $Y$,
$$I(X; U \mid Y) = I(S, B; U \mid S, Y') = I(B; U \mid S, Y') = \frac{1}{2} I(B; U \mid S = 0) + \frac{1}{2} I(B; U \mid Y', S = 1).$$
Conditioned on $S = 0$, letting $\hat{X}_0 = g(U, (0, 0))$ and $d_0 = \mathbb{E}[d((0, B), \hat{X}_0) \mid S = 0]$, data processing and Claim 1 (scaled by $w_0$, using $\lambda^*/w_0 = \lambda_1$) give
$$I(B; U \mid S = 0) \ge I(B; \hat{X}_0 \mid S = 0) \ge \lambda^*\left(1 - \frac{d_0}{w_0}\right) = \lambda^* - \lambda_1 d_0.$$
Conditioned on $S = 1$, Markovity $I(U; Y \mid X) = 0$ implies $I(U; Y' \mid B, S = 1) = 0$; letting $d_1 = \mathbb{E}[d((1, B), g(U, (1, Y'))) \mid S = 1]$, Claim 2 gives
$$I(B; U \mid Y', S = 1) \ge \lambda_1(p - d_1).$$
Averaging the two inequalities and using $\frac{1}{2} d_0 + \frac{1}{2} d_1 = \mathbb{E}[d(X, g(U, Y))] \le D$,
$$I(X; U \mid Y) \ge \frac{\lambda^* + \lambda_1 p}{2} - \lambda_1\left(\frac{d_0 + d_1}{2}\right) \ge \frac{\lambda^* + \lambda_1 p}{2} - \lambda_1 D.$$
For the matching upper bound at $D = 0.415$: set $d_0^{(A)} = 2D - p = 0.43$. Verify numerically (and algebraically) that
$$w_0 d_0^- \approx 0.348953 < 0.43 < 0.524510 \approx 0.43 + (p - d_c) < 0.609047 \approx w_0.$$
Take $k_U = 3$ ($\mathcal{U} = \{0, 1, e\}$): when $S = 0$, generate $U$ via Claim 1's optimal mixture at distortion $d_0^{(A)} = 0.43$ and set $g(u, (0, 0)) = u$; when $S = 1$, set $U = e$ deterministically and $g(u, (1, y')) = y'$. Then $U - X - Y$, $\mathbb{E}[d] = (0.43 + 0.40)/2 = 0.415 = D$, and $I(X; U \mid Y) = \frac{1}{2}(\lambda^* - \lambda_1 \cdot 0.43) = \frac{\lambda^* + \lambda_1 p}{2} - \lambda_1 D \approx 0.10204627 > 0$.

For `IsInteriorDistortion P d D`: we have $R_{\mathrm{WZ}}(D) > 0$, and taking $k_U = 2$, $U = B$, $g(u, y) = u$ yields $U - X - Y$ and expected distortion $0 < 0.415 = D$. $\square$

### Proof of Claim 4

We first record the elementary covering lemma used in both modes.

**Lemma (Exact-Radius Sphere Covering).** *For every integer $K \ge 1$ and $0 \le r \le K/2$, there exists a deterministic codebook $C \subset \{0, 1\}^K$ of size*
$$|C| \le \left\lceil \frac{(K\ln 2 + 1) 2^K}{\binom{K}{r}} \right\rceil \le (K+1)(K\ln 2 + 2)\,2^{K(1 - h_2(r/K))}$$
*such that for every $b^K \in \{0, 1\}^K$ there exists $\phi(b^K) \in C$ with exact Hamming distance $d_H(b^K, \phi(b^K)) = r$.*

*Proof of Lemma.* Draw $L = \lceil (K\ln 2 + 1)2^K/\binom{K}{r}\rceil$ codewords independently uniformly from $\{0, 1\}^K$. Each fixed $b^K$ fails to be at distance $r$ from all $L$ codewords with probability $(1 - \binom{K}{r}/2^K)^L \le \exp(-L\binom{K}{r}/2^K) \le e^{-(K\ln 2 + 1)} = 2^{-K} e^{-1}$. Summing over all $2^K$ vectors gives expected uncovered count $\le e^{-1} < 1$, so a zero-error covering codebook $C$ exists. The second inequality uses $\binom{K}{r} \ge 2^{K h_2(r/K)}/(K+1)$. $\square$

Now fix $c \in \mathbb{R}$, and for each large $n$ set $M_n := \lfloor 2^{n R_{\mathrm{WZ}}(D) - c\sqrt{n}}\rfloor$ (so $\frac{1}{n}\log_2 M_n \le R_{\mathrm{WZ}}(D) - c/\sqrt{n}$ and $\log_2 M_n = n R_{\mathrm{WZ}}(D) - c\sqrt{n} - O(1)$).

Both the encoder (seeing $X^n = (S^n, B^n)$) and the decoder (seeing $Y^n = (S^n, Y'^n)$) observe the **exact same** indicator sequence $S^n \in \{0, 1\}^n$, hence the exact index sets $I_0 = \{i : S_i = 0\}$, $I_1 = \{i : S_i = 1\}$, counts $N_0 = |I_0|$, $N_1 = n - N_0 = |I_1|$, and standardized fluctuation
$$G_n := \frac{N_0 - N_1}{\sqrt{n}} = \frac{2 N_0 - n}{\sqrt{n}}.$$
Conditioned on $S^n = s^n$, $(B_i)_{i \in I_0}$ are i.i.d. $\mathrm{Bern}(1/2)$, and $(B_i, Z_i)_{i \in I_1}$ are i.i.d. $\mathrm{Bern}(1/2) \times \mathrm{Bern}(p)$, independent of $(B_i)_{i \in I_0}$. Because $s^n$ is known to both encoder and decoder, we may design a deterministic code `(enc_{s^n}, dec_{s^n})` with message set `Fin M_n` separately for each $s^n$.

Let $\mathcal{T}_n := \{s^n : |N_0 - n/2| \le n^{3/5}\}$. By Hoeffding's inequality, $\mathbb{P}(S^n \notin \mathcal{T}_n) \le 2 e^{-2 n^{1/5}} \to 0$. For $s^n \notin \mathcal{T}_n$ output an arbitrary codeword. For $s^n \in \mathcal{T}_n$, switch deterministically between two modes based on the sign of $\tau G_n + c$:

#### Mode A (used when $\tau G_n + c > 0$)

- On $I_1$: leave all $N_1$ coordinates uncoded; decoder outputs $\hat{X}_i = Y'_i$. Rate used is $0$; realized distortion on $I_1$ is $\sum_{i \in I_1} Z_i$.
- On $I_0$: let $r_0^- = 1 - h_2(p_0^-) = \lambda^*(1 - d_0^-) = \lambda_1 w_0 (1 - d_0^-)$. Choose the largest integer $K_0 \in \{1, \dots, N_0\}$ for which the Lemma's sphere-covering codebook $C_0 \subset \{0, 1\}^{K_0}$ of radius $r_0 := \lfloor K_0 p_0^-\rfloor$ satisfies $|C_0| \le M_n$. Since $h_2(p_0^-) - h_2(r_0/K_0) \le O(1/K_0)$, $\log_2 |C_0| \le K_0 r_0^- + 3\log_2(n+2) + O(1)$, so
  $$K_0 \ge \frac{\log_2 M_n - 3\log_2(n+2) - O(1)}{r_0^-} - 1.$$
  Notice $K_0 / N_0 \to (w_0 - 0.43)/(w_0(1 - d_0^-)) \approx 0.6884 \in (0, 1)$, so $1 \le K_0 \le N_0$ for all large $n$ and $s^n \in \mathcal{T}_n$. Encode the first $K_0$ coordinates of $I_0$ using $C_0$ (exact distortion $3 w_0 r_0 \le w_0 K_0 d_0^-$) and output $e$ on the remaining $N_0 - K_0$ coordinates of $I_0$ (exact distortion $w_0(N_0 - K_0)$).
- Using $w_0(1 - d_0^-)/r_0^- = 1/\lambda_1$, the deterministic distortion on $I_0$ satisfies
  $$D_0^{(A)} = 3 w_0 r_0 + w_0(N_0 - K_0) \le w_0 N_0 - w_0(1 - d_0^-) K_0 \le w_0 N_0 - \frac{n R_{\mathrm{WZ}}(D) - c\sqrt{n}}{\lambda_1} + O(\log n).$$
- Multiplying the total distortion excess $D_{\mathrm{tot}} - nD = D_0^{(A)} + \sum_{i \in I_1} Z_i - nD$ by $\lambda_1$ and substituting $\lambda_1 w_0 = \lambda^*$, $n R_{\mathrm{WZ}}(D) + \lambda_1 n D = \frac{n}{2}(\lambda^* + \lambda_1 p)$, and $N_0 = \frac{n}{2} + \frac{\sqrt{n}}{2} G_n$, $N_1 = \frac{n}{2} - \frac{\sqrt{n}}{2} G_n$:
  $$\lambda_1(D_{\mathrm{tot}} - n D) \le \sqrt{n}(\tau G_n + c) + \lambda_1 \sum_{i \in I_1} (Z_i - p) + O(\log n).$$
- Thus $D_{\mathrm{tot}} \le n D$ whenever $\frac{\lambda_1}{\sqrt{n}}\sum_{i \in I_1}(Z_i - p) \le -(\tau G_n + c) - O(\frac{\log n}{\sqrt{n}})$. Conditioned on $S^n = s^n$, the left-hand side is a sum of $N_1$ i.i.d. centered Bernoulli terms with variance $\frac{N_1}{n}\lambda_1^2 p(1-p) = \sigma_A^2(1 + O(n^{-2/5}))$. By the Berry–Esseen theorem, uniformly over $s^n \in \mathcal{T}_n$ with $\tau G_n + c > 0$,
  $$\mathbb{P}(D_{\mathrm{tot}} \le n D \mid S^n = s^n) \ge \Phi\!\left(\frac{-(\tau G_n + c) - O(\log n/\sqrt{n})}{\sigma_A \sqrt{2 N_1 / n}}\right) - O(n^{-1/2}).$$

#### Mode B (used when $\tau G_n + c \le 0$)

- On $I_1$: set $r_1 := \lfloor N_1 d_c\rfloor$, and let $C_1 \subset \{0, 1\}^{N_1}$ be the Lemma's sphere-covering codebook of exact radius $r_1$, with encoder map $\phi_1 : \{0, 1\}^{N_1} \to C_1$ satisfying $d_H(b^{N_1}, \phi_1(b^{N_1})) = r_1$ for all $b^{N_1}$, and
  $$\log_2 |C_1| \le N_1\bigl(1 - h_2(d_c)\bigr) + 3\log_2(n + 2) + O(1).$$
- On $I_0$: set
  $$K_0 := \left\lceil \frac{w_0 N_0 + r_1 - n D}{w_0(1 - d_0^-)} \right\rceil, \qquad r_0 := \lfloor K_0 p_0^-\rfloor.$$
  Check $K_0 / N_0 \to (w_0 + d_c - 2D)/(w_0(1 - d_0^-)) = (w_0 - 0.52451)/(w_0(1 - d_0^-)) \approx 0.3250 \in (0, 1)$, so $1 \le K_0 \le N_0$ for all large $n$ and $s^n \in \mathcal{T}_n$. Let $C_0 \subset \{0, 1\}^{K_0}$ be the Lemma's sphere-covering codebook of exact radius $r_0$ with $M_0 := |C_0|$, and encode the first $K_0$ coordinates of $I_0$ using $C_0$ and the remaining $N_0 - K_0$ coordinates as $e$. Whenever $u_1 = \phi_1(B_1^{N_1}) \in C_1$ is decoded correctly, the total distortion on all $n$ coordinates is **deterministically** at most $n D$:
  $$3 w_0 r_0 + w_0(N_0 - K_0) + r_1 \le w_0 N_0 - w_0(1 - d_0^-) K_0 + r_1 \le n D.$$
- Using $r_0^- / (w_0(1 - d_0^-)) = \lambda_1$, we have $\log_2 M_0 \le \lambda_1(w_0 N_0 + N_1 d_c - n D) + 3\log_2(n + 2) + O(1)$. Set $M_1 := \lfloor M_n / M_0 \rfloor$ (so $M_0 M_1 \le M_n$, allowing $(m_0, m_1) \in \mathrm{Fin}\,M_0 \times \mathrm{Fin}\,M_1$ to be injected into $\mathrm{Fin}\,M_n$). Then
  $$\begin{aligned}
  \log_2 M_1 &\ge n R_{\mathrm{WZ}}(D) - c\sqrt{n} - \lambda_1(w_0 N_0 + N_1 d_c - n D) - 3\log_2(n + 2) - O(1) \\
  &= N_1 g(d_c) - \sqrt{n}(\tau G_n + c) - 3\log_2(n + 2) - O(1),
  \end{aligned}$$
  using $\lambda_1(p - d_c) = g(d_c)$ and $\frac{n}{2}(\lambda^* + \lambda_1 p) - \lambda^* N_0 - \lambda_1 p N_1 = -\tau\sqrt{n} G_n$.
- **Random binning of $C_1$ into $M_1$ bins:** Draw a uniformly random map $H : C_1 \to \mathrm{Fin}\,M_1$. Choose a constant $c_4 > 0$ small enough that $p * d_c + c_4 / h_2'(p * d_c) < 1/2$, and define the decoding Hamming-distance threshold
  $$t_n := \left\lfloor N_1(p * d_c) + \frac{\min\bigl(-\sqrt{n}(\tau G_n + c),\, c_4 N_1\bigr) - C_3 \log_2(n + 2)}{h_2'(p * d_c)} \right\rfloor,$$
  where $C_3 > 0$ is chosen large enough to absorb $6\log_2(n+2) + O(1) + 2\log_2 n$. Given bin $H(u_1)$ and $Y_1^{N_1}$, the decoder outputs the unique $u' \in C_1$ with $H(u') = H(u_1)$ and $d_H(u', Y_1^{N_1}) \le t_n$ (or declares error if none or more than one exists).
- **Exact collision bound:** For any $u' \in C_1 \setminus \{u_1\}$, $\mathbb{P}_H(H(u') = H(u_1) \mid B_1^{N_1}, Y_1^{N_1}) = 1/M_1$. By union bound over $u' \in C_1 \setminus \{u_1\}$ and linearity of expectation,
  $$\begin{aligned}
  \mathbb{P}_{B_1, Z, H}\bigl(\exists u' \in C_1 \setminus \{u_1\} : H(u') = H(u_1),\, d_H(u', Y_1^{N_1}) \le t_n\bigr)
  &\le \frac{1}{M_1} \sum_{u' \in C_1} \mathbb{P}_{B_1, Z}\bigl(d_H(u', Y_1^{N_1}) \le t_n\bigr).
  \end{aligned}$$
  Because $B_1^{N_1} \sim \mathrm{Unif}(\{0,1\}^{N_1})$ and $Y_1^{N_1} = B_1^{N_1} \oplus Z^{N_1}$, the marginal $Y_1^{N_1}$ is **exact** $\mathrm{Unif}(\{0,1\}^{N_1})$! Hence for every $u' \in C_1$, $\mathbb{P}(d_H(u', Y_1^{N_1}) \le t_n) = \mathrm{Vol}(B(0, t_n)) / 2^{N_1} \le 2^{N_1 h_2(t_n/N_1) - N_1}$ (standard Chernoff bound for $t_n \le N_1/2$). By **concavity** of $h_2$, the tangent line at $p * d_c$ is an exact global upper bound:
  $$N_1 h_2(t_n / N_1) \le N_1 h_2(p * d_c) + h_2'(p * d_c)\bigl(t_n - N_1(p * d_c)\bigr).$$
  Combining with $|C_1|$ and $M_1$ yields collision probability $\le |C_1| 2^{N_1 h_2(t_n/N_1) - N_1} / M_1 \le n^{-2}$!
- **Existence of a deterministic hash & conditional Berry–Esseen:** Averaging over $H$, there exists a deterministic hash $h_{s^n} : C_1 \to \mathrm{Fin}\,M_1$ whose error probability given $S^n = s^n$ is at most $\mathbb{P}(d_H(u_1, Y_1^{N_1}) > t_n \mid S^n = s^n) + n^{-2}$. For every fixed $b^{N_1} \in \{0,1\}^{N_1}$, $u_1 = \phi_1(b^{N_1})$ has exact Hamming distance $r_1$ from $b^{N_1}$, so conditioned on $B_1^{N_1} = b^{N_1}$,
  $$d_H(u_1, Y_1^{N_1}) = \sum_{i : u_{1,i} \ne b_{1,i}} (1 - Z_i) + \sum_{i : u_{1,i} = b_{1,i}} Z_i \stackrel{d}{=} \mathrm{Bin}(r_1, 1-p) + \mathrm{Bin}(N_1 - r_1, p),$$
  which has mean $r_1(1-p) + (N_1 - r_1)p = N_1(p * d_c) + O(1)$ and variance $r_1 p(1-p) + (N_1 - r_1) p(1-p) = N_1 p(1-p)$! By Berry–Esseen, uniformly over $s^n \in \mathcal{T}_n$ with $\tau G_n + c \le 0$,
  $$\mathbb{P}(D_{\mathrm{tot}} \le n D \mid S^n = s^n) \ge \Phi\!\left(\frac{\min(-(\tau G_n + c),\, c_4 N_1/\sqrt{n}) - O(\log n/\sqrt{n})}{\sigma_B\sqrt{2 N_1 / n}}\right) - O(n^{-1/2}) - n^{-2}.$$

#### Combining Modes A and B

Fix any cutoff $M > 0$. On the compact interval $G_n \in [-M, M]$ (which lies inside $\mathcal{T}_n$ and avoids the $c_4 N_1/\sqrt{n}$ cap for all sufficiently large $n$), the conditional success probability $\mathbb{P}(D_{\mathrm{tot}} \le n D \mid S^n)$ is bounded below uniformly by $f(G_n) - o_M(1)$, where
$$f(g) := \max\!\left(\Phi\!\left(\frac{-\tau g - c}{\sigma_B}\right),\, \Phi\!\left(\frac{-\tau g - c}{\sigma_A}\right)\right) = \begin{cases} \Phi\bigl(\frac{-\tau g - c}{\sigma_B}\bigr) & \tau g + c \le 0, \\ \Phi\bigl(\frac{-\tau g - c}{\sigma_A}\bigr) & \tau g + c > 0. \end{cases}$$
Since $f$ is continuous and bounded on $[-M, M]$ and $G_n \xrightarrow{d} G \sim \mathcal{N}(0, 1)$,
$$\liminf_{n \to \infty} \mathbb{P}(D_{\mathrm{tot}} \le n D) \ge \mathbb{E}\bigl[f(G)\,\mathbf{1}_{|G| \le M}\bigr].$$
Letting $M \to \infty$ gives $\limsup_{n \to \infty} \varepsilon_n \le 1 - \mathbb{E}[f(G)] = \varepsilon_{\mathrm{ach}}(c)$.

At $c = 0$, using the symmetry of $G \sim \mathcal{N}(0, 1)$ and the classical bivariate-normal orthant integral $\mathbb{E}[\Phi(\kappa |G|)] = \frac{1}{2} + \frac{1}{\pi}\arctan(\kappa)$ (equivalently $\mathbb{P}(Z_1 \le \kappa Z_2 \mid Z_2 > 0)$ for independent standard normals $Z_1, Z_2$):
$$\begin{aligned}
1 - \varepsilon_{\mathrm{ach}}(0)
&= \frac{1}{2}\mathbb{E}\!\left[\Phi\!\left(\frac{\tau |G|}{\sigma_B}\right)\right] + \frac{1}{2}\mathbb{E}\!\left[1 - \Phi\!\left(\frac{\tau |G|}{\sigma_A}\right)\right] \\
&= \frac{1}{2} + \frac{1}{2\pi}\left(\arctan\!\left(\frac{\tau}{\sigma_B}\right) - \arctan\!\left(\frac{\tau}{\sigma_A}\right)\right).
\end{aligned}$$
Since $\tau > 0$ and $0 < \sigma_B < \sigma_A$, $\arctan(\tau/\sigma_B) > \arctan(\tau/\sigma_A)$, so $1 - \varepsilon_{\mathrm{ach}}(0) > 1/2$ strictly ($\approx 0.611176$). By continuity and strict monotonicity of $c \mapsto \varepsilon_{\mathrm{ach}}(c)$, $\varepsilon_{\mathrm{ach}}(c) < 1/2$ for all $c \in [0, c^*)$, where $c^* \approx 0.062396 > 0$. $\square$

### Proof of Claim 5

Take $c \in (0, c^*)$ (for concreteness, $c = 0.03$, where $\varepsilon_{\mathrm{ach}}(0.03) \approx 0.444149 < 1/2$). By Claim 4, there exists $N \ge 1$ such that for all $n \ge N$, the deterministic code of message size $M_n = \lfloor 2^{n R_{\mathrm{WZ}}(D) - c\sqrt{n}}\rfloor$ has excess-distortion probability $\le 1/2$. By definition of `wynerZivFiniteRate` as an infimum over all codes with `excessProb ≤ ε`, for all $n \ge N$:
$$R_{\mathrm{WZ}}(n, D, 1/2) \le \frac{\log_2 M_n}{n} \le R_{\mathrm{WZ}}(D) - \frac{c}{\sqrt{n}},$$
whence $\sqrt{n}(R_{\mathrm{WZ}}(n, D, 1/2) - R_{\mathrm{WZ}}(D)) \le -c$. Letting $c \uparrow c^*$ gives $\limsup_{n \to \infty} \sqrt{n}(R_{\mathrm{WZ}}(n, D, 1/2) - R_{\mathrm{WZ}}(D)) \le -c^* \approx -0.062396 < 0$.

On the other hand, in `NonAsymptoticLossyDispersion.lean`, `gaussianPdf1D 1 x = (1/\sqrt{2\pi})e^{-x^2/2}` is strictly positive, even, and integrates to $1$, so `stdNormalCDF 0 = 1/2` and `stdNormalCDF t < 1/2` for all $t < 0$; hence `stdNormalQuantile (1 - 1/2) = sInf (Set.Ici 0) = 0`. Thus `Statement` implies that for our source $(P, d)$ and interior $D = 0.415$,
$$\lim_{n \to \infty} \sqrt{n}\bigl(R_{\mathrm{WZ}}(n, D, 1/2) - R_{\mathrm{WZ}}(D)\bigr) = \sqrt{V_{\max}} \cdot 0 = 0,$$
contradicting $\limsup \le -c^* < 0$.

Similarly, at $\varepsilon = 0.40 < 1/2$, $\varepsilon_{\mathrm{ach}}(0.00595) \approx 0.40$ (so e.g. for $c = 0.005$, $\varepsilon_{\mathrm{ach}}(0.005) < 0.40$), giving $\limsup_{n\to\infty}\sqrt{n}(R_{\mathrm{WZ}}(n, D, 0.40) - R_{\mathrm{WZ}}(D)) \le -0.005950 < 0$, whereas `Statement` requires $\sqrt{V_{\min}}\,\Phi^{-1}(0.60) \ge 0$ since $V_{\min} \ge 0$ and $\Phi^{-1}(0.60) \approx +0.253347 > 0$. Therefore `¬ Statement`. $\square$

### Lean 4 Formalization Blueprint

Because the refutation requires **no** second-order converse, formalizing `theorem disproof : ¬ InfoTheory.Problems.NonAsymptoticLossyDispersion.Statement` in `lean/InfoTheory/Solutions/NonAsymptoticLossyDispersion.lean` decomposes cleanly into six self-contained lemmas:
1. `stdNormalQuantile_half : stdNormalQuantile (1/2) = 0` (from evenness and positivity of `gaussianPdf1D 1`).
2. Claim 1 (4-line Jensen + Gibbs inequality using `klDivergence_nonneg` from `InfoTheory.Bridge`).
3. Claim 2 (strict convexity of $g(\alpha) = h_2(p * \alpha) - h_2(\alpha)$ + scalar identity $H(Y' \mid U = u) = h_2(p * \alpha_u)$).
4. Exact-radius probabilistic sphere covering Lemma (finite counting argument over `Fin L → Fin K → Bool`).
5. Random binning collision bound (exact expectation over `H : C₁ → Fin M₁` using uniformity of $Y_1^{N_1}$ + concavity of `binaryEntropy`).
6. CLT / Berry–Esseen for independent (not necessarily identically distributed) Bernoulli sums (for $G_n$, $\sum Z_i$, and $d_H(u_1, Y_1^{N_1})$).

## Verification

All numerical constants, single-letter supporting-hyperplane bounds, asymptotic limits, and **non-asymptotic certified finite-$n$ upper bounds** were verified by `attempts/non-asymptotic-lossy-dispersion/code/verify_counterexample.py` (run with `.venv/bin/python`).

Key outputs:
- **Single-letter verification:** Independent numerical BFGS minimization over $P_{\hat{X}|B}$ confirms $\min (I(B; \hat{X}) + \lambda^* \mathbb{E}[d_0]) = 0.694241913635$ vs exact $\lambda^* = 0.694241913631$; dense grid verification over $10^5$ points confirms $\min_{\alpha \in [0, 1/2]} (g(\alpha) - \lambda_1(p - \alpha)) = 9.047 \times 10^{-12} \ge 0$.
- **Certified non-asymptotic bounds at $c = 0.03$** (exact $\mathrm{Bin}(n, 1/2)$ sum over $N_0$, exact probabilistic sphere-covering counts, exact $\mathrm{Bin}(N_1, p)$ tail in Mode A, exact random-binning union bound + concavity tangent bound + Shevtsova 2010 non-i.i.d. Berry–Esseen constant $C_{\mathrm{BE}} = 0.56$ in Mode B):
  - $n = 10^5$: $\text{excessProb} \le 0.592572$
  - $n = 10^6$: $\text{excessProb} \le 0.521951$
  - $n = 5 \times 10^6$: $\text{excessProb} \le 0.487506 < 1/2$
  - $n = 2 \times 10^7$: $\text{excessProb} \le 0.468894 < 1/2$
  - $n = 10^8$: $\text{excessProb} \le 0.456684 < 1/2$ (asymptotic limit: $0.444149$)
- **Asymptotic achievable second-order curve $L_{\mathrm{ach}}(\varepsilon)$:**
  - $\varepsilon = 0.05$: $+0.228743$ ($L / \Phi^{-1} = +0.1391$)
  - $\varepsilon = 0.25$: $+0.073548$ ($L / \Phi^{-1} = +0.1090$)
  - $\varepsilon = 0.40$: $-0.005950$ (opposite sign to $\Phi^{-1}(0.60) = +0.2533$)
  - $\varepsilon = 0.50$: $-0.062396$ (violates $\Phi^{-1}(0.50) = 0$)
  - $\varepsilon = 0.90$: $-0.528577$ ($L / \Phi^{-1} = +0.4125$)

What the computation establishes and does not establish: the script provides an independent check of the exact constants and a non-asymptotic finite-$n$ certificate confirming that `excessProb < 1/2` is already achieved at $n = 5 \times 10^6$ with $\sqrt{n}(R_n - R_{\mathrm{WZ}}(D)) = -0.03$. The refutation of `Statement` itself rests on the analytic proofs of Claims 1–5 above, not on numerical computation alone.

### Referee Audit (2026-11-27)
Independently audited by a fresh-context referee agent (Gemini 4 Neon): verified `IsInteriorDistortion`, both supporting hyperplanes (plus 5,000 random $|U| = 8$ adversarial trials with zero violations), the type-adaptive achievability proof, the non-asymptotic certificate (`verify_counterexample.py` updated to conservative `-1e-12` floor tolerance with identical outputs), and the real 2025/2026 arXiv papers (Li & Li `arXiv:2510.20241`, Lin Zhou `arXiv:2610.11998`). Clarified non-i.i.d. Berry–Esseen constant citation (Shevtsova 2010, *Doklady Math.* 82(3):862–864). Verdict: `VERIFIED`; status moved to `community-reviewed`.

## Dead ends

1. **Single binary symmetric Wyner–Ziv source (or ternary source with an idle symbol $X = 2$):** On the linear segment $D \in (d_c, p)$ of a single binary symmetric Wyner–Ziv source, the time-sharing fraction $\alpha = (p - D)/(p - d_c)$ is uniquely determined by $D$ at first order. Even after adding an idle symbol $X = 2$ to make the $X$-type sensitivity $\tau > 0$, there is only one first-order optimal allocation $(\alpha, 1-\alpha)$, so the encoder cannot switch between two different conditional variances $\sigma_A \ne \sigma_B$.
2. **Adding an erasure symbol $e$ with $d_1(b, e) = p$ directly to binary Wyner–Ziv on $S = 1$:** Attempting to obtain two zero-rate actions ($g(Y') = Y'$ with variance $p(1-p)$ vs $g(Y') = e$ with variance $0$) at $d_1 = p$ with nonzero left slope $-R_1'(p^-) > 0$ fails: we verified both analytically and numerically (via SLSQP dual optimization) that $R_1'(p^-) = 0$. The obstruction is that correlating $U$ with $B$ by $\pm\eta$ costs only $O(\eta^2)$ rate while allowing $g(u, y')$ to output $y'$ when $u = y'$ and cap distortion at $p$ via $e$ when $u \ne y'$, lowering expected distortion by $\Omega(\eta)$. Thus $S = 1$ cannot stay pinned at zero rate while $S = 0$ has positive slope.
3. **Pairing two binary Wyner–Ziv sub-sources ($p_0 \ne p_1$) with separate encoded/uncoded blocks in both modes:** When both modes simultaneously leave a positive fraction of noisy coordinates uncoded ($\sigma_D > 0$) and encode a positive fraction of noisy coordinates via Slepian–Wolf binning ($\sigma_R > 0$), a simple fixed-allocation scheme requires two independent Gaussian events (rate event and distortion event) to succeed simultaneously, yielding conditional success probability $\Phi(-s/\sigma_R)\Phi((s - \tau G - c)/\sigma_D) \le 1/4$ at $\tau G + c = 0$ instead of $1/2$. Replacing $S = 0$ by a point-to-point linear-segment source ($\sigma_R = \sigma_D = 0$) eliminates the simultaneous-noise obstruction completely: Mode A has $\sigma_R = 0$ and Mode B has $\sigma_D = 0$.

## References

- V. Kostina and S. Verdú, "Fixed-length lossy compression in the finite blocklength regime," *IEEE Trans. Inf. Theory*, vol. 58, no. 6, pp. 3309–3338, 2012.
- X. Li and C. T. Li, "New Second-Order Achievability Bounds for Coding with Side Information via Type Deviation Convergence," arXiv:2510.20241, Oct. 2025.
- I. G. Shevtsova, "On the absolute constants in the Berry–Esseen type inequalities for identically distributed summands," arXiv:1111.6554, 2011.
- V. Y. F. Tan and O. Kosut, "On the dispersions of three network information theory problems," *IEEE Trans. Inf. Theory*, vol. 60, no. 2, pp. 881–903, 2014.
- S. Watanabe, S. Kuzuoka, and V. Y. F. Tan, "Nonasymptotic and second-order achievability bounds for coding with side-information," *IEEE Trans. Inf. Theory*, vol. 61, no. 4, pp. 1574–1605, 2015.
- A. D. Wyner and J. Ziv, "The rate-distortion function for source coding with side information at the decoder," *IEEE Trans. Inf. Theory*, vol. 22, no. 1, pp. 1–10, 1976.
- L. Zhou, "Exact Second-Order Asymptotics for the Discrete Wyner–Ziv Problem," arXiv:2610.11998, Oct. 2026.
