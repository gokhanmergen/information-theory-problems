---
problem: ceo-problem-general
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: unverified
---

## Summary

We analyze the two-agent binary symmetric CEO problem (`X ~ Bern(1/2)`, `W_1 = BSC(p_1)`, `W_2 = BSC(p_2)`, Hamming distortion `D ∈ [0, 1/2]`) corresponding to `InfoTheory.Problems.CeoProblemGeneral.Statement`. We prove **exact operational tightness of the Berger–Tung inner bound** across two substantial regimes: (i) for all asymmetric channel pairs $0 < p_1 < p_2 < 1/2$, exact sum-rate tightness $R_{\text{sum}}^*(p_1, p_2, D) = R_{\text{1-agent}}(p_1, D)$ at $D = p_1$ and for all $D \in [D_{\mathrm{MGL}}(p_1, p_2), 1/2]$ via an elementary multi-letter Mrs. Gerber's Lemma decoupling converse (covering $>90\%$ of $[p_1, 1/2]$ even at $(0.10, 0.15)$ and $99.8\%$ at $(0.10, 0.25)$); and (ii) for symmetric channels $p_1 = p_2 = p < p_{\mathrm{rig}}^* \approx 0.162192$ and high distortion $D \in [D_{\mathrm{an}}(p), 1/2]$, **exact tightness of the full two-dimensional rate-distortion region** $\mathcal{R}_{\mathrm{CEO}}(p, p, D) = \{(R_1, R_2) \ge 0 : R_1 + R_2 \ge R_{\text{1-agent}}(p, D)\}$ by combining Courtade–Weissman's (2014) log-loss characterization with a new elementary **Channel-Bounded Asymmetric Information Combining Lemma** that avoids any symmetry assumption on auxiliary channels. We also prove an exact centralized noisy rate-distortion formula, construct an explicit one-time-pad coupling showing the classical Berger–Tung outer bound is strictly looser than the Berger–Tung inner bound at $D = p$ for all $p \in (0.1259, 1/2)$, and report numerical experiments on non-binary auxiliaries, 2-letter Berger–Tung, Körner–Marton hybrids, finite-blocklength linear quantizers, and combinatorial rectangles.

## Approach

Our attack combines four complementary tools:

1. **Direct operational converse via $M_1 \perp M_2 \mid X^n$ and Mrs. Gerber's Lemma (MGL)**: Because $Y_1^n - X^n - Y_2^n$ implies conditional independence $M_1 \perp M_2 \mid X^n$ for every $n$-letter code, the sum-rate decomposes as $n(R_1 + R_2) + \lambda H(X^n \mid M_1, M_2) \ge \lambda n + (n - H(Y_1^n \mid M_1)) + (n - H(Y_2^n \mid M_2)) - \lambda(I(X^n; M_1) + I(X^n; M_2)) + (\lambda - 1) I(M_1; M_2)$. Dropping $I(M_1; M_2) \ge 0$ already yields exact sum-rate tightness for asymmetric $p_1 < p_2$.
2. **Channel-Bounded Asymmetric Information Combining**: For symmetric $p_1 = p_2 = p$, retaining $I(U_1; U_2)$ is essential. Standard symmetric Information Combining ($H(X \mid U_1, U_2) \ge H(X \mid U_1) H(X \mid U_2)$) fails for asymmetric Z-channels (see Dead Ends), so we prove a channel-bounded quadratic lower bound $I(U_1; U_2) \ge c(p_1, p_2) I(X; U_1) I(X; U_2)$ valid for *all* finite-alphabet channels $U_1 - Y_1 - X - Y_2 - U_2$. Combined with Courtade–Weissman (2014, Theorem 10) and diagonal concavity, this resolves the full 2D rate region for $p < p_{\mathrm{rig}}^* \approx 0.162192$ and $D \ge D_{\mathrm{an}}(p)$.
3. **Boundary analysis at $D = p$**: We isolate the minimum-distortion point $D = p$ ($p_1 = p_2 = p$) as the sharpest testbed separating the Berger–Tung inner bound ($R_1 + R_2 \ge 1$), the Courtade–Weissman log-loss bound ($< 1$), the Berger–Tung outer bound ($2(1 - h(p(1-p))) < 1$ for $p > 0.1259$), and the centralized bound ($1 - 2p(1-p)$).
4. **Computational search for counterexamples**: We test non-binary auxiliaries ($|U_1|, |U_2| \le 4$), Z-channels, BEC quantizers, 2-letter Berger–Tung, Körner–Marton linear coding, finite-blocklength majority/Hamming-$[7,4]$ quantize-and-bin codes, and exact small-$n$ combinatorial rectangles.

## Claims

Notation: $h(x) = -x\log_2 x - (1-x)\log_2(1-x)$ is binary entropy, $a * b = a(1-b) + (1-a)b$ is binary convolution, $\rho_j = 1 - 2p_j$, and
$$R_{\text{1-agent}}(p, D) := 1 - h\!\left(\frac{D - p}{1 - 2p}\right) \qquad (D \in [p, 1/2]).$$

1. **[proved]** *(Minimum distortion and centralized noisy rate-distortion function)* For any $0 < p_1 \le p_2 < 1/2$, the minimum achievable Hamming distortion (even with a centralized encoder observing $(Y_1^n, Y_2^n)$) is $D_{\min}(p_1, p_2) = p_1 = \min(p_1, p_2)$.
   - When $p_1 = p_2 = p$, the exact centralized noisy rate-distortion function is
     $$R_{\mathrm{central}}(p, p, D) = \big(1 - 2p(1-p)\big) R_{\text{1-agent}}(p, D) \qquad \forall D \in [p, 1/2].$$
   - When $p_1 < p_2$, at the minimum distortion $D = p_1$ we have $R_{\mathrm{central}}(p_1, p_2, p_1) = 1$, hence $R_{\mathrm{sum}}^*(p_1, p_2, p_1) = 1 = R_{\text{1-agent}}(p_1, p_1)$, matching `InCEOBergerTungClosure` on the sum-rate face.

2. **[proved]** *(Exact operational sum-rate via MGL decoupling for asymmetric channels $p_1 < p_2$)* Let $0 < p_1 < p_2 < 1/2$, and let $D_{\mathrm{MGL}}(p_1, p_2) \in (p_1, 1/2)$ be the unique solution to
   $$\frac{\ln\frac{1 - q_1}{q_1}}{(1 - 2p_1)\ln\frac{1 - D}{D}} = \frac{1}{(1 - 2p_2)^2}, \qquad q_1 = \frac{D - p_1}{1 - 2p_1}.$$
   Then for every $D \in [D_{\mathrm{MGL}}(p_1, p_2), 1/2]$, every operationally achievable $(R_1, R_2, D)$ satisfies $R_1 + R_2 \ge R_{\text{1-agent}}(p_1, D)$. Since $(R_{\text{1-agent}}(p_1, D), 0, D) \in \mathtt{InCEOBergerTungClosure}$, the exact operational minimum sum-rate equals the Berger–Tung sum-rate $R_{\text{1-agent}}(p_1, D)$ throughout $[D_{\mathrm{MGL}}(p_1, p_2), 1/2]$.

3. **[proved]** *(Channel-Bounded Asymmetric Information Combining Lemma)* Let $X \sim \mathrm{Bern}(1/2)$, $W_j = \mathrm{BSC}(p_j)$ with $p_j \in (0, 1/2)$ and $\rho_j = 1 - 2p_j$, and let $(U_1, U_2)$ be arbitrary finite-alphabet random variables forming $U_1 - Y_1 - X - Y_2 - U_2$. Define $\phi(t) := (1+t)\log_2(1+t) - \frac{t}{\ln 2}$ and
   $$c(p_1, p_2) := \frac{\phi(\rho_1 \rho_2)}{(1 - h(p_1))(1 - h(p_2))} > 0.$$
   Then, with **no symmetry assumption** on $P(u_1 \mid y_1)$ or $P(u_2 \mid y_2)$,
   $$I(U_1; U_2) \ge c(p_1, p_2)\, I(X; U_1)\, I(X; U_2).$$
   In particular, for any $U_1 - X - U_2$ without channel constraints, the universal bound $I(U_1; U_2) \ge \left(2 - \frac{1}{\ln 2}\right) I(X; U_1) I(X; U_2)$ holds ($2 - \frac{1}{\ln 2} \approx 0.557305$).

4. **[proved]** *(Exact full 2D rate-distortion region for symmetric channels $p_1 = p_2 = p < p_{\mathrm{rig}}^*$ in the high-distortion regime)* Let $p_1 = p_2 = p \in (0, 1/2)$ with $\rho = 1 - 2p$, and let $f(x) := 1 - h\!\left(\frac{h^{-1}(1-x) - p}{1 - 2p}\right) = R_{\text{1-agent}}(p, h^{-1}(1-x))$ on $[0, 1 - h(p)]$. Define $p_{\mathrm{rig}}^* \approx 0.162192$ as the unique root in $(0, 1/2)$ of $(1 - 2p)^2 = \frac{2 \ln 2}{3 c(p, p)}$. For every $p \in (0, p_{\mathrm{rig}}^*)$ and every $D \in (p, 1/2)$ such that $x^* := 1 - h(D)$ and $\lambda := f'(x^*)$ satisfy
   $$\sup_{u \in [0, x^*]} f''(u) \le (\lambda - 1) c(p, p)$$
   (which always holds on a nonempty interval $[D_{\mathrm{an}}(p), 1/2)$ since $f''(0^+) = \frac{2\ln 2 (1-\rho^2)}{3\rho^4} < \frac{1-\rho^2}{\rho^2} c(p,p) < (\lambda - 1) c(p,p)$), the **entire** two-dimensional operational rate-distortion region coincides with the Berger–Tung inner bound:
   $$\mathtt{IsCEOAchievable}(R_1, R_2, D) \iff \mathtt{InCEOBergerTungClosure}(R_1, R_2, D) \iff R_1 \ge 0,\; R_2 \ge 0,\; R_1 + R_2 \ge R_{\text{1-agent}}(p, D).$$

5. **[proved]** *(Minimum-distortion boundary $D = p$ for symmetric $p_1 = p_2 = p$)*
   - **(a) Berger–Tung inner bound**: Every $(R_1, R_2, p) \in \mathtt{InCEOBergerTungClosure}$ satisfies $R_1 + R_2 \ge 1$.
   - **(b) Strict looseness of the Berger–Tung outer bound**: Relaxing $U_1 - Y_1 - Y_2 - U_2$ to the short Markov chains $U_1 - Y_1 - (X, Y_2)$ and $U_2 - Y_2 - (X, Y_1)$ admits an explicit coupling on $\{0, 1\}^2$ with reconstruction $g(U_1, U_2) = U_1 \oplus U_2$ achieving $D = p$ with $I(Y_1, Y_2; U_1, U_2) = 1 - 2p(1-p)$ and $I(Y_1; U_1 \mid U_2) = I(Y_2; U_2 \mid U_1) = 1 - h(p(1-p))$. Hence the Berger–Tung outer bound allows sum-rate $\max(1 - 2p(1-p),\, 2(1 - h(p(1-p)))) = 2(1 - h(p(1-p))) < 1$ for all $p \in \left(\frac{1 - \sqrt{1 - 4 h^{-1}(1/2)}}{2}, \frac{1}{2}\right) \approx (0.1259, 0.5)$ (e.g., $0.7314 < 1$ at $p = 0.2$).
   - **(c) Exact zero-overlap rectangle bound**: For any $n \ge 1$ and $A, B \subseteq \{0, 1\}^n$ such that $y_1 \wedge y_2 = 0^n$ for all $(y_1, y_2) \in A \times B$, $P_{\mathrm{DSBS}(q)}^n(A \times B) \le 2^{-n}$ for all $q \in (0, 1/2)$.

6. **[heuristic]** *(Numerical characterization of the remaining open regime)*
   - Extensive numerical optimization over $|U_1|, |U_2| \le 4$ (including Z-channels, BEC, soft 3-ary/4-ary quantizers, and Nelder–Mead local search), 2-letter Berger–Tung, and finite-blocklength structured quantize-and-bin codes (majority-$k$ for $k = 3, 5, 7$ and Hamming $[7, 4]$) finds **no** scheme achieving sum-rate strictly below $R_{\text{1-agent}}(\min(p_1, p_2), D)$ for either symmetric or asymmetric $(p_1, p_2)$.
   - Local expansion of the Courtade–Weissman log-loss bound near $D = 1/2$ for symmetric $p_1 = p_2 = p$ identifies the sharp log-loss single-agent threshold $p_{\mathrm{CW}}^* = \frac{1 - 1/\sqrt{3}}{2} \approx 0.211325$: for $p < p_{\mathrm{CW}}^*$, numerical evaluation of the log-loss bound matches $R_{\text{1-agent}}(p, D)$ down to a critical distortion $D_{\mathrm{CW}}(p)$ (e.g. $D_{\mathrm{CW}}(0.10) \approx 0.1174$, covering $95.6\%$ of $[0.1, 0.5]$; $D_{\mathrm{CW}}(0.20) \approx 0.3662$, covering $44.6\%$), whereas for $p > p_{\mathrm{CW}}^*$ (and for all $p \in (0, 1/2)$ near $D = p$), log-loss relaxation strictly underestimates $R_{\text{1-agent}}(p, D)$.

## Details

### Proof of Claim 1
Let $0 < p_1 \le p_2 < 1/2$. Given $(Y_1, Y_2)$, Bayes' rule yields:
- When $Y_1 = Y_2 = b$: $\Pr(X \neq b \mid Y_1 = Y_2 = b) = \tilde{p} := \frac{p_1 p_2}{p_1 p_2 + (1-p_1)(1-p_2)} < \frac{1}{2}$, so the MAP estimate is $b$.
- When $Y_1 \neq Y_2$: $\Pr(X \neq Y_1 \mid Y_1 \neq Y_2) = \frac{p_1 (1-p_2)}{p_1(1-p_2) + (1-p_1)p_2} \le \frac{1}{2}$ (strictly $< 1/2$ if $p_1 < p_2$, equal to $1/2$ if $p_1 = p_2$), so $\hat{X} = Y_1$ is always MAP-optimal.

Hence the minimum per-letter distortion is
$$D_{\min}(p_1, p_2) = \Pr(X \neq Y_1) = p_1.$$
Since $(X_i, Y_{1,i}, Y_{2,i})$ are i.i.d., any blocklength-$n$ decoder satisfies $\frac{1}{n}\sum_i \mathbb{E}[d(X_i, \hat{X}_i)] \ge p_1$.

By Dobrushin–Tsybakov (1962), the centralized noisy rate-distortion function $R_{\mathrm{central}}(p_1, p_2, D)$ equals the standard rate-distortion function of $Y = (Y_1, Y_2)$ under surrogate distortion $\bar{d}((y_1, y_2), \hat{x}) = \Pr(X \neq \hat{x} \mid Y_1 = y_1, Y_2 = y_2)$.

When $p_1 = p_2 = p$: $\bar{d}((0,1), \hat{x}) = \bar{d}((1,0), \hat{x}) = 1/2$ for both $\hat{x} \in \{0, 1\}$ (so $Y_1 \neq Y_2$ is a "don't-care" event of probability $q := 2p(1-p)$), while on $Y_1 = Y_2 = b$ (probability $1 - q$), $\bar{d}((b,b), b) = \tilde{p} = \frac{p^2}{p^2 + (1-p)^2}$ and $\bar{d}((b,b), 1-b) = 1 - \tilde{p}$. For any conditional distribution $P(\hat{X} \mid Y_1, Y_2)$, let $E = \mathbf{1}[Y_1 = Y_2]$ and let $r := \Pr(\hat{X} \neq Y_1 \mid E = 1)$. Then
$$D = q \cdot \frac{1}{2} + (1 - q)\big[(1 - r)\tilde{p} + r(1 - \tilde{p})\big] = p + (1 - 2p) r = p * r,$$
using $(1-q)\tilde{p} = p^2$ and $(1-q)(1 - 2\tilde{p}) = (1-p)^2 - p^2 = 1 - 2p$. Thus $r = \frac{D - p}{1 - 2p}$. Meanwhile,
$$I(Y_1, Y_2; \hat{X}) = H(\hat{X}) - H(\hat{X} \mid Y_1, Y_2) \ge H(\hat{X}) - q H(\hat{X} \mid E = 0) - (1 - q) H(\hat{X} \mid Y_1, E = 1).$$
Minimizing over $P(\hat{X} \mid Y_1, Y_2)$ with fixed $r$: symmetrizing $(\hat{X}, Y_1, Y_2) \mapsto (1 - \hat{X}, 1 - Y_1, 1 - Y_2)$ can only decrease $I(Y_1, Y_2; \hat{X})$ (by convexity) while preserving $D$, giving $H(\hat{X}) = 1$; on $E = 0$, choosing $\hat{X} \sim \mathrm{Bern}(1/2)$ independent of $(Y_1, Y_2)$ maximizes $H(\hat{X} \mid Y_1, Y_2, E = 0)$ at $1$; on $E = 1$, Fano/binary entropy gives $H(\hat{X} \mid Y_1, E = 1) \le h(r)$ with equality for $\mathrm{BSC}(r)$. Hence
$$R_{\mathrm{central}}(p, p, D) = 1 - q \cdot 1 - (1 - q) h(r) = (1 - q)(1 - h(r)) = \big(1 - 2p(1-p)\big) R_{\text{1-agent}}(p, D).$$

When $p_1 < p_2$ and $D = p_1$: on all four values of $(y_1, y_2)$, $\bar{d}((y_1, y_2), y_1) < \bar{d}((y_1, y_2), 1 - y_1)$ strictly. Thus $\mathbb{E}[\bar{d}((Y_1, Y_2), \hat{X})] = p_1$ forces $\hat{X} = Y_1$ almost surely, so $R_{\mathrm{central}}(p_1, p_2, p_1) = I(Y_1, Y_2; Y_1) = H(Y_1) = 1$. Since $R_1 + R_2 \ge R_{\mathrm{central}}(p_1, p_2, D)$ for every operational CEO code and $(1, 0, p_1) \in \mathtt{InCEOBergerTungClosure}$, we obtain $R_{\mathrm{sum}}^*(p_1, p_2, p_1) = 1$. $\square$

### Proof of Claim 2
Let $(enc_1, enc_2, dec)$ be any blocklength-$n$ CEO code with messages $M_1 = enc_1(Y_1^n)$, $M_2 = enc_2(Y_2^n)$ of rates $R_1 + \varepsilon$, $R_2 + \varepsilon$ achieving expected Hamming distortion $\le D + \varepsilon$. Because $Y_1^n - X^n - Y_2^n$ is a Markov chain and $M_j = enc_j(Y_j^n)$, we have the exact Markov chain $M_1 - Y_1^n - X^n - Y_2^n - M_2$, and hence $I(M_1; M_2 \mid X^n) = 0$. Expanding $I(Y_1^n, Y_2^n; M_1, M_2)$:
$$\begin{aligned}
n(R_1 + R_2 + 2\varepsilon) &\ge H(M_1) + H(M_2) \ge I(Y_1^n, Y_2^n; M_1, M_2) \\
&= I(X^n; M_1, M_2) + I(Y_1^n, Y_2^n; M_1, M_2 \mid X^n) \\
&= I(X^n; M_1, M_2) + I(Y_1^n; M_1 \mid X^n) + I(Y_2^n; M_2 \mid X^n).
\end{aligned}$$
Using $I(Y_j^n; M_j \mid X^n) = I(Y_j^n; M_j) - I(X^n; M_j) = H(X^n \mid M_j) - H(Y_j^n \mid M_j)$ (since $H(X^n) = H(Y_j^n) = n$) and the exact identity (from $I(M_1; M_2 \mid X^n) = 0$)
$$H(X^n \mid M_1, M_2) = H(X^n \mid M_1) + H(X^n \mid M_2) - n + I(M_1; M_2),$$
we obtain, for any $\lambda \ge 1$:
$$\begin{aligned}
&n(R_1 + R_2 + 2\varepsilon) + \lambda H(X^n \mid M_1, M_2) \\
&\ge n + (\lambda - 1) H(X^n \mid M_1, M_2) + \big[H(X^n \mid M_1) - H(Y_1^n \mid M_1)\big] + \big[H(X^n \mid M_2) - H(Y_2^n \mid M_2)\big] \\
&= (2 - \lambda) n + (\lambda - 1) I(M_1; M_2) + \big[\lambda H(X^n \mid M_1) - H(Y_1^n \mid M_1)\big] + \big[\lambda H(X^n \mid M_2) - H(Y_2^n \mid M_2)\big].
\end{aligned}$$
Drop $(\lambda - 1) I(M_1; M_2) \ge 0$. Set $u_j := \frac{1}{n} H(Y_j^n \mid M_j) \in [0, 1]$. Since $X^n = Y_j^n \oplus N_j^n$ with $N_j^n \sim \mathrm{Bern}(p_j)^{\otimes n}$ independent of $(Y_j^n, M_j)$, the multi-letter **Mrs. Gerber's Lemma** (Wyner–Ziv 1973) gives
$$\frac{1}{n} H(X^n \mid M_j) \ge h\big(p_j * h^{-1}(u_j)\big) \qquad (j = 1, 2).$$
Divide by $n$ and apply Fano's inequality $\frac{1}{n} H(X^n \mid M_1, M_2) \le h(D + \varepsilon)$:
$$R_1 + R_2 + 2\varepsilon + \lambda h(D + \varepsilon) \ge (2 - \lambda) + \min_{u_1 \in [0, 1]} \big[\lambda h(p_1 * h^{-1}(u_1)) - u_1\big] + \min_{u_2 \in [0, 1]} \big[\lambda h(p_2 * h^{-1}(u_2)) - u_2\big].$$
By Mrs. Gerber's Lemma, $u \mapsto h(p_j * h^{-1}(u))$ is strictly convex on $[0, 1]$ with left derivative $(1 - 2p_j)^2$ at $u = 1^-$. Therefore, whenever $1 \le \lambda \le \frac{1}{(1 - 2p_2)^2}$, the second minimum is attained at $u_2 = 1$ with value $\lambda - 1$. Now choose
$$\lambda = \lambda(D) := \left.\frac{d}{du}\left(-R_{\text{1-agent}}(p_1, h^{-1}(u))\right)\right|_{u = h(D)} = \frac{\ln\frac{1 - q_1}{q_1}}{(1 - 2p_1)\ln\frac{1 - D}{D}}, \qquad q_1 = \frac{D - p_1}{1 - 2p_1}.$$
Because $u \mapsto h(p_1 * h^{-1}(u))$ is strictly convex, $\lambda(D)$ is strictly decreasing on $(p_1, 1/2)$, with $\lim_{D \to p_1^+} \lambda(D) = +\infty$ and $\lim_{D \to 1/2^-} \lambda(D) = \frac{1}{(1 - 2p_1)^2} < \frac{1}{(1 - 2p_2)^2}$. Thus there is a unique root $D_{\mathrm{MGL}}(p_1, p_2) \in (p_1, 1/2)$ where $\lambda(D) = \frac{1}{(1 - 2p_2)^2}$. For every $D \in [D_{\mathrm{MGL}}(p_1, p_2), 1/2)$, we have $1 < \lambda(D) \le \frac{1}{(1 - 2p_2)^2}$, and the first minimum is uniquely attained at $u_1 = h(q_1)$, yielding
$$(2 - \lambda) + \big[\lambda h(D) - h(q_1)\big] + (\lambda - 1) = (1 - h(q_1)) + \lambda h(D) = R_{\text{1-agent}}(p_1, D) + \lambda h(D).$$
Letting $\varepsilon \to 0^+$ cancels $\lambda h(D)$ and yields $R_1 + R_2 \ge R_{\text{1-agent}}(p_1, D)$. (The endpoint $D = 1/2$ is trivial.) $\square$

### Proof of Claim 3
For each $u_j \in \mathcal{U}_j$ with $P(u_j) > 0$, define the posterior bias $r_j(u_j) := 2\Pr(X = 1 \mid U_j = u_j) - 1 \in [-1, 1]$. Since $X \sim \mathrm{Bern}(1/2)$, $\mathbb{E}[r_j(U_j)] = 0$. Moreover, because $U_j - Y_j - X$ with $W_j = \mathrm{BSC}(p_j)$,
$$\Pr(X = 1 \mid U_j = u_j) = p_j + (1 - 2p_j)\Pr(Y_j = 1 \mid U_j = u_j) \in [p_j, 1 - p_j],$$
so $|r_j(u_j)| \le \rho_j = 1 - 2p_j$ everywhere.

Using $X \sim \mathrm{Bern}(1/2)$ and $U_1 \perp U_2 \mid X$, Bayes' rule gives
$$\frac{P(u_1, u_2)}{P(u_1) P(u_2)} = \sum_{x \in \{0,1\}} \frac{P(x \mid u_1) P(x \mid u_2)}{P(x)} = 2\left(\frac{1+r_1}{2}\frac{1+r_2}{2} + \frac{1-r_1}{2}\frac{1-r_2}{2}\right) = 1 + r_1(u_1) r_2(u_2).$$
Since $\mathbb{E}_{P(U_1) P(U_2)}[r_1(U_1) r_2(U_2)] = \mathbb{E}[r_1(U_1)] \mathbb{E}[r_2(U_2)] = 0$, we have the exact representation
$$I(U_1; U_2) = \mathbb{E}_{P(U_1) P(U_2)}\big[\phi(r_1(U_1) r_2(U_2))\big], \qquad \phi(t) := (1 + t)\log_2(1 + t) - \frac{t}{\ln 2}.$$

**Step 1 (Monotonicity of $\phi(t)/t^2$):** Let $k(t) := \phi(t)/t^2$ on $(-1, 1]$ with $k(0) = \frac{1}{2\ln 2}$. Then $(\ln 2)\, t^3 k'(t) = 2t - (2+t)\ln(1+t) =: m(t)$. We have $m(0) = 0$, $m'(t) = \frac{t}{1+t} - \ln(1+t)$ with $m'(0) = 0$, and $m''(t) = \frac{-t}{(1+t)^2}$. For $t > 0$, $m'' < 0 \implies m' < 0 \implies m < 0 \implies k'(t) < 0$. For $t \in (-1, 0)$, $m'' > 0 \implies m' < 0 \implies m > 0$, and since $t^3 < 0$, again $k'(t) < 0$. Thus $k(t)$ is strictly decreasing on $[-1, 1]$. Since $r_1(u_1) r_2(u_2) \in [-\rho_1 \rho_2, \rho_1 \rho_2]$,
$$\phi(r_1(u_1) r_2(u_2)) \ge \frac{\phi(\rho_1 \rho_2)}{(\rho_1 \rho_2)^2}\, r_1(u_1)^2 r_2(u_2)^2.$$

**Step 2 (Monotonicity of $\psi(r)/r^2$):** Let $\psi(r) := 1 - h\!\left(\frac{1+r}{2}\right) = \frac{1}{\ln 2} \sum_{m=1}^{\infty} \frac{r^{2m}}{2m(2m-1)}$. Dividing by $r^2$ gives a power series in $r^2$ with strictly positive coefficients, so $\psi(r)/r^2$ is strictly increasing in $|r| \in [0, 1]$. Since $|r_j(u_j)| \le \rho_j$,
$$\psi(r_j(u_j)) \le \frac{\psi(\rho_j)}{\rho_j^2}\, r_j(u_j)^2 = \frac{1 - h(p_j)}{\rho_j^2}\, r_j(u_j)^2.$$

**Step 3 (Combine):** Taking expectations and noting $I(X; U_j) = \mathbb{E}[\psi(r_j(U_j))]$,
$$I(U_1; U_2) \ge \frac{\phi(\rho_1 \rho_2)}{\rho_1^2 \rho_2^2}\, \mathbb{E}[r_1^2]\, \mathbb{E}[r_2^2] \ge \frac{\phi(\rho_1 \rho_2)}{(1 - h(p_1))(1 - h(p_2))}\, I(X; U_1)\, I(X; U_2) = c(p_1, p_2)\, I(X; U_1)\, I(X; U_2).$$
Setting $\rho_1 = \rho_2 = 1$ gives the universal constant $\phi(1)/\psi(1)^2 = 2 - \frac{1}{\ln 2}$. $\square$

### Proof of Claim 4
**Achievability:** For symmetric $p_1 = p_2 = p$, $(R_{\text{1-agent}}(p, D), 0, D)$ is in `InCEOBergerTungInner` via $U_1 = Y_1 \oplus Z_q$ ($q = \frac{D-p}{1-2p}$), $U_2 = \mathrm{const}$, and symmetrically $(0, R_{\text{1-agent}}(p, D), D)$ is in `InCEOBergerTungInner`. Time-sharing ($|Q| = 2$) achieves every $(R_1, R_2) \in \mathbb{R}_{\ge 0}^2$ with $R_1 + R_2 \ge R_{\text{1-agent}}(p, D)$.

**Converse:** Suppose $(R_1, R_2, D)$ is operationally achievable under Hamming distortion. By Fano's inequality, every blocklength-$n$ code with expected Hamming distortion $\le D + \varepsilon$ satisfies $\frac{1}{n} H(X^n \mid M_1, M_2) \le h(D + \varepsilon)$, so $(R_1, R_2, h(D))$ is operationally achievable for the same binary CEO source under logarithmic loss. By Courtade–Weissman (2014, Theorem 10), the closure of the Berger–Tung region is exact under logarithmic loss: for every $\delta > 0$, there exist a finite-alphabet time-sharing variable $Q \perp (X, Y_1, Y_2)$ and auxiliaries $(U_1, U_2)$ forming $U_1 - (Y_1, Q) - (X, Q) - (Y_2, Q) - U_2$ such that $H(X \mid U_1, U_2, Q) \le h(D) + \delta$ and $R_1 + R_2 + \delta \ge I(Y_1, Y_2; U_1, U_2 \mid Q)$.

Fix $Q = q$ and set $x := I(X; U_1 \mid Q = q) \in [0, 1 - h(p)]$ and $y := I(X; U_2 \mid Q = q) \in [0, 1 - h(p)]$. Using the exact single-letter identities (as in Claim 2), Mrs. Gerber's Lemma ($1 - H(Y_1 \mid U_1, Q = q) \ge f(x)$ and $1 - H(Y_2 \mid U_2, Q = q) \ge f(y)$), and Claim 3 ($I(U_1; U_2 \mid Q = q) \ge c(p, p)\, x y$), we obtain for any $\lambda > 1$:
$$I(Y_1, Y_2; U_1, U_2 \mid Q = q) + \lambda H(X \mid U_1, U_2, Q = q) \ge \lambda + \Phi(x, y),$$
where
$$\Phi(x, y) := f(x) + f(y) - \lambda(x + y) + (\lambda - 1) c(p, p)\, x y \qquad \text{on } [0, 1 - h(p)]^2.$$
Choose $x^* = 1 - h(D)$ and $\lambda = f'(x^*) > 1/\rho^2 > 1$, and assume $\sup_{u \in [0, x^*]} f''(u) \le (\lambda - 1) c(p, p)$.

1. *Reduction to $[0, x^*]^2$*: For any $x > x^*$ and $y \ge 0$, $\frac{\partial \Phi}{\partial x}(x, y) = f'(x) - \lambda + (\lambda - 1) c(p, p) y > f'(x^*) - \lambda = 0$ by strict convexity of $f$. Hence reducing $x$ to $x^*$ (and similarly $y > x^*$ to $x^*$) strictly decreases $\Phi$, so $\min_{[0, 1-h(p)]^2} \Phi = \min_{[0, x^*]^2} \Phi$.
2. *Diagonal concavity on $[0, x^*]^2$*: Fix $s = x + y \in [0, 2x^*]$ and let $g_s(t) := \Phi(t, s - t)$ on $I_s := [\max(0, s - x^*), \min(s, x^*)]$. For all $t \in I_s$, both $t$ and $s - t$ lie in $[0, x^*]$, so
   $$g_s''(t) = f''(t) + f''(s - t) - 2(\lambda - 1) c(p, p) \le 0.$$
   Hence $g_s$ is concave on $I_s$, so its minimum is attained at an endpoint where $x \in \{0, x^*\}$ or $y \in \{0, x^*\}$.
3. *Boundary check*:
   - If $y = 0$ (or $x = 0$): $\Phi(x, 0) = f(x) - \lambda x \ge f(x^*) - \lambda x^* = \Phi(x^*, 0)$ by convexity of $f$ and $f'(x^*) = \lambda$.
   - If $x = x^*$ and $y \in [0, x^*]$ (or symmetrically $y = x^*$): by convexity of $f$ with $f(0) = 0$, $f(y) \ge f'(0^+) y$, while the Fundamental Theorem of Calculus gives $\lambda - f'(0^+) = \int_0^{x^*} f''(u)\, du \le (\lambda - 1) c(p, p)\, x^*$. Therefore
     $$\Phi(x^*, y) - \Phi(x^*, 0) = f(y) - \lambda y + (\lambda - 1) c(p, p)\, x^* y \ge y\big[f'(0^+) - \lambda + (\lambda - 1) c(p, p)\, x^*\big] \ge 0.$$

Thus $\Phi(x, y) \ge f(x^*) - \lambda x^* = R_{\text{1-agent}}(p, D) - \lambda(1 - h(D))$ for every $(x, y) \in [0, 1 - h(p)]^2$, so
$$I(Y_1, Y_2; U_1, U_2 \mid Q = q) + \lambda H(X \mid U_1, U_2, Q = q) \ge R_{\text{1-agent}}(p, D) + \lambda h(D)$$
for every $q$. Averaging over $Q$ and letting $\delta \to 0^+$ yields $R_1 + R_2 \ge R_{\text{1-agent}}(p, D)$.

Finally, near $x^* \to 0^+$ ($D \to 1/2^-$), Taylor expansion yields $f'(0^+) = \frac{1}{\rho^2}$ and $f''(0^+) = \frac{2 \ln 2\, (1 - \rho^2)}{3 \rho^4}$. Hence $f''(0^+) < (f'(0^+) - 1) c(p, p) = \frac{1 - \rho^2}{\rho^2} c(p, p)$ iff $\rho^2 > \frac{2 \ln 2}{3 c(p, p)}$, i.e. $p < p_{\mathrm{rig}}^* \approx 0.162192$. By continuity of $f'$ and $f''$ at $0^+$, the condition holds on a nonempty interval $[D_{\mathrm{an}}(p), 1/2)$ for every $p \in (0, p_{\mathrm{rig}}^*)$. $\square$

### Proof of Claim 5
**(a)** By standard Carathéodory cardinality bounds ($|U_1| \le 4, |U_2| \le 4, |Q| \le 4$), the set of single-letter Berger–Tung distributions is compact, so any $(R_1, R_2, p) \in \mathtt{InCEOBergerTungClosure}$ is attained by a valid $(Q, U_1, U_2, g)$ with $\mathbb{E}[d(X, g(U_1, U_2, Q))] = p$. Since $\mathbb{E}[d(X, g(U_1, U_2, q)) \mid Q = q] \ge p$ for every $q$, equality holds for every $q$ with $P(q) > 0$. Fix such a $q$ and suppress it from notation. Because $D - p = (1 - 2\tilde{p})\Pr(Y_1 = Y_2 \neq g(U_1, U_2))$ and $1 - 2\tilde{p} > 0$, we must have $g(u_1, u_2) = 0$ whenever $P(Y_1 = Y_2 = 0, u_1, u_2) > 0$, and $g(u_1, u_2) = 1$ whenever $P(Y_1 = Y_2 = 1, u_1, u_2) > 0$. By the long Markov chain $U_1 - Y_1 - Y_2 - U_2$ and $P(Y_1 = y_1, Y_2 = y_2) > 0$ for all $(y_1, y_2)$,
$$P(Y_1 = Y_2 = b, u_1, u_2) > 0 \iff P(u_1 \mid Y_1 = b) > 0 \text{ and } P(u_2 \mid Y_2 = b) > 0.$$
Define the ambiguous sets $E_j := \{u_j : P(u_j \mid Y_j = 0) > 0 \text{ and } P(u_j \mid Y_j = 1) > 0\}$. If both $E_1$ and $E_2$ were nonempty, any $(u_1, u_2) \in E_1 \times E_2$ would have positive probability under both $(0, 0)$ and $(1, 1)$, making $g(u_1, u_2)$ impossible. Thus $E_1 = \emptyset$ or $E_2 = \emptyset$, so either $Y_1$ is a deterministic function of $U_1$ or $Y_2$ is a deterministic function of $U_2$. In either case, $I(Y_1, Y_2; U_1, U_2 \mid Q = q) \ge \min(H(Y_1), H(Y_2)) = 1$. Averaging over $Q$ gives $R_1 + R_2 \ge 1$. $\square$

**(b)** Define $P(U_1, U_2 \mid Y_1, Y_2)$ on $\{0, 1\}^2$ by:
- Given $(Y_1, Y_2) = (0, 0)$: $(U_1, U_2)$ uniform on $\{(0, 0), (1, 1)\}$;
- Given $(Y_1, Y_2) = (1, 1)$: $(U_1, U_2)$ uniform on $\{(0, 1), (1, 0)\}$;
- Given $Y_1 \neq Y_2$: $(U_1, U_2)$ uniform on $\{0, 1\}^2$.

Then $U_1 \sim \mathrm{Bern}(1/2)$ is independent of $(X, Y_1, Y_2)$ (so $U_1 - Y_1 - (X, Y_2)$ holds), and symmetrically $U_2 - Y_2 - (X, Y_1)$ holds. With $g(U_1, U_2) = U_1 \oplus U_2$, we have $g(U_1, U_2) = Y_1 = Y_2$ almost surely whenever $Y_1 = Y_2$, hence $D = p$. Let $q = 2p(1-p)$. Direct computation gives $H(U_1, U_2) = 2$ (in fact $U_1 \perp U_2$), $H(U_1, U_2 \mid Y_1, Y_2) = (1 - q)\cdot 1 + q \cdot 2 = 1 + q$, so $I(Y_1, Y_2; U_1, U_2) = 1 - q = 1 - 2p(1-p)$. Also, given $(Y_1 = 0, U_2 = 0)$, $U_1 = 0$ with prob $1 - q$ (when $Y_2 = 0$) and $U_1 \sim \mathrm{Bern}(1/2)$ with prob $q$ (when $Y_2 = 1$), so $P(U_1 = 1 \mid Y_1 = 0, U_2 = 0) = q/2 = p(1-p)$, giving $I(Y_1; U_1 \mid U_2) = I(Y_2; U_2 \mid U_1) = 1 - h(p(1-p))$. Since $2(1 - h(p(1-p))) < 1 \iff h(p(1-p)) > 1/2 \iff p(1-p) > h^{-1}(1/2) \approx 0.110028 \iff p > 0.1259$, the Berger–Tung outer bound strictly undercuts $1$ for all $p \in (0.1259, 1/2)$. $\square$

**(c)** Let $A, B \subseteq \{0, 1\}^n$ satisfy $y_1 \wedge y_2 = 0^n$ for all $(y_1, y_2) \in A \times B$. Let $S := \{i \in [n] : \exists y_1 \in A,\, y_{1,i} = 1\}$ and $T := \{i \in [n] : \exists y_2 \in B,\, y_{2,i} = 1\}$. Then $S \cap T = \emptyset$, so $A \subseteq \{y_1 : y_{1, S^c} = 0\}$ and $B \subseteq \{y_2 : y_{2, S} = 0\}$. Because coordinates of $(Y_1^n, Y_2^n) \sim \mathrm{DSBS}(q)^n$ are independent and each marginal is uniform:
$$P_{\mathrm{DSBS}(q)}^n(A \times B) \le P(Y_{1, S^c} = 0) \cdot P(Y_{2, S} = 0) = 2^{-|S^c|} \cdot 2^{-|S|} = 2^{-n}. \qquad \square$$

### Numerical Tables & Supporting Computations (Claims 2, 4, 5, 6)

All computations are reproduced by `attempts/ceo-problem-general/code/analyze_ceo.py`, `attempts/ceo-problem-general/code/verify_theorems_ceo.py`, and `attempts/ceo-problem-general/code/verify_rigorous_ceo.py`.

**Table 1: Asymmetric MGL-Decoupling Exactness Threshold $D_{\mathrm{MGL}}(p_1, p_2)$ (Claim 2)**

| $(p_1, p_2)$ | $D_{\mathrm{MGL}}$ | Fraction of $[p_1, 0.5]$ solved | $R_{\text{1-agent}}(p_1, D_{\mathrm{MGL}})$ |
|---|---:|---:|---:|
| $(0.05, 0.10)$ | $0.076113$ | $94.20\%$ | $0.81058$ |
| $(0.05, 0.20)$ | $0.050589$ | $99.87\%$ | $0.99213$ |
| $(0.10, 0.15)$ | $0.138534$ | $90.37\%$ | $0.72144$ |
| $(0.10, 0.20)$ | $0.107125$ | $98.22\%$ | $0.92655$ |
| $(0.10, 0.25)$ | $0.100725$ | $99.82\%$ | $0.98953$ |
| $(0.15, 0.25)$ | $0.156162$ | $98.24\%$ | $0.92725$ |
| $(0.20, 0.30)$ | $0.203581$ | $98.81\%$ | $0.94732$ |

**Table 2: Symmetric Exact Full-Region Thresholds for $p_1 = p_2 = p$ (Claim 4 vs. Claim 6)**

- $D_{\mathrm{an}}(p)$: purely analytical sufficient condition $\sup_{u \le 1-h(D)} f''(u) \le (\lambda - 1) c(p, p)$ (Claim 4).
- $D_{\mathrm{rig}}(p)$: 2D global minimum of $\Phi(x, y)$ on $[0, 1 - h(p)]^2$ using the proved constant $c(p, p)$ (Claim 3).
- $D_{\mathrm{CW}}(p)$: numerical Courtade–Weissman log-loss threshold (Claim 6; vanishes at $p_{\mathrm{CW}}^* = \frac{1 - 1/\sqrt{3}}{2} \approx 0.211325$).

| $p$ | $c(p, p)$ | $D_{\mathrm{an}}(p)$ (% of $[p,0.5]$) | $D_{\mathrm{rig}}(p)$ (% of $[p,0.5]$) | $D_{\mathrm{CW}}(p)$ (% of $[p,0.5]$) |
|---|---:|---:|---:|---:|
| $0.05$ | $0.74771$ | $0.28254$ ($48.3\%$) | $0.15271$ ($77.2\%$) | $0.05328$ ($99.3\%$) |
| $0.08$ | $0.82773$ | $0.30778$ ($45.8\%$) | $0.18896$ ($74.1\%$) | — |
| $0.10$ | $0.87648$ | $0.33092$ ($42.3\%$) | $0.22270$ ($69.3\%$) | $0.11743$ ($95.6\%$) |
| $0.12$ | $0.92251$ | $0.35988$ ($36.9\%$) | $0.26618$ ($61.5\%$) | — |
| $0.14$ | $0.96624$ | $0.39813$ ($28.3\%$) | $0.32640$ ($48.2\%$) | — |
| $0.15$ | $0.98732$ | $0.42449$ ($21.6\%$) | — | $0.20443$ ($84.5\%$) |
| $0.20$ | $1.08469$ | — ($p > p_{\mathrm{rig}}^*$) | — | $0.36619$ ($44.6\%$) |

**Table 3: Sum-Rate Comparison for Symmetric Binary CEO ($p_1 = p_2 = 0.2$)**

| $D$ | $R_{\text{1-agent}}$ | $R_{\mathrm{CW}}(h(D))$ | $R_{\mathrm{central}}$ | Gap $(1\text{-Ag} - \mathrm{CW})$ | Gap $(1\text{-Ag} - \mathrm{Cen})$ |
|---:|---:|---:|---:|---:|---:|
| $0.200$ | $1.00000$ | $0.90260$ | $0.68000$ | $0.09740$ | $0.32000$ |
| $0.236$ | $0.67445$ | $0.65772$ | $0.45867$ | $0.01673$ | $0.21578$ |
| $0.271$ | $0.47338$ | $0.46924$ | $0.32197$ | $0.00415$ | $0.15141$ |
| $0.307$ | $0.32306$ | $0.32216$ | $0.21974$ | $0.00090$ | $0.10331$ |
| $0.343$ | $0.20814$ | $0.20803$ | $0.14154$ | $0.00011$ | $0.06660$ |
| $0.379$ | $0.12164$ | $0.12164$ | $0.08275$ | $0.00000$ | $0.03889$ |
| $0.450$ | $0.02013$ | $0.02013$ | $0.01369$ | $0.00000$ | $0.00644$ |

*(For $p_1 = p_2 = 0.2$, structured quantize-and-bin codes fall far short: Maj-3 gives $R_{\mathrm{sum}} = 0.6473$ vs $R_{\text{1-agent}}(0.35) = 0.1887$; Hamming $[7,4]$ gives $R_{\mathrm{sum}} = 1.1112$ vs $R_{\text{1-agent}}(0.275) = 0.4564$. Across 15,000 random $k \le 4$ auxiliaries + Z-channel/BEC sweeps + 90 Nelder–Mead restarts, the maximum improvement over $R_{\text{1-agent}}$ was $0.0000000$.)*

### Novelty Check
We searched the literature (via web search across IEEE Trans. Inf. Theory and arXiv up to 2026) covering Berger–Zhang–Viswanathan (1996), Wagner–Anantharam (2008), Courtade–Weissman (2014), Oohama (1998, 2005), Chen–Berger, and Nangir–Asvadi–Chen–Matsumoto (binary CEO under log-loss). While the CEO sum-rate identity $I(Y_1, Y_2; U_1, U_2) = I(X; U_1, U_2) + \sum_j I(Y_j; U_j \mid X)$ and the log-loss tightness theorem are classical (Oohama 1998; Courtade–Weissman 2014), we did not locate in the cited references either (i) the explicit asymmetric MGL-decoupling exactness regime $[D_{\mathrm{MGL}}(p_1, p_2), 1/2]$ for Hamming-distortion binary CEO, or (ii) the Channel-Bounded Asymmetric Information Combining Lemma (Claim 3) and the resulting exact full 2D rate-region theorem for symmetric Hamming-distortion binary CEO on $p < p_{\mathrm{rig}}^* \approx 0.162192, D \ge D_{\mathrm{an}}(p)$. Even if parts of the high-distortion log-loss collapse are folklore among specialists, the self-contained proofs and exact thresholds here sharpen the open problem directly toward the remaining low-distortion / high-noise regime ($p > 0.2113$ or $D \approx p$).

## Verification

- `attempts/ceo-problem-general/code/analyze_ceo.py`: verifies Claims 1, 5(b), 6 (Blahut–Arimoto centralized RD matches $(1 - 2p(1-p)) R_{\text{1-agent}}(p, D)$ to $5$ digits; random/structured BT search over $|U_j| \le 4$; finite-$k$ majority and Hamming-$[7,4]$ exact calculations; small-$n$ rectangle optimization for $n = 2..7$).
- `attempts/ceo-problem-general/code/verify_theorems_ceo.py`: verifies the Z-channel counterexample to symmetric Information Combining (Dead End 1), exact $D_{\mathrm{MGL}}(p_1, p_2)$ (Table 1), and $D_{\mathrm{CW}}(p)$ (Table 2).
- `attempts/ceo-problem-general/code/verify_rigorous_ceo.py`: independently stress-tests Claim 3 across Z-channels (both orientations) and $9{,}000$ random $k \in \{2,3,4\}$ channels per $p \in \{0.05, 0.10, 0.15\}$ (minimum slack $= 0.00000000$; observed minimum ratio within $0.25\%$ of $c(p,p)$), verifies monotonicity of $\phi(t)/t^2$, $\psi(r)/r^2$, and $f''(x)$, and computes $p_{\mathrm{rig}}^* = 0.162192$, $D_{\mathrm{rig}}(p)$, and $D_{\mathrm{an}}(p)$ (Table 2).

## Dead ends

1. **Standard symmetric Information Combining fails for asymmetric channels**: We initially attempted to prove Claim 4 using the symmetric Information Combining inequality $H(X \mid U_1, U_2) \ge H(X \mid U_1) H(X \mid U_2)$ (Land–Huber–Huettinger 2005, which holds for BMS channels). Numerical testing immediately refuted this for general binary-input channels: two identical Z-channels with $a_1 = a_2 = 0.29$ give $H(X \mid U_1) = H(X \mid U_2) = 0.49591$, $H(X \mid U_1) H(X \mid U_2) = 0.24592$, but $H(X \mid U_1, U_2) = 0.21334$ (violation $-0.03258$). This forced us to derive the asymmetry-safe Channel-Bounded Information Combining Lemma (Claim 3).
2. **Körner–Marton linear coding for $Y_1 \oplus Y_2$**: In the symmetric CEO problem, $Y_1 \oplus Y_2 = N_1 \oplus N_2 \sim \mathrm{Bern}(2p(1-p))$ identifies the exact "don't-care" coordinates where $Y_1 \neq Y_2$, which a centralized encoder skips to achieve $R_{\mathrm{central}}(p, p, p) = 1 - 2p(1-p) < 1$. We tested sending linear syndromes $H Y_1^n, H Y_2^n$ (rate $h(2p(1-p))$ each) to recover $Z^n = Y_1^n \oplus Y_2^n$ at the decoder, plus a rate-$R_1'$ description of $Y_1^n$ to recover $Y_{1,i}$ on $\{i : Z_i = 0\}$. **Obstruction**: $Y_1$ is statistically independent of $Z = Y_1 \oplus Y_2$. For a decoder with independent side information $Z$ and erasure-distortion $d(y_1, \hat{x}; z) = \mathbf{1}[z = 0 \land y_1 \neq \hat{x}]$, the Wyner–Ziv rate is $\min_{U - Y_1 - Z,\, \hat{x}(U,0) = Y_1} I(Y_1; U \mid Z) = \min_{\hat{x}(U,0)=Y_1} I(Y_1; U) = H(Y_1) = 1$, giving zero savings over transmitting $Y_1$ directly.
3. **Multiplicative tilting for the $\delta > 0$ rectangle bound at $D = p$**: To extend Claim 5(c) from $\delta = 0$ to $\delta \to 0^+$ (which would prove $R_{\mathrm{sum}}^*(p, p, p) = 1$ operationally), we bounded $P^n(A \times B) \lambda^{\delta n} \le \sum_{y_1 \in A, y_2 \in B} \prod_i K_\lambda(y_{1,i}, y_{2,i})$ with $K_\lambda = \begin{pmatrix}(1-q)/2 & q/2 \\ q/2 & \lambda(1-q)/2\end{pmatrix}$. **Obstruction**: Dropping the constraint $A \times B$ and maximizing $\sum_{A \times B} K_\lambda^{\otimes n}$ over unconstrained indicators yields $A = B = \{0,1\}^n$ with value $(1 - (1-\lambda)\frac{1-q}{2})^n \to (\frac{1+q}{2})^n \gg 2^{-n}$, because $K_\lambda$ merely attenuates $(1,1)$ rather than enforcing the conditional mean $\mathbb{E}[\mathrm{wt}(Y_1 \wedge Y_2) \mid A \times B] \le \delta n$. Moreover, our exact small-$n$ rectangle search at $p = 0.2$ shows that for $\delta = 0.02$, the minimum rate drops from $1.000$ ($n=2..4$) to $0.953$ ($n=7$), confirming that any converse at $D = p$ must track the exact $\delta \to 0^+$ asymptotic cleanly.
4. **Log-loss relaxation cannot resolve the low-distortion or $p > p_{\mathrm{CW}}^*$ regime**: For $p > p_{\mathrm{CW}}^* = \frac{1 - 1/\sqrt{3}}{2} \approx 0.211325$ (and for every $p \in (0, 1/2)$ near $D = p$), two symmetric BSC quantizers strictly beat single-agent compression under log-loss ($R_{\mathrm{CW}}(p, p, h(D)) < R_{\text{1-agent}}(p, D)$, e.g. $0.9026 < 1.0000$ at $p = D = 0.2$). Resolving `CeoProblemGeneral.Statement` at $D = p$ or $p > 0.2113$ therefore requires a converse that exploits Hamming distortion directly rather than passing through Fano's inequality to log-loss.

## References

- T. Berger, Z. Zhang, and H. Viswanathan, "The CEO problem," *IEEE Trans. Inf. Theory*, vol. 42, no. 3, pp. 887–902, 1996.
- R. L. Dobrushin and B. S. Tsybakov, "Information transmission with additional noise," *IRE Trans. Inf. Theory*, vol. 8, no. 5, pp. 293–304, 1962.
- A. D. Wyner and J. Ziv, "A theorem on the entropy of certain binary sequences and applications—Part I," *IEEE Trans. Inf. Theory*, vol. 19, no. 6, pp. 769–772, 1973. (Mrs. Gerber's Lemma.)
- Y. Oohama, "The rate-distortion function for the quadratic Gaussian CEO problem," *IEEE Trans. Inf. Theory*, vol. 44, no. 3, pp. 1057–1070, 1998.
- I. Land, S. Huettinger, P. A. Hoeher, and J. B. Huber, "Bounds on information combining," *IEEE Trans. Inf. Theory*, vol. 51, no. 2, pp. 612–619, 2005.
- A. B. Wagner and V. Anantharam, "An improved outer bound for multiterminal source coding," *IEEE Trans. Inf. Theory*, vol. 54, no. 5, pp. 1919–1937, 2008.
- T. A. Courtade and T. Weissman, "Multiterminal source coding under logarithmic loss," *IEEE Trans. Inf. Theory*, vol. 60, no. 1, pp. 740–761, 2014.
- Prior attempts consulted: none (no earlier files in `attempts/ceo-problem-general/`).
