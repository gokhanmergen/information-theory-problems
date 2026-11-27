---
problem: gray-wyner-lossy
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: unverified
---

## Summary

We **disprove the frozen formal statement** `InfoTheory.Problems.GrayWynerLossy.Statement` (and the matching formula in `problems/gray-wyner-lossy.md`) via an elementary 4-state **degraded, lossless** counterexample ($X_1 = X_2 \sim \mathrm{Bern}(1/2)$, $Z_1 = \mathrm{BEC}(1/2)(X)$, $Z_2 = \emptyset$, $D_1 = D_2 = 0$, at $(R_0, R_1, R_2) = (1/2, 0, 1/2)$), together with a full lossy family $(D_1, D_2) = (eD, D)$ for all $e \in (0, 1)$ and $D \in [0, 1/2)$. This refutation does **not** resolve the genuine open mathematical question (tightness for non-degraded lossy side information); rather, it uncovers a **modeling/catalog error** in `lossyGWSIInner`, which forces the common link $R_0$ alone to carry $r_{00} \ge \max(I(X_1, X_2; U_0 \mid Z_1), I(X_1, X_2; U_0 \mid Z_2))$ and forbids the private links $R_1, R_2$ from supplying incremental bin indices for $U_0$ — contradicting the problem file's own claim that `lossyGWSIInner` reproduces the known degraded and lossless regions. We derive the corrected split-binning inner bound (and its exact Fourier–Motzkin projection), update the literature survey (noting bibliographic discrepancies in `problems/gray-wyner-lossy.md`), and numerically benchmark the genuine open $R_1 = R_2 = 0$ non-degraded 2-decoder Heegard–Berger case on an incomparable $\mathrm{BEC}(0.45)$ vs. $\mathrm{BSC}(0.11)$ side-information pair.

## Approach

1. **Structural audit of `lossyGWSIInner` vs. operational Gray–Wyner + side-information coding**: We checked whether the rate-splitting constraints in `lean/InfoTheory/Problems/GrayWynerLossy.lean` (lines 48–63) actually recover the known lossless Slepian–Wolf and degraded Gray–Wyner regions claimed in `problems/gray-wyner-lossy.md`. Separating the common-rate variable $r_{00}$ from the private rates $R_1, R_2$ immediately revealed that whenever $I(X; U_0 \mid Z_1) < I(X; U_0 \mid Z_2)$, `lossyGWSIInner` cannot exploit $M_2$ to help Decoder 2 decode $U_0$.
2. **Separating hyperplane for `InLossyGWSIClosure`**: For $Z_1 = \mathrm{BEC}(e)(X)$ and $Z_2 = \emptyset$, the erasure symmetry forces the exact identity $I(X; U_0 \mid Z_1) = e\, I(X; U_0 \mid Z_2)$ for *every* Markov auxiliary $U_0 - X - Z_1$. Weighting the three inequalities of `lossyGWSIInner` by $(1+e, 1, 1)$ cancels $I(X; U_0)$ identically and produces a convex distortion-dependent lower bound on $(1+e)R_0 + R_1 + R_2$ that survives convex combinations and closure (`InLossyGWSIClosure`), yet is strictly violated by elementary Slepian–Wolf / random binning.
3. **Corrected inner bound and genuine open regime ($R_1 = R_2 = 0$)**: After correcting the rate-splitting constraints to allow private-link bin indices for $U_0$, we verified via Fourier–Motzkin elimination that the corrected region recovers the lossless and degraded benchmarks and collapses at $R_1 = R_2 = 0$ to the classical 2-decoder Heegard–Berger inner bound. We then surveyed the post-1985 literature (Heegard–Berger 1985, Kaspi 1994, Timo–Chan–Grant 2011, Timo–Grant–Kramer 2013, Watanabe 2013, Timo–Oechtering–Wigger 2014, Benammar–Zaidi 2017/2018) and ran numerical optimizations on a non-degraded, non-less-noisy $\mathrm{BEC}(e)$ vs. $\mathrm{BSC}(p)$ benchmark.

## Claims

1. **[proved]** (**Disproof of the frozen `InfoTheory.Problems.GrayWynerLossy.Statement` — catalog modeling error**.) Let $X_1 = X_2 = X \sim \mathrm{Bern}(1/2)$ on $\mathrm{Fin}\,2$, let $Z_1 \in \mathrm{Fin}\,3$ be the output of $\mathrm{BEC}(e)$ applied to $X$ ($Z_1 = X$ w.p. $1 - e$ and $Z_1 = 2$ w.p. $e$, for any $e \in (0, 1)$), let $Z_2 \in \mathrm{Fin}\,1$ be constant (no side information), and let $d_1 = d_2$ be Hamming distortion on $\mathrm{Fin}\,2 \times \mathrm{Fin}\,2$. Then for $(R_0, R_1, R_2, D_1, D_2) = (e, 0, 1 - e, 0, 0)$ (in particular $(1/2, 0, 1/2, 0, 0)$ at $e = 1/2$):
   - `IsLossyGWSIAchievable P d₁ d₂ e 0 (1 - e) 0 0` holds, whereas
   - `InLossyGWSIClosure P d₁ d₂ e 0 (1 - e) 0 0` is **false** (separated by an exact gap of $e(1 - e) > 0$, maximized at $1/4$ bit for $e = 1/2$, on the linear functional $(1 + e)R_0 + R_1 + R_2$).
   Hence `¬ InfoTheory.Problems.GrayWynerLossy.Statement`.

2. **[proved]** (**Lossy extension of the counterexample**.) For the same $\mathrm{BEC}(e)$ degraded source and every $D \in [0, 1/2)$, setting $(D_1, D_2) = (eD, D)$, every tuple in `InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ (eD) D` satisfies
   $$(1 + e) R_0 + R_1 + R_2 \ge (1 + e)\big(1 - h(D)\big),$$
   whereas the rate triple $(R_0, R_1, R_2) = \big(e(1 - h(D)),\, 0,\, (1 - e)(1 - h(D))\big)$ is operationally achievable (via a single Wyner–Ziv/Shannon test channel $U_0 = X \oplus E$ with $E \sim \mathrm{Bern}(D)$ whose bin index is split across $M_0$ and $M_2$) and attains $(1 + e)R_0 + R_1 + R_2 = (1 + e^2)(1 - h(D))$, leaving a strict gap of $e(1 - e)(1 - h(D)) > 0$.

3. **[proved]** (**Corrected split-binning inner bound and Fourier–Motzkin equivalence**.) Replacing the common-link-only constraint $r_{00} \ge \max(a_1, a_2)$ in `lossyGWSIInner` by splitting $U_0$'s bin indices across $(M_0, M_1, M_2)$ — i.e., $R_0 = r_{00} + r_{01} + r_{02}$, $R_1 = r_{10} + r_{11}$, $R_2 = r_{20} + r_{22}$ (all $\ge 0$) with $r_{00} + r_{10} \ge a_1$, $r_{00} + r_{20} \ge a_2$, $r_{01} + r_{11} \ge b_1$, $r_{02} + r_{22} \ge b_2$ where $a_j = I(X_1, X_2; U_0 \mid Z_j)$ and $b_j = I(X_1, X_2; U_j \mid U_0, Z_j)$ — eliminates cleanly to the polytope
   $$R_0, R_1, R_2 \ge 0,\qquad R_0 + R_1 \ge a_1 + b_1,\qquad R_0 + R_2 \ge a_2 + b_2,\qquad R_0 + R_1 + R_2 \ge \max(a_1, a_2) + b_1 + b_2.$$
   This corrected inner bound recovers the exact lossless Gray–Wyner + side-information region (for $X_1 = X_2 = X$, arbitrary $(Z_1, Z_2)$), achieves the $\mathrm{BEC}(e)$ lossless and lossy points of Claims 1–2, recovers Gray–Wyner (1974) when $Z_1 = Z_2 = \emptyset$, and reduces at $R_1 = R_2 = 0$ to the classical 2-decoder Heegard–Berger inner bound.

4. **[proved]** (**Literature & bibliographic audit of `problems/gray-wyner-lossy.md`**.) Our literature check (see Novelty Check & References) clarifies four points relative to `problems/gray-wyner-lossy.md`:
   - The problem statement's claim that `lossyGWSIInner` matches the degraded and lossless regions is refuted by Claim 1.
   - The paper cited as S. Watanabe (2013) *"The rate-distortion region of the Gray–Wyner system with side information"* conflates two distinct works: S. Watanabe, *"The Rate-Distortion Function for Product of Two Sources With Side-Information at Decoders"* (*IEEE Trans. Inf. Theory*, vol. 59, no. 9, pp. 5678–5691, Sept. 2013, arXiv:1105.2864), and M. Benammar & A. Zaidi, *"Rate-Distortion Region of a Gray–Wyner Model with Side Information"* (arXiv:1701.03612; *Entropy* 2018, solving the Gray–Wyner model with arbitrary side information when one decoder is lossless and the other is lossy).
   - R. Timo, A. Grant, and G. Kramer, *"Lossy broadcasting with complementary side information"*, appeared in *IEEE Trans. Inf. Theory*, **vol. 59, no. 1, pp. 104–131, Jan. 2013** (not vol. 57, 2011). Their 2011 *IEEE Trans. Inf. Theory* paper (vol. 57, no. 8, pp. 5240–5257, by R. Timo, T. Chan, and A. Grant, *"Rate Distortion with Side-Information at Many Decoders"*) disproved Heegard–Berger's 1985 Theorem 2 for multi-decoder setups.
   - Tightness of the 2-decoder Heegard–Berger inner bound ($R_1 = R_2 = 0$) was extended beyond degradedness to **conditionally less noisy** side information by R. Timo, T. J. Oechtering, and M. Wigger (*IEEE Trans. Inf. Theory*, vol. 60, no. 9, pp. 5516–5532, Sept. 2014), while the general non-degraded, non-less-noisy 2-decoder lossy case remains open.

5. **[heuristic]** (**Numerical benchmark on non-degraded, non-less-noisy 2-decoder Heegard–Berger ($R_1 = R_2 = 0$)**.) For $X \sim \mathrm{Bern}(1/2)$ with independent $Z_1 = \mathrm{BEC}(0.45)(X)$ and $Z_2 = \mathrm{BSC}(0.11)(X)$, neither channel is degraded nor less noisy with respect to the other ($2p = 0.22 < 4p(1-p) = 0.3916 < e = 0.45 < h(p) = 0.4999$). Numerical optimization of the 2-decoder Heegard–Berger inner bound $R_{\mathrm{HB}}(D_1, D_2)$ finds a strict gap above $\max(R^{\mathrm{WZ}}_{X \mid Z_1}(D_1), R^{\mathrm{WZ}}_{X \mid Z_2}(D_2))$ (e.g., $R_{\mathrm{HB}}(0.05, 0.05) \approx 0.3162$ vs. $\max\mathrm{WZ} = 0.2653$, gap $+0.0509$ bits), where the optimizer uses a coarse $U_0$ satisfying $I(X; U_0 \mid Z_1) > I(X; U_0 \mid Z_2)$ (reversing the lossless ordering $H(X \mid Z_1) < H(X \mid Z_2)$) plus a private refinement $U_2$ for Decoder 2. This does not establish whether $R_{\mathrm{HB}}$ itself is tight or loose at this point.

## Details

### Proof of Claim 1 (Disproof of `GrayWynerLossy.Statement`)

Fix $e \in (0, 1)$ (for concreteness, $e = 1/2$). Define the finite-alphabet instance on `Fin 2 × Fin 2 × Fin 3 × Fin 1`:
- $P(0, 0, 0, 0) = P(1, 1, 1, 0) = \frac{1-e}{2}$,
- $P(0, 0, 2, 0) = P(1, 1, 2, 0) = \frac{e}{2}$,
- $P(\cdot) = 0$ elsewhere,
and Hamming distortions $d_1(x, \hat x) = d_2(x, \hat x) = \mathbf{1}_{x \neq \hat x}$ on $\mathrm{Fin}\,2 \times \mathrm{Fin}\,2$. Note that $X_1 = X_2 =: X \sim \mathrm{Bern}(1/2)$ a.s., $Z_1 = X$ w.p. $1 - e$ and $Z_1 = 2$ (erasure) w.p. $e$ independently of $X$, and $Z_2 = 0$ is constant.

#### Part A: Proof of `IsLossyGWSIAchievable P d₁ d₂ e 0 (1 - e) 0 0`

Let $\varepsilon > 0$. Set $M_0 = \max(1, \lfloor 2^{n(e + \varepsilon)} \rfloor)$, $M_1 = 1$ (unused), and $M_2 = \max(1, \lfloor 2^{n(1 - e + \varepsilon)} \rfloor)$. For $n$ sufficiently large, $M_0 \ge \frac{1}{2} 2^{n(e + \varepsilon)}$ and $M_0 M_2 \ge \frac{1}{4} 2^{n(1 + 2\varepsilon)}$.

Draw random deterministic encoders $\mathrm{enc}_0 : \{0,1\}^n \to \mathrm{Fin}\,M_0$ and $\mathrm{enc}_2 : \{0,1\}^n \to \mathrm{Fin}\,M_2$ independently and uniformly at random over all functions (equivalently, independent uniform hash/bin indices for each $x^n \in \{0,1\}^n$), and let $\mathrm{enc}_1 \equiv 0$.
- **Decoder 1** on input $(m_0, m_1, z_1^n)$: let $\mathcal{C}(z_1^n) = \{x' \in \{0,1\}^n : \forall i,\, z_{1,i} \neq 2 \implies x'_i = z_{1,i}\}$. If there is a unique $x' \in \mathcal{C}(z_1^n)$ with $\mathrm{enc}_0(x') = m_0$, output $x'$; otherwise output $0^n$.
- **Decoder 2** on input $(m_0, m_2, z_2^n)$: if there is a unique $x' \in \{0,1\}^n$ with $(\mathrm{enc}_0(x'), \mathrm{enc}_2(x')) = (m_0, m_2)$, output $x'$; otherwise output $0^n$.

Compute the expected block error probabilities over the random codebook and the i.i.d. source $(X^n, Z_1^n)$:
1. **Decoder 2**: For any fixed $x^n \in \{0,1\}^n$, an error occurs only if there exists $x' \neq x^n$ with $(\mathrm{enc}_0(x'), \mathrm{enc}_2(x')) = (\mathrm{enc}_0(x^n), \mathrm{enc}_2(x^n))$. By the union bound and independence across distinct $x'$,
   $$\mathbb{E}[\Pr(\hat X_2^n \neq X^n)] \le (2^n - 1) \cdot \frac{1}{M_0 M_2} \le 4 \cdot 2^{-2n\varepsilon}.$$
2. **Decoder 1**: Let $E = |\{i \in \mathrm{Fin}\,n : Z_{1,i} = 2\}| \sim \mathrm{Binomial}(n, e)$. Note $|\mathcal{C}(Z_1^n)| = 2^E$. By Chebyshev's inequality,
   $$\Pr\!\big(E > n(e + \varepsilon/2)\big) \le \frac{e(1-e)}{n(\varepsilon/2)^2} = \frac{4 e(1-e)}{n\varepsilon^2}.$$
   Conditioned on $(X^n, Z_1^n)$ with $E \le n(e + \varepsilon/2)$, a decoding error occurs only if some $x' \in \mathcal{C}(Z_1^n) \setminus \{X^n\}$ satisfies $\mathrm{enc}_0(x') = \mathrm{enc}_0(X^n)$. By the union bound,
   $$\mathbb{E}[\Pr(\hat X_1^n \neq X^n \mid E \le n(e + \varepsilon/2))] \le 2^{n(e + \varepsilon/2)} \cdot \frac{1}{M_0} \le 2 \cdot 2^{-n\varepsilon/2}.$$
   Hence
   $$\mathbb{E}[\mathrm{avg}D_1 + \mathrm{avg}D_2] \le \mathbb{E}[\Pr(\hat X_1^n \neq X^n) + \Pr(\hat X_2^n \neq X^n)] \le \frac{4 e(1-e)}{n\varepsilon^2} + 2 \cdot 2^{-n\varepsilon/2} + 4 \cdot 2^{-2n\varepsilon}.$$
   For all sufficiently large $n$, the right-hand side is $\le \varepsilon$. By the first-moment method, there exists a deterministic encoder/decoder pair $(\mathrm{enc}_0, \mathrm{enc}_1, \mathrm{enc}_2, \mathrm{dec}_1, \mathrm{dec}_2)$ with $\mathrm{avg}D_1 + \mathrm{avg}D_2 \le \varepsilon$, so $\mathrm{avg}D_1 \le \varepsilon$ and $\mathrm{avg}D_2 \le \varepsilon$. Thus `(e, 0, 1 - e, 0, 0)` is operationally achievable. $\square$

*(Remark: The same achievability also follows from the repo's `InfoTheory.Bridge.NetworkIT.slepian_wolf_theorem`, or via a linear code over $\mathbb{F}_2$ whose top $k_0 = \lceil n(e + \varepsilon)\rceil$ rows decode $\mathrm{BEC}(e)$ and whose remaining $n - k_0$ rows are sent on $M_2$, giving zero error at Decoder 2 for every $n$.)*

#### Part B: Proof of `¬ InLossyGWSIClosure P d₁ d₂ e 0 (1 - e) 0 0`

First observe an elementary bound on binary entropy: for all $p \in [0, 1]$,
$$h(p) \le \frac{2}{\ln 2}\sqrt{p} \le 3\sqrt{p}.$$
*Proof:* Trivial at $p \in \{0, 1\}$. For $p \in (0, 1)$, applying $\ln t \le t - 1$ to $t = 1/\sqrt{p}$ and $t = 1/(1-p)$ gives $-p\ln p = 2p\ln(1/\sqrt{p}) \le 2\sqrt{p} - 2p$ and $-(1-p)\ln(1-p) = (1-p)\ln(1/(1-p)) \le p$. Summing gives $h(p)\ln 2 \le 2\sqrt{p} - p \le 2\sqrt{p}$, and $\ln 2 > 2/3$ yields $2/\ln 2 < 3$. (In fact $h(p) \le 2\sqrt{p(1-p)} \le 2\sqrt{p}$ also holds, though $3\sqrt{p}$ suffices with this 2-line proof.)

Now let $(r_0, r_1, r_2) \in \mathrm{lossyGWSIInner}(P, d_1, d_2, \delta_1, \delta_2)$ be any single-letter point witnessed by $(U_0, U_1, U_2, g_1, g_2, r_{00}, r_{01}, r_{02})$ with $Q$ extending $P$ and $I(U_0, U_1, U_2; Z_1, Z_2 \mid X_1, X_2) = 0$. Since $X_1 = X_2 = X$ a.s. and $Z_2$ is constant:
1. **Exact erasure scaling**: Since $(U_0, U_1, U_2) - X - Z_1$, for any subset $V$ of $(U_0, U_1, U_2)$:
   - Given $Z_1 = 0$ (prob. $(1-e)/2$), $X = 0$ a.s., so $I(X; V \mid Z_1 = 0) = 0$. Similarly $I(X; V \mid Z_1 = 1) = 0$.
   - Given $Z_1 = 2$ (prob. $e$), the event $\{Z_1 = 2\}$ is independent of $X$ and (by the Markov chain) independent of $(X, V)$, so the conditional joint law of $(X, V)$ given $Z_1 = 2$ equals its unconditional joint law.
   Therefore,
   $$I(X; V \mid Z_1) = e \cdot I(X; V).$$
2. **Common-link constraint**: Letting $a := I(X; U_0) \ge 0$, we have $I(X; U_0 \mid Z_1) = e a$ and $I(X; U_0 \mid Z_2) = a$. Hence
   $$r_{00} \ge \max(ea, a) = a.$$
3. **Decoder 1 constraint**: By the chain rule and Step 1,
   $$r_{01} + r_1 \ge I(X; U_1 \mid U_0, Z_1) = I(X; U_0, U_1 \mid Z_1) - I(X; U_0 \mid Z_1) = e\, I(X; U_0, U_1) - ea.$$
   Let $\hat X_1 := g_1(U_0, U_1, 2)$ and $p_1 := \Pr(X \neq \hat X_1)$. Because $(X, U_0, U_1) \perp \{Z_1 = 2\}$ and $d_1 \ge 0$,
   $$\delta_1 \ge \mathbb{E}[d_1(X, g_1(U_0, U_1, Z_1))] \ge \Pr(Z_1 = 2)\,\mathbb{E}[d_1(X, g_1(U_0, U_1, 2)) \mid Z_1 = 2] = e p_1,$$
   so $p_1 \le \delta_1 / e$ (and $\delta_1 \ge 0$). By DPI and binary Fano's inequality,
   $$I(X; U_0, U_1) \ge I(X; \hat X_1) = 1 - H(X \mid \hat X_1) \ge 1 - h(p_1) \ge 1 - 3\sqrt{p_1} \ge 1 - 3\sqrt{\delta_1 / e}.$$
   (Note: $1 - 3\sqrt{\delta_1 / e} \le 0 \le I(X; U_0, U_1)$ automatically if $\delta_1 / e \ge 1/9$, so no case split on $\delta_1/e \le 1/2$ is needed!)
   Thus
   $$r_{01} + r_1 \ge e - 3\sqrt{e \delta_1} - ea.$$
4. **Decoder 2 constraint**: Since $Z_2$ is constant, letting $\hat X_2 := g_2(U_0, U_2, 0)$ and $p_2 := \Pr(X \neq \hat X_2) \le \delta_2$,
   $$r_{02} + r_2 \ge I(X; U_2 \mid U_0) = I(X; U_0, U_2) - a \ge 1 - h(p_2) - a \ge 1 - 3\sqrt{\delta_2} - a.$$
5. **Linear combination cancelling $a$**: Since $r_0 = r_{00} + r_{01} + r_{02}$ with $r_{00}, r_{01}, r_{02} \ge 0$ and $1 + e \ge 1$,
   $$(1 + e)r_0 + r_1 + r_2 \ge (1 + e)r_{00} + (r_{01} + r_1) + (r_{02} + r_2)$$
   $$\ge (1 + e)a + \big(e - 3\sqrt{e\delta_1} - ea\big) + \big(1 - 3\sqrt{\delta_2} - a\big) = (1 + e) - 3\sqrt{e\delta_1} - 3\sqrt{\delta_2}.$$
6. **Passing to `InLossyGWSIClosure`**: Suppose `InLossyGWSIClosure P d₁ d₂ e 0 (1 - e) 0 0` held. For any $\varepsilon > 0$, pick weights $w_i \ge 0$ ($\sum w_i = 1$) and points $(r_{0,i}, r_{1,i}, r_{2,i}) \in \mathrm{lossyGWSIInner}(P, d_1, d_2, \delta_{1,i}, \delta_{2,i})$ with $\sum w_i r_{0,i} \le e + \varepsilon$, $\sum w_i r_{1,i} \le \varepsilon$, $\sum w_i r_{2,i} \le 1 - e + \varepsilon$, $\sum w_i \delta_{1,i} \le \varepsilon$, $\sum w_i \delta_{2,i} \le \varepsilon$. Averaging Step 5 and applying Jensen's inequality to the concave function $t \mapsto \sqrt{t}$ on $[0, \infty)$ gives
   $$(1 + e)(e + \varepsilon) + \varepsilon + (1 - e + \varepsilon) \ge (1 + e) - 3\sqrt{e\varepsilon} - 3\sqrt{\varepsilon}.$$
   Simplifying the left-hand side to $(1 + e^2) + (3 + e)\varepsilon$ and rearranging yields
   $$(3 + e)\varepsilon + 3(\sqrt{e} + 1)\sqrt{\varepsilon} \ge e(1 - e).$$
   For $e = 1/2$ and $\varepsilon = 10^{-4}$, the LHS is $0.00035 + 3(1 + 1/\sqrt{2})(0.01) < 0.052 < 0.25 = e(1 - e)$, a contradiction. $\square$

### Proof of Claim 2 (Lossy extension)

In Steps 3–4 above, replace the $3\sqrt{p}$ bound by the exact binary rate-distortion function $R_{\mathrm{Bern}}(d) := \max(0, 1 - h(\min(d, 1/2)))$, which is convex and non-increasing on $[0, \infty)$. Then every single-letter point satisfies
$$(1 + e)r_0 + r_1 + r_2 \ge e R_{\mathrm{Bern}}(\delta_1 / e) + R_{\mathrm{Bern}}(\delta_2).$$
By Jensen's inequality and continuity of $R_{\mathrm{Bern}}$, every point in `InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ (eD) D` satisfies $(1 + e)R_0 + R_1 + R_2 \ge (1 + e)(1 - h(D))$.

Conversely, for any $D \in [0, 1/2)$, let $U_0 = X \oplus E$ with $E \sim \mathrm{Bern}(D)$ independent of $(X, Z_1)$. Standard rate-distortion covering covers $X^n$ by a codebook $\mathcal{C}_0$ of $2^{n(1 - h(D) + \varepsilon)}$ codewords $U_0^n$ with average Hamming distortion $\le D + \varepsilon/2$. Assign each codeword $u_0^n \in \mathcal{C}_0$ two independent random bin indices: $M_0 \in [2^{n(e(1-h(D)) + \varepsilon)}]$ and $M_2 \in [2^{n((1-e)(1-h(D)) + \varepsilon)}]$.
- Decoder 2 receives $(M_0, M_2)$ at combined bin rate $1 - h(D) + 2\varepsilon > \frac{1}{n}\log_2 |\mathcal{C}_0|$, recovering $U_0^n$ with vanishing error probability and reconstructing $\hat X_2^n = U_0^n$ at distortion $D$.
- Decoder 1 receives $(M_0, Z_1^n)$ at bin rate $e(1 - h(D)) + \varepsilon > I(X; U_0 \mid Z_1) = e(1 - h(D))$, recovering $U_0^n$ via Wyner–Ziv joint-typicality decoding and reconstructing $\hat X_{1,i} = Z_{1,i}$ when $Z_{1,i} \neq 2$ (distortion $0$) and $\hat X_{1,i} = U_{0,i}$ when $Z_{1,i} = 2$ (distortion $D$), achieving expected distortion $eD$.
Thus $(e(1 - h(D)),\, 0,\, (1 - e)(1 - h(D)))$ is operationally achievable and evaluates to $(1 + e^2)(1 - h(D))$, leaving a gap of $e(1 - e)(1 - h(D)) > 0$. $\square$

### Proof of Claim 3 (Corrected split-binning inner bound and Fourier–Motzkin projection)

In the Gray–Wyner network with side information, the random bin index of $U_0^n$ can be partitioned into three independent pieces: $r_{00}$ bits on $M_0$, $r_{10}$ bits on $M_1$, and $r_{20}$ bits on $M_2$; similarly $U_1^n$ uses $r_{01}$ bits on $M_0$ and $r_{11}$ bits on $M_1$, and $U_2^n$ uses $r_{02}$ bits on $M_0$ and $r_{22}$ bits on $M_2$. Decoding succeeds when:
$$r_{00} + r_{10} \ge a_1,\qquad r_{00} + r_{20} \ge a_2,\qquad r_{01} + r_{11} \ge b_1,\qquad r_{02} + r_{22} \ge b_2,$$
with $R_0 = r_{00} + r_{01} + r_{02}$, $R_1 = r_{10} + r_{11}$, $R_2 = r_{20} + r_{22}$, and all 7 sub-rates nonnegative.

**Necessity**:
- $R_0 + R_1 \ge (r_{00} + r_{10}) + (r_{01} + r_{11}) \ge a_1 + b_1$.
- $R_0 + R_2 \ge (r_{00} + r_{20}) + (r_{02} + r_{22}) \ge a_2 + b_2$.
- $R_0 + R_1 + R_2 = (r_{00} + r_{10}) + (r_{01} + r_{11}) + (r_{02} + r_{22}) + r_{20} \ge a_1 + b_1 + b_2$, and symmetrically $\ge a_2 + b_1 + b_2$, so $R_0 + R_1 + R_2 \ge \max(a_1, a_2) + b_1 + b_2$.

**Sufficiency**: Assume $R_0, R_1, R_2 \ge 0$, $R_0 + R_1 \ge a_1 + b_1$, $R_0 + R_2 \ge a_2 + b_2$, and $R_0 + R_1 + R_2 \ge \max(a_1, a_2) + b_1 + b_2$. W.l.o.g. assume $a_1 \le a_2$. Set:
- $r_{01} = \max(0, b_1 - R_1)$ and $r_{11} = \min(b_1, R_1)$ (so $r_{01} + r_{11} = b_1$ and remaining private rate $R'_1 := R_1 - r_{11} = \max(0, R_1 - b_1)$);
- $r_{02} = \max(0, b_2 - R_2)$ and $r_{22} = \min(b_2, R_2)$ (so $r_{02} + r_{22} = b_2$ and $R'_2 := R_2 - r_{22} = \max(0, R_2 - b_2)$);
- Let $R'_0 := R_0 - r_{01} - r_{02}$. Check $R'_0 \ge 0$:
  - If $R_1 \ge b_1$ and $R_2 \ge b_2$, then $r_{01} = r_{02} = 0$, $R'_0 = R_0 \ge 0$.
  - If $R_1 < b_1$ and $R_2 \ge b_2$, then $R'_0 = R_0 + R_1 - b_1 \ge a_1 \ge 0$.
  - If $R_1 \ge b_1$ and $R_2 < b_2$, then $R'_0 = R_0 + R_2 - b_2 \ge a_2 \ge 0$.
  - If $R_1 < b_1$ and $R_2 < b_2$, then $R'_0 = R_0 + R_1 + R_2 - b_1 - b_2 \ge \max(a_1, a_2) \ge 0$.
- Finally, set $r_{00} = R'_0$, $r_{10} = R'_1$, $r_{20} = R'_2$ (all $\ge 0$):
  - $r_{00} + r_{10} = R_0 + R_1 - b_1 - r_{02}$. If $r_{02} = 0$, this is $R_0 + R_1 - b_1 \ge a_1$. If $r_{02} = b_2 - R_2 > 0$, this is $R_0 + R_1 + R_2 - b_1 - b_2 \ge \max(a_1, a_2) \ge a_1$.
  - Symmetrically, $r_{00} + r_{20} = R_0 + R_2 - b_2 - r_{01} \ge a_2$ in both cases ($r_{01} = 0$ or $r_{01} = b_1 - R_1$).
This proves exact equality of the split-binning LP and the 3-inequality polytope. $\square$

### Novelty Check

- We searched via web queries across Heegard & Berger (1985), Kaspi (1994), Timo–Chan–Grant (2011), Timo–Grant–Kramer (2013), Watanabe (2013), Timo–Oechtering–Wigger (2014), Benammar–Zaidi (2017/2018), and Sefidgaran–Tchamkerten.
- The **counterexample to the frozen statement** (Claims 1–2) is specific to the modeling error in `problems/gray-wyner-lossy.md` / `lean/InfoTheory/Problems/GrayWynerLossy.lean` (forbidding private links from carrying incremental bin bits of $U_0$), and is new relative to the repository (no prior attempts existed in `attempts/gray-wyner-lossy/`).
- The **corrected split-binning scheme** (Claim 3) is standard in the Gray–Wyner + side-information literature (e.g., Benammar–Zaidi 2017/2018; Timo–Oechtering–Wigger 2014). We do **not** claim Claim 3 as a new theorem in information theory; rather, it identifies the exact correction needed for a statement-fix PR on `GrayWynerLossy.lean`.

## Verification

All computations are reproducible via `attempts/gray-wyner-lossy/code/verify_gwsi.py` (run with `.venv/bin/python attempts/gray-wyner-lossy/code/verify_gwsi.py`, NumPy 2.5.1, SciPy 1.18.0):

1. **Part 1 (BEC(1/2) counterexample checks)**:
   - Tested 3,000 random Markov auxiliary distributions $P(u_0, u_1, u_2 \mid x)$ with $k_0 \le 4$, $k_1, k_2 \le 3$ (including sparse Dirichlet draws $\alpha \in \{0.05, 0.2, 1.0, 3.0\}$):
     - $\max |I(X; U_0 \mid Z_1) - \frac{1}{2} I(X; U_0 \mid Z_2)| = 1.998 \times 10^{-15}$,
     - $\min (\frac{3}{2}\max(a_1, a_2) + b_1 + b_2 - [\frac{1}{2} R_{\mathrm{Bern}}(2D_1) + R_{\mathrm{Bern}}(D_2)]) = +4.07 \times 10^{-4} \ge 0$,
     - $\min (\text{LHS} - [1.5 - \sqrt{2 D_1} - 2\sqrt{D_2}]) = +2.86 \times 10^{-2} \ge 0$,
     - $\max_{p \in [0, 1]} (h_2(p) - 2\sqrt{p}) \le 0$ on a $10^5$-point grid.
   - Finite-blocklength $\mathrm{GF}(2)$ linear-code Monte Carlo simulation (400 trials each) confirms operational achievability of $(1/2 + \varepsilon, 0, 1/2 - \varepsilon, 0, 0)$: at $n = 160$, $R_0 = 0.581$, $R_2 = 0.419$, Decoder 2 has $\mathrm{avg}D_2 = 0$ identically and Decoder 1 achieves $\mathrm{avg}D_1 \le 0.0053$.
   - Note: these numerical checks corroborate Claim 1–2; the proofs of Claims 1–2 are purely analytical and do not rely on numerics.
2. **Part 2 (Fourier–Motzkin equivalence)**:
   - Tested 2,000 random tuples $(a_1, a_2, b_1, b_2, R_0, R_1, R_2)$ comparing `scipy.optimize.linprog` feasibility of the 7-variable split-binning LP against the 3-inequality eliminated polytope: **0 mismatches out of 2,000**.
3. **Part 3 (Non-degraded BEC(0.45) vs. BSC(0.11) at $R_1 = R_2 = 0$)**:
   - Structured BSC-test-channel sweep + 5 Nelder–Mead restarts ($k_0 = k_1 = k_2 = 2$) yields:
     - $(D_1, D_2) = (0.00, 0.00)$: $\mathrm{WZ}_1 = 0.4500$, $\mathrm{WZ}_2 = 0.4999$, $R_{\mathrm{HB}} = 0.4999$,
     - $(D_1, D_2) = (0.05, 0.02)$: $\max\mathrm{WZ} = 0.3980$, $R_{\mathrm{HB}} \approx 0.4038$ ($+0.0058$),
     - $(D_1, D_2) = (0.05, 0.05)$: $\max\mathrm{WZ} = 0.2653$, $R_{\mathrm{HB}} \approx 0.3162$ ($+0.0509$; $a_1 = 0.255, a_2 = 0.246, b_1 = 0, b_2 = 0.061$),
     - $(D_1, D_2) = (0.10, 0.03)$: $\max\mathrm{WZ} = 0.3538$, $R_{\mathrm{HB}} \approx 0.3723$ ($+0.0185$),
     - $(D_1, D_2) = (0.10, 0.05)$: $\max\mathrm{WZ} = 0.2653$, $R_{\mathrm{HB}} \approx 0.3016$ ($+0.0362$).
   - Because optimization is non-convex and restricted to $k_0 = k_1 = k_2 = 2$, these values are rigorous *upper bounds* on $R_{\mathrm{HB}}(D_1, D_2)$ and heuristic estimates of its exact value.

## Dead ends

1. **Independent complementary side information ($X_1 \perp X_2$, $Z_1 = X_2$, $Z_2 = X_1$, $R_1 = R_2 = 0$)**: We first attempted to separate `lossyGWSIInner` at $R_1 = R_2 = 0$ by contrasting operational XOR index coding ($M_0 = W_1 \oplus W_2$ achieving $R_0 = \max(R_1(D_1), R_2(D_2))$) against single-letter $U_0$, expecting that asymmetric sources (e.g., lossless binary $X_1$ and lossy quaternary $X_2$ with $R_1(0) = R_2(D_2) = 1$) could not share a single-letter $U_0$. **Obstruction**: Setting $U_0 = (\hat X_1, \hat X_2)$ with independent optimal test channels $\hat X_1 - X_1$ and $\hat X_2 - X_2$ *does* achieve $R_0 = \max(R_1(D_1), R_2(D_2))$ inside `lossyGWSIInner`, because conditioning on $Z_1 = X_2$ kills $\hat X_2$'s contribution: $I(X_1, X_2; \hat X_1, \hat X_2 \mid X_2) = I(X_1; \hat X_1) = R_1(D_1)$, and symmetrically $I(X_1, X_2; \hat X_1, \hat X_2 \mid X_1) = R_2(D_2)$. Thus independent complementary sources cannot separate `lossyGWSIInner` at $R_1 = R_2 = 0$.
2. **Correlating $(U_1, U_2)$ given $(X, U_0)$ (Marton-style mutual covering) at $R_1 = R_2 = 0$**: We checked whether choosing $U_1, U_2$ non-independent given $(X, U_0)$ could strictly improve the 2-decoder Heegard–Berger inner bound. **Obstruction**: In source coding with two separate decoders, the distortion constraints $\mathbb{E}[d_j(X_j, g_j(U_0, U_j, Z_j))] \le D_j$ and the binning savings $I(U_j; Z_j \mid U_0)$ depend only on the marginals $P(x, z_1, u_0, u_1)$ and $P(x, z_2, u_0, u_2)$, never on the joint coupling of $(U_1, U_2)$ given $(X, U_0)$. By the mutual covering lemma, correlating $(U_1, U_2)$ given $(X, U_0)$ adds a nonnegative rate penalty $+I(U_1; U_2 \mid X, U_0) \ge 0$, so $U_1 \perp U_2 \mid (X, U_0)$ is strictly optimal for this coding architecture.
3. **Resolving the *corrected* non-degraded 2-decoder lossy problem ($R_1 = R_2 = 0$)**: For the incomparable $\mathrm{BEC}(0.45)$ vs. $\mathrm{BSC}(0.11)$ pair, we observed a $+0.0509$-bit gap between $R_{\mathrm{HB}}(0.05, 0.05)$ and the individual Wyner–Ziv lower bound $\max(\mathrm{WZ}_1, \mathrm{WZ}_2)$, but we did not obtain either a matching single-letter converse or an operational scheme beating $R_{\mathrm{HB}}$. Closing this gap for general non-degraded $(Z_1, Z_2)$ remains the genuine open problem once the Lean statement is fixed.

## References

- Repository files: `problems/gray-wyner-lossy.md`, `lean/InfoTheory/Problems/GrayWynerLossy.lean` (no prior attempts in `attempts/gray-wyner-lossy/`).
- R. M. Gray and A. D. Wyner, "Source coding for a simple network," *Bell Syst. Tech. J.*, vol. 53, no. 9, pp. 1681–1721, 1974.
- C. Heegard and T. Berger, "Rate distortion when side information may be absent," *IEEE Trans. Inf. Theory*, vol. 31, no. 6, pp. 727–734, 1985.
- A. H. Kaspi, "Rate-distortion function when side-information may be present at the decoder," *IEEE Trans. Inf. Theory*, vol. 40, no. 6, pp. 2031–2034, 1994.
- R. Timo, T. Chan, and A. Grant, "Rate distortion with side-information at many decoders," *IEEE Trans. Inf. Theory*, vol. 57, no. 8, pp. 5240–5257, Aug. 2011 (arXiv:0901.1705).
- R. Timo, A. Grant, and G. Kramer, "Lossy broadcasting with complementary side information," *IEEE Trans. Inf. Theory*, vol. 59, no. 1, pp. 104–131, Jan. 2013.
- S. Watanabe, "The rate-distortion function for product of two sources with side-information at decoders," *IEEE Trans. Inf. Theory*, vol. 59, no. 9, pp. 5678–5691, Sept. 2013 (arXiv:1105.2864).
- R. Timo, T. J. Oechtering, and M. Wigger, "Source coding problems with conditionally less noisy side information," *IEEE Trans. Inf. Theory*, vol. 60, no. 9, pp. 5516–5532, Sept. 2014.
- M. Benammar and A. Zaidi, "Rate-distortion region of a Gray–Wyner model with side information," arXiv:1701.03612, 2017 (*Entropy*, 2018).
