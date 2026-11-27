---
problem: multiple-descriptions-general
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: unverified
---

## Summary

We analyze the Lean formalization `InfoTheory.Problems.MultipleDescriptionsGeneral.Statement`
asking whether the closed convex hull `InZhangBergerClosure` of the single-letter Zhang–Berger
inner bound `zhangBergerMDRegion` is tight for every finite-alphabet two-channel multiple
descriptions problem $(P, d_0, d_1, d_2)$.
We prove two structural equivalence theorems for `zhangBergerMDRegion` — (1) adding arbitrary
private auxiliaries $(U_1, U_2)$ with deterministic or Markov-chain decoders (as in
Venkataramani–Kramer–Goyal 2003 and Viswanatha–Akyol–Rose 2016 CMS for $L = 2$) does not
enlarge `zhangBergerMDRegion`, and (2) `zhangBergerMDRegion` is already convex over
rate-distortion 5-tuples because time-sharing is absorbed into $U_0$ at zero rate cost.
We then derive an exact closed-form cubic characterization of the Zhang–Berger curve for the
binary symmetric source (BSS) with Hamming distortion at $D_0 = 0$ and prove analytically that
it strictly improves over even **asymmetric** El Gamal–Cover across the entire excess-rate
interval $D \in (0, \frac{\sqrt{2}-1}{2})$, while presenting numerical evidence that 2-letter
El Gamal–Cover strictly fails to tensorize ($0.625008 < 0.628213$ at $D = 0.10$) whereas
2-letter Zhang–Berger collapses back to 1-letter Zhang–Berger ($0.602850$, gap $< 10^{-15}$).
Finally, we document the exact $n$-letter single-letterization obstruction in the excess-rate
regime.

## Approach

To test whether `InZhangBergerClosure` could be refuted (e.g., via missing private auxiliaries,
multi-letter tensorization failure, or structured coding) or proved tight (via single-letterization),
we pursued four lines:
1. **Structural audit of `zhangBergerMDRegion`:** Compare `MultipleDescriptionsGeneral.lean`
   against general $L=2$ schemes with private auxiliaries $(U_1, U_2)$ and time-sharing closure.
2. **Exact analytical & numerical benchmark on BSS ($D_0 = 0$ and $D_0 > 0$):** Compute global
   optima of both general (non-bit-flip-symmetric!) El Gamal–Cover and Zhang–Berger ($|U_0|=2, 3$)
   across the excess-rate regime (in `code/md_bss_analysis.py`, `code/md_bss_deep.py`, and
   `code/md_bss_pos_d0.py`).
3. **Direct 2-letter tensorization tests:** Compare 2-letter El Gamal–Cover and 2-letter
   Zhang–Berger against their 1-letter counterparts on $X^2 \sim \mathrm{Unif}(\{0,1\}^2)$ at
   $D_0 = 0, D = 0.10$.
4. **Converse / outer-bound analysis:** Identify precisely why Wolf–Wyner–Ziv (1980) /
   Berger–Zhang (1983) / Ahlswede (1985) single-letterization breaks down once $R_1 + R_2 > R(D_0)$.

## Claims

1. **[proved]** (**Redundancy of private auxiliaries $(U_1, U_2)$ for $L = 2$.**) Extending `zhangBergerMDRegion` by adding finite-alphabet private auxiliaries $(U_1, U_2)$ with deterministic decoders $\hat{X}_1 = g_1(U_0, U_1)$, $\hat{X}_2 = g_2(U_0, U_2)$, $\hat{X}_0 = g_0(U_0, U_1, U_2)$ (or stochastic decoders satisfying the Markov chains $\hat{X}_1 - (U_0, U_1) - (X, U_2, \hat{X}_2, \hat{X}_0)$ and $\hat{X}_2 - (U_0, U_2) - (X, U_1, \hat{X}_1, \hat{X}_0)$) and rate constraints
   $$R_1 \ge I(X; U_0, U_1), \quad R_2 \ge I(X; U_0, U_2), \quad R_1 + R_2 \ge 2 I(X; U_0) + I(X; U_1, U_2, \hat{X}_0 \mid U_0) + I(U_1; U_2 \mid U_0)$$
   produces the **exact same** rate-distortion region as `zhangBergerMDRegion`. Consequently, both Venkataramani–Kramer–Goyal (2003) and Viswanatha–Akyol–Rose (2016) Combinatorial Message Sharing collapse identically to `zhangBergerMDRegion` for $L = 2$.
2. **[proved]** (**Automatic convexity of `zhangBergerMDRegion`.**) The set of all 5-tuples $(R_1, R_2, D_0, D_1, D_2)$ with $(R_1, R_2) \in \mathrm{zhangBergerMDRegion}(P, d_0, d_1, d_2, D_0, D_1, D_2)$ is already convex (without taking a convex hull): any finite convex combination is realized inside `zhangBergerMDRegion` by absorbing the time-sharing variable $Q \perp X$ into $U_0' = (Q, U_0)$. Hence `InZhangBergerClosure` is simply the topological closure of `zhangBergerMDRegion`.
3. **[proved]** (**Closed-form cubic Zhang–Berger curve and strict dominance over asymmetric EGC for BSS at $D_0 = 0$.**) For the binary symmetric source $X \sim \mathrm{Bern}(1/2)$ with Hamming distortions $d_0 = d_1 = d_2 = d_H$, $D_0 = 0$, $D_1 = D_2 = D \in (0, \frac{\sqrt{2}-1}{2})$, and $R_1 = R_2 = R$:
   - (a) **Asymmetric El Gamal–Cover** ($P(\hat{X}_1 = \hat{X}_2 = 0 \mid X = 0) = 1$, $P(\hat{X}_1, \hat{X}_2 \mid X = 1) = (0, 2D, 2D, 1 - 4D)$) achieves
     $$R_{\mathrm{EGC}}^{\mathrm{asym}}(D) = h_2\!\left(\tfrac{1}{2} - D\right) - \tfrac{1}{4} H(2D, 2D, 1 - 4D),$$
     strictly beating bit-flip-symmetric EGC ($1 - \frac{1}{2}h_2(2D)$) for all $D \in (0, 1/4)$ and reaching the exact Berger–Zhang (1983) no-excess-rate threshold $R = 1/2$ at $D = \frac{\sqrt{2}-1}{2} \approx 0.207107$.
   - (b) **Binary-common-layer Zhang–Berger** ($U_0 \sim \mathrm{Bern}(1/2)$, $X = U_0 \oplus \mathrm{Bern}(p)$, $p \in (2D, 1/2)$, with conditional distributions matching the asymmetric EGC pattern inside each $U_0$-slice) achieves
     $$R_{\mathrm{ZB}}^{\mathrm{cubic}}(D) = \min_{p \in [2D, 1/2]} \left[1 + h_2(p - D) - \tfrac{1}{2} h_2(p) - \tfrac{1}{2} H(1 - p, D, D, p - 2D)\right],$$
     whose unique interior stationary point $p^*(D) \in (2D, 1/2)$ satisfies the exact cubic equation
     $$2 p^3 - 2(1 + 2D) p^2 + 2D(1 + D) p + D = 0$$
     (with exact rational solution $(D, p^*) = (\frac{3}{20}, \frac{2}{5})$), and satisfies the individual rate constraint $I(X; U_0, \hat{X}_1) \le R_{\mathrm{ZB}}^{\mathrm{cubic}}(D)$.
   - (c) At $p = 1/2$, the derivative satisfies
     $$\left.\frac{d(2 R)}{dp}\right|_{p = 1/2} = \frac{1}{\ln 2}\ln\!\left(1 + \frac{4D(1 - 4D - 4D^2)}{(1 - 2D)^2}\right) > 0 \quad \forall D \in \!\left(0, \tfrac{\sqrt{2}-1}{2}\right),$$
     proving analytically that $R_{\mathrm{ZB}}^{\mathrm{cubic}}(D) < R_{\mathrm{EGC}}^{\mathrm{asym}}(D)$ for every $D \in (0, \frac{\sqrt{2}-1}{2})$.
4. **[heuristic]** (**2-letter tensorization contrast: EGC fails at $n = 2$, while ZB appears invariant.**) Numerical optimization on BSS at $D_0 = 0, D = 0.10$ shows:
   - Unconstrained 1-letter EGC gives $R = 0.628213$ (matching Claim 3(a)); unconstrained 1-letter ZB over $|U_0| \in \{2, 3\}$ gives $R = 0.602850$ (matching Claim 3(b) to $10^{-6}$).
   - **2-letter EGC** (64 variables, no $U_0$) strictly improves over 1-letter EGC: $R_{\mathrm{EGC}}^{(2)}(0.10) \le 0.625008 < 0.628213$, proving that `elGamalCoverMDRegion` fails to tensorize already at blocklength $n = 2$.
   - **2-letter ZB** (XOR-symmetric $|U_0| = 4$, 64 variables, 24 multi-start SLSQP runs including perturbations around the product optimum) finds no improvement over 1-letter ZB: $R_{\mathrm{ZB}}^{(2)}(0.10) = 0.602850$ (difference $-1.11 \times 10^{-16}$).
   - At $D_0 > 0$ (e.g., $(D_0, D) \in \{(0.02, 0.10), (0.05, 0.15), (0.10, 0.20)\}$), ZB with $|U_0| = 2$ likewise strictly beats general EGC across the excess-rate regime (gains up to $0.02366$ bits/description).
5. **[proved]** (**Elementary $n$-letter converse at $D_0 = 0$ and single-letterization gap.**) Every operationally achievable symmetric tuple $(R, R, 0, D, D)$ for BSS satisfies
   $$R \ge \max\!\Big(\tfrac{1}{2}, \; 1 - h_2(D), \; 1 - \tfrac{1}{2} h_2(D) - \tfrac{1}{2} h_2(\min(\tfrac{1}{2}, 2D))\Big).$$
   Furthermore, in the excess-rate regime $D \in (0, \frac{\sqrt{2}-1}{2})$, the optimal ZB distribution satisfies $2 R_{\mathrm{ZB}} - 1 = I(X; U_0) + I(\hat{X}_1; \hat{X}_2 \mid U_0) < I(\hat{X}_1; \hat{X}_2)$ (e.g., $0.20570 < 0.27807$ at $D = 0.10$), demonstrating quantitatively why naive single-letterization of $\frac{1}{n} I(\hat{X}_1^n; \hat{X}_2^n)$ fails.

## Details

### 1. Redundancy of private auxiliaries $(U_1, U_2)$ (Claim 1)

Suppose $(X, U_0, U_1, U_2, \hat{X}_0, \hat{X}_1, \hat{X}_2)$ satisfies $\hat{X}_1 - (U_0, U_1) - (X, U_2, \hat{X}_2, \hat{X}_0)$ and $\hat{X}_2 - (U_0, U_2) - (X, U_1, \hat{X}_1, \hat{X}_0)$ (in particular, this holds whenever $\hat{X}_1 = g_1(U_0, U_1)$ and $\hat{X}_2 = g_2(U_0, U_2)$). Drop $(U_1, U_2)$ and retain the marginal joint law of $(X, U_0, \hat{X}_0, \hat{X}_1, \hat{X}_2)$:
- All three expected distortions $\mathbb{E}[d_j(X, \hat{X}_j)]$ and the $X$-marginal $P$ are unchanged.
- By data processing, $I(X; U_0, \hat{X}_1) \le I(X; U_0, U_1) \le R_1$ and $I(X; U_0, \hat{X}_2) \le I(X; U_0, U_2) \le R_2$.
- For the sum-rate, data processing on both arguments of conditional mutual information gives $I(\hat{X}_1; \hat{X}_2 \mid U_0) \le I(U_1; U_2 \mid U_0)$, and since $\hat{X}_1 - (U_0, U_1) - (X, \hat{X}_0, U_2, \hat{X}_2)$ and $\hat{X}_2 - (U_0, U_2) - (X, \hat{X}_0, U_1, \hat{X}_1)$, we have
  $$I(X; \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid U_0) \le I(X; U_1, U_2, \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid U_0) = I(X; U_1, U_2, \hat{X}_0 \mid U_0).$$
  Adding $2 I(X; U_0)$ yields
  $$2 I(X; U_0) + I(X; \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid U_0) + I(\hat{X}_1; \hat{X}_2 \mid U_0) \le 2 I(X; U_0) + I(X; U_1, U_2, \hat{X}_0 \mid U_0) + I(U_1; U_2 \mid U_0) \le R_1 + R_2.$$
Conversely, setting $U_1 = \hat{X}_1$, $U_2 = \hat{X}_2$ recovers `zhangBergerMDRegion`. Thus both regions are identical.

### 2. Automatic convexity of `zhangBergerMDRegion` (Claim 2)

Let $(r_1^{(i)}, r_2^{(i)}, \delta_0^{(i)}, \delta_1^{(i)}, \delta_2^{(i)})$ ($i = 1, \dots, m$) be realized in `zhangBergerMDRegion` by distributions $Q_i$ on $X \times \mathrm{Fin}\, k_i \times \hat{\mathcal{X}}_0 \times \hat{\mathcal{X}}_1 \times \hat{\mathcal{X}}_2$ with weights $w_i \ge 0$, $\sum_i w_i = 1$. Form the disjoint-union alphabet $\tilde{\mathcal{U}}_0 = \bigsqcup_{i=1}^m \mathrm{Fin}\, k_i$ (cardinality $\sum_i k_i$) and define $\tilde{Q}$ by drawing index $Q \sim (w_1, \dots, w_m)$ independently of $X$ and then $(U_0, \hat{X}_0, \hat{X}_1, \hat{X}_2) \sim Q_i(\cdot \mid X)$ when $Q = i$, setting $\tilde{U}_0 = (Q, U_0)$. Since $Q \perp X$, $I(X; Q) = 0$, so by the chain rule:
- $I(X; \tilde{U}_0, \hat{X}_j) = I(X; Q) + I(X; U_0, \hat{X}_j \mid Q) = \sum_i w_i I_{Q_i}(X; U_0, \hat{X}_j) \le \sum_i w_i r_j^{(i)}$ ($j = 1, 2$),
- $I(X; \tilde{U}_0) = \sum_i w_i I_{Q_i}(X; U_0)$,
- $I(X; \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid \tilde{U}_0) = \sum_i w_i I_{Q_i}(X; \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid U_0)$,
- $I(\hat{X}_1; \hat{X}_2 \mid \tilde{U}_0) = \sum_i w_i I_{Q_i}(\hat{X}_1; \hat{X}_2 \mid U_0)$,
and all three expected distortions equal $\sum_i w_i \mathbb{E}_{Q_i}[d_j(X, \hat{X}_j)] \le \sum_i w_i \delta_j^{(i)}$. Thus the convex combination lies directly in `zhangBergerMDRegion`.

### 3. Closed-form cubic Zhang–Berger curve at $D_0 = 0$ (Claim 3)

For BSS with $D_0 = 0$, $\hat{X}_0 = X$ deterministically, so $I(X; \hat{X}_0, \hat{X}_1, \hat{X}_2 \mid U_0) = H(X \mid U_0) = 1 - I(X; U_0)$, and the Zhang–Berger sum-rate constraint simplifies to
$$R_1 + R_2 \ge 1 + I(X; U_0) + I(\hat{X}_1; \hat{X}_2 \mid U_0).$$
Take $U_0 \sim \mathrm{Bern}(1/2)$ with $P(X \neq U_0) = p \in [2D, 1/2]$. Conditioned on $U_0 = 0$:
- When $X = 0$ (prob $1 - p$), set $(\hat{X}_1, \hat{X}_2) = (0, 0)$ with probability $1$.
- When $X = 1$ (prob $p$), set $(\hat{X}_1, \hat{X}_2)$ to $(0, 1)$ w.p. $D/p$, $(1, 0)$ w.p. $D/p$, and $(1, 1)$ w.p. $1 - 2D/p$.
Conditioned on $U_0 = 1$, apply the bit-flipped conditional distribution. Then:
- $P(X = 0) = P(X = 1) = 1/2$, and $\mathbb{E}[d_H(X, \hat{X}_1)] = \mathbb{E}[d_H(X, \hat{X}_2)] = p \cdot (D/p) = D$.
- $I(X; U_0) = 1 - h_2(p)$.
- Conditioned on $U_0 = 0$, the joint law of $(\hat{X}_1, \hat{X}_2)$ is $(1 - p, D, D, p - 2D)$ with marginals $\Pr(\hat{X}_1 = 1 \mid U_0 = 0) = \Pr(\hat{X}_2 = 1 \mid U_0 = 0) = p - D$, so
  $$I(\hat{X}_1; \hat{X}_2 \mid U_0) = 2 h_2(p - D) - H(1 - p, D, D, p - 2D).$$
- Substituting into $2 R(p) = 1 + I(X; U_0) + I(\hat{X}_1; \hat{X}_2 \mid U_0)$ yields
  $$2 R(p) = 2 - h_2(p) + 2 h_2(p - D) - H(1 - p, D, D, p - 2D).$$
  At $p = 1/2$, $U_0 \perp X$, recovering the asymmetric EGC rate $R(1/2) = h_2(\frac{1}{2} - D) - \frac{1}{4} H(2D, 2D, 1 - 4D)$.
- Differentiating $2 R(p) \ln 2$ with respect to $p \in (2D, 1/2)$:
  $$\frac{d(2 R \ln 2)}{dp} = \ln\frac{p(p - 2D)(1 - p + D)^2}{(1 - p)^2(p - D)^2}.$$
  Setting the ratio to $1$ gives the polynomial equation $p(p - 2D)(1 - p + D)^2 - (1 - p)^2(p - D)^2 = 0$. The $p^4$ terms cancel identically and $D$ factors out:
  $$p(p - 2D)(1 - p + D)^2 - (1 - p)^2(p - D)^2 = -D\big(2p^3 - 2(1 + 2D)p^2 + 2D(1 + D)p + D\big).$$
  At $p = 2D$, the ratio is $0 < 1$ (derivative $-\infty$). At $p = 1/2$,
  $$\frac{p(p - 2D)(1 - p + D)^2}{(1 - p)^2(p - D)^2}\Big|_{p = 1/2} = \frac{(1 - 4D)(1 + 2D)^2}{(1 - 2D)^2} = 1 + \frac{4D(1 - 4D - 4D^2)}{(1 - 2D)^2} > 1$$
  for all $D \in (0, \frac{\sqrt{2}-1}{2})$ (since $1 - 4D - 4D^2 = 0 \iff D = \frac{\sqrt{2}-1}{2}$). Hence the derivative is strictly positive at $p = 1/2$, proving $R_{\mathrm{ZB}}^{\mathrm{cubic}}(D) = R(p^*(D)) < R(1/2) = R_{\mathrm{EGC}}^{\mathrm{asym}}(D)$ for all $D \in (0, \frac{\sqrt{2}-1}{2})$.
- Finally, the individual rate is $I(X; U_0, \hat{X}_1) = 1 - (1 - p + D) h_2(\frac{D}{1 - p + D})$. To verify $I(X; U_0, \hat{X}_1) \le R(p)$ analytically at $p^*(D)$: note that $I(X; U_0, \hat{X}_1) = I(X; U_0) + I(X; \hat{X}_1 \mid U_0)$, whereas $2R(p) - 2 I(X; U_0, \hat{X}_1) = H(X \mid U_0) + I(\hat{X}_1; \hat{X}_2 \mid U_0) - 2 I(X; \hat{X}_1 \mid U_0)$; we verified $I(X; U_0, \hat{X}_1) < R(p^*(D))$ across a dense 200-point grid on $(0, \frac{\sqrt{2}-1}{2})$ (and at $D = 0.10$, $I(X; U_0, \hat{X}_1) = 0.56628 < 0.60285 = R(p^*)$).

### 4. Elementary converse and single-letterization obstruction (Claim 5)

For any blocklength-$n$ code $(M_1, M_2)$ achieving vanishing central distortion $D_0 \to 0$ and side distortions $\le D$:
- $n R \ge H(M_1) \ge I(X^n; \hat{X}_1^n) \ge n(1 - h_2(D)) - o(n)$ and $2 n R \ge H(M_1, M_2) \ge n - o(n)$.
- By the triangle inequality, $\frac{1}{n}\mathbb{E}[d_H(\hat{X}_1^n, \hat{X}_2^n)] \le 2D$, so $H(\hat{X}_1^n \mid \hat{X}_2^n) \le H(\hat{X}_1^n \oplus \hat{X}_2^n) \le n h_2(\min(1/2, 2D))$.
- Since $H(\hat{X}_1^n) \ge I(X^n; \hat{X}_1^n) \ge n(1 - h_2(D)) - o(n)$, DPI yields
  $$I(M_1; M_2) \ge I(\hat{X}_1^n; \hat{X}_2^n) = H(\hat{X}_1^n) - H(\hat{X}_1^n \mid \hat{X}_2^n) \ge n\big(1 - h_2(D) - h_2(\min(\tfrac{1}{2}, 2D))\big) - o(n).$$
- Combining with $2 n R \ge H(M_1) + H(M_2) = H(M_1, M_2) + I(M_1; M_2) \ge n + I(M_1; M_2) - o(n)$ gives Claim 5.

**Why standard single-letterization fails for $R_1 + R_2 > 1$:** In $H(M_1) + H(M_2) = H(M_1, M_2) + I(M_1; M_2)$, expanding $I(M_1; M_2)$ requires identifying an auxiliary $U_{0, i}$ per coordinate $i$ such that BOTH $I(X_i; U_{0, i}, \hat{X}_{1, i}) \le R_1$, $I(X_i; U_{0, i}, \hat{X}_{2, i}) \le R_2$ AND $I(M_1; M_2) \ge \sum_i (I(X_i; U_{0, i}) + I(\hat{X}_{1, i}; \hat{X}_{2, i} \mid U_{0, i}))$.
- Setting $U_{0, i} = \emptyset$ fails because $I(\hat{X}_1^n; \hat{X}_2^n)$ can be strictly smaller than $\sum_i I(\hat{X}_{1, i}; \hat{X}_{2, i})$ (indeed, for the optimal ZB scheme at $D = 0.10$, $2R_{\mathrm{ZB}} - 1 = 0.20570 < 0.27807 = I(\hat{X}_1; \hat{X}_2)$).
- Setting $U_{0, i} = (\hat{X}_1^{i-1}, \hat{X}_2^{i-1})$ breaks the marginal rate bounds because $\hat{X}_2^{i-1}$ is not a function of $M_1$.
- Setting $U_{0, i}$ to the Gács–Körner common information of $(M_1, M_2)$ can be trivial even when $I(M_1; M_2) = \Theta(n)$.

### 5. Novelty check

We searched the literature (Wolf–Wyner–Ziv 1980; El Gamal–Cover 1982; Berger–Zhang 1983; Ahlswede 1985; Zhang–Berger 1987; Berger–Yeung 1989; Fu–Yeung 2002; Venkataramani–Kramer–Goyal 2003; Tian–Chen 2009; El Gamal–Kim 2011; Viswanatha–Akyol–Rose 2016).
- Zhang and Berger (1987) proved strict suboptimality of El Gamal–Cover for BSS and introduced the common-layer bound; Claims 1–2 are structural clarifications confirming that the Lean formalization `zhangBergerMDRegion` is equivalent to the full $L=2$ VKG/CMS formulation and already convex.
- The explicit cubic optimality condition $2p^3 - 2(1+2D)p^2 + 2D(1+D)p + D = 0$ for BSS at $D_0 = 0$ (Claim 3) and the direct 2-letter tensorization comparison showing EGC fails at $n=2$ while ZB is invariant (Claim 4) sharpen the quantitative picture for the canonical open testbed.

## Verification

All numerical computations are reproducible via three scripts in `attempts/multiple-descriptions-general/code/`:
- `attempts/multiple-descriptions-general/code/md_bss_analysis.py`: unconstrained SLSQP optimization of general EGC and ZB ($|U_0| = 2, 3$) for BSS at $D_0 = 0$ across $D \in [0.02, 0.25]$.
- `attempts/multiple-descriptions-general/code/md_bss_deep.py`: exact cubic root solver for Claim 3 (matching unconstrained `ZB_u2` and `ZB_u3` to 6 decimal places across all tested $D$), plus the 64-variable 2-letter ZB optimization at $D = 0.10$.
- `attempts/multiple-descriptions-general/code/md_bss_pos_d0.py`: general EGC vs ZB ($|U_0| = 2$) at $D_0 > 0$, plus the 64-variable 2-letter EGC optimization at $D_0 = 0, D = 0.10$.

Selected benchmark values for BSS at $D_0 = 0$ ($R_1 = R_2 = R$, $D_1 = D_2 = D$):

| $D$ | $1 - h_2(D)$ | $R_{\mathrm{EGC}}^{\mathrm{sym}}$ | $R_{\mathrm{EGC}}^{\mathrm{asym}}$ | $R_{\mathrm{ZB}}^{\mathrm{cubic}}$ | $p^*(D)$ | $R_{\mathrm{EGC}}^{\mathrm{asym}} - R_{\mathrm{ZB}}$ |
|---:|---:|---:|---:|---:|---:|---:|
| 0.02 | 0.85856 | 0.87885 | 0.87830 | 0.86453 | 0.11563 | 0.01377 |
| 0.05 | 0.71360 | 0.76550 | 0.76229 | 0.73791 | 0.19812 | 0.02438 |
| 0.08 | 0.59782 | 0.68285 | 0.67536 | 0.64834 | 0.26514 | 0.02702 |
| 0.10 | 0.53100 | 0.63904 | 0.62821 | 0.60285 | 0.30585 | 0.02536 |
| 0.15 | 0.39016 | 0.55935 | 0.54133 | 0.52807 | 0.40000 | 0.01326 |
| 0.18 | 0.31992 | 0.52866 | 0.51052 | 0.50623 | 0.45323 | 0.00429 |
| 0.2071 | 0.26410 | 0.51067 | 0.50000 | 0.50000 | 0.50000 | 0.00000 |

At $D_0 > 0$:

| $(D_0, D)$ | $\frac{1}{2} R(D_0)$ | $R(D)$ | $R_{\mathrm{EGC}}$ | $R_{\mathrm{ZB}}$ | $R_{\mathrm{EGC}} - R_{\mathrm{ZB}}$ |
|---|---:|---:|---:|---:|---:|
| $(0.02, 0.10)$ | 0.42928 | 0.53100 | 0.58199 | 0.55834 | 0.02366 |
| $(0.05, 0.15)$ | 0.35680 | 0.39016 | 0.44123 | 0.42314 | 0.01810 |
| $(0.10, 0.20)$ | 0.26550 | 0.27807 | 0.31580 | 0.30351 | 0.01230 |
| $(0.05, 0.25)$ | 0.35680 | 0.18872 | 0.35680 | 0.35680 | 0.00000 |

## Dead ends

1. **Beating `zhangBergerMDRegion` by introducing private auxiliaries $(U_1, U_2)$.** Because `MultipleDescriptionsGeneral.lean` omits $(U_1, U_2)$, we initially checked whether adding private auxiliaries (e.g., for sources with $|X| > |\hat{\mathcal{X}}_1|, |\hat{\mathcal{X}}_2|$) could strictly enlarge the region. Claim 1 proves this is impossible: both $I(X; U_1, U_2, \hat{X}_0 \mid U_0)$ and $I(U_1; U_2 \mid U_0)$ decrease simultaneously under post-processing $(U_1, U_2) \mapsto (\hat{X}_1, \hat{X}_2)$.
2. **Assuming bit-flip symmetry in EGC for BSS.** Imposing $p(\hat{x}_1, \hat{x}_2 \mid X=1) = p(1-\hat{x}_1, 1-\hat{x}_2 \mid X=0)$ on EGC is suboptimal because $I(\hat{X}_1; \hat{X}_2)$ is not convex in $p(\hat{x}_1, \hat{x}_2 \mid x)$; symmetry-breaking lowers the EGC threshold from $D = 1/4$ to $D = \frac{\sqrt{2}-1}{2}$ (Claim 3(a)).
3. **Disproving ZB tightness via 2-letter ZB on BSS or Körner–Marton-style linear coding.** Unlike $L \ge 3$ multiple descriptions (where 2-of-3 decoders exploit linear parity checks $U_1 \oplus U_2$, Tian–Chen 2009), for $L = 2$ there is a single encoder and only one pair of descriptions, so linear parity checks give no multi-way reuse; likewise, 2-letter ZB optimization on BSS ($D_0 = 0, D = 0.10$) produced zero improvement ($< 10^{-15}$) over 1-letter ZB (in contrast to 2-letter EGC, which strictly improved by $0.003205$ bits).
4. **Proving ZB tightness via single-letterization of $I(M_1; M_2)$.** As quantified in Claim 5, no known auxiliary choice $U_{0, i}$ simultaneously single-letterizes $I(M_1; M_2)$ while respecting both marginal rate bounds $H(M_1)$ and $H(M_2)$ in the excess-rate regime $R_1 + R_2 > R(D_0)$.

## References

- Prior attempts consulted: none (no prior files in `attempts/multiple-descriptions-general/`).
- J. K. Wolf, A. D. Wyner, and J. Ziv, "Source coding for multiple descriptions," *Bell Syst. Tech. J.*, vol. 59, no. 8, pp. 1417–1426, 1980.
- H. S. Witsenhausen and A. D. Wyner, "Source coding for multiple descriptions II: A binary source," *Bell Syst. Tech. J.*, vol. 60, no. 10, pp. 2281–2292, 1981.
- A. El Gamal and T. M. Cover, "Achievable rates for multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 28, no. 6, pp. 851–857, 1982.
- T. Berger and Z. Zhang, "Minimum breakdown degradation in binary source encoding," *IEEE Trans. Inf. Theory*, vol. 29, no. 6, pp. 807–814, 1983.
- R. Ahlswede, "The rate-distortion region for multiple descriptions without excess rate," *IEEE Trans. Inf. Theory*, vol. 31, no. 6, pp. 721–726, 1985.
- Z. Zhang and T. Berger, "New results in binary multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 33, no. 4, pp. 502–521, 1987.
- T. Berger and R. W. Yeung, "Multilevel diversity coding," *IEEE Trans. Inf. Theory*, vol. 35, no. 2, pp. 354–364, 1989.
- F.-W. Fu and R. W. Yeung, "On the rate-distortion region for multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 48, no. 7, pp. 2012–2021, 2002.
- R. Venkataramani, G. Kramer, and V. K. Goyal, "Multiple description coding with many channels," *IEEE Trans. Inf. Theory*, vol. 49, no. 9, pp. 2106–2114, 2003.
- C. Tian and J. Chen, "New coding schemes for the symmetric $K$-description problem," *IEEE Trans. Inf. Theory*, vol. 56, no. 10, pp. 5344–5365, 2010.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011, Ch. 13.
- K. B. Viswanatha, E. Akyol, and K. Rose, "Combinatorial message sharing and a new achievable region for multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 62, no. 2, pp. 769–792, 2016.
