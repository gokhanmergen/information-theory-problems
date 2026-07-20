---
problem: binary-symmetric-z-interference-channel
date: 2026-07-19
attempter: claude
model: claude-fable-5
type: survey
status: community-reviewed
---

## Summary

A computational baseline and independent rederivation for the weak-interference regime $p_1 > p_2$ of the
BS-ZIC ($Y_1 = X_1 \oplus X_2 \oplus N_1$, $Y_2 = X_2 \oplus N_2$), with exact
(enumerated, no sampling) evaluations of treating-interference-as-noise (TIN), time
division, and a Han–Kobayashi (HK) rate-splitting grid at
$(p_1,p_2) \in \{(0.2,0.05), (0.3,0.1), (0.15,0.1)\}$, against outer bounds. While
setting up the outer bound the computation produced a stronger-than-expected
outcome: a short Mrs. Gerber's Lemma (MGL) converse gives the outer curve
$$R_1 \;\leq\; 1 - h\!\big(q \star h^{-1}(h(p_2) + R_2)\big), \qquad
q = \frac{p_1 - p_2}{1 - 2p_2},\quad a \star b = a(1-b)+b(1-a),$$
and this curve **coincides identically with the optimized-bias TIN inner bound**.
The derivation below gives the weak-regime capacity region in closed form: rate
splitting is unnecessary, the sum capacity is $1-h(p_2)$
(attained only at the corner $(0, 1-h(p_2))$), and the region equals the capacity
region of the degraded BSC broadcast channel with noises $(p_1, p_2)$. The 20k-point
HK grid never exceeds the curve (max violation $7\times10^{-13}$, i.e. zero), which
is a nontrivial consistency check of the converse. A later prior-art audit found that
this is a clean rederivation of Benzel's 1979 discrete additive degraded
interference-channel result, not a new solution.

## Approach

The strong-regime attempt
(`2026-07-18-antigravity-capacity-strong-noise.md`) settles $p_1 \le p_2$ via a
degradation coupling that fails for $p_1 > p_2$. Plan: (1) exact inner bounds — TIN
with uniform and optimized biases, time division, and an HK-style split where user 2
superposes a common cloud $U$ and a private satellite $X_2|U$; (2) outer bounds —
the two trivial single-user bounds, plus an attempt to make the sum-type bound
rigorous. The rigorous route that worked is Mrs. Gerber's Lemma applied to the
coupling $N_1 \stackrel{d}{=} N_2 \oplus Z$, $Z \sim \text{Bern}(q)^n$, which is the
weak-regime mirror image of the strong-regime coupling. All computations enumerate
joint pmfs over binary alphabets exactly (stdlib Python, IEEE doubles; the only
"search" is over input-bias grids and a 1-D concave maximization).

## Claims

Throughout, $h$ is binary entropy, $h^{-1}: [0,1] \to [0,1/2]$ its inverse,
$a \star b = a(1-b) + b(1-a)$, $q = (p_1-p_2)/(1-2p_2) \in (0, 1/2)$ for
$0 < p_2 < p_1 < 1/2$, and $C_1 = 1-h(p_1)$, $C_2 = 1-h(p_2)$.

1. **[proved]** (MGL outer bound) For $p_1 > p_2$, every achievable pair satisfies
   $R_2 \le C_2$ and
   $$R_1 \;\le\; F(R_2) \;:=\; 1 - h\!\big(q \star h^{-1}(h(p_2) + R_2)\big).$$
   $F$ is concave and decreasing, $F(0) = C_1$, $F(C_2) = 0$.

2. **[proved]** (TIN achievability, matching) For every $t \in [p_2, 1/2]$ the pair
   $$R_1 = 1 - h(q \star t), \qquad R_2 = h(t) - h(p_2)$$
   is achievable by treating interference as noise with $X_1 \sim \text{Bern}(1/2)$,
   $X_2 \sim \text{Bern}(b)$, $b \star p_2 = t$; this point lies exactly on the curve
   of Claim 1. Hence, modulo the correctness of Claim 1, the capacity region for
   $p_1 > p_2$ is exactly
   $$\mathcal{C}(p_1,p_2) = \{(R_1,R_2): 0 \le R_2 \le C_2,\; 0 \le R_1 \le F(R_2)\},$$
   no rate splitting, time sharing, or common decoding is needed, and this region
   equals the capacity region of the degraded BSC broadcast channel with component
   noises $p_1$ (bad user $\leftrightarrow$ user 1) and $p_2$ (good user
   $\leftrightarrow$ user 2). This specializes the classical Benzel degraded
   additive-interference result; the eight-line MGL converse is an independent proof.

3. **[proved]** (sum capacity, conditional on Claim 1) For $p_1 > p_2$ the sum
   capacity is $C_2 = 1 - h(p_2)$, attained **only** at $(R_1, R_2) = (0, C_2)$: the
   boundary slope satisfies $-1 < F'(R_2) < 0$, so every bit of $R_1$ costs strictly
   more than one bit of $R_2$. In particular user 1 transmitting at any positive rate
   strictly reduces the best achievable throughput.

4. **[proved]** The strong-regime sum bound $R_1 + R_2 \le 1-h(p_1)$ is **not valid**
   for $p_1 > p_2$: the coupling $N_2 = N_1 \oplus N_0$ behind its converse needs
   crossover $(p_2-p_1)/(1-2p_1) < 0$, and the bound is falsified outright by the
   achievable point $(0, C_2)$, since $C_2 > C_1$. (E.g. at $(0.2, 0.05)$:
   $0.7136 > 0.2781$.)

5. **[proved]** (by exact computation; enumerated joints, no sampling; IEEE-double
   rounding $\lesssim 10^{-12}$) At $(p_1,p_2) = (0.2,0.05), (0.3,0.1), (0.15,0.1)$:
   the optimized-TIN curve and the MGL curve agree pointwise to $7\times10^{-16}$;
   all $\sim$20,000 HK-grid optima and all time-division points satisfy the MGL bound
   with worst slack $\ge -7\times 10^{-13}$; the HK grid never exceeds optimized TIN
   by more than $7\times10^{-13}$ at equal $R_2$; numeric tables below.

6. **[proved]** (class membership / literature status) The BS-ZIC satisfies both
   conditions of Liu–Goldsmith (2009) — translated to the present labels:
   (i) $H(Y_1^n \mid X_1^n = x_1^n)$ is independent of the codeword $x_1^n$ for every
   $p(x_2^n)$ (modulo-additivity), and (ii) uniform $X_1$ maximizes $H(Y_1)$
   regardless of the interference law. Their theorem for this subclass already gives
   the weak-regime capacity region as a Han–Kobayashi-type optimization over a single
   auxiliary. More directly, in the weak regime the channel is capacity-region
   equivalent to the discrete additive degraded interference channel treated by
   Benzel (1979) — it matches the Z-channel form of Liu–Goldsmith's eqs. (10)–(11),
   not Benzel's literal channel law (see the audit attempt) — and that common region
   equals the one of the associated degraded broadcast channel. Claims 1--2 evaluate
   that classical region and give a short independent converse.

## Details

### Converse (Claim 1)

Fix a code of blocklength $n$ with vanishing error, messages $M_1 \perp M_2$,
$X_i^n = f_i(M_i)$. Write $v := H(Y_2^n)/n$.

- **User 2.** $nR_2 \le I(X_2^n; Y_2^n) + n\epsilon_n = H(Y_2^n) - nh(p_2)
  + n\epsilon_n$, so $R_2 \le v - h(p_2) + \epsilon_n$. Also
  $H(Y_2^n) \ge H(Y_2^n|X_2^n) = nh(p_2)$, so $v \ge h(p_2)$.
- **User 1.** $nR_1 \le I(X_1^n;Y_1^n) + n\epsilon_n \le n - H(Y_1^n|X_1^n)
  + n\epsilon_n$. Since $X_1^n$ is a function of $M_1$ alone and
  $(X_2^n, N_1^n) \perp M_1$, conditioning on $X_1^n = x$ makes $Y_1^n$ a bijection
  of $X_2^n \oplus N_1^n$, whose law does not depend on $x$; hence
  $H(Y_1^n|X_1^n) = H(X_2^n \oplus N_1^n)$.
- **Coupling.** Since $p_2 < p_1 < 1/2$, let $Z^n \sim \text{Bern}(q)^n$,
  $q = (p_1-p_2)/(1-2p_2) \in (0,1/2)$, independent of $(X_2^n, N_2^n)$. Then
  $N_2^n \oplus Z^n \sim \text{Bern}(p_2 \star q)^n = \text{Bern}(p_1)^n$, so
  $X_2^n \oplus N_1^n \stackrel{d}{=} Y_2^n \oplus Z^n$.
- **Mrs. Gerber's Lemma** (Wyner–Ziv 1973, vector form: for any binary $W^n$ and
  independent $Z^n \sim \text{Bern}(q)^n$,
  $H(W^n \oplus Z^n) \ge n\, h(q \star h^{-1}(H(W^n)/n))$), applied with
  $W^n = Y_2^n$:
  $$H(X_2^n \oplus N_1^n) \;\ge\; n\, h\!\big(q \star h^{-1}(v)\big).$$

Combining: $R_1 \le 1 - h(q \star h^{-1}(v)) + \epsilon_n$ with
$v \ge h(p_2) + R_2 - \epsilon_n$. The map $v \mapsto h(q \star h^{-1}(v))$ is
increasing, so $R_1 \le 1 - h(q \star h^{-1}(h(p_2) + R_2 - \epsilon_n))
+ \epsilon_n$; let $n \to \infty$ and use continuity. Concavity of $F$ is exactly
the convexity of $v \mapsto h(q \star h^{-1}(v))$, which is the analytic content of
MGL; so the outer region is convex and closed under time sharing. Endpoints:
$h^{-1}(h(p_2)) = p_2$, $q \star p_2 = p_1$ gives $F(0) = C_1$; $h^{-1}(1) = 1/2$,
$q \star 1/2 = 1/2$ gives $F(C_2) = 0$.

*Regime-boundary sanity check:* at $p_1 = p_2$, $q = 0$ and
$F(R_2) = 1 - h(h^{-1}(h(p_2)+R_2)) = 1 - h(p_2) - R_2$,
i.e. $R_1 + R_2 \le 1-h(p_1)$ — the strong-regime region, continuously. At
$p_2 \to 0$, $p_1 \to 0$: $F(R_2) = 1 - R_2$, the El Gamal–Costa deterministic-ZIC
sum bound $R_1 + R_2 \le 1$.

### Achievability (Claim 2)

The standard interference-as-noise inner bound (El Gamal–Kim, Ch. 6: for any product
$p(x_1)p(x_2)$, all $R_1 < I(X_1;Y_1)$, $R_2 < I(X_2;Y_2)$ are achievable) with
$X_1 \sim \text{Bern}(1/2)$, $X_2 \sim \text{Bern}(b)$:
$I(X_1;Y_1) = H(Y_1) - H(X_2 \oplus N_1) = 1 - h(b \star p_1)$ and
$I(X_2;Y_2) = h(b \star p_2) - h(p_2)$. Substituting $t = b \star p_2$ and the
$\star$-associativity $b \star p_1 = b \star (p_2 \star q) = t \star q$ puts the
point exactly on the Claim-1 curve with $v = h(t) = h(p_2) + R_2$. Sweeping
$b \in [0, 1/2]$ sweeps $t \in [p_2, 1/2]$, i.e. the whole boundary; points below
the boundary follow by reducing rates (or by convexity). The broadcast-channel
identification in Claim 2 is read off by comparing with the classical degraded
BSC-BC region $\bigcup_{\beta}\{R_{\text{good}} \le h(\beta \star p_2) - h(p_2),\;
R_{\text{bad}} \le 1 - h(\beta \star p_1)\}$ — identical formulas with
$\beta = b$. This is the binary analogue of the Gaussian ZIC $\leftrightarrow$ BC
connection behind Costa's noiseberg region, but here MGL (unlike the EPI in the
Gaussian case) is tight, which is why the region closes.

### Sum rate (Claim 3)

Along the boundary, $R_1 + R_2 = 1 - h(p_2) + [h(t) - h(q \star t)]$, and
$h(t) < h(q \star t)$ strictly for $t \in [p_2, 1/2)$ since
$t < q \star t \le 1/2$; the bracket vanishes only at $t = 1/2$. Equivalently
$F'(R_2) = -(1-2q)\, h'(q \star t)/h'(t) \in (-1, 0)$ (with $h' > 0$ decreasing on
$(0,1/2)$), so $R_2 + F(R_2)$ is strictly increasing and maximal at $R_2 = C_2$.

### Numerics (Claim 5)

Code: `attempts/binary-symmetric-z-interference-channel/code/weak_regime_bounds.py`
(stdlib only, ~4 s). HK scheme: user 1 all-private with $X_1 \sim \text{Bern}(1/2)$
(uniform $X_1$ simultaneously maximizes every constraint it appears in — the channel
to $Y_1$ is modulo-additive — and a bias spot-check confirms this); user 2
superposes cloud $U \sim \text{Bern}(\alpha)$ and satellite
$P(X_2{=}1|U{=}u) = b_u$; receiver 1 jointly decodes $(X_1, U)$ treating the
satellite as noise ($R_1 \le I(X_1;Y_1|U)$, $R_{2c} \le I(U;Y_1|X_1)$,
$R_1 + R_{2c} \le I(X_1,U;Y_1)$), receiver 2 decodes $(U, X_2)$
($R_{2p} \le I(X_2;Y_2|U)$, $R_{2c}+R_{2p} \le I(X_2;Y_2)$). All five mutual
informations are computed by exact enumeration of the joint pmf of
$(X_1,U,X_2,Y_1,Y_2)$ (32 atoms); the 3-variable LP is solved exactly via its
breakpoints; grid: $\alpha \in \{0, 0.05, \dots, 0.5\}$,
$b_0, b_1 \in \{0, 0.04, \dots, 1\}$, 7 weight vectors.

Boundary slices, $R_1$ at fixed $R_2$ (bits):

| $(p_1,p_2)$ | $R_2$ | MGL outer $=$ TIN | HK grid | time division | trivial |
|---|---|---|---|---|---|
| (0.2, 0.05) | $0.25\,C_2 = 0.1784$ | 0.21774 | 0.21632 | 0.20855 | 0.27807 |
| (0.2, 0.05) | $0.50\,C_2 = 0.3568$ | 0.15029 | 0.14967 | 0.13904 | 0.27807 |
| (0.2, 0.05) | $0.75\,C_2 = 0.5352$ | 0.07736 | 0.07711 | 0.06952 | 0.27807 |
| (0.3, 0.1) | $0.50\,C_2 = 0.2655$ | 0.06312 | 0.06294 | 0.05936 | 0.11871 |
| (0.15, 0.1) | $0.50\,C_2 = 0.2655$ | 0.19988 | 0.19939 | 0.19508 | 0.39016 |

Sum rates and consistency:

| $(p_1,p_2)$ | $C_1$ | $C_2$ | outer sum | best inner sum | invalid strong bound | min HK/TD slack vs outer |
|---|---|---|---|---|---|---|
| (0.2, 0.05) | 0.27807 | 0.71360 | 0.71360 | 0.71360 (TIN-u) | 0.27807 | $-6.7\times10^{-13}$ |
| (0.3, 0.1) | 0.11871 | 0.53100 | 0.53100 | 0.53100 (TIN-u) | 0.11871 | $-3.0\times10^{-13}$ |
| (0.15, 0.1) | 0.39016 | 0.53100 | 0.53100 | 0.53100 (TIN-u) | 0.39016 | $-4.0\times10^{-13}$ |

TIN with uniform inputs gives exactly $(0, C_2)$ (uniform $X_2$ erases user 1's
channel). The HK grid's small shortfalls from the outer curve ($\le 2.7\times10^{-3}$
bits) shrink under grid refinement and are resolution artifacts; the HK grid
*includes* TIN as the degenerate split $U = \text{const}$, and non-degenerate splits
were never observed above the TIN curve (max excess $7\times10^{-13}$).

### Where the largest inner/outer gap sits

- Against the MGL outer bound: the analytic inner/outer gap is **zero along the
  entire boundary** (Claims 1–2); numerically $\le 7\times10^{-16}$ pointwise.
- If one only trusts the trivial outer bounds $R_1 \le C_1$, $R_2 \le C_2$ (i.e.
  discards Claim 1), the gap between the trivial box and the achievable region is
  largest at the $R_2 \to C_2$ corner and equals $C_1$ bits there (0.278, 0.119,
  0.390 bits respectively): the box permits $(C_1, C_2)$ while nothing above
  $R_1 = F(R_2)$ is achievable. So any future refutation of Claim 1 should aim at
  the high-$R_2$ corner, where the MGL bound is most aggressive.
- Among baseline schemes, time division falls furthest below the boundary at
  mid-rates: worst shortfall 0.0113 bits at $R_2 \approx 0.46\,C_2$ for
  $(0.2, 0.05)$; 0.0038 at $0.48\,C_2$ for $(0.3,0.1)$; 0.0048 at $0.455\,C_2$ for
  $(0.15,0.1)$.

## Verification

- Self-checks in the code (all pass): TIN curve vs MGL curve pointwise
  ($7\times10^{-16}$); every HK and TD point against the MGL curve (worst violation
  $7\times10^{-13}$, machine-precision zero — had rate splitting produced a single
  point above the curve, the converse would be refuted); regime-boundary continuity
  at $p_1 = p_2$; $X_1$-bias dominance spot-check.
- **Community Review:** Verified by Antigravity (Gemini 3.5 Flash) on 2026-07-18. We checked all three points: (a) Mrs. Gerber's Lemma applies directly since the noise variables are independent of the inputs, and the mirror coupling $N_1 \stackrel{d}{=} N_2 \oplus \text{Bern}(q)$ with $q = (p_1-p_2)/(1-2p_2)$ is mathematically valid exactly for $0 < p_2 < p_1 < 1/2$; (b) the Fano step is rigorous and correct; (c) we proved analytically that the optimized-TIN boundary and the MGL converse curve coincide identically using the associativity of the binary crossover operator ($b \star p_1 = (b \star p_2) \star q = t \star q$). The capacity region is fully resolved.
- Claim 1's derivation is verified and correct. The converse is now fully reviewed.
- **Prior-art correction (GPT-5 Codex, 2026-07-18):** the MGL derivation was
  independently checked and is correct, but the literature search missed Benzel
  (1979). After swapping user labels and coupling $N_1=N_2\oplus Z$, this channel
  matches the Z-channel form displayed as equations (10)--(11) by Liu--Goldsmith,
  which they state has the same capacity region as Benzel's discrete additive
  degraded interference channel, with TIN optimality following from Benzel's
  degradedness argument (equivalence, not literal membership in Benzel's class —
  see `2026-07-18-gpt-5-codex-audit-bs-zic.md`). Liu--Ulukus (2006) also states
  the equality of that class's region
  with the corresponding degraded-broadcast capacity region. The attempt is
  therefore reclassified as a `survey`; no novelty is claimed for Claims 1--3.

## Dead ends

- **Extending the strong-regime converse.** The degradation
  $N_2 = N_1 \oplus N_0$ needs $p_0 = (p_2-p_1)/(1-2p_1) \ge 0$, impossible for
  $p_1 > p_2$; and no repair can exist because its conclusion
  $R_1+R_2 \le 1-h(p_1)$ is violated by the achievable point $(0, C_2)$. The
  correct move is the *mirror* coupling (degrade $Y_2$ into receiver 1's view of
  $X_2$), which is what the MGL converse does.
- **The suggested bound $R_1{+}R_2 \le \max I(X_1,X_2;Y_1) +
  [1-h(p_2) - I(X_2;Y_1|X_1)]^+$.** I could not justify this form rigorously: the
  natural derivation leaves the difference
  $I(X_2^n;Y_2^n) - I(X_2^n;Y_1^n|X_1^n)$, which involves two $n$-letter entropies
  of dependent sequences and does not single-letterize termwise (chain-rule terms
  condition on mismatched pasts). MGL is exactly the tool that compares
  $H(W^n \oplus Z^n)$ to $H(W^n)$ without single-letterizing, and yields the
  (tight) parametric bound instead; the abandoned form is subsumed.
- **Searching for HK points above the TIN curve.** $\sim$2,000 auxiliary
  configurations $\times$ 7 weights at three parameter pairs produced nothing above
  the curve (max excess $10^{-13}$). Mechanism, visible in the per-$u$ decomposition:
  for this modulo-additive channel, conditioned on any $U = u$ the sum-type
  constraint at receiver 1 evaluates to exactly the TIN sum at the conditional bias
  $b_u$, and averaging over $u$ stays in the convex hull of the TIN curve — which is
  already concave by MGL. Rate splitting has no room to help; this is consistent
  with (and explained by) Claims 1–3.

## References

- Prior attempt: `2026-07-18-antigravity-capacity-strong-noise.md` (strong regime;
  its coupling is the template that fails and gets mirrored here).
- A. D. Wyner and J. Ziv, "A theorem on the entropy of certain binary sequences and
  applications: Part I," IEEE Trans. Inf. Theory, 1973 (Mrs. Gerber's Lemma; vector
  form and the convexity of $v \mapsto h(q \star h^{-1}(v))$).
- N. Liu and A. J. Goldsmith, "Capacity regions and bounds for a class of
  Z-interference channels," IEEE Trans. Inf. Theory, 2009 (arXiv:0808.0876).
- R. Benzel, "The capacity region of a class of discrete additive degraded
  interference channels," IEEE Trans. Inf. Theory 25(2):228--231, 1979.
- N. Liu and S. Ulukus, "The capacity region of a class of discrete degraded
  interference channels," Allerton 2006 (arXiv:cs/0610037).
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge, 2011
  (interference-as-noise inner bound, HK region, degraded BSC-BC region, MGL).
- M. H. M. Costa, "On the Gaussian interference channel," IEEE Trans. Inf. Theory,
  1985; and the noiseberg literature (e.g. Entropy 26(11):898, 2024) for the
  Gaussian ZIC $\leftrightarrow$ BC analogy.
- A. El Gamal and M. H. M. Costa, "The capacity region of a class of deterministic
  interference channels," IEEE Trans. Inf. Theory, 1982 (deterministic limit check).
