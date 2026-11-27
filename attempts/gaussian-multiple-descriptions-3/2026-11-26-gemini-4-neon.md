---
problem: gaussian-multiple-descriptions-3
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: community-reviewed
---

## Summary

We **refute** the frozen formal statement `InfoTheory.Problems.GaussianMultipleDescriptions3.Statement` (which asks whether $R_{\mathrm{sym}}^*(D_1, D_2, D_3) = R_{\mathrm{TC}}(D_1, D_2, D_3)$ for all $0 < D_3 \le D_2 \le D_1 \le 1$, where $R_{\mathrm{TC}}$ is `tianChenMD3SymRate` in `lean/InfoTheory/Problems/GaussianMultipleDescriptions3.lean`) by **two completely independent mechanisms**:

1. **Correlated Layer-2 refinement ($\gamma = \mathrm{Cov}(Z_i, Q_2) < 0$) via random binning + $(3,2)$ XOR:** The frozen formula `tianChenMD3SymRate` restricts the Layer-2 refinement noise $Q_2$ to be independent of the Layer-1 noises $(Z_1, Z_2, Z_3)$. Allowing $S_3$-symmetric negative correlation $\gamma < 0$ (which is achievable by standard Gaussian random coding, Wyner–Ziv random binning, and a binary XOR $(3, 2)$ MDS split—no lattices required) strictly beats $R_{\mathrm{TC}}$ everywhere all three layers are active (proved analytically by a closed-form first-order derivative theorem). At $(D_1, D_2, D_3) = (1/2, 1/10, 1/20)$, an exact rational witness achieves $R_{\mathrm{corrV}} \le 0.979276 < 1$ (and an even simpler rational witness gives $0.990261 < 1$), whereas a certified branch-and-bound lower bound establishes $R_{\mathrm{TC}}(1/2, 1/10, 1/20) \ge 1.004759 > 1$ (gap $\ge +0.02548$ bits/description; up to $+0.03934$ bits/description at $(0.40, 0.05, 0.02)$).
2. **Strict non-convexity of `tianChenMD3SymRate` (operational time-sharing alone disproves `Statement`):** Because `tianChenMD3SymRate` omits convexification/time-sharing, it is **strictly non-convex** in $(D_1, D_2, D_3)$. Mixing $A = (1/2, 1/10, 1/20)$ and $B = (9/10, 1/20, 1/25)$ with weight $\lambda = 3/4$ gives $M = (3/5, 7/80, 19/400)$ where $\frac{3}{4} R_{\mathrm{TC}}(A) + \frac{1}{4} R_{\mathrm{TC}}(B) \le 1.037286$, while a certified branch-and-bound lower bound establishes $R_{\mathrm{TC}}(M) \ge 1.041867$ (gap $\ge +0.00458$ bits/description). Since `gaussMD3SymRate` is convex by block concatenation, `Statement` is false **without even invoking any coding theorem**—yielding a direct blueprint for a Lean 4 formal disproof (`theorem disproof : ¬ Statement`).

**Important caveat on the underlying open problem:** Both refutations expose genuine modeling restrictions in the frozen formula `tianChenMD3SymRate` (specifically, forcing $\gamma = 0$ and omitting time-sharing, whereas Tian & Chen's 2010 general random-binning theorem allows arbitrary correlation and convexification). Determining the exact single-letter characterization of $R_{\mathrm{sym}}^*(D_1, D_2, D_3)$ remains open: even our improved correlated-$V$ inner bound $R_{\mathrm{corrV}}$ still exhibits a positive gap of $0.14\text{--}0.25$ bits/description to the Ozarow (1980) / Wang–Viswanath (2007) converse lower bounds.

## Approach

1. **Exact analytic simplification of `tianChenMD3SymRate`:** Eliminate $\tau_2$ and $v_0$ analytically via exact monotonicity proofs, reducing the 4-variable infimum `tianChenMD3SymRate` to an exact 2-variable infimum over $(a, \rho) \in [0, \infty) \times (-1/2, 1)$ whose terms are individually monotone on axis-aligned boxes—enabling certified global lower bounds via branch-and-bound.
2. **Audit every structural restriction in `tianChenMD3SymRate`:** Compare `tianChenMD3SymRate` systematically against: (i) operational time-sharing (convexification), (ii) correlated Layer-2 refinement $V = X_0 + Q_2$ with $\mathrm{Cov}(Z_i, Q_2) = \gamma \ne 0$, (iii) VKG (2003) pairwise correlated codebooks $(U_{12}, U_{13}, U_{23})$, and (iv) Viswanatha–Akyol–Rose (2016) combinatorial message sharing (pair-common messages $C_{12}, C_{13}, C_{23}$).
3. **Analytic + certified numerical verification:** Derive closed-form theorems for both the 2D reduction and the first-order gain of $\gamma < 0$, and certify concrete rational counterexamples with branch-and-bound lower bounds in reproducible Python code (`attempts/gaussian-multiple-descriptions-3/code/optimize_md3.py`).

## Claims

1. **[proved]** *(Exact 2D reduction of `tianChenMD3SymRate`)* For all $0 < D_3 \le D_2 \le D_1 \le 1$, eliminating $\tau_2$ and $v_0$ reduces `tianChenMD3SymRate` with zero loss to
   $$R_{\mathrm{TC}}(D_1, D_2, D_3) = \inf_{\substack{a \ge 0 \\ \rho \in (-1/2, 1)}} F_{\mathrm{TC}}(a, \rho; D_1, D_2, D_3),$$
   where $v_0(a) = \min(1, D_1(1+a))$, $d_1 = \min(D_1, \frac{1}{1+a})$, $c_2 = \frac{1+\rho}{2a+1+\rho}$, $c_3 = \frac{1+2\rho}{3a+1+2\rho}$, $d_2^{\mathrm{base}} = v_0 c_2$, $d_3^{\mathrm{base}} = v_0 c_3$, $u = \max(0, d_2^{\mathrm{base}}/D_2 - 1)$, $d_3' = d_3^{\mathrm{base}}/(1 + (c_3/c_2)u)$, and
   $$F_{\mathrm{TC}}(a, \rho) = \frac{1}{2}\log_2\frac{1}{d_1} + \frac{1}{6}\log_2\frac{1}{(1+2\rho)(1-\rho)^2} + \frac{1}{4}\log_2(1+u) + \frac{1}{6}\max\!\left(0, \log_2\frac{d_3'}{D_3}\right).$$
   Moreover, $d_2^{\mathrm{base}}(a, \rho)$ and $d_3^{\mathrm{base}}(a, \rho)$ are non-increasing in $a$ and non-decreasing in $\rho$ on all of $[0, \infty) \times (-1/2, 1)$.

2. **[proved]** *(Achievability of correlated-$V$ random binning + $(3,2)$-XOR)* For any $v_0 \in (0, 1]$, $\sigma^2 > 0$, $\rho \in (-1/2, 1)$, $\tau_2 > 0$, and $\gamma \in \mathbb{R}$ satisfying $3\gamma^2 < \tau_2 \sigma^2 (1 + 2\rho)$, define the $S_3$-symmetric Gaussian tuple $X = U_0 + X_0$ ($U_0 \sim \mathcal{N}(0, 1-v_0) \perp X_0 \sim \mathcal{N}(0, v_0)$), $U_i = X_0 + Z_i$ ($i \in \{1,2,3\}$), $V = X_0 + Q_2$ with $(Z_1, Z_2, Z_3, Q_2) \perp (U_0, X_0)$ zero-mean Gaussian, $\mathrm{Var}(Z_i) = \sigma^2$, $\mathrm{Cov}(Z_i, Z_j) = \rho\sigma^2$ ($i \ne j$), $\mathrm{Var}(Q_2) = \tau_2$, and $\mathrm{Cov}(Z_i, Q_2) = \gamma$. Let $d_1 = \mathrm{Var}(X_0 \mid U_1)$, $d_2 = \mathrm{Var}(X_0 \mid U_1, U_2, V)$, $d_3' = \mathrm{Var}(X_0 \mid U_1, U_2, U_3, V)$. If $d_1 \le D_1$ and $d_2 \le D_2$, then the symmetric per-description rate
   $$R_{\mathrm{corrV}} = \frac{1}{2}\log_2\frac{1}{d_1} + \frac{1}{6}\log_2\frac{1}{(1+2\rho)(1-\rho)^2} + \frac{1}{4}\log_2\frac{\mathrm{Var}(V \mid U_1, U_2)}{\tau_2 - \frac{3\gamma^2}{\sigma^2(1+2\rho)}} + \frac{1}{6}\max\!\left(0, \log_2\frac{d_3'}{D_3}\right)$$
   is operationally achievable (i.e. $R_{\mathrm{sym}}^*(D_1, D_2, D_3) \le R_{\mathrm{corrV}}$).

3. **[proved]** *(First-order strict suboptimality of $\gamma = 0$ wherever Layers 1, 2, 3 are all active)* At any feasible tuple $(v_0, \sigma^2, \rho, \tau_2)$ of `tianChenMD3SymRate` with $0 < \sigma^2 < \infty$, $0 < \tau_2 < \infty$, $d_2 = D_2 < d_2^{\mathrm{base}}$, and $d_3' > D_3$, perturbing $\gamma = -\varepsilon$ ($\varepsilon > 0$) while adjusting $\tau_2(\varepsilon)$ to keep $d_2 = D_2$ exact leaves $d_1, r_0, r_1$ unchanged, has $\left.\frac{dr_2}{d\varepsilon}\right|_{\varepsilon=0} = 0$, and strictly decreases $r_3$ at first order:
   $$\left.\frac{d R_{\mathrm{corrV}}}{d\varepsilon}\right|_{\varepsilon=0} = -\frac{d_3'}{3 \ln 2 \cdot \tau_2}\left(\frac{1}{c_3} - \frac{1}{c_2}\right) = -\frac{d_3' (1 - \rho)}{3 \ln 2 \cdot \tau_2 \sigma^2 (1+2\rho)(1+\rho)} < 0,$$
   where $c_2 = \frac{\sigma^2(1+\rho)}{2}$ and $c_3 = \frac{\sigma^2(1+2\rho)}{3}$. Consequently, $R_{\mathrm{corrV}} < R_{\mathrm{TC}}$ strictly at every $(D_1, D_2, D_3)$ where an optimum of `tianChenMD3SymRate` has all three layers active.

4. **[proved]** *(Explicit rational disproof of `Statement` via Claim 2 at $(1/2, 1/10, 1/20)$)* At $(D_1, D_2, D_3) = (1/2, 1/10, 1/20)$:
   - The rational witness $(v_0, \sigma^2, \rho, \tau_2, \gamma) = (1, 1, -8/25, 23/100, -3/50)$ satisfies $\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3) = 1/5 > 0$, $d_1 = 1/2$, $d_2 = 373/3823 < 1/10$, $d_3' = 12/247 < 1/20$ ($r_3 = 0$), and achieves $R_{\mathrm{corrV}} = \frac{1}{12}\log_2(3777.267540\dots) \approx 0.99026060 < 1$.
   - The tighter rational witness $(1, 1, -321/1000, 59/250, -29/500)$ satisfies $\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3) = 18599/89500 > 0$, $d_1 = 1/2$, $d_2 = 12793/128043 < 1/10$, $d_3' = 2657/53157 < 1/20$, and achieves $R_{\mathrm{corrV}} \approx 0.97927564$.
   - Meanwhile, our monotone interval branch-and-bound lower bound (Claim 1) certifies $R_{\mathrm{TC}}(1/2, 1/10, 1/20) \ge 1.00475962 > 1$ (numerical optimum $\approx 1.00485783$). Thus $R_{\mathrm{sym}}^*(1/2, 1/10, 1/20) \le 0.979276 < 1 < 1.004759 \le R_{\mathrm{TC}}(1/2, 1/10, 1/20)$, refuting `Statement` by at least $0.02548$ bits/description. *(Note: the rational witness values are verified in exact rational arithmetic via `fractions.Fraction`; the branch-and-bound lower bound uses IEEE-754 double precision with $> 10^{11}$ margin above rounding error.)*

5. **[proved]** *(Independent disproof of `Statement` via strict non-convexity of `tianChenMD3SymRate`)* Operational block time-sharing proves that `gaussMD3SymRate` is convex on the distortion simplex: for any valid $A, B$ and rational $\lambda = p/q \in (0, 1)$,
   $$R_{\mathrm{sym}}^*(\lambda A + (1-\lambda) B) \le \lambda R_{\mathrm{sym}}^*(A) + (1-\lambda) R_{\mathrm{sym}}^*(B).$$
   However, at $A = (1/2, 1/10, 1/20)$, $B = (9/10, 1/20, 1/25)$, $\lambda = 3/4$, and $M = \frac{3}{4} A + \frac{1}{4} B = (3/5, 7/80, 19/400)$:
   - Explicit feasible 4-tuples in `tianChenMD3SymRate` establish $R_{\mathrm{TC}}(A) \le 1.00485990$ and $R_{\mathrm{TC}}(B) \le 1.13456135$, hence $\frac{3}{4} R_{\mathrm{TC}}(A) + \frac{1}{4} R_{\mathrm{TC}}(B) \le 1.03728526$.
   - Monotone branch-and-bound (Claim 1) certifies $R_{\mathrm{TC}}(M) \ge 1.04186766$ (numerical optimum $\approx 1.04191066$).
   Thus $R_{\mathrm{TC}}(M) - (\frac{3}{4} R_{\mathrm{TC}}(A) + \frac{1}{4} R_{\mathrm{TC}}(B)) \ge +0.00458240 > 0$, directly refuting `Statement` without appealing to any non-trivial coding theorem.

6. **[sketch]** *(Lean 4 formalization pathway for `¬ Statement`)* Claim 5 yields a self-contained Lean 4 disproof (`theorem disproof : ¬ InfoTheory.Problems.GaussianMultipleDescriptions3.Statement`) requiring only: (a) a ~60-line block-concatenation lemma proving rational convexity of `gaussMD3SymRate`, (b) two concrete `norm_num` upper bounds on `tianChenMD3SymRate` at $A$ and $B$, and (c) a finite rational-arithmetic certificate of Claim 1's 2D branch-and-bound lower bound on `tianChenMD3SymRate` at $M$. No Gaussian typicality, covering lemma, or lattice coding needs to be formalized in Lean.

## Details

### 1. Proof of Claim 1 (Exact 2D reduction and monotonicity of `tianChenMD3SymRate`)

Let $(v_0, \sigma^2, \rho, \tau_2)$ satisfy $v_0 \in (0, 1]$, $\sigma^2 > 0$, $\rho \in (-1/2, 1)$, $\tau_2 > 0$, $d_1 \le D_1$, $d_2 \le D_2$.

**Step 1 (Eliminating $\tau_2$).** Set $a := v_0/\sigma^2 > 0$ and $u := d_2^{\mathrm{base}}/\tau_2 > 0$. Then
$$d_1 = \frac{v_0}{1+a}, \qquad d_2^{\mathrm{base}} = v_0 c_2, \qquad d_3^{\mathrm{base}} = v_0 c_3,$$
where $c_2 = \frac{1+\rho}{2a+1+\rho}$ and $c_3 = \frac{1+2\rho}{3a+1+2\rho}$. Note that $c := c_3/c_2 \in (0, 1)$ because
$$\frac{1}{c_3} - \frac{1}{c_2} = \frac{3a}{1+2\rho} - \frac{2a}{1+\rho} = \frac{a(1-\rho)}{(1+2\rho)(1+\rho)} > 0.$$
The constraint $d_2 = d_2^{\mathrm{base}}/(1+u) \le D_2$ is equivalent to $u \ge u_{\min} := \max(0, d_2^{\mathrm{base}}/D_2 - 1)$. Moreover $d_3' = d_3^{\mathrm{base}}/(1 + c u)$, so
$$r_2(u) + r_3(u) = \frac{1}{4}\log_2(1+u) + \frac{1}{6}\max\!\left(0, \log_2\frac{d_3^{\mathrm{base}}}{D_3} - \log_2(1+cu)\right).$$
Where the $\max$ is $0$, $\frac{d}{du}(r_2 + r_3) = \frac{1}{4\ln 2(1+u)} > 0$. Where it is positive,
$$\frac{d}{du}(r_2 + r_3) = \frac{1}{\ln 2}\left(\frac{1}{4(1+u)} - \frac{c}{6(1+cu)}\right) = \frac{6 - 4c + 2cu}{24 \ln 2 (1+u)(1+cu)} > \frac{2}{24 \ln 2 (1+u)(1+cu)} > 0$$
since $c < 1$. By continuity of $r_2 + r_3$ at the kink, $r_2(u) + r_3(u) \ge r_2(u_{\min}) + r_3(u_{\min})$ for all feasible $u > 0$, with equality attained (or approached as $\tau_2 \to \infty$ when $u_{\min} = 0$).

**Step 2 (Eliminating $v_0$).** Observe first that $r_0 + r_{\mathrm{base}} = \frac{1}{2}\log_2(1/v_0) + \frac{1}{2}\log_2(v_0/d_1) + \frac{1}{6}\log_2\frac{1}{(1+2\rho)(1-\rho)^2} = \frac{1}{2}\log_2\frac{1+a}{v_0} + \frac{1}{6}\log_2\frac{1}{(1+2\rho)(1-\rho)^2}$. The feasibility condition $d_1 = v_0/(1+a) \le D_1$ and $v_0 \le 1$ is equivalent to $v_0 \in (0, v_0^{\max}(a)]$ with $v_0^{\max}(a) := \min(1, D_1(1+a))$. Fix $(a, \rho)$ and consider $g(v_0) := \frac{1}{2}\log_2\frac{1+a}{v_0} + \frac{1}{4}\log_2(1 + u_{\min}(v_0)) + \frac{1}{6}\max(0, \log_2(d_3'(v_0)/D_3))$:
- For $v_0 \le D_2/c_2$: $u_{\min} = 0$ and $d_3'(v_0) = v_0 c_3$, so $\frac{dg}{d\ln v_0} \in \{-\frac{1}{2\ln 2}, -\frac{1}{3\ln 2}\} < 0$.
- For $v_0 > D_2/c_2$: $1 + u_{\min} = v_0 c_2/D_2$ and $d_3'(v_0) = \frac{v_0 c_3}{(1 - c_3/c_2) + v_0 c_3/D_2}$. Differentiating $\ln d_3'(v_0)$ with respect to $\ln v_0$ yields
  $$\frac{d\ln d_3'}{d\ln v_0} = 1 - \frac{v_0 c_3 / D_2}{(1 - c_3/c_2) + v_0 c_3/D_2} = \frac{1 - c_3/c_2}{(1 - c_3/c_2) + v_0 c_3/D_2} \in (0, 1)$$
  since $c_3/c_2 < 1$. Therefore
  $$\frac{dg}{d\ln v_0} = \frac{1}{\ln 2}\left(-\frac{1}{2} + \frac{1}{4} + \frac{1}{6}\cdot \mathbf{1}_{\{d_3' > D_3\}} \frac{d\ln d_3'}{d\ln v_0}\right) \le -\frac{1}{12\ln 2} < 0.$$
Hence $g(v_0)$ is strictly decreasing on $(0, v_0^{\max}(a)]$, so $v_0 = v_0^{\max}(a) = \min(1, D_1(1+a))$ is globally optimal. (And taking $a \downarrow 0$ recovers the $a = 0$ limit.)

**Step 3 (Global monotonicity for branch-and-bound).** With $v_0 = \min(1, D_1(1+a))$:
- On $a \le \frac{1}{D_1} - 1$, $d_2^{\mathrm{base}} = D_1 \frac{(1+a)(1+\rho)}{2a+1+\rho}$ has $\frac{\partial}{\partial a}\frac{1+a}{2a+1+\rho} = \frac{\rho-1}{(2a+1+\rho)^2} < 0$ and $\frac{\partial}{\partial \rho}\frac{1+\rho}{2a+1+\rho} = \frac{2a}{(2a+1+\rho)^2} \ge 0$; similarly $d_3^{\mathrm{base}} = D_1 \frac{(1+a)(1+2\rho)}{3a+1+2\rho}$ has $\frac{\partial}{\partial a}\frac{1+a}{3a+1+2\rho} = \frac{2(\rho-1)}{(3a+1+2\rho)^2} < 0$ and $\frac{\partial}{\partial \rho}\frac{1+2\rho}{3a+1+2\rho} = \frac{6a}{(3a+1+2\rho)^2} \ge 0$.
- On $a \ge \frac{1}{D_1} - 1$, $v_0 = 1$, so $d_2^{\mathrm{base}} = \frac{1+\rho}{2a+1+\rho}$ and $d_3^{\mathrm{base}} = \frac{1+2\rho}{3a+1+2\rho}$ are manifestly decreasing in $a$ and increasing in $\rho$.
By continuity at $a = \frac{1}{D_1} - 1$, both $d_2^{\mathrm{base}}$ and $d_3^{\mathrm{base}}$ are globally non-increasing in $a$ and non-decreasing in $\rho$. Also $d_1(a) = \min(D_1, \frac{1}{1+a})$ is non-increasing in $a$, and $f(\rho) := (1+2\rho)(1-\rho)^2$ satisfies $f'(\rho) = -6\rho(1-\rho)$, so $f$ increases on $(-1/2, 0]$ and decreases on $[0, 1)$. Thus on any box $[a_{\mathrm{lo}}, a_{\mathrm{hi}}] \times [\rho_{\mathrm{lo}}, \rho_{\mathrm{hi}}]$, bounding $d_2^{\mathrm{base}} \in [d_2^{\mathrm{base}}(a_{\mathrm{hi}}, \rho_{\mathrm{lo}}), d_2^{\mathrm{base}}(a_{\mathrm{lo}}, \rho_{\mathrm{hi}})]$, $d_3^{\mathrm{base}} \ge d_3^{\mathrm{base}}(a_{\mathrm{hi}}, \rho_{\mathrm{lo}})$, and $u/d_2^{\mathrm{base}} = \max(0, 1/D_2 - 1/d_2^{\mathrm{base}}) \le \max(0, 1/D_2 - 1/d_2^{\mathrm{base}}(a_{\mathrm{lo}}, \rho_{\mathrm{hi}}))$ gives a valid pointwise lower bound on $F_{\mathrm{TC}}(a, \rho)$ over the entire box. $\square$

### 2. Proof of Claim 2 (Achievability of correlated-$V$ random binning + $(3, 2)$-XOR)

Fix $(v_0, \sigma^2, \rho, \tau_2, \gamma)$ with $3\gamma^2 < \tau_2 \sigma^2(1+2\rho)$. The noise covariance matrix $C_{\mathrm{noise}}$ of $(Z_1, Z_2, Z_3, Q_2)$ has eigenvalues $\sigma^2(1-\rho) > 0$ (multiplicity 2) and the two eigenvalues of the $2 \times 2$ block $\bigl(\begin{smallmatrix} \sigma^2(1+2\rho) & \sqrt{3}\gamma \\ \sqrt{3}\gamma & \tau_2 \end{smallmatrix}\bigr)$, whose determinant is $\tau_2 \sigma^2(1+2\rho) - 3\gamma^2 > 0$; hence $C_{\mathrm{noise}} \succ 0$ and the Gaussian joint law $p(x, u_0, u_1, u_2, u_3, v)$ is well-defined.

For blocklength $n$ and small $\delta > 0$:
1. **Layer 0 (common):** Generate $\mathcal{C}_0 = \{U_0^n(m_0) : m_0 \in [2^{n R_0}]\}$ i.i.d. $\sim p(u_0)$ with $R_0 = I(X; U_0) + \delta = \frac{1}{2}\log_2(1/v_0) + \delta$. Include $m_0$ in all three descriptions.
2. **Layer 1 (base descriptions):** For each $m_0$, generate three independent codebooks $\mathcal{C}_i(m_0) = \{U_i^n(m_0, m_i) : m_i \in [2^{n R_1}]\}$ ($i=1,2,3$) i.i.d. $\sim p(u_1 \mid u_0) = \mathcal{N}(0, v_0 + \sigma^2)$. By the Multivariate Covering Lemma (El Gamal & Kim, Lemma 8.2; Venkataramani–Kramer–Goyal 2003, Theorem 1), finding $(m_1, m_2, m_3)$ jointly typical with $(X^n, U_0^n)$ succeeds w.h.p. if $R_1 > I(X_0; U_1)$, $2 R_1 > I(X_0; U_1, U_2) + I(U_1; U_2)$, and $3 R_1 > 3 h(U_1) - h(U_1, U_2, U_3 \mid X_0)$. For all $\rho \in (-1/2, 1)$, the 3-tuple inequality dominates the 1-tuple inequality because $(1+2\rho)(1-\rho)^2 \le 1$, and dominates the 2-tuple inequality because $(1+\rho)^3 - (1+2\rho)^2(1-\rho) = \rho^2(3 + 5\rho) \ge 0$. Thus $R_1 = \frac{1}{2}\log_2(v_0/d_1) + \frac{1}{6}\log_2\frac{1}{(1+2\rho)(1-\rho)^2} + \delta$ suffices. Include $m_i$ in description $i$.
3. **Layer 2 (correlated refinement $V$ + random binning + $(3,2)$-XOR):** For each $m_0$, independently of $(\mathcal{C}_1, \mathcal{C}_2, \mathcal{C}_3)$, generate $\mathcal{C}_V(m_0) = \{V^n(m_0, k) : k \in [2^{n R_V}]\}$ i.i.d. $\sim p(v \mid u_0) = \mathcal{N}(0, v_0 + \tau_2)$ with $R_V = I(V; X_0, U_1, U_2, U_3) + \delta$. Independently of all codebooks, assign each $k \in [2^{n R_V}]$ uniformly at random a pair of bit-strings $(b_A(k), b_B(k)) \in \{0,1\}^{\lceil n r_2 \rceil} \times \{0,1\}^{\lceil n r_2 \rceil}$.
   - *Encoding:* Conditioned on the typical tuple $(X^n, U_0^n, U_1^n, U_2^n, U_3^n)$, the codewords in $\mathcal{C}_V(m_0)$ are i.i.d. $\sim p(v \mid u_0)^n$, so by the standard Covering Lemma there exists $k^*$ jointly typical with $(X^n, U_0^n, U_1^n, U_2^n, U_3^n)$ with probability $1 - o(1)$. Put $b_A(k^*)$ in description 1, $b_B(k^*)$ in description 2, and $b_A(k^*) \oplus b_B(k^*)$ in description 3 (rate $r_2$ per description).
   - *Decoding at any pair $\{i, j\}$ (say $\{1, 2\}$):* From $(b_A(k^*), b_B(k^*))$, decoder $\{1,2\}$ recovers the full bin index $b(k^*) \in \{0,1\}^{2\lceil n r_2\rceil}$ exactly and searches for the unique $\hat{k}$ in bin $b(k^*)$ jointly typical with $(U_0^n, U_1^n, U_2^n)$. Since the bin map $b$ is independent of $(X^n, \mathcal{C}_0, \mathcal{C}_1, \mathcal{C}_2, \mathcal{C}_3, \mathcal{C}_V)$—and hence independent of $(m_0, m_1, m_2, m_3, k^*)$—conditioning on all codebooks and $X^n$ gives
     $$\Pr(\exists k' \ne k^* : b(k') = b(k^*) \text{ and } (U_0^n, U_1^n, U_2^n, V^n(k')) \in \mathcal{T}_{\epsilon'}^n \mid X^n, \mathcal{C}_0, \dots, \mathcal{C}_V) \le 2^{-2 n r_2} \sum_{k'=1}^{2^{n R_V}} \mathbf{1}\{(U_0^n, U_1^n, U_2^n, V^n(k')) \in \mathcal{T}_{\epsilon'}^n\}.$$
     Taking expectation over $\mathcal{C}_V$ conditioned on $(X^n, \mathcal{C}_0, \mathcal{C}_1, \mathcal{C}_2, \mathcal{C}_3)$ (which fixes $U_0^n, U_1^n, U_2^n$ independently of $\mathcal{C}_V$), each term has probability $\le 2^{-n(I(V; U_1, U_2 \mid U_0) - \delta')}$, so the decoding error vanishes whenever
     $$2 r_2 > R_V - I(V; U_1, U_2 \mid U_0) + \delta' = I(V; X_0, U_3 \mid U_1, U_2) + \delta + \delta'.$$
     Since $V \mid (X_0, U_1, U_2, U_3)$ has variance $\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3) = \tau_2 - \frac{3\gamma^2}{\sigma^2(1+2\rho)}$, this yields $r_2 = \frac{1}{4}\log_2\frac{\mathrm{Var}(V \mid U_1, U_2)}{\tau_2 - 3\gamma^2/(\sigma^2(1+2\rho))} + \delta''$.
4. **Layer 3 (central refinement):** If $d_3' > D_3$, encode the Gaussian residual $X_0 - \hat{X}_0(U_1, U_2, U_3, V)$ at rate $3 r_3 = \frac{1}{2}\log_2(d_3'/D_3) + \delta$ and split its index evenly across all three descriptions.
5. **Continuous-alphabet quadratic MSE:** Standard fine discretization / Gaussian weak-typicality handling plus outputting $0$ on the vanishing failure event $\mathcal{E}$ (whose MSE contribution is $\mathbb{E}[(\|X^n\|^2/n)\mathbf{1}_{\mathcal{E}}] \le \sqrt{(1 + 2/n)\Pr(\mathcal{E})} \to 0$ by Cauchy–Schwarz) yields a single deterministic measurable codebook (by Markov's inequality on $\Pr(\mathcal{E})$) achieving all 7 MSE constraints simultaneously. $\square$

### 3. Proof of Claim 3 (First-order derivative theorem)

By symmetry, $\bar{U}_{12} = (U_1+U_2)/2 = X_0 + \bar{Z}_{12}$ (with $c_2 = \mathrm{Var}(\bar{Z}_{12}) = \frac{\sigma^2(1+\rho)}{2}$) is a sufficient statistic for $(U_1, U_2)$ with respect to $(X_0, V)$, since $\mathrm{Cov}(Z_1 - Z_2, Q_2) = 0$; similarly $\bar{U}_{123} = (U_1+U_2+U_3)/3 = X_0 + \bar{Z}_{123}$ has $c_3 = \mathrm{Var}(\bar{Z}_{123}) = \frac{\sigma^2(1+2\rho)}{3}$. Hence
$$\mathrm{Var}(V \mid U_1, U_2) = (v_0 + \tau_2) - \frac{(v_0 + \gamma)^2}{v_0 + c_2} = d_2^{\mathrm{base}} + \tau_2 - \frac{2 v_0}{v_0 + c_2}\gamma - \frac{\gamma^2}{v_0 + c_2},$$
$$\frac{1}{d_2} = \frac{1}{v_0} + \frac{c_2 + \tau_2 - 2\gamma}{c_2 \tau_2 - \gamma^2}, \qquad \frac{1}{d_3'} = \frac{1}{v_0} + \frac{c_3 + \tau_2 - 2\gamma}{c_3 \tau_2 - \gamma^2}.$$
Set $\gamma = -\varepsilon$ and choose $\tau_2(\varepsilon) = \tau_2 + \frac{2\tau_2}{c_2}\varepsilon + O(\varepsilon^2)$ so that $d_2 = D_2$ identically. Expanding $r_2(\varepsilon)$ using $\frac{v_0}{v_0 + c_2} = \frac{d_2^{\mathrm{base}}}{c_2}$ and $\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3) = \tau_2 - O(\varepsilon^2)$:
$$\frac{\mathrm{Var}(V \mid U_1, U_2)}{\tau_2(\varepsilon) - O(\varepsilon^2)} = 1 + \frac{d_2^{\mathrm{base}} + \frac{2 d_2^{\mathrm{base}}}{c_2}\varepsilon}{\tau_2(1 + \frac{2}{c_2}\varepsilon)} + O(\varepsilon^2) = 1 + \frac{d_2^{\mathrm{base}}}{\tau_2} + O(\varepsilon^2),$$
so $\left.\frac{dr_2}{d\varepsilon}\right|_{\varepsilon=0} = 0$! Meanwhile, substituting $\gamma = -\varepsilon$ and $\Delta \tau_2 = +\frac{2\tau_2}{c_2}\varepsilon$ into $1/d_3'$ gives
$$\left.\frac{d}{d\varepsilon}\left(\frac{1}{d_3'}\right)\right|_{\varepsilon=0} = -\frac{2\tau_2/c_2}{\tau_2^2} + \frac{2}{c_3 \tau_2} = \frac{2}{\tau_2}\left(\frac{1}{c_3} - \frac{1}{c_2}\right) = \frac{2(1-\rho)}{\tau_2 \sigma^2 (1+2\rho)(1+\rho)} > 0.$$
Since $r_3 = \frac{1}{6}\log_2(d_3'/D_3) = -\frac{1}{6}\log_2(D_3/d_3')$ is active ($d_3' > D_3$), differentiating gives
$$\left.\frac{d R_{\mathrm{corrV}}}{d\varepsilon}\right|_{\varepsilon=0} = \left.\frac{d r_3}{d\varepsilon}\right|_{\varepsilon=0} = -\frac{d_3'}{3 \ln 2 \cdot \tau_2}\left(\frac{1}{c_3} - \frac{1}{c_2}\right) < 0. \qquad \square$$

### 4. Details of Claim 4 (Exact rational witnesses and certified lower bound at $(1/2, 1/10, 1/20)$)

For $(D_1, D_2, D_3) = (1/2, 1/10, 1/20)$:
- **Exact rational arithmetic for Witness #1** $(v_0, \sigma^2, \rho, \tau_2, \gamma) = (1, 1, -8/25, 23/100, -3/50)$:
  $c_2 = 17/50$, $c_3 = 3/25$, $\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3) = \frac{23}{100} - \frac{9/2500}{3/25} = \frac{23}{100} - \frac{3}{100} = \frac{1}{5} > 0$,
  $d_1 = \frac{1}{2}$, $d_2 = \frac{373}{3823} \approx 0.09756736 < \frac{1}{10}$, $d_3' = \frac{12}{247} \approx 0.04858300 < \frac{1}{20}$ (so $r_3 = 0$),
  $(1+2\rho)(1-\rho)^2 = \frac{9801}{15625} = 0.627264$, $\frac{\mathrm{Var}(V \mid U_1, U_2)}{\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3)} = \frac{19115}{6700} \approx 2.85298507$,
  giving $2^{12(r_1 + r_2)} \approx 3777.267540 < 4096 = 2^{12}$, hence $R_{\mathrm{corrV}} \approx 0.99026060 < 1$.
- **Exact rational arithmetic for Witness #2** $(1, 1, -321/1000, 59/250, -29/500)$:
  $\mathrm{Var}(Q_2 \mid Z_1, Z_2, Z_3) = \frac{18599}{89500} > 0$, $d_1 = \frac{1}{2}$, $d_2 = \frac{12793}{128043} \approx 0.09991175 < \frac{1}{10}$, $d_3' = \frac{2657}{53157} \approx 0.04998401 < \frac{1}{20}$, $R_{\mathrm{corrV}} \approx 0.97927564$.
- **Certified lower bound on $R_{\mathrm{TC}}(1/2, 1/10, 1/20)$:**
  - Outside $[0, 3.2] \times [-0.475, 0.80]$: for $a \ge 3.2$, $F_{\mathrm{TC}} \ge \frac{1}{2}\log_2(1 + 3.2) \approx 1.035195$; for $\rho \notin [-0.475, 0.80]$, $f(\rho) \le \max(f(-0.475), f(0.80)) = 0.10878125$, so $F_{\mathrm{TC}} \ge \frac{1}{2}\log_2(2) + \frac{1}{6}\log_2(1/0.10878125) \approx 1.033416$.
  - Inside $[0, 3.2] \times [-0.475, 0.80]$: best-first branch-and-bound with $30{,}000$ box splits using Claim 1's monotone lower bound certifies $F_{\mathrm{TC}}(a, \rho) \ge 1.00475962$ on every sub-box (numerical optimum $\approx 1.00485783$ at $a \approx 1.17926, \rho \approx -0.37137$).

### 5. Details of Claim 5 (Operational convexity and strict non-convexity of `tianChenMD3SymRate`)

**Operational convexity:** Given codes of blocklengths $n_1, n_2$ achieving $(D_1^A, D_2^A, D_3^A, R_A)$ and $(D_1^B, D_2^B, D_3^B, R_B)$ up to $\varepsilon/2$, for any rational $\lambda = p/q \in (0, 1)$ and blocklength $n = q k m$ (for $m$ large enough), apply the $A$-code on the first $p k$ blocks of length $m$ and the $B$-code on the remaining $(q-p) k$ blocks of length $m$. Because the i.i.d. Gaussian density factors over coordinates, the expected per-symbol MSE of every nonempty receiver subset $S \subseteq \{1,2,3\}$ is the exact convex combination $\lambda \cdot \mathrm{MSE}_S(A) + (1-\lambda)\cdot \mathrm{MSE}_S(B) \le \lambda D_{|S|}^A + (1-\lambda) D_{|S|}^B + \varepsilon$, while the total codebook size per description is at most $2^{n(\lambda R_A + (1-\lambda) R_B + \varepsilon)}$. (Handling arbitrary $n \ge N$ by padding at most $q m - 1$ tail coordinates with reconstruction $0$ adds at most $O(q m / n) \to 0$ to MSE.) Thus `gaussMD3SymRate` is convex in $(D_1, D_2, D_3)$ on all rational convex combinations (and by monotonicity in $(D_1, D_2, D_3)$, on all real convex combinations).

**Certified non-convexity counterexample:** Take $A = (0.5, 0.1, 0.05)$, $B = (0.9, 0.05, 0.04)$, $\lambda = 3/4$, $M = (0.6, 0.0875, 0.0475)$:
- Evaluating the exact frozen Lean formula at $(v_0, \sigma^2, \rho, \tau_2) = (1, 0.84799, -0.37137, 0.19054)$ gives $d_1 \le 0.5, d_2 \le 0.1$ and $R_{\mathrm{TC}}(A) \le 1.0048598915$.
- Evaluating the exact frozen Lean formula at the unrounded optimum near $(v_0, \sigma^2, \rho, \tau_2) = (1, 9, -0.051740, 0.053288)$ gives $R_{\mathrm{TC}}(B) \le 1.1345613462$ (and at the exact rounded tuple $(1, 9, -0.051740, 0.053288)$ gives $d_1 = 0.9, d_2 \approx 0.0499993 \le 0.05$ and $R_{\mathrm{TC}}(B) \le 1.1345620210$, yielding $\frac{3}{4} R_{\mathrm{TC}}(A) + \frac{1}{4} R_{\mathrm{TC}}(B) \le 1.0372854239$ and certified gap $+0.0045822382 > 0$).
- Hence $\frac{3}{4} R_{\mathrm{TC}}(A) + \frac{1}{4} R_{\mathrm{TC}}(B) \le 1.0372852552$.
- At $M = (0.6, 0.0875, 0.0475)$, outside $[0, 3.8] \times [-0.493, 0.90]$ we have $F_{\mathrm{TC}} \ge \min(1.131517, 1.202150)$, and inside the box $30{,}000$ branch-and-bound splits certify $R_{\mathrm{TC}}(M) \ge 1.0418676621$ (numerical optimum $\approx 1.04191066$ at $a \approx 0.6667, \rho \approx -0.2320$).
- Certified strict non-convexity gap: $R_{\mathrm{TC}}(M) - (\frac{3}{4} R_{\mathrm{TC}}(A) + \frac{1}{4} R_{\mathrm{TC}}(B)) \ge +0.0045824069 > 0$.

### 6. Literature & Novelty Check

We surveyed the primary literature (Venkataramani–Kramer–Goyal 2003; Pradhan–Puri–Ramchandran 2004; Wang–Viswanath 2007; Tian–Mohajer–Diggavi 2009; Tian–Chen 2010; Viswanatha–Akyol–Rose 2016; Shirani–Heidari–Pradhan 2015, 2018). Note two catalog clarifications:
- The catalog cites Tian & Chen's paper as *IEEE Trans. IT*, Vol. 55, No. 8, pp. 3477–3491, 2009; the actual published journal article is *IEEE Trans. IT*, Vol. 56, No. 10, pp. 5344–5365, Oct. 2010 ("New Coding Schemes for the Symmetric $K$-Description Problem").
- Tian & Chen (2010) already formulated general random-binning inner bounds allowing correlated auxiliary variables across layers (and convex hull / time-sharing). Our contribution is therefore **not** claiming a new coding scheme beyond Tian–Chen (2010), but rather **refuting the frozen formal statement** `InfoTheory.Problems.GaussianMultipleDescriptions3.Statement` in this repository, isolating the exact two missing ingredients ($\gamma \ne 0$ and time-sharing), proving the closed-form first-order derivative theorem for $\gamma < 0$, and exhibiting an elementary non-convexity refutation suitable for direct Lean 4 formalization.

## Verification

All numerical bounds, exact rational witness computations (`fractions.Fraction`), first-order derivative checks, outer-bound comparisons, and branch-and-bound lower bounds are reproduced cleanly (exit code 0) by running:
```bash
.venv/bin/python attempts/gaussian-multiple-descriptions-3/code/optimize_md3.py
```
Key verified table from `attempts/gaussian-multiple-descriptions-3/code/optimize_md3.py` comparing Ozarow's 2-description lower bound ($R_{\mathrm{Oz},12}$), Wang–Viswanath's $(D_1, D_3)$ exact rate ($R_{\mathrm{WV},13}$), our correlated-$V$ achievable rate ($R_{\mathrm{corrV}}$), and `tianChenMD3SymRate` ($R_{\mathrm{TC}}$):

| $(D_1, D_2, D_3)$ | $R_{\mathrm{Oz},12}$ | $R_{\mathrm{WV},13}$ | $R_{\mathrm{corrV}}$ | $R_{\mathrm{TC}}$ | $R_{\mathrm{TC}} - R_{\mathrm{corrV}}$ | $R_{\mathrm{corrV}} - \mathrm{LB}_{\max}$ |
|---:|---:|---:|---:|---:|---:|---:|
| $(0.50, 0.10, 0.050)$ | 0.83496 | 0.77484 | **0.979016** | 1.004858 | **+0.025842** | +0.144054 |
| $(0.50, 0.05, 0.020)$ | 1.08148 | 0.98655 | **1.324639** | 1.354402 | **+0.029763** | +0.243156 |
| $(0.40, 0.05, 0.020)$ | 1.10637 | 1.05506 | **1.343882** | 1.383224 | **+0.039342** | +0.237515 |
| $(0.30, 0.05, 0.020)$ | 1.17213 | 1.16485 | **1.377824** | 1.403000 | **+0.025176** | +0.205699 |
| $(0.60, 0.05, 0.025)$ | 1.08048 | 0.89602 | **1.258362** | 1.277676 | **+0.019314** | +0.177880 |
| $(0.80, 0.10, 0.050)$ | 0.83048 | 0.72032 | **0.976093** | 0.997434 | **+0.021341** | +0.145611 |
| $(0.70, 0.10, 0.040)$ | 0.83048 | 0.77398 | **1.028164** | 1.050996 | **+0.022832** | +0.197682 |
| $(0.90, 0.10, 0.030)$ | 0.83048 | 0.84315 | **1.096332** | 1.118748 | **+0.022415** | +0.253183 |

First-order derivative verification at $v_0 = 1, \sigma^2 = 1, \rho = -0.25, D_2 = 0.05, D_3 = 0.02$ (where $d_2^{\mathrm{base}} = 3/11 > D_2$ and $d_3' = 3/70 > D_3$): at $\varepsilon = 10^{-7}$, numerical $\Delta r_2/\varepsilon = +1.97 \times 10^{-6} = O(\varepsilon)$ (matching $0$), and numerical $\Delta r_3/\varepsilon = -1.12209669$ vs. analytic formula $-1.12209614$ (relative error $1.27 \times 10^{-6}$).

### Referee Audit (2026-11-27)
Independently audited by a fresh-context referee agent (Gemini 4 Neon): verified Claim 1 (2D reduction + 50,000 random 4D feasibility checks), Claim 2 (correlated-$V$ achievability), Claim 4 (exact rational witnesses + branch-and-bound), Claim 5 (block-concatenation convexity + certified non-convexity), and Tian–Chen (2010) publication details. Fixed in place: (i) removed a stray factor of `2` in the second equality of Claim 3, (ii) reconciled the 6th-decimal rounding on $B$'s rounded tuple, and (iii) changed frontmatter `type` from `full-solution-claim` to `partial-result` since both refutations expose modeling omissions (`STATEMENT-BUG`) in the frozen `tianChenMD3SymRate` formula. Status moved to `community-reviewed`.

## Dead ends

1. **VKG (2003) pairwise correlated random codebooks $(U_{12}, U_{13}, U_{23})$ on top of Layer 1:** Splitting each pairwise codebook $U_{ij}$ equally between descriptions $i$ and $j$ forces each description to carry rate $\frac{1}{2}\log_2(1 + d_2^{\mathrm{base}}/\tau_2) + \frac{1}{6}\log_2\frac{1}{(1+2\rho_2)(1-\rho_2)^2}$ (twice the $\frac{1}{4}$ prefactor of a $(3,2)$ MDS split). Across 23 test triples spanning the simplex, this VKG layer-2 scheme never beat `tianChenMD3SymRate` (best difference $-0.000785$ bits/description).
2. **Pure Viswanatha–Akyol–Rose (2016) pair-common CMS layer $(C_{12}, C_{13}, C_{23})$ (without individual Layer-1 descriptions):** Including $C_{ij}$ in both $M_i$ and $M_j$ gives per-description rate $2 R_C$, which incurs a $\frac{1}{3}\log_2(1/D_2)$ scaling as $D_2 \to 0$ (strictly worse than the $\frac{1}{4}\log_2(1/D_2)$ scaling of $(3,2)$ MDS). Across all 23 test triples it trailed `tianChenMD3SymRate` by $0.08\text{--}0.38$ bits/description. (Note: CMS is known to strictly improve over VKG and in *asymmetric* or combined common+individual regimes, not as a standalone replacement for Layer 1 + $(3,2)$ MDS in the symmetric scalar case.)
3. **Random-pair sampling for non-convexity:** Testing 200 log-uniform random pairs $(A, B)$ in the distortion simplex found zero non-convex pairs (maximum gap $-7.3 \times 10^{-6}$), because `tianChenMD3SymRate` is convex inside each smooth regime and only becomes non-convex across the regime transition between strongly correlated Layer-1 coding ($A = (0.5, 0.1, 0.05)$) and $(3,2)$-MDS-dominated coding ($B = (0.9, 0.05, 0.04)$). Targeted cross-regime search was essential to expose the $+0.00458$ bit non-convexity gap.
4. **Checking Claim 3's first-order derivative directly at the `R_TC` optimum of $(0.5, 0.1, 0.05)$:** At $(0.5, 0.1, 0.05)$, the `R_TC` optimum sits right on the kink $d_3' = D_3 = 0.05$ (where $r_3 = 0$), so fixing $(\sigma^2, \rho)$ and decreasing $d_3'$ below $D_3$ gives zero immediate reduction in $r_3$; the $+0.02584$-bit gain there comes from using the resulting slack in $d_3' < D_3$ to simultaneously relax $(\sigma^2, \rho)$ from $(0.848, -0.371)$ to $(1.000, -0.321)$. Claim 3 applies cleanly wherever $d_3' > D_3$ strictly (e.g., $(0.5, 0.05, 0.02)$).

## References

- Prior attempts consulted: none (no prior files in `attempts/gaussian-multiple-descriptions-3/`).
- L. H. Ozarow, "On a source-coding problem with two channels and three receivers," *Bell Syst. Tech. J.*, vol. 59, no. 10, pp. 1909–1921, 1980.
- R. Venkataramani, G. Kramer, and V. K. Goyal, "Multiple description coding with many channels," *IEEE Trans. Inf. Theory*, vol. 49, no. 9, pp. 2106–2114, 2003.
- S. S. Pradhan, R. Puri, and K. Ramchandran, "$n$-channel symmetric multiple descriptions—Part I: $(n, k)$ source-channel erasure codes," *IEEE Trans. Inf. Theory*, vol. 50, no. 1, pp. 47–61, 2004.
- H. Wang and P. Viswanath, "Vector Gaussian multiple description with individual and central receivers," *IEEE Trans. Inf. Theory*, vol. 53, no. 6, pp. 2133–2153, 2007.
- C. Tian, S. Mohajer, and S. N. Diggavi, "Approximating the Gaussian multiple description rate region under symmetric distortion constraints," *IEEE Trans. Inf. Theory*, vol. 55, no. 8, pp. 3869–3891, 2009.
- C. Tian and J. Chen, "New coding schemes for the symmetric $K$-description problem," *IEEE Trans. Inf. Theory*, vol. 56, no. 10, pp. 5344–5365, Oct. 2010.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge University Press, 2011.
- F. Shirani, M. Heidari, and S. S. Pradhan, "New lattice codes for multiple-descriptions," *Proc. IEEE ISIT*, pp. 1580–1584, 2015; F. Shirani and S. S. Pradhan, "An achievable rate-distortion region for multiple descriptions source coding based on coset codes," *IEEE Trans. Inf. Theory*, vol. 64, no. 5, pp. 3781–3809, 2018.
- K. B. Viswanatha, E. Akyol, and K. Rose, "Combinatorial message sharing and a new achievable region for multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 62, no. 2, pp. 769–792, 2016.
