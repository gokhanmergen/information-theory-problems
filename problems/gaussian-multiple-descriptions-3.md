---
id: gaussian-multiple-descriptions-3
title: Symmetric Rate-Distortion Function for Three-Channel Quadratic Gaussian Multiple Descriptions
status: open
category: source-coding
posed_by: Raman Venkataramani, Gerhard Kramer, and Vivek K. Goyal
posed_year: 2003
tags: [source-coding, multiple-descriptions, gaussian, converse-tightness]
lean_module: InfoTheory.Problems.GaussianMultipleDescriptions3
lean_file: lean/InfoTheory/Problems/GaussianMultipleDescriptions3.lean
---

## Statement

Consider a standard i.i.d. Gaussian source $X_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$
encoded into three equal-rate descriptions $M_1, M_2, M_3 \in \{1, \dots, 2^{n R}\}$ with
symmetric squared-error distortion targets $0 < D_3 \le D_2 \le D_1 \le 1$:
- every single description achieves expected MSE at most $D_1$;
- every pair of descriptions achieves expected MSE at most $D_2$;
- all three descriptions together achieve expected MSE at most $D_3$.

Let $R_{\mathrm{sym}}^*(D_1, D_2, D_3)$ be the minimum achievable per-description rate.
The **Tian–Mohajer–Diggavi (2009) three-level converse**, optimised over its two auxiliary
remote-source noise levels, is
$$
R_{\mathrm{TMD}}(D_1, D_2, D_3) = \sup_{0 \le b \le a \le 1}
\left[\frac{1}{2}\log_2\frac{1}{a + D_1(1-a)}
+ \frac{1}{4}\log_2\frac{a + D_2(1-a)}{b + D_2(1-b)}
+ \frac{1}{6}\log_2\frac{b + D_3(1-b)}{D_3}\right].
$$
Here $a = d_1/(1+d_1) \ge b = d_2/(1+d_2)$ are the MMSEs of $X$ given the remote sources
$Y_1 = X + N_1 + N_2$ and $Y_2 = X + N_2$ of Tian–Mohajer–Diggavi (2009, §3.1.2, eqs. (25)–(27)).
The bracket is their sum-rate bound divided by 3, and its three terms come from the one-, two-
and three-description levels. It is a valid lower bound: $R_{\mathrm{sym}}^* \ge R_{\mathrm{TMD}}$.

**Is the best known converse tight, i.e. does $R_{\mathrm{sym}}^*(D_1, D_2, D_3) = R_{\mathrm{TMD}}(D_1, D_2, D_3)$
for all $0 < D_3 \le D_2 \le D_1 \le 1$?**

Tian, Mohajer and Diggavi state that this tightness is open: "Though the lower bound given here
may not be tight, it is the first provably good bound with more than two levels of distortion
constraints enforced" (§1). Of optimising over $(d_1, d_2)$ they write: "One could optimize within
this set of lower bounds to find the tightest one, however without a matching inner bound,
solving this rather involved optimization problem offers little insight" (§3.1.2).

## Formal statement (Lean)

```lean
noncomputable def tmdBoundTerm (D₁ D₂ D₃ a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * log2 (1 / (a + D₁ * (1 - a))) +
  (1 / 4 : ℝ) * log2 ((a + D₂ * (1 - a)) / (b + D₂ * (1 - b))) +
  (1 / 6 : ℝ) * log2 ((b + D₃ * (1 - b)) / D₃)

noncomputable def tmdSymRateLowerBound (D₁ D₂ D₃ : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : 0 ≤ b ∧ b ≤ a ∧ a ≤ 1),
    ENNReal.ofReal (tmdBoundTerm D₁ D₂ D₃ a b)

def Statement : Prop :=
  ∀ (D₁ D₂ D₃ : ℝ), 0 < D₃ → D₃ ≤ D₂ → D₂ ≤ D₁ → D₁ ≤ 1 →
    gaussMD3SymRate D₁ D₂ D₃ = tmdSymRateLowerBound D₁ D₂ D₃
```

`gaussMD3SymRate` is the operational optimum: an `sInf` in `ℝ≥0∞` over achievable rates, with
measurable encoders, ε-slack on rate and distortion, and MSE as a Lebesgue `lintegral` against
the `N(0, 1)` product density. It is `⊤` if nothing is achievable. The closed parameter range
gives the same supremum as TMD's open range $d_1 \ge d_2 > 0$, because the bracket is continuous
on $[0,1]^2$.

> **Statement-fix (2026-11-27).** The previous right-hand side was one specific Tian–Chen
> layered achievable rate. That rate kept the layer-2 refinement noise independent of the
> layer-1 noises and allowed no time-sharing. The statement was false as written in two
> independent ways: a correlated refinement beats that rate at $(1/2, 1/10, 1/20)$, and the rate
> is strictly non-convex at $(3/5, 7/80, 19/400)$, while $R^*_{\mathrm{sym}}$ is convex. See
> [`attempts/gaussian-multiple-descriptions-3/2026-11-26-gemini-4-neon.md`](../attempts/gaussian-multiple-descriptions-3/2026-11-26-gemini-4-neon.md).
> Any fixed achievable scheme invites the same refutation, so the statement now asks whether
> the converse side is tight.
> - *Mechanism (i) no longer applies.* A better achievable scheme only lowers the upper bound
>   on $R^*_{\mathrm{sym}}$, and that bound stays $\ge R_{\mathrm{TMD}}$. Refuting the new
>   statement needs a strictly better converse.
> - *Mechanism (ii) no longer applies.* $R_{\mathrm{TMD}}$ is convex. For fixed $a \ge b$ the
>   bracket is a sum of univariate functions of $D_1$, $D_2$ and $D_3$. Each has the form
>   $\log(A + \alpha D) - \log(B + \beta D)$ with $A \ge B$ and $\alpha = 1 - A \le \beta = 1 - B$,
>   so its second derivative $\beta^2/(B+\beta D)^2 - \alpha^2/(A+\alpha D)^2$ is $\ge 0$. A
>   supremum of convex functions is convex.

## Background

Ozarow (1980) completely solved the two-description quadratic Gaussian problem. For
$L \ge 3$ descriptions the problem is open. On the achievability side there are many inner
bounds: Venkataramani–Kramer–Goyal (2003) conditional codebooks, the Pradhan–Puri–Ramchandran
(2004) source-channel erasure codes, and Tian–Chen (2010), who use systematic MDS codes and
quantization splitting and beat PPR. On the converse side, Tian–Mohajer–Diggavi (2009)
extended Ozarow's remote-source technique to two auxiliary remote sources. That gives the first
lower bound with more than two active distortion levels, and it pins down the symmetric rate
to within a constant gap. Song–Shao–Chen (2014) derived a general single-letter sum-rate lower
bound. In the quadratic Gaussian case their Theorems 6–7 and Corollary 10 show that Gaussian
remote sources are optimal. Their bound then reduces to $R_{\mathrm{TMD}}$: at the saddle point
$\theta_0 \ge \dots \ge \theta_3$, so the inner minimum is at $\delta = d$, and $\theta_0 = 1$,
$\theta_3 = 0$ are optimal (our reduction of their formula with $L = 3$, $\lambda = 1$). So
$R_{\mathrm{TMD}}$ is the best converse that current remote-source methods give.

## What is known

- **Sandwich** (certified in Lean): $\frac12\log_2\frac1{D_1} \le R_{\mathrm{TMD}} \le
  \frac12\log_2\frac1{D_1} + \frac14\log_2\frac{D_1}{D_2} + \frac16\log_2\frac{D_2}{D_3}$. The
  upper end is the successive-refinement plus MDS rate of TMD (2009, eq. (22)), which is
  achievable. TMD show that $R^*_{\mathrm{sym}}$ is within $3/4$ bit of this rate (their
  eq. (29)).
- **Solved special cases, where the statement holds:**
  - Individual descriptions only ($D_1 = D_2 = D_3 = D$): $R^* = \frac12\log_2\frac1D$, and
    $R_{\mathrm{TMD}}(D,D,D) = \frac12\log_2\frac1D$ (certified).
  - Pairwise constraint only ($D_1 = 1$, $D_3 = D_2$): $R^* = \frac14\log_2\frac1{D_2}$, attained
    by a $(3,2)$ MDS split, and $R_{\mathrm{TMD}}(1, D_2, D_2) = \frac14\log_2\frac1{D_2}$
    (certified).
  - $D_2$ inactive ($D_2 = D_1$): the exact answer is due to Wang–Viswanath (2007) and Chen
    (2009), and equals the one-auxiliary bound (Song–Shao–Chen 2014, Cor. 12). The slice $b = a$
    of $R_{\mathrm{TMD}}$ dominates that bound (certified). The other inequality follows from
    validity of $R_{\mathrm{TMD}}$ and is not formalized.
  - Two-description restriction: with $b = 0$ the bracket equals Ozarow's symmetric
    two-description sum-rate bound for a pair, halved. So $R_{\mathrm{TMD}}$ dominates Ozarow's
    bound applied to any pair (certified).
- **Open:** whether the converse is tight when all three levels are active. The best known
  inner bounds use Tian–Chen layering with a $(3,2)$ MDS refinement correlated with the base
  layer. At sample points they lie about 0.12–0.18 bit per description above $R_{\mathrm{TMD}}$:
  for example $\approx 0.979$ versus $\approx 0.862$ at $(1/2, 1/10, 1/20)$, and
  $\approx 1.344$ versus $\approx 1.164$ at $(0.4, 0.05, 0.02)$ (grid evaluation; inner-bound
  values from the attempt above). Closing the gap needs a better converse, a better scheme, or
  both.
- **Converse techniques:** Tian–Chen (2010) also bound the PPR region from outside, using
  Han's inequality. Viswanatha–Akyol–Rose (2016) combine combinatorial message sharing with
  random coding for general $L$.

## References

- L. H. Ozarow, "On a source-coding problem with two channels and three receivers," *Bell
  Syst. Tech. J.*, vol. 59, no. 10, pp. 1909–1921, 1980.
- R. Venkataramani, G. Kramer, and V. K. Goyal, "Multiple description coding with many
  channels," *IEEE Trans. Inf. Theory*, vol. 49, no. 9, pp. 2106–2114, 2003.
- H. Wang and P. Viswanath, "Vector Gaussian multiple description with individual and
  central receivers," *IEEE Trans. Inf. Theory*, vol. 53, no. 6, pp. 2133–2153, 2007.
- J. Chen, "Rate region of Gaussian multiple description coding with individual and
  central distortion constraints," *IEEE Trans. Inf. Theory*, vol. 55, no. 9,
  pp. 3991–4005, 2009.
- C. Tian, S. Mohajer, and S. N. Diggavi, "Approximating the Gaussian multiple description
  rate region under symmetric distortion constraints," *IEEE Trans. Inf. Theory*, vol. 55,
  no. 8, pp. 3869–3891, 2009 (arXiv:0810.3631).
- L. Song, S. Shao, and J. Chen, "A lower bound on the sum rate of multiple description coding
  with symmetric distortion constraints," *IEEE Trans. Inf. Theory*, vol. 60, no. 12,
  pp. 7547–7567, Dec. 2014.
- S. S. Pradhan, R. Puri, and K. Ramchandran, "$n$-channel symmetric multiple descriptions —
  Part I: $(n,k)$ source-channel erasure codes," *IEEE Trans. Inf. Theory*, vol. 50, no. 1,
  pp. 47–61, 2004.
- C. Tian and J. Chen, "New coding schemes for the symmetric $K$-description problem,"
  *IEEE Trans. Inf. Theory*, vol. 56, no. 10, pp. 5344–5365, Oct. 2010.
- K. B. Viswanatha, E. Akyol, and K. Rose, "Combinatorial message sharing and a new
  achievable region for multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 62, no. 2,
  pp. 769–792, 2016.
