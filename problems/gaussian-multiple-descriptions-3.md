---
id: gaussian-multiple-descriptions-3
title: Symmetric Rate-Distortion Function for Three-Channel Quadratic Gaussian Multiple Descriptions
status: open
category: source-coding
posed_by: Ramzam Venkataramani, Gerhard Kramer, and Vivek K. Goyal
posed_year: 2003
tags: [source-coding, multiple-descriptions, gaussian, lattice-coding]
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
The **Tian–Chen (2009) three-layer hybrid Gaussian-and-MDS-lattice rate**
$R_{\mathrm{TC}}(D_1, D_2, D_3)$ is the infimum of $r_0 + r_{\mathrm{base}} + r_2 + r_3$
over common-layer conditional variance $v_0 \in (0, 1]$, base Gaussian noise variance
$\sigma^2 > 0$, pairwise correlation $\rho \in (-1/2, 1)$, and $(3, 2)$ MDS lattice
refinement variance $\tau_2 > 0$ such that:
$$
d_1 = \frac{v_0 \sigma^2}{v_0 + \sigma^2} \le D_1, \qquad
d_2^{\mathrm{base}} = \frac{v_0 \sigma^2 (1 + \rho)}{2 v_0 + \sigma^2 (1 + \rho)}, \qquad
d_2 = \frac{d_2^{\mathrm{base}} \tau_2}{d_2^{\mathrm{base}} + \tau_2} \le D_2,
$$
$$
d_3^{\mathrm{base}} = \frac{v_0 \sigma^2 (1 + 2\rho)}{3 v_0 + \sigma^2 (1 + 2\rho)}, \qquad
d_3' = \frac{d_3^{\mathrm{base}} \tau_2}{d_3^{\mathrm{base}} + \tau_2},
$$
with per-description layer rates:
$$
r_0 = \frac{1}{2} \log_2 \frac{1}{v_0}, \quad
r_{\mathrm{base}} = \frac{1}{2} \log_2 \frac{v_0}{d_1} + \frac{1}{6} \log_2 \frac{1}{(1 + 2\rho)(1 - \rho)^2}, \quad
r_2 = \frac{1}{4} \log_2 \!\left(1 + \frac{d_2^{\mathrm{base}}}{\tau_2}\right), \quad
r_3 = \frac{1}{6} \max\!\left(0, \log_2 \frac{d_3'}{D_3}\right).
$$

**Does $R_{\mathrm{sym}}^*(D_1, D_2, D_3) = R_{\mathrm{TC}}(D_1, D_2, D_3)$ for all
$0 < D_3 \le D_2 \le D_1 \le 1$?**

## Background

While Ozarow (1980) completely solved the two-description quadratic Gaussian problem using
only unstructured Gaussian random codebooks (El Gamal–Cover), moving from $L = 2$ to
$L = 3$ descriptions reveals a dramatic structural phenomenon. Venkataramani, Kramer, and
Goyal (2003) generalized Zhang–Berger to combinatorial layers of random codebooks for
$L \ge 3$ descriptions. In a breakthrough 2009 paper, Tian and Chen proved that when the
intermediate pairwise distortion constraint $D_2$ is active, **structured lattice coding**
(splitting a quantized refinement across descriptions via a $(3, 2)$ MDS code) strictly
outperforms random-codebook layering. Determining the exact symmetric rate-distortion
function $R_{\mathrm{sym}}^*(D_1, D_2, D_3)$ — and whether Tian–Chen's hybrid
random-and-lattice architecture is optimal — remains a flagship open problem of
multiterminal source coding.

## What is known

- **$L = 2$ descriptions**: completely solved by Ozarow (1980).
- **$L = 3$ without pairwise constraint ($D_2$ inactive)**: Wang and Viswanath (2007)
  determined the exact symmetric sum-rate (and Chen 2009 determined the full rate region)
  when only individual distortion $D_1$ and central distortion $D_3$ are constrained.
  This is recovered as a special case of $R_{\mathrm{TC}}$ by letting $\tau_2 \to \infty$
  and $v_0 = 1$.
- **Strict suboptimality of random coding (VKG)**: Tian and Chen (2009) proved that
  combining Gaussian random descriptions with $(3, 2)$ MDS lattice refinement strictly
  beats Venkataramani–Kramer–Goyal's (2003) unstructured inner bound on open sets of
  $(D_1, D_2, D_3)$.
- **Converse bounds**: Tian and Chen (2009) derived a tightened outer bound strictly
  improving the naive maximum of 1-, 2-, and 3-description bounds; however, a positive gap
  between $R_{\mathrm{TC}}$ and the best known outer bounds persists when all three
  distortion constraints $(D_1, D_2, D_3)$ are simultaneously active.
- **Combinatorial message sharing**: Viswanatha, Akyol, and Rose (2016) unified
  combinatorial message sharing with lattice coding for general $L$-description networks,
  yet the exact three-description Gaussian rate-distortion function remains open.
- **Formalization note (2026-11):** The frozen Lean formula `tianChenMD3SymRate` in
  `lean/InfoTheory/Problems/GaussianMultipleDescriptions3.lean` omits both (i) cross-layer
  correlation $\gamma = \mathrm{Cov}(Z_i, Q_2) < 0$ between Layer 1 and Layer 2 and
  (ii) convexification/time-sharing. Consequently, `GaussianMultipleDescriptions3.Statement`
  is **false as written** by two independent mechanisms: correlated Layer-2 refinement beats
  `tianChenMD3SymRate` at $(1/2, 1/10, 1/20)$ by $\ge 0.02548$ bits/description (up to
  $0.03934$ bits), and `tianChenMD3SymRate` is strictly non-convex at $(3/5, 7/80, 19/400)$
  by $\ge 0.00458$ bits/description (see `attempts/gaussian-multiple-descriptions-3/2026-11-26-gemini-4-neon.md`).
  A statement-fix PR is needed to compare against Tian–Chen (2010)'s full correlated,
  time-shared region. The underlying open problem of exact $R_{\mathrm{sym}}^*(D_1, D_2, D_3)$
  remains open.

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
- C. Tian and J. Chen, "New coding schemes for the symmetric $K$-description problem,"
  *IEEE Trans. Inf. Theory*, vol. 56, no. 10, pp. 5344–5365, Oct. 2010.
- K. B. Viswanatha, E. Akyol, and K. Rose, "Combinatorial message sharing and a new
  achievable region for multiple descriptions," *IEEE Trans. Inf. Theory*, vol. 62, no. 2,
  pp. 769–792, 2016.
