---
id: gray-wyner-lossy
title: Rate-Distortion Region of the Lossy Gray–Wyner Network with Decoder Side Information
status: open
category: source-coding
posed_by: Robert M. Gray and Aaron D. Wyner (with Heegard–Berger / Kaspi)
posed_year: 1985
tags: [source-coding, gray-wyner, heegard-berger, rate-distortion, side-information]
lean_module: InfoTheory.Problems.GrayWynerLossy
lean_file: lean/InfoTheory/Problems/GrayWynerLossy.lean
---

## Statement

Consider a discrete memoryless correlated tuple $(X_1, X_2, Z_1, Z_2) \sim P$ over finite
alphabets, equipped with distortion measures
$d_j : \mathcal{X}_j \times \hat{\mathcal{X}}_j \to \mathbb{R}_{\ge 0}$ ($j = 1, 2$).
In the **lossy Gray–Wyner network with decoder side information**, a single encoder
observing $(X_1^n, X_2^n)$ sends a common message $M_0$ (rate $R_0$) to both decoders and
private messages $M_1$ (rate $R_1$) and $M_2$ (rate $R_2$) to decoders $1$ and $2$,
respectively. Decoder $j \in \{1, 2\}$ additionally observes correlated side information
$Z_j^n$ and reconstructs $\hat{X}_j^n$ to expected distortion at most $D_j$.

The **split-binning Heegard–Berger / Kaspi / Gray–Wyner single-letter inner bound** consists
of the closed convex hull of all 5-tuples $(R_0, R_1, R_2, D_1, D_2)$ for which there exist
finite-alphabet auxiliaries $(U_0, U_1, U_2)$ satisfying the Markov chain
$(U_0, U_1, U_2) - (X_1, X_2) - (Z_1, Z_2)$, reconstruction maps
$g_1(U_0, U_1, Z_1) \in \hat{\mathcal{X}}_1$ and $g_2(U_0, U_2, Z_2) \in \hat{\mathcal{X}}_2$
with $\mathbb{E}[d_j(X_j, g_j(U_0, U_j, Z_j))] \le D_j$ such that, writing $X = (X_1, X_2)$,
$a_j = I(X; U_0 \mid Z_j)$ and $b_j = I(X; U_j \mid U_0, Z_j)$:
$$
\begin{aligned}
R_0, R_1, R_2 &\ge 0, \\
R_0 + R_1 &\ge a_1 + b_1, \\
R_0 + R_2 &\ge a_2 + b_2, \\
R_0 + R_1 + R_2 &\ge \max(a_1, a_2) + b_1 + b_2.
\end{aligned}
$$
This is the Fourier–Motzkin projection of the scheme that covers $X^n$ by a superposition
codebook $U_0^n \to (U_1^n, U_2^n)$ and splits the Wyner–Ziv bin index of $U_0^n$ over all
three links and that of $U_j^n$ over $M_0$ and $M_j$ (sequential and joint decoding give the
same projection). At $R_1 = R_2 = 0$ it is the classical two-decoder Heegard–Berger inner bound
$R_0 \ge \max(a_1, a_2) + b_1 + b_2$.

**Does the closed convex hull of this single-letter inner bound equal the exact operational
rate-distortion region for every finite-alphabet lossy Gray–Wyner network with decoder side
information?**

> **Statement-fix (2026-11-27).** The original formulation charged the bin index of $U_0$ to
> the common link alone ($R_{00} \ge \max(a_1, a_2)$ with $R_0 = R_{00} + R_{01} + R_{02}$,
> $R_{0j} + R_j \ge b_j$), so the private links could not carry bits of $U_0$. That made the
> frozen statement **false**: for $X_1 = X_2 = X \sim \mathrm{Bern}(1/2)$,
> $Z_1 = \mathrm{BEC}(e)(X)$, $Z_2 = \emptyset$, Hamming distortions, the tuple
> $(R_0, R_1, R_2, D_1, D_2) = (e, 0, 1 - e, 0, 0)$ is achievable by Slepian–Wolf split binning,
> while the old closure forced $(1 + e) R_0 + R_1 + R_2 \ge 1 + e$ against $1 + e^2$ for the
> tuple (gap $e(1 - e)$; `attempts/gray-wyner-lossy/2026-11-26-gemini-4-neon.md`, Claims 1–3).
> The inner bound was replaced by the split-binning polytope above. The tuple is now a
> single-letter point ($U_0 = X$, $U_1, U_2$ constant: $a_1 = H(X \mid Z_1) = e$,
> $a_2 = H(X) = 1$, $b_1 = b_2 = 0$), as machine-checked in
> `InfoTheory.Known.Certificates.GrayWynerLossy.bec_point_mem`. The operational definition, the
> time-sharing closure and the question are unchanged.

## Background

In 1974, Gray and Wyner established the exact single-letter rate-distortion region of the
lossy Gray–Wyner network *without* decoder side information ($Z_1 = Z_2 = \emptyset$).
However, as soon as the two decoders possess non-degraded correlated side information
$(Z_1, Z_2)$, the problem becomes dramatically harder: setting $R_1 = R_2 = 0$ and
$X_1 = X_2 = X$ recovers the classical **Heegard–Berger (1985) / Kaspi (1994)** problem of
lossy source coding when side information may be different at two decoders, while setting
$Z_1 = X_2, Z_2 = X_1$ yields **lossy broadcasting with complementary side information**
(Timo–Grant–Kramer 2011). Determining a tight single-letter characterization for general
non-degraded $(Z_1, Z_2)$ remains one of the major open problems in multiterminal lossy
source coding.

## What is known

- **No side information ($Z_1 = Z_2 = \emptyset$)**: completely solved by Gray and Wyner
  (1974, Theorem 8); the closure of the inner bound above then coincides with Gray–Wyner's exact
  region (its points with $R_0 < I(X; U_0)$ are Gray–Wyner points for a coarser or finer
  common auxiliary; the cut-set bounds $R_{X_i}(D_i) \le R_0 + R_i$ are machine-checked for
  both sides)
  $R_0 \ge I(X_1, X_2; U_0)$, $R_1 \ge R_{X_1 \mid U_0}(D_1)$, $R_2 \ge R_{X_2 \mid U_0}(D_2)$.
- **Stochastically degraded / conditionally less noisy side information**: the two-decoder
  Heegard–Berger (1985) region is tight for stochastically degraded side information and
  more generally for conditionally less noisy side information (Timo–Oechtering–Wigger 2014).
  For the Gray–Wyner network with side information, Benammar and Zaidi (2017/2018) solved the
  case where both decoders reconstruct a common source component losslessly and Decoder 1
  additionally reconstructs a second component lossily; Watanabe (2013) characterized the
  rate-distortion function for a product of two sources with decoder side information.
- **Lossless reconstruction ($D_1 = D_2 = 0$)**: the lossless Heegard–Berger case
  ($R_1 = R_2 = 0$, rate $\max_j H(X \mid Z_j)$) follows from Slepian–Wolf binning; the lossless
  Gray–Wyner network with receiver side information is solved for $X_1 = X_2$, for a degraded
  network and for complementary delivery (Timo–Grant–Chan–Kramer 2008; see below), and for
  the Benammar–Zaidi (2017/2018) lossless/lossy split.
- **Quadratic Gaussian Heegard–Berger / Gray–Wyner**: solved in the scalar Gaussian case
  (where side information is always stochastically degraded) and in certain vector Gaussian
  settings (Tian–Diggavi 2007; Watanabe 2013; Xu–Liu–Chen 2016).
- **General non-degraded lossy case**: for general discrete memoryless sources with
  non-degraded $(Z_1, Z_2)$ — even in the pure broadcast specialization $R_1 = R_2 = 0$
  (Heegard–Berger 1985) or complementary side information $Z_1 = X_2, Z_2 = X_1$
  (Timo–Grant–Kramer 2013) — whether the single-letter inner bound is universally
  tight remains open. (For three or more decoders, Timo–Chan–Grant 2011 disproved Heegard–Berger's
  Theorem 2.)
- **Lossless Gray–Wyner with receiver side information** (Timo–Grant–Chan–Kramer 2008):
  inner and outer bounds, tight when $X_1 = X_2$, for a degraded network, and for complementary
  delivery ($Z_1 = X_2$, $Z_2 = X_1$). Their general inner bound (Thm. 2) charges the common
  auxiliary to $M_0$ alone and is contained in the corrected region above (take $U_0 = W$,
  $U_j = X_j$). At $D_1 = D_2 = 0$ the corrected region also contains their exact regions for
  $X_1 = X_2$ and complementary delivery, which equal the cut-set region
  $R_0 + R_j \ge H(X_1, X_2 \mid Z_j)$ (take $U_0 = (X_1, X_2)$). The degraded case was not
  checked against the corrected region.
- **Formalization history:** the 2026-11 formalization charged the bin index of $U_0$ to the
  common link only and was refuted by the $\mathrm{BEC}(e)$ example above. It was fixed on
  2026-11-27 (see the Statement-fix note). The underlying non-degraded lossy problem remains
  open.

## Formal statement (Lean)

`InfoTheory.Problems.GrayWynerLossy` (`lean/InfoTheory/Problems/GrayWynerLossy.lean`):

- `IsLossyGWSIAchievable P d₁ d₂ R₀ R₁ R₂ D₁ D₂`: $R_0, R_1, R_2 \ge 0$ and for every
  $\varepsilon > 0$ and all large $n$ there are encoders onto $\max(1, \lfloor 2^{n(R_i +
  \varepsilon)} \rfloor)$ messages and decoders $\mathrm{dec}_j(M_0, M_j, Z_j^n)$ with expected
  per-letter distortion $\le D_j + \varepsilon$ under the i.i.d. law $P^{\otimes n}$.
- `lossyGWSIInner P d₁ d₂ D₁ D₂ : Set (ℝ × ℝ × ℝ)`: triples $r = (R_0, R_1, R_2) \ge 0$ for
  which there exist $k_0, k_1, k_2$, a joint law `Q` on
  `X₁ × X₂ × Z₁ × Z₂ × Fin k₀ × Fin k₁ × Fin k₂` with $(X_1, X_2, Z_1, Z_2)$-marginal `P`,
  $I(U_0 U_1 U_2; Z_1 Z_2 \mid X_1 X_2) = 0$, maps $g_1(U_0, U_1, Z_1)$, $g_2(U_0, U_2, Z_2)$
  meeting $D_1, D_2$, and the four rate inequalities $R_0 + R_1 \ge a_1 + b_1$,
  $R_0 + R_2 \ge a_2 + b_2$, $R_0 + R_1 + R_2 \ge a_1 + b_1 + b_2$,
  $R_0 + R_1 + R_2 \ge a_2 + b_1 + b_2$ (all `condMutualInfo` of pushforwards of `Q`).
- `InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ D₁ D₂`: for every $\varepsilon > 0$ a finite convex
  combination of points of `lossyGWSIInner P d₁ d₂ δ₁ᵢ δ₂ᵢ` with averaged rates and
  distortions within $\varepsilon$ of $(R_0, R_1, R_2, D_1, D_2)$.
- `Statement`: for all finite alphabets `Fin k`, all `P`, `d₁`, `d₂` and all
  $(R_0, R_1, R_2, D_1, D_2)$: `IsLossyGWSIAchievable ↔ InLossyGWSIClosure`.

Certificate (`lean/InfoTheory/Known/Certificates/GrayWynerLossy.lean`): Gray–Wyner cut-set
bounds $R_{X_i}(D_i) \le R_0 + R_i$ for both sides when $Z_i$ is trivial; nonemptiness of both
sides; lossless split-binning points ($U_0 = (X_1, X_2)$) lie in the inner bound; the BEC
statement-fix regression `bec_point_mem`.

## References

- R. M. Gray and A. D. Wyner, "Source coding for a simple network," *Bell Syst. Tech. J.*,
  vol. 53, no. 9, pp. 1681–1721, 1974.
- C. Heegard and T. Berger, "Rate distortion when side information may be absent," *IEEE
  Trans. Inf. Theory*, vol. 31, no. 6, pp. 727–734, 1985.
- A. H. Kaspi, "Rate-distortion function when side-information may be present at the
  decoder," *IEEE Trans. Inf. Theory*, vol. 40, no. 6, pp. 2031–2034, 1994.
- R. Timo, T. Chan, and A. Grant, "Rate distortion with side-information at many decoders,"
  *IEEE Trans. Inf. Theory*, vol. 57, no. 8, pp. 5240–5257, Aug. 2011 (arXiv:0901.1705).
- R. Timo, A. Grant, and G. Kramer, "Lossy broadcasting with complementary side
  information," *IEEE Trans. Inf. Theory*, vol. 59, no. 1, pp. 104–131, Jan. 2013.
- S. Watanabe, "The rate-distortion function for product of two sources with side-information
  at decoders," *IEEE Trans. Inf. Theory*, vol. 59, no. 9, pp. 5678–5691, Sept. 2013
  (arXiv:1105.2864).
- R. Timo, T. J. Oechtering, and M. Wigger, "Source coding problems with conditionally less
  noisy side information," *IEEE Trans. Inf. Theory*, vol. 60, no. 9, pp. 5516–5532, Sept. 2014.
- M. Benammar and A. Zaidi, "Rate-distortion region of a Gray–Wyner model with side
  information," arXiv:1701.03612, 2017 (*Entropy*, vol. 20, no. 1, 2018).
- R. Timo, A. Grant, T. Chan, and G. Kramer, "Source coding for a simple network with receiver
  side information," *Proc. IEEE ISIT 2008*, pp. 2307–2311 (arXiv:0805.4053).
- K. B. Viswanatha, E. Akyol, and K. Rose, "The lossy common information of correlated
  sources," *IEEE Trans. Inf. Theory*, vol. 60, no. 6, pp. 3238–3253, 2014.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 14.
