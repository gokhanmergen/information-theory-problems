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

The canonical **Heegard–Berger / Kaspi / Gray–Wyner single-letter inner bound** consists of
the closed convex hull of all 5-tuples $(R_0, R_1, R_2, D_1, D_2)$ for which there exist
finite-alphabet auxiliaries $(U_0, U_1, U_2)$ satisfying the Markov chain
$(U_0, U_1, U_2) - (X_1, X_2) - (Z_1, Z_2)$, reconstruction maps
$g_1(U_0, U_1, Z_1) \in \hat{\mathcal{X}}_1$ and $g_2(U_0, U_2, Z_2) \in \hat{\mathcal{X}}_2$
with $\mathbb{E}[d_j(X_j, g_j(U_0, U_j, Z_j))] \le D_j$, and a common-rate split
$R_0 = R_{00} + R_{01} + R_{02}$ ($R_{00}, R_{01}, R_{02} \ge 0$) such that:
$$
\begin{aligned}
R_{00} &\ge \max\!\big(I(X_1, X_2; U_0 \mid Z_1),\; I(X_1, X_2; U_0 \mid Z_2)\big), \\
R_{01} + R_1 &\ge I(X_1, X_2; U_1 \mid U_0, Z_1), \\
R_{02} + R_2 &\ge I(X_1, X_2; U_2 \mid U_0, Z_2).
\end{aligned}
$$

**Does the closed convex hull of this single-letter inner bound equal the exact operational
rate-distortion region for every finite-alphabet lossy Gray–Wyner network with decoder side
information?**

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
  (1974, Theorem 8); the inner bound above reduces identically to Gray–Wyner's exact region
  $R_0 \ge I(X_1, X_2; U_0)$, $R_1 \ge R_{X_1 \mid U_0}(D_1)$, $R_2 \ge R_{X_2 \mid U_0}(D_2)$.
- **Stochastically degraded side information** ($X - Z_1 - Z_2$): the Heegard–Berger
  (1985) and Gray–Wyner with degraded side information (Watanabe 2013) regions are
  completely solved and coincide with the inner bound above.
- **Lossless reconstruction ($D_1 = D_2 = 0$)**: solved for complementary side information
  and for the lossless Heegard–Berger / Gray–Wyner network with side information via
  Slepian–Wolf binning (Watanabe 2013; Timo–Grant–Kramer 2011).
- **Quadratic Gaussian Heegard–Berger / Gray–Wyner**: solved in the scalar Gaussian case
  (where side information is always stochastically degraded) and in certain vector Gaussian
  settings (Tian–Diggavi 2007; Watanabe 2013; Xu–Liu–Chen 2016).
- **General non-degraded lossy case**: for general discrete memoryless sources with
  non-degraded $(Z_1, Z_2)$ — even in the pure broadcast specialization $R_1 = R_2 = 0$
  (Heegard–Berger 1985) or complementary side information $Z_1 = X_2, Z_2 = X_1$
  (Timo–Grant–Kramer 2011) — whether the single-letter inner bound above is universally
  tight remains open.

## References

- R. M. Gray and A. D. Wyner, "Source coding for a simple network," *Bell Syst. Tech. J.*,
  vol. 53, no. 9, pp. 1681–1721, 1974.
- C. Heegard and T. Berger, "Rate distortion when side information may be absent," *IEEE
  Trans. Inf. Theory*, vol. 31, no. 6, pp. 727–734, 1985.
- A. H. Kaspi, "Rate-distortion function when side-information may be present at the
  decoder," *IEEE Trans. Inf. Theory*, vol. 40, no. 6, pp. 2031–2034, 1994.
- R. Timo, A. Grant, and G. Kramer, "Lossy broadcasting with complementary side
  information," *IEEE Trans. Inf. Theory*, vol. 57, no. 1, pp. 104–131, 2011.
- S. Watanabe, "The rate-distortion region of the Gray–Wyner system with side
  information," *IEEE Trans. Inf. Theory*, vol. 59, no. 4, pp. 2106–2119, 2013.
- K. B. Viswanatha, E. Akyol, and K. Rose, "The lossy common information of correlated
  sources," *IEEE Trans. Inf. Theory*, vol. 60, no. 6, pp. 3238–3253, 2014.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 14.
