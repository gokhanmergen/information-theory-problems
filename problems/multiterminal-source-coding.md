---
id: multiterminal-source-coding
title: Rate-Distortion Region for Two-Terminal Distributed Lossy Source Coding
status: open
category: source-coding
posed_by: Toby Berger and Sui-Yin Tung
posed_year: 1977
tags: [source-coding, rate-distortion, berger-tung, distributed-source-coding]
lean_module: InfoTheory.Problems.MultiterminalSourceCoding
lean_file: lean/InfoTheory/Problems/MultiterminalSourceCoding.lean
---

## Statement

Let $(X_1, X_2) \sim P(x_1, x_2)$ be a discrete memoryless correlated source over finite
alphabets $\mathcal{X}_1 \times \mathcal{X}_2$, equipped with two separate single-letter
distortion measures $d_1 : \mathcal{X}_1 \times \hat{\mathcal{X}}_1 \to \mathbb{R}_{\ge 0}$
and $d_2 : \mathcal{X}_2 \times \hat{\mathcal{X}}_2 \to \mathbb{R}_{\ge 0}$. Two
non-communicating encoders observe $X_1^n$ and $X_2^n$ and transmit rate-$R_1$ and
rate-$R_2$ descriptions to a joint decoder that reconstructs $(\hat{X}_1^n, \hat{X}_2^n)$
within expected distortions $(D_1, D_2)$.

The **Berger–Tung inner bound** (Berger 1977; Tung 1978) consists of the closure of the
convex hull (via time-sharing) of all 4-tuples $(R_1, R_2, D_1, D_2)$ for which there exist
finite-alphabet auxiliary random variables $(U_1, U_2)$ forming the Markov chains
$U_1 - X_1 - X_2 - U_2$ and reconstruction maps $g_1(U_1, U_2) \in \hat{\mathcal{X}}_1$,
$g_2(U_1, U_2) \in \hat{\mathcal{X}}_2$ with $\mathbb{E}[d_j(X_j, g_j(U_1, U_2))] \le D_j$
and:
$$
\begin{aligned}
R_1 &\ge I(X_1; U_1 \mid U_2), \\
R_2 &\ge I(X_2; U_2 \mid U_1), \\
R_1 + R_2 &\ge I(X_1, X_2; U_1, U_2).
\end{aligned}
$$

**Open Problem (Two-Terminal Binary Berger–Tung Problem).** While Wagner, Kelly, and Altuğ (2011) proved that the Berger–Tung inner bound is *not* tight in general even for separate distortions (by embedding a Körner–Marton modulo-2 sum task), it remains open whether the closed convex hull of the Berger–Tung inner bound equals the exact rate-distortion region for the **doubly symmetric binary source** $(X_1, X_2) \sim \mathrm{DSBS}(p)$ ($p \in (0, 1/2)$) under separate Hamming distortions $d_1(x, \hat{x}) = d_2(x, \hat{x}) = \mathbf{1}[x \neq \hat{x}]$.

## Background

Formulated by Berger (1977) and Tung (1978) as the lossy generalization of Slepian–Wolf
coding (1973) and the two-encoder generalization of Wyner–Ziv coding (1976), the
two-terminal distributed source coding problem is the central open problem of multiterminal
rate-distortion theory. The Berger–Tung scheme combines Wyner–Ziv quantization at each
encoder with Slepian–Wolf random binning across encoders, and is matched by a natural
outer bound relaxing the double Markov chain $U_1 - X_1 - X_2 - U_2$ to the weaker
marginal Markov chains $U_1 - X_1 - X_2$ and $U_2 - X_2 - X_1$. Closing the gap between
the inner and outer bounds — or showing that structured coding can beat Berger–Tung even
for separate distortions — has remained open for nearly fifty years.

## What is known

- **Lossless case ($D_1 = D_2 = 0$)**: completely solved by Slepian and Wolf (1973).
- **One lossless, one lossy ($D_1 = 0$ or $D_2 = 0$)**: Berger–Tung is tight (Berger–Yeung
  1989; Kaspi–Berger 1982).
- **Quadratic Gaussian case**: Oohama (1997) resolved the one-distortion case, and Wagner,
  Tavildar, and Viswanath (2008) proved that the Berger–Tung inner bound is **tight** for
  the full two-terminal quadratic Gaussian rate-distortion region.
- **Logarithmic loss**: Courtade and Weissman (2014) proved that Berger–Tung is tight for
  every discrete memoryless source under logarithmic-loss distortion.
- **Suboptimality of Berger–Tung in general (Wagner–Kelly–Altuğ, 2011):** Contrary to earlier hopes, Wagner, Kelly, and Altuğ (2011) constructed a discrete memoryless source with separate distortion measures where structured linear coding strictly outperforms the Berger–Tung inner bound (leveraging a Körner–Marton modulo-2 sum component).
- **Doubly symmetric binary source (open):** For the canonical two-terminal **doubly symmetric binary source** $(X_1, X_2) \sim \mathrm{DSBS}(p)$ under separate Hamming distortions, no counterexample to Berger–Tung is known, and determining its exact rate-distortion region remains one of the flagship open problems in source coding.

## References

- T. Berger, "Multiterminal source coding," in *The Information Theory Approach to
  Communications* (G. Longo, ed.), CISM Courses and Lectures, vol. 229, Springer, 1978,
  pp. 171–231.
- S.-Y. Tung, *Multiterminal Source Coding*, Ph.D. dissertation, Cornell University, 1978.
- J. Körner and K. Marton, "How to encode the modulo-two sum of binary sources," *IEEE
  Trans. Inf. Theory*, vol. 25, no. 2, pp. 219–221, 1979.
- T. Berger and R. W. Yeung, "Multiterminal source encoding with one distortion criterion,"
  *IEEE Trans. Inf. Theory*, vol. 35, no. 2, pp. 228–236, 1989.
- A. B. Wagner, S. Tavildar, and P. Viswanath, "Rate region of the quadratic Gaussian
  two-encoder source-coding problem," *IEEE Trans. Inf. Theory*, vol. 54, no. 5,
  pp. 1938–1961, 2008.
- T. A. Courtade and T. Weissman, "Multiterminal source coding under logarithmic loss,"
  *IEEE Trans. Inf. Theory*, vol. 60, no. 1, pp. 740–761, 2014.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 12.
