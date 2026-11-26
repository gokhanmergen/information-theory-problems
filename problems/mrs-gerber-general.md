---
id: mrs-gerber-general
title: Generalization of Mrs. Gerber's Lemma to Cyclic Groups
status: open
category: entropy-inequalities
posed_by: Aaron D. Wyner and Jacob Ziv; Varun Jog and Venkat Anantharam
posed_year: 1973
tags: [entropy-inequalities, mrs-gerber-lemma, finite-groups, discrete-epi]
lean_module: InfoTheory.Problems.MrsGerberGeneral
lean_file: lean/InfoTheory/Problems/MrsGerberGeneral.lean
---

## Statement

For an integer $q \ge 2$, consider the cyclic group $\mathbb{Z}/q\mathbb{Z}$. For $u, v \in [0, \log_2 q]$, define the minimum sum-entropy function
$$f_q(u, v) := \inf \Big\{ H(X + Y) \;\Big|\; X, Y \text{ independent on } \mathbb{Z}/q\mathbb{Z},\; H(X) \ge u,\; H(Y) \ge v \Big\},$$
where $H(\cdot)$ denotes Shannon entropy in bits and addition is taken modulo $q$.

**Conjecture (Generalized Mrs. Gerber's Lemma for Cyclic Groups; Jog–Anantharam, 2014).** For every integer $q \ge 2$ and every fixed $v \in [0, \log_2 q]$, the function $u \mapsto f_q(u, v)$ is convex on $[0, \log_2 q]$: for all $u_1, u_2 \in [0, \log_2 q]$ and $\lambda \in [0, 1]$,
$$f_q(\lambda u_1 + (1 - \lambda) u_2,\, v) \;\le\; \lambda f_q(u_1, v) + (1 - \lambda) f_q(u_2, v).$$

## Background

In 1973, Wyner and Ziv proved **Mrs. Gerber's Lemma (MGL)** for $\mathbb{Z}/2\mathbb{Z}$: for independent binary random variables $X, Z$ with $H(Z) = h(\alpha)$, the map $u \mapsto h(h^{-1}(u) \star \alpha)$ is convex on $[0, 1]$, which immediately tensorizes via the chain rule and data processing to give the sharp $n$-letter inequality
$$\frac{1}{n} H(X^n \oplus Z^n) \;\ge\; h\!\left(h^{-1}\!\left(\frac{1}{n} H(X^n)\right) \star \alpha\right).$$
MGL is the canonical discrete counterpart of Shannon's Entropy Power Inequality (EPI) and is an indispensable tool in multiuser information theory (e.g., the binary symmetric broadcast channel, Wyner–Ziv coding, and wiretap channels).

For $q \ge 3$, Witsenhausen (1974) observed that fixing $Y$ to be a *symmetric* $q$-ary channel noise ($\mathsf{QSC}(q, \alpha)$) yields a single-letter entropy curve $u \mapsto \inf_{H(X) \ge u} H(X + Y)$ that is **not** convex in general, so the naive $q$-ary symmetric formula fails. Jog and Anantharam (2014) formulated the right group-theoretic generalization via the two-variable extremal function $f_G(u, v)$ over arbitrary independent $X, Y$ on a finite abelian group $G$, proving convexity for all groups of order $2^m$ and conjecturing convexity for all finite abelian groups — in particular all cyclic groups $\mathbb{Z}/q\mathbb{Z}$. Convexity of $u \mapsto f_q(u, v)$ is equivalent to the $n$-letter tensorized Mrs. Gerber's Lemma for independent $X^n, Y^n$ on $(\mathbb{Z}/q\mathbb{Z})^n$ with i.i.d. $Y_i$.

## What is known

- **$q = 2$ (Wyner–Ziv, 1973):** Proved completely; $f_2(u, v) = h(h^{-1}(u) \star h^{-1}(v))$ is strictly convex in $u$ for every $v \in (0, 1)$.
- **Binary-input memoryless symmetric channels (Chayat–Shamai, 1989):** Extended MGL convexity to arbitrary BMS channels.
- **Abelian groups of order $2^m$ (Jog–Anantharam, 2014):** Proved that $u \mapsto f_G(u, v)$ is convex for every finite abelian group $G$ of order $2^m$ (including $\mathbb{Z}/2^m\mathbb{Z}$ and $\mathbb{F}_2^m$), characterizing the extremal distributions via subgroup mixtures.
- **General DMCs via lower convex envelopes (Witsenhausen, 1974; Ahlswede–Körner; Nair–El Gamal):** The *lower convex envelope* $\breve{F}_W$ of the single-letter input-output entropy curve always tensorizes to $W^{\otimes n}$, but for $q \ge 3$ and $\mathsf{QSC}(q, \alpha)$ the single-letter curve itself is strictly non-convex for small $\alpha$.
- **Prime-order cyclic groups $\mathbb{Z}/q\mathbb{Z}$ ($q = 3, 5, \dots$):** Numerical evidence in Jog–Anantharam (2014) supports convexity of $f_q(\cdot, v)$ on $\mathbb{Z}/3\mathbb{Z}$ and $\mathbb{Z}/5\mathbb{Z}$, but a rigorous proof remains open for every $q$ not a power of $2$.

## References

- A. D. Wyner and J. Ziv, "A theorem on the entropy of certain binary sequences and applications — Part I," *IEEE Trans. Inf. Theory*, 19(6):769–772, 1973.
- H. S. Witsenhausen, "Entropy inequalities for discrete channels," *IEEE Trans. Inf. Theory*, 20(5):610–616, 1974.
- N. Chayat and S. Shamai (Shitz), "Extension of an entropy property for binary input memoryless symmetric channels," *IEEE Trans. Inf. Theory*, 35(5):1077–1079, 1989.
- V. Jog and V. Anantharam, "The entropy power inequality and Mrs. Gerber's lemma for abelian groups of order $2^n$," *IEEE Trans. Inf. Theory*, 60(7):3773–3786, 2014.
- C. Nair and A. El Gamal, "The capacity region of a class of three-receiver broadcast channels with degraded message sets," *IEEE Trans. Inf. Theory*, 55(10):4479–4493, 2009.
