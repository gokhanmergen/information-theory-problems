---
id: li-medard-conjecture
title: The Li–Médard Conjecture on Noisy Boolean Functions
status: open
category: entropy-inequalities
posed_by: Jiange Li and Muriel Médard
posed_year: 2018
tags: [entropy-inequalities, boolean-functions, noise-stability, discrete-fourier]
lean_module: InfoTheory.Problems.LiMedardConjecture
lean_file: lean/InfoTheory/Problems/LiMedardConjecture.lean
formal_status: claimed-resolved
formal_status_note: "Lei Yu, arXiv:2611.00868 (Nov 2026), reported by gemini-neon; unrefereed, not yet checked here"
---

## Statement

Let $X \sim \mathrm{Uniform}(\{0,1\}^n)$ and let $Y$ be the output of the memoryless binary symmetric channel $\mathsf{BSC}(\alpha)^n$ with crossover probability $\alpha \in (0, 1/2)$ (equivalently noise correlation $\rho = 1 - 2\alpha \in (0, 1)$). For a Boolean function $f : \{0,1\}^n \to \{0,1\}$, let $T_\rho f : \{0,1\}^n \to [0,1]$ denote the Bonami–Beckner noise operator:
$$(T_\rho f)(y) = \mathbb{E}[f(X) \mid Y = y] = \sum_{x \in \{0,1\}^n} (1-\alpha)^{n - d_H(x,y)} \alpha^{d_H(x,y)} f(x).$$

**Conjecture (Li–Médard, 2018).** For every $n \ge 1$, every crossover probability $\alpha \in (0, 1/2)$, every exponent $q \in (1, 2]$, and every balanced Boolean function $f : \{0,1\}^n \to \{0,1\}$ (meaning $|\{x : f(x) = 1\}| = 2^{n-1}$),
$$\mathbb{E}\!\left[(T_\rho f(Y))^q\right] \;\le\; \frac{\alpha^q + (1 - \alpha)^q}{2},$$
with equality achieved by dictator functions $f(x) = x_i$ (and their complements $f(x) = 1 - x_i$).

## Background

The Li–Médard conjecture sits at the heart of the modern program linking information theory, noise stability, and extremal analysis of Boolean functions. It generalizes the $q = 2$ noise-stability inequality $\mathbb{E}[(T_\rho f)^2] \le \frac{1}{4}(1 + \rho^2)$ — which follows immediately from Parseval's identity — to all exponents $q \in (1, 2]$. Differentiating both sides at $q = 1^+$ recovers the balanced case of the Courtade–Kumar most-informative Boolean function conjecture:
$$I(f(X); Y) = 1 - \mathbb{E}[h(T_\rho f(Y))] \;\le\; 1 - h(\alpha).$$
More broadly, the inequality asks whether dictator functions maximize $q$-th moments of posterior beliefs $(T_\rho f)(Y)$ over the hypercube, connecting directly to $q$-player non-interactive correlation distillation (NICD) and $\Phi$-stability for convex test functions $\Phi$.

## What is known

- **Case $q = 2$:** Holds unconditionally for all $n \ge 1$ and all $\alpha \in (0, 1/2)$ by Fourier expansion (Parseval's identity), since $\mathbb{E}[(T_\rho f)^2] = \frac{1}{4} + \sum_{S \ne \emptyset} \rho^{2|S|} \hat{f}(S)^2 \le \frac{1}{4} + \frac{1}{4}\rho^2 = \frac{1}{2}(\alpha^2 + (1-\alpha)^2)$.
- **Failure for large $q$:** For sufficiently large $q$ (not restricted to $q \in (1, 2]$), dictators are *not* global maximizers: for instance, the 3-bit majority function $\mathrm{Maj}_3$ attains $(T_\rho \mathrm{Maj}_3)(1,1,1) = \frac{1}{2} + \frac{3}{4}\rho - \frac{1}{4}\rho^3 > \frac{1}{2} + \frac{1}{2}\rho = 1 - \alpha$, which dominates the dictator moment $\frac{1}{2}(\alpha^q + (1-\alpha)^q)$ once $q$ is large enough.
- **Equivalence to Courtade–Kumar (Barnes–Özgür, 2020):** Barnes and Özgür proved that a symmetrized formulation of the Li–Médard conjecture (for arbitrary, not necessarily balanced Boolean functions) is equivalent to the full Courtade–Kumar conjecture.
- **High-noise regime:** Following Samorodnitsky's (2016) breakthrough on noisy Boolean functions, the conjecture holds in a neighborhood of $\alpha = 1/2$ (small $\rho$).
- **Local optimality and balanced progress (Yu, 2024):** Lei Yu established general local optimality of dictator functions for $\Phi$-stability among balanced Boolean functions and obtained substantial global noise-parameter ranges for both the Courtade–Kumar and Li–Médard conjectures.
- **General $q \in (1, 2)$ and moderate/low noise:** The full conjecture over all $n \ge 1$, $\alpha \in (0, 1/2)$, and $q \in (1, 2]$ remains open.

## References

- J. Li and M. Médard, "Boolean functions: Noise stability, non-interactive correlation distillation, and mutual information," *Proc. IEEE Int. Symp. Information Theory (ISIT)*, 2018 (arXiv:1801.03344).
- T. A. Courtade and G. R. Kumar, "Which Boolean functions maximize mutual information on noisy inputs?" *IEEE Trans. Inf. Theory*, 60(8):4515–4525, 2014.
- A. Samorodnitsky, "On the entropy of a noisy function," *IEEE Trans. Inf. Theory*, 62(10):5446–5464, 2016.
- L. Barnes and A. Özgür, "The Courtade–Kumar most informative Boolean function conjecture and a symmetrized Li–Médard conjecture are equivalent," *Proc. IEEE ISIT*, 2020 (arXiv:2004.01277).
- L. Yu, "Local optimality of dictator functions with applications to Courtade–Kumar and Li–Médard conjectures," arXiv:2410.10147, 2024.
