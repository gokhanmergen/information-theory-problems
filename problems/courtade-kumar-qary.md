---
id: courtade-kumar-qary
title: The q-ary Courtade–Kumar Most-Informative-Function Conjecture
status: open
category: entropy-inequalities
posed_by: Thomas A. Courtade and Gowtham R. Kumar
posed_year: 2014
tags: [entropy-inequalities, q-ary-functions, noise-stability, hypercontractivity]
lean_module: InfoTheory.Problems.CourtadeKumarQary
lean_file: lean/InfoTheory/Problems/CourtadeKumarQary.lean
---

## Statement

Fix an alphabet size $q \ge 2$, blocklength $n \ge 1$, and error probability $\alpha \in (0, 1 - 1/q)$. Let $X = (X_1, \dots, X_n) \sim \mathrm{Uniform}(\{0, \dots, q-1\}^n)$, and let $Y = (Y_1, \dots, Y_n)$ be obtained by passing $X$ independently through the $q$-ary symmetric channel $\mathsf{QSC}(q, \alpha)$ with transition probabilities
$$W(y \mid x) = \begin{cases} 1 - \alpha & \text{if } y = x, \\ \dfrac{\alpha}{q - 1} & \text{if } y \ne x. \end{cases}$$

**Conjecture ($q$-ary Courtade–Kumar Conjecture).** For every function $f : \{0, \dots, q-1\}^n \to \{0, \dots, q-1\}$,
$$I(f(X); Y) \;\le\; \log_2 q - h(\alpha) - \alpha \log_2(q - 1),$$
where $h(\alpha) = -\alpha \log_2 \alpha - (1-\alpha)\log_2(1-\alpha)$ is the binary entropy function. Equality is achieved by any single-coordinate ("dictator") function $f(x) = \pi(x_i)$ for a bijection $\pi$ of $\{0, \dots, q-1\}$.

## Background

In their 2014 paper introducing the most-informative Boolean function conjecture for $q = 2$, Courtade and Kumar also asked whether dictator optimality extends to larger alphabets $q \ge 3$ under the $q$-ary symmetric channel $\mathsf{QSC}(q, \alpha)$, and more generally to functions $f : \mathcal{X}^n \to \mathcal{U}$ of fixed output cardinality. The $q$-ary case is strictly harder than the binary case: not only does it contain the binary Courtade–Kumar conjecture at $q = 2$, but the hypercontractive parameters of $\mathsf{QSC}(q, \alpha)$ degrade asymmetrically with $q$ (the log-Sobolev constant depends on $q$ differently from the Poincaré constant), breaking naive generalizations of binary Fourier-analytic arguments.

## What is known

- **Binary case ($q = 2$ — RESOLVED September 2026):** Proved in full (including for unbalanced Boolean functions) by Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, and Woodruff (`arXiv:2609.24931`, with end-to-end Lean 4 formalization) as well as independently by Ky–Tran (`arXiv:2609.24184`), Mahdavifar–Beirami (`arXiv:2609.26444`), and Kramer–Sağlam (`arXiv:2611.05430`). The $q \ge 3$ conjecture under $\mathsf{QSC}(q, \alpha)$ remains open. (Note: Mahdavifar–Beirami 2026 also exhibited counterexamples for *multi-bit* outputs on the binary symmetric channel for $k \ge 8$, which is distinct from the $q$-ary channel $\mathsf{QSC}(q, \alpha)$ formalized here.)
- **High-noise regime for general $q$:** Pichler, Piantanida, and Matz (2018) and subsequent hypercontractive analyses (e.g., via strong data processing inequalities for $\mathsf{QSC}(q, \alpha)$) showed that the conjecture holds when $\alpha$ is sufficiently close to $1 - 1/q$ (small correlation $\rho = 1 - \frac{q}{q-1}\alpha$), though the known threshold shrinks with $q$.
- **Unrestricted output cardinality vs. $q$-ary output:** When $f : \{0,1\}^n \to \{0, \dots, M-1\}$ has $M > 2$ outputs on the binary hypercube, the natural lexicographic/subcube generalization is subtle and closely linked to the edge-isoperimetric inequality and the Anantharam–Gohari–Kamath–Nair hypercontractivity framework.
- **Balanced vs. unbalanced $q$-ary functions:** For $q \ge 3$, even the balanced case (where $f(X)$ is uniform on $\{0, \dots, q-1\}$) remains open for general $\alpha \in (0, 1 - 1/q)$ and $n \ge 2$.

## Formal statement and certificate

Adversarial audit (2026-11-27): the Lean `Statement` is faithful.
- **Bearing of the 2026 binary resolution.** The `q = 2` slice of the Statement is exactly the
  binary Courtade–Kumar conjecture. `QSC(2, α) = BSC(α)`, and the bound becomes `1 - h(α)`; both
  facts are certified. So arXiv:2609.24931 and the independent proofs settle `q = 2` only.
- **The `q ≥ 3` case remains open.** None of the 2026 papers treats `QSC(q, α)` with `q ≥ 3`.
  Mahdavifar–Beirami's multi-bit-output counterexamples on the binary cube are a different setting.
- **Numerical check (2026-11-27).** No counterexample was found:
  - exhaustive search over all `f` for `(q, n) = (3, 2)`;
  - hill-climbing from random starts for `(4, 2)`, `(3, 3)` and `(5, 2)`;
  - `α ∈ {0.05, 0.2, 0.4, ≈0.9(1-1/q)}`.

  The dictator was always optimal. For example, at `q = 4`, the "two-bit" function
  `(x₁ mod 2, x₂ mod 2)` is strictly worse.

Certificate `lean/InfoTheory/Known/Certificates/CourtadeKumarQary.lean` proves the following:
- `0 ≤ I(f(X); Y) ≤ log₂ q`.
- The conjectured bound is non-negative for all `α ∈ [0, 1]`.
- The `q = 2` reduction to the binary bound.

## References

- T. A. Courtade and G. R. Kumar, "Which Boolean functions maximize mutual information on noisy inputs?" *IEEE Trans. Inf. Theory*, 60(8):4515–4525, 2014.
- A. Samorodnitsky, "On the entropy of a noisy function," *IEEE Trans. Inf. Theory*, 62(10):5446–5464, 2016.
- G. Pichler, P. Piantanida, and G. Matz, "Dictator functions maximize mutual information," *Ann. Appl. Probab.*, 28(5):3094–3101, 2018.
- A. Anantharam, A. Gohari, S. Kamath, and C. Nair, "On hypercontractivity and a data processing inequality," *Proc. IEEE ISIT*, 2014.
- L. Yu, "Local optimality of dictator functions with applications to Courtade–Kumar and Li–Médard conjectures," arXiv:2410.10147, 2024.
