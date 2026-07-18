# Referee Report on "The Most-Informative-Boolean-Function Conjecture Holds for $n = 4$"

## Summary

This paper presents a complete, computer-assisted mathematical proof of the Courtade–Kumar conjecture for $n = 4$. By partitioning the noise range $\alpha \in (0, 0.5)$ into four regimes, the authors verify the inequality $I(f(X); Y) \leq 1 - h(\alpha)$ for all $222$ NPN equivalence classes. The boundary regimes are checked analytically via low-noise and high-noise lemmas verified in exact rational arithmetic, while the middle regimes are certified using outward-rounded interval arithmetic.

As an adversarial reviewer, we have audited the mathematical statements, code logic, and references. The proof is sound, reproducible, and mathematically rigorous. Below are the key points a journal referee would flag for improvement.

---

## 1. Mathematical and Algorithmic Clarity

* **Interval Arithmetic Rigor**: In Section 6, the manuscript states that `mpmath.iv` (90-bit precision) is used for the middle range. A referee would ask for a brief sentence clarifying how the infimum of the interval enclosure is guaranteed to be strictly positive despite floating-point representations. Specifying that `mpmath.iv` uses outward-rounded interval arithmetic to produce rigorous mathematical enclosures of the polynomials is essential.
* **Low-Noise Lemma Bounds**: In the proof of Lemma 1, step (ii) uses $h(b_y \beta) \geq b_y \beta [t - \log_2 b_y]$ where $t = \log_2(1/\alpha)$. Since $\beta = \alpha(1-\alpha)^3$ and $\beta \leq \alpha$, this inequality relies on the fact that $h(u) \geq u \log_2(1/u)$ for $u \in [0, 0.5]$. A referee would appreciate a brief explicit mention of the domain constraint $b_y \beta \le 1/2$ (which is satisfied since $4\alpha \le 4\times 10^{-3} < 1/2$) to justify the monotonicity and bound direction.
* **High-Noise Lemma Taylor Expansion**: In Lemma 2, the scalar inequality $(1+\varepsilon)\ln(1+\varepsilon) \leq \varepsilon + \frac{\varepsilon^2}{2} + \frac{2}{3}|\varepsilon|^3$ is established for $|\varepsilon| \leq 1/2$. The derivation for $\varepsilon \in [-1/2, 0)$ bounds the remainder using a geometric series:
  $$\sum_{k=3}^\infty \frac{|\varepsilon|^k}{k(k-1)} \leq \frac{|\varepsilon|^3}{6} \sum_{j=0}^\infty |\varepsilon|^j \leq \frac{|\varepsilon|^3}{3}.$$
  This is correct, but since it leads to the term $\frac{4}{3}\varepsilon_{\max}$ in the main inequality, the transition from natural log ($\ln$) to binary log ($\log_2$) should be explicitly highlighted to ensure the reader can easily follow the cancellation of the $\ln 2$ factors.

---

## 2. Terminology and Notation

* **Dictators vs. Anti-Dictators**: In Theorem 1 and the abstract, the term "anti-dictator" is used. In standard Boolean function literature, dictators and anti-dictators are often grouped together as "dictator functions" (sometimes with a note that output negation is allowed). Keeping this clear and standard is recommended.
* **Boundary Degree $b_y$**: In Lemma 1, $b_y$ is defined as the number of Hamming neighbors $x$ of $y$ with $f(x) \neq f(y)$. This is also known as the local sensitivity of $f$ at $y$ or the local boundary degree. Adding a brief parenthetical pointing out this connection would improve readability.
* **Consistency of Indicator Notation**: The paper uses $\ind{f}$ in some places (e.g., Lemma 2) and $1_f$ in other attempt files. Ensure $\ind{f}$ is used consistently throughout the LaTeX source.

---

## 3. Reference and Attribution Check

* **Javanmard-Woodruff (2026)**: The citation of Javanmard & Woodruff (arXiv:2601.09679) is accurate. They indeed proved the generalized coordinate-wise mutual information bound, resolving an open question posed by Courtade & Kumar, and made significant progress in the high-noise regime.
* **Yu (2024)**: The citation of Lei Yu (arXiv:2410.10147) is correct. Yu proved local optimality of dictators for $\rho \in [0, 0.914]$ for balanced functions, and this paper has been accepted by the *Annals of Applied Probability*.
* **Harper (1964)**: The reference to Harper's classic paper on hypercube edge-isoperimetry is correct and correctly attributed.

---

## 4. Minor Typos and Suggestions

* **Self-Contained Closeness**: Emphasize more strongly in the abstract/introduction that because the high-noise lemma (Lemma 2) checks all 220 non-dictator classes explicitly and passes, this paper provides the **first completely self-contained** proof of the $n=4$ case that does not rely on any non-explicit external theorems. This is a major selling point.
