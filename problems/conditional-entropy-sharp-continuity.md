---
id: conditional-entropy-sharp-continuity
title: Sharp Uniform Continuity Bounds for Conditional Entropy
status: partially-solved
formal_status: claimed-resolved
formal_status_note: Formalized quantum conditional entropy bound proved by Berta–Costa Rico–Kossmann–Lami–Zeiss (arXiv:2607.24687, July/Sept 2026); MI/CMI continuity remains open.
category: statistical-info-theory
posed_by: Zhen Zhang; Andreas Winter; Mohammad A. Alhejji and Graeme Smith
posed_year: 2007
tags: [continuity-bounds, conditional-entropy, total-variation, trace-distance, quantum-entropy]
lean_module: InfoTheory.Problems.ConditionalEntropySharpContinuity
lean_file: lean/InfoTheory/Problems/ConditionalEntropySharpContinuity.lean
---

## Statement

Let $P_{XY}, Q_{XY}$ be discrete joint distributions on finite alphabets $\mathcal{X} \times \mathcal{Y}$ at total variation distance $\varepsilon = \mathrm{TV}(P_{XY}, Q_{XY})$, and more generally let $\rho_{AB}, \sigma_{AB} \in \mathcal{D}(\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B})$ be bipartite quantum states at trace distance $\varepsilon = \frac{1}{2} \|\rho_{AB} - \sigma_{AB}\|_1$.

- **Classical conditional entropy (resolved by Alhejji–Smith 2020):** For all discrete joint distributions with $\varepsilon \le 1 - 1/|\mathcal{X}|$,
  $$
  |H(X \mid Y)_P - H(X \mid Y)_Q| \le \varepsilon \log_2(|\mathcal{X}| - 1) + h(\varepsilon),
  $$
  matching Zhang's (2007) sharp unconditional Fannes–Audenaert bound.
- **Remaining open problems (quantum conditional entropy — formalized in Lean — and conditional mutual information):**
  1. Prove (or refute) the exact sharp continuity bound for **quantum conditional entropy** $S(A \mid B)_\rho = S(\rho_{AB}) - S(\rho_B)$ conjectured by Wilde (2020) and Alhejji–Smith (2020): for all $d_A \ge 2, d_B \ge 1$ and $\varepsilon = \frac{1}{2}\|\rho_{AB} - \sigma_{AB}\|_1 \le 1 - 1/d_A^2$,
  $$
  |S(A \mid B)_\rho - S(A \mid B)_\sigma| \le \varepsilon \log_2(d_A^2 - 1) + h(\varepsilon),
  $$
  which is attained with equality between a maximally entangled state $|\Phi_{d_A}\rangle$ and its isotropic depolarization $(1 - \varepsilon)|\Phi_{d_A}\rangle\langle\Phi_{d_A}| + \varepsilon \frac{I - |\Phi_{d_A}\rangle\langle\Phi_{d_A}|}{d_A^2 - 1}$.
  2. Determine the exact sharp continuity bounds for classical and quantum mutual information $|I(X; Y)_P - I(X; Y)_Q|$ and conditional mutual information $|I(X; Y \mid Z)_P - I(X; Y \mid Z)_Q|$ as functions of $\varepsilon$.

## Background

Tight uniform continuity bounds (Fannes–Audenaert–Zhang inequalities) are indispensable tools throughout classical and quantum Shannon theory, powering asymptotic equipartition, converse proofs, strong-secrecy upgrades, and decoupling arguments. Zhang (2007) and Audenaert (2007) independently determined the exact sharp continuity bound for unconditional Shannon and von Neumann entropy.

For *conditional* entropy, Alicki and Fannes (2004) and Winter (2016) established tight dimension-independent-in-$B$ bounds via the coupling/meta-lemma method, losing an extra factor in the binary entropy term $(1+\varepsilon)h(\frac{\varepsilon}{1+\varepsilon})$. Alhejji and Smith (2020) closed the classical conditional entropy problem completely using optimal transport / maximal couplings, leaving the fully quantum conditional entropy bound and sharp continuity of (conditional) mutual information as the active open frontier.

## What is known

- **Unconditional entropy (solved):** Zhang (2007) (classical) and Audenaert (2007) (quantum) proved $|S(\rho) - S(\sigma)| \le \varepsilon \log_2(d - 1) + h(\varepsilon)$ for $\varepsilon \le 1 - 1/d$, which is achieved with equality.
- **Classical conditional entropy (solved):** Alhejji and Smith (2020) proved the exact sharp bound $|H(X \mid Y)_P - H(X \mid Y)_Q| \le \varepsilon \log_2(|\mathcal{X}| - 1) + h(\varepsilon)$ for all $\varepsilon \le 1 - 1/|\mathcal{X}|$ (and $\log_2 |\mathcal{X}|$ for $\varepsilon > 1 - 1/|\mathcal{X}|$), completely resolving the classical conditional entropy case.
- **Classical-quantum and fully quantum conditional entropy (RESOLVED in preprint, July/Sept 2026):**
  - **Berta, Costa Rico, Kossmann, Lami, and Zeiss** (`arXiv:2607.24687`, July 2026, rev. Sept. 2026) proved the exact sharp uniform continuity bound for quantum conditional entropy: $|S(A \mid B)_\rho - S(A \mid B)_\sigma| \le \varepsilon \log_2(d_A^2 - 1) + h(\varepsilon)$ for $\varepsilon \le 1 - 1/d_A^2$ (and $2\log_2 d_A$ for $\varepsilon > 1 - 1/d_A^2$), settling the exact statement formalized in `InfoTheory.Problems.ConditionalEntropySharpContinuity`. (The authors note proof concepts were developed with assistance from ChatGPT 5.6 Sol, building on Alhejji–Smith.)
  - Earlier milestones: Winter (2016) proved $|S(A \mid B)_\rho - S(A \mid B)_\sigma| \le 2\varepsilon \log_2 d_A + (1 + \varepsilon) h\!\left(\frac{\varepsilon}{1+\varepsilon}\right)$ for general bipartite quantum states (and $\varepsilon \log_2 d_A + (1 + \varepsilon) h\!\left(\frac{\varepsilon}{1+\varepsilon}\right)$ for classical-quantum states); Wilde (2020) and Shirokov (2023) refined bounds for quantum conditional entropy and conditional mutual information.
  - **Still open:** exact sharp uniform continuity bounds for classical and quantum mutual information $I(X; Y)$ and conditional mutual information $I(X; Y \mid Z)$ (subproblem 2 above).

## References

- M. Berta, P. Costa Rico, G. Kossmann, L. Lami, and J. A. Zeiss, "Sharp continuity of quantum conditional entropy," arXiv:2607.24687, July 2026 (rev. Sept. 2026).

- M. Fannes, "A continuity property of the entropy density for spin lattice systems," *Commun. Math. Phys.* **31**, 291–294 (1973).
- R. Alicki and M. Fannes, "Continuity of quantum conditional information," *J. Phys. A: Math. Gen.* **37**, L55–L57 (2004).
- K. M. R. Audenaert, "A sharp continuity estimate for the von Neumann entropy," *J. Phys. A: Math. Theor.* **40**, 8127–8136 (2007).
- Z. Zhang, "Estimating mutual information via Kolmogorov distance," *IEEE Trans. Inf. Theory* **53**(9), 3280–3282 (2007).
- A. Winter, "Tight uniform continuity bounds for quantum entropies: Conditional entropy, relative entropy distance and energy constraints," *Commun. Math. Phys.* **347**, 291–313 (2016).
- M. A. Alhejji and G. Smith, "A tight uniform continuity bound for equivocation," *IEEE Trans. Inf. Theory* **66**(11), 6701–6706 (2020).
- M. M. Wilde, "Optimal uniform continuity bound for conditional entropy of classical-quantum states," *Quantum Inf. Process.* **19**, 61 (2020).
- M. E. Shirokov, "Close-to-optimal continuity bound for the von Neumann entropy and other quasi-classical applications of the Alicki–Fannes–Winter technique," *Lett. Math. Phys.* **113**, 121 (2023).
