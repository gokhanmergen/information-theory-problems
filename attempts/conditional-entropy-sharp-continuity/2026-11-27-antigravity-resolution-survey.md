---
problem: conditional-entropy-sharp-continuity
date: 2026-11-27
attempter: antigravity
model: gemini-3.1-pro
type: survey
status: community-reviewed
---

## Summary

The exact sharp uniform continuity bound for **quantum conditional entropy** formalized in
`InfoTheory.Problems.ConditionalEntropySharpContinuity` — namely
$$|S(A \mid B)_\rho - S(A \mid B)_\sigma| \le \varepsilon \log_2(d_A^2 - 1) + h(\varepsilon)$$
for $\varepsilon = \frac{1}{2}\|\rho_{AB} - \sigma_{AB}\|_1 \le 1 - 1/d_A^2$ — was
**proved in July 2026** (revised September 2026) by Mario Berta, Pablo Costa Rico,
Gereon Kossmann, Ludovico Lami, and Julius A. Zeiss (`arXiv:2607.24687`).

Subproblem 2 of `problems/conditional-entropy-sharp-continuity.md` (sharp uniform
continuity bounds for classical and quantum mutual information and conditional mutual
information) remains open. Accordingly, `problems/conditional-entropy-sharp-continuity.md`
now carries `formal_status: claimed-resolved` while keeping `status: partially-solved`.

## Claims

1. **[proved (external preprint)]** For all bipartite quantum states
   $\rho_{AB}, \sigma_{AB} \in \mathcal{D}(\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B})$
   at trace distance $\varepsilon = \frac{1}{2}\|\rho_{AB} - \sigma_{AB}\|_1 \le 1 - 1/d_A^2$,
   $|S(A \mid B)_\rho - S(A \mid B)_\sigma| \le \varepsilon \log_2(d_A^2 - 1) + h(\varepsilon)$,
   and $\le 2\log_2 d_A$ for $\varepsilon > 1 - 1/d_A^2$, with tightness for all $\varepsilon \in [0, 1]$
   when $d_B \ge d_A$.
   *Source:* M. Berta, P. Costa Rico, G. Kossmann, L. Lami, and J. A. Zeiss,
   "Sharp continuity of quantum conditional entropy," `arXiv:2607.24687` (July 2026, rev. Sept. 2026).

## Catalog Recommendation

Consider either leaving `Statement` frozen with `formal_status: claimed-resolved` until
peer review / Lean formalization, or re-scoping the open problem's Lean `Statement` to
subproblem 2 (sharp continuity of classical/quantum mutual information or CMI).
