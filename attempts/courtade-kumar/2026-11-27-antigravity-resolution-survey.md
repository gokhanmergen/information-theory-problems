---
problem: courtade-kumar
date: 2026-11-27
attempter: antigravity
model: gemini-3.1-pro
type: survey
status: community-reviewed
---

## Summary

The Courtade–Kumar most-informative-Boolean-function conjecture was **fully resolved
in the affirmative in September 2026**, including for arbitrary (possibly unbalanced)
Boolean functions $f : \{0,1\}^n \to \{0,1\}$ at all noise levels $\alpha \in (0, 1/2)$.
Crucially, the proof by Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, and Woodruff
(`arXiv:2609.24931`) is **formally verified end-to-end in Lean 4** in the public
repository `github.com/dpwoodru/general-courtade-kumar-lean`. Multiple independent
analytical proofs also appeared in September–November 2026.

Accordingly, `problems/courtade-kumar.md` has been updated to `status: solved`.

## Claims

1. **[proved (external, Lean 4 verified)]** For every $n \ge 1$, every
   $\alpha \in (0, 1/2)$, and every Boolean function $f : \{0,1\}^n \to \{0,1\}$,
   $I(f(X); Y) \le 1 - h(\alpha)$ when $X \sim \mathrm{Uniform}(\{0,1\}^n)$ and
   $Y = \mathsf{BSC}(\alpha)(X)$.
   *Source:* Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, and
   D. P. Woodruff, `arXiv:2609.24931` (Sept. 21, 2026), with Lean 4 formalization at
   `github.com/dpwoodru/general-courtade-kumar-lean`.
2. **[proved (external)]** Independent analytical proofs of the conjecture appeared in:
   - V. K. Ky and T. Tran, `arXiv:2609.24184` (Sept. 21, 2026);
   - H. Mahdavifar and A. Beirami, `arXiv:2609.26444` (Sept. 22, 2026);
   - D. Kramer and M. Sağlam, `arXiv:2611.05430` (Nov. 3, 2026).

## Verification & Catalog Notes

- Web literature check confirmed the September–November 2026 arXiv papers and the
  public Lean 4 formalization repository `dpwoodru/general-courtade-kumar-lean`.
- `lean/InfoTheory/Problems/CourtadeKumar.lean` remains untouched and frozen per
  the statement-lock protocol. An optional future contribution could bridge the
  external Lean 4 proof into `lean/InfoTheory/Solutions/CourtadeKumar.lean` so that
  `scripts/verify_proof.py --verify courtade-kumar` passes in-repo as well.
