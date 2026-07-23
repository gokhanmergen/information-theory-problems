---
problem: courtade-kumar
date: 2026-07-18
attempter: claude
model: claude-fable-5
type: survey
status: community-reviewed
---

## Summary

A literature check (web search, 2026-07-18) executing the protocol's novelty-check rule
for the two computational attempts in this directory, and updating the problem file's
"What is known" section. Headlines: the conjecture **remains open** (confirmed by
papers through January 2026); two claimed proofs on arXiv were **withdrawn** with
acknowledged flaws; the *local* optimality of dictators — the analytic counterpart of
the single-flip runner-up structure found numerically in the `n4`/`n5` attempts — is
**a general theorem of Lei Yu (2024)**; Yu also proves the global balanced
Courtade–Kumar conjecture for a large correlation range. Two recent frameworks
(a differential-equation reformulation, and coordinate-wise MI bounds) mark the
current frontier.

## Approach

Targeted web searches on the conjecture's status, claimed proofs, small-$n$
verification, and 2024–2026 developments; primary-source checks of arXiv abstract
pages (withdrawal notices, version histories). Limitation stated below.

## Claims

1. **[proved]** (by inspection of arXiv records) Two claimed proofs of the full
   conjecture were withdrawn by their authors: Kesal, arXiv:1511.01828 (v3 2017,
   "withdrawn due to a serious flaw in the proof") and Sârbu, arXiv:1604.05113
   (v2 2017, "withdrawn due to a critical error in the way the equation of the
   mutual information … was applied"). The conjecture is treated as open by papers
   dated January 2025 through January 2026.

2. **[proved]** (published result, not verified line-by-line here) Yu,
   *Local Optimality of Dictator Functions with Applications to Courtade–Kumar and
   Li–Médard Conjectures* (arXiv:2410.10147, 2024, rev. 2026), proves dictators are
   locally optimal among balanced Boolean functions for $\Phi$-stability. This local
   theorem is distinct from the paper's computer-assisted global result: for
   symmetric $q$-stability at $q=1$, dictators maximize over all balanced Boolean
   functions when $\rho=1-2\alpha\in[0,0.914]$, confirming the balanced
   Courtade–Kumar conjecture in that range. **Consequence for this attempt log:**
   the single-flip runner-up structure observed exhaustively at $n = 4, 5$ is the
   finite-$n$, global-enumeration counterpart of a known local theorem; the
   *observation* is qualitatively anticipated, while the exact runner-up
   identification and gap values appear to be additional detail.

3. **[proved]** (published results) Current frontier, with sources:
   - Barnes–Özgür (arXiv:2004.01277, ISIT 2020): the conjecture is *equivalent* to a
     symmetrized Li–Médard conjecture.
   - Chen–Gohari–Nair (arXiv:2502.10019, 2025): a differential-equation
     reformulation reducing the balanced case to a finite-dimensional functional
     inequality, established modulo four explicit numerically-supported
     inequalities.
   - Javanmard–Woodruff (arXiv:2601.09679, Jan 2026): the coordinate-wise bound
     $\sum_i I(f(X);Y_i) \leq 1 - h(\alpha)$ extended from balanced to all Boolean
     functions, plus an optimal $O(\lambda^2)$ high-noise entropy expansion,
     enlarging the proven noise range.
   - High-noise thresholds have improved steadily since Samorodnitsky
     (arXiv:1510.08656); proofs for structured classes exist (e.g.
     arXiv:1702.03953).

4. **[heuristic]** Novelty assessment of the `n4`/`n5` exhaustive attempts: this
   search did not locate a documented, code-published full-space enumeration at
   $n = 5$ (nor a traceable source for the folklore claim "verified for $n \leq 7$",
   which cannot mean literal exhaustion — $2^{2^7}$ functions). No priority is
   claimed; absence of evidence in a web search is weak evidence of absence.

## Details

Search queries and the arXiv records consulted are listed in the References. The
problem file `problems/courtade-kumar.md` is updated in this same commit to
incorporate Claims 1–3 with citations.

## Verification

Withdrawal notices and version histories in Claims 1 read directly from arXiv
abstract pages. Claims 2–3 summarize abstracts; the underlying proofs were **not**
checked line-by-line — a reviewer confirming the summaries against the papers can
move this attempt to `community-reviewed`.

**Review (claude-fable-5 reviewer, 2026-07-23, same-family — flag for external
re-review):** every citation re-checked against the arXiv abstract pages on
2026-07-23. (a) Claim 1 verbatim-correct: Kesal arXiv:1511.01828 v3 (Oct 2017)
"withdrawn due to a serious flaw in the proof"; Sârbu arXiv:1604.05113 v2
(Jan 2017) "withdrawn due to a critical error in the way the equation of the
mutual information that involved conditional entropies was applied". (b) Claim 2
matches Yu arXiv:2410.10147 (v5, Apr 2026): local optimality of dictators for
$\Phi$-stability among balanced functions, plus the balanced conjecture for
$\rho \in [0, 0.914]$ (computer-assisted component confirmed). (c) Claim 3
matches the abstracts of arXiv:2004.01277 (which says "essentially equivalent" —
a hair weaker than this file's "equivalent"; the ISIT 2020 venue is not stated
on the abs page), arXiv:2502.10019 (four explicit numerically-supported
inequalities, balanced case), and arXiv:2601.09679 (coordinate-wise bound for
*all* Boolean functions; optimal $O(\lambda^2)$ expansion, $\lambda=(1-2\alpha)^2$);
arXiv:1702.03953 (structured classes) confirmed — it is by Sârbu, the same
author as the withdrawn full-proof claim. (d) Claim 4 and the Dead-ends item
were subsequently sharpened by `2026-07-18-gpt-5-codex-n4-referee-audit.md`:
the 2014 TIT paper's own $n \leq 7$ check enumerated the *compressed* family
$S_n$ (Sec. II-B) with a separate $0.001$-grid test (Sec. II-D) — consistent
with this file's inference that "verified for $n \leq 7$" was not literal
exhaustion. No factual errors found; claims-as-stated stand. Same-family
review (claude reviewing claude): flag for external re-review.

## Dead ends

- The original Kumar–Courtade ISIT 2013 paper's numerical-evidence section could not
  be read through the tooling used (PDF text extraction failed), so the exact scope
  of the authors' own numerics (which $n$, which function families) remains
  unrecorded here. Worth one manual look.

## References

- P. Kumar and T. A. Courtade, "Which Boolean functions are most informative?"
  ISIT 2013; arXiv:1302.2512.
- M. Kesal, arXiv:1511.01828 (withdrawn 2017).
- S. Sârbu, arXiv:1604.05113 (withdrawn 2017).
- A. Samorodnitsky, "The 'most informative Boolean function' conjecture holds for
  high noise," arXiv:1510.08656.
- L. Barnes and A. Özgür, "The Courtade–Kumar most informative Boolean function
  conjecture and a symmetrized Li–Médard conjecture are equivalent,"
  arXiv:2004.01277, ISIT 2020.
- L. Yu, "Local optimality of dictator functions with applications to
  Courtade–Kumar and Li–Médard conjectures," arXiv:2410.10147, 2024 (rev. 2026).
- Z. Chen, A. Gohari, and C. Nair, "A differential equation approach to the
  most-informative Boolean function conjecture," arXiv:2502.10019, 2025.
- A. Javanmard and D. P. Woodruff, "Progress on the Courtade–Kumar conjecture:
  optimal high-noise entropy bounds and generalized coordinate-wise mutual
  information," arXiv:2601.09679, 2026.
- Prior attempts in this directory: `2026-07-17-claude-fable-5-n4-exhaustive.md`,
  `2026-07-17-claude-fable-5-n5-exhaustive.md`.
