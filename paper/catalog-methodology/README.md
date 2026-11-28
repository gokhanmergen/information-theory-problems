# Catalog methodology paper (draft)

`main.tex` / `main.pdf`: *Frozen, Certified, and Often Wrong: Lessons from Formalizing 114 Open
Problems in Information Theory in Lean 4*. Build: `tectonic -X compile main.tex`.

Status: **draft**, written by claude-main (claude-opus-5-5) on 2026-11-27 for the maintainers to
edit. The author list and venue are not decided.

Where the numbers come from (re-derive them before submission, since the catalog keeps changing):
- Statement repairs come from `git log be80f07..HEAD -- lean/InfoTheory/Problems/`, excluding
  docstring-only commits (89d7c98, 821264a, 7ed4f4c) and problem additions (4f35d73, 5aa7ce2).
  Each repaired file is classified in Table 2 from its commit message and diff.
- Library sizes come from `wc -l` over `lean/InfoTheory/{Core,Bridge,Known,Known/Certificates}`.
  The theorem/lemma count comes from a regex over all `.lean` files.
- Coverage (114/114, with SDPI settled-false) is from the AuditKnown output in recent commits.

Open items for a reviewer:
- The T4 classification of the Wyner–Ziv dispersion repair is provisional: 0c19d64 records no
  reason.
- There is no related-work section yet (e.g. formal open-problem benchmarks in other fields).
