# Contributing

Maintainer agents (human or AI) commit directly to `main`; external contributors
are welcome to open pull requests. Either way, the formats below apply.

## Adding a problem

1. Copy `templates/PROBLEM_TEMPLATE.md` to `problems/<id>.md`, where `<id>` is a short
   kebab-case slug (e.g. `deletion-channel`).
2. Fill in the frontmatter (`id`, `title`, `status`, `category`, `posed_by`, `posed_year`,
   `tags`, `lean_module`, `lean_file`) and the four sections: **Statement**, **Background**,
   **What is known**, **References**.
3. Create the matching Lean 4 formal problem statement at
   `lean/InfoTheory/Problems/<Module>.lean` defining `def Statement : Prop` and
   `def problem : OpenProblem`, with **zero `sorry`** and **zero custom `axiom`s**, and
   import it in `lean/InfoTheory/Problems.lean`.
4. A good problem file is *precise* (the statement is unambiguous, with notation
   defined), *honest about the state of the art* (the "What is known" section should
   save an attempter a literature search), and *sourced* (every claim in "What is
   known" carries a reference).
5. Run checks before committing:
   ```bash
   cd lean && lake build && cd ..
   python3 scripts/verify_proof.py --check-catalog
   python3 build.py
   ```
6. Commit (or open a PR, for external contributors).

Corrections to existing problem files (sharper known bounds, improved Lean formalizations,
new references, or a solved-status change) are especially valuable and can be small.

## Submitting a Lean 4 proof (or disproof)

1. Do **not** weaken or edit `lean/InfoTheory/Problems/<Module>.lean` to make a proof easier.
   (If you discover a genuine bug in a formal statement, open a separate PR fixing the statement first.)
2. Add `lean/InfoTheory/Solutions/<Module>.lean` defining either:
   - `theorem proof : InfoTheory.Problems.<Module>.Statement`
   - `theorem disproof : ¬ InfoTheory.Problems.<Module>.Statement`
3. Verify mechanically:
   ```bash
   python3 scripts/verify_proof.py --verify <problem-id>
   ```
4. Record the corresponding attempt write-up under `attempts/<problem-id>/` citing the
   verified Lean module.

## Informal & computational attempts

Read [AGENTS.md](AGENTS.md) — the protocol is the same for humans and AI agents.
One attempt = one file under `attempts/<problem-id>/`.

## Review standards

- Lean 4 proofs verified by `scripts/verify_proof.py` (standard axioms only) are
  automatically certified as formally valid proofs of the frozen `Statement`.
- Claims labeled `proved` in an informal attempt must be checkable from the write-up alone
  (plus cited references). Anyone — including another agent — may downgrade a
  label or correct a claim in place; put substantive corrections in the commit
  message.
- An attempt in the repository is **not** an endorsement of its claims.
  Verification is recorded by changing the attempt's `status` field.
- Be generous with `dead-end` write-ups. Knowing what fails, and why, is a real
  contribution.

## Math notation

LaTeX between `$...$` (inline) or `$$...$$` (display) is rendered by MathJax on the
site. Use `\mathsf{}` for channels ($\mathsf{BSC}(\alpha)$), capital letters for random
variables, and define anything non-standard in place.
