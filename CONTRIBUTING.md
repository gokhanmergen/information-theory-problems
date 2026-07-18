# Contributing

All contributions — problems, corrections, attempts — arrive as pull requests.

## Adding a problem

1. Copy `templates/PROBLEM_TEMPLATE.md` to `problems/<id>.md`, where `<id>` is a short
   kebab-case slug (e.g. `deletion-channel`).
2. Fill in the frontmatter and the four sections: **Statement**, **Background**,
   **What is known**, **References**.
3. A good problem file is *precise* (the statement is unambiguous, with notation
   defined), *honest about the state of the art* (the "What is known" section should
   save an attempter a literature search), and *sourced* (every claim in "What is
   known" carries a reference).
4. Run `python3 build.py` — the build fails loudly on malformed frontmatter.
5. Open a PR.

Corrections to existing problem files (sharper known bounds, new references, a
solved-status change) are especially valuable and can be small PRs.

## Attempting a problem

Read [AGENTS.md](AGENTS.md) — the protocol is the same for humans and AI agents.
One attempt = one file under `attempts/<problem-id>/`, added by PR.

## Review standards

- Claims labeled `proved` in an attempt must be checkable from the write-up alone
  (plus cited references). Reviewers will downgrade anything that isn't.
- An attempt PR is merged when it follows the format and its labels are honest —
  merging an attempt does **not** endorse its claims. Verification is recorded by a
  later PR changing the attempt's `status` field.
- Be generous with `dead-end` write-ups. Knowing what fails, and why, is a real
  contribution.

## Math notation

LaTeX between `$...$` (inline) or `$$...$$` (display) is rendered by MathJax on the
site. Use `\mathsf{}` for channels ($\mathsf{BSC}(\alpha)$), capital letters for random
variables, and define anything non-standard in place.
