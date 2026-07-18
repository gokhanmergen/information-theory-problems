# Open Problems in Information Theory

**Live site: [gokhanmergen.github.io/information-theory-problems](https://gokhanmergen.github.io/information-theory-problems/)**
— rebuilt and deployed automatically on every push to `main`.

An [erdosproblems.com](https://www.erdosproblems.com/)-style catalog of open problems in
information theory — maintained as a git repository so that **humans and AI agents
contribute through the same transparent workflow: commits whose history shows who
claimed, corrected, and verified what.**

Every problem is a markdown file with structured metadata. Every attempt at a problem —
whether by a researcher or an AI agent — is a structured markdown file recording the
approach, the claims (each labeled by rigor), and the dead ends, so the next attempt
starts where the last one stopped.

## Repository layout

```
problems/     One file per problem: statement, background, what's known, references.
attempts/     One directory per problem id; one file per attempt.
templates/    Templates for new problems and new attempts.
build.py      Dependency-free static site generator (Python 3, stdlib only).
site/         Generated output (not committed; built by CI for GitHub Pages).
AGENTS.md     The attempt protocol — read this before working on a problem.
```

## Getting started

```bash
git clone git@github.com:gokhanmergen/information-theory-problems.git
cd information-theory-problems

# Build and view the site locally (stdlib only, no dependencies).
# This renders exactly what the live GitHub Pages site shows.
python3 build.py && open site/index.html
```

Some attempt code has extra dependencies (kept out of the site build on purpose):

```bash
python3 -m venv .venv
.venv/bin/pip install mpmath numpy scipy
# mpmath      -> attempts/courtade-kumar/code/certify_n4.py (interval arithmetic)
# numpy/scipy -> attempts/relay-channel/code/egn_bound.py,
#                attempts/broadcast-channel/code/bssc_bounds.py
```

C/C++ certificates under `attempts/*/code/` build with any recent compiler; each
file's header comment gives the exact command.

## Contributing

- **Add or improve a problem** — see [CONTRIBUTING.md](CONTRIBUTING.md).
- **Attempt a problem** (human or AI) — follow the protocol in [AGENTS.md](AGENTS.md):
  one attempt = one file under `attempts/<problem-id>/`, committed directly to `main`
  (external contributors: pull requests welcome).

## Problem status vocabulary

| Status | Meaning |
|---|---|
| `open` | No complete solution known. |
| `partially-solved` | Significant special cases resolved; general problem open. |
| `solved` | Resolved (kept for the record, with the solution referenced). |

## Why

Curated problem lists concentrate effort. Erdős's problems shaped combinatorics for
decades; the hope here is that a well-maintained, machine-readable list of open problems
in information theory can do the same — and that AI agents, attempting problems one by
one under a protocol that separates proof from heuristic, become genuine contributors
alongside the community.
