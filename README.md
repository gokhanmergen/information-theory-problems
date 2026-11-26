# Open Problems in Information Theory

**Live site: [gokhanmergen.github.io/information-theory-problems](https://gokhanmergen.github.io/information-theory-problems/)**
— rebuilt and deployed automatically on every push to `main`.

An [erdosproblems.com](https://www.erdosproblems.com/)-style catalog of **100+ open problems in
information theory**, each paired with a **machine-checked Lean 4 + Mathlib formal problem
statement** — maintained as a git repository so that **humans and AI agents contribute
through the same transparent workflow, and provability comes for free via Lean.**

Every problem is a Markdown file (`problems/<id>.md`) paired with an immutable Lean 4
statement (`lean/InfoTheory/Problems/<Module>.lean`) defining `def Statement : Prop`.
To resolve a problem mechanically, supply a Lean 4 proof of `Statement` (or `¬ Statement`)
in `lean/InfoTheory/Solutions/<Module>.lean` and let Lean's kernel certify it.

## Repository layout

```
problems/     100+ problem files: statement, background, what's known, references.
lean/         Lean 4 + Mathlib formalization package (`InfoTheory`).
  InfoTheory/Core/       Shared definitions (entropy, channels, source coding, zero-error,
                         coding theory, network coding, quantum info, security/stats).
  InfoTheory/Problems/   One frozen `Statement : Prop` file per cataloged problem.
  InfoTheory/Solutions/  Submitted Lean 4 proofs (`proof : Statement` or `disproof : ¬ Statement`).
scripts/      Automated Lean kernel verifier (`verify_proof.py`).
attempts/     One directory per problem id; one file per informal/computational attempt.
templates/    Templates for new problems and new attempts.
build.py      Dependency-free static site generator (Python 3, stdlib only).
site/         Generated output (not committed; built by CI for GitHub Pages).
AGENTS.md     The attempt & formal proof protocol — read this before working on a problem.
```

## Getting started

### 1. Browse & build the static site (stdlib only, no dependencies)

```bash
git clone git@github.com:gokhanmergen/information-theory-problems.git
cd information-theory-problems

python3 build.py && open site/index.html
```

### 2. Build & verify Lean 4 problem statements

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib oleans
lake build           # typecheck Core + all 100+ Lean problem statements
cd ..

# Check catalog consistency & kernel verifier self-test
python3 scripts/verify_proof.py --check-catalog
python3 scripts/verify_proof.py --self-test
```

### 3. Certify a proof (provability comes for free)

Create `lean/InfoTheory/Solutions/<Module>.lean`:

```lean
import InfoTheory.Problems.<Module>

namespace InfoTheory.Solutions.<Module>

theorem proof : InfoTheory.Problems.<Module>.Statement := by
  -- your Lean 4 proof (or `theorem disproof : ¬ InfoTheory.Problems.<Module>.Statement`)
  ...

end InfoTheory.Solutions.<Module>
```

Then verify against the frozen statement and Lean's axiom checker:

```bash
python3 scripts/verify_proof.py --verify <problem-id>
```

The verifier compiles the solution, checks exact definitional type equality with the frozen
`Statement` (or `¬ Statement`), and confirms via `#print axioms` that the proof uses **only**
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) — rejecting `sorryAx`,
custom axioms, and compiler-trust cheats.

### Optional attempt-code dependencies

Some existing informal/computational attempt scripts use extra Python packages (kept out of the
site build on purpose):

```bash
python3 -m venv .venv
.venv/bin/pip install mpmath numpy scipy
```

## Problem categories

The catalog spans 10 major subfields of information theory:

1. **Entropy Inequalities & Geometry** (`entropy-inequalities`)
2. **Point-to-Point Channel Capacity & Synchronization** (`channel-capacity`)
3. **Network Information Theory** (`network-info-theory`)
4. **Multi-Terminal Source Coding & Compression** (`source-coding`)
5. **Zero-Error Information Theory & Graph Capacity** (`zero-error`)
6. **Error-Correcting Codes & Coding Theory Bounds** (`coding-theory`)
7. **Network Coding, Index Coding & Distributed Storage** (`network-coding`)
8. **Quantum Information Theory** (`quantum-info`)
9. **Information-Theoretic Security, Privacy & Secrecy** (`security-privacy`)
10. **Statistical Information Theory, Testing & Estimation** (`statistical-info-theory`)

## Problem status vocabulary

| Status | Meaning |
|---|---|
| `open` | No complete solution known. |
| `partially-solved` | Significant special cases resolved; general problem open. |
| `solved` | Resolved (kept for the record, with the solution referenced). |

## Contributing

- **Add or refine a problem or its Lean statement** — see [CONTRIBUTING.md](CONTRIBUTING.md).
- **Submit a formal Lean proof or informal attempt** (human or AI) — follow [AGENTS.md](AGENTS.md).
