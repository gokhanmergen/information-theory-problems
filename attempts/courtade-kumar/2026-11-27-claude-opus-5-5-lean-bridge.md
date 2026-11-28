---
problem: courtade-kumar
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: reduction
status: unverified
---

## Summary

The external Lean 4 proof of the Courtade–Kumar conjecture
(`github.com/dpwoodru/general-courtade-kumar-lean`, for Chen–Gohari–Javanmard–Lin–Mirrokni–Nair–Woodruff,
arXiv:2609.24931) proves a target proposition `GeneralCK.GeneralCourtadeKumar` that was written
independently of this catalog. We prove in Lean, in this repository, that this target implies the
catalog's frozen `InfoTheory.Problems.CourtadeKumar.Statement`. More strongly, the two formalisations
of $I(f(X);Y)$ are *equal* for every $n$, every Boolean $f$ and every $\alpha\in[0,1]$. This connects
the published machine-checked proof to the frozen statement in two hops. Each hop is kernel-checked,
but in a separate build (see Verification).

## Approach

The external development cannot be imported: it has about 45,500 modules on Lean `v4.33.1`, and this
repository is on `v4.36.0`. Its target statement file `GeneralCK/Statement.lean`, however, uses only
Mathlib. We copied it byte-for-byte into `lean/InfoTheory/External/GeneralCKStatement.lean`, which still
compiles on `v4.36.0` unchanged, and proved the implication against that copy.

Provenance of the copy:
- upstream commit `68cd46b433a1003f06a5c3ee39df2af1a4a314e1` (2026-10-15);
- SHA-256 `698272477382649febc3cd331c9c15f0e036285e1d8180f6107f76b115479342`.

## Claims

1. **[proved]** (Lean: `InfoTheory.External.CourtadeKumar.mutualInfoBSC_eq`) For all $n$, all
   $f:\{0,1\}^n\to\{0,1\}$ and all $\alpha\in[0,1]$, `mutualInfoBSC n α _ _ f = GeneralCK.mutualInformation f α`.
2. **[proved]** (Lean: `binaryEntropy_eq`) `binaryEntropy p = GeneralCK.H p` for $p\in[0,1]$.
3. **[proved]** (Lean: `statement_of_generalCourtadeKumar`)
   `GeneralCK.GeneralCourtadeKumar → InfoTheory.Problems.CourtadeKumar.Statement`. The upstream target
   is strictly stronger: it also covers $n=0$ and $\alpha\in[0,1]$.
4. **[proved]** (external, trusted via the upstream build, not replayed here) Upstream
   `FinalCheck.lean` uses `#guard_msgs` to check that
   `GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar`
   depends only on `propext`, `Classical.choice` and `Quot.sound`. Claims 3 and 4 together give the
   frozen statement.

## Details

The proof is a definitional comparison of two independent formalisations:
- **Entropy summand.** The catalog's `negPLogP p` (set to $0$ for $p\le0$) equals
  `Real.negMulLog p / log 2` for $p\ge0$. Hence `shannonEntropy P = GeneralCK.entropy P.pmf`.
- **Joint law.** The catalog's joint law of $(f(X),Y)$ is a pushforward of `bscNoisyPair`, which is
  the uniform distribution through `(bsc α).power n`. Its mass at $(b,y)$ reduces to
  $2^{-n}\sum_x \mathbf 1[f(x)=b]\prod_i(\ldots)$. That is upstream's `jointMass`; the product is
  literally upstream's `noiseKernel`.
- **Mutual information.** Both sides define $I = H(\text{first}) + H(\text{second}) - H(\text{joint})$
  over the same finite types, so equality of the masses gives equality of the three entropies.
- **Binary entropy.** Mathlib's `binEntropy_eq_negMulLog_add_negMulLog_one_sub` gives the binary
  entropy case.

It is a useful side result that two independently written formalisations of this quantity agree
exactly. This guards against a modelling error on either side.

## Verification

Run in `lean/` on 2026-11-27 (Lean `v4.36.0`, Mathlib `v4.36.0`):
```
lake build InfoTheory.External                 # builds, no errors
lake env leanchecker InfoTheory.External.GeneralCKStatement   # ok
lake env leanchecker InfoTheory.External.CourtadeKumar        # ok
#print axioms InfoTheory.External.CourtadeKumar.statement_of_generalCourtadeKumar
  -- [propext, Classical.choice, Quot.sound]
```
CI now builds `InfoTheory.External` and kernel-replays it (`.github/workflows/lean.yml`).

**What this does not establish.**
- **The upstream theorem is not replayed here.** That needs a separate build of the external
  repository on `v4.33.1`. An end-to-end single-kernel check would need a bridge project on the
  upstream toolchain that imports both the upstream proof and a copy of this catalog's `Core`
  definitions.
- **No `Solutions/CourtadeKumar.lean` was added.** `verify_proof.py` requires an unconditional
  `proof : Statement` built in this repository.

## Dead ends

- **Importing the upstream proof directly fails.** The toolchains are incompatible (`v4.33.1` vs
  `v4.36.0`), and the proof's import closure is about 45,500 modules. Porting it is out of scope.

## References

- Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff,
  "A Proof of the Most Informative Boolean Function Conjecture", arXiv:2609.24931.
- `github.com/dpwoodru/general-courtade-kumar-lean`, commit `68cd46b`; files `GeneralCK/Statement.lean`
  and `FinalCheck.lean`.
- Prior attempt consulted: `attempts/courtade-kumar/2026-11-27-antigravity-resolution-survey.md`.
  It suggested this bridge.
