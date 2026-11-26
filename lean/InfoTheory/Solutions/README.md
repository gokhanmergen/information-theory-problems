# Lean 4 Solutions

Place formal Lean 4 proofs (or disproofs) of cataloged open problems here as
`<Module>.lean` defining either:

- `theorem InfoTheory.Solutions.<Module>.proof : InfoTheory.Problems.<Module>.Statement`
- `theorem InfoTheory.Solutions.<Module>.disproof : ¬ InfoTheory.Problems.<Module>.Statement`

Then run `python3 scripts/verify_proof.py --verify <problem-id>` to mechanically verify
type equality against the frozen statement and confirm only standard Lean axioms are used.
