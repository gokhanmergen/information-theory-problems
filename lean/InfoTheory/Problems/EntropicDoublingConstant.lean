import InfoTheory.Core

open scoped BigOperators Classical

namespace InfoTheory.Problems.EntropicDoublingConstant

/-- Entropic Ruzsa distance `d[X; Y] = H(X + Y) - ½ H(X) - ½ H(Y)` for independent
    `X ~ P`, `Y ~ Q` on `𝔽_2^n`. -/
noncomputable def ruzsaDist (n : ℕ) (P Q : ProbDist (Fin n → ZMod 2)) : ℝ :=
  shannonEntropy ((P.prod Q).map (fun xy i => xy.1 i + xy.2 i)) -
    (shannonEntropy P + shannonEntropy Q) / 2

/-- Predicate stating that `U` is the uniform distribution on a linear subspace `H ≤ 𝔽_2^n`. -/
def IsUniformOnSubspace (n : ℕ) (U : ProbDist (Fin n → ZMod 2)) : Prop :=
  ∃ (H : Submodule (ZMod 2) (Fin n → ZMod 2)),
    ∀ x : Fin n → ZMod 2,
      U.pmf x = if x ∈ H then (1 : ℝ) / ((2 : ℝ) ^ (Module.finrank (ZMod 2) H)) else 0

/-- Sharp Entropic PFR Constant Conjecture: for every `n ≥ 1` and every `𝔽_2^n`-valued
    distribution `P`, there exists a subspace uniform distribution `U_H` such that
    `d[P; U_H] ≤ 2 · d[P; P]`. (The existence of an absolute constant `C` was proved by
    Gowers–Green–Manners–Tao 2023 and sharpened by Liao 2024, while the sharp constant
    remains open.) -/
def Statement : Prop :=
  ∀ (n : ℕ) (P : ProbDist (Fin n → ZMod 2)),
    ∃ (U : ProbDist (Fin n → ZMod 2)),
      IsUniformOnSubspace n U ∧ ruzsaDist n P U ≤ 2 * ruzsaDist n P P

def problem : OpenProblem where
  id := "entropic-doubling-constant"
  title := "Sharp Constant in the Entropic Polynomial Freiman–Ruzsa Inequality"
  category := .entropyInequalities
  status := .partiallySolved
  posedBy := "Katalin Marton; Terence Tao"
  posedYear := 2023
  statement := Statement

end InfoTheory.Problems.EntropicDoublingConstant
