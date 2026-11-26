import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.GilbertVarshamovBinary

/-- Asymptotic tightness of the binary Gilbert–Varshamov bound: for every relative minimum
    distance `δ ∈ (0, 1/2)`, the maximum asymptotic rate `R_2(δ)` of binary error-correcting
    codes equals the Gilbert–Varshamov bound `1 - h(δ)`. -/
def Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    asymptoticCodeRate 2 δ = gilbertVarshamov δ

def problem : OpenProblem where
  id := "gilbert-varshamov-binary"
  title := "Asymptotic Tightness of the Binary Gilbert–Varshamov Bound"
  category := .codingTheory
  status := .open
  posedBy := "E. N. Gilbert; R. R. Varshamov"
  posedYear := 1952
  statement := Statement

end InfoTheory.Problems.GilbertVarshamovBinary
