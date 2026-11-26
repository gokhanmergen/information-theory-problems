import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CourtadeKumar

/-- The Courtade–Kumar Most-Informative-Boolean-Function Conjecture (2013):
    For `X ~ Uniform({0,1}^n)` and `Y = BSC(α)^n(X)` with `α ∈ (0, 1/2)`,
    every Boolean function `f : {0,1}^n → {0,1}` satisfies `I(f(X); Y) ≤ 1 - h(α)`. -/
def Statement : Prop :=
  ∀ (n : ℕ) (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (f : (Fin n → Bool) → Bool),
    mutualInfoBSC n α (le_of_lt h0) (by linarith) f ≤ 1 - binaryEntropy α

def problem : OpenProblem where
  id := "courtade-kumar"
  title := "The Courtade–Kumar Most-Informative-Boolean-Function Conjecture"
  category := .entropyInequalities
  status := .open
  posedBy := "Courtade and Kumar"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.CourtadeKumar
