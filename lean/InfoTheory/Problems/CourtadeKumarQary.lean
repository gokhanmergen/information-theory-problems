import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CourtadeKumarQary

/-- The q-ary Courtade–Kumar Conjecture (2014): for `X ~ Uniform((Fin q)^n)` passed through
    `QSC(q, α)^n` with `q ≥ 2`, `n ≥ 1`, and `0 ≤ α < 1 - 1/q`, every function
    `f : (Fin q)^n → Fin q` satisfies
    `I(f(X); Y) ≤ log₂ q - h(α) - α log₂ (q - 1)`,
    the value achieved by a single-coordinate dictator function. -/
def Statement : Prop :=
  ∀ (q n : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1),
    α < 1 - 1 / (q : ℝ) →
    ∀ (f : (Fin n → Fin q) → Fin q),
      mutualInfoQSC q n hq α h0 h1 f ≤
        log2 (q : ℝ) - binaryEntropy α - α * log2 ((q : ℝ) - 1)

def problem : OpenProblem where
  id := "courtade-kumar-qary"
  title := "The q-ary Courtade–Kumar Most-Informative-Function Conjecture"
  category := .entropyInequalities
  status := .open
  posedBy := "Thomas A. Courtade and Gowtham R. Kumar"
  posedYear := 2014
  statement := Statement

end InfoTheory.Problems.CourtadeKumarQary
