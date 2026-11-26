import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.KissingNumberHighDim

/-- Open problem: Does the asymptotic exponential growth rate `lim sup_{d → ∞} (1/d) log₂ τ(d)`
    of the Euclidean kissing number strictly exceed the Chabauty–Shannon–Wyner lower bound
    `log₂(2 / √3) ≈ 0.207519`? -/
def Statement : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ D : ℕ, ∃ d : ℕ, D ≤ d ∧ 0 < d ∧
      log2 (2 / Real.sqrt 3) + ε ≤ log2 (kissingNumber d : ℝ) / (d : ℝ)

def problem : OpenProblem where
  id := "kissing-number-high-dim"
  title := "Asymptotic Exponential Growth Rate of the High-Dimensional Kissing Number"
  category := .codingTheory
  status := .open
  posedBy := "Claude E. Shannon; Aaron D. Wyner; Grigorii A. Kabatiansky and Vladimir I. Levenshtein"
  posedYear := 1959
  statement := Statement

end InfoTheory.Problems.KissingNumberHighDim
