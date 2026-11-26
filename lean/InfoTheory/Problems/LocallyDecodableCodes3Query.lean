import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.LocallyDecodableCodes3Query

/-- Open problem: Must every 3-query binary Locally Decodable Code with constant noise
    tolerance `δ > 0` and constant recovery advantage `ε > 0` have super-polynomial
    blocklength `n = ω(k^d)` for every integer degree `d`? -/
def Statement : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    ∀ (d : ℕ) (C : ℝ), 0 < C →
      ∃ K : ℕ, ∀ (k n : ℕ), K ≤ k → IsBinaryLDC k n 3 δ ε →
        C * (k : ℝ) ^ d < (n : ℝ)

def problem : OpenProblem where
  id := "locally-decodable-codes-3-query"
  title := "Optimal Blocklength of 3-Query Binary Locally Decodable Codes"
  category := .codingTheory
  status := .open
  posedBy := "Jonathan Katz and Luca Trevisan"
  posedYear := 2000
  statement := Statement

end InfoTheory.Problems.LocallyDecodableCodes3Query
