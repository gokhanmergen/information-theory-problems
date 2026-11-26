import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.EditDistanceCodeCapacity

/-- Open problem: Does the zero-rate threshold of binary adversarial deletion codes strictly
    exceed the Bukh–Guruswami–Håstad lower bound `√2 - 1`? (Bukh–Guruswami–Håstad 2017 proved
    `deletionCodeCapacity δ > 0` for all `δ < √2 - 1`; Guruswami–He–Li 2021 proved
    `deletionCodeCapacity δ = 0` for all `δ ≥ 1/2 - ε₀` for an absolute constant `ε₀ > 0`.) -/
def Statement : Prop :=
  ∃ δ : ℝ, Real.sqrt 2 - 1 < δ ∧ 0 < deletionCodeCapacity δ

def problem : OpenProblem where
  id := "edit-distance-code-capacity"
  title := "Zero-Rate Threshold and Capacity of Binary Adversarial Deletion Codes"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "Vladimir I. Levenshtein; Boris Bukh, Venkatesan Guruswami, and Johan Håstad"
  posedYear := 1966
  statement := Statement

end InfoTheory.Problems.EditDistanceCodeCapacity
