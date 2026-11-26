import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ZeroErrorMacAdder

/-- Zero-Error Sum Capacity of the Two-User Binary Adder Multiple-Access Channel
    (Lindström 1969; Kasami–Lin 1976; Urbanke–Li 1998; Mattas–Östergård 2005):
    Current bounds bracket `zeroErrorAdderMACSumCapacity` in `[≈ 1.3186, ≈ 1.480]`.
    Does some finite blocklength `n ≥ 1` attain the exact zero-error sum capacity
    of the two-user binary adder MAC? -/
def Statement : Prop :=
  ∃ (n : ℕ) (A B : Finset (Fin n → Fin 2)),
    0 < n ∧ A.Nonempty ∧ B.Nonempty ∧ IsAdderMACCode n A B ∧
    (log2 (A.card : ℝ) + log2 (B.card : ℝ)) / (n : ℝ) = zeroErrorAdderMACSumCapacity

def problem : OpenProblem where
  id := "zero-error-mac-adder"
  title := "Zero-Error Sum Capacity of the Two-User Binary Adder Multiple-Access Channel"
  category := .zeroError
  status := .open
  posedBy := "Bernt Lindström; Tadao Kasami, Shu Lin"
  posedYear := 1969
  statement := Statement

end InfoTheory.Problems.ZeroErrorMacAdder
