import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ListDecodingZeroErrorCapacity

/-- A trifferent code (3-perfect hash family) of length `n`: for every three distinct
    codewords `x, y, z ∈ C ⊆ (Fin 3)^n`, there is a coordinate `i` where all three symbols
    are pairwise distinct. Equivalently, a zero-error list-of-2 code for Elias's `3/2`-channel. -/
def IsTrifferentCode (n : ℕ) (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C,
    x ≠ y → y ≠ z → x ≠ z →
    ∃ i : Fin n, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i

/-- Zero-error list-of-2 capacity `C_{3/2, 2} = limsup_{n → ∞} (1/n) log₂ T(n)` of Elias's
    `3/2`-channel (trifferent capacity). Note: trifferent codes are NOT closed under
    concatenation (`T(1) = 3`, `T(2) = 4`), so `limsup` — NOT `sup_n` — is required. -/
noncomputable def zeroErrorList2Cap32 : ℝ :=
  sInf { r : ℝ | ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    ∀ C : Finset (Fin n → Fin 3), C.Nonempty → IsTrifferentCode n C →
      log2 (C.card : ℝ) / (n : ℝ) ≤ r }

/-- Zero-Error List-Decoding Capacity of the `3/2`-Channel (Elias 1988; Körner–Marton 1988):
    It is known that `(1/4) log₂(9/5) ≈ 0.2120 ≤ C_{3/2, 2} ≤ log₂(3/2) ≈ 0.5850`.
    Does the zero-error list-of-2 capacity of the `3/2`-channel strictly fall below
    the elementary upper bound `log₂(3/2)`? -/
def Statement : Prop :=
  zeroErrorList2Cap32 < log2 ((3 : ℝ) / 2)

def problem : OpenProblem where
  id := "list-decoding-zero-error-capacity"
  title := "Zero-Error List-Decoding Capacity of the 3/2 Channel (Trifferent Codes)"
  category := .zeroError
  status := .open
  posedBy := "Peter Elias; János Körner, Katalin Marton"
  posedYear := 1988
  statement := Statement

end InfoTheory.Problems.ListDecodingZeroErrorCapacity
