import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BatchCodesOptimalRedundancy

/-- A binary linear primitive multiset `k`-batch code of dimension `n` and length `N`:
    a linear encoder `enc : 𝔽₂^n →ₗ 𝔽₂^N` such that every multiset request of `k`
    message indices can be recovered from `k` pairwise disjoint subsets of codeword bits. -/
def IsLinearBinaryBatchCode (n N k : ℕ) : Prop :=
  ∃ enc : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin N → ZMod 2),
    ∀ req : Fin k → Fin n,
      ∃ (R : Fin k → Finset (Fin N))
        (dec : Fin k → (Fin N → ZMod 2) → ZMod 2),
        (∀ t₁ t₂ : Fin k, t₁ ≠ t₂ → ∀ j : Fin N, ¬ (j ∈ R t₁ ∧ j ∈ R t₂)) ∧
        (∀ t : Fin k, ∀ c₁ c₂ : Fin N → ZMod 2,
          (∀ j ∈ R t, c₁ j = c₂ j) → dec t c₁ = dec t c₂) ∧
        (∀ x : Fin n → ZMod 2, ∀ t : Fin k, dec t (enc x) = x (req t))

/-- Minimum redundancy `r_B(n, k) = N_min(n, k) - n` of a binary linear primitive multiset
    `k`-batch code of dimension `n`. -/
noncomputable def minBatchRedundancy (n k : ℕ) : ℕ :=
  sInf { r : ℕ | IsLinearBinaryBatchCode n (n + r) k }

/-- Asi–Yaakobi conjecture: for every fixed constant batch size `k ≥ 3`, the optimal redundancy
    of binary linear primitive multiset `k`-batch codes satisfies `r_B(n, k) = O_k(√n)`. -/
def Statement : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (minBatchRedundancy n k : ℝ) ≤ C * Real.sqrt (n : ℝ)

def problem : OpenProblem where
  id := "batch-codes-optimal-redundancy"
  title := "Optimal Redundancy of Primitive Multiset Batch Codes"
  category := .networkCoding
  status := .open
  posedBy := "Yuval Ishai, Eyal Kushilevitz, Rafail Ostrovsky, and Amit Sahai; Hilal Asi and Eitan Yaakobi"
  posedYear := 2004
  statement := Statement

end InfoTheory.Problems.BatchCodesOptimalRedundancy
