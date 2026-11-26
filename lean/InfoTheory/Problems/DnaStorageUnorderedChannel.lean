import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DnaStorageUnorderedChannel

/-- Achievability of storage rate `R` (bits per stored symbol) over the shuffled binary
    deletion channel `Del_d` with `M` unordered strands of length `L = ⌊β log₂ M⌋`.
    Unordered observation is captured by requiring the decoder `dec` to be invariant under
    every permutation `σ` of the `M` output traces. -/
def IsShuffledDeletionAchievable (d β R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → 2 ≤ M →
      let L : ℕ := Nat.floor (β * log2 (M : ℝ))
      let K : ℕ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((M * L : ℕ) : ℝ) * R)))
      ∃ (enc : Fin K → Fin M → Fin L → Bool)
        (dec : (Fin M → Σ k : Fin (L + 1), Fin k.1 → Bool) → Fin K),
        -- Unordered output constraint: decoder is permutation-invariant across the M traces
        (∀ (σ : Fin M → Fin M), Function.Bijective σ →
          ∀ y : Fin M → Σ k : Fin (L + 1), Fin k.1 → Bool,
            dec (fun i => y (σ i)) = dec y) ∧
        let err : ℝ :=
          ((1 : ℝ) / (K : ℝ)) *
            ∑ msg : Fin K,
              ∑ y : Fin M → Σ k : Fin (L + 1), Fin k.1 → Bool,
                if dec y ≠ msg then
                  ∏ i : Fin M, deletionProb d (List.ofFn (enc msg i)) (List.ofFn (y i).2)
                else 0
        err ≤ ε

/-- Capacity `C_{shuf-del}(d, β)` of the shuffled binary deletion DNA storage channel. -/
noncomputable def shuffledDeletionCapacity (d β : ℝ) : ℝ :=
  sSup { R : ℝ | IsShuffledDeletionAchievable d β R }

/-- Open problem: Does the Shomorony–Heckel shuffling-penalty law hold for the binary
    deletion channel at sufficiently large molecule-length scaling `β`, i.e., for every
    `d ∈ (0, 1)`, does `C_{shuf-del}(d, β) = C_del(d) - 1 / β` hold for all sufficiently
    large `β`? -/
def Statement : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 →
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      shuffledDeletionCapacity d β = binaryDeletionCapacity d - 1 / β

def problem : OpenProblem where
  id := "dna-storage-unordered-channel"
  title := "Capacity of the Shuffled Noisy-Draws DNA Storage Channel with Deletion Noise"
  category := .networkCoding
  status := .partiallySolved
  posedBy := "Ilan Shomorony and Reinhard Heckel; Nir Weinberger and Neri Merhav"
  posedYear := 2021
  statement := Statement

end InfoTheory.Problems.DnaStorageUnorderedChannel
