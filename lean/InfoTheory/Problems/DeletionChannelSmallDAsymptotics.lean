import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DeletionChannelSmallDAsymptotics

/-- The Kanoria–Montanari (2013) exact linear correction constant
    `c₁ = (∑_{ℓ ≥ 1} 2^{-(ℓ+1)} ℓ log₂ ℓ) - 1` in `C(d) = 1 - h(d) + c₁ d + o(d)`. -/
noncomputable def kanoriaMontanariC1 : ℝ :=
  (∑' l : ℕ, ((1 : ℝ) / ((2 : ℝ) ^ (l + 2))) * ((l + 1 : ℕ) : ℝ) * log2 ((l + 1 : ℕ) : ℝ)) - 1

/-- Small-d Analyticity / All-Orders Expansion Conjecture for the Binary Deletion Channel
    (building on Kanoria–Montanari 2013): does `C(d) - (1 - h(d))` admit a convergent
    power series `∑_{k ≥ 1} c_k d^k` on some interval `(0, δ)` with leading coefficient
    `c_1 = kanoriaMontanariC1`? -/
def Statement : Prop :=
  ∃ (δ : ℝ) (c : ℕ → ℝ),
    0 < δ ∧
    c 1 = kanoriaMontanariC1 ∧
    ∀ (d : ℝ), 0 < d → d < δ →
      Summable (fun k : ℕ => c (k + 1) * d ^ (k + 1)) ∧
      binaryDeletionCapacity d =
        1 - binaryEntropy d + ∑' k : ℕ, c (k + 1) * d ^ (k + 1)

def problem : OpenProblem where
  id := "deletion-channel-small-d-asymptotics"
  title := "Small-Deletion-Probability Asymptotic Expansion of the Binary Deletion Channel"
  category := .channelCapacity
  status := .partiallySolved
  posedBy := "Yashodhan Kanoria and Andrea Montanari"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.DeletionChannelSmallDAsymptotics
