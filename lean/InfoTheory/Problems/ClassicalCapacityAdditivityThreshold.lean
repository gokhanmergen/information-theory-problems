import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ClassicalCapacityAdditivityThreshold

/-- Qubit-output (`d = 2`) additivity threshold for minimum output von Neumann entropy:
    do there exist quantum channels `N₁ : M_{d₁} → M_2` and `N₂ : M_{e₁} → M_2` with
    strictly subadditive minimum output entropy `S_min(N₁ ⊗ N₂) < S_min(N₁) + S_min(N₂)`? -/
def Statement : Prop :=
  ∃ (d₁ e₁ : ℕ) (N₁ : QuantumChannel d₁ 2) (N₂ : QuantumChannel e₁ 2),
    0 < d₁ ∧ 0 < e₁ ∧
    minOutputEntropyTensor N₁ N₂ < minOutputEntropy N₁ + minOutputEntropy N₂

def problem : OpenProblem where
  id := "classical-capacity-additivity-threshold"
  title := "Minimum Output Dimension for Non-Additivity of Minimum Output Entropy"
  category := .quantumInfo
  status := .open
  posedBy := "Matthew B. Hastings"
  posedYear := 2009
  statement := Statement

end InfoTheory.Problems.ClassicalCapacityAdditivityThreshold
