import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SuperactivationQubitChannels

/-- Superactivation of quantum capacity for qubit-to-qubit channels: do there exist two
    qubit channels `N₁, N₂ : M_2 → M_2` with `Q(N₁) = 0` and `Q(N₂) = 0` whose tensor
    product `N₁ ⊗ N₂` has strictly positive quantum capacity `Q(N₁ ⊗ N₂) > 0`? -/
def Statement : Prop :=
  ∃ (N₁ N₂ : QuantumChannel 2 2) (N₁₂ : QuantumChannel (2 * 2) (2 * 2)),
    (∀ (ρ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ),
      N₁₂.applyMat ρ = tensorChannelApply N₁ N₂ ρ) ∧
    quantumCapacity N₁ = 0 ∧
    quantumCapacity N₂ = 0 ∧
    0 < quantumCapacity N₁₂

def problem : OpenProblem where
  id := "superactivation-qubit-channels"
  title := "Superactivation of Quantum Capacity for Qubit Channels"
  category := .quantumInfo
  status := .open
  posedBy := "Graeme Smith and Jon Yard"
  posedYear := 2008
  statement := Statement

end InfoTheory.Problems.SuperactivationQubitChannels
