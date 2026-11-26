import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.QuantumCapacityTwoPauli

/-- Zero-capacity threshold of the qubit two-Pauli channel `N_p(ρ) = (1-p)ρ + (p/2)(XρX + ZρZ)`:
    does there exist `p ∈ (0, 1/3)` strictly below the anti-degradability (no-cloning)
    threshold `1/3` such that `Q(N_p) = 0`? -/
def Statement : Prop :=
  ∃ (p : ℝ), 0 < p ∧ p < (1 : ℝ) / 3 ∧
    ∀ (N : QuantumChannel 2 2), IsTwoPauliChannel p N → quantumCapacity N = 0

def problem : OpenProblem where
  id := "quantum-capacity-two-pauli"
  title := "Exact Quantum Capacity and Positivity Threshold of the Qubit Two-Pauli Channel"
  category := .quantumInfo
  status := .open
  posedBy := "David P. DiVincenzo, Peter W. Shor, and John A. Smolin"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.QuantumCapacityTwoPauli
