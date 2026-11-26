import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.QuantumCapacitySingleLetter

/-- Bounded-letter regularization of quantum capacity: does there exist, for every fixed pair
    of positive input/output dimensions `(d₁, d₂)`, a uniform finite integer `k ≥ 1` such that
    `Q(N) = (1 / k) Q^{(k)}(N)` for every CPTP channel `N : M_{d₁} → M_{d₂}`? -/
def Statement : Prop :=
  ∀ (d₁ d₂ : ℕ), 0 < d₁ → 0 < d₂ →
    ∃ (k : ℕ), 0 < k ∧
      ∀ (N : QuantumChannel d₁ d₂), quantumCapacity N = coherentInfoRegN N k

def problem : OpenProblem where
  id := "quantum-capacity-single-letter"
  title := "Bounded-Letter Regularization and Computability of Quantum Capacity"
  category := .quantumInfo
  status := .open
  posedBy := "David P. DiVincenzo, Peter W. Shor, and John A. Smolin"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.QuantumCapacitySingleLetter
