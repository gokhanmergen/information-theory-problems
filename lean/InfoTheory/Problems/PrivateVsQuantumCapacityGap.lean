import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.PrivateVsQuantumCapacityGap

/-- Existence of a qubit-to-qubit quantum channel with zero quantum capacity and strictly
    positive private classical capacity (`Q(N) = 0 ∧ P(N) > 0`). Known to occur in
    dimensions `d ≥ 4` via PPT private states, while completely open for `d₁ = d₂ = 2`. -/
def Statement : Prop :=
  ∃ (N : QuantumChannel 2 2), quantumCapacity N = 0 ∧ 0 < privateCapacity N

def problem : OpenProblem where
  id := "private-vs-quantum-capacity-gap"
  title := "Zero-Quantum-Capacity Qubit Channels with Positive Private Capacity"
  category := .quantumInfo
  status := .open
  posedBy := "Karol Horodecki, Michał Horodecki, Paweł Horodecki, and Jonathan Oppenheim"
  posedYear := 2005
  statement := Statement

end InfoTheory.Problems.PrivateVsQuantumCapacityGap
