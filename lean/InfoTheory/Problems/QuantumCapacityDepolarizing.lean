import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.QuantumCapacityDepolarizing

/-- Strict improvement over the no-cloning zero-capacity threshold `p = 1/4` for the qubit
    depolarizing channel `D_p`: does there exist `p ∈ (0, 1/4)` such that `Q(D_p) = 0`?
    Known bounds establish `0.19086 ≤ p_0 ≤ 1/4`, while proving `p_0 < 1/4` or `p_0 = 1/4`
    remains open. -/
def Statement : Prop :=
  ∃ (p : ℝ), 0 < p ∧ p < (1 : ℝ) / 4 ∧
    ∀ (N : QuantumChannel 2 2), IsDepolarizingChannel p N → quantumCapacity N = 0

def problem : OpenProblem where
  id := "quantum-capacity-depolarizing"
  title := "Exact Quantum Capacity and Zero-Capacity Threshold of the Qubit Depolarizing Channel"
  category := .quantumInfo
  status := .open
  posedBy := "Charles H. Bennett, David P. DiVincenzo, John A. Smolin, and William K. Wootters"
  posedYear := 1996
  statement := Statement

end InfoTheory.Problems.QuantumCapacityDepolarizing
