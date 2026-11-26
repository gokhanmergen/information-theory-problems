import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness

/-- Sharp `1 / min(d_A, d_B)` faithfulness lower bound for squashed entanglement in trace
    distance: does there exist a universal constant `c > 0` such that for all bipartite
    density matrices `ρ_{AB}` on `ℂ^{d_A} ⊗ ℂ^{d_B}`,
    `E_sq(ρ_{AB}) ≥ (c / min(d_A, d_B)) · dist_1(ρ_{AB}, SEP)²`?
    Known bounds prove `1 / min(d_A, d_B)²` (Brandão–Christandl–Yard 2011; Li–Winter 2018),
    while the antisymmetric state shows `1 / min(d_A, d_B)` cannot be beaten. -/
def Statement : Prop :=
  ∃ (c : ℝ), 0 < c ∧
    ∀ (dA dB : ℕ) (ρ : DensityMatrix (dA * dB)),
      0 < dA → 0 < dB →
      ∃ (σ : DensityMatrix (dA * dB)),
        @IsSeparable dA dB σ ∧
        (c / ((min dA dB : ℕ) : ℝ)) * (traceDistance ρ σ) ^ 2 ≤ @squashedEntanglement dA dB ρ

def problem : OpenProblem where
  id := "quantum-squashed-entanglement-faithfulness"
  title := "Optimal Dimension Dependence for Faithfulness of Squashed Entanglement"
  category := .quantumInfo
  status := .open
  posedBy := "Fernando G. S. L. Brandão, Matthias Christandl, and Jon Yard"
  posedYear := 2011
  statement := Statement

end InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness
