import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.NptBoundEntanglement

/-- Existence of Non-Positive Partial Transpose (NPT) bound entangled bipartite states:
    do there exist dimensions `dA, dB ≥ 1` and a bipartite density matrix `ρ` on
    `ℂ^{dA} ⊗ ℂ^{dB}` that is NPT (`¬ IsPPT ρ`) yet undistillable (`¬ IsDistillable ρ`)? -/
def Statement : Prop :=
  ∃ (dA dB : ℕ) (ρ : DensityMatrix (dA * dB)),
    0 < dA ∧ 0 < dB ∧ ¬ @IsPPT dA dB ρ ∧ ¬ @IsDistillable dA dB ρ

def problem : OpenProblem where
  id := "npt-bound-entanglement"
  title := "Existence of NPT Bound Entangled Quantum States"
  category := .quantumInfo
  status := .open
  posedBy := "David P. DiVincenzo, Peter W. Shor, John A. Smolin, Barbara M. Terhal, and Ashish V. Thapliyal"
  posedYear := 2000
  statement := Statement

end InfoTheory.Problems.NptBoundEntanglement
