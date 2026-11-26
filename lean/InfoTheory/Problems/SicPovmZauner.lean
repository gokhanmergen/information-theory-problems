import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SicPovmZauner

/-- Zauner's Conjecture: for every dimension `d ≥ 2`, there exists a SIC-POVM consisting of
    `d²` unit vectors in `ℂ^d` with pairwise overlap `|⟨ψ_j | ψ_k⟩|² = 1 / (d + 1)`. -/
def Statement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ (ψ : Fin (d * d) → Fin d → ℂ), IsSICPOVM d ψ

def problem : OpenProblem where
  id := "sic-povm-zauner"
  title := "Zauner's Conjecture on the Existence of SIC-POVMs in Every Dimension"
  category := .quantumInfo
  status := .open
  posedBy := "Gerhard Zauner"
  posedYear := 1999
  statement := Statement

end InfoTheory.Problems.SicPovmZauner
