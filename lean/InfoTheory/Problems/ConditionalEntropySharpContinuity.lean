import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ConditionalEntropySharpContinuity

/-- Sharp uniform continuity bound for quantum conditional entropy `S(A | B) = S(AB) - S(B)`
    (generalizing the classical bound proved by Alhejji–Smith 2020, and sharpening Winter 2016):
    for all `d_A ≥ 2`, `d_B ≥ 1`, and bipartite states `ρ, σ` with trace distance
    `ε ≤ 1 - 1 / d_A²`, does `|S(A | B)_ρ - S(A | B)_σ| ≤ ε log₂(d_A² - 1) + h(ε)` hold? -/
def Statement : Prop :=
  ∀ (dA dB : ℕ) (ρ σ : DensityMatrix (dA * dB)),
    2 ≤ dA → 1 ≤ dB →
    let ε := traceDistance ρ σ
    ε ≤ 1 - (1 : ℝ) / ((dA * dA : ℕ) : ℝ) →
    |(vonNeumannEntropy ρ - matEntropy (@partialTraceA dA dB ρ.mat)) -
     (vonNeumannEntropy σ - matEntropy (@partialTraceA dA dB σ.mat))| ≤
      ε * log2 ((dA * dA - 1 : ℕ) : ℝ) + binaryEntropy ε

def problem : OpenProblem where
  id := "conditional-entropy-sharp-continuity"
  title := "Sharp Uniform Continuity Bounds for Conditional Entropy"
  category := .statisticalInfoTheory
  status := .partiallySolved
  posedBy := "Zhen Zhang; Andreas Winter; Mohammad A. Alhejji and Graeme Smith"
  posedYear := 2007
  statement := Statement

end InfoTheory.Problems.ConditionalEntropySharpContinuity
