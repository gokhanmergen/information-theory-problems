import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.RenyiEntropyPowerSharp

/-- Rényi entropy power `N_α(f) = exp((2 / d) · h_α(f))` for a density `f` on `ℝ^d`. -/
noncomputable def renyiEntropyPower {d : ℕ} (α : ℝ) (f : Density d) : ℝ :=
  Real.exp ((2 / (d : ℝ)) * renyiDiffEntropy α f)

/-- Conjectured sharp dimension-free constant `c*(α)` achieved asymptotically by identical
    uniform Euclidean balls as `d → ∞`:
    `c*(α) = (α + 1)^((α + 1)/(α - 1)) / (2 · 4^(1/(α - 1)) · α^(α/(α - 1)))`. -/
noncomputable def sharpRenyiConst (α : ℝ) : ℝ :=
  ((α + 1) ^ ((α + 1) / (α - 1))) /
    (2 * ((4 : ℝ) ^ (1 / (α - 1))) * (α ^ (α / (α - 1))))

/-- Sharp Rényi Entropy Power Inequality Conjecture for `α > 1` (Bobkov–Chistyakov 2015;
    Ram–Sason 2016; Li 2018): for every `α > 1`, every dimension `d ≥ 1`, and all
    independent continuous random vectors `X, Y` on `ℝ^d` with finite `L^α` norms
    (ensuring well-defined finite Rényi differential entropies),
    `N_α(X + Y) ≥ c*(α) · (N_α(X) + N_α(Y))`. -/
def Statement : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (α : ℝ), 1 < α →
      ∀ (f g fg : Density d),
        HasFiniteRenyiEntropy α f → HasFiniteRenyiEntropy α g → HasFiniteRenyiEntropy α fg →
        (∀ x : Fin d → ℝ, fg.pdf x = densityConv f g x) →
        renyiEntropyPower α fg ≥
          sharpRenyiConst α * (renyiEntropyPower α f + renyiEntropyPower α g)

def problem : OpenProblem where
  id := "renyi-entropy-power-sharp"
  title := "Sharp Constant in the Rényi Entropy Power Inequality for Order α > 1"
  category := .entropyInequalities
  status := .open
  posedBy := "Sergey G. Bobkov and Gennadiy P. Chistyakov; Jiange Li"
  posedYear := 2015
  statement := Statement

end InfoTheory.Problems.RenyiEntropyPowerSharp
