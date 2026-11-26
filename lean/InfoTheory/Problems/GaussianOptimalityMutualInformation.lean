import InfoTheory.Core

open scoped BigOperators
open MeasureTheory

namespace InfoTheory.Problems.GaussianOptimalityMutualInformation

/-- Predicate stating that `g : Density d` is a centered non-degenerate multivariate Gaussian
    density on `ℝ^d`: `g(x) = c · exp(-½ xᵀ Q x)` with `c > 0` and symmetric positive-definite `Q`. -/
def IsCenteredGaussian (d : ℕ) (g : Density d) : Prop :=
  ∃ (c : ℝ) (Q : Fin d → Fin d → ℝ),
    0 < c ∧
    (∀ i j : Fin d, Q i j = Q j i) ∧
    (∀ v : Fin d → ℝ, (∃ i : Fin d, v i ≠ 0) →
      0 < ∑ i : Fin d, ∑ j : Fin d, Q i j * v i * v j) ∧
    (∀ x : Fin d → ℝ,
      g.pdf x = c * Real.exp (-(1 / 2 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, Q i j * x i * x j))

/-- Second-moment (covariance) upper bound `E_f[⟨v, X⟩²] ≤ vᵀ K v` for all `v ∈ ℝ^d`. -/
def HasSecondMomentLe (d : ℕ) (f : Density d) (K : Fin d → Fin d → ℝ) : Prop :=
  ∀ v : Fin d → ℝ,
    (∫ x : Fin d → ℝ, (∑ i : Fin d, v i * x i) ^ 2 * f.pdf x) ≤
      ∑ i : Fin d, ∑ j : Fin d, K i j * v i * v j

/-- Multi-Branch Gaussian Optimality Conjecture (Anantharam–Jog–Nair; Courtade):
    for any dimension `d ≥ 1`, any two centered Gaussian noise densities `g₁, g₂` on `ℝ^d`,
    any positive-definite covariance bound `K`, and any `β ∈ (1, 2)`, the supremum of
    `β · h(f) - h(f * g₁) - h(f * g₂)` over all densities `f` with `E[XXᵀ] ⪯ K`
    is achieved by a centered Gaussian density `f*` with `E[X*X*ᵀ] ⪯ K`. -/
def Statement : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (g₁ g₂ : Density d),
      IsCenteredGaussian d g₁ → IsCenteredGaussian d g₂ →
      ∀ (K : Fin d → Fin d → ℝ),
        (∀ i j : Fin d, K i j = K j i) →
        (∀ v : Fin d → ℝ, (∃ i : Fin d, v i ≠ 0) →
          0 < ∑ i : Fin d, ∑ j : Fin d, K i j * v i * v j) →
        ∀ (β : ℝ), 1 < β → β < 2 →
          ∃ (fStar fg₁Star fg₂Star : Density d),
            IsCenteredGaussian d fStar ∧
            HasSecondMomentLe d fStar K ∧
            (∀ x : Fin d → ℝ, fg₁Star.pdf x = densityConv fStar g₁ x) ∧
            (∀ x : Fin d → ℝ, fg₂Star.pdf x = densityConv fStar g₂ x) ∧
            ∀ (f fg₁ fg₂ : Density d),
              HasFiniteDiffEntropy f → HasFiniteDiffEntropy fg₁ → HasFiniteDiffEntropy fg₂ →
              HasFiniteSecondMoment f →
              HasSecondMomentLe d f K →
              (∀ x : Fin d → ℝ, fg₁.pdf x = densityConv f g₁ x) →
              (∀ x : Fin d → ℝ, fg₂.pdf x = densityConv f g₂ x) →
              β * diffEntropy f - diffEntropy fg₁ - diffEntropy fg₂ ≤
                β * diffEntropy fStar - diffEntropy fg₁Star - diffEntropy fg₂Star

def problem : OpenProblem where
  id := "gaussian-optimality-mutual-information"
  title := "Gaussian Optimality for Multi-Branch Vector Information Bottleneck Functionals"
  category := .entropyInequalities
  status := .open
  posedBy := "Venkat Anantharam, Varun Jog, and Chandra Nair; Thomas A. Courtade"
  posedYear := 2016
  statement := Statement

end InfoTheory.Problems.GaussianOptimalityMutualInformation
