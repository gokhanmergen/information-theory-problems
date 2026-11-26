import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ConditionalEntropyPowerConjecture

/-- Unconstrained Strong Conditional Entropy Power Inequality (Courtade 2018; extending
    Madiman–Kontoyiannis and Zamir–Feder): for every dimension `d ≥ 1` and all independent
    continuous random vectors `X, Y, W` on `ℝ^d` with finite-entropy, finite-second-moment
    densities `fX, fY, fW` (and finite-entropy convolutions),
    `N(X + W) · N(Y + W) ≥ N(X + Y + W) · N(W) + N(X) · N(Y)`.
    Proved by Courtade (2018) when `W` is Gaussian; open for unconstrained `W`. -/
def Statement : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (fX fY fW fXW fYW fXYW : Density d),
      HasFiniteDiffEntropy fX → HasFiniteDiffEntropy fY → HasFiniteDiffEntropy fW →
      HasFiniteDiffEntropy fXW → HasFiniteDiffEntropy fYW → HasFiniteDiffEntropy fXYW →
      HasFiniteSecondMoment fX → HasFiniteSecondMoment fY → HasFiniteSecondMoment fW →
      (∀ x : Fin d → ℝ, fXW.pdf x = densityConv fX fW x) →
      (∀ x : Fin d → ℝ, fYW.pdf x = densityConv fY fW x) →
      (∀ x : Fin d → ℝ, fXYW.pdf x = densityConv fXW fY x) →
      entropyPower fXW * entropyPower fYW ≥
        entropyPower fXYW * entropyPower fW + entropyPower fX * entropyPower fY

def problem : OpenProblem where
  id := "conditional-entropy-power-conjecture"
  title := "Unconstrained Strong Conditional Entropy Power Inequality"
  category := .entropyInequalities
  status := .open
  posedBy := "Thomas A. Courtade; Mokshay Madiman and Ioannis Kontoyiannis; Ram Zamir and Meir Feder"
  posedYear := 2016
  statement := Statement

end InfoTheory.Problems.ConditionalEntropyPowerConjecture
