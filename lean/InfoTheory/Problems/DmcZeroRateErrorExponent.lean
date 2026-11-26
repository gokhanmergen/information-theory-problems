import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DmcZeroRateErrorExponent

/-- Low-Rate Reliability Function Conjecture for Strictly Positive Binary-Input DMCs
    (Shannon–Gallager–Berlekamp 1967; Dalai–Polyanskiy 2018):
    while Katsman–Tsfasman–Vlăduţ (1984) and Dalai–Polyanskiy (2018) disproved tightness of
    the expurgated bound for DMCs with `|X| ≥ 4`, it remains open whether every strictly
    positive binary-input DMC `W : DMC Bool (Fin k)` (`W(y|x) > 0`, ensuring finite
    reliability and expurgated exponents) satisfies
    `E(W, R) = max(E_r(W, R), E_ex(W, R))` for all `0 < R < C(W)`. -/
def Statement : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ (W : DMC Bool (Fin k)) (R : ℝ),
      W.IsPositive →
      0 < R → R < W.capacity →
      reliabilityFunction W R =
        max (randomCodingExponent W R) (expurgatedExponent W R)

def problem : OpenProblem where
  id := "dmc-zero-rate-error-exponent"
  title := "Tightness of the Expurgated and Random-Coding Exponents for Binary-Input DMCs"
  category := .channelCapacity
  status := .open
  posedBy := "Claude E. Shannon, Robert G. Gallager, and Elwyn R. Berlekamp; Marco Dalai"
  posedYear := 1967
  statement := Statement

end InfoTheory.Problems.DmcZeroRateErrorExponent
