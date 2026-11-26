import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DiscreteEntropyPowerInequality

/-- Discrete convolution of two nonnegative sequences on `ℤ`. -/
noncomputable def intConvFn (p q : ℤ → ℝ) : ℤ → ℝ :=
  fun n => ∑' k : ℤ, p k * q (n - k)

/-- `n`-fold convolution power of a PMF on `ℤ` (the PMF of `X₁ + ⋯ + Xₙ` for i.i.d. copies). -/
noncomputable def intConvPow (p : ℤ → ℝ) : ℕ → (ℤ → ℝ)
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => intConvFn (intConvPow p n) p

/-- Shannon entropy (in nats) of a PMF function `p : ℤ → ℝ`. -/
noncomputable def intEntropyFn (p : ℤ → ℝ) : ℝ :=
  ∑' k : ℤ, if p k ≤ 0 then 0 else -p k * Real.log (p k)

/-- Tao's Discrete Entropy Power Inequality Conjecture (2010): for every `n ≥ 1` and `ε > 0`,
    there exists `M > 0` such that any i.i.d. integer-valued random variables `X₁, ..., X_{n+1}`
    with finite entropy `H(X₁) ≥ M` (and finite convolution entropies) satisfy
    `H(X₁ + ⋯ + X_{n+1}) ≥ H(X₁ + ⋯ + Xₙ) + ½ ln((n + 1) / n) - ε`.
    Proved by Gavalakis (2023) for log-concave distributions; open in general. -/
def Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (ε : ℝ), 0 < ε →
      ∃ (M : ℝ), 0 < M ∧
        ∀ (P : IntProbDist),
          HasFiniteIntEntropy P →
          Summable (fun k : ℤ =>
            let pk := intConvPow P.pmf n k
            if pk ≤ 0 then 0 else -pk * Real.log pk) →
          Summable (fun k : ℤ =>
            let pk := intConvPow P.pmf (n + 1) k
            if pk ≤ 0 then 0 else -pk * Real.log pk) →
          M ≤ intEntropy P →
          intEntropyFn (intConvPow P.pmf (n + 1)) ≥
            intEntropyFn (intConvPow P.pmf n) +
              (1 / 2 : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) - ε

def problem : OpenProblem where
  id := "discrete-entropy-power-inequality"
  title := "Discrete Entropy Power Inequality on the Integers"
  category := .entropyInequalities
  status := .open
  posedBy := "Terence Tao; Peter Harremoës and Christophe Vignat; Mokshay Madiman"
  posedYear := 2010
  statement := Statement

end InfoTheory.Problems.DiscreteEntropyPowerInequality
