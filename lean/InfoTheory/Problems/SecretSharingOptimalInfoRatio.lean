import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SecretSharingOptimalInfoRatio

/-- Super-linear growth (`ω(n)`) of the worst-case optimal secret sharing information ratio
    over `n`-party monotone access structures, breaking the Csirmaz (1997) linear barrier
    of Shannon-type information inequalities. Known bounds stand at `Ω(n / log n)` vs
    `2^{0.585 n + o(n)}`. -/
def Statement : Prop :=
  ∀ (C : ℝ), ∃ (n : ℕ) (Γ : AccessStructure n),
    0 < n ∧ C * (n : ℝ) < optimalSecretSharingRatio Γ

def problem : OpenProblem where
  id := "secret-sharing-optimal-info-ratio"
  title := "Super-Linear Lower Bounds on the Optimal Information Ratio of Secret Sharing"
  category := .securityPrivacy
  status := .open
  posedBy := "László Csirmaz"
  posedYear := 1997
  statement := Statement

end InfoTheory.Problems.SecretSharingOptimalInfoRatio
