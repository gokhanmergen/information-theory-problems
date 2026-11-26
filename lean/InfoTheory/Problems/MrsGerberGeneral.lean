import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MrsGerberGeneral

/-- Minimum sum-entropy `f_q(u, v) = inf { H(X + Y mod q) : H(X) ≥ u, H(Y) ≥ v }`
    for independent random variables `X, Y` on the cyclic group `ℤ/qℤ`. -/
noncomputable def minCyclicSumEntropy (q : ℕ) (hq : 0 < q) (u v : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ (P Q : ProbDist (Fin q)),
    u ≤ shannonEntropy P ∧ v ≤ shannonEntropy Q ∧
    r = shannonEntropy ((P.prod Q).map (fun xy => (⟨(xy.1.1 + xy.2.1) % q, Nat.mod_lt _ hq⟩ : Fin q))) }

/-- Generalized Mrs. Gerber's Lemma for Cyclic Groups (Jog–Anantharam Conjecture 1, 2014):
    for every cyclic group `ℤ/qℤ` (`q ≥ 2`) and every fixed `v ∈ [0, log₂ q]`, the minimum
    sum-entropy function `u ↦ f_q(u, v)` is convex on `[0, log₂ q]`. -/
def Statement : Prop :=
  ∀ (q : ℕ) (hq : 0 < q), 2 ≤ q →
    ∀ (v u₁ u₂ lam : ℝ),
      0 ≤ v → v ≤ log2 (q : ℝ) →
      0 ≤ u₁ → u₁ ≤ log2 (q : ℝ) →
      0 ≤ u₂ → u₂ ≤ log2 (q : ℝ) →
      0 ≤ lam → lam ≤ 1 →
      minCyclicSumEntropy q hq (lam * u₁ + (1 - lam) * u₂) v ≤
        lam * minCyclicSumEntropy q hq u₁ v + (1 - lam) * minCyclicSumEntropy q hq u₂ v

def problem : OpenProblem where
  id := "mrs-gerber-general"
  title := "Generalization of Mrs. Gerber's Lemma to Cyclic Groups"
  category := .entropyInequalities
  status := .open
  posedBy := "Aaron D. Wyner and Jacob Ziv; Varun Jog and Venkat Anantharam"
  posedYear := 1973
  statement := Statement

end InfoTheory.Problems.MrsGerberGeneral
