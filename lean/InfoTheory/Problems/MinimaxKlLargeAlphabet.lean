import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MinimaxKlLargeAlphabet

/-- Empirical count of symbol `a` in a length-`n` sample `x : Fin n → Fin k`. -/
def countOcc {k n : ℕ} (x : Fin n → Fin k) (a : Fin k) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i = a)).card

/-- Predicate that an estimator `est` belongs to the two-parameter Braess–Sauer (2004)
    add-constant family: weight `β₀` for unseen symbols (`count = 0`) and `count + β₁`
    for seen symbols (`count ≥ 1`), normalized to a probability distribution. -/
def IsBraessSauerEst {k n : ℕ} (β₀ β₁ : ℝ)
    (est : (Fin n → Fin k) → ProbDist (Fin k)) : Prop :=
  0 < β₀ ∧ 0 < β₁ ∧
  ∀ (x : Fin n → Fin k),
    let weight (a : Fin k) : ℝ :=
      if countOcc x a = 0 then β₀ else (countOcc x a : ℝ) + β₁
    let Z : ℝ := ∑ a : Fin k, weight a
    ∀ (a : Fin k), (est x).pmf a = weight a / Z

/-- Minimax KL risk restricted to the two-parameter Braess–Sauer estimator family. -/
noncomputable def braessSauerKLRisk (k n : ℕ) : ℝ :=
  sInf { R : ℝ | ∃ (β₀ β₁ : ℝ) (est : (Fin n → Fin k) → ProbDist (Fin k)),
    IsBraessSauerEst β₀ β₁ est ∧
    ∀ (P : ProbDist (Fin k)),
      (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x)) ≤ R }

/-- Asymptotic minimax optimality of the two-parameter Braess–Sauer family in the
    high-dimensional proportional regime `k / n → α ∈ (0, ∞)`: does `braessSauerKLRisk`
    match the exact minimax KL risk `minimaxKLRisk` up to `o(1)` for every `α > 0`? -/
def Statement : Prop :=
  ∀ (α ε : ℝ), 0 < α → 0 < ε →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      let k := Nat.max 2 (Nat.floor (α * (n : ℝ)))
      braessSauerKLRisk k n ≤ minimaxKLRisk k n + ε

def problem : OpenProblem where
  id := "minimax-kl-large-alphabet"
  title := "Exact Leading Constant of Minimax KL Risk for Large-Alphabet Distribution Estimation"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Dietrich Braess and Thomas Sauer; Sudeep Kamath, Alon Orlitsky, Dheeraj Pichapati, and Ananda Theertha Suresh"
  posedYear := 2004
  statement := Statement

end InfoTheory.Problems.MinimaxKlLargeAlphabet
