import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.LiMedardConjecture

/-- The Bonami–Beckner noise operator `(T_ρ f)(y) = E[f(X) | Y = y]` for `X ~ Uniform({0,1}^n)`
    and `Y = BSC(α)^n(X)`. -/
noncomputable def noiseOp (n : ℕ) (α : ℝ) (f : (Fin n → Bool) → Bool) (y : Fin n → Bool) : ℝ :=
  ∑ x : Fin n → Bool,
    (∏ i : Fin n, if x i = y i then 1 - α else α) * (if f x then (1 : ℝ) else 0)

/-- Li–Médard Conjecture (2018): for all `n ≥ 1`, `α ∈ (0, 1/2)`, `q ∈ (1, 2]`, and every
    balanced Boolean function `f : {0,1}^n → {0,1}`, the `q`-th moment `E[(T_ρ f(Y))^q]`
    is maximized by dictator functions, attaining `(α^q + (1 - α)^q) / 2`. -/
def Statement : Prop :=
  ∀ (n : ℕ) (α q : ℝ),
    1 ≤ n → 0 < α → α < 1 / 2 → 1 < q → q ≤ 2 →
    ∀ (f : (Fin n → Bool) → Bool),
      2 * (Finset.univ.filter (fun x : Fin n → Bool => f x = true)).card = 2 ^ n →
      ((1 : ℝ) / ((2 : ℝ) ^ n)) * ∑ y : Fin n → Bool, (noiseOp n α f y) ^ q ≤
        (α ^ q + (1 - α) ^ q) / 2

def problem : OpenProblem where
  id := "li-medard-conjecture"
  title := "The Li–Médard Conjecture on Noisy Boolean Functions"
  category := .entropyInequalities
  status := .open
  posedBy := "Jiange Li and Muriel Médard"
  posedYear := 2018
  statement := Statement

end InfoTheory.Problems.LiMedardConjecture
