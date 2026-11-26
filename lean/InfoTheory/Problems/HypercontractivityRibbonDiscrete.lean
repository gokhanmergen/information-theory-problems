import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.HypercontractivityRibbonDiscrete

/-- Exact Nair (2014) KL characterization of the forward hypercontractivity ribbon
    `R(P_XY)` for `1 < p ≤ q` (whose slope at `(1, 1)` recovers `inHypercontractivityRibbon`). -/
def inFullHypercontractivityRibbon {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) (p q : ℝ) : Prop :=
  1 < p ∧ p ≤ q ∧
  ∀ (Q : ProbDist (X × Y)),
    AbsCont Q P →
    (1 / p) * klDivergence Q.fst P.fst + (1 - 1 / q) * klDivergence Q.snd P.snd ≤
      klDivergence Q P

/-- Predicate that a real function on a finite type takes at most two distinct values. -/
def IsTwoValued {α : Type*} (f : α → ℝ) : Prop :=
  ∃ (a b : ℝ), ∀ (x : α), f x = a ∨ f x = b

/-- Two-valued functional hypercontractivity test for `(p, q)` with `1 < p ≤ q`
    (with dual exponent `q' = q / (q - 1)`). -/
def passesTwoValuedHCTest {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) (p q : ℝ) : Prop :=
  let q' := q / (q - 1)
  ∀ (f : X → ℝ) (g : Y → ℝ),
    (∀ (x : X), 0 ≤ f x) → (∀ (y : Y), 0 ≤ g y) →
    IsTwoValued f → IsTwoValued g →
    ∑ xy : X × Y, P.pmf xy * f xy.1 * g xy.2 ≤
      (∑ x : X, P.fst.pmf x * (f x) ^ p) ^ (1 / p) *
      (∑ y : Y, P.snd.pmf y * (g y) ^ q') ^ (1 / q')

/-- Two-Valued Extremizer Conjecture for the `q`-ary symmetric channel hypercontractivity
    ribbon: for every alphabet size `m ≥ 3`, crossover probability `α ∈ (0, 1)`, and
    exponents `1 < p ≤ q`, does testing only two-valued nonnegative functions suffice to
    certify membership `(p, q) ∈ R(P_XY)` of the uniform-input `m`-ary symmetric channel? -/
def Statement : Prop :=
  ∀ (m : ℕ) (hm : 3 ≤ m) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (p q : ℝ),
    1 < p → p ≤ q →
    haveI : Nonempty (Fin m) := ⟨⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hm⟩⟩
    let h2 : 2 ≤ m := Nat.le_trans (by decide : 2 ≤ 3) hm
    let P : ProbDist (Fin m × Fin m) := (qarySC m h2 α h0 h1).joint ProbDist.uniform
    passesTwoValuedHCTest P p q → inFullHypercontractivityRibbon P p q

def problem : OpenProblem where
  id := "hypercontractivity-ribbon-discrete"
  title := "Computable Characterization and Two-Valued Extremizers of the Discrete Hypercontractivity Ribbon"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Venkat Anantharam, Amin Gohari, Sudeep Kamath, and Chandra Nair"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.HypercontractivityRibbonDiscrete
