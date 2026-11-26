import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CommonInformationExactVsWyner

/-- `n`-letter i.i.d. product distribution of a bipartite source `P : ProbDist (X × Y)`. -/
def bipartitePower {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) (n : ℕ) : ProbDist ((Fin n → X) × (Fin n → Y)) where
  pmf := fun xy => ∏ i : Fin n, P.pmf (xy.1 i, xy.2 i)
  nonneg := fun xy => Finset.prod_nonneg (fun i _ => P.nonneg _)
  sum_one := by
    let e : (Fin n → X) × (Fin n → Y) ≃ (Fin n → X × Y) :=
      { toFun := fun xy i => (xy.1 i, xy.2 i)
        invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun _ => rfl }
    have h : ∑ xy : (Fin n → X) × (Fin n → Y), ∏ i : Fin n, P.pmf (xy.1 i, xy.2 i) =
        ∑ z : Fin n → X × Y, ∏ i : Fin n, P.pmf (z i) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [h, ← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun _ _ => P.sum_one)

/-- Finite-Letter Attainment Problem for Exact Common Information
    (Kumar–Li–El Gamal 2014; Yu–Tan 2020):
    It is known that `wynerCommonInfo P ≤ exactCommonInfo P ≤ exactCommonInfoSingle P`,
    that `wynerCommonInfo P < exactCommonInfo P` for doubly symmetric binary sources
    (Yu–Tan 2020), and that `exactCommonInfo P = wynerCommonInfo P < exactCommonInfoSingle P`
    can occur (e.g., SBES with `e > 1/2`, Kumar–Li–El Gamal 2014).
    Does every finite-alphabet bipartite source `P` attain its exact common information
    at some finite blocklength `n ≥ 1`, i.e., `exactCommonInfo P = exactCommonInfoSingle (P^{⊗ n}) / n`? -/
def Statement : Prop :=
  ∀ (kX kY : ℕ), 0 < kX → 0 < kY →
    ∀ (P : ProbDist (Fin kX × Fin kY)),
      ∃ n : ℕ, 0 < n ∧ exactCommonInfo P = exactCommonInfoSingle (bipartitePower P n) / (n : ℝ)

def problem : OpenProblem where
  id := "common-information-exact-vs-wyner"
  title := "Finite-Letter Attainment and Single-Letter Characterization of Exact Common Information"
  category := .sourceCoding
  status := .open
  posedBy := "Gowtham R. Kumar, Cheuk Ting Li, and Abbas El Gamal; Lei Yu and Vincent Y. F. Tan"
  posedYear := 2014
  statement := Statement

end InfoTheory.Problems.CommonInformationExactVsWyner
