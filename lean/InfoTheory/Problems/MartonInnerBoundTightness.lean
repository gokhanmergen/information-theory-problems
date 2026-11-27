import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MartonInnerBoundTightness

/-- Operational achievability of rate triple `(R₀, R₁, R₂)` (common message `M₀`,
    private messages `M₁, M₂`) over a two-receiver DMBC `W`. -/
def IsBCCommonAchievable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) (R₀ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₀ ∧ 0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₀ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀)))
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc : Fin M₀ → Fin M₁ → Fin M₂ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₀ × Fin M₂),
      let err := ((1 : ℝ) / ((M₀ * M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          if dec₁ (fun i => (y i).1) ≠ (m₀, m₁) ∨ dec₂ (fun i => (y i).2) ≠ (m₀, m₂)
          then (W.power n).trans (enc m₀ m₁ m₂) y else 0
      err ≤ ε

/-- Full common-and-private-message capacity region (closed) `C_com(W)` of a 2-DMBC. -/
def bcCommonCapacityRegion {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ × ℝ) :=
  closure { r | IsBCCommonAchievable W r.1 r.2.1 r.2.2 }

/-- Marton's inner bound (closed) with a common message (Marton 1979; Liang–Kramer 2007;
    El Gamal–Kim 2011, Theorem 8.4). -/
def martonCommonInnerBound {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧
    ∃ (k₀ k₁ k₂ : ℕ) (P : ProbDist (Fin k₀ × Fin k₁ × Fin k₂ × X)),
      let J : ProbDist ((Fin k₀ × Fin k₁ × Fin k₂ × X) × (Y₁ × Y₂)) :=
        { pmf := fun z => P.pmf z.1 * W.trans z.1.2.2.2 z.2
          nonneg := fun z => mul_nonneg (P.nonneg z.1) (W.nonneg z.1.2.2.2 z.2)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, W.sum_one, mul_one, P.sum_one] }
      let I01_Y1 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.1), z.2.1)))
      let I02_Y2 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)))
      let I1_Y1_0 := condMutualInfo (J.map (fun z => (z.1.2.1, z.2.1, z.1.1)))
      let I2_Y2_0 := condMutualInfo (J.map (fun z => (z.1.2.2.1, z.2.2, z.1.1)))
      let I12_0 := condMutualInfo (P.map (fun t => (t.2.1, t.2.2.1, t.1)))
      r.1 + r.2.1 ≤ I01_Y1 ∧
      r.1 + r.2.2 ≤ I02_Y2 ∧
      r.1 + r.2.1 + r.2.2 ≤ I01_Y1 + I2_Y2_0 - I12_0 ∧
      r.1 + r.2.1 + r.2.2 ≤ I1_Y1_0 + I02_Y2 - I12_0 ∧
      2 * r.1 + r.2.1 + r.2.2 ≤ I01_Y1 + I02_Y2 - I12_0 }

/-- Tightness of Marton's Inner Bound with a Common Message (Marton 1979):
    Does Marton's five-inequality inner bound with common message equal the exact
    capacity region `(R₀, R₁, R₂)` for every finite-alphabet two-receiver DMBC? -/
def Statement : Prop :=
  ∀ (kX kY₁ kY₂ : ℕ) (W : BroadcastChannel (Fin kX) (Fin kY₁) (Fin kY₂)),
    bcCommonCapacityRegion W = martonCommonInnerBound W

def problem : OpenProblem where
  id := "marton-inner-bound-tightness"
  title := "Tightness of Marton's Inner Bound with a Common Message"
  category := .networkInfoTheory
  status := .open
  posedBy := "Katalin Marton"
  posedYear := 1979
  statement := Statement

end InfoTheory.Problems.MartonInnerBoundTightness
