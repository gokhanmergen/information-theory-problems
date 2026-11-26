import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BroadcastChannelThreeReceivers

/-- Three-receiver Discrete Memoryless Broadcast Channel `p(y₁, y₂, y₃ | x)`. -/
abbrev BroadcastChannel3 (X Y₁ Y₂ Y₃ : Type*)
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃] :=
  DMC X (Y₁ × Y₂ × Y₃)

/-- Operational achievability of private-message rate triple `(R₁, R₂, R₃)` over a 3-DMBC `W`. -/
def IsBC3Achievable {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (R₁ R₂ R₃ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ 0 ≤ R₃ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    let M₃ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₃)))
    ∃ (enc : Fin M₁ → Fin M₂ → Fin M₃ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₂)
      (dec₃ : (Fin n → Y₃) → Fin M₃),
      let err := ((1 : ℝ) / ((M₁ * M₂ * M₃ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ m₃ : Fin M₃, ∑ y : Fin n → Y₁ × Y₂ × Y₃,
          if dec₁ (fun i => (y i).1) ≠ m₁ ∨
             dec₂ (fun i => (y i).2.1) ≠ m₂ ∨
             dec₃ (fun i => (y i).2.2) ≠ m₃
          then (W.power n).trans (enc m₁ m₂ m₃) y else 0
      err ≤ ε

/-- Capacity region (closed) `C₃(W)` of a three-receiver DMBC. -/
def bc3CapacityRegion {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ × ℝ) :=
  closure { r | IsBC3Achievable W r.1 r.2.1 r.2.2 }

/-- Three-receiver Marton inner bound with common cloud `W₀`, pairwise nested-superposition
    clouds `(W₁₂, W₁₃, W₂₃)`, and multivariate covering over `(U₁, U₂, U₃)`
    (Gohari–Anantharam; Nair–El Gamal 2009; El Gamal–Kim Ch. 8), closed. -/
def marton3InnerBound {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧
    ∃ (k₀ k₁₂ k₁₃ k₂₃ k₁ k₂ k₃ : ℕ)
      (P : ProbDist (Fin k₀ × (Fin k₁₂ × Fin k₁₃ × Fin k₂₃) × (Fin k₁ × Fin k₂ × Fin k₃) × X))
      (r₁₀ r₂₀ r₃₀ r₁₂ r₁₃ r₂₃ r₁₁ r₂₁ r₃₁ rp₁ rp₂ rp₃ : ℝ),
      0 ≤ r₁₀ ∧ 0 ≤ r₂₀ ∧ 0 ≤ r₃₀ ∧
      0 ≤ r₁₂ ∧ 0 ≤ r₁₃ ∧ 0 ≤ r₂₃ ∧
      0 ≤ r₁₁ ∧ 0 ≤ r₂₁ ∧ 0 ≤ r₃₁ ∧
      0 ≤ rp₁ ∧ 0 ≤ rp₂ ∧ 0 ≤ rp₃ ∧
      r.1 = r₁₀ + r₁₂ + r₁₃ + r₁₁ ∧
      r.2.1 = r₂₀ + r₂₃ + r₂₁ ∧
      r.2.2 = r₃₀ + r₃₁ ∧
      let J : ProbDist ((Fin k₀ × (Fin k₁₂ × Fin k₁₃ × Fin k₂₃) × (Fin k₁ × Fin k₂ × Fin k₃) × X) ×
          (Y₁ × Y₂ × Y₃)) :=
        { pmf := fun z => P.pmf z.1 * W.trans z.1.2.2.2 z.2
          nonneg := fun z => mul_nonneg (P.nonneg z.1) (W.nonneg z.1.2.2.2 z.2)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, W.sum_one, mul_one, P.sum_one] }
      let IW_Y1 := mutualInfo (J.map (fun z => (z.1.1, z.2.1)))
      let IW_Y2 := mutualInfo (J.map (fun z => (z.1.1, z.2.2.1)))
      let IW_Y3 := mutualInfo (J.map (fun z => (z.1.1, z.2.2.2)))
      let V1 (t : Fin k₀ × (Fin k₁₂ × Fin k₁₃ × Fin k₂₃) × (Fin k₁ × Fin k₂ × Fin k₃) × X) :=
        (t.2.1.1, t.2.1.2.1, t.2.2.1.1)
      let V2 (t : Fin k₀ × (Fin k₁₂ × Fin k₁₃ × Fin k₂₃) × (Fin k₁ × Fin k₂ × Fin k₃) × X) :=
        (t.2.1.1, t.2.1.2.2, t.2.2.1.2.1)
      let V3 (t : Fin k₀ × (Fin k₁₂ × Fin k₁₃ × Fin k₂₃) × (Fin k₁ × Fin k₂ × Fin k₃) × X) :=
        (t.2.1.2.1, t.2.1.2.2, t.2.2.1.2.2)
      let IV1_Y1 := condMutualInfo (J.map (fun z => (V1 z.1, z.2.1, z.1.1)))
      let IV2_Y2 := condMutualInfo (J.map (fun z => (V2 z.1, z.2.2.1, z.1.1)))
      let IV3_Y3 := condMutualInfo (J.map (fun z => (V3 z.1, z.2.2.2, z.1.1)))
      let I12 := condMutualInfo (P.map (fun t => (V1 t, V2 t, t.1)))
      let I13 := condMutualInfo (P.map (fun t => (V1 t, V3 t, t.1)))
      let I23 := condMutualInfo (P.map (fun t => (V2 t, V3 t, t.1)))
      let HV1 := condEntropy (P.map (fun t => (V1 t, t.1)))
      let HV2 := condEntropy (P.map (fun t => (V2 t, t.1)))
      let HV3 := condEntropy (P.map (fun t => (V3 t, t.1)))
      let HV123 := condEntropy (P.map (fun t => ((V1 t, V2 t, V3 t), t.1)))
      r₁₀ + r₂₀ + r₃₀ ≤ min IW_Y1 (min IW_Y2 IW_Y3) ∧
      r₁₂ + r₁₃ + r₁₁ + rp₁ ≤ IV1_Y1 ∧
      r₁₂ + r₂₃ + r₂₁ + rp₂ ≤ IV2_Y2 ∧
      r₁₃ + r₂₃ + r₃₁ + rp₃ ≤ IV3_Y3 ∧
      rp₁ + rp₂ ≥ I12 ∧
      rp₁ + rp₃ ≥ I13 ∧
      rp₂ + rp₃ ≥ I23 ∧
      rp₁ + rp₂ + rp₃ ≥ HV1 + HV2 + HV3 - HV123 }

/-- Capacity Region of the Three-Receiver Broadcast Channel (Cover 1972; Nair–El Gamal 2009):
    Does the three-receiver Marton inner bound (with common cloud and multivariate covering)
    equal the exact private-message capacity region for every finite-alphabet 3-DMBC? -/
def Statement : Prop :=
  ∀ (kX kY₁ kY₂ kY₃ : ℕ) (W : BroadcastChannel3 (Fin kX) (Fin kY₁) (Fin kY₂) (Fin kY₃)),
    bc3CapacityRegion W = marton3InnerBound W

def problem : OpenProblem where
  id := "broadcast-channel-three-receivers"
  title := "Capacity Region of the Three-Receiver Broadcast Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas Cover"
  posedYear := 1972
  statement := Statement

end InfoTheory.Problems.BroadcastChannelThreeReceivers
