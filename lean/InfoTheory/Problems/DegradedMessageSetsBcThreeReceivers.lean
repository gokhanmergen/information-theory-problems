import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DegradedMessageSetsBcThreeReceivers

/-- Three-receiver Discrete Memoryless Broadcast Channel `p(y₁, y₂, y₃ | x)`. -/
abbrev BroadcastChannel3 (X Y₁ Y₂ Y₃ : Type*)
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃] :=
  DMC X (Y₁ × Y₂ × Y₃)

/-- Operational achievability of `(R₀, R₁)` over a 3-DMBC with two degraded message sets:
    the common message `M₀` (rate `R₀`) must be decoded by all three receivers and the private
    message `M₁` (rate `R₁`) by receiver `Y₁` only. Average error probability over uniformly
    distributed `(M₀, M₁)`; an error occurs if any receiver errs on any message it must decode. -/
def IsDMS3Achievable {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (R₀ R₁ : ℝ) : Prop :=
  0 ≤ R₀ ∧ 0 ≤ R₁ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₀ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀)))
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    ∃ (enc : Fin M₀ → Fin M₁ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₀)
      (dec₃ : (Fin n → Y₃) → Fin M₀),
      let err := ((1 : ℝ) / ((M₀ * M₁ : ℕ) : ℝ)) *
        ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ y : Fin n → Y₁ × Y₂ × Y₃,
          if dec₁ (fun i => (y i).1) ≠ (m₀, m₁) ∨
             dec₂ (fun i => (y i).2.1) ≠ m₀ ∨
             dec₃ (fun i => (y i).2.2) ≠ m₀
          then (W.power n).trans (enc m₀ m₁) y else 0
      err ≤ ε

/-- Capacity region (closed) of the 3-DMBC with two degraded message sets
    (`M₀` to all receivers, `M₁` to `Y₁` only). -/
def dms3CapacityRegion {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ) :=
  closure { r | IsDMS3Achievable W r.1 r.2 }

/-- Nair–El Gamal inner bound (superposition coding, Marton-type binning of two satellite
    layers, and indirect decoding; Nair–El Gamal 2009, Prop. 5; El Gamal–Kim §8.2), closed.

    Auxiliaries `(U₁, U₂, U₃)` with an arbitrary joint law `p(u₁, u₂, u₃, x)`; the satellite
    codewords are `V₂ = (U₁, U₂)` and `V₃ = (U₁, U₃)`. With this substitution the two Markov
    chains `U₁ → V₂ → (V₃, X)` and `U₁ → V₃ → (V₂, X)` required in Prop. 5 hold automatically,
    and every distribution satisfying them arises this way (Nair–El Gamal 2009, Remark 1 after
    Prop. 5), so the union below equals the region of Prop. 5. The constraints are, with
    `I(X; Y₁ | V₂, V₃) = I(X; Y₁ | U₁, U₂, U₃)`:
    `R₀ ≤ min{I(V₂;Y₂), I(V₃;Y₃)}`,
    `2R₀ ≤ I(V₂;Y₂) + I(V₃;Y₃) - I(V₂;V₃|U₁)`,
    `R₁ ≤ min{I(X;Y₁|V₂) + I(X;Y₁|V₃), I(X;Y₁|U₁)}`,
    `R₀ + R₁ ≤ min{I(X;Y₁), I(V₂;Y₂) + I(X;Y₁|V₂), I(V₃;Y₃) + I(X;Y₁|V₃)}`,
    `2R₀ + R₁ ≤ I(V₂;Y₂) + I(V₃;Y₃) + I(X;Y₁|V₂,V₃) - I(V₂;V₃|U₁)`,
    `2R₀ + 2R₁ ≤ I(V₂;Y₂) + I(X;Y₁|V₂) + I(V₃;Y₃) + I(X;Y₁|V₃) - I(V₂;V₃|U₁)`. -/
def nairElGamalInnerBound {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (k₁ k₂ k₃ : ℕ) (P : ProbDist (Fin k₁ × Fin k₂ × Fin k₃ × X)),
      let J : ProbDist ((Fin k₁ × Fin k₂ × Fin k₃ × X) × (Y₁ × Y₂ × Y₃)) :=
        { pmf := fun z => P.pmf z.1 * W.trans z.1.2.2.2 z.2
          nonneg := fun z => mul_nonneg (P.nonneg z.1) (W.nonneg z.1.2.2.2 z.2)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, W.sum_one, mul_one, P.sum_one] }
      let IV2Y2 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.1), z.2.2.1)))
      let IV3Y3 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2.2)))
      let IV2V3gU1 := condMutualInfo (P.map (fun t => ((t.1, t.2.1), (t.1, t.2.2.1), t.1)))
      let IXY1gV2 := condMutualInfo (J.map (fun z => (z.1.2.2.2, z.2.1, (z.1.1, z.1.2.1))))
      let IXY1gV3 := condMutualInfo (J.map (fun z => (z.1.2.2.2, z.2.1, (z.1.1, z.1.2.2.1))))
      let IXY1gU1 := condMutualInfo (J.map (fun z => (z.1.2.2.2, z.2.1, z.1.1)))
      let IXY1gV23 := condMutualInfo
        (J.map (fun z => (z.1.2.2.2, z.2.1, (z.1.1, z.1.2.1, z.1.2.2.1))))
      let IXY1 := mutualInfo (J.map (fun z => (z.1.2.2.2, z.2.1)))
      r.1 ≤ IV2Y2 ∧ r.1 ≤ IV3Y3 ∧
      2 * r.1 ≤ IV2Y2 + IV3Y3 - IV2V3gU1 ∧
      r.2 ≤ IXY1gV2 + IXY1gV3 ∧ r.2 ≤ IXY1gU1 ∧
      r.1 + r.2 ≤ IXY1 ∧
      r.1 + r.2 ≤ IV2Y2 + IXY1gV2 ∧
      r.1 + r.2 ≤ IV3Y3 + IXY1gV3 ∧
      2 * r.1 + r.2 ≤ IV2Y2 + IV3Y3 + IXY1gV23 - IV2V3gU1 ∧
      2 * r.1 + 2 * r.2 ≤ IV2Y2 + IXY1gV2 + IV3Y3 + IXY1gV3 - IV2V3gU1 }

/-- Three-Receiver Broadcast Channel with Two Degraded Message Sets (Körner–Marton 1977;
    Nair–El Gamal 2009): with a common message to all three receivers and a private message to
    receiver `Y₁` only, does the Nair–El Gamal superposition/indirect-decoding inner bound equal
    the capacity region for every finite-alphabet 3-DMBC? -/
def Statement : Prop :=
  ∀ (kX kY₁ kY₂ kY₃ : ℕ) (W : BroadcastChannel3 (Fin kX) (Fin kY₁) (Fin kY₂) (Fin kY₃)),
    dms3CapacityRegion W = nairElGamalInnerBound W

def problem : OpenProblem where
  id := "degraded-message-sets-bc-three-receivers"
  title := "Three-Receiver Broadcast Channel with Two Degraded Message Sets"
  category := .networkInfoTheory
  status := .open
  posedBy := "János Körner and Katalin Marton; Chandra Nair and Abbas El Gamal"
  posedYear := 2009
  statement := Statement

end InfoTheory.Problems.DegradedMessageSetsBcThreeReceivers
