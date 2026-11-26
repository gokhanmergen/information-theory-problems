import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.PrimitiveRelayChannelBsc

/-- Product of two independent binary symmetric channels `BSC(p₁) × BSC(p₂)` from source `X`
    to destination `Y` and relay `Yr`. -/
def bscRelayBroadcast (p₁ p₂ : ℝ) (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) : DMC Bool (Bool × Bool) where
  trans := fun x y =>
    (if x = y.1 then 1 - p₁ else p₁) * (if x = y.2 then 1 - p₂ else p₂)
  nonneg := fun x y => by
    apply mul_nonneg <;> split_ifs <;> linarith
  sum_one := fun x => by
    cases x <;> simp [Fintype.sum_prod_type] <;> ring

/-- Operational achievability of rate `R` over the primitive BSC relay channel with
    crossover probabilities `(p₁, p₂)` and noiseless relay bit-pipe rate `R₀`. -/
def IsPrimitiveBscAchievable (p₁ p₂ : ℝ) (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) (R₀ R : ℝ) : Prop :=
  0 ≤ R ∧
  let W := bscRelayBroadcast p₁ p₂ h10 h11 h20 h21
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    let M₀ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀)))
    ∃ (enc : Fin M → Fin n → Bool)
      (relay : (Fin n → Bool) → Fin M₀)
      (dec : (Fin n → Bool) → Fin M₀ → Fin M),
      let err := ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ y : Fin n → Bool × Bool,
          if dec (fun i => (y i).1) (relay (fun i => (y i).2)) ≠ m
          then (W.power n).trans (enc m) y else 0
      err ≤ ε

/-- Capacity `C_BSC(p₁, p₂, R₀)` of the primitive relay channel with BSC components. -/
noncomputable def primitiveBscRelayCapacity (p₁ p₂ : ℝ) (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) (R₀ : ℝ) : ℝ :=
  sSup { R : ℝ | IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 R₀ R }

/-- Partial decode-and-forward achievable rate for the primitive BSC relay channel. -/
noncomputable def primitiveBscPDFRate (p₁ p₂ : ℝ) (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) (R₀ : ℝ) : ℝ :=
  let W := bscRelayBroadcast p₁ p₂ h10 h11 h20 h21
  sSup { r : ℝ | ∃ (kU : ℕ) (Pux : ProbDist (Fin kU × Bool)),
    let J : ProbDist ((Fin kU × Bool) × (Bool × Bool)) :=
      { pmf := fun z => Pux.pmf z.1 * W.trans z.1.2 z.2
        nonneg := fun z => mul_nonneg (Pux.nonneg z.1) (W.nonneg z.1.2 z.2)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, W.sum_one, mul_one, Pux.sum_one] }
    let b1 := mutualInfo (J.map (fun z => (z.1.2, z.2.1))) + R₀
    let b2 := mutualInfo (J.map (fun z => (z.1.1, z.2.2))) +
              condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1)))
    r = min b1 b2 }

/-- Compress-and-forward (noisy network coding) achievable rate for the primitive BSC
    relay channel. -/
noncomputable def primitiveBscCFRate (p₁ p₂ : ℝ) (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1)
    (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) (R₀ : ℝ) : ℝ :=
  let W := bscRelayBroadcast p₁ p₂ h10 h11 h20 h21
  sSup { r : ℝ | ∃ (kU : ℕ) (Px : ProbDist Bool) (Q : DMC Bool (Fin kU)),
    let J : ProbDist (Bool × (Bool × Bool) × Fin kU) :=
      { pmf := fun t => Px.pmf t.1 * W.trans t.1 t.2.1 * Q.trans t.2.1.2 t.2.2
        nonneg := fun t => mul_nonneg (mul_nonneg (Px.nonneg _) (W.nonneg _ _)) (Q.nonneg _ _)
        sum_one := by
          simp_rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, Q.sum_one, mul_one]
          have hW : ∀ x, ∑ y : Bool, ∑ yr : Bool, W.trans x (y, yr) = 1 := fun x => by
            rw [← Fintype.sum_prod_type]; exact W.sum_one x
          simp_rw [← Finset.mul_sum, hW, mul_one, Px.sum_one] }
    let b1 := mutualInfo (J.map (fun t => (t.1, (t.2.1.1, t.2.2))))
    let b2 := mutualInfo (J.map (fun t => (t.1, t.2.1.1))) + R₀ -
              condMutualInfo (J.map (fun t => (t.2.2, t.2.1.2, (t.1, t.2.1.1))))
    r = min b1 b2 }

/-- Capacity of the Primitive Relay Channel with BSC Components (Cover 1987; Kim 2007):
    Is the capacity of every primitive BSC relay channel `(p₁, p₂, R₀)` achieved by the
    maximum of partial decode-and-forward and compress-and-forward? -/
def Statement : Prop :=
  ∀ (p₁ p₂ R₀ : ℝ) (h10 : 0 < p₁) (h11 : p₁ < 1 / 2)
    (h20 : 0 < p₂) (h21 : p₂ < 1 / 2), 0 ≤ R₀ →
    primitiveBscRelayCapacity p₁ p₂ (le_of_lt h10) (by linarith)
      (le_of_lt h20) (by linarith) R₀ =
    max (primitiveBscPDFRate p₁ p₂ (le_of_lt h10) (by linarith)
          (le_of_lt h20) (by linarith) R₀)
        (primitiveBscCFRate p₁ p₂ (le_of_lt h10) (by linarith)
          (le_of_lt h20) (by linarith) R₀)

def problem : OpenProblem where
  id := "primitive-relay-channel-bsc"
  title := "Capacity of the Primitive Relay Channel with BSC Components"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas Cover"
  posedYear := 1987
  statement := Statement

end InfoTheory.Problems.PrimitiveRelayChannelBsc
