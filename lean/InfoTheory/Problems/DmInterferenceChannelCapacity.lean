import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DmInterferenceChannelCapacity

/-- `k`-fold memoryless product of a two-user discrete memoryless interference channel. -/
def icPower {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (k : ℕ) :
    InterferenceChannel (Fin k → X₁) (Fin k → X₂) (Fin k → Y₁) (Fin k → Y₂) where
  trans := fun x y => ∏ i : Fin k, W.trans (x.1 i, x.2 i) (y.1 i, y.2 i)
  nonneg := fun x y => Finset.prod_nonneg (fun i _ => W.nonneg _ _)
  sum_one := fun x => by
    let e : ((Fin k → Y₁) × (Fin k → Y₂)) ≃ (Fin k → Y₁ × Y₂) :=
      { toFun := fun p i => (p.1 i, p.2 i)
        invFun := fun f => (fun i => (f i).1, fun i => (f i).2)
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun _ => rfl }
    have h : ∑ p : (Fin k → Y₁) × (Fin k → Y₂), ∏ i : Fin k, W.trans (x.1 i, x.2 i) (p.1 i, p.2 i) =
        ∑ f : Fin k → Y₁ × Y₂, ∏ i : Fin k, W.trans (x.1 i, x.2 i) (f i) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    rw [h, ← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun i _ => W.sum_one (x.1 i, x.2 i))

/-- Single-letter Han–Kobayashi inner bound in the equivalent compact CMGE (2008) /
    El Gamal–Kim (2011, Theorem 6.4) representation. -/
def hanKobayashiRegion {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kQ kU₁ kU₂ : ℕ) (Pq : ProbDist (Fin kQ))
      (P₁ : Fin kQ → ProbDist (Fin kU₁ × X₁))
      (P₂ : Fin kQ → ProbDist (Fin kU₂ × X₂)),
      let J : ProbDist (Fin kQ × (Fin kU₁ × X₁) × (Fin kU₂ × X₂) × (Y₁ × Y₂)) :=
        { pmf := fun t => Pq.pmf t.1 * (P₁ t.1).pmf t.2.1 * (P₂ t.1).pmf t.2.2.1 *
            W.trans (t.2.1.2, t.2.2.1.2) t.2.2.2
          nonneg := fun t => mul_nonneg (mul_nonneg (mul_nonneg (Pq.nonneg _)
            ((P₁ _).nonneg _)) ((P₂ _).nonneg _)) (W.nonneg _ _)
          sum_one := by
            simp_rw [Fintype.sum_prod_type]
            have hW : ∀ x₁ x₂, ∑ y₁ : Y₁, ∑ y₂ : Y₂, W.trans (x₁, x₂) (y₁, y₂) = 1 :=
              fun x₁ x₂ => by rw [← Fintype.sum_prod_type]; exact W.sum_one (x₁, x₂)
            simp_rw [← Finset.mul_sum, hW, mul_one]
            have h2 : ∀ q, ∑ u₂ : Fin kU₂, ∑ x₂ : X₂, (P₂ q).pmf (u₂, x₂) = 1 :=
              fun q => by rw [← Fintype.sum_prod_type]; exact (P₂ q).sum_one
            simp_rw [← Finset.mul_sum, h2, mul_one]
            have h1 : ∀ q, ∑ u₁ : Fin kU₁, ∑ x₁ : X₁, (P₁ q).pmf (u₁, x₁) = 1 :=
              fun q => by rw [← Fintype.sum_prod_type]; exact (P₁ q).sum_one
            simp_rw [← Finset.mul_sum, h1, mul_one, Pq.sum_one] }
      let a1 := condMutualInfo (J.map (fun t => (t.2.1.2, t.2.2.2.1, (t.2.2.1.1, t.1))))
      let a2 := condMutualInfo (J.map (fun t => (t.2.2.1.2, t.2.2.2.2, (t.2.1.1, t.1))))
      let b1 := condMutualInfo (J.map (fun t => ((t.2.1.2, t.2.2.1.1), t.2.2.2.1, t.1)))
      let b2 := condMutualInfo (J.map (fun t => ((t.2.2.1.2, t.2.1.1), t.2.2.2.2, t.1)))
      let c1 := condMutualInfo (J.map (fun t => (t.2.1.2, t.2.2.2.1, (t.2.1.1, t.2.2.1.1, t.1))))
      let c2 := condMutualInfo (J.map (fun t => (t.2.2.1.2, t.2.2.2.2, (t.2.1.1, t.2.2.1.1, t.1))))
      let d1 := condMutualInfo (J.map (fun t => ((t.2.1.2, t.2.2.1.1), t.2.2.2.1, (t.2.1.1, t.1))))
      let d2 := condMutualInfo (J.map (fun t => ((t.2.2.1.2, t.2.1.1), t.2.2.2.2, (t.2.2.1.1, t.1))))
      r.1 ≤ a1 ∧
      r.2 ≤ a2 ∧
      r.1 + r.2 ≤ b1 + c2 ∧
      r.1 + r.2 ≤ c1 + b2 ∧
      r.1 + r.2 ≤ d1 + d2 ∧
      2 * r.1 + r.2 ≤ b1 + c1 + d2 ∧
      r.1 + 2 * r.2 ≤ b2 + c2 + d1 }

/-- Normalized `k`-letter Han–Kobayashi inner bound (closed) `cl((1/k) R_HK(W^{⊗ k}))`. -/
def hanKobayashiKLetterRegion {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (k : ℕ) (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { r | ((k : ℝ) * r.1, (k : ℝ) * r.2) ∈ hanKobayashiRegion (icPower W k) }

/-- Capacity Region of the General Discrete Memoryless Interference Channel
    (Ahlswede 1974; Han–Kobayashi 1981; Nair–Xia–Yazdanpanah 2015):
    Given that single-letter Han–Kobayashi (`k = 1`) is strictly suboptimal for some DM-ICs,
    does every finite-alphabet two-user DM-IC achieve its exact capacity region at some
    finite blocklength `k ≥ 1` of the `k`-letter Han–Kobayashi hierarchy? -/
def Statement : Prop :=
  ∀ (kX₁ kX₂ kY₁ kY₂ : ℕ) (W : InterferenceChannel (Fin kX₁) (Fin kX₂) (Fin kY₁) (Fin kY₂)),
    ∃ k : ℕ, 0 < k ∧ icCapacityRegion W = hanKobayashiKLetterRegion k W

def problem : OpenProblem where
  id := "dm-interference-channel-capacity"
  title := "Capacity Region of the General Discrete Memoryless Interference Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Rudolf Ahlswede"
  posedYear := 1974
  statement := Statement

end InfoTheory.Problems.DmInterferenceChannelCapacity
