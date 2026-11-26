import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CognitiveInterferenceChannel

/-- Operational capacity region (closed) of a two-user discrete memoryless cognitive
    interference channel: transmitter 1 knows `M₁`, cognitive transmitter 2 knows `(M₁, M₂)`,
    receiver 1 decodes `M₁`, and receiver 2 decodes `M₂`. -/
def cognitiveICCapacityRegion {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * r.1)))
      let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * r.2)))
      ∃ (enc₁ : Fin M₁ → Fin n → X₁)
        (enc₂ : Fin M₁ → Fin M₂ → Fin n → X₂)
        (dec₁ : (Fin n → Y₁) → Fin M₁)
        (dec₂ : (Fin n → Y₂) → Fin M₂),
        let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
            if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
            then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₁ m₂ i)) y else 0
        err ≤ ε }

/-- Rini–Tuninetti–Devroye (2011, Theorem 7) unified single-letter inner bound (with
    time-sharing / convex hull closure) for the discrete memoryless cognitive IC. -/
def rtdInnerBound {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kQ k₀ k₁p k₂c k₂p : ℕ)
      (Pq : ProbDist (Fin kQ))
      (P : Fin kQ → ProbDist (Fin k₀ × Fin k₁p × Fin k₂c × Fin k₂p × X₁ × X₂))
      (r₁c r₁p r₂c r₂p rp₁p rp₂c rp₂p : ℝ),
      0 ≤ r₁c ∧ 0 ≤ r₁p ∧ 0 ≤ r₂c ∧ 0 ≤ r₂p ∧
      0 ≤ rp₁p ∧ 0 ≤ rp₂c ∧ 0 ≤ rp₂p ∧
      r.1 = r₁c + r₁p ∧ r.2 = r₂c + r₂p ∧
      let J : ProbDist (Fin kQ × (Fin k₀ × Fin k₁p × Fin k₂c × Fin k₂p × X₁ × X₂) × (Y₁ × Y₂)) :=
        { pmf := fun z => Pq.pmf z.1 * (P z.1).pmf z.2.1 *
            W.trans (z.2.1.2.2.2.2.1, z.2.1.2.2.2.2.2) z.2.2
          nonneg := fun z => mul_nonneg (mul_nonneg (Pq.nonneg _) ((P _).nonneg _)) (W.nonneg _ _)
          sum_one := by
            simp_rw [Fintype.sum_prod_type]
            have hW : ∀ x₁ x₂, ∑ y₁ : Y₁, ∑ y₂ : Y₂, W.trans (x₁, x₂) (y₁, y₂) = 1 :=
              fun x₁ x₂ => by rw [← Fintype.sum_prod_type]; exact W.sum_one (x₁, x₂)
            simp_rw [← Finset.mul_sum, hW, mul_one]
            have hP : ∀ q, ∑ a : Fin k₀, ∑ b : Fin k₁p, ∑ c : Fin k₂c, ∑ d : Fin k₂p,
                ∑ x₁ : X₁, ∑ x₂ : X₂, (P q).pmf (a, b, c, d, x₁, x₂) = 1 := fun q => by
              simpa [Fintype.sum_prod_type] using (P q).sum_one
            simp_rw [← Finset.mul_sum, hP, mul_one, Pq.sum_one] }
      let bin2c := condMutualInfo (J.map (fun z => (z.2.1.2.2.1, z.2.1.2.2.2.2.1, (z.2.1.1, z.1))))
      let bin2p := condMutualInfo (J.map (fun z =>
        (z.2.1.2.2.2.1, z.2.1.2.2.2.2.1, (z.2.1.1, z.2.1.2.2.1, z.1))))
      let bin12p := condMutualInfo (J.map (fun z =>
        (z.2.1.2.1, z.2.1.2.2.2.1, (z.2.1.1, z.2.1.2.2.2.2.1, z.2.1.2.2.1, z.1))))
      let bin2cp := condMutualInfo (J.map (fun z =>
        ((z.2.1.2.2.1, z.2.1.2.2.2.1), z.2.1.2.2.2.2.1, (z.2.1.1, z.1))))
      let bin12cp := condMutualInfo (J.map (fun z =>
        (z.2.1.2.1, (z.2.1.2.2.1, z.2.1.2.2.2.1), (z.2.1.1, z.2.1.2.2.2.2.1, z.1))))
      let pen1 := condMutualInfo (J.map (fun z =>
        ((z.2.1.2.2.2.2.1, z.2.1.2.1), z.2.1.2.2.1, (z.2.1.1, z.1))))
      rp₂c ≥ bin2c ∧
      rp₂p ≥ bin2p ∧
      rp₁p + rp₂p ≥ bin2p + bin12p ∧
      rp₁p + rp₂c + rp₂p ≥ bin2cp + bin12cp ∧
      r₁p + rp₁p ≤ condMutualInfo (J.map (fun z =>
        ((z.2.1.2.2.2.2.1, z.2.1.2.1), z.2.2.1, (z.2.1.1, z.2.1.2.2.1, z.1)))) + pen1 ∧
      r₁p + r₂c + rp₁p + rp₂c ≤ condMutualInfo (J.map (fun z =>
        ((z.2.1.2.2.2.2.1, z.2.1.2.1, z.2.1.2.2.1), z.2.2.1, (z.2.1.1, z.1)))) + pen1 ∧
      r₁c + r₁p + r₂c + rp₁p + rp₂c ≤ condMutualInfo (J.map (fun z =>
        ((z.2.1.1, z.2.1.2.2.2.2.1, z.2.1.2.1, z.2.1.2.2.1), z.2.2.1, z.1))) + pen1 ∧
      r₂p + rp₂p ≤ condMutualInfo (J.map (fun z =>
        (z.2.1.2.2.2.1, z.2.2.2, (z.2.1.1, z.2.1.2.2.1, z.1)))) ∧
      r₂c + r₂p + rp₂c + rp₂p ≤ condMutualInfo (J.map (fun z =>
        ((z.2.1.2.2.1, z.2.1.2.2.2.1), z.2.2.2, (z.2.1.1, z.1)))) ∧
      r₁c + r₂c + r₂p + rp₂c + rp₂p ≤ condMutualInfo (J.map (fun z =>
        ((z.2.1.1, z.2.1.2.2.1, z.2.1.2.2.2.1), z.2.2.2, z.1))) }

/-- Capacity Region of the Discrete Memoryless Cognitive Interference Channel
    (Devroye–Mitran–Tarokh 2006; Rini–Tuninetti–Devroye 2011):
    Does the Rini–Tuninetti–Devroye single-letter inner bound characterize the exact
    capacity region of every finite-alphabet discrete memoryless cognitive interference
    channel? -/
def Statement : Prop :=
  ∀ (kX₁ kX₂ kY₁ kY₂ : ℕ) (W : InterferenceChannel (Fin kX₁) (Fin kX₂) (Fin kY₁) (Fin kY₂)),
    cognitiveICCapacityRegion W = rtdInnerBound W

def problem : OpenProblem where
  id := "cognitive-interference-channel"
  title := "Capacity Region of the Discrete Memoryless Cognitive Interference Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Natasha Devroye, Patrick Mitran, and Vahid Tarokh"
  posedYear := 2006
  statement := Statement

end InfoTheory.Problems.CognitiveInterferenceChannel
