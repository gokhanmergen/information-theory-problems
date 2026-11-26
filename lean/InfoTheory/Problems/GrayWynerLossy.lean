import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.GrayWynerLossy

/-- Operational achievability of `(R₀, R₁, R₂, D₁, D₂)` for the lossy Gray–Wyner network
    with correlated decoder side information `(Z₁, Z₂)`. -/
def IsLossyGWSIAchievable {X₁ X₂ Z₁ Z₂ Xh₁ Xh₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Z₁] [Fintype Z₂] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (R₀ R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  0 ≤ R₀ ∧ 0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₀ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₀ + ε))))
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))))
    ∃ (enc₀ : (Fin n → X₁ × X₂) → Fin M₀)
      (enc₁ : (Fin n → X₁ × X₂) → Fin M₁)
      (enc₂ : (Fin n → X₁ × X₂) → Fin M₂)
      (dec₁ : Fin M₀ × Fin M₁ × (Fin n → Z₁) → Fin n → Xh₁)
      (dec₂ : Fin M₀ × Fin M₂ × (Fin n → Z₂) → Fin n → Xh₂),
      let Pn (w : Fin n → X₁ × X₂ × Z₁ × Z₂) : ℝ := ∏ i : Fin n, P.pmf (w i)
      let avgD₁ := ∑ w : Fin n → X₁ × X₂ × Z₁ × Z₂, Pn w *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          let x := fun j => ((w j).1, (w j).2.1)
          d₁.dist (w i).1 (dec₁ (enc₀ x, enc₁ x, fun j => (w j).2.2.1) i))
      let avgD₂ := ∑ w : Fin n → X₁ × X₂ × Z₁ × Z₂, Pn w *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          let x := fun j => ((w j).1, (w j).2.1)
          d₂.dist (w i).2.1 (dec₂ (enc₀ x, enc₂ x, fun j => (w j).2.2.2) i))
      avgD₁ ≤ D₁ + ε ∧ avgD₂ ≤ D₂ + ε

/-- Single-letter Heegard–Berger / Kaspi / Gray–Wyner inner bound for the lossy Gray–Wyner
    network with decoder side information `(Z₁, Z₂)`. -/
def lossyGWSIInner {X₁ X₂ Z₁ Z₂ Xh₁ Xh₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Z₁] [Fintype Z₂] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (D₁ D₂ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧
    ∃ (k₀ k₁ k₂ : ℕ)
      (Q : ProbDist (X₁ × X₂ × Z₁ × Z₂ × Fin k₀ × Fin k₁ × Fin k₂))
      (g₁ : Fin k₀ × Fin k₁ × Z₁ → Xh₁)
      (g₂ : Fin k₀ × Fin k₂ × Z₂ → Xh₂)
      (r₀₀ r₀₁ r₀₂ : ℝ),
      0 ≤ r₀₀ ∧ 0 ≤ r₀₁ ∧ 0 ≤ r₀₂ ∧
      r.1 = r₀₀ + r₀₁ + r₀₂ ∧
      Q.map (fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2.1)) = P ∧
      -- Markov chain (U₀, U₁, U₂) - (X₁, X₂) - (Z₁, Z₂)
      condMutualInfo (Q.map (fun t =>
        ((t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2),
         (t.2.2.1, t.2.2.2.1),
         (t.1, t.2.1)))) = 0 ∧
      (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.1))) ≤ D₁ ∧
      (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.2.2.1, t.2.2.2.2.2.2, t.2.2.2.1))) ≤ D₂ ∧
      r₀₀ ≥ condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.1))) ∧
      r₀₀ ≥ condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.2.1))) ∧
      r₀₁ + r.2.1 ≥ condMutualInfo (Q.map (fun t =>
        ((t.1, t.2.1), t.2.2.2.2.2.1, (t.2.2.2.2.1, t.2.2.1)))) ∧
      r₀₂ + r.2.2 ≥ condMutualInfo (Q.map (fun t =>
        ((t.1, t.2.1), t.2.2.2.2.2.2, (t.2.2.2.2.1, t.2.2.2.1)))) }

/-- Closed convex hull (time-sharing closure) of the single-letter inner bound for the
    lossy Gray–Wyner network with decoder side information. -/
def InLossyGWSIClosure {X₁ X₂ Z₁ Z₂ Xh₁ Xh₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Z₁] [Fintype Z₂] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (R₀ R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  ∀ ε > 0, ∃ (m : ℕ) (w r₀ r₁ r₂ δ₁ δ₂ : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
    (∀ i, (r₀ i, r₁ i, r₂ i) ∈ lossyGWSIInner P d₁ d₂ (δ₁ i) (δ₂ i)) ∧
    (∑ i : Fin m, w i * r₀ i) ≤ R₀ + ε ∧
    (∑ i : Fin m, w i * r₁ i) ≤ R₁ + ε ∧
    (∑ i : Fin m, w i * r₂ i) ≤ R₂ + ε ∧
    (∑ i : Fin m, w i * δ₁ i) ≤ D₁ + ε ∧
    (∑ i : Fin m, w i * δ₂ i) ≤ D₂ + ε

/-- Rate-Distortion Region of the Lossy Gray–Wyner Network with Decoder Side Information
    (Gray–Wyner 1974; Heegard–Berger 1985; Kaspi 1994; Watanabe 2013):
    Does the closed convex hull of the single-letter Heegard–Berger / Gray–Wyner inner bound
    characterize the exact rate-distortion region for every finite-alphabet source with
    correlated decoder side information? -/
def Statement : Prop :=
  ∀ (kX₁ kX₂ kZ₁ kZ₂ kh₁ kh₂ : ℕ)
    (P : ProbDist (Fin kX₁ × Fin kX₂ × Fin kZ₁ × Fin kZ₂))
    (d₁ : Distortion (Fin kX₁) (Fin kh₁))
    (d₂ : Distortion (Fin kX₂) (Fin kh₂))
    (R₀ R₁ R₂ D₁ D₂ : ℝ),
    IsLossyGWSIAchievable P d₁ d₂ R₀ R₁ R₂ D₁ D₂ ↔
    InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ D₁ D₂

def problem : OpenProblem where
  id := "gray-wyner-lossy"
  title := "Rate-Distortion Region of the Lossy Gray–Wyner Network with Decoder Side Information"
  category := .sourceCoding
  status := .open
  posedBy := "Robert M. Gray and Aaron D. Wyner (with Heegard–Berger / Kaspi)"
  posedYear := 1985
  statement := Statement

end InfoTheory.Problems.GrayWynerLossy
