import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MultipleDescriptionsGeneral

/-- Single-letter Zhang–Berger (1987) inner bound for two-channel multiple descriptions
    (extending `elGamalCoverMDRegion` with a common layer `U₀`). -/
def zhangBergerMDRegion {X Xh₀ Xh₁ Xh₂ : Type*}
    [Fintype X] [Fintype Xh₀] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁) (d₂ : Distortion X Xh₂)
    (D₀ D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU₀ : ℕ) (Q : ProbDist (X × Fin kU₀ × Xh₀ × Xh₁ × Xh₂)),
      Q.fst = P ∧
      (∑ t, Q.pmf t * d₀.dist t.1 t.2.2.1) ≤ D₀ ∧
      (∑ t, Q.pmf t * d₁.dist t.1 t.2.2.2.1) ≤ D₁ ∧
      (∑ t, Q.pmf t * d₂.dist t.1 t.2.2.2.2) ≤ D₂ ∧
      r.1 ≥ mutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.2.1)))) ∧
      r.2 ≥ mutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.2.2)))) ∧
      r.1 + r.2 ≥ 2 * mutualInfo (Q.map (fun t => (t.1, t.2.1))) +
                  condMutualInfo (Q.map (fun t => (t.1, (t.2.2.1, t.2.2.2.1, t.2.2.2.2), t.2.1))) +
                  condMutualInfo (Q.map (fun t => (t.2.2.2.1, t.2.2.2.2, t.2.1))) }

/-- Closed convex hull (time-sharing closure) of the Zhang–Berger inner bound over
    rate-distortion 5-tuples `(R₁, R₂, D₀, D₁, D₂)`. -/
def InZhangBergerClosure {X Xh₀ Xh₁ Xh₂ : Type*}
    [Fintype X] [Fintype Xh₀] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁) (d₂ : Distortion X Xh₂)
    (R₁ R₂ D₀ D₁ D₂ : ℝ) : Prop :=
  ∀ ε > 0, ∃ (m : ℕ) (w r₁ r₂ δ₀ δ₁ δ₂ : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
    (∀ i, (r₁ i, r₂ i) ∈ zhangBergerMDRegion P d₀ d₁ d₂ (δ₀ i) (δ₁ i) (δ₂ i)) ∧
    (∑ i : Fin m, w i * r₁ i) ≤ R₁ + ε ∧
    (∑ i : Fin m, w i * r₂ i) ≤ R₂ + ε ∧
    (∑ i : Fin m, w i * δ₀ i) ≤ D₀ + ε ∧
    (∑ i : Fin m, w i * δ₁ i) ≤ D₁ + ε ∧
    (∑ i : Fin m, w i * δ₂ i) ≤ D₂ + ε

/-- Rate-Distortion Region for General Two-Channel Multiple Descriptions
    (El Gamal–Cover 1982; Zhang–Berger 1987):
    Does the closed convex hull of the Zhang–Berger inner bound characterize the exact
    operational rate-distortion region for every finite-alphabet two-description source
    coding problem? -/
def Statement : Prop :=
  ∀ (kX kh₀ kh₁ kh₂ : ℕ)
    (P : ProbDist (Fin kX))
    (d₀ : Distortion (Fin kX) (Fin kh₀))
    (d₁ : Distortion (Fin kX) (Fin kh₁))
    (d₂ : Distortion (Fin kX) (Fin kh₂))
    (R₁ R₂ D₀ D₁ D₂ : ℝ),
    IsMDAchievable P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ ↔
    InZhangBergerClosure P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂

def problem : OpenProblem where
  id := "multiple-descriptions-general"
  title := "Rate-Distortion Region for General Two-Channel Multiple Descriptions"
  category := .sourceCoding
  status := .open
  posedBy := "Abbas El Gamal and Thomas Cover (and Zhang–Berger)"
  posedYear := 1982
  statement := Statement

end InfoTheory.Problems.MultipleDescriptionsGeneral
