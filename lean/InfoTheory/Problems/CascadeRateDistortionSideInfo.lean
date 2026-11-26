import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CascadeRateDistortionSideInfo

/-- Operational achievability of rate pair `(R₁, R₂)` at distortion `D` in the three-node
    cascade network where Node 1 observes `X^n`, Node 2 observes `(M₁, Y^n)`, and Node 3
    reconstructs `Xhat^n` from `M₂`. -/
def IsCascadeAchievable {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (R₁ R₂ D : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))))
    ∃ (enc₁ : (Fin n → X) → Fin M₁)
      (enc₂ : Fin M₁ → (Fin n → Y) → Fin M₂)
      (dec : Fin M₂ → (Fin n → Xhat)),
      let Pn (xy : Fin n → X × Y) : ℝ := ∏ i : Fin n, P.pmf (xy i)
      let avgD : ℝ := ∑ xy : Fin n → X × Y, Pn xy *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          d.dist (xy i).1 (dec (enc₂ (enc₁ (fun j => (xy j).1)) (fun j => (xy j).2)) i))
      avgD ≤ D + ε

/-- Cuff–Su–El Gamal (2009) single-letter outer bound for cascade rate-distortion with side
    information `Y` at the intermediate node: `U - X - Y`, `X - (U, Y) - Xhat`,
    `E[d(X, Xhat)] ≤ D`, `R₁ ≥ I(X; U | Y)`, and `R₂ ≥ I(X, Y; Xhat)`. -/
def cascadeOuterBound {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU × Xhat)),
      0 < kU ∧
      Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) = 0 ∧
      condMutualInfo (Q.map (fun t => (t.1, t.2.2.2, (t.2.2.1, t.2.1)))) = 0 ∧
      (∑ t : X × Y × Fin kU × Xhat, Q.pmf t * d.dist t.1 t.2.2.2) ≤ D ∧
      r.1 ≥ condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.1))) ∧
      r.2 ≥ mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2))) }

/-- Cascade Rate-Distortion with Side Information (Vasudevan–Tian–Diggavi 2006;
    Cuff–Su–El Gamal 2009): does the single-letter outer bound coincide with the
    operational cascade rate-distortion region for every finite-alphabet DMS `(X, Y)`
    and distortion measure `d`? -/
def Statement : Prop :=
  ∀ (kX kY kXh : ℕ), 0 < kX → 0 < kY → 0 < kXh →
    ∀ (P : ProbDist (Fin kX × Fin kY)) (d : Distortion (Fin kX) (Fin kXh)) (D R₁ R₂ : ℝ),
      (R₁, R₂) ∈ cascadeOuterBound P d D → IsCascadeAchievable P d R₁ R₂ D

def problem : OpenProblem where
  id := "cascade-rate-distortion-side-info"
  title := "Cascade Rate-Distortion with Side Information at the Intermediate Node"
  category := .sourceCoding
  status := .open
  posedBy := "Dinkar Vasudevan, Chao Tian, Suhas Diggavi; Paul Cuff, Han-I Su, Abbas El Gamal"
  posedYear := 2006
  statement := Statement

end InfoTheory.Problems.CascadeRateDistortionSideInfo
