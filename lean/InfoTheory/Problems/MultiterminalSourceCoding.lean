import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MultiterminalSourceCoding

/-- Doubly Symmetric Binary Source `DSBS(p)` on `Bool × Bool`: `X₁ ~ Bern(1/2)` and
    `X₂ = X₁ ⊕ Z` with `Z ~ Bern(p)` (`0 ≤ p ≤ 1`). -/
noncomputable def dsbsDist (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ProbDist (Bool × Bool) where
  pmf := fun xy => if xy.1 = xy.2 then (1 - p) / 2 else p / 2
  nonneg := fun xy => by split_ifs <;> linarith
  sum_one := by simp [Fintype.sum_prod_type]; ring

/-- Binary Hamming distortion on `Bool`. -/
def binHamming : Distortion Bool Bool where
  dist := fun x y => if x = y then 0 else 1
  nonneg := fun x y => by split_ifs <;> norm_num

/-- Closed convex hull (time-sharing closure) of the Berger–Tung inner bound over
    rate-distortion 4-tuples `(R₁, R₂, D₁, D₂)`. -/
def InBergerTungClosure {X₁ X₂ Xh₁ Xh₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  ∀ ε > 0, ∃ (m : ℕ) (w r₁ r₂ δ₁ δ₂ : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
    (∀ i, (r₁ i, r₂ i) ∈ bergerTungInnerBound P d₁ d₂ (δ₁ i) (δ₂ i)) ∧
    (∑ i : Fin m, w i * r₁ i) ≤ R₁ + ε ∧
    (∑ i : Fin m, w i * r₂ i) ≤ R₂ + ε ∧
    (∑ i : Fin m, w i * δ₁ i) ≤ D₁ + ε ∧
    (∑ i : Fin m, w i * δ₂ i) ≤ D₂ + ε

/-- Two-Terminal Binary Multiterminal Source Coding Problem (Berger 1977; Tung 1978):
    While Wagner–Kelly–Altuğ (2011) proved that the Berger–Tung inner bound is strictly
    suboptimal for certain general discrete sources with separate distortions (embedding
    a Körner–Marton modulo-2 structure), it remains a central open problem whether the
    Berger–Tung inner bound is tight for the **doubly symmetric binary source `DSBS(p)`**
    under separate binary Hamming distortions `(d₁, d₂)`. -/
def Statement : Prop :=
  ∀ (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) (R₁ R₂ D₁ D₂ : ℝ),
    0 ≤ D₁ → D₁ ≤ 1 / 2 → 0 ≤ D₂ → D₂ ≤ 1 / 2 →
    (IsBergerTungAchievable (dsbsDist p (le_of_lt hp0) (by linarith)) binHamming binHamming R₁ R₂ D₁ D₂ ↔
     InBergerTungClosure (dsbsDist p (le_of_lt hp0) (by linarith)) binHamming binHamming R₁ R₂ D₁ D₂)

def problem : OpenProblem where
  id := "multiterminal-source-coding"
  title := "Rate-Distortion Region for Two-Terminal Binary Multiterminal Source Coding"
  category := .sourceCoding
  status := .open
  posedBy := "Toby Berger and Sui-Yin Tung"
  posedYear := 1977
  statement := Statement

end InfoTheory.Problems.MultiterminalSourceCoding
