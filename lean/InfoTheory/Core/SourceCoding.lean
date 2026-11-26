import InfoTheory.Core.Entropy

/-!
# Multi-Terminal Source Coding, Rate-Distortion, and Common Information

Definitions for:
- Single-user rate-distortion function `R(D)`
- Distributed / Berger-Tung multi-terminal source coding
- Discrete memoryless CEO problem
- Multiple descriptions (El Gamal-Cover, Zhang-Berger)
- Wyner, Gács-Körner, and Exact common information
- Lossy Gray-Wyner network
-/

open scoped BigOperators

namespace InfoTheory

/-- Single-letter distortion measure `d : X × Xhat → ℝ≥0`. -/
structure Distortion (X Xhat : Type*) where
  dist : X → Xhat → ℝ
  nonneg : ∀ x y, 0 ≤ dist x y

/-- Single-user Shannon rate-distortion function `R(D) = inf_{E[d(X, Xhat)] ≤ D} I(X; Xhat)`. -/
noncomputable def rateDistortion {X Xhat : Type*} [Fintype X] [Fintype Xhat]
    (P : ProbDist X) (d : Distortion X Xhat) (D : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ Q : ProbDist (X × Xhat),
    Q.fst = P ∧
    (∑ xy : X × Xhat, Q.pmf xy * d.dist xy.1 xy.2) ≤ D ∧
    r = mutualInfo Q }

/-- Operational achievability for two-terminal distributed lossy source coding (Berger-Tung). -/
def IsBergerTungAchievable {X₁ X₂ Xh₁ Xh₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (R₁ R₂ D₁ D₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))))
    ∃ (enc₁ : (Fin n → X₁) → Fin M₁) (enc₂ : (Fin n → X₂) → Fin M₂)
      (dec₁ : Fin M₁ × Fin M₂ → Fin n → Xh₁)
      (dec₂ : Fin M₁ × Fin M₂ → Fin n → Xh₂),
      let Pn (x : Fin n → X₁ × X₂) : ℝ := ∏ i : Fin n, P.pmf (x i)
      let avgD₁ := ∑ x : Fin n → X₁ × X₂, Pn x *
        ((1 / (n : ℝ)) * ∑ i : Fin n, d₁.dist (x i).1 (dec₁ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))
      let avgD₂ := ∑ x : Fin n → X₁ × X₂, Pn x *
        ((1 / (n : ℝ)) * ∑ i : Fin n, d₂.dist (x i).2 (dec₂ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))
      avgD₁ ≤ D₁ + ε ∧ avgD₂ ≤ D₂ + ε

/-- Berger-Tung (1977/1978) inner bound for distributed lossy source coding. -/
def bergerTungInnerBound {X₁ X₂ Xh₁ Xh₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU₁ kU₂ : ℕ) (Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂))
      (g₁ : Fin kU₁ × Fin kU₂ → Xh₁) (g₂ : Fin kU₁ × Fin kU₂ → Xh₂),
      Q.map (fun t => (t.1, t.2.1)) = P ∧
      -- Markov chains U₁ - X₁ - X₂ - U₂
      condMutualInfo (Q.map (fun t => (t.2.2.1, (t.2.1, t.2.2.2), t.1))) = 0 ∧
      condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0 ∧
      (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) ≤ D₁ ∧
      (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) ≤ D₂ ∧
      r.1 ≥ condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) ∧
      r.2 ≥ condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) ∧
      r.1 + r.2 ≥ mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) }

/-- Wyner's common information `C_W(X; Y) = inf_{X - W - Y} I(X, Y; W)`. -/
noncomputable def wynerCommonInfo {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) : ℝ :=
  sInf { r : ℝ | ∃ (kW : ℕ) (Q : ProbDist (X × Y × Fin kW)),
    Q.map (fun t => (t.1, t.2.1)) = P ∧
    condMutualInfo Q = 0 ∧
    r = mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2))) }

/-- Exact common information `G(X; Y)` (Kumar-Li-El Gamal 2014):
    minimum entropy `H(W)` over finite-alphabet `W` making `X` and `Y` conditionally independent. -/
noncomputable def exactCommonInfoSingle {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) : ℝ :=
  sInf { r : ℝ | ∃ (kW : ℕ) (Q : ProbDist (X × Y × Fin kW)),
    Q.map (fun t => (t.1, t.2.1)) = P ∧
    condMutualInfo Q = 0 ∧
    r = shannonEntropy (Q.map (fun t => t.2.2)) }

/-- Asymptotic exact common information `G(X; Y) = inf_{n ≥ 1} (1/n) G_1(X^n; Y^n)`. -/
noncomputable def exactCommonInfo {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) : ℝ :=
  sInf { r : ℝ | ∃ n : ℕ, 0 < n ∧
    let Pn : ProbDist ((Fin n → X) × (Fin n → Y)) :=
      { pmf := fun xy => ∏ i : Fin n, P.pmf (xy.1 i, xy.2 i)
        nonneg := fun xy => Finset.prod_nonneg (fun i _ => P.nonneg _)
        sum_one := by
          have h : ∑ xy : (Fin n → X) × (Fin n → Y), ∏ i : Fin n, P.pmf (xy.1 i, xy.2 i) =
              ∑ z : Fin n → X × Y, ∏ i : Fin n, P.pmf (z i) := by
            let e : (Fin n → X) × (Fin n → Y) ≃ (Fin n → X × Y) :=
              { toFun := fun xy i => (xy.1 i, xy.2 i)
                invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
                left_inv := fun ⟨_, _⟩ => rfl
                right_inv := fun _ => rfl }
            exact Fintype.sum_equiv e _ _ (fun _ => rfl)
          rw [h, ← Fintype.prod_sum]
          exact Finset.prod_eq_one (fun _ _ => P.sum_one) }
    r = exactCommonInfoSingle Pn / (n : ℝ) }

/-- Two-channel multiple descriptions operational achievability. -/
def IsMDAchievable {X Xh₀ Xh₁ Xh₂ : Type*}
    [Fintype X] [Fintype Xh₀] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁) (d₂ : Distortion X Xh₂)
    (R₁ R₂ D₀ D₁ D₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))))
    ∃ (enc₁ : (Fin n → X) → Fin M₁) (enc₂ : (Fin n → X) → Fin M₂)
      (dec₀ : Fin M₁ × Fin M₂ → Fin n → Xh₀)
      (dec₁ : Fin M₁ → Fin n → Xh₁)
      (dec₂ : Fin M₂ → Fin n → Xh₂),
      let Pn (x : Fin n → X) : ℝ := ∏ i : Fin n, P.pmf (x i)
      (∑ x, Pn x * ((1 / (n : ℝ)) * ∑ i : Fin n, d₀.dist (x i) (dec₀ (enc₁ x, enc₂ x) i))) ≤ D₀ + ε ∧
      (∑ x, Pn x * ((1 / (n : ℝ)) * ∑ i : Fin n, d₁.dist (x i) (dec₁ (enc₁ x) i))) ≤ D₁ + ε ∧
      (∑ x, Pn x * ((1 / (n : ℝ)) * ∑ i : Fin n, d₂.dist (x i) (dec₂ (enc₂ x) i))) ≤ D₂ + ε

/-- El Gamal-Cover (1982) inner bound for two-channel multiple descriptions. -/
def elGamalCoverMDRegion {X Xh₀ Xh₁ Xh₂ : Type*}
    [Fintype X] [Fintype Xh₀] [Fintype Xh₁] [Fintype Xh₂]
    (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁) (d₂ : Distortion X Xh₂)
    (D₀ D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ Q : ProbDist (X × Xh₀ × Xh₁ × Xh₂),
      Q.fst = P ∧
      (∑ t, Q.pmf t * d₀.dist t.1 t.2.1) ≤ D₀ ∧
      (∑ t, Q.pmf t * d₁.dist t.1 t.2.2.1) ≤ D₁ ∧
      (∑ t, Q.pmf t * d₂.dist t.1 t.2.2.2) ≤ D₂ ∧
      r.1 ≥ mutualInfo (Q.map (fun t => (t.1, t.2.2.1))) ∧
      r.2 ≥ mutualInfo (Q.map (fun t => (t.1, t.2.2.2))) ∧
      r.1 + r.2 ≥ mutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.1, t.2.2.2)))) +
                  mutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2))) }

end InfoTheory
