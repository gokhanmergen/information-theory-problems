import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.NonAsymptoticLossyDispersion

/-- Single-letter Wyner–Ziv rate-distortion function
    `R_WZ(D) = inf_{U - X - Y, E[d(X, g(U, Y))] ≤ D} I(X; U | Y)`. -/
noncomputable def wynerZivRate {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
    0 < kU ∧
    Q.map (fun t => (t.1, t.2.1)) = P ∧
    condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
    (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D ∧
    r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) }

/-- Minimum finite-blocklength Wyner–Ziv rate `R_WZ(n, D, ε)` at blocklength `n`,
    distortion threshold `D`, and excess-distortion probability `≤ ε`. -/
noncomputable def wynerZivFiniteRate {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (n : ℕ) (D ε : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ (M : ℕ) (enc : (Fin n → X) → Fin M)
    (dec : Fin M → (Fin n → Y) → Fin n → Xhat),
    0 < M ∧
    let Pn (xy : Fin n → X × Y) : ℝ := ∏ i : Fin n, P.pmf (xy i)
    let excessProb : ℝ := ∑ xy : Fin n → X × Y,
      if ((1 / (n : ℝ)) * ∑ i : Fin n,
          d.dist (xy i).1 (dec (enc (fun j => (xy j).1)) (fun j => (xy j).2) i)) > D
      then Pn xy else 0
    excessProb ≤ ε ∧
    r = log2 (M : ℝ) / (n : ℝ) }

open MeasureTheory in
/-- Standard normal cumulative distribution function `Φ(t)`. -/
noncomputable def stdNormalCDF (t : ℝ) : ℝ :=
  ∫ x : ℝ, if x ≤ t then gaussianPdf1D 1 x else 0

/-- Standard normal quantile function `Φ⁻¹(p)`. -/
noncomputable def stdNormalQuantile (p : ℝ) : ℝ :=
  sInf { t : ℝ | p ≤ stdNormalCDF t }

/-- Interior feasibility predicate: `D` lies strictly above the minimum achievable distortion
    and strictly below the zero-rate distortion (`0 < R_WZ(D)`). -/
def IsInteriorDistortion {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) : Prop :=
  0 < wynerZivRate P d D ∧
  ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
    0 < kU ∧
    Q.map (fun t => (t.1, t.2.1)) = P ∧
    condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
    (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) < D

/-- Single-Dispersion Conjecture for Wyner–Ziv Lossy Source Coding
    (Kostina–Verdú 2012; Watanabe–Kuzuoka–Tan 2015):
    for every finite-alphabet source `(P, d)` and interior distortion level `D`, does
    there exist a single dispersion constant `V ≥ 0` such that for every excess-distortion
    probability `ε ∈ (0, 1)`,
    `√n · (R_WZ(n, D, ε) - R_WZ(D)) → √V · Φ⁻¹(1 - ε)`? -/
def Statement : Prop :=
  ∀ (kX kY kXh : ℕ), 0 < kX → 0 < kY → 0 < kXh →
    ∀ (P : ProbDist (Fin kX × Fin kY)) (d : Distortion (Fin kX) (Fin kXh)) (D : ℝ),
      IsInteriorDistortion P d D →
      ∃ (V : ℝ), 0 ≤ V ∧
        ∀ (ε : ℝ), 0 < ε → ε < 1 →
          let target : ℝ := Real.sqrt V * stdNormalQuantile (1 - ε)
          ∀ (δ : ℝ), 0 < δ → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
            |Real.sqrt (n : ℝ) * (wynerZivFiniteRate P d n D ε - wynerZivRate P d D) -
              target| < δ

def problem : OpenProblem where
  id := "non-asymptotic-lossy-dispersion"
  title := "Second-Order Dispersion of Lossy Source Coding with Side Information (Wyner–Ziv)"
  category := .sourceCoding
  status := .open
  posedBy := "Victoria Kostina, Sergio Verdú; Shun Watanabe, Shigeaki Kuzuoka, Vincent Y. F. Tan"
  posedYear := 2012
  statement := Statement

end InfoTheory.Problems.NonAsymptoticLossyDispersion
