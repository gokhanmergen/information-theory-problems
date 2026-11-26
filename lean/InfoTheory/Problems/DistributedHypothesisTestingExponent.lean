import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DistributedHypothesisTestingExponent

/-- Operational optimal type-II error exponent `E*(R, P, Q)` for two-terminal distributed
    hypothesis testing of `H_0 : P_{XY}` against `H_1 : Q_{XY}` at encoder rate `R > 0`. -/
noncomputable def dhtOptimalExponent {X Y : Type*} [Fintype X] [Fintype Y]
    (P Q : ProbDist (X × Y)) (R : ℝ) : ℝ :=
  sSup { E : ℝ | ∀ (ε : ℝ), 0 < ε →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : (Fin n → X) → Fin M) (acc : Fin M → (Fin n → Y) → Bool),
        let type1 := ∑ xy : Fin n → X × Y,
          (∏ i : Fin n, P.pmf (xy i)) *
            if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = false then 1 else 0
        let type2 := ∑ xy : Fin n → X × Y,
          (∏ i : Fin n, Q.pmf (xy i)) *
            if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = true then 1 else 0
        type1 ≤ ε ∧ type2 ≤ (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) }

/-- Shimokawa–Han–Amari (1994) single-letter achievable type-II error exponent `E_SHA(R, P, Q)`
    via quantization `U - X - Y` and Wyner–Ziv binning (properly handling both `I(U; X) ≤ R`
    where no binning error `term2` occurs and `I(U; X | Y) ≤ R < I(U; X)`). -/
noncomputable def shaInnerBound {X Y : Type*} [Fintype X] [Fintype Y]
    (P Q : ProbDist (X × Y)) (R : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ (kU : ℕ) (Puxy Quxy : ProbDist (Fin kU × X × Y)),
    Puxy.map (fun t => (t.2.1, t.2.2)) = P ∧
    condMutualInfo (Puxy.map (fun t => (t.1, t.2.2, t.2.1))) = 0 ∧
    (∀ (u : Fin kU) (x : X) (y : Y),
      Quxy.pmf (u, x, y) * P.fst.pmf x =
        Q.pmf (x, y) * (Puxy.map (fun t => (t.1, t.2.1))).pmf (u, x)) ∧
    let rateUsed := condMutualInfo (Puxy.map (fun t => (t.1, t.2.1, t.2.2)))
    let fullRate := mutualInfo (Puxy.map (fun t => (t.1, t.2.1)))
    rateUsed ≤ R ∧
    let term1 := sInf { d : ℝ | ∃ (Pt : ProbDist (Fin kU × X × Y)),
      Pt.map (fun t => (t.1, t.2.1)) = Puxy.map (fun t => (t.1, t.2.1)) ∧
      Pt.map (fun t => (t.1, t.2.2)) = Puxy.map (fun t => (t.1, t.2.2)) ∧
      AbsCont Pt Quxy ∧ d = klDivergence Pt Quxy }
    let term2 := sInf { d : ℝ | ∃ (Pt : ProbDist (Fin kU × X × Y)),
      Pt.map (fun t => (t.1, t.2.1)) = Puxy.map (fun t => (t.1, t.2.1)) ∧
      Pt.map (fun t => t.2.2) = P.snd ∧
      condEntropy (Puxy.map (fun t => (t.1, t.2.2))) ≤
        condEntropy (Pt.map (fun t => (t.1, t.2.2))) ∧
      AbsCont Pt Quxy ∧ d = klDivergence Pt Quxy + R - rateUsed }
    r = if fullRate ≤ R then term1 else min term1 term2 }

/-- Optimal Type-II Error Exponent for Binary Distributed Hypothesis Testing
    (Ahlswede–Csiszár 1986; Shimokawa–Han–Amari 1994; Watanabe 2022; Kochman–Wang 2023):
    While Watanabe (2022) and Kochman–Wang (2023) showed that `E_SHA` can be strictly
    suboptimal for larger alphabets, it remains open whether the Shimokawa–Han–Amari
    inner bound is tight for **binary-alphabet** sources (`X = Y = Bool`) with full support. -/
def Statement : Prop :=
  ∀ (P Q : ProbDist (Bool × Bool)) (R : ℝ),
    0 < R →
    (∀ xy : Bool × Bool, 0 < P.pmf xy) →
    (∀ xy : Bool × Bool, 0 < Q.pmf xy) →
    dhtOptimalExponent P Q R = shaInnerBound P Q R

def problem : OpenProblem where
  id := "distributed-hypothesis-testing-exponent"
  title := "Optimal Type-II Error Exponent for General Two-Terminal Distributed Hypothesis Testing"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Rudolf Ahlswede and Imre Csiszár"
  posedYear := 1986
  statement := Statement

end InfoTheory.Problems.DistributedHypothesisTestingExponent
