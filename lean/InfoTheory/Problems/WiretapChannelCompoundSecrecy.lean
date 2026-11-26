import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.WiretapChannelCompoundSecrecy

/-- `n`-letter compound wiretap secrecy expression
    `sup_{V - X^n} [ min_s I(V; Y_s^n) - max_s I(V; Z_s^n) ]`. -/
noncomputable def compoundWiretapRateN {kS : ℕ} {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (W : Fin kS → WiretapChannel X Y Z) (n : ℕ) : ℝ :=
  sSup { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × (Fin n → X)))
    (joint : Fin kS → ProbDist (Fin kV × (Fin n → X) × (Fin n → Y × Z))),
    (∀ (s : Fin kS) (t : Fin kV × (Fin n → X) × (Fin n → Y × Z)),
      (joint s).pmf t = Pvx.pmf (t.1, t.2.1) * ((W s).power n).trans t.2.1 t.2.2) ∧
    let minY := sInf { a : ℝ | ∃ (s : Fin kS),
      a = mutualInfo ((joint s).map (fun t => (t.1, fun i => (t.2.2 i).1))) }
    let maxZ := sSup { b : ℝ | ∃ (s : Fin kS),
      b = mutualInfo ((joint s).map (fun t => (t.1, fun i => (t.2.2 i).2))) }
    r = minY - maxZ }

/-- Regularized secrecy capacity of a finite-state compound DM wiretap channel
    (Bjelaković–Boche–Sommerfeld 2013). -/
noncomputable def compoundSecrecyCapacity {kS : ℕ} {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (W : Fin kS → WiretapChannel X Y Z) : ℝ :=
  sSup { r : ℝ | ∃ (n : ℕ), 0 < n ∧ r = compoundWiretapRateN W n / (n : ℝ) }

/-- Single-letter Liang–Kramer–Poor–Shamai (2009) inner bound
    `sup_{U - V - X} [ min_s I(V; Y_s | U) - max_s I(V; Z_s | U) ]`. -/
noncomputable def lkpsSingleLetterBound {kS : ℕ} {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (W : Fin kS → WiretapChannel X Y Z) : ℝ :=
  sSup { r : ℝ | ∃ (kU kV : ℕ) (Puvx : ProbDist (Fin kU × Fin kV × X))
    (joint : Fin kS → ProbDist (Fin kU × Fin kV × X × (Y × Z))),
    (∀ (s : Fin kS) (t : Fin kU × Fin kV × X × (Y × Z)),
      (joint s).pmf t = Puvx.pmf (t.1, t.2.1, t.2.2.1) * (W s).trans t.2.2.1 t.2.2.2) ∧
    let minY := sInf { a : ℝ | ∃ (s : Fin kS),
      a = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.1, t.1))) }
    let maxZ := sSup { b : ℝ | ∃ (s : Fin kS),
      b = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.2, t.1))) }
    r = minY - maxZ }

/-- Single-letterization conjecture for finite-state compound DM wiretap channels:
    does the Liang–Kramer–Poor–Shamai single-letter inner bound equal the regularized
    compound secrecy capacity for every finite family of DM wiretap channels? -/
def Statement : Prop :=
  ∀ (kS kX kY kZ : ℕ) (W : Fin kS → WiretapChannel (Fin kX) (Fin kY) (Fin kZ)),
    0 < kS → 0 < kX → 0 < kY → 0 < kZ →
    compoundSecrecyCapacity W = lkpsSingleLetterBound W

def problem : OpenProblem where
  id := "wiretap-channel-compound-secrecy"
  title := "Single-Letter Secrecy Capacity of the Compound Discrete Memoryless Wiretap Channel"
  category := .securityPrivacy
  status := .open
  posedBy := "Yingbin Liang, Gerhard Kramer, H. Vincent Poor, and Shlomo Shamai (Shitz)"
  posedYear := 2009
  statement := Statement

end InfoTheory.Problems.WiretapChannelCompoundSecrecy
