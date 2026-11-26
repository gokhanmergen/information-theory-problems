import InfoTheory.Core

open scoped BigOperators ComplexOrder

namespace InfoTheory.Problems.QuantumBroadcastCapacity

/-- Predicate that a family of matrices forms a valid POVM on `ℂ^d`. -/
def IsPOVM (d m : ℕ) (Λ : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ (x : Fin m), (Λ x).PosSemidef) ∧ (∑ x : Fin m, Λ x = 1)

/-- Operational achievability of rate pair `(R₁, R₂)` over a classical-quantum 2-receiver
    broadcast channel `W : Fin kX → DensityMatrix (d₁ * d₂)`. -/
def IsCQBroadcastAchievable {kX d₁ d₂ : ℕ}
    (W : Fin kX → DensityMatrix (d₁ * d₂)) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc : Fin M₁ → Fin M₂ → Fin n → Fin kX)
      (Λ₁ : Fin M₁ → Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ)
      (Λ₂ : Fin M₂ → Matrix (Fin (d₂ ^ n)) (Fin (d₂ ^ n)) ℂ),
      IsPOVM (d₁ ^ n) M₁ Λ₁ ∧
      IsPOVM (d₂ ^ n) M₂ Λ₂ ∧
      let succ₁ := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          (Λ₁ m₁ * kronPowerMat n (fun i => @partialTraceB d₁ d₂ (W (enc m₁ m₂ i)).mat)).trace.re
      let succ₂ := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          (Λ₂ m₂ * kronPowerMat n (fun i => @partialTraceA d₁ d₂ (W (enc m₁ m₂ i)).mat)).trace.re
      1 - succ₁ ≤ ε ∧ 1 - succ₂ ≤ ε

/-- Capacity region (closed) of a classical-quantum 2-receiver broadcast channel. -/
def cqBroadcastCapacityRegion {kX d₁ d₂ : ℕ}
    (W : Fin kX → DensityMatrix (d₁ * d₂)) : Set (ℝ × ℝ) :=
  closure { p : ℝ × ℝ | IsCQBroadcastAchievable W p.1 p.2 }

/-- Single-letter quantum Marton inner bound (closed) for a c-q 2-receiver broadcast channel,
    including the common auxiliary random variable `W₀` (Savov–Wilde 2015, Theorem 1). -/
def cqMartonInnerBound {kX d₁ d₂ : ℕ}
    (W : Fin kX → DensityMatrix (d₁ * d₂)) : Set (ℝ × ℝ) :=
  closure { p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∃ (kW kU kV : ℕ) (Pwuvx : ProbDist (Fin kW × Fin kU × Fin kV × Fin kX)),
      let pW (w : Fin kW) : ℝ :=
        ∑ u : Fin kU, ∑ v : Fin kV, ∑ x : Fin kX, Pwuvx.pmf (w, u, v, x)
      let pWU (w : Fin kW) (u : Fin kU) : ℝ :=
        ∑ v : Fin kV, ∑ x : Fin kX, Pwuvx.pmf (w, u, v, x)
      let pWV (w : Fin kW) (v : Fin kV) : ℝ :=
        ∑ u : Fin kU, ∑ x : Fin kX, Pwuvx.pmf (w, u, v, x)
      let avgB1 := ∑ t : Fin kW × Fin kU × Fin kV × Fin kX,
        (Pwuvx.pmf t : ℂ) • @partialTraceB d₁ d₂ (W t.2.2.2).mat
      let avgB2 := ∑ t : Fin kW × Fin kU × Fin kV × Fin kX,
        (Pwuvx.pmf t : ℂ) • @partialTraceA d₁ d₂ (W t.2.2.2).mat
      let stateW1 (w : Fin kW) := ((1 / pW w : ℝ) : ℂ) •
        ∑ u : Fin kU, ∑ v : Fin kV, ∑ x : Fin kX,
          (Pwuvx.pmf (w, u, v, x) : ℂ) • @partialTraceB d₁ d₂ (W x).mat
      let stateW2 (w : Fin kW) := ((1 / pW w : ℝ) : ℂ) •
        ∑ u : Fin kU, ∑ v : Fin kV, ∑ x : Fin kX,
          (Pwuvx.pmf (w, u, v, x) : ℂ) • @partialTraceA d₁ d₂ (W x).mat
      let stateWU (w : Fin kW) (u : Fin kU) := ((1 / pWU w u : ℝ) : ℂ) •
        ∑ v : Fin kV, ∑ x : Fin kX,
          (Pwuvx.pmf (w, u, v, x) : ℂ) • @partialTraceB d₁ d₂ (W x).mat
      let stateWV (w : Fin kW) (v : Fin kV) := ((1 / pWV w v : ℝ) : ℂ) •
        ∑ u : Fin kU, ∑ x : Fin kX,
          (Pwuvx.pmf (w, u, v, x) : ℂ) • @partialTraceA d₁ d₂ (W x).mat
      let hB1_W := ∑ w : Fin kW, if pW w ≤ 0 then 0 else pW w * matEntropy (stateW1 w)
      let hB2_W := ∑ w : Fin kW, if pW w ≤ 0 then 0 else pW w * matEntropy (stateW2 w)
      let hB1_WU := ∑ w : Fin kW, ∑ u : Fin kU,
        if pWU w u ≤ 0 then 0 else pWU w u * matEntropy (stateWU w u)
      let hB2_WV := ∑ w : Fin kW, ∑ v : Fin kV,
        if pWV w v ≤ 0 then 0 else pWV w v * matEntropy (stateWV w v)
      let IWUB1 := matEntropy avgB1 - hB1_WU
      let IWVB2 := matEntropy avgB2 - hB2_WV
      let IUB1_W := hB1_W - hB1_WU
      let IVB2_W := hB2_W - hB2_WV
      let IUV_W := condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1)))
      p.1 ≤ IWUB1 ∧ p.2 ≤ IWVB2 ∧
      p.1 + p.2 ≤ IWUB1 + IVB2_W - IUV_W ∧
      p.1 + p.2 ≤ IUB1_W + IWVB2 - IUV_W }

/-- Tightness of the single-letter quantum Marton inner bound for all finite-alphabet
    two-receiver classical-quantum broadcast channels. -/
def Statement : Prop :=
  ∀ (kX d₁ d₂ : ℕ) (W : Fin kX → DensityMatrix (d₁ * d₂)),
    0 < kX → 0 < d₁ → 0 < d₂ →
    cqBroadcastCapacityRegion W = cqMartonInnerBound W

def problem : OpenProblem where
  id := "quantum-broadcast-capacity"
  title := "Capacity Region of the Classical-Quantum Two-Receiver Broadcast Channel"
  category := .quantumInfo
  status := .open
  posedBy := "Jon Yard, Patrick Hayden, and Igor Devetak"
  posedYear := 2011
  statement := Statement

end InfoTheory.Problems.QuantumBroadcastCapacity
