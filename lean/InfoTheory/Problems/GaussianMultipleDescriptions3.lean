import InfoTheory.Core

open scoped BigOperators
open MeasureTheory

namespace InfoTheory.Problems.GaussianMultipleDescriptions3

/-- Operational achievability of symmetric per-description rate `R` for the 3-channel
    quadratic Gaussian multiple descriptions problem (`X ~ N(0, 1)`) with measurable
    encoders and MSE evaluated via Lebesgue `lintegral` (preventing non-measurable `0` junk). -/
def IsGaussMD3SymAchievable (D₁ D₂ D₃ R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R + ε))))
    ∃ (enc₁ enc₂ enc₃ : (Fin n → ℝ) → Fin M)
      (dec₁ dec₂ dec₃ : Fin M → Fin n → ℝ)
      (dec₁₂ dec₁₃ dec₂₃ : Fin M × Fin M → Fin n → ℝ)
      (dec₁₂₃ : Fin M × Fin M × Fin M → Fin n → ℝ),
      Measurable enc₁ ∧ Measurable enc₂ ∧ Measurable enc₃ ∧
      let mse (recon : (Fin n → ℝ) → Fin n → ℝ) : ENNReal :=
        ∫⁻ x : Fin n → ℝ,
          ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (x i)) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, (x i - recon x i) ^ 2))
      mse (fun x => dec₁ (enc₁ x)) ≤ ENNReal.ofReal (D₁ + ε) ∧
      mse (fun x => dec₂ (enc₂ x)) ≤ ENNReal.ofReal (D₁ + ε) ∧
      mse (fun x => dec₃ (enc₃ x)) ≤ ENNReal.ofReal (D₁ + ε) ∧
      mse (fun x => dec₁₂ (enc₁ x, enc₂ x)) ≤ ENNReal.ofReal (D₂ + ε) ∧
      mse (fun x => dec₁₃ (enc₁ x, enc₃ x)) ≤ ENNReal.ofReal (D₂ + ε) ∧
      mse (fun x => dec₂₃ (enc₂ x, enc₃ x)) ≤ ENNReal.ofReal (D₂ + ε) ∧
      mse (fun x => dec₁₂₃ (enc₁ x, enc₂ x, enc₃ x)) ≤ ENNReal.ofReal (D₃ + ε)

/-- Optimal symmetric per-description rate `R*_sym(D₁, D₂, D₃)` for 3-channel quadratic
    Gaussian multiple descriptions. -/
noncomputable def gaussMD3SymRate (D₁ D₂ D₃ : ℝ) : ℝ :=
  sInf { R : ℝ | IsGaussMD3SymAchievable D₁ D₂ D₃ R }

/-- Tian–Chen (2009) three-layer hybrid Gaussian + `(3, 2)` MDS lattice + `(3, 3)` MDS
    central refinement achievable symmetric rate for 3-channel quadratic Gaussian MD. -/
noncomputable def tianChenMD3SymRate (D₁ D₂ D₃ : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ (v₀ σsq ρ τ₂ : ℝ),
    0 < v₀ ∧ v₀ ≤ 1 ∧ 0 < σsq ∧ -(1 / 2 : ℝ) < ρ ∧ ρ < 1 ∧ 0 < τ₂ ∧
    let d1 := (v₀ * σsq) / (v₀ + σsq)
    let d2Base := (v₀ * σsq * (1 + ρ)) / (2 * v₀ + σsq * (1 + ρ))
    let d2 := (d2Base * τ₂) / (d2Base + τ₂)
    let d3Base := (v₀ * σsq * (1 + 2 * ρ)) / (3 * v₀ + σsq * (1 + 2 * ρ))
    let d3' := (d3Base * τ₂) / (d3Base + τ₂)
    d1 ≤ D₁ ∧ d2 ≤ D₂ ∧
    let r0 := (1 / 2 : ℝ) * log2 (1 / v₀)
    let rBase := (1 / 2 : ℝ) * log2 (v₀ / d1) +
                 (1 / 6 : ℝ) * log2 (1 / ((1 + 2 * ρ) * (1 - ρ) ^ 2))
    let r2 := (1 / 4 : ℝ) * log2 (1 + d2Base / τ₂)
    let r3 := (1 / 6 : ℝ) * max 0 (log2 (d3' / D₃))
    r = r0 + rBase + r2 + r3 }

/-- Symmetric Rate-Distortion Function for Three-Channel Quadratic Gaussian Multiple
    Descriptions (Venkataramani–Kramer–Goyal 2003; Tian–Chen 2009):
    Does the Tian–Chen hybrid Gaussian and MDS-lattice layering scheme achieve the exact
    symmetric rate-distortion function for all `0 < D₃ ≤ D₂ ≤ D₁ ≤ 1`? -/
def Statement : Prop :=
  ∀ (D₁ D₂ D₃ : ℝ), 0 < D₃ → D₃ ≤ D₂ → D₂ ≤ D₁ → D₁ ≤ 1 →
    gaussMD3SymRate D₁ D₂ D₃ = tianChenMD3SymRate D₁ D₂ D₃

def problem : OpenProblem where
  id := "gaussian-multiple-descriptions-3"
  title := "Symmetric Rate-Distortion Function for Three-Channel Quadratic Gaussian Multiple Descriptions"
  category := .sourceCoding
  status := .open
  posedBy := "Ramzam Venkataramani, Gerhard Kramer, and Vivek K. Goyal"
  posedYear := 2003
  statement := Statement

end InfoTheory.Problems.GaussianMultipleDescriptions3
