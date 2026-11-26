import InfoTheory.Core

open scoped BigOperators Classical
open MeasureTheory

namespace InfoTheory.Problems.GaussianRelayChannelCapacity

/-- Operational achievability of rate `R` over the memoryless Gaussian relay channel
    `Y_r = g₁₂ X + Z_r`, `Y = g₁₃ X + g₂₃ X_r + Z` with independent `Z_r, Z ~ N(0, 1)`,
    measurable causal relay functions and decoder, and power/error evaluated via Lebesgue
    `lintegral` (preventing Bochner junk `0` on non-measurable or infinite-power relays). -/
def IsGaussianRelayAchievable (g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : Fin M → Fin n → ℝ)
      (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
      (dec : (Fin n → ℝ) → Fin M),
      (∀ i : Fin n, Measurable (relay i)) ∧
      Measurable dec ∧
      (∀ m : Fin M, (∑ i : Fin n, (enc m i) ^ 2) ≤ (n : ℝ) * P₁) ∧
      (∀ m : Fin M,
        (∫⁻ zr : Fin n → ℝ,
          ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
          ∑ i : Fin n, (relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
            zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2)) ≤ ENNReal.ofReal ((n : ℝ) * P₂)) ∧
      let errProb (m : Fin M) : ℝ :=
        (∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
          let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
          let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
          let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
          let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
          let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
          if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0).toReal
      ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, errProb m ≤ ε

/-- Capacity `C_Gauss(g₁₂, g₁₃, g₂₃, P₁, P₂)` of the three-node Gaussian relay channel. -/
noncomputable def gaussianRelayCapacity (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) : ℝ :=
  sSup { R : ℝ | IsGaussianRelayAchievable g₁₂ g₁₃ g₂₃ P₁ P₂ R }

/-- Gaussian hybrid decode-and-forward / compress-and-forward (Cover–El Gamal Theorem 7)
    achievable rate for the three-node Gaussian relay channel. -/
noncomputable def gaussianHybridDFCFRate (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) : ℝ :=
  let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
  sSup { r : ℝ | ∃ (α β γ θ σsq R₁ R₂ : ℝ),
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ ≤ 1 ∧
    0 ≤ θ ∧ θ ≤ 1 ∧ 0 < σsq ∧
    0 ≤ R₁ ∧ 0 ≤ R₂ ∧ r = R₁ + R₂ ∧
    R₁ ≤ cap ((g₁₂ ^ 2 * β * P₁) / (1 + g₁₂ ^ 2 * γ * P₁)) ∧
    R₂ ≤ cap (g₁₃ ^ 2 * γ * P₁ + (g₁₂ ^ 2 * γ * P₁) / (1 + σsq)) ∧
    R₂ ≤ cap (g₁₃ ^ 2 * γ * P₁ + g₂₃ ^ 2 * (1 - θ) * P₂) - cap (1 / σsq) ∧
    R₁ + R₂ ≤ cap (g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ +
      2 * |g₁₃ * g₂₃| * Real.sqrt (α * θ * P₁ * P₂)) - cap (1 / σsq) }

/-- Exact Capacity of the Three-Node Gaussian Relay Channel (Cover–El Gamal 1979):
    Does the Gaussian hybrid decode-and-forward / compress-and-forward rate achieve
    the exact capacity of the memoryless Gaussian relay channel for all channel gains
    and positive power constraints? -/
def Statement : Prop :=
  ∀ (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ), 0 < P₁ → 0 < P₂ →
    gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂ = gaussianHybridDFCFRate g₁₂ g₁₃ g₂₃ P₁ P₂

def problem : OpenProblem where
  id := "gaussian-relay-channel-capacity"
  title := "Exact Capacity of the Three-Node Gaussian Relay Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas Cover and Abbas El Gamal"
  posedYear := 1979
  statement := Statement

end InfoTheory.Problems.GaussianRelayChannelCapacity
