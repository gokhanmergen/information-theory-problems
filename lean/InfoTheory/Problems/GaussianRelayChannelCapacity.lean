import InfoTheory.Core

open scoped BigOperators Classical ENNReal
open MeasureTheory

namespace InfoTheory.Problems.GaussianRelayChannelCapacity

/-- Operational achievability of rate `R` over the memoryless Gaussian relay channel
    `Y_r = g₁₂ X + Z_r`, `Y = g₁₃ X + g₂₃ X_r + Z` with independent `Z_r, Z ~ N(0, 1)`,
    measurable causal relay functions and decoder, and power/error evaluated directly in
    `ℝ≥0∞` via Lebesgue `lintegral` (preventing Bochner/toReal junk `0`). -/
def IsGaussianRelayAchievable (g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
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
      let errProb (m : Fin M) : ℝ≥0∞ :=
        ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
          let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
          let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
          let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
          let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
          let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
          if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
      (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errProb m ≤ ENNReal.ofReal ε

/-- Capacity `C_Gauss(g₁₂, g₁₃, g₂₃, P₁, P₂)` of the three-node Gaussian relay channel,
    valued in `ℝ≥0∞` so an unbounded achievable set evaluates to `⊤` rather than junk `0`. -/
noncomputable def gaussianRelayCapacity (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) : ℝ≥0∞ :=
  sSup { r : ℝ≥0∞ | ∃ R : ℝ, IsGaussianRelayAchievable g₁₂ g₁₃ g₂₃ P₁ P₂ R ∧ r = ENNReal.ofReal R }

/-- Gaussian hybrid decode-and-forward / compress-and-forward (Cover–El Gamal Theorem 7)
    achievable rate for the three-node Gaussian relay channel, valued in `ℝ≥0∞`.
    Here `c ≥ 0` represents the inverse compression noise variance `1 / σ²`, with `c = 0`
    recovering pure decode-and-forward (`σ² = ∞`) so the feasible set is nonempty even when
    `g₁₃ = g₂₃ = 0`. -/
noncomputable def gaussianHybridDFCFRate (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) : ℝ≥0∞ :=
  let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
  sSup { r : ℝ≥0∞ | ∃ (α β γ θ c R₁ R₂ : ℝ),
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ ≤ 1 ∧
    0 ≤ θ ∧ θ ≤ 1 ∧ 0 ≤ c ∧
    0 ≤ R₁ ∧ 0 ≤ R₂ ∧ r = ENNReal.ofReal (R₁ + R₂) ∧
    R₁ ≤ cap ((g₁₂ ^ 2 * β * P₁) / (1 + g₁₂ ^ 2 * γ * P₁)) ∧
    R₂ ≤ cap (g₁₃ ^ 2 * γ * P₁ + (g₁₂ ^ 2 * γ * P₁) * c / (1 + c)) ∧
    R₂ ≤ cap (g₁₃ ^ 2 * γ * P₁ + g₂₃ ^ 2 * (1 - θ) * P₂) - cap c ∧
    R₁ + R₂ ≤ cap (g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ +
      2 * |g₁₃ * g₂₃| * Real.sqrt (α * θ * P₁ * P₂)) - cap c }

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
