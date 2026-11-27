import InfoTheory.Core

open scoped BigOperators Classical ENNReal
open MeasureTheory

/-!
# Exact Capacity of the Three-Node Gaussian Relay Channel (Cover–El Gamal 1979)

Channel: `Y_r = g₁₂ X + Z_r`, `Y = g₁₃ X + g₂₃ X_r + Z`, independent `Z_r, Z ~ N(0, 1)`,
per-codeword source power `∑ᵢ xᵢ² ≤ n P₁`, per-message expected relay power
`E ∑ᵢ X_{r,i}² ≤ n P₂`, strictly causal measurable relay `X_{r,i} = f_i(Y_r^{i-1})`.
`gaussianRelayCapacity` is the operational capacity, valued in `ℝ≥0∞`.

The exact capacity is open for every choice of nonzero gains. The formal statement poses the
sharpest open first-order question at a standard benchmark: with unit gains and equal powers
`P₁ = P₂ = P`, is `lim_{P → 0⁺} C_Gauss(1, 1, 1, P, P) / P = 1 / ln 2`, i.e. does capacity
match the cutset bound to first order at low SNR (minimum energy-per-bit equal to the cutset
lower bound)?

**Statement-fix (2026-11-27).** The previous statement asked whether `gaussianRelayCapacity`
equals the Gaussian hybrid decode-and-forward / compress-and-forward rate (Cover–El Gamal
Theorem 7 with jointly Gaussian inputs) for all gains and powers. That rate has no power
time-sharing, and the formal model allows bursty signalling. El Gamal–Mohseni–Zahedi (2006,
eq. (8)) already showed that bursty compress-forward beats it, and their block-length-2 linear
relaying (Example 1) beats it and even its upper concave envelope over power allocations. So
the old statement was false by known results
(`attempts/gaussian-relay-channel-capacity/2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md`).
Any "capacity = single-letter Gaussian DF/CF/hybrid rate" re-posing is refuted or very likely
refuted in the same way, so the statement now asks about a quantity whose value is unknown.

Known facts (unit gains, `P₁ = P₂ = P > 0`):
* cutset: `C_Gauss ≤ ½ log₂(1 + 2P) ≤ P / ln 2`, so `limsup C_Gauss / P ≤ 1 / ln 2`
  (Cover–El Gamal 1979; not formalized);
* direct link with a silent relay: `C_Gauss ≥ ½ log₂(1 + P)`, so
  `liminf C_Gauss / P ≥ 1 / (2 ln 2)` (certified in
  `Known.Certificates.GaussianRelayChannelCapacity`);
* EMZ Example 1 with bursting: `C_Gauss ≥ 0.88283 · P` for `P ∈ (0, 1/10]` (on paper, in the
  attempt above), against the cutset slope `1 / ln 2 ≈ 1.4427`;
* El Gamal–Gohari–Nair (2022): `C_Gauss` is strictly below the cutset bound at every fixed
  `P > 0`. No converse improving the cutset slope at `P → 0` is known to us
  (Kosut–Effros–Langberg 2024 still compare with the cutset bound only).
-/

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

/-- Exact Capacity of the Three-Node Gaussian Relay Channel (Cover–El Gamal 1979), low-SNR
    benchmark (minimum energy-per-bit, El Gamal–Mohseni–Zahedi 2006): for unit channel gains
    and equal source/relay powers `P₁ = P₂ = P`, does the capacity per unit power
    `C_Gauss(1, 1, 1, P, P) / P` tend, as `P → 0⁺`, to the cutset slope `1 / ln 2`
    (bits per unit power)? Equivalently: is the cutset bound tight to first order at low SNR? -/
def Statement : Prop :=
  Filter.Tendsto (fun P : ℝ => gaussianRelayCapacity 1 1 1 P P / ENNReal.ofReal P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (1 / Real.log 2)))

def problem : OpenProblem where
  id := "gaussian-relay-channel-capacity"
  title := "Exact Capacity of the Three-Node Gaussian Relay Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas Cover and Abbas El Gamal"
  posedYear := 1979
  statement := Statement

end InfoTheory.Problems.GaussianRelayChannelCapacity
