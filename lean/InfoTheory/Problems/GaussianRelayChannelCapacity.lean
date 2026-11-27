import InfoTheory.Core

open scoped BigOperators Classical ENNReal
open MeasureTheory

/-!
# Minimum Energy per Bit of the Symmetric Gaussian Relay Channel: Is Linear Relaying Optimal?

Channel: `Y_r = g₁₂ X + Z_r`, `Y = g₁₃ X + g₂₃ X_r + Z`, independent `Z_r, Z ~ N(0, 1)`,
per-codeword source power `∑ᵢ xᵢ² ≤ n P₁`, per-message expected relay power
`E ∑ᵢ X_{r,i}² ≤ n P₂`, strictly causal measurable relay `X_{r,i} = f_i(Y_r^{i-1})`.
A relay is *linear* if `X_{r,i} = ∑_{j<i} d_{ij} Y_{r,j}` (El Gamal–Mohseni–Zahedi 2006,
Sec. V; Kosut–Effros–Langberg 2024). The minimum energy per bit is
`E* = inf { (P₁ + P₂) / R : P₁, P₂ > 0, R > 0 achievable at (P₁, P₂) }` (EMZ 2006, Thm. 1 form),
and `E*_lin` is the same infimum over linear-relaying codes; both are valued in `ℝ≥0∞`.

**Question.** At unit gains, is `E*(1,1,1) = E*_lin(1,1,1)`, i.e. does linear relaying achieve
the minimum energy per bit of the symmetric AWGN relay channel?

Known (unit gains):
* `(3/4) · 2 ln 2 ≤ E*`: cutset bound (EMZ 2006, Table II; not formalized);
* `E* ≤ E*_lin ≤ 2 ln 2`: linear relays are relays, and direct transmission with a silent
  (hence linear) relay achieves every energy per bit above `2 ln 2` (both certified in
  `Known.Certificates.GaussianRelayChannelCapacity`);
* no published code is known to beat `2 ln 2` at these gains; `E*_lin` has no closed form and
  only upper bounds are known (EMZ 2006, KEL 2024);
* a first-order evaluation of the El Gamal–Gohari–Nair (2022) bound gives
  `E* ≳ 0.93 · 2 ln 2` (numerical, unpublished;
  `attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md`).

**Statement fix 1 (2026-11-27).** The original statement ("capacity = Gaussian hybrid
DF/CF rate of Cover–El Gamal Thm. 7 for all gains and powers") was false: the rate has no power
time-sharing and El Gamal–Mohseni–Zahedi 2006 (bursty CF, eq. (8); linear relaying, Example 1)
beat it (`attempts/gaussian-relay-channel-capacity/2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md`).

**Statement fix 2 (2026-11-27).** The replacement asked whether
`gaussianRelayCapacity 1 1 1 P P / P → 1 / ln 2` as `P → 0⁺` (cutset tight to first order;
kept below as `LowSnrCutsetSlopeStatement`). It is believed false: the published
El Gamal–Gohari–Nair 2022 Gaussian upper bound (Cor. 1 / Thm. 2) evaluates, to first order,
to `C_Gauss(1,1,1,P,P) ≲ 1.1106 · P` bits `< P / ln 2`; a closed-form reduction of that
first-order bound is certified `≤ 0.7700 ×` cutset by interval arithmetic (see the 2026-11-27
EGN attempt for exactly what is and is not certified).
-/

namespace InfoTheory.Problems.GaussianRelayChannelCapacity

/-- A strictly causal relay strategy `relay i : (Fin i → ℝ) → ℝ` is *linear* if every relay
    symbol is a fixed linear combination of the relay's past received symbols,
    `x_{r,i} = ∑_{j < i} d_{ij} y_{r,j}` (a strictly lower-triangular relaying matrix), as in
    El Gamal–Mohseni–Zahedi 2006, Sec. V, and Kosut–Effros–Langberg 2024, Sec. II. The source
    encoder and the decoder are unrestricted. -/
def IsLinearRelay {n : ℕ} (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ) : Prop :=
  ∃ d : ∀ i : Fin n, Fin i.1 → ℝ, ∀ (i : Fin n) (y : Fin i.1 → ℝ), relay i y = ∑ j, d i j * y j

/-- Operational achievability of rate `R` over the memoryless Gaussian relay channel
    `Y_r = g₁₂ X + Z_r`, `Y = g₁₃ X + g₂₃ X_r + Z` with independent `Z_r, Z ~ N(0, 1)`,
    measurable causal relay functions and decoder, and power/error evaluated directly in
    `ℝ≥0∞` via Lebesgue `lintegral` (preventing Bochner/toReal junk `0`). With
    `linearOnly = true` the relay must be linear (`IsLinearRelay`); with `linearOnly = false`
    the extra conjunct is vacuous and the relay is arbitrary. -/
def IsGaussianRelayAchievable (linearOnly : Bool) (g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : Fin M → Fin n → ℝ)
      (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
      (dec : (Fin n → ℝ) → Fin M),
      (linearOnly = true → IsLinearRelay relay) ∧
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

/-- Capacity `C_Gauss(g₁₂, g₁₃, g₂₃, P₁, P₂)` of the three-node Gaussian relay channel
    (arbitrary relays), valued in `ℝ≥0∞` so an unbounded achievable set evaluates to `⊤`
    rather than junk `0`. Not used by `Statement`. -/
noncomputable def gaussianRelayCapacity (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) : ℝ≥0∞ :=
  sSup { r : ℝ≥0∞ | ∃ R : ℝ, IsGaussianRelayAchievable false g₁₂ g₁₃ g₂₃ P₁ P₂ R ∧
    r = ENNReal.ofReal R }

/-- Minimum (total) energy per bit, in the form of El Gamal–Mohseni–Zahedi 2006, Thm. 1: the
    infimum of `(P₁ + P₂) / R` over operating points with `P₁, P₂ > 0`, `R > 0` and `R`
    achievable at powers `(P₁, P₂)`. Source and relay energy have equal weight and the noise
    variances are `1`. With `linearOnly = true` the infimum is over linear-relaying codes
    (`E*_lin`), otherwise over all codes (`E*`). Valued in `ℝ≥0∞`: an empty operating set gives
    `⊤`, never junk `0`; `R > 0` rules out division by zero. -/
noncomputable def gaussianRelayMinEnergyPerBit (linearOnly : Bool) (g₁₂ g₁₃ g₂₃ : ℝ) : ℝ≥0∞ :=
  sInf { e : ℝ≥0∞ | ∃ P₁ P₂ R : ℝ, 0 < P₁ ∧ 0 < P₂ ∧ 0 < R ∧
    IsGaussianRelayAchievable linearOnly g₁₂ g₁₃ g₂₃ P₁ P₂ R ∧
    e = ENNReal.ofReal ((P₁ + P₂) / R) }

/-- RETIRED (statement fix 2, 2026-11-27): the previous catalog statement, "is the cutset slope
    `1 / ln 2` the low-SNR capacity slope at unit gains and equal powers?". Believed FALSE: the
    El Gamal–Gohari–Nair 2022 Gaussian upper bound gives slope `≲ 1.1106 < 1 / ln 2 ≈ 1.4427`
    (see the module docstring). Kept for reference only; it is not the catalog `Statement`. -/
def LowSnrCutsetSlopeStatement : Prop :=
  Filter.Tendsto (fun P : ℝ => gaussianRelayCapacity 1 1 1 P P / ENNReal.ofReal P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (1 / Real.log 2)))

/-- Minimum Energy per Bit of the Symmetric Gaussian Relay Channel — Is Linear Relaying
    Optimal? (El Gamal–Mohseni–Zahedi 2006; Kosut–Effros–Langberg 2024.)
    At unit gains `g₁₂ = g₁₃ = g₂₃ = 1`, does linear relaying achieve the minimum energy per
    bit, `E*(1,1,1) = E*_lin(1,1,1)`?

    Known: `(3/4) · 2 ln 2 ≤ E* ≤ E*_lin ≤ 2 ln 2`. The lower bound is the cutset bound
    (EMZ 2006, Table II); `E* ≤ E*_lin` holds because linear relays are relays;
    `E*_lin ≤ 2 ln 2` is direct transmission with a silent relay. `E*_lin` has no closed form,
    and no published code is known to beat `2 ln 2` at these gains. -/
def Statement : Prop :=
  gaussianRelayMinEnergyPerBit false 1 1 1 = gaussianRelayMinEnergyPerBit true 1 1 1

def problem : OpenProblem where
  id := "gaussian-relay-channel-capacity"
  title := "Minimum Energy per Bit of the Symmetric Gaussian Relay Channel: Is Linear Relaying Optimal?"
  category := .networkInfoTheory
  status := .open
  posedBy := "Abbas El Gamal, Mehdi Mohseni, and Sina Zahedi"
  posedYear := 2006
  statement := Statement

end InfoTheory.Problems.GaussianRelayChannelCapacity
