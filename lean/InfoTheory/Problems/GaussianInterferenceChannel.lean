import InfoTheory.Core

open scoped BigOperators Classical
open MeasureTheory

namespace InfoTheory.Problems.GaussianInterferenceChannel

/-- Single-letter Gaussian Han–Kobayashi achievable rate pair `(R₁, R₂)` for the
    two-user Gaussian interference channel `Y₁ = X₁ + a X₂ + Z₁`, `Y₂ = b X₁ + X₂ + Z₂`
    with power constraints `P₁, P₂` and power splits `P₁ = P₁c + P₁p`, `P₂ = P₂c + P₂p`
    (without time-sharing; full convex hull is taken in `InGaussianHKRegion`). -/
def InGaussianHKBasic (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ (P₁c P₁p P₂c P₂p : ℝ),
    0 ≤ P₁c ∧ 0 ≤ P₁p ∧ P₁c + P₁p ≤ P₁ ∧
    0 ≤ P₂c ∧ 0 ≤ P₂p ∧ P₂c + P₂p ≤ P₂ ∧
    let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
    let N₁ := 1 + a ^ 2 * P₂p
    let N₂ := 1 + b ^ 2 * P₁p
    R₁ ≤ cap ((P₁c + P₁p) / N₁) ∧
    R₂ ≤ cap ((P₂c + P₂p) / N₂) ∧
    R₁ + R₂ ≤ cap ((P₁c + P₁p + a ^ 2 * P₂c) / N₁) + cap (P₂p / N₂) ∧
    R₁ + R₂ ≤ cap (P₁p / N₁) + cap ((P₂c + P₂p + b ^ 2 * P₁c) / N₂) ∧
    R₁ + R₂ ≤ cap ((P₁p + a ^ 2 * P₂c) / N₁) + cap ((P₂p + b ^ 2 * P₁c) / N₂) ∧
    2 * R₁ + R₂ ≤ cap ((P₁c + P₁p + a ^ 2 * P₂c) / N₁) + cap (P₁p / N₁) +
                  cap ((P₂p + b ^ 2 * P₁c) / N₂) ∧
    R₁ + 2 * R₂ ≤ cap ((P₂c + P₂p + b ^ 2 * P₁c) / N₂) + cap (P₂p / N₂) +
                  cap ((P₁p + a ^ 2 * P₂c) / N₁)

/-- Convex hull (time-sharing with power control) of Gaussian Han–Kobayashi achievable rate pairs. -/
def InGaussianHKRegion (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  ∃ (m : ℕ) (w : Fin m → ℝ) (p₁ p₂ r₁ r₂ : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
    (∀ i, 0 ≤ p₁ i ∧ 0 ≤ p₂ i) ∧
    (∑ i : Fin m, w i * p₁ i ≤ P₁) ∧
    (∑ i : Fin m, w i * p₂ i ≤ P₂) ∧
    (∀ i, InGaussianHKBasic a b (p₁ i) (p₂ i) (r₁ i) (r₂ i)) ∧
    R₁ = ∑ i : Fin m, w i * r₁ i ∧
    R₂ = ∑ i : Fin m, w i * r₂ i

/-- Operational Gaussian IC achievability with measurable decoders, average power
    constraints `P₁, P₂`, and error evaluated via Lebesgue `lintegral`. -/
def InGaussianICAchievable (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc₁ : Fin M₁ → Fin n → ℝ) (enc₂ : Fin M₂ → Fin n → ℝ)
      (dec₁ : (Fin n → ℝ) → Fin M₁) (dec₂ : (Fin n → ℝ) → Fin M₂),
      Measurable dec₁ ∧ Measurable dec₂ ∧
      (∀ m₁, (∑ i : Fin n, (enc₁ m₁ i) ^ 2) ≤ (n : ℝ) * P₁) ∧
      (∀ m₂, (∑ i : Fin n, (enc₂ m₂ i) ^ 2) ≤ (n : ℝ) * P₂) ∧
      let errProb (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ :=
        (∫⁻ z₁ : Fin n → ℝ, ∫⁻ z₂ : Fin n → ℝ,
          let g₁ := ∏ i : Fin n, gaussianPdf1D 1 (z₁ i)
          let g₂ := ∏ i : Fin n, gaussianPdf1D 1 (z₂ i)
          let y₁ := fun i => enc₁ m₁ i + a * enc₂ m₂ i + z₁ i
          let y₂ := fun i => b * enc₁ m₁ i + enc₂ m₂ i + z₂ i
          if dec₁ y₁ ≠ m₁ ∨ dec₂ y₂ ≠ m₂ then ENNReal.ofReal (g₁ * g₂) else 0).toReal
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, errProb m₁ m₂ ≤ ε

/-- Exact Capacity Region of the Two-User Gaussian Interference Channel (Ahlswede; Carleial 1974;
    Han–Kobayashi 1981): Does the closure of the Gaussian Han–Kobayashi inner bound (with
    time-sharing) equal the closed capacity region for all coupling coefficients `(a, b)`
    and positive powers `(P₁, P₂)`? -/
def Statement : Prop :=
  ∀ (a b P₁ P₂ : ℝ), 0 < P₁ → 0 < P₂ →
    closure { p : ℝ × ℝ | InGaussianICAchievable a b P₁ P₂ p.1 p.2 } =
      closure { p : ℝ × ℝ | InGaussianHKRegion a b P₁ P₂ p.1 p.2 }

def problem : OpenProblem where
  id := "gaussian-interference-channel"
  title := "Exact Capacity Region of the Two-User Gaussian Interference Channel"
  category := .networkInfoTheory
  status := .partiallySolved
  posedBy := "Ahlswede; Carleial"
  posedYear := 1974
  statement := Statement

end InfoTheory.Problems.GaussianInterferenceChannel
