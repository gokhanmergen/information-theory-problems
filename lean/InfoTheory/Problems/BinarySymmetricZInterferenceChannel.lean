import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BinarySymmetricZInterferenceChannel

/-- Closed-form capacity region of the Binary Symmetric Z-Interference Channel (BS-ZIC):
    - Strong regime (`p₁ ≤ p₂`): `R₂ ≤ 1 - h(p₂)` and `R₁ + R₂ ≤ 1 - h(p₁)` (Sato 1981 / Costa–El Gamal).
    - Weak regime (`p₁ > p₂`): `R₂ ≤ 1 - h(p₂)` and
      `R₁ ≤ 1 - h(q ★ h⁻¹(h(p₂) + R₂))` where `q = (p₁ - p₂) / (1 - 2 p₂)` (Benzel 1979 / Liu–Goldsmith 2009). -/
def bsZicClosedFormRegion (p₁ p₂ : ℝ) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.2 ≤ 1 - binaryEntropy p₂ ∧
    if p₁ ≤ p₂ then
      r.1 + r.2 ≤ 1 - binaryEntropy p₁
    else
      let q := (p₁ - p₂) / (1 - 2 * p₂)
      r.1 ≤ 1 - binaryEntropy (binaryConv q (invBinaryEntropy (binaryEntropy p₂ + r.2))) }

/-- Capacity Region of the Binary Symmetric Z-Interference Channel (resolved via
    Benzel 1979, Sato 1981, Liu–Goldsmith 2009): for all `p₁, p₂ ∈ (0, 1/2)`, the
    operational capacity region equals `bsZicClosedFormRegion p₁ p₂`. -/
def Statement : Prop :=
  ∀ (p₁ p₂ : ℝ) (h10 : 0 < p₁) (h11 : p₁ < 1 / 2) (h20 : 0 < p₂) (h21 : p₂ < 1 / 2),
    icCapacityRegion (bsZicChannel p₁ p₂ (le_of_lt h10) (by linarith) (le_of_lt h20) (by linarith)) =
      bsZicClosedFormRegion p₁ p₂

def problem : OpenProblem where
  id := "binary-symmetric-z-interference-channel"
  title := "Capacity Region of the Binary Symmetric Z-Interference Channel"
  category := .networkInfoTheory
  status := .solved
  posedBy := "folklore"
  posedYear := 1980
  statement := Statement

end InfoTheory.Problems.BinarySymmetricZInterferenceChannel
