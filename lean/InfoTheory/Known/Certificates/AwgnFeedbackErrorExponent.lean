import InfoTheory.Problems.AwgnFeedbackErrorExponent
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.AwgnFeedbackErrorExponent`

The frozen statement asks whether the reliability function of the peak-energy-constrained
AWGN channel with noiseless feedback (valued in `ℝ≥0∞`) equals Shannon's sphere-packing
exponent `E_sp(R, P)` for `0 < R < ½ ln(1 + P)`.

## Certified (about exactly these objects)
* `awgnSpherePacking_capacity` — `E_sp(½ ln(1+P), P) = 0` exactly: Shannon's (1959) formula as
  formalized vanishes at capacity, a sanity check of its normalization (nats, unit noise
  variance, `A = √P`).

## Not certified
* Finiteness of `awgnFeedbackPeakReliability` (needs a lower bound on the error probability of
  every feedback code, i.e. Pinsker's 1968 sphere-packing converse with feedback) and any
  achievability (needs Gaussian random coding with explicit `lintegral` computations over
  `Fin n → ℝ`); neither is in `Bridge`.
* Positivity of `E_sp(R, P)` for `R < C` (requires a monotonicity analysis of the formula; not
  attempted).
-/

open scoped BigOperators ENNReal

namespace InfoTheory.Known.Certificates.AwgnFeedbackErrorExponent

open InfoTheory InfoTheory.Problems.AwgnFeedbackErrorExponent

/-- **Sanity check of Shannon's sphere-packing formula**: at capacity `R = ½ ln(1 + P)` the
    exponent `E_sp(R, P)` vanishes exactly (Shannon 1959, Eq. (5) and §5: `E_sp(C) = 0`),
    so `awgnSpherePacking` is the correctly normalized (nats, unit noise) exponent. -/
theorem awgnSpherePacking_capacity {P : ℝ} (hP : 0 < P) :
    awgnSpherePacking ((1 / 2 : ℝ) * Real.log (1 + P)) P = 0 := by
  have h1P : 0 < 1 + P := by linarith
  set s := Real.sqrt (1 + P) with hs
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h1P
  have hs_sq : s * s = 1 + P := Real.mul_self_sqrt h1P.le
  have hsqP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP.le
  have hsin : Real.exp (-((1 / 2 : ℝ) * Real.log (1 + P))) = s⁻¹ := by
    rw [Real.exp_neg, hs, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h1P, mul_comm]
  have hcos : Real.sqrt (1 - Real.exp (-2 * ((1 / 2 : ℝ) * Real.log (1 + P)))) =
      Real.sqrt P / s := by
    have : -2 * ((1 / 2 : ℝ) * Real.log (1 + P)) = -Real.log (1 + P) := by ring
    rw [this, Real.exp_neg, Real.exp_log h1P,
      show 1 - (1 + P)⁻¹ = P / (1 + P) by field_simp; ring, Real.sqrt_div hP.le]
  have hA : Real.sqrt P * (Real.sqrt P / s) = P / s := by rw [← mul_div_assoc, hsqP]
  have hinner : Real.sqrt (P * (Real.sqrt P / s) ^ 2 + 4) = (P + 2) / s := by
    have : P * (Real.sqrt P / s) ^ 2 + 4 = ((P + 2) / s) ^ 2 := by
      rw [div_pow, div_pow, sq (Real.sqrt P), hsqP, sq s, hs_sq]
      field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hg : (1 / 2 : ℝ) * (P / s + (P + 2) / s) = s := by
    field_simp
    nlinarith [hs_sq]
  unfold awgnSpherePacking
  dsimp only
  rw [hcos, hsin, hA, hinner, hg]
  have hlog : Real.log (s * s⁻¹) = 0 := by rw [mul_inv_cancel₀ hs_pos.ne', Real.log_one]
  rw [hlog]
  field_simp
  nlinarith [hsqP]

end InfoTheory.Known.Certificates.AwgnFeedbackErrorExponent
