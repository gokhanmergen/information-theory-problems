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
* **Regression (zero-rate value; passes).**  `awgnSpherePacking_zero` : `E_sp(0, P) = P/2`;
  `continuousAt_awgnSpherePacking_zero`, `tendsto_awgnSpherePacking_zero` : `E_sp(R, P) → P/2`
  as `R → 0⁺`, the known zero-rate value (Shannon 1959), equal to the zero-rate peak-energy
  feedback exponent `E_fb^peak(0⁺, P) = P/2` (Pinsker 1968; Zigangirov 1970) quoted in the
  problem file.  Consequently `eventually_awgnSpherePacking_pos` : `E_sp(R, P) > 0` for small
  `R > 0`.

## Not certified
* Finiteness of `awgnFeedbackPeakReliability` (needs a lower bound on the error probability of
  every feedback code, i.e. Pinsker's 1968 sphere-packing converse with feedback) and any
  achievability (needs Gaussian random coding with explicit `lintegral` computations over
  `Fin n → ℝ`); neither is in `Bridge`.
* Positivity of `E_sp(R, P)` on all of `(0, C)` (requires a monotonicity analysis of the
  formula; only small `R` is certified).
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

/-- **Regression (zero-rate value).**  `E_sp(0, P) = P/2`: at `R = 0` (`sin θ = 1`, `cos θ = 0`,
    `g = 1`) Shannon's formula gives the known zero-rate value `E_sp(0⁺, P) = P/2`
    (Shannon 1959), which is also the zero-rate peak-energy feedback exponent
    `E_fb^peak(0⁺, P) = P/2` (Pinsker 1968; Zigangirov 1970). -/
theorem awgnSpherePacking_zero (P : ℝ) : awgnSpherePacking 0 P = P / 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold awgnSpherePacking
  simp [h4]

/-- `R ↦ E_sp(R, P)` is continuous at `R = 0` (the logarithm's argument is `g sin θ = 1 ≠ 0`
    there). -/
theorem continuousAt_awgnSpherePacking_zero (P : ℝ) :
    ContinuousAt (fun R => awgnSpherePacking R P) 0 := by
  have hcos : Continuous fun R : ℝ => Real.sqrt (1 - Real.exp (-2 * R)) := by fun_prop
  have hg : Continuous fun R : ℝ => (1 / 2 : ℝ) * (Real.sqrt P * Real.sqrt (1 - Real.exp (-2 * R)) +
      Real.sqrt (P * Real.sqrt (1 - Real.exp (-2 * R)) ^ 2 + 4)) := by fun_prop
  have hsin : Continuous fun R : ℝ => Real.exp (-R) := by fun_prop
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold awgnSpherePacking
  dsimp only
  refine ContinuousAt.sub (ContinuousAt.sub continuousAt_const ?_) ?_
  · exact (((continuous_const.mul hg).mul hcos).div_const 2).continuousAt
  · refine ((hg.mul hsin).continuousAt).log ?_
    simp [h4]

/-- Hence `E_sp(R, P) → P/2` as `R → 0⁺`, matching the known zero-rate exponent. -/
theorem tendsto_awgnSpherePacking_zero (P : ℝ) :
    Filter.Tendsto (fun R => awgnSpherePacking R P) (nhdsWithin 0 (Set.Ioi 0)) (nhds (P / 2)) := by
  have h := (continuousAt_awgnSpherePacking_zero P).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rwa [awgnSpherePacking_zero] at h

/-- In particular `E_sp(R, P) > 0` for all sufficiently small rates `R > 0` (when `P > 0`). -/
theorem eventually_awgnSpherePacking_pos {P : ℝ} (hP : 0 < P) :
    ∀ᶠ R in nhdsWithin 0 (Set.Ioi 0), 0 < awgnSpherePacking R P :=
  (tendsto_awgnSpherePacking_zero P).eventually (lt_mem_nhds (by linarith))

end InfoTheory.Known.Certificates.AwgnFeedbackErrorExponent
