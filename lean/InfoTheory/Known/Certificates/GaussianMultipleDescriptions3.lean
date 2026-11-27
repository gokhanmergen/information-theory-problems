import InfoTheory.Problems.GaussianMultipleDescriptions3
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.GaussianMultipleDescriptions3`

The frozen statement asks whether the optimal symmetric per-description rate
`gaussMD3SymRate` of three-description quadratic Gaussian multiple descriptions equals the
Tian–Chen rate `tianChenMD3SymRate` for all `0 < D₃ ≤ D₂ ≤ D₁ ≤ 1` (both in `ℝ≥0∞`).

## Certified (about exactly these objects)
* `tianChenMD3SymRate_lt_top` — the Tian–Chen rate is finite (feasible parameter set nonempty)
  whenever `D₁, D₂ > 0`, so the right-hand side is not the junk `⊤`.
* `half_log_le_tianChenMD3SymRate` — the Tian–Chen rate respects the single-description
  converse `R ≥ ½ log₂(1/D₁)` (Shannon's Gaussian rate–distortion function), as any achievable
  symmetric rate must; uses `mds_factor_le_one` (`(1+2ρ)(1-ρ)² ≤ 1` on `(-1/2, 1)`).

## Not certified
* Anything about `gaussMD3SymRate` itself: finiteness needs explicit measurable quantizers and
  Gaussian integrals over `Fin n → ℝ`, and lower bounds need the Gaussian MD converse
  (Ozarow 1980; Tian–Chen 2009, Wang–Viswanath 2007); none are in `Bridge`.
-/

open scoped BigOperators ENNReal

namespace InfoTheory.Known.Certificates.GaussianMultipleDescriptions3

open InfoTheory InfoTheory.Problems.GaussianMultipleDescriptions3

/-- **The Tian–Chen rate is finite** (not the `⊤` of an empty feasible set) whenever
    `D₁, D₂ > 0`: the parameters `v₀ = 1, σ² = D₁, ρ = 0, τ₂ = D₂` are feasible. -/
theorem tianChenMD3SymRate_lt_top {D₁ D₂ D₃ : ℝ} (h1 : 0 < D₁) (h2 : 0 < D₂) :
    tianChenMD3SymRate D₁ D₂ D₃ < ⊤ := by
  unfold tianChenMD3SymRate
  refine lt_of_le_of_lt (sInf_le ⟨1, D₁, 0, D₂, one_pos, le_rfl, h1, by norm_num, by norm_num,
    h2, ?_, ?_, rfl⟩) ENNReal.ofReal_lt_top
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · have hb : 0 ≤ 1 * D₁ * (1 + 0) / (2 * 1 + D₁ * (1 + 0)) := by positivity
    rw [div_le_iff₀ (by positivity)]; nlinarith

/-- `(1 + 2ρ)(1 - ρ)² ≤ 1` on `(-1/2, 1)`, so the MDS-lattice penalty term is nonnegative. -/
theorem mds_factor_le_one {ρ : ℝ} (h0 : -(1 / 2 : ℝ) < ρ) (h1 : ρ < 1) :
    0 < (1 + 2 * ρ) * (1 - ρ) ^ 2 ∧ (1 + 2 * ρ) * (1 - ρ) ^ 2 ≤ 1 := by
  refine ⟨mul_pos (by linarith) (by nlinarith), ?_⟩
  nlinarith [sq_nonneg ρ, mul_nonneg (sq_nonneg ρ) (by linarith : (0 : ℝ) ≤ 3 - 2 * ρ)]

theorem log2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  div_nonneg (Real.log_nonneg hx) (Real.log_pos one_lt_two).le

theorem log2_mul_inv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log2 (1 / x) + log2 (x / y) = log2 (1 / y) := by
  unfold log2
  rw [← add_div, ← Real.log_mul (by positivity) (by positivity)]
  congr 2; field_simp

/-- **The Tian–Chen rate respects the single-description converse**
    `R ≥ R_X(D₁) = ½ log₂ (1 / D₁)` (Shannon's Gaussian rate–distortion function; any
    achievable symmetric rate must satisfy it, since each description alone reaches `D₁`). -/
theorem half_log_le_tianChenMD3SymRate {D₁ D₂ D₃ : ℝ} (h1 : 0 < D₁) :
    ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 / D₁)) ≤ tianChenMD3SymRate D₁ D₂ D₃ := by
  unfold tianChenMD3SymRate
  refine le_sInf ?_
  rintro r ⟨v₀, σsq, ρ, τ₂, hv0, hv1, hσ, hρ0, hρ1, hτ, hd1, hd2, rfl⟩
  refine ENNReal.ofReal_le_ofReal ?_
  set d1 := (v₀ * σsq) / (v₀ + σsq) with hd1def
  have hd1pos : 0 < d1 := by positivity
  have hρ1' : 0 < 1 + ρ := by linarith
  have hbase : 0 ≤ (v₀ * σsq * (1 + ρ)) / (2 * v₀ + σsq * (1 + ρ)) := by positivity
  obtain ⟨hfpos, hfle⟩ := mds_factor_le_one hρ0 hρ1
  have hA : 0 ≤ (1 / 6 : ℝ) * log2 (1 / ((1 + 2 * ρ) * (1 - ρ) ^ 2)) :=
    mul_nonneg (by norm_num) (log2_nonneg (by rw [le_div_iff₀ hfpos]; linarith))
  have hB : 0 ≤ (1 / 4 : ℝ) * log2 (1 + (v₀ * σsq * (1 + ρ)) / (2 * v₀ + σsq * (1 + ρ)) / τ₂) :=
    mul_nonneg (by norm_num) (log2_nonneg (by
      have : 0 ≤ (v₀ * σsq * (1 + ρ)) / (2 * v₀ + σsq * (1 + ρ)) / τ₂ := by positivity
      linarith))
  have hC : 0 ≤ (1 / 6 : ℝ) * max 0 (log2 ((((v₀ * σsq * (1 + 2 * ρ)) /
      (3 * v₀ + σsq * (1 + 2 * ρ))) * τ₂) / (((v₀ * σsq * (1 + 2 * ρ)) /
      (3 * v₀ + σsq * (1 + 2 * ρ))) + τ₂) / D₃)) :=
    mul_nonneg (by norm_num) (le_max_left _ _)
  have hsum := log2_mul_inv hv0 hd1pos
  have hmono : log2 (1 / D₁) ≤ log2 (1 / d1) := by
    unfold log2
    exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity)
      (one_div_le_one_div_of_le hd1pos hd1)) (Real.log_pos one_lt_two).le
  linarith

end InfoTheory.Known.Certificates.GaussianMultipleDescriptions3
