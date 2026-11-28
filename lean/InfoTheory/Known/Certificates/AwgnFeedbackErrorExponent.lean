import InfoTheory.Problems.AwgnFeedbackErrorExponent
import InfoTheory.Known
import InfoTheory.Bridge.GaussianConverse

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
* **The frozen feedback model is the `Bridge` causal model.**  `fbDrift`, `fbDrift_causal`,
  `fbDrift_measurable`, `awgnFeedbackPrefix_eq` / `awgnFeedbackPrefix_full` (the frozen
  recursion `awgnFeedbackPrefix` is `Bridge.causalOutput (fbDrift enc m)`), and
  `awgnFeedbackAvgError_eq` (the frozen density-`lintegral` error equals the
  `awgnNoise n 1` error probability).  `feasible_code_converse` : every feasible code of
  `awgnFeedbackPeakMinError` satisfies the weak feedback converse
  `(1 - P_e) ln M ≤ n · ½ ln(1 + P) + 1` (peak energy ⇒ expected energy;
  `Bridge.causal_awgn_feedback_code_converse`).
* **Regression (reliability vanishes above capacity; passes).**
  `awgnFeedbackPeakReliability_eq_zero_of_gt` : for `P ≥ 0` and `R > ½ ln(1 + P)`,
  `awgnFeedbackPeakReliability R P = 0`.  This confirms the rate normalization (nats,
  `M = ⌈e^{nR}⌉`) of the frozen reliability function; it says nothing about `R < C`, where
  `Statement` lives.

## Not certified
* Finiteness of `awgnFeedbackPeakReliability` for `0 < R < ½ ln(1 + P)` (needs an exponential
  lower bound on the error probability of every feedback code, i.e. Pinsker's 1968
  sphere-packing converse with feedback; the `Bridge` weak converse gives nothing below
  capacity) and any
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

/-! ### The operational model and the weak feedback converse -/

section Converse

open MeasureTheory
open InfoTheory.Bridge (causalOutput IsStrictlyCausal causalOutput_eq measurable_causalOutput
  lintegral_awgnNoise_eq_volume causal_awgn_feedback_code_converse)

variable {n M : ℕ}

/-- The prefix-indexed feedback encoder `enc i m : (Fin i → ℝ) → ℝ` of the frozen model, read
    as a full-block drift `Fin n → (Fin n → ℝ) → ℝ` (it only looks at `y_t`, `t < i`). -/
def fbDrift (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ) (m : Fin M) :
    Fin n → (Fin n → ℝ) → ℝ :=
  fun i y => enc i m (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)

theorem fbDrift_causal (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ) (m : Fin M) :
    IsStrictlyCausal (fbDrift enc m) := by
  intro i y y' h
  simp only [fbDrift]
  congr 1
  funext j
  exact h _ (Fin.lt_def.mpr j.2)

theorem fbDrift_measurable (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ)
    (henc : ∀ i m, Measurable (enc i m)) (m : Fin M) (i : Fin n) :
    Measurable (fbDrift enc m i) :=
  (henc i m).comp (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)

/-- **The frozen causal recursion is the `Bridge` causal output**: the `k`-prefix built by
    `awgnFeedbackPrefix` agrees with the first `k` symbols of
    `Bridge.causalOutput (fbDrift enc m) z`. -/
theorem awgnFeedbackPrefix_eq (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ) (m : Fin M)
    (z : Fin n → ℝ) : ∀ (k : ℕ) (hk : k ≤ n) (j : Fin k),
      awgnFeedbackPrefix n M enc m z k hk j =
        causalOutput (fbDrift enc m) z ⟨j.1, lt_of_lt_of_le j.2 hk⟩
  | 0, _, j => j.elim0
  | k + 1, hk, j => by
    have ih := awgnFeedbackPrefix_eq enc m z k (Nat.le_of_succ_le hk)
    have hprev : awgnFeedbackPrefix n M enc m z k (Nat.le_of_succ_le hk) =
        fun j : Fin k => causalOutput (fbDrift enc m) z ⟨j.1, by omega⟩ := funext ih
    rw [awgnFeedbackPrefix]
    dsimp only
    split_ifs with h
    · exact ih ⟨j.1, h⟩
    · have hj : j.1 = k := by omega
      have hfin : (⟨j.1, lt_of_lt_of_le j.2 hk⟩ : Fin n) = ⟨k, hk⟩ := Fin.ext hj
      rw [hfin, causalOutput_eq (fbDrift_causal enc m) z ⟨k, hk⟩, hprev]
      rfl

theorem awgnFeedbackPrefix_full (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ) (m : Fin M)
    (z : Fin n → ℝ) :
    awgnFeedbackPrefix n M enc m z n (Nat.le_refl n) = causalOutput (fbDrift enc m) z :=
  funext fun j => awgnFeedbackPrefix_eq enc m z n (Nat.le_refl n) j

/-- **The frozen error functional is the `Bridge` error probability**: for `M ≠ 0` and
    measurable `enc`, `dec`, `awgnFeedbackAvgError` equals the average of
    `awgnNoise n 1 {z | dec (causalOutput (fbDrift enc m) z) ≠ m}`. -/
theorem awgnFeedbackAvgError_eq (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ)
    (dec : (Fin n → ℝ) → Fin M) (henc : ∀ i m, Measurable (enc i m)) (hdec : Measurable dec)
    (hM : M ≠ 0) :
    awgnFeedbackAvgError n M enc dec = (M : ℝ≥0∞)⁻¹ *
      ∑ m : Fin M, awgnNoise n 1 {z | dec (causalOutput (fbDrift enc m) z) ≠ m} := by
  unfold awgnFeedbackAvgError
  simp only [hM, ↓reduceIte]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hS : MeasurableSet {z : Fin n → ℝ | dec (causalOutput (fbDrift enc m) z) ≠ m} :=
    ((hdec.comp (measurable_causalOutput (fbDrift_measurable enc henc m)))
      (measurableSet_singleton m)).compl
  rw [← lintegral_indicator_one hS,
    lintegral_awgnNoise_eq_volume one_pos (measurable_one.indicator hS)]
  refine lintegral_congr fun z => ?_
  rw [awgnFeedbackPrefix_full]
  split_ifs with h
  · rw [Set.indicator_of_mem (show z ∈ _ from h), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (show z ∉ _ from h), mul_zero]

/-- **Weak feedback converse for every feasible code of the frozen model** (in nats):
    `(1 - P_e) ln M ≤ n · ½ ln(1 + P) + 1`, via `Bridge.causal_awgn_feedback_code_converse`
    (the peak energy constraint implies the expected one). -/
theorem feasible_code_converse {P : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ) (dec : (Fin n → ℝ) → Fin M)
    (henc : ∀ i m, Measurable (enc i m)) (hdec : Measurable dec)
    (hpeak : SatisfiesPeakEnergy n M P enc) :
    (1 - (awgnFeedbackAvgError n M enc dec).toReal) * Real.log (M : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P)) + 1 := by
  have hM0 : M ≠ 0 := by omega
  have henergy : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ *
      ∑ m : Fin M, ∫⁻ z, ENNReal.ofReal
        (∑ i : Fin n, (fbDrift enc m i (causalOutput (fbDrift enc m) z)) ^ 2) ∂(awgnNoise n 1) ≤
      ENNReal.ofReal ((n : ℝ) * P) := by
    rw [Fintype.card_fin]
    calc (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (fbDrift enc m i (causalOutput (fbDrift enc m) z)) ^ 2) ∂(awgnNoise n 1)
        ≤ (M : ℝ≥0∞)⁻¹ * ∑ _m : Fin M, ∫⁻ _z, ENNReal.ofReal ((n : ℝ) * P) ∂(awgnNoise n 1) := by
          gcongr with m z
          exact hpeak m _
      _ = ENNReal.ofReal ((n : ℝ) * P) := by
          rw [lintegral_const, measure_univ, mul_one, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel (by exact_mod_cast hM0) (ENNReal.natCast_ne_top M), one_mul]
  have hconv := causal_awgn_feedback_code_converse (N := 1) (S := P) one_pos hP
    (by rw [Fintype.card_fin]; exact hM) (fbDrift enc) (fbDrift_causal enc)
    (fbDrift_measurable enc henc) dec hdec henergy
  dsimp only at hconv
  rw [Fintype.card_fin, div_one] at hconv
  rwa [awgnFeedbackAvgError_eq enc dec henc hdec hM0]

/-- **Regression (reliability vanishes above capacity; passes).**  For `P ≥ 0` and any rate
    `R > ½ ln(1 + P)` (nats), the frozen reliability function is exactly `0`: an exponent
    `E > 0` would force `P_e* → 0` at a rate above capacity, contradicting the weak feedback
    converse.  This checks that the frozen `awgnFeedbackPeakReliability` uses the right rate
    normalization (`M = ⌈e^{nR}⌉`, capacity `½ ln(1 + P)` nats) and does not report a junk
    positive value where the answer is known. -/
theorem awgnFeedbackPeakReliability_eq_zero_of_gt {P R : ℝ} (hP : 0 ≤ P)
    (hR : (1 / 2 : ℝ) * Real.log (1 + P) < R) : awgnFeedbackPeakReliability R P = 0 := by
  set C := (1 / 2 : ℝ) * Real.log (1 + P) with hC
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hRpos : 0 < R := lt_of_le_of_lt hC0 hR
  refine le_antisymm (sSup_le ?_) bot_le
  rintro e ⟨E, hE0, rfl, hE⟩
  rcases hE0.eq_or_lt with h0 | hEpos
  · rw [← h0, ENNReal.ofReal_zero]
  exfalso
  -- `η = (R - C) / (2R)` so that `(1 - η) R - C = (R - C) / 2 > 0`.
  set d := (R - C) / 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set η := (R - C) / (2 * R) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by linarith)
  have hηR : (1 - η) * R - C = d := by rw [hη, hd]; field_simp; ring
  obtain ⟨N₀, -, hN₀⟩ := hE (E / 2) (by linarith)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (1 / d)
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (4 / (η * E))
  set n := max N₀ (max n₁ n₂) with hn
  have hnN₀ : N₀ ≤ n := le_max_left _ _
  have hn₁' : (n₁ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) (le_max_right _ _)
  have hn₂' : (n₂ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _)
  set M := Nat.ceil (Real.exp ((n : ℝ) * R)) with hMdef
  have hMge : Real.exp ((n : ℝ) * R) ≤ (M : ℝ) := Nat.le_ceil _
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (Real.exp_pos _)))
  have hlogM : (n : ℝ) * R ≤ Real.log (M : ℝ) := by
    rw [← Real.log_exp ((n : ℝ) * R)]
    exact Real.log_le_log (Real.exp_pos _) hMge
  -- the exponent bound at blocklength `n`
  set a := Real.exp (-(n : ℝ) * (E - E / 2)) with ha
  have hapos : 0 < a := Real.exp_pos _
  have hmin := hN₀ n hnN₀
  have hlt : awgnFeedbackPeakMinError n M P < ENNReal.ofReal (2 * a) :=
    lt_of_le_of_lt hmin ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  obtain ⟨e', ⟨enc, dec, henc, hdec, hpeak, rfl⟩, he'⟩ := sInf_lt_iff.mp hlt
  have herr : (awgnFeedbackAvgError n M enc dec).toReal ≤ 2 * a :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) he'.le
  have hconv := feasible_code_converse hP hM1 enc dec henc hdec hpeak
  -- `2a ≤ η`: `e^{-x} ≤ 1 / (1 + x)` with `x = nE/2`
  have hx : (n : ℝ) * (E / 2) * (η / 2) ≥ 1 := by
    have h1 : (4 / (η * E) : ℝ) < n := lt_of_lt_of_le hn₂ hn₂'
    have h2 : 4 < (n : ℝ) * (η * E) := by
      rwa [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  have ha_le : 2 * a ≤ η := by
    have hexp : 1 + (n : ℝ) * (E / 2) ≤ Real.exp ((n : ℝ) * (E / 2)) := by
      have := Real.add_one_le_exp ((n : ℝ) * (E / 2)); linarith
    have hprod : a * Real.exp ((n : ℝ) * (E / 2)) = 1 := by
      rw [ha, ← Real.exp_add]; rw [show -(n : ℝ) * (E - E / 2) + (n : ℝ) * (E / 2) = 0 by ring,
        Real.exp_zero]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set x := (n : ℝ) * (E / 2) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have h1 : a * (1 + x) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hexp hapos.le
      linarith
    have h2 : 2 ≤ η * x := by linarith
    have h3 : (2 * a - η) * (1 + x) ≤ 0 := by nlinarith
    by_contra hcon
    have : 0 < (2 * a - η) * (1 + x) := mul_pos (by linarith) (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by linarith)]; linarith
  have key : (1 - η) * ((n : ℝ) * R) ≤ (n : ℝ) * C + 1 := by
    calc (1 - η) * ((n : ℝ) * R) ≤ (1 - η) * Real.log (M : ℝ) :=
          mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ (1 - (awgnFeedbackAvgError n M enc dec).toReal) * Real.log (M : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlog0
      _ ≤ (n : ℝ) * C + 1 := hconv
  have hnd : 1 < (n : ℝ) * d := by
    have h1 : (1 / d : ℝ) < n := lt_of_lt_of_le hn₁ hn₁'
    rwa [div_lt_iff₀ hdpos] at h1
  have : (n : ℝ) * ((1 - η) * R - C) ≤ 1 := by nlinarith
  rw [hηR] at this
  linarith

end Converse

end InfoTheory.Known.Certificates.AwgnFeedbackErrorExponent
