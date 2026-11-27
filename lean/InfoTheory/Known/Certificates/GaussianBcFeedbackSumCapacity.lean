import InfoTheory.Problems.GaussianBcFeedbackSumCapacity
import InfoTheory.Known.GaussianAchievability

/-!
# Certificate for `InfoTheory.Problems.GaussianBcFeedbackSumCapacity`

The frozen statement asks whether, for the two-receiver Gaussian broadcast channel
`Y_k = h X + Z_k` with independent unit-variance noises and perfect output feedback, the
operational feedback sum-capacity `bcFbSumCapacity h h P` (in `ℝ≥0∞`) equals the
linear-feedback sum-capacity `linearFbSumRate h h P` of Belhadj Amor–Steinberg–Wigger (2015).

## Certified (about exactly these objects)
* **The feedback recursion is well posed.**  `output_fixed` : the received blocks `output`
  solve the causal channel equations `y_{k,i} = h_k xᵢ(y^{i-1}) + z_{k,i}`;
  `eq_output_of_fixed` : they are the unique solution; `measurable_output` : they depend
  measurably on the noise (so the energy `lintegral` is a genuine expectation).
* **Operational side non-vacuous.**  `isBcFbAchievable_zero` (`(0, 0)` achievable);
  `isBcFbAchievable_single` : every `0 ≤ R < ½ log₂(1 + h₁²P)` is achievable for receiver 1
  alone (using the operational AWGN coding theorem
  `Known.GaussianAchievability.isAwgnAchievable_of_lt_capacity` with a non-feedback code);
  hence `single_le_bcFbSumCapacity` : `ofReal(½ log₂(1 + h₁²P)) ≤ bcFbSumCapacity h₁ h₂ P`.
* **Formula side non-junk.**  `zero_mem_linearFbRegion`, `linearFbRegion_sum_le`
  (nonempty, bounded by `½ log₂(1 + (|h₁| + |h₂|)² P)`), so `linearFbSumRate` is a genuine
  supremum; `single_le_linearFbSumRate` and `linearFbSumRate_le`.
* `both_sides_ge_single` : in the symmetric case both sides of the equation are at least the
  no-feedback single-user rate `½ log₂(1 + h²P)`.

## Not certified
* Any upper bound on `bcFbSumCapacity` (a feedback converse, e.g. the cut-set bound
  `R₁ + R₂ ≤ ½ log₂(1 + 2h²P)`); in particular we do not certify that it is finite.  This needs
  a converse for codes with feedback (a change-of-measure through the causal output map), which
  the current `Known` library does not provide.
* Achievability of the linear-feedback region (Ozarow–Leung, Elia, Ardestanizadeh–Minero–
  Franceschetti, Belhadj Amor–Steinberg–Wigger), i.e. `ofReal (linearFbSumRate h h P) ≤
  bcFbSumCapacity h h P`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace InfoTheory.Known.Certificates.GaussianBcFeedbackSumCapacity

open InfoTheory InfoTheory.Problems.GaussianBcFeedbackSumCapacity

/-! ### The causal recursion -/

section Recursion

variable {n M₁ M₂ : ℕ} (C : BcFeedbackCode n M₁ M₂) (h₁ h₂ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂)
  (z : BcBlock n)

theorem step_fst (y : BcBlock n) (t : Fin n) :
    (C.step h₁ h₂ m₁ m₂ z y).1 t = h₁ * C.enc t m₁ m₂ y + z.1 t := rfl

theorem step_snd (y : BcBlock n) (t : Fin n) :
    (C.step h₁ h₂ m₁ m₂ z y).2 t = h₂ * C.enc t m₁ m₂ y + z.2 t := rfl

/-- After `k` passes, the output symbols at times `t < k` no longer change. -/
theorem iterate_stable (k : ℕ) : ∀ t : Fin n, t.val < k →
    ((C.step h₁ h₂ m₁ m₂ z)^[k + 1] z).1 t = ((C.step h₁ h₂ m₁ m₂ z)^[k] z).1 t ∧
    ((C.step h₁ h₂ m₁ m₂ z)^[k + 1] z).2 t = ((C.step h₁ h₂ m₁ m₂ z)^[k] z).2 t := by
  induction k with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ k ih =>
    intro t ht
    have henc : C.enc t m₁ m₂ ((C.step h₁ h₂ m₁ m₂ z)^[k + 1] z) =
        C.enc t m₁ m₂ ((C.step h₁ h₂ m₁ m₂ z)^[k] z) :=
      C.causal t m₁ m₂ _ _ (fun s hs =>
        ih s (lt_of_lt_of_le (Fin.lt_def.mp hs) (Nat.lt_succ_iff.mp ht)))
    rw [Function.iterate_succ_apply' _ (k + 1), step_fst, step_snd, henc,
      Function.iterate_succ_apply' _ k]
    exact ⟨rfl, rfl⟩

/-- **The output solves the causal channel equations**:
    `y_{k,i} = h_k · enc i m₁ m₂ y + z_{k,i}` for all `i`. -/
theorem output_fixed :
    C.step h₁ h₂ m₁ m₂ z (C.output h₁ h₂ m₁ m₂ z) = C.output h₁ h₂ m₁ m₂ z := by
  have hs := iterate_stable C h₁ h₂ m₁ m₂ z n
  unfold BcFeedbackCode.output
  rw [← Function.iterate_succ_apply' (C.step h₁ h₂ m₁ m₂ z) n]
  exact Prod.ext (funext fun t => (hs t t.2).1) (funext fun t => (hs t t.2).2)

/-- **Uniqueness**: any solution of the causal channel equations is `output`. -/
theorem eq_output_of_fixed (y : BcBlock n) (hy : C.step h₁ h₂ m₁ m₂ z y = y) :
    y = C.output h₁ h₂ m₁ m₂ z := by
  have key : ∀ k : ℕ, ∀ t : Fin n, t.val < k →
      ((C.step h₁ h₂ m₁ m₂ z)^[k] z).1 t = y.1 t ∧
      ((C.step h₁ h₂ m₁ m₂ z)^[k] z).2 t = y.2 t := by
    intro k
    induction k with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
    | succ k ih =>
      intro t ht
      have henc : C.enc t m₁ m₂ ((C.step h₁ h₂ m₁ m₂ z)^[k] z) = C.enc t m₁ m₂ y :=
        C.causal t m₁ m₂ _ _ (fun s hs =>
          ih s (lt_of_lt_of_le (Fin.lt_def.mp hs) (Nat.lt_succ_iff.mp ht)))
      rw [Function.iterate_succ_apply', step_fst, step_snd, henc]
      constructor
      · conv_rhs => rw [← hy]
        rfl
      · conv_rhs => rw [← hy]
        rfl
  unfold BcFeedbackCode.output
  exact (Prod.ext (funext fun t => (key n t t.2).1) (funext fun t => (key n t t.2).2)).symm

/-- The received blocks depend measurably on the noise. -/
theorem measurable_output : Measurable (C.output h₁ h₂ m₁ m₂) := by
  have hstep : ∀ g : BcBlock n → BcBlock n, Measurable g →
      Measurable (fun w => C.step h₁ h₂ m₁ m₂ w (g w)) := by
    intro g hg
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun i =>
        ((C.measurable_enc i m₁ m₂).comp hg).const_mul h₁ |>.add
          ((measurable_pi_apply i).comp measurable_fst)
    · exact measurable_pi_iff.mpr fun i =>
        ((C.measurable_enc i m₁ m₂).comp hg).const_mul h₂ |>.add
          ((measurable_pi_apply i).comp measurable_snd)
  have hk : ∀ k : ℕ, Measurable (fun w => (C.step h₁ h₂ m₁ m₂ w)^[k] w) := by
    intro k
    induction k with
    | zero => exact measurable_id
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      exact hstep _ ih
  exact hk n

end Recursion

/-! ### Operational side: achievable points -/

section Operational

variable {h₁ h₂ P R : ℝ}

/-- If an encoder ignores the feedback, the output is one pass of the channel equations. -/
theorem output_eq_of_open_loop {n M₁ M₂ : ℕ} (C : BcFeedbackCode n M₁ M₂) (m₁ : Fin M₁)
    (m₂ : Fin M₂) (z : BcBlock n)
    (hc : ∀ y, C.step h₁ h₂ m₁ m₂ z y = C.step h₁ h₂ m₁ m₂ z z) :
    C.output h₁ h₂ m₁ m₂ z = C.step h₁ h₂ m₁ m₂ z z := by
  unfold BcFeedbackCode.output
  cases n with
  | zero => exact Prod.ext (funext fun t => Fin.elim0 t) (funext fun t => Fin.elim0 t)
  | succ k => rw [Function.iterate_succ_apply']; exact hc _

theorem noise_isProb (n : ℕ) : IsProbabilityMeasure (BcFeedbackCode.noise n) := by
  unfold BcFeedbackCode.noise awgnNoise
  infer_instance

/-- Rate pair `(0, 0)` is achievable (one message each, zero input). -/
theorem isBcFbAchievable_zero : IsBcFbAchievable h₁ h₂ P 0 0 := by
  refine ⟨le_rfl, le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  have hM : max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * 0)⌋₊ = 1 := by simp
  rw [hM]
  let C : BcFeedbackCode n 1 1 :=
    { enc := fun _ _ _ _ => 0
      causal := fun _ _ _ _ _ _ => rfl
      measurable_enc := fun _ _ _ => measurable_const
      dec₁ := fun _ => 0
      dec₂ := fun _ => 0
      measurable_dec₁ := measurable_const
      measurable_dec₂ := measurable_const }
  refine ⟨C, ?_, ?_⟩
  · unfold BcFeedbackCode.SatisfiesPower BcFeedbackCode.expectedEnergy BcFeedbackCode.input
    simp [C]
  · have h0 : ∀ m₁ m₂ : Fin 1, C.errorProb h₁ h₂ m₁ m₂ = 0 := by
      intro m₁ m₂
      unfold BcFeedbackCode.errorProb
      have hempty : {z : BcBlock n | C.dec₁ (C.output h₁ h₂ m₁ m₂ z).1 ≠ m₁ ∨
          C.dec₂ (C.output h₁ h₂ m₁ m₂ z).2 ≠ m₂} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_or, not_not]
        exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [hempty, measure_empty]
    unfold BcFeedbackCode.avgErrorProb
    simp [h0]

/-- The non-feedback broadcast code that serves receiver 1 only, built from an AWGN code `D`
    (codewords scaled by `1/h₁`). -/
noncomputable def singleUserCode (h₁ : ℝ) {n M : ℕ} (D : AwgnCode n M) :
    BcFeedbackCode n M 1 where
  enc i m _ _ := D.encoder m i / h₁
  causal := fun _ _ _ _ _ _ => rfl
  measurable_enc := fun _ _ _ => measurable_const
  dec₁ := D.decoder
  dec₂ := fun _ => 0
  measurable_dec₁ := D.measurable_decoder
  measurable_dec₂ := measurable_const

theorem singleUserCode_errorProb (hh : h₁ ≠ 0) {n M : ℕ} (D : AwgnCode n M) (m₁ : Fin M)
    (m₂ : Fin 1) : (singleUserCode h₁ D).errorProb h₁ h₂ m₁ m₂ = awgnErrorProb D 1 m₁ := by
  unfold BcFeedbackCode.errorProb
  have hout : ∀ z, ((singleUserCode h₁ D).output h₁ h₂ m₁ m₂ z).1 = D.encoder m₁ + z.1 := by
    intro z
    rw [output_eq_of_open_loop _ m₁ m₂ z (fun y => rfl)]
    funext i
    simp only [BcFeedbackCode.step, singleUserCode, Pi.add_apply]
    rw [mul_div_cancel₀ _ hh]
  have hset : {z : BcBlock n | (singleUserCode h₁ D).dec₁
        ((singleUserCode h₁ D).output h₁ h₂ m₁ m₂ z).1 ≠ m₁ ∨
      (singleUserCode h₁ D).dec₂ ((singleUserCode h₁ D).output h₁ h₂ m₁ m₂ z).2 ≠ m₂} =
      {w : Fin n → ℝ | D.decoder (D.encoder m₁ + w) ≠ m₁} ×ˢ Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, hout]
    have : ¬ ((singleUserCode h₁ D).dec₂ ((singleUserCode h₁ D).output h₁ h₂ m₁ m₂ z).2 ≠ m₂) :=
      not_not.mpr (Subsingleton.elim _ _)
    simp only [this, or_false]
    rfl
  rw [hset, BcFeedbackCode.noise, Measure.prod_prod, measure_univ, mul_one]
  rfl

theorem singleUserCode_avgErrorProb (hh : h₁ ≠ 0) {n M : ℕ} (D : AwgnCode n M) :
    (singleUserCode h₁ D).avgErrorProb h₁ h₂ = awgnAvgErrorProb D 1 := by
  unfold BcFeedbackCode.avgErrorProb awgnAvgErrorProb
  simp only [singleUserCode_errorProb hh, Finset.univ_unique, Finset.sum_singleton, mul_one]

theorem singleUserCode_satisfiesPower (hh : h₁ ≠ 0) {n M : ℕ} (hM : 1 ≤ M) (D : AwgnCode n M)
    (hD : D.SatisfiesPower (h₁ ^ 2 * P)) : (singleUserCode h₁ D).SatisfiesPower h₁ h₂ P := by
  have := noise_isProb n
  unfold BcFeedbackCode.SatisfiesPower BcFeedbackCode.expectedEnergy
  have hpt : ∀ m₁ : Fin M, ∀ m₂ : Fin 1, (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
      ((singleUserCode h₁ D).input h₁ h₂ m₁ m₂ z i) ^ 2) ∂BcFeedbackCode.noise n) ≤
      ENNReal.ofReal ((n : ℝ) * P) := by
    intro m₁ m₂
    have hconst : ∀ z, ∑ i : Fin n, ((singleUserCode h₁ D).input h₁ h₂ m₁ m₂ z i) ^ 2 =
        (∑ i : Fin n, (D.encoder m₁ i) ^ 2) / h₁ ^ 2 := by
      intro z
      simp only [BcFeedbackCode.input, singleUserCode, div_pow, Finset.sum_div]
    simp only [hconst, lintegral_const, measure_univ, mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hh2 : 0 < h₁ ^ 2 := by positivity
    rw [div_le_iff₀ hh2]
    have := hD m₁
    nlinarith
  have hsum : ∑ m₁ : Fin M, ∑ m₂ : Fin 1, (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
      ((singleUserCode h₁ D).input h₁ h₂ m₁ m₂ z i) ^ 2) ∂BcFeedbackCode.noise n) ≤
      ((M * 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * P) := by
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_one]
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin M)) _ _
      (fun m₁ _ => hpt m₁ default)
    simpa [nsmul_eq_mul] using this
  have hM0 : ((M * 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [mul_one, ne_eq, Nat.cast_eq_zero]; omega
  calc ((M * 1 : ℕ) : ℝ≥0∞)⁻¹ * _ ≤ ((M * 1 : ℕ) : ℝ≥0∞)⁻¹ *
        (((M * 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * P)) := by gcongr
    _ = ENNReal.ofReal ((n : ℝ) * P) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hM0 (ENNReal.natCast_ne_top _), one_mul]

/-- **Single-user rates are achievable** (no feedback needed): every `0 ≤ R < ½ log₂(1 + h₁²P)`
    is achievable for receiver 1 with `R₂ = 0`. -/
theorem isBcFbAchievable_single (hh : h₁ ≠ 0) (hP : 0 ≤ P) (hR0 : 0 ≤ R)
    (hR : R < awgnCapacityFormula (h₁ ^ 2 * P) 1) : IsBcFbAchievable h₁ h₂ P R 0 := by
  have hach := Known.GaussianAchievability.isAwgnAchievable_of_lt_capacity
    (N := 1) (P := h₁ ^ 2 * P) one_pos (by positivity) hR0 hR
  refine ⟨hR0, le_rfl, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hach.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨D, hpow, herr⟩ := hn₀ n hn
  have hM : max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * 0)⌋₊ = 1 := by simp
  rw [hM]
  refine ⟨singleUserCode h₁ D, singleUserCode_satisfiesPower hh (le_max_left _ _) D hpow, ?_⟩
  rw [singleUserCode_avgErrorProb hh]
  exact herr

/-- `ofReal(½ log₂(1 + h₁²P)) ≤ bcFbSumCapacity h₁ h₂ P`. -/
theorem single_le_bcFbSumCapacity (hh : h₁ ≠ 0) (hP : 0 ≤ P) :
    ENNReal.ofReal (awgnCapacityFormula (h₁ ^ 2 * P) 1) ≤ bcFbSumCapacity h₁ h₂ P := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  have hrtop : r ≠ ⊤ := ne_top_of_lt hr
  have hlt : r.toReal < awgnCapacityFormula (h₁ ^ 2 * P) 1 :=
    ENNReal.toReal_lt_of_lt_ofReal hr
  have hach := isBcFbAchievable_single (h₂ := h₂) hh hP ENNReal.toReal_nonneg hlt
  refine le_sSup ⟨r.toReal, 0, hach, ?_⟩
  rw [add_zero, ENNReal.ofReal_toReal hrtop]

end Operational

/-! ### Formula side: the linear-feedback sum-rate is a genuine supremum -/

section Formula

variable {h₁ h₂ P : ℝ}

lemma log2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos one_lt_two).le

lemma log2_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  div_nonneg (Real.log_nonneg hx) (Real.log_pos one_lt_two).le

theorem single_mem_linearFbRegion (hP : 0 ≤ P) :
    InLinearFbRegion h₁ h₂ P ((1 / 2 : ℝ) * log2 (1 + h₁ ^ 2 * P)) 0 := by
  have h1 : 0 ≤ (1 / 2 : ℝ) * log2 (1 + h₁ ^ 2 * P) :=
    mul_nonneg (by norm_num) (log2_nonneg_of_one_le (by nlinarith [sq_nonneg h₁]))
  refine ⟨h1, le_rfl, P, 0, 0, hP, le_rfl, by ring, le_rfl, zero_le_one, ?_, ?_, ?_⟩
  · simp
  · simp [log2]
  · simp

theorem zero_mem_linearFbRegion (hP : 0 ≤ P) : InLinearFbRegion h₁ h₂ P 0 0 := by
  obtain ⟨h1, -, P₁, P₂, ρ, hP₁, hP₂, hsum, hρ0, hρ1, hr1, hr2, hr12⟩ :=
    single_mem_linearFbRegion (h₁ := h₁) (h₂ := h₂) hP
  refine ⟨le_rfl, le_rfl, P₁, P₂, ρ, hP₁, hP₂, hsum, hρ0, hρ1, le_trans h1 hr1, ?_, ?_⟩
  · exact le_trans le_rfl hr2
  · linarith

/-- Every pair in the linear-feedback region has `R₁ + R₂ ≤ ½ log₂(1 + (|h₁| + |h₂|)² P)`. -/
theorem linearFbRegion_sum_le {R₁ R₂ : ℝ} (h : InLinearFbRegion h₁ h₂ P R₁ R₂) :
    R₁ + R₂ ≤ (1 / 2 : ℝ) * log2 (1 + (|h₁| + |h₂|) ^ 2 * P) := by
  obtain ⟨-, -, P₁, P₂, ρ, hP₁, hP₂, hsum, hρ0, hρ1, -, -, hr12⟩ := h
  refine le_trans hr12 (mul_le_mul_of_nonneg_left (log2_mono ?_ ?_) (by norm_num))
  · have : 0 ≤ 2 * |h₁ * h₂| * Real.sqrt (P₁ * P₂) * ρ := by positivity
    nlinarith [sq_nonneg h₁, sq_nonneg h₂]
  · have hsq : Real.sqrt (P₁ * P₂) ≤ (P₁ + P₂) / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg (P₁ - P₂)]
    have habs : |h₁ * h₂| = |h₁| * |h₂| := abs_mul _ _
    have hs0 : 0 ≤ Real.sqrt (P₁ * P₂) := Real.sqrt_nonneg _
    have hq : 2 * |h₁ * h₂| * Real.sqrt (P₁ * P₂) * ρ ≤ |h₁| * |h₂| * (P₁ + P₂) := by
      rw [habs]
      have h12 : 0 ≤ |h₁| * |h₂| := by positivity
      calc 2 * (|h₁| * |h₂|) * Real.sqrt (P₁ * P₂) * ρ
          ≤ 2 * (|h₁| * |h₂|) * Real.sqrt (P₁ * P₂) * 1 := by gcongr
        _ ≤ 2 * (|h₁| * |h₂|) * ((P₁ + P₂) / 2) := by nlinarith
        _ = |h₁| * |h₂| * (P₁ + P₂) := by ring
    have e1 : h₁ ^ 2 = |h₁| ^ 2 := (sq_abs h₁).symm
    have e2 : h₂ ^ 2 = |h₂| ^ 2 := (sq_abs h₂).symm
    rw [e1, e2, ← hsum]
    nlinarith [abs_nonneg h₁, abs_nonneg h₂, mul_nonneg (abs_nonneg h₁) (abs_nonneg h₂)]

theorem linearFbSum_nonempty (hP : 0 ≤ P) :
    { s : ℝ | ∃ R₁ R₂ : ℝ, InLinearFbRegion h₁ h₂ P R₁ R₂ ∧ s = R₁ + R₂ }.Nonempty :=
  ⟨0, 0, 0, zero_mem_linearFbRegion hP, by ring⟩

theorem linearFbSum_bddAbove :
    BddAbove { s : ℝ | ∃ R₁ R₂ : ℝ, InLinearFbRegion h₁ h₂ P R₁ R₂ ∧ s = R₁ + R₂ } :=
  ⟨_, fun _ ⟨_, _, h, hs⟩ => hs ▸ linearFbRegion_sum_le h⟩

theorem single_le_linearFbSumRate (hP : 0 ≤ P) :
    (1 / 2 : ℝ) * log2 (1 + h₁ ^ 2 * P) ≤ linearFbSumRate h₁ h₂ P :=
  le_csSup linearFbSum_bddAbove ⟨_, 0, single_mem_linearFbRegion hP, by ring⟩

theorem linearFbSumRate_le (hP : 0 ≤ P) :
    linearFbSumRate h₁ h₂ P ≤ (1 / 2 : ℝ) * log2 (1 + (|h₁| + |h₂|) ^ 2 * P) :=
  csSup_le (linearFbSum_nonempty hP) (fun _ ⟨_, _, h, hs⟩ => hs ▸ linearFbRegion_sum_le h)

end Formula

/-- In the symmetric case, both sides of the frozen equation are at least the no-feedback
    single-user rate `½ log₂(1 + h²P)`, and the formula side is at most
    `½ log₂(1 + 4h²P)`. -/
theorem both_sides_ge_single {h P : ℝ} (hh : h ≠ 0) (hP : 0 < P) :
    ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 + h ^ 2 * P)) ≤ bcFbSumCapacity h h P ∧
      (1 / 2 : ℝ) * log2 (1 + h ^ 2 * P) ≤ linearFbSumRate h h P ∧
      linearFbSumRate h h P ≤ (1 / 2 : ℝ) * log2 (1 + (|h| + |h|) ^ 2 * P) := by
  refine ⟨?_, single_le_linearFbSumRate hP.le, linearFbSumRate_le hP.le⟩
  have := single_le_bcFbSumCapacity (h₂ := h) hh hP.le
  simpa [awgnCapacityFormula] using this

end InfoTheory.Known.Certificates.GaussianBcFeedbackSumCapacity
