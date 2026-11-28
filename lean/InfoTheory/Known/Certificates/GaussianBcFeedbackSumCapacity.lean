import InfoTheory.Problems.GaussianBcFeedbackSumCapacity
import InfoTheory.Known.GaussianAchievability
import InfoTheory.Bridge.GaussianConverse

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
* **Regressions against the no-feedback symmetric BC (both pass).**
  `noFeedback_triangle_subset` : the whole no-feedback capacity region of the symmetric BC, the
  time-sharing triangle `R₁ + R₂ ≤ ½ log₂(1 + h²P)`, lies in `InLinearFbRegion h h P` (feedback
  cannot hurt; `ρ = 0`).  `single_lt_linearFbSumRate` : for `h ≠ 0`, `P > 0`,
  `½ log₂(1 + h²P) < linearFbSumRate h h P` strictly — feedback strictly enlarges the symmetric
  Gaussian BC sum-rate, as Ozarow–Leung (1984) showed.  A mis-transcribed `ρ`-term (e.g. a sign
  error or a missing `√(P₁P₂)`) would break the second check.
* **Operational upper bound (feedback converse).**  `sum_le_of_isBcFbAchievable` : every
  achievable pair has `R₁ + R₂ ≤ ½ log₂(1 + (h₁² + h₂²)P)` (cooperating-receivers / SIMO cut-set
  bound), obtained by feeding the frozen `BcFeedbackCode`, `noise`, `SatisfiesPower` and
  `avgErrorProb` verbatim into `Bridge.gaussian_bc_feedback_sum_rate_converse` with `N = 1`
  (the frozen `output` is definitionally `Bridge.causalOutput2` of the drifts `h_k · enc`; same
  expected-energy constraint and average error criterion).  Hence `bcFbSumCapacity_le`,
  `bcFbSumCapacity_lt_top` (finite, not `⊤`) and, symmetrically,
  `bcFbSumCapacity_symm_le` : `bcFbSumCapacity h h P ≤ ofReal(½ log₂(1 + 2h²P))`.
* **Consistency check (passes).**  `linearFbSumRate_le_cutset` :
  `linearFbSumRate h h P ≤ ½ log₂(1 + 2h²P)`, i.e. the formula side of `Statement` does not
  exceed the certified operational upper bound (otherwise `Statement` would be trivially false).

## Not certified
* Upper bounds sharper than the cut-set bound (e.g. dependence-balance bounds).
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

/-! ### Regressions against the no-feedback symmetric BC -/

section Regression

variable {h P : ℝ}

/-- **Regression (feedback cannot hurt, whole region).**  For the symmetric BC the
    no-feedback capacity region is the time-sharing triangle
    `{R₁, R₂ ≥ 0, R₁ + R₂ ≤ ½ log₂(1 + h²P)}` (Cover 1972; Bergmans 1973 with equal gains);
    it lies inside the frozen linear-feedback region (take `ρ = 0` and the power split
    `h²P₁ = 2^{2R₁} - 1`). -/
theorem noFeedback_triangle_subset (hh : h ≠ 0) (hP : 0 ≤ P) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁)
    (hR₂ : 0 ≤ R₂) (hsum : R₁ + R₂ ≤ (1 / 2 : ℝ) * log2 (1 + h ^ 2 * P)) :
    InLinearFbRegion h h P R₁ R₂ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hh2 : 0 < h ^ 2 := by positivity
  have hx : 0 < 1 + h ^ 2 * P := by nlinarith
  set a := Real.exp (2 * R₁ * Real.log 2) with ha
  set b := Real.exp (2 * R₂ * Real.log 2) with hb
  have ha1 : 1 ≤ a := Real.one_le_exp (by positivity)
  have hb1 : 1 ≤ b := Real.one_le_exp (by positivity)
  have hab : a * b ≤ 1 + h ^ 2 * P := by
    rw [ha, hb, ← Real.exp_add]
    calc Real.exp (2 * R₁ * Real.log 2 + 2 * R₂ * Real.log 2)
        ≤ Real.exp (Real.log (1 + h ^ 2 * P)) := by
          apply Real.exp_le_exp.mpr
          have : (R₁ + R₂) * Real.log 2 ≤ (1 / 2 : ℝ) * Real.log (1 + h ^ 2 * P) := by
            have h' := mul_le_mul_of_nonneg_right hsum hl2.le
            unfold log2 at h'
            rw [show (1 / 2 : ℝ) * (Real.log (1 + h ^ 2 * P) / Real.log 2) * Real.log 2 =
              (1 / 2 : ℝ) * Real.log (1 + h ^ 2 * P) by field_simp] at h'
            exact h'
          linarith
      _ = 1 + h ^ 2 * P := Real.exp_log hx
  have hlog_a : (1 / 2 : ℝ) * log2 a = R₁ := by
    unfold log2; rw [ha, Real.log_exp]; field_simp
  have hlog_b : (1 / 2 : ℝ) * log2 b = R₂ := by
    unfold log2; rw [hb, Real.log_exp]; field_simp
  set P₁ := (a - 1) / h ^ 2 with hP₁
  have hP₁h : h ^ 2 * P₁ = a - 1 := by rw [hP₁]; field_simp
  have hP₁0 : 0 ≤ P₁ := div_nonneg (by linarith) hh2.le
  have hkey : a + b - 1 ≤ a * b := by nlinarith
  refine ⟨hR₁, hR₂, P₁, P - P₁, 0, hP₁0, ?_, by ring, le_rfl, zero_le_one, ?_, ?_, ?_⟩
  · have : h ^ 2 * P₁ ≤ h ^ 2 * P := by rw [hP₁h]; nlinarith
    have := le_of_mul_le_mul_left this hh2
    linarith
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, mul_one]
    rw [hP₁h, show 1 + (a - 1) = a by ring, hlog_a]
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, mul_one]
    rw [← hlog_b]
    refine mul_le_mul_of_nonneg_left (log2_mono (by linarith) ?_) (by norm_num)
    have : h ^ 2 * (P - P₁) = h ^ 2 * P - (a - 1) := by rw [mul_sub, hP₁h]
    rw [this]
    linarith
  · simp only [mul_zero, add_zero]
    have : h ^ 2 * P₁ + h ^ 2 * (P - P₁) = h ^ 2 * P := by ring
    rw [add_assoc, this]
    exact hsum

/-- **Regression (feedback strictly helps; Ozarow–Leung 1984).**  For `h ≠ 0`, `P > 0` the
    linear-feedback sum-rate strictly exceeds the no-feedback symmetric sum capacity
    `½ log₂(1 + h²P)`.  Witness: `P₁ = P₂ = P/2`, `ρ = x / (2(x + 4))` with `x = h²P`, and
    `R₁ = R₂ = min(½ log₂(1 + (x/2)(1 - ρ²)), ¼ log₂(1 + x + xρ))`. -/
theorem single_lt_linearFbSumRate (hh : h ≠ 0) (hP : 0 < P) :
    (1 / 2 : ℝ) * log2 (1 + h ^ 2 * P) < linearFbSumRate h h P := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set x := h ^ 2 * P with hxdef
  have hx : 0 < x := by positivity
  set ρ := x / (2 * (x + 4)) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 / 2 := by
    rw [hρ, div_le_iff₀ (by positivity)]; linarith
  have hρpos : 0 < ρ := by positivity
  set y := x / 2 * (1 - ρ ^ 2) with hy
  have hy0 : 0 ≤ y := by
    have : ρ ^ 2 ≤ 1 := by nlinarith
    rw [hy]; exact mul_nonneg (by positivity) (by linarith)
  -- `(1 + y)² > 1 + x`
  have hsq : 1 + x < (1 + y) ^ 2 := by
    have hρsq : 4 * (x + 4) ^ 2 * ρ ^ 2 = x ^ 2 := by
      rw [hρ]; field_simp; ring
    have h16 : 16 * x ≤ (x + 4) ^ 2 := by nlinarith [sq_nonneg (x - 4)]
    have hρ2 : ρ ^ 2 ≤ 1 / 4 := by nlinarith
    -- `(1 + y)² - (1 + x) = y² - x ρ² = x² (1 - ρ²)² / 4 - x ρ²`
    have hexp : (1 + y) ^ 2 - (1 + x) = x ^ 2 * (1 - ρ ^ 2) ^ 2 / 4 - x * ρ ^ 2 := by
      rw [hy]; ring
    have hA : x * ρ ^ 2 * (16 * (x + 4) ^ 2) = 4 * x ^ 3 := by nlinarith
    have hB : 9 / 16 ≤ (1 - ρ ^ 2) ^ 2 := by nlinarith
    -- `x ρ² = x³ / (4 (x+4)²) ≤ x² / 64 < 9 x² / 64 ≤ x² (1 - ρ²)² / 4`
    have hC : x * ρ ^ 2 ≤ x ^ 2 / 64 := by
      have hpos : 0 < 16 * (x + 4) ^ 2 := by positivity
      have : x * ρ ^ 2 = 4 * x ^ 3 / (16 * (x + 4) ^ 2) := by
        rw [eq_div_iff hpos.ne']; linarith
      rw [this, div_le_div_iff₀ hpos (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left h16 (by positivity : (0 : ℝ) ≤ 4 * x ^ 2)]
    have hD : x ^ 2 / 64 < x ^ 2 * (1 - ρ ^ 2) ^ 2 / 4 := by
      have : 0 < x ^ 2 := by positivity
      nlinarith
    linarith
  set r := min ((1 / 2 : ℝ) * log2 (1 + y)) ((1 / 4 : ℝ) * log2 (1 + x + x * ρ)) with hr
  have hc1 : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * log2 (1 + x)) < (1 / 2 : ℝ) * log2 (1 + y) := by
    unfold log2
    have := Real.log_lt_log (by linarith) hsq
    rw [Real.log_pow] at this
    have : Real.log (1 + x) / Real.log 2 < 2 * Real.log (1 + y) / Real.log 2 := by
      gcongr; exact_mod_cast this
    rw [mul_div_assoc] at this
    linarith
  have hc2 : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * log2 (1 + x)) < (1 / 4 : ℝ) * log2 (1 + x + x * ρ) := by
    unfold log2
    have := Real.log_lt_log (by linarith) (show 1 + x < 1 + x + x * ρ by nlinarith)
    have : Real.log (1 + x) / Real.log 2 < Real.log (1 + x + x * ρ) / Real.log 2 := by gcongr
    nlinarith
  have hrlow : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * log2 (1 + x)) < r := lt_min hc1 hc2
  have hr0 : 0 ≤ r := by
    have : 0 ≤ (1 / 2 : ℝ) * log2 (1 + x) :=
      mul_nonneg (by norm_num) (log2_nonneg_of_one_le (by linarith))
    linarith
  have hmem : InLinearFbRegion h h P r r := by
    refine ⟨hr0, hr0, P / 2, P / 2, ρ, by positivity, by positivity, by ring, hρ0,
      by linarith, ?_, ?_, ?_⟩
    · have : h ^ 2 * (P / 2) * (1 - ρ ^ 2) = y := by rw [hy, hxdef]; ring
      rw [this]; exact min_le_left _ _
    · have : h ^ 2 * (P / 2) * (1 - ρ ^ 2) = y := by rw [hy, hxdef]; ring
      rw [this]; exact min_le_left _ _
    · have hsqrt : Real.sqrt (P / 2 * (P / 2)) = P / 2 := Real.sqrt_mul_self (by positivity)
      have habs : |h * h| = h ^ 2 := by rw [abs_mul_self, sq]
      rw [hsqrt, habs]
      have : 1 + h ^ 2 * (P / 2) + h ^ 2 * (P / 2) + 2 * h ^ 2 * (P / 2) * ρ = 1 + x + x * ρ := by
        rw [hxdef]; ring
      rw [this]
      have := min_le_right ((1 / 2 : ℝ) * log2 (1 + y)) ((1 / 4 : ℝ) * log2 (1 + x + x * ρ))
      rw [← hr] at this
      linarith
  have hle : r + r ≤ linearFbSumRate h h P :=
    le_csSup linearFbSum_bddAbove ⟨r, r, hmem, rfl⟩
  linarith

end Regression

/-! ### Operational upper bound: the SIMO cut-set feedback converse -/

section Converse

variable {h₁ h₂ P R₁ R₂ : ℝ}

/-- **Feedback converse on the exact frozen objects**: every achievable pair satisfies
    `R₁ + R₂ ≤ ½ log₂(1 + (h₁² + h₂²) P)` (the cooperative-receivers / SIMO cut-set bound).
    The frozen `BcFeedbackCode` (its `output` is definitionally `Bridge.causalOutput2` of the
    drifts `h_k · enc`), `noise n = N(0,1)^{⊗n} ⊗ N(0,1)^{⊗n}`, `SatisfiesPower` and
    `avgErrorProb` are fed verbatim into `Bridge.gaussian_bc_feedback_sum_rate_converse`
    (with `N = 1`). -/
theorem sum_le_of_isBcFbAchievable (hP : 0 ≤ P) (h : IsBcFbAchievable h₁ h₂ P R₁ R₂) :
    R₁ + R₂ ≤ (1 / 2 : ℝ) * log2 (1 + (h₁ ^ 2 + h₂ ^ 2) * P) := by
  obtain ⟨_, _, hach⟩ := h
  have key := InfoTheory.Bridge.gaussian_bc_feedback_sum_rate_converse (h₁ := h₁) (h₂ := h₂)
    (R₁ := R₁) (R₂ := R₂) one_pos hP (fun δ hδ => ?_)
  · simpa only [div_one] using key
  · obtain ⟨n₀, hn₀⟩ := hach δ hδ
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨C, hpow, herr⟩ := hn₀ n hn
    exact ⟨C.enc, C.dec₁, C.dec₂, C.causal, C.measurable_enc, C.measurable_dec₁,
      C.measurable_dec₂, hpow, herr⟩

/-- **Operational upper bound**: `bcFbSumCapacity h₁ h₂ P ≤ ofReal(½ log₂(1 + (h₁² + h₂²) P))`. -/
theorem bcFbSumCapacity_le (hP : 0 ≤ P) :
    bcFbSumCapacity h₁ h₂ P ≤ ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 + (h₁ ^ 2 + h₂ ^ 2) * P)) :=
  sSup_le fun _ ⟨_, _, h, hr⟩ => hr ▸ ENNReal.ofReal_le_ofReal (sum_le_of_isBcFbAchievable hP h)

/-- The feedback sum-capacity is finite (not the junk value `⊤`). -/
theorem bcFbSumCapacity_lt_top (hP : 0 ≤ P) : bcFbSumCapacity h₁ h₂ P < ⊤ :=
  lt_of_le_of_lt (bcFbSumCapacity_le hP) ENNReal.ofReal_lt_top

/-- Symmetric case: `bcFbSumCapacity h h P ≤ ofReal(½ log₂(1 + 2h²P))`. -/
theorem bcFbSumCapacity_symm_le {h : ℝ} (hP : 0 ≤ P) :
    bcFbSumCapacity h h P ≤ ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 + 2 * h ^ 2 * P)) := by
  have := bcFbSumCapacity_le (h₁ := h) (h₂ := h) hP
  rwa [show (h ^ 2 + h ^ 2) * P = 2 * h ^ 2 * P by ring] at this

/-- **Consistency of the formula side with the converse** (necessary for `Statement` to be
    satisfiable at all): `linearFbSumRate h h P ≤ ½ log₂(1 + 2h²P)`, since
    `2|h·h|√(P₁P₂)ρ ≤ h²(P₁ + P₂)` for `ρ ∈ [0, 1]`. -/
theorem linearFbSumRate_le_cutset {h : ℝ} (hP : 0 ≤ P) :
    linearFbSumRate h h P ≤ (1 / 2 : ℝ) * log2 (1 + 2 * h ^ 2 * P) := by
  refine csSup_le (linearFbSum_nonempty hP) fun s ⟨R₁, R₂, hR, hs⟩ => ?_
  obtain ⟨_, _, P₁, P₂, ρ, hP₁, hP₂, hsum, hρ0, hρ1, _, _, hR12⟩ := hR
  rw [hs]
  refine le_trans hR12 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have habs : |h * h| = h ^ 2 := by rw [abs_mul_self, sq]
  set q := Real.sqrt (P₁ * P₂) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = P₁ * P₂ := Real.sq_sqrt (mul_nonneg hP₁ hP₂)
  have h2q : 2 * q ≤ P₁ + P₂ := by nlinarith [sq_nonneg (P₁ - P₂)]
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  have hterm0 : 0 ≤ 2 * |h * h| * q * ρ := by positivity
  have hterm : 2 * |h * h| * q * ρ ≤ h ^ 2 * (P₁ + P₂) := by
    rw [habs]
    have : q * ρ ≤ q := mul_le_of_le_one_right hq0 hρ1
    nlinarith
  apply log2_mono
  · nlinarith
  · rw [← hsum]; nlinarith

end Converse

end InfoTheory.Known.Certificates.GaussianBcFeedbackSumCapacity
