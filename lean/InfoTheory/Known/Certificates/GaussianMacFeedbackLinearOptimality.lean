import InfoTheory.Problems.GaussianMacFeedbackLinearOptimality
import InfoTheory.Known.GaussianAchievability

/-!
# Certificate for `InfoTheory.Problems.GaussianMacFeedbackLinearOptimality`

The frozen statement asks whether, for the symmetric `K`-user Gaussian MAC with feedback
(`K ≥ 3`, equal expected powers `P`, noise variance `N > 0`), the closure of the operational
feedback capacity region `macFbRegion K P N` equals the closure of the region
`macLinearFbRegion K P N` achievable by linear-feedback codes (Ardestanizadeh–Wigger–Kim–Javidi
2012, Def. 1).

## Certified (about exactly these objects)
* **The feedback recursion is well posed.**  `output_fixed` (the received block solves the causal
  channel equation `yᵢ = ∑_j x_{j,i}(m_j, y^{i-1}) + zᵢ`), `eq_output_of_fixed` (uniquely),
  `measurable_output` (measurable in the noise, so the energy `lintegral` is a genuine
  expectation).
* **Easy inclusion.**  `macLinearFbRegion_subset` and `closure_linear_subset`: linear-feedback
  codes are feedback codes.  Only the reverse inclusion is open.
* **Non-vacuity.**  `zero_mem_macLinearFbRegion` / `zero_mem_macFbRegion`; and
  `single_mem_macLinearFbRegion`: for each sender `j₀`, every rate vector `R · e_{j₀}` with
  `0 ≤ R < ½ log₂(1 + P/N)` is achievable by a (feedback-free, hence linear) code, using the
  operational AWGN coding theorem
  `Known.GaussianAchievability.isAwgnAchievable_of_lt_capacity`.  Hence both closures contain
  the single-user corner segments `[0, ½ log₂(1 + P/N)] · e_{j₀}`
  (`single_mem_closure_macLinearFbRegion`).

## Not certified
* Boundedness of `macFbRegion` (e.g. the total-cooperation bound
  `∑_j R_j ≤ ½ log₂(1 + K²P/N)`): this needs a converse for codes with feedback (a change of
  measure through the causal output map), which the current `Known` library does not provide.
* Achievability of Kramer's Fourier-MEC rates and the Sula–Gastpar–Kramer sum-capacity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace InfoTheory.Known.Certificates.GaussianMacFeedbackLinearOptimality

open InfoTheory InfoTheory.Problems.GaussianMacFeedbackLinearOptimality

/-! ### The causal recursion -/

section Recursion

variable {K n : ℕ} {M : Fin K → ℕ} (C : MacFeedbackCode K n M) (m : (j : Fin K) → Fin (M j))
  (z : Fin n → ℝ)

theorem step_apply (y : Fin n → ℝ) (t : Fin n) :
    C.step m z y t = (∑ j : Fin K, C.enc j t (m j) y) + z t := rfl

theorem iterate_stable (k : ℕ) : ∀ t : Fin n, t.val < k →
    ((C.step m z)^[k + 1] z) t = ((C.step m z)^[k] z) t := by
  induction k with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ k ih =>
    intro t ht
    have henc : ∀ j, C.enc j t (m j) ((C.step m z)^[k + 1] z) =
        C.enc j t (m j) ((C.step m z)^[k] z) := fun j =>
      C.causal j t (m j) _ _ (fun s hs =>
        ih s (lt_of_lt_of_le (Fin.lt_def.mp hs) (Nat.lt_succ_iff.mp ht)))
    rw [Function.iterate_succ_apply' _ (k + 1), step_apply]
    simp only [henc]
    rw [Function.iterate_succ_apply' _ k, step_apply]

/-- **The output solves the causal channel equation** `yᵢ = ∑_j enc j i m_j y + zᵢ`. -/
theorem output_fixed : C.step m z (C.output m z) = C.output m z := by
  have hs := iterate_stable C m z n
  unfold MacFeedbackCode.output
  rw [← Function.iterate_succ_apply' (C.step m z) n]
  exact funext fun t => hs t t.2

/-- **Uniqueness**: any solution of the causal channel equation is `output`. -/
theorem eq_output_of_fixed (y : Fin n → ℝ) (hy : C.step m z y = y) : y = C.output m z := by
  have key : ∀ k : ℕ, ∀ t : Fin n, t.val < k → ((C.step m z)^[k] z) t = y t := by
    intro k
    induction k with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
    | succ k ih =>
      intro t ht
      have henc : ∀ j, C.enc j t (m j) ((C.step m z)^[k] z) = C.enc j t (m j) y := fun j =>
        C.causal j t (m j) _ _ (fun s hs =>
          ih s (lt_of_lt_of_le (Fin.lt_def.mp hs) (Nat.lt_succ_iff.mp ht)))
      rw [Function.iterate_succ_apply', step_apply]
      simp only [henc]
      conv_rhs => rw [← hy, step_apply]
  unfold MacFeedbackCode.output
  exact (funext fun t => key n t t.2).symm

/-- The received block depends measurably on the noise. -/
theorem measurable_output : Measurable (C.output m) := by
  have hstep : ∀ g : (Fin n → ℝ) → (Fin n → ℝ), Measurable g →
      Measurable (fun w => C.step m w (g w)) := by
    intro g hg
    exact measurable_pi_iff.mpr fun i =>
      (Finset.measurable_sum _ fun j _ => (C.measurable_enc j i (m j)).comp hg).add
        (measurable_pi_apply i)
  have hk : ∀ k : ℕ, Measurable (fun w => (C.step m w)^[k] w) := by
    intro k
    induction k with
    | zero => exact measurable_id
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      exact hstep _ ih
  exact hk n

end Recursion

/-! ### Inclusions and achievable points -/

section Regions

variable {K : ℕ} {P N : ℝ}

/-- Linear-feedback codes are feedback codes. -/
theorem macLinearFbRegion_subset : macLinearFbRegion K P N ⊆ macFbRegion K P N := by
  intro R ⟨h0, h⟩
  refine ⟨h0, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  exact ⟨n₀, fun n hn => by
    obtain ⟨C, -, hpow, herr⟩ := hn₀ n hn
    exact ⟨C, fun h => absurd h (by decide), hpow, herr⟩⟩

theorem closure_linear_subset :
    closure (macLinearFbRegion K P N) ⊆ closure (macFbRegion K P N) :=
  closure_mono macLinearFbRegion_subset

lemma subsingleton_fin_of_eq_one {k : ℕ} (hk : k = 1) : Subsingleton (Fin k) := by
  subst hk; infer_instance

/-- The feedback-free `K`-user code in which only sender `j₀` transmits, using the AWGN code
    `D`; all other senders have a single message and send `0`. -/
noncomputable def singleUserCode {n M₀ : ℕ} (D : AwgnCode n M₀) (j₀ : Fin K) (M : Fin K → ℕ)
    (hM0 : M j₀ = M₀) (hpos : ∀ j, 1 ≤ M j) : MacFeedbackCode K n M where
  enc j i m _ := if h : j = j₀ then D.encoder (Fin.cast ((congrArg M h).trans hM0) m) i else 0
  causal := fun _ _ _ _ _ _ => rfl
  measurable_enc := fun _ _ _ => measurable_const
  dec j y := if h : j = j₀ then Fin.cast ((congrArg M h).trans hM0).symm (D.decoder y)
    else ⟨0, hpos j⟩
  measurable_dec j := by
    by_cases h : j = j₀
    · simp only [h, dite_true]
      exact (measurable_from_top (f := Fin.cast _)).comp D.measurable_decoder
    · simp only [h, dite_false]
      exact measurable_const

section SingleUser

variable {n M₀ : ℕ} (D : AwgnCode n M₀) (j₀ : Fin K) (M : Fin K → ℕ) (hM0 : M j₀ = M₀)
  (hpos : ∀ j, 1 ≤ M j)

theorem singleUserCode_output (m : (j : Fin K) → Fin (M j)) (z : Fin n → ℝ) :
    (singleUserCode D j₀ M hM0 hpos).output m z = D.encoder (Fin.cast hM0 (m j₀)) + z := by
  unfold MacFeedbackCode.output
  have hstep : ∀ y, (singleUserCode D j₀ M hM0 hpos).step m z y =
      D.encoder (Fin.cast hM0 (m j₀)) + z := by
    intro y
    funext i
    simp only [MacFeedbackCode.step, singleUserCode, Pi.add_apply]
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by simp [hj]) (fun h => absurd
      (Finset.mem_univ _) h)]
    simp
  cases n with
  | zero => exact funext fun t => Fin.elim0 t
  | succ k => rw [Function.iterate_succ_apply']; exact hstep _

theorem singleUserCode_isLinear : (singleUserCode D j₀ M hM0 hpos).IsLinear := by
  refine ⟨fun j m i => if h : j = j₀ then D.encoder (Fin.cast ((congrArg M h).trans hM0) m) i
    else 0, fun _ _ _ => 0, fun _ _ _ _ => rfl, fun j i m y => ?_⟩
  simp [singleUserCode]

theorem singleUserCode_errorProb (hM1 : ∀ j, j ≠ j₀ → M j = 1) (N : ℝ)
    (m : (j : Fin K) → Fin (M j)) :
    (singleUserCode D j₀ M hM0 hpos).errorProb N m = awgnErrorProb D N (Fin.cast hM0 (m j₀)) := by
  unfold MacFeedbackCode.errorProb awgnErrorProb
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, singleUserCode_output]
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : j = j₀
    · subst h
      simp only [singleUserCode, dite_true] at hj
      intro heq
      apply hj
      rw [heq]
      ext
      simp
    · have := subsingleton_fin_of_eq_one (hM1 j h)
      exact absurd (Subsingleton.elim _ _) hj
  · intro hne
    refine ⟨j₀, ?_⟩
    simp only [singleUserCode, dite_true]
    intro heq
    apply hne
    apply Fin.ext
    have := congrArg Fin.val heq
    simpa using this

theorem singleUserCode_avgErrorProb (hM1 : ∀ j, j ≠ j₀ → M j = 1) (N : ℝ) :
    (singleUserCode D j₀ M hM0 hpos).avgErrorProb N = awgnAvgErrorProb D N := by
  unfold MacFeedbackCode.avgErrorProb awgnAvgErrorProb
  have hprod : (∏ j, M j : ℕ) = M₀ := by
    rw [Finset.prod_eq_single j₀ (fun j _ hj => hM1 j hj) (fun h => absurd
      (Finset.mem_univ _) h), hM0]
  rw [hprod]
  congr 1
  simp only [singleUserCode_errorProb D j₀ M hM0 hpos hM1]
  have hbij : Function.Bijective (fun m : (j : Fin K) → Fin (M j) => Fin.cast hM0 (m j₀)) := by
    refine ⟨?_, ?_⟩
    · intro m m' hmm
      funext j
      by_cases h : j = j₀
      · subst h
        have := congrArg Fin.val hmm
        simp only [Fin.val_cast] at this
        exact Fin.ext this
      · have := subsingleton_fin_of_eq_one (hM1 j h)
        exact Subsingleton.elim _ _
    · intro a
      refine ⟨fun j => if h : j = j₀ then Fin.cast ((congrArg M h).trans hM0).symm a
        else ⟨0, hpos j⟩, ?_⟩
      ext
      simp
  exact Fintype.sum_bijective _ hbij
    (fun m : (j : Fin K) → Fin (M j) => awgnErrorProb D N (Fin.cast hM0 (m j₀)))
    (fun a => awgnErrorProb D N a) (fun _ => rfl)

theorem singleUserCode_satisfiesPower {P : ℝ} (N : ℝ) (hD : D.SatisfiesPower P) :
    (singleUserCode D j₀ M hM0 hpos).SatisfiesPower N P := by
  intro j
  unfold MacFeedbackCode.expectedEnergy
  have hpt : ∀ m : (j : Fin K) → Fin (M j), (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
      ((singleUserCode D j₀ M hM0 hpos).input j m z i) ^ 2) ∂awgnNoise n N) ≤
      ENNReal.ofReal ((n : ℝ) * P) := by
    intro m
    have : IsProbabilityMeasure (awgnNoise n N) := by unfold awgnNoise; infer_instance
    by_cases h : j = j₀
    · subst h
      have hconst : ∀ z, ∑ i : Fin n, ((singleUserCode D j M hM0 hpos).input j m z i) ^ 2 =
          ∑ i : Fin n, (D.encoder (Fin.cast hM0 (m j)) i) ^ 2 := by
        intro z
        simp [MacFeedbackCode.input, singleUserCode]
      simp only [hconst, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_le_ofReal (hD _)
    · have hconst : ∀ z, ∑ i : Fin n, ((singleUserCode D j₀ M hM0 hpos).input j m z i) ^ 2 = 0 := by
        intro z
        simp [MacFeedbackCode.input, singleUserCode, h]
      simp only [hconst, ENNReal.ofReal_zero, lintegral_const, zero_mul]
      exact bot_le
  have hcard : (Finset.univ : Finset ((j : Fin K) → Fin (M j))).card = ∏ j, M j := by
    simp [Finset.card_univ, Fintype.card_pi]
  have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset ((j : Fin K) → Fin (M j))) _ _
    (fun m _ => hpt m)
  rw [hcard, nsmul_eq_mul] at hsum
  have hM0' : ((∏ j, M j : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by have := hpos j; omega
  calc ((∏ j, M j : ℕ) : ℝ≥0∞)⁻¹ * _ ≤ ((∏ j, M j : ℕ) : ℝ≥0∞)⁻¹ *
        (((∏ j, M j : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * P)) := by
          gcongr
    _ = ENNReal.ofReal ((n : ℝ) * P) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hM0' (ENNReal.natCast_ne_top _), one_mul]

end SingleUser

/-- The zero rate vector is achievable with (trivially linear) codes. -/
theorem zero_mem_macLinearFbRegion : (0 : Fin K → ℝ) ∈ macLinearFbRegion K P N := by
  refine ⟨fun _ => le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  have hM : (fun j : Fin K => max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * (0 : Fin K → ℝ) j)⌋₊) = fun _ => 1 := by
    funext j; simp
  rw [hM]
  let C : MacFeedbackCode K n (fun _ => 1) :=
    { enc := fun _ _ _ _ => 0
      causal := fun _ _ _ _ _ _ => rfl
      measurable_enc := fun _ _ _ => measurable_const
      dec := fun _ _ => 0
      measurable_dec := fun _ => measurable_const }
  refine ⟨C, fun _ => ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ _ => rfl,
    fun _ _ _ _ => by simp [C]⟩, fun j => ?_, ?_⟩
  · unfold MacFeedbackCode.expectedEnergy MacFeedbackCode.input
    simp [C]
  · have h0 : ∀ m, C.errorProb N m = 0 := by
      intro m
      unfold MacFeedbackCode.errorProb
      have hempty : {z : Fin n → ℝ | ∃ j, C.dec j (C.output m z) ≠ m j} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_not]
        exact fun j => Subsingleton.elim _ _
      rw [hempty, measure_empty]
    unfold MacFeedbackCode.avgErrorProb
    simp [h0]

theorem zero_mem_macFbRegion : (0 : Fin K → ℝ) ∈ macFbRegion K P N :=
  macLinearFbRegion_subset zero_mem_macLinearFbRegion

/-- **Single-user corner points**: for every sender `j₀` and `0 ≤ R < ½ log₂(1 + P/N)`, the rate
    vector `R · e_{j₀}` is achievable by linear-feedback codes (in fact by feedback-free ones). -/
theorem single_mem_macLinearFbRegion (hN : 0 < N) (hP : 0 ≤ P) (j₀ : Fin K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R < awgnCapacityFormula P N) :
    (fun j => if j = j₀ then R else 0) ∈ macLinearFbRegion K P N := by
  have hach := Known.GaussianAchievability.isAwgnAchievable_of_lt_capacity hN hP hR0 hR
  refine ⟨fun j => by dsimp only; split_ifs <;> simp [hR0], fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hach.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨D, hpow, herr⟩ := hn₀ n hn
  set M : Fin K → ℕ := fun j => max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * (if j = j₀ then R else 0))⌋₊
    with hMdef
  have hM0 : M j₀ = max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ := by simp [hMdef]
  have hM1 : ∀ j, j ≠ j₀ → M j = 1 := fun j hj => by simp [hMdef, hj]
  have hpos : ∀ j, 1 ≤ M j := fun j => le_max_left _ _
  refine ⟨singleUserCode D j₀ M hM0 hpos, fun _ => singleUserCode_isLinear D j₀ M hM0 hpos,
    singleUserCode_satisfiesPower D j₀ M hM0 hpos N hpow, ?_⟩
  rw [singleUserCode_avgErrorProb D j₀ M hM0 hpos hM1]
  exact herr

/-- Both closures contain the whole single-user segment `[0, ½ log₂(1 + P/N)] · e_{j₀}`. -/
theorem single_mem_closure_macLinearFbRegion (hN : 0 < N) (hP : 0 ≤ P) (j₀ : Fin K) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ awgnCapacityFormula P N) :
    (fun j => if j = j₀ then R else 0) ∈ closure (macLinearFbRegion K P N) ∧
      (fun j => if j = j₀ then R else 0) ∈ closure (macFbRegion K P N) := by
  have hmem : (fun j => if j = j₀ then R else 0) ∈ closure (macLinearFbRegion K P N) := by
    rcases hR.lt_or_eq with hlt | heq
    · exact subset_closure (single_mem_macLinearFbRegion hN hP j₀ hR0 hlt)
    · -- approximate `R` from below by `R (1 - 1/(k+2))`
      have hseq : Filter.Tendsto (fun k : ℕ => fun j : Fin K =>
          if j = j₀ then R * (1 - 1 / ((k : ℝ) + 1)) else 0) Filter.atTop
          (nhds (fun j => if j = j₀ then R else 0)) := by
        refine tendsto_pi_nhds.mpr fun j => ?_
        by_cases hj : j = j₀
        · simp only [hj, ↓reduceIte]
          have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_sub 1).const_mul R
          simpa using this
        · simp only [hj, ↓reduceIte]; exact tendsto_const_nhds
      refine mem_closure_of_tendsto hseq (Filter.Eventually.of_forall fun k => ?_)
      have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
      have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
      by_cases hR00 : R = 0
      · have : (fun j : Fin K => if j = j₀ then R * (1 - 1 / ((k : ℝ) + 1)) else 0) =
            (0 : Fin K → ℝ) := by funext j; simp [hR00]
        rw [this]; exact zero_mem_macLinearFbRegion
      · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hR00)
        exact single_mem_macLinearFbRegion hN hP j₀ (by nlinarith) (by nlinarith)
  exact ⟨hmem, closure_linear_subset hmem⟩

end Regions

end InfoTheory.Known.Certificates.GaussianMacFeedbackLinearOptimality
