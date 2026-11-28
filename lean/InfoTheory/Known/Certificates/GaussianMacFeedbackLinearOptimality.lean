import InfoTheory.Problems.GaussianMacFeedbackLinearOptimality
import InfoTheory.Known.GaussianAchievability
import InfoTheory.Known.GaussianNetwork
import InfoTheory.Bridge.GaussianConverse

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
* **Regression (no-feedback two-user MAC).**  `pentagon_subset_closure_macLinearFbRegion`: for
  any two senders `j₁ ≠ j₂` the full Cover–Thomas Gaussian MAC pentagon
  `{0 ≤ R₁, R₂ ≤ ½ log₂(1 + P/N), R₁ + R₂ ≤ ½ log₂(1 + 2P/N)}`, embedded at `(j₁, j₂)`
  (`embed2`), lies in both closures; in particular the no-feedback two-user sum capacity
  `½ log₂(1 + 2P/N)` is reached (`sumRate_corner_mem_closure`).  This uses the operational
  two-user MAC capacity theorem `Known.gaussianMACCapacityRegion_eq` and the code embedding
  `twoUserCode` (exact transfer of error probability and power).  The check passes: the frozen
  operational regions contain the known feedback-free answer.
* **Boundedness (feedback converse).**  `sum_le_of_mem_macFbRegion` : every
  `R ∈ macFbRegion K P N` has `∑_j R_j ≤ coopBound K P N = ½ log₂(1 + K²P/N)` (total-cooperation
  bound), for `N > 0`, `P ≥ 0`; obtained by feeding the frozen `MacFeedbackCode`,
  `SatisfiesPower` and `avgErrorProb` verbatim into
  `Bridge.gaussian_mac_feedback_sum_rate_converse` (the frozen `output` is definitionally
  `Bridge.causalOutput` of the summed drift; same expected-energy constraint, same average
  error criterion, same message counts `max 1 ⌊2^{nR_j}⌋`).  Consequences:
  `macFbRegion_subset_Icc`, `isBounded_macFbRegion`, `closure_macFbRegion_subset_Icc`,
  `sum_le_of_mem_closure_macFbRegion`, `isCompact_closure_macFbRegion`,
  `isCompact_closure_macLinearFbRegion`.  So both closures in `Statement` are compact sets
  between the no-feedback pentagons and the cooperation box, not all of `ℝ^K`.

## Not certified
* The sharper Kramer / Ozarow-type dependence-balance outer bounds (only total cooperation
  `½ log₂(1 + K²P/N)` is certified).
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

/-! ### Regression: the no-feedback two-user MAC pentagon -/

section TwoUser

variable {K : ℕ} {P N : ℝ}

/-- Embed a rate pair at senders `j₁, j₂` (all other senders at rate `0`). -/
def embed2 (j₁ j₂ : Fin K) (r : ℝ × ℝ) : Fin K → ℝ :=
  fun j => if j = j₁ then r.1 else if j = j₂ then r.2 else 0

theorem continuous_embed2 (j₁ j₂ : Fin K) : Continuous (embed2 j₁ j₂) := by
  refine continuous_pi fun j => ?_
  unfold embed2
  split_ifs
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const

/-- The feedback-free `K`-user code in which senders `j₁ ≠ j₂` run a two-user Gaussian MAC code
    `D` (from `Known.GaussianNetwork`) and all other senders have one message and send `0`. -/
noncomputable def twoUserCode {n M₁ M₂ : ℕ} (D : Known.GaussianMACCode n M₁ M₂) (j₁ j₂ : Fin K)
    (M : Fin K → ℕ) (h₁ : M j₁ = M₁) (h₂ : M j₂ = M₂) (hpos : ∀ j, 1 ≤ M j) :
    MacFeedbackCode K n M where
  enc j i m _ := if h : j = j₁ then D.encoder₁ (Fin.cast ((congrArg M h).trans h₁) m) i
    else if h' : j = j₂ then D.encoder₂ (Fin.cast ((congrArg M h').trans h₂) m) i else 0
  causal := fun _ _ _ _ _ _ => rfl
  measurable_enc := fun _ _ _ => measurable_const
  dec j y := if h : j = j₁ then Fin.cast ((congrArg M h).trans h₁).symm (D.decoder y).1
    else if h' : j = j₂ then Fin.cast ((congrArg M h').trans h₂).symm (D.decoder y).2
    else ⟨0, hpos j⟩
  measurable_dec j := by
    by_cases h : j = j₁
    · simp only [h, dite_true]
      exact (measurable_from_top (f := Fin.cast _)).comp (measurable_fst.comp D.measurable_decoder)
    · simp only [h, dite_false]
      by_cases h' : j = j₂
      · simp only [h', dite_true]
        exact (measurable_from_top (f := Fin.cast _)).comp
          (measurable_snd.comp D.measurable_decoder)
      · simp only [h', dite_false]
        exact measurable_const

section TwoUserCode

variable {n M₁ M₂ : ℕ} (D : Known.GaussianMACCode n M₁ M₂) {j₁ j₂ : Fin K} (hj : j₁ ≠ j₂)
  (M : Fin K → ℕ) (h₁ : M j₁ = M₁) (h₂ : M j₂ = M₂) (hpos : ∀ j, 1 ≤ M j)
include hj

theorem twoUserCode_enc_sum (m : (j : Fin K) → Fin (M j)) (i : Fin n) (y : Fin n → ℝ) :
    ∑ j : Fin K, (twoUserCode D j₁ j₂ M h₁ h₂ hpos).enc j i (m j) y =
      D.encoder₁ (Fin.cast h₁ (m j₁)) i + D.encoder₂ (Fin.cast h₂ (m j₂)) i := by
  rw [Fintype.sum_eq_add j₁ j₂ hj (fun j hj' => by simp [twoUserCode, hj'.1, hj'.2])]
  simp [twoUserCode, hj.symm]

theorem twoUserCode_output (m : (j : Fin K) → Fin (M j)) (z : Fin n → ℝ) :
    (twoUserCode D j₁ j₂ M h₁ h₂ hpos).output m z =
      D.encoder₁ (Fin.cast h₁ (m j₁)) + D.encoder₂ (Fin.cast h₂ (m j₂)) + z := by
  unfold MacFeedbackCode.output
  have hstep : ∀ y, (twoUserCode D j₁ j₂ M h₁ h₂ hpos).step m z y =
      D.encoder₁ (Fin.cast h₁ (m j₁)) + D.encoder₂ (Fin.cast h₂ (m j₂)) + z := by
    intro y
    funext i
    simp only [MacFeedbackCode.step, Pi.add_apply]
    rw [twoUserCode_enc_sum D hj M h₁ h₂ hpos]
  cases n with
  | zero => exact funext fun t => Fin.elim0 t
  | succ k => rw [Function.iterate_succ_apply']; exact hstep _

omit hj in
theorem twoUserCode_isLinear : (twoUserCode D j₁ j₂ M h₁ h₂ hpos).IsLinear :=
  ⟨fun j m i => (twoUserCode D j₁ j₂ M h₁ h₂ hpos).enc j i m 0, fun _ _ _ => 0,
    fun _ _ _ _ => rfl, fun j i m y => by simp [twoUserCode]⟩

theorem twoUserCode_errorProb (hM1 : ∀ j, j ≠ j₁ → j ≠ j₂ → M j = 1) (m : (j : Fin K) → Fin (M j)) :
    (twoUserCode D j₁ j₂ M h₁ h₂ hpos).errorProb N m =
      Known.gaussianMACErrorProb D N (Fin.cast h₁ (m j₁)) (Fin.cast h₂ (m j₂)) := by
  unfold MacFeedbackCode.errorProb Known.gaussianMACErrorProb
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, twoUserCode_output D hj M h₁ h₂ hpos]
  set y := D.encoder₁ (Fin.cast h₁ (m j₁)) + D.encoder₂ (Fin.cast h₂ (m j₂)) + z
  have hd1 : (twoUserCode D j₁ j₂ M h₁ h₂ hpos).dec j₁ y = Fin.cast h₁.symm (D.decoder y).1 := by
    simp [twoUserCode]
  have hd2 : (twoUserCode D j₁ j₂ M h₁ h₂ hpos).dec j₂ y = Fin.cast h₂.symm (D.decoder y).2 := by
    simp [twoUserCode, hj.symm]
  constructor
  · rintro ⟨j, hj'⟩ heq
    by_cases ha : j = j₁
    · subst ha
      rw [hd1, heq] at hj'
      exact hj' (Fin.ext (by simp))
    · by_cases hb : j = j₂
      · subst hb
        rw [hd2, heq] at hj'
        exact hj' (Fin.ext (by simp))
      · have := subsingleton_fin_of_eq_one (hM1 j ha hb)
        exact hj' (Subsingleton.elim _ _)
  · intro hne
    by_contra hall
    push Not at hall
    apply hne
    have e1 := hall j₁
    have e2 := hall j₂
    rw [hd1] at e1
    rw [hd2] at e2
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · have := congrArg Fin.val e1; simpa using this
    · have := congrArg Fin.val e2; simpa using this

theorem twoUserCode_avgErrorProb (hM1 : ∀ j, j ≠ j₁ → j ≠ j₂ → M j = 1) :
    (twoUserCode D j₁ j₂ M h₁ h₂ hpos).avgErrorProb N = Known.gaussianMACAvgError D N := by
  unfold MacFeedbackCode.avgErrorProb Known.gaussianMACAvgError
  have hprod : (∏ j, M j : ℕ) = M₁ * M₂ := by
    rw [Fintype.prod_eq_mul j₁ j₂ hj (fun j hj' => hM1 j hj'.1 hj'.2), h₁, h₂]
  rw [hprod]
  congr 1
  simp only [twoUserCode_errorProb D hj M h₁ h₂ hpos hM1]
  rw [← Fintype.sum_prod_type']
  have hbij : Function.Bijective
      (fun m : (j : Fin K) → Fin (M j) => (Fin.cast h₁ (m j₁), Fin.cast h₂ (m j₂))) := by
    refine ⟨?_, ?_⟩
    · intro m m' hmm
      funext j
      by_cases ha : j = j₁
      · subst ha
        have := congrArg (fun p => (p.1 : ℕ)) hmm
        exact Fin.ext (by simpa using this)
      · by_cases hb : j = j₂
        · subst hb
          have := congrArg (fun p => (p.2 : ℕ)) hmm
          exact Fin.ext (by simpa using this)
        · have := subsingleton_fin_of_eq_one (hM1 j ha hb)
          exact Subsingleton.elim _ _
    · rintro ⟨a, b⟩
      refine ⟨fun j => if ha : j = j₁ then Fin.cast ((congrArg M ha).trans h₁).symm a
        else if hb : j = j₂ then Fin.cast ((congrArg M hb).trans h₂).symm b
        else ⟨0, hpos j⟩, ?_⟩
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
      · simp
      · simp [hj.symm]
  exact Fintype.sum_bijective _ hbij _ (fun p => Known.gaussianMACErrorProb D N p.1 p.2)
    (fun _ => rfl)

theorem twoUserCode_satisfiesPower (hD : D.SatisfiesPower P P) :
    (twoUserCode D j₁ j₂ M h₁ h₂ hpos).SatisfiesPower N P := by
  intro j
  unfold MacFeedbackCode.expectedEnergy
  have hpt : ∀ m : (j : Fin K) → Fin (M j), (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
      ((twoUserCode D j₁ j₂ M h₁ h₂ hpos).input j m z i) ^ 2) ∂awgnNoise n N) ≤
      ENNReal.ofReal ((n : ℝ) * P) := by
    intro m
    have : IsProbabilityMeasure (awgnNoise n N) := by unfold awgnNoise; infer_instance
    by_cases ha : j = j₁
    · subst ha
      have hconst : ∀ z, ∑ i : Fin n, ((twoUserCode D j j₂ M h₁ h₂ hpos).input j m z i) ^ 2 =
          ∑ i : Fin n, (D.encoder₁ (Fin.cast h₁ (m j)) i) ^ 2 := by
        intro z
        simp [MacFeedbackCode.input, twoUserCode]
      simp only [hconst, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_le_ofReal (hD.1 _)
    · by_cases hb : j = j₂
      · subst hb
        have hconst : ∀ z, ∑ i : Fin n, ((twoUserCode D j₁ j M h₁ h₂ hpos).input j m z i) ^ 2 =
            ∑ i : Fin n, (D.encoder₂ (Fin.cast h₂ (m j)) i) ^ 2 := by
          intro z
          simp [MacFeedbackCode.input, twoUserCode, ha]
        simp only [hconst, lintegral_const, measure_univ, mul_one]
        exact ENNReal.ofReal_le_ofReal (hD.2 _)
      · have hconst : ∀ z, ∑ i : Fin n,
            ((twoUserCode D j₁ j₂ M h₁ h₂ hpos).input j m z i) ^ 2 = 0 := by
          intro z
          simp [MacFeedbackCode.input, twoUserCode, ha, hb]
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

end TwoUserCode

/-- Every rate pair achievable on the two-user Gaussian MAC without feedback (equal powers `P`),
    placed at senders `j₁ ≠ j₂`, is achievable on the `K`-user MAC with linear feedback. -/
theorem embed2_mem_macLinearFbRegion {j₁ j₂ : Fin K} (hj : j₁ ≠ j₂) {R₁ R₂ : ℝ}
    (h : Known.IsGaussianMACAchievable P P N R₁ R₂) :
    embed2 j₁ j₂ (R₁, R₂) ∈ macLinearFbRegion K P N := by
  obtain ⟨hR₁, hR₂, h⟩ := h
  refine ⟨fun j => by unfold embed2; split_ifs <;> simp [hR₁, hR₂], fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨D, hpow, herr⟩ := hn₀ n hn
  set M : Fin K → ℕ := fun j => max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * embed2 j₁ j₂ (R₁, R₂) j)⌋₊
    with hMdef
  have h₁ : M j₁ = max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊ := by simp [hMdef, embed2]
  have h₂ : M j₂ = max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊ := by simp [hMdef, embed2, hj.symm]
  have hM1 : ∀ j, j ≠ j₁ → j ≠ j₂ → M j = 1 := fun j ha hb => by simp [hMdef, embed2, ha, hb]
  have hpos : ∀ j, 1 ≤ M j := fun j => le_max_left _ _
  refine ⟨twoUserCode D j₁ j₂ M h₁ h₂ hpos, fun _ => twoUserCode_isLinear D M h₁ h₂ hpos,
    twoUserCode_satisfiesPower D hj M h₁ h₂ hpos hpow, ?_⟩
  rw [twoUserCode_avgErrorProb D hj M h₁ h₂ hpos hM1]
  exact herr

/-- **Regression (no-feedback MAC pentagon).**  For any two distinct senders `j₁ ≠ j₂` of the
    `K`-user model, the whole Cover–Thomas Gaussian MAC pentagon
    `0 ≤ R₁, R₂ ≤ ½ log₂(1 + P/N)`, `R₁ + R₂ ≤ ½ log₂(1 + 2P/N)` (embedded at `j₁, j₂`) lies in
    the closure of the linear-feedback region, hence also of the feedback region.  This is the
    known answer when feedback is ignored and only two senders are active (feedback cannot
    hurt), obtained from the operational two-user MAC capacity theorem
    `Known.gaussianMACCapacityRegion_eq`. -/
theorem pentagon_subset_closure_macLinearFbRegion (hN : 0 < N) (hP : 0 ≤ P) {j₁ j₂ : Fin K}
    (hj : j₁ ≠ j₂) {r : ℝ × ℝ} (hr : r ∈ Known.gaussianMACPentagon P P N) :
    embed2 j₁ j₂ r ∈ closure (macLinearFbRegion K P N) ∧
      embed2 j₁ j₂ r ∈ closure (macFbRegion K P N) := by
  rw [← Known.gaussianMACCapacityRegion_eq hP hP hN] at hr
  have hmem : embed2 j₁ j₂ r ∈ closure (macLinearFbRegion K P N) :=
    map_mem_closure (continuous_embed2 j₁ j₂) hr fun p hp => embed2_mem_macLinearFbRegion hj hp
  exact ⟨hmem, closure_linear_subset hmem⟩

/-- In particular the no-feedback two-user sum capacity `½ log₂(1 + 2P/N)` is approached:
    the corner `(½ log₂(1 + P/N), ½ log₂(1 + 2P/N) - ½ log₂(1 + P/N))` lies in both closures. -/
theorem sumRate_corner_mem_closure (hN : 0 < N) (hP : 0 ≤ P) {j₁ j₂ : Fin K} (hj : j₁ ≠ j₂) :
    embed2 j₁ j₂ (awgnCapacityFormula P N, awgnCapacityFormula (P + P) N - awgnCapacityFormula P N)
      ∈ closure (macLinearFbRegion K P N) := by
  refine (pentagon_subset_closure_macLinearFbRegion hN hP hj ?_).1
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : 0 ≤ awgnCapacityFormula P N := by
    unfold awgnCapacityFormula log2
    have := Real.log_nonneg (show 1 ≤ 1 + P / N by have := div_nonneg hP hN.le; linarith)
    positivity
  have hmono : awgnCapacityFormula P N ≤ awgnCapacityFormula (P + P) N := by
    unfold awgnCapacityFormula log2
    have h1 : 0 < 1 + P / N := by have := div_nonneg hP hN.le; linarith
    have h2 : 1 + P / N ≤ 1 + (P + P) / N := by
      have := div_nonneg hP hN.le; rw [add_div]; linarith
    have := Real.log_le_log h1 h2
    gcongr
  -- `C(2P) ≤ 2 C(P)` since `1 + 2x ≤ (1 + x)²`
  have hsub : awgnCapacityFormula (P + P) N ≤ awgnCapacityFormula P N + awgnCapacityFormula P N := by
    unfold awgnCapacityFormula log2
    have hx : 0 ≤ P / N := div_nonneg hP hN.le
    have h1 : 0 < 1 + (P + P) / N := by rw [add_div]; linarith
    have h2 : 1 + (P + P) / N ≤ (1 + P / N) ^ 2 := by rw [add_div]; nlinarith
    have := Real.log_le_log h1 h2
    rw [Real.log_pow] at this
    have : Real.log (1 + (P + P) / N) / Real.log 2 ≤
        2 * Real.log (1 + P / N) / Real.log 2 := by gcongr; exact_mod_cast this
    linarith [show 2 * Real.log (1 + P / N) / Real.log 2 =
      Real.log (1 + P / N) / Real.log 2 + Real.log (1 + P / N) / Real.log 2 by ring]
  exact ⟨hA, by linarith, le_rfl, by linarith, by linarith⟩

end TwoUser

/-! ### Boundedness: the total-cooperation feedback converse -/

section Converse

variable {K : ℕ} {P N : ℝ}

/-- The total-cooperation sum-rate bound `½ log₂(1 + K²P/N)`. -/
noncomputable def coopBound (K : ℕ) (P N : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + (K : ℝ) ^ 2 * P / N)

/-- **Feedback converse on the exact frozen objects**: every rate vector in `macFbRegion K P N`
    has sum rate at most `½ log₂(1 + K²P/N)`.  The frozen `MacFeedbackCode` (its `output` is
    definitionally `Bridge.causalOutput` of the summed drift), `SatisfiesPower` and
    `avgErrorProb` are fed verbatim into `Bridge.gaussian_mac_feedback_sum_rate_converse`. -/
theorem sum_le_of_mem_macFbRegion (hN : 0 < N) (hP : 0 ≤ P) {R : Fin K → ℝ}
    (hR : R ∈ macFbRegion K P N) : ∑ j, R j ≤ coopBound K P N := by
  obtain ⟨_, hach⟩ := hR
  refine InfoTheory.Bridge.gaussian_mac_feedback_sum_rate_converse hN hP (fun δ hδ => ?_)
  obtain ⟨n₀, hn₀⟩ := hach δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨C, -, hpow, herr⟩ := hn₀ n hn
  exact ⟨C.enc, C.dec, C.causal, C.measurable_enc, C.measurable_dec, hpow, herr⟩

/-- Each coordinate of a feedback-achievable rate vector lies in `[0, ½ log₂(1 + K²P/N)]`. -/
theorem macFbRegion_subset_Icc (hN : 0 < N) (hP : 0 ≤ P) :
    macFbRegion K P N ⊆ Set.Icc 0 (fun _ => coopBound K P N) := by
  intro R hR
  have h0 : ∀ j, 0 ≤ R j := hR.1
  have hs := sum_le_of_mem_macFbRegion hN hP hR
  refine ⟨fun j => h0 j, fun j => ?_⟩
  exact le_trans (Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)) hs

/-- **`macFbRegion` is bounded** (so its closure is a compact set, not all of `ℝ^K`). -/
theorem isBounded_macFbRegion (hN : 0 < N) (hP : 0 ≤ P) :
    Bornology.IsBounded (macFbRegion K P N) :=
  (Metric.isBounded_Icc _ _).subset (macFbRegion_subset_Icc hN hP)

theorem closure_macFbRegion_subset_Icc (hN : 0 < N) (hP : 0 ≤ P) :
    closure (macFbRegion K P N) ⊆ Set.Icc 0 (fun _ => coopBound K P N) :=
  closure_minimal (macFbRegion_subset_Icc hN hP) isClosed_Icc

/-- The closure of the feedback region (hence also of the linear-feedback region) is compact. -/
theorem isCompact_closure_macFbRegion (hN : 0 < N) (hP : 0 ≤ P) :
    IsCompact (closure (macFbRegion K P N)) :=
  (isBounded_macFbRegion hN hP).isCompact_closure

theorem isCompact_closure_macLinearFbRegion (hN : 0 < N) (hP : 0 ≤ P) :
    IsCompact (closure (macLinearFbRegion K P N)) :=
  ((isBounded_macFbRegion hN hP).subset macLinearFbRegion_subset).isCompact_closure

/-- The sum-rate bound passes to the closure. -/
theorem sum_le_of_mem_closure_macFbRegion (hN : 0 < N) (hP : 0 ≤ P) {R : Fin K → ℝ}
    (hR : R ∈ closure (macFbRegion K P N)) : ∑ j, R j ≤ coopBound K P N := by
  have hcl : IsClosed {R : Fin K → ℝ | ∑ j, R j ≤ coopBound K P N} :=
    isClosed_le (by fun_prop) continuous_const
  exact closure_minimal (fun R hR => sum_le_of_mem_macFbRegion hN hP hR) hcl hR

end Converse

end InfoTheory.Known.Certificates.GaussianMacFeedbackLinearOptimality
