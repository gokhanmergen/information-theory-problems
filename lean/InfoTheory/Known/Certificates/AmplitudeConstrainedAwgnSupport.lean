import InfoTheory.Problems.AmplitudeConstrainedAwgnSupport
import InfoTheory.Known.GaussianAchievability

/-!
# Certificate for `InfoTheory.Problems.AmplitudeConstrainedAwgnSupport`

The frozen statement compares the operational capacity `peakCapacity A N` of the AWGN channel
under the peak constraint `|X| ≤ A` with the operational capacity `peakCapacityWithin A N k` of
codes restricted to `k`-point constellations in `[-A, A]`, and asks whether
`C_k(A', N) = C(A', N)` implies `C_k(A, N) = C(A, N)` for `A ≤ A'` (monotonicity of the support
size of the capacity-achieving input, Sharma–Shamai 2010).

## Certified (about exactly these objects)
* **Both `sSup`s are non-junk** for `A ≥ 0`, `N > 0`, `k ≥ 1`:
  `isPeakAchievableWithin_zero` / `isPeakAchievable_zero` (rate `0`; nonempty) and
  `isPeakAchievable_le` (every peak-achievable rate is `≤ ½ log₂(1 + A²/N)`; bounded).
  The bound uses the existing operational AWGN converse
  (`Known.GaussianChannel.isAwgnAchievable_le`) and `|x| ≤ A ⇒ ∑ xᵢ² ≤ nA²`.
* `peakCapacity_le_formula` : `C(A, N) ≤ ½ log₂(1 + A²/N)` (Smith 1971; Cover–Thomas Ch. 9).
* `peakCapacity_le_awgnOperationalCapacity` : `C(A, N) ≤ C_AWGN(A², N)` (operational, using
  `Known.GaussianAchievability.awgnOperationalCapacity_eq`).
* `peakCapacityWithin_le_peakCapacity`, `peakCapacityWithin_mono` :
  `C_k ≤ C_{k'} ≤ C` for `1 ≤ k ≤ k'`.
* `bsc_rate_le_peakCapacityWithin_two`, `peakCapacityWithin_two_pos`, `peakCapacity_pos` :
  binary antipodal signalling `±A` with hard decisions gives
  `C(A, N) ≥ C_2(A, N) ≥ 1 - h(Q(A/√N)) > 0` for `A, N > 0`.
* **Regression `C₁ = 0`.**  `peakCapacityWithin_one_eq_zero` : `C₁(A, N) = 0` (a one-point
  constellation makes all codewords equal, so `half_le_avgErrorProb_of_const` forces average
  error `≥ 1/2` once `M ≥ 2`); hence `peakCapacityWithin_one_lt_peakCapacity` : `C₁ < C` for
  `A, N > 0` — the optimal input has at least two mass points (Smith 1971), and the
  hypothesis of `Statement` at `k = 1` is never met for `A' > 0`.  The check passes.
* **Monotonicity in the amplitude.**  `peakCapacity_mono_amp`, `peakCapacityWithin_mono_amp` :
  `C(A, N)` and `C_k(A, N)` are nondecreasing in `A`.

## Not certified
* Smith's theorem (the capacity-achieving input is unique, symmetric and has finitely many mass
  points), the coding theorem `C(A, N) = max_{P_X([-A,A]) = 1} I(X; X + Z)`, and its `k`-point
  analogue.  These are what make `C_k(A, N) = C(A, N) ⇔ K(A/√N) ≤ k` (see the problem file).
* Sharma–Shamai's characterization `C_2(A, 1) = C(A, 1) ⇔ A ≤ Ā ≈ 1.665`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace InfoTheory.Known.Certificates.AmplitudeConstrainedAwgnSupport

open InfoTheory InfoTheory.Problems.AmplitudeConstrainedAwgnSupport

variable {A N R : ℝ} {k : ℕ}

/-! ### Constraint bookkeeping -/

theorem satisfiesPeak_of_usesConstellation {n M : ℕ} {C : AwgnCode n M}
    (h : UsesConstellation C A k) : SatisfiesPeak C A := by
  obtain ⟨S, _, hSA, hC⟩ := h
  exact fun m i => hSA _ (hC m i)

theorem usesConstellation_mono {n M : ℕ} {C : AwgnCode n M} {k' : ℕ} (hk : k ≤ k')
    (h : UsesConstellation C A k) : UsesConstellation C A k' := by
  obtain ⟨S, hS, hSA, hC⟩ := h
  exact ⟨S, hS.trans hk, hSA, hC⟩

/-- The peak constraint `|xᵢ| ≤ A` implies the (per-codeword) power constraint `∑ xᵢ² ≤ nA²`. -/
theorem satisfiesPower_of_satisfiesPeak {n M : ℕ} {C : AwgnCode n M}
    (h : SatisfiesPeak C A) : C.SatisfiesPower (A ^ 2) := by
  intro m
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (C.encoder m i) ^ 2 ≤ A ^ 2 := by
    intro i _
    have h1 := h m i
    have h0 : 0 ≤ |C.encoder m i| := abs_nonneg _
    have := pow_le_pow_left₀ h0 h1 2
    rwa [sq_abs] at this
  have := Finset.sum_le_card_nsmul _ _ _ hle
  simpa [nsmul_eq_mul] using this

theorem isPeakAchievable_of_within (h : IsPeakAchievableWithin A N k R) :
    IsPeakAchievable A N R := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2 δ hδ
  exact ⟨n₀, fun n hn => by
    obtain ⟨C, hC, herr⟩ := hn₀ n hn
    exact ⟨C, satisfiesPeak_of_usesConstellation hC, herr⟩⟩

theorem isPeakAchievableWithin_mono {k' : ℕ} (hk : k ≤ k')
    (h : IsPeakAchievableWithin A N k R) : IsPeakAchievableWithin A N k' R := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2 δ hδ
  exact ⟨n₀, fun n hn => by
    obtain ⟨C, hC, herr⟩ := hn₀ n hn
    exact ⟨C, usesConstellation_mono hk hC, herr⟩⟩

theorem isAwgnAchievable_of_isPeakAchievable (h : IsPeakAchievable A N R) :
    IsAwgnAchievable (A ^ 2) N R := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2 δ hδ
  exact ⟨n₀, fun n hn => by
    obtain ⟨C, hC, herr⟩ := hn₀ n hn
    exact ⟨C, satisfiesPower_of_satisfiesPeak hC, herr⟩⟩

/-! ### Non-junk: nonempty and bounded -/

/-- Rate `0` is achievable with the one-point constellation `{0}` (needs `A ≥ 0`, `k ≥ 1`). -/
theorem isPeakAchievableWithin_zero (hA : 0 ≤ A) (hk : 1 ≤ k) (N : ℝ) :
    IsPeakAchievableWithin A N k 0 := by
  refine ⟨le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  have hM : max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * 0)⌋₊ = 1 := by simp
  rw [hM]
  let C : AwgnCode n 1 := ⟨fun _ _ => 0, fun _ => 0, measurable_const⟩
  refine ⟨C, ⟨{0}, by simpa using hk, by simpa using hA, fun m i => by simp [C]⟩, ?_⟩
  have h0 : ∀ m : Fin 1, awgnErrorProb C N m = 0 := by
    intro m
    unfold awgnErrorProb
    have hempty : {z : Fin n → ℝ | C.decoder (C.encoder m + z) ≠ m} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Subsingleton.elim _ _
    rw [hempty, measure_empty]
  unfold awgnAvgErrorProb
  simp [h0]

theorem isPeakAchievable_zero (hA : 0 ≤ A) (N : ℝ) : IsPeakAchievable A N 0 :=
  isPeakAchievable_of_within (isPeakAchievableWithin_zero (k := 1) hA le_rfl N)

/-- **Converse**: every peak-achievable rate is at most `½ log₂(1 + A²/N)`. -/
theorem isPeakAchievable_le (hN : 0 < N) (h : IsPeakAchievable A N R) :
    R ≤ awgnCapacityFormula (A ^ 2) N :=
  Known.GaussianChannel.isAwgnAchievable_le hN (sq_nonneg A)
    (isAwgnAchievable_of_isPeakAchievable h)

theorem peakAchievable_nonempty (hA : 0 ≤ A) (N : ℝ) :
    { R : ℝ | IsPeakAchievable A N R }.Nonempty :=
  ⟨0, isPeakAchievable_zero hA N⟩

theorem peakAchievable_bddAbove (hN : 0 < N) :
    BddAbove { R : ℝ | IsPeakAchievable A N R } :=
  ⟨_, fun _ hR => isPeakAchievable_le hN hR⟩

theorem peakAchievableWithin_nonempty (hA : 0 ≤ A) (hk : 1 ≤ k) (N : ℝ) :
    { R : ℝ | IsPeakAchievableWithin A N k R }.Nonempty :=
  ⟨0, isPeakAchievableWithin_zero hA hk N⟩

theorem peakAchievableWithin_bddAbove (hN : 0 < N) :
    BddAbove { R : ℝ | IsPeakAchievableWithin A N k R } :=
  ⟨_, fun _ hR => isPeakAchievable_le hN (isPeakAchievable_of_within hR)⟩

/-! ### Comparisons of the capacities -/

/-- `C(A, N) ≤ ½ log₂(1 + A²/N)`. -/
theorem peakCapacity_le_formula (hA : 0 ≤ A) (hN : 0 < N) :
    peakCapacity A N ≤ awgnCapacityFormula (A ^ 2) N :=
  csSup_le (peakAchievable_nonempty hA N) (fun _ hR => isPeakAchievable_le hN hR)

/-- The peak-constrained capacity is at most the operational AWGN capacity at power `A²`. -/
theorem peakCapacity_le_awgnOperationalCapacity (hA : 0 ≤ A) (hN : 0 < N) :
    peakCapacity A N ≤ awgnOperationalCapacity (A ^ 2) N := by
  rw [Known.GaussianAchievability.awgnOperationalCapacity_eq hN (sq_nonneg A)]
  exact peakCapacity_le_formula hA hN

theorem le_peakCapacity (hN : 0 < N) (h : IsPeakAchievable A N R) : R ≤ peakCapacity A N :=
  le_csSup (peakAchievable_bddAbove hN) h

theorem le_peakCapacityWithin (hN : 0 < N) (h : IsPeakAchievableWithin A N k R) :
    R ≤ peakCapacityWithin A N k :=
  le_csSup (peakAchievableWithin_bddAbove hN) h

theorem peakCapacity_nonneg (hA : 0 ≤ A) (hN : 0 < N) : 0 ≤ peakCapacity A N :=
  le_peakCapacity hN (isPeakAchievable_zero hA N)

theorem peakCapacityWithin_nonneg (hA : 0 ≤ A) (hk : 1 ≤ k) (hN : 0 < N) :
    0 ≤ peakCapacityWithin A N k :=
  le_peakCapacityWithin hN (isPeakAchievableWithin_zero hA hk N)

/-- `C_k(A, N) ≤ C(A, N)`. -/
theorem peakCapacityWithin_le_peakCapacity (hA : 0 ≤ A) (hk : 1 ≤ k) (hN : 0 < N) :
    peakCapacityWithin A N k ≤ peakCapacity A N :=
  csSup_le (peakAchievableWithin_nonempty hA hk N)
    (fun _ hR => le_peakCapacity hN (isPeakAchievable_of_within hR))

/-- `C_k(A, N) ≤ C_{k'}(A, N)` for `1 ≤ k ≤ k'`. -/
theorem peakCapacityWithin_mono {k' : ℕ} (hA : 0 ≤ A) (hk : 1 ≤ k) (hkk : k ≤ k')
    (hN : 0 < N) : peakCapacityWithin A N k ≤ peakCapacityWithin A N k' :=
  csSup_le (peakAchievableWithin_nonempty hA hk N)
    (fun _ hR => le_peakCapacityWithin hN (isPeakAchievableWithin_mono hkk hR))

/-! ### Positivity: binary antipodal signalling `±A` -/

open Known.GaussianChannel in
/-- BPSK at power `A²` uses only the two amplitudes `±A`. -/
theorem bpskCode_usesConstellation (hA : 0 ≤ A) {n M : ℕ} (enc : Fin M → Fin n → Bool)
    (dec : (Fin n → Bool) → Fin M) : UsesConstellation (bpskCode (A ^ 2) enc dec) A 2 := by
  refine ⟨{A, -A}, ?_, ?_, ?_⟩
  · exact (Finset.card_insert_le _ _).trans (by simp)
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [abs_of_nonneg hA]
    · rw [abs_neg, abs_of_nonneg hA]
  · intro m i
    simp only [bpskCode, bpskSymbol, Real.sqrt_sq hA, Finset.mem_insert, Finset.mem_singleton]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

open Known.GaussianChannel in
/-- Every rate below the BPSK/hard-decision BSC capacity `1 - h(Q(A/√N))` is achievable with the
    two-point constellation `{±A}`. -/
theorem isPeakAchievableWithin_two_of_lt_bsc (hA : 0 ≤ A) (hN : 0 < N) (hR0 : 0 ≤ R)
    (hR : R < 1 - binaryEntropy (bpskCrossover (A ^ 2) N)) :
    IsPeakAchievableWithin A N 2 R := by
  have hach := Bridge.shannon_channel_coding_achievability
    (bsc (bpskCrossover (A ^ 2) N) bpskCrossover_nonneg bpskCrossover_le_one) R hR0
    (by rw [Known.bsc_capacity]; exact hR)
  refine ⟨hR0, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hach.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hn₀ n hn
  refine ⟨bpskCode (A ^ 2) enc dec, bpskCode_usesConstellation hA enc dec, ?_⟩
  have hM : 1 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ := le_max_left _ _
  rw [ENNReal.le_ofReal_iff_toReal_le (awgnAvgErrorProb_ne_top hM _ N) hδ.le,
    @bpskCode_avgErrorProb (A ^ 2) N hN n _ hM enc dec (Classical.decEq Bool)]
  exact herr

open Known.GaussianChannel in
/-- `C_2(A, N) ≥ 1 - h(Q(A/√N))`. -/
theorem bsc_rate_le_peakCapacityWithin_two (hA : 0 ≤ A) (hN : 0 < N) :
    1 - binaryEntropy (bpskCrossover (A ^ 2) N) ≤ peakCapacityWithin A N 2 := by
  by_contra hlt
  push Not at hlt
  have h0 := peakCapacityWithin_nonneg hA (by norm_num : 1 ≤ 2) hN
  set R := (peakCapacityWithin A N 2 + (1 - binaryEntropy (bpskCrossover (A ^ 2) N))) / 2
    with hRdef
  have hR := isPeakAchievableWithin_two_of_lt_bsc hA hN (R := R) (by rw [hRdef]; linarith)
    (by rw [hRdef]; linarith)
  have := le_peakCapacityWithin hN hR
  rw [hRdef] at this
  linarith

/-- **Non-vacuity**: `C_2(A, N) > 0` for `A, N > 0`. -/
theorem peakCapacityWithin_two_pos (hA : 0 < A) (hN : 0 < N) : 0 < peakCapacityWithin A N 2 :=
  lt_of_lt_of_le (Known.GaussianChannel.bsc_bpsk_capacity_pos hN (pow_pos hA 2))
    (bsc_rate_le_peakCapacityWithin_two hA.le hN)

/-- **Non-vacuity**: `C(A, N) > 0` for `A, N > 0`. -/
theorem peakCapacity_pos (hA : 0 < A) (hN : 0 < N) : 0 < peakCapacity A N :=
  lt_of_lt_of_le (peakCapacityWithin_two_pos hA hN)
    (peakCapacityWithin_le_peakCapacity hA.le (by norm_num) hN)

/-- Summary: `0 < C_2(A, N) ≤ C(A, N) ≤ ½ log₂(1 + A²/N)` for `A, N > 0`. -/
theorem peak_capacity_chain (hA : 0 < A) (hN : 0 < N) :
    0 < peakCapacityWithin A N 2 ∧ peakCapacityWithin A N 2 ≤ peakCapacity A N ∧
      peakCapacity A N ≤ awgnCapacityFormula (A ^ 2) N :=
  ⟨peakCapacityWithin_two_pos hA hN,
    peakCapacityWithin_le_peakCapacity hA.le (by norm_num) hN,
    peakCapacity_le_formula hA.le hN⟩

/-! ### Regressions: one point gives zero capacity; monotonicity in the amplitude -/

/-- A code whose codewords all coincide (and has `M ≥ 2` messages) has average error
    probability at least `1/2` (exactly `1 - 1/M`): the decoder's output law does not depend on
    the message. -/
theorem half_le_avgErrorProb_of_const {n M : ℕ} (C : AwgnCode n M) (hM : 2 ≤ M)
    (hconst : ∀ m m' : Fin M, C.encoder m = C.encoder m') (N : ℝ) :
    (1 / 2 : ℝ) ≤ (awgnAvgErrorProb C N).toReal := by
  set μ := awgnNoise n N
  have : IsProbabilityMeasure μ := by unfold μ awgnNoise; infer_instance
  set x := C.encoder ⟨0, by omega⟩
  set f : (Fin n → ℝ) → Fin M := fun z => C.decoder (x + z) with hf
  have hfm : Measurable f := C.measurable_decoder.comp (measurable_const.add measurable_id)
  have hmeas : ∀ m : Fin M, MeasurableSet (f ⁻¹' {m}) := fun m => hfm (measurableSet_singleton m)
  have herr : ∀ m, awgnErrorProb C N m = μ (f ⁻¹' {m})ᶜ := by
    intro m
    unfold awgnErrorProb
    rw [hconst m ⟨0, by omega⟩]
    rfl
  have hsum1 : ∑ m : Fin M, μ (f ⁻¹' {m}) = 1 := by
    rw [sum_measure_preimage_singleton _ (fun m _ => hmeas m)]
    simp
  have hadd : (∑ m : Fin M, awgnErrorProb C N m) + 1 = (M : ℝ≥0∞) := by
    rw [← hsum1, ← Finset.sum_add_distrib]
    simp_rw [herr]
    have : ∀ m : Fin M, μ (f ⁻¹' {m})ᶜ + μ (f ⁻¹' {m}) = 1 := fun m => by
      rw [add_comm, measure_add_measure_compl (hmeas m), measure_univ]
    simp [this]
  have hE := ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top hadd
  unfold awgnAvgErrorProb
  rw [hE, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_sub_of_le
    (by exact_mod_cast (by omega : 1 ≤ M)) (ENNReal.natCast_ne_top M)]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

/-- With a one-point constellation only rate `0` is achievable. -/
theorem isPeakAchievableWithin_one_le_zero (h : IsPeakAchievableWithin A N 1 R) : R ≤ 0 := by
  by_contra hR
  push Not at hR
  obtain ⟨n₀, hn₀⟩ := h.2 (1 / 4) (by norm_num)
  set n := max n₀ ⌈1 / R⌉₊
  obtain ⟨C, ⟨S, hS, -, hCS⟩, herr⟩ := hn₀ n (le_max_left _ _)
  have hnR : 1 ≤ (n : ℝ) * R := by
    have h1 : 1 / R ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rwa [div_le_iff₀ hR] at h1
  have hM : 2 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ := by
    refine le_max_of_le_right (Nat.le_floor ?_)
    calc ((2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR
  have hconst : ∀ m m', C.encoder m = C.encoder m' := fun m m' => funext fun i =>
    Finset.card_le_one.mp hS _ (hCS m i) _ (hCS m' i)
  have hhalf := half_le_avgErrorProb_of_const C hM hconst N
  have := ENNReal.toReal_le_of_le_ofReal (by norm_num) herr
  linarith

/-- **Regression: `C₁(A, N) = 0`.**  A one-point constellation carries no information. -/
theorem peakCapacityWithin_one_eq_zero (hA : 0 ≤ A) (hN : 0 < N) :
    peakCapacityWithin A N 1 = 0 :=
  le_antisymm (csSup_le (peakAchievableWithin_nonempty hA le_rfl N)
    (fun _ hR => isPeakAchievableWithin_one_le_zero hR)) (peakCapacityWithin_nonneg hA le_rfl hN)

/-- Hence `C₁(A, N) < C(A, N)` for `A, N > 0`: the capacity-achieving input always has at least
    two mass points (consistent with Smith 1971), so the hypothesis of `Statement` at `k = 1`
    never holds for `A' > 0`. -/
theorem peakCapacityWithin_one_lt_peakCapacity (hA : 0 < A) (hN : 0 < N) :
    peakCapacityWithin A N 1 < peakCapacity A N := by
  rw [peakCapacityWithin_one_eq_zero hA.le hN]
  exact peakCapacity_pos hA hN

theorem isPeakAchievable_mono_amp {A' : ℝ} (hAA : A ≤ A') (h : IsPeakAchievable A N R) :
    IsPeakAchievable A' N R := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2 δ hδ
  exact ⟨n₀, fun n hn => by
    obtain ⟨C, hC, herr⟩ := hn₀ n hn
    exact ⟨C, fun m i => (hC m i).trans hAA, herr⟩⟩

theorem isPeakAchievableWithin_mono_amp {A' : ℝ} (hAA : A ≤ A')
    (h : IsPeakAchievableWithin A N k R) : IsPeakAchievableWithin A' N k R := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2 δ hδ
  exact ⟨n₀, fun n hn => by
    obtain ⟨C, ⟨S, hS, hSA, hCS⟩, herr⟩ := hn₀ n hn
    exact ⟨C, ⟨S, hS, fun s hs => (hSA s hs).trans hAA, hCS⟩, herr⟩⟩

/-- **Monotonicity in the amplitude**: `C(A, N) ≤ C(A', N)` for `0 ≤ A ≤ A'`. -/
theorem peakCapacity_mono_amp {A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hN : 0 < N) :
    peakCapacity A N ≤ peakCapacity A' N :=
  csSup_le (peakAchievable_nonempty hA N)
    (fun _ hR => le_peakCapacity hN (isPeakAchievable_mono_amp hAA hR))

/-- **Monotonicity in the amplitude**: `C_k(A, N) ≤ C_k(A', N)` for `0 ≤ A ≤ A'`, `k ≥ 1`. -/
theorem peakCapacityWithin_mono_amp {A' : ℝ} (hA : 0 ≤ A) (hk : 1 ≤ k) (hAA : A ≤ A')
    (hN : 0 < N) : peakCapacityWithin A N k ≤ peakCapacityWithin A' N k :=
  csSup_le (peakAchievableWithin_nonempty hA hk N)
    (fun _ hR => le_peakCapacityWithin hN (isPeakAchievableWithin_mono_amp hAA hR))

end InfoTheory.Known.Certificates.AmplitudeConstrainedAwgnSupport
