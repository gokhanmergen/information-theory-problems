import InfoTheory.Problems.GaussianRelayChannelCapacity
import InfoTheory.Known.GaussianAchievability
import InfoTheory.Bridge.Gaussian

/-!
# Certificate for `InfoTheory.Problems.GaussianRelayChannelCapacity`

The statement (statement-fixed 2026-11-27) asks whether, for unit gains and equal powers
`P₁ = P₂ = P`, `gaussianRelayCapacity 1 1 1 P P / P → 1 / ln 2` as `P → 0⁺` (the cutset slope,
in bits per unit power).

## Certified (about exactly these objects)
* `pi_gaussian_eq_withDensity` — the noise model of `IsGaussianRelayAchievable` (Lebesgue
  integrals against `∏ᵢ gaussianPdf1D 1 (zᵢ)`) is the i.i.d. `N(0, 1)` law: `Measure.pi`
  of `gaussianReal 0 1` equals `volume.withDensity (∏ᵢ φ(zᵢ))`.
* `isGaussianRelayAchievable_zero` — rate `0` is achievable (single message, silent nodes), so
  `gaussianRelayCapacity` is the supremum of a nonempty set.
* `isGaussianRelayAchievable_of_awgn`, `isGaussianRelayAchievable_direct`,
  `direct_le_gaussianRelayCapacity` — **direct-link lower bound**: for `g₁₃ ≠ 0`, `P₁ ≥ 0` and
  any `g₁₂, g₂₃, P₂`, a point-to-point AWGN code used with a silent relay is a relay code with
  the same error probability, so
  `ofReal (½ log₂(1 + g₁₃² P₁)) ≤ gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂`
  (using the operational AWGN coding theorem
  `Known.GaussianAchievability.isAwgnAchievable_of_lt_capacity`).
* `direct_slope_le_ratio` — hence for every `P > 0`,
  `ofReal (log₂(1 + P) / (2P)) ≤ gaussianRelayCapacity 1 1 1 P P / ofReal P`; the left side
  tends to `1 / (2 ln 2)`, which is `< 1 / ln 2` (`direct_slope_lt_target`), so the direct
  link alone does not decide the statement. `target_pos`, `target_ne_top`: the target
  `ofReal (1 / ln 2)` is a finite positive number.

## Not certified
* The cutset upper bound `gaussianRelayCapacity 1 1 1 P P ≤ ½ log₂(1 + 2P)` (in particular
  finiteness of the capacity): this needs a converse for Gaussian relay codes, which the
  library does not provide. (If the capacity were `⊤`, the ratio would be `⊤` and the
  statement false, so no junk value can make it true.)
* The El Gamal–Mohseni–Zahedi bursty linear-relaying lower bound `C ≥ 0.88283 P` for
  `P ∈ (0, 1/10]` (on paper in
  `attempts/gaussian-relay-channel-capacity/2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace InfoTheory.Known.Certificates.GaussianRelayChannelCapacity

open InfoTheory InfoTheory.Bridge InfoTheory.Problems.GaussianRelayChannelCapacity

/-! ### The noise model -/

lemma gaussianPdf1D_one_eq (x : ℝ) :
    gaussianPdf1D 1 x = gaussianPDFReal 0 1 x :=
  gaussianPdf1D_eq_gaussianPDFReal zero_le_one x

/-- **The i.i.d. standard Gaussian law as a density**:
    `N(0, 1)^{⊗n} = volume.withDensity (z ↦ ∏ᵢ φ(zᵢ))`. -/
theorem pi_gaussian_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun z => ENNReal.ofReal (∏ i, gaussianPdf1D 1 (z i))) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  set g : Fin n → ℝ → ℝ := fun i => (s i).indicator (gaussianPDFReal 0 1) with hg
  have hpt : ∀ z : Fin n → ℝ,
      (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (∏ i, gaussianPdf1D 1 (z i))) z =
        ENNReal.ofReal (∏ i, g i (z i)) := by
    intro z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      have hz' : ∀ i, z i ∈ s i := fun i => hz i (Set.mem_univ i)
      simp only [hg, Set.indicator_of_mem (hz' _), gaussianPdf1D_one_eq]
    · rw [Set.indicator_of_notMem hz]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  simp_rw [hpt]
  have hint : ∀ i, Integrable (g i) volume := fun i =>
    (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hnn : ∀ i x, 0 ≤ g i x := fun i x => by
    simp only [hg]
    exact Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) x
  have hprod_int : Integrable (fun z : Fin n → ℝ => ∏ i, g i (z i)) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hprod_int
      (Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hnn i (z i)),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, hg, integral_indicator (hs i)]

/-- Lebesgue integral against the Gaussian density product = integral against `N(0,1)^{⊗n}`. -/
theorem lintegral_gaussian_density (n : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ z, ENNReal.ofReal (∏ i, gaussianPdf1D 1 (z i)) * f z =
      ∫⁻ z, f z ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hmeas : Measurable (gaussianPdf1D 1) := by
    rw [show gaussianPdf1D 1 = gaussianPDFReal 0 1 from funext gaussianPdf1D_one_eq]
    exact measurable_gaussianPDFReal 0 1
  rw [pi_gaussian_eq_withDensity, lintegral_withDensity_eq_lintegral_mul_non_measurable]
  · rfl
  · exact (Finset.measurable_prod _ fun i _ => hmeas.comp (measurable_pi_apply i)).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-! ### Silent-relay codes -/

lemma gaussianReal_toNNReal_one : gaussianReal 0 (1 : ℝ).toNNReal = gaussianReal 0 1 := by
  rw [Real.toNNReal_one]

lemma awgnNoise_one (n : ℕ) : awgnNoise n 1 = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
  unfold awgnNoise
  rw [Real.toNNReal_one]

lemma lintegral_gaussian_density_one (n : ℕ) :
    ∫⁻ z : Fin n → ℝ, ENNReal.ofReal (∏ i, gaussianPdf1D 1 (z i)) = 1 := by
  have h := lintegral_gaussian_density n (fun _ => 1)
  simp only [mul_one] at h
  rw [h, lintegral_const, measure_univ, one_mul]

/-- **Error of a silent-relay code**: the error integral of `IsGaussianRelayAchievable` for
    the code `(x(m) / g₁₃, 0, ĝ)` built from an AWGN code `(x, ĝ)` equals the AWGN error
    probability of that code at noise variance `1`. -/
theorem errProb_silent {g₁₃ g₂₃ : ℝ} (hg : g₁₃ ≠ 0) {n M : ℕ} (C : AwgnCode n M) (m : Fin M) :
    (∫⁻ (zr : Fin n → ℝ) (z : Fin n → ℝ),
      if (C.decoder fun i => g₁₃ * (C.encoder m i / g₁₃) + g₂₃ * 0 + z i) ≠ m then
        ENNReal.ofReal ((∏ i, gaussianPdf1D 1 (zr i)) * ∏ i, gaussianPdf1D 1 (z i))
      else 0) = awgnErrorProb C 1 m := by
  set E : Set (Fin n → ℝ) := {z | C.decoder (C.encoder m + z) ≠ m} with hE
  have hEm : MeasurableSet E :=
    (C.measurable_decoder.comp (measurable_const.add measurable_id))
      (measurableSet_singleton m).compl
  have hpt : ∀ zr z : Fin n → ℝ,
      (if (C.decoder fun i => g₁₃ * (C.encoder m i / g₁₃) + g₂₃ * 0 + z i) ≠ m then
        ENNReal.ofReal ((∏ i, gaussianPdf1D 1 (zr i)) * ∏ i, gaussianPdf1D 1 (z i))
      else 0) =
      ENNReal.ofReal (∏ i, gaussianPdf1D 1 (zr i)) *
        (ENNReal.ofReal (∏ i, gaussianPdf1D 1 (z i)) * E.indicator 1 z) := by
    intro zr z
    have hy : (fun i => g₁₃ * (C.encoder m i / g₁₃) + g₂₃ * 0 + z i) = C.encoder m + z := by
      funext i
      simp only [mul_zero, add_zero, Pi.add_apply]
      rw [mul_div_cancel₀ _ hg]
    simp only [hy]
    have hnn1 : 0 ≤ ∏ i, gaussianPdf1D 1 (zr i) :=
      Finset.prod_nonneg fun i _ => gaussianPdf1D_nonneg zero_le_one _
    by_cases hz : z ∈ E
    · have hz' : C.decoder (C.encoder m + z) ≠ m := hz
      rw [Set.indicator_of_mem hz, ite_eq_left_of_eq_true _ _ (eq_true hz'), Pi.one_apply, mul_one,
        ENNReal.ofReal_mul hnn1]
    · have hz' : ¬ C.decoder (C.encoder m + z) ≠ m := hz
      rw [Set.indicator_of_notMem hz, ite_eq_right_of_eq_false _ _ (eq_false hz'), mul_zero, mul_zero]
  simp_rw [hpt]
  have hinner : ∀ zr : Fin n → ℝ,
      ∫⁻ z, ENNReal.ofReal (∏ i, gaussianPdf1D 1 (zr i)) *
        (ENNReal.ofReal (∏ i, gaussianPdf1D 1 (z i)) * E.indicator 1 z) =
      ENNReal.ofReal (∏ i, gaussianPdf1D 1 (zr i)) * awgnErrorProb C 1 m := by
    intro zr
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gaussian_density,
      lintegral_indicator_one hEm, awgnErrorProb, awgnNoise_one]
  simp_rw [hinner]
  rw [lintegral_mul_const' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top ?_),
    lintegral_gaussian_density_one, one_mul]
  rw [awgnErrorProb, awgnNoise_one]
  exact prob_le_one

/-- **Silent-relay transfer**: every rate achievable on the AWGN channel with power `g₁₃² P₁`
    and noise variance `1` is achievable on the Gaussian relay channel (`g₁₃ ≠ 0`; any
    `g₁₂, g₂₃, P₂`): the source sends `x(m) / g₁₃`, the relay stays silent. -/
theorem isGaussianRelayAchievable_of_awgn {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ} (hg : g₁₃ ≠ 0)
    (h : IsAwgnAchievable (g₁₃ ^ 2 * P₁) 1 R) :
    IsGaussianRelayAchievable g₁₂ g₁₃ g₂₃ P₁ P₂ R := by
  obtain ⟨hR, h⟩ := h
  refine ⟨hR, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨max n₀ 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun n hn => ?_⟩
  obtain ⟨C, hpow, herr⟩ := hn₀ n (le_trans (le_max_left _ _) hn)
  have hg2 : 0 < g₁₃ ^ 2 := by positivity
  refine ⟨fun m i => C.encoder m i / g₁₃, fun _ _ => 0, C.decoder,
    fun _ => measurable_const, C.measurable_decoder, fun m => ?_, fun m => ?_, ?_⟩
  · have h1 := hpow m
    have h2 : ∑ i, (C.encoder m i / g₁₃) ^ 2 = (∑ i, (C.encoder m i) ^ 2) / g₁₃ ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => div_pow _ _ _
    rw [h2, div_le_iff₀ hg2]
    linarith
  · show ∫⁻ zr : Fin n → ℝ, ENNReal.ofReal ((∏ i, gaussianPdf1D 1 (zr i)) *
      ∑ i : Fin n, (0 : ℝ) ^ 2) ≤ _
    simp
  · dsimp only
    simp_rw [errProb_silent hg C]
    exact herr

/-- Rate `0` is achievable (single message, silent nodes): `gaussianRelayCapacity` is the
    supremum of a nonempty set. -/
theorem isGaussianRelayAchievable_zero (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) (hP₁ : 0 ≤ P₁) :
    IsGaussianRelayAchievable g₁₂ g₁₃ g₂₃ P₁ P₂ 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨1, Nat.zero_lt_one, fun n _ => ?_⟩⟩
  have hM : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  dsimp only
  rw [hM]
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => measurable_const, measurable_const,
    fun m => ?_, fun m => ?_, ?_⟩
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · simp
  · simp

/-- **Direct-link lower bound**: for `g₁₃ ≠ 0` and `P₁ ≥ 0`, every
    `0 ≤ R < ½ log₂(1 + g₁₃² P₁)` is achievable on the Gaussian relay channel. -/
theorem isGaussianRelayAchievable_direct {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ} (hg : g₁₃ ≠ 0)
    (hP₁ : 0 ≤ P₁) (hR0 : 0 ≤ R) (hR : R < (1 / 2 : ℝ) * log2 (1 + g₁₃ ^ 2 * P₁)) :
    IsGaussianRelayAchievable g₁₂ g₁₃ g₂₃ P₁ P₂ R := by
  refine isGaussianRelayAchievable_of_awgn hg
    (GaussianAchievability.isAwgnAchievable_of_lt_capacity one_pos (by positivity) hR0 ?_)
  simpa [awgnCapacityFormula] using hR

lemma direct_rate_nonneg {g P : ℝ} (hP : 0 ≤ P) : 0 ≤ (1 / 2 : ℝ) * log2 (1 + g ^ 2 * P) := by
  unfold log2
  have : 0 ≤ Real.log (1 + g ^ 2 * P) := Real.log_nonneg (by nlinarith [sq_nonneg g])
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  positivity

/-- **Direct-link lower bound on the capacity**:
    `ofReal (½ log₂(1 + g₁₃² P₁)) ≤ gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂`. -/
theorem direct_le_gaussianRelayCapacity {g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ} (hg : g₁₃ ≠ 0) (hP₁ : 0 ≤ P₁) :
    ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 + g₁₃ ^ 2 * P₁)) ≤
      gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂ := by
  set c := (1 / 2 : ℝ) * log2 (1 + g₁₃ ^ 2 * P₁) with hc
  have hc0 : 0 ≤ c := direct_rate_nonneg hP₁
  rcases hc0.lt_or_eq with hcpos | hceq
  · -- approach `c` from below by achievable rates
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    by_cases hδc : (δ : ℝ) < c
    · have hach := isGaussianRelayAchievable_direct (g₁₂ := g₁₂) (g₂₃ := g₂₃) (P₂ := P₂) hg hP₁
        (sub_nonneg.mpr hδc.le) (by linarith [(NNReal.coe_pos.mpr hδ)] : c - δ < c)
      have hle : ENNReal.ofReal (c - δ) ≤ gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂ :=
        le_sSup ⟨c - δ, hach, rfl⟩
      calc ENNReal.ofReal c = ENNReal.ofReal (c - δ + δ) := by ring_nf
        _ ≤ ENNReal.ofReal (c - δ) + ENNReal.ofReal δ := ENNReal.ofReal_add_le
        _ ≤ gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂ + δ := by
          gcongr
          rw [ENNReal.ofReal_coe_nnreal]
    · push Not at hδc
      calc ENNReal.ofReal c ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hδc
        _ = (δ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
        _ ≤ gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂ + δ := le_add_self
  · rw [← hceq, ENNReal.ofReal_zero]
    exact zero_le

/-! ### Consequences for the statement's ratio -/

/-- For every `P > 0`: `ofReal (log₂(1 + P) / (2P)) ≤ gaussianRelayCapacity 1 1 1 P P / ofReal P`.
    The left side tends to `1 / (2 ln 2)` as `P → 0⁺`. -/
theorem direct_slope_le_ratio {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal (log2 (1 + P) / (2 * P)) ≤
      gaussianRelayCapacity 1 1 1 P P / ENNReal.ofReal P := by
  have h := direct_le_gaussianRelayCapacity (g₁₂ := 1) (g₂₃ := 1) (P₂ := P) one_ne_zero hP.le
  simp only [one_pow, one_mul] at h
  have hl : 0 ≤ log2 (1 + P) / (2 * P) := by
    unfold log2
    have : 0 ≤ Real.log (1 + P) := Real.log_nonneg (by linarith)
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hP)) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hl]
  refine le_trans (le_of_eq ?_) h
  congr 1
  field_simp

/-- The target slope `1 / ln 2` is a finite positive number. -/
theorem target_pos : 0 < ENNReal.ofReal (1 / Real.log 2) :=
  ENNReal.ofReal_pos.mpr (by have := Real.log_pos one_lt_two; positivity)

theorem target_ne_top : ENNReal.ofReal (1 / Real.log 2) ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The direct-link slope `1 / (2 ln 2)` is strictly below the target `1 / ln 2`. -/
theorem direct_slope_lt_target : 1 / (2 * Real.log 2) < 1 / Real.log 2 := by
  have h := Real.log_pos one_lt_two
  rw [div_lt_div_iff₀ (by positivity) h]
  linarith

end InfoTheory.Known.Certificates.GaussianRelayChannelCapacity
