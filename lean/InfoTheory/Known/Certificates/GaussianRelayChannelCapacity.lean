import InfoTheory.Problems.GaussianRelayChannelCapacity
import InfoTheory.Known.GaussianAchievability
import InfoTheory.Bridge.Gaussian

/-!
# Certificate for `InfoTheory.Problems.GaussianRelayChannelCapacity`

The statement (statement fix 2, 2026-11-27) asks whether, at unit gains, the minimum energy
per bit over all codes equals the minimum energy per bit over linear-relaying codes:
`gaussianRelayMinEnergyPerBit false 1 1 1 = gaussianRelayMinEnergyPerBit true 1 1 1`.

**History.** This module was added in 49c683f for the previous statement (the low-SNR cutset
slope, now `LowSnrCutsetSlopeStatement`). For statement fix 2:
* the operational lemmas were kept, with a `linearOnly : Bool` argument added because
  `IsGaussianRelayAchievable` gained that flag; the silent relay is linear, so every
  silent-relay code works for both values (`isLinearRelay_zero`);
* the ratio facts about the retired statement were kept unchanged;
* the energy-per-bit section at the end is new.

## Certified (about exactly these objects)
* `pi_gaussian_eq_withDensity` — the noise model of `IsGaussianRelayAchievable` (Lebesgue
  integrals against `∏ᵢ gaussianPdf1D 1 (zᵢ)`) is the i.i.d. `N(0, 1)` law: `Measure.pi`
  of `gaussianReal 0 1` equals `volume.withDensity (∏ᵢ φ(zᵢ))`.
* `isGaussianRelayAchievable_zero` — rate `0` is achievable (single message, silent nodes), so
  `gaussianRelayCapacity` is the supremum of a nonempty set.
* `isGaussianRelayAchievable_of_awgn`, `isGaussianRelayAchievable_direct`,
  `direct_le_gaussianRelayCapacity` — **direct-link lower bound**: for `g₁₃ ≠ 0`, `P₁ ≥ 0` and
  any `g₁₂, g₂₃, P₂`, a point-to-point AWGN code used with a silent relay is a relay code with
  the same error probability. Hence
  `ofReal (½ log₂(1 + g₁₃² P₁)) ≤ gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂`, using the operational
  AWGN coding theorem `Known.GaussianAchievability.isAwgnAchievable_of_lt_capacity`.
* `direct_slope_le_ratio`, `target_pos`, `target_ne_top`, `direct_slope_lt_target` — facts
  about the ratio in the retired `LowSnrCutsetSlopeStatement`. They do not decide it.
* `achievable_of_linear`, `minEnergyPerBit_le_linear` — `E*(g) ≤ E*_lin(g)` for all gains.
* `statement_iff` — `Statement ↔ E*_lin(1,1,1) ≤ E*(1,1,1)`. This neither proves nor disproves
  `Statement`.
* `minEnergyPerBit_linear_le`, `minEnergyPerBit_le`, `minEnergyPerBit_linear_ne_top` —
  **direct transmission**: `E*(1,1,1) ≤ E*_lin(1,1,1) ≤ 2 ln 2`. In particular neither side is
  the junk value `⊤`.

## Not certified
* `E*(1,1,1) ≥ (3/4) · 2 ln 2` (cutset bound, El Gamal–Mohseni–Zahedi 2006, Table II), and in
  particular `E* > 0`: this needs a Fano/cutset converse for Gaussian relay codes, which the
  library does not provide. (If both sides collapsed to the junk value `0`, `Statement` would
  hold vacuously; the cutset bound rules this out on paper.)
* The cutset upper bound `gaussianRelayCapacity 1 1 1 P P ≤ ½ log₂(1 + 2P)`.
* Any bound on `E*_lin` below `2 ln 2`: none is published at unit gains.
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

/-- The silent relay (`x_{r,i} = 0`, all coefficients `d_{ij} = 0`) is linear. -/
theorem isLinearRelay_zero (n : ℕ) :
    IsLinearRelay (fun (_ : Fin n) (_ : Fin _ → ℝ) => (0 : ℝ)) :=
  ⟨fun _ _ => 0, fun _ _ => by simp⟩

/-- **Silent-relay transfer**: every rate achievable on the AWGN channel with power `g₁₃² P₁`
    and noise variance `1` is achievable on the Gaussian relay channel (`g₁₃ ≠ 0`; any
    `g₁₂, g₂₃, P₂`): the source sends `x(m) / g₁₃`, the relay stays silent. The silent relay
    is linear, so this holds for both values of `linearOnly`. -/
theorem isGaussianRelayAchievable_of_awgn (lo : Bool) {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ} (hg : g₁₃ ≠ 0)
    (h : IsAwgnAchievable (g₁₃ ^ 2 * P₁) 1 R) :
    IsGaussianRelayAchievable lo g₁₂ g₁₃ g₂₃ P₁ P₂ R := by
  obtain ⟨hR, h⟩ := h
  refine ⟨hR, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨max n₀ 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun n hn => ?_⟩
  obtain ⟨C, hpow, herr⟩ := hn₀ n (le_trans (le_max_left _ _) hn)
  have hg2 : 0 < g₁₃ ^ 2 := by positivity
  refine ⟨fun m i => C.encoder m i / g₁₃, fun _ _ => 0, C.decoder,
    fun _ => isLinearRelay_zero n, fun _ => measurable_const, C.measurable_decoder,
    fun m => ?_, fun m => ?_, ?_⟩
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
theorem isGaussianRelayAchievable_zero (lo : Bool) (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) (hP₁ : 0 ≤ P₁) :
    IsGaussianRelayAchievable lo g₁₂ g₁₃ g₂₃ P₁ P₂ 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨1, Nat.zero_lt_one, fun n _ => ?_⟩⟩
  have hM : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  dsimp only
  rw [hM]
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => isLinearRelay_zero n,
    fun _ => measurable_const, measurable_const, fun m => ?_, fun m => ?_, ?_⟩
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · simp
  · simp

/-- **Direct-link lower bound**: for `g₁₃ ≠ 0` and `P₁ ≥ 0`, every
    `0 ≤ R < ½ log₂(1 + g₁₃² P₁)` is achievable on the Gaussian relay channel. -/
theorem isGaussianRelayAchievable_direct (lo : Bool) {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ} (hg : g₁₃ ≠ 0)
    (hP₁ : 0 ≤ P₁) (hR0 : 0 ≤ R) (hR : R < (1 / 2 : ℝ) * log2 (1 + g₁₃ ^ 2 * P₁)) :
    IsGaussianRelayAchievable lo g₁₂ g₁₃ g₂₃ P₁ P₂ R := by
  refine isGaussianRelayAchievable_of_awgn lo hg
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
    · have hach := isGaussianRelayAchievable_direct false (g₁₂ := g₁₂) (g₂₃ := g₂₃) (P₂ := P₂) hg hP₁
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

/-! ### Facts about the retired `LowSnrCutsetSlopeStatement` ratio (kept from 49c683f) -/

/-- For every `P > 0`: `ofReal (log₂(1 + P) / (2P)) ≤ gaussianRelayCapacity 1 1 1 P P / ofReal P`.
    The left side tends to `1 / (2 ln 2)` as `P → 0⁺`. (About the ratio in the retired
    `LowSnrCutsetSlopeStatement`; it does not decide that statement.) -/
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

/-! ### Linear relaying and the minimum energy per bit (the current `Statement`) -/

/-- Linear relaying is a special case of relaying: a rate achievable with linear relays is
    achievable with arbitrary relays (same code). -/
theorem achievable_of_linear {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ}
    (h : IsGaussianRelayAchievable true g₁₂ g₁₃ g₂₃ P₁ P₂ R) :
    IsGaussianRelayAchievable false g₁₂ g₁₃ g₂₃ P₁ P₂ R := by
  obtain ⟨hR, h⟩ := h
  refine ⟨hR, fun ε hε => ?_⟩
  obtain ⟨N, hN, h⟩ := h ε hε
  refine ⟨N, hN, fun n hn => ?_⟩
  obtain ⟨enc, relay, dec, -, rest⟩ := h n hn
  exact ⟨enc, relay, dec, fun hf => absurd hf (by decide), rest⟩

/-- `E*(g) ≤ E*_lin(g)` for all gains. -/
theorem minEnergyPerBit_le_linear (g₁₂ g₁₃ g₂₃ : ℝ) :
    gaussianRelayMinEnergyPerBit false g₁₂ g₁₃ g₂₃ ≤
      gaussianRelayMinEnergyPerBit true g₁₂ g₁₃ g₂₃ := by
  unfold gaussianRelayMinEnergyPerBit
  refine sInf_le_sInf ?_
  rintro e ⟨P₁, P₂, R, h₁, h₂, hR, hach, rfl⟩
  exact ⟨P₁, P₂, R, h₁, h₂, hR, achievable_of_linear hach, rfl⟩

/-- The open content of `Statement` is exactly `E*_lin(1,1,1) ≤ E*(1,1,1)`. -/
theorem statement_iff :
    Statement ↔
      gaussianRelayMinEnergyPerBit true 1 1 1 ≤ gaussianRelayMinEnergyPerBit false 1 1 1 := by
  unfold Statement
  exact ⟨fun h => h.symm.le, fun h => le_antisymm (minEnergyPerBit_le_linear 1 1 1) h⟩

/-- Rate used for the direct-transmission energy bound: `R(x) = x / (2 ln 2 (1 + x)²)` bits. -/
private lemma direct_rate_lt {x : ℝ} (hx : 0 < x) :
    x / (2 * Real.log 2 * (1 + x) ^ 2) < (1 / 2 : ℝ) * log2 (1 + 1 ^ 2 * x) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1x : 0 < 1 + x := by linarith
  -- `log (1 + x) ≥ 1 - (1 + x)⁻¹ = x / (1 + x)`
  have hlog : x / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos h1x
    have he : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    linarith
  have hlt : x / (1 + x) ^ 2 < x / (1 + x) := by
    apply div_lt_div_of_pos_left hx h1x
    nlinarith
  unfold log2
  rw [one_pow, one_mul]
  calc x / (2 * Real.log 2 * (1 + x) ^ 2) = (x / (1 + x) ^ 2) / (2 * Real.log 2) := by
        field_simp
    _ < (x / (1 + x)) / (2 * Real.log 2) := by gcongr
    _ ≤ Real.log (1 + x) / (2 * Real.log 2) := by gcongr
    _ = (1 / 2 : ℝ) * (Real.log (1 + x) / Real.log 2) := by field_simp

/-- **Direct transmission**: `E*_lin(1,1,1) ≤ 2 ln 2` (so `E*_lin` is not the junk value `⊤`).
    For every `x > 0` the operating point `P₁ = x`, `P₂ = x²`, `R = x / (2 ln 2 (1 + x)²)` is
    achievable with a silent (hence linear) relay and has energy per bit `2 ln 2 (1 + x)³`;
    let `x → 0⁺`. -/
theorem minEnergyPerBit_linear_le :
    gaussianRelayMinEnergyPerBit true 1 1 1 ≤ ENNReal.ofReal (2 * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (2 * Real.log 2 * (1 + x) ^ 3) with hf
  have hlim : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (2 * Real.log 2))) := by
    have hc : Continuous f :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul
        ((continuous_const.add continuous_id).pow 3))
    have h0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hf0 : f 0 = ENNReal.ofReal (2 * Real.log 2) := by simp [hf]
    rwa [hf0] at h0
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun x hx => ?_)
  have hx : (0 : ℝ) < x := hx
  have h1x : 0 < 1 + x := by linarith
  set R : ℝ := x / (2 * Real.log 2 * (1 + x) ^ 2) with hR
  have hRpos : 0 < R := by positivity
  have hach : IsGaussianRelayAchievable true 1 1 1 x (x ^ 2) R :=
    isGaussianRelayAchievable_direct true one_ne_zero hx.le hRpos.le (direct_rate_lt hx)
  have hmem : ENNReal.ofReal ((x + x ^ 2) / R) ∈
      { e : ℝ≥0∞ | ∃ P₁ P₂ R : ℝ, 0 < P₁ ∧ 0 < P₂ ∧ 0 < R ∧
        IsGaussianRelayAchievable true 1 1 1 P₁ P₂ R ∧
        e = ENNReal.ofReal ((P₁ + P₂) / R) } :=
    ⟨x, x ^ 2, R, hx, by positivity, hRpos, hach, rfl⟩
  have heq : (x + x ^ 2) / R = 2 * Real.log 2 * (1 + x) ^ 3 := by
    rw [hR]
    field_simp
  calc gaussianRelayMinEnergyPerBit true 1 1 1 ≤ ENNReal.ofReal ((x + x ^ 2) / R) := sInf_le hmem
    _ = f x := by rw [heq]

/-- Consequently `E*(1,1,1) ≤ E*_lin(1,1,1) ≤ 2 ln 2 < ⊤`. -/
theorem minEnergyPerBit_le :
    gaussianRelayMinEnergyPerBit false 1 1 1 ≤ ENNReal.ofReal (2 * Real.log 2) :=
  (minEnergyPerBit_le_linear 1 1 1).trans minEnergyPerBit_linear_le

theorem minEnergyPerBit_linear_ne_top : gaussianRelayMinEnergyPerBit true 1 1 1 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top minEnergyPerBit_linear_le

end InfoTheory.Known.Certificates.GaussianRelayChannelCapacity
