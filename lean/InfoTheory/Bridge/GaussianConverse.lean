import InfoTheory.Core.GaussianOperational
import InfoTheory.Bridge.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Measure

/-!
# Causal-Gaussian Multi-User Feedback Converse Toolkit

General operational converse machinery for causal Gaussian channels with feedback, proved directly
from Lebesgue measure preservation of strictly causal channel equations and the meta-converse
(change-of-measure) inequality `ln u ≤ u - 1`.

## Main results

1. **Abstract meta-converse (`meta_converse_message_bound`, `meta_converse_avg_error`)**:
   for any family of output laws `P : ι → Measure Ω` and reference probability law `Q` with
   `Q = (P m).withDensity (fun y => ENNReal.ofReal (Real.exp (-L m y)))` and integrable `L m`,
   `(1 - P_e) ln |ι| ≤ (1 / |ι|) ∑_m E_{P_m}[L_m] + 1`.
2. **Causal bijection & unit Jacobian (`causalOutput`, `causalInverse`,
   `measurePreserving_causalOutput`, `map_causalOutput_volume`)**:
   for any strictly causal measurable drift on `Fin n → E`, the causal output map is a measurable
   bijection whose inverse is `y ↦ y - drift y` and preserves any product of right-invariant
   σ-finite measures (in particular Lebesgue `volume` on `ℝⁿ` and `(ℝ × ℝ)ⁿ`).
3. **1D causal vector-AWGN feedback converse (`causal_awgn_feedback_code_converse`,
   `causal_awgn_feedback_rate_le`)**:
   `(1 - P_e) ln |ι| ≤ (n / 2) ln (1 + S / N) + 1`, hence `R ≤ ½ log₂(1 + S / N)`.
4. **2-output (`d = 2`) causal AWGN feedback converse (`causal_awgn2_feedback_code_converse`,
   `causal_awgn2_feedback_rate_le`)** and **2D orthogonal rotation invariance / sharp SIMO
   converse (`measurePreserving_rot2D_awgnNoise`, `causal_simo_awgn_feedback_converse`,
   `causal_simo_awgn_feedback_rate_le`)**:
   `(1 - P_e) ln |ι| ≤ (n / 2) ln (1 + (h₁² + h₂²) P / N) + 1`.
5. **Ready-to-call corollaries for the three wireless open problems**:
   - **K-user Gaussian MAC with feedback** (`gaussian_mac_feedback_code_converse`,
     `gaussian_mac_feedback_sum_rate_converse`): `∑ R_j ≤ ½ log₂(1 + K² P / N)`.
   - **2-user Gaussian BC with feedback** (`gaussian_bc_feedback_code_converse`,
     `gaussian_bc_feedback_sum_rate_converse`): `R₁ + R₂ ≤ ½ log₂(1 + (h₁² + h₂²) P / N)`.
   - **3-node Gaussian relay channel** (`gaussian_relay_code_cutset_converse`,
     `gaussian_relay_cutset_converse_bc`, `gaussian_relay_cutset_converse_mac`,
     `gaussian_relay_cutset_converse_coupled`, `gaussian_relay_unit_energy_per_bit_ge`):
     both BC and MAC cuts, the correlation-coupled Cover–El Gamal cut-set bound, and the
     El Gamal–Mohseni–Zahedi (2006) Table II unit-gain lower bound
     `(3 / 4) · 2 ln 2 ≤ (P₁ + P₂) / R`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace InfoTheory.Bridge

open InfoTheory

/-! ### 1. Abstract Meta-Converse and Asymptotic Rate Helper -/

section MetaConverse

/-- Per-message meta-converse inequality: if `P, Q` are probability measures on `Ω` with
    `Q = P.withDensity (e^{-L})` and `Integrable L P`, then for every measurable set `A` and
    every `c ≥ 1`, `P.real A * ln c - (c - 1) * Q.real A ≤ ∫ y, L y ∂P`. -/
theorem meta_converse_message_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (L : Ω → ℝ) (hLm : Measurable L) (hLint : Integrable L P)
    (hQ : Q = P.withDensity (fun y => ENNReal.ofReal (Real.exp (-L y))))
    {A : Set Ω} (hA : MeasurableSet A) {c : ℝ} (hc : 1 ≤ c) :
    P.real A * Real.log c - (c - 1) * Q.real A ≤ ∫ y, L y ∂P := by
  set G : Ω → ℝ := fun y => Real.exp (-L y) with hG
  have hGm : Measurable G := hLm.neg.exp
  have hGofReal : ∀ y, (ENNReal.ofReal (G y)).toReal = G y :=
    fun y => ENNReal.toReal_ofReal (Real.exp_pos _).le
  have hlint : ∫⁻ y, ENNReal.ofReal (G y) ∂P = 1 := by
    have h := congrArg (fun μ : Measure Ω => μ Set.univ) hQ
    simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, measure_univ] at h
    exact h.symm
  have hGint : Integrable G P := by
    have h := integrable_toReal_of_lintegral_ne_top hGm.ennreal_ofReal.aemeasurable
      (by rw [hlint]; exact ENNReal.one_ne_top)
    exact h.congr (ae_of_all _ hGofReal)
  have hGA : ∫ y, A.indicator G y ∂P = Q.real A := by
    rw [integral_indicator hA, measureReal_def, hQ, withDensity_apply _ hA,
      ← integral_toReal hGm.ennreal_ofReal.aemeasurable
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    exact integral_congr_ae (ae_of_all _ (fun y => (hGofReal y).symm))
  have hG1 : ∫ y, G y ∂P = 1 := by
    have h := integral_toReal (μ := P) hGm.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))
    rw [hlint, ENNReal.toReal_one] at h
    rw [← h]
    exact integral_congr_ae (ae_of_all _ (fun y => (hGofReal y).symm))
  have hc0 : 0 < c := by linarith
  have hpt : ∀ y, A.indicator (fun _ => Real.log c) y + 1 - ((c - 1) * A.indicator G y + G y) ≤
      L y := by
    intro y
    by_cases hy : y ∈ A
    · simp only [Set.indicator_of_mem hy]
      have h := Real.log_le_sub_one_of_pos (mul_pos hc0 (Real.exp_pos (-L y)))
      rw [Real.log_mul hc0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
      simp only [hG]
      nlinarith
    · simp only [Set.indicator_of_notMem hy]
      have h := Real.log_le_sub_one_of_pos (Real.exp_pos (-L y))
      rw [Real.log_exp] at h
      simp only [hG]
      linarith
  have hint1 : Integrable (fun y => A.indicator (fun _ => Real.log c) y) P :=
    (integrable_const _).indicator hA
  have hint2 : Integrable (fun y => (c - 1) * A.indicator G y + G y) P :=
    ((hGint.indicator hA).const_mul _).add hGint
  have hint3 : Integrable
      (fun y => A.indicator (fun _ => Real.log c) y + 1 - ((c - 1) * A.indicator G y + G y)) P :=
    (hint1.add (integrable_const _)).sub hint2
  have hmono := integral_mono hint3 hLint hpt
  have hcalc : ∫ y, (A.indicator (fun _ => Real.log c) y + 1 -
      ((c - 1) * A.indicator G y + G y)) ∂P =
      P.real A * Real.log c + 1 - ((c - 1) * Q.real A + 1) := by
    have hint4 : Integrable (fun y => A.indicator (fun _ => Real.log c) y + 1) P :=
      hint1.add (integrable_const _)
    have hint5 : Integrable (fun y => (c - 1) * A.indicator G y) P :=
      (hGint.indicator hA).const_mul _
    have hint6 : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const _
    rw [integral_sub hint4 hint2, integral_add hint1 hint6, integral_add hint5 hGint,
      integral_const_mul, integral_indicator_const _ hA, hGA, hG1, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hcalc] at hmono
  linarith

/-- Average-error meta-converse over any nonempty finite message set `ι`:
    if `Q = (P m).withDensity (e^{-L m})` with `Integrable (L m) (P m)` for every `m : ι`
    and `dec : Ω → ι` is measurable, then
    `(1 - avgErr.toReal) * ln |ι| ≤ (1 / |ι|) * (∑ m, ∫ y, L m y ∂(P m)) + 1`. -/
theorem meta_converse_avg_error {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hcard : 1 ≤ Fintype.card ι)
    (P : ι → Measure Ω) [∀ m, IsProbabilityMeasure (P m)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (dec : Ω → ι) (hdec : Measurable dec)
    (L : ι → Ω → ℝ) (hLm : ∀ m, Measurable (L m)) (hLint : ∀ m, Integrable (L m) (P m))
    (hQ : ∀ m, Q = (P m).withDensity (fun y => ENNReal.ofReal (Real.exp (-L m y)))) :
    let avgErr : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ m : ι, P m {y | dec y ≠ m}
    (1 - avgErr.toReal) * Real.log (Fintype.card ι : ℝ) ≤
      (1 / (Fintype.card ι : ℝ)) * (∑ m : ι, ∫ y, L m y ∂(P m)) + 1 := by
  intro avgErr
  set M : ℕ := Fintype.card ι with hM_def
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hcard
  have hMpos : (0 : ℝ) < M := by linarith
  have hpre : ∀ m : ι, MeasurableSet (dec ⁻¹' {m}) :=
    fun m => hdec (measurableSet_singleton m)
  have hmsg : ∀ m : ι,
      (1 - (P m {y | dec y ≠ m}).toReal) * Real.log (M : ℝ) -
        ((M : ℝ) - 1) * Q.real (dec ⁻¹' {m}) ≤ ∫ y, L m y ∂(P m) := by
    intro m
    have h1 := meta_converse_message_bound (P m) Q (L m) (hLm m) (hLint m) (hQ m) (hpre m) hMr
    have hcompl : (P m).real (dec ⁻¹' {m}) = 1 - (P m {y | dec y ≠ m}).toReal := by
      have hadd := measure_add_measure_compl (μ := P m) (hpre m)
      rw [measure_univ] at hadd
      have heq : (dec ⁻¹' {m})ᶜ = {y | dec y ≠ m} := by ext y; simp
      rw [heq] at hadd
      have h' := congrArg ENNReal.toReal hadd
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h'
      rw [measureReal_def]
      linarith
    rw [hcompl] at h1
    exact h1
  have hsumQ : ∑ m : ι, Q.real (dec ⁻¹' {m}) = 1 := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
      sum_measure_preimage_singleton Finset.univ (fun m _ => hpre m)]
    simp
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hmsg m)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumQ, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_one] at hsum
  have havg : avgErr.toReal = (1 / (M : ℝ)) * ∑ m : ι, (P m {y | dec y ≠ m}).toReal := by
    simp only [avgErr, hM_def, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), one_div]
  rw [havg]
  set E := ∑ m : ι, (P m {y | dec y ≠ m}).toReal
  have hrw : (1 - 1 / (M : ℝ) * E) * Real.log M = ((M - E) * Real.log M) / M := by
    field_simp
  rw [hrw, div_le_iff₀ hMpos]
  have hcalc : ((1 / (M : ℝ)) * (∑ m : ι, ∫ y, L m y ∂(P m)) + 1) * M =
      (∑ m : ι, ∫ y, L m y ∂(P m)) + M := by
    field_simp
  rw [hcalc]
  linarith

/-- Lower bound `((n : ℝ) * R - 1) * ln 2 ≤ ln (max 1 ⌊2^{nR}⌋)`. -/
lemma log_max_one_floor_rpow_two_ge (n : ℕ) (R : ℝ) :
    ((n : ℝ) * R - 1) * Real.log 2 ≤
      Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) := by
  set M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
  have hpow_pos : 0 < (2 : ℝ) ^ ((n : ℝ) * R - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hM : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ M := by
    have hhalf : (2 : ℝ) ^ ((n : ℝ) * R - 1) = (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have h1M : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left 1 _
    have hleM : (⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℝ) ≤ M := Nat.cast_le.mpr (le_max_right 1 _)
    have hfloor := Nat.lt_floor_add_one ((2 : ℝ) ^ ((n : ℝ) * R))
    rw [hhalf]
    by_cases h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R)
    · linarith
    · push Not at h2
      linarith
  have h := Real.log_le_log hpow_pos hM
  rwa [Real.log_rpow (by norm_num)] at h

/-- Asymptotic rate extraction: if for every `δ ∈ (0, 1)` and all sufficiently large `n`,
    `(1 - δ) * ((n * R - c) * ln 2) ≤ n * K + 1`, then `R ≤ K / ln 2` (assuming `0 ≤ K`). -/
lemma rate_le_of_eventually_converse {R K c : ℝ} (hK0 : 0 ≤ K)
    (hconv : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ᶠ n : ℕ in atTop, (1 - δ) * (((n : ℝ) * R - c) * Real.log 2) ≤ (n : ℝ) * K + 1) :
    R ≤ K / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have step1 : ∀ δ : ℝ, 0 < δ → δ < 1 → (1 - δ) * R * Real.log 2 ≤ K := by
    intro δ hδ hδ1
    have hev : ∀ᶠ n : ℕ in atTop,
        (1 - δ) * R * Real.log 2 ≤ K + (1 + (1 - δ) * c * Real.log 2) * (1 / (n : ℝ)) := by
      filter_upwards [hconv δ hδ hδ1, eventually_ge_atTop (1 : ℕ)] with n hn hn1
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
      have hdiv : (1 - δ) * R * Real.log 2 =
          ((1 - δ) * (((n : ℝ) * R - c) * Real.log 2) + (1 - δ) * c * Real.log 2) / n := by
        field_simp
        ring
      rw [hdiv, div_le_iff₀ hnr]
      have hexp : (K + (1 + (1 - δ) * c * Real.log 2) * (1 / (n : ℝ))) * n =
          (n : ℝ) * K + 1 + (1 - δ) * c * Real.log 2 := by
        field_simp
        ring
      rw [hexp]
      linarith
    have hlim : Tendsto (fun n : ℕ => K + (1 + (1 - δ) * c * Real.log 2) * (1 / (n : ℝ))) atTop
        (𝓝 K) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat.const_mul
        (1 + (1 - δ) * c * Real.log 2)).const_add K
      simpa using h
    exact ge_of_tendsto hlim hev
  have hRK : R * Real.log 2 ≤ K := by
    by_contra hlt
    push Not at hlt
    have hRpos : 0 < R * Real.log 2 := lt_of_le_of_lt hK0 hlt
    set δ := (R * Real.log 2 - K) / (2 * (R * Real.log 2)) with hδ
    have hδpos : 0 < δ := div_pos (by linarith) (by linarith)
    have hδ1 : δ < 1 := by
      rw [hδ, div_lt_one (by linarith)]
      linarith
    have h := step1 δ hδpos hδ1
    have hR0 : R ≠ 0 := by
      rintro rfl
      simp at hRpos
    have hcalc : (1 - δ) * R * Real.log 2 = (R * Real.log 2 + K) / 2 := by
      rw [hδ]
      field_simp
      ring
    rw [hcalc] at h
    linarith
  rwa [le_div_iff₀ hlog2]

end MetaConverse

/-! ### 2. Strictly Causal Bijections and Measure Preservation -/

section CausalBijection

variable {E : Type*} [AddCommGroup E]

/-- Strict causality of a time-indexed drift `drift : Fin n → (Fin n → E) → E`:
    coordinate `i` depends only on strictly earlier coordinates `t < i`. -/
def IsStrictlyCausal {n : ℕ} (drift : Fin n → (Fin n → E) → E) : Prop :=
  ∀ (i : Fin n) (y y' : Fin n → E), (∀ t : Fin n, t < i → y t = y' t) → drift i y = drift i y'

/-- One pass of the causal channel equation `yᵢ = driftᵢ(y) + zᵢ`. -/
def causalStep {n : ℕ} (drift : Fin n → (Fin n → E) → E) (z y : Fin n → E) : Fin n → E :=
  fun i => drift i y + z i

/-- The causal output block obtained by `n` passes of `causalStep` starting from `z`. -/
def causalOutput {n : ℕ} (drift : Fin n → (Fin n → E) → E) (z : Fin n → E) : Fin n → E :=
  (causalStep drift z)^[n] z

/-- The exact inverse of `causalOutput`: recovers noise `zᵢ = yᵢ - driftᵢ(y)`. -/
def causalInverse {n : ℕ} (drift : Fin n → (Fin n → E) → E) (y : Fin n → E) : Fin n → E :=
  fun i => y i - drift i y

lemma causalStep_iterate_congr {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (z : Fin n → E) :
    ∀ (k : ℕ) (y y' : Fin n → E) (i : Fin n), i.1 < k →
      ((causalStep drift z)^[k] y) i = ((causalStep drift z)^[k] y') i
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, y, y', i, hi => by
    simp only [Function.iterate_succ_apply', causalStep]
    congr 1
    apply hcausal
    intro t ht
    exact causalStep_iterate_congr hcausal z k y y' t (Nat.lt_of_lt_of_le ht (Nat.lt_succ_iff.mp hi))

/-- `causalOutput` satisfies the causal channel equation `yᵢ = driftᵢ(y) + zᵢ`. -/
theorem causalOutput_eq {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (z : Fin n → E) (i : Fin n) :
    causalOutput drift z i = drift i (causalOutput drift z) + z i := by
  unfold causalOutput
  have h := causalStep_iterate_congr hcausal z n z (causalStep drift z z) i i.2
  rw [← Function.iterate_succ_apply (causalStep drift z) n z,
    Function.iterate_succ_apply' (causalStep drift z) n z] at h
  exact h

/-- Uniqueness of the fixed point of `causalStep drift z`. -/
theorem causalOutput_unique {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (z y : Fin n → E)
    (hy : ∀ i : Fin n, y i = drift i y + z i) :
    y = causalOutput drift z := by
  funext i
  suffices ∀ (k : ℕ) (j : Fin n), j.1 < k → y j = causalOutput drift z j from this n i i.2
  intro k
  induction k with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro j hj
    rw [hy j, causalOutput_eq hcausal z j]
    congr 1
    apply hcausal
    intro t ht
    exact ih t (Nat.lt_of_lt_of_le ht (Nat.lt_succ_iff.mp hj))

theorem causalInverse_causalOutput {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (z : Fin n → E) :
    causalInverse drift (causalOutput drift z) = z := by
  funext i
  simp only [causalInverse, causalOutput_eq hcausal z i, add_sub_cancel_left]

theorem causalOutput_causalInverse {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (y : Fin n → E) :
    causalOutput drift (causalInverse drift y) = y := by
  symm
  apply causalOutput_unique hcausal
  intro i
  simp only [causalInverse, add_sub_cancel]

/-- Strict causality in noise: the first `k` output symbols depend only on the first `k` noise
    symbols. -/
theorem causalOutput_congr_lt {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) {k : ℕ} {z z' : Fin n → E}
    (hz : ∀ t : Fin n, t.1 < k → z t = z' t) :
    ∀ t : Fin n, t.1 < k → causalOutput drift z t = causalOutput drift z' t := by
  suffices ∀ m : ℕ, m ≤ k → ∀ t : Fin n, t.1 < m → causalOutput drift z t = causalOutput drift z' t
    from this k le_rfl
  intro m
  induction m with
  | zero => intro _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ m ih =>
    intro hmk t ht
    rw [causalOutput_eq hcausal z t, causalOutput_eq hcausal z' t, hz t (lt_of_lt_of_le ht hmk)]
    congr 1
    apply hcausal
    intro s hs
    exact ih (Nat.le_of_succ_le hmk) s (Nat.lt_of_lt_of_le hs (Nat.lt_succ_iff.mp ht))

/-- `drift i (causalOutput drift z)` depends only on strictly earlier noise coordinates `t < i`. -/
theorem drift_causalOutput_congr_lt {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (i : Fin n) {z z' : Fin n → E}
    (hz : ∀ t : Fin n, t < i → z t = z' t) :
    drift i (causalOutput drift z) = drift i (causalOutput drift z') := by
  apply hcausal
  intro t ht
  exact causalOutput_congr_lt hcausal (k := i.1) (fun s hs => hz s hs) t ht

section Measurable

variable [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableNeg E]

omit [MeasurableNeg E] in
lemma measurable_causalOutput {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hmeas : ∀ i, Measurable (drift i)) :
    Measurable (causalOutput drift) := by
  unfold causalOutput
  suffices ∀ k : ℕ, Measurable (fun z : Fin n → E => (causalStep drift z)^[k] z) from this n
  intro k
  induction k with
  | zero => exact measurable_id
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    refine measurable_pi_iff.mpr (fun i => ?_)
    exact ((hmeas i).comp ih).add (measurable_pi_apply i)

lemma measurable_causalInverse {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hmeas : ∀ i, Measurable (drift i)) :
    Measurable (causalInverse drift) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact (measurable_pi_apply i).sub (hmeas i)

/-- The causal channel map as a `MeasurableEquiv`. -/
def causalEquiv {n : ℕ} {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (hmeas : ∀ i, Measurable (drift i)) :
    (Fin n → E) ≃ᵐ (Fin n → E) where
  toFun := causalOutput drift
  invFun := causalInverse drift
  left_inv := causalInverse_causalOutput hcausal
  right_inv := causalOutput_causalInverse hcausal
  measurable_toFun := measurable_causalOutput hmeas
  measurable_invFun := measurable_causalInverse hmeas

/-- A measurable shear `(t, u) ↦ (t - g u, u)` preserves `ν.prod μ` for any right-invariant
    σ-finite measure `ν` and s-finite measure `μ`. -/
lemma measurePreserving_shear_fst {α : Type*} [MeasurableSpace α]
    (ν : Measure E) [SigmaFinite ν] [ν.IsAddRightInvariant]
    (μ : Measure α) [SFinite μ]
    (g : α → E) (hg : Measurable g) :
    MeasurePreserving (fun p : E × α => (p.1 - g p.2, p.2)) (ν.prod μ) (ν.prod μ) := by
  have hf : Measurable (fun p : E × α => (p.1 - g p.2, p.2)) :=
    (measurable_fst.sub (hg.comp measurable_snd)).prodMk measurable_snd
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply_symm (hf hs), Measure.prod_apply_symm hs]
  refine lintegral_congr (fun u => ?_)
  have hpre : (fun t : E => (t, u)) ⁻¹' ((fun p : E × α => (p.1 - g p.2, p.2)) ⁻¹' s) =
      (fun t : E => t - g u) ⁻¹' ((fun t : E => (t, u)) ⁻¹' s) := by
    ext t; simp
  rw [hpre]
  exact (measurePreserving_sub_right ν (g u)).measure_preimage
    ((measurable_id.prodMk measurable_const) hs).nullMeasurableSet

/-- `causalInverse` preserves the product measure `Measure.pi (fun _ => ν)` for any
    right-invariant σ-finite measure `ν` (unit-Jacobian theorem for strictly causal maps). -/
theorem measurePreserving_causalInverse :
    ∀ {n : ℕ} (ν : Measure E) [SigmaFinite ν] [ν.IsAddRightInvariant]
      {drift : Fin n → (Fin n → E) → E},
      IsStrictlyCausal drift → (∀ i, Measurable (drift i)) →
      MeasurePreserving (causalInverse drift)
        (Measure.pi fun _ : Fin n => ν) (Measure.pi fun _ : Fin n => ν)
  | 0, ν, _, _, drift, _, _ => by
    have heq : causalInverse drift = id := by
      funext y i; exact i.elim0
    rw [heq]
    exact MeasurePreserving.id _
  | n + 1, ν, _, _, drift, hcausal, hmeas => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) (Fin.last n)
    have he : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n)
    let g : (Fin n → E) → E := fun u => drift (Fin.last n) (e.symm (0, u))
    let drift' : Fin n → (Fin n → E) → E := fun j u => drift j.castSucc (e.symm (0, u))
    have hg_meas : Measurable g :=
      (hmeas (Fin.last n)).comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
    have hdrift'_meas : ∀ j, Measurable (drift' j) := fun j =>
      (hmeas j.castSucc).comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
    have hdrift'_causal : IsStrictlyCausal drift' := by
      intro j u u' hu
      apply hcausal j.castSucc
      intro t ht
      have hne : t ≠ Fin.last n := ne_of_lt (lt_trans ht (Fin.castSucc_lt_last j))
      obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      have hkj : k < j := Fin.castSucc_lt_castSucc_iff.mp ht
      have h1' : e.symm (0, u) ((Fin.last n).succAbove k) = u k := by
        have := congrArg (fun p => p.2 k) (e.apply_symm_apply (0, u))
        simp [e] at this ⊢
      have h2' : e.symm (0, u') ((Fin.last n).succAbove k) = u' k := by
        have := congrArg (fun p => p.2 k) (e.apply_symm_apply (0, u'))
        simp [e] at this ⊢
      simp only [Fin.succAbove_last] at h1' h2'
      rw [h1', h2', hu k hkj]
    have hih := measurePreserving_causalInverse ν hdrift'_causal hdrift'_meas
    have hshear := measurePreserving_shear_fst ν (Measure.pi fun _ : Fin n => ν) g hg_meas
    have hprod : MeasurePreserving (Prod.map id (causalInverse drift'))
        (ν.prod (Measure.pi fun _ : Fin n => ν)) (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      (MeasurePreserving.id ν).prod hih
    have hcomp := he.symm.comp ((hprod.comp hshear).comp he)
    have hfun : (fun y => e.symm (Prod.map id (causalInverse drift')
        ((fun p : E × (Fin n → E) => (p.1 - g p.2, p.2)) (e y)))) = causalInverse drift := by
      funext y
      apply e.injective
      rw [e.apply_symm_apply]
      apply Prod.ext
      · change y (Fin.last n) - drift (Fin.last n) (e.symm (0, fun j => y ((Fin.last n).succAbove j))) =
            y (Fin.last n) - drift (Fin.last n) y
        congr 1
        apply hcausal (Fin.last n)
        intro t ht
        have hne : t ≠ Fin.last n := ne_of_lt ht
        obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
        have h1' : e.symm (0, fun j => y ((Fin.last n).succAbove j)) ((Fin.last n).succAbove k) =
            y ((Fin.last n).succAbove k) := by
          have := congrArg (fun p => p.2 k)
            (e.apply_symm_apply (0, fun j => y ((Fin.last n).succAbove j)))
          simp [e] at this ⊢
        simpa [Fin.succAbove_last] using h1'
      · funext j
        change y ((Fin.last n).succAbove j) -
            drift j.castSucc (e.symm (0, fun k => y ((Fin.last n).succAbove k))) =
            y ((Fin.last n).succAbove j) - drift ((Fin.last n).succAbove j) y
        simp only [Fin.succAbove_last]
        congr 1
        apply hcausal j.castSucc
        intro t ht
        have hne : t ≠ Fin.last n := ne_of_lt (lt_trans ht (Fin.castSucc_lt_last j))
        obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
        have h1' : e.symm (0, fun r => y ((Fin.last n).succAbove r)) ((Fin.last n).succAbove k) =
            y ((Fin.last n).succAbove k) := by
          have := congrArg (fun p => p.2 k)
            (e.apply_symm_apply (0, fun r => y ((Fin.last n).succAbove r)))
          simp [e] at this ⊢
        simpa [Fin.succAbove_last] using h1'
    have hcomp' : MeasurePreserving (fun y => e.symm (Prod.map id (causalInverse drift')
        ((fun p : E × (Fin n → E) => (p.1 - g p.2, p.2)) (e y))))
        (Measure.pi fun _ : Fin (n + 1) => ν) (Measure.pi fun _ : Fin (n + 1) => ν) := hcomp
    rwa [hfun] at hcomp'

/-- `causalOutput` preserves the product measure `Measure.pi (fun _ => ν)`. -/
theorem measurePreserving_causalOutput {n : ℕ} (ν : Measure E) [SigmaFinite ν]
    [ν.IsAddRightInvariant] {drift : Fin n → (Fin n → E) → E}
    (hcausal : IsStrictlyCausal drift) (hmeas : ∀ i, Measurable (drift i)) :
    MeasurePreserving (causalOutput drift)
      (Measure.pi fun _ : Fin n => ν) (Measure.pi fun _ : Fin n => ν) := by
  have hinv := measurePreserving_causalInverse ν hcausal hmeas
  exact MeasurePreserving.symm (causalEquiv hcausal hmeas).symm hinv

/-- Pushforward of `μ.withDensity f` along a measure-preserving measurable equivalence `e`
    is `ν.withDensity (f ∘ e.symm)`. -/
lemma map_withDensity_of_measurePreserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  rw [← he.symm.lintegral_comp (hf.indicator (e.measurable hs))]
  refine lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ s
  · have hmem : e.symm y ∈ e ⁻¹' s := by simp [hy]
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
  · have hmem : e.symm y ∉ e ⁻¹' s := by simp [hy]
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hmem]

end Measurable

/-- Specialization to Lebesgue measure `volume` on `Fin n → ℝ`:
    `Measure.map (causalOutput drift) volume = volume`. -/
theorem map_causalOutput_volume {n : ℕ} {drift : Fin n → (Fin n → ℝ) → ℝ}
    (hcausal : IsStrictlyCausal drift) (hmeas : ∀ i, Measurable (drift i)) :
    Measure.map (causalOutput drift) volume = volume :=
  (measurePreserving_causalOutput (volume : Measure ℝ) hcausal hmeas).map_eq

end CausalBijection

/-! ### 3. Gaussian Product Densities and Causal Orthogonality -/

section GaussianProduct

lemma toNNReal_ne_zero_of_pos' {v : ℝ} (hv : 0 < v) : v.toNNReal ≠ 0 := by
  simpa using hv

lemma prod_withDensity_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    [SigmaFinite (μ.withDensity f)] [SigmaFinite (ν.withDensity g)] :
    (μ.withDensity f).prod (ν.withDensity g) =
      (μ.prod ν).withDensity (fun p => f p.1 * g p.2) := by
  refine Measure.prod_eq (fun s t hs ht => ?_)
  rw [withDensity_apply _ hs, withDensity_apply _ ht, withDensity_apply _ (hs.prod ht),
    ← lintegral_indicator hs, ← lintegral_indicator ht, ← lintegral_indicator (hs.prod ht)]
  have hpt : ∀ p : α × β,
      (s ×ˢ t).indicator (fun p => f p.1 * g p.2) p =
        s.indicator f p.1 * t.indicator g p.2 := by
    intro ⟨a, b⟩
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;> simp [ha, hb]
  simp_rw [hpt]
  rw [lintegral_prod_mul (hf.indicator hs).aemeasurable (hg.indicator ht).aemeasurable]

/-- `awgnNoise n N` is `volume` with product Gaussian density. -/
theorem awgnNoise_eq_withDensity :
    ∀ (n : ℕ) {N : ℝ}, 0 < N →
      awgnNoise n N =
        volume.withDensity (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (z i))
  | 0, N, _ => by
    unfold awgnNoise
    have h1 : (fun z : Fin 0 → ℝ => ∏ i : Fin 0, gaussianPDF 0 N.toNNReal (z i)) = 1 := by
      funext z; simp
    rw [h1, withDensity_one]
    ext s _
    change Measure.pi (fun _ : Fin 0 => gaussianReal 0 N.toNNReal) s =
      Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) s
    by_cases hs : (Fin.elim0 : Fin 0 → ℝ) ∈ s
    · have hsu : s = Set.univ := by ext x; simp [Subsingleton.elim x Fin.elim0, hs]
      rw [hsu]
      simp
    · have hse : s = ∅ := by ext x; simp [Subsingleton.elim x Fin.elim0, hs]
      rw [hse]
      simp
  | n + 1, N, hN => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have h1 : MeasurePreserving e (awgnNoise (n + 1) N)
        ((gaussianReal 0 N.toNNReal).prod (awgnNoise n N)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 N.toNNReal) 0
    have h2 : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hih := awgnNoise_eq_withDensity n hN
    have hg0 : gaussianReal 0 N.toNNReal = volume.withDensity (gaussianPDF 0 N.toNNReal) :=
      gaussianReal_of_var_ne_zero 0 (toNNReal_ne_zero_of_pos' hN)
    have hmf1 : Measurable (gaussianPDF 0 N.toNNReal) := measurable_gaussianPDF 0 N.toNNReal
    have hmf2 : Measurable (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (z i)) :=
      Finset.measurable_prod _ (fun i _ => hmf1.comp (measurable_pi_apply i))
    have hsf1 : SigmaFinite (volume.withDensity (gaussianPDF 0 N.toNNReal)) := by
      rw [← hg0]; infer_instance
    have hsf2 : SigmaFinite (volume.withDensity
        (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (z i))) := by
      rw [← hih]; unfold awgnNoise; infer_instance
    have hprod : (gaussianReal 0 N.toNNReal).prod (awgnNoise n N) =
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).withDensity
          (fun p => gaussianPDF 0 N.toNNReal p.1 *
            ∏ i : Fin n, gaussianPDF 0 N.toNNReal (p.2 i)) := by
      rw [hg0, hih]
      exact prod_withDensity_eq volume volume hmf1 hmf2
    have hpush := map_withDensity_of_measurePreserving e.symm h2.symm
      (f := fun p : ℝ × (Fin n → ℝ) => gaussianPDF 0 N.toNNReal p.1 *
        ∏ i : Fin n, gaussianPDF 0 N.toNNReal (p.2 i))
      ((hmf1.comp measurable_fst).mul (hmf2.comp measurable_snd))
    rw [← hprod, ← h1.map_eq, Measure.map_map e.symm.measurable e.measurable] at hpush
    simp only [MeasurableEquiv.symm_comp_self, Measure.map_id] at hpush
    rw [hpush]
    congr 1
    funext z
    rw [Fin.prod_univ_succ]
    simp [e, Fin.insertNthEquiv, Fin.tail]

lemma gaussianPDF_eq_ofReal_gaussianPdf1D {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    gaussianPDF 0 N.toNNReal t = ENNReal.ofReal (gaussianPdf1D N t) := by
  rw [gaussianPDF_def, gaussianPdf1D_eq_gaussianPDFReal hN]
  have h : (⟨N, hN⟩ : ℝ≥0) = N.toNNReal := by ext; simp [hN]
  rw [h]

theorem awgnNoise_eq_withDensity_gaussianPdf1D {n : ℕ} {N : ℝ} (hN : 0 < N) :
    awgnNoise n N =
      volume.withDensity (fun z : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (z i))) := by
  rw [awgnNoise_eq_withDensity n hN]
  congr 1
  funext z
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPdf1D_nonneg hN.le (z i))]
  refine Finset.prod_congr rfl (fun i _ => gaussianPDF_eq_ofReal_gaussianPdf1D hN.le (z i))

/-- Rewriting `∫⁻ z, f z ∂(awgnNoise n N)` as a Lebesgue integral with `∏ i, gaussianPdf1D N (z i)`. -/
theorem lintegral_awgnNoise_eq_volume {n : ℕ} {N : ℝ} (hN : 0 < N)
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(awgnNoise n N) =
      ∫⁻ z, ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (z i)) * f z ∂volume := by
  rw [awgnNoise_eq_withDensity_gaussianPdf1D hN]
  have hd : Measurable (fun z : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (z i))) := by
    have h : (fun z : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (z i))) =
        fun z => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (z i) := by
      funext z
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPdf1D_nonneg hN.le (z i))]
      exact Finset.prod_congr rfl (fun i _ => (gaussianPDF_eq_ofReal_gaussianPdf1D hN.le (z i)).symm)
    rw [h]
    exact Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N.toNNReal).comp (measurable_pi_apply i))
  exact lintegral_withDensity_eq_lintegral_mul volume hd hf

/-- Change-of-variables formula for `causalOutput` under `awgnNoise`:
    `∫⁻ z, f (causalOutput drift z) ∂(awgnNoise n N) = ∫⁻ y, f y * ofReal (∏ i, φ_N(y_i - drift_i(y))) ∂volume`. -/
theorem lintegral_causalOutput_awgnNoise {n : ℕ} {N : ℝ} (hN : 0 < N)
    {drift : Fin n → (Fin n → ℝ) → ℝ}
    (hcausal : IsStrictlyCausal drift) (hmeas : ∀ i, Measurable (drift i))
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f (causalOutput drift z) ∂(awgnNoise n N) =
      ∫⁻ y, f y * ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (y i - drift i y)) ∂volume := by
  have he : MeasurePreserving (causalEquiv hcausal hmeas) volume volume :=
    measurePreserving_causalOutput (volume : Measure ℝ) hcausal hmeas
  have hpdf : Measurable (fun z : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (z i))) := by
    have h : (fun z : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (z i))) =
        fun z => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (z i) := by
      funext z
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPdf1D_nonneg hN.le (z i))]
      exact Finset.prod_congr rfl (fun i _ => (gaussianPDF_eq_ofReal_gaussianPdf1D hN.le (z i)).symm)
    rw [h]
    exact Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N.toNNReal).comp (measurable_pi_apply i))
  have hmap : (awgnNoise n N).map (causalOutput drift) =
      volume.withDensity (fun y => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (y i - drift i y))) := by
    rw [awgnNoise_eq_withDensity_gaussianPdf1D hN]
    exact map_withDensity_of_measurePreserving (causalEquiv hcausal hmeas) he hpdf
  rw [← lintegral_map hf (measurable_causalOutput hmeas), hmap,
    lintegral_withDensity_eq_lintegral_mul volume
      (f := fun y => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D N (y i - drift i y)))
      (hpdf.comp (measurable_causalInverse hmeas)) hf]
  refine lintegral_congr (fun y => mul_comm _ _)

instance instIsProbabilityMeasureAwgnNoise (n : ℕ) (N : ℝ) :
    IsProbabilityMeasure (awgnNoise n N) := by
  unfold awgnNoise; infer_instance

lemma integrable_sq_coord_awgnNoise {n : ℕ} (N : ℝ) (i : Fin n) :
    Integrable (fun z : Fin n → ℝ => (z i) ^ 2) (awgnNoise n N) := by
  unfold awgnNoise
  have h1 : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 N.toNNReal) :=
    (memLp_id_gaussianReal 2).integrable_sq
  exact integrable_comp_eval (μ := fun _ : Fin n => gaussianReal 0 N.toNNReal) h1

lemma integral_sq_coord_awgnNoise {n : ℕ} {N : ℝ} (hN : 0 ≤ N) (i : Fin n) :
    ∫ z : Fin n → ℝ, (z i) ^ 2 ∂(awgnNoise n N) = N := by
  unfold awgnNoise
  rw [integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 N.toNNReal)
    (f := fun t : ℝ => t ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable]
  have hvar : Var[fun t : ℝ => t; gaussianReal 0 N.toNNReal] = (N.toNNReal : ℝ) :=
    variance_fun_id_gaussianReal
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  simpa [Real.coe_toNNReal _ hN] using hvar

/-- **Causal orthogonality (1D)**: if `f : (Fin n → ℝ) → ℝ` is measurable, does not depend on
    coordinate `i`, and has finite second moment under `awgnNoise n N`, then `f z * z i` is
    integrable with expectation `0`. -/
theorem integral_mul_coord_eq_zero_of_indep_coord :
    ∀ {n : ℕ} {N : ℝ} (i : Fin n) (f : (Fin n → ℝ) → ℝ),
      Measurable f →
      (∀ z z' : Fin n → ℝ, (∀ s : Fin n, s ≠ i → z s = z' s) → f z = f z') →
      Integrable (fun z => f z ^ 2) (awgnNoise n N) →
      Integrable (fun z => f z * z i) (awgnNoise n N) ∧
        ∫ z, f z * z i ∂(awgnNoise n N) = 0
  | 0, _, i, _, _, _, _ => i.elim0
  | n + 1, N, i, f, hf_meas, hf_indep, hf_sq => by
    have hprod_int : Integrable (fun z : Fin (n + 1) → ℝ => f z * z i) (awgnNoise (n + 1) N) := by
      have hdom : Integrable (fun z : Fin (n + 1) → ℝ => (f z ^ 2 + (z i) ^ 2) / 2)
          (awgnNoise (n + 1) N) :=
        (hf_sq.add (integrable_sq_coord_awgnNoise N i)).div_const 2
      refine hdom.mono' (hf_meas.mul (measurable_pi_apply i)).aestronglyMeasurable
        (ae_of_all _ (fun z => ?_))
      rw [Real.norm_eq_abs]
      have h1 : 0 ≤ (|f z| - |z i|) ^ 2 := sq_nonneg _
      have h2 : |f z * z i| = |f z| * |z i| := abs_mul _ _
      rw [h2]
      nlinarith [sq_abs (f z), sq_abs (z i)]
    refine ⟨hprod_int, ?_⟩
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    have he : MeasurePreserving e (awgnNoise (n + 1) N)
        ((gaussianReal 0 N.toNNReal).prod (awgnNoise n N)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 N.toNNReal) i
    rw [← he.symm.integral_comp' (g := fun z => f z * z i)]
    have hrewrite : ∀ p : ℝ × (Fin n → ℝ),
        f (e.symm p) * (e.symm p) i = p.1 * f (e.symm (0, p.2)) := by
      intro ⟨t, u⟩
      have hi : (e.symm (t, u)) i = t := by
        have := congrArg Prod.fst (e.apply_symm_apply (t, u))
        simp [e] at this ⊢
      have hfeq : f (e.symm (t, u)) = f (e.symm (0, u)) := by
        apply hf_indep
        intro s hs
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hs
        have h1 := congrArg (fun p => p.2 k) (e.apply_symm_apply (t, u))
        have h2 := congrArg (fun p => p.2 k) (e.apply_symm_apply (0, u))
        simp [e] at h1 h2 ⊢
      rw [hi, hfeq, mul_comm]
    simp_rw [hrewrite]
    rw [integral_prod_mul (f := fun t : ℝ => t) (g := fun u : Fin n → ℝ => f (e.symm (0, u))),
      integral_id_gaussianReal, zero_mul]

/-- **Causal orthogonality (2D, first noise coordinate)**: if `f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ`
    is measurable, independent of `z.1 i`, and square-integrable under
    `(awgnNoise n N₁).prod (awgnNoise n N₂)`, then `f z * z.1 i` is integrable with integral `0`. -/
theorem integral_mul_fst_coord_eq_zero_of_indep_coord {n : ℕ} {N₁ N₂ : ℝ} (i : Fin n)
    (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hf_meas : Measurable f)
    (hf_indep : ∀ p q : (Fin n → ℝ) × (Fin n → ℝ),
      p.2 = q.2 → (∀ s : Fin n, s ≠ i → p.1 s = q.1 s) → f p = f q)
    (hf_sq : Integrable (fun p => f p ^ 2) ((awgnNoise n N₁).prod (awgnNoise n N₂))) :
    Integrable (fun p => f p * p.1 i) ((awgnNoise n N₁).prod (awgnNoise n N₂)) ∧
      ∫ p, f p * p.1 i ∂((awgnNoise n N₁).prod (awgnNoise n N₂)) = 0 := by
  have hz1_sq : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 i) ^ 2)
      ((awgnNoise n N₁).prod (awgnNoise n N₂)) :=
    (integrable_sq_coord_awgnNoise N₁ i).comp_fst (awgnNoise n N₂)
  have hprod_int : Integrable (fun p => f p * p.1 i) ((awgnNoise n N₁).prod (awgnNoise n N₂)) := by
    have hdom := (hf_sq.add hz1_sq).div_const 2
    refine hdom.mono' (hf_meas.mul ((measurable_pi_apply i).comp measurable_fst)).aestronglyMeasurable
      (ae_of_all _ (fun p => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (|f p| - |p.1 i|), sq_abs (f p), sq_abs (p.1 i)]
  refine ⟨hprod_int, ?_⟩
  rw [integral_prod_symm _ hprod_int]
  have hae : ∀ᵐ z₂ ∂(awgnNoise n N₂), Integrable (fun z₁ => f (z₁, z₂) ^ 2) (awgnNoise n N₁) :=
    hf_sq.prod_left_ae
  have hzero : (fun z₂ => ∫ z₁, f (z₁, z₂) * z₁ i ∂(awgnNoise n N₁)) =ᵐ[awgnNoise n N₂] 0 := by
    filter_upwards [hae] with z₂ hz₂
    have h1 := integral_mul_coord_eq_zero_of_indep_coord i (fun z₁ => f (z₁, z₂))
      (hf_meas.comp (measurable_id.prodMk measurable_const))
      (fun z₁ z₁' h => hf_indep (z₁, z₂) (z₁', z₂) rfl h) hz₂
    exact h1.2
  rw [integral_congr_ae hzero]
  exact integral_zero _ _

/-- **Causal orthogonality (2D, second noise coordinate)**. -/
theorem integral_mul_snd_coord_eq_zero_of_indep_coord {n : ℕ} {N₁ N₂ : ℝ} (i : Fin n)
    (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hf_meas : Measurable f)
    (hf_indep : ∀ p q : (Fin n → ℝ) × (Fin n → ℝ),
      p.1 = q.1 → (∀ s : Fin n, s ≠ i → p.2 s = q.2 s) → f p = f q)
    (hf_sq : Integrable (fun p => f p ^ 2) ((awgnNoise n N₁).prod (awgnNoise n N₂))) :
    Integrable (fun p => f p * p.2 i) ((awgnNoise n N₁).prod (awgnNoise n N₂)) ∧
      ∫ p, f p * p.2 i ∂((awgnNoise n N₁).prod (awgnNoise n N₂)) = 0 := by
  have hswap := Measure.measurePreserving_swap (μ := awgnNoise n N₁) (ν := awgnNoise n N₂)
  have hswap' := Measure.measurePreserving_swap (μ := awgnNoise n N₂) (ν := awgnNoise n N₁)
  have hf_sq' : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.swap ^ 2)
      ((awgnNoise n N₂).prod (awgnNoise n N₁)) :=
    (hswap'.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hf_sq
  have hres := integral_mul_fst_coord_eq_zero_of_indep_coord i (fun p => f p.swap)
    (hf_meas.comp measurable_swap)
    (fun p q h1 h2 => hf_indep p.swap q.swap h1 h2) hf_sq'
  refine ⟨?_, ?_⟩
  · have h := (hswap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hres.1
    simpa [Function.comp_def, Prod.swap] using h
  · have h := hswap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.swap * p.1 i)
    simpa [Function.comp_def, Prod.swap] using h.trans hres.2

/-- Extracting `Integrable (fun z => f z ^ 2)` from a finite `lintegral` of `ofReal (∑ (f i z)^2)`. -/
lemma integrable_sq_of_lintegral_sum_sq_lt_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} {f : Fin n → Ω → ℝ} (hmeas : ∀ i, Measurable (f i))
    (hlt : ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (f i z) ^ 2) ∂μ < ⊤) (i : Fin n) :
    Integrable (fun z => (f i z) ^ 2) μ := by
  have hle : ∫⁻ z, ENNReal.ofReal ((f i z) ^ 2) ∂μ ≤
      ∫⁻ z, ENNReal.ofReal (∑ j : Fin n, (f j z) ^ 2) ∂μ :=
    lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
      (Finset.single_le_sum (fun j _ => sq_nonneg (f j z)) (Finset.mem_univ i)))
  have hne : ∫⁻ z, ENNReal.ofReal ((f i z) ^ 2) ∂μ ≠ ⊤ := (lt_of_le_of_lt hle hlt).ne
  have hint := integrable_toReal_of_lintegral_ne_top
    ((hmeas i).pow_const 2).ennreal_ofReal.aemeasurable hne
  exact hint.congr (ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _)))

lemma integral_sum_sq_eq_toReal_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} {f : Fin n → Ω → ℝ} (hmeas : ∀ i, Measurable (f i)) :
    (∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (f i z) ^ 2) ∂μ).toReal =
      ∫ z, (∑ i : Fin n, (f i z) ^ 2) ∂μ := by
  have hm : Measurable (fun z => ∑ i : Fin n, (f i z) ^ 2) :=
    Finset.measurable_sum _ (fun i _ => (hmeas i).pow_const 2)
  rw [← integral_toReal hm.ennreal_ofReal.aemeasurable (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  exact integral_congr_ae (ae_of_all _ (fun z =>
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => sq_nonneg _))))

end GaussianProduct

/-! ### 4. 1D Strictly Causal Vector-AWGN Feedback Converse -/

section Causal1DConverse

/-- Causal block log-likelihood ratio between `P = map (causalOutput drift) (awgnNoise n N)`
    and `Q = awgnNoise n V`: `L(y) = ∑ᵢ (½ ln(V/N) - (yᵢ - driftᵢ(y))²/(2N) + yᵢ²/(2V))`. -/
noncomputable def causalBlockLLR {n : ℕ} (N V : ℝ) (drift : Fin n → (Fin n → ℝ) → ℝ)
    (y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ((1 / 2 : ℝ) * Real.log (V / N) - (y i - drift i y) ^ 2 / (2 * N) +
    (y i) ^ 2 / (2 * V))

lemma measurable_causalBlockLLR {n : ℕ} (N V : ℝ) {drift : Fin n → (Fin n → ℝ) → ℝ}
    (hmeas : ∀ i, Measurable (drift i)) :
    Measurable (causalBlockLLR N V drift) := by
  unfold causalBlockLLR
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact ((measurable_const.sub (((measurable_pi_apply i).sub (hmeas i)).pow_const 2 |>.div_const _)).add
    (((measurable_pi_apply i).pow_const 2).div_const _))

lemma awgnNoise_eq_withDensity_causalBlockLLR {n : ℕ} {N V : ℝ} (hN : 0 < N) (hV : 0 < V)
    {drift : Fin n → (Fin n → ℝ) → ℝ}
    (hcausal : IsStrictlyCausal drift) (hmeas : ∀ i, Measurable (drift i)) :
    awgnNoise n V =
      ((awgnNoise n N).map (causalOutput drift)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-causalBlockLLR N V drift y))) := by
  have he : MeasurePreserving (causalEquiv hcausal hmeas) volume volume :=
    measurePreserving_causalOutput (volume : Measure ℝ) hcausal hmeas
  have hpdfN : Measurable (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (z i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N.toNNReal).comp (measurable_pi_apply i))
  have hP : (awgnNoise n N).map (causalOutput drift) =
      volume.withDensity (fun y => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (y i - drift i y)) := by
    rw [awgnNoise_eq_withDensity n hN]
    exact map_withDensity_of_measurePreserving (causalEquiv hcausal hmeas) he hpdfN
  rw [hP, ← withDensity_mul volume
      (f := fun y => ∏ i : Fin n, gaussianPDF 0 N.toNNReal (y i - drift i y))
      (g := fun y => ENNReal.ofReal (Real.exp (-causalBlockLLR N V drift y)))
      (hpdfN.comp (measurable_causalInverse hmeas))
      ((measurable_causalBlockLLR N V hmeas).neg.exp.ennreal_ofReal),
    awgnNoise_eq_withDensity n hV]
  congr 1
  funext y
  simp only [Pi.mul_apply, causalBlockLLR, ← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gaussianPDF_eq_ofReal_gaussianPdf1D hV.le, gaussianPDF_eq_ofReal_gaussianPdf1D hN.le,
    ← ENNReal.ofReal_mul (gaussianPdf1D_nonneg hN.le _)]
  congr 1
  have hpos1 : 0 < gaussianPdf1D N (y i - drift i y) := gaussianPdf1D_pos hN _
  have hpos2 : 0 < gaussianPdf1D V (y i) := gaussianPdf1D_pos hV _
  have hlog : Real.log (gaussianPdf1D N (y i - drift i y) *
      Real.exp (-((1 / 2 : ℝ) * Real.log (V / N) - (y i - drift i y) ^ 2 / (2 * N) +
        (y i) ^ 2 / (2 * V)))) = Real.log (gaussianPdf1D V (y i)) := by
    rw [Real.log_mul hpos1.ne' (Real.exp_pos _).ne', Real.log_exp,
      log_gaussianPdf1D hN, log_gaussianPdf1D hV, Real.log_div hV.ne' hN.ne',
      Real.log_mul (by positivity) hN.ne', Real.log_mul (by positivity) hV.ne']
    ring
  exact (Real.log_injOn_pos (mul_pos hpos1 (Real.exp_pos _)) hpos2 hlog).symm

/-- Expected causal block LLR under `P = map (causalOutput drift) (awgnNoise n N)`:
    equals `n * (½ ln(V/N) - ½) + (E[∑ drift_i(Y)²] + n N) / (2 V)`. -/
lemma integrable_and_integral_causalBlockLLR {n : ℕ} {N V : ℝ} (hN : 0 < N) (hV : 0 < V)
    {drift : Fin n → (Fin n → ℝ) → ℝ}
    (hcausal : IsStrictlyCausal drift) (hmeas : ∀ i, Measurable (drift i))
    (henergy : ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift i (causalOutput drift z)) ^ 2)
        ∂(awgnNoise n N) < ⊤) :
    Integrable (causalBlockLLR N V drift) ((awgnNoise n N).map (causalOutput drift)) ∧
      ∫ y, causalBlockLLR N V drift y ∂((awgnNoise n N).map (causalOutput drift)) =
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log (V / N) - 1 / 2) +
          ((∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift i (causalOutput drift z)) ^ 2)
              ∂(awgnNoise n N)).toReal + (n : ℝ) * N) / (2 * V) := by
  let X : Fin n → (Fin n → ℝ) → ℝ := fun i z => drift i (causalOutput drift z)
  have hXmeas : ∀ i, Measurable (X i) := fun i => (hmeas i).comp (measurable_causalOutput hmeas)
  have hXsq : ∀ i, Integrable (fun z => (X i z) ^ 2) (awgnNoise n N) :=
    integrable_sq_of_lintegral_sum_sq_lt_top hXmeas henergy
  have hXcross : ∀ i, Integrable (fun z => X i z * z i) (awgnNoise n N) ∧
      ∫ z, X i z * z i ∂(awgnNoise n N) = 0 := fun i =>
    integral_mul_coord_eq_zero_of_indep_coord i (X i) (hXmeas i)
      (fun z z' h => drift_causalOutput_congr_lt hcausal i (fun t ht => h t (ne_of_lt ht)))
      (hXsq i)
  have hcomp : ∀ z, causalBlockLLR N V drift (causalOutput drift z) =
      ∑ i : Fin n, (((1 / 2 : ℝ) * Real.log (V / N) - (z i) ^ 2 / (2 * N)) +
        ((X i z) ^ 2 / (2 * V) + (2 / (2 * V)) * (X i z * z i) + (z i) ^ 2 / (2 * V))) := by
    intro z
    unfold causalBlockLLR
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have heq := causalOutput_eq hcausal z i
    change _ = _
    rw [heq]
    have hsub : drift i (causalOutput drift z) + z i - drift i (causalOutput drift z) = z i :=
      add_sub_cancel_left _ _
    rw [hsub]
    dsimp only [X]
    ring
  have hterm_int : ∀ i : Fin n, Integrable (fun z =>
      ((1 / 2 : ℝ) * Real.log (V / N) - (z i) ^ 2 / (2 * N)) +
        ((X i z) ^ 2 / (2 * V) + (2 / (2 * V)) * (X i z * z i) + (z i) ^ 2 / (2 * V)))
      (awgnNoise n N) := fun i =>
    ((integrable_const _).sub ((integrable_sq_coord_awgnNoise N i).div_const _)).add
      ((((hXsq i).div_const _).add ((hXcross i).1.const_mul _)).add
        ((integrable_sq_coord_awgnNoise N i).div_const _))
  have hint_z : Integrable (fun z => causalBlockLLR N V drift (causalOutput drift z))
      (awgnNoise n N) := by
    simpa only [hcomp] using integrable_finsetSum Finset.univ (fun i _ => hterm_int i)
  have hint_y : Integrable (causalBlockLLR N V drift) ((awgnNoise n N).map (causalOutput drift)) :=
    (integrable_map_measure (measurable_causalBlockLLR N V hmeas).aestronglyMeasurable
      (measurable_causalOutput hmeas).aemeasurable).mpr hint_z
  refine ⟨hint_y, ?_⟩
  rw [integral_map (measurable_causalOutput hmeas).aemeasurable
    (measurable_causalBlockLLR N V hmeas).aestronglyMeasurable]
  simp_rw [hcomp]
  rw [integral_finsetSum Finset.univ (fun i _ => hterm_int i)]
  have hterm_val : ∀ i : Fin n,
      ∫ z, (((1 / 2 : ℝ) * Real.log (V / N) - (z i) ^ 2 / (2 * N)) +
        ((X i z) ^ 2 / (2 * V) + (2 / (2 * V)) * (X i z * z i) + (z i) ^ 2 / (2 * V)))
        ∂(awgnNoise n N) =
      ((1 / 2 : ℝ) * Real.log (V / N) - 1 / 2) +
        ((∫ z, (X i z) ^ 2 ∂(awgnNoise n N)) + N) / (2 * V) := by
    intro i
    have ha1 : Integrable (fun _ : Fin n → ℝ => (1 / 2 : ℝ) * Real.log (V / N)) (awgnNoise n N) :=
      integrable_const _
    have ha2 : Integrable (fun z : Fin n → ℝ => (z i) ^ 2 / (2 * N)) (awgnNoise n N) :=
      (integrable_sq_coord_awgnNoise N i).div_const _
    have hb1 : Integrable (fun z : Fin n → ℝ => (X i z) ^ 2 / (2 * V)) (awgnNoise n N) :=
      (hXsq i).div_const _
    have hb2 : Integrable (fun z : Fin n → ℝ => (2 / (2 * V)) * (X i z * z i)) (awgnNoise n N) :=
      (hXcross i).1.const_mul _
    have hb3 : Integrable (fun z : Fin n → ℝ => (z i) ^ 2 / (2 * V)) (awgnNoise n N) :=
      (integrable_sq_coord_awgnNoise N i).div_const _
    have ha : Integrable (fun z : Fin n → ℝ => (1 / 2 : ℝ) * Real.log (V / N) - (z i) ^ 2 / (2 * N))
        (awgnNoise n N) := ha1.sub ha2
    have hb12 : Integrable (fun z : Fin n → ℝ => (X i z) ^ 2 / (2 * V) + (2 / (2 * V)) * (X i z * z i))
        (awgnNoise n N) := hb1.add hb2
    have hb : Integrable (fun z : Fin n → ℝ =>
        (X i z) ^ 2 / (2 * V) + (2 / (2 * V)) * (X i z * z i) + (z i) ^ 2 / (2 * V))
        (awgnNoise n N) := hb12.add hb3
    rw [integral_add ha hb, integral_sub ha1 ha2, integral_add hb12 hb3, integral_add hb1 hb2,
      integral_const, integral_div, integral_div, integral_div, integral_const_mul,
      integral_sq_coord_awgnNoise hN.le i, (hXcross i).2]
    simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
    have hNne : N ≠ 0 := hN.ne'
    have hVne : V ≠ 0 := hV.ne'
    field_simp
  simp_rw [hterm_val]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← integral_finsetSum Finset.univ (fun i _ => hXsq i),
    ← integral_sum_sq_eq_toReal_lintegral hXmeas]

/-- **1D Strictly Causal Vector-AWGN Feedback Converse (finite blocklength, nats)**:
    for any nonempty finite message set `ι`, noise variance `N > 0`, energy budget `S ≥ 0`,
    strictly causal measurable drift `drift : ι → Fin n → (Fin n → ℝ) → ℝ`, and measurable
    decoder `dec : (Fin n → ℝ) → ι` with average drift energy `≤ n S`:
    `(1 - avgErr.toReal) * ln |ι| ≤ (n / 2) * ln (1 + S / N) + 1`. -/
theorem causal_awgn_feedback_code_converse {n : ℕ} {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) (hcard : 1 ≤ Fintype.card ι)
    (drift : ι → Fin n → (Fin n → ℝ) → ℝ)
    (hcausal : ∀ m, IsStrictlyCausal (drift m))
    (hmeas : ∀ m i, Measurable (drift m i))
    (dec : (Fin n → ℝ) → ι) (hdec : Measurable dec)
    (henergy : (Fintype.card ι : ℝ≥0∞)⁻¹ *
        ∑ m : ι, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift m i (causalOutput (drift m) z)) ^ 2) ∂(awgnNoise n N) ≤
      ENNReal.ofReal ((n : ℝ) * S)) :
    let avgErr : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)⁻¹ *
      ∑ m : ι, awgnNoise n N {z | dec (causalOutput (drift m) z) ≠ m}
    (1 - avgErr.toReal) * Real.log (Fintype.card ι : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N)) + 1 := by
  intro avgErr
  set M : ℕ := Fintype.card ι with hM_def
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hcard
  have hV : 0 < S + N := by linarith
  set P : ι → Measure (Fin n → ℝ) := fun m => (awgnNoise n N).map (causalOutput (drift m))
  have hPprob : ∀ m, IsProbabilityMeasure (P m) := fun m =>
    ⟨by rw [Measure.map_apply (measurable_causalOutput (hmeas m)) MeasurableSet.univ,
        Set.preimage_univ, measure_univ]⟩
  have hEm_lt_top : ∀ m : ι,
      ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift m i (causalOutput (drift m) z)) ^ 2)
        ∂(awgnNoise n N) < ⊤ := by
    intro m
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have hsum_top : ∑ m' : ι, ∫⁻ z, ENNReal.ofReal
        (∑ i : Fin n, (drift m' i (causalOutput (drift m') z)) ^ 2) ∂(awgnNoise n N) = ⊤ :=
      top_unique (htop ▸ Finset.single_le_sum
        (f := fun m' : ι => ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift m' i (causalOutput (drift m') z)) ^ 2) ∂(awgnNoise n N))
        (fun _ _ => bot_le) (Finset.mem_univ m))
    rw [hsum_top, ENNReal.mul_top] at henergy
    · exact ENNReal.ofReal_lt_top.not_ge henergy
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
  have hLLR := fun m => integrable_and_integral_causalBlockLLR hN hV (hcausal m) (hmeas m)
    (hEm_lt_top m)
  have hmeta := meta_converse_avg_error hcard P (awgnNoise n (S + N)) dec hdec
    (fun m => causalBlockLLR N (S + N) (drift m))
    (fun m => measurable_causalBlockLLR N (S + N) (hmeas m))
    (fun m => (hLLR m).1)
    (fun m => awgnNoise_eq_withDensity_causalBlockLLR hN hV (hcausal m) (hmeas m))
  have herr_eq : (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ m : ι, P m {y | dec y ≠ m} = avgErr := by
    simp only [avgErr, P]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hs : MeasurableSet {y : Fin n → ℝ | dec y ≠ m} := (hdec (measurableSet_singleton m)).compl
    rw [Measure.map_apply (measurable_causalOutput (hmeas m)) hs]
    rfl
  rw [herr_eq] at hmeta
  have havgE : (1 / (M : ℝ)) * ∑ m : ι, (∫⁻ z, ENNReal.ofReal
      (∑ i : Fin n, (drift m i (causalOutput (drift m) z)) ^ 2) ∂(awgnNoise n N)).toReal ≤
      (n : ℝ) * S := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) henergy
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ => (hEm_lt_top m).ne), ← one_div] at h1
    exact h1
  have hsum_LLR : (1 / (M : ℝ)) * ∑ m : ι, ∫ y, causalBlockLLR N (S + N) (drift m) y ∂(P m) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N)) := by
    dsimp only [P]
    simp_rw [fun m => (hLLR m).2]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hlog : Real.log ((S + N) / N) = Real.log (1 + S / N) := by
      congr 1; field_simp; ring
    rw [hlog]
    have hrw : (1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N) - 1 / 2)) +
        (∑ m : ι, (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
          (drift m i (causalOutput (drift m) z)) ^ 2) ∂(awgnNoise n N)).toReal +
          (M : ℝ) * ((n : ℝ) * N)) / (2 * (S + N))) =
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N) - 1 / 2) +
          ((1 / (M : ℝ)) * ∑ m : ι, (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
            (drift m i (causalOutput (drift m) z)) ^ 2) ∂(awgnNoise n N)).toReal +
            (n : ℝ) * N) / (2 * (S + N)) := by
      field_simp
    rw [hrw]
    have hdiv : ((1 / (M : ℝ)) * ∑ m : ι, (∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
        (drift m i (causalOutput (drift m) z)) ^ 2) ∂(awgnNoise n N)).toReal +
        (n : ℝ) * N) / (2 * (S + N)) ≤ (n : ℝ) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  linarith

/-- **1D Strictly Causal Vector-AWGN Feedback Rate Converse (asymptotic)**:
    if a sequence of strictly causal feedback codes at rate `R` with average drift energy `≤ n S`
    and noise variance `N > 0` has vanishing average error, then `R ≤ ½ log₂(1 + S / N)`. -/
theorem causal_awgn_feedback_rate_le {N S R : ℝ} (hN : 0 < N) (hS : 0 ≤ S)
    (hach : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
      ∃ (drift : Fin M → Fin n → (Fin n → ℝ) → ℝ) (dec : (Fin n → ℝ) → Fin M),
        (∀ m, IsStrictlyCausal (drift m)) ∧
        (∀ m i, Measurable (drift m i)) ∧
        Measurable dec ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift m i (causalOutput (drift m) z)) ^ 2) ∂(awgnNoise n N) ≤
            ENNReal.ofReal ((n : ℝ) * S)) ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
          awgnNoise n N {z | dec (causalOutput (drift m) z) ≠ m} ≤ ENNReal.ofReal δ)) :
    R ≤ (1 / 2 : ℝ) * log2 (1 + S / N) := by
  set K := (1 / 2 : ℝ) * Real.log (1 + S / N) with hK
  have hK0 : 0 ≤ K := by
    have : 1 ≤ 1 + S / N := by linarith [div_nonneg hS hN.le]
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  have hrate := rate_le_of_eventually_converse (R := R) (K := K) (c := 1) hK0 (fun δ hδ hδ1 => ?_)
  · unfold log2; rw [hK] at hrate; linarith [mul_div_assoc (1 / 2 : ℝ) (Real.log (1 + S / N)) (Real.log 2)]
  · obtain ⟨n₀, hn₀⟩ := hach δ hδ
    refine eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    set M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
    obtain ⟨drift, dec, hcausal, hmeas, hdec, henergy, herr⟩ := hn₀ n hn
    have hM : 1 ≤ M := le_max_left 1 _
    have hconv := causal_awgn_feedback_code_converse hN hS (by simp)
      drift hcausal hmeas dec hdec (by simpa only [Fintype.card_fin] using henergy)
    simp only [Fintype.card_fin] at hconv
    have he : ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
        awgnNoise n N {z | dec (causalOutput (drift m) z) ≠ m}).toReal ≤ δ :=
      ENNReal.toReal_le_of_le_ofReal hδ.le herr
    have hlogM := log_max_one_floor_rpow_two_ge n R
    have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    calc (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2)
        ≤ (1 - δ) * Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ (1 - ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
          awgnNoise n N {z | dec (causalOutput (drift m) z) ≠ m}).toReal) * Real.log (M : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlogM0
      _ ≤ (n : ℝ) * K + 1 := hconv

end Causal1DConverse

/-! ### 5. Two-Output (`d = 2`) Causal AWGN Feedback Converse & Sharp SIMO Rotation -/

section Causal2DConverse

/-- Strict causality for a scalar drift on two-output blocks `(Fin n → ℝ) × (Fin n → ℝ)`. -/
def IsStrictlyCausal2 {n : ℕ} (drift : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) : Prop :=
  ∀ (i : Fin n) (y y' : (Fin n → ℝ) × (Fin n → ℝ)),
    (∀ t : Fin n, t < i → y.1 t = y'.1 t ∧ y.2 t = y'.2 t) → drift i y = drift i y'

/-- One pass of the 2-output causal channel equation. -/
def causalStep2 {n : ℕ} (drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (z y : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => drift₁ i y + z.1 i, fun i => drift₂ i y + z.2 i)

/-- The 2-output causal channel block obtained by `n` passes of `causalStep2` from `z`. -/
def causalOutput2 {n : ℕ} (drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (causalStep2 drift₁ drift₂ z)^[n] z

/-- Exact inverse of `causalOutput2`. -/
def causalInverse2 {n : ℕ} (drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (y : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => y.1 i - drift₁ i y, fun i => y.2 i - drift₂ i y)

/-- Pack a pair of 2-output drifts into a single `Fin n → (Fin n → ℝ × ℝ) → ℝ × ℝ` drift. -/
private def packDrift2 {n : ℕ} (drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ) :
    Fin n → (Fin n → ℝ × ℝ) → ℝ × ℝ :=
  fun i w => (drift₁ i (fun t => (w t).1, fun t => (w t).2),
              drift₂ i (fun t => (w t).1, fun t => (w t).2))

private lemma packDrift2_causal {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂) :
    IsStrictlyCausal (packDrift2 drift₁ drift₂) := by
  intro i w w' hw
  have hw' : ∀ t : Fin n, t < i → (w t).1 = (w' t).1 ∧ (w t).2 = (w' t).2 := fun t ht =>
    ⟨congrArg Prod.fst (hw t ht), congrArg Prod.snd (hw t ht)⟩
  exact Prod.ext (hc₁ i _ _ hw') (hc₂ i _ _ hw')

private lemma packDrift2_measurable {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    ∀ i, Measurable (packDrift2 drift₁ drift₂ i) := by
  intro i
  have he : Measurable (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) :=
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).measurable
  exact ((hm₁ i).comp he).prodMk ((hm₂ i).comp he)

private lemma causalOutput2_eq_pack {n : ℕ}
    (drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
    causalOutput2 drift₁ drift₂ z = e (causalOutput (packDrift2 drift₁ drift₂) (e.symm z)) := by
  intro e
  unfold causalOutput2 causalOutput
  suffices ∀ k : ℕ, ∀ y : (Fin n → ℝ) × (Fin n → ℝ),
      (causalStep2 drift₁ drift₂ z)^[k] y =
        e ((causalStep (packDrift2 drift₁ drift₂) (e.symm z))^[k] (e.symm y)) by
    exact this n z
  intro k
  induction k with
  | zero => intro y; simp [e]
  | succ k ih =>
    intro y
    simp only [Function.iterate_succ_apply', ih y]
    rfl

theorem causalOutput2_eq {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    (causalOutput2 drift₁ drift₂ z).1 i = drift₁ i (causalOutput2 drift₁ drift₂ z) + z.1 i ∧
    (causalOutput2 drift₁ drift₂ z).2 i = drift₂ i (causalOutput2 drift₁ drift₂ z) + z.2 i := by
  rw [causalOutput2_eq_pack]
  have h := causalOutput_eq (packDrift2_causal hc₁ hc₂)
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm z) i
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem causalOutput2_unique {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (z y : (Fin n → ℝ) × (Fin n → ℝ))
    (hy : ∀ i : Fin n, y.1 i = drift₁ i y + z.1 i ∧ y.2 i = drift₂ i y + z.2 i) :
    y = causalOutput2 drift₁ drift₂ z := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  rw [causalOutput2_eq_pack]
  have h : e.symm y = causalOutput (packDrift2 drift₁ drift₂) (e.symm z) := by
    apply causalOutput_unique (packDrift2_causal hc₁ hc₂)
    intro i
    exact Prod.ext (hy i).1 (hy i).2
  rw [← h, e.apply_symm_apply]

lemma measurable_causalOutput2 {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    Measurable (causalOutput2 drift₁ drift₂) := by
  have heq : causalOutput2 drift₁ drift₂ =
      fun z => (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
        (causalOutput (packDrift2 drift₁ drift₂)
          ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm z)) :=
    funext (causalOutput2_eq_pack drift₁ drift₂)
  rw [heq]
  exact (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).measurable.comp
    ((measurable_causalOutput (packDrift2_measurable hm₁ hm₂)).comp
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm.measurable)

lemma measurable_causalInverse2 {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    Measurable (causalInverse2 drift₁ drift₂) :=
  (measurable_pi_iff.mpr (fun i => ((measurable_pi_apply i).comp measurable_fst).sub (hm₁ i))).prodMk
    (measurable_pi_iff.mpr (fun i => ((measurable_pi_apply i).comp measurable_snd).sub (hm₂ i)))

def causalEquiv2 {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ ((Fin n → ℝ) × (Fin n → ℝ)) where
  toFun := causalOutput2 drift₁ drift₂
  invFun := causalInverse2 drift₁ drift₂
  left_inv z := by
    apply Prod.ext <;> funext i
    · simp only [causalInverse2, (causalOutput2_eq hc₁ hc₂ z i).1, add_sub_cancel_left]
    · simp only [causalInverse2, (causalOutput2_eq hc₁ hc₂ z i).2, add_sub_cancel_left]
  right_inv y := by
    symm
    apply causalOutput2_unique hc₁ hc₂
    intro i
    exact ⟨by simp [causalInverse2], by simp [causalInverse2]⟩
  measurable_toFun := measurable_causalOutput2 hm₁ hm₂
  measurable_invFun := measurable_causalInverse2 hm₁ hm₂

lemma drift_causalOutput2_congr_lt {n : ℕ} {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (i : Fin n) {z z' : (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : ∀ t : Fin n, t < i → z.1 t = z'.1 t ∧ z.2 t = z'.2 t) :
    drift₁ i (causalOutput2 drift₁ drift₂ z) = drift₁ i (causalOutput2 drift₁ drift₂ z') ∧
    drift₂ i (causalOutput2 drift₁ drift₂ z) = drift₂ i (causalOutput2 drift₁ drift₂ z') := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have h := drift_causalOutput_congr_lt (packDrift2_causal hc₁ hc₂) i (z := e.symm z) (z' := e.symm z')
    (fun t ht => Prod.ext (hz t ht).1 (hz t ht).2)
  rw [causalOutput2_eq_pack, causalOutput2_eq_pack]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Helper: swapping the middle two factors of a 4-fold product preserves product measures. -/
private lemma measurePreserving_prodProdProdComm' {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) (μ₄ : Measure δ)
    [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite μ₃] [SigmaFinite μ₄] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μ₁.prod μ₂).prod (μ₃.prod μ₄))
      ((μ₁.prod μ₃).prod (μ₂.prod μ₄)) := by
  let f : (α × β) × (γ × δ) → (α × γ) × (β × δ) := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
  have hf : Measurable f :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  refine ⟨hf, ?_⟩
  refine (Measure.prod_eq (fun s t hs ht => ?_)).symm
  rw [Measure.map_apply hf (hs.prod ht), ← lintegral_indicator_one (hf (hs.prod ht)),
    lintegral_prod (f := (f ⁻¹' (s ×ˢ t)).indicator (1 : ((α × β) × (γ × δ)) → ℝ≥0∞))
      (measurable_const.indicator (hf (hs.prod ht))).aemeasurable]
  have hinner : ∀ p₁ : α × β,
      ∫⁻ p₂ : γ × δ, (f ⁻¹' (s ×ˢ t)).indicator (1 : ((α × β) × (γ × δ)) → ℝ≥0∞) (p₁, p₂) ∂(μ₃.prod μ₄) =
        (∫⁻ c, s.indicator (1 : (α × γ) → ℝ≥0∞) (p₁.1, c) ∂μ₃) *
        (∫⁻ d, t.indicator (1 : (β × δ) → ℝ≥0∞) (p₁.2, d) ∂μ₄) := by
    intro ⟨a, b⟩
    have hpt : ∀ p₂ : γ × δ,
        (f ⁻¹' (s ×ˢ t)).indicator (1 : ((α × β) × (γ × δ)) → ℝ≥0∞) ((a, b), p₂) =
          s.indicator (1 : (α × γ) → ℝ≥0∞) (a, p₂.1) * t.indicator (1 : (β × δ) → ℝ≥0∞) (b, p₂.2) := by
      intro ⟨c, d⟩
      by_cases hac : (a, c) ∈ s <;> by_cases hbd : (b, d) ∈ t
      · have hm : ((a, b), (c, d)) ∈ f ⁻¹' (s ×ˢ t) := ⟨hac, hbd⟩
        simp [Set.indicator_of_mem hm, Set.indicator_of_mem hac, Set.indicator_of_mem hbd]
      · have hm : ((a, b), (c, d)) ∉ f ⁻¹' (s ×ˢ t) := fun h => hbd h.2
        simp [Set.indicator_of_notMem hm, Set.indicator_of_notMem hbd]
      · have hm : ((a, b), (c, d)) ∉ f ⁻¹' (s ×ˢ t) := fun h => hac h.1
        simp [Set.indicator_of_notMem hm, Set.indicator_of_notMem hac]
      · have hm : ((a, b), (c, d)) ∉ f ⁻¹' (s ×ˢ t) := fun h => hac h.1
        simp [Set.indicator_of_notMem hm, Set.indicator_of_notMem hac]
    simp_rw [hpt]
    exact lintegral_prod_mul
      ((measurable_const.indicator hs).comp (measurable_const.prodMk measurable_id)).aemeasurable
      ((measurable_const.indicator ht).comp (measurable_const.prodMk measurable_id)).aemeasurable
  simp_rw [hinner]
  have hm1 : Measurable (fun a : α => ∫⁻ c, s.indicator (1 : (α × γ) → ℝ≥0∞) (a, c) ∂μ₃) :=
    (measurable_const.indicator hs).lintegral_prod_right'
  have hm2 : Measurable (fun b : β => ∫⁻ d, t.indicator (1 : (β × δ) → ℝ≥0∞) (b, d) ∂μ₄) :=
    (measurable_const.indicator ht).lintegral_prod_right'
  rw [lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable,
    ← lintegral_prod (f := s.indicator (1 : (α × γ) → ℝ≥0∞)) (measurable_const.indicator hs).aemeasurable,
    ← lintegral_prod (f := t.indicator (1 : (β × δ) → ℝ≥0∞)) (measurable_const.indicator ht).aemeasurable,
    lintegral_indicator_one hs, lintegral_indicator_one ht]

/-- `MeasurableEquiv.arrowProdEquivProdArrow` preserves product measures. -/
lemma measurePreserving_arrowProdEquivProdArrow (n : ℕ) (μ₁ μ₂ : Measure ℝ)
    [SigmaFinite μ₁] [SigmaFinite μ₂] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (Measure.pi fun _ : Fin n => μ₁.prod μ₂)
      ((Measure.pi fun _ : Fin n => μ₁).prod (Measure.pi fun _ : Fin n => μ₂)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  refine ⟨e.measurable, ?_⟩
  induction n with
  | zero =>
    ext s _
    rw [Measure.map_apply e.measurable (by trivial)]
    by_cases hs : ((Fin.elim0 : Fin 0 → ℝ), (Fin.elim0 : Fin 0 → ℝ)) ∈ s
    · have hsu : s = Set.univ := by
        ext ⟨a, b⟩
        simp [Subsingleton.elim a Fin.elim0, Subsingleton.elim b Fin.elim0, hs]
      rw [hsu, Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod]
      simp
    · have hse : s = ∅ := by
        ext ⟨a, b⟩
        simp [Subsingleton.elim a Fin.elim0, Subsingleton.elim b Fin.elim0, hs]
      rw [hse]
      simp
  | succ n ih =>
    let e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) 0
    let e1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have h0 : MeasurePreserving e0 (Measure.pi fun _ : Fin (n + 1) => μ₁.prod μ₂)
        ((μ₁.prod μ₂).prod (Measure.pi fun _ : Fin n => μ₁.prod μ₂)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ₁.prod μ₂) 0
    have h1 : MeasurePreserving e1 (Measure.pi fun _ : Fin (n + 1) => μ₁)
        (μ₁.prod (Measure.pi fun _ : Fin n => μ₁)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ₁) 0
    have h2 : MeasurePreserving e1 (Measure.pi fun _ : Fin (n + 1) => μ₂)
        (μ₂.prod (Measure.pi fun _ : Fin n => μ₂)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ₂) 0
    have hih : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
        (Measure.pi fun _ : Fin n => μ₁.prod μ₂)
        ((Measure.pi fun _ : Fin n => μ₁).prod (Measure.pi fun _ : Fin n => μ₂)) :=
      ⟨(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).measurable, ih⟩
    have hmid : MeasurePreserving
        (Prod.map id (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)))
        ((μ₁.prod μ₂).prod (Measure.pi fun _ : Fin n => μ₁.prod μ₂))
        ((μ₁.prod μ₂).prod ((Measure.pi fun _ : Fin n => μ₁).prod (Measure.pi fun _ : Fin n => μ₂))) :=
      (MeasurePreserving.id _).prod hih
    have hcomm := measurePreserving_prodProdProdComm' μ₁ μ₂
      (Measure.pi fun _ : Fin n => μ₁) (Measure.pi fun _ : Fin n => μ₂)
    have hback : MeasurePreserving (Prod.map e1.symm e1.symm)
        ((μ₁.prod (Measure.pi fun _ : Fin n => μ₁)).prod (μ₂.prod (Measure.pi fun _ : Fin n => μ₂)))
        ((Measure.pi fun _ : Fin (n + 1) => μ₁).prod (Measure.pi fun _ : Fin (n + 1) => μ₂)) :=
      h1.symm.prod h2.symm
    have htot := hback.comp (hcomm.comp (hmid.comp h0))
    have hfun : (fun w : Fin (n + 1) → ℝ × ℝ =>
        Prod.map e1.symm e1.symm
          ((fun p : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
            (Prod.map id (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) (e0 w)))) =
        e := by
      funext w
      apply Prod.ext
      · apply e1.injective
        simp only [Prod.map_fst]
        rw [e1.apply_symm_apply]
        rfl
      · apply e1.injective
        simp only [Prod.map_snd]
        rw [e1.apply_symm_apply]
        rfl
    have htot' : MeasurePreserving
        (fun w : Fin (n + 1) → ℝ × ℝ =>
          Prod.map e1.symm e1.symm
            ((fun p : (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
              (Prod.map id (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) (e0 w))))
        (Measure.pi fun _ : Fin (n + 1) => μ₁.prod μ₂)
        ((Measure.pi fun _ : Fin (n + 1) => μ₁).prod (Measure.pi fun _ : Fin (n + 1) => μ₂)) := htot
    rw [hfun] at htot'
    exact htot'.map_eq

theorem measurePreserving_causalOutput2_volume {n : ℕ}
    {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    MeasurePreserving (causalOutput2 drift₁ drift₂)
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he : MeasurePreserving e
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))) :=
    measurePreserving_arrowProdEquivProdArrow n volume volume
  have hpack := measurePreserving_causalOutput
    ((volume : Measure ℝ).prod (volume : Measure ℝ))
    (packDrift2_causal hc₁ hc₂) (packDrift2_measurable hm₁ hm₂)
  have hcomp : MeasurePreserving
      (fun z => e (causalOutput (packDrift2 drift₁ drift₂) (e.symm z)))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))) :=
    he.comp (hpack.comp he.symm)
  have hfun : (fun z => e (causalOutput (packDrift2 drift₁ drift₂) (e.symm z))) =
      causalOutput2 drift₁ drift₂ := funext (fun z => (causalOutput2_eq_pack drift₁ drift₂ z).symm)
  rwa [hfun] at hcomp

/-- 2-output causal block LLR against `(awgnNoise n V₁).prod (awgnNoise n V₂)`. -/
noncomputable def causalBlockLLR2 {n : ℕ} (N₁ N₂ V₁ V₂ : ℝ)
    (drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (y : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i : Fin n,
    (((1 / 2 : ℝ) * Real.log (V₁ / N₁) - (y.1 i - drift₁ i y) ^ 2 / (2 * N₁) +
        (y.1 i) ^ 2 / (2 * V₁)) +
     ((1 / 2 : ℝ) * Real.log (V₂ / N₂) - (y.2 i - drift₂ i y) ^ 2 / (2 * N₂) +
        (y.2 i) ^ 2 / (2 * V₂)))

lemma measurable_causalBlockLLR2 {n : ℕ} (N₁ N₂ V₁ V₂ : ℝ)
    {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    Measurable (causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂) := by
  unfold causalBlockLLR2
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have h1 : Measurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) => y.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have h2 : Measurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) => y.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact ((measurable_const.sub (((h1.sub (hm₁ i)).pow_const 2).div_const _)).add
    ((h1.pow_const 2).div_const _)).add
    ((measurable_const.sub (((h2.sub (hm₂ i)).pow_const 2).div_const _)).add
    ((h2.pow_const 2).div_const _))

private lemma gaussianPDF_eq_mul_exp_llr {N V : ℝ} (hN : 0 < N) (hV : 0 < V) (a b : ℝ) :
    gaussianPDF 0 V.toNNReal b =
      gaussianPDF 0 N.toNNReal a *
        ENNReal.ofReal (Real.exp (-((1 / 2 : ℝ) * Real.log (V / N) - a ^ 2 / (2 * N) +
          b ^ 2 / (2 * V)))) := by
  rw [gaussianPDF_eq_ofReal_gaussianPdf1D hN.le, gaussianPDF_eq_ofReal_gaussianPdf1D hV.le,
    ← ENNReal.ofReal_mul (gaussianPdf1D_nonneg hN.le _)]
  congr 1
  have hpos1 := gaussianPdf1D_pos hN a
  have hpos2 := gaussianPdf1D_pos hV b
  have hlog : Real.log (gaussianPdf1D N a *
      Real.exp (-((1 / 2 : ℝ) * Real.log (V / N) - a ^ 2 / (2 * N) + b ^ 2 / (2 * V)))) =
      Real.log (gaussianPdf1D V b) := by
    rw [Real.log_mul hpos1.ne' (Real.exp_pos _).ne', Real.log_exp,
      log_gaussianPdf1D hN, log_gaussianPdf1D hV, Real.log_div hV.ne' hN.ne',
      Real.log_mul (by positivity) hN.ne', Real.log_mul (by positivity) hV.ne']
    ring
  exact (Real.log_injOn_pos (mul_pos hpos1 (Real.exp_pos _)) hpos2 hlog).symm

private lemma awgnNoise2_eq_withDensity_prod {n : ℕ} {V₁ V₂ : ℝ} (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    (awgnNoise n V₁).prod (awgnNoise n V₂) =
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).withDensity
        (fun y => (∏ i : Fin n, gaussianPDF 0 V₁.toNNReal (y.1 i)) *
          (∏ i : Fin n, gaussianPDF 0 V₂.toNNReal (y.2 i))) := by
  have hd₁ : Measurable (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 V₁.toNNReal (z i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 V₁.toNNReal).comp (measurable_pi_apply i))
  have hd₂ : Measurable (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 V₂.toNNReal (z i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 V₂.toNNReal).comp (measurable_pi_apply i))
  have hsf₁ : SigmaFinite (volume.withDensity (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 V₁.toNNReal (z i))) := by
    rw [← awgnNoise_eq_withDensity n hV₁]; infer_instance
  have hsf₂ : SigmaFinite (volume.withDensity (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 V₂.toNNReal (z i))) := by
    rw [← awgnNoise_eq_withDensity n hV₂]; infer_instance
  rw [awgnNoise_eq_withDensity n hV₁, awgnNoise_eq_withDensity n hV₂]
  exact prod_withDensity_eq volume volume hd₁ hd₂

lemma awgnNoise2_eq_withDensity_causalBlockLLR2 {n : ℕ} {N₁ N₂ V₁ V₂ : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i)) :
    (awgnNoise n V₁).prod (awgnNoise n V₂) =
      (((awgnNoise n N₁).prod (awgnNoise n N₂)).map (causalOutput2 drift₁ drift₂)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂ y))) := by
  have hmp := measurePreserving_causalOutput2_volume hc₁ hc₂ hm₁ hm₂
  have hdN₁ : Measurable (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 N₁.toNNReal (z i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N₁.toNNReal).comp (measurable_pi_apply i))
  have hdN₂ : Measurable (fun z : Fin n → ℝ => ∏ i : Fin n, gaussianPDF 0 N₂.toNNReal (z i)) :=
    Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N₂.toNNReal).comp (measurable_pi_apply i))
  have hP : ((awgnNoise n N₁).prod (awgnNoise n N₂)).map (causalOutput2 drift₁ drift₂) =
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).withDensity
        (fun y => (∏ i : Fin n, gaussianPDF 0 N₁.toNNReal (y.1 i - drift₁ i y)) *
          (∏ i : Fin n, gaussianPDF 0 N₂.toNNReal (y.2 i - drift₂ i y))) := by
    rw [awgnNoise2_eq_withDensity_prod hN₁ hN₂]
    exact map_withDensity_of_measurePreserving (causalEquiv2 hc₁ hc₂ hm₁ hm₂) hmp
      (f := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (∏ i : Fin n, gaussianPDF 0 N₁.toNNReal (z.1 i)) *
          (∏ i : Fin n, gaussianPDF 0 N₂.toNNReal (z.2 i)))
      ((hdN₁.comp measurable_fst).mul (hdN₂.comp measurable_snd))
  have hf_meas : Measurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
      (∏ i : Fin n, gaussianPDF 0 N₁.toNNReal (y.1 i - drift₁ i y)) *
        (∏ i : Fin n, gaussianPDF 0 N₂.toNNReal (y.2 i - drift₂ i y))) :=
    (Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N₁.toNNReal).comp
        (((measurable_pi_apply i).comp measurable_fst).sub (hm₁ i)))).mul
    (Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDF 0 N₂.toNNReal).comp
        (((measurable_pi_apply i).comp measurable_snd).sub (hm₂ i))))
  have hg_meas : Measurable (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal (Real.exp (-causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂ y))) :=
    (measurable_causalBlockLLR2 N₁ N₂ V₁ V₂ hm₁ hm₂).neg.exp.ennreal_ofReal
  rw [hP, ← withDensity_mul ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ)))
      hf_meas hg_meas,
    awgnNoise2_eq_withDensity_prod hV₁ hV₂]
  refine congrArg (Measure.withDensity _) ?_
  funext y
  dsimp only [Pi.mul_apply]
  have hexp : ENNReal.ofReal (Real.exp (-causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂ y)) =
      (∏ i : Fin n, ENNReal.ofReal (Real.exp (-((1 / 2 : ℝ) * Real.log (V₁ / N₁) -
          (y.1 i - drift₁ i y) ^ 2 / (2 * N₁) + (y.1 i) ^ 2 / (2 * V₁))))) *
      (∏ i : Fin n, ENNReal.ofReal (Real.exp (-((1 / 2 : ℝ) * Real.log (V₂ / N₂) -
          (y.2 i - drift₂ i y) ^ 2 / (2 * N₂) + (y.2 i) ^ 2 / (2 * V₂))))) := by
    unfold causalBlockLLR2
    rw [← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [hexp, mul_mul_mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => gaussianPDF_eq_mul_exp_llr hN₁ hV₁ _ _)
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => gaussianPDF_eq_mul_exp_llr hN₂ hV₂ _ _)

lemma integrable_and_integral_causalBlockLLR2 {n : ℕ} {N₁ N₂ V₁ V₂ : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    {drift₁ drift₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hc₁ : IsStrictlyCausal2 drift₁) (hc₂ : IsStrictlyCausal2 drift₂)
    (hm₁ : ∀ i, Measurable (drift₁ i)) (hm₂ : ∀ i, Measurable (drift₂ i))
    (he₁ : ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift₁ i (causalOutput2 drift₁ drift₂ z)) ^ 2)
        ∂((awgnNoise n N₁).prod (awgnNoise n N₂)) < ⊤)
    (he₂ : ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift₂ i (causalOutput2 drift₁ drift₂ z)) ^ 2)
        ∂((awgnNoise n N₁).prod (awgnNoise n N₂)) < ⊤) :
    let ν := (awgnNoise n N₁).prod (awgnNoise n N₂)
    Integrable (causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂) (ν.map (causalOutput2 drift₁ drift₂)) ∧
      ∫ y, causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂ y ∂(ν.map (causalOutput2 drift₁ drift₂)) =
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log (V₁ / N₁) - 1 / 2) +
          ((∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift₁ i (causalOutput2 drift₁ drift₂ z)) ^ 2)
              ∂ν).toReal + (n : ℝ) * N₁) / (2 * V₁) +
        ((n : ℝ) * ((1 / 2 : ℝ) * Real.log (V₂ / N₂) - 1 / 2) +
          ((∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift₂ i (causalOutput2 drift₁ drift₂ z)) ^ 2)
              ∂ν).toReal + (n : ℝ) * N₂) / (2 * V₂)) := by
  intro ν
  let X₁ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun i z => drift₁ i (causalOutput2 drift₁ drift₂ z)
  let X₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun i z => drift₂ i (causalOutput2 drift₁ drift₂ z)
  have hX₁m : ∀ i, Measurable (X₁ i) := fun i => (hm₁ i).comp (measurable_causalOutput2 hm₁ hm₂)
  have hX₂m : ∀ i, Measurable (X₂ i) := fun i => (hm₂ i).comp (measurable_causalOutput2 hm₁ hm₂)
  have hX₁sq : ∀ i, Integrable (fun z => (X₁ i z) ^ 2) ν :=
    integrable_sq_of_lintegral_sum_sq_lt_top hX₁m he₁
  have hX₂sq : ∀ i, Integrable (fun z => (X₂ i z) ^ 2) ν :=
    integrable_sq_of_lintegral_sum_sq_lt_top hX₂m he₂
  have hZ₁sq : ∀ i, Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1 i) ^ 2) ν :=
    fun i => (integrable_sq_coord_awgnNoise N₁ i).comp_fst (awgnNoise n N₂)
  have hZ₂sq : ∀ i, Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.2 i) ^ 2) ν :=
    fun i => (integrable_sq_coord_awgnNoise N₂ i).comp_snd (awgnNoise n N₁)
  have hZ₁val : ∀ i, ∫ z : (Fin n → ℝ) × (Fin n → ℝ), (z.1 i) ^ 2 ∂ν = N₁ := by
    intro i
    rw [integral_prod _ (hZ₁sq i)]
    simp [integral_sq_coord_awgnNoise hN₁.le i]
  have hZ₂val : ∀ i, ∫ z : (Fin n → ℝ) × (Fin n → ℝ), (z.2 i) ^ 2 ∂ν = N₂ := by
    intro i
    rw [integral_prod _ (hZ₂sq i)]
    simp [integral_sq_coord_awgnNoise hN₂.le i]
  have hX₁cross : ∀ i, Integrable (fun z => X₁ i z * z.1 i) ν ∧
      ∫ z, X₁ i z * z.1 i ∂ν = 0 := fun i =>
    integral_mul_fst_coord_eq_zero_of_indep_coord i (X₁ i) (hX₁m i)
      (fun p q h2 h1 => (drift_causalOutput2_congr_lt hc₁ hc₂ i
        (fun t ht => ⟨h1 t (ne_of_lt ht), congrFun h2 t⟩)).1) (hX₁sq i)
  have hX₂cross : ∀ i, Integrable (fun z => X₂ i z * z.2 i) ν ∧
      ∫ z, X₂ i z * z.2 i ∂ν = 0 := fun i =>
    integral_mul_snd_coord_eq_zero_of_indep_coord i (X₂ i) (hX₂m i)
      (fun p q h1 h2 => (drift_causalOutput2_congr_lt hc₁ hc₂ i
        (fun t ht => ⟨congrFun h1 t, h2 t (ne_of_lt ht)⟩)).2) (hX₂sq i)
  let t₁ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun i z =>
    ((1 / 2 : ℝ) * Real.log (V₁ / N₁) - (z.1 i) ^ 2 / (2 * N₁)) +
      ((X₁ i z) ^ 2 / (2 * V₁) + (2 / (2 * V₁)) * (X₁ i z * z.1 i) + (z.1 i) ^ 2 / (2 * V₁))
  let t₂ : Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun i z =>
    ((1 / 2 : ℝ) * Real.log (V₂ / N₂) - (z.2 i) ^ 2 / (2 * N₂)) +
      ((X₂ i z) ^ 2 / (2 * V₂) + (2 / (2 * V₂)) * (X₂ i z * z.2 i) + (z.2 i) ^ 2 / (2 * V₂))
  have ht₁_int : ∀ i, Integrable (t₁ i) ν := fun i =>
    ((integrable_const _).sub ((hZ₁sq i).div_const _)).add
      ((((hX₁sq i).div_const _).add ((hX₁cross i).1.const_mul _)).add ((hZ₁sq i).div_const _))
  have ht₂_int : ∀ i, Integrable (t₂ i) ν := fun i =>
    ((integrable_const _).sub ((hZ₂sq i).div_const _)).add
      ((((hX₂sq i).div_const _).add ((hX₂cross i).1.const_mul _)).add ((hZ₂sq i).div_const _))
  have hcomp : ∀ z, causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂ (causalOutput2 drift₁ drift₂ z) =
      ∑ i : Fin n, (t₁ i z + t₂ i z) := by
    intro z
    unfold causalBlockLLR2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    obtain ⟨he1, he2⟩ := causalOutput2_eq hc₁ hc₂ z i
    rw [he1, he2, add_sub_cancel_left, add_sub_cancel_left]
    dsimp only [t₁, t₂, X₁, X₂]
    ring
  have ht_int : ∀ i, Integrable (fun z => t₁ i z + t₂ i z) ν :=
    fun i => (ht₁_int i).add (ht₂_int i)
  have hint_z : Integrable (fun z => causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂
      (causalOutput2 drift₁ drift₂ z)) ν := by
    simpa only [hcomp] using integrable_finsetSum Finset.univ (fun i _ => ht_int i)
  have hint_y : Integrable (causalBlockLLR2 N₁ N₂ V₁ V₂ drift₁ drift₂)
      (ν.map (causalOutput2 drift₁ drift₂)) :=
    (integrable_map_measure (measurable_causalBlockLLR2 N₁ N₂ V₁ V₂ hm₁ hm₂).aestronglyMeasurable
      (measurable_causalOutput2 hm₁ hm₂).aemeasurable).mpr hint_z
  refine ⟨hint_y, ?_⟩
  rw [integral_map (measurable_causalOutput2 hm₁ hm₂).aemeasurable
    (measurable_causalBlockLLR2 N₁ N₂ V₁ V₂ hm₁ hm₂).aestronglyMeasurable]
  simp_rw [hcomp]
  rw [integral_finsetSum Finset.univ (fun i _ => ht_int i)]
  have hv₁ : ∀ i, ∫ z, t₁ i z ∂ν =
      ((1 / 2 : ℝ) * Real.log (V₁ / N₁) - 1 / 2) + ((∫ z, (X₁ i z) ^ 2 ∂ν) + N₁) / (2 * V₁) := by
    intro i
    dsimp only [t₁]
    have ha1 : Integrable (fun _ : (Fin n → ℝ) × (Fin n → ℝ) => (1 / 2 : ℝ) * Real.log (V₁ / N₁)) ν :=
      integrable_const _
    have ha2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1 i) ^ 2 / (2 * N₁)) ν :=
      (hZ₁sq i).div_const _
    have hb1 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (X₁ i z) ^ 2 / (2 * V₁)) ν :=
      (hX₁sq i).div_const _
    have hb2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (2 / (2 * V₁)) * (X₁ i z * z.1 i)) ν :=
      (hX₁cross i).1.const_mul _
    have hb3 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1 i) ^ 2 / (2 * V₁)) ν :=
      (hZ₁sq i).div_const _
    have ha : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (1 / 2 : ℝ) * Real.log (V₁ / N₁) - (z.1 i) ^ 2 / (2 * N₁)) ν := ha1.sub ha2
    have hb12 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (X₁ i z) ^ 2 / (2 * V₁) + (2 / (2 * V₁)) * (X₁ i z * z.1 i)) ν := hb1.add hb2
    have hb : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (X₁ i z) ^ 2 / (2 * V₁) + (2 / (2 * V₁)) * (X₁ i z * z.1 i) + (z.1 i) ^ 2 / (2 * V₁)) ν :=
      hb12.add hb3
    rw [integral_add ha hb, integral_sub ha1 ha2, integral_add hb12 hb3, integral_add hb1 hb2,
      integral_const, integral_div, integral_div, integral_div, integral_const_mul,
      hZ₁val i, (hX₁cross i).2]
    simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
    have hN1ne : N₁ ≠ 0 := hN₁.ne'
    have hV1ne : V₁ ≠ 0 := hV₁.ne'
    field_simp
  have hv₂ : ∀ i, ∫ z, t₂ i z ∂ν =
      ((1 / 2 : ℝ) * Real.log (V₂ / N₂) - 1 / 2) + ((∫ z, (X₂ i z) ^ 2 ∂ν) + N₂) / (2 * V₂) := by
    intro i
    dsimp only [t₂]
    have ha1 : Integrable (fun _ : (Fin n → ℝ) × (Fin n → ℝ) => (1 / 2 : ℝ) * Real.log (V₂ / N₂)) ν :=
      integrable_const _
    have ha2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.2 i) ^ 2 / (2 * N₂)) ν :=
      (hZ₂sq i).div_const _
    have hb1 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (X₂ i z) ^ 2 / (2 * V₂)) ν :=
      (hX₂sq i).div_const _
    have hb2 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (2 / (2 * V₂)) * (X₂ i z * z.2 i)) ν :=
      (hX₂cross i).1.const_mul _
    have hb3 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.2 i) ^ 2 / (2 * V₂)) ν :=
      (hZ₂sq i).div_const _
    have ha : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (1 / 2 : ℝ) * Real.log (V₂ / N₂) - (z.2 i) ^ 2 / (2 * N₂)) ν := ha1.sub ha2
    have hb12 : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (X₂ i z) ^ 2 / (2 * V₂) + (2 / (2 * V₂)) * (X₂ i z * z.2 i)) ν := hb1.add hb2
    have hb : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (X₂ i z) ^ 2 / (2 * V₂) + (2 / (2 * V₂)) * (X₂ i z * z.2 i) + (z.2 i) ^ 2 / (2 * V₂)) ν :=
      hb12.add hb3
    rw [integral_add ha hb, integral_sub ha1 ha2, integral_add hb12 hb3, integral_add hb1 hb2,
      integral_const, integral_div, integral_div, integral_div, integral_const_mul,
      hZ₂val i, (hX₂cross i).2]
    simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
    have hN2ne : N₂ ≠ 0 := hN₂.ne'
    have hV2ne : V₂ ≠ 0 := hV₂.ne'
    field_simp
  simp_rw [fun i => integral_add (ht₁_int i) (ht₂_int i), hv₁, hv₂]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← integral_finsetSum Finset.univ (fun i _ => hX₁sq i),
      ← integral_sum_sq_eq_toReal_lintegral hX₁m]
  · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← integral_finsetSum Finset.univ (fun i _ => hX₂sq i),
      ← integral_sum_sq_eq_toReal_lintegral hX₂m]

/-- **2-Output Causal AWGN Feedback Converse (finite blocklength, nats)**:
    for independent noises `N₁, N₂ > 0`, energy budgets `S₁, S₂ ≥ 0`, strictly causal measurable
    drifts `drift₁, drift₂`, and measurable decoder `dec`:
    `(1 - avgErr.toReal) * ln |ι| ≤ (n / 2) * (ln (1 + S₁ / N₁) + ln (1 + S₂ / N₂)) + 1`. -/
theorem causal_awgn2_feedback_code_converse {n : ℕ} {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {N₁ N₂ S₁ S₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hcard : 1 ≤ Fintype.card ι)
    (drift₁ drift₂ : ι → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (hc₁ : ∀ m, IsStrictlyCausal2 (drift₁ m)) (hc₂ : ∀ m, IsStrictlyCausal2 (drift₂ m))
    (hm₁ : ∀ m i, Measurable (drift₁ m i)) (hm₂ : ∀ m i, Measurable (drift₂ m i))
    (dec : ((Fin n → ℝ) × (Fin n → ℝ)) → ι) (hdec : Measurable dec)
    (he₁ : (Fintype.card ι : ℝ≥0∞)⁻¹ *
        ∑ m : ι, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₁ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2)
          ∂((awgnNoise n N₁).prod (awgnNoise n N₂)) ≤ ENNReal.ofReal ((n : ℝ) * S₁))
    (he₂ : (Fintype.card ι : ℝ≥0∞)⁻¹ *
        ∑ m : ι, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2)
          ∂((awgnNoise n N₁).prod (awgnNoise n N₂)) ≤ ENNReal.ofReal ((n : ℝ) * S₂)) :
    let ν := (awgnNoise n N₁).prod (awgnNoise n N₂)
    let avgErr : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)⁻¹ *
      ∑ m : ι, ν {z | dec (causalOutput2 (drift₁ m) (drift₂ m) z) ≠ m}
    (1 - avgErr.toReal) * Real.log (Fintype.card ι : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S₁ / N₁) + (1 / 2 : ℝ) * Real.log (1 + S₂ / N₂)) + 1 := by
  intro ν avgErr
  set M : ℕ := Fintype.card ι with hM_def
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hcard
  have hV₁ : 0 < S₁ + N₁ := by linarith
  have hV₂ : 0 < S₂ + N₂ := by linarith
  set P : ι → Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
    fun m => ν.map (causalOutput2 (drift₁ m) (drift₂ m))
  have hPprob : ∀ m, IsProbabilityMeasure (P m) := fun m =>
    ⟨by rw [Measure.map_apply (measurable_causalOutput2 (hm₁ m) (hm₂ m)) MeasurableSet.univ,
        Set.preimage_univ, measure_univ]⟩
  have hE1_lt : ∀ m : ι, ∫⁻ z, ENNReal.ofReal
      (∑ i : Fin n, (drift₁ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2) ∂ν < ⊤ := by
    intro m; by_contra htop; rw [not_lt, top_le_iff] at htop
    have hs : ∑ m' : ι, ∫⁻ z, ENNReal.ofReal
        (∑ i : Fin n, (drift₁ m' i (causalOutput2 (drift₁ m') (drift₂ m') z)) ^ 2) ∂ν = ⊤ :=
      top_unique (htop ▸ Finset.single_le_sum
        (f := fun m' : ι => ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₁ m' i (causalOutput2 (drift₁ m') (drift₂ m') z)) ^ 2) ∂ν)
        (fun _ _ => bot_le) (Finset.mem_univ m))
    rw [hs, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M))] at he₁
    exact ENNReal.ofReal_lt_top.not_ge he₁
  have hE2_lt : ∀ m : ι, ∫⁻ z, ENNReal.ofReal
      (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2) ∂ν < ⊤ := by
    intro m; by_contra htop; rw [not_lt, top_le_iff] at htop
    have hs : ∑ m' : ι, ∫⁻ z, ENNReal.ofReal
        (∑ i : Fin n, (drift₂ m' i (causalOutput2 (drift₁ m') (drift₂ m') z)) ^ 2) ∂ν = ⊤ :=
      top_unique (htop ▸ Finset.single_le_sum
        (f := fun m' : ι => ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₂ m' i (causalOutput2 (drift₁ m') (drift₂ m') z)) ^ 2) ∂ν)
        (fun _ _ => bot_le) (Finset.mem_univ m))
    rw [hs, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M))] at he₂
    exact ENNReal.ofReal_lt_top.not_ge he₂
  have hLLR := fun m => integrable_and_integral_causalBlockLLR2 hN₁ hN₂ hV₁ hV₂
    (hc₁ m) (hc₂ m) (hm₁ m) (hm₂ m) (hE1_lt m) (hE2_lt m)
  have hmeta := meta_converse_avg_error hcard P
    ((awgnNoise n (S₁ + N₁)).prod (awgnNoise n (S₂ + N₂))) dec hdec
    (fun m => causalBlockLLR2 N₁ N₂ (S₁ + N₁) (S₂ + N₂) (drift₁ m) (drift₂ m))
    (fun m => measurable_causalBlockLLR2 N₁ N₂ (S₁ + N₁) (S₂ + N₂) (hm₁ m) (hm₂ m))
    (fun m => (hLLR m).1)
    (fun m => awgnNoise2_eq_withDensity_causalBlockLLR2 hN₁ hN₂ hV₁ hV₂
      (hc₁ m) (hc₂ m) (hm₁ m) (hm₂ m))
  have herr_eq : (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ m : ι, P m {y | dec y ≠ m} = avgErr := by
    simp only [avgErr, P]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hs : MeasurableSet {y : (Fin n → ℝ) × (Fin n → ℝ) | dec y ≠ m} :=
      (hdec (measurableSet_singleton m)).compl
    rw [Measure.map_apply (measurable_causalOutput2 (hm₁ m) (hm₂ m)) hs]
    rfl
  rw [herr_eq] at hmeta
  have havgE₁ : (1 / (M : ℝ)) * ∑ m : ι, (∫⁻ z, ENNReal.ofReal
      (∑ i : Fin n, (drift₁ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2) ∂ν).toReal ≤
      (n : ℝ) * S₁ := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) he₁
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ => (hE1_lt m).ne), ← one_div] at h1
    exact h1
  have havgE₂ : (1 / (M : ℝ)) * ∑ m : ι, (∫⁻ z, ENNReal.ofReal
      (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2) ∂ν).toReal ≤
      (n : ℝ) * S₂ := by
    have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) he₂
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun m _ => (hE2_lt m).ne), ← one_div] at h1
    exact h1
  have hbound : ∀ (N S : ℝ) (hN : 0 < N) (hS : 0 ≤ S) (E : ι → ℝ),
      (1 / (M : ℝ)) * ∑ m : ι, E m ≤ (n : ℝ) * S →
      (1 / (M : ℝ)) * ∑ m : ι,
        ((n : ℝ) * ((1 / 2 : ℝ) * Real.log ((S + N) / N) - 1 / 2) +
          (E m + (n : ℝ) * N) / (2 * (S + N))) ≤
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N)) := by
    intro N S hN hS E hE
    have hV : 0 < S + N := by linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hlog : Real.log ((S + N) / N) = Real.log (1 + S / N) := by congr 1; field_simp; ring
    rw [hlog]
    have hrw : (1 / (M : ℝ)) * ((M : ℝ) * ((n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N) - 1 / 2)) +
        (∑ m : ι, E m + (M : ℝ) * ((n : ℝ) * N)) / (2 * (S + N))) =
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S / N) - 1 / 2) +
          ((1 / (M : ℝ)) * ∑ m : ι, E m + (n : ℝ) * N) / (2 * (S + N)) := by
      field_simp
    rw [hrw]
    have hdiv : ((1 / (M : ℝ)) * ∑ m : ι, E m + (n : ℝ) * N) / (2 * (S + N)) ≤ (n : ℝ) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hsum_LLR : (1 / (M : ℝ)) * ∑ m : ι,
      ∫ y, causalBlockLLR2 N₁ N₂ (S₁ + N₁) (S₂ + N₂) (drift₁ m) (drift₂ m) y ∂(P m) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + S₁ / N₁) + (1 / 2 : ℝ) * Real.log (1 + S₂ / N₂)) := by
    have hLLR2 : ∀ m : ι,
        ∫ y, causalBlockLLR2 N₁ N₂ (S₁ + N₁) (S₂ + N₂) (drift₁ m) (drift₂ m) y ∂(P m) =
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log ((S₁ + N₁) / N₁) - 1 / 2) +
          ((∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift₁ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2)
              ∂ν).toReal + (n : ℝ) * N₁) / (2 * (S₁ + N₁)) +
        ((n : ℝ) * ((1 / 2 : ℝ) * Real.log ((S₂ + N₂) / N₂) - 1 / 2) +
          ((∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2)
              ∂ν).toReal + (n : ℝ) * N₂) / (2 * (S₂ + N₂))) := fun m => (hLLR m).2
    simp_rw [hLLR2]
    rw [Finset.sum_add_distrib, mul_add]
    have hb1 := hbound N₁ S₁ hN₁ hS₁ _ havgE₁
    have hb2 := hbound N₂ S₂ hN₂ hS₂ _ havgE₂
    linarith
  linarith

/-- **2-Output Causal AWGN Feedback Rate Converse (asymptotic)**. -/
theorem causal_awgn2_feedback_rate_le {N₁ N₂ S₁ S₂ R : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂)
    (hach : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
      let ν := (awgnNoise n N₁).prod (awgnNoise n N₂)
      ∃ (drift₁ drift₂ : Fin M → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
        (dec : ((Fin n → ℝ) × (Fin n → ℝ)) → Fin M),
        (∀ m, IsStrictlyCausal2 (drift₁ m)) ∧ (∀ m, IsStrictlyCausal2 (drift₂ m)) ∧
        (∀ m i, Measurable (drift₁ m i)) ∧ (∀ m i, Measurable (drift₂ m i)) ∧
        Measurable dec ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₁ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2) ∂ν ≤
            ENNReal.ofReal ((n : ℝ) * S₁)) ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) z)) ^ 2) ∂ν ≤
            ENNReal.ofReal ((n : ℝ) * S₂)) ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
          ν {z | dec (causalOutput2 (drift₁ m) (drift₂ m) z) ≠ m} ≤ ENNReal.ofReal δ)) :
    R ≤ (1 / 2 : ℝ) * log2 (1 + S₁ / N₁) + (1 / 2 : ℝ) * log2 (1 + S₂ / N₂) := by
  set K := (1 / 2 : ℝ) * Real.log (1 + S₁ / N₁) + (1 / 2 : ℝ) * Real.log (1 + S₂ / N₂) with hK
  have hK0 : 0 ≤ K := add_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [div_nonneg hS₁ hN₁.le])))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [div_nonneg hS₂ hN₂.le])))
  have hrate := rate_le_of_eventually_converse (R := R) (K := K) (c := 1) hK0 (fun δ hδ hδ1 => ?_)
  · unfold log2; rw [hK] at hrate
    have hrw : ((1 / 2 : ℝ) * Real.log (1 + S₁ / N₁) + (1 / 2 : ℝ) * Real.log (1 + S₂ / N₂)) / Real.log 2 =
        (1 / 2 : ℝ) * (Real.log (1 + S₁ / N₁) / Real.log 2) +
        (1 / 2 : ℝ) * (Real.log (1 + S₂ / N₂) / Real.log 2) := by ring
    linarith
  · obtain ⟨n₀, hn₀⟩ := hach δ hδ
    refine eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    set M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
    obtain ⟨drift₁, drift₂, dec, hc₁, hc₂, hm₁, hm₂, hdec, he₁, he₂, herr⟩ := hn₀ n hn
    have hM : 1 ≤ M := le_max_left 1 _
    have hconv := causal_awgn2_feedback_code_converse hN₁ hN₂ hS₁ hS₂ (by simp)
      drift₁ drift₂ hc₁ hc₂ hm₁ hm₂ dec hdec
      (by simpa only [Fintype.card_fin] using he₁) (by simpa only [Fintype.card_fin] using he₂)
    simp only [Fintype.card_fin] at hconv
    have he := ENNReal.toReal_le_of_le_ofReal hδ.le herr
    have hlogM := log_max_one_floor_rpow_two_ge n R
    have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    calc (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2)
        ≤ (1 - δ) * Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlogM0
      _ ≤ (n : ℝ) * K + 1 := hconv

/-! #### 2D Orthogonal Rotation Invariance & Sharp SIMO Feedback Converse -/

/-- 1-letter 2D orthogonal rotation `(a, b) ↦ (c a + s b, -s a + c b)` as a `LinearEquiv`. -/
def rot2DLinearEquiv (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (c * p.1 + s * p.2, -s * p.1 + c * p.2)
  invFun p := (c * p.1 - s * p.2, s * p.1 + c * p.2)
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' r p := by ext <;> dsimp <;> ring
  left_inv p := by
    ext <;> dsimp
    · linear_combination p.1 * hcs
    · linear_combination p.2 * hcs
  right_inv p := by
    ext <;> dsimp
    · linear_combination p.1 * hcs
    · linear_combination p.2 * hcs

lemma det_rot2DLinearEquiv_symm (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    LinearMap.det ((rot2DLinearEquiv c s hcs).symm.toLinearMap) = 1 := by
  let b : Module.Basis (Fin 2) ℝ (ℝ × ℝ) :=
    Module.Basis.ofEquivFun (LinearEquiv.finTwoArrow ℝ ℝ).symm
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, b, Module.Basis.ofEquivFun_repr_apply,
    Module.Basis.coe_ofEquivFun, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_symm,
    LinearEquiv.finTwoArrow_apply, LinearEquiv.finTwoArrow_symm_apply, rot2DLinearEquiv]
  norm_num [Fin.isValue, Pi.single_apply]
  linarith

lemma measurePreserving_rot2D_volume (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    MeasurePreserving (rot2DLinearEquiv c s hcs)
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hmeas : Measurable (rot2DLinearEquiv c s hcs) :=
    (rot2DLinearEquiv c s hcs).toContinuousLinearEquiv.continuous.measurable
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply hmeas hA]
  have hhaar := Measure.addHaar_preimage_linearEquiv (volume : Measure (ℝ × ℝ))
    (rot2DLinearEquiv c s hcs) A
  rw [det_rot2DLinearEquiv_symm c s hcs, abs_one, ENNReal.ofReal_one, one_mul] at hhaar
  exact hhaar

lemma measurePreserving_rot2D_gaussian (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) {N : ℝ} (hN : 0 < N) :
    MeasurePreserving (rot2DLinearEquiv c s hcs)
      ((gaussianReal 0 N.toNNReal).prod (gaussianReal 0 N.toNNReal))
      ((gaussianReal 0 N.toNNReal).prod (gaussianReal 0 N.toNNReal)) := by
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (rot2DLinearEquiv c s hcs).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hvol : MeasurePreserving e
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    measurePreserving_rot2D_volume c s hcs
  have hg : gaussianReal 0 N.toNNReal = volume.withDensity (gaussianPDF 0 N.toNNReal) :=
    gaussianReal_of_var_ne_zero 0 (toNNReal_ne_zero_of_pos' hN)
  have hsf : SigmaFinite (volume.withDensity (gaussianPDF 0 N.toNNReal)) := by
    rw [← hg]; infer_instance
  have hprod : (gaussianReal 0 N.toNNReal).prod (gaussianReal 0 N.toNNReal) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        (fun p => gaussianPDF 0 N.toNNReal p.1 * gaussianPDF 0 N.toNNReal p.2) := by
    rw [hg]
    exact prod_withDensity_eq volume volume (measurable_gaussianPDF 0 N.toNNReal)
      (measurable_gaussianPDF 0 N.toNNReal)
  refine ⟨e.measurable, ?_⟩
  have hpush := map_withDensity_of_measurePreserving e hvol
    (f := fun p : ℝ × ℝ => gaussianPDF 0 N.toNNReal p.1 * gaussianPDF 0 N.toNNReal p.2)
    (((measurable_gaussianPDF 0 N.toNNReal).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 N.toNNReal).comp measurable_snd))
  rw [hprod]
  refine hpush.trans ?_
  congr 1
  funext ⟨a, b⟩
  have he_symm : e.symm (a, b) = (c * a - s * b, s * a + c * b) := rfl
  dsimp only
  rw [he_symm]
  rw [gaussianPDF_eq_ofReal_gaussianPdf1D hN.le, gaussianPDF_eq_ofReal_gaussianPdf1D hN.le,
    gaussianPDF_eq_ofReal_gaussianPdf1D hN.le, gaussianPDF_eq_ofReal_gaussianPdf1D hN.le,
    ← ENNReal.ofReal_mul (gaussianPdf1D_nonneg hN.le _),
    ← ENNReal.ofReal_mul (gaussianPdf1D_nonneg hN.le _)]
  congr 1
  unfold gaussianPdf1D
  have hsq : (c * a - s * b) ^ 2 + (s * a + c * b) ^ 2 = a ^ 2 + b ^ 2 := by
    linear_combination (a ^ 2 + b ^ 2) * hcs
  have hrew : -((c * a - s * b) ^ 2) / (2 * N) + -((s * a + c * b) ^ 2) / (2 * N) =
      -(a ^ 2) / (2 * N) + -(b ^ 2) / (2 * N) := by
    rw [← add_div, ← add_div]
    congr 1
    linarith
  calc (1 / Real.sqrt (2 * Real.pi * N) * Real.exp (-((c * a - s * b) ^ 2) / (2 * N))) *
        (1 / Real.sqrt (2 * Real.pi * N) * Real.exp (-((s * a + c * b) ^ 2) / (2 * N)))
      = (1 / Real.sqrt (2 * Real.pi * N)) * (1 / Real.sqrt (2 * Real.pi * N)) *
        Real.exp (-((c * a - s * b) ^ 2) / (2 * N) + -((s * a + c * b) ^ 2) / (2 * N)) := by
          rw [Real.exp_add]; ring
    _ = (1 / Real.sqrt (2 * Real.pi * N)) * (1 / Real.sqrt (2 * Real.pi * N)) *
        Real.exp (-(a ^ 2) / (2 * N) + -(b ^ 2) / (2 * N)) := by rw [hrew]
    _ = (1 / Real.sqrt (2 * Real.pi * N) * Real.exp (-(a ^ 2) / (2 * N))) *
        (1 / Real.sqrt (2 * Real.pi * N) * Real.exp (-(b ^ 2) / (2 * N))) := by
          rw [Real.exp_add]; ring

/-- Blockwise 2D orthogonal rotation on `(Fin n → ℝ) × (Fin n → ℝ)`. -/
def rot2DBlock {n : ℕ} (c s : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => c * p.1 i + s * p.2 i, fun i => -s * p.1 i + c * p.2 i)

/-- **Blockwise 2D rotation invariance of i.i.d. isotropic Gaussian noise**:
    for `c² + s² = 1` and `N > 0`, `rot2DBlock c s` preserves `(awgnNoise n N).prod (awgnNoise n N)`. -/
theorem measurePreserving_rot2D_awgnNoise {n : ℕ} (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    {N : ℝ} (hN : 0 < N) :
    MeasurePreserving (rot2DBlock (n := n) c s)
      ((awgnNoise n N).prod (awgnNoise n N))
      ((awgnNoise n N).prod (awgnNoise n N)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow n (gaussianReal 0 N.toNNReal)
    (gaussianReal 0 N.toNNReal)
  have h1 := measurePreserving_rot2D_gaussian c s hcs hN
  have hpi : MeasurePreserving (fun w : Fin n → ℝ × ℝ => fun i => rot2DLinearEquiv c s hcs (w i))
      (Measure.pi fun _ : Fin n => (gaussianReal 0 N.toNNReal).prod (gaussianReal 0 N.toNNReal))
      (Measure.pi fun _ : Fin n => (gaussianReal 0 N.toNNReal).prod (gaussianReal 0 N.toNNReal)) :=
    measurePreserving_pi _ _ (fun _ => h1)
  have hcomp : MeasurePreserving
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        e (fun i => rot2DLinearEquiv c s hcs (e.symm p i)))
      ((awgnNoise n N).prod (awgnNoise n N))
      ((awgnNoise n N).prod (awgnNoise n N)) :=
    he.comp (hpi.comp he.symm)
  have hfun : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      e (fun i => rot2DLinearEquiv c s hcs (e.symm p i))) = rot2DBlock c s := by
    funext ⟨y₁, y₂⟩; rfl
  rwa [hfun] at hcomp

/-- **Sharp SIMO Causal AWGN Feedback Converse (finite blocklength, nats)**:
    for two outputs `Y₁ = h₁ X + Z₁`, `Y₂ = h₂ X + Z₂` with independent `Z₁, Z₂ ~ N(0, N)^{⊗n}`,
    strictly causal measurable `X = drift m i (Y₁, Y₂)` of average energy `≤ n P`, and measurable
    decoder `dec`:
    `(1 - avgErr.toReal) * ln |ι| ≤ (n / 2) * ln (1 + (h₁² + h₂²) * P / N) + 1`. -/
theorem causal_simo_awgn_feedback_converse {n : ℕ} {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {h₁ h₂ N P : ℝ} (hN : 0 < N) (hP : 0 ≤ P) (hcard : 1 ≤ Fintype.card ι)
    (drift : ι → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (hcausal : ∀ m, IsStrictlyCausal2 (drift m))
    (hmeas : ∀ m i, Measurable (drift m i))
    (dec : ((Fin n → ℝ) × (Fin n → ℝ)) → ι) (hdec : Measurable dec)
    (henergy : (Fintype.card ι : ℝ≥0∞)⁻¹ *
        ∑ m : ι, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift m i (causalOutput2 (fun i y => h₁ * drift m i y)
            (fun i y => h₂ * drift m i y) z)) ^ 2)
          ∂((awgnNoise n N).prod (awgnNoise n N)) ≤ ENNReal.ofReal ((n : ℝ) * P)) :
    let ν := (awgnNoise n N).prod (awgnNoise n N)
    let out := fun m => causalOutput2 (fun i y => h₁ * drift m i y) (fun i y => h₂ * drift m i y)
    let avgErr : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ m : ι, ν {z | dec (out m z) ≠ m}
    (1 - avgErr.toReal) * Real.log (Fintype.card ι : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N)) + 1 := by
  intro ν out avgErr
  by_cases hr0 : h₁ ^ 2 + h₂ ^ 2 = 0
  · have hh1 : h₁ = 0 := by nlinarith [sq_nonneg h₁, sq_nonneg h₂]
    have hh2 : h₂ = 0 := by nlinarith [sq_nonneg h₁, sq_nonneg h₂]
    have hconv := causal_awgn2_feedback_code_converse hN hN le_rfl le_rfl hcard
      (fun m i y => h₁ * drift m i y) (fun m i y => h₂ * drift m i y)
      (fun m i y y' h => by rw [hh1]; simp) (fun m i y y' h => by rw [hh2]; simp)
      (fun m i => measurable_const.mul (hmeas m i)) (fun m i => measurable_const.mul (hmeas m i))
      dec hdec
      (by simp [hh1]) (by simp [hh2])
    simpa only [hr0, zero_mul, zero_div, add_zero, Real.log_one, mul_zero] using hconv
  · have hr2_pos : 0 < h₁ ^ 2 + h₂ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hr0)
    set r := Real.sqrt (h₁ ^ 2 + h₂ ^ 2) with hr_def
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hr2_pos
    have hr_sq : r ^ 2 = h₁ ^ 2 + h₂ ^ 2 := Real.sq_sqrt hr2_pos.le
    set c := h₁ / r
    set s := h₂ / r
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      simp only [c, s, div_pow, ← add_div, hr_sq, div_self hr2_pos.ne']
    have hcs_inv : c ^ 2 + (-s) ^ 2 = 1 := by simpa using hcs
    -- Rotate outputs by `R = rot2DBlock c s`, inverse `R⁻¹ = rot2DBlock c (-s)`
    have hrot_inv : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
        rot2DBlock c (-s) (rot2DBlock c s w) = w := by
      intro ⟨w₁, w₂⟩
      apply Prod.ext <;> funext i <;> simp only [rot2DBlock]
      · linear_combination (w₁ i) * hcs
      · linear_combination (w₂ i) * hcs
    have hrot_inv' : ∀ w : (Fin n → ℝ) × (Fin n → ℝ),
        rot2DBlock c s (rot2DBlock c (-s) w) = w := by
      intro ⟨w₁, w₂⟩
      apply Prod.ext <;> funext i <;> simp only [rot2DBlock]
      · linear_combination (w₁ i) * hcs
      · linear_combination (w₂ i) * hcs
    have hmeas_rot_inv : Measurable (rot2DBlock (n := n) c (-s)) :=
      (measurable_pi_iff.mpr (fun i => (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)))).prodMk
      (measurable_pi_iff.mpr (fun i => (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))))
    let drift₁' : ι → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
      fun m i w => r * drift m i (rot2DBlock c (-s) w)
    let drift₂' : ι → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
      fun _ _ _ => 0
    let dec' : ((Fin n → ℝ) × (Fin n → ℝ)) → ι := fun w => dec (rot2DBlock c (-s) w)
    have hc₁' : ∀ m, IsStrictlyCausal2 (drift₁' m) := by
      intro m i w w' hw
      dsimp only [drift₁']
      congr 1
      apply hcausal m i
      intro t ht
      obtain ⟨h1, h2⟩ := hw t ht
      simp only [rot2DBlock, h1, h2, and_self]
    have hc₂' : ∀ m, IsStrictlyCausal2 (drift₂' m) := fun _ _ _ _ _ => rfl
    have hm₁' : ∀ m i, Measurable (drift₁' m i) := fun m i =>
      measurable_const.mul ((hmeas m i).comp hmeas_rot_inv)
    have hm₂' : ∀ m i, Measurable (drift₂' m i) := fun _ _ => measurable_const
    have hdec' : Measurable dec' := hdec.comp hmeas_rot_inv
    -- Key algebraic relation: `causalOutput2 (drift₁' m) (drift₂' m) (rot2DBlock c s z) = rot2DBlock c s (out m z)`
    have hout_rot : ∀ m z,
        causalOutput2 (drift₁' m) (drift₂' m) (rot2DBlock c s z) = rot2DBlock c s (out m z) := by
      intro m z
      symm
      apply causalOutput2_unique (hc₁' m) (hc₂' m)
      intro i
      have ho := causalOutput2_eq
        (drift₁ := fun i y => h₁ * drift m i y) (drift₂ := fun i y => h₂ * drift m i y)
        (fun i y y' h => by dsimp only; rw [hcausal m i y y' h])
        (fun i y y' h => by dsimp only; rw [hcausal m i y y' h]) z i
      dsimp only [out] at ho ⊢
      constructor
      · dsimp only [drift₁']
        rw [hrot_inv]
        simp only [rot2DBlock, ho.1, ho.2]
        have hr1 : c * h₁ + s * h₂ = r := by
          simp only [c, s]
          field_simp [hr_pos.ne']
          linarith [hr_sq]
        linear_combination (drift m i (out m z)) * hr1
      · simp only [rot2DBlock, drift₂', zero_add, ho.1, ho.2]
        have hr2 : -s * h₁ + c * h₂ = 0 := by
          simp only [c, s]; ring
        linear_combination (drift m i (out m z)) * hr2
    have hmp_rot := measurePreserving_rot2D_awgnNoise (n := n) c s hcs hN
    -- Transfer energy bound along `hmp_rot`
    have he₁' : (Fintype.card ι : ℝ≥0∞)⁻¹ *
        ∑ m : ι, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₁' m i (causalOutput2 (drift₁' m) (drift₂' m) z)) ^ 2) ∂ν ≤
        ENNReal.ofReal ((n : ℝ) * ((h₁ ^ 2 + h₂ ^ 2) * P)) := by
      have hterm : ∀ m : ι,
          ∫⁻ z, ENNReal.ofReal
            (∑ i : Fin n, (drift₁' m i (causalOutput2 (drift₁' m) (drift₂' m) z)) ^ 2) ∂ν =
          ENNReal.ofReal (h₁ ^ 2 + h₂ ^ 2) *
            ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) ∂ν := by
        intro m
        have hfm : Measurable (fun z => ENNReal.ofReal
            (∑ i : Fin n, (drift₁' m i (causalOutput2 (drift₁' m) (drift₂' m) z)) ^ 2)) :=
          (Finset.measurable_sum _ (fun i _ =>
            ((hm₁' m i).comp (measurable_causalOutput2 (hm₁' m) (hm₂' m))).pow_const 2)).ennreal_ofReal
        rw [← hmp_rot.lintegral_comp hfm]
        have hpt : ∀ z, ENNReal.ofReal (∑ i : Fin n,
            (drift₁' m i (causalOutput2 (drift₁' m) (drift₂' m) (rot2DBlock c s z))) ^ 2) =
            ENNReal.ofReal (h₁ ^ 2 + h₂ ^ 2) *
              ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) := by
          intro z
          rw [hout_rot m z]
          simp only [drift₁', hrot_inv, mul_pow, hr_sq, ← Finset.mul_sum,
            ENNReal.ofReal_mul hr2_pos.le]
        simp_rw [hpt]
        have hm_out : Measurable (fun z => ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2)) :=
          (Finset.measurable_sum _ (fun i _ =>
            ((hmeas m i).comp (measurable_causalOutput2
              (fun i => measurable_const.mul (hmeas m i))
              (fun i => measurable_const.mul (hmeas m i)))).pow_const 2)).ennreal_ofReal
        exact lintegral_const_mul (ENNReal.ofReal (h₁ ^ 2 + h₂ ^ 2)) hm_out
      simp_rw [hterm, ← Finset.mul_sum]
      calc (Fintype.card ι : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (h₁ ^ 2 + h₂ ^ 2) *
            ∑ m : ι, ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) ∂ν)
          = ENNReal.ofReal (h₁ ^ 2 + h₂ ^ 2) * ((Fintype.card ι : ℝ≥0∞)⁻¹ *
            ∑ m : ι, ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) ∂ν) := by ring
        _ ≤ ENNReal.ofReal (h₁ ^ 2 + h₂ ^ 2) * ENNReal.ofReal ((n : ℝ) * P) := by
            gcongr
        _ = ENNReal.ofReal ((n : ℝ) * ((h₁ ^ 2 + h₂ ^ 2) * P)) := by
            rw [← ENNReal.ofReal_mul hr2_pos.le]; congr 1; ring
    have he₂' : (Fintype.card ι : ℝ≥0∞)⁻¹ *
        ∑ m : ι, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift₂' m i (causalOutput2 (drift₁' m) (drift₂' m) z)) ^ 2) ∂ν ≤
        ENNReal.ofReal ((n : ℝ) * 0) := by
      simp [drift₂']
    have hconv := causal_awgn2_feedback_code_converse hN hN (mul_nonneg hr2_pos.le hP) le_rfl hcard
      drift₁' drift₂' hc₁' hc₂' hm₁' hm₂' dec' hdec' he₁' he₂'
    -- Error probabilities match via `hmp_rot`
    have herr_eq : ∀ m : ι,
        ν {z | dec' (causalOutput2 (drift₁' m) (drift₂' m) z) ≠ m} =
        ν {z | dec (out m z) ≠ m} := by
      intro m
      have hs : MeasurableSet {z | dec' (causalOutput2 (drift₁' m) (drift₂' m) z) ≠ m} :=
        (hdec'.comp (measurable_causalOutput2 (hm₁' m) (hm₂' m))) (measurableSet_singleton m).compl
      rw [← hmp_rot.measure_preimage hs.nullMeasurableSet]
      congr 1
      ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hout_rot m z, dec', hrot_inv]
    dsimp only [ν] at herr_eq
    dsimp only at hconv
    simp_rw [herr_eq] at hconv
    have hzero_term : (1 / 2 : ℝ) * Real.log (1 + 0 / N) = 0 := by simp
    rw [hzero_term, add_zero] at hconv
    exact hconv

/-- **Sharp SIMO Causal AWGN Feedback Rate Converse (asymptotic)**. -/
theorem causal_simo_awgn_feedback_rate_le {h₁ h₂ N P R : ℝ} (hN : 0 < N) (hP : 0 ≤ P)
    (hach : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
      let ν := (awgnNoise n N).prod (awgnNoise n N)
      ∃ (drift : Fin M → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
        (dec : ((Fin n → ℝ) × (Fin n → ℝ)) → Fin M),
        (∀ m, IsStrictlyCausal2 (drift m)) ∧
        (∀ m i, Measurable (drift m i)) ∧
        Measurable dec ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∫⁻ z, ENNReal.ofReal
          (∑ i : Fin n, (drift m i (causalOutput2 (fun i y => h₁ * drift m i y)
            (fun i y => h₂ * drift m i y) z)) ^ 2) ∂ν ≤ ENNReal.ofReal ((n : ℝ) * P)) ∧
        ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
          ν {z | dec (causalOutput2 (fun i y => h₁ * drift m i y)
            (fun i y => h₂ * drift m i y) z) ≠ m} ≤ ENNReal.ofReal δ)) :
    R ≤ (1 / 2 : ℝ) * log2 (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N) := by
  set K := (1 / 2 : ℝ) * Real.log (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N) with hK
  have hK0 : 0 ≤ K := by
    have hnn : 0 ≤ (h₁ ^ 2 + h₂ ^ 2) * P / N :=
      div_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hP) hN.le
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hrate := rate_le_of_eventually_converse (R := R) (K := K) (c := 1) hK0 (fun δ hδ hδ1 => ?_)
  · unfold log2; rw [hK] at hrate
    linarith [mul_div_assoc (1 / 2 : ℝ) (Real.log (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N)) (Real.log 2)]
  · obtain ⟨n₀, hn₀⟩ := hach δ hδ
    refine eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    set M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊
    obtain ⟨drift, dec, hcausal, hmeas, hdec, henergy, herr⟩ := hn₀ n hn
    have hM : 1 ≤ M := le_max_left 1 _
    have hconv := causal_simo_awgn_feedback_converse hN hP (by simp)
      drift hcausal hmeas dec hdec (by simpa only [Fintype.card_fin] using henergy)
    simp only [Fintype.card_fin] at hconv
    have he := ENNReal.toReal_le_of_le_ofReal hδ.le herr
    have hlogM := log_max_one_floor_rpow_two_ge n R
    have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    calc (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2)
        ≤ (1 - δ) * Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlogM0
      _ ≤ (n : ℝ) * K + 1 := hconv

end Causal2DConverse

/-! ### 6. Ready-to-Call Corollaries for the Three Wireless Open Problems -/

section WirelessApplications

/-! #### 6A. K-User Gaussian MAC with Feedback -/

/-- **K-User Gaussian MAC with Feedback (finite blocklength converse)**:
    given `K` strictly causal measurable encoders with individual average energies `≤ n P` and
    measurable decoders, `(1 - avgErr.toReal) * ln (∏ j, M j) ≤ (n / 2) * ln (1 + K² P / N) + 1`. -/
theorem gaussian_mac_feedback_code_converse {K n : ℕ} {M : Fin K → ℕ} {P N : ℝ}
    (hN : 0 < N) (hP : 0 ≤ P) (hM : ∀ j, 1 ≤ M j)
    (enc : (j : Fin K) → Fin n → Fin (M j) → (Fin n → ℝ) → ℝ)
    (hcausal : ∀ (j : Fin K) (i : Fin n) (m : Fin (M j)) (y y' : Fin n → ℝ),
      (∀ t : Fin n, t < i → y t = y' t) → enc j i m y = enc j i m y')
    (hm_enc : ∀ j i m, Measurable (enc j i m))
    (dec : (j : Fin K) → (Fin n → ℝ) → Fin (M j))
    (hm_dec : ∀ j, Measurable (dec j))
    (hpow : ∀ j : Fin K,
      ((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : (k : Fin K) → Fin (M k),
        ∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
          (enc j i (m j) (causalOutput (fun i y => ∑ k : Fin K, enc k i (m k) y) z)) ^ 2)
          ∂(awgnNoise n N) ≤ ENNReal.ofReal ((n : ℝ) * P)) :
    let out := fun (m : (k : Fin K) → Fin (M k)) =>
      causalOutput (fun i y => ∑ k : Fin K, enc k i (m k) y)
    let avgErr : ℝ≥0∞ := ((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ m : (k : Fin K) → Fin (M k), awgnNoise n N {z | ∃ j, dec j (out m z) ≠ m j}
    (1 - avgErr.toReal) * Real.log ((∏ k, M k : ℕ) : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + (K : ℝ) ^ 2 * P / N)) + 1 := by
  intro out avgErr
  let ι := (k : Fin K) → Fin (M k)
  let drift : ι → Fin n → (Fin n → ℝ) → ℝ := fun m i y => ∑ k : Fin K, enc k i (m k) y
  have hcard_eq : Fintype.card ι = ∏ k : Fin K, M k := by
    simp [ι]
  have hcard : 1 ≤ Fintype.card ι := by
    rw [hcard_eq]
    exact Finset.one_le_prod (fun k _ => hM k)
  have hdrift_c : ∀ m, IsStrictlyCausal (drift m) := fun m i y y' hy =>
    Finset.sum_congr rfl (fun k _ => hcausal k i (m k) y y' hy)
  have hdrift_m : ∀ m i, Measurable (drift m i) := fun m i =>
    Finset.measurable_sum _ (fun k _ => hm_enc k i (m k))
  let decJoint : (Fin n → ℝ) → ι := fun y j => dec j y
  have hdecJoint : Measurable decJoint := measurable_pi_iff.mpr hm_dec
  have hsq_sum : ∀ (f : Fin K → ℝ), (∑ k : Fin K, f k) ^ 2 ≤ (K : ℝ) * ∑ k : Fin K, (f k) ^ 2 := by
    intro f
    have hnn : 0 ≤ ∑ j : Fin K, ∑ k : Fin K, (f j - f k) ^ 2 :=
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
    have hexp : ∑ j : Fin K, ∑ k : Fin K, (f j - f k) ^ 2 =
        2 * ((K : ℝ) * ∑ k : Fin K, (f k) ^ 2 - (∑ k : Fin K, f k) ^ 2) := by
      have h1 : ∀ j : Fin K, ∑ k : Fin K, (f j - f k) ^ 2 =
          (K : ℝ) * (f j) ^ 2 - (2 * ∑ k : Fin K, f k) * f j + ∑ k : Fin K, (f k) ^ 2 := by
        intro j
        have hsub : ∀ k : Fin K, (f j - f k) ^ 2 = (f j) ^ 2 - (2 * f j) * f k + (f k) ^ 2 := fun k => by ring
        simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    linarith
  have hlint_sum : ∀ (s : Finset (Fin K)) (g : Fin K → (Fin n → ℝ) → ℝ≥0∞),
      (∀ j ∈ s, Measurable (g j)) →
      ∫⁻ x, ∑ j ∈ s, g j x ∂(awgnNoise n N) = ∑ j ∈ s, ∫⁻ x, g j x ∂(awgnNoise n N) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      rw [lintegral_add_left (hg a (Finset.mem_insert_self a s)),
        ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))]
  have htot_energy : (Fintype.card ι : ℝ≥0∞)⁻¹ *
      ∑ m : ι, ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) ∂(awgnNoise n N) ≤
      ENNReal.ofReal ((n : ℝ) * ((K : ℝ) ^ 2 * P)) := by
    rw [hcard_eq]
    have hcs : ∀ m z, ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) ≤
        ENNReal.ofReal (K : ℝ) * ∑ j : Fin K,
          ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2) := by
      intro m z
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => sq_nonneg _)),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      apply ENNReal.ofReal_le_ofReal
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => hsq_sum (fun k => enc k i (m k) (out m z)))
    have hmeas_j : ∀ j m, Measurable (fun z =>
        ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2)) := fun j m =>
      (Finset.measurable_sum _ (fun i _ =>
        ((hm_enc j i (m j)).comp (measurable_causalOutput (hdrift_m m))).pow_const 2)).ennreal_ofReal
    calc ((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ m : ι, ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (drift m i (out m z)) ^ 2) ∂(awgnNoise n N)
        ≤ ((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ m : ι, ∫⁻ z, ENNReal.ofReal (K : ℝ) *
            ∑ j : Fin K, ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2)
            ∂(awgnNoise n N) := by
          gcongr with m z
          exact hcs m z
      _ = ENNReal.ofReal (K : ℝ) * ∑ j : Fin K, (((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ *
          ∑ m : ι, ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2)
            ∂(awgnNoise n N)) := by
          have hstep : ∀ m : ι,
              ∫⁻ z, ENNReal.ofReal (K : ℝ) *
                ∑ j : Fin K, ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2)
                ∂(awgnNoise n N) =
              ENNReal.ofReal (K : ℝ) * ∑ j : Fin K,
                ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2)
                ∂(awgnNoise n N) := by
            intro m
            rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun j _ => hmeas_j j m)),
              hlint_sum Finset.univ (fun j z => ENNReal.ofReal (∑ i : Fin n, (enc j i (m j) (out m z)) ^ 2))
                (fun j _ => hmeas_j j m)]
          simp_rw [hstep, ← Finset.mul_sum]
          rw [Finset.sum_comm, ← mul_assoc, mul_comm ((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ (ENNReal.ofReal (K : ℝ)),
            mul_assoc, Finset.mul_sum]
      _ ≤ ENNReal.ofReal (K : ℝ) * ∑ _j : Fin K, ENNReal.ofReal ((n : ℝ) * P) := by
          gcongr with j
          exact hpow j
      _ = ENNReal.ofReal ((n : ℝ) * ((K : ℝ) ^ 2 * P)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (Nat.cast_nonneg K),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
          congr 1; ring
  have hconv := causal_awgn_feedback_code_converse hN (by positivity) hcard
    drift hdrift_c hdrift_m decJoint hdecJoint htot_energy
  have herr_eq : (Fintype.card ι : ℝ≥0∞)⁻¹ *
      ∑ m : ι, awgnNoise n N {z | decJoint (out m z) ≠ m} = avgErr := by
    simp only [avgErr, hcard_eq]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, decJoint]
    rw [ne_eq, funext_iff, not_forall]
  dsimp only at hconv
  rw [herr_eq, hcard_eq] at hconv
  exact hconv

/-- **K-User Gaussian MAC with Feedback Sum-Rate Converse (asymptotic)**:
    `∑ j, R j ≤ ½ log₂(1 + K² P / N)`. -/
theorem gaussian_mac_feedback_sum_rate_converse {K : ℕ} {P N : ℝ} {R : Fin K → ℝ}
    (hN : 0 < N) (hP : 0 ≤ P)
    (hach : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let M : Fin K → ℕ := fun j => max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R j)⌋₊
      ∃ (enc : (j : Fin K) → Fin n → Fin (M j) → (Fin n → ℝ) → ℝ)
        (dec : (j : Fin K) → (Fin n → ℝ) → Fin (M j)),
        (∀ j i m y y', (∀ t : Fin n, t < i → y t = y' t) → enc j i m y = enc j i m y') ∧
        (∀ j i m, Measurable (enc j i m)) ∧
        (∀ j, Measurable (dec j)) ∧
        (∀ j, ((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : (k : Fin K) → Fin (M k),
          ∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
            (enc j i (m j) (causalOutput (fun i y => ∑ k : Fin K, enc k i (m k) y) z)) ^ 2)
            ∂(awgnNoise n N) ≤ ENNReal.ofReal ((n : ℝ) * P)) ∧
        (((∏ k, M k : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : (k : Fin K) → Fin (M k),
          awgnNoise n N {z | ∃ j, dec j
            (causalOutput (fun i y => ∑ k : Fin K, enc k i (m k) y) z) ≠ m j} ≤
          ENNReal.ofReal δ)) :
    ∑ j : Fin K, R j ≤ (1 / 2 : ℝ) * log2 (1 + (K : ℝ) ^ 2 * P / N) := by
  set Kval := (1 / 2 : ℝ) * Real.log (1 + (K : ℝ) ^ 2 * P / N) with hKval
  have hK0 : 0 ≤ Kval := mul_nonneg (by norm_num)
    (Real.log_nonneg (by linarith [div_nonneg (mul_nonneg (sq_nonneg (K : ℝ)) hP) hN.le]))
  have hrate := rate_le_of_eventually_converse (R := ∑ j : Fin K, R j) (K := Kval) (c := (K : ℝ))
    hK0 (fun δ hδ hδ1 => ?_)
  · unfold log2; rw [hKval] at hrate
    linarith [mul_div_assoc (1 / 2 : ℝ) (Real.log (1 + (K : ℝ) ^ 2 * P / N)) (Real.log 2)]
  · obtain ⟨n₀, hn₀⟩ := hach δ hδ
    refine eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    set M : Fin K → ℕ := fun j => max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R j)⌋₊
    obtain ⟨enc, dec, hc, hme, hmd, hpow, herr⟩ := hn₀ n hn
    have hM : ∀ j, 1 ≤ M j := fun j => le_max_left 1 _
    have hconv := gaussian_mac_feedback_code_converse hN hP hM enc hc hme dec hmd hpow
    have he := ENNReal.toReal_le_of_le_ofReal hδ.le herr
    have hlogM : (((n : ℝ) * (∑ j : Fin K, R j) - (K : ℝ)) * Real.log 2) ≤
        Real.log ((∏ k : Fin K, M k : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod (fun k _ => by positivity [hM k])]
      have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
        log_max_one_floor_rpow_two_ge n (R j))
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
      exact hsum
    have hlogM0 : 0 ≤ Real.log ((∏ k : Fin K, M k : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Finset.one_le_prod (fun k _ => hM k))
    calc (1 - δ) * (((n : ℝ) * (∑ j : Fin K, R j) - (K : ℝ)) * Real.log 2)
        ≤ (1 - δ) * Real.log ((∏ k : Fin K, M k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlogM0
      _ ≤ (n : ℝ) * Kval + 1 := hconv

/-! #### 6B. Two-User Gaussian BC with Feedback -/

/-- **2-User Gaussian BC with Feedback (finite blocklength SIMO converse)**:
    `(1 - avgErr.toReal) * ln (M₁ * M₂) ≤ (n / 2) * ln (1 + (h₁² + h₂²) * P / N) + 1`. -/
theorem gaussian_bc_feedback_code_converse {n M₁ M₂ : ℕ} {h₁ h₂ N P : ℝ}
    (hN : 0 < N) (hP : 0 ≤ P) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (enc : Fin n → Fin M₁ → Fin M₂ → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
    (hcausal : ∀ i m₁ m₂ (y y' : (Fin n → ℝ) × (Fin n → ℝ)),
      (∀ t : Fin n, t < i → y.1 t = y'.1 t ∧ y.2 t = y'.2 t) → enc i m₁ m₂ y = enc i m₁ m₂ y')
    (hm_enc : ∀ i m₁ m₂, Measurable (enc i m₁ m₂))
    (dec₁ : (Fin n → ℝ) → Fin M₁) (dec₂ : (Fin n → ℝ) → Fin M₂)
    (hm_dec₁ : Measurable dec₁) (hm_dec₂ : Measurable dec₂)
    (hpow : ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
        ∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
          (enc i m₁ m₂ (causalOutput2 (fun i y => h₁ * enc i m₁ m₂ y)
            (fun i y => h₂ * enc i m₁ m₂ y) z)) ^ 2)
          ∂((awgnNoise n N).prod (awgnNoise n N)) ≤ ENNReal.ofReal ((n : ℝ) * P)) :
    let ν := (awgnNoise n N).prod (awgnNoise n N)
    let out := fun m₁ m₂ =>
      causalOutput2 (fun i y => h₁ * enc i m₁ m₂ y) (fun i y => h₂ * enc i m₁ m₂ y)
    let avgErr : ℝ≥0∞ := ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
      ν {z | dec₁ (out m₁ m₂ z).1 ≠ m₁ ∨ dec₂ (out m₁ m₂ z).2 ≠ m₂}
    (1 - avgErr.toReal) * Real.log ((M₁ * M₂ : ℕ) : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N)) + 1 := by
  intro ν out avgErr
  let drift : (Fin M₁ × Fin M₂) → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun m i y => enc i m.1 m.2 y
  let dec : ((Fin n → ℝ) × (Fin n → ℝ)) → Fin M₁ × Fin M₂ :=
    fun y => (dec₁ y.1, dec₂ y.2)
  have hcard : 1 ≤ Fintype.card (Fin M₁ × Fin M₂) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hM₁ hM₂
  have henergy : (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ *
      ∑ m : Fin M₁ × Fin M₂, ∫⁻ z, ENNReal.ofReal
        (∑ i : Fin n, (drift m i (causalOutput2 (fun i y => h₁ * drift m i y)
          (fun i y => h₂ * drift m i y) z)) ^ 2) ∂ν ≤ ENNReal.ofReal ((n : ℝ) * P) := by
    simpa [Fintype.card_prod, Fintype.card_fin, Fintype.sum_prod_type, drift] using hpow
  have hconv := causal_simo_awgn_feedback_converse hN hP hcard drift
    (fun m i y y' h => hcausal i m.1 m.2 y y' h) (fun m i => hm_enc i m.1 m.2)
    dec ((hm_dec₁.comp measurable_fst).prodMk (hm_dec₂.comp measurable_snd)) henergy
  have herr_eq : (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ *
      ∑ m : Fin M₁ × Fin M₂, ν {z | dec (causalOutput2 (fun i y => h₁ * drift m i y)
        (fun i y => h₂ * drift m i y) z) ≠ m} = avgErr := by
    simp only [avgErr, Fintype.card_prod, Fintype.card_fin, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl (fun m₁ _ => Finset.sum_congr rfl (fun m₂ _ => ?_))
    congr 1; ext z; simp only [Set.mem_ofPred_eq, dec, drift, out, ne_eq, Prod.mk.injEq]; tauto
  dsimp only at hconv
  rw [herr_eq, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hconv
  exact hconv

/-- **2-User Gaussian BC with Feedback Sum-Rate Converse (asymptotic, sharp SIMO bound)**:
    `R₁ + R₂ ≤ ½ log₂(1 + (h₁² + h₂²) * P / N)`. -/
theorem gaussian_bc_feedback_sum_rate_converse {h₁ h₂ N P R₁ R₂ : ℝ}
    (hN : 0 < N) (hP : 0 ≤ P)
    (hach : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let M₁ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊
      let M₂ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊
      let ν := (awgnNoise n N).prod (awgnNoise n N)
      ∃ (enc : Fin n → Fin M₁ → Fin M₂ → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ)
        (dec₁ : (Fin n → ℝ) → Fin M₁) (dec₂ : (Fin n → ℝ) → Fin M₂),
        (∀ i m₁ m₂ (y y' : (Fin n → ℝ) × (Fin n → ℝ)),
          (∀ t : Fin n, t < i → y.1 t = y'.1 t ∧ y.2 t = y'.2 t) →
            enc i m₁ m₂ y = enc i m₁ m₂ y') ∧
        (∀ i m₁ m₂, Measurable (enc i m₁ m₂)) ∧
        Measurable dec₁ ∧ Measurable dec₂ ∧
        (((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          ∫⁻ z, ENNReal.ofReal (∑ i : Fin n,
            (enc i m₁ m₂ (causalOutput2 (fun i y => h₁ * enc i m₁ m₂ y)
              (fun i y => h₂ * enc i m₁ m₂ y) z)) ^ 2) ∂ν ≤ ENNReal.ofReal ((n : ℝ) * P)) ∧
        (((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          ν {z | dec₁ (causalOutput2 (fun i y => h₁ * enc i m₁ m₂ y)
              (fun i y => h₂ * enc i m₁ m₂ y) z).1 ≠ m₁ ∨
            dec₂ (causalOutput2 (fun i y => h₁ * enc i m₁ m₂ y)
              (fun i y => h₂ * enc i m₁ m₂ y) z).2 ≠ m₂} ≤ ENNReal.ofReal δ)) :
    R₁ + R₂ ≤ (1 / 2 : ℝ) * log2 (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N) := by
  set K := (1 / 2 : ℝ) * Real.log (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N) with hK
  have hK0 : 0 ≤ K := by
    have hnn : 0 ≤ (h₁ ^ 2 + h₂ ^ 2) * P / N :=
      div_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hP) hN.le
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hrate := rate_le_of_eventually_converse (R := R₁ + R₂) (K := K) (c := 2) hK0 (fun δ hδ hδ1 => ?_)
  · unfold log2; rw [hK] at hrate
    linarith [mul_div_assoc (1 / 2 : ℝ) (Real.log (1 + (h₁ ^ 2 + h₂ ^ 2) * P / N)) (Real.log 2)]
  · obtain ⟨n₀, hn₀⟩ := hach δ hδ
    refine eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    set M₁ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊
    set M₂ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊
    obtain ⟨enc, dec₁, dec₂, hc, hme, hmd₁, hmd₂, hpow, herr⟩ := hn₀ n hn
    have hM₁ : 1 ≤ M₁ := le_max_left 1 _
    have hM₂ : 1 ≤ M₂ := le_max_left 1 _
    have hconv := gaussian_bc_feedback_code_converse hN hP hM₁ hM₂ enc hc hme dec₁ dec₂ hmd₁ hmd₂ hpow
    have he := ENNReal.toReal_le_of_le_ofReal hδ.le herr
    have hlogM : (((n : ℝ) * (R₁ + R₂) - 2) * Real.log 2) ≤ Real.log ((M₁ * M₂ : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      linarith [log_max_one_floor_rpow_two_ge n R₁, log_max_one_floor_rpow_two_ge n R₂]
    have hlogM0 : 0 ≤ Real.log ((M₁ * M₂ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.mul_pos hM₁ hM₂)
    calc (1 - δ) * (((n : ℝ) * (R₁ + R₂) - 2) * Real.log 2)
        ≤ (1 - δ) * Real.log ((M₁ * M₂ : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlogM0
      _ ≤ (n : ℝ) * K + 1 := hconv

/-! #### 6C. Three-Node Gaussian Relay Channel Cut-Set Converses -/

/-- Helper: rewriting the `lintegral` relay error probability (written with `∏ i, gaussianPdf1D 1`)
    as the product-measure probability under `(awgnNoise n 1).prod (awgnNoise n 1)`. -/
lemma relay_errProb_lintegral_eq_prod {n : ℕ}
    {P : (Fin n → ℝ) × (Fin n → ℝ) → Prop} [DecidablePred P]
    (hP : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) | P p}) :
    (∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
      if P (zr, z) then
        ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
          (∏ i : Fin n, gaussianPdf1D 1 (z i)))
      else 0) =
    ((awgnNoise n 1).prod (awgnNoise n 1)) {p | P p} := by
  have hd : Measurable (fun u : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (u i))) := by
    have h : (fun u : Fin n → ℝ => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (u i))) =
        fun u => ∏ i : Fin n, gaussianPDF 0 (1 : ℝ).toNNReal (u i) := by
      funext u
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPdf1D_nonneg zero_le_one (u i))]
      exact Finset.prod_congr rfl (fun i _ => (gaussianPDF_eq_ofReal_gaussianPdf1D zero_le_one (u i)).symm)
    rw [h]
    exact Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDF 0 (1 : ℝ).toNNReal).comp (measurable_pi_apply i))
  have hsf : SigmaFinite (volume.withDensity (fun u : Fin n → ℝ =>
      ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (u i)))) := by
    rw [← awgnNoise_eq_withDensity_gaussianPdf1D zero_lt_one]; infer_instance
  have hprod : (awgnNoise n 1).prod (awgnNoise n 1) =
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).withDensity
        (fun p => ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (p.1 i)) *
          ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (p.2 i))) := by
    rw [awgnNoise_eq_withDensity_gaussianPdf1D zero_lt_one]
    exact prod_withDensity_eq volume volume hd hd
  rw [← lintegral_indicator_one hP, hprod,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (p.1 i)) *
          ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (p.2 i)))
      (g := {p | P p}.indicator (1 : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ≥0∞))
      ((hd.comp measurable_fst).mul (hd.comp measurable_snd)) (measurable_const.indicator hP),
    lintegral_prod
      (f := (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (p.1 i)) *
          ENNReal.ofReal (∏ i : Fin n, gaussianPdf1D 1 (p.2 i))) *
        {p | P p}.indicator (1 : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ≥0∞))
      (((hd.comp measurable_fst).mul (hd.comp measurable_snd)).mul
        (measurable_const.indicator hP)).aemeasurable]
  refine lintegral_congr (fun zr => lintegral_congr (fun z => ?_))
  dsimp only [Pi.mul_apply]
  by_cases hp : P (zr, z)
  · have hmem : (zr, z) ∈ {p | P p} := hp
    simp only [hp, ↓reduceIte, Set.indicator_of_mem hmem, Pi.one_apply, mul_one,
      ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => gaussianPdf1D_nonneg zero_le_one (zr i)))]
  · have hmem : (zr, z) ∉ {p | P p} := hp
    simp only [hp, ↓reduceIte, Set.indicator_of_notMem hmem, mul_zero]

/-- Helper: rewriting the `lintegral` relay power constraint (written with `∏ i, gaussianPdf1D 1`)
    as an `awgnNoise n 1` lintegral. -/
lemma relay_power_lintegral_eq_awgnNoise {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable f) :
    (∫⁻ zr : Fin n → ℝ,
      ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) * f zr)) =
    ∫⁻ zr, ENNReal.ofReal (f zr) ∂(awgnNoise n 1) := by
  rw [lintegral_awgnNoise_eq_volume zero_lt_one hf_meas.ennreal_ofReal]
  refine lintegral_congr (fun zr => ?_)
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => gaussianPdf1D_nonneg zero_le_one (zr i)))]

/-- Measurability of the realized relay transmit block `xr m zr i = relay i (g₁₂ * enc m + zr)^{i-1}`. -/
private lemma measurable_relay_xr {n : ℕ} (g₁₂ : ℝ) (x : Fin n → ℝ)
    (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ) (hm_relay : ∀ i, Measurable (relay i)) (i : Fin n) :
    Measurable (fun zr : Fin n → ℝ =>
      relay i (fun j : Fin i.1 => g₁₂ * x ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
        zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) :=
  (hm_relay i).comp (measurable_pi_iff.mpr (fun j =>
    measurable_const.add (measurable_pi_apply (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n))))

/-- **Gaussian Relay Channel — Finite-Blocklength Correlation-Coupled Cut-Set Converse**:
    for any `(n, M)` relay code (`0 < n`, `1 ≤ M`) with source power `∑ x(m)ᵢ² ≤ n P₁` and
    relay expected power `E[∑ X_{r,i}²] ≤ n P₂` (`0 ≤ P₁`, `0 ≤ P₂`), there exists
    `ρ ∈ [-1, 1]` such that BOTH cut-set bounds hold simultaneously:
    1. **BC cut**: `(1 - avgErr) ln M ≤ (n / 2) ln (1 + (g₁₂² + g₁₃²) P₁ (1 - ρ²)) + 1`
    2. **MAC cut**: `(1 - avgErr) ln M ≤ (n / 2) ln (1 + g₁₃² P₁ + g₂₃² P₂ + 2 g₁₃ g₂₃ ρ √(P₁ P₂)) + 1`. -/
theorem gaussian_relay_code_cutset_converse {n M : ℕ} {g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ}
    (hn : 0 < n) (hM : 1 ≤ M) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (enc : Fin M → Fin n → ℝ)
    (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
    (dec : (Fin n → ℝ) → Fin M)
    (hm_relay : ∀ i, Measurable (relay i))
    (hm_dec : Measurable dec)
    (hpow₁ : ∀ m : Fin M, (∑ i : Fin n, (enc m i) ^ 2) ≤ (n : ℝ) * P₁)
    (hpow₂ : ∀ m : Fin M,
      (∫⁻ zr : Fin n → ℝ,
        ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
          ∑ i : Fin n, (relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
            zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2)) ≤ ENNReal.ofReal ((n : ℝ) * P₂)) :
    let errProb (m : Fin M) : ℝ≥0∞ :=
      ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
        let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
        let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
        let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
        let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
        let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
        if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
    let avgErr : ℝ≥0∞ := (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errProb m
    ∃ ρ : ℝ, -1 ≤ ρ ∧ ρ ≤ 1 ∧
      (1 - avgErr.toReal) * Real.log (M : ℝ) ≤
        (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2))) + 1 ∧
      (1 - avgErr.toReal) * Real.log (M : ℝ) ≤
        (n : ℝ) * ((1 / 2 : ℝ) *
          Real.log (1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ + 2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂))) + 1 := by
  intro errProb avgErr
  let ν := (awgnNoise n 1).prod (awgnNoise n 1)
  let xr : Fin M → (Fin n → ℝ) → Fin n → ℝ := fun m zr i =>
    relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ + zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
  have hxr_meas : ∀ m i, Measurable (fun zr => xr m zr i) :=
    fun m i => measurable_relay_xr g₁₂ (enc m) relay hm_relay i
  -- Rewrite power & error probabilities in terms of `awgnNoise n 1`
  have hpow₂' : ∀ m : Fin M,
      ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2) ∂(awgnNoise n 1) ≤
        ENNReal.ofReal ((n : ℝ) * P₂) := by
    intro m
    rw [← relay_power_lintegral_eq_awgnNoise
      (Finset.measurable_sum _ (fun i _ => (hxr_meas m i).pow_const 2))]
    exact hpow₂ m
  have hxr_sq_int : ∀ m i, Integrable (fun zr => (xr m zr i) ^ 2) (awgnNoise n 1) := fun m i =>
    integrable_sq_of_lintegral_sum_sq_lt_top (hxr_meas m)
      (lt_of_le_of_lt (hpow₂' m) ENNReal.ofReal_lt_top) i
  have hxr_int : ∀ m i, Integrable (fun zr => xr m zr i) (awgnNoise n 1) := by
    intro m i
    refine ((hxr_sq_int m i).add (integrable_const 1)).mono' (hxr_meas m i).aestronglyMeasurable
      (ae_of_all _ (fun zr => ?_))
    rw [Real.norm_eq_abs]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (|xr m zr i| - 1), sq_abs (xr m zr i)]
  have herr_eq : ∀ m : Fin M, errProb m =
      ν {p | dec (fun i => g₁₃ * enc m i + g₂₃ * xr m p.1 i + p.2 i) ≠ m} := by
    intro m
    have hmeas_y : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        fun i : Fin n => g₁₃ * enc m i + g₂₃ * xr m p.1 i + p.2 i) :=
      measurable_pi_iff.mpr (fun i =>
        (measurable_const.add (measurable_const.mul ((hxr_meas m i).comp measurable_fst))).add
          ((measurable_pi_apply i).comp measurable_snd))
    have hset : MeasurableSet {p : (Fin n → ℝ) × (Fin n → ℝ) |
        dec (fun i => g₁₃ * enc m i + g₂₃ * xr m p.1 i + p.2 i) ≠ m} :=
      (hm_dec.comp hmeas_y) (measurableSet_singleton m).compl
    exact relay_errProb_lintegral_eq_prod
      (P := fun p => dec (fun i => g₁₃ * enc m i + g₂₃ * xr m p.1 i + p.2 i) ≠ m) hset
  -- Empirical second moments `CX, CXr, CXXr` averaged over `m` and `i`
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set CX : ℝ := (1 / ((M : ℝ) * n)) * ∑ m : Fin M, ∑ i : Fin n, (enc m i) ^ 2
  set CXr : ℝ := (1 / ((M : ℝ) * n)) *
    ∑ m : Fin M, ∑ i : Fin n, ∫ zr, (xr m zr i) ^ 2 ∂(awgnNoise n 1)
  set CXXr : ℝ := (1 / ((M : ℝ) * n)) *
    ∑ m : Fin M, ∑ i : Fin n, enc m i * ∫ zr, xr m zr i ∂(awgnNoise n 1)
  have hCX0 : 0 ≤ CX := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hCXr0 : 0 ≤ CXr := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun i _ =>
      integral_nonneg (fun _ => sq_nonneg _)))
  have hCX_le : CX ≤ P₁ := by
    have hsum : ∑ m : Fin M, ∑ i : Fin n, (enc m i) ^ 2 ≤ (M : ℝ) * ((n : ℝ) * P₁) := by
      calc ∑ m : Fin M, ∑ i : Fin n, (enc m i) ^ 2
          ≤ ∑ _m : Fin M, (n : ℝ) * P₁ := Finset.sum_le_sum (fun m _ => hpow₁ m)
        _ = (M : ℝ) * ((n : ℝ) * P₁) := by simp
    dsimp only [CX]
    rw [one_div, inv_mul_le_iff₀ (mul_pos hMpos hnpos)]
    linarith
  have hCXr_le : CXr ≤ P₂ := by
    have hm_le : ∀ m : Fin M, ∑ i : Fin n, ∫ zr, (xr m zr i) ^ 2 ∂(awgnNoise n 1) ≤ (n : ℝ) * P₂ := by
      intro m
      rw [← integral_finsetSum Finset.univ (fun i _ => hxr_sq_int m i),
        ← integral_sum_sq_eq_toReal_lintegral (hxr_meas m)]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hpow₂' m)
    have hsum : ∑ m : Fin M, ∑ i : Fin n, ∫ zr, (xr m zr i) ^ 2 ∂(awgnNoise n 1) ≤
        (M : ℝ) * ((n : ℝ) * P₂) := by
      calc _ ≤ ∑ _m : Fin M, (n : ℝ) * P₂ := Finset.sum_le_sum (fun m _ => hm_le m)
        _ = (M : ℝ) * ((n : ℝ) * P₂) := by simp
    dsimp only [CXr]
    rw [one_div, inv_mul_le_iff₀ (mul_pos hMpos hnpos)]
    linarith
  -- Key quadratic identity for any linear combination `α * X + β * Xr`
  have hquad : ∀ α β : ℝ,
      (1 / (M : ℝ)) * ∑ m : Fin M,
        (∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (α * enc m i + β * xr m zr i) ^ 2)
          ∂(awgnNoise n 1)).toReal =
      (n : ℝ) * (α ^ 2 * CX + 2 * α * β * CXXr + β ^ 2 * CXr) := by
    intro α β
    have hterm : ∀ m : Fin M,
        (∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (α * enc m i + β * xr m zr i) ^ 2)
          ∂(awgnNoise n 1)).toReal =
        α ^ 2 * (∑ i : Fin n, (enc m i) ^ 2) +
          2 * α * β * (∑ i : Fin n, enc m i * ∫ zr, xr m zr i ∂(awgnNoise n 1)) +
          β ^ 2 * (∑ i : Fin n, ∫ zr, (xr m zr i) ^ 2 ∂(awgnNoise n 1)) := by
      intro m
      have hm_lin : ∀ i, Measurable (fun zr => α * enc m i + β * xr m zr i) := fun i =>
        measurable_const.add (measurable_const.mul (hxr_meas m i))
      rw [integral_sum_sq_eq_toReal_lintegral hm_lin]
      have hint_i : ∀ i, Integrable (fun zr => (α * enc m i + β * xr m zr i) ^ 2) (awgnNoise n 1) := by
        intro i
        have hrew : (fun zr => (α * enc m i + β * xr m zr i) ^ 2) =
            fun zr => (α ^ 2 * (enc m i) ^ 2) + (2 * α * β * enc m i) * xr m zr i +
              β ^ 2 * (xr m zr i) ^ 2 := by funext zr; ring
        rw [hrew]
        exact ((integrable_const _).add ((hxr_int m i).const_mul _)).add
          ((hxr_sq_int m i).const_mul _)
      rw [integral_finsetSum Finset.univ (fun i _ => hint_i i)]
      have hval_i : ∀ i, ∫ zr, (α * enc m i + β * xr m zr i) ^ 2 ∂(awgnNoise n 1) =
          α ^ 2 * (enc m i) ^ 2 + 2 * α * β * (enc m i * ∫ zr, xr m zr i ∂(awgnNoise n 1)) +
            β ^ 2 * ∫ zr, (xr m zr i) ^ 2 ∂(awgnNoise n 1) := by
        intro i
        have hrew : (fun zr => (α * enc m i + β * xr m zr i) ^ 2) =
            fun zr => (α ^ 2 * (enc m i) ^ 2) + (2 * α * β * enc m i) * xr m zr i +
              β ^ 2 * (xr m zr i) ^ 2 := by funext zr; ring
        have h1 : Integrable (fun _ : Fin n → ℝ => α ^ 2 * (enc m i) ^ 2) (awgnNoise n 1) :=
          integrable_const _
        have h2 : Integrable (fun zr => (2 * α * β * enc m i) * xr m zr i) (awgnNoise n 1) :=
          (hxr_int m i).const_mul _
        have h3 : Integrable (fun zr => β ^ 2 * (xr m zr i) ^ 2) (awgnNoise n 1) :=
          (hxr_sq_int m i).const_mul _
        have h12 : Integrable (fun zr => α ^ 2 * (enc m i) ^ 2 + (2 * α * β * enc m i) * xr m zr i)
            (awgnNoise n 1) := h1.add h2
        rw [hrew, integral_add h12 h3, integral_add h1 h2,
          integral_const, integral_const_mul, integral_const_mul]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        ring
      simp_rw [hval_i, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp only [CX, CXXr, CXr]
    field_simp
  -- Quadratic nonnegativity implies Cauchy–Schwarz `CXXr^2 ≤ CX * CXr`
  have hquad_nonneg : ∀ α β : ℝ, 0 ≤ α ^ 2 * CX + 2 * α * β * CXXr + β ^ 2 * CXr := by
    intro α β
    have hnonneg : 0 ≤ (n : ℝ) * (α ^ 2 * CX + 2 * α * β * CXXr + β ^ 2 * CXr) := by
      rw [← hquad α β]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    exact nonneg_of_mul_nonneg_right hnonneg hnpos
  have hCS : CXXr ^ 2 ≤ CX * CXr := by
    by_cases h0 : CXr = 0
    · have h1 : ∀ t : ℝ, 0 ≤ CX + 2 * t * CXXr := fun t => by
        simpa [h0] using hquad_nonneg 1 t
      have hCXXr0 : CXXr = 0 := by
        by_contra hne
        have := h1 (-(CX + 1) / (2 * CXXr))
        have heq : CX + 2 * (-(CX + 1) / (2 * CXXr)) * CXXr = -1 := by field_simp; ring
        linarith
      simp [h0, hCXXr0]
    · have hCXr_pos : 0 < CXr := lt_of_le_of_ne hCXr0 (Ne.symm h0)
      have h := hquad_nonneg CXr (-CXXr)
      have hcalc : CXr ^ 2 * CX + 2 * CXr * -CXXr * CXXr + (-CXXr) ^ 2 * CXr =
          CXr * (CX * CXr - CXXr ^ 2) := by ring
      rw [hcalc] at h
      have := nonneg_of_mul_nonneg_right h hCXr_pos
      linarith
  -- Choose `ρ` and optimal causal-shift weight `a`
  let ρ : ℝ := if h : 0 < P₁ * P₂ then CXXr / Real.sqrt (P₁ * P₂) else 0
  let a : ℝ := if 0 < CXr then CXXr / CXr else 0
  have hρ_sq : ρ ^ 2 ≤ 1 := by
    dsimp only [ρ]
    split_ifs with h
    · rw [div_pow, Real.sq_sqrt h.le, div_le_one h]
      exact hCS.trans (mul_le_mul hCX_le hCXr_le hCXr0 hP₁)
    · norm_num
  have hρ_bounds : -1 ≤ ρ ∧ ρ ≤ 1 := abs_le.mp (by nlinarith [sq_abs ρ])
  have hCXXr_eq : CXXr = ρ * Real.sqrt (P₁ * P₂) := by
    dsimp only [ρ]
    split_ifs with h
    · exact (div_mul_cancel₀ CXXr (Real.sqrt_pos.mpr h).ne').symm
    · have hprod0 : P₁ * P₂ = 0 := le_antisymm (not_lt.mp h) (mul_nonneg hP₁ hP₂)
      have hCXXr0 : CXXr = 0 := by
        have hle : CXXr ^ 2 ≤ 0 := by
          calc CXXr ^ 2 ≤ CX * CXr := hCS
            _ ≤ P₁ * P₂ := mul_le_mul hCX_le hCXr_le hCXr0 hP₁
            _ = 0 := hprod0
        nlinarith [sq_nonneg CXXr]
      simp [hCXXr0]
  have hBC_var_le : CX - 2 * a * CXXr + a ^ 2 * CXr ≤ P₁ * (1 - ρ ^ 2) := by
    dsimp only [a, ρ]
    split_ifs with hCXr_pos hP_pos
    · have hcalc : CX - 2 * (CXXr / CXr) * CXXr + (CXXr / CXr) ^ 2 * CXr = CX - CXXr ^ 2 / CXr := by
        field_simp [hCXr_pos.ne']; ring
      rw [hcalc, div_pow, Real.sq_sqrt hP_pos.le]
      have hP1pos : 0 < P₁ := by nlinarith
      have hP2pos : 0 < P₂ := by nlinarith
      have hdiv_le : CXXr ^ 2 / P₂ ≤ CXXr ^ 2 / CXr :=
        div_le_div_of_nonneg_left (sq_nonneg _) hCXr_pos hCXr_le
      have hrw : P₁ * (1 - CXXr ^ 2 / (P₁ * P₂)) = P₁ - CXXr ^ 2 / P₂ := by
        field_simp [hP1pos.ne', hP2pos.ne']
      rw [hrw]
      linarith
    · have hcalc : CX - 2 * (CXXr / CXr) * CXXr + (CXXr / CXr) ^ 2 * CXr = CX - CXXr ^ 2 / CXr := by
        field_simp [hCXr_pos.ne']; ring
      rw [hcalc]
      have : 0 ≤ CXXr ^ 2 / CXr := div_nonneg (sq_nonneg _) hCXr_pos.le
      nlinarith
    · have hCXr0' : CXr = 0 := le_antisymm (not_lt.mp hCXr_pos) hCXr0
      have hCXXr0 : CXXr = 0 := by
        have hle : CXXr ^ 2 ≤ 0 := by simpa [hCXr0'] using hCS
        nlinarith [sq_nonneg CXXr]
      simp [hCXXr0, hCX_le]
    · simp [hCX_le]
  -- **PART 1: BC Cut via causal shift `(Ỹ_r, Ỹ')` + `causal_simo_awgn_feedback_converse`**
  have hBC_cut : (1 - avgErr.toReal) * Real.log (M : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2))) + 1 := by
    let recDrift : Fin n → (Fin n → ℝ) → ℝ := fun i y =>
      g₁₂ * a * relay i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)
    have hrec_c : IsStrictlyCausal recDrift := by
      intro i y y' hy
      dsimp only [recDrift]
      congr 2
      funext j
      exact hy ⟨j.1, Nat.lt_trans j.2 i.2⟩ j.2
    have hrec_m : ∀ i, Measurable (recDrift i) := fun i =>
      measurable_const.mul ((hm_relay i).comp
        (measurable_pi_iff.mpr (fun j => measurable_pi_apply (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n))))
    let recoverYr : (Fin n → ℝ) → (Fin n → ℝ) := causalOutput recDrift
    have hrec_meas : Measurable recoverYr := measurable_causalOutput hrec_m
    -- Effective SIMO drift `X̃_m i (ỹ_r, ỹ') = enc m i - a * relay i (recoverYr ỹ_r)^{i-1}`
    let simoDrift : Fin M → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
      fun m i y => enc m i - a * relay i (fun j => recoverYr y.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩)
    have hsimo_c : ∀ m, IsStrictlyCausal2 (simoDrift m) := by
      intro m i y y' hy
      dsimp only [simoDrift]
      congr 2
      congr 1
      funext j
      exact causalOutput_congr_lt hrec_c (k := i.1) (fun t ht => (hy t ht).1)
        ⟨j.1, Nat.lt_trans j.2 i.2⟩ j.2
    have hsimo_m : ∀ m i, Measurable (simoDrift m i) := fun m i =>
      measurable_const.sub (measurable_const.mul ((hm_relay i).comp
        (measurable_pi_iff.mpr (fun j =>
          (measurable_pi_apply (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n)).comp
            (hrec_meas.comp measurable_fst)))))
    -- Enhanced measurable decoder recovering `Y` from `(Ỹ_r, Ỹ')`
    let decBC : ((Fin n → ℝ) × (Fin n → ℝ)) → Fin M := fun y =>
      dec (fun i => y.2 i + (g₂₃ + g₁₃ * a) *
        relay i (fun j => recoverYr y.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩))
    have hdecBC : Measurable decBC :=
      hm_dec.comp (measurable_pi_iff.mpr (fun i =>
        ((measurable_pi_apply i).comp measurable_snd).add
          (measurable_const.mul ((hm_relay i).comp
            (measurable_pi_iff.mpr (fun j =>
              (measurable_pi_apply (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n)).comp
                (hrec_meas.comp measurable_fst)))))))
    -- Key identity: under SIMO output `w = out m (zr, z)`, `recoverYr w.1 = yr`, `simoDrift = enc - a * xr`, `decBC w = dec y`
    let outSIMO := fun m =>
      causalOutput2 (fun i y => g₁₂ * simoDrift m i y) (fun i y => g₁₃ * simoDrift m i y)
    have hout_id : ∀ m (p : (Fin n → ℝ) × (Fin n → ℝ)),
        recoverYr (outSIMO m p).1 = (fun i => g₁₂ * enc m i + p.1 i) ∧
        (∀ i, simoDrift m i (outSIMO m p) = enc m i - a * xr m p.1 i) ∧
        decBC (outSIMO m p) = dec (fun i => g₁₃ * enc m i + g₂₃ * xr m p.1 i + p.2 i) := by
      intro m p
      have h1 : recoverYr (outSIMO m p).1 = (fun i => g₁₂ * enc m i + p.1 i) := by
        funext t
        have hrec_eq := causalOutput_eq hrec_c (outSIMO m p).1 t
        have ho := (causalOutput2_eq
          (drift₁ := fun i y => g₁₂ * simoDrift m i y)
          (drift₂ := fun i y => g₁₃ * simoDrift m i y)
          (fun i y y' h => by dsimp only; rw [hsimo_c m i y y' h])
          (fun i y y' h => by dsimp only; rw [hsimo_c m i y y' h]) p t).1
        change recoverYr (outSIMO m p).1 t = recDrift t (recoverYr (outSIMO m p).1) + (outSIMO m p).1 t at hrec_eq
        rw [hrec_eq, ho]
        dsimp only [recDrift, simoDrift]
        ring
      have h2 : ∀ i, simoDrift m i (outSIMO m p) = enc m i - a * xr m p.1 i := by
        intro i; dsimp only [simoDrift, xr]; rw [h1]
      refine ⟨h1, h2, ?_⟩
      dsimp only [decBC]
      congr 1
      funext i
      have ho2 := (causalOutput2_eq
        (drift₁ := fun i y => g₁₂ * simoDrift m i y)
        (drift₂ := fun i y => g₁₃ * simoDrift m i y)
        (fun i y y' h => by dsimp only; rw [hsimo_c m i y y' h])
        (fun i y y' h => by dsimp only; rw [hsimo_c m i y y' h]) p i).2
      rw [ho2, h2 i, h1]
      dsimp only [xr]
      ring
    -- Energy bound for `simoDrift`
    have hP1_eff : 0 ≤ P₁ * (1 - ρ ^ 2) := mul_nonneg hP₁ (by linarith)
    have hsimo_energy : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ *
        ∑ m : Fin M, ∫⁻ p, ENNReal.ofReal (∑ i : Fin n, (simoDrift m i (outSIMO m p)) ^ 2) ∂ν ≤
        ENNReal.ofReal ((n : ℝ) * (P₁ * (1 - ρ ^ 2))) := by
      have hterm : ∀ m : Fin M,
          ∫⁻ p, ENNReal.ofReal (∑ i : Fin n, (simoDrift m i (outSIMO m p)) ^ 2) ∂ν =
          ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m zr i) ^ 2)
            ∂(awgnNoise n 1) := by
        intro m
        have hpt : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
            ENNReal.ofReal (∑ i : Fin n, (simoDrift m i (outSIMO m p)) ^ 2) =
            ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m p.1 i) ^ 2) := by
          intro p
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [(hout_id m p).2.1 i]; ring
        simp_rw [hpt]
        have hm' : Measurable (fun zr : Fin n → ℝ =>
            ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m zr i) ^ 2)) :=
          (Finset.measurable_sum _ (fun i _ =>
            (measurable_const.add (measurable_const.mul (hxr_meas m i))).pow_const 2)).ennreal_ofReal
        rw [lintegral_prod
          (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
            ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m p.1 i) ^ 2))
          (hm'.comp measurable_fst).aemeasurable]
        simp
      simp_rw [hterm, Fintype.card_fin]
      have hlt_top : ∀ m : Fin M,
          ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m zr i) ^ 2)
            ∂(awgnNoise n 1) < ⊤ := by
        intro m
        have hle : ∀ zr, ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m zr i) ^ 2) ≤
            ENNReal.ofReal (2 * ∑ i : Fin n, (enc m i) ^ 2) +
              ENNReal.ofReal (2 * a ^ 2) * ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2) := by
          intro zr
          rw [← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [sq_nonneg (enc m i + a * xr m zr i)]
        calc ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m zr i) ^ 2)
              ∂(awgnNoise n 1)
            ≤ ∫⁻ zr, (ENNReal.ofReal (2 * ∑ i : Fin n, (enc m i) ^ 2) +
                ENNReal.ofReal (2 * a ^ 2) * ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2))
                ∂(awgnNoise n 1) := lintegral_mono hle
          _ = ENNReal.ofReal (2 * ∑ i : Fin n, (enc m i) ^ 2) +
                ENNReal.ofReal (2 * a ^ 2) *
                  ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2) ∂(awgnNoise n 1) := by
              rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                lintegral_const_mul _ (Finset.measurable_sum _
                  (fun i _ => (hxr_meas m i).pow_const 2)).ennreal_ofReal]
          _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
              ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                (lt_of_le_of_lt (hpow₂' m) ENNReal.ofReal_lt_top)⟩
      have hfin_lhs : ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
          ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (1 * enc m i + (-a) * xr m zr i) ^ 2)
            ∂(awgnNoise n 1)) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)))
          (ENNReal.sum_ne_top.mpr (fun m _ => (hlt_top m).ne))
      rw [← ENNReal.ofReal_toReal hfin_lhs]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_sum (fun m _ => (hlt_top m).ne), ← one_div, hquad 1 (-a)]
      have hsimp : 1 ^ 2 * CX + 2 * 1 * -a * CXXr + (-a) ^ 2 * CXr =
          CX - 2 * a * CXXr + a ^ 2 * CXr := by ring
      rw [hsimp]
      exact mul_le_mul_of_nonneg_left hBC_var_le (Nat.cast_nonneg n)
    have hconv := causal_simo_awgn_feedback_converse zero_lt_one hP1_eff
      (by simp [hM]) simoDrift hsimo_c hsimo_m decBC hdecBC hsimo_energy
    have herr_match : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ *
        ∑ m : Fin M, ν {p | decBC (outSIMO m p) ≠ m} = avgErr := by
      simp only [avgErr, Fintype.card_fin]
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [herr_eq m]
      congr 1; ext p
      simp only [Set.mem_ofPred_eq, (hout_id m p).2.2]
    dsimp only [ν, outSIMO] at herr_match
    dsimp only at hconv
    rw [herr_match, Fintype.card_fin] at hconv
    simpa only [div_one, mul_assoc] using hconv
  -- **PART 2: MAC Cut via `causal_awgn2_feedback_code_converse` with `drift₁ = 0`, `drift₂ = g₁₃ X + g₂₃ X_r`**
  have hMAC_cut : (1 - avgErr.toReal) * Real.log (M : ℝ) ≤
      (n : ℝ) * ((1 / 2 : ℝ) *
        Real.log (1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ + 2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂))) + 1 := by
    let drift₁ : Fin M → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun _ _ _ => 0
    let drift₂ : Fin M → Fin n → ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
      fun m i y => g₁₃ * enc m i +
        g₂₃ * relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
          y.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩)
    have hc₁ : ∀ m, IsStrictlyCausal2 (drift₁ m) := fun _ _ _ _ _ => rfl
    have hc₂ : ∀ m, IsStrictlyCausal2 (drift₂ m) := by
      intro m i y y' hy
      dsimp only [drift₂]
      congr 2
      congr 1
      funext j
      rw [(hy ⟨j.1, Nat.lt_trans j.2 i.2⟩ j.2).1]
    have hm₁ : ∀ m i, Measurable (drift₁ m i) := fun _ _ => measurable_const
    have hm₂ : ∀ m i, Measurable (drift₂ m i) := fun m i =>
      measurable_const.add (measurable_const.mul ((hxr_meas m i).comp measurable_fst))
    let decMAC : ((Fin n → ℝ) × (Fin n → ℝ)) → Fin M := fun y => dec y.2
    have hdecMAC : Measurable decMAC := hm_dec.comp measurable_snd
    -- Explicit form of `causalOutput2 (drift₁ m) (drift₂ m) (zr, z)`
    have houtMAC : ∀ m (p : (Fin n → ℝ) × (Fin n → ℝ)),
        causalOutput2 (drift₁ m) (drift₂ m) p =
          (p.1, fun i => g₁₃ * enc m i + g₂₃ * xr m p.1 i + p.2 i) := by
      intro m p
      symm
      apply causalOutput2_unique (hc₁ m) (hc₂ m)
      intro i
      exact ⟨by simp [drift₁], by simp [drift₂, xr]⟩
    set S_mac : ℝ := g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ + 2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂)
    have hS_mac_ge : g₁₃ ^ 2 * CX + 2 * g₁₃ * g₂₃ * CXXr + g₂₃ ^ 2 * CXr ≤ S_mac := by
      dsimp only [S_mac]
      rw [hCXXr_eq]
      nlinarith [sq_nonneg g₁₃, sq_nonneg g₂₃]
    have hS_mac_nonneg : 0 ≤ S_mac := le_trans (hquad_nonneg g₁₃ g₂₃) hS_mac_ge
    have he₁ : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ *
        ∑ m : Fin M, ∫⁻ p, ENNReal.ofReal
          (∑ i : Fin n, (drift₁ m i (causalOutput2 (drift₁ m) (drift₂ m) p)) ^ 2) ∂ν ≤
        ENNReal.ofReal ((n : ℝ) * 0) := by simp [drift₁]
    have he₂ : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ *
        ∑ m : Fin M, ∫⁻ p, ENNReal.ofReal
          (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) p)) ^ 2) ∂ν ≤
        ENNReal.ofReal ((n : ℝ) * S_mac) := by
      have hterm : ∀ m : Fin M,
          ∫⁻ p, ENNReal.ofReal
            (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) p)) ^ 2) ∂ν =
          ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m zr i) ^ 2)
            ∂(awgnNoise n 1) := by
        intro m
        have hpt : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
            ENNReal.ofReal (∑ i : Fin n, (drift₂ m i (causalOutput2 (drift₁ m) (drift₂ m) p)) ^ 2) =
            ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m p.1 i) ^ 2) := by
          intro p; rw [houtMAC m p]
        simp_rw [hpt]
        have hm' : Measurable (fun zr : Fin n → ℝ =>
            ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m zr i) ^ 2)) :=
          (Finset.measurable_sum _ (fun i _ =>
            (measurable_const.add (measurable_const.mul (hxr_meas m i))).pow_const 2)).ennreal_ofReal
        rw [lintegral_prod
          (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
            ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m p.1 i) ^ 2))
          (hm'.comp measurable_fst).aemeasurable]
        simp
      simp_rw [hterm, Fintype.card_fin]
      have hlt_top : ∀ m : Fin M,
          ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m zr i) ^ 2)
            ∂(awgnNoise n 1) < ⊤ := by
        intro m
        have hle : ∀ zr, ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m zr i) ^ 2) ≤
            ENNReal.ofReal (2 * g₁₃ ^ 2 * ∑ i : Fin n, (enc m i) ^ 2) +
              ENNReal.ofReal (2 * g₂₃ ^ 2) * ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2) := by
          intro zr
          rw [← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [sq_nonneg (g₁₃ * enc m i - g₂₃ * xr m zr i)]
        calc ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m zr i) ^ 2)
              ∂(awgnNoise n 1)
            ≤ ∫⁻ zr, (ENNReal.ofReal (2 * g₁₃ ^ 2 * ∑ i : Fin n, (enc m i) ^ 2) +
                ENNReal.ofReal (2 * g₂₃ ^ 2) * ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2))
                ∂(awgnNoise n 1) := lintegral_mono hle
          _ = ENNReal.ofReal (2 * g₁₃ ^ 2 * ∑ i : Fin n, (enc m i) ^ 2) +
                ENNReal.ofReal (2 * g₂₃ ^ 2) *
                  ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (xr m zr i) ^ 2) ∂(awgnNoise n 1) := by
              rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                lintegral_const_mul _ (Finset.measurable_sum _
                  (fun i _ => (hxr_meas m i).pow_const 2)).ennreal_ofReal]
          _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
              ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                (lt_of_le_of_lt (hpow₂' m) ENNReal.ofReal_lt_top)⟩
      have hfin_lhs : ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M,
          ∫⁻ zr, ENNReal.ofReal (∑ i : Fin n, (g₁₃ * enc m i + g₂₃ * xr m zr i) ^ 2)
            ∂(awgnNoise n 1)) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hM)))
          (ENNReal.sum_ne_top.mpr (fun m _ => (hlt_top m).ne))
      rw [← ENNReal.ofReal_toReal hfin_lhs]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_sum (fun m _ => (hlt_top m).ne), ← one_div, hquad g₁₃ g₂₃]
      exact mul_le_mul_of_nonneg_left hS_mac_ge (Nat.cast_nonneg n)
    have hconv := causal_awgn2_feedback_code_converse zero_lt_one zero_lt_one le_rfl hS_mac_nonneg
      (by simp [hM]) drift₁ drift₂ hc₁ hc₂ hm₁ hm₂ decMAC hdecMAC he₁ he₂
    have herr_match : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ *
        ∑ m : Fin M, ν {p | decMAC (causalOutput2 (drift₁ m) (drift₂ m) p) ≠ m} = avgErr := by
      simp only [avgErr, Fintype.card_fin]
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [herr_eq m]
      congr 1; ext p
      simp only [Set.mem_ofPred_eq, houtMAC m p, decMAC]
    dsimp only [ν] at herr_match
    dsimp only at hconv
    rw [herr_match, Fintype.card_fin] at hconv
    have harg : 1 + S_mac / 1 =
        1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ + 2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂) := by
      dsimp only [S_mac]; ring
    simpa only [zero_div, add_zero, Real.log_one, mul_zero, zero_add, harg] using hconv
  exact ⟨ρ, hρ_bounds.1, hρ_bounds.2, hBC_cut, hMAC_cut⟩

/-- **Gaussian Relay Channel — Coupled Cut-Set Converse (asymptotic)**:
    for any upper bound `B ≥ 0` dominating the correlation-coupled Cover–El Gamal cut-set bound
    for all `ρ ∈ [-1, 1]`, every operationally achievable relay rate satisfies `R ≤ B`. -/
theorem gaussian_relay_cutset_converse_coupled {g₁₂ g₁₃ g₂₃ P₁ P₂ R B : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hB0 : 0 ≤ B)
    (hB : ∀ ρ : ℝ, -1 ≤ ρ → ρ ≤ 1 →
      min ((1 / 2 : ℝ) * log2 (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2)))
          ((1 / 2 : ℝ) * log2 (1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ +
            2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂))) ≤ B)
    (hach : ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : Fin M → Fin n → ℝ)
        (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
        (dec : (Fin n → ℝ) → Fin M),
        (∀ i : Fin n, Measurable (relay i)) ∧
        Measurable dec ∧
        (∀ m : Fin M, (∑ i : Fin n, (enc m i) ^ 2) ≤ (n : ℝ) * P₁) ∧
        (∀ m : Fin M,
          (∫⁻ zr : Fin n → ℝ,
            ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
              ∑ i : Fin n, (relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
                zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2)) ≤ ENNReal.ofReal ((n : ℝ) * P₂)) ∧
        let errProb (m : Fin M) : ℝ≥0∞ :=
          ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
            let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
            let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
            let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
            let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
            let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
            if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
        (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errProb m ≤ ENNReal.ofReal ε) :
    R ≤ B := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ B * Real.log 2 := mul_nonneg hB0 hlog2.le
  have hrate := rate_le_of_eventually_converse (R := R) (K := B * Real.log 2) (c := 1) hK0
    (fun δ hδ hδ1 => ?_)
  · rwa [mul_div_cancel_right₀ _ hlog2.ne'] at hrate
  · obtain ⟨N, hNpos, hN⟩ := hach δ hδ
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hn_pos : 0 < n := lt_of_lt_of_le hNpos hn
    set M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    obtain ⟨enc, relay, dec, hm_r, hm_d, hp₁, hp₂, herr⟩ := hN n hn
    have hM : 1 ≤ M := le_max_left 1 _
    obtain ⟨ρ, hρ1, hρ2, hbc, hmac⟩ :=
      gaussian_relay_code_cutset_converse (g₁₂ := g₁₂) (g₁₃ := g₁₃) (g₂₃ := g₂₃)
        hn_pos hM hP₁ hP₂ enc relay dec hm_r hm_d hp₁ hp₂
    have hmin_div : ∀ a b c : ℝ, 0 ≤ c → min a b / c = min (a / c) (b / c) := fun a b c hc => by
      rcases le_total a b with h | h
      · simp [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h hc)]
      · simp [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h hc)]
    have hmin_le : min ((1 / 2 : ℝ) * Real.log (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2)))
        ((1 / 2 : ℝ) * Real.log (1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ +
          2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂))) ≤ B * Real.log 2 := by
      have h := hB ρ hρ1 hρ2
      unfold log2 at h
      have h' : min ((1 / 2 : ℝ) * Real.log (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2)))
          ((1 / 2 : ℝ) * Real.log (1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ +
            2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂))) / Real.log 2 ≤ B := by
        rw [hmin_div _ _ _ hlog2.le]
        simpa only [mul_div_assoc] using h
      rwa [div_le_iff₀ hlog2] at h'
    let errP (m : Fin M) : ℝ≥0∞ :=
      ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
        let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
        let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
        let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
        let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
        let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
        if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
    have hcomb : (1 - ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errP m).toReal) * Real.log (M : ℝ) ≤
        (n : ℝ) * (B * Real.log 2) + 1 := by
      have hle_min : (1 - ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errP m).toReal) * Real.log (M : ℝ) ≤
          (n : ℝ) * min ((1 / 2 : ℝ) * Real.log (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2)))
            ((1 / 2 : ℝ) * Real.log (1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ +
              2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂))) + 1 := by
        rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg n), min_add]
        exact le_min hbc hmac
      exact le_trans hle_min (by nlinarith)
    have he := ENNReal.toReal_le_of_le_ofReal hδ.le herr
    have hlogM := log_max_one_floor_rpow_two_ge n R
    have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    calc (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2)
        ≤ (1 - δ) * Real.log (M : ℝ) := mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlogM0
      _ ≤ (n : ℝ) * (B * Real.log 2) + 1 := hcomb

/-- **Gaussian Relay Channel — BC Cut-Set Converse**:
    `R ≤ ½ log₂(1 + (g₁₂² + g₁₃²) P₁)`. -/
theorem gaussian_relay_cutset_converse_bc {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hach : ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : Fin M → Fin n → ℝ)
        (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
        (dec : (Fin n → ℝ) → Fin M),
        (∀ i : Fin n, Measurable (relay i)) ∧
        Measurable dec ∧
        (∀ m : Fin M, (∑ i : Fin n, (enc m i) ^ 2) ≤ (n : ℝ) * P₁) ∧
        (∀ m : Fin M,
          (∫⁻ zr : Fin n → ℝ,
            ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
              ∑ i : Fin n, (relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
                zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2)) ≤ ENNReal.ofReal ((n : ℝ) * P₂)) ∧
        let errProb (m : Fin M) : ℝ≥0∞ :=
          ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
            let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
            let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
            let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
            let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
            let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
            if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
        (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errProb m ≤ ENNReal.ofReal ε) :
    R ≤ (1 / 2 : ℝ) * log2 (1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine gaussian_relay_cutset_converse_coupled hP₁ hP₂ ?_ ?_ hach
  · unfold log2
    have : 1 ≤ 1 + (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ := by nlinarith [sq_nonneg g₁₂, sq_nonneg g₁₃]
    exact mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg this) hlog2.le)
  · intro ρ hρ1 hρ2
    refine le_trans (min_le_left _ _) ?_
    unfold log2
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply div_le_div_of_nonneg_right _ hlog2.le
    apply Real.log_le_log
    · have h1m : 0 ≤ 1 - ρ ^ 2 := by nlinarith
      have hgp : 0 ≤ (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ := mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hP₁
      have hprod : 0 ≤ (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * (1 - ρ ^ 2) := mul_nonneg hgp h1m
      linarith
    · have hgp : 0 ≤ (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ := mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hP₁
      have hprod : 0 ≤ (g₁₂ ^ 2 + g₁₃ ^ 2) * P₁ * ρ ^ 2 := mul_nonneg hgp (sq_nonneg ρ)
      linarith

/-- **Gaussian Relay Channel — MAC Cut-Set Converse**:
    `R ≤ ½ log₂(1 + (|g₁₃| √P₁ + |g₂₃| √P₂)²)`. -/
theorem gaussian_relay_cutset_converse_mac {g₁₂ g₁₃ g₂₃ P₁ P₂ R : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hach : ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : Fin M → Fin n → ℝ)
        (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
        (dec : (Fin n → ℝ) → Fin M),
        (∀ i : Fin n, Measurable (relay i)) ∧
        Measurable dec ∧
        (∀ m : Fin M, (∑ i : Fin n, (enc m i) ^ 2) ≤ (n : ℝ) * P₁) ∧
        (∀ m : Fin M,
          (∫⁻ zr : Fin n → ℝ,
            ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
              ∑ i : Fin n, (relay i (fun j => g₁₂ * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
                zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2)) ≤ ENNReal.ofReal ((n : ℝ) * P₂)) ∧
        let errProb (m : Fin M) : ℝ≥0∞ :=
          ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
            let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
            let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
            let yr (i : Fin n) : ℝ := g₁₂ * enc m i + zr i
            let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
            let y (i : Fin n) : ℝ := g₁₃ * enc m i + g₂₃ * xr i + z i
            if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
        (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errProb m ≤ ENNReal.ofReal ε) :
    R ≤ (1 / 2 : ℝ) * log2 (1 + (|g₁₃| * Real.sqrt P₁ + |g₂₃| * Real.sqrt P₂) ^ 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine gaussian_relay_cutset_converse_coupled hP₁ hP₂ ?_ ?_ hach
  · unfold log2
    have : 1 ≤ 1 + (|g₁₃| * Real.sqrt P₁ + |g₂₃| * Real.sqrt P₂) ^ 2 := by nlinarith [sq_nonneg (|g₁₃| * Real.sqrt P₁ + |g₂₃| * Real.sqrt P₂)]
    exact mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg this) hlog2.le)
  · intro ρ hρ1 hρ2
    refine le_trans (min_le_right _ _) ?_
    unfold log2
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply div_le_div_of_nonneg_right _ hlog2.le
    have hsqrt : Real.sqrt (P₁ * P₂) = Real.sqrt P₁ * Real.sqrt P₂ := Real.sqrt_mul hP₁ P₂
    have hpos : 0 < 1 + g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂ + 2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂) := by
      have h1 : |g₁₃ * g₂₃ * ρ| ≤ |g₁₃| * |g₂₃| := by
        rw [abs_mul, abs_mul]
        exact mul_le_of_le_one_right (by positivity) (abs_le.mpr ⟨hρ1, hρ2⟩)
      have h2 : -(g₁₃ ^ 2 * P₁ + g₂₃ ^ 2 * P₂) ≤ 2 * g₁₃ * g₂₃ * ρ * Real.sqrt (P₁ * P₂) := by
        rw [hsqrt]
        have habs : |g₁₃ * g₂₃ * ρ * (Real.sqrt P₁ * Real.sqrt P₂)| ≤
            |g₁₃| * Real.sqrt P₁ * (|g₂₃| * Real.sqrt P₂) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
          calc |g₁₃ * g₂₃ * ρ| * (Real.sqrt P₁ * Real.sqrt P₂)
              ≤ (|g₁₃| * |g₂₃|) * (Real.sqrt P₁ * Real.sqrt P₂) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = |g₁₃| * Real.sqrt P₁ * (|g₂₃| * Real.sqrt P₂) := by ring
        have hsq : 0 ≤ (|g₁₃| * Real.sqrt P₁ - |g₂₃| * Real.sqrt P₂) ^ 2 := sq_nonneg _
        have hsq1 : (|g₁₃| * Real.sqrt P₁) ^ 2 = g₁₃ ^ 2 * P₁ := by
          rw [mul_pow, sq_abs, Real.sq_sqrt hP₁]
        have hsq2 : (|g₂₃| * Real.sqrt P₂) ^ 2 = g₂₃ ^ 2 * P₂ := by
          rw [mul_pow, sq_abs, Real.sq_sqrt hP₂]
        have hneg := neg_le_of_abs_le habs
        nlinarith
      linarith
    apply Real.log_le_log hpos
    rw [hsqrt]
    have hsq1 : (|g₁₃| * Real.sqrt P₁) ^ 2 = g₁₃ ^ 2 * P₁ := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hP₁]
    have hsq2 : (|g₂₃| * Real.sqrt P₂) ^ 2 = g₂₃ ^ 2 * P₂ := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hP₂]
    have hprod_le : g₁₃ * g₂₃ * ρ ≤ |g₁₃| * |g₂₃| := by
      calc g₁₃ * g₂₃ * ρ ≤ |g₁₃ * g₂₃ * ρ| := le_abs_self _
        _ = |g₁₃| * |g₂₃| * |ρ| := by rw [abs_mul, abs_mul]
        _ ≤ |g₁₃| * |g₂₃| * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hρ1, hρ2⟩) (by positivity)
        _ = |g₁₃| * |g₂₃| := mul_one _
    have hmul : 2 * (g₁₃ * g₂₃ * ρ) * (Real.sqrt P₁ * Real.sqrt P₂) ≤
        2 * (|g₁₃| * |g₂₃|) * (Real.sqrt P₁ * Real.sqrt P₂) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith

/-- **El Gamal–Mohseni–Zahedi (2006) Table II Unit-Gain Energy-per-Bit Lower Bound**:
    at unit gains `g₁₂ = g₁₃ = g₂₃ = 1` with `P₁ > 0, P₂ > 0, R > 0`, every achievable rate
    satisfies `(3 / 4) * (2 * ln 2) ≤ (P₁ + P₂) / R`. -/
theorem gaussian_relay_unit_energy_per_bit_ge {P₁ P₂ R : ℝ}
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) (hR : 0 < R)
    (hach : ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : Fin M → Fin n → ℝ)
        (relay : ∀ i : Fin n, (Fin i.1 → ℝ) → ℝ)
        (dec : (Fin n → ℝ) → Fin M),
        (∀ i : Fin n, Measurable (relay i)) ∧
        Measurable dec ∧
        (∀ m : Fin M, (∑ i : Fin n, (enc m i) ^ 2) ≤ (n : ℝ) * P₁) ∧
        (∀ m : Fin M,
          (∫⁻ zr : Fin n → ℝ,
            ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (zr i)) *
              ∑ i : Fin n, (relay i (fun j => 1 * enc m ⟨j.1, Nat.lt_trans j.2 i.2⟩ +
                zr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2)) ≤ ENNReal.ofReal ((n : ℝ) * P₂)) ∧
        let errProb (m : Fin M) : ℝ≥0∞ :=
          ∫⁻ zr : Fin n → ℝ, ∫⁻ z : Fin n → ℝ,
            let gzr := ∏ i : Fin n, gaussianPdf1D 1 (zr i)
            let gz := ∏ i : Fin n, gaussianPdf1D 1 (z i)
            let yr (i : Fin n) : ℝ := 1 * enc m i + zr i
            let xr (i : Fin n) : ℝ := relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)
            let y (i : Fin n) : ℝ := 1 * enc m i + 1 * xr i + z i
            if dec y ≠ m then ENNReal.ofReal (gzr * gz) else 0
        (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, errProb m ≤ ENNReal.ofReal ε) :
    (3 / 4 : ℝ) * (2 * Real.log 2) ≤ (P₁ + P₂) / R := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR_le : R ≤ (4 / 3 : ℝ) * (P₁ + P₂) / (2 * Real.log 2) := by
    refine gaussian_relay_cutset_converse_coupled hP₁.le hP₂.le (by positivity) ?_ hach
    intro ρ hρ1 hρ2
    unfold log2
    have hlog_le : ∀ u : ℝ, -1 < u → Real.log (1 + u) ≤ u := fun u hu => by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u)]
    have h1 : (1 / 2 : ℝ) * (Real.log (1 + (1 ^ 2 + 1 ^ 2) * P₁ * (1 - ρ ^ 2)) / Real.log 2) ≤
        (2 * P₁ * (1 - ρ ^ 2)) / (2 * Real.log 2) := by
      have h1m : 0 ≤ 1 - ρ ^ 2 := by nlinarith
      have hpos : -1 < (1 ^ 2 + 1 ^ 2) * P₁ * (1 - ρ ^ 2) := by
        have : 0 ≤ (1 ^ 2 + 1 ^ 2) * P₁ * (1 - ρ ^ 2) := by positivity
        linarith
      have h := hlog_le _ hpos
      have hrw : (1 / 2 : ℝ) * (Real.log (1 + (1 ^ 2 + 1 ^ 2) * P₁ * (1 - ρ ^ 2)) / Real.log 2) =
          Real.log (1 + (1 ^ 2 + 1 ^ 2) * P₁ * (1 - ρ ^ 2)) / (2 * Real.log 2) := by ring
      rw [hrw]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : (1 / 2 : ℝ) * (Real.log (1 + 1 ^ 2 * P₁ + 1 ^ 2 * P₂ +
        2 * 1 * 1 * ρ * Real.sqrt (P₁ * P₂)) / Real.log 2) ≤
        (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) / (2 * Real.log 2) := by
      have hsqrt : Real.sqrt (P₁ * P₂) = Real.sqrt P₁ * Real.sqrt P₂ := Real.sqrt_mul hP₁.le P₂
      have hnonneg : 0 ≤ P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂) := by
        rw [hsqrt]
        have hsq : 0 ≤ (Real.sqrt P₁ + ρ * Real.sqrt P₂) ^ 2 := sq_nonneg _
        have h1m : 0 ≤ (1 - ρ ^ 2) * P₂ := mul_nonneg (by nlinarith) hP₂.le
        have h1' : Real.sqrt P₁ ^ 2 = P₁ := Real.sq_sqrt hP₁.le
        have h2' : Real.sqrt P₂ ^ 2 = P₂ := Real.sq_sqrt hP₂.le
        nlinarith
      have harg : 1 + 1 ^ 2 * P₁ + 1 ^ 2 * P₂ + 2 * 1 * 1 * ρ * Real.sqrt (P₁ * P₂) =
          1 + (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) := by ring
      rw [harg]
      have h := hlog_le (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) (by linarith)
      have hrw : (1 / 2 : ℝ) * (Real.log (1 + (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂))) / Real.log 2) =
          Real.log (1 + (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂))) / (2 * Real.log 2) := by ring
      rw [hrw]
      exact div_le_div_of_nonneg_right h (by positivity)
    -- Convex combination `(1/3) * (2 P₁ (1 - ρ²)) + (2/3) * (P₁ + P₂ + 2 ρ √(P₁ P₂)) = (4/3)(P₁+P₂) - (2/3)(√P₂ - ρ√P₁)²`
    have hcomb : min (2 * P₁ * (1 - ρ ^ 2)) (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) ≤
        (4 / 3 : ℝ) * (P₁ + P₂) := by
      have hsqrt : Real.sqrt (P₁ * P₂) = Real.sqrt P₁ * Real.sqrt P₂ := Real.sqrt_mul hP₁.le P₂
      have hsq : 0 ≤ (Real.sqrt P₂ - ρ * Real.sqrt P₁) ^ 2 := sq_nonneg _
      have h1' : Real.sqrt P₁ ^ 2 = P₁ := Real.sq_sqrt hP₁.le
      have h2' : Real.sqrt P₂ ^ 2 = P₂ := Real.sq_sqrt hP₂.le
      have hconvex : (1 / 3 : ℝ) * (2 * P₁ * (1 - ρ ^ 2)) +
          (2 / 3 : ℝ) * (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) ≤ (4 / 3 : ℝ) * (P₁ + P₂) := by
        rw [hsqrt]
        nlinarith
      have hml := min_le_left (2 * P₁ * (1 - ρ ^ 2)) (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂))
      have hmr := min_le_right (2 * P₁ * (1 - ρ ^ 2)) (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂))
      linarith
    have hmin_div : ∀ a b c : ℝ, 0 ≤ c → min a b / c = min (a / c) (b / c) := fun a b c hc => by
      rcases le_total a b with h | h
      · simp [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h hc)]
      · simp [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h hc)]
    calc min ((1 / 2 : ℝ) * (Real.log (1 + (1 ^ 2 + 1 ^ 2) * P₁ * (1 - ρ ^ 2)) / Real.log 2))
            ((1 / 2 : ℝ) * (Real.log (1 + 1 ^ 2 * P₁ + 1 ^ 2 * P₂ +
              2 * 1 * 1 * ρ * Real.sqrt (P₁ * P₂)) / Real.log 2))
        ≤ min ((2 * P₁ * (1 - ρ ^ 2)) / (2 * Real.log 2))
            ((P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) / (2 * Real.log 2)) :=
          min_le_min h1 h2
      _ = min (2 * P₁ * (1 - ρ ^ 2)) (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) / (2 * Real.log 2) :=
          (hmin_div _ _ _ (by positivity)).symm
      _ ≤ (4 / 3 : ℝ) * (P₁ + P₂) / (2 * Real.log 2) :=
          div_le_div_of_nonneg_right hcomb (by positivity)
  rw [le_div_iff₀ hR]
  rw [le_div_iff₀ (by positivity)] at hR_le
  linarith

end WirelessApplications

end InfoTheory.Bridge
