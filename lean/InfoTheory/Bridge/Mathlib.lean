import InfoTheory.Core
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.InformationTheory.Hamming
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Bridge Between `InfoTheory.Core` and Mathlib's `InformationTheory`

Non-destructive bridge layer connecting our finite-alphabet `ProbDist`, `DMC`,
`klDivergence`, `shannonEntropy`, `mutualInfo`, and `hammingDistVec` definitions
to Mathlib's standard library:

1. `PMF` and `MeasureTheory.Measure` (`toPMF`, `toMeasure`)
2. `ProbabilityTheory.Kernel` (`dmcToKernel`)
3. `InformationTheory.klDiv` (Gibbs' inequality, equality iff `P = Q`, data processing
   inequality for deterministic maps and noisy channels)
4. Cover & Thomas Chapter 2 foundational theorems derived via Mathlib's `klDiv`:
   - `shannonEntropy_nonneg`, `shannonEntropy_le_log2_card`, `shannonEntropy_eq_log2_card_iff`
   - `mutualInfo_eq_klDivergence`, `mutualInfo_nonneg`, `mutualInfo_eq_zero_iff_indep`
   - `condEntropy_le_shannonEntropy` (conditioning reduces entropy)
   - `mutualInfo_map_right_le`, `mutualInfo_channel_right_le` (Data Processing Inequality for `I(X; Y)`)
5. `Mathlib.InformationTheory.Hamming.hammingDist`
6. `InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`
   (Kraft–McMillan inequality, Cover & Thomas Theorem 5.5.1)

This module is purely additive and leaves `Core/`, `Problems/`, and `STATEMENT_LOCK.json`
untouched so parallel work in `Known/` and `Solutions/` can import it freely.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace InfoTheory.Bridge

/-! ### 1. Bridging `ProbDist` to Mathlib `PMF` and `Measure` -/

section ProbDistBridge

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Convert a finite distribution `P : ProbDist α` into a Mathlib `PMF α`. -/
noncomputable def toPMF (P : ProbDist α) : PMF α :=
  ⟨fun a => ENNReal.ofReal (P.pmf a), by
    convert hasSum_fintype (fun a => ENNReal.ofReal (P.pmf a))
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => P.nonneg a), P.sum_one, ENNReal.ofReal_one]⟩

@[simp]
lemma toPMF_apply (P : ProbDist α) (a : α) : toPMF P a = ENNReal.ofReal (P.pmf a) := rfl

/-- Convert a finite distribution `P : ProbDist α` into a Mathlib probability measure. -/
noncomputable def toMeasure [MeasurableSpace α] (P : ProbDist α) : Measure α :=
  (toPMF P).toMeasure

instance isProbabilityMeasure_toMeasure [MeasurableSpace α] (P : ProbDist α) :
    IsProbabilityMeasure (toMeasure P) :=
  PMF.toMeasure.isProbabilityMeasure (toPMF P)

@[simp]
lemma toMeasure_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : ProbDist α) (a : α) :
    toMeasure P {a} = ENNReal.ofReal (P.pmf a) := by
  simp [toMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]

lemma toMeasure_eq_iff [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbDist α) :
    toMeasure P = toMeasure Q ↔ P = Q := by
  constructor
  · intro h
    cases P with | mk pmfP hP0 hP1 =>
    cases Q with | mk pmfQ hQ0 hQ1 =>
    congr
    funext a
    have hsing : ENNReal.ofReal (pmfP a) = ENNReal.ofReal (pmfQ a) := by
      have := congrArg (fun μ : Measure α => μ {a}) h
      simpa [toMeasure_singleton] using this
    exact (ENNReal.ofReal_eq_ofReal_iff (hP0 a) (hQ0 a)).mp hsing
  · intro h; subst h; rfl

lemma toMeasure_absCont_iff [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (P Q : ProbDist α) :
    toMeasure P ≪ toMeasure Q ↔ AbsCont P Q := by
  constructor
  · intro hac a hQ0
    have hQa : toMeasure Q {a} = 0 := by simp [hQ0]
    have hPa : toMeasure P {a} = 0 := hac hQa
    simp only [toMeasure_singleton, ENNReal.ofReal_eq_zero] at hPa
    exact le_antisymm hPa (P.nonneg a)
  · intro hac s hQs
    rw [toMeasure, PMF.toMeasure_apply _ MeasurableSet.of_discrete] at hQs ⊢
    rw [tsum_eq_zero_iff] at hQs ⊢
    intro a
    have hQa := hQs a
    by_cases ha : a ∈ s
    · simp only [Set.indicator_of_mem ha, toPMF_apply, ENNReal.ofReal_eq_zero] at hQa ⊢
      have hQ0 : Q.pmf a = 0 := le_antisymm hQa (Q.nonneg a)
      rw [hac a hQ0]
    · simp [Set.indicator_of_notMem ha]

lemma toMeasure_map [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (f : α → β) (P : ProbDist α) :
    toMeasure (P.map f) = (toMeasure P).map f := by
  classical
  ext s _
  rw [Measure.map_apply (measurable_of_countable f) MeasurableSet.of_discrete]
  rw [toMeasure, toMeasure,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete]
  rw [tsum_fintype, tsum_fintype]
  have h1 : ∀ b : β, s.indicator (toPMF (P.map f)) b =
      ∑ a : α, if b ∈ s ∧ f a = b then ENNReal.ofReal (P.pmf a) else 0 := by
    intro b
    by_cases hb : b ∈ s
    · simp only [Set.indicator_of_mem hb, toPMF_apply, ProbDist.map, hb, true_and]
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by split_ifs; exact P.nonneg a; exact le_rfl)]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    · simp [hb]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hfa : f a ∈ s
  · have hmem : a ∈ f ⁻¹' s := hfa
    rw [Set.indicator_of_mem hmem, toPMF_apply, Finset.sum_eq_single (f a)]
    · simp [hfa]
    · intro b _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hnotmem : a ∉ f ⁻¹' s := hfa
    have hzero : ∀ b : β, ¬ (b ∈ s ∧ f a = b) := fun b ⟨hb, heq⟩ => hfa (heq ▸ hb)
    rw [Set.indicator_of_notMem hnotmem]
    simp [hzero]

/-! ### 2. Bridging `DMC` to Mathlib `ProbabilityTheory.Kernel` -/

/-- Row distribution `W(· | x)` of a DMC `W` as a `ProbDist β`. -/
def dmcRow (W : DMC α β) (x : α) : ProbDist β where
  pmf := W.trans x
  nonneg := W.nonneg x
  sum_one := W.sum_one x

/-- Convert a `DMC α β` into a Mathlib Markov kernel `Kernel α β`. -/
noncomputable def dmcToKernel [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (W : DMC α β) : Kernel α β :=
  Kernel.ofFunOfCountable (fun x => toMeasure (dmcRow W x))

instance isMarkovKernel_dmcToKernel [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (W : DMC α β) :
    IsMarkovKernel (dmcToKernel W) where
  isProbabilityMeasure x := isProbabilityMeasure_toMeasure (dmcRow W x)

lemma dmcToKernel_comp_toMeasure [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (W : DMC α β) (P : ProbDist α) :
    dmcToKernel W ∘ₘ toMeasure P = toMeasure (W.joint P).snd := by
  ext s _
  rw [Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)]
  rw [show toMeasure (W.joint P).snd s = (toPMF (W.joint P).snd).toMeasure s from rfl,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete, tsum_fintype]
  rw [lintegral_fintype]
  have hrow : ∀ x : α, (dmcToKernel W x) s =
      ∑ y : β, s.indicator (fun y => ENNReal.ofReal (W.trans x y)) y := fun x => by
    change toMeasure (dmcRow W x) s = _
    rw [toMeasure, PMF.toMeasure_apply _ MeasurableSet.of_discrete, tsum_fintype]
    rfl
  simp_rw [hrow, toMeasure_singleton, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ s
  · simp only [Set.indicator_of_mem hy, toPMF_apply, ProbDist.snd, DMC.joint]
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (P.nonneg x) (W.nonneg x y))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_mul (P.nonneg x), mul_comm]
  · simp [Set.indicator_of_notMem hy]

/-! ### 3. Bridging `klDivergence` to Mathlib's `InformationTheory.klDiv` -/

lemma klDivergence_eq_toReal_klDiv [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (P Q : ProbDist α) (hac : AbsCont P Q) :
    Real.log 2 * klDivergence P Q =
      (InformationTheory.klDiv (toMeasure P) (toMeasure Q)).toReal := by
  have hμν : toMeasure P ≪ toMeasure Q := (toMeasure_absCont_iff P Q).mpr hac
  have heq_univ : toMeasure P Set.univ = toMeasure Q Set.univ := by simp
  rw [InformationTheory.toReal_klDiv_of_measure_eq hμν heq_univ]
  rw [integral_fintype Integrable.of_finite]
  unfold klDivergence log2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hreal : (toMeasure P).real {a} = P.pmf a := by
    simp [Measure.real, toMeasure_singleton, ENNReal.toReal_ofReal (P.nonneg a)]
  rw [smul_eq_mul, hreal]
  by_cases hPa : P.pmf a ≤ 0
  · have hP0 : P.pmf a = 0 := le_antisymm hPa (P.nonneg a)
    simp [hP0]
  · have hPpos : 0 < P.pmf a := lt_of_not_ge hPa
    have hQpos : 0 < Q.pmf a := lt_of_le_of_ne (Q.nonneg a) (fun h => by
      have := hac a h.symm; linarith)
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hPa)]
    have hrn : ((toMeasure P).rnDeriv (toMeasure Q) a).toReal = P.pmf a / Q.pmf a := by
      have h1 : (toMeasure P).rnDeriv (toMeasure Q) a =
          (toMeasure P {a}) / (toMeasure Q {a}) := by
        have hcount : toMeasure P {a} = (toMeasure P).rnDeriv (toMeasure Q) a * toMeasure Q {a} := by
          have := Measure.setLIntegral_rnDeriv hμν {a}
          rw [lintegral_singleton] at this
          exact this.symm
        have hQne0 : toMeasure Q {a} ≠ 0 := by
          simp [toMeasure_singleton, ENNReal.ofReal_pos.mpr hQpos |>.ne']
        have hQneTop : toMeasure Q {a} ≠ ⊤ := measure_ne_top _ _
        exact (ENNReal.eq_div_iff hQne0 hQneTop).mpr (by rw [mul_comm]; exact hcount.symm)
      rw [h1, toMeasure_singleton, toMeasure_singleton, ENNReal.toReal_div,
        ENNReal.toReal_ofReal (P.nonneg a), ENNReal.toReal_ofReal (Q.nonneg a)]
    have hllr : MeasureTheory.llr (toMeasure P) (toMeasure Q) a =
        Real.log (P.pmf a / Q.pmf a) := by
      rw [MeasureTheory.llr_def]; dsimp only; rw [hrn]
    rw [hllr]
    field_simp [hlog2]

/-- **Gibbs' Inequality** (Cover & Thomas, Theorem 2.6.3), inherited directly from Mathlib's
    `InformationTheory.klDiv`: `D(P ‖ Q) ≥ 0` whenever `P ≪ Q`. -/
theorem klDivergence_nonneg (P Q : ProbDist α) (hac : AbsCont P Q) :
    0 ≤ klDivergence P Q := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  have h := klDivergence_eq_toReal_klDiv P Q hac
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnonneg : 0 ≤ Real.log 2 * klDivergence P Q := by
    rw [h]; exact ENNReal.toReal_nonneg
  exact nonneg_of_mul_nonneg_right hnonneg hlog2

/-- **KL Divergence Equality Case** (Cover & Thomas, Theorem 2.6.3), inherited directly from
    Mathlib's `InformationTheory.klDiv_eq_zero_iff`: `D(P ‖ Q) = 0 ↔ P = Q` whenever `P ≪ Q`. -/
theorem klDivergence_eq_zero_iff (P Q : ProbDist α) (hac : AbsCont P Q) :
    klDivergence P Q = 0 ↔ P = Q := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  have hμν : toMeasure P ≪ toMeasure Q := (toMeasure_absCont_iff P Q).mpr hac
  have hfin : InformationTheory.klDiv (toMeasure P) (toMeasure Q) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hμν (Integrable.of_finite)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [← mul_eq_zero_iff_left hlog2, klDivergence_eq_toReal_klDiv P Q hac,
    ENNReal.toReal_eq_zero_iff]
  simp only [hfin, or_false]
  rw [InformationTheory.klDiv_eq_zero_iff, toMeasure_eq_iff]

/-- **Data Processing Inequality for Deterministic Maps** (Cover & Thomas, §2.8),
    inherited directly from Mathlib's `InformationTheory.klDiv_map_le`. -/
theorem klDivergence_map_le (f : α → β) (P Q : ProbDist α) (hac : AbsCont P Q) :
    klDivergence (P.map f) (Q.map f) ≤ klDivergence P Q := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace β := ⊤
  have _ : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
  have hμν : toMeasure P ≪ toMeasure Q := (toMeasure_absCont_iff P Q).mpr hac
  have hac_map : AbsCont (P.map f) (Q.map f) := by
    rw [← toMeasure_absCont_iff, toMeasure_map, toMeasure_map]
    exact hμν.map (measurable_of_countable f)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine le_of_mul_le_mul_left ?_ hlog2
  rw [klDivergence_eq_toReal_klDiv _ _ hac_map, klDivergence_eq_toReal_klDiv _ _ hac,
    toMeasure_map, toMeasure_map]
  exact ENNReal.toReal_mono (InformationTheory.klDiv_ne_top hμν Integrable.of_finite)
    (InformationTheory.klDiv_map_le (toMeasure P) (toMeasure Q) (measurable_of_countable f))

/-- **Data Processing Inequality for Noisy Channels (DMCs)** (Cover & Thomas, §2.8),
    inherited directly from Mathlib's `InformationTheory.klDiv_comp_right_le`:
    `D(W P ‖ W Q) ≤ D(P ‖ Q)`. -/
theorem klDivergence_channel_le (W : DMC α β) (P Q : ProbDist α) (hac : AbsCont P Q) :
    klDivergence (W.joint P).snd (W.joint Q).snd ≤ klDivergence P Q := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace β := ⊤
  have _ : DiscreteMeasurableSpace β := ⟨fun _ => trivial⟩
  have hμν : toMeasure P ≪ toMeasure Q := (toMeasure_absCont_iff P Q).mpr hac
  have hdpi := InformationTheory.klDiv_comp_right_le (toMeasure P) (toMeasure Q) (dmcToKernel W)
  rw [dmcToKernel_comp_toMeasure, dmcToKernel_comp_toMeasure] at hdpi
  have hfin : InformationTheory.klDiv (toMeasure P) (toMeasure Q) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hμν Integrable.of_finite
  have hfin_out : InformationTheory.klDiv (toMeasure (W.joint P).snd)
      (toMeasure (W.joint Q).snd) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin hdpi
  have hac_out : AbsCont (W.joint P).snd (W.joint Q).snd :=
    (toMeasure_absCont_iff _ _).mp (InformationTheory.klDiv_ne_top_iff.mp hfin_out).1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine le_of_mul_le_mul_left ?_ hlog2
  rw [klDivergence_eq_toReal_klDiv _ _ hac_out, klDivergence_eq_toReal_klDiv _ _ hac]
  exact ENNReal.toReal_mono hfin hdpi

/-! ### 4. Cover & Thomas Chapter 2 Corollaries via Mathlib's `klDiv` -/

lemma pmf_le_one (P : ProbDist α) (a : α) : P.pmf a ≤ 1 := by
  calc P.pmf a
    _ ≤ ∑ x : α, P.pmf x :=
        Finset.single_le_sum (fun x _ => P.nonneg x) (Finset.mem_univ a)
    _ = 1 := P.sum_one

/-- **Non-negativity of Shannon Entropy** (Cover & Thomas, Lemma 2.1.1): `H(X) ≥ 0`. -/
theorem shannonEntropy_nonneg (P : ProbDist α) : 0 ≤ shannonEntropy P := by
  unfold shannonEntropy negPLogP log2
  refine Finset.sum_nonneg fun a _ => ?_
  by_cases hp : P.pmf a ≤ 0
  · simp [hp]
  · simp only [ite_eq_right_iff.mpr (fun h => absurd h hp)]
    have hpos : 0 < P.pmf a := lt_of_not_ge hp
    have hle1 : P.pmf a ≤ 1 := pmf_le_one P a
    have hlogp : Real.log (P.pmf a) ≤ 0 := Real.log_nonpos (le_of_lt hpos) hle1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : Real.log (P.pmf a) / Real.log 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlogp (le_of_lt hlog2)
    nlinarith

/-- Any distribution on a nonempty finite type is absolutely continuous w.r.t. the uniform distribution. -/
lemma absCont_uniform [Nonempty α] (P : ProbDist α) : AbsCont P ProbDist.uniform := by
  intro a h0
  exfalso
  simp [ProbDist.uniform] at h0

/-- Identity `D(P ‖ Unif) = log₂ |α| - H(P)` (Cover & Thomas, Theorem 2.6.4 proof). -/
lemma klDivergence_uniform [Nonempty α] (P : ProbDist α) :
    klDivergence P ProbDist.uniform = log2 (Fintype.card α : ℝ) - shannonEntropy P := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard
  have hterm : ∀ a : α,
      (if P.pmf a ≤ 0 then (0 : ℝ) else P.pmf a * log2 (P.pmf a / ProbDist.uniform.pmf a)) =
        P.pmf a * log2 (Fintype.card α : ℝ) - negPLogP (P.pmf a) := by
    intro a
    by_cases hp : P.pmf a ≤ 0
    · have hp0 : P.pmf a = 0 := le_antisymm hp (P.nonneg a)
      simp [hp0, negPLogP]
    · have hpos : 0 < P.pmf a := lt_of_not_ge hp
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hp), negPLogP, ProbDist.uniform, log2]
      rw [one_div, div_inv_eq_mul, Real.log_mul (ne_of_gt hpos) hcard_ne]
      ring
  unfold klDivergence shannonEntropy
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_one, one_mul]

/-- **Maximum Entropy Bound** (Cover & Thomas, Theorem 2.6.4): `H(X) ≤ log₂ |α|`. -/
theorem shannonEntropy_le_log2_card [Nonempty α] (P : ProbDist α) :
    shannonEntropy P ≤ log2 (Fintype.card α : ℝ) := by
  have h := klDivergence_nonneg P ProbDist.uniform (absCont_uniform P)
  rw [klDivergence_uniform] at h
  linarith

/-- **Maximum Entropy Equality Case** (Cover & Thomas, Theorem 2.6.4):
    `H(X) = log₂ |α| ↔ P = Unif`. -/
theorem shannonEntropy_eq_log2_card_iff [Nonempty α] (P : ProbDist α) :
    shannonEntropy P = log2 (Fintype.card α : ℝ) ↔ P = ProbDist.uniform := by
  rw [← klDivergence_eq_zero_iff P ProbDist.uniform (absCont_uniform P), klDivergence_uniform]
  constructor <;> intro h <;> linarith

/-- Every joint distribution `P_{XY}` is absolutely continuous w.r.t. the product of its marginals `P_X × P_Y`. -/
lemma absCont_prod_marginals (P : ProbDist (α × β)) : AbsCont P (P.fst.prod P.snd) := by
  intro ⟨a, b⟩ h0
  simp only [ProbDist.prod, mul_eq_zero] at h0
  rcases h0 with hfst | hsnd
  · have hle : P.pmf (a, b) ≤ P.fst.pmf a :=
      Finset.single_le_sum (fun b' _ => P.nonneg (a, b')) (Finset.mem_univ b)
    linarith [P.nonneg (a, b)]
  · have hle : P.pmf (a, b) ≤ P.snd.pmf b :=
      Finset.single_le_sum (fun a' _ => P.nonneg (a', b)) (Finset.mem_univ a)
    linarith [P.nonneg (a, b)]

/-- **Mutual Information as KL Divergence** (Cover & Thomas, Eq. 2.28):
    `I(X; Y) = D(P_{XY} ‖ P_X × P_Y)`. -/
theorem mutualInfo_eq_klDivergence (P : ProbDist (α × β)) :
    mutualInfo P = klDivergence P (P.fst.prod P.snd) := by
  have hlog2_mul : ∀ x y : ℝ, 0 < x → 0 < y → log2 (x * y) = log2 x + log2 y := fun x y hx hy => by
    unfold log2; rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy), add_div]
  have hlog2_div : ∀ x y : ℝ, 0 < x → 0 < y → log2 (x / y) = log2 x - log2 y := fun x y hx hy => by
    unfold log2; rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy), sub_div]
  have hterm : ∀ ab : α × β,
      (if P.pmf ab ≤ 0 then (0 : ℝ) else P.pmf ab * log2 (P.pmf ab / (P.fst.prod P.snd).pmf ab)) =
        -negPLogP (P.pmf ab) - P.pmf ab * log2 (P.fst.pmf ab.1) - P.pmf ab * log2 (P.snd.pmf ab.2) := by
    intro ⟨a, b⟩
    by_cases hp : P.pmf (a, b) ≤ 0
    · have hp0 : P.pmf (a, b) = 0 := le_antisymm hp (P.nonneg (a, b))
      simp [hp0, negPLogP]
    · have hpos : 0 < P.pmf (a, b) := lt_of_not_ge hp
      have hfst : 0 < P.fst.pmf a := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun b' _ => P.nonneg (a, b')) (Finset.mem_univ b))
      have hsnd : 0 < P.snd.pmf b := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun a' _ => P.nonneg (a', b)) (Finset.mem_univ a))
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hp), negPLogP, ProbDist.prod]
      rw [hlog2_div _ _ hpos (mul_pos hfst hsnd), hlog2_mul _ _ hfst hsnd]
      ring
  have hsum_fst : ∑ ab : α × β, P.pmf ab * log2 (P.fst.pmf ab.1) = -shannonEntropy P.fst := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_mul]
    unfold shannonEntropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    change P.fst.pmf a * log2 (P.fst.pmf a) = -negPLogP (P.fst.pmf a)
    by_cases hfa : P.fst.pmf a ≤ 0
    · have h0 : P.fst.pmf a = 0 := le_antisymm hfa (P.fst.nonneg a)
      simp [h0, negPLogP]
    · simp [negPLogP, hfa]
  have hsum_snd : ∑ ab : α × β, P.pmf ab * log2 (P.snd.pmf ab.2) = -shannonEntropy P.snd := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    unfold shannonEntropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    change P.snd.pmf b * log2 (P.snd.pmf b) = -negPLogP (P.snd.pmf b)
    by_cases hsb : P.snd.pmf b ≤ 0
    · have h0 : P.snd.pmf b = 0 := le_antisymm hsb (P.snd.nonneg b)
      simp [h0, negPLogP]
    · simp [negPLogP, hsb]
  unfold klDivergence mutualInfo
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  change shannonEntropy P.fst + shannonEntropy P.snd - shannonEntropy P =
    -shannonEntropy P - (∑ ab : α × β, P.pmf ab * log2 (P.fst.pmf ab.1)) -
      (∑ ab : α × β, P.pmf ab * log2 (P.snd.pmf ab.2))
  rw [hsum_fst, hsum_snd]
  ring

/-- **Non-negativity of Mutual Information** (Cover & Thomas, Eq. 2.90): `I(X; Y) ≥ 0`. -/
theorem mutualInfo_nonneg (P : ProbDist (α × β)) : 0 ≤ mutualInfo P := by
  rw [mutualInfo_eq_klDivergence]
  exact klDivergence_nonneg P (P.fst.prod P.snd) (absCont_prod_marginals P)

/-- **Mutual Information Equality Case** (Cover & Thomas, Eq. 2.90):
    `I(X; Y) = 0 ↔ P_{XY} = P_X × P_Y`. -/
theorem mutualInfo_eq_zero_iff_indep (P : ProbDist (α × β)) :
    mutualInfo P = 0 ↔ P = P.fst.prod P.snd := by
  rw [mutualInfo_eq_klDivergence]
  exact klDivergence_eq_zero_iff P (P.fst.prod P.snd) (absCont_prod_marginals P)

/-- **Conditioning Reduces Entropy** (Cover & Thomas, Theorem 2.6.5): `H(X | Y) ≤ H(X)`. -/
theorem condEntropy_le_shannonEntropy (P : ProbDist (α × β)) :
    condEntropy P ≤ shannonEntropy P.fst := by
  have h := mutualInfo_nonneg P
  unfold mutualInfo at h
  unfold condEntropy
  linarith

/-- **Data Processing Inequality for Deterministic Post-Processing** (Cover & Thomas, Theorem 2.8.1):
    `I(X; f(Y)) ≤ I(X; Y)`. -/
theorem mutualInfo_map_right_le (P : ProbDist (α × β)) (f : β → γ) :
    mutualInfo (P.map (Prod.map id f)) ≤ mutualInfo P := by
  classical
  have hfst : (P.map (Prod.map id f)).fst = P.fst := by
    cases P with | mk pmf h0 h1 =>
    unfold ProbDist.fst ProbDist.map
    congr
    funext a
    simp only [Prod.map, id_eq]
    rw [Finset.sum_comm]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a' : α, ∑ b' : β, ∑ c : γ,
        (if (a', f b') = (a, c) then pmf (a', b') else 0) =
        if a' = a then ∑ b' : β, pmf (a', b') else 0 := by
      intro a'
      by_cases ha : a' = a
      · subst ha
        simp only [↓reduceIte, Prod.mk.injEq, true_and]
        refine Finset.sum_congr rfl fun b' _ => by simp
      · simp [ha]
    simp_rw [hinner]
    simp
  have hsnd : (P.map (Prod.map id f)).snd = P.snd.map f := by
    cases P with | mk pmf h0 h1 =>
    unfold ProbDist.snd ProbDist.map
    congr
    funext c
    simp only [Prod.map, id_eq]
    rw [Finset.sum_comm]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hfb : f b = c
    · subst hfb
      simp only [↓reduceIte, Prod.mk.injEq, and_true]
      refine Finset.sum_congr rfl fun a' _ => by simp
    · simp [hfb]
  have hprod : (P.fst.prod P.snd).map (Prod.map id f) =
      (P.map (Prod.map id f)).fst.prod (P.map (Prod.map id f)).snd := by
    rw [hfst, hsnd]
    unfold ProbDist.prod ProbDist.map
    congr
    funext ⟨a, c⟩
    simp only [Prod.map, id_eq]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a' : α, ∑ b' : β,
        (if (a', f b') = (a, c) then P.fst.pmf a' * P.snd.pmf b' else 0) =
        if a' = a then P.fst.pmf a * ∑ b' : β, (if f b' = c then P.snd.pmf b' else 0) else 0 := by
      intro a'
      by_cases ha : a' = a
      · subst ha
        simp only [↓reduceIte, Prod.mk.injEq, true_and, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => by split_ifs <;> ring
      · simp [ha]
    simp_rw [hinner]
    simp
  rw [mutualInfo_eq_klDivergence, mutualInfo_eq_klDivergence, ← hprod]
  exact klDivergence_map_le (Prod.map id f) P (P.fst.prod P.snd) (absCont_prod_marginals P)

/-- Lift a channel `W : DMC β γ` to `id × W : DMC (α × β) (α × γ)` acting on the second coordinate. -/
noncomputable def dmcLiftRight (W : DMC β γ) : DMC (α × β) (α × γ) := by
  classical
  exact
    { trans := fun ab ac => if ab.1 = ac.1 then W.trans ab.2 ac.2 else 0
      nonneg := fun ab ac => by split_ifs; exact W.nonneg ab.2 ac.2; exact le_rfl
      sum_one := fun ⟨a, b⟩ => by
        rw [Fintype.sum_prod_type]
        have hinner : ∀ a' : α, ∑ c : γ, (if a = a' then W.trans b c else 0) =
            if a = a' then 1 else 0 := fun a' => by
          by_cases ha : a = a'
          · simp [ha, W.sum_one b]
          · simp [ha]
        simp_rw [hinner]
        simp }

/-- **Data Processing Inequality for Noisy Channels** (Cover & Thomas, Theorem 2.8.1):
    For `X — Y — Z` where `Z` is obtained by passing `Y` through a DMC `W : DMC β γ`,
    `I(X; Z) ≤ I(X; Y)`. -/
theorem mutualInfo_channel_right_le (P : ProbDist (α × β)) (W : DMC β γ) :
    mutualInfo ((dmcLiftRight (α := α) W).joint P).snd ≤ mutualInfo P := by
  classical
  let Wext := dmcLiftRight (α := α) W
  let Pxz := (Wext.joint P).snd
  have hPxz_pmf : ∀ a c, Pxz.pmf (a, c) = ∑ b : β, P.pmf (a, b) * W.trans b c := by
    intro a c
    simp only [Pxz, Wext, dmcLiftRight, ProbDist.snd, DMC.joint]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a' : α, ∑ b : β, P.pmf (a', b) * (if a' = a then W.trans b c else 0) =
        if a' = a then ∑ b : β, P.pmf (a, b) * W.trans b c else 0 := fun a' => by
      by_cases ha : a' = a
      · subst ha; simp
      · simp [ha]
    simp_rw [hinner]
    simp
  have hfst : Pxz.fst = P.fst := by
    unfold ProbDist.fst
    congr
    funext a
    simp_rw [hPxz_pmf]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, W.sum_one b, mul_one]
  have hsnd : Pxz.snd = (W.joint P.snd).snd := by
    unfold ProbDist.snd DMC.joint
    congr
    funext c
    simp_rw [hPxz_pmf]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul]
  have hprod : (Wext.joint (P.fst.prod P.snd)).snd = Pxz.fst.prod Pxz.snd := by
    rw [hfst, hsnd]
    unfold ProbDist.prod ProbDist.snd DMC.joint
    congr
    funext ⟨a, c⟩
    simp only [Wext, dmcLiftRight]
    rw [Fintype.sum_prod_type]
    dsimp only
    trans (∑ a' : α, if a' = a then P.fst.pmf a * ∑ b : β, P.snd.pmf b * W.trans b c else 0)
    · refine Finset.sum_congr rfl fun a' _ => ?_
      by_cases ha : a' = a
      · subst ha
        simp only [↓reduceIte, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => by
          rw [← Finset.mul_sum]
          change P.fst.pmf a' * P.snd.pmf b * W.trans b c = _
          ring
      · simp [ha]
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rfl
  change mutualInfo Pxz ≤ mutualInfo P
  rw [mutualInfo_eq_klDivergence, mutualInfo_eq_klDivergence, ← hprod]
  exact klDivergence_channel_le Wext P (P.fst.prod P.snd) (absCont_prod_marginals P)

end ProbDistBridge

/-! ### 5. Bridging `hammingDistVec` to `Mathlib.InformationTheory.Hamming.hammingDist` -/

/-- Exact definitional bridge between `InfoTheory.hammingDistVec` and Mathlib's `hammingDist`. -/
lemma hammingDistVec_eq_hammingDist {α : Type*} [DecidableEq α] {n : ℕ}
    (x y : Fin n → α) : hammingDistVec x y = hammingDist x y := rfl

lemma hammingDistVec_comm {α : Type*} [DecidableEq α] {n : ℕ} (x y : Fin n → α) :
    hammingDistVec x y = hammingDistVec y x :=
  hammingDist_comm x y

lemma hammingDistVec_triangle {α : Type*} [DecidableEq α] {n : ℕ} (x y z : Fin n → α) :
    hammingDistVec x z ≤ hammingDistVec x y + hammingDistVec y z :=
  hammingDist_triangle x y z

lemma hammingDistVec_eq_zero {α : Type*} [DecidableEq α] {n : ℕ} (x y : Fin n → α) :
    hammingDistVec x y = 0 ↔ x = y :=
  hammingDist_eq_zero

/-! ### 6. Re-exporting Mathlib's Kraft–McMillan Inequality (Cover & Thomas, Thm. 5.5.1) -/

/-- **Kraft–McMillan Inequality** (Cover & Thomas, Theorem 5.5.1): for any finite uniquely
    decodable code `S` over a `D`-ary alphabet `α`, `∑_{w ∈ S} (1 / D)^{|w|} ≤ 1`. -/
theorem kraft_mcmillan_inequality {α : Type*} [Fintype α] [Nonempty α]
    {S : Finset (List α)} (h : InformationTheory.IsUniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length ≤ 1 :=
  h.finsetSum_one_div_card_pow_length_le_one

end InfoTheory.Bridge
