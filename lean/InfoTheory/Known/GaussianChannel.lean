import InfoTheory.Core.GaussianOperational
import InfoTheory.Bridge.ChannelAchievability
import InfoTheory.Known.Channels
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Topology.MetricSpace.Perfect

/-!
# Validation of the Gaussian-Channel Operational Framework

Validates `InfoTheory.Core.GaussianOperational` (Cover–Thomas Ch. 9; El Gamal–Kim Ch. 3):

* **Junk-proofness.**  `not_exists_code_of_not_measurable`, `exists_not_measurable_decoder`,
  `exists_function_not_decoder` (non-measurable decoders exist and are excluded by construction);
  `measurableSet_error`, `sum_measure_decoder_preimage`, `awgnErrorProb_add_success`
  (error probabilities are genuine, finitely additive probabilities);
  `awgnErrorProb_eq_errorProb` (noise form `P_Z{z | ĝ(x(m)+z) ≠ m}` agrees with the generic
  memoryless-channel form).
* **The capacity `sSup` is not junk.**  `awgnAchievable_nonempty` (`R = 0`),
  `awgnAchievable_bddAbove`.
* **Converse.**  `awgn_code_converse`: every `(n, M)` code with `∑ᵢ x(m)ᵢ² ≤ nP` has
  `(1 - P_e) ln M ≤ n · ½ ln(1 + P/N) + 1`; hence `isAwgnAchievable_le` and
  `awgnOperationalCapacity_le : C_op(P, N) ≤ ½ log₂(1 + P/N)`.
  The proof is the "meta-converse" form of Fano's inequality (compare each output law
  `N(x(m), N I)` with the reference `N(0, (P+N) I)` through the block likelihood ratio and
  `ln u ≤ u - 1`); its key inputs are an exact Gaussian change of measure
  (`awgnRefLaw_eq_withDensity`) and the Gaussian KL computation
  (`integral_awgnBlockLLR`, which is where the maximum-entropy bound `½ ln(1 + P/N)` appears).
* **Non-vacuity / achievability of a positive rate.**  BPSK + hard decisions reduce the AWGN
  channel to `BSC(Q(√(P/N)))`; with the DMC coding theorem
  (`InfoTheory.Bridge.shannon_channel_coding_achievability`) and `C(BSC(p)) = 1 - h(p)`
  (`InfoTheory.Known.bsc_capacity`): `isAwgnAchievable_of_lt_bsc`,
  `bsc_rate_le_awgnOperationalCapacity`, and `awgnOperationalCapacity_pos` (`P, N > 0`).

The matching achievability `C_op ≥ ½ log₂(1 + P/N)`, and hence the exact operational capacity
`awgnOperationalCapacity P N = ½ log₂(1 + P/N)`, is proved in
`InfoTheory.Known.GaussianAchievability.awgnOperationalCapacity_eq` (via discretization and
cost-constrained DMC coding).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace InfoTheory.Known.GaussianChannel

open InfoTheory

/-! ### 1. One-letter Gaussian computations -/

section OneLetter

variable {N S : ℝ}

/-- Per-letter log-likelihood ratio `ℓ_x(t) = ln (φ_{x,N}(t) / φ_{0,S}(t))`. -/
noncomputable def awgnLetterLLR (N S x t : ℝ) : ℝ :=
  Real.log (gaussianPDFReal x N.toNNReal t / gaussianPDFReal 0 S.toNNReal t)

lemma toNNReal_ne_zero_of_pos {v : ℝ} (hv : 0 < v) : v.toNNReal ≠ 0 := by
  simpa using hv

lemma log_gaussianPDFReal {v : ℝ} (hv : 0 < v) (μ t : ℝ) :
    Real.log (gaussianPDFReal μ v.toNNReal t) =
      -((1 / 2 : ℝ) * Real.log (2 * Real.pi * v)) - (t - μ) ^ 2 / (2 * v) := by
  rw [gaussianPDFReal_def]
  simp only [Real.coe_toNNReal _ hv.le]
  have h2piv : 0 < 2 * Real.pi * v := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr h2piv
  rw [Real.log_mul (inv_ne_zero hsqrt.ne') (Real.exp_ne_zero _), Real.log_inv,
    Real.log_sqrt h2piv.le, Real.log_exp]
  ring

lemma awgnLetterLLR_eq (hN : 0 < N) (hS : 0 < S) (x t : ℝ) :
    awgnLetterLLR N S x t =
      (1 / 2 : ℝ) * Real.log (S / N) - (t - x) ^ 2 / (2 * N) + t ^ 2 / (2 * S) := by
  unfold awgnLetterLLR
  rw [Real.log_div (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero_of_pos hN)).ne'
      (gaussianPDFReal_pos _ _ _ (toNNReal_ne_zero_of_pos hS)).ne',
    log_gaussianPDFReal hN, log_gaussianPDFReal hS,
    Real.log_div hS.ne' hN.ne',
    Real.log_mul (by positivity) hS.ne', Real.log_mul (by positivity) hN.ne']
  ring

lemma exp_neg_awgnLetterLLR (N S x t : ℝ) (hN : 0 < N) (hS : 0 < S) :
    gaussianPDFReal x N.toNNReal t * Real.exp (-awgnLetterLLR N S x t) =
      gaussianPDFReal 0 S.toNNReal t := by
  unfold awgnLetterLLR
  have hp := gaussianPDFReal_pos x _ t (toNNReal_ne_zero_of_pos hN)
  have hq := gaussianPDFReal_pos 0 _ t (toNNReal_ne_zero_of_pos hS)
  rw [Real.exp_neg, Real.exp_log (div_pos hp hq)]
  field_simp

lemma measurable_awgnLetterLLR (N S x : ℝ) : Measurable (awgnLetterLLR N S x) := by
  unfold awgnLetterLLR
  exact ((measurable_gaussianPDFReal _ _).div (measurable_gaussianPDFReal _ _)).log

/-- One-letter change of measure: `∫⁻_s e^{-ℓ_x} dN(x, N) = N(0, S)(s)`. -/
lemma setLIntegral_exp_neg_awgnLetterLLR (hN : 0 < N) (hS : 0 < S) (x : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫⁻ t in s, ENNReal.ofReal (Real.exp (-awgnLetterLLR N S x t)) ∂gaussianReal x N.toNNReal =
      gaussianReal 0 S.toNNReal s := by
  rw [gaussianReal_of_var_ne_zero _ (toNNReal_ne_zero_of_pos hN),
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF _ _)
      (g := fun t => ENNReal.ofReal (Real.exp (-awgnLetterLLR N S x t)))
      ((measurable_awgnLetterLLR N S x).neg.exp.ennreal_ofReal) hs,
    gaussianReal_apply _ (toNNReal_ne_zero_of_pos hS)]
  refine setLIntegral_congr_fun hs (fun t _ => ?_)
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), exp_neg_awgnLetterLLR N S x t hN hS]

lemma integrable_sq_sub_gaussianReal (x : ℝ) (v : ℝ≥0) :
    Integrable (fun t : ℝ => (t - x) ^ 2) (gaussianReal x v) := by
  have h : MemLp (fun t : ℝ => t - x) 2 (gaussianReal x v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const x)
  exact h.integrable_sq

lemma integrable_id_gaussianReal' (x : ℝ) (v : ℝ≥0) :
    Integrable (fun t : ℝ => t) (gaussianReal x v) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integral_sq_sub_gaussianReal (x : ℝ) (v : ℝ≥0) :
    ∫ t, (t - x) ^ 2 ∂gaussianReal x v = v := by
  have hvar : Var[fun t : ℝ => t; gaussianReal x v] = v := variance_fun_id_gaussianReal
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  have hmean : ∫ t, t ∂gaussianReal x v = x := integral_id_gaussianReal
  simpa [hmean] using hvar

lemma integrable_awgnLetterLLR (hN : 0 < N) (hS : 0 < S) (x : ℝ) :
    Integrable (awgnLetterLLR N S x) (gaussianReal x N.toNNReal) := by
  have heq : awgnLetterLLR N S x = fun t =>
      ((1 / 2 : ℝ) * Real.log (S / N) - x ^ 2 / (2 * S)) +
        (1 / (2 * S) - 1 / (2 * N)) * (t - x) ^ 2 + (2 * x / (2 * S)) * t := by
    funext t
    rw [awgnLetterLLR_eq hN hS]
    field_simp
    ring
  rw [heq]
  exact ((integrable_const _).add ((integrable_sq_sub_gaussianReal x _).const_mul _)).add
    ((integrable_id_gaussianReal' x _).const_mul _)

/-- One-letter expected log-likelihood ratio:
    `E_{N(x,N)}[ℓ_x] = ½ ln(S/N) - ½ + (x² + N)/(2S)`. -/
lemma integral_awgnLetterLLR (hN : 0 < N) (hS : 0 < S) (x : ℝ) :
    ∫ t, awgnLetterLLR N S x t ∂gaussianReal x N.toNNReal =
      (1 / 2 : ℝ) * Real.log (S / N) - 1 / 2 + (x ^ 2 + N) / (2 * S) := by
  have heq : awgnLetterLLR N S x = fun t =>
      ((1 / 2 : ℝ) * Real.log (S / N) - x ^ 2 / (2 * S)) +
        (1 / (2 * S) - 1 / (2 * N)) * (t - x) ^ 2 + (2 * x / (2 * S)) * t := by
    funext t
    rw [awgnLetterLLR_eq hN hS]
    field_simp
    ring
  rw [heq, integral_add, integral_add, integral_const, integral_const_mul, integral_const_mul,
    integral_sq_sub_gaussianReal, integral_id_gaussianReal]
  · simp only [Real.coe_toNNReal _ hN.le, probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  · exact integrable_const _
  · exact (integrable_sq_sub_gaussianReal x _).const_mul _
  · exact (integrable_const _).add ((integrable_sq_sub_gaussianReal x _).const_mul _)
  · exact (integrable_id_gaussianReal' x _).const_mul _

end OneLetter

/-! ### 2. Block (n-letter) change of measure and expected log-likelihood ratio -/

section Block

variable {n : ℕ} {N S : ℝ}

/-- Block log-likelihood ratio `L_x(y) = ∑ᵢ ℓ_{xᵢ}(yᵢ) = ln (dN(x, N I)/dN(0, S I))(y)`. -/
noncomputable def awgnBlockLLR (N S : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i, awgnLetterLLR N S (x i) (y i)

lemma measurable_awgnBlockLLR (N S : ℝ) (x : Fin n → ℝ) : Measurable (awgnBlockLLR N S x) :=
  Finset.measurable_sum _ (fun i _ => (measurable_awgnLetterLLR N S (x i)).comp
    (measurable_pi_apply i))

/-- The reference output law `N(0, S)^{⊗n}`. -/
noncomputable def awgnRefLaw (n : ℕ) (S : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 S.toNNReal

instance (n : ℕ) (S : ℝ) : IsProbabilityMeasure (awgnRefLaw n S) := by
  unfold awgnRefLaw; infer_instance

instance (N a : ℝ) : IsProbabilityMeasure (awgnLetterLaw N a) := by
  unfold awgnLetterLaw; infer_instance

instance (n : ℕ) (N : ℝ) (x : Fin n → ℝ) : IsProbabilityMeasure (awgnBlockLaw n N x) := by
  unfold awgnBlockLaw memorylessLaw awgnLetterLaw; infer_instance

/-- **Block change of measure**: `N(0, S I) = N(x, N I).withDensity (e^{-L_x})`. -/
theorem awgnRefLaw_eq_withDensity (hN : 0 < N) (hS : 0 < S) (x : Fin n → ℝ) :
    awgnRefLaw n S =
      (awgnBlockLaw n N x).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-awgnBlockLLR N S x y))) := by
  unfold awgnRefLaw
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : ∀ y : Fin n → ℝ,
      (Set.univ.pi s).indicator (fun y => ENNReal.ofReal (Real.exp (-awgnBlockLLR N S x y))) y =
        ∏ i, (s i).indicator
          (fun t => ENNReal.ofReal (Real.exp (-awgnLetterLLR N S (x i) t))) (y i) := by
    intro y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      have hy' : ∀ i, y i ∈ s i := fun i => hy i (Set.mem_univ i)
      simp only [Set.indicator_of_mem (hy' _)]
      rw [awgnBlockLLR, ← Finset.sum_neg_distrib, Real.exp_sum,
        ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [hpt]
  set g : Fin n → ℝ → ℝ≥0∞ := fun i => (s i).indicator
      (fun t => ENNReal.ofReal (Real.exp (-awgnLetterLLR N S (x i) t))) with hg
  have hmeas : ∀ i, Measurable (g i) := fun i =>
    ((measurable_awgnLetterLLR N S (x i)).neg.exp.ennreal_ofReal).indicator (hs i)
  set μ : Fin n → Measure ℝ := fun i => gaussianReal (x i) N.toNNReal with hμ
  have hP : awgnBlockLaw n N x = Measure.pi μ := rfl
  rw [hP]
  have hprob : ∀ i, IsProbabilityMeasure (μ i) := fun i => by
    rw [hμ]; infer_instance
  have hind : iIndepFun (fun i (ω : Fin n → ℝ) => g i (ω i)) (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := g) (fun i => (hmeas i).aemeasurable)
  have key := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hmeas i).comp (measurable_pi_apply i))
  refine key.trans ?_
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [(measurePreserving_eval μ i).lintegral_comp (hmeas i), hg, lintegral_indicator (hs i)]
  exact setLIntegral_exp_neg_awgnLetterLLR hN hS (x i) (hs i)

lemma integrable_awgnBlockLLR (hN : 0 < N) (hS : 0 < S) (x : Fin n → ℝ) :
    Integrable (awgnBlockLLR N S x) (awgnBlockLaw n N x) := by
  unfold awgnBlockLLR awgnBlockLaw memorylessLaw awgnLetterLaw
  exact integrable_finsetSum _ (fun i _ =>
    integrable_comp_eval (μ := fun i => gaussianReal (x i) N.toNNReal)
      (integrable_awgnLetterLLR hN hS (x i)))

/-- Expected block log-likelihood ratio (a KL divergence `D(N(x, N I) ‖ N(0, S I))`). -/
lemma integral_awgnBlockLLR (hN : 0 < N) (hS : 0 < S) (x : Fin n → ℝ) :
    ∫ y, awgnBlockLLR N S x y ∂awgnBlockLaw n N x =
      ∑ i, ((1 / 2 : ℝ) * Real.log (S / N) - 1 / 2 + (x i ^ 2 + N) / (2 * S)) := by
  unfold awgnBlockLLR
  rw [integral_finsetSum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold awgnBlockLaw memorylessLaw awgnLetterLaw
    rw [integral_comp_eval (μ := fun i => gaussianReal (x i) N.toNNReal)
      (measurable_awgnLetterLLR N S (x i)).aestronglyMeasurable,
      integral_awgnLetterLLR hN hS]
  · unfold awgnBlockLaw memorylessLaw awgnLetterLaw
    exact integrable_comp_eval (μ := fun i => gaussianReal (x i) N.toNNReal)
      (integrable_awgnLetterLLR hN hS (x i))

/-- Under the power constraint `∑ xᵢ² ≤ nP` and `S = P + N`, the expected block LLR is at most
    `n · ½ ln(1 + P/N)` (Cover–Thomas eq. (9.17), in nats). -/
lemma integral_awgnBlockLLR_le {P : ℝ} (hN : 0 < N) (hP : 0 ≤ P) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 ≤ (n : ℝ) * P) :
    ∫ y, awgnBlockLLR N (P + N) x y ∂awgnBlockLaw n N x ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P / N)) := by
  have hS : 0 < P + N := by linarith
  rw [integral_awgnBlockLLR hN hS, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlog : Real.log ((P + N) / N) = Real.log (1 + P / N) := by
    congr 1; field_simp; ring
  rw [hlog]
  have hdiv : (∑ i, x i ^ 2 + (n : ℝ) * N) / (2 * (P + N)) ≤ (n : ℝ) / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end Block

/-! ### 3. Basic sanity facts about the framework (junk-proofness) -/

section Sanity

variable {n M : ℕ}

instance (n : ℕ) (N : ℝ) : IsProbabilityMeasure (awgnNoise n N) := by
  unfold awgnNoise; infer_instance

/-- Encoders out of the finite message set are automatically measurable. -/
theorem measurable_encoder {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (C : MeasurableBlockCode α β n M) : Measurable C.encoder :=
  measurable_of_finite _

/-- Every decoding region `ĝ⁻¹{m}` is a measurable set. -/
theorem measurableSet_decoder_preimage {α β : Type*} [MeasurableSpace β]
    (C : MeasurableBlockCode α β n M) (m : Fin M) : MeasurableSet (C.decoder ⁻¹' {m}) :=
  C.measurable_decoder (measurableSet_singleton m)

/-- Every error event `{y | ĝ(y) ≠ m}` is a measurable set. -/
theorem measurableSet_error {α β : Type*} [MeasurableSpace β]
    (C : MeasurableBlockCode α β n M) (m : Fin M) : MeasurableSet {y | C.decoder y ≠ m} :=
  (measurableSet_decoder_preimage C m).compl

/-- **Junk-proofness**: a non-measurable decoder cannot be part of any code. -/
theorem not_exists_code_of_not_measurable {α β : Type*} [MeasurableSpace β]
    {d : (Fin n → β) → Fin M} (hd : ¬ Measurable d) :
    ¬ ∃ C : MeasurableBlockCode α β n M, C.decoder = d := by
  rintro ⟨C, rfl⟩
  exact hd C.measurable_decoder

/-- There are non-measurable subsets of `ℝ` (cardinality: Borel sets number `≤ 𝔠 < 2^𝔠`). -/
theorem exists_not_measurableSet_real : ∃ A : Set ℝ, ¬ MeasurableSet A := by
  by_contra h
  push Not at h
  have heq : (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.generateFrom (⋃ a : ℚ, {Set.Iio (a : ℝ)}) :=
    BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iio_rat
  have hs : Cardinal.mk (⋃ a : ℚ, {Set.Iio (a : ℝ)} : Set (Set ℝ)) ≤ Cardinal.continuum :=
    (Set.countable_iUnion fun _ => Set.countable_singleton _).le_aleph0.trans
      Cardinal.aleph0_le_continuum
  have hle := MeasurableSpace.cardinal_measurableSet_le_continuum hs
  rw [← heq] at hle
  have huniv : {t : Set ℝ | MeasurableSet t} = Set.univ := Set.eq_univ_of_forall h
  rw [huniv, Cardinal.mk_univ, Cardinal.mk_set] at hle
  -- `𝔠 ≤ #ℝ` via a continuous injection of the Cantor space `ℕ → Bool` into `ℝ`
  obtain ⟨f, -, -, hf⟩ :=
    (PerfectSpace.univ_perfect (α := ℝ)).exists_nat_bool_injection Set.univ_nonempty
  have hc : Cardinal.continuum ≤ Cardinal.mk ℝ := by
    have h1 := Cardinal.mk_le_of_injective hf
    have h2 : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
      rw [← Cardinal.two_power_aleph0, ← Cardinal.mk_bool, ← Cardinal.mk_nat, Cardinal.power_def]
    rwa [h2] at h1
  have := (Cardinal.power_le_power_left two_ne_zero hc).trans hle
  exact absurd (lt_of_lt_of_le (Cardinal.cantor _) this) (lt_irrefl _)

/-- Non-measurable "decoders" exist, so the measurability requirement in `MeasurableBlockCode`
    has teeth: the function below cannot be the decoder of any code. -/
theorem exists_not_measurable_decoder : ∃ d : (Fin 1 → ℝ) → Fin 2, ¬ Measurable d := by
  classical
  obtain ⟨A, hA⟩ := exists_not_measurableSet_real
  refine ⟨fun y => if y 0 ∈ A then 1 else 0, fun hd => hA ?_⟩
  have h1 := hd (measurableSet_singleton (1 : Fin 2))
  have hc : Measurable (fun t : ℝ => (fun _ : Fin 1 => t)) :=
    measurable_pi_iff.mpr (fun _ => measurable_id)
  have h2 := hc h1
  convert h2 using 1
  ext t
  by_cases ht : t ∈ A <;> simp [ht]

/-- **Junk-proofness, concretely**: some function `(Fin 1 → ℝ) → Fin 2` is not the decoder of
    any `(1, 2)` AWGN code. -/
theorem exists_function_not_decoder :
    ∃ d : (Fin 1 → ℝ) → Fin 2, ∀ C : AwgnCode 1 2, C.decoder ≠ d := by
  obtain ⟨d, hd⟩ := exists_not_measurable_decoder
  exact ⟨d, fun C hC => not_exists_code_of_not_measurable hd ⟨C, hC⟩⟩

/-- The AWGN output law is the noise law translated by the codeword: `x + Zⁿ ~ ⊗ᵢ N(xᵢ, N)`. -/
theorem awgnBlockLaw_eq_map (n : ℕ) (N : ℝ) (x : Fin n → ℝ) :
    awgnBlockLaw n N x = (awgnNoise n N).map (fun z => x + z) := by
  unfold awgnBlockLaw memorylessLaw awgnLetterLaw awgnNoise
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 N.toNNReal)
    (f := fun i t => x i + t) (fun i => (measurable_const_add (x i)).aemeasurable)
  simp only [gaussianReal_map_const_add, zero_add] at h
  rw [← h]
  rfl

/-- The noise-form AWGN error probability agrees with the generic memoryless-channel one. -/
theorem awgnErrorProb_eq_errorProb (C : AwgnCode n M) (N : ℝ) (m : Fin M) :
    awgnErrorProb C N m = C.errorProb (awgnBlockLaw n N) m := by
  unfold awgnErrorProb MeasurableBlockCode.errorProb
  rw [awgnBlockLaw_eq_map, Measure.map_apply (measurable_const_add _) (measurableSet_error C m)]
  rfl

theorem awgnErrorProb_le_one (C : AwgnCode n M) (N : ℝ) (m : Fin M) :
    awgnErrorProb C N m ≤ 1 :=
  prob_le_one

/-- Genuine probabilities: error and success probabilities of each message add up to `1`. -/
theorem awgnErrorProb_add_success (C : AwgnCode n M) (N : ℝ) (m : Fin M) :
    awgnErrorProb C N m + awgnBlockLaw n N (C.encoder m) (C.decoder ⁻¹' {m}) = 1 := by
  rw [awgnErrorProb_eq_errorProb, MeasurableBlockCode.errorProb]
  have h := measure_add_measure_compl (μ := awgnBlockLaw n N (C.encoder m))
    (measurableSet_decoder_preimage C m)
  rw [measure_univ, add_comm] at h
  exact h

/-- The decoding regions of any code partition the output space measurably, so their
    probabilities under any probability measure sum to exactly `1`.  (This finite additivity is
    what fails for non-measurable decoders.) -/
theorem sum_measure_decoder_preimage {α β : Type*} [MeasurableSpace β]
    (C : MeasurableBlockCode α β n M) (μ : Measure (Fin n → β)) [IsProbabilityMeasure μ] :
    ∑ m : Fin M, μ (C.decoder ⁻¹' {m}) = 1 := by
  rw [sum_measure_preimage_singleton Finset.univ
    (fun m _ => measurableSet_decoder_preimage C m)]
  simp

theorem awgnAvgErrorProb_toReal (C : AwgnCode n M) (N : ℝ) :
    (awgnAvgErrorProb C N).toReal = (1 / (M : ℝ)) * ∑ m, (awgnErrorProb C N m).toReal := by
  unfold awgnAvgErrorProb
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun m _ => ne_top_of_le_ne_top ENNReal.one_ne_top
      (awgnErrorProb_le_one C N m)), one_div]

end Sanity

/-! ### 4. The converse (Cover–Thomas Thm. 9.1.1 converse, §9.2; El Gamal–Kim §3.3)

We use the "meta-converse" form of Fano's inequality: comparing each conditional output law
`N(x(m), N I)` with the fixed reference law `N(0, (P+N) I)` via the elementary inequality
`ln u ≤ u - 1` integrated against the block likelihood ratio. -/

section Converse

variable {n M : ℕ} {N S : ℝ}

/-- Per-message bound: for measurable `A` and `c ≥ 1`,
    `P_x(A) ln c - (c - 1) Q(A) ≤ E_{P_x}[L_x]`, where `P_x = N(x, N I)`, `Q = N(0, S I)`. -/
lemma awgn_message_bound (hN : 0 < N) (hS : 0 < S) (x : Fin n → ℝ) {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) {c : ℝ} (hc : 1 ≤ c) :
    (awgnBlockLaw n N x).real A * Real.log c - (c - 1) * (awgnRefLaw n S).real A ≤
      ∫ y, awgnBlockLLR N S x y ∂awgnBlockLaw n N x := by
  have hLm : Measurable (awgnBlockLLR N S x) := measurable_awgnBlockLLR N S x
  set L := awgnBlockLLR N S x with hL
  set P := awgnBlockLaw n N x with hP
  set G : (Fin n → ℝ) → ℝ := fun y => Real.exp (-L y) with hG
  have hGm : Measurable G := hLm.neg.exp
  have hQ : awgnRefLaw n S = P.withDensity (fun y => ENNReal.ofReal (G y)) :=
    awgnRefLaw_eq_withDensity hN hS x
  have hGofReal : ∀ y, (ENNReal.ofReal (G y)).toReal = G y :=
    fun y => ENNReal.toReal_ofReal (Real.exp_pos _).le
  have hlint : ∫⁻ y, ENNReal.ofReal (G y) ∂P = 1 := by
    have h := congrArg (fun μ : Measure (Fin n → ℝ) => μ Set.univ) hQ
    simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, measure_univ] at h
    exact h.symm
  have hGint : Integrable G P := by
    have h := integrable_toReal_of_lintegral_ne_top hGm.ennreal_ofReal.aemeasurable
      (by rw [hlint]; exact ENNReal.one_ne_top)
    exact h.congr (ae_of_all _ hGofReal)
  have hGA : ∫ y, A.indicator G y ∂P = (awgnRefLaw n S).real A := by
    rw [integral_indicator hA, measureReal_def, hQ, withDensity_apply _ hA,
      ← integral_toReal hGm.ennreal_ofReal.aemeasurable (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
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
  have hmono := integral_mono hint3 (integrable_awgnBlockLLR hN hS x) hpt
  have hcalc : ∫ y, (A.indicator (fun _ => Real.log c) y + 1 -
      ((c - 1) * A.indicator G y + G y)) ∂P =
      P.real A * Real.log c + 1 - ((c - 1) * (awgnRefLaw n S).real A + 1) := by
    have hint4 : Integrable (fun y => A.indicator (fun _ => Real.log c) y + 1) P :=
      hint1.add (integrable_const _)
    have hint5 : Integrable (fun y => (c - 1) * A.indicator G y) P :=
      (hGint.indicator hA).const_mul _
    have hint6 : Integrable (fun _ : Fin n → ℝ => (1 : ℝ)) P := integrable_const _
    rw [integral_sub hint4 hint2, integral_add hint1 hint6, integral_add hint5 hGint,
      integral_const_mul,
      integral_indicator_const _ hA, hGA, hG1, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hcalc] at hmono
  linarith

/-- **Finite-blocklength converse for the AWGN channel** (Fano/meta-converse form;
    cf. Cover–Thomas §9.2, El Gamal–Kim §3.3): every `(n, M)` code (`M ≥ 1`) whose codewords
    satisfy `∑ᵢ x(m)ᵢ² ≤ nP` has
    `(1 - P_e) ln M ≤ n · ½ ln(1 + P/N) + 1`  (nats). -/
theorem awgn_code_converse {P : ℝ} (hN : 0 < N) (hP : 0 ≤ P) (hM : 1 ≤ M) (C : AwgnCode n M)
    (hpow : C.SatisfiesPower P) :
    (1 - (awgnAvgErrorProb C N).toReal) * Real.log M ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P / N)) + 1 := by
  have hS : 0 < P + N := by linarith
  set K := (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P / N)) with hK
  set Q := awgnRefLaw n (P + N) with hQ
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmsg : ∀ m : Fin M, (1 - (awgnErrorProb C N m).toReal) * Real.log M -
      ((M : ℝ) - 1) * Q.real (C.decoder ⁻¹' {m}) ≤ K := by
    intro m
    have hA := measurableSet_decoder_preimage C m
    have h1 := awgn_message_bound hN hS (C.encoder m) hA hMr
    have h2 := integral_awgnBlockLLR_le hN hP (C.encoder m) (hpow m)
    have h3 : (awgnBlockLaw n N (C.encoder m)).real (C.decoder ⁻¹' {m}) =
        1 - (awgnErrorProb C N m).toReal := by
      have h := awgnErrorProb_add_success C N m
      have hne : awgnErrorProb C N m ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (awgnErrorProb_le_one C N m)
      rw [measureReal_def]
      have h' := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add hne (measure_ne_top _ _), ENNReal.toReal_one] at h'
      linarith
    rw [h3] at h1
    linarith
  have hsumQ : ∑ m : Fin M, Q.real (C.decoder ⁻¹' {m}) = 1 := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), sum_measure_decoder_preimage C Q,
      ENNReal.toReal_one]
  have hsum := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hmsg m)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumQ, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, mul_one] at hsum
  rw [awgnAvgErrorProb_toReal]
  set E := ∑ m : Fin M, (awgnErrorProb C N m).toReal
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hMr
  have hrw : (1 - 1 / (M : ℝ) * E) * Real.log M = ((M - E) * Real.log M) / M := by
    field_simp
  rw [hrw, div_le_iff₀ hMpos]
  nlinarith

end Converse

/-! ### 5. Operational capacity: nonempty, bounded, and `≤ ½ log₂(1 + P/N)` -/

section Capacity

variable {P N R : ℝ}

/-- `M = max 1 ⌊2^{nR}⌋ ≥ 2^{nR - 1}`, hence `ln M ≥ (nR - 1) ln 2`. -/
lemma log_codeSize_ge (n : ℕ) (R : ℝ) :
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

/-- Rate `0` is achievable whenever `P ≥ 0` (single-message code, constant decoder). -/
theorem isAwgnAchievable_zero (hP : 0 ≤ P) (N : ℝ) : IsAwgnAchievable P N 0 := by
  refine ⟨le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  have hM : max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * 0)⌋₊ = 1 := by simp
  rw [hM]
  let C : AwgnCode n 1 := ⟨fun _ _ => 0, fun _ => 0, measurable_const⟩
  refine ⟨C, fun m => ?_, ?_⟩
  · simp only [C, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · have h0 : ∀ m : Fin 1, awgnErrorProb C N m = 0 := by
      intro m
      unfold awgnErrorProb
      have hempty : {z : Fin n → ℝ | C.decoder (C.encoder m + z) ≠ m} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact Subsingleton.elim _ _
      rw [hempty, measure_empty]
    unfold awgnAvgErrorProb
    simp [h0]

/-- **Converse (asymptotic)**: every achievable rate satisfies `R ≤ ½ log₂(1 + P/N)`
    (Cover–Thomas Thm. 9.1.1, converse part; El Gamal–Kim Thm. 3.2). -/
theorem isAwgnAchievable_le (hN : 0 < N) (hP : 0 ≤ P) (hR : IsAwgnAchievable P N R) :
    R ≤ awgnCapacityFormula P N := by
  set K := (1 / 2 : ℝ) * Real.log (1 + P / N) with hK
  have hK0 : 0 ≤ K := by
    have : 1 ≤ 1 + P / N := by have := div_nonneg hP hN.le; linarith
    have := Real.log_nonneg this
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Step 1: for every `δ ∈ (0, 1)`, `(1 - δ) R ln 2 ≤ K`.
  have step1 : ∀ δ : ℝ, 0 < δ → δ < 1 → (1 - δ) * R * Real.log 2 ≤ K := by
    intro δ hδ hδ1
    obtain ⟨n₀, hn₀⟩ := hR.2 δ hδ
    have hev : ∀ᶠ n : ℕ in atTop,
        (1 - δ) * R * Real.log 2 ≤ K + (1 + (1 - δ) * Real.log 2) * (1 / (n : ℝ)) := by
      refine eventually_atTop.2 ⟨max n₀ 1, fun n hn => ?_⟩
      obtain ⟨C, hpow, herr⟩ := hn₀ n (le_trans (le_max_left _ _) hn)
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
      have hMge : 1 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ := le_max_left _ _
      have hconv := awgn_code_converse hN hP hMge C hpow
      have he : (awgnAvgErrorProb C N).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le herr
      have hlogM := log_codeSize_ge n R
      have hlogM0 : 0 ≤ Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hMge)
      have h1 : (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2) ≤
          (1 - (awgnAvgErrorProb C N).toReal) *
            Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) := by
        calc (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2)
            ≤ (1 - δ) * Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hlogM (by linarith)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlogM0
      have h2 : (1 - δ) * (((n : ℝ) * R - 1) * Real.log 2) ≤ (n : ℝ) * K + 1 :=
        le_trans h1 hconv
      have hdiv : (1 - δ) * R * Real.log 2 =
          ((1 - δ) * (((n : ℝ) * R - 1) * Real.log 2) + (1 - δ) * Real.log 2) / n := by
        field_simp
        ring
      rw [hdiv, div_le_iff₀ hnr]
      have hexp : (K + (1 + (1 - δ) * Real.log 2) * (1 / (n : ℝ))) * n =
          (n : ℝ) * K + 1 + (1 - δ) * Real.log 2 := by
        field_simp
        ring
      rw [hexp]
      linarith
    have hlim : Tendsto (fun n : ℕ => K + (1 + (1 - δ) * Real.log 2) * (1 / (n : ℝ))) atTop
        (𝓝 K) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat.const_mul
        (1 + (1 - δ) * Real.log 2)).const_add K
      simpa using h
    exact ge_of_tendsto hlim hev
  -- Step 2: let `δ → 0`.
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
  have hcap : awgnCapacityFormula P N = K / Real.log 2 := by
    unfold awgnCapacityFormula log2
    rw [hK]
    ring
  rw [hcap, le_div_iff₀ hlog2]
  exact hRK

/-- The achievable-rate set is nonempty (it contains `0`). -/
theorem awgnAchievable_nonempty (hP : 0 ≤ P) (N : ℝ) :
    { R : ℝ | IsAwgnAchievable P N R }.Nonempty :=
  ⟨0, isAwgnAchievable_zero hP N⟩

/-- The achievable-rate set is bounded above (by `½ log₂(1 + P/N)`), so the `sSup` defining
    `awgnOperationalCapacity` is not a junk value. -/
theorem awgnAchievable_bddAbove (hN : 0 < N) (hP : 0 ≤ P) :
    BddAbove { R : ℝ | IsAwgnAchievable P N R } :=
  ⟨awgnCapacityFormula P N, fun _ hR => isAwgnAchievable_le hN hP hR⟩

/-- **Converse**: `C_op(P, N) ≤ ½ log₂(1 + P/N)`. -/
theorem awgnOperationalCapacity_le (hN : 0 < N) (hP : 0 ≤ P) :
    awgnOperationalCapacity P N ≤ awgnCapacityFormula P N :=
  csSup_le (awgnAchievable_nonempty hP N) (fun _ hR => isAwgnAchievable_le hN hP hR)

theorem awgnOperationalCapacity_nonneg (hN : 0 < N) (hP : 0 ≤ P) :
    0 ≤ awgnOperationalCapacity P N :=
  le_csSup (awgnAchievable_bddAbove hN hP) (isAwgnAchievable_zero hP N)

/-- Every achievable rate is at most the operational capacity (non-junk `sSup`). -/
theorem le_awgnOperationalCapacity (hN : 0 < N) (hP : 0 ≤ P) (hR : IsAwgnAchievable P N R) :
    R ≤ awgnOperationalCapacity P N :=
  le_csSup (awgnAchievable_bddAbove hN hP) hR

end Capacity

/-! ### 6. Achievability of an explicit positive rate (BPSK + hard decisions → BSC)

Binary antipodal signalling `x = ±√P` with the threshold detector `ŷ = [y > 0]` turns `n` uses
of the AWGN channel into `n` uses of a BSC with crossover `p = Q(√(P/N)) < ½`
(Cover–Thomas §9.3 remark / Problem 9.x; El Gamal–Kim §3.3).  Composing with the DMC channel
coding theorem (`InfoTheory.Bridge.shannon_channel_coding_achievability`) shows every rate
`R < 1 - h(p)` is AWGN-achievable; in particular `awgnOperationalCapacity P N > 0`. -/

section Achievability

variable {P N : ℝ}

/-- BPSK symbol `true ↦ √P`, `false ↦ -√P`. -/
noncomputable def bpskSymbol (P : ℝ) (b : Bool) : ℝ :=
  if b then Real.sqrt P else -Real.sqrt P

/-- Hard-decision (threshold) detector `t ↦ [t > 0]`. -/
noncomputable def hardDecision (t : ℝ) : Bool :=
  decide (0 < t)

/-- Crossover probability of the induced BSC: `p = P(√P + Z ≤ 0) = Q(√(P/N))`. -/
noncomputable def bpskCrossover (P N : ℝ) : ℝ :=
  (gaussianReal (Real.sqrt P) N.toNNReal).real (Set.Iic 0)

lemma hardDecision_preimage_true : hardDecision ⁻¹' {true} = Set.Ioi 0 := by
  ext t; simp [hardDecision]

lemma hardDecision_preimage_false : hardDecision ⁻¹' {false} = Set.Iic 0 := by
  ext t; simp [hardDecision]

lemma measurable_hardDecision : Measurable hardDecision := by
  refine measurable_to_countable' (fun b => ?_)
  cases b
  · rw [hardDecision_preimage_false]; exact measurableSet_Iic
  · rw [hardDecision_preimage_true]; exact measurableSet_Ioi

lemma bpskCrossover_nonneg : 0 ≤ bpskCrossover P N := measureReal_nonneg

lemma bpskCrossover_le_one : bpskCrossover P N ≤ 1 := measureReal_le_one

lemma gaussianReal_real_Ioi_zero (P N : ℝ) :
    (gaussianReal (Real.sqrt P) N.toNNReal).real (Set.Ioi 0) = 1 - bpskCrossover P N := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rfl

lemma gaussianReal_neg_real_Ioi_zero (hN : 0 < N) (P : ℝ) :
    (gaussianReal (-Real.sqrt P) N.toNNReal).real (Set.Ioi 0) = bpskCrossover P N := by
  rw [← gaussianReal_map_neg, measureReal_def, Measure.map_apply measurable_neg measurableSet_Ioi]
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by ext t; simp
  rw [hpre]
  have := nullSingletonClass_gaussianReal (μ := Real.sqrt P) (toNNReal_ne_zero_of_pos hN)
  rw [measure_congr (Iio_ae_eq_Iic (μ := gaussianReal (Real.sqrt P) N.toNNReal))]
  rfl

lemma gaussianReal_neg_real_Iic_zero (hN : 0 < N) (P : ℝ) :
    (gaussianReal (-Real.sqrt P) N.toNNReal).real (Set.Iic 0) = 1 - bpskCrossover P N := by
  rw [← gaussianReal_neg_real_Ioi_zero hN P, ← Set.compl_Ioi,
    probReal_compl_eq_one_sub measurableSet_Ioi]

/-- The induced channel is exactly `BSC(p)`. -/
lemma gaussianReal_hardDecision (hN : 0 < N) (b c : Bool) :
    (gaussianReal (bpskSymbol P b) N.toNNReal).real (hardDecision ⁻¹' {c}) =
      (bsc (bpskCrossover P N) bpskCrossover_nonneg bpskCrossover_le_one).trans b c := by
  cases b <;> cases c <;>
    simp only [bpskSymbol, bsc, hardDecision_preimage_true, hardDecision_preimage_false,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, gaussianReal_neg_real_Iic_zero hN,
      gaussianReal_neg_real_Ioi_zero hN, gaussianReal_real_Ioi_zero]
  rfl

/-- For `P > 0`, `N > 0`: the crossover probability is `< ½`. -/
lemma bpskCrossover_lt_half (hN : 0 < N) (hP : 0 < P) : bpskCrossover P N < 1 / 2 := by
  set a := Real.sqrt P with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr hP
  set μ := gaussianReal a N.toNNReal with hμ
  -- reflection `t ↦ 2a - t` preserves `μ`
  have hrefl : μ.map (fun t => 2 * a - t) = μ := by
    rw [hμ, gaussianReal_map_const_sub]
    congr 1
    ring
  have hIic : μ.real (Set.Iic 0) = μ.real (Set.Ici (2 * a)) := by
    conv_lhs => rw [← hrefl]
    rw [measureReal_def, measureReal_def,
      Measure.map_apply (measurable_const_sub _) measurableSet_Iic]
    congr 2
    ext t
    simp
  have hsplit : μ.real (Set.Ioi 0) = μ.real (Set.Ioo 0 (2 * a)) + μ.real (Set.Ici (2 * a)) := by
    rw [← Set.Ioo_union_Ici_eq_Ioi (by linarith : (0 : ℝ) < 2 * a),
      measureReal_union (Set.disjoint_left.2 fun t (ht : t ∈ Set.Ioo 0 (2 * a))
        (ht' : t ∈ Set.Ici (2 * a)) => (not_le.2 ht.2) ht')
        measurableSet_Ici (measure_ne_top _ _) (measure_ne_top _ _)]
  have hpos : 0 < μ.real (Set.Ioo 0 (2 * a)) := by
    rw [measureReal_def]
    refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    intro h0
    have hac := gaussianReal_absolutelyContinuous' a (toNNReal_ne_zero_of_pos hN)
    have hvol := hac h0
    rw [Real.volume_Ioo] at hvol
    simp at hvol
    linarith
  have h1 := gaussianReal_real_Ioi_zero P N
  have hp : bpskCrossover P N = μ.real (Set.Iic 0) := rfl
  rw [← hμ] at h1
  linarith

/-- For `P > 0`, `N > 0`: the induced BSC has positive capacity `1 - h(p) > 0`. -/
lemma bsc_bpsk_capacity_pos (hN : 0 < N) (hP : 0 < P) :
    0 < 1 - binaryEntropy (bpskCrossover P N) := by
  have h0 := (bpskCrossover_nonneg : 0 ≤ bpskCrossover P N)
  have h1 := (bpskCrossover_le_one : bpskCrossover P N ≤ 1)
  have hlt := bpskCrossover_lt_half hN hP
  rw [Known.binaryEntropy_eq_binEntropy_div h0 h1]
  have hne : bpskCrossover P N ≠ 2⁻¹ := by
    intro h; rw [h] at hlt; norm_num at hlt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := Real.binEntropy_lt_log_two.mpr hne
  rw [sub_pos, div_lt_one hlog2]
  exact this

/-- The AWGN code obtained from a binary block code `(enc, dec)` by BPSK modulation and
    symbol-wise hard decisions.  Its decoder `y ↦ dec ([yᵢ > 0])ᵢ` is measurable. -/
noncomputable def bpskCode (P : ℝ) {n M : ℕ} (enc : Fin M → Fin n → Bool)
    (dec : (Fin n → Bool) → Fin M) : AwgnCode n M where
  encoder m i := bpskSymbol P (enc m i)
  decoder y := dec (fun i => hardDecision (y i))
  measurable_decoder := (measurable_of_finite dec).comp
    (measurable_pi_iff.mpr (fun i => measurable_hardDecision.comp (measurable_pi_apply i)))

lemma bpskCode_satisfiesPower (hP : 0 ≤ P) {n M : ℕ} (enc : Fin M → Fin n → Bool)
    (dec : (Fin n → Bool) → Fin M) : (bpskCode P enc dec).SatisfiesPower P := by
  intro m
  have h : ∀ i, (bpskSymbol P (enc m i)) ^ 2 = P := by
    intro i
    unfold bpskSymbol
    split_ifs <;> simp [Real.sq_sqrt hP]
  simp only [bpskCode, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    le_refl]

/-- The error probability of the BPSK code equals that of `(enc, dec)` over `BSC(p)ⁿ`. -/
lemma bpskCode_errorProb_toReal (hN : 0 < N) {n M : ℕ} (enc : Fin M → Fin n → Bool)
    (dec : (Fin n → Bool) → Fin M) (m : Fin M) :
    (awgnErrorProb (bpskCode P enc dec) N m).toReal =
      ∑ y : Fin n → Bool, if dec y ≠ m then
        ((bsc (bpskCrossover P N) bpskCrossover_nonneg bpskCrossover_le_one).power n).trans
          (enc m) y else 0 := by
  set x : Fin n → ℝ := fun i => bpskSymbol P (enc m i) with hx
  set thr : (Fin n → ℝ) → (Fin n → Bool) := fun y i => hardDecision (y i) with hthr_def
  have hthr : Measurable thr :=
    measurable_pi_iff.mpr (fun i => measurable_hardDecision.comp (measurable_pi_apply i))
  rw [awgnErrorProb_eq_errorProb, MeasurableBlockCode.errorProb]
  have hset : {y | (bpskCode P enc dec).decoder y ≠ m} = thr ⁻¹' {b | dec b ≠ m} := rfl
  have hfin : MeasurableSet {b : Fin n → Bool | dec b ≠ m} := (Set.toFinite _).measurableSet
  rw [hset, ← Measure.map_apply hthr hfin]
  have hmap : (awgnBlockLaw n N ((bpskCode P enc dec).encoder m)).map thr =
      Measure.pi (fun i => (gaussianReal (x i) N.toNNReal).map hardDecision) :=
    Measure.pi_map_pi (fun i => measurable_hardDecision.aemeasurable)
  rw [hmap]
  have hS : {b : Fin n → Bool | dec b ≠ m} = ↑(Finset.univ.filter (fun b => dec b ≠ m)) := by
    ext; simp
  rw [hS, ← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs with h
  · rw [Measure.pi_singleton, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Measure.map_apply measurable_hardDecision (measurableSet_singleton _)]
    exact gaussianReal_hardDecision hN (enc m i) (b i)
  · rfl

lemma awgnAvgErrorProb_ne_top {n M : ℕ} (hM : 1 ≤ M) (C : AwgnCode n M) (N : ℝ) :
    awgnAvgErrorProb C N ≠ ⊤ := by
  unfold awgnAvgErrorProb
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.mp hM)))
    (ENNReal.sum_ne_top.2 fun m _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (awgnErrorProb_le_one C N m))

/-- The average error of the BPSK code is exactly the DMC average error over `BSC(p)`. -/
lemma bpskCode_avgErrorProb (hN : 0 < N) {n M : ℕ} (hM : 1 ≤ M) (enc : Fin M → Fin n → Bool)
    (dec : (Fin n → Bool) → Fin M) [DecidableEq Bool] :
    (awgnAvgErrorProb (bpskCode P enc dec) N).toReal =
      dmcAvgError (bsc (bpskCrossover P N) bpskCrossover_nonneg bpskCrossover_le_one)
        n M enc dec := by
  rw [awgnAvgErrorProb_toReal]
  unfold dmcAvgError
  rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.one_le_iff_ne_zero.mp hM))]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [bpskCode_errorProb_toReal hN]

/-- **Achievability below the BPSK/hard-decision BSC capacity**: for `P ≥ 0`, `N > 0`, every rate
    `0 ≤ R < 1 - h(Q(√(P/N)))` is AWGN-achievable (in the sense of `IsAwgnAchievable`). -/
theorem isAwgnAchievable_of_lt_bsc (hN : 0 < N) (hP : 0 ≤ P) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < 1 - binaryEntropy (bpskCrossover P N)) : IsAwgnAchievable P N R := by
  have hach := Bridge.shannon_channel_coding_achievability
    (bsc (bpskCrossover P N) bpskCrossover_nonneg bpskCrossover_le_one) R hR0
    (by rw [Known.bsc_capacity]; exact hR)
  refine ⟨hR0, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hach.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hn₀ n hn
  refine ⟨bpskCode P enc dec, bpskCode_satisfiesPower hP enc dec, ?_⟩
  have hM : 1 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ := le_max_left _ _
  rw [ENNReal.le_ofReal_iff_toReal_le (awgnAvgErrorProb_ne_top hM _ N) hδ.le,
    @bpskCode_avgErrorProb P N hN n _ hM enc dec (Classical.decEq Bool)]
  exact herr

/-- **Non-vacuity**: the operational capacity is at least the BPSK/hard-decision rate
    `1 - h(Q(√(P/N)))`. -/
theorem bsc_rate_le_awgnOperationalCapacity (hN : 0 < N) (hP : 0 ≤ P) :
    1 - binaryEntropy (bpskCrossover P N) ≤ awgnOperationalCapacity P N := by
  by_contra hlt
  push Not at hlt
  have h0 := awgnOperationalCapacity_nonneg hN hP
  set R := (awgnOperationalCapacity P N + (1 - binaryEntropy (bpskCrossover P N))) / 2 with hRdef
  have hR := isAwgnAchievable_of_lt_bsc hN hP (R := R) (by rw [hRdef]; linarith)
    (by rw [hRdef]; linarith)
  have := le_awgnOperationalCapacity hN hP hR
  rw [hRdef] at this
  linarith

/-- **Non-vacuity**: for `P > 0`, `N > 0` the operational capacity is strictly positive. -/
theorem awgnOperationalCapacity_pos (hN : 0 < N) (hP : 0 < P) :
    0 < awgnOperationalCapacity P N :=
  lt_of_lt_of_le (bsc_bpsk_capacity_pos hN hP) (bsc_rate_le_awgnOperationalCapacity hN hP.le)

end Achievability

end InfoTheory.Known.GaussianChannel
