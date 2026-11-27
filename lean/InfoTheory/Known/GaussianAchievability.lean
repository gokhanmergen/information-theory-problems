import InfoTheory.Known.GaussianChannel
import InfoTheory.Known.CostConstrainedCoding
import Mathlib.MeasureTheory.Function.Floor

/-!
# Achievability for the AWGN Channel: `C_op(P, N) = ½ log₂(1 + P/N)`

Completes the validation of `InfoTheory.Core.GaussianOperational` by proving the matching
achievability bound, hence Shannon's AWGN capacity theorem in operational form
(Cover–Thomas Thm. 9.1.1; El Gamal–Kim Thm. 3.2):

* `awgnOperationalCapacity_eq` : `0 < N → 0 ≤ P →
    awgnOperationalCapacity P N = awgnCapacityFormula P N`;
* `isAwgnAchievable_of_lt_capacity` : every `0 ≤ R < ½ log₂(1 + P/N)` is achievable
  (codes with measurable decoders, per-codeword power `∑ᵢ xᵢ² ≤ nP`, vanishing average error).

## Route (El Gamal–Kim §3.4 "discretization procedure")

1. **Cost-constrained DMC coding** (`InfoTheory.Known.CostConstrainedCoding`): random coding +
   expurgation give codes all of whose codewords satisfy `∑ᵢ a(xᵢ)² ≤ nP` whenever the input law
   has `E[a(X)²] < P`.
2. **Transfer** (`awgnQuantDMC`, `quantCode`, `quantCode_avgErrorProb`,
   `isAwgnAchievable_of_quantDMC`): a finite set of input amplitudes `a : α → ℝ` together with a
   measurable output quantizer `q : ℝ → β` defines a genuine DMC
   `W_q(j | x) = P[q(a(x) + Z) = j]`; a DMC code `(enc, dec)` becomes an AWGN code with encoder
   `a ∘ enc` and measurable decoder `dec ∘ q^{⊗n}`, with *the same* error probability and power.
3. **Approximation** (`exists_good_quantization`): with the uniform quantizer `qIdx k` of step
   `1/k` on `[-k, k]` (used both to discretize the input `N(0, v)` and to quantize the output),
   `I(P_k, W_k) → ½ log(1 + v/N)` from below in the sense needed.  The lower bound is the
   **Donsker–Varadhan variational inequality** for finite alphabets (`mutualInfo_ge_dv`)
   `I · ln 2 ≥ E_{P_{XY}}[T] - ln E_{P_X ⊗ P_Y}[e^T]`
   with the Gaussian test function `T(x, y) = ln(φ_{x,N}(y)/φ_{0,v+N}(y))` evaluated at the cell
   values (`gLLR`).  Both terms are written as iterated Gaussian integrals (`dvA_eq`, `dvB_eq`)
   and passed to the limit by dominated convergence (`tendsto_dvA`, `tendsto_dvB`); the
   dominating functions are `exp(c(|t|+1)²)` with `c` below the Gaussian threshold
   (`integrable_exp_shift_sq_gaussianReal`).  The limit of the second term is exactly `1` by the
   identity `N(0,v) ∗ N(0,N) = N(0,v+N)` (`integral_integral_exp_gLLR`), and the limit of the
   first term is `½ ln((v+N)/N)` (`GaussianChannel.integral_awgnLetterLLR`).
4. **Conclusion**: choose `v < P` close to `P`, then a quantization level `k`, then apply 1–2;
   combine with the converse `GaussianChannel.awgnOperationalCapacity_le`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace InfoTheory.Known.GaussianAchievability

open InfoTheory InfoTheory.Bridge

/-! ### 1. A Donsker–Varadhan lower bound for the mutual information of a DMC -/

section DV

variable {α β : Type*} [Fintype α] [Fintype β]

lemma exists_pmf_pos (P : ProbDist α) : ∃ a, 0 < P.pmf a := by
  by_contra h
  push Not at h
  have : ∑ a, P.pmf a ≤ 0 := Finset.sum_nonpos fun a _ => h a
  linarith [P.sum_one]

/-- **Donsker–Varadhan / variational lower bound** (in nats): for every test function
    `T : α → β → ℝ`,
    `E_{P_{XY}}[T] - ln E_{P_X ⊗ P_Y}[e^T] ≤ I(X; Y) · ln 2`. -/
theorem mutualInfo_ge_dv (W : DMC α β) (Px : ProbDist α) (T : α → β → ℝ) :
    (∑ x, ∑ y, Px.pmf x * W.trans x y * T x y) -
      Real.log (∑ x, ∑ y, Px.pmf x * (∑ x', Px.pmf x' * W.trans x' y) * Real.exp (T x y))
      ≤ W.mutualInfo Px * Real.log 2 := by
  classical
  set J := W.joint Px with hJ
  set Py : β → ℝ := fun y => ∑ x', Px.pmf x' * W.trans x' y with hPy
  set c := ∑ x, ∑ y, Px.pmf x * Py y * Real.exp (T x y) with hc
  have hfst : ∀ x, J.fst.pmf x = Px.pmf x := fun x => by rw [hJ, dmc_joint_fst]
  have hsnd : ∀ y, J.snd.pmf y = Py y := fun y => rfl
  have hJpmf : ∀ ab : α × β, J.pmf ab = Px.pmf ab.1 * W.trans ab.1 ab.2 := fun ab => rfl
  have hPy0 : ∀ y, 0 ≤ Py y := fun y =>
    Finset.sum_nonneg fun x _ => mul_nonneg (Px.nonneg x) (W.nonneg x y)
  -- `c > 0`
  have hc_pos : 0 < c := by
    obtain ⟨x₀, hx₀⟩ := exists_pmf_pos Px
    obtain ⟨y₀, hy₀⟩ := exists_pmf_pos J.snd
    rw [hsnd] at hy₀
    refine Finset.sum_pos' (fun x _ => Finset.sum_nonneg fun y _ => ?_) ⟨x₀, Finset.mem_univ _, ?_⟩
    · exact mul_nonneg (mul_nonneg (Px.nonneg x) (hPy0 y)) (Real.exp_pos _).le
    · refine Finset.sum_pos' (fun y _ => ?_) ⟨y₀, Finset.mem_univ _, ?_⟩
      · exact mul_nonneg (mul_nonneg (Px.nonneg x₀) (hPy0 y)) (Real.exp_pos _).le
      · exact mul_pos (mul_pos hx₀ hy₀) (Real.exp_pos _)
  let q : α × β → ℝ := fun ab => Px.pmf ab.1 * Py ab.2 * Real.exp (T ab.1 ab.2) / c
  have hq0 : ∀ ab ∈ (Finset.univ : Finset (α × β)), 0 ≤ q ab := fun ab _ =>
    div_nonneg (mul_nonneg (mul_nonneg (Px.nonneg _) (hPy0 _)) (Real.exp_pos _).le) hc_pos.le
  have hpos : ∀ ab : α × β, 0 < J.pmf ab → 0 < Px.pmf ab.1 ∧ 0 < Py ab.2 := by
    intro ab h
    rw [← hfst, ← hsnd]
    exact ⟨lt_of_lt_of_le h (Known.pmf_le_fst J ab.1 ab.2),
      lt_of_lt_of_le h (Known.pmf_le_snd J ab.1 ab.2)⟩
  have hac : ∀ ab ∈ (Finset.univ : Finset (α × β)), 0 < J.pmf ab → 0 < q ab := by
    intro ab _ h
    obtain ⟨h1, h2⟩ := hpos ab h
    exact div_pos (mul_pos (mul_pos h1 h2) (Real.exp_pos _)) hc_pos
  have hqsum : ∑ ab, q ab = 1 := by
    simp only [q, ← Finset.sum_div, Fintype.sum_prod_type]
    exact div_self hc_pos.ne'
  have hsum : ∑ ab ∈ (Finset.univ : Finset (α × β)), q ab ≤
      ∑ ab ∈ (Finset.univ : Finset (α × β)), J.pmf ab := by
    rw [hqsum, J.sum_one]
  have hg := Known.gibbs_sum Finset.univ J.pmf q hq0 hac hsum
  have hterm : ∀ ab : α × β,
      (if J.pmf ab ≤ 0 then 0 else J.pmf ab * Real.log (J.pmf ab / q ab)) =
        (if J.pmf ab ≤ 0 then 0 else
          J.pmf ab * Real.log (J.pmf ab / (J.fst.pmf ab.1 * J.snd.pmf ab.2))) -
        J.pmf ab * T ab.1 ab.2 + J.pmf ab * Real.log c := by
    intro ab
    split_ifs with h
    · have h0 : J.pmf ab = 0 := le_antisymm h (J.nonneg ab)
      simp [h0]
    · have hJ0 : 0 < J.pmf ab := lt_of_not_ge h
      obtain ⟨h1, h2⟩ := hpos ab hJ0
      rw [hfst, hsnd]
      have hq : q ab = (Px.pmf ab.1 * Py ab.2) * Real.exp (T ab.1 ab.2) / c := rfl
      rw [Real.log_div hJ0.ne' (hac ab (Finset.mem_univ _) hJ0).ne',
        Real.log_div hJ0.ne' (mul_pos h1 h2).ne', hq,
        Real.log_div (mul_pos (mul_pos h1 h2) (Real.exp_pos _)).ne' hc_pos.ne',
        Real.log_mul (mul_pos h1 h2).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
  simp_rw [hterm] at hg
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, J.sum_one,
    one_mul] at hg
  have hMI : W.mutualInfo Px * Real.log 2 = ∑ ab : α × β, (if J.pmf ab ≤ 0 then 0 else
      J.pmf ab * Real.log (J.pmf ab / (J.fst.pmf ab.1 * J.snd.pmf ab.2))) :=
    Known.mutualInfo_mul_log_two J
  have hET : ∑ ab : α × β, J.pmf ab * T ab.1 ab.2 = ∑ x, ∑ y, Px.pmf x * W.trans x y * T x y := by
    rw [Fintype.sum_prod_type]; rfl
  rw [hMI]
  linarith

end DV

/-! ### 2. The transfer lemma: quantized-output DMCs embed into the AWGN channel -/

section Transfer

variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma sum_measureReal_preimage_eq_one {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ι}
    (hf : Measurable f) : ∑ i, μ.real (f ⁻¹' {i}) = 1 := by
  rw [sum_measureReal_preimage_singleton Finset.univ
    (fun i _ => hf (measurableSet_singleton i))]
  simp

/-- The DMC obtained from the AWGN channel by restricting the input to the finite set of
    amplitudes `a : α → ℝ` and quantizing the output with a measurable map `q : ℝ → β`:
    `W(j | x) = P[q(a(x) + Z) = j]`, `Z ~ N(0, N)`. -/
noncomputable def awgnQuantDMC (N : ℝ) (a : α → ℝ) (q : ℝ → β) (hq : Measurable q) :
    DMC α β where
  trans x j := (gaussianReal (a x) N.toNNReal).real (q ⁻¹' {j})
  nonneg _ _ := measureReal_nonneg
  sum_one _ := sum_measureReal_preimage_eq_one _ hq

/-- The AWGN code induced by a block code `(enc, dec)` for `awgnQuantDMC N a q`: transmit the
    amplitudes `a(enc m i)` and decode `y ↦ dec (q ∘ y)` (a measurable decoder). -/
noncomputable def quantCode (a : α → ℝ) (q : ℝ → β) (hq : Measurable q) {n M : ℕ}
    (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) : AwgnCode n M where
  encoder m i := a (enc m i)
  decoder y := dec (fun i => q (y i))
  measurable_decoder := (measurable_of_finite dec).comp
    (measurable_pi_iff.mpr fun i => hq.comp (measurable_pi_apply i))

/-- **Transfer of error probabilities**: the AWGN error probability of `quantCode` equals the
    error probability of `(enc, dec)` over the DMC `awgnQuantDMC N a q`. -/
lemma quantCode_errorProb_toReal (N : ℝ) (a : α → ℝ) (q : ℝ → β) (hq : Measurable q)
    {n M : ℕ} (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) (m : Fin M) :
    (awgnErrorProb (quantCode a q hq enc dec) N m).toReal =
      ∑ y : Fin n → β, if dec y ≠ m then
        ((awgnQuantDMC N a q hq).power n).trans (enc m) y else 0 := by
  classical
  set thr : (Fin n → ℝ) → (Fin n → β) := fun y i => q (y i) with hthr_def
  have hthr : Measurable thr := measurable_pi_iff.mpr fun i => hq.comp (measurable_pi_apply i)
  rw [GaussianChannel.awgnErrorProb_eq_errorProb, MeasurableBlockCode.errorProb]
  have hset : {y | (quantCode a q hq enc dec).decoder y ≠ m} = thr ⁻¹' {b | dec b ≠ m} := rfl
  have hfin : MeasurableSet {b : Fin n → β | dec b ≠ m} := (Set.toFinite _).measurableSet
  rw [hset, ← Measure.map_apply hthr hfin]
  have hmap : (awgnBlockLaw n N ((quantCode a q hq enc dec).encoder m)).map thr =
      Measure.pi (fun i => (gaussianReal (a (enc m i)) N.toNNReal).map q) :=
    Measure.pi_map_pi (fun i => hq.aemeasurable)
  rw [hmap]
  have hS : {b : Fin n → β | dec b ≠ m} = ↑(Finset.univ.filter (fun b => dec b ≠ m)) := by
    ext; simp
  rw [hS, ← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs with h
  · rw [Measure.pi_singleton, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Measure.map_apply hq (measurableSet_singleton _)]
    rfl
  · rfl

lemma quantCode_avgErrorProb [DecidableEq β] (N : ℝ) (a : α → ℝ) (q : ℝ → β)
    (hq : Measurable q) {n M : ℕ} (hM : 1 ≤ M) (enc : Fin M → Fin n → α)
    (dec : (Fin n → β) → Fin M) :
    (awgnAvgErrorProb (quantCode a q hq enc dec) N).toReal =
      dmcAvgError (awgnQuantDMC N a q hq) n M enc dec := by
  rw [GaussianChannel.awgnAvgErrorProb_toReal]
  unfold dmcAvgError
  rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.one_le_iff_ne_zero.mp hM))]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [quantCode_errorProb_toReal]

/-- **Transfer theorem**: if `R < I(P_X, W_q)` for the quantized DMC `W_q = awgnQuantDMC N a q`
    and an input law with `E[a(X)²] < P`, then `R` is AWGN-achievable under power `P`
    (cost-constrained DMC coding + the error-preserving embedding `quantCode`). -/
theorem isAwgnAchievable_of_quantDMC [DecidableEq β] {N P R : ℝ} (a : α → ℝ) (q : ℝ → β)
    (hq : Measurable q) (Px : ProbDist α) (hR0 : 0 ≤ R)
    (hR : R < (awgnQuantDMC N a q hq).mutualInfo Px)
    (hpow : ∑ x, Px.pmf x * a x ^ 2 < P) : IsAwgnAchievable P N R := by
  refine ⟨hR0, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := CostConstrainedCoding.dmc_cost_constrained_achievable
    (awgnQuantDMC N a q hq) Px (fun x => a x ^ 2) (B := P) hpow hR0 hR hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨enc, dec, hcost, herr⟩ := hn₀ n hn
  refine ⟨quantCode a q hq enc dec, fun m => hcost m, ?_⟩
  have hM : 1 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ := le_max_left _ _
  rw [ENNReal.le_ofReal_iff_toReal_le (GaussianChannel.awgnAvgErrorProb_ne_top hM _ N) hδ.le,
    quantCode_avgErrorProb N a q hq hM enc dec]
  convert herr

end Transfer

/-! ### 3. One-letter Gaussian estimates -/

section Analytic

variable {N S : ℝ}

/-- Closed form of the AWGN log-likelihood ratio `ln(φ_{x,N}(y) / φ_{0,S}(y))`. -/
noncomputable def gLLR (N S x y : ℝ) : ℝ :=
  1 / 2 * Real.log (S / N) - (y - x) ^ 2 / (2 * N) + y ^ 2 / (2 * S)

lemma continuous_gLLR (N S : ℝ) : Continuous (fun p : ℝ × ℝ => gLLR N S p.1 p.2) := by
  unfold gLLR; fun_prop

lemma gLLR_eq_awgnLetterLLR (hN : 0 < N) (hS : 0 < S) (x y : ℝ) :
    gLLR N S x y = GaussianChannel.awgnLetterLLR N S x y :=
  (GaussianChannel.awgnLetterLLR_eq hN hS x y).symm

lemma pdf_mul_exp_gLLR (hN : 0 < N) (hS : 0 < S) (x y : ℝ) :
    gaussianPDFReal 0 S.toNNReal y * Real.exp (gLLR N S x y) =
      gaussianPDFReal x N.toNNReal y := by
  have h1 := gaussianPDFReal_pos x _ y (GaussianChannel.toNNReal_ne_zero_of_pos hN)
  have h2 := gaussianPDFReal_pos 0 _ y (GaussianChannel.toNNReal_ne_zero_of_pos hS)
  rw [gLLR_eq_awgnLetterLLR hN hS, GaussianChannel.awgnLetterLLR, Real.exp_log (div_pos h1 h2)]
  field_simp

lemma gLLR_le (hN : 0 < N) (hNS : N < S) (x y : ℝ) :
    gLLR N S x y ≤ 1 / 2 * Real.log (S / N) + x ^ 2 / (2 * (2 * S - N)) + y ^ 2 / (4 * S) := by
  have hS : 0 < S := by linarith
  have h2 : 0 < 2 * S - N := by linarith
  have key : x ^ 2 / (2 * (2 * S - N)) + y ^ 2 / (4 * S) -
      (-((y - x) ^ 2 / (2 * N)) + y ^ 2 / (2 * S)) =
      ((2 * S - N) * y - 2 * S * x) ^ 2 / (4 * S * N * (2 * S - N)) := by
    field_simp
    ring
  have hnn : 0 ≤ ((2 * S - N) * y - 2 * S * x) ^ 2 / (4 * S * N * (2 * S - N)) := by positivity
  unfold gLLR
  linarith

lemma abs_gLLR_le (hN : 0 < N) (hS : 0 < S) (x y : ℝ) :
    |gLLR N S x y| ≤ |1 / 2 * Real.log (S / N)| + (x ^ 2 + y ^ 2) * (1 / N + 1 / (2 * S)) := by
  have h1 : (y - x) ^ 2 / (2 * N) ≤ (x ^ 2 + y ^ 2) / N := by
    rw [div_le_div_iff₀ (by positivity) hN]; nlinarith [sq_nonneg (x + y)]
  have h2 : y ^ 2 / (2 * S) ≤ (x ^ 2 + y ^ 2) / (2 * S) := by
    gcongr; nlinarith [sq_nonneg x]
  have h3 : 0 ≤ (y - x) ^ 2 / (2 * N) := by positivity
  have h4 : 0 ≤ y ^ 2 / (2 * S) := by positivity
  have hexp : (x ^ 2 + y ^ 2) * (1 / N + 1 / (2 * S)) =
      (x ^ 2 + y ^ 2) / N + (x ^ 2 + y ^ 2) / (2 * S) := by ring
  rw [hexp]
  unfold gLLR
  have := abs_nonneg (1 / 2 * Real.log (S / N))
  have := le_abs_self (1 / 2 * Real.log (S / N))
  have := neg_abs_le (1 / 2 * Real.log (S / N))
  rw [abs_le]
  constructor <;> linarith

lemma integrable_exp_mul_sq_gaussianReal {v c : ℝ} (hv : 0 < v) (hc : c < 1 / (2 * v)) :
    Integrable (fun t => Real.exp (c * t ^ 2)) (gaussianReal 0 v.toNNReal) := by
  have hv' : v.toNNReal ≠ 0 := GaussianChannel.toNNReal_ne_zero_of_pos hv
  rw [gaussianReal_of_var_ne_zero _ hv',
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have hfun : (fun t => (gaussianPDF 0 v.toNNReal t).toReal • Real.exp (c * t ^ 2)) =
      fun t => (√(2 * Real.pi * v))⁻¹ * Real.exp (-(1 / (2 * v) - c) * t ^ 2) := by
    funext t
    rw [toReal_gaussianPDF]
    simp only [gaussianPDFReal, smul_eq_mul, Real.coe_toNNReal _ hv.le]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun]
  exact (integrable_exp_neg_mul_sq (by linarith)).const_mul _

lemma integrable_exp_shift_sq_gaussianReal {v c : ℝ} (hv : 0 < v) (hc : c < 1 / (2 * v)) :
    Integrable (fun t => Real.exp (c * (|t| + 1) ^ 2)) (gaussianReal 0 v.toNNReal) := by
  set c' := (c + 1 / (2 * v)) / 2 with hc'
  set d := c' - c with hd
  have hd0 : 0 < d := by rw [hd, hc']; linarith
  have hc'v : c' < 1 / (2 * v) := by rw [hc']; linarith
  set K := c + c ^ 2 / d with hK
  have hbound : ∀ t : ℝ, c * (|t| + 1) ^ 2 ≤ c' * t ^ 2 + K := by
    intro t
    have key : 0 ≤ (d * |t| - c) ^ 2 / d := by positivity
    have hc'd : c' = c + d := by rw [hd]; ring
    have heq : c' * t ^ 2 + K - c * (|t| + 1) ^ 2 = (d * |t| - c) ^ 2 / d := by
      rw [hc'd, hK, ← sq_abs t]
      field_simp
      ring
    linarith
  refine ((integrable_exp_mul_sq_gaussianReal hv hc'v).const_mul (Real.exp K)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (c * (|t| + 1) ^ 2)).aestronglyMeasurable
  · refine ae_of_all _ fun t => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hbound t])

lemma integral_gaussianReal_eq_translate (x : ℝ) (v : ℝ≥0) (f : ℝ → ℝ) :
    ∫ y, f y ∂gaussianReal x v = ∫ z, f (x + z) ∂gaussianReal 0 v := by
  have h : gaussianReal x v = (gaussianReal 0 v).map (MeasurableEquiv.addLeft x) := by
    have := gaussianReal_map_const_add (μ := 0) (v := v) x
    rw [zero_add] at this
    rw [← this]
    rfl
  rw [h, integral_map_equiv]
  rfl

lemma integral_sq_gaussianReal_zero (v : ℝ≥0) : ∫ t, t ^ 2 ∂gaussianReal 0 v = v := by
  simpa using GaussianChannel.integral_sq_sub_gaussianReal 0 v

lemma integrable_sq_gaussianReal_zero (v : ℝ≥0) :
    Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 v) := by
  simpa using GaussianChannel.integrable_sq_sub_gaussianReal 0 v

end Analytic

/-! ### 4. The uniform quantizer / discretizer -/

section Quantizer

/-- Number of quantization cells: `2k² + 1` (step `1/k` on `[-k, k]`). -/
def qCard (k : ℕ) : ℕ := 2 * k ^ 2 + 1

/-- Clamp an integer to `[-k², k²]`. -/
def qClamp (k : ℕ) (z : ℤ) : ℤ := max (-((k ^ 2 : ℕ) : ℤ)) (min ((k ^ 2 : ℕ) : ℤ) z)

lemma qClamp_bounds (k : ℕ) (z : ℤ) :
    -((k ^ 2 : ℕ) : ℤ) ≤ qClamp k z ∧ qClamp k z ≤ ((k ^ 2 : ℕ) : ℤ) := by
  unfold qClamp
  have h0 : (0 : ℤ) ≤ ((k ^ 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Cell index of a (rounded) integer. -/
def qIdxOfInt (k : ℕ) (z : ℤ) : Fin (qCard k) :=
  ⟨(qClamp k z + ((k ^ 2 : ℕ) : ℤ)).toNat, by
    have h := qClamp_bounds k z
    unfold qCard
    generalize k ^ 2 = K at h ⊢
    omega⟩

/-- The quantizer `t ↦` index of `clamp(round(k t), -k², k²)`. -/
noncomputable def qIdx (k : ℕ) (t : ℝ) : Fin (qCard k) := qIdxOfInt k ⌊(k : ℝ) * t + 1 / 2⌋

lemma measurable_qIdx (k : ℕ) : Measurable (qIdx k) :=
  (Measurable.of_discrete (f := qIdxOfInt k)).comp
    (Measurable.comp Int.measurable_floor
      (by fun_prop : Measurable fun t : ℝ => (k : ℝ) * t + 1 / 2))

/-- Reconstruction value of cell `i`: `(i - k²)/k`. -/
noncomputable def qVal (k : ℕ) (i : Fin (qCard k)) : ℝ := ((i : ℕ) - ((k ^ 2 : ℕ) : ℝ)) / k

/-- The rounding map `t ↦ qVal (qIdx t)`. -/
noncomputable def qRound (k : ℕ) (t : ℝ) : ℝ := qVal k (qIdx k t)

lemma measurable_qRound (k : ℕ) : Measurable (qRound k) :=
  (Measurable.of_discrete (f := qVal k)).comp (measurable_qIdx k)

lemma qRound_eq (k : ℕ) (t : ℝ) :
    qRound k t = (qClamp k ⌊(k : ℝ) * t + 1 / 2⌋ : ℝ) / k := by
  unfold qRound qVal qIdx qIdxOfInt
  congr 1
  have h := qClamp_bounds k ⌊(k : ℝ) * t + 1 / 2⌋
  have hnn : 0 ≤ qClamp k ⌊(k : ℝ) * t + 1 / 2⌋ + ((k ^ 2 : ℕ) : ℤ) := by linarith [h.1]
  have h1 : (((qClamp k ⌊(k : ℝ) * t + 1 / 2⌋ + ((k ^ 2 : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
      qClamp k ⌊(k : ℝ) * t + 1 / 2⌋ + ((k ^ 2 : ℕ) : ℤ) := Int.toNat_of_nonneg hnn
  have h2 : (((qClamp k ⌊(k : ℝ) * t + 1 / 2⌋ + ((k ^ 2 : ℕ) : ℤ)).toNat : ℕ) : ℝ) =
      (((qClamp k ⌊(k : ℝ) * t + 1 / 2⌋ + ((k ^ 2 : ℕ) : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast h1
  simp only
  rw [h2]
  push_cast
  ring

lemma abs_floor_add_half_sub_le (s : ℝ) : |(⌊s + 1 / 2⌋ : ℝ) - s| ≤ 1 / 2 := by
  have h1 := Int.floor_le (s + 1 / 2)
  have h2 := Int.lt_floor_add_one (s + 1 / 2)
  rw [abs_le]; constructor <;> linarith

lemma abs_qClamp_le (k : ℕ) (z : ℤ) : |(qClamp k z : ℝ)| ≤ |(z : ℝ)| := by
  have h0 : (0 : ℤ) ≤ ((k ^ 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have : |qClamp k z| ≤ |z| := by
    unfold qClamp
    rw [abs_le]
    constructor
    · have : -|z| ≤ min ((k ^ 2 : ℕ) : ℤ) z :=
        le_min (by linarith [abs_nonneg z]) (neg_abs_le z)
      exact le_trans this (le_max_right _ _)
    · exact max_le (by linarith [abs_nonneg z]) (le_trans (min_le_right _ _) (le_abs_self z))
  exact_mod_cast this

lemma abs_floor_le (k : ℕ) (t : ℝ) :
    |(⌊(k : ℝ) * t + 1 / 2⌋ : ℝ)| ≤ k * |t| + 1 / 2 := by
  have h2 := abs_floor_add_half_sub_le ((k : ℝ) * t)
  have := abs_sub_abs_le_abs_sub (⌊(k : ℝ) * t + 1 / 2⌋ : ℝ) ((k : ℝ) * t)
  rw [abs_mul, Nat.abs_cast] at this
  linarith

/-- `|qRound k t| ≤ |t| + 1`. -/
lemma abs_qRound_le (k : ℕ) (t : ℝ) : |qRound k t| ≤ |t| + 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [qRound_eq]
    simp only [Nat.cast_zero, div_zero, abs_zero]
    positivity
  · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    rw [qRound_eq, abs_div, Nat.abs_cast, div_le_iff₀ hk0]
    have h1 := abs_qClamp_le k ⌊(k : ℝ) * t + 1 / 2⌋
    have h3 := abs_floor_le k t
    nlinarith [abs_nonneg t]

/-- Without clamping (`|t| + 1 ≤ k`) the rounding error is at most `1/k`. -/
lemma abs_qRound_sub_le (k : ℕ) (t : ℝ) (ht : |t| + 1 ≤ k) : |qRound k t - t| ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg t]
  set r := ⌊(k : ℝ) * t + 1 / 2⌋ with hr
  have h2 := abs_floor_add_half_sub_le ((k : ℝ) * t)
  have h3 := abs_floor_le k t
  have hrabs : |(r : ℝ)| < ((k ^ 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith [abs_nonneg t, mul_le_mul_of_nonneg_left ht hk0.le]
  have hclamp : qClamp k r = r := by
    have h' : |r| < ((k ^ 2 : ℕ) : ℤ) := by exact_mod_cast hrabs
    rw [abs_lt] at h'
    unfold qClamp
    rw [min_eq_right h'.2.le, max_eq_right h'.1.le]
  have : (r : ℝ) / k - t = ((r : ℝ) - k * t) / k := by field_simp
  rw [qRound_eq, ← hr, hclamp, this, abs_div, Nat.abs_cast]
  gcongr
  linarith

/-- If `w_k → x` then `qRound k (w k) → x`. -/
lemma tendsto_qRound {w : ℕ → ℝ} {x : ℝ} (hw : Tendsto w atTop (𝓝 x)) :
    Tendsto (fun k => qRound k (w k)) atTop (𝓝 x) := by
  have hev : ∀ᶠ k : ℕ in atTop, |qRound k (w k) - w k| ≤ 1 / k := by
    have h1 : ∀ᶠ k in atTop, |w k - x| < 1 :=
      (Metric.tendsto_nhds.mp hw 1 one_pos).mono fun k hk => by rwa [Real.dist_eq] at hk
    have h2 : ∀ᶠ k : ℕ in atTop, |x| + 2 ≤ (k : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    filter_upwards [h1, h2] with k hk1 hk2
    apply abs_qRound_sub_le
    have := abs_sub_abs_le_abs_sub (w k) x
    linarith
  have hlim : Tendsto (fun k => qRound k (w k) - w k) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [hev] with k hk
    rwa [Real.norm_eq_abs]
  have := hlim.add hw
  simpa using this

end Quantizer

/-! ### 5. Discretized Gaussian input, quantized channel, and integral representations -/

section Representation

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Push-forward of a probability measure on `ℝ` along a measurable map into a finite type. -/
noncomputable def pushPD (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ι)
    (hf : Measurable f) : ProbDist ι where
  pmf i := μ.real (f ⁻¹' {i})
  nonneg _ := measureReal_nonneg
  sum_one := sum_measureReal_preimage_eq_one μ hf

lemma sum_measureReal_preimage_mul (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ι}
    (hf : Measurable f) (F : ι → ℝ) :
    ∑ i, μ.real (f ⁻¹' {i}) * F i = ∫ u, F (f u) ∂μ := by
  rw [← integral_map hf.aemeasurable (measurable_of_finite F).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_measureReal_apply hf (measurableSet_singleton i), smul_eq_mul]

variable (v N : ℝ)

/-- The discretized Gaussian input law: `N(0, v)` pushed through the quantizer `qIdx k`. -/
noncomputable def gIn (k : ℕ) : ProbDist (Fin (qCard k)) :=
  pushPD (gaussianReal 0 v.toNNReal) (qIdx k) (measurable_qIdx k)

/-- The quantized AWGN channel with input amplitudes `qVal k` and output quantizer `qIdx k`. -/
noncomputable def gChan (k : ℕ) : DMC (Fin (qCard k)) (Fin (qCard k)) :=
  awgnQuantDMC N (qVal k) (qIdx k) (measurable_qIdx k)

lemma sum_gIn_mul (k : ℕ) (h : ℝ → ℝ) :
    ∑ i, (gIn v k).pmf i * h (qVal k i) = ∫ u, h (qRound k u) ∂gaussianReal 0 v.toNNReal :=
  sum_measureReal_preimage_mul _ (measurable_qIdx k) (fun i => h (qVal k i))

lemma sum_gChan_mul (k : ℕ) (i : Fin (qCard k)) (g : ℝ → ℝ) :
    ∑ j, (gChan N k).trans i j * g (qVal k j) =
      ∫ z, g (qRound k (qVal k i + z)) ∂gaussianReal 0 N.toNNReal := by
  have h := sum_measureReal_preimage_mul (gaussianReal (qVal k i) N.toNNReal) (measurable_qIdx k)
    (fun j => g (qVal k j))
  have h2 := integral_gaussianReal_eq_translate (qVal k i) N.toNNReal
    (fun y => g (qVal k (qIdx k y)))
  exact h.trans h2

/-- The first Donsker–Varadhan term as an iterated Gaussian integral. -/
lemma dvA_eq (k : ℕ) (T : ℝ → ℝ → ℝ) :
    ∑ x, ∑ y, (gIn v k).pmf x * (gChan N k).trans x y * T (qVal k x) (qVal k y) =
      ∫ u, ∫ z, T (qRound k u) (qRound k (qRound k u + z))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v.toNNReal := by
  have h1 : ∀ x, ∑ y, (gIn v k).pmf x * (gChan N k).trans x y * T (qVal k x) (qVal k y) =
      (gIn v k).pmf x *
        ∫ z, T (qVal k x) (qRound k (qVal k x + z)) ∂gaussianReal 0 N.toNNReal := by
    intro x
    rw [← sum_gChan_mul N k x (T (qVal k x)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  exact sum_gIn_mul v k (fun a => ∫ z, T a (qRound k (a + z)) ∂gaussianReal 0 N.toNNReal)

/-- The second Donsker–Varadhan term as an iterated Gaussian integral. -/
lemma dvB_eq (k : ℕ) (T : ℝ → ℝ → ℝ) :
    ∑ x, ∑ y, (gIn v k).pmf x * (∑ x', (gIn v k).pmf x' * (gChan N k).trans x' y) *
        Real.exp (T (qVal k x) (qVal k y)) =
      ∫ u', ∫ u, ∫ z, Real.exp (T (qRound k u') (qRound k (qRound k u + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v.toNNReal ∂gaussianReal 0 v.toNNReal := by
  have h1 : ∀ x, ∑ y, (gIn v k).pmf x * (∑ x', (gIn v k).pmf x' * (gChan N k).trans x' y) *
        Real.exp (T (qVal k x) (qVal k y)) =
      (gIn v k).pmf x * ∑ x', (gIn v k).pmf x' *
        ∑ y, (gChan N k).trans x' y * Real.exp (T (qVal k x) (qVal k y)) := by
    intro x
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y _ => by ring
  have h2 : ∀ x x', ∑ y, (gChan N k).trans x' y * Real.exp (T (qVal k x) (qVal k y)) =
      ∫ z, Real.exp (T (qVal k x) (qRound k (qVal k x' + z))) ∂gaussianReal 0 N.toNNReal :=
    fun x x' => sum_gChan_mul N k x' (fun b => Real.exp (T (qVal k x) b))
  have h3 : ∀ x, ∑ x', (gIn v k).pmf x' *
        ∫ z, Real.exp (T (qVal k x) (qRound k (qVal k x' + z))) ∂gaussianReal 0 N.toNNReal =
      ∫ u, ∫ z, Real.exp (T (qVal k x) (qRound k (qRound k u + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v.toNNReal :=
    fun x => sum_gIn_mul v k
      (fun a => ∫ z, Real.exp (T (qVal k x) (qRound k (a + z))) ∂gaussianReal 0 N.toNNReal)
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  simp_rw [h2, h3]
  exact sum_gIn_mul v k (fun a => ∫ u, ∫ z, Real.exp (T a (qRound k (qRound k u + z)))
    ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v.toNNReal)

/-- The input power as a Gaussian integral. -/
lemma power_gIn_eq (k : ℕ) :
    ∑ i, (gIn v k).pmf i * qVal k i ^ 2 = ∫ u, qRound k u ^ 2 ∂gaussianReal 0 v.toNNReal :=
  sum_gIn_mul v k (fun a => a ^ 2)

end Representation

/-! ### 6. Limits as the quantization is refined -/

section Limits

variable {v N : ℝ}

lemma aesm_comp_qRound (k : ℕ) (H : ℝ → ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun u => H (qRound k u)) μ :=
  ((Measurable.of_discrete (f := fun i => H (qVal k i))).comp (measurable_qIdx k)).aestronglyMeasurable

lemma sq_le_two_sq_add_two {x u : ℝ} (h : |x| ≤ |u| + 1) : x ^ 2 ≤ 2 * u ^ 2 + 2 := by
  have h1 : x ^ 2 ≤ (|u| + 1) ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) h 2
  nlinarith [sq_abs u, sq_nonneg (|u| - 1)]

lemma sq_le_shift_sq {y u z : ℝ} (h : |y| ≤ |u| + |z| + 2) :
    y ^ 2 ≤ 2 * (|u| + 1) ^ 2 + 2 * (|z| + 1) ^ 2 := by
  have h1 : y ^ 2 ≤ ((|u| + 1) + (|z| + 1)) ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) (by linarith) 2
  nlinarith [sq_nonneg ((|u| + 1) - (|z| + 1))]

lemma abs_qRound_comp_le (k : ℕ) (u z : ℝ) :
    |qRound k (qRound k u + z)| ≤ |u| + |z| + 2 := by
  have h1 := abs_qRound_le k u
  have h2 := abs_qRound_le k (qRound k u + z)
  have h3 := abs_add_le (qRound k u) z
  linarith

lemma tendsto_qRound_pair (u z : ℝ) :
    Tendsto (fun k : ℕ => (qRound k u, qRound k (qRound k u + z))) atTop (𝓝 (u, u + z)) := by
  have h1 : Tendsto (fun k : ℕ => qRound k u) atTop (𝓝 u) := tendsto_qRound tendsto_const_nhds
  exact h1.prodMk_nhds (tendsto_qRound (h1.add_const z))

lemma tendsto_gLLR_qRound (N S u' u z : ℝ) :
    Tendsto (fun k : ℕ => gLLR N S (qRound k u') (qRound k (qRound k u + z))) atTop
      (𝓝 (gLLR N S u' (u + z))) := by
  have h1 : Tendsto (fun k : ℕ => qRound k u') atTop (𝓝 u') := tendsto_qRound tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ => qRound k u) atTop (𝓝 u) := tendsto_qRound tendsto_const_nhds
  have h3 : Tendsto (fun k : ℕ => (qRound k u', qRound k (qRound k u + z))) atTop
      (𝓝 (u', u + z)) := h1.prodMk_nhds (tendsto_qRound (h2.add_const z))
  have h4 := ((continuous_gLLR N S).tendsto (u', u + z)).comp h3
  exact h4

lemma tendsto_exp_gLLR_qRound (N S u' u z : ℝ) :
    Tendsto (fun k : ℕ => Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z)))) atTop
      (𝓝 (Real.exp (gLLR N S u' (u + z)))) := by
  have h := (Real.continuous_exp.tendsto _).comp (tendsto_gLLR_qRound N S u' u z)
  exact h

lemma measurable_gLLR_qRound (N S : ℝ) (k : ℕ) (u' u : ℝ) :
    Measurable (fun z => gLLR N S (qRound k u') (qRound k (qRound k u + z))) := by
  have h : Measurable (fun z => (qRound k u', qRound k (qRound k u + z))) :=
    measurable_const.prodMk ((measurable_qRound k).comp (measurable_const_add _))
  have h2 := (continuous_gLLR N S).measurable.comp h
  exact h2

lemma integral_const_add_mul_sq (a b : ℝ) (w : ℝ) (hw : 0 ≤ w) :
    ∫ t, (a + b * t ^ 2) ∂gaussianReal 0 w.toNNReal = a + b * w := by
  rw [integral_add (integrable_const _) ((integrable_sq_gaussianReal_zero _).const_mul _),
    integral_const, integral_const_mul, integral_sq_gaussianReal_zero, Real.coe_toNNReal _ hw]
  simp

lemma integrable_const_add_mul_sq (a b : ℝ) (w : ℝ≥0) :
    Integrable (fun t : ℝ => a + b * t ^ 2) (gaussianReal 0 w) :=
  (integrable_const _).add ((integrable_sq_gaussianReal_zero _).const_mul _)

/-- **Limit of the first DV term**: `→ ½ ln(S/N)` with `S = v + N`. -/
theorem tendsto_dvA (hv : 0 < v) (hN : 0 < N) :
    Tendsto (fun k : ℕ => ∫ u, ∫ z, gLLR N (v + N) (qRound k u) (qRound k (qRound k u + z))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v.toNNReal) atTop
      (𝓝 (1 / 2 * Real.log ((v + N) / N))) := by
  set S := v + N with hS_def
  have hS : 0 < S := by linarith
  set c₀ := |1 / 2 * Real.log (S / N)| with hc₀
  set K := 1 / N + 1 / (2 * S) with hK_def
  have hK : 0 ≤ K := by positivity
  -- pointwise domination
  have hbd : ∀ (k : ℕ) (u z : ℝ),
      ‖gLLR N S (qRound k u) (qRound k (qRound k u + z))‖ ≤
        (c₀ + K * (5 * u ^ 2 + 14)) + 3 * K * z ^ 2 := by
    intro k u z
    have hx := sq_le_two_sq_add_two (abs_qRound_le k u)
    have hy := sq_le_shift_sq (abs_qRound_comp_le k u z)
    have hy' : qRound k (qRound k u + z) ^ 2 ≤ 3 * u ^ 2 + 3 * z ^ 2 + 12 := by
      nlinarith [sq_abs u, sq_abs z, sq_nonneg (|u| - 2), sq_nonneg (|z| - 2)]
    rw [Real.norm_eq_abs]
    refine le_trans (abs_gLLR_le hN hS _ _) ?_
    have : (qRound k u ^ 2 + qRound k (qRound k u + z) ^ 2) * K ≤
        (5 * u ^ 2 + 3 * z ^ 2 + 14) * K := mul_le_mul_of_nonneg_right (by linarith) hK
    linarith
  -- the limit integrand
  have hinner : ∀ u : ℝ, ∫ z, gLLR N S u (u + z) ∂gaussianReal 0 N.toNNReal =
      (1 / 2 * Real.log (S / N) - 1 / 2 + N / (2 * S)) + 1 / (2 * S) * u ^ 2 := by
    intro u
    have h := integral_gaussianReal_eq_translate u N.toNNReal (fun y => gLLR N S u y)
    rw [← h]
    have h2 : (fun y => gLLR N S u y) = GaussianChannel.awgnLetterLLR N S u := by
      funext y; exact gLLR_eq_awgnLetterLLR hN hS u y
    rw [h2, GaussianChannel.integral_awgnLetterLLR hN hS u]
    ring
  -- inner convergence
  have hconv_in : ∀ u : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, gLLR N S (qRound k u) (qRound k (qRound k u + z)) ∂gaussianReal 0 N.toNNReal) atTop
      (𝓝 (∫ z, gLLR N S u (u + z) ∂gaussianReal 0 N.toNNReal)) := by
    intro u
    refine tendsto_integral_of_dominated_convergence
      (fun z => (c₀ + K * (5 * u ^ 2 + 14)) + 3 * K * z ^ 2) (fun k => ?_)
      (integrable_const_add_mul_sq _ _ _) (fun k => ae_of_all _ fun z => hbd k u z)
      (ae_of_all _ fun z => ?_)
    · exact (measurable_gLLR_qRound N S k u u).aestronglyMeasurable
    · exact tendsto_gLLR_qRound N S u u z
  -- outer convergence
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (fun u =>
      ∫ z, gLLR N S (qRound k u) (qRound k (qRound k u + z)) ∂gaussianReal 0 N.toNNReal)
      (gaussianReal 0 v.toNNReal) := fun k =>
    aesm_comp_qRound k (fun a => ∫ z, gLLR N S a (qRound k (a + z)) ∂gaussianReal 0 N.toNNReal) _
  have hbd_out : ∀ (k : ℕ) (u : ℝ),
      ‖∫ z, gLLR N S (qRound k u) (qRound k (qRound k u + z)) ∂gaussianReal 0 N.toNNReal‖ ≤
        (c₀ + K * 14 + 3 * K * N) + 5 * K * u ^ 2 := by
    intro k u
    refine le_trans (norm_integral_le_of_norm_le (integrable_const_add_mul_sq _ _ _)
      (ae_of_all _ fun z => hbd k u z)) (le_of_eq ?_)
    rw [integral_const_add_mul_sq _ _ _ hN.le]
    ring
  have hlim := tendsto_integral_of_dominated_convergence
    (fun u => (c₀ + K * 14 + 3 * K * N) + 5 * K * u ^ 2) hmeas
    (integrable_const_add_mul_sq _ _ _) (fun k => ae_of_all _ fun u => hbd_out k u)
    (ae_of_all _ fun u => hconv_in u)
  have hval : ∫ u, ∫ z, gLLR N S u (u + z) ∂gaussianReal 0 N.toNNReal
      ∂gaussianReal 0 v.toNNReal = 1 / 2 * Real.log (S / N) := by
    simp_rw [hinner]
    rw [integral_const_add_mul_sq _ _ _ hv.le, hS_def]
    field_simp
    ring
  rw [hval] at hlim
  exact hlim

/-- The pointwise bound `e^{ℓ(x,y)} ≤ e^{c₀} E₁(u') E₂(u) E₂(z)` used for the second DV term. -/
lemma exp_gLLR_le {S : ℝ} (hN : 0 < N) (hNS : N < S) (k : ℕ) (u' u z : ℝ) :
    Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z))) ≤
      Real.exp (1 / 2 * Real.log (S / N)) *
        Real.exp (1 / (2 * (2 * S - N)) * (|u'| + 1) ^ 2) *
        Real.exp (1 / (2 * S) * (|u| + 1) ^ 2) * Real.exp (1 / (2 * S) * (|z| + 1) ^ 2) := by
  have hS : 0 < S := by linarith
  have h2 : 0 < 2 * S - N := by linarith
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr (le_trans (gLLR_le hN hNS _ _) ?_)
  have hx : qRound k u' ^ 2 ≤ (|u'| + 1) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_qRound_le k u') 2
  have hy := sq_le_shift_sq (abs_qRound_comp_le k u z)
  have e1 : qRound k u' ^ 2 / (2 * (2 * S - N)) ≤ 1 / (2 * (2 * S - N)) * (|u'| + 1) ^ 2 := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hx (one_div_pos.mpr (by linarith)).le
  have e2 : qRound k (qRound k u + z) ^ 2 / (4 * S) ≤
      1 / (2 * S) * (|u| + 1) ^ 2 + 1 / (2 * S) * (|z| + 1) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 / (2 * S) * (|u| + 1) ^ 2 + 1 / (2 * S) * (|z| + 1) ^ 2) * (4 * S) =
        2 * (|u| + 1) ^ 2 + 2 * (|z| + 1) ^ 2 := by field_simp; ring
    rw [this]; exact hy
  linarith

/-- **Key Gaussian identity**: `∫∫ e^{ℓ(u', u+z)} dN(0,N)(z) dN(0,v)(u) = 1` with `S = v + N`
    (the output law of `N(0,v) + N(0,N)` is `N(0,S)`, and `φ_S e^{ℓ(u',·)} = φ_{u',N}`). -/
lemma integral_integral_exp_gLLR (hv : 0 < v) (hN : 0 < N) (u' : ℝ) :
    ∫ u, ∫ z, Real.exp (gLLR N (v + N) u' (u + z)) ∂gaussianReal 0 N.toNNReal
      ∂gaussianReal 0 v.toNNReal = 1 := by
  set S := v + N with hS_def
  have hS : 0 < S := by linarith
  have hNS : N < S := by linarith
  have h2 : 0 < 2 * S - N := by linarith
  have hconv : gaussianReal 0 v.toNNReal ∗ gaussianReal 0 N.toNNReal =
      gaussianReal 0 S.toNNReal := by
    rw [gaussianReal_conv_gaussianReal, add_zero, hS_def, Real.toNNReal_add hv.le hN.le]
  have hint : Integrable (fun y => Real.exp (gLLR N S u' y)) (gaussianReal 0 S.toNNReal) := by
    refine ((integrable_exp_mul_sq_gaussianReal hS (c := 1 / (4 * S))
      (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith)).const_mul
      (Real.exp (1 / 2 * Real.log (S / N) + u' ^ 2 / (2 * (2 * S - N))))).mono' ?_ ?_
    · exact (Real.continuous_exp.comp ((continuous_gLLR N S).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    · refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      refine Real.exp_le_exp.mpr (le_trans (gLLR_le hN hNS u' y) (le_of_eq ?_))
      ring
  have hint' : Integrable (fun y => Real.exp (gLLR N S u' y))
      (gaussianReal 0 v.toNNReal ∗ gaussianReal 0 N.toNNReal) := by rw [hconv]; exact hint
  have h := integral_conv hint'
  rw [← h, hconv, integral_gaussianReal_eq_integral_smul
    (GaussianChannel.toNNReal_ne_zero_of_pos hS)]
  simp_rw [smul_eq_mul, pdf_mul_exp_gLLR hN hS]
  exact integral_gaussianPDFReal_eq_one _ (GaussianChannel.toNNReal_ne_zero_of_pos hN)

/-- **Limit of the second DV term**: `→ 1`. -/
theorem tendsto_dvB (hv : 0 < v) (hN : 0 < N) :
    Tendsto (fun k : ℕ => ∫ u', ∫ u, ∫ z,
        Real.exp (gLLR N (v + N) (qRound k u') (qRound k (qRound k u + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v.toNNReal ∂gaussianReal 0 v.toNNReal)
      atTop (𝓝 1) := by
  set S := v + N with hS_def
  have hS : 0 < S := by linarith
  have hNS : N < S := by linarith
  have h2 : 0 < 2 * S - N := by linarith
  set γv := gaussianReal 0 v.toNNReal with hγv
  set γN := gaussianReal 0 N.toNNReal with hγN
  set a₀ := Real.exp (1 / 2 * Real.log (S / N)) with ha₀
  set E1 : ℝ → ℝ := fun t => Real.exp (1 / (2 * (2 * S - N)) * (|t| + 1) ^ 2) with hE1
  set E2 : ℝ → ℝ := fun t => Real.exp (1 / (2 * S) * (|t| + 1) ^ 2) with hE2
  have hE1v : Integrable E1 γv := integrable_exp_shift_sq_gaussianReal hv
    (by rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith)
  have hE2v : Integrable E2 γv := integrable_exp_shift_sq_gaussianReal hv
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith)
  have hE2N : Integrable E2 γN := integrable_exp_shift_sq_gaussianReal hN
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith)
  set IN := ∫ z, E2 z ∂γN with hIN
  set Iv := ∫ u, E2 u ∂γv with hIv
  have hbd : ∀ (k : ℕ) (u' u z : ℝ),
      ‖Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z)))‖ ≤
        a₀ * E1 u' * E2 u * E2 z := by
    intro k u' u z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_gLLR_le hN hNS k u' u z
  -- level 1
  have hlev1 : ∀ u' u : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z))) ∂γN) atTop
      (𝓝 (∫ z, Real.exp (gLLR N S u' (u + z)) ∂γN)) := by
    intro u' u
    refine tendsto_integral_of_dominated_convergence (fun z => a₀ * E1 u' * E2 u * E2 z)
      (fun k => ?_) (hE2N.const_mul _) (fun k => ae_of_all _ fun z => hbd k u' u z)
      (ae_of_all _ fun z => ?_)
    · exact (Real.continuous_exp.measurable.comp
        (measurable_gLLR_qRound N S k u' u)).aestronglyMeasurable
    · exact tendsto_exp_gLLR_qRound N S u' u z
  -- level 2
  have hbd2 : ∀ (k : ℕ) (u' u : ℝ),
      ‖∫ z, Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z))) ∂γN‖ ≤
        a₀ * E1 u' * E2 u * IN := by
    intro k u' u
    refine le_trans (norm_integral_le_of_norm_le (hE2N.const_mul (a₀ * E1 u' * E2 u))
      (ae_of_all _ fun z => hbd k u' u z)) (le_of_eq ?_)
    rw [integral_const_mul]
  have hlev2 : ∀ u' : ℝ, Tendsto (fun k : ℕ =>
      ∫ u, ∫ z, Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z))) ∂γN ∂γv) atTop
      (𝓝 (∫ u, ∫ z, Real.exp (gLLR N S u' (u + z)) ∂γN ∂γv)) := by
    intro u'
    refine tendsto_integral_of_dominated_convergence (fun u => a₀ * E1 u' * E2 u * IN)
      (fun k => ?_) ((hE2v.const_mul _).mul_const _)
      (fun k => ae_of_all _ fun u => hbd2 k u' u) (ae_of_all _ fun u => ?_)
    · exact aesm_comp_qRound k
        (fun a => ∫ z, Real.exp (gLLR N S (qRound k u') (qRound k (a + z))) ∂γN) _
    · exact hlev1 u' u
  -- level 3
  have hbd3 : ∀ (k : ℕ) (u' : ℝ),
      ‖∫ u, ∫ z, Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z))) ∂γN ∂γv‖ ≤
        a₀ * E1 u' * Iv * IN := by
    intro k u'
    refine le_trans (norm_integral_le_of_norm_le ((hE2v.const_mul (a₀ * E1 u')).mul_const IN)
      (ae_of_all _ fun u => hbd2 k u' u)) (le_of_eq ?_)
    rw [integral_mul_const, integral_const_mul]
  have hmeas3 : ∀ k : ℕ, AEStronglyMeasurable (fun u' =>
      ∫ u, ∫ z, Real.exp (gLLR N S (qRound k u') (qRound k (qRound k u + z))) ∂γN ∂γv) γv :=
    fun k => aesm_comp_qRound k
      (fun a => ∫ u, ∫ z, Real.exp (gLLR N S a (qRound k (qRound k u + z))) ∂γN ∂γv) _
  have hlev3 := tendsto_integral_of_dominated_convergence (μ := γv)
    (fun u' => a₀ * E1 u' * Iv * IN) hmeas3
    (((hE1v.const_mul a₀).mul_const Iv).mul_const IN)
    (fun k => ae_of_all _ fun u' => hbd3 k u') (ae_of_all _ fun u' => hlev2 u')
  have hval : ∫ u', ∫ u, ∫ z, Real.exp (gLLR N S u' (u + z)) ∂γN ∂γv ∂γv = 1 := by
    simp_rw [hγv, hγN, hS_def, integral_integral_exp_gLLR hv hN]
    simp
  rw [hval] at hlev3
  exact hlev3

/-- The input power of the discretized Gaussian converges to `v`. -/
theorem tendsto_power (hv : 0 < v) :
    Tendsto (fun k : ℕ => ∫ u, qRound k u ^ 2 ∂gaussianReal 0 v.toNNReal) atTop (𝓝 v) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := gaussianReal 0 v.toNNReal)
    (F := fun k u => qRound k u ^ 2) (f := fun u => u ^ 2) (fun u => 2 + 2 * u ^ 2)
    (fun k => ((measurable_qRound k).pow_const 2).aestronglyMeasurable)
    (integrable_const_add_mul_sq _ _ _)
    (fun k => ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith [sq_le_two_sq_add_two (abs_qRound_le k u)])
    (ae_of_all _ fun u => (tendsto_qRound tendsto_const_nhds).pow 2)
  rwa [integral_sq_gaussianReal_zero, Real.coe_toNNReal _ hv.le] at hlim

end Limits

/-! ### 7. AWGN achievability and the capacity theorem -/

section Capacity

variable {P N : ℝ}

/-- For every `R < ½ log₂(1 + v/N)` and `P > v` some quantization level `k` gives a finite DMC
    with `I > R` and input power `< P`. -/
theorem exists_good_quantization {v : ℝ} (hv : 0 < v) (hN : 0 < N) {R : ℝ}
    (hR : R < awgnCapacityFormula v N) (hP : v < P) :
    ∃ k : ℕ, R < (gChan N k).mutualInfo (gIn v k) ∧
      ∑ i, (gIn v k).pmf i * qVal k i ^ 2 < P := by
  have hA := tendsto_dvA hv hN
  have hB := tendsto_dvB hv hN
  have hlim := hA.sub (hB.log one_ne_zero)
  rw [Real.log_one, sub_zero] at hlim
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hRlt : R * Real.log 2 < 1 / 2 * Real.log ((v + N) / N) := by
    have hN0 : N ≠ 0 := hN.ne'
    have h1 : 1 + v / N = (v + N) / N := by field_simp; ring
    unfold awgnCapacityFormula log2 at hR
    rw [h1] at hR
    have h3 := mul_lt_mul_of_pos_right hR hlog2
    have h2 : 1 / 2 * (Real.log ((v + N) / N) / Real.log 2) * Real.log 2 =
        1 / 2 * Real.log ((v + N) / N) := by field_simp
    linarith
  have hev1 := (tendsto_order.1 hlim).1 _ hRlt
  have hev2 := (tendsto_order.1 (tendsto_power hv)).2 _ hP
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  refine ⟨k, ?_, ?_⟩
  · have hdv := mutualInfo_ge_dv (gChan N k) (gIn v k)
      (fun x y => gLLR N (v + N) (qVal k x) (qVal k y))
    rw [dvA_eq v N k (gLLR N (v + N)), dvB_eq v N k (gLLR N (v + N))] at hdv
    have : R * Real.log 2 < (gChan N k).mutualInfo (gIn v k) * Real.log 2 := by linarith
    exact lt_of_mul_lt_mul_right this hlog2.le
  · rw [power_gIn_eq]; exact hk2

/-- **AWGN achievability** (Cover–Thomas Thm. 9.1.1, achievability; El Gamal–Kim Thm. 3.2):
    for `N > 0`, `P ≥ 0`, every rate `0 ≤ R < ½ log₂(1 + P/N)` is achievable. -/
theorem isAwgnAchievable_of_lt_capacity (hN : 0 < N) (hP : 0 ≤ P) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < awgnCapacityFormula P N) : IsAwgnAchievable P N R := by
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hR; simp [awgnCapacityFormula, log2] at hR; linarith
  have hcont : ContinuousAt (fun w => awgnCapacityFormula w N) P := by
    unfold awgnCapacityFormula log2
    have h1 : (1 + P / N) ≠ 0 := by positivity
    exact (((continuousAt_const.add (continuousAt_id.div_const N)).log h1).div_const _).const_mul _
  have hev : ∀ᶠ w in 𝓝[<] P, R < awgnCapacityFormula w N ∧ w ∈ Set.Ioo 0 P :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont.eventually (lt_mem_nhds hR))).and
      (Ioo_mem_nhdsLT hPpos)
  obtain ⟨w, hwR, hw0, hwP⟩ := hev.exists
  obtain ⟨k, hk1, hk2⟩ := exists_good_quantization hw0 hN hwR hwP
  exact isAwgnAchievable_of_quantDMC (qVal k) (qIdx k) (measurable_qIdx k) (gIn w k) hR0 hk1 hk2

/-- **Shannon's AWGN channel capacity theorem** (Cover–Thomas Thm. 9.1.1; El Gamal–Kim Thm. 3.2):
    for noise variance `N > 0` and power `P ≥ 0`, the operational capacity of the AWGN channel
    equals `½ log₂(1 + P/N)`. -/
theorem awgnOperationalCapacity_eq (hN : 0 < N) (hP : 0 ≤ P) :
    awgnOperationalCapacity P N = awgnCapacityFormula P N := by
  refine le_antisymm (GaussianChannel.awgnOperationalCapacity_le hN hP) ?_
  by_contra hlt
  push Not at hlt
  have h0 := GaussianChannel.awgnOperationalCapacity_nonneg hN hP
  set R := (awgnOperationalCapacity P N + awgnCapacityFormula P N) / 2 with hR
  have hRach := isAwgnAchievable_of_lt_capacity hN hP (R := R) (by rw [hR]; linarith)
    (by rw [hR]; linarith)
  have := GaussianChannel.le_awgnOperationalCapacity hN hP hRach
  rw [hR] at this
  linarith

/-- Characterization of achievable rates: for `R ≥ 0`, `R < ½ log₂(1 + P/N)` implies achievable,
    and achievable implies `R ≤ ½ log₂(1 + P/N)`. -/
theorem isAwgnAchievable_iff_of_ne (hN : 0 < N) (hP : 0 ≤ P) {R : ℝ}
    (hne : R ≠ awgnCapacityFormula P N) :
    IsAwgnAchievable P N R ↔ 0 ≤ R ∧ R < awgnCapacityFormula P N := by
  constructor
  · intro h
    exact ⟨h.1, lt_of_le_of_ne (GaussianChannel.isAwgnAchievable_le hN hP h) hne⟩
  · rintro ⟨h0, h⟩
    exact isAwgnAchievable_of_lt_capacity hN hP h0 h

end Capacity


end InfoTheory.Known.GaussianAchievability
