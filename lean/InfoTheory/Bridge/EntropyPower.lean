import InfoTheory.Bridge.ContinuousIT
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# De Bruijn's Identity, Stam's Inequality, Shannon's EPI & Bergmans's Gaussian BC Converse

Formalization of Cover & Thomas Theorems 17.7.1, 17.7.2, 17.8.1, and §15.6.2 (plus Cramér–Rao)
for 1D continuous probability densities (`InfoTheory.Density 1`), building on
`InfoTheory.Bridge.Gaussian` and `InfoTheory.Bridge.ContinuousIT`:

1. **Convolution & Mixture Densities**:
   - `convDensity`, `convDensity_comm`, `convDensity_assoc_of_bdd_right`,
     `convDensity_gaussian_eq_awgn`, `awgnOutputDensity_awgnOutputDensity`, `convDensity_awgn`,
     `hasFiniteSecondMoment_convDensity`
   - `mixDensity`, `mixDensity_awgnOutputDensity`
2. **Gaussian Smoothing & Fisher Information**:
   - `fisherInfo`, `fisherInfo_nonneg`, `fisherInfo_translate`, `fisherInfo_scale`,
     `fisherInfo_gaussian` (`J(N(0, v)) = 1 / v`)
   - `awgnOutputDensity_pdf_pos`, `hasDerivAt_awgnOutputDensity_pdf`,
     `hasDerivAt_deriv_awgnOutputDensity_pdf`, `awgnOutputDensity_heat_equation` (`∂_t f_t = ½ ∂_y² f_t`)
   - `fisherInfo_awgnOutput_le_inv` (`J(X + √t Z) ≤ 1 / t`)
   - `cramer_rao_inequality`, `cramer_rao_inv_le`, `cramer_rao_awgnOutput` (`1 / J(X) ≤ E[(X - μ)²]`)
3. **Stam's Fisher Information Inequality** (Cover & Thomas Thm. 17.7.2; Blachman 1965):
   - `stam_weighted_inequality` (`J(f * g) ≤ α² J(f) + β² J(g)` for `α + β = 1`)
   - `stam_inequality` (`1 / J(f) + 1 / J(g) ≤ 1 / J(f * g)`)
   - `stam_weighted_inequality_awgn`, `stam_inequality_awgn`
4. **De Bruijn's Identity** (Cover & Thomas Thm. 17.7.1):
   - `hasFiniteDiffEntropy_awgnOutputDensity`
   - `awgnDiffEntropy`, `de_bruijn_identity` (`d/dt h(X + √t Z) = ½ J(X + √t Z)`)
5. **Shannon's 1D Entropy Power Inequality** (Cover & Thomas Thm. 17.8.1):
   - `awgn_mutualInfo_nonneg`, `diffEntropy_awgnOutput_ge`
   - `tendsto_awgnDiffEntropy_sub_gaussian`, `diffEntropy_awgnOutput_tendsto_zero`
   - `entropyPower_add_ge_of_awgn`, `entropyPower_add_ge` (`N(X + Y) ≥ N(X) + N(Y)`)
   - `entropyPower_awgnOutput_ge`, `entropyPower_awgnOutput_add_ge`
6. **Bergmans's Scalar Gaussian Broadcast Channel Single-Letter Converse** (Cover & Thomas §15.6.2):
   - `gaussianBC_single_letter_converse`
-/

open scoped BigOperators NNReal Real Topology
open MeasureTheory ProbabilityTheory InfoTheory Filter

namespace InfoTheory.Bridge

/-! ### Private 1D, Shear Fubini, and Gaussian-Kernel Helpers -/

private lemma ep_fin1_eq_const (x : Fin 1 → ℝ) : x = fun _ => x 0 :=
  funext fun i => by rw [Fin.eq_zero i]

private lemma ep_integral_fin1 (h : (Fin 1 → ℝ) → ℝ) :
    ∫ x : Fin 1 → ℝ, h x = ∫ t : ℝ, h (fun _ => t) := by
  have hrew : h = fun x : Fin 1 → ℝ => h (fun _ => x 0) := by
    funext x; conv_lhs => rw [ep_fin1_eq_const x]
  conv_lhs => rw [hrew]
  exact integral_fin1_eq (fun t => h (fun _ => t))

private lemma ep_integrable_fin1_iff (h : (Fin 1 → ℝ) → ℝ) :
    Integrable h volume ↔ Integrable (fun t : ℝ => h (fun _ => t)) volume := by
  have hrew : h = fun x : Fin 1 → ℝ => h (fun _ => x 0) := by
    funext x; conv_lhs => rw [ep_fin1_eq_const x]
  conv_lhs => rw [hrew]
  exact integrable_fin1_iff (fun t => h (fun _ => t))

private lemma ep_pdf1_integrable (f : Density 1) :
    Integrable (fun t : ℝ => f.pdf (fun _ => t)) volume :=
  (ep_integrable_fin1_iff f.pdf).mp f.integrable

private lemma ep_pdf1_integral_one (f : Density 1) :
    ∫ t : ℝ, f.pdf (fun _ => t) = 1 := by
  rw [← ep_integral_fin1 f.pdf]
  exact f.integral_one

private lemma ep_secondMoment_integrable (f : Density 1) (hm2 : HasFiniteSecondMoment f) :
    Integrable (fun t : ℝ => t ^ 2 * f.pdf (fun _ => t)) volume := by
  have hm2' : Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x) volume := by
    simpa [HasFiniteSecondMoment, Fin.sum_univ_one] using hm2
  exact (ep_integrable_fin1_iff (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x)).mp hm2'

private lemma ep_density_ext {f g : Density 1}
    (h : ∀ t : ℝ, f.pdf (fun _ => t) = g.pdf (fun _ => t)) : f = g := by
  have hpdf : f.pdf = g.pdf := by
    funext x
    rw [ep_fin1_eq_const x]
    exact h (x 0)
  cases f; cases g
  simp only at hpdf
  subst hpdf
  rfl

private lemma ep_integrable_finset_sum {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {g : ι → α → ℝ} (hg : ∀ i ∈ s, Integrable (g i) μ) :
    Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

private lemma ep_integral_finset_sum {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {g : ι → α → ℝ} (hg : ∀ i ∈ s, Integrable (g i) μ) :
    ∫ x, (∑ i ∈ s, g i x) ∂μ = ∑ i ∈ s, ∫ x, g i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [integral_add (hg a (Finset.mem_insert_self a s))
      (ep_integrable_finset_sum s fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- Shear measurable equivalence `(x, y) ↦ (x - y, y)` preserving `volume.prod volume`. -/
private def ep_shearEquiv : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun p := (p.1 - p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd

private lemma ep_measurePreserving_shear :
    MeasurePreserving ep_shearEquiv ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  refine ⟨ep_shearEquiv.measurable, ?_⟩
  symm
  refine Measure.prod_eq (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) fun s t hs ht => ?_
  rw [Measure.map_apply ep_shearEquiv.measurable (hs.prod ht),
    Measure.prod_apply_symm (ep_shearEquiv.measurable (hs.prod ht))]
  have hsec : ∀ y : ℝ, (volume : Measure ℝ) ((fun x : ℝ => (x, y)) ⁻¹' (ep_shearEquiv ⁻¹' (s ×ˢ t))) =
      t.indicator (fun _ => (volume : Measure ℝ) s) y := by
    intro y
    by_cases hy : y ∈ t
    · simp only [Set.indicator_of_mem hy]
      have hset : ((fun x : ℝ => (x, y)) ⁻¹' (ep_shearEquiv ⁻¹' (s ×ˢ t))) = (fun x : ℝ => x - y) ⁻¹' s := by
        ext x; simp [ep_shearEquiv, hy]
      rw [hset]
      exact (measurePreserving_sub_right (volume : Measure ℝ) y).measure_preimage hs.nullMeasurableSet
    · simp only [Set.indicator_of_notMem hy]
      have hset : ((fun x : ℝ => (x, y)) ⁻¹' (ep_shearEquiv ⁻¹' (s ×ˢ t))) = ∅ := by
        ext x; simp [ep_shearEquiv, hy]
      rw [hset, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator ht, lintegral_const, Measure.restrict_apply_univ]

private lemma ep_integrable_prod_shear {a b : ℝ → ℝ}
    (ha : Integrable a volume) (hb : Integrable b volume) :
    Integrable (fun p : ℝ × ℝ => a p.2 * b (p.1 - p.2)) (volume.prod volume) := by
  have hprod : Integrable (fun q : ℝ × ℝ => b q.1 * a q.2) (volume.prod volume) := hb.mul_prod ha
  have hcomp := (ep_measurePreserving_shear.integrable_comp_emb
    ep_shearEquiv.measurableEmbedding).mpr hprod
  refine hcomp.congr (ae_of_all _ fun p => ?_)
  change b (p.1 - p.2) * a p.2 = a p.2 * b (p.1 - p.2)
  ring

private lemma ep_integral_prod_shear {a b : ℝ → ℝ}
    (_ha : Integrable a volume) (_hb : Integrable b volume) :
    ∫ p : ℝ × ℝ, a p.2 * b (p.1 - p.2) ∂(volume.prod volume) =
      (∫ x : ℝ, a x) * (∫ u : ℝ, b u) := by
  have hrew : (fun p : ℝ × ℝ => a p.2 * b (p.1 - p.2)) =
      fun p : ℝ × ℝ => (fun q : ℝ × ℝ => b q.1 * a q.2) (ep_shearEquiv p) := by
    funext p
    change a p.2 * b (p.1 - p.2) = b (p.1 - p.2) * a p.2
    ring
  rw [hrew, ep_measurePreserving_shear.integral_comp' (fun q : ℝ × ℝ => b q.1 * a q.2),
    integral_prod_mul, mul_comm]

private lemma ep_integrable_conv_fun {a b : ℝ → ℝ}
    (ha : Integrable a volume) (hb : Integrable b volume) :
    Integrable (fun z : ℝ => ∫ x : ℝ, a x * b (z - x)) volume :=
  (ep_integrable_prod_shear ha hb).integral_prod_left

private lemma ep_integral_conv_fun {a b : ℝ → ℝ}
    (ha : Integrable a volume) (hb : Integrable b volume) :
    ∫ z : ℝ, (∫ x : ℝ, a x * b (z - x)) = (∫ x : ℝ, a x) * (∫ u : ℝ, b u) := by
  rw [← integral_prod _ (ep_integrable_prod_shear ha hb)]
  exact ep_integral_prod_shear ha hb

private lemma ep_conv_fun_comm (a b : ℝ → ℝ) (z : ℝ) :
    ∫ x : ℝ, a x * b (z - x) = ∫ y : ℝ, b y * a (z - y) := by
  have h := integral_sub_left_eq_self (fun y : ℝ => b y * a (z - y)) volume z
  refine Eq.trans ?_ h
  congr 1
  funext x
  simp [mul_comm]

private lemma ep_continuous_gaussianPdf1D (v : ℝ) : Continuous (gaussianPdf1D v) := by
  unfold gaussianPdf1D
  fun_prop

private lemma ep_integrable_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    Integrable (gaussianPdf1D v) volume := by
  have heq : gaussianPdf1D v = gaussianPDFReal 0 ⟨v, hv.le⟩ :=
    funext (gaussianPdf1D_eq_gaussianPDFReal hv.le)
  rw [heq]
  exact integrable_gaussianPDFReal 0 ⟨v, hv.le⟩

private lemma ep_integral_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    ∫ t : ℝ, gaussianPdf1D v t = 1 := by
  have heq : gaussianPdf1D v = gaussianPDFReal 0 ⟨v, hv.le⟩ :=
    funext (gaussianPdf1D_eq_gaussianPDFReal hv.le)
  rw [heq]
  exact integral_gaussianPDFReal_eq_one 0 (NNReal.coe_ne_zero.mp (ne_of_gt hv))

private lemma ep_gaussianPdf1D_le_const {v : ℝ} (hv : 0 < v) (u : ℝ) :
    gaussianPdf1D v u ≤ 1 / Real.sqrt (2 * Real.pi * v) := by
  unfold gaussianPdf1D
  have h1 : Real.exp (-(u ^ 2) / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) (by positivity)
  have hc : 0 ≤ 1 / Real.sqrt (2 * Real.pi * v) := by positivity
  nlinarith

private lemma ep_mul_exp_neg_le_one {w : ℝ} (_hw : 0 ≤ w) :
    w * Real.exp (-w) ≤ 1 := by
  have h1 : w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
  have h2 : 0 < Real.exp w := Real.exp_pos w
  rw [Real.exp_neg]
  calc w * (Real.exp w)⁻¹ = w / Real.exp w := by rw [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one h2).mpr h1

private lemma ep_sq_mul_exp_neg_le_four {w : ℝ} (hw : 0 ≤ w) :
    w ^ 2 * Real.exp (-w) ≤ 4 := by
  have h1 : (w / 2) * Real.exp (-(w / 2)) ≤ 1 := ep_mul_exp_neg_le_one (by linarith)
  have h0 : 0 ≤ (w / 2) * Real.exp (-(w / 2)) := by positivity
  have hsq : ((w / 2) * Real.exp (-(w / 2))) ^ 2 ≤ 1 ^ 2 := by nlinarith
  have heq : ((w / 2) * Real.exp (-(w / 2))) ^ 2 = (w ^ 2 / 4) * Real.exp (-w) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  rw [heq] at hsq
  linarith

private lemma ep_abs_mul_exp_neg_sq_le {v : ℝ} (hv : 0 < v) (u : ℝ) :
    |u| * Real.exp (-(u ^ 2) / (2 * v)) ≤ Real.sqrt v := by
  have h1 : (u ^ 2 / v) * Real.exp (-(u ^ 2 / v)) ≤ 1 :=
    ep_mul_exp_neg_le_one (by positivity)
  have hsq : (|u| * Real.exp (-(u ^ 2) / (2 * v))) ^ 2 ≤ v := by
    have heq : (|u| * Real.exp (-(u ^ 2) / (2 * v))) ^ 2 =
        v * ((u ^ 2 / v) * Real.exp (-(u ^ 2 / v))) := by
      rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
      have hv0 : v ≠ 0 := ne_of_gt hv
      have harg : (2 : ℕ) * (-(u ^ 2) / (2 * v)) = -(u ^ 2 / v) := by
        push_cast; field_simp [hv0]
      rw [harg]
      field_simp [hv0]
    rw [heq]
    nlinarith
  exact Real.le_sqrt_of_sq_le hsq

private lemma ep_sq_mul_exp_neg_sq_le {v : ℝ} (hv : 0 < v) (u : ℝ) :
    u ^ 2 * Real.exp (-(u ^ 2) / (2 * v)) ≤ 2 * v := by
  have h1 : (u ^ 2 / (2 * v)) * Real.exp (-(u ^ 2 / (2 * v))) ≤ 1 :=
    ep_mul_exp_neg_le_one (by positivity)
  have h2 : -(u ^ 2) / (2 * v) = -(u ^ 2 / (2 * v)) := by ring
  rw [h2]
  have hv0 : 2 * v ≠ 0 := by positivity
  calc u ^ 2 * Real.exp (-(u ^ 2 / (2 * v)))
      = (2 * v) * ((u ^ 2 / (2 * v)) * Real.exp (-(u ^ 2 / (2 * v)))) := by field_simp [hv0]
    _ ≤ (2 * v) * 1 := by nlinarith
    _ = 2 * v := mul_one _

private lemma ep_pow4_mul_exp_neg_sq_le {v : ℝ} (hv : 0 < v) (u : ℝ) :
    u ^ 4 * Real.exp (-(u ^ 2) / (2 * v)) ≤ 16 * v ^ 2 := by
  have h1 : (u ^ 2 / (2 * v)) ^ 2 * Real.exp (-(u ^ 2 / (2 * v))) ≤ 4 :=
    ep_sq_mul_exp_neg_le_four (by positivity)
  have h2 : -(u ^ 2) / (2 * v) = -(u ^ 2 / (2 * v)) := by ring
  rw [h2]
  have hv0 : 2 * v ≠ 0 := by positivity
  calc u ^ 4 * Real.exp (-(u ^ 2 / (2 * v)))
      = (4 * v ^ 2) * ((u ^ 2 / (2 * v)) ^ 2 * Real.exp (-(u ^ 2 / (2 * v)))) := by
          field_simp [hv0]; ring
    _ ≤ (4 * v ^ 2) * 4 := by nlinarith [sq_nonneg v]
    _ = 16 * v ^ 2 := by ring

private lemma ep_integrable_abs_mul_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    Integrable (fun u : ℝ => |u| * gaussianPdf1D v u) volume := by
  have hdom : Integrable (fun u : ℝ => gaussianPdf1D v u + u ^ 2 * gaussianPdf1D v u) volume :=
    (ep_integrable_gaussianPdf1D hv).add (integrable_sq_mul_gaussianPdf1D hv)
  refine hdom.mono' ((continuous_abs.mul (ep_continuous_gaussianPdf1D v)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  have hg : 0 ≤ gaussianPdf1D v u := gaussianPdf1D_nonneg hv.le u
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg u) hg)]
  have hle : |u| ≤ 1 + u ^ 2 := by
    have hsq : 0 ≤ (|u| - 1) ^ 2 := sq_nonneg _
    have habs : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith
  nlinarith

private lemma ep_integrable_pow4_mul_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    Integrable (fun u : ℝ => u ^ 4 * gaussianPdf1D v u) volume := by
  have h2v : 0 < 2 * v := by positivity
  let C : ℝ := 64 * v ^ 2 * Real.sqrt 2
  have hdom : Integrable (fun u : ℝ => C * gaussianPdf1D (2 * v) u) volume :=
    (ep_integrable_gaussianPdf1D h2v).const_mul C
  refine hdom.mono' (((continuous_pow 4).mul (ep_continuous_gaussianPdf1D v)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  have hg : 0 ≤ gaussianPdf1D v u := gaussianPdf1D_nonneg hv.le u
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hg)]
  unfold gaussianPdf1D
  have hsplit : Real.exp (-(u ^ 2) / (2 * v)) =
      Real.exp (-(u ^ 2) / (2 * (2 * v))) * Real.exp (-(u ^ 2) / (2 * (2 * v))) := by
    rw [← Real.exp_add]
    congr 1; ring
  have hpow4 : u ^ 4 * Real.exp (-(u ^ 2) / (2 * (2 * v))) ≤ 16 * (2 * v) ^ 2 :=
    ep_pow4_mul_exp_neg_sq_le h2v u
  have hsqrt : Real.sqrt (2 * Real.pi * (2 * v)) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * v) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  have hs1 : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hexp_nn : 0 ≤ Real.exp (-(u ^ 2) / (2 * (2 * v))) := (Real.exp_pos _).le
  rw [hsplit, hsqrt]
  have hC : C * (1 / (Real.sqrt 2 * Real.sqrt (2 * Real.pi * v)) *
      Real.exp (-(u ^ 2) / (2 * (2 * v)))) =
      (1 / Real.sqrt (2 * Real.pi * v)) * (64 * v ^ 2 * Real.exp (-(u ^ 2) / (2 * (2 * v)))) := by
    dsimp only [C]
    field_simp [ne_of_gt hs1, ne_of_gt hs2]
  rw [hC]
  have hbound : u ^ 4 * (1 / Real.sqrt (2 * Real.pi * v) *
      (Real.exp (-(u ^ 2) / (2 * (2 * v))) * Real.exp (-(u ^ 2) / (2 * (2 * v))))) =
      (1 / Real.sqrt (2 * Real.pi * v)) *
        ((u ^ 4 * Real.exp (-(u ^ 2) / (2 * (2 * v)))) * Real.exp (-(u ^ 2) / (2 * (2 * v)))) := by
    ring
  rw [hbound]
  have h64 : 16 * (2 * v) ^ 2 = 64 * v ^ 2 := by ring
  rw [h64] at hpow4
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow4 hexp_nn) (by positivity)

private lemma ep_hasDerivAt_gaussianPdf1D {v : ℝ} (hv : 0 < v) (u : ℝ) :
    HasDerivAt (gaussianPdf1D v) (-(u / v) * gaussianPdf1D v u) u := by
  unfold gaussianPdf1D
  have hinner : HasDerivAt (fun x : ℝ => -(x ^ 2) / (2 * v)) (-(u / v)) u := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h2 := h1.neg.div_const (2 * v)
    have heq : -(2 * u) / (2 * v) = -(u / v) := by
      have hv0 : v ≠ 0 := ne_of_gt hv
      field_simp [hv0]
    rwa [heq] at h2
  have hexp := hinner.exp.const_mul (1 / Real.sqrt (2 * Real.pi * v))
  refine hexp.congr_deriv ?_
  ring

private lemma ep_hasDerivAt_deriv_gaussianPdf1D {v : ℝ} (hv : 0 < v) (u : ℝ) :
    HasDerivAt (fun x : ℝ => -(x / v) * gaussianPdf1D v x)
      ((u ^ 2 / v ^ 2 - 1 / v) * gaussianPdf1D v u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -(x / v)) (-(1 / v)) u := by
    have h := (hasDerivAt_id u).div_const v
    have hneg : HasDerivAt (fun x : ℝ => -(x / v)) (-(1 / v)) u := h.neg
    exact hneg
  have h2 := ep_hasDerivAt_gaussianPdf1D hv u
  have hprod := h1.mul h2
  refine hprod.congr_deriv ?_
  ring

private lemma ep_hasDerivAt_gaussianPdf1D_var {v : ℝ} (hv : 0 < v) (u : ℝ) :
    HasDerivAt (fun t : ℝ => gaussianPdf1D t u)
      ((1 / 2 : ℝ) * ((u ^ 2 / v ^ 2 - 1 / v) * gaussianPdf1D v u)) v := by
  unfold gaussianPdf1D
  have h2piv : 0 < 2 * Real.pi * v := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi * v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2piv)
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) v := by
    simpa using (hasDerivAt_id v).const_mul (2 * Real.pi)
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (2 * Real.pi * t))
      (2 * Real.pi / (2 * Real.sqrt (2 * Real.pi * v))) v := by
    have hs := hlin.sqrt (ne_of_gt h2piv)
    refine hs.congr_deriv ?_
    ring
  have hpref : HasDerivAt (fun t : ℝ => 1 / Real.sqrt (2 * Real.pi * t))
      (-(1 / (2 * v)) * (1 / Real.sqrt (2 * Real.pi * v))) v := by
    have hi := (hasDerivAt_const v (1 : ℝ)).div hsqrt hsqrt_ne
    refine hi.congr_deriv ?_
    have hsq : Real.sqrt (2 * Real.pi * v) ^ 2 = 2 * Real.pi * v := Real.sq_sqrt h2piv.le
    field_simp [hsqrt_ne, hv0]
    rw [hsq]
    ring
  have hexp_arg : HasDerivAt (fun t : ℝ => -(u ^ 2) / (2 * t)) (u ^ 2 / (2 * v ^ 2)) v := by
    have hd : HasDerivAt (fun t : ℝ => 2 * t) 2 v := by
      simpa using (hasDerivAt_id v).const_mul (2 : ℝ)
    have hq := (hasDerivAt_const v (-(u ^ 2))).div hd (by positivity)
    refine hq.congr_deriv ?_
    field_simp [hv0]
    ring
  have hexp := hexp_arg.exp
  have hprod := hpref.mul hexp
  refine hprod.congr_deriv ?_
  field_simp [hv0]
  ring

private lemma ep_abs_deriv_gaussianPdf1D_le {v : ℝ} (hv : 0 < v) (u : ℝ) :
    |-(u / v) * gaussianPdf1D v u| ≤ 1 / (Real.sqrt (2 * Real.pi * v) * Real.sqrt v) := by
  unfold gaussianPdf1D
  have h1 : |u| * Real.exp (-(u ^ 2) / (2 * v)) ≤ Real.sqrt v := ep_abs_mul_exp_neg_sq_le hv u
  have hs0 : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
  have hrv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  rw [abs_mul, abs_neg, abs_div, abs_of_pos hv, abs_mul,
    abs_of_pos (by positivity : 0 < 1 / Real.sqrt (2 * Real.pi * v)),
    abs_of_pos (Real.exp_pos _)]
  have hlhs : |u| / v * (1 / Real.sqrt (2 * Real.pi * v) * Real.exp (-(u ^ 2) / (2 * v))) =
      (|u| * Real.exp (-(u ^ 2) / (2 * v))) / (v * Real.sqrt (2 * Real.pi * v)) := by ring
  rw [hlhs]
  calc (|u| * Real.exp (-(u ^ 2) / (2 * v))) / (v * Real.sqrt (2 * Real.pi * v))
      ≤ Real.sqrt v / (v * Real.sqrt (2 * Real.pi * v)) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = 1 / (Real.sqrt (2 * Real.pi * v) * Real.sqrt v) := by
        have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
        field_simp [ne_of_gt hs0, ne_of_gt hrv, ne_of_gt hv]
        nlinarith [hsq]

private lemma ep_abs_deriv2_gaussianPdf1D_le {v : ℝ} (hv : 0 < v) (u : ℝ) :
    |(u ^ 2 / v ^ 2 - 1 / v) * gaussianPdf1D v u| ≤ 3 / (v * Real.sqrt (2 * Real.pi * v)) := by
  have hg_pos : 0 < gaussianPdf1D v u := gaussianPdf1D_pos hv u
  rw [abs_mul, abs_of_pos hg_pos]
  have htri : |u ^ 2 / v ^ 2 - 1 / v| ≤ u ^ 2 / v ^ 2 + 1 / v := by
    calc |u ^ 2 / v ^ 2 - 1 / v| ≤ |u ^ 2 / v ^ 2| + |1 / v| := abs_sub _ _
      _ = u ^ 2 / v ^ 2 + 1 / v := by
          rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  have hterm1 : (u ^ 2 / v ^ 2) * gaussianPdf1D v u ≤ 2 / (v * Real.sqrt (2 * Real.pi * v)) := by
    unfold gaussianPdf1D
    have hsq := ep_sq_mul_exp_neg_sq_le hv u
    have hv0 : v ≠ 0 := ne_of_gt hv
    have hs0 : Real.sqrt (2 * Real.pi * v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    calc (u ^ 2 / v ^ 2) * (1 / Real.sqrt (2 * Real.pi * v) * Real.exp (-(u ^ 2) / (2 * v)))
        = (u ^ 2 * Real.exp (-(u ^ 2) / (2 * v))) / (v ^ 2 * Real.sqrt (2 * Real.pi * v)) := by ring
      _ ≤ (2 * v) / (v ^ 2 * Real.sqrt (2 * Real.pi * v)) :=
          div_le_div_of_nonneg_right hsq (by positivity)
      _ = 2 / (v * Real.sqrt (2 * Real.pi * v)) := by field_simp [hv0, hs0]
  have hterm2 : (1 / v) * gaussianPdf1D v u ≤ 1 / (v * Real.sqrt (2 * Real.pi * v)) := by
    have hle := ep_gaussianPdf1D_le_const hv u
    have hv0 : v ≠ 0 := ne_of_gt hv
    have hs0 : Real.sqrt (2 * Real.pi * v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    calc (1 / v) * gaussianPdf1D v u ≤ (1 / v) * (1 / Real.sqrt (2 * Real.pi * v)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 / (v * Real.sqrt (2 * Real.pi * v)) := by field_simp [hv0, hs0]
  calc |u ^ 2 / v ^ 2 - 1 / v| * gaussianPdf1D v u
      ≤ (u ^ 2 / v ^ 2 + 1 / v) * gaussianPdf1D v u :=
        mul_le_mul_of_nonneg_right htri hg_pos.le
    _ = (u ^ 2 / v ^ 2) * gaussianPdf1D v u + (1 / v) * gaussianPdf1D v u := by ring
    _ ≤ 2 / (v * Real.sqrt (2 * Real.pi * v)) + 1 / (v * Real.sqrt (2 * Real.pi * v)) :=
        add_le_add hterm1 hterm2
    _ = 3 / (v * Real.sqrt (2 * Real.pi * v)) := by ring

/-! ### Section 0: Convolution and Mixture Densities -/

private lemma ep_densityConv_eq_1d (f g : Density 1) (z : ℝ) :
    densityConv f g (fun _ => z) = ∫ x : ℝ, f.pdf (fun _ => x) * g.pdf (fun _ => z - x) := by
  unfold densityConv
  exact ep_integral_fin1 _

/-- Convolution of two 1D probability densities `f` and `g`, representing the density of
    `X + Y` for independent `X ~ f` and `Y ~ g`. -/
noncomputable def convDensity (f g : Density 1) : Density 1 where
  pdf := densityConv f g
  nonneg := fun x =>
    integral_nonneg fun y => mul_nonneg (f.nonneg y) (g.nonneg (x - y))
  integrable := by
    rw [ep_integrable_fin1_iff (densityConv f g)]
    have hrew : (fun z : ℝ => densityConv f g (fun _ => z)) =
        fun z : ℝ => ∫ x : ℝ, f.pdf (fun _ => x) * g.pdf (fun _ => z - x) :=
      funext (ep_densityConv_eq_1d f g)
    rw [hrew]
    exact ep_integrable_conv_fun (a := fun x => f.pdf (fun _ => x)) (b := fun u => g.pdf (fun _ => u))
      (ep_pdf1_integrable f) (ep_pdf1_integrable g)
  integral_one := by
    rw [ep_integral_fin1 (densityConv f g)]
    have hrew : (fun z : ℝ => densityConv f g (fun _ => z)) =
        fun z : ℝ => ∫ x : ℝ, f.pdf (fun _ => x) * g.pdf (fun _ => z - x) :=
      funext (ep_densityConv_eq_1d f g)
    rw [hrew, ep_integral_conv_fun (a := fun x => f.pdf (fun _ => x)) (b := fun u => g.pdf (fun _ => u))
      (ep_pdf1_integrable f) (ep_pdf1_integrable g),
      ep_pdf1_integral_one f, ep_pdf1_integral_one g, mul_one]

lemma convDensity_pdf_eq (f g : Density 1) (z : ℝ) :
    (convDensity f g).pdf (fun _ => z) =
      ∫ x : ℝ, f.pdf (fun _ => x) * g.pdf (fun _ => z - x) :=
  ep_densityConv_eq_1d f g z

/-- Commutativity of 1D density convolution: `f * g = g * f`. -/
theorem convDensity_comm (f g : Density 1) : convDensity f g = convDensity g f := by
  refine ep_density_ext fun z => ?_
  rw [convDensity_pdf_eq, convDensity_pdf_eq]
  exact ep_conv_fun_comm (fun x => f.pdf (fun _ => x)) (fun x => g.pdf (fun _ => x)) z

/-- Associativity of 1D density convolution when the rightmost density is bounded:
    `(f * g) * h = f * (g * h)`. -/
theorem convDensity_assoc_of_bdd_right (f g h : Density 1)
    {M : ℝ} (hM : ∀ u : ℝ, h.pdf (fun _ => u) ≤ M) :
    convDensity (convDensity f g) h = convDensity f (convDensity g h) := by
  refine ep_density_ext fun z => ?_
  rw [convDensity_pdf_eq, convDensity_pdf_eq]
  simp_rw [convDensity_pdf_eq]
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  let g1 : ℝ → ℝ := fun x => g.pdf (fun _ => x)
  let h1 : ℝ → ℝ := fun x => h.pdf (fun _ => x)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hg1 : Integrable g1 volume := ep_pdf1_integrable g
  have hh1 : Integrable h1 volume := ep_pdf1_integrable h
  have h_lhs_pull : (fun w : ℝ => (∫ x : ℝ, f1 x * g1 (w - x)) * h1 (z - w)) =
      fun w : ℝ => ∫ x : ℝ, f1 x * (g1 (w - x) * h1 (z - w)) := by
    funext w
    rw [← integral_mul_const]
    congr 1; funext x; ring
  have h_rhs_pull : (fun x : ℝ => f1 x * ∫ u : ℝ, g1 u * h1 (z - x - u)) =
      fun x : ℝ => ∫ w : ℝ, f1 x * (g1 (w - x) * h1 (z - w)) := by
    funext x
    rw [← integral_const_mul]
    have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun u : ℝ => f1 x * (g1 u * h1 (z - x - u))) x
    refine hshift.symm.trans ?_
    congr 1; funext w
    have hsub : z - x - (w - x) = z - w := by ring
    rw [hsub]
  change ∫ w : ℝ, (∫ x : ℝ, f1 x * g1 (w - x)) * h1 (z - w) =
    ∫ x : ℝ, f1 x * ∫ u : ℝ, g1 u * h1 (z - x - u)
  rw [h_lhs_pull, h_rhs_pull]
  have hdom : Integrable (fun p : ℝ × ℝ => M * (f1 p.2 * g1 (p.1 - p.2))) (volume.prod volume) :=
    (ep_integrable_prod_shear hf1 hg1).const_mul M
  have hmeas_fg : AEStronglyMeasurable (fun p : ℝ × ℝ => f1 p.2 * g1 (p.1 - p.2))
      (volume.prod volume) := (ep_integrable_prod_shear hf1 hg1).aestronglyMeasurable
  have hmeas_h : AEStronglyMeasurable (fun p : ℝ × ℝ => h1 (z - p.1)) (volume.prod volume) :=
    (hh1.comp_sub_left z).aestronglyMeasurable.comp_fst
  have hjoint : Integrable (fun p : ℝ × ℝ => f1 p.2 * (g1 (p.1 - p.2) * h1 (z - p.1)))
      (volume.prod volume) := by
    refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact (hmeas_fg.mul hmeas_h).congr (ae_of_all _ fun p => by dsimp only [Pi.mul_apply]; ring)
    · have hnn1 : 0 ≤ f1 p.2 := f.nonneg _
      have hnn2 : 0 ≤ g1 (p.1 - p.2) := g.nonneg _
      have hnn3 : 0 ≤ h1 (z - p.1) := h.nonneg _
      rw [Real.norm_of_nonneg (mul_nonneg hnn1 (mul_nonneg hnn2 hnn3))]
      have hle := hM (z - p.1)
      have hfg_nn : 0 ≤ f1 p.2 * g1 (p.1 - p.2) := mul_nonneg hnn1 hnn2
      calc f1 p.2 * (g1 (p.1 - p.2) * h1 (z - p.1))
          = (f1 p.2 * g1 (p.1 - p.2)) * h1 (z - p.1) := by ring
        _ ≤ (f1 p.2 * g1 (p.1 - p.2)) * M := mul_le_mul_of_nonneg_left hle hfg_nn
        _ = M * (f1 p.2 * g1 (p.1 - p.2)) := mul_comm _ _
  exact integral_integral_swap hjoint

/-- `convDensity f (gaussianDensity1D t ht)` equals `awgnOutputDensity f t ht`. -/
lemma convDensity_gaussian_eq_awgn (f : Density 1) {t : ℝ} (ht : 0 < t) :
    convDensity f (gaussianDensity1D t ht) = awgnOutputDensity f t ht :=
  ep_density_ext fun _ => rfl

/-- Semigroup property of AWGN Gaussian smoothing:
    `(X + √a Z₁) + √b Z₂` has the same density as `X + √(a + b) Z`. -/
theorem awgnOutputDensity_awgnOutputDensity (f : Density 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    awgnOutputDensity (awgnOutputDensity f a ha) b hb =
      awgnOutputDensity f (a + b) (add_pos ha hb) := by
  rw [← convDensity_gaussian_eq_awgn, ← convDensity_gaussian_eq_awgn,
    convDensity_assoc_of_bdd_right f (gaussianDensity1D a ha) (gaussianDensity1D b hb)
      (fun u => ep_gaussianPdf1D_le_const hb u),
    convDensity_gaussian_eq_awgn, awgnOutputDensity_gaussian ha hb,
    convDensity_gaussian_eq_awgn]

/-- Convolution of two AWGN-smoothed densities:
    `(f * φ_a) * (g * φ_b) = (f * g) * φ_{a + b}`. -/
theorem convDensity_awgn (f g : Density 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb) =
      awgnOutputDensity (convDensity f g) (a + b) (add_pos ha hb) := by
  have hb_bdd : ∀ u : ℝ, (gaussianDensity1D b hb).pdf (fun _ => u) ≤ 1 / Real.sqrt (2 * Real.pi * b) :=
    fun u => ep_gaussianPdf1D_le_const hb u
  have ha_bdd : ∀ u : ℝ, (gaussianDensity1D a ha).pdf (fun _ => u) ≤ 1 / Real.sqrt (2 * Real.pi * a) :=
    fun u => ep_gaussianPdf1D_le_const ha u
  calc convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)
      = convDensity (awgnOutputDensity f a ha) (convDensity g (gaussianDensity1D b hb)) := by
          rw [convDensity_gaussian_eq_awgn]
    _ = convDensity (convDensity (awgnOutputDensity f a ha) g) (gaussianDensity1D b hb) :=
          (convDensity_assoc_of_bdd_right _ _ _ hb_bdd).symm
    _ = convDensity (convDensity g (convDensity f (gaussianDensity1D a ha))) (gaussianDensity1D b hb) := by
          rw [convDensity_comm (awgnOutputDensity f a ha) g, ← convDensity_gaussian_eq_awgn f ha]
    _ = convDensity (convDensity (convDensity g f) (gaussianDensity1D a ha)) (gaussianDensity1D b hb) := by
          rw [(convDensity_assoc_of_bdd_right g f (gaussianDensity1D a ha) ha_bdd).symm]
    _ = convDensity (convDensity (convDensity f g) (gaussianDensity1D a ha)) (gaussianDensity1D b hb) := by
          rw [convDensity_comm g f]
    _ = awgnOutputDensity (awgnOutputDensity (convDensity f g) a ha) b hb := by
          rw [convDensity_gaussian_eq_awgn, convDensity_gaussian_eq_awgn]
    _ = awgnOutputDensity (convDensity f g) (a + b) (add_pos ha hb) :=
          awgnOutputDensity_awgnOutputDensity (convDensity f g) ha hb

/-- Convolution of two finite-second-moment densities has finite second moment. -/
lemma hasFiniteSecondMoment_convDensity (f g : Density 1)
    (hf : HasFiniteSecondMoment f) (hg : HasFiniteSecondMoment g) :
    HasFiniteSecondMoment (convDensity f g) := by
  unfold HasFiniteSecondMoment
  simp only [Fin.sum_univ_one]
  rw [ep_integrable_fin1_iff]
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  let g1 : ℝ → ℝ := fun x => g.pdf (fun _ => x)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hg1 : Integrable g1 volume := ep_pdf1_integrable g
  have hfm2 : Integrable (fun x : ℝ => x ^ 2 * f1 x) volume := ep_secondMoment_integrable f hf
  have hgm2 : Integrable (fun u : ℝ => u ^ 2 * g1 u) volume := ep_secondMoment_integrable g hg
  have hprod1 := ep_integrable_prod_shear (hfm2.const_mul 2) hg1
  have hprod2 := ep_integrable_prod_shear hf1 (hgm2.const_mul 2)
  have hdom : Integrable (fun z : ℝ =>
      (∫ x : ℝ, 2 * (x ^ 2 * f1 x) * g1 (z - x)) +
        ∫ x : ℝ, f1 x * (2 * ((z - x) ^ 2 * g1 (z - x)))) volume :=
    hprod1.integral_prod_left.add hprod2.integral_prod_left
  have hmeas : AEStronglyMeasurable (fun z : ℝ => z ^ 2 * (convDensity f g).pdf (fun _ => z))
      volume :=
    ((continuous_pow 2).aestronglyMeasurable).mul
      (ep_pdf1_integrable (convDensity f g)).aestronglyMeasurable
  have hae1 : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => 2 * (x ^ 2 * f1 x) * g1 (z - x)) volume :=
    hprod1.prod_right_ae
  have hae2 : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => f1 x * (2 * ((z - x) ^ 2 * g1 (z - x)))) volume :=
    hprod2.prod_right_ae
  refine hdom.mono' hmeas ((hae1.and hae2).mono fun z ⟨h1, h2⟩ => ?_)
  have hnn : 0 ≤ z ^ 2 * (convDensity f g).pdf (fun _ => z) :=
    mul_nonneg (sq_nonneg z) ((convDensity f g).nonneg _)
  rw [Real.norm_of_nonneg hnn, convDensity_pdf_eq, ← integral_const_mul]
  change ∫ x : ℝ, z ^ 2 * (f1 x * g1 (z - x)) ≤
    (∫ x : ℝ, 2 * (x ^ 2 * f1 x) * g1 (z - x)) +
      ∫ x : ℝ, f1 x * (2 * ((z - x) ^ 2 * g1 (z - x)))
  have hpt : ∀ x : ℝ, z ^ 2 * (f1 x * g1 (z - x)) ≤
      2 * (x ^ 2 * f1 x) * g1 (z - x) + f1 x * (2 * ((z - x) ^ 2 * g1 (z - x))) := by
    intro x
    have hsq : z ^ 2 ≤ 2 * x ^ 2 + 2 * (z - x) ^ 2 := by
      have : 0 ≤ (x - (z - x)) ^ 2 := sq_nonneg _
      linarith
    have hfg_nn : 0 ≤ f1 x * g1 (z - x) := mul_nonneg (f.nonneg _) (g.nonneg _)
    nlinarith
  have hsum : Integrable (fun x : ℝ =>
      2 * (x ^ 2 * f1 x) * g1 (z - x) + f1 x * (2 * ((z - x) ^ 2 * g1 (z - x)))) volume :=
    h1.add h2
  have hint_lhs : Integrable (fun x : ℝ => z ^ 2 * (f1 x * g1 (z - x))) volume := by
    refine hsum.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((hf1.aestronglyMeasurable.mul
        (hg1.comp_sub_left z).aestronglyMeasurable).const_mul (z ^ 2))
    · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg z) (mul_nonneg (f.nonneg _) (g.nonneg _)))]
      exact hpt x
  rw [← integral_add h1 h2]
  exact integral_mono hint_lhs hsum hpt

/-- Finite convex mixture of 1D densities `∑ u, P(u) f_u`. -/
noncomputable def mixDensity {U : Type*} [Fintype U]
    (P : ProbDist U) (fs : U → Density 1) : Density 1 where
  pdf := fun x => ∑ u : U, P.pmf u * (fs u).pdf x
  nonneg := fun x => Finset.sum_nonneg fun u _ => mul_nonneg (P.nonneg u) ((fs u).nonneg x)
  integrable :=
    ep_integrable_finset_sum Finset.univ fun u _ => (fs u).integrable.const_mul (P.pmf u)
  integral_one := by
    rw [ep_integral_finset_sum Finset.univ fun u _ => (fs u).integrable.const_mul (P.pmf u)]
    simp_rw [integral_const_mul, (fs _).integral_one, mul_one]
    exact P.sum_one

lemma mixDensity_awgnOutputDensity {U : Type*} [Fintype U]
    (P : ProbDist U) (fs : U → Density 1) {N : ℝ} (hN : 0 < N) :
    mixDensity P (fun u => awgnOutputDensity (fs u) N hN) =
      awgnOutputDensity (mixDensity P fs) N hN := by
  refine ep_density_ext fun z => ?_
  change ∑ u : U, P.pmf u * (∫ y : Fin 1 → ℝ, (fs u).pdf y * gaussianPdf1D N (z - y 0)) =
    ∫ y : Fin 1 → ℝ, (∑ u : U, P.pmf u * (fs u).pdf y) * gaussianPdf1D N (z - y 0)
  simp_rw [Finset.sum_mul, ← integral_const_mul]
  have hint : ∀ u ∈ (Finset.univ : Finset U),
      Integrable (fun y : Fin 1 → ℝ => P.pmf u * (fs u).pdf y * gaussianPdf1D N (z - y 0)) volume := by
    intro u _
    have hdom := ((fs u).integrable.const_mul (P.pmf u)).const_mul (1 / Real.sqrt (2 * Real.pi * N))
    refine hdom.mono' ?_ (ae_of_all _ fun y => ?_)
    · exact (((fs u).integrable.aestronglyMeasurable.const_mul _).mul
        ((ep_continuous_gaussianPdf1D N).comp
          (continuous_const.sub (continuous_apply 0))).aestronglyMeasurable)
    · have hnn : 0 ≤ P.pmf u * (fs u).pdf y := mul_nonneg (P.nonneg u) ((fs u).nonneg y)
      rw [Real.norm_of_nonneg (mul_nonneg hnn (gaussianPdf1D_nonneg hN.le _))]
      have hle := ep_gaussianPdf1D_le_const hN (z - y 0)
      nlinarith
  rw [ep_integral_finset_sum Finset.univ hint]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1; funext y; ring

lemma hasFiniteSecondMoment_mixDensity {U : Type*} [Fintype U]
    (P : ProbDist U) (fs : U → Density 1) (hm2 : ∀ u, HasFiniteSecondMoment (fs u)) :
    HasFiniteSecondMoment (mixDensity P fs) := by
  unfold HasFiniteSecondMoment
  simp only [Fin.sum_univ_one]
  change Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * ∑ u : U, P.pmf u * (fs u).pdf x) volume
  have hrew : (fun x : Fin 1 → ℝ => (x 0) ^ 2 * ∑ u : U, P.pmf u * (fs u).pdf x) =
      fun x : Fin 1 → ℝ => ∑ u : U, P.pmf u * ((x 0) ^ 2 * (fs u).pdf x) := by
    funext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by ring
  rw [hrew]
  refine ep_integrable_finset_sum Finset.univ fun u _ => ?_
  have hu : Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * (fs u).pdf x) volume := by
    simpa [HasFiniteSecondMoment, Fin.sum_univ_one] using hm2 u
  exact hu.const_mul (P.pmf u)

lemma mixDensity_secondMoment {U : Type*} [Fintype U]
    (P : ProbDist U) (fs : U → Density 1) (hm2 : ∀ u, HasFiniteSecondMoment (fs u)) :
    ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (mixDensity P fs).pdf x =
      ∑ u : U, P.pmf u * ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (fs u).pdf x := by
  have hrew : (fun x : Fin 1 → ℝ => (x 0) ^ 2 * (mixDensity P fs).pdf x) =
      fun x : Fin 1 → ℝ => ∑ u : U, P.pmf u * ((x 0) ^ 2 * (fs u).pdf x) := by
    funext x
    change (x 0) ^ 2 * ∑ u : U, P.pmf u * (fs u).pdf x = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => by ring
  rw [hrew, ep_integral_finset_sum Finset.univ fun u _ => ?_]
  · simp_rw [integral_const_mul]
  · have hu : Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * (fs u).pdf x) volume := by
      simpa [HasFiniteSecondMoment, Fin.sum_univ_one] using hm2 u
    exact hu.const_mul (P.pmf u)

/-! ### Section 1: Fisher Information, Gaussian Smoothing, and Cramér–Rao Inequality -/

/-- **1D Fisher Information** of a probability density `f`:
    `J(f) = ∫ (f'(y))² / f(y) dy` (using Lean's convention `x / 0 = 0` outside the support). -/
noncomputable def fisherInfo (f : Density 1) : ℝ :=
  ∫ y : ℝ, (deriv (fun t : ℝ => f.pdf (fun _ => t)) y) ^ 2 / f.pdf (fun _ => y)

/-- Fisher information is always nonnegative: `J(f) ≥ 0`. -/
theorem fisherInfo_nonneg (f : Density 1) : 0 ≤ fisherInfo f :=
  integral_nonneg fun _ => div_nonneg (sq_nonneg _) (f.nonneg _)

/-- **Translation Invariance of Fisher Information**: `J(X + c) = J(X)`. -/
theorem fisherInfo_translate (f : Density 1) (c : ℝ) :
    fisherInfo (translateDensity1D f c) = fisherInfo f := by
  unfold fisherInfo translateDensity1D
  let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
  have hderiv : ∀ y : ℝ, deriv (fun t : ℝ => f1 (t - c)) y = deriv f1 (y - c) :=
    fun y => deriv_comp_sub_const f1 c y
  change ∫ y : ℝ, (deriv (fun t : ℝ => f1 (t - c)) y) ^ 2 / f1 (y - c) =
    ∫ y : ℝ, (deriv f1 y) ^ 2 / f1 y
  simp_rw [hderiv]
  exact integral_sub_right_eq_self (fun u : ℝ => (deriv f1 u) ^ 2 / f1 u) c

/-- **Scaling Law for Fisher Information**: `J(a X) = J(X) / a²` for `a ≠ 0`. -/
theorem fisherInfo_scale (f : Density 1) {a : ℝ} (ha : a ≠ 0) :
    fisherInfo (scaleDensity1D f ha) = fisherInfo f / a ^ 2 := by
  unfold fisherInfo scaleDensity1D
  let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
  have hderiv : ∀ y : ℝ,
      deriv (fun t : ℝ => |a|⁻¹ * f1 (a⁻¹ * t)) y = |a|⁻¹ * (a⁻¹ * deriv f1 (a⁻¹ * y)) := by
    intro y
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul]
  change ∫ y : ℝ, (deriv (fun t : ℝ => |a|⁻¹ * f1 (a⁻¹ * t)) y) ^ 2 /
      (|a|⁻¹ * f1 (a⁻¹ * y)) = (∫ u : ℝ, (deriv f1 u) ^ 2 / f1 u) / a ^ 2
  simp_rw [hderiv]
  have ha_abs : |a| ≠ 0 := abs_ne_zero.mpr ha
  have hrew : (fun y : ℝ => (|a|⁻¹ * (a⁻¹ * deriv f1 (a⁻¹ * y))) ^ 2 / (|a|⁻¹ * f1 (a⁻¹ * y))) =
      fun y : ℝ => (|a|⁻¹ * (a ^ 2)⁻¹) * ((deriv f1 (a⁻¹ * y)) ^ 2 / f1 (a⁻¹ * y)) := by
    funext y
    by_cases hf0 : f1 (a⁻¹ * y) = 0
    · simp [hf0]
    · field_simp [ha, ha_abs, hf0]
  rw [hrew, integral_const_mul,
    Measure.integral_comp_mul_left (fun u : ℝ => (deriv f1 u) ^ 2 / f1 u) a⁻¹]
  simp only [smul_eq_mul, inv_inv]
  field_simp [ha, ha_abs]

/-- **Fisher Information of a 1D Gaussian**: `J(N(0, v)) = 1 / v` for `v > 0`. -/
theorem fisherInfo_gaussian {v : ℝ} (hv : 0 < v) :
    fisherInfo (gaussianDensity1D v hv) = 1 / v := by
  unfold fisherInfo
  have hderiv : ∀ y : ℝ, deriv (gaussianPdf1D v) y = -(y / v) * gaussianPdf1D v y :=
    fun y => (ep_hasDerivAt_gaussianPdf1D hv y).deriv
  change ∫ y : ℝ, (deriv (gaussianPdf1D v) y) ^ 2 / gaussianPdf1D v y = 1 / v
  simp_rw [hderiv]
  have hrew : (fun y : ℝ => (-(y / v) * gaussianPdf1D v y) ^ 2 / gaussianPdf1D v y) =
      fun y : ℝ => (1 / v ^ 2) * (y ^ 2 * gaussianPdf1D v y) := by
    funext y
    have hg0 : gaussianPdf1D v y ≠ 0 := ne_of_gt (gaussianPdf1D_pos hv y)
    have hv0 : v ≠ 0 := ne_of_gt hv
    field_simp [hg0, hv0]
  rw [hrew, integral_const_mul, integral_sq_mul_gaussianPdf1D hv]
  have hv0 : v ≠ 0 := ne_of_gt hv
  field_simp [hv0]

/-- Strictly positive everywhere: `f_t(y) > 0` for any 1D density `f`, `t > 0`, and `y ∈ ℝ`. -/
theorem awgnOutputDensity_pdf_pos (f : Density 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    0 < (awgnOutputDensity f t ht).pdf (fun _ => y) := by
  have hrew : (awgnOutputDensity f t ht).pdf (fun _ => y) =
      ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) := by
    rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]
    rfl
  rw [hrew]
  have hint : Integrable (fun x : ℝ => f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) volume := by
    have hdom := (ep_pdf1_integrable f).const_mul (1 / Real.sqrt (2 * Real.pi * t))
    refine hdom.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
      have hle := ep_gaussianPdf1D_le_const ht (y - x)
      have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
      nlinarith
  have hnn : 0 ≤ ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) :=
    integral_nonneg fun x => mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _)
  rcases lt_or_eq_of_le hnn with hpos | heq
  · exact hpos
  · exfalso
    have hae0 : (fun x : ℝ => f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))
        hint).mp heq.symm
    have hf0 : (fun x : ℝ => f.pdf (fun _ => x)) =ᵐ[volume] 0 :=
      hae0.mono fun x hx => by
        have hgpos : 0 < gaussianPdf1D t (y - x) := gaussianPdf1D_pos ht (y - x)
        exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt hgpos)
    have h1 : ∫ x : ℝ, f.pdf (fun _ => x) = 0 := by
      simpa using integral_congr_ae hf0
    linarith [ep_pdf1_integral_one f]

/-- First spatial derivative of the Gaussian-smoothed density `f_t`:
    `f_t'(y) = ∫ f(x) · (-(y - x) / t) · φ_t(y - x) dx`. -/
theorem hasDerivAt_awgnOutputDensity_pdf (f : Density 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))
      (∫ x : ℝ, f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))) y := by
  have hrew : (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) =
      fun z : ℝ => ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (z - x) := by
    funext z
    rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]
    rfl
  rw [hrew]
  let F : ℝ → ℝ → ℝ := fun z x => f.pdf (fun _ => x) * gaussianPdf1D t (z - x)
  let F' : ℝ → ℝ → ℝ := fun z x => f.pdf (fun _ => x) * (-((z - x) / t) * gaussianPdf1D t (z - x))
  let C : ℝ := 1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt t)
  have hF_meas : ∀ᶠ z in 𝓝 y, AEStronglyMeasurable (F z) volume :=
    Filter.Eventually.of_forall fun z =>
      (ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (F y) volume := by
    have hdom := (ep_pdf1_integrable f).const_mul (1 / Real.sqrt (2 * Real.pi * t))
    refine hdom.mono' ((ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
    have hle := ep_gaussianPdf1D_le_const ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hF'_meas : AEStronglyMeasurable (F' y) volume :=
    (ep_pdf1_integrable f).aestronglyMeasurable.mul
      ((((continuous_const.sub continuous_id).div_const t).neg).mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂volume, ∀ z ∈ (Set.univ : Set ℝ), ‖F' z x‖ ≤ C * f.pdf (fun _ => x) := by
    refine ae_of_all _ fun x z _ => ?_
    dsimp only [F', C]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle := ep_abs_deriv_gaussianPdf1D_le ht (z - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    calc f.pdf (fun _ => x) * |-((z - x) / t) * gaussianPdf1D t (z - x)|
        ≤ f.pdf (fun _ => x) * (1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt t)) :=
          mul_le_mul_of_nonneg_left hle hfnn
      _ = 1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt t) * f.pdf (fun _ => x) := mul_comm _ _
  have h_diff : ∀ᵐ x ∂volume, ∀ z ∈ (Set.univ : Set ℝ), HasDerivAt (F · x) (F' z x) z := by
    refine ae_of_all _ fun x z _ => ?_
    have hsub : HasDerivAt (fun w : ℝ => w - x) 1 z := by simpa using (hasDerivAt_id z).sub_const x
    have hcomp := (ep_hasDerivAt_gaussianPdf1D ht (z - x)).comp z hsub
    simpa [F, F'] using hcomp.const_mul (f.pdf (fun _ => x))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    hF_meas hF_int hF'_meas h_bound ((ep_pdf1_integrable f).const_mul C) h_diff).2

/-- Second spatial derivative of the Gaussian-smoothed density `f_t`:
    `f_t''(y) = ∫ f(x) · (((y - x)/t)² - 1/t) · φ_t(y - x) dx`. -/
theorem hasDerivAt_deriv_awgnOutputDensity_pdf (f : Density 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)))
      (∫ x : ℝ, f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (y - x))) y := by
  have hrew : deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) =
      fun z : ℝ => ∫ x : ℝ, f.pdf (fun _ => x) * (-((z - x) / t) * gaussianPdf1D t (z - x)) := by
    funext z
    exact (hasDerivAt_awgnOutputDensity_pdf f ht z).deriv
  rw [hrew]
  let F : ℝ → ℝ → ℝ := fun z x => f.pdf (fun _ => x) * (-((z - x) / t) * gaussianPdf1D t (z - x))
  let F' : ℝ → ℝ → ℝ := fun z x =>
    f.pdf (fun _ => x) * (((z - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (z - x))
  let C : ℝ := 3 / (t * Real.sqrt (2 * Real.pi * t))
  have hF_meas : ∀ᶠ z in 𝓝 y, AEStronglyMeasurable (F z) volume :=
    Filter.Eventually.of_forall fun z =>
      (ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((((continuous_const.sub continuous_id).div_const t).neg).mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hF_int : Integrable (F y) volume := by
    let C1 : ℝ := 1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt t)
    have hdom := (ep_pdf1_integrable f).const_mul C1
    refine hdom.mono' ((ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((((continuous_const.sub continuous_id).div_const t).neg).mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    dsimp only [F, C1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle := ep_abs_deriv_gaussianPdf1D_le ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hF'_meas : AEStronglyMeasurable (F' y) volume :=
    (ep_pdf1_integrable f).aestronglyMeasurable.mul
      (((((continuous_const.sub continuous_id).pow 2).div_const (t ^ 2)).sub continuous_const).mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂volume, ∀ z ∈ (Set.univ : Set ℝ), ‖F' z x‖ ≤ C * f.pdf (fun _ => x) := by
    refine ae_of_all _ fun x z _ => ?_
    dsimp only [F', C]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle := ep_abs_deriv2_gaussianPdf1D_le ht (z - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have h_diff : ∀ᵐ x ∂volume, ∀ z ∈ (Set.univ : Set ℝ), HasDerivAt (F · x) (F' z x) z := by
    refine ae_of_all _ fun x z _ => ?_
    have hsub : HasDerivAt (fun w : ℝ => w - x) 1 z := by simpa using (hasDerivAt_id z).sub_const x
    have hcomp := (ep_hasDerivAt_deriv_gaussianPdf1D ht (z - x)).comp z hsub
    simpa [F, F'] using hcomp.const_mul (f.pdf (fun _ => x))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    hF_meas hF_int hF'_meas h_bound ((ep_pdf1_integrable f).const_mul C) h_diff).2

/-- **1D Heat Equation** for the Gaussian-smoothed density:
    `∂_t f_t(y) = (1/2) ∂_y² f_t(y)` for all `t > 0` and `y ∈ ℝ`. -/
theorem awgnOutputDensity_heat_equation (f : Density 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D s (y - x))
      ((1 / 2 : ℝ) * deriv (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) y) t := by
  have hderiv2 : deriv (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) y =
      ∫ x : ℝ, f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (y - x)) :=
    (hasDerivAt_deriv_awgnOutputDensity_pdf f ht y).deriv
  rw [hderiv2, ← integral_const_mul]
  let F : ℝ → ℝ → ℝ := fun s x => f.pdf (fun _ => x) * gaussianPdf1D s (y - x)
  let F' : ℝ → ℝ → ℝ := fun s x =>
    (1 / 2 : ℝ) * (f.pdf (fun _ => x) * (((y - x) ^ 2 / s ^ 2 - 1 / s) * gaussianPdf1D s (y - x)))
  have ht1 : 0 < t / 2 := half_pos ht
  have hs_mem : Set.Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (half_lt_self ht)
  let C : ℝ := (1 / 2 : ℝ) * (3 / ((t / 2) * Real.sqrt (2 * Real.pi * (t / 2))))
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume :=
    Filter.Eventually.of_forall fun s =>
      (ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (F t) volume := by
    have hdom := (ep_pdf1_integrable f).const_mul (1 / Real.sqrt (2 * Real.pi * t))
    refine hdom.mono' ((ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
    have hle := ep_gaussianPdf1D_le_const ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hF'_meas : AEStronglyMeasurable (F' t) volume :=
    ((ep_pdf1_integrable f).aestronglyMeasurable.mul
      (((((continuous_const.sub continuous_id).pow 2).div_const (t ^ 2)).sub continuous_const).mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable).const_mul _
  have h_bound : ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioi (t / 2), ‖F' s x‖ ≤ C * f.pdf (fun _ => x) := by
    refine ae_of_all _ fun x s hs => ?_
    have hs_gt : t / 2 < s := hs
    have hs_pos : 0 < s := lt_trans ht1 hs_gt
    dsimp only [F', C]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle1 := ep_abs_deriv2_gaussianPdf1D_le hs_pos (y - x)
    have hpi_le : 2 * Real.pi * (t / 2) ≤ 2 * Real.pi * s :=
      mul_le_mul_of_nonneg_left hs_gt.le (by positivity)
    have hle2 : 3 / (s * Real.sqrt (2 * Real.pi * s)) ≤
        3 / ((t / 2) * Real.sqrt (2 * Real.pi * (t / 2))) := by
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      exact mul_le_mul hs_gt.le (Real.sqrt_le_sqrt hpi_le) (Real.sqrt_nonneg _) hs_pos.le
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    have hle := le_trans hle1 hle2
    nlinarith
  have h_diff : ∀ᵐ x ∂volume, ∀ s ∈ Set.Ioi (t / 2), HasDerivAt (F · x) (F' s x) s := by
    refine ae_of_all _ fun x s hs => ?_
    have hs_pos : 0 < s := lt_trans ht1 hs
    have hd := (ep_hasDerivAt_gaussianPdf1D_var hs_pos (y - x)).const_mul (f.pdf (fun _ => x))
    refine hd.congr_deriv ?_
    dsimp only [F']; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_mem
    hF_meas hF_int hF'_meas h_bound ((ep_pdf1_integrable f).const_mul C) h_diff).2

/-- Pointwise Cauchy–Schwarz bound on the score of a Gaussian-smoothed density:
    `(f_t'(y))² / f_t(y) ≤ ∫ f(x) ((y - x)² / t²) φ_t(y - x) dx`. -/
private lemma ep_awgn_score_le (f : Density 1) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) y) ^ 2 /
        (awgnOutputDensity f t ht).pdf (fun _ => y) ≤
      ∫ x : ℝ, f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2) * gaussianPdf1D t (y - x)) := by
  set p_val : ℝ := (awgnOutputDensity f t ht).pdf (fun _ => y)
  set p'_val : ℝ := deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) y
  have hp_pos : 0 < p_val := awgnOutputDensity_pdf_pos f ht y
  have hp_eq : p_val = ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) := by
    dsimp only [p_val]
    rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]; rfl
  have hp'_eq : p'_val = ∫ x : ℝ, f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x)) :=
    (hasDerivAt_awgnOutputDensity_pdf f ht y).deriv
  have hf1 : Integrable (fun x : ℝ => f.pdf (fun _ => x)) volume := ep_pdf1_integrable f
  have hint0 : Integrable (fun x : ℝ => f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) volume := by
    have hdom := hf1.const_mul (1 / Real.sqrt (2 * Real.pi * t))
    refine hdom.mono' (hf1.aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
    have hle := ep_gaussianPdf1D_le_const ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hint1 : Integrable (fun x : ℝ => f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))) volume := by
    have hdom := hf1.const_mul (1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt t))
    refine hdom.mono' (hf1.aestronglyMeasurable.mul
        ((((continuous_const.sub continuous_id).div_const t).neg).mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle := ep_abs_deriv_gaussianPdf1D_le ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hint2 : Integrable (fun x : ℝ => f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2) * gaussianPdf1D t (y - x))) volume := by
    have hdom := hf1.const_mul (2 / (t * Real.sqrt (2 * Real.pi * t)))
    refine hdom.mono' (hf1.aestronglyMeasurable.mul
        ((((continuous_const.sub continuous_id).pow 2).div_const (t ^ 2)).mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (mul_nonneg (by positivity) (gaussianPdf1D_nonneg ht.le _)))]
    have hsq := ep_sq_mul_exp_neg_sq_le ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hs0 : Real.sqrt (2 * Real.pi * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hle : ((y - x) ^ 2 / t ^ 2) * gaussianPdf1D t (y - x) ≤ 2 / (t * Real.sqrt (2 * Real.pi * t)) := by
      unfold gaussianPdf1D
      calc ((y - x) ^ 2 / t ^ 2) * (1 / Real.sqrt (2 * Real.pi * t) * Real.exp (-((y - x) ^ 2) / (2 * t)))
          = ((y - x) ^ 2 * Real.exp (-((y - x) ^ 2) / (2 * t))) / (t ^ 2 * Real.sqrt (2 * Real.pi * t)) := by ring
        _ ≤ (2 * t) / (t ^ 2 * Real.sqrt (2 * Real.pi * t)) :=
            div_le_div_of_nonneg_right hsq (by positivity)
        _ = 2 / (t * Real.sqrt (2 * Real.pi * t)) := by field_simp [ht0, hs0]
    nlinarith
  set lam : ℝ := -p'_val / p_val
  have hquad_nn : 0 ≤ ∫ x : ℝ,
      (lam ^ 2 * (f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) +
       (2 * lam) * (f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))) +
       f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2) * gaussianPdf1D t (y - x))) := by
    refine integral_nonneg fun x => ?_
    have heq : lam ^ 2 * (f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) +
        (2 * lam) * (f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))) +
        f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2) * gaussianPdf1D t (y - x)) =
        (lam - (y - x) / t) ^ 2 * (f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) := by ring
    rw [heq]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))
  have hi0 := hint0.const_mul (lam ^ 2)
  have hi1 := hint1.const_mul (2 * lam)
  have hi01 : Integrable (fun x : ℝ =>
      lam ^ 2 * (f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) +
      (2 * lam) * (f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x)))) volume :=
    hi0.add hi1
  rw [integral_add hi01 hint2, integral_add hi0 hi1, integral_const_mul, integral_const_mul,
    ← hp_eq, ← hp'_eq] at hquad_nn
  have hsimp : lam ^ 2 * p_val + (2 * lam) * p'_val = -(p'_val ^ 2 / p_val) := by
    dsimp only [lam]
    have hp0 : p_val ≠ 0 := ne_of_gt hp_pos
    field_simp [hp0]; ring
  linarith

private lemma ep_integrable_fisherInfo_awgn (f : Density 1) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) y) ^ 2 /
      (awgnOutputDensity f t ht).pdf (fun _ => y)) volume := by
  have hg2 : Integrable (fun u : ℝ => (u ^ 2 / t ^ 2) * gaussianPdf1D t u) volume := by
    have h := (integrable_sq_mul_gaussianPdf1D ht).const_mul (1 / t ^ 2)
    refine h.congr (ae_of_all _ fun u => ?_); ring
  have hq_int := ep_integrable_conv_fun (ep_pdf1_integrable f) hg2
  have hp_cont : Continuous (fun y : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => y)) :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).continuousAt
  have hp'_cont : Continuous (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_deriv_awgnOutputDensity_pdf f ht y).continuousAt
  refine hq_int.mono' ?_ (ae_of_all _ fun y => ?_)
  · exact ((hp'_cont.pow 2).div hp_cont fun y => ne_of_gt (awgnOutputDensity_pdf_pos f ht y)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (awgnOutputDensity_pdf_pos f ht y).le)]
    exact ep_awgn_score_le f ht y

/-- **Fisher Information Upper Bound for Gaussian-Smoothed Densities**:
    `J(X + √t Z) ≤ 1 / t` for any 1D density `f` and `t > 0` (via Cauchy–Schwarz + Tonelli). -/
theorem fisherInfo_awgnOutput_le_inv (f : Density 1) {t : ℝ} (ht : 0 < t) :
    fisherInfo (awgnOutputDensity f t ht) ≤ 1 / t := by
  have hg2 : Integrable (fun u : ℝ => (u ^ 2 / t ^ 2) * gaussianPdf1D t u) volume := by
    have h := (integrable_sq_mul_gaussianPdf1D ht).const_mul (1 / t ^ 2)
    refine h.congr (ae_of_all _ fun u => ?_); ring
  have hq_int := ep_integrable_conv_fun (ep_pdf1_integrable f) hg2
  have hq_val : ∫ y : ℝ, (∫ x : ℝ, f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2) * gaussianPdf1D t (y - x))) =
      1 / t := by
    rw [ep_integral_conv_fun (ep_pdf1_integrable f) hg2, ep_pdf1_integral_one f, one_mul]
    have hrew : (fun u : ℝ => (u ^ 2 / t ^ 2) * gaussianPdf1D t u) =
        fun u : ℝ => (1 / t ^ 2) * (u ^ 2 * gaussianPdf1D t u) := by funext u; ring
    rw [hrew, integral_const_mul, integral_sq_mul_gaussianPdf1D ht]
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp [ht0]
  unfold fisherInfo
  rw [← hq_val]
  exact integral_mono (ep_integrable_fisherInfo_awgn f ht) hq_int (ep_awgn_score_le f ht)

private lemma ep_integrable_deriv_awgn (f : Density 1) {t : ℝ} (ht : 0 < t) :
    Integrable (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) volume := by
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hgu : Integrable (fun u : ℝ => (|u| / t) * gaussianPdf1D t u) volume := by
    have h := (ep_integrable_abs_mul_gaussianPdf1D ht).const_mul (1 / t)
    refine h.congr (ae_of_all _ fun u => ?_); ring
  have hdom := ep_integrable_conv_fun hf1 hgu
  have hp'_cont : Continuous (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_deriv_awgnOutputDensity_pdf f ht y).continuousAt
  refine hdom.mono' hp'_cont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [(hasDerivAt_awgnOutputDensity_pdf f ht y).deriv]
  calc ‖∫ x : ℝ, f1 x * (-((y - x) / t) * gaussianPdf1D t (y - x))‖
      ≤ ∫ x : ℝ, ‖f1 x * (-((y - x) / t) * gaussianPdf1D t (y - x))‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, f1 x * ((|y - x| / t) * gaussianPdf1D t (y - x)) := by
        congr 1; funext x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _), abs_mul, abs_neg,
          abs_div, abs_of_pos ht, abs_of_pos (gaussianPdf1D_pos ht _)]

private lemma ep_bdd_deriv_awgn (f : Density 1) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ y : ℝ, |deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) y| ≤ C := by
  let C : ℝ := 1 / (Real.sqrt (2 * Real.pi * t) * Real.sqrt t)
  refine ⟨C, fun y => ?_⟩
  rw [(hasDerivAt_awgnOutputDensity_pdf f ht y).deriv]
  have h1 : |∫ x : ℝ, f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))| ≤
      ∫ x : ℝ, |f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))| :=
    abs_integral_le_integral_abs
  have h2 : ∫ x : ℝ, |f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))| ≤
      ∫ x : ℝ, C * f.pdf (fun _ => x) := by
    have hdom := (ep_pdf1_integrable f).const_mul C
    have hint_lhs : Integrable (fun x : ℝ =>
        |f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))|) volume := by
      refine hdom.mono' ?_ (ae_of_all _ fun x => ?_)
      · exact ((ep_pdf1_integrable f).aestronglyMeasurable.mul
          ((((continuous_const.sub continuous_id).div_const t).neg).mul
            ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable).norm
      · rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
        have hle := ep_abs_deriv_gaussianPdf1D_le ht (y - x)
        have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
        nlinarith
    refine integral_mono hint_lhs hdom fun x => ?_
    rw [abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle := ep_abs_deriv_gaussianPdf1D_le ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  rw [integral_const_mul, ep_pdf1_integral_one f, mul_one] at h2
  exact le_trans h1 h2

/-- Any differentiable strictly positive density with integrable Fisher information has
    strictly positive Fisher information: `0 < J(f)`. -/
lemma fisherInfo_pos_of_pos_diff (f : Density 1)
    (hpos : ∀ y : ℝ, 0 < f.pdf (fun _ => y))
    (hdiff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => f.pdf (fun _ => t)) y)
    (hJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => f.pdf (fun _ => t)) y) ^ 2 / f.pdf (fun _ => y)) volume)
    (hderiv_int : Integrable (deriv (fun t : ℝ => f.pdf (fun _ => t))) volume) :
    0 < fisherInfo f := by
  rcases lt_or_eq_of_le (fisherInfo_nonneg f) with hlt | heq
  · exact hlt
  · exfalso
    let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
    have hae0 : (fun y : ℝ => (deriv f1 y) ^ 2 / f1 y) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => div_nonneg (sq_nonneg _) (f.nonneg _)) hJ_int).mp heq.symm
    have hderiv0 : deriv f1 =ᵐ[volume] 0 :=
      hae0.mono fun y hy => by
        have hp : f1 y ≠ 0 := ne_of_gt (hpos y)
        have hsq : (deriv f1 y) ^ 2 = 0 := (div_eq_zero_iff.mp hy).resolve_right hp
        exact sq_eq_zero_iff.mp hsq
    have hconst : ∀ y : ℝ, f1 y = f1 0 := by
      intro y
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := f1) (f' := deriv f1) (a := 0) (b := y)
        (fun x _ => (hdiff x).hasDerivAt) hderiv_int.intervalIntegrable
      have hzero : ∫ x in (0 : ℝ)..y, deriv f1 x = 0 := by
        rw [intervalIntegral.integral_congr_ae (hderiv0.mono fun x hx _ => hx)]
        simp
      linarith
    have hc_pos : 0 < f1 0 := hpos 0
    have hint_c : Integrable (fun _ : ℝ => f1 0) volume :=
      (ep_pdf1_integrable f).congr (ae_of_all _ hconst)
    rcases integrable_const_iff.mp hint_c with hc0 | hfin
    · linarith
    · exact absurd hfin.measure_univ_lt_top (by simp)

/-- **Cramér–Rao Inequality** (product form, Cover & Thomas §17.7):
    for any differentiable 1D density `f` with finite second moment and integrable Fisher
    information, and any `μ ∈ ℝ` (in particular `μ = E[X]`),
    `1 ≤ E[(X - μ)²] · J(X)`. -/
theorem cramer_rao_inequality (f : Density 1) (μ : ℝ)
    (hm2 : HasFiniteSecondMoment f)
    (hdiff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => f.pdf (fun _ => t)) y)
    (hJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => f.pdf (fun _ => t)) y) ^ 2 / f.pdf (fun _ => y)) volume) :
    1 ≤ (∫ y : ℝ, (y - μ) ^ 2 * f.pdf (fun _ => y)) * fisherInfo f := by
  let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
  let f1' : ℝ → ℝ := deriv f1
  have hf1_int : Integrable f1 volume := ep_pdf1_integrable f
  have hm2_int : Integrable (fun y : ℝ => y ^ 2 * f1 y) volume := ep_secondMoment_integrable f hm2
  have hvar_int : Integrable (fun y : ℝ => (y - μ) ^ 2 * f1 y) volume := by
    have hdom : Integrable (fun y : ℝ => 2 * (y ^ 2 * f1 y) + (2 * μ ^ 2) * f1 y) volume :=
      (hm2_int.const_mul 2).add (hf1_int.const_mul (2 * μ ^ 2))
    refine hdom.mono' ((((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable).mul
        hf1_int.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (f.nonneg _))]
    have hsq : (y - μ) ^ 2 ≤ 2 * y ^ 2 + 2 * μ ^ 2 := by
      have : 0 ≤ (y + μ) ^ 2 := sq_nonneg _
      linarith
    have hfnn : 0 ≤ f1 y := f.nonneg _
    nlinarith
  have hlin_int : Integrable (fun y : ℝ => (y - μ) * f1 y) volume := by
    have hdom : Integrable (fun y : ℝ => f1 y + (y - μ) ^ 2 * f1 y) volume := hf1_int.add hvar_int
    refine hdom.mono' (((continuous_id.sub continuous_const).aestronglyMeasurable).mul
        hf1_int.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle : |y - μ| ≤ 1 + (y - μ) ^ 2 := by
      have : 0 ≤ (|y - μ| - 1) ^ 2 := sq_nonneg _
      have habs : |y - μ| ^ 2 = (y - μ) ^ 2 := sq_abs _
      nlinarith
    have hfnn : 0 ≤ f1 y := f.nonneg _
    nlinarith
  have hderiv_zero_at_zero : ∀ y : ℝ, f1 y = 0 → f1' y = 0 := by
    intro y hy
    have hmin : IsLocalMin f1 y :=
      Filter.Eventually.of_forall fun z => by rw [hy]; exact f.nonneg _
    exact hmin.deriv_eq_zero
  have hcross_int : Integrable (fun y : ℝ => (y - μ) * f1' y) volume := by
    have hdom : Integrable (fun y : ℝ =>
        (1 / 2 : ℝ) * ((y - μ) ^ 2 * f1 y + (f1' y) ^ 2 / f1 y)) volume :=
      (hvar_int.add hJ_int).const_mul (1 / 2)
    have hf1'_meas : AEStronglyMeasurable f1' volume :=
      (measurable_deriv f1).aestronglyMeasurable
    refine hdom.mono' (((continuous_id.sub continuous_const).aestronglyMeasurable).mul hf1'_meas)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    by_cases hy : f1 y = 0
    · have h0 := hderiv_zero_at_zero y hy
      simp [hy, h0]
    · have hpos : 0 < f1 y := lt_of_le_of_ne (f.nonneg _) (Ne.symm hy)
      have hsq : 0 ≤ (|y - μ| * f1 y - |f1' y|) ^ 2 := sq_nonneg _
      have h2 : 2 * (|y - μ| * |f1' y|) * f1 y ≤ (y - μ) ^ 2 * (f1 y) ^ 2 + (f1' y) ^ 2 := by
        have ha : |y - μ| ^ 2 = (y - μ) ^ 2 := sq_abs _
        have hb : |f1' y| ^ 2 = (f1' y) ^ 2 := sq_abs _
        nlinarith
      rw [abs_mul]
      have hdiv := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 * f1 y)
      have hne : f1 y ≠ 0 := ne_of_gt hpos
      have hl : 2 * (|y - μ| * |f1' y|) * f1 y / (2 * f1 y) = |y - μ| * |f1' y| := by
        field_simp [hne]
      have hr : ((y - μ) ^ 2 * (f1 y) ^ 2 + (f1' y) ^ 2) / (2 * f1 y) =
          (1 / 2 : ℝ) * ((y - μ) ^ 2 * f1 y + (f1' y) ^ 2 / f1 y) := by
        field_simp [hne]
      rwa [hl, hr] at hdiv
  have hibp : ∫ y : ℝ, (y - μ) * f1' y = -1 := by
    have hderiv_prod : ∀ y : ℝ,
        HasDerivAt (fun t : ℝ => (t - μ) * f1 t) (f1 y + (y - μ) * f1' y) y := by
      intro y
      have h1 : HasDerivAt (fun t : ℝ => t - μ) 1 y := by simpa using (hasDerivAt_id y).sub_const μ
      have h2 : HasDerivAt f1 (f1' y) y := (hdiff y).hasDerivAt
      exact (h1.mul h2).congr_deriv (by ring)
    have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv_prod
      (hf1_int.add hcross_int) hlin_int
    rw [integral_add hf1_int hcross_int, ep_pdf1_integral_one f] at hzero
    linarith
  set V : ℝ := ∫ y : ℝ, (y - μ) ^ 2 * f1 y
  set J : ℝ := fisherInfo f
  have hquad : ∀ lam : ℝ, 0 ≤ lam ^ 2 * V - 2 * lam + J := by
    intro lam
    have hnn : 0 ≤ ∫ y : ℝ,
        (lam ^ 2 * ((y - μ) ^ 2 * f1 y) + (2 * lam) * ((y - μ) * f1' y) + (f1' y) ^ 2 / f1 y) := by
      refine integral_nonneg fun y => ?_
      by_cases hy : f1 y = 0
      · have h0 := hderiv_zero_at_zero y hy
        simp [hy, h0]
      · have hpos : 0 < f1 y := lt_of_le_of_ne (f.nonneg _) (Ne.symm hy)
        have hne : f1 y ≠ 0 := ne_of_gt hpos
        have heq : lam ^ 2 * ((y - μ) ^ 2 * f1 y) + (2 * lam) * ((y - μ) * f1' y) +
            (f1' y) ^ 2 / f1 y = (lam * (y - μ) * f1 y + f1' y) ^ 2 / f1 y := by
          field_simp [hne]; ring
        rw [heq]
        exact div_nonneg (sq_nonneg _) hpos.le
    have hi1 : Integrable (fun y : ℝ => lam ^ 2 * ((y - μ) ^ 2 * f1 y)) volume :=
      hvar_int.const_mul (lam ^ 2)
    have hi2 : Integrable (fun y : ℝ => (2 * lam) * ((y - μ) * f1' y)) volume :=
      hcross_int.const_mul (2 * lam)
    have hi12 : Integrable (fun y : ℝ =>
        lam ^ 2 * ((y - μ) ^ 2 * f1 y) + (2 * lam) * ((y - μ) * f1' y)) volume := hi1.add hi2
    have hJ_int' : Integrable (fun y : ℝ => (f1' y) ^ 2 / f1 y) volume := hJ_int
    rw [integral_add hi12 hJ_int', integral_add hi1 hi2, integral_const_mul, integral_const_mul,
      hibp] at hnn
    have hJeq : ∫ y : ℝ, (f1' y) ^ 2 / f1 y = J := rfl
    rw [hJeq] at hnn
    linarith
  have hV_pos : 0 < V := by
    have hV_nn : 0 ≤ V := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (f.nonneg _)
    rcases lt_or_eq_of_le hV_nn with hlt | heq
    · exact hlt
    · exfalso
      have h1 := hquad (J + 1)
      rw [← heq] at h1
      have hJ_nn : 0 ≤ J := fisherInfo_nonneg f
      linarith
  have hbest := hquad (1 / V)
  have hV0 : V ≠ 0 := ne_of_gt hV_pos
  have hsimp : (1 / V) ^ 2 * V - 2 * (1 / V) + J = J - 1 / V := by field_simp [hV0]; ring
  rw [hsimp] at hbest
  have h1V : 1 / V ≤ J := by linarith
  have hmul := mul_le_mul_of_nonneg_left h1V hV_pos.le
  rwa [mul_one_div_cancel hV0] at hmul

/-- **Cramér–Rao Inequality** (reciprocal form): `1 / J(X) ≤ E[(X - μ)²]`. -/
theorem cramer_rao_inv_le (f : Density 1) (μ : ℝ)
    (hm2 : HasFiniteSecondMoment f)
    (hdiff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => f.pdf (fun _ => t)) y)
    (hJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => f.pdf (fun _ => t)) y) ^ 2 / f.pdf (fun _ => y)) volume) :
    0 < fisherInfo f ∧ 1 / fisherInfo f ≤ ∫ y : ℝ, (y - μ) ^ 2 * f.pdf (fun _ => y) := by
  have hprod := cramer_rao_inequality f μ hm2 hdiff hJ_int
  have hJ_pos : 0 < fisherInfo f := by
    rcases lt_or_eq_of_le (fisherInfo_nonneg f) with hlt | heq
    · exact hlt
    · rw [← heq, mul_zero] at hprod; linarith
  refine ⟨hJ_pos, ?_⟩
  rw [div_le_iff₀ hJ_pos]
  exact hprod

/-- **Cramér–Rao Inequality for Gaussian-Smoothed Densities** (no smoothness hypotheses needed):
    `1 / J(X + √t Z) ≤ E[(X + √t Z - μ)²]`. -/
theorem cramer_rao_awgnOutput (f : Density 1) (μ : ℝ) (hm2 : HasFiniteSecondMoment f)
    {t : ℝ} (ht : 0 < t) :
    0 < fisherInfo (awgnOutputDensity f t ht) ∧
      1 / fisherInfo (awgnOutputDensity f t ht) ≤
        ∫ y : ℝ, (y - μ) ^ 2 * (awgnOutputDensity f t ht).pdf (fun _ => y) :=
  cramer_rao_inv_le (awgnOutputDensity f t ht) μ
    (hasFiniteSecondMoment_awgnOutputDensity f hm2 ht)
    (fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).differentiableAt)
    (ep_integrable_fisherInfo_awgn f ht)

/-! ### Section 2: Stam's Fisher Information Inequality (Cover & Thomas Thm. 17.7.2) -/

private lemma ep_pdf_le_integral_abs_deriv (g : Density 1)
    (hg_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => g.pdf (fun _ => t)) y)
    (hg'_int : Integrable (deriv (fun t : ℝ => g.pdf (fun _ => t))) volume) (u : ℝ) :
    g.pdf (fun _ => u) ≤ ∫ w : ℝ, |deriv (fun t : ℝ => g.pdf (fun _ => t)) w| := by
  let g1 : ℝ → ℝ := fun t => g.pdf (fun _ => t)
  have htend_bot : Tendsto g1 atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _ => (hg_diff x).hasDerivAt)
      hg'_int.integrableOn (ep_pdf1_integrable g).integrableOn
  have hftc := integral_Iic_of_hasDerivAt_of_tendsto' (a := u)
    (fun x _ => (hg_diff x).hasDerivAt) hg'_int.integrableOn htend_bot
  rw [sub_zero] at hftc
  calc g1 u = ∫ x in Set.Iic u, deriv g1 x := hftc.symm
    _ ≤ ∫ x in Set.Iic u, |deriv g1 x| :=
        integral_mono hg'_int.integrableOn hg'_int.norm.integrableOn fun x => le_abs_self _
    _ ≤ ∫ w : ℝ, |deriv g1 w| :=
        setIntegral_le_integral hg'_int.norm (ae_of_all _ fun w => abs_nonneg _)

private lemma ep_conv_pdf_pos (f g : Density 1)
    (hg_pos : ∀ y : ℝ, 0 < g.pdf (fun _ => y))
    (hg_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => g.pdf (fun _ => t)) y)
    (hg'_int : Integrable (deriv (fun t : ℝ => g.pdf (fun _ => t))) volume) (z : ℝ) :
    0 < (convDensity f g).pdf (fun _ => z) := by
  rw [convDensity_pdf_eq]
  have hf1_int : Integrable (fun x : ℝ => f.pdf (fun _ => x)) volume := ep_pdf1_integrable f
  have hg1_cont : Continuous (fun x : ℝ => g.pdf (fun _ => x)) :=
    continuous_iff_continuousAt.mpr fun y => (hg_diff y).continuousAt
  have hint_z : Integrable (fun x : ℝ => f.pdf (fun _ => x) * g.pdf (fun _ => z - x)) volume := by
    have hdom := hf1_int.const_mul (∫ w : ℝ, |deriv (fun t : ℝ => g.pdf (fun _ => t)) w|)
    refine hdom.mono' (hf1_int.aestronglyMeasurable.mul
        (hg1_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (g.nonneg _))]
    have hle := ep_pdf_le_integral_abs_deriv g hg_diff hg'_int (z - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hnn : 0 ≤ ∫ x : ℝ, f.pdf (fun _ => x) * g.pdf (fun _ => z - x) :=
    integral_nonneg fun x => mul_nonneg (f.nonneg _) (g.nonneg _)
  rcases lt_or_eq_of_le hnn with hlt | h0
  · exact hlt
  · exfalso
    have hae0 : (fun x : ℝ => f.pdf (fun _ => x) * g.pdf (fun _ => z - x)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (f.nonneg _) (g.nonneg _)) hint_z).mp h0.symm
    have hf0 : (fun x : ℝ => f.pdf (fun _ => x)) =ᵐ[volume] 0 := hae0.mono fun x hx =>
      (mul_eq_zero.mp hx).resolve_right (ne_of_gt (hg_pos (z - x)))
    have h1_zero : ∫ x : ℝ, f.pdf (fun _ => x) = 0 := by simpa using integral_congr_ae hf0
    linarith [ep_pdf1_integral_one f]

private lemma ep_hasDerivAt_conv_right (f g : Density 1)
    (hg_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => g.pdf (fun _ => t)) y)
    (hg'_int : Integrable (deriv (fun t : ℝ => g.pdf (fun _ => t))) volume)
    (hg'_bdd : ∃ C : ℝ, ∀ y : ℝ, |deriv (fun t : ℝ => g.pdf (fun _ => t)) y| ≤ C) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (convDensity f g).pdf (fun _ => w))
      (∫ x : ℝ, f.pdf (fun _ => x) * deriv (fun t : ℝ => g.pdf (fun _ => t)) (z - x)) z := by
  have hrew : (fun w : ℝ => (convDensity f g).pdf (fun _ => w)) =
      fun w : ℝ => ∫ x : ℝ, f.pdf (fun _ => x) * g.pdf (fun _ => w - x) :=
    funext (convDensity_pdf_eq f g)
  rw [hrew]
  rcases hg'_bdd with ⟨Cg, hCg⟩
  let F : ℝ → ℝ → ℝ := fun w x => f.pdf (fun _ => x) * g.pdf (fun _ => w - x)
  let F' : ℝ → ℝ → ℝ := fun w x => f.pdf (fun _ => x) * deriv (fun t : ℝ => g.pdf (fun _ => t)) (w - x)
  have hf1_int : Integrable (fun x : ℝ => f.pdf (fun _ => x)) volume := ep_pdf1_integrable f
  have hg1_cont : Continuous (fun x : ℝ => g.pdf (fun _ => x)) :=
    continuous_iff_continuousAt.mpr fun y => (hg_diff y).continuousAt
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume :=
    Filter.Eventually.of_forall fun w =>
      hf1_int.aestronglyMeasurable.mul
        (hg1_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (F z) volume := by
    have hdom := hf1_int.const_mul (∫ w : ℝ, |deriv (fun t : ℝ => g.pdf (fun _ => t)) w|)
    refine hdom.mono' (hf1_int.aestronglyMeasurable.mul
        (hg1_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    dsimp only [F]
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (g.nonneg _))]
    have hle := ep_pdf_le_integral_abs_deriv g hg_diff hg'_int (z - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have hF'_meas : AEStronglyMeasurable (F' z) volume :=
    hf1_int.aestronglyMeasurable.mul
      ((measurable_deriv (fun t : ℝ => g.pdf (fun _ => t))).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂volume, ∀ w ∈ (Set.univ : Set ℝ), ‖F' w x‖ ≤ Cg * f.pdf (fun _ => x) := by
    refine ae_of_all _ fun x w _ => ?_
    dsimp only [F']
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (f.nonneg _)]
    have hle := hCg (w - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  have h_diff : ∀ᵐ x ∂volume, ∀ w ∈ (Set.univ : Set ℝ), HasDerivAt (F · x) (F' w x) w := by
    refine ae_of_all _ fun x w _ => ?_
    have hsub : HasDerivAt (fun u : ℝ => u - x) 1 w := by simpa using (hasDerivAt_id w).sub_const x
    have hcomp := (hg_diff (w - x)).hasDerivAt.comp w hsub
    simpa [F, F'] using hcomp.const_mul (f.pdf (fun _ => x))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (s := Set.univ)
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound (hf1_int.const_mul Cg) h_diff).2

private lemma ep_hasDerivAt_conv_left (f g : Density 1)
    (hf_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => f.pdf (fun _ => t)) y)
    (hf'_int : Integrable (deriv (fun t : ℝ => f.pdf (fun _ => t))) volume)
    (hf'_bdd : ∃ C : ℝ, ∀ y : ℝ, |deriv (fun t : ℝ => f.pdf (fun _ => t)) y| ≤ C) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (convDensity f g).pdf (fun _ => w))
      (∫ x : ℝ, deriv (fun t : ℝ => f.pdf (fun _ => t)) x * g.pdf (fun _ => z - x)) z := by
  have hcomm : convDensity f g = convDensity g f := convDensity_comm f g
  rw [hcomm]
  have hd := ep_hasDerivAt_conv_right g f hf_diff hf'_int hf'_bdd z
  refine hd.congr_deriv ?_
  exact (ep_conv_fun_comm (deriv (fun t : ℝ => f.pdf (fun _ => t))) (fun y => g.pdf (fun _ => y)) z).symm

/-- **Weighted Blachman–Stam Inequality** (Blachman 1965):
    for any two strictly positive differentiable densities `f, g` with bounded integrable
    derivatives and finite Fisher information, and any `α, β ∈ ℝ` with `α + β = 1`,
    `J(f * g) ≤ α² J(f) + β² J(g)`. -/
theorem stam_weighted_inequality (f g : Density 1)
    (hf_pos : ∀ y : ℝ, 0 < f.pdf (fun _ => y))
    (hg_pos : ∀ y : ℝ, 0 < g.pdf (fun _ => y))
    (hf_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => f.pdf (fun _ => t)) y)
    (hg_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => g.pdf (fun _ => t)) y)
    (hf'_int : Integrable (deriv (fun t : ℝ => f.pdf (fun _ => t))) volume)
    (hg'_int : Integrable (deriv (fun t : ℝ => g.pdf (fun _ => t))) volume)
    (hf'_bdd : ∃ C : ℝ, ∀ y : ℝ, |deriv (fun t : ℝ => f.pdf (fun _ => t)) y| ≤ C)
    (hg'_bdd : ∃ C : ℝ, ∀ y : ℝ, |deriv (fun t : ℝ => g.pdf (fun _ => t)) y| ≤ C)
    (hfJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => f.pdf (fun _ => t)) y) ^ 2 / f.pdf (fun _ => y)) volume)
    (hgJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => g.pdf (fun _ => t)) y) ^ 2 / g.pdf (fun _ => y)) volume)
    {α β : ℝ} (hαβ : α + β = 1) :
    fisherInfo (convDensity f g) ≤ α ^ 2 * fisherInfo f + β ^ 2 * fisherInfo g := by
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  let g1 : ℝ → ℝ := fun x => g.pdf (fun _ => x)
  let f1' : ℝ → ℝ := deriv f1
  let g1' : ℝ → ℝ := deriv g1
  let h1 : ℝ → ℝ := fun z => (convDensity f g).pdf (fun _ => z)
  have hf1_int : Integrable f1 volume := ep_pdf1_integrable f
  have hg1_int : Integrable g1 volume := ep_pdf1_integrable g
  have hh_pos : ∀ z : ℝ, 0 < h1 z := ep_conv_pdf_pos f g hg_pos hg_diff hg'_int
  have hh_deriv_g : ∀ z : ℝ, HasDerivAt h1 (∫ x : ℝ, f1 x * g1' (z - x)) z :=
    ep_hasDerivAt_conv_right f g hg_diff hg'_int hg'_bdd
  have hh_deriv_f : ∀ z : ℝ, HasDerivAt h1 (∫ x : ℝ, f1' x * g1 (z - x)) z :=
    ep_hasDerivAt_conv_left f g hf_diff hf'_int hf'_bdd
  let prod1 : ℝ × ℝ → ℝ := fun p => (α ^ 2 * ((f1' p.2) ^ 2 / f1 p.2)) * g1 (p.1 - p.2)
  let prod2 : ℝ × ℝ → ℝ := fun p => ((2 * α * β) * f1' p.2) * g1' (p.1 - p.2)
  let prod3 : ℝ × ℝ → ℝ := fun p => f1 p.2 * (β ^ 2 * ((g1' (p.1 - p.2)) ^ 2 / g1 (p.1 - p.2)))
  have hp1 : Integrable prod1 (volume.prod volume) :=
    ep_integrable_prod_shear (hfJ_int.const_mul (α ^ 2)) hg1_int
  have hp2 : Integrable prod2 (volume.prod volume) :=
    ep_integrable_prod_shear (hf'_int.const_mul (2 * α * β)) hg'_int
  have hp3 : Integrable prod3 (volume.prod volume) :=
    ep_integrable_prod_shear hf1_int (hgJ_int.const_mul (β ^ 2))
  let Q : ℝ → ℝ := fun z =>
    (∫ x : ℝ, prod1 (z, x)) + (∫ x : ℝ, prod2 (z, x)) + (∫ x : ℝ, prod3 (z, x))
  have hQ1 : Integrable (fun z : ℝ => ∫ x : ℝ, prod1 (z, x)) volume := hp1.integral_prod_left
  have hQ2 : Integrable (fun z : ℝ => ∫ x : ℝ, prod2 (z, x)) volume := hp2.integral_prod_left
  have hQ3 : Integrable (fun z : ℝ => ∫ x : ℝ, prod3 (z, x)) volume := hp3.integral_prod_left
  have hQ12 : Integrable (fun z : ℝ => (∫ x : ℝ, prod1 (z, x)) + (∫ x : ℝ, prod2 (z, x))) volume :=
    hQ1.add hQ2
  have hQ_int : Integrable Q volume := hQ12.add hQ3
  have hf'_zero : ∫ x : ℝ, f1' x = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable (fun x => (hf_diff x).hasDerivAt) hf'_int hf1_int
  have hQ_val : ∫ z : ℝ, Q z = α ^ 2 * fisherInfo f + β ^ 2 * fisherInfo g := by
    dsimp only [Q]
    rw [integral_add hQ12 hQ3, integral_add hQ1 hQ2]
    have hI1 : ∫ z : ℝ, ∫ x : ℝ, prod1 (z, x) = α ^ 2 * fisherInfo f := by
      dsimp only [prod1]
      rw [ep_integral_conv_fun (hfJ_int.const_mul (α ^ 2)) hg1_int, integral_const_mul,
        ep_pdf1_integral_one g, mul_one]; rfl
    have hI2 : ∫ z : ℝ, ∫ x : ℝ, prod2 (z, x) = 0 := by
      dsimp only [prod2]
      rw [ep_integral_conv_fun (hf'_int.const_mul (2 * α * β)) hg'_int, integral_const_mul,
        hf'_zero, mul_zero, zero_mul]
    have hI3 : ∫ z : ℝ, ∫ x : ℝ, prod3 (z, x) = β ^ 2 * fisherInfo g := by
      dsimp only [prod3]
      rw [ep_integral_conv_fun hf1_int (hgJ_int.const_mul (β ^ 2)), integral_const_mul,
        ep_pdf1_integral_one f, one_mul]; rfl
    rw [hI1, hI2, hI3, add_zero]
  have hae_fg : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => f1 x * g1 (z - x)) volume :=
    (ep_integrable_prod_shear hf1_int hg1_int).prod_right_ae
  have hae_f'g : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => f1' x * g1 (z - x)) volume :=
    (ep_integrable_prod_shear hf'_int hg1_int).prod_right_ae
  have hae_fg' : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => f1 x * g1' (z - x)) volume :=
    (ep_integrable_prod_shear hf1_int hg'_int).prod_right_ae
  have hae_p1 : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => prod1 (z, x)) volume := hp1.prod_right_ae
  have hae_p2 : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => prod2 (z, x)) volume := hp2.prod_right_ae
  have hae_p3 : ∀ᵐ z : ℝ, Integrable (fun x : ℝ => prod3 (z, x)) volume := hp3.prod_right_ae
  have hpt_ae : ∀ᵐ z : ℝ, (deriv h1 z) ^ 2 / h1 z ≤ Q z := by
    filter_upwards [hae_fg, hae_f'g, hae_fg', hae_p1, hae_p2, hae_p3] with z hfg hf'g hfg' hi1 hi2 hi3
    have h_h1 : h1 z = ∫ x : ℝ, f1 x * g1 (z - x) := convDensity_pdf_eq f g z
    have h_df : deriv h1 z = ∫ x : ℝ, f1' x * g1 (z - x) := (hh_deriv_f z).deriv
    have h_dg : deriv h1 z = ∫ x : ℝ, f1 x * g1' (z - x) := (hh_deriv_g z).deriv
    have h_comb : deriv h1 z = ∫ x : ℝ, (α * (f1' x * g1 (z - x)) + β * (f1 x * g1' (z - x))) := by
      rw [integral_add (hf'g.const_mul α) (hfg'.const_mul β), integral_const_mul, integral_const_mul,
        ← h_df, ← h_dg]
      have : α * deriv h1 z + β * deriv h1 z = (α + β) * deriv h1 z := by ring
      rw [this, hαβ, one_mul]
    set lam : ℝ := -(deriv h1 z) / h1 z
    have hquad_nn : 0 ≤ ∫ x : ℝ,
        (lam ^ 2 * (f1 x * g1 (z - x)) +
         (2 * lam) * (α * (f1' x * g1 (z - x)) + β * (f1 x * g1' (z - x))) +
         (prod1 (z, x) + prod2 (z, x) + prod3 (z, x))) := by
      refine integral_nonneg fun x => ?_
      have hfp : 0 < f1 x := hf_pos x
      have hgp : 0 < g1 (z - x) := hg_pos (z - x)
      have hfne : f1 x ≠ 0 := ne_of_gt hfp
      have hgne : g1 (z - x) ≠ 0 := ne_of_gt hgp
      have heq : lam ^ 2 * (f1 x * g1 (z - x)) +
          (2 * lam) * (α * (f1' x * g1 (z - x)) + β * (f1 x * g1' (z - x))) +
          (prod1 (z, x) + prod2 (z, x) + prod3 (z, x)) =
          (lam + α * (f1' x / f1 x) + β * (g1' (z - x) / g1 (z - x))) ^ 2 * (f1 x * g1 (z - x)) := by
        dsimp only [prod1, prod2, prod3]
        field_simp [hfne, hgne]
        ring
      rw [heq]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg hfp.le hgp.le)
    have hcomb_int : Integrable (fun x : ℝ => α * (f1' x * g1 (z - x)) + β * (f1 x * g1' (z - x))) volume :=
      (hf'g.const_mul α).add (hfg'.const_mul β)
    have hiQ12 : Integrable (fun x : ℝ => prod1 (z, x) + prod2 (z, x)) volume := hi1.add hi2
    have hiQ : Integrable (fun x : ℝ => prod1 (z, x) + prod2 (z, x) + prod3 (z, x)) volume := hiQ12.add hi3
    have hi0 : Integrable (fun x : ℝ => lam ^ 2 * (f1 x * g1 (z - x))) volume := hfg.const_mul (lam ^ 2)
    have hi_c : Integrable (fun x : ℝ => (2 * lam) * (α * (f1' x * g1 (z - x)) + β * (f1 x * g1' (z - x)))) volume :=
      hcomb_int.const_mul (2 * lam)
    have hi01 : Integrable (fun x : ℝ =>
        lam ^ 2 * (f1 x * g1 (z - x)) +
        (2 * lam) * (α * (f1' x * g1 (z - x)) + β * (f1 x * g1' (z - x)))) volume := hi0.add hi_c
    rw [integral_add hi01 hiQ, integral_add hi0 hi_c, integral_add hiQ12 hi3, integral_add hi1 hi2,
      integral_const_mul, integral_const_mul, ← h_h1, ← h_comb] at hquad_nn
    have hsimp : lam ^ 2 * h1 z + (2 * lam) * deriv h1 z = -((deriv h1 z) ^ 2 / h1 z) := by
      dsimp only [lam]
      have hhne : h1 z ≠ 0 := ne_of_gt (hh_pos z)
      field_simp [hhne]; ring
    dsimp only [Q]
    linarith
  have hh1_cont : Continuous h1 :=
    continuous_iff_continuousAt.mpr fun z => (hh_deriv_g z).continuousAt
  have hh_score_int : Integrable (fun z : ℝ => (deriv h1 z) ^ 2 / h1 z) volume := by
    refine hQ_int.mono' ?_ (hpt_ae.mono fun z hz => ?_)
    · exact (((measurable_deriv h1).pow_const 2).div hh1_cont.measurable).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (hh_pos z).le)]
      exact hz
  change ∫ z : ℝ, (deriv h1 z) ^ 2 / h1 z ≤ α ^ 2 * fisherInfo f + β ^ 2 * fisherInfo g
  rw [← hQ_val]
  exact integral_mono_ae hh_score_int hQ_int hpt_ae

/-- **Stam's Fisher Information Inequality** (Cover & Thomas Theorem 17.7.2; Stam 1959):
    for independent `X ~ f`, `Y ~ g` with strictly positive differentiable densities,
    bounded integrable derivatives, and finite Fisher information,
    `1 / J(X) + 1 / J(Y) ≤ 1 / J(X + Y)`. -/
theorem stam_inequality (f g : Density 1)
    (hf_pos : ∀ y : ℝ, 0 < f.pdf (fun _ => y))
    (hg_pos : ∀ y : ℝ, 0 < g.pdf (fun _ => y))
    (hf_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => f.pdf (fun _ => t)) y)
    (hg_diff : ∀ y : ℝ, DifferentiableAt ℝ (fun t : ℝ => g.pdf (fun _ => t)) y)
    (hf'_int : Integrable (deriv (fun t : ℝ => f.pdf (fun _ => t))) volume)
    (hg'_int : Integrable (deriv (fun t : ℝ => g.pdf (fun _ => t))) volume)
    (hf'_bdd : ∃ C : ℝ, ∀ y : ℝ, |deriv (fun t : ℝ => f.pdf (fun _ => t)) y| ≤ C)
    (hg'_bdd : ∃ C : ℝ, ∀ y : ℝ, |deriv (fun t : ℝ => g.pdf (fun _ => t)) y| ≤ C)
    (hfJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => f.pdf (fun _ => t)) y) ^ 2 / f.pdf (fun _ => y)) volume)
    (hgJ_int : Integrable (fun y : ℝ =>
      (deriv (fun t : ℝ => g.pdf (fun _ => t)) y) ^ 2 / g.pdf (fun _ => y)) volume)
    (hJfg_pos : 0 < fisherInfo (convDensity f g)) :
    1 / fisherInfo f + 1 / fisherInfo g ≤ 1 / fisherInfo (convDensity f g) := by
  have hJf_pos : 0 < fisherInfo f :=
    fisherInfo_pos_of_pos_diff f hf_pos hf_diff hfJ_int hf'_int
  have hJg_pos : 0 < fisherInfo g :=
    fisherInfo_pos_of_pos_diff g hg_pos hg_diff hgJ_int hg'_int
  have hsum_pos : 0 < fisherInfo f + fisherInfo g := add_pos hJf_pos hJg_pos
  let α : ℝ := fisherInfo g / (fisherInfo f + fisherInfo g)
  let β : ℝ := fisherInfo f / (fisherInfo f + fisherInfo g)
  have hαβ : α + β = 1 := by
    dsimp only [α, β]
    field_simp [ne_of_gt hsum_pos]
    ring
  have hw := stam_weighted_inequality f g hf_pos hg_pos hf_diff hg_diff hf'_int hg'_int
    hf'_bdd hg'_bdd hfJ_int hgJ_int hαβ
  have hrhs : α ^ 2 * fisherInfo f + β ^ 2 * fisherInfo g =
      fisherInfo f * fisherInfo g / (fisherInfo f + fisherInfo g) := by
    dsimp only [α, β]
    field_simp [ne_of_gt hsum_pos]
    ring
  rw [hrhs] at hw
  have hfg_inv : 1 / fisherInfo f + 1 / fisherInfo g =
      (fisherInfo f + fisherInfo g) / (fisherInfo f * fisherInfo g) := by
    field_simp [ne_of_gt hJf_pos, ne_of_gt hJg_pos]
    ring
  rw [hfg_inv, div_le_div_iff₀ (mul_pos hJf_pos hJg_pos) hJfg_pos, one_mul]
  have hmul := mul_le_mul_of_nonneg_left hw hsum_pos.le
  rw [mul_div_cancel₀ _ (ne_of_gt hsum_pos)] at hmul
  linarith

/-- Weighted Blachman–Stam inequality for any two Gaussian-smoothed densities `f_a, g_b`. -/
theorem stam_weighted_inequality_awgn (f g : Density 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {α β : ℝ} (hαβ : α + β = 1) :
    fisherInfo (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)) ≤
      α ^ 2 * fisherInfo (awgnOutputDensity f a ha) +
        β ^ 2 * fisherInfo (awgnOutputDensity g b hb) :=
  stam_weighted_inequality (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)
    (awgnOutputDensity_pdf_pos f ha) (awgnOutputDensity_pdf_pos g hb)
    (fun y => (hasDerivAt_awgnOutputDensity_pdf f ha y).differentiableAt)
    (fun y => (hasDerivAt_awgnOutputDensity_pdf g hb y).differentiableAt)
    (ep_integrable_deriv_awgn f ha) (ep_integrable_deriv_awgn g hb)
    (ep_bdd_deriv_awgn f ha) (ep_bdd_deriv_awgn g hb)
    (ep_integrable_fisherInfo_awgn f ha) (ep_integrable_fisherInfo_awgn g hb) hαβ

/-- **Stam's Inequality for Gaussian-Smoothed Densities** (no regularity hypotheses needed):
    `1 / J(f_a) + 1 / J(g_b) ≤ 1 / J(f_a * g_b)` for all `a, b > 0`. -/
theorem stam_inequality_awgn (f g : Density 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / fisherInfo (awgnOutputDensity f a ha) + 1 / fisherInfo (awgnOutputDensity g b hb) ≤
      1 / fisherInfo (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)) := by
  have hJfg_pos : 0 < fisherInfo (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)) := by
    rw [convDensity_awgn f g ha hb]
    exact fisherInfo_pos_of_pos_diff _
      (awgnOutputDensity_pdf_pos (convDensity f g) (add_pos ha hb))
      (fun y => (hasDerivAt_awgnOutputDensity_pdf (convDensity f g) (add_pos ha hb) y).differentiableAt)
      (ep_integrable_fisherInfo_awgn (convDensity f g) (add_pos ha hb))
      (ep_integrable_deriv_awgn (convDensity f g) (add_pos ha hb))
  exact stam_inequality (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)
    (awgnOutputDensity_pdf_pos f ha) (awgnOutputDensity_pdf_pos g hb)
    (fun y => (hasDerivAt_awgnOutputDensity_pdf f ha y).differentiableAt)
    (fun y => (hasDerivAt_awgnOutputDensity_pdf g hb y).differentiableAt)
    (ep_integrable_deriv_awgn f ha) (ep_integrable_deriv_awgn g hb)
    (ep_bdd_deriv_awgn f ha) (ep_bdd_deriv_awgn g hb)
    (ep_integrable_fisherInfo_awgn f ha) (ep_integrable_fisherInfo_awgn g hb) hJfg_pos

/-! ### Section 3: De Bruijn's Identity (Cover & Thomas Thm. 17.7.1) -/

private lemma ep_exists_radius_mass_ge_half (f : Density 1) (hm2 : HasFiniteSecondMoment f) :
    ∃ R : ℝ, 0 < R ∧ (1 / 2 : ℝ) ≤ ∫ x in Set.Icc (-R) R, f.pdf (fun _ => x) := by
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hm2_int : Integrable (fun x : ℝ => x ^ 2 * f1 x) volume := ep_secondMoment_integrable f hm2
  set M2 : ℝ := ∫ x : ℝ, x ^ 2 * f1 x
  have hM2_nn : 0 ≤ M2 := integral_nonneg fun x => mul_nonneg (sq_nonneg x) (f.nonneg _)
  set R : ℝ := Real.sqrt (2 * M2 + 1)
  have hR2 : R ^ 2 = 2 * M2 + 1 := Real.sq_sqrt (by linarith)
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by linarith)
  refine ⟨R, hR_pos, ?_⟩
  have hsplit : (∫ x in Set.Icc (-R) R, f1 x) + (∫ x in (Set.Icc (-R) R)ᶜ, f1 x) = 1 := by
    rw [integral_add_compl measurableSet_Icc hf1]
    exact ep_pdf1_integral_one f
  have htail : ∫ x in (Set.Icc (-R) R)ᶜ, f1 x ≤ 1 / 2 := by
    have hpt : ∀ x ∈ (Set.Icc (-R) R)ᶜ, f1 x ≤ (1 / R ^ 2) * (x ^ 2 * f1 x) := by
      intro x hx
      have hRx : R ^ 2 ≤ x ^ 2 := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hlt | hgt <;> nlinarith
      have h1 : 1 ≤ x ^ 2 / R ^ 2 := (one_le_div (by positivity)).mpr hRx
      have hfnn : 0 ≤ f1 x := f.nonneg _
      calc f1 x = 1 * f1 x := (one_mul _).symm
        _ ≤ (x ^ 2 / R ^ 2) * f1 x := mul_le_mul_of_nonneg_right h1 hfnn
        _ = (1 / R ^ 2) * (x ^ 2 * f1 x) := by ring
    have hmono : ∫ x in (Set.Icc (-R) R)ᶜ, f1 x ≤
        ∫ x in (Set.Icc (-R) R)ᶜ, (1 / R ^ 2) * (x ^ 2 * f1 x) :=
      setIntegral_mono_on hf1.integrableOn (hm2_int.const_mul (1 / R ^ 2)).integrableOn
        measurableSet_Icc.compl hpt
    have hfull : ∫ x in (Set.Icc (-R) R)ᶜ, (1 / R ^ 2) * (x ^ 2 * f1 x) ≤
        ∫ x : ℝ, (1 / R ^ 2) * (x ^ 2 * f1 x) :=
      setIntegral_le_integral (hm2_int.const_mul (1 / R ^ 2))
        (ae_of_all _ fun x => mul_nonneg (by positivity) (mul_nonneg (sq_nonneg x) (f.nonneg _)))
    conv_rhs at hfull => rw [integral_const_mul]
    have hfrac : (1 / R ^ 2) * M2 ≤ 1 / 2 := by
      rw [hR2]
      have hden : 0 < 2 * M2 + 1 := by linarith
      rw [one_div_mul_eq_div, div_le_iff₀ hden]
      linarith
    exact le_trans (le_trans hmono hfull) hfrac
  linarith

private lemma ep_awgn_pdf_lower_bound (f : Density 1) {R t1 t2 t : ℝ}
    (hR : 0 < R) (hmass : (1 / 2 : ℝ) ≤ ∫ x in Set.Icc (-R) R, f.pdf (fun _ => x))
    (ht1 : 0 < t1) (h1t : t1 ≤ t) (ht2 : t ≤ t2) (ht : 0 < t) (y : ℝ) :
    (1 / (2 * Real.sqrt (2 * Real.pi * t2))) * Real.exp (-(y ^ 2 + R ^ 2) / t1) ≤
      (awgnOutputDensity f t ht).pdf (fun _ => y) := by
  have hrew : (awgnOutputDensity f t ht).pdf (fun _ => y) =
      ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) := by
    rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]; rfl
  rw [hrew]
  have hf1 : Integrable (fun x : ℝ => f.pdf (fun _ => x)) volume := ep_pdf1_integrable f
  have hint_full : Integrable (fun x : ℝ => f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) volume := by
    have hdom := hf1.const_mul (1 / Real.sqrt (2 * Real.pi * t))
    refine hdom.mono' (hf1.aestronglyMeasurable.mul
        ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
    have hle := ep_gaussianPdf1D_le_const ht (y - x)
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    nlinarith
  let c : ℝ := (1 / Real.sqrt (2 * Real.pi * t2)) * Real.exp (-(y ^ 2 + R ^ 2) / t1)
  have hc_le : ∀ x ∈ Set.Icc (-R) R, c ≤ gaussianPdf1D t (y - x) := by
    intro x hx
    unfold gaussianPdf1D
    dsimp only [c]
    have hpi : 2 * Real.pi * t ≤ 2 * Real.pi * t2 :=
      mul_le_mul_of_nonneg_left ht2 (by positivity)
    have hpref : 1 / Real.sqrt (2 * Real.pi * t2) ≤ 1 / Real.sqrt (2 * Real.pi * t) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hpi)
    have hx2 : x ^ 2 ≤ R ^ 2 := by
      rcases hx with ⟨h1, h2⟩
      nlinarith
    have hyx : (y - x) ^ 2 ≤ 2 * (y ^ 2 + R ^ 2) := by
      have : 0 ≤ (y + x) ^ 2 := sq_nonneg _
      nlinarith
    have hexp_arg : -(y ^ 2 + R ^ 2) / t1 ≤ -((y - x) ^ 2) / (2 * t) := by
      have h1 : (y - x) ^ 2 / (2 * t) ≤ (y ^ 2 + R ^ 2) / t1 := by
        calc (y - x) ^ 2 / (2 * t)
            ≤ (2 * (y ^ 2 + R ^ 2)) / (2 * t) := div_le_div_of_nonneg_right hyx (by positivity)
          _ = (y ^ 2 + R ^ 2) / t := by
              have ht0 : t ≠ 0 := ne_of_gt ht; field_simp [ht0]
          _ ≤ (y ^ 2 + R ^ 2) / t1 := div_le_div_of_nonneg_left (by positivity) ht1 h1t
      have hl : -(y ^ 2 + R ^ 2) / t1 = -((y ^ 2 + R ^ 2) / t1) := by ring
      have hr : -((y - x) ^ 2) / (2 * t) = -((y - x) ^ 2 / (2 * t)) := by ring
      linarith
    exact mul_le_mul hpref (Real.exp_le_exp.mpr hexp_arg) (Real.exp_pos _).le (by positivity)
  have h1 : (1 / 2 : ℝ) * c ≤ ∫ x in Set.Icc (-R) R, f.pdf (fun _ => x) * c := by
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hmass (by positivity)
  have h2 : ∫ x in Set.Icc (-R) R, f.pdf (fun _ => x) * c ≤
      ∫ x in Set.Icc (-R) R, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) :=
    setIntegral_mono_on (hf1.mul_const c).integrableOn hint_full.integrableOn measurableSet_Icc
      fun x hx => mul_le_mul_of_nonneg_left (hc_le x hx) (f.nonneg _)
  have h3 : ∫ x in Set.Icc (-R) R, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) ≤
      ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) :=
    setIntegral_le_integral hint_full
      (ae_of_all _ fun x => mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))
  have hlhs : (1 / (2 * Real.sqrt (2 * Real.pi * t2))) * Real.exp (-(y ^ 2 + R ^ 2) / t1) =
      (1 / 2 : ℝ) * c := by dsimp only [c]; ring
  rw [hlhs]
  exact le_trans (le_trans h1 h2) h3

private lemma ep_abs_log_awgn_pdf_le (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t1 t2 : ℝ} (ht1 : 0 < t1) (h12 : t1 ≤ t2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ {t : ℝ} (ht : 0 < t), t1 ≤ t → t ≤ t2 → ∀ y : ℝ,
        |Real.log ((awgnOutputDensity f t ht).pdf (fun _ => y))| ≤ A + B * y ^ 2 := by
  obtain ⟨R, hR, hmass⟩ := ep_exists_radius_mass_ge_half f hm2
  let c1 : ℝ := |Real.log (1 / Real.sqrt (2 * Real.pi * t1))|
  let c2 : ℝ := |Real.log (1 / (2 * Real.sqrt (2 * Real.pi * t2)))|
  refine ⟨c1 + c2 + R ^ 2 / t1, 1 / t1, by positivity, by positivity, ?_⟩
  intro t ht h1t ht2 y
  have hp_pos : 0 < (awgnOutputDensity f t ht).pdf (fun _ => y) := awgnOutputDensity_pdf_pos f ht y
  have hupper : (awgnOutputDensity f t ht).pdf (fun _ => y) ≤ 1 / Real.sqrt (2 * Real.pi * t1) := by
    have hrew : (awgnOutputDensity f t ht).pdf (fun _ => y) =
        ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) := by
      rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]; rfl
    rw [hrew]
    have hf1 := ep_pdf1_integrable f
    have hint : Integrable (fun x : ℝ => f.pdf (fun _ => x) * gaussianPdf1D t (y - x)) volume := by
      have hdom := hf1.const_mul (1 / Real.sqrt (2 * Real.pi * t))
      refine hdom.mono' (hf1.aestronglyMeasurable.mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
      have hle := ep_gaussianPdf1D_le_const ht (y - x)
      have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
      nlinarith
    have hle1 : ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D t (y - x) ≤
        ∫ x : ℝ, f.pdf (fun _ => x) * (1 / Real.sqrt (2 * Real.pi * t1)) := by
      refine integral_mono hint (hf1.mul_const _) fun x => ?_
      have hg1 := ep_gaussianPdf1D_le_const ht (y - x)
      have hg2 : 1 / Real.sqrt (2 * Real.pi * t) ≤ 1 / Real.sqrt (2 * Real.pi * t1) :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1t (by positivity)))
      exact mul_le_mul_of_nonneg_left (le_trans hg1 hg2) (f.nonneg _)
    rw [integral_mul_const, ep_pdf1_integral_one f, one_mul] at hle1
    exact hle1
  have hlower := ep_awgn_pdf_lower_bound f hR hmass ht1 h1t ht2 ht y
  have hlog_up : Real.log ((awgnOutputDensity f t ht).pdf (fun _ => y)) ≤ c1 := by
    have h := Real.log_le_log hp_pos hupper
    exact le_trans h (le_abs_self _)
  have hlog_lo : -(c2 + R ^ 2 / t1 + (1 / t1) * y ^ 2) ≤
      Real.log ((awgnOutputDensity f t ht).pdf (fun _ => y)) := by
    have h2pos : 0 < 2 * Real.sqrt (2 * Real.pi * t2) := by
      have : 0 < t2 := lt_of_lt_of_le ht1 h12
      positivity
    have hlog := Real.log_le_log (by positivity) hlower
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hneg_c2 : -c2 ≤ Real.log (1 / (2 * Real.sqrt (2 * Real.pi * t2))) := neg_abs_le _
    have hsplit : -(y ^ 2 + R ^ 2) / t1 = -(R ^ 2 / t1) - (1 / t1) * y ^ 2 := by ring
    linarith
  rw [abs_le]
  constructor
  · have : 0 ≤ c1 := abs_nonneg _
    linarith
  · have : 0 ≤ c2 := abs_nonneg _
    have : 0 ≤ R ^ 2 / t1 := by positivity
    have : 0 ≤ (1 / t1) * y ^ 2 := by positivity
    linarith

/-- Every Gaussian-smoothed density `f_t` (`t > 0`) of a finite-second-moment density `f`
    has finite differential entropy. -/
theorem hasFiniteDiffEntropy_awgnOutputDensity (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t : ℝ} (ht : 0 < t) :
    HasFiniteDiffEntropy (awgnOutputDensity f t ht) := by
  unfold HasFiniteDiffEntropy
  rw [ep_integrable_fin1_iff]
  obtain ⟨A, B, hA, hB, hlog⟩ := ep_abs_log_awgn_pdf_le f hm2 ht le_rfl
  let p : ℝ → ℝ := fun y => (awgnOutputDensity f t ht).pdf (fun _ => y)
  have hp_int : Integrable p volume := ep_pdf1_integrable (awgnOutputDensity f t ht)
  have hp2_int : Integrable (fun y : ℝ => y ^ 2 * p y) volume :=
    ep_secondMoment_integrable (awgnOutputDensity f t ht)
      (hasFiniteSecondMoment_awgnOutputDensity f hm2 ht)
  have hdom : Integrable (fun y : ℝ => A * p y + B * (y ^ 2 * p y)) volume :=
    (hp_int.const_mul A).add (hp2_int.const_mul B)
  have hp_cont : Continuous p :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).continuousAt
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => if p y ≤ 0 then (0 : ℝ) else -p y * Real.log (p y)) volume := by
    have heq : (fun y : ℝ => if p y ≤ 0 then (0 : ℝ) else -p y * Real.log (p y)) =
        fun y : ℝ => -p y * Real.log (p y) := by
      funext y
      exact ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr (awgnOutputDensity_pdf_pos f ht y))
    rw [heq]
    exact (hp_cont.neg.mul (hp_cont.log fun y => ne_of_gt (awgnOutputDensity_pdf_pos f ht y))).aestronglyMeasurable
  refine hdom.mono' hmeas (ae_of_all _ fun y => ?_)
  have hp_pos : 0 < p y := awgnOutputDensity_pdf_pos f ht y
  rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hp_pos)),
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp_pos]
  have hle := hlog ht le_rfl le_rfl y
  nlinarith

private lemma ep_gaussianPdf1D_le_of_le {t1 t2 t : ℝ} (ht1 : 0 < t1) (h1t : t1 ≤ t) (ht2 : t ≤ t2)
    (u : ℝ) :
    gaussianPdf1D t u ≤ Real.sqrt (t2 / t1) * gaussianPdf1D t2 u := by
  unfold gaussianPdf1D
  have ht_pos : 0 < t := lt_of_lt_of_le ht1 h1t
  have ht2_pos : 0 < t2 := lt_of_lt_of_le ht_pos ht2
  have hexp : Real.exp (-(u ^ 2) / (2 * t)) ≤ Real.exp (-(u ^ 2) / (2 * t2)) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv : u ^ 2 / (2 * t2) ≤ u ^ 2 / (2 * t) :=
      div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)
    have h1 : -(u ^ 2) / (2 * t) = -(u ^ 2 / (2 * t)) := by ring
    have h2 : -(u ^ 2) / (2 * t2) = -(u ^ 2 / (2 * t2)) := by ring
    linarith
  have hpref : 1 / Real.sqrt (2 * Real.pi * t) ≤
      Real.sqrt (t2 / t1) * (1 / Real.sqrt (2 * Real.pi * t2)) := by
    have hsqrt_div : Real.sqrt (t2 / t1) = Real.sqrt t2 / Real.sqrt t1 :=
      Real.sqrt_div ht2_pos.le t1
    have hsqrt_t2 : Real.sqrt (2 * Real.pi * t2) = Real.sqrt (2 * Real.pi) * Real.sqrt t2 :=
      Real.sqrt_mul (by positivity) t2
    have hsqrt_t1 : Real.sqrt (2 * Real.pi * t1) = Real.sqrt (2 * Real.pi) * Real.sqrt t1 :=
      Real.sqrt_mul (by positivity) t1
    have h1 : 1 / Real.sqrt (2 * Real.pi * t) ≤ 1 / Real.sqrt (2 * Real.pi * t1) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1t (by positivity)))
    have h2 : Real.sqrt (t2 / t1) * (1 / Real.sqrt (2 * Real.pi * t2)) =
        1 / Real.sqrt (2 * Real.pi * t1) := by
      rw [hsqrt_div, hsqrt_t2, hsqrt_t1]
      have hs1 : Real.sqrt t1 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht1)
      have hs2 : Real.sqrt t2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht2_pos)
      have hspi : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
      field_simp [hs1, hs2, hspi]
    linarith
  have hmul := mul_le_mul hpref hexp (Real.exp_pos _).le (by positivity)
  linarith

/-- Universal integrable envelope `D(y) = ∫ (1 + x²) f(x) (1 + (y - x)⁴) φ_{t2}(y - x) dx`
    controlling `(1 + y²)(|f_t'(y)| + |f_t''(y)|)` uniformly for `t ∈ [t1, t2]`. -/
private noncomputable def ep_awgnPolyDom (f : Density 1) (t2 : ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, ((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x))

private lemma ep_integrable_awgnPolyDom (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t2 : ℝ} (ht2 : 0 < t2) :
    Integrable (ep_awgnPolyDom f t2) volume := by
  have ha : Integrable (fun x : ℝ => (1 + x ^ 2) * f.pdf (fun _ => x)) volume := by
    have h := (ep_pdf1_integrable f).add (ep_secondMoment_integrable f hm2)
    refine h.congr (ae_of_all _ fun x => ?_); dsimp only [Pi.add_apply]; ring
  have hb : Integrable (fun u : ℝ => (1 + u ^ 4) * gaussianPdf1D t2 u) volume := by
    have h := (ep_integrable_gaussianPdf1D ht2).add (ep_integrable_pow4_mul_gaussianPdf1D ht2)
    refine h.congr (ae_of_all _ fun u => ?_); dsimp only [Pi.add_apply]; ring
  exact ep_integrable_conv_fun
    (a := fun x : ℝ => (1 + x ^ 2) * f.pdf (fun _ => x))
    (b := fun u : ℝ => (1 + u ^ 4) * gaussianPdf1D t2 u) ha hb

private lemma ep_awgn_deriv_poly_bound (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t1 t2 : ℝ} (ht1 : 0 < t1) (h12 : t1 ≤ t2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ} (ht : 0 < t), t1 ≤ t → t ≤ t2 → ∀ y : ℝ,
      (1 + y ^ 2) * |deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z)) y| ≤
        K * ep_awgnPolyDom f t2 y := by
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 h12
  let K : ℝ := (4 / t1) * Real.sqrt (t2 / t1)
  refine ⟨K, by positivity, ?_⟩
  intro t ht h1t ht2_le y
  rw [(hasDerivAt_awgnOutputDensity_pdf f ht y).deriv]
  have h1 : (1 + y ^ 2) * |∫ x : ℝ, f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))| ≤
      ∫ x : ℝ, (1 + y ^ 2) * |f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))| := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
  have hint_dom : Integrable (fun x : ℝ =>
      K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x)))) volume := by
    have ha : Integrable (fun x : ℝ => (1 + x ^ 2) * f.pdf (fun _ => x)) volume := by
      have h := (ep_pdf1_integrable f).add (ep_secondMoment_integrable f hm2)
      refine h.congr (ae_of_all _ fun x => ?_); dsimp only [Pi.add_apply]; ring
    have hbdd : ∀ u : ℝ, (1 + u ^ 4) * gaussianPdf1D t2 u ≤
        (1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2) := by
      intro u
      unfold gaussianPdf1D
      have h0 : Real.exp (-(u ^ 2) / (2 * t2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) (by positivity)
      have h4 := ep_pow4_mul_exp_neg_sq_le ht2 u
      have hsum : (1 + u ^ 4) * Real.exp (-(u ^ 2) / (2 * t2)) ≤ 1 + 16 * t2 ^ 2 := by nlinarith
      calc (1 + u ^ 4) * (1 / Real.sqrt (2 * Real.pi * t2) * Real.exp (-(u ^ 2) / (2 * t2)))
          = ((1 + u ^ 4) * Real.exp (-(u ^ 2) / (2 * t2))) / Real.sqrt (2 * Real.pi * t2) := by ring
        _ ≤ (1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2) :=
            div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg _)
    have hdom := ha.const_mul (K * ((1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2)))
    refine hdom.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((ha.aestronglyMeasurable.mul
        ((continuous_const.add ((continuous_const.sub continuous_id).pow 4)).mul
          ((ep_continuous_gaussianPdf1D t2).comp (continuous_const.sub continuous_id))).aestronglyMeasurable).const_mul K)
    · have hnn : 0 ≤ ((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x)) :=
        mul_nonneg (mul_nonneg (by positivity) (f.nonneg _))
          (mul_nonneg (by positivity) (gaussianPdf1D_nonneg ht2.le _))
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hnn)]
      have hle := hbdd (y - x)
      have hann : 0 ≤ (1 + x ^ 2) * f.pdf (fun _ => x) := mul_nonneg (by positivity) (f.nonneg _)
      have hKnn : 0 ≤ K := by positivity
      calc K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x)))
          ≤ K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hann) hKnn
        _ = K * ((1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2)) * ((1 + x ^ 2) * f.pdf (fun _ => x)) := by ring
  have hpt : ∀ x : ℝ,
      (1 + y ^ 2) * |f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))| ≤
        K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x))) := by
    intro x
    set u : ℝ := y - x
    rw [abs_mul, abs_of_nonneg (f.nonneg _), abs_mul, abs_neg, abs_div, abs_of_pos ht,
      abs_of_pos (gaussianPdf1D_pos ht u)]
    have hg := ep_gaussianPdf1D_le_of_le ht1 h1t ht2_le u
    have hy2 : 1 + y ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + u ^ 2) := by
      have hsq : y ^ 2 ≤ 2 * x ^ 2 + 2 * u ^ 2 := by
        have : 0 ≤ (x - u) ^ 2 := sq_nonneg _
        have : y = x + u := by dsimp only [u]; ring
        nlinarith
      nlinarith [sq_nonneg x, sq_nonneg u]
    have hu1 : |u| ≤ 1 + u ^ 2 := by
      have : 0 ≤ (|u| - 1) ^ 2 := sq_nonneg _
      have : |u| ^ 2 = u ^ 2 := sq_abs u
      nlinarith
    have hu2 : (1 + u ^ 2) * |u| ≤ 2 * (1 + u ^ 4) := by
      have h1 : (1 + u ^ 2) * |u| ≤ (1 + u ^ 2) ^ 2 := by
        nlinarith [sq_nonneg u, abs_nonneg u]
      have h2 : (1 + u ^ 2) ^ 2 ≤ 2 * (1 + u ^ 4) := by
        have : 0 ≤ (1 - u ^ 2) ^ 2 := sq_nonneg _
        linarith
      exact le_trans h1 h2
    have hpoly : (1 + y ^ 2) * (|u| / t) ≤ (4 / t1) * ((1 + x ^ 2) * (1 + u ^ 4)) := by
      have ht_inv : 1 / t ≤ 1 / t1 := one_div_le_one_div_of_le ht1 h1t
      have hmul : (1 + y ^ 2) * |u| ≤ 4 * ((1 + x ^ 2) * (1 + u ^ 4)) := by
        calc (1 + y ^ 2) * |u| ≤ (2 * (1 + x ^ 2) * (1 + u ^ 2)) * |u| :=
              mul_le_mul_of_nonneg_right hy2 (abs_nonneg u)
          _ = 2 * (1 + x ^ 2) * ((1 + u ^ 2) * |u|) := by ring
          _ ≤ 2 * (1 + x ^ 2) * (2 * (1 + u ^ 4)) :=
              mul_le_mul_of_nonneg_left hu2 (by positivity)
          _ = 4 * ((1 + x ^ 2) * (1 + u ^ 4)) := by ring
      calc (1 + y ^ 2) * (|u| / t) = ((1 + y ^ 2) * |u|) * (1 / t) := by ring
        _ ≤ (4 * ((1 + x ^ 2) * (1 + u ^ 4))) * (1 / t1) :=
            mul_le_mul hmul ht_inv (by positivity) (by positivity)
        _ = (4 / t1) * ((1 + x ^ 2) * (1 + u ^ 4)) := by ring
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    have hcomb := mul_le_mul hpoly hg (gaussianPdf1D_nonneg ht.le u) (by positivity)
    have hfinal := mul_le_mul_of_nonneg_left hcomb hfnn
    dsimp only [K]
    nlinarith
  have hint_lhs : Integrable (fun x : ℝ =>
      (1 + y ^ 2) * |f.pdf (fun _ => x) * (-((y - x) / t) * gaussianPdf1D t (y - x))|) volume := by
    refine hint_dom.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (((ep_pdf1_integrable f).aestronglyMeasurable.mul
        ((((continuous_const.sub continuous_id).div_const t).neg).mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable).norm).const_mul _
    · rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _))]
      exact hpt x
  have h2 := integral_mono hint_lhs hint_dom hpt
  conv_rhs at h2 => rw [integral_const_mul]
  exact le_trans h1 h2

private lemma ep_awgn_deriv2_poly_bound (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t1 t2 : ℝ} (ht1 : 0 < t1) (h12 : t1 ≤ t2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ} (ht : 0 < t), t1 ≤ t → t ≤ t2 → ∀ y : ℝ,
      (1 + y ^ 2) * |deriv (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) y| ≤
        K * ep_awgnPolyDom f t2 y := by
  have ht2 : 0 < t2 := lt_of_lt_of_le ht1 h12
  let K : ℝ := (4 * (1 / t1 ^ 2 + 1 / t1)) * Real.sqrt (t2 / t1)
  refine ⟨K, by positivity, ?_⟩
  intro t ht h1t ht2_le y
  rw [(hasDerivAt_deriv_awgnOutputDensity_pdf f ht y).deriv]
  have h1 : (1 + y ^ 2) * |∫ x : ℝ, f.pdf (fun _ => x) *
        (((y - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (y - x))| ≤
      ∫ x : ℝ, (1 + y ^ 2) * |f.pdf (fun _ => x) *
        (((y - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (y - x))| := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
  have hint_dom : Integrable (fun x : ℝ =>
      K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x)))) volume := by
    have ha : Integrable (fun x : ℝ => (1 + x ^ 2) * f.pdf (fun _ => x)) volume := by
      have h := (ep_pdf1_integrable f).add (ep_secondMoment_integrable f hm2)
      refine h.congr (ae_of_all _ fun x => ?_); dsimp only [Pi.add_apply]; ring
    have hbdd : ∀ u : ℝ, (1 + u ^ 4) * gaussianPdf1D t2 u ≤
        (1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2) := by
      intro u
      unfold gaussianPdf1D
      have h0 : Real.exp (-(u ^ 2) / (2 * t2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) (by positivity)
      have h4 := ep_pow4_mul_exp_neg_sq_le ht2 u
      have hsum : (1 + u ^ 4) * Real.exp (-(u ^ 2) / (2 * t2)) ≤ 1 + 16 * t2 ^ 2 := by nlinarith
      calc (1 + u ^ 4) * (1 / Real.sqrt (2 * Real.pi * t2) * Real.exp (-(u ^ 2) / (2 * t2)))
          = ((1 + u ^ 4) * Real.exp (-(u ^ 2) / (2 * t2))) / Real.sqrt (2 * Real.pi * t2) := by ring
        _ ≤ (1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2) :=
            div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg _)
    have hdom := ha.const_mul (K * ((1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2)))
    refine hdom.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((ha.aestronglyMeasurable.mul
        ((continuous_const.add ((continuous_const.sub continuous_id).pow 4)).mul
          ((ep_continuous_gaussianPdf1D t2).comp (continuous_const.sub continuous_id))).aestronglyMeasurable).const_mul K)
    · have hnn : 0 ≤ ((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x)) :=
        mul_nonneg (mul_nonneg (by positivity) (f.nonneg _))
          (mul_nonneg (by positivity) (gaussianPdf1D_nonneg ht2.le _))
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hnn)]
      have hle := hbdd (y - x)
      have hann : 0 ≤ (1 + x ^ 2) * f.pdf (fun _ => x) := mul_nonneg (by positivity) (f.nonneg _)
      have hKnn : 0 ≤ K := by positivity
      calc K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x)))
          ≤ K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hann) hKnn
        _ = K * ((1 + 16 * t2 ^ 2) / Real.sqrt (2 * Real.pi * t2)) * ((1 + x ^ 2) * f.pdf (fun _ => x)) := by ring
  have hpt : ∀ x : ℝ,
      (1 + y ^ 2) * |f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (y - x))| ≤
        K * (((1 + x ^ 2) * f.pdf (fun _ => x)) * ((1 + (y - x) ^ 4) * gaussianPdf1D t2 (y - x))) := by
    intro x
    set u : ℝ := y - x
    rw [abs_mul, abs_of_nonneg (f.nonneg _), abs_mul, abs_of_pos (gaussianPdf1D_pos ht u)]
    have hg := ep_gaussianPdf1D_le_of_le ht1 h1t ht2_le u
    have htri : |u ^ 2 / t ^ 2 - 1 / t| ≤ (1 / t1 ^ 2 + 1 / t1) * (1 + u ^ 2) := by
      have h1 : |u ^ 2 / t ^ 2 - 1 / t| ≤ u ^ 2 / t ^ 2 + 1 / t := by
        calc |u ^ 2 / t ^ 2 - 1 / t| ≤ |u ^ 2 / t ^ 2| + |1 / t| := abs_sub _ _
          _ = u ^ 2 / t ^ 2 + 1 / t := by
              rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
      have ht_inv : 1 / t ≤ 1 / t1 := one_div_le_one_div_of_le ht1 h1t
      have ht2_inv : 1 / t ^ 2 ≤ 1 / t1 ^ 2 :=
        one_div_le_one_div_of_le (sq_pos_of_pos ht1) (sq_le_sq' (by linarith) h1t)
      have hu2 : u ^ 2 / t ^ 2 ≤ (1 / t1 ^ 2) * u ^ 2 := by
        calc u ^ 2 / t ^ 2 = (1 / t ^ 2) * u ^ 2 := by ring
          _ ≤ (1 / t1 ^ 2) * u ^ 2 := mul_le_mul_of_nonneg_right ht2_inv (sq_nonneg u)
      have hnn1 : 0 ≤ (1 / t1 ^ 2) := by positivity
      have hnn2 : 0 ≤ (1 / t1) * u ^ 2 := by positivity
      calc |u ^ 2 / t ^ 2 - 1 / t| ≤ u ^ 2 / t ^ 2 + 1 / t := h1
        _ ≤ (1 / t1 ^ 2) * u ^ 2 + 1 / t1 := add_le_add hu2 ht_inv
        _ ≤ (1 / t1 ^ 2) * u ^ 2 + 1 / t1 + 1 / t1 ^ 2 + (1 / t1) * u ^ 2 := by linarith
        _ = (1 / t1 ^ 2 + 1 / t1) * (1 + u ^ 2) := by ring
    have hy2 : 1 + y ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + u ^ 2) := by
      have hsq : y ^ 2 ≤ 2 * x ^ 2 + 2 * u ^ 2 := by
        have : 0 ≤ (x - u) ^ 2 := sq_nonneg _
        have : y = x + u := by dsimp only [u]; ring
        nlinarith
      nlinarith [sq_nonneg x, sq_nonneg u]
    have hu4 : (1 + u ^ 2) ^ 2 ≤ 2 * (1 + u ^ 4) := by
      have : 0 ≤ (1 - u ^ 2) ^ 2 := sq_nonneg _
      linarith
    have hpoly : (1 + y ^ 2) * |u ^ 2 / t ^ 2 - 1 / t| ≤
        (4 * (1 / t1 ^ 2 + 1 / t1)) * ((1 + x ^ 2) * (1 + u ^ 4)) := by
      calc (1 + y ^ 2) * |u ^ 2 / t ^ 2 - 1 / t|
          ≤ (2 * (1 + x ^ 2) * (1 + u ^ 2)) * ((1 / t1 ^ 2 + 1 / t1) * (1 + u ^ 2)) :=
            mul_le_mul hy2 htri (abs_nonneg _) (by positivity)
        _ = 2 * (1 / t1 ^ 2 + 1 / t1) * (1 + x ^ 2) * (1 + u ^ 2) ^ 2 := by ring
        _ ≤ 2 * (1 / t1 ^ 2 + 1 / t1) * (1 + x ^ 2) * (2 * (1 + u ^ 4)) :=
            mul_le_mul_of_nonneg_left hu4 (by positivity)
        _ = (4 * (1 / t1 ^ 2 + 1 / t1)) * ((1 + x ^ 2) * (1 + u ^ 4)) := by ring
    have hfnn : 0 ≤ f.pdf (fun _ => x) := f.nonneg _
    have hcomb := mul_le_mul hpoly hg (gaussianPdf1D_nonneg ht.le u) (by positivity)
    have hfinal := mul_le_mul_of_nonneg_left hcomb hfnn
    dsimp only [K]
    nlinarith
  have hint_lhs : Integrable (fun x : ℝ =>
      (1 + y ^ 2) * |f.pdf (fun _ => x) * (((y - x) ^ 2 / t ^ 2 - 1 / t) * gaussianPdf1D t (y - x))|) volume := by
    refine hint_dom.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (((ep_pdf1_integrable f).aestronglyMeasurable.mul
        (((((continuous_const.sub continuous_id).pow 2).div_const (t ^ 2)).sub continuous_const).mul
          ((ep_continuous_gaussianPdf1D t).comp (continuous_const.sub continuous_id))).aestronglyMeasurable).norm).const_mul _
    · rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _))]
      exact hpt x
  have h2 := integral_mono hint_lhs hint_dom hpt
  conv_rhs at h2 => rw [integral_const_mul]
  exact le_trans h1 h2

/-- Total-function wrapper `t ↦ h(X + √t Z)` for `t > 0` (and `0` for `t ≤ 0`), enabling
    clean `HasDerivAt` and `Tendsto` statements on `ℝ`. -/
noncomputable def awgnDiffEntropy (f : Density 1) (t : ℝ) : ℝ :=
  if ht : 0 < t then diffEntropy (awgnOutputDensity f t ht) else 0

lemma awgnDiffEntropy_eq (f : Density 1) {t : ℝ} (ht : 0 < t) :
    awgnDiffEntropy f t = diffEntropy (awgnOutputDensity f t ht) := by
  simp [awgnDiffEntropy, ht]

private lemma ep_awgn_ibp_fisher (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t : ℝ} (ht : 0 < t) :
    ∫ y : ℝ, -(Real.log ((awgnOutputDensity f t ht).pdf (fun _ => y)) + 1) *
        deriv (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) y =
      fisherInfo (awgnOutputDensity f t ht) := by
  let p : ℝ → ℝ := fun y => (awgnOutputDensity f t ht).pdf (fun _ => y)
  let p' : ℝ → ℝ := deriv p
  let p'' : ℝ → ℝ := deriv p'
  have hp_pos : ∀ y : ℝ, 0 < p y := awgnOutputDensity_pdf_pos f ht
  have hp_diff : ∀ y : ℝ, HasDerivAt p (p' y) y :=
    fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).differentiableAt.hasDerivAt
  have hp'_diff : ∀ y : ℝ, HasDerivAt p' (p'' y) y :=
    fun y => (hasDerivAt_deriv_awgnOutputDensity_pdf f ht y).differentiableAt.hasDerivAt
  have hp_cont : Continuous p := continuous_iff_continuousAt.mpr fun y => (hp_diff y).continuousAt
  have hp'_cont : Continuous p' := continuous_iff_continuousAt.mpr fun y => (hp'_diff y).continuousAt
  obtain ⟨A, B, hA, hB, hlog⟩ := ep_abs_log_awgn_pdf_le f hm2 ht le_rfl
  obtain ⟨K1, hK1, hd1⟩ := ep_awgn_deriv_poly_bound f hm2 ht le_rfl
  obtain ⟨K2, hK2, hd2⟩ := ep_awgn_deriv2_poly_bound f hm2 ht le_rfl
  have hD_int : Integrable (ep_awgnPolyDom f t) volume := ep_integrable_awgnPolyDom f hm2 ht
  let M : ℝ := max (A + 1) B
  have hM_nn : 0 ≤ M := le_trans hB (le_max_right _ _)
  have hlog1 : ∀ y : ℝ, |Real.log (p y) + 1| ≤ M * (1 + y ^ 2) := by
    intro y
    have h1 : |Real.log (p y) + 1| ≤ |Real.log (p y)| + 1 := by
      simpa using abs_add_le (Real.log (p y)) 1
    have h2 := hlog ht le_rfl le_rfl y
    have hM1 : A + 1 ≤ M := le_max_left _ _
    have hM2 : B ≤ M := le_max_right _ _
    nlinarith [sq_nonneg y]
  have hF_int : Integrable (fun y : ℝ => -(Real.log (p y) + 1) * p' y) volume := by
    refine (hD_int.const_mul (M * K1)).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((((hp_cont.log fun y => ne_of_gt (hp_pos y)).add continuous_const).neg).mul hp'_cont).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_neg]
      have h1 := hlog1 y
      have h2 := hd1 ht le_rfl le_rfl y
      calc |Real.log (p y) + 1| * |p' y|
          ≤ (M * (1 + y ^ 2)) * |p' y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = M * ((1 + y ^ 2) * |p' y|) := by ring
        _ ≤ M * (K1 * ep_awgnPolyDom f t y) := mul_le_mul_of_nonneg_left h2 hM_nn
        _ = M * K1 * ep_awgnPolyDom f t y := by ring
  have hterm2_int : Integrable (fun y : ℝ => -(Real.log (p y) + 1) * p'' y) volume := by
    refine (hD_int.const_mul (M * K2)).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((((hp_cont.log fun y => ne_of_gt (hp_pos y)).add continuous_const).neg).aestronglyMeasurable).mul
        (measurable_deriv p').aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_neg]
      have h1 := hlog1 y
      have h2 := hd2 ht le_rfl le_rfl y
      calc |Real.log (p y) + 1| * |p'' y|
          ≤ (M * (1 + y ^ 2)) * |p'' y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = M * ((1 + y ^ 2) * |p'' y|) := by ring
        _ ≤ M * (K2 * ep_awgnPolyDom f t y) := mul_le_mul_of_nonneg_left h2 hM_nn
        _ = M * K2 * ep_awgnPolyDom f t y := by ring
  have hscore_int : Integrable (fun y : ℝ => (p' y) ^ 2 / p y) volume :=
    ep_integrable_fisherInfo_awgn f ht
  have hscore_neg : Integrable (fun y : ℝ => -((p' y) ^ 2 / p y)) volume := hscore_int.neg
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => -(Real.log (p z) + 1) * p' z)
      (-((p' y) ^ 2 / p y) + -(Real.log (p y) + 1) * p'' y) y := by
    intro y
    have hlog_d : HasDerivAt (fun z : ℝ => -(Real.log (p z) + 1)) (-(p' y / p y)) y := by
      have h1 := ((hp_diff y).log (ne_of_gt (hp_pos y))).add_const (1 : ℝ)
      exact h1.neg
    have hprod := hlog_d.mul (hp'_diff y)
    refine hprod.congr_deriv ?_
    have hp0 : p y ≠ 0 := ne_of_gt (hp_pos y)
    field_simp [hp0]
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv
    (hscore_neg.add hterm2_int) hF_int
  rw [integral_add hscore_neg hterm2_int, integral_neg] at hzero
  have hJ : ∫ y : ℝ, (p' y) ^ 2 / p y = fisherInfo (awgnOutputDensity f t ht) := rfl
  linarith

/-- **De Bruijn's Identity** (Cover & Thomas Theorem 17.7.1; Stam 1959):
    for any 1D density `f` with finite second moment and every `t > 0`,
    `d/dt h(X + √t Z) = ½ J(X + √t Z)`. -/
theorem de_bruijn_identity (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (awgnDiffEntropy f) ((1 / 2 : ℝ) * fisherInfo (awgnOutputDensity f t ht)) t := by
  let t1 : ℝ := t / 2
  let t2 : ℝ := 2 * t
  have ht1 : 0 < t1 := half_pos ht
  have h12 : t1 ≤ t2 := by dsimp only [t1, t2]; linarith
  have ht2 : 0 < t2 := by dsimp only [t2]; positivity
  let s_set : Set ℝ := Set.Ioo t1 t2
  have hs_mem : s_set ∈ 𝓝 t := Ioo_mem_nhds (by dsimp only [t1]; linarith) (by dsimp only [t2]; linarith)
  -- Express `awgnDiffEntropy f s` as `∫ y, F s y` on `s ∈ s_set`.
  let P : ℝ → ℝ → ℝ := fun s y => ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D s (y - x)
  let F : ℝ → ℝ → ℝ := fun s y => -P s y * Real.log (P s y)
  let F' : ℝ → ℝ → ℝ := fun s y =>
    if hs : 0 < s then
      (1 / 2 : ℝ) * (-(Real.log ((awgnOutputDensity f s hs).pdf (fun _ => y)) + 1) *
        deriv (deriv (fun z : ℝ => (awgnOutputDensity f s hs).pdf (fun _ => z))) y)
    else 0
  have hP_eq : ∀ {s : ℝ} (hs : 0 < s) (y : ℝ),
      P s y = (awgnOutputDensity f s hs).pdf (fun _ => y) := by
    intro s hs y
    rw [← convDensity_gaussian_eq_awgn f hs, convDensity_pdf_eq]; rfl
  have h_eq_nhds : awgnDiffEntropy f =ᶠ[𝓝 t] fun s : ℝ => ∫ y : ℝ, F s y := by
    filter_upwards [hs_mem] with s hs
    have hs_pos : 0 < s := lt_trans ht1 hs.1
    rw [awgnDiffEntropy_eq f hs_pos]
    unfold diffEntropy
    rw [ep_integral_fin1]
    congr 1; funext y
    dsimp only [F]
    rw [← hP_eq hs_pos y]
    exact ite_eq_right_iff.mpr fun h =>
      absurd h (not_le.mpr (by rw [hP_eq hs_pos y]; exact awgnOutputDensity_pdf_pos f hs_pos y))
  obtain ⟨A, B, hA, hB, hlog⟩ := ep_abs_log_awgn_pdf_le f hm2 ht1 h12
  obtain ⟨K2, hK2, hd2⟩ := ep_awgn_deriv2_poly_bound f hm2 ht1 h12
  let M : ℝ := max (A + 1) B
  have hM_nn : 0 ≤ M := le_trans hB (le_max_right _ _)
  let C : ℝ := (1 / 2 : ℝ) * (M * K2)
  have hD_int : Integrable (ep_awgnPolyDom f t2) volume := ep_integrable_awgnPolyDom f hm2 ht2
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [hs_mem] with s hs
    have hs_pos : 0 < s := lt_trans ht1 hs.1
    have hPs_cont : Continuous (P s) := by
      have heq : P s = fun y : ℝ => (awgnOutputDensity f s hs_pos).pdf (fun _ => y) :=
        funext (hP_eq hs_pos)
      rw [heq]
      exact continuous_iff_continuousAt.mpr fun y => (hasDerivAt_awgnOutputDensity_pdf f hs_pos y).continuousAt
    have hPs_ne : ∀ y : ℝ, P s y ≠ 0 := fun y => by
      rw [hP_eq hs_pos y]; exact ne_of_gt (awgnOutputDensity_pdf_pos f hs_pos y)
    exact (hPs_cont.neg.mul (hPs_cont.log hPs_ne)).aestronglyMeasurable
  have hF_int : Integrable (F t) volume := by
    have hfe := hasFiniteDiffEntropy_awgnOutputDensity f hm2 ht
    unfold HasFiniteDiffEntropy at hfe
    rw [ep_integrable_fin1_iff] at hfe
    refine hfe.congr (ae_of_all _ fun y => ?_)
    dsimp only [F]
    rw [hP_eq ht y]
    exact ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr (awgnOutputDensity_pdf_pos f ht y))
  have hF'_meas : AEStronglyMeasurable (F' t) volume := by
    have heq : F' t = fun y : ℝ =>
        (1 / 2 : ℝ) * (-(Real.log ((awgnOutputDensity f t ht).pdf (fun _ => y)) + 1) *
          deriv (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) y) := by
      funext y; simp [F', ht]
    rw [heq]
    have hp_cont : Continuous (fun y : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => y)) :=
      continuous_iff_continuousAt.mpr fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).continuousAt
    exact ((((hp_cont.log fun y => ne_of_gt (awgnOutputDensity_pdf_pos f ht y)).add
      continuous_const).neg.aestronglyMeasurable).mul
      (measurable_deriv _).aestronglyMeasurable).const_mul (1 / 2)
  have h_bound : ∀ᵐ y ∂volume, ∀ s ∈ s_set, ‖F' s y‖ ≤ C * ep_awgnPolyDom f t2 y := by
    refine ae_of_all _ fun y s hs => ?_
    have hs_pos : 0 < s := lt_trans ht1 hs.1
    dsimp only [F', C]
    simp only [hs_pos, ↓reduceDIte]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_mul, abs_neg]
    have hlog1 : |Real.log ((awgnOutputDensity f s hs_pos).pdf (fun _ => y)) + 1| ≤ M * (1 + y ^ 2) := by
      have h1 : |Real.log ((awgnOutputDensity f s hs_pos).pdf (fun _ => y)) + 1| ≤
          |Real.log ((awgnOutputDensity f s hs_pos).pdf (fun _ => y))| + 1 := by
        simpa using abs_add_le (Real.log ((awgnOutputDensity f s hs_pos).pdf (fun _ => y))) 1
      have h2 := hlog hs_pos hs.1.le hs.2.le y
      have hM1 : A + 1 ≤ M := le_max_left _ _
      have hM2 : B ≤ M := le_max_right _ _
      nlinarith [sq_nonneg y]
    have h2 := hd2 hs_pos hs.1.le hs.2.le y
    calc (1 / 2 : ℝ) * (|Real.log ((awgnOutputDensity f s hs_pos).pdf (fun _ => y)) + 1| *
          |deriv (deriv (fun z : ℝ => (awgnOutputDensity f s hs_pos).pdf (fun _ => z))) y|)
        ≤ (1 / 2 : ℝ) * ((M * (1 + y ^ 2)) *
          |deriv (deriv (fun z : ℝ => (awgnOutputDensity f s hs_pos).pdf (fun _ => z))) y|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog1 (abs_nonneg _)) (by positivity)
      _ = (1 / 2 : ℝ) * (M * ((1 + y ^ 2) *
          |deriv (deriv (fun z : ℝ => (awgnOutputDensity f s hs_pos).pdf (fun _ => z))) y|)) := by ring
      _ ≤ (1 / 2 : ℝ) * (M * (K2 * ep_awgnPolyDom f t2 y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hM_nn) (by positivity)
      _ = (1 / 2 : ℝ) * (M * K2) * ep_awgnPolyDom f t2 y := by ring
  have h_diff : ∀ᵐ y ∂volume, ∀ s ∈ s_set, HasDerivAt (F · y) (F' s y) s := by
    refine ae_of_all _ fun y s hs => ?_
    have hs_pos : 0 < s := lt_trans ht1 hs.1
    have hP_deriv := awgnOutputDensity_heat_equation f hs_pos y
    have hP_pos : 0 < P s y := by rw [hP_eq hs_pos y]; exact awgnOutputDensity_pdf_pos f hs_pos y
    have hlog_deriv := hP_deriv.log (ne_of_gt hP_pos)
    have hprod := hP_deriv.neg.mul hlog_deriv
    refine hprod.congr_deriv ?_
    dsimp only [F', Pi.neg_apply]
    have hP_eq' : ∫ x : ℝ, f.pdf (fun _ => x) * gaussianPdf1D s (y - x) =
        (awgnOutputDensity f s hs_pos).pdf (fun _ => y) := hP_eq hs_pos y
    simp only [hs_pos, ↓reduceDIte]
    rw [hP_eq']
    have hpne : (awgnOutputDensity f s hs_pos).pdf (fun _ => y) ≠ 0 :=
      ne_of_gt (awgnOutputDensity_pdf_pos f hs_pos y)
    field_simp [hpne]
    ring
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_mem
    hF_meas hF_int hF'_meas h_bound (hD_int.const_mul C) h_diff).2
  have hmain' := hmain.congr_of_eventuallyEq h_eq_nhds
  refine hmain'.congr_deriv ?_
  have hF't : (fun y : ℝ => F' t y) = fun y : ℝ =>
      (1 / 2 : ℝ) * (-(Real.log ((awgnOutputDensity f t ht).pdf (fun _ => y)) + 1) *
        deriv (deriv (fun z : ℝ => (awgnOutputDensity f t ht).pdf (fun _ => z))) y) := by
    funext y; dsimp only [F']; simp only [ht, ↓reduceDIte]
  rw [hF't, integral_const_mul, ep_awgn_ibp_fisher f hm2 ht]

/-! ### Section 4: Shannon's 1D Entropy Power Inequality (Cover & Thomas Thm. 17.8.1) -/

/-- **Nonnegativity of Continuous AWGN Mutual Information**:
    `h(X + Z) ≥ h(Z)` for any finite-second-moment input `X ~ f` and independent `Z ~ N(0, t)`. -/
theorem awgn_mutualInfo_nonneg (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {t : ℝ} (ht : 0 < t) :
    diffEntropy (gaussianDensity1D t ht) ≤ diffEntropy (awgnOutputDensity f t ht) := by
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  let p : ℝ → ℝ := fun y => (awgnOutputDensity f t ht).pdf (fun _ => y)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hp_int : Integrable p volume := ep_pdf1_integrable (awgnOutputDensity f t ht)
  have hp_pos : ∀ y : ℝ, 0 < p y := awgnOutputDensity_pdf_pos f ht
  have hp_cont : Continuous p :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).continuousAt
  obtain ⟨A, B, hA, hB, hlog⟩ := ep_abs_log_awgn_pdf_le f hm2 ht le_rfl
  have hglog_int : Integrable (fun u : ℝ => gaussianPdf1D t u * Real.log (gaussianPdf1D t u)) volume := by
    have hfe := hasFiniteDiffEntropy_gaussianDensity1D ht
    unfold HasFiniteDiffEntropy at hfe
    rw [ep_integrable_fin1_iff] at hfe
    refine hfe.neg.congr (ae_of_all _ fun u => ?_)
    change -(if gaussianPdf1D t u ≤ 0 then 0 else -gaussianPdf1D t u * Real.log (gaussianPdf1D t u)) = _
    rw [ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr (gaussianPdf1D_pos ht u))]; ring
  have hT1 : Integrable (fun q : ℝ × ℝ => f1 q.2 * (gaussianPdf1D t (q.1 - q.2) * Real.log (gaussianPdf1D t (q.1 - q.2))))
      (volume.prod volume) := ep_integrable_prod_shear hf1 hglog_int
  have hT2 : Integrable (fun q : ℝ × ℝ => -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1)))
      (volume.prod volume) := by
    have hdom1 := (ep_integrable_prod_shear hf1 (ep_integrable_gaussianPdf1D ht)).const_mul A
    have hdom2a := ep_integrable_prod_shear ((ep_secondMoment_integrable f hm2).const_mul (2 * B))
      (ep_integrable_gaussianPdf1D ht)
    have hdom2b := ep_integrable_prod_shear hf1 ((integrable_sq_mul_gaussianPdf1D ht).const_mul (2 * B))
    have hdom := (hdom1.add hdom2a).add hdom2b
    have hmeas : AEStronglyMeasurable
        (fun q : ℝ × ℝ => -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1)))
        (volume.prod volume) := by
      have h1 := (ep_integrable_prod_shear hf1 (ep_integrable_gaussianPdf1D ht)).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun q : ℝ × ℝ => Real.log (p q.1)) (volume.prod volume) :=
        ((hp_cont.log fun y => ne_of_gt (hp_pos y)).comp (continuous_fst (X := ℝ) (Y := ℝ))).aestronglyMeasurable
      exact (h1.mul h2).neg
    refine hdom.mono' hmeas (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _))]
    have hl := hlog ht le_rfl le_rfl q.1
    have hsq : q.1 ^ 2 ≤ 2 * q.2 ^ 2 + 2 * (q.1 - q.2) ^ 2 := by
      have : 0 ≤ (q.2 - (q.1 - q.2)) ^ 2 := sq_nonneg _
      linarith
    have hnn : 0 ≤ f1 q.2 * gaussianPdf1D t (q.1 - q.2) :=
      mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg ht.le _)
    have hBnn : 0 ≤ B := hB
    change f1 q.2 * gaussianPdf1D t (q.1 - q.2) * |Real.log (p q.1)| ≤
      A * (f1 q.2 * gaussianPdf1D t (q.1 - q.2)) +
        2 * B * (q.2 ^ 2 * f1 q.2) * gaussianPdf1D t (q.1 - q.2) +
        f1 q.2 * (2 * B * ((q.1 - q.2) ^ 2 * gaussianPdf1D t (q.1 - q.2)))
    calc f1 q.2 * gaussianPdf1D t (q.1 - q.2) * |Real.log (p q.1)|
        ≤ f1 q.2 * gaussianPdf1D t (q.1 - q.2) * (A + B * q.1 ^ 2) :=
          mul_le_mul_of_nonneg_left hl hnn
      _ ≤ f1 q.2 * gaussianPdf1D t (q.1 - q.2) * (A + B * (2 * q.2 ^ 2 + 2 * (q.1 - q.2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hnn
      _ = A * (f1 q.2 * gaussianPdf1D t (q.1 - q.2)) +
          2 * B * (q.2 ^ 2 * f1 q.2) * gaussianPdf1D t (q.1 - q.2) +
          f1 q.2 * (2 * B * ((q.1 - q.2) ^ 2 * gaussianPdf1D t (q.1 - q.2))) := by ring
  have hT3 : Integrable (fun q : ℝ × ℝ => p q.1 * f1 q.2) (volume.prod volume) := hp_int.mul_prod hf1
  have hT4 : Integrable (fun q : ℝ × ℝ => f1 q.2 * gaussianPdf1D t (q.1 - q.2)) (volume.prod volume) :=
    ep_integrable_prod_shear hf1 (ep_integrable_gaussianPdf1D ht)
  have hT12 : Integrable (fun q : ℝ × ℝ =>
      f1 q.2 * (gaussianPdf1D t (q.1 - q.2) * Real.log (gaussianPdf1D t (q.1 - q.2))) +
      -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1))) (volume.prod volume) := hT1.add hT2
  have hT123 : Integrable (fun q : ℝ × ℝ =>
      f1 q.2 * (gaussianPdf1D t (q.1 - q.2) * Real.log (gaussianPdf1D t (q.1 - q.2))) +
      -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1)) +
      p q.1 * f1 q.2) (volume.prod volume) := hT12.add hT3
  have hnn_int : 0 ≤ ∫ q : ℝ × ℝ,
      (f1 q.2 * (gaussianPdf1D t (q.1 - q.2) * Real.log (gaussianPdf1D t (q.1 - q.2))) +
       -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1)) +
       p q.1 * f1 q.2 -
       f1 q.2 * gaussianPdf1D t (q.1 - q.2)) ∂(volume.prod volume) := by
    refine integral_nonneg fun q => ?_
    have hgp : 0 < gaussianPdf1D t (q.1 - q.2) := gaussianPdf1D_pos ht _
    have hpp : 0 < p q.1 := hp_pos q.1
    have hkl : 0 ≤ InformationTheory.klFun (gaussianPdf1D t (q.1 - q.2) / p q.1) :=
      InformationTheory.klFun_nonneg (div_nonneg hgp.le hpp.le)
    unfold InformationTheory.klFun at hkl
    have hmul := mul_nonneg (mul_nonneg (f.nonneg (fun _ => q.2)) hpp.le) hkl
    have hident : f1 q.2 * p q.1 *
        (gaussianPdf1D t (q.1 - q.2) / p q.1 * Real.log (gaussianPdf1D t (q.1 - q.2) / p q.1) +
          1 - gaussianPdf1D t (q.1 - q.2) / p q.1) =
        f1 q.2 * (gaussianPdf1D t (q.1 - q.2) * Real.log (gaussianPdf1D t (q.1 - q.2))) +
        -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1)) +
        p q.1 * f1 q.2 -
        f1 q.2 * gaussianPdf1D t (q.1 - q.2) := by
      rw [Real.log_div (ne_of_gt hgp) (ne_of_gt hpp)]
      have hpne : p q.1 ≠ 0 := ne_of_gt hpp
      field_simp [hpne]
      ring
    rwa [hident] at hmul
  rw [integral_sub hT123 hT4, integral_add hT12 hT3, integral_add hT1 hT2] at hnn_int
  have hI1 : ∫ q : ℝ × ℝ, f1 q.2 * (gaussianPdf1D t (q.1 - q.2) * Real.log (gaussianPdf1D t (q.1 - q.2)))
      ∂(volume.prod volume) = -diffEntropy (gaussianDensity1D t ht) := by
    rw [ep_integral_prod_shear hf1 hglog_int, ep_pdf1_integral_one f, one_mul]
    unfold diffEntropy
    rw [ep_integral_fin1, ← integral_neg]
    congr 1; funext u
    change gaussianPdf1D t u * Real.log (gaussianPdf1D t u) =
      -(if gaussianPdf1D t u ≤ 0 then 0 else -gaussianPdf1D t u * Real.log (gaussianPdf1D t u))
    rw [ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr (gaussianPdf1D_pos ht u))]; ring
  have hI2 : ∫ q : ℝ × ℝ, -(f1 q.2 * gaussianPdf1D t (q.1 - q.2) * Real.log (p q.1))
      ∂(volume.prod volume) = diffEntropy (awgnOutputDensity f t ht) := by
    rw [integral_prod _ hT2]
    unfold diffEntropy
    rw [ep_integral_fin1]
    congr 1; funext y
    have hpull : (fun x : ℝ => -(f1 x * gaussianPdf1D t (y - x) * Real.log (p y))) =
        fun x : ℝ => (f1 x * gaussianPdf1D t (y - x)) * (-Real.log (p y)) := by funext x; ring
    rw [hpull, integral_mul_const]
    have hp_eq : ∫ x : ℝ, f1 x * gaussianPdf1D t (y - x) = p y := by
      dsimp only [p, f1]
      rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]; rfl
    rw [hp_eq, ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr (hp_pos y))]; ring
  have hI3 : ∫ q : ℝ × ℝ, p q.1 * f1 q.2 ∂(volume.prod volume) = 1 := by
    rw [integral_prod_mul, ep_pdf1_integral_one (awgnOutputDensity f t ht),
      ep_pdf1_integral_one f, mul_one]
  have hI4 : ∫ q : ℝ × ℝ, f1 q.2 * gaussianPdf1D t (q.1 - q.2) ∂(volume.prod volume) = 1 := by
    rw [ep_integral_prod_shear hf1 (ep_integrable_gaussianPdf1D ht),
      ep_pdf1_integral_one f, ep_integral_gaussianPdf1D ht, mul_one]
  rw [hI1, hI2, hI3, hI4] at hnn_int
  linarith

/-- **Conditioning Reduces Differential Entropy for AWGN**:
    `h(X) ≤ h(X + √t Z)` for any finite-second-moment density `f` with finite differential
    entropy and any `t > 0`. -/
theorem diffEntropy_awgnOutput_ge (f : Density 1) (hf : HasFiniteDiffEntropy f)
    (hm2 : HasFiniteSecondMoment f) {t : ℝ} (ht : 0 < t) :
    diffEntropy f ≤ diffEntropy (awgnOutputDensity f t ht) := by
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  let p : ℝ → ℝ := fun y => (awgnOutputDensity f t ht).pdf (fun _ => y)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hg1 : Integrable (gaussianPdf1D t) volume := ep_integrable_gaussianPdf1D ht
  have hp_int : Integrable p volume := ep_pdf1_integrable (awgnOutputDensity f t ht)
  have hp_pos : ∀ y : ℝ, 0 < p y := awgnOutputDensity_pdf_pos f ht
  have hp_cont : Continuous p :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_awgnOutputDensity_pdf f ht y).continuousAt
  obtain ⟨A, B, hA, hB, hlog⟩ := ep_abs_log_awgn_pdf_le f hm2 ht le_rfl
  let flog : ℝ → ℝ := fun x => if f1 x ≤ 0 then 0 else f1 x * Real.log (f1 x)
  have hflog_int : Integrable flog volume := by
    unfold HasFiniteDiffEntropy at hf
    rw [ep_integrable_fin1_iff] at hf
    refine hf.neg.congr (ae_of_all _ fun x => ?_)
    dsimp only [Pi.neg_apply, flog, f1]
    split_ifs <;> ring
  have hT1 : Integrable (fun q : ℝ × ℝ => gaussianPdf1D t q.2 * flog (q.1 - q.2))
      (volume.prod volume) := ep_integrable_prod_shear hg1 hflog_int
  have hT2 : Integrable (fun q : ℝ × ℝ => -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1)))
      (volume.prod volume) := by
    have hdom1 := (ep_integrable_prod_shear hg1 hf1).const_mul A
    have hdom2a := ep_integrable_prod_shear ((integrable_sq_mul_gaussianPdf1D ht).const_mul (2 * B)) hf1
    have hdom2b := ep_integrable_prod_shear hg1 ((ep_secondMoment_integrable f hm2).const_mul (2 * B))
    have hdom := (hdom1.add hdom2a).add hdom2b
    have hmeas : AEStronglyMeasurable
        (fun q : ℝ × ℝ => -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1)))
        (volume.prod volume) := by
      have h1 := (ep_integrable_prod_shear hg1 hf1).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun q : ℝ × ℝ => Real.log (p q.1)) (volume.prod volume) :=
        ((hp_cont.log fun y => ne_of_gt (hp_pos y)).comp (continuous_fst (X := ℝ) (Y := ℝ))).aestronglyMeasurable
      exact (h1.mul h2).neg
    refine hdom.mono' hmeas (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (mul_nonneg (gaussianPdf1D_nonneg ht.le _) (f.nonneg _))]
    have hl := hlog ht le_rfl le_rfl q.1
    have hsq : q.1 ^ 2 ≤ 2 * q.2 ^ 2 + 2 * (q.1 - q.2) ^ 2 := by
      have : 0 ≤ (q.2 - (q.1 - q.2)) ^ 2 := sq_nonneg _
      linarith
    have hnn : 0 ≤ gaussianPdf1D t q.2 * f1 (q.1 - q.2) :=
      mul_nonneg (gaussianPdf1D_nonneg ht.le _) (f.nonneg _)
    change gaussianPdf1D t q.2 * f1 (q.1 - q.2) * |Real.log (p q.1)| ≤
      A * (gaussianPdf1D t q.2 * f1 (q.1 - q.2)) +
        2 * B * (q.2 ^ 2 * gaussianPdf1D t q.2) * f1 (q.1 - q.2) +
        gaussianPdf1D t q.2 * (2 * B * ((q.1 - q.2) ^ 2 * f1 (q.1 - q.2)))
    calc gaussianPdf1D t q.2 * f1 (q.1 - q.2) * |Real.log (p q.1)|
        ≤ gaussianPdf1D t q.2 * f1 (q.1 - q.2) * (A + B * q.1 ^ 2) :=
          mul_le_mul_of_nonneg_left hl hnn
      _ ≤ gaussianPdf1D t q.2 * f1 (q.1 - q.2) * (A + B * (2 * q.2 ^ 2 + 2 * (q.1 - q.2) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hnn
      _ = A * (gaussianPdf1D t q.2 * f1 (q.1 - q.2)) +
          2 * B * (q.2 ^ 2 * gaussianPdf1D t q.2) * f1 (q.1 - q.2) +
          gaussianPdf1D t q.2 * (2 * B * ((q.1 - q.2) ^ 2 * f1 (q.1 - q.2))) := by ring
  have hT3 : Integrable (fun q : ℝ × ℝ => p q.1 * gaussianPdf1D t q.2) (volume.prod volume) :=
    hp_int.mul_prod hg1
  have hT4 : Integrable (fun q : ℝ × ℝ => gaussianPdf1D t q.2 * f1 (q.1 - q.2)) (volume.prod volume) :=
    ep_integrable_prod_shear hg1 hf1
  have hT12 : Integrable (fun q : ℝ × ℝ =>
      gaussianPdf1D t q.2 * flog (q.1 - q.2) +
      -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1))) (volume.prod volume) := hT1.add hT2
  have hT123 : Integrable (fun q : ℝ × ℝ =>
      gaussianPdf1D t q.2 * flog (q.1 - q.2) +
      -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1)) +
      p q.1 * gaussianPdf1D t q.2) (volume.prod volume) := hT12.add hT3
  have hnn_int : 0 ≤ ∫ q : ℝ × ℝ,
      (gaussianPdf1D t q.2 * flog (q.1 - q.2) +
       -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1)) +
       p q.1 * gaussianPdf1D t q.2 -
       gaussianPdf1D t q.2 * f1 (q.1 - q.2)) ∂(volume.prod volume) := by
    refine integral_nonneg fun q => ?_
    have hpp : 0 < p q.1 := hp_pos q.1
    have hgnn : 0 ≤ gaussianPdf1D t q.2 := gaussianPdf1D_nonneg ht.le _
    by_cases hfx : f1 (q.1 - q.2) ≤ 0
    · have hf0 : f1 (q.1 - q.2) = 0 := le_antisymm hfx (f.nonneg _)
      have h0 : gaussianPdf1D t q.2 * flog (q.1 - q.2) +
          -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1)) +
          p q.1 * gaussianPdf1D t q.2 -
          gaussianPdf1D t q.2 * f1 (q.1 - q.2) = p q.1 * gaussianPdf1D t q.2 := by
        simp [flog, hf0]
      rw [h0]
      exact mul_nonneg hpp.le hgnn
    · have hfpos : 0 < f1 (q.1 - q.2) := lt_of_not_ge hfx
      have hkl : 0 ≤ InformationTheory.klFun (f1 (q.1 - q.2) / p q.1) :=
        InformationTheory.klFun_nonneg (div_nonneg hfpos.le hpp.le)
      unfold InformationTheory.klFun at hkl
      have hmul := mul_nonneg (mul_nonneg hgnn hpp.le) hkl
      have hident : gaussianPdf1D t q.2 * p q.1 *
          (f1 (q.1 - q.2) / p q.1 * Real.log (f1 (q.1 - q.2) / p q.1) +
            1 - f1 (q.1 - q.2) / p q.1) =
          gaussianPdf1D t q.2 * flog (q.1 - q.2) +
          -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1)) +
          p q.1 * gaussianPdf1D t q.2 -
          gaussianPdf1D t q.2 * f1 (q.1 - q.2) := by
        simp only [flog, hfx, ↓reduceIte]
        rw [Real.log_div (ne_of_gt hfpos) (ne_of_gt hpp)]
        have hpne : p q.1 ≠ 0 := ne_of_gt hpp
        field_simp [hpne]
        ring
      rwa [hident] at hmul
  rw [integral_sub hT123 hT4, integral_add hT12 hT3, integral_add hT1 hT2] at hnn_int
  have hI1 : ∫ q : ℝ × ℝ, gaussianPdf1D t q.2 * flog (q.1 - q.2) ∂(volume.prod volume) =
      -diffEntropy f := by
    rw [ep_integral_prod_shear hg1 hflog_int, ep_integral_gaussianPdf1D ht, one_mul]
    unfold diffEntropy
    rw [ep_integral_fin1, ← integral_neg]
    congr 1; funext u
    dsimp only [flog, f1]; split_ifs <;> ring
  have hI2 : ∫ q : ℝ × ℝ, -(gaussianPdf1D t q.2 * f1 (q.1 - q.2) * Real.log (p q.1))
      ∂(volume.prod volume) = diffEntropy (awgnOutputDensity f t ht) := by
    rw [integral_prod _ hT2]
    unfold diffEntropy
    rw [ep_integral_fin1]
    congr 1; funext y
    have hpull : (fun z : ℝ => -(gaussianPdf1D t z * f1 (y - z) * Real.log (p y))) =
        fun z : ℝ => (gaussianPdf1D t z * f1 (y - z)) * (-Real.log (p y)) := by funext z; ring
    rw [hpull, integral_mul_const]
    have hp_eq : ∫ z : ℝ, gaussianPdf1D t z * f1 (y - z) = p y := by
      rw [ep_conv_fun_comm (gaussianPdf1D t) f1 y]
      dsimp only [p, f1]
      rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]; rfl
    rw [hp_eq, ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr (hp_pos y))]; ring
  have hI3 : ∫ q : ℝ × ℝ, p q.1 * gaussianPdf1D t q.2 ∂(volume.prod volume) = 1 := by
    rw [integral_prod_mul, ep_pdf1_integral_one (awgnOutputDensity f t ht),
      ep_integral_gaussianPdf1D ht, mul_one]
  have hI4 : ∫ q : ℝ × ℝ, gaussianPdf1D t q.2 * f1 (q.1 - q.2) ∂(volume.prod volume) = 1 := by
    rw [ep_integral_prod_shear hg1 hf1, ep_integral_gaussianPdf1D ht, ep_pdf1_integral_one f, mul_one]
  rw [hI1, hI2, hI3, hI4] at hnn_int
  linarith

/-- **Large-Noise Asymptotics of Gaussian-Smoothed Differential Entropy**:
    `h(X + √t Z) - ½ ln(2π e t) → 0` as `t → ∞` (by the sandwich `0 ≤ h(X + √t Z) - h(√t Z) ≤ ½ ln(1 + E[X²]/t)`). -/
theorem tendsto_awgnDiffEntropy_sub_gaussian (f : Density 1) (hm2 : HasFiniteSecondMoment f) :
    Tendsto (fun t : ℝ => awgnDiffEntropy f t - (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * t))
      atTop (𝓝 0) := by
  set M2 : ℝ := ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x
  have hM2_nn : 0 ≤ M2 := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (f.nonneg x)
  have hupper_tendsto : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.log (1 + M2 / t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => M2 / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun t : ℝ => 1 + M2 / t) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add h1
    have h3 : Tendsto (fun t : ℝ => Real.log (1 + M2 / t)) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log one_ne_zero).tendsto.comp h2
    rw [Real.log_one] at h3
    simpa using h3.const_mul (1 / 2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tendsto ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [awgnDiffEntropy_eq f ht, ← diffEntropy_gaussianDensity1D ht]
    linarith [awgn_mutualInfo_nonneg f hm2 ht]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [awgnDiffEntropy_eq f ht, ← diffEntropy_gaussianDensity1D ht]
    exact awgn_mutualInfo_le_capacity f hM2_nn ht hm2
      (hasFiniteDiffEntropy_awgnOutputDensity f hm2 ht) le_rfl

/-- **Blachman–Stam Monotonicity** (`F'(t) ≤ 0` on `(0, ∞)`):
    for any finite-second-moment `f, g`, `r ∈ (0, 1)`, and `t₀ > 0`,
    `-(1/2) (r ln r + (1 - r) ln(1 - r)) ≤ h((f * g)_{t₀}) - r h(f_{r t₀}) - (1 - r) h(g_{(1 - r) t₀})`. -/
theorem diffEntropy_conv_ge_weighted_awgn (f g : Density 1)
    (hf : HasFiniteSecondMoment f) (hg : HasFiniteSecondMoment g)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    -(1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r)) ≤
      awgnDiffEntropy (convDensity f g) t₀ -
        r * awgnDiffEntropy f (r * t₀) - (1 - r) * awgnDiffEntropy g ((1 - r) * t₀) := by
  have h1mr : 0 < 1 - r := sub_pos.mpr hr1
  have hfg : HasFiniteSecondMoment (convDensity f g) := hasFiniteSecondMoment_convDensity f g hf hg
  let F : ℝ → ℝ := fun t =>
    awgnDiffEntropy (convDensity f g) t -
      r * awgnDiffEntropy f (r * t) - (1 - r) * awgnDiffEntropy g ((1 - r) * t)
  -- Derivative of `F` on `t > 0` via De Bruijn + Stam.
  have hF_deriv : ∀ t (ht : 0 < t),
      HasDerivAt F ((1 / 2 : ℝ) * (fisherInfo (awgnOutputDensity (convDensity f g) t ht) -
        r ^ 2 * fisherInfo (awgnOutputDensity f (r * t) (mul_pos hr0 ht)) -
        (1 - r) ^ 2 * fisherInfo (awgnOutputDensity g ((1 - r) * t) (mul_pos h1mr ht)))) t := by
    intro t ht
    have h1 := de_bruijn_identity (convDensity f g) hfg ht
    have hrt : 0 < r * t := mul_pos hr0 ht
    have h1rt : 0 < (1 - r) * t := mul_pos h1mr ht
    have h2_inner : HasDerivAt (fun s : ℝ => r * s) r t := by
      simpa using (hasDerivAt_id t).const_mul r
    have h2 := ((de_bruijn_identity f hf hrt).comp t h2_inner).const_mul r
    have h3_inner : HasDerivAt (fun s : ℝ => (1 - r) * s) (1 - r) t := by
      simpa using (hasDerivAt_id t).const_mul (1 - r)
    have h3 := ((de_bruijn_identity g hg h1rt).comp t h3_inner).const_mul (1 - r)
    have hcomb := (h1.sub h2).sub h3
    refine hcomb.congr_deriv ?_
    ring
  have hF_nonpos : ∀ t (ht : 0 < t),
      (1 / 2 : ℝ) * (fisherInfo (awgnOutputDensity (convDensity f g) t ht) -
        r ^ 2 * fisherInfo (awgnOutputDensity f (r * t) (mul_pos hr0 ht)) -
        (1 - r) ^ 2 * fisherInfo (awgnOutputDensity g ((1 - r) * t) (mul_pos h1mr ht))) ≤ 0 := by
    intro t ht
    have hrt : 0 < r * t := mul_pos hr0 ht
    have h1rt : 0 < (1 - r) * t := mul_pos h1mr ht
    have hstam := stam_weighted_inequality_awgn f g hrt h1rt (show r + (1 - r) = 1 by ring)
    have hsum : r * t + (1 - r) * t = t := by ring
    have heq : convDensity (awgnOutputDensity f (r * t) hrt) (awgnOutputDensity g ((1 - r) * t) h1rt) =
        awgnOutputDensity (convDensity f g) t ht := by
      rw [convDensity_awgn f g hrt h1rt]
      refine ep_density_ext fun z => ?_
      simp_rw [hsum]
    rw [heq] at hstam
    linarith
  have hF_anti : AntitoneOn F (Set.Ioi 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (f' := fun t => if ht : 0 < t then
        (1 / 2 : ℝ) * (fisherInfo (awgnOutputDensity (convDensity f g) t ht) -
          r ^ 2 * fisherInfo (awgnOutputDensity f (r * t) (mul_pos hr0 ht)) -
          (1 - r) ^ 2 * fisherInfo (awgnOutputDensity g ((1 - r) * t) (mul_pos h1mr ht)))
        else 0) ?_ ?_ ?_
    · intro t ht
      exact (hF_deriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      have ht' : 0 < t := ht
      have hd : HasDerivWithinAt F
          ((1 / 2 : ℝ) * (fisherInfo (awgnOutputDensity (convDensity f g) t ht') -
            r ^ 2 * fisherInfo (awgnOutputDensity f (r * t) (mul_pos hr0 ht')) -
            (1 - r) ^ 2 * fisherInfo (awgnOutputDensity g ((1 - r) * t) (mul_pos h1mr ht'))))
          (interior (Set.Ioi 0)) t := (hF_deriv t ht').hasDerivWithinAt
      simpa [ht'] using hd
    · intro t ht
      rw [interior_Ioi] at ht
      have ht' : 0 < t := ht
      simp only [ht', ↓reduceDIte]
      exact hF_nonpos t ht'
  -- Limit of `F t` as `t → ∞`.
  have hF_tendsto : Tendsto F atTop
      (𝓝 (-(1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r)))) := by
    have hL1 := tendsto_awgnDiffEntropy_sub_gaussian (convDensity f g) hfg
    have hL2 := ((tendsto_awgnDiffEntropy_sub_gaussian f hf).comp
      (tendsto_id.const_mul_atTop hr0)).const_mul r
    have hL3 := ((tendsto_awgnDiffEntropy_sub_gaussian g hg).comp
      (tendsto_id.const_mul_atTop h1mr)).const_mul (1 - r)
    have hcomb := ((hL1.sub hL2).sub hL3).add
      (tendsto_const_nhds (x := -(1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r))))
    have hlim : (0 : ℝ) - r * 0 - (1 - r) * 0 +
        -(1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r)) =
        -(1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r)) := by ring
    rw [hlim] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h2pie : 0 < 2 * Real.pi * Real.exp 1 * t := by positivity
    have hlog_r : Real.log (2 * Real.pi * Real.exp 1 * (r * t)) =
        Real.log (2 * Real.pi * Real.exp 1 * t) + Real.log r := by
      have : 2 * Real.pi * Real.exp 1 * (r * t) = (2 * Real.pi * Real.exp 1 * t) * r := by ring
      rw [this, Real.log_mul (ne_of_gt h2pie) (ne_of_gt hr0)]
    have hlog_1r : Real.log (2 * Real.pi * Real.exp 1 * ((1 - r) * t)) =
        Real.log (2 * Real.pi * Real.exp 1 * t) + Real.log (1 - r) := by
      have : 2 * Real.pi * Real.exp 1 * ((1 - r) * t) = (2 * Real.pi * Real.exp 1 * t) * (1 - r) := by ring
      rw [this, Real.log_mul (ne_of_gt h2pie) (ne_of_gt h1mr)]
    dsimp only [F, Function.comp_apply, id_eq]
    rw [hlog_r, hlog_1r]
    ring
  refine le_of_tendsto hF_tendsto ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  exact hF_anti ht₀ (lt_of_lt_of_le ht₀ ht) ht

/-- Algebraic conversion from the concave Shannon–Stam inequality (holding for all `r ∈ (0, 1)`)
    to the standard Entropy Power Inequality `N₁ + N₂ ≤ N₃`. -/
private lemma ep_entropyPower_of_weighted_diffEntropy {h₁ h₂ h₃ : ℝ}
    (hw : ∀ r : ℝ, 0 < r → r < 1 →
      r * h₁ + (1 - r) * h₂ - (1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r)) ≤ h₃) :
    (1 / (2 * Real.pi * Real.exp 1)) * Real.exp (2 * h₁) +
      (1 / (2 * Real.pi * Real.exp 1)) * Real.exp (2 * h₂) ≤
      (1 / (2 * Real.pi * Real.exp 1)) * Real.exp (2 * h₃) := by
  set c : ℝ := 1 / (2 * Real.pi * Real.exp 1)
  have hc : 0 < c := by positivity
  set N₁ : ℝ := c * Real.exp (2 * h₁)
  set N₂ : ℝ := c * Real.exp (2 * h₂)
  set N₃ : ℝ := c * Real.exp (2 * h₃)
  have hN₁ : 0 < N₁ := mul_pos hc (Real.exp_pos _)
  have hN₂ : 0 < N₂ := mul_pos hc (Real.exp_pos _)
  have hS : 0 < N₁ + N₂ := add_pos hN₁ hN₂
  set r : ℝ := N₁ / (N₁ + N₂)
  have hr0 : 0 < r := div_pos hN₁ hS
  have hr1 : r < 1 := (div_lt_one hS).mpr (by linarith)
  have h1mr : 1 - r = N₂ / (N₁ + N₂) := by
    dsimp only [r]; field_simp [ne_of_gt hS]; ring
  have h_ineq := hw r hr0 hr1
  -- Show `2 * (r * h₁ + (1 - r) * h₂ - ½ (r ln r + (1 - r) ln(1 - r))) = ln ((N₁ + N₂) / c)`.
  have h2h1 : 2 * h₁ = Real.log (N₁ / c) := by
    dsimp only [N₁]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hc), Real.log_exp]
  have h2h2 : 2 * h₂ = Real.log (N₂ / c) := by
    dsimp only [N₂]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hc), Real.log_exp]
  have hlhs_eq : 2 * (r * h₁ + (1 - r) * h₂ - (1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r))) =
      Real.log ((N₁ + N₂) / c) := by
    have hstep : 2 * (r * h₁ + (1 - r) * h₂ - (1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r))) =
        r * (2 * h₁ - Real.log r) + (1 - r) * (2 * h₂ - Real.log (1 - r)) := by ring
    rw [hstep, h2h1, h2h2,
      ← Real.log_div (ne_of_gt (div_pos hN₁ hc)) (ne_of_gt hr0),
      ← Real.log_div (ne_of_gt (div_pos hN₂ hc)) (ne_of_gt (sub_pos.mpr hr1))]
    have hd1 : (N₁ / c) / r = (N₁ + N₂) / c := by
      dsimp only [r]; field_simp [ne_of_gt hc, ne_of_gt hN₁, ne_of_gt hS]
    have hd2 : (N₂ / c) / (1 - r) = (N₁ + N₂) / c := by
      rw [h1mr]; field_simp [ne_of_gt hc, ne_of_gt hN₂, ne_of_gt hS]
    rw [hd1, hd2]
    ring
  have hle_exp : Real.log ((N₁ + N₂) / c) ≤ 2 * h₃ := by linarith
  have hexp := Real.exp_le_exp.mpr hle_exp
  rw [Real.exp_log (div_pos hS hc)] at hexp
  have hmul := mul_le_mul_of_nonneg_left hexp hc.le
  rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at hmul

/-- **Shannon's 1D Entropy Power Inequality for Gaussian-Smoothed Densities**:
    `N(f_a) + N(g_b) ≤ N(f_a * g_b)` for any finite-second-moment `f, g` and `a, b > 0`. -/
theorem entropyPower_add_ge_of_awgn (f g : Density 1)
    (hf : HasFiniteSecondMoment f) (hg : HasFiniteSecondMoment g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    entropyPower (awgnOutputDensity f a ha) + entropyPower (awgnOutputDensity g b hb) ≤
      entropyPower (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)) := by
  unfold entropyPower
  simp only [Nat.cast_one, div_one]
  refine ep_entropyPower_of_weighted_diffEntropy fun r hr0 hr1 => ?_
  have hfa : HasFiniteSecondMoment (awgnOutputDensity f a ha) :=
    hasFiniteSecondMoment_awgnOutputDensity f hf ha
  have hgb : HasFiniteSecondMoment (awgnOutputDensity g b hb) :=
    hasFiniteSecondMoment_awgnOutputDensity g hg hb
  have hfg : HasFiniteSecondMoment (convDensity f g) :=
    hasFiniteSecondMoment_convDensity f g hf hg
  have h1mr : 0 < 1 - r := sub_pos.mpr hr1
  -- Apply Blachman–Stam to `f_a` and `g_b` at `t₀ > 0`, and let `t₀ → 0⁺`.
  have hcont_fg : ContinuousAt (awgnDiffEntropy (convDensity f g)) (a + b) :=
    (de_bruijn_identity (convDensity f g) hfg (add_pos ha hb)).continuousAt
  have hcont_f : ContinuousAt (awgnDiffEntropy f) a :=
    (de_bruijn_identity f hf ha).continuousAt
  have hcont_g : ContinuousAt (awgnDiffEntropy g) b :=
    (de_bruijn_identity g hg hb).continuousAt
  have hT_fg : Tendsto (fun t : ℝ => awgnDiffEntropy (convDensity f g) (a + b + t))
      (𝓝[>] 0) (𝓝 (diffEntropy (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)))) := by
    rw [convDensity_awgn f g ha hb, ← awgnDiffEntropy_eq (convDensity f g) (add_pos ha hb)]
    have hlin : Tendsto (fun t : ℝ => a + b + t) (𝓝[>] 0) (𝓝 (a + b)) := by
      have : Tendsto (fun t : ℝ => a + b + t) (𝓝 0) (𝓝 (a + b + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hcont_fg.tendsto.comp hlin
  have hT_f : Tendsto (fun t : ℝ => awgnDiffEntropy f (a + r * t))
      (𝓝[>] 0) (𝓝 (diffEntropy (awgnOutputDensity f a ha))) := by
    rw [← awgnDiffEntropy_eq f ha]
    have hlin : Tendsto (fun t : ℝ => a + r * t) (𝓝[>] 0) (𝓝 a) := by
      have : Tendsto (fun t : ℝ => a + r * t) (𝓝 0) (𝓝 (a + r * 0)) :=
        tendsto_const_nhds.add (tendsto_id.const_mul r)
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hcont_f.tendsto.comp hlin
  have hT_g : Tendsto (fun t : ℝ => awgnDiffEntropy g (b + (1 - r) * t))
      (𝓝[>] 0) (𝓝 (diffEntropy (awgnOutputDensity g b hb))) := by
    rw [← awgnDiffEntropy_eq g hb]
    have hlin : Tendsto (fun t : ℝ => b + (1 - r) * t) (𝓝[>] 0) (𝓝 b) := by
      have : Tendsto (fun t : ℝ => b + (1 - r) * t) (𝓝 0) (𝓝 (b + (1 - r) * 0)) :=
        tendsto_const_nhds.add (tendsto_id.const_mul (1 - r))
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hcont_g.tendsto.comp hlin
  have hT_comb := (hT_fg.sub (hT_f.const_mul r)).sub (hT_g.const_mul (1 - r))
  have hle : -(1 / 2 : ℝ) * (r * Real.log r + (1 - r) * Real.log (1 - r)) ≤
      diffEntropy (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)) -
        r * diffEntropy (awgnOutputDensity f a ha) -
        (1 - r) * diffEntropy (awgnOutputDensity g b hb) := by
    refine ge_of_tendsto hT_comb ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hbs := diffEntropy_conv_ge_weighted_awgn (awgnOutputDensity f a ha)
      (awgnOutputDensity g b hb) hfa hgb hr0 hr1 ht
    have heq1 : awgnDiffEntropy (convDensity (awgnOutputDensity f a ha) (awgnOutputDensity g b hb)) t =
        awgnDiffEntropy (convDensity f g) (a + b + t) := by
      rw [awgnDiffEntropy_eq _ ht, awgnDiffEntropy_eq _ (by positivity),
        convDensity_awgn f g ha hb, awgnOutputDensity_awgnOutputDensity]
    have heq2 : awgnDiffEntropy (awgnOutputDensity f a ha) (r * t) =
        awgnDiffEntropy f (a + r * t) := by
      rw [awgnDiffEntropy_eq _ (mul_pos hr0 ht), awgnDiffEntropy_eq _ (by positivity),
        awgnOutputDensity_awgnOutputDensity]
    have heq3 : awgnDiffEntropy (awgnOutputDensity g b hb) ((1 - r) * t) =
        awgnDiffEntropy g (b + (1 - r) * t) := by
      rw [awgnDiffEntropy_eq _ (mul_pos h1mr ht), awgnDiffEntropy_eq _ (by positivity),
        awgnOutputDensity_awgnOutputDensity]
    rwa [heq1, heq2, heq3] at hbs
  linarith

/-! #### Continuity of `h(f_t)` at `t = 0⁺` via `L¹` Approximation and Fatou's Lemma -/

private lemma ep_tendsto_L1_shift {h : ℝ → ℝ} (hh : Integrable h volume) :
    Tendsto (fun s : ℝ => ∫ y : ℝ, |h (y - s) - h y|) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨g, hg_supp, hg_close, hg_cont, hg_int⟩ :=
    hh.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 4 by linarith)
  have hcomp_supp : IsCompact (tsupport g) := hg_supp
  obtain ⟨R, hR⟩ := hcomp_supp.isBounded.subset_closedBall (0 : ℝ)
  set R0 : ℝ := max R 0
  have hR0 : 0 ≤ R0 := le_max_right R 0
  have hsupp_Icc : ∀ x : ℝ, R0 < |x| → g x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport g := subset_tsupport g hne
    have hball := hR hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
    have : R ≤ R0 := le_max_left R 0
    linarith
  have hg_unif : UniformContinuous g := hg_supp.uniformContinuous_of_continuous hg_cont
  have hvol_pos : 0 < 2 * (R0 + 1) := by linarith
  obtain ⟨δ0, hδ0, hδ_unif⟩ := Metric.uniformContinuous_iff.mp hg_unif
    (ε / (4 * (2 * (R0 + 1)))) (by positivity)
  refine ⟨min δ0 1, lt_min hδ0 one_pos, fun s hs => ?_⟩
  rw [Real.dist_eq, sub_zero] at hs ⊢
  have hs_δ : |s| < δ0 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs_1 : |s| < 1 := lt_of_lt_of_le hs (min_le_right _ _)
  have hnn : 0 ≤ ∫ y : ℝ, |h (y - s) - h y| := integral_nonneg fun y => abs_nonneg _
  rw [abs_of_nonneg hnn]
  have h1 : Integrable (fun y : ℝ => |h (y - s) - g (y - s)|) volume :=
    ((hh.sub hg_int).comp_sub_right s).norm
  have h2 : Integrable (fun y : ℝ => |g (y - s) - g y|) volume :=
    ((hg_int.comp_sub_right s).sub hg_int).norm
  have h3 : Integrable (fun y : ℝ => |g y - h y|) volume := (hg_int.sub hh).norm
  have hlhs_int : Integrable (fun y : ℝ => |h (y - s) - h y|) volume :=
    ((hh.comp_sub_right s).sub hh).norm
  have h12 : Integrable (fun y : ℝ => |h (y - s) - g (y - s)| + |g (y - s) - g y|) volume := h1.add h2
  have htri : ∫ y : ℝ, |h (y - s) - h y| ≤
      (∫ y : ℝ, |h (y - s) - g (y - s)|) + (∫ y : ℝ, |g (y - s) - g y|) + (∫ y : ℝ, |g y - h y|) := by
    rw [← integral_add h1 h2, ← integral_add h12 h3]
    refine integral_mono hlhs_int (h12.add h3) fun y => ?_
    have t1 := abs_sub_le (h (y - s)) (g (y - s)) (h y)
    have t2 := abs_sub_le (g (y - s)) (g y) (h y)
    linarith
  have hI1 : ∫ y : ℝ, |h (y - s) - g (y - s)| ≤ ε / 4 := by
    rw [integral_sub_right_eq_self (fun u : ℝ => |h u - g u|) s]
    simpa [Real.norm_eq_abs] using hg_close
  have hI3 : ∫ y : ℝ, |g y - h y| ≤ ε / 4 := by
    have hsym : (fun y : ℝ => |g y - h y|) = fun y : ℝ => ‖h y - g y‖ := by
      funext y; rw [Real.norm_eq_abs, abs_sub_comm]
    rw [hsym]; exact hg_close
  have hI2 : ∫ y : ℝ, |g (y - s) - g y| ≤ ε / 4 := by
    let S : Set ℝ := Set.Icc (-(R0 + 1)) (R0 + 1)
    let bound : ℝ := ε / (4 * (2 * (R0 + 1)))
    have hpt : ∀ y : ℝ, |g (y - s) - g y| ≤ S.indicator (fun _ => bound) y := by
      intro y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        have hdist : dist (y - s) y < δ0 := by
          rw [Real.dist_eq]
          have : y - s - y = -s := by ring
          rw [this, abs_neg]; exact hs_δ
        exact (hδ_unif hdist).le
      · rw [Set.indicator_of_notMem hy]
        have hy_gt : R0 + 1 < |y| := by
          simp only [S, Set.mem_Icc, not_and_or, not_le] at hy
          rcases hy with hlt | hgt
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have hy_s_gt : R0 < |y - s| := by
          have : |y| - |s| ≤ |y - s| := abs_sub_abs_le_abs_sub y s
          linarith
        rw [hsupp_Icc (y - s) hy_s_gt, hsupp_Icc y (by linarith), sub_self, abs_zero]
    have hbound_int : Integrable (S.indicator (fun _ : ℝ => bound)) volume :=
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne)).integrable_indicator
        measurableSet_Icc
    have hmono := integral_mono h2 hbound_int hpt
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
      Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hmono
    have hcalc : (R0 + 1 - -(R0 + 1)) * bound = ε / 4 := by
      dsimp only [bound]
      have hne : 2 * (R0 + 1) ≠ 0 := ne_of_gt hvol_pos
      have : R0 + 1 - -(R0 + 1) = 2 * (R0 + 1) := by ring
      rw [this]; field_simp [hne]
    linarith [hmono, hcalc]
  linarith

/-- `f_{t_n} → f` in `L¹(ℝ)` along `t_n = 1 / (n + 1)`. -/
private lemma ep_tendsto_L1_awgn_seq (f : Density 1) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, |(awgnOutputDensity f (1 / (n + 1 : ℝ)) (by positivity)).pdf (fun _ => y) -
        f.pdf (fun _ => y)|) atTop (𝓝 0) := by
  let f1 : ℝ → ℝ := fun x => f.pdf (fun _ => x)
  have hf1 : Integrable f1 volume := ep_pdf1_integrable f
  have hshift := ep_tendsto_L1_shift hf1
  let G : ℕ → ℝ → ℝ := fun n u =>
    gaussianPdf1D 1 u * ∫ y : ℝ, |f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u) - f1 y|
  have hG_tendsto : Tendsto (fun n : ℕ => ∫ u : ℝ, G n u) atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ u : ℝ, (0 : ℝ) := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence (fun u : ℝ => 2 * gaussianPdf1D 1 u) ?_ ?_ ?_ ?_
    · intro n
      have hcont_inner : Continuous (fun u : ℝ => ∫ y : ℝ, |f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u) - f1 y|) := by
        rw [continuous_iff_continuousAt]
        intro u₀
        rw [Metric.continuousAt_iff]
        intro ε hε
        obtain ⟨δ, hδ, hδ_shift⟩ := Metric.tendsto_nhds_nhds.mp hshift ε hε
        have hsqrt_pos : 0 < Real.sqrt (1 / (n + 1 : ℝ)) := Real.sqrt_pos.mpr (by positivity)
        refine ⟨δ / Real.sqrt (1 / (n + 1 : ℝ)), div_pos hδ hsqrt_pos, fun u hu => ?_⟩
        rw [Real.dist_eq] at hu ⊢
        set s : ℝ := Real.sqrt (1 / (n + 1 : ℝ)) * u
        set s₀ : ℝ := Real.sqrt (1 / (n + 1 : ℝ)) * u₀
        have hs_diff : |s - s₀| < δ := by
          have : s - s₀ = Real.sqrt (1 / (n + 1 : ℝ)) * (u - u₀) := by dsimp only [s, s₀]; ring
          rw [this, abs_mul, abs_of_pos hsqrt_pos]
          exact (lt_div_iff₀' hsqrt_pos).mp hu
        have hint_s : Integrable (fun y : ℝ => |f1 (y - s) - f1 y|) volume :=
          ((hf1.comp_sub_right s).sub hf1).norm
        have hint_s0 : Integrable (fun y : ℝ => |f1 (y - s₀) - f1 y|) volume :=
          ((hf1.comp_sub_right s₀).sub hf1).norm
        have hint_diff : Integrable (fun y : ℝ => |f1 (y - s) - f1 (y - s₀)|) volume :=
          ((hf1.comp_sub_right s).sub (hf1.comp_sub_right s₀)).norm
        have hlip : |(∫ y : ℝ, |f1 (y - s) - f1 y|) - (∫ y : ℝ, |f1 (y - s₀) - f1 y|)| ≤
            ∫ y : ℝ, |f1 (y - s) - f1 (y - s₀)| := by
          rw [← integral_sub hint_s hint_s0]
          refine le_trans abs_integral_le_integral_abs ?_
          refine integral_mono (hint_s.sub hint_s0).norm hint_diff fun y => ?_
          have := abs_abs_sub_abs_le_abs_sub (f1 (y - s) - f1 y) (f1 (y - s₀) - f1 y)
          simpa [sub_sub_sub_cancel_right] using this
        have hshift_eq : ∫ y : ℝ, |f1 (y - s) - f1 (y - s₀)| = ∫ y : ℝ, |f1 (y - (s - s₀)) - f1 y| := by
          have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
            (fun y : ℝ => |f1 (y - (s - s₀)) - f1 y|) s₀
          refine Eq.trans ?_ h
          congr 1; funext y
          have : y - s₀ - (s - s₀) = y - s := by ring
          rw [this]
        rw [hshift_eq] at hlip
        have hlt := hδ_shift (by simpa [Real.dist_eq] using hs_diff)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at hlt
        exact lt_of_le_of_lt hlip hlt
      exact ((ep_continuous_gaussianPdf1D 1).mul hcont_inner).aestronglyMeasurable
    · exact (ep_integrable_gaussianPdf1D one_pos).const_mul 2
    · intro n
      refine ae_of_all _ fun u => ?_
      dsimp only [G]
      have hnn_int : 0 ≤ ∫ y : ℝ, |f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u) - f1 y| :=
        integral_nonneg fun _ => abs_nonneg _
      rw [Real.norm_of_nonneg (mul_nonneg (gaussianPdf1D_nonneg zero_le_one u) hnn_int)]
      have hle2 : ∫ y : ℝ, |f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u) - f1 y| ≤ 2 := by
        have hint_a : Integrable (fun y : ℝ => ‖f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u)‖) volume :=
          (hf1.comp_sub_right (Real.sqrt (1 / (n + 1 : ℝ)) * u)).norm
        have hint_b : Integrable (fun y : ℝ => ‖f1 y‖) volume := hf1.norm
        have hint_lhs : Integrable (fun y : ℝ => |f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u) - f1 y|) volume :=
          ((hf1.comp_sub_right (Real.sqrt (1 / (n + 1 : ℝ)) * u)).sub hf1).norm
        have hint_ab : Integrable (fun y : ℝ => ‖f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u)‖ + ‖f1 y‖) volume :=
          hint_a.add hint_b
        have hle : ∫ y : ℝ, |f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u) - f1 y| ≤
            ∫ y : ℝ, (‖f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u)‖ + ‖f1 y‖) :=
          integral_mono hint_lhs hint_ab fun y => abs_sub _ _
        rw [integral_add hint_a hint_b] at hle
        have ha1 : ∫ y : ℝ, ‖f1 (y - Real.sqrt (1 / (n + 1 : ℝ)) * u)‖ = 1 := by
          rw [integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun x : ℝ => ‖f1 x‖)]
          have hpos : (fun x : ℝ => ‖f1 x‖) = f1 := funext fun x => Real.norm_of_nonneg (f.nonneg _)
          rw [hpos]; exact ep_pdf1_integral_one f
        have hb1 : ∫ y : ℝ, ‖f1 y‖ = 1 := by
          have hpos : (fun x : ℝ => ‖f1 x‖) = f1 := funext fun x => Real.norm_of_nonneg (f.nonneg _)
          rw [hpos]; exact ep_pdf1_integral_one f
        linarith
      nlinarith [gaussianPdf1D_nonneg zero_le_one u]
    · refine ae_of_all _ fun u => ?_
      dsimp only [G]
      have hsqrt_t : Tendsto (fun n : ℕ => Real.sqrt (1 / (n + 1 : ℝ)) * u) atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hs : Tendsto (fun n : ℕ => Real.sqrt (1 / (n + 1 : ℝ))) atTop (𝓝 (Real.sqrt 0)) :=
          Real.continuous_sqrt.continuousAt.tendsto.comp hinv
        rw [Real.sqrt_zero] at hs
        simpa using hs.mul_const u
      simpa using (hshift.comp hsqrt_t).const_mul (gaussianPdf1D 1 u)
  -- Sandwich: `0 ≤ ∫ |f_{t_n} - f| ≤ ∫ G n`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG_tendsto
    (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_)
  set t : ℝ := 1 / (n + 1 : ℝ)
  have ht : 0 < t := by positivity
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  -- Rewrite `f_t(y) - f(y) = ∫ u, φ_1(u) * (f1(y - √t u) - f1(y))`.
  have hdiff_eq : ∀ y : ℝ, (awgnOutputDensity f t ht).pdf (fun _ => y) - f1 y =
      ∫ u : ℝ, gaussianPdf1D 1 u * (f1 (y - Real.sqrt t * u) - f1 y) := by
    intro y
    have hft : (awgnOutputDensity f t ht).pdf (fun _ => y) =
        ∫ u : ℝ, gaussianPdf1D 1 u * f1 (y - Real.sqrt t * u) := by
      rw [← convDensity_gaussian_eq_awgn f ht, convDensity_pdf_eq]
      change ∫ x : ℝ, f1 x * gaussianPdf1D t (y - x) = _
      rw [ep_conv_fun_comm f1 (gaussianPdf1D t) y]
      -- Substitute `z = √t * u` using `Measure.integral_comp_mul_left`.
      have hscale := Measure.integral_comp_mul_left
        (fun z : ℝ => gaussianPdf1D t z * f1 (y - z)) (Real.sqrt t)
      have hst_ne : Real.sqrt t ≠ 0 := ne_of_gt hst
      have hst_abs : |Real.sqrt t| = Real.sqrt t := abs_of_pos hst
      have hpdf_scale : ∀ u : ℝ,
          Real.sqrt t * gaussianPdf1D t (Real.sqrt t * u) = gaussianPdf1D 1 u := by
        intro u
        unfold gaussianPdf1D
        have hsq : (Real.sqrt t * u) ^ 2 / (2 * t) = u ^ 2 / (2 * 1) := by
          rw [mul_pow, Real.sq_sqrt ht.le]
          have ht0 : t ≠ 0 := ne_of_gt ht; field_simp [ht0]
        have harg : -((Real.sqrt t * u) ^ 2) / (2 * t) = -(u ^ 2) / (2 * 1) := by
          have h1 : -((Real.sqrt t * u) ^ 2) / (2 * t) = -((Real.sqrt t * u) ^ 2 / (2 * t)) := by ring
          have h2 : -(u ^ 2) / (2 * 1) = -(u ^ 2 / (2 * 1)) := by ring
          rw [h1, h2, hsq]
        rw [harg]
        have hsqrt_t : Real.sqrt (2 * Real.pi * t) = Real.sqrt (2 * Real.pi * 1) * Real.sqrt t := by
          rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
        rw [hsqrt_t]
        have hs2pi : Real.sqrt (2 * Real.pi * 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
        field_simp [hst_ne, hs2pi]
      rw [abs_inv, hst_abs, smul_eq_mul] at hscale
      have hmul := congrArg (fun v => Real.sqrt t * v) hscale
      rw [← mul_assoc, mul_inv_cancel₀ hst_ne, one_mul, ← integral_const_mul] at hmul
      rw [← hmul]
      congr 1; funext u
      rw [← mul_assoc, hpdf_scale u]
    rw [hft]
    have h1 : ∫ u : ℝ, gaussianPdf1D 1 u * f1 y = f1 y := by
      rw [integral_mul_const, ep_integral_gaussianPdf1D one_pos, one_mul]
    have hint_a : Integrable (fun u : ℝ => gaussianPdf1D 1 u * f1 (y - Real.sqrt t * u)) volume := by
      have hmul_int : Integrable (fun u : ℝ => f1 (y - Real.sqrt t * u)) volume := by
        have hsub := hf1.comp_sub_left y
        exact (integrable_comp_mul_left_iff (g := fun z : ℝ => f1 (y - z)) (ne_of_gt hst)).mpr hsub
      have hdom := hmul_int.const_mul (1 / Real.sqrt (2 * Real.pi * 1))
      refine hdom.mono' ((ep_continuous_gaussianPdf1D 1).aestronglyMeasurable.mul
        hmul_int.aestronglyMeasurable) (ae_of_all _ fun u => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (gaussianPdf1D_nonneg zero_le_one u) (f.nonneg _))]
      have hle := ep_gaussianPdf1D_le_const one_pos u
      exact mul_le_mul_of_nonneg_right hle (f.nonneg _)
    have hint_b : Integrable (fun u : ℝ => gaussianPdf1D 1 u * f1 y) volume :=
      (ep_integrable_gaussianPdf1D one_pos).mul_const (f1 y)
    conv_lhs => rw [← h1]
    rw [← integral_sub hint_a hint_b]
    congr 1; funext u; ring
  have hprod_int : Integrable (fun p : ℝ × ℝ =>
      gaussianPdf1D 1 p.2 * |f1 (p.1 - Real.sqrt t * p.2) - f1 p.1|) (volume.prod volume) := by
    have hg1 := ep_integrable_gaussianPdf1D one_pos
    have hcomp_shift : Integrable (fun p : ℝ × ℝ => gaussianPdf1D 1 p.2 * f1 (p.1 - Real.sqrt t * p.2))
        (volume.prod volume) := by
      let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
        { toFun := fun p => (p.1 - Real.sqrt t * p.2, p.2)
          invFun := fun p => (p.1 + Real.sqrt t * p.2, p.2)
          left_inv := fun p => by simp
          right_inv := fun p => by simp
          measurable_toFun := (measurable_fst.sub (measurable_const.mul measurable_snd)).prodMk measurable_snd
          measurable_invFun := (measurable_fst.add (measurable_const.mul measurable_snd)).prodMk measurable_snd }
      have hmp : MeasurePreserving e ((volume : Measure ℝ).prod (volume : Measure ℝ))
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
        refine ⟨e.measurable, ?_⟩
        symm
        refine Measure.prod_eq (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) fun s₁ s₂ hs₁ hs₂ => ?_
        rw [Measure.map_apply e.measurable (hs₁.prod hs₂),
          Measure.prod_apply_symm (e.measurable (hs₁.prod hs₂))]
        have hsec : ∀ u : ℝ, (volume : Measure ℝ) ((fun y : ℝ => (y, u)) ⁻¹' (e ⁻¹' (s₁ ×ˢ s₂))) =
            s₂.indicator (fun _ => (volume : Measure ℝ) s₁) u := by
          intro u
          by_cases hu : u ∈ s₂
          · simp only [Set.indicator_of_mem hu]
            have hset : ((fun y : ℝ => (y, u)) ⁻¹' (e ⁻¹' (s₁ ×ˢ s₂))) =
                (fun y : ℝ => y - Real.sqrt t * u) ⁻¹' s₁ := by
              ext y; simp [e, hu]
            rw [hset]
            exact (measurePreserving_sub_right (volume : Measure ℝ) (Real.sqrt t * u)).measure_preimage
              hs₁.nullMeasurableSet
          · simp only [Set.indicator_of_notMem hu]
            have hset : ((fun y : ℝ => (y, u)) ⁻¹' (e ⁻¹' (s₁ ×ˢ s₂))) = ∅ := by
              ext y; simp [e, hu]
            rw [hset, measure_empty]
        simp_rw [hsec]
        rw [lintegral_indicator hs₂, lintegral_const, Measure.restrict_apply_univ]
      have hbase : Integrable (fun q : ℝ × ℝ => f1 q.1 * gaussianPdf1D 1 q.2) (volume.prod volume) :=
        hf1.mul_prod hg1
      have hcomp := (hmp.integrable_comp_emb e.measurableEmbedding).mpr hbase
      refine hcomp.congr (ae_of_all _ fun p => ?_)
      change f1 (p.1 - Real.sqrt t * p.2) * gaussianPdf1D 1 p.2 =
        gaussianPdf1D 1 p.2 * f1 (p.1 - Real.sqrt t * p.2)
      ring
    have hcomp_id : Integrable (fun p : ℝ × ℝ => gaussianPdf1D 1 p.2 * f1 p.1) (volume.prod volume) :=
      (hf1.mul_prod hg1).congr (ae_of_all _ fun p => mul_comm _ _)
    have hdom : Integrable (fun p : ℝ × ℝ =>
        gaussianPdf1D 1 p.2 * f1 (p.1 - Real.sqrt t * p.2) + gaussianPdf1D 1 p.2 * f1 p.1)
        (volume.prod volume) := hcomp_shift.add hcomp_id
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => gaussianPdf1D 1 p.2 * |f1 (p.1 - Real.sqrt t * p.2) - f1 p.1|)
        (volume.prod volume) := by
      refine (hcomp_shift.sub hcomp_id).norm.aestronglyMeasurable.congr (ae_of_all _ fun p => ?_)
      dsimp only [Pi.sub_apply]
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (gaussianPdf1D_nonneg zero_le_one p.2)]
    refine hdom.mono' hmeas (ae_of_all _ fun p => ?_)
    have hg_nn : 0 ≤ gaussianPdf1D 1 p.2 := gaussianPdf1D_nonneg zero_le_one p.2
    rw [Real.norm_of_nonneg (mul_nonneg hg_nn (abs_nonneg _))]
    have htri : |f1 (p.1 - Real.sqrt t * p.2) - f1 p.1| ≤ f1 (p.1 - Real.sqrt t * p.2) + f1 p.1 := by
      calc |f1 (p.1 - Real.sqrt t * p.2) - f1 p.1|
          ≤ |f1 (p.1 - Real.sqrt t * p.2)| + |f1 p.1| := abs_sub _ _
        _ = f1 (p.1 - Real.sqrt t * p.2) + f1 p.1 := by
            rw [abs_of_nonneg (f.nonneg _), abs_of_nonneg (f.nonneg _)]
    nlinarith
  have hlhs_int : Integrable (fun y : ℝ => |(awgnOutputDensity f t ht).pdf (fun _ => y) - f1 y|) volume :=
    ((ep_pdf1_integrable (awgnOutputDensity f t ht)).sub hf1).norm
  have h1 : ∫ y : ℝ, |(awgnOutputDensity f t ht).pdf (fun _ => y) - f1 y| ≤
      ∫ y : ℝ, ∫ u : ℝ, gaussianPdf1D 1 u * |f1 (y - Real.sqrt t * u) - f1 y| := by
    refine integral_mono hlhs_int hprod_int.integral_prod_left fun y => ?_
    rw [hdiff_eq y]
    refine le_trans abs_integral_le_integral_abs ?_
    refine le_of_eq ?_
    congr 1; funext u
    rw [abs_mul, abs_of_nonneg (gaussianPdf1D_nonneg zero_le_one u)]
  have h2 : ∫ y : ℝ, ∫ u : ℝ, gaussianPdf1D 1 u * |f1 (y - Real.sqrt t * u) - f1 y| =
      ∫ u : ℝ, G n u := by
    rw [integral_integral_swap hprod_int]
    congr 1; funext u
    dsimp only [G]
    rw [integral_const_mul]
  linarith

/-- KL divergence to `N(0, 1)` expressed via differential entropy and second moment:
    `∫ φ_1(y) klFun(f(y) / φ_1(y)) dy = -h(f) + ½ ln(2π) + ½ E[X²]`. -/
private lemma ep_kl_to_stdGaussian_eq (f : Density 1)
    (hf : HasFiniteDiffEntropy f) (hm2 : HasFiniteSecondMoment f) :
    ∫ y : ℝ, gaussianPdf1D 1 y * InformationTheory.klFun (f.pdf (fun _ => y) / gaussianPdf1D 1 y) =
      -diffEntropy f + (1 / 2 : ℝ) * Real.log (2 * Real.pi) +
        (1 / 2 : ℝ) * ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x := by
  let f1 : ℝ → ℝ := fun y => f.pdf (fun _ => y)
  let g : ℝ → ℝ := gaussianPdf1D 1
  have hpt : ∀ y : ℝ, g y * InformationTheory.klFun (f1 y / g y) =
      -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y +
        (1 / 2 : ℝ) * (y ^ 2 * f1 y) + g y - f1 y := by
    intro y
    have hgp : 0 < g y := gaussianPdf1D_pos one_pos y
    have hlogg : Real.log (g y) = -((1 / 2 : ℝ) * Real.log (2 * Real.pi)) - y ^ 2 / 2 := by
      simpa using log_gaussianPdf1D one_pos y
    by_cases hfx : f1 y ≤ 0
    · have hf0 : f1 y = 0 := le_antisymm hfx (f.nonneg _)
      rw [hf0]
      simp [InformationTheory.klFun]
    · have hfpos : 0 < f1 y := lt_of_not_ge hfx
      rw [ite_eq_right_iff.mpr fun h => absurd h hfx]
      unfold InformationTheory.klFun
      rw [Real.log_div (ne_of_gt hfpos) (ne_of_gt hgp), hlogg]
      have hgne : g y ≠ 0 := ne_of_gt hgp
      field_simp [hgne]
      ring
  change ∫ y : ℝ, g y * InformationTheory.klFun (f1 y / g y) = _
  simp_rw [hpt]
  have hf_int : Integrable f1 volume := ep_pdf1_integrable f
  have hg_int : Integrable g volume := ep_integrable_gaussianPdf1D one_pos
  have hm2_int : Integrable (fun y : ℝ => y ^ 2 * f1 y) volume := ep_secondMoment_integrable f hm2
  have hh_int : Integrable (fun y : ℝ => -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y))) volume := by
    unfold HasFiniteDiffEntropy at hf
    rw [ep_integrable_fin1_iff] at hf
    exact hf.neg
  have h1 : Integrable (fun y : ℝ => (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y) volume :=
    hf_int.const_mul ((1 / 2 : ℝ) * Real.log (2 * Real.pi))
  have h2 : Integrable (fun y : ℝ => (1 / 2 : ℝ) * (y ^ 2 * f1 y)) volume :=
    hm2_int.const_mul (1 / 2 : ℝ)
  have h01 : Integrable (fun y : ℝ =>
      -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y) volume := hh_int.add h1
  have h012 : Integrable (fun y : ℝ =>
      -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y + (1 / 2 : ℝ) * (y ^ 2 * f1 y)) volume := h01.add h2
  have h0123 : Integrable (fun y : ℝ =>
      -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y + (1 / 2 : ℝ) * (y ^ 2 * f1 y) + g y) volume :=
    h012.add hg_int
  rw [integral_sub h0123 hf_int, integral_add h012 hg_int, integral_add h01 h2,
    integral_add hh_int h1, integral_neg, integral_const_mul, integral_const_mul,
    ep_pdf1_integral_one f, ep_integral_gaussianPdf1D one_pos]
  have hdiff_eq : ∫ y : ℝ, (if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) = diffEntropy f := by
    unfold diffEntropy; rw [ep_integral_fin1]
  have hm2_eq : ∫ y : ℝ, y ^ 2 * f1 y = ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x := by
    rw [ep_integral_fin1 (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x)]
  rw [hdiff_eq, hm2_eq]
  ring

private lemma ep_integrable_kl_to_stdGaussian (f : Density 1)
    (hf : HasFiniteDiffEntropy f) (hm2 : HasFiniteSecondMoment f) :
    Integrable (fun y : ℝ =>
      gaussianPdf1D 1 y * InformationTheory.klFun (f.pdf (fun _ => y) / gaussianPdf1D 1 y)) volume := by
  let f1 : ℝ → ℝ := fun y => f.pdf (fun _ => y)
  have hpt : ∀ y : ℝ,
      -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y +
        (1 / 2 : ℝ) * (y ^ 2 * f1 y) + gaussianPdf1D 1 y - f1 y =
      gaussianPdf1D 1 y * InformationTheory.klFun (f1 y / gaussianPdf1D 1 y) := by
    intro y
    have hgp : 0 < gaussianPdf1D 1 y := gaussianPdf1D_pos one_pos y
    have hlogg : Real.log (gaussianPdf1D 1 y) = -((1 / 2 : ℝ) * Real.log (2 * Real.pi)) - y ^ 2 / 2 := by
      simpa using log_gaussianPdf1D one_pos y
    by_cases hfx : f1 y ≤ 0
    · have hf0 : f1 y = 0 := le_antisymm hfx (f.nonneg _)
      rw [hf0]
      simp [InformationTheory.klFun]
    · have hfpos : 0 < f1 y := lt_of_not_ge hfx
      rw [ite_eq_right_iff.mpr fun h => absurd h hfx]
      unfold InformationTheory.klFun
      rw [Real.log_div (ne_of_gt hfpos) (ne_of_gt hgp), hlogg]
      have hgne : gaussianPdf1D 1 y ≠ 0 := ne_of_gt hgp
      field_simp [hgne]; ring
  have hh_int : Integrable (fun y : ℝ => -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y))) volume := by
    unfold HasFiniteDiffEntropy at hf; rw [ep_integrable_fin1_iff] at hf; exact hf.neg
  have hf1_int : Integrable f1 volume := ep_pdf1_integrable f
  have hm2_int : Integrable (fun y : ℝ => y ^ 2 * f1 y) volume := ep_secondMoment_integrable f hm2
  have hsum : Integrable (fun y : ℝ =>
      -(if f1 y ≤ 0 then (0 : ℝ) else -f1 y * Real.log (f1 y)) +
        (1 / 2 : ℝ) * Real.log (2 * Real.pi) * f1 y +
        (1 / 2 : ℝ) * (y ^ 2 * f1 y) + gaussianPdf1D 1 y - f1 y) volume :=
    (((hh_int.add (hf1_int.const_mul ((1 / 2 : ℝ) * Real.log (2 * Real.pi)))).add
      (hm2_int.const_mul (1 / 2 : ℝ))).add (ep_integrable_gaussianPdf1D one_pos)).sub hf1_int
  exact hsum.congr (ae_of_all _ hpt)

/-- **Continuity of Gaussian-Smoothed Differential Entropy at `t = 0⁺`**:
    for any 1D density `f` with finite second moment and finite differential entropy,
    `h(X + √t Z) → h(X)` as `t → 0⁺`. -/
theorem diffEntropy_awgnOutput_tendsto_zero (f : Density 1)
    (hf : HasFiniteDiffEntropy f) (hm2 : HasFiniteSecondMoment f) :
    Tendsto (awgnDiffEntropy f) (𝓝[>] 0) (𝓝 (diffEntropy f)) := by
  -- Step 1: `t ↦ awgnDiffEntropy f t` is monotone increasing on `(0, ∞)` by De Bruijn + `J ≥ 0`.
  have hmono : MonotoneOn (awgnDiffEntropy f) (Set.Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (f' := fun t => if ht : 0 < t then (1 / 2 : ℝ) * fisherInfo (awgnOutputDensity f t ht) else 0)
      ?_ ?_ ?_
    · intro t ht
      exact (de_bruijn_identity f hm2 ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      have ht' : 0 < t := ht
      have hd : HasDerivWithinAt (awgnDiffEntropy f)
          ((1 / 2 : ℝ) * fisherInfo (awgnOutputDensity f t ht')) (interior (Set.Ioi 0)) t :=
        (de_bruijn_identity f hm2 ht').hasDerivWithinAt
      simpa [ht'] using hd
    · intro t ht
      rw [interior_Ioi] at ht
      have ht' : 0 < t := ht
      simp only [ht', ↓reduceDIte]
      exact mul_nonneg (by norm_num) (fisherInfo_nonneg _)
  -- Step 2: Extract a subsequence `t_k = 1 / (ns k + 1) → 0` with `f_{t_k}(y) → f(y)` a.e.
  let p_seq : ℕ → ℝ → ℝ := fun n y =>
    (awgnOutputDensity f (1 / (n + 1 : ℝ)) (by positivity)).pdf (fun _ => y)
  let f1 : ℝ → ℝ := fun y => f.pdf (fun _ => y)
  have hL1 := ep_tendsto_L1_awgn_seq f
  have heLp : Tendsto (fun n : ℕ => eLpNorm (p_seq n - f1) 1 volume) atTop (𝓝 0) := by
    have hconv : ∀ n : ℕ, eLpNorm (p_seq n - f1) 1 volume =
        ENNReal.ofReal (∫ y : ℝ, |p_seq n y - f1 y|) := by
      intro n
      rw [eLpNorm_one_eq_lintegral_eNorm]
      have hint : Integrable (fun y : ℝ => |p_seq n y - f1 y|) volume :=
        ((ep_pdf1_integrable _).sub (ep_pdf1_integrable f)).norm
      have hrew : (fun x : ℝ => ‖(p_seq n - f1) x‖ₑ) =
          fun x : ℝ => ENNReal.ofReal |p_seq n x - f1 x| := by
        funext x; simp [Pi.sub_apply, Real.eNorm_eq_ofReal_abs]
      rw [hrew, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => abs_nonneg _)]
      · exact ((ep_pdf1_integrable _).sub (ep_pdf1_integrable f)).aestronglyMeasurable
    have hL1' : Tendsto (fun n : ℕ => ∫ y : ℝ, |p_seq n y - f1 y|) atTop (𝓝 0) := hL1
    have hcomp := (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hL1'
    rw [ENNReal.ofReal_zero] at hcomp
    exact hcomp.congr fun n => (hconv n).symm
  have hmeas_conv : TendstoInMeasure volume p_seq atTop f1 :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero heLp
  obtain ⟨ns, hns_mono, hns_ae⟩ := hmeas_conv.exists_seq_tendsto_ae
  -- Step 3: Fatou's lemma on `D(f_{t_k} ‖ N(0, 1))` gives `∀ ε > 0, ∃ k, h(f_{t_k}) ≤ h(f) + ε`.
  let K_fun : ℕ → ℝ → ℝ := fun k y =>
    gaussianPdf1D 1 y * InformationTheory.klFun (p_seq (ns k) y / gaussianPdf1D 1 y)
  let K_lim : ℝ → ℝ := fun y =>
    gaussianPdf1D 1 y * InformationTheory.klFun (f1 y / gaussianPdf1D 1 y)
  have hK_nn : ∀ k y, 0 ≤ K_fun k y := fun k y =>
    mul_nonneg (gaussianPdf1D_nonneg zero_le_one y)
      (InformationTheory.klFun_nonneg (div_nonneg ((awgnOutputDensity _ _ _).nonneg _)
        (gaussianPdf1D_nonneg zero_le_one y)))
  have hKlim_nn : ∀ y, 0 ≤ K_lim y := fun y =>
    mul_nonneg (gaussianPdf1D_nonneg zero_le_one y)
      (InformationTheory.klFun_nonneg (div_nonneg (f.nonneg _) (gaussianPdf1D_nonneg zero_le_one y)))
  have hK_int : ∀ k, Integrable (K_fun k) volume := fun k =>
    ep_integrable_kl_to_stdGaussian (awgnOutputDensity f (1 / (ns k + 1 : ℝ)) (by positivity))
      (hasFiniteDiffEntropy_awgnOutputDensity f hm2 (by positivity))
      (hasFiniteSecondMoment_awgnOutputDensity f hm2 (by positivity))
  have hKlim_int : Integrable K_lim volume := ep_integrable_kl_to_stdGaussian f hf hm2
  have hfatou : ∫⁻ y : ℝ, ENNReal.ofReal (K_lim y) ≤
      liminf (fun k : ℕ => ∫⁻ y : ℝ, ENNReal.ofReal (K_fun k y)) atTop := by
    have hae_lim : (fun y : ℝ => ENNReal.ofReal (K_lim y)) =ᵐ[volume]
        fun y : ℝ => liminf (fun k : ℕ => ENNReal.ofReal (K_fun k y)) atTop := by
      filter_upwards [hns_ae] with y hy
      have hcont : Tendsto (fun k : ℕ => ENNReal.ofReal (K_fun k y)) atTop
          (𝓝 (ENNReal.ofReal (K_lim y))) := by
        have h1 : Tendsto (fun k : ℕ => p_seq (ns k) y / gaussianPdf1D 1 y) atTop
            (𝓝 (f1 y / gaussianPdf1D 1 y)) := hy.div_const _
        have h2 : Tendsto (fun k : ℕ => InformationTheory.klFun (p_seq (ns k) y / gaussianPdf1D 1 y))
            atTop (𝓝 (InformationTheory.klFun (f1 y / gaussianPdf1D 1 y))) :=
          InformationTheory.continuous_klFun.continuousAt.tendsto.comp h1
        have h3 := h2.const_mul (gaussianPdf1D 1 y)
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h3
      exact hcont.liminf_eq.symm
    rw [lintegral_congr_ae hae_lim]
    exact lintegral_liminf_le' fun k => ((hK_int k).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  -- Step 4: Translate `hfatou` into `∀ ε > 0, ∃ t > 0, awgnDiffEntropy f t < diffEntropy f + ε`.
  have hexists_close : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ awgnDiffEntropy f t < diffEntropy f + ε := by
    intro ε hε
    by_contra hcontra
    push Not at hcontra
    have hK_le : ∀ k : ℕ, ∫ y : ℝ, K_fun k y ≤
        (∫ y : ℝ, K_lim y) - ε + (1 / 2 : ℝ) * (1 / (ns k + 1 : ℝ)) := by
      intro k
      set tk : ℝ := 1 / (ns k + 1 : ℝ)
      have htk : 0 < tk := by positivity
      have h1 := ep_kl_to_stdGaussian_eq (awgnOutputDensity f tk htk)
        (hasFiniteDiffEntropy_awgnOutputDensity f hm2 htk)
        (hasFiniteSecondMoment_awgnOutputDensity f hm2 htk)
      have h2 := ep_kl_to_stdGaussian_eq f hf hm2
      have hsm := awgnOutputDensity_secondMoment f hm2 htk
      have hge := hcontra tk htk
      rw [awgnDiffEntropy_eq f htk] at hge
      change ∫ y : ℝ, gaussianPdf1D 1 y *
        InformationTheory.klFun ((awgnOutputDensity f tk htk).pdf (fun _ => y) / gaussianPdf1D 1 y) ≤ _
      rw [h1, hsm]
      change _ ≤ (∫ y : ℝ, gaussianPdf1D 1 y * InformationTheory.klFun (f.pdf (fun _ => y) / gaussianPdf1D 1 y)) -
        ε + (1 / 2 : ℝ) * tk
      rw [h2]
      linarith
    -- For large `k`, `(1 / 2) * (1 / (ns k + 1)) ≤ ε / 2`, so `∫ K_fun k ≤ ∫ K_lim - ε / 2`.
    have hns_top : Tendsto (fun k : ℕ => (ns k : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hns_mono.tendsto_atTop).atTop_add tendsto_const_nhds
    have htk_zero : Tendsto (fun k : ℕ => (1 / 2 : ℝ) * (1 / ((ns k : ℝ) + 1))) atTop (𝓝 0) := by
      have hdiv : Tendsto (fun k : ℕ => (1 : ℝ) / ((ns k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hns_top
      simpa using hdiv.const_mul (1 / 2 : ℝ)
    have hev : ∀ᶠ k : ℕ in atTop, ∫ y : ℝ, K_fun k y ≤ (∫ y : ℝ, K_lim y) - ε / 2 := by
      filter_upwards [htk_zero.eventually (gt_mem_nhds (half_pos hε))] with k hk
      linarith [hK_le k]
    have hliminf_le : liminf (fun k : ℕ => ∫⁻ y : ℝ, ENNReal.ofReal (K_fun k y)) atTop ≤
        ENNReal.ofReal ((∫ y : ℝ, K_lim y) - ε / 2) := by
      refine liminf_le_of_frequently_le' (hev.frequently.mono fun k hk => ?_)
      rw [← ofReal_integral_eq_lintegral_ofReal (hK_int k) (ae_of_all _ (hK_nn k))]
      exact ENNReal.ofReal_le_ofReal hk
    have hlhs_eq : ∫⁻ y : ℝ, ENNReal.ofReal (K_lim y) = ENNReal.ofReal (∫ y : ℝ, K_lim y) :=
      (ofReal_integral_eq_lintegral_ofReal hKlim_int (ae_of_all _ hKlim_nn)).symm
    have hle_enn := le_trans hfatou hliminf_le
    rw [hlhs_eq] at hle_enn
    have hKlim_int_nn : 0 ≤ ∫ y : ℝ, K_lim y := integral_nonneg hKlim_nn
    by_cases hneg : (∫ y : ℝ, K_lim y) - ε / 2 ≤ 0
    · rw [ENNReal.ofReal_eq_zero.mpr hneg] at hle_enn
      have h0 : ∫ y : ℝ, K_lim y ≤ 0 := (ENNReal.ofReal_eq_zero.mp (le_antisymm hle_enn bot_le))
      -- Actually `∫ K_lim ≥ 0` so `∫ K_lim = 0`, contradicting `∫ K_fun k ≥ 0` and `∫ K_fun k ≤ -ε/2`!
      obtain ⟨k, hk⟩ := hev.exists
      have hkn : 0 ≤ ∫ y : ℝ, K_fun k y := integral_nonneg (hK_nn k)
      linarith
    · have hpos : 0 < (∫ y : ℝ, K_lim y) - ε / 2 := lt_of_not_ge hneg
      have hle_real := (ENNReal.ofReal_le_ofReal_iff hpos.le).mp hle_enn
      linarith
  -- Step 5: Monotonicity + `diffEntropy f ≤ awgnDiffEntropy f t` + `hexists_close` ⇒ `Tendsto`.
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_lt⟩ := hexists_close ε hε
  have hmem : Set.Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδ_pos
  filter_upwards [hmem] with t ht
  rw [Real.dist_eq]
  have hge : diffEntropy f ≤ awgnDiffEntropy f t := by
    rw [awgnDiffEntropy_eq f ht.1]
    exact diffEntropy_awgnOutput_ge f hf hm2 ht.1
  have hle : awgnDiffEntropy f t ≤ awgnDiffEntropy f δ :=
    hmono ht.1 hδ_pos ht.2.le
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Shannon's 1D Entropy Power Inequality (EPI)** (Cover & Thomas Theorem 17.8.1;
    Shannon 1948; Stam 1959; Blachman 1965):
    for any two independent 1D random variables with densities `f, g` having finite second
    moments and finite differential entropies (and `f * g` having finite differential entropy),
    `N(X + Y) ≥ N(X) + N(Y)`. -/
theorem entropyPower_add_ge (f g : Density 1)
    (hf_ent : HasFiniteDiffEntropy f) (hg_ent : HasFiniteDiffEntropy g)
    (hfg_ent : HasFiniteDiffEntropy (convDensity f g))
    (hf_m2 : HasFiniteSecondMoment f) (hg_m2 : HasFiniteSecondMoment g) :
    entropyPower f + entropyPower g ≤ entropyPower (convDensity f g) := by
  unfold entropyPower
  simp only [Nat.cast_one, div_one]
  refine ep_entropyPower_of_weighted_diffEntropy fun r hr0 hr1 => ?_
  have h1mr : 0 < 1 - r := sub_pos.mpr hr1
  have hfg_m2 := hasFiniteSecondMoment_convDensity f g hf_m2 hg_m2
  have htend := diffEntropy_awgnOutput_tendsto_zero (convDensity f g) hfg_ent hfg_m2
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hbs := diffEntropy_conv_ge_weighted_awgn f g hf_m2 hg_m2 hr0 hr1 ht
  have hf_ge : diffEntropy f ≤ awgnDiffEntropy f (r * t) := by
    rw [awgnDiffEntropy_eq f (mul_pos hr0 ht)]
    exact diffEntropy_awgnOutput_ge f hf_ent hf_m2 (mul_pos hr0 ht)
  have hg_ge : diffEntropy g ≤ awgnDiffEntropy g ((1 - r) * t) := by
    rw [awgnDiffEntropy_eq g (mul_pos h1mr ht)]
    exact diffEntropy_awgnOutput_ge g hg_ent hg_m2 (mul_pos h1mr ht)
  nlinarith

/-- **EPI for AWGN Addition**: `N(X) + t ≤ N(X + √t Z)` for any finite-second-moment `X ~ f`
    with finite differential entropy and `t > 0`. -/
theorem entropyPower_awgnOutput_ge (f : Density 1)
    (hf_ent : HasFiniteDiffEntropy f) (hf_m2 : HasFiniteSecondMoment f)
    {t : ℝ} (ht : 0 < t) :
    entropyPower f + t ≤ entropyPower (awgnOutputDensity f t ht) := by
  have hg_m2 : HasFiniteSecondMoment (gaussianDensity1D t ht) := by
    unfold HasFiniteSecondMoment
    simp only [Fin.sum_univ_one]
    rw [ep_integrable_fin1_iff]
    exact integrable_sq_mul_gaussianPdf1D ht
  have h := entropyPower_add_ge f (gaussianDensity1D t ht) hf_ent
    (hasFiniteDiffEntropy_gaussianDensity1D ht)
    (by rw [convDensity_gaussian_eq_awgn f ht]; exact hasFiniteDiffEntropy_awgnOutputDensity f hf_m2 ht)
    hf_m2 hg_m2
  rwa [convDensity_gaussian_eq_awgn f ht, entropyPower_gaussianDensity1D ht] at h

/-- **EPI for Degraded AWGN Noise Levels**: for ANY finite-second-moment input `f`
    (with NO smoothness or finite-entropy assumption on `f`!) and `0 < N₁ ≤ N₂`,
    `N(X + Z₁) + (N₂ - N₁) ≤ N(X + Z₂)`. -/
theorem entropyPower_awgnOutput_add_ge (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (h12 : N₁ ≤ N₂) :
    entropyPower (awgnOutputDensity f N₁ hN₁) + (N₂ - N₁) ≤
      entropyPower (awgnOutputDensity f N₂ (lt_of_lt_of_le hN₁ h12)) := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · simp
  · have hΔ : 0 < N₂ - N₁ := sub_pos.mpr hlt
    have h := entropyPower_awgnOutput_ge (awgnOutputDensity f N₁ hN₁)
      (hasFiniteDiffEntropy_awgnOutputDensity f hm2 hN₁)
      (hasFiniteSecondMoment_awgnOutputDensity f hm2 hN₁) hΔ
    have heq : awgnOutputDensity (awgnOutputDensity f N₁ hN₁) (N₂ - N₁) hΔ =
        awgnOutputDensity f N₂ (lt_of_lt_of_le hN₁ h12) := by
      rw [awgnOutputDensity_awgnOutputDensity]
      refine ep_density_ext fun z => ?_
      have hadd : N₁ + (N₂ - N₁) = N₂ := by ring
      simp_rw [hadd]
    rwa [heq] at h

/-! ### Section 5: Bergmans's Scalar Gaussian Broadcast Channel Converse (C&T §15.6.2) -/

/-- Convexity of `ψ(t) = ½ ln(e^{2t} + c)` for any `c ≥ 0` (used to lift scalar EPI across
    conditioning on an auxiliary random variable `U`). -/
private lemma ep_convexOn_half_log_exp_add {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ Set.univ (fun t : ℝ => (1 / 2 : ℝ) * Real.log (Real.exp (2 * t) + c)) := by
  let ψ : ℝ → ℝ := fun t => (1 / 2 : ℝ) * Real.log (Real.exp (2 * t) + c)
  have hderiv : ∀ t : ℝ, HasDerivAt ψ (Real.exp (2 * t) / (Real.exp (2 * t) + c)) t := by
    intro t
    have hpos : 0 < Real.exp (2 * t) + c := add_pos_of_pos_of_nonneg (Real.exp_pos _) hc
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (2 * x) + c) (Real.exp (2 * t) * 2) t :=
      (hlin.exp).add_const c
    have hlog := (hexp.log (ne_of_gt hpos)).const_mul (1 / 2 : ℝ)
    refine hlog.congr_deriv ?_
    ring
  refine MonotoneOn.convexOn_of_deriv convex_univ
    (continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt).continuousOn
    (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
  intro a _ b _ hab
  rw [(hderiv a).deriv, (hderiv b).deriv]
  have ha : 0 < Real.exp (2 * a) + c := add_pos_of_pos_of_nonneg (Real.exp_pos _) hc
  have hb : 0 < Real.exp (2 * b) + c := add_pos_of_pos_of_nonneg (Real.exp_pos _) hc
  rw [div_le_div_iff₀ ha hb]
  have hexp_le : Real.exp (2 * a) ≤ Real.exp (2 * b) := Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- **Bergmans's Scalar Gaussian Broadcast Channel Single-Letter Converse**
    (Bergmans 1974; Cover & Thomas §15.6.2, Theorem 15.6.2):
    for a degraded scalar Gaussian broadcast channel `Y₁ = X + Z₁`, `Y₂ = X + Z₂` with
    `0 < N₁ ≤ N₂`, power budget `P ≥ 0`, finite auxiliary `U ~ P_U`, and conditional input
    densities `f u` (`X | U = u`) satisfying `∑ u, P_U(u) E[X² | U = u] ≤ P`,
    there exists a power-splitting parameter `α ∈ [0, 1]` such that:
    - `I(X; Y₁ | U) = h(Y₁ | U) - h(Z₁) ≤ ½ ln(1 + α P / N₁)`, AND
    - `I(U; Y₂) = h(Y₂) - h(Y₂ | U) ≤ ½ ln(1 + (1 - α) P / (α P + N₂))`. -/
theorem gaussianBC_single_letter_converse {U : Type*} [Fintype U]
    (P_U : ProbDist U) (f : U → Density 1)
    {P N₁ N₂ : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁) (h12 : N₁ ≤ N₂)
    (hm2 : ∀ u : U, HasFiniteSecondMoment (f u))
    (hpow : ∑ u : U, P_U.pmf u * (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) ≤ P) :
    let hN₂ : 0 < N₂ := lt_of_lt_of_le hN₁ h12
    let Y₁ : U → Density 1 := fun u => awgnOutputDensity (f u) N₁ hN₁
    let Y₂ : U → Density 1 := fun u => awgnOutputDensity (f u) N₂ hN₂
    let hY₁_given_U : ℝ := ∑ u : U, P_U.pmf u * diffEntropy (Y₁ u)
    let hY₂_given_U : ℝ := ∑ u : U, P_U.pmf u * diffEntropy (Y₂ u)
    let hY₂ : ℝ := diffEntropy (mixDensity P_U Y₂)
    ∃ α ∈ Set.Icc (0 : ℝ) 1,
      hY₁_given_U - diffEntropy (gaussianDensity1D N₁ hN₁) ≤
        (1 / 2 : ℝ) * Real.log (1 + α * P / N₁) ∧
      hY₂ - hY₂_given_U ≤
        (1 / 2 : ℝ) * Real.log (1 + (1 - α) * P / (α * P + N₂)) := by
  intro hN₂ Y₁ Y₂ hY₁_given_U hY₂_given_U hY₂
  have h2pie_pos : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  -- Step 1: Lower and upper bounds on `h(Y₁ | U)`: `½ ln(2πe N₁) ≤ h(Y₁ | U) ≤ ½ ln(2πe (P + N₁))`.
  have hY1_lo : (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * N₁) ≤ hY₁_given_U := by
    dsimp only [hY₁_given_U]
    calc (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * N₁)
        = ∑ u : U, P_U.pmf u * diffEntropy (gaussianDensity1D N₁ hN₁) := by
            rw [← Finset.sum_mul, P_U.sum_one, one_mul, diffEntropy_gaussianDensity1D hN₁]
      _ ≤ ∑ u : U, P_U.pmf u * diffEntropy (Y₁ u) :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left
              (awgn_mutualInfo_nonneg (f u) (hm2 u) hN₁) (P_U.nonneg u)
  have hY1_hi : hY₁_given_U ≤ (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (P + N₁)) := by
    -- By Gaussian max-entropy + concavity of `log` (via `log u ≤ u - 1`).
    set c : ℝ := P + N₁
    have hc_pos : 0 < c := by linarith
    have hper_u : ∀ u : U, diffEntropy (Y₁ u) -
        (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * c) ≤
        (1 / 2 : ℝ) * (((∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) + N₁) / c - 1) := by
      intro u
      set vu : ℝ := (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) + N₁
      have hvu_pos : 0 < vu := by
        have hnn : 0 ≤ ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x :=
          integral_nonneg fun x => mul_nonneg (sq_nonneg _) ((f u).nonneg x)
        linarith
      have hgauss : diffEntropy (Y₁ u) ≤ (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * vu) := by
        refine diffEntropy_le_gaussian (Y₁ u)
          (hasFiniteDiffEntropy_awgnOutputDensity (f u) (hm2 u) hN₁)
          (hasFiniteSecondMoment_awgnOutputDensity (f u) (hm2 u) hN₁) hvu_pos ?_
        rw [awgnOutputDensity_secondMoment (f u) (hm2 u) hN₁]
      have hlog_diff : Real.log (2 * Real.pi * Real.exp 1 * vu) -
          Real.log (2 * Real.pi * Real.exp 1 * c) = Real.log (vu / c) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp [ne_of_gt h2pie_pos, ne_of_gt hc_pos]
      have hlog_le : Real.log (vu / c) ≤ vu / c - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hvu_pos hc_pos)
      linarith
    have hsum : ∑ u : U, P_U.pmf u * (diffEntropy (Y₁ u) -
        (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * c)) ≤
        ∑ u : U, P_U.pmf u * ((1 / 2 : ℝ) * (((∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) + N₁) / c - 1)) :=
      Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hper_u u) (P_U.nonneg u)
    have hlhs : ∑ u : U, P_U.pmf u * (diffEntropy (Y₁ u) -
        (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * c)) =
        hY₁_given_U - (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * c) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P_U.sum_one, one_mul]
      rfl
    have hrhs : ∑ u : U, P_U.pmf u * ((1 / 2 : ℝ) *
        (((∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) + N₁) / c - 1)) ≤ 0 := by
      have hrew : ∑ u : U, P_U.pmf u * ((1 / 2 : ℝ) *
          (((∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) + N₁) / c - 1)) =
          (1 / 2 : ℝ) * (((∑ u : U, P_U.pmf u * (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x)) + N₁) / c - 1) := by
        have h1 : ∀ u : U, P_U.pmf u * ((1 / 2 : ℝ) *
            (((∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x) + N₁) / c - 1)) =
            (1 / (2 * c)) * (P_U.pmf u * (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x)) +
            ((1 / 2 : ℝ) * (N₁ / c - 1)) * P_U.pmf u := by
          intro u; field_simp [ne_of_gt hc_pos]; ring
        simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, P_U.sum_one, mul_one]
        field_simp [ne_of_gt hc_pos]; ring
      rw [hrew]
      have hdiv : ((∑ u : U, P_U.pmf u * (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (f u).pdf x)) + N₁) / c ≤ 1 :=
        (div_le_one hc_pos).mpr (by dsimp only [c]; linarith)
      linarith
    linarith
  -- Step 2: Upper bound on marginal `h(Y₂)`: `h(Y₂) ≤ ½ ln(2πe (P + N₂))`.
  have hY2_hi : hY₂ ≤ (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (P + N₂)) := by
    dsimp only [hY₂, Y₂]
    rw [mixDensity_awgnOutputDensity P_U f hN₂]
    have hmix_m2 := hasFiniteSecondMoment_mixDensity P_U f hm2
    refine diffEntropy_le_gaussian _ (hasFiniteDiffEntropy_awgnOutputDensity _ hmix_m2 hN₂)
      (hasFiniteSecondMoment_awgnOutputDensity _ hmix_m2 hN₂) (by linarith) ?_
    rw [awgnOutputDensity_secondMoment _ hmix_m2 hN₂, mixDensity_secondMoment P_U f hm2]
    linarith
  -- Step 3: Lift scalar EPI across conditioning on `U` via convexity of `t ↦ ½ ln(e^{2t} + 2πe(N₂ - N₁))`.
  have hY2_epi : (1 / 2 : ℝ) * Real.log (Real.exp (2 * hY₁_given_U) +
      2 * Real.pi * Real.exp 1 * (N₂ - N₁)) ≤ hY₂_given_U := by
    let cΔ : ℝ := 2 * Real.pi * Real.exp 1 * (N₂ - N₁)
    have hcΔ : 0 ≤ cΔ := mul_nonneg h2pie_pos.le (sub_nonneg.mpr h12)
    let ψ : ℝ → ℝ := fun t => (1 / 2 : ℝ) * Real.log (Real.exp (2 * t) + cΔ)
    have hconv : ConvexOn ℝ Set.univ ψ := ep_convexOn_half_log_exp_add hcΔ
    have hjensen := hconv.map_sum_le (t := Finset.univ) (w := P_U.pmf) (p := fun u => diffEntropy (Y₁ u))
      (fun u _ => P_U.nonneg u) P_U.sum_one (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hjensen
    refine le_trans hjensen ?_
    refine Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (P_U.nonneg u)
    have hepi := entropyPower_awgnOutput_add_ge (f u) (hm2 u) hN₁ h12
    unfold entropyPower at hepi
    simp only [Nat.cast_one, div_one] at hepi
    have hmul : Real.exp (2 * diffEntropy (Y₁ u)) + cΔ ≤ Real.exp (2 * diffEntropy (Y₂ u)) := by
      have h1 := mul_le_mul_of_nonneg_left hepi h2pie_pos.le
      have h2pie_ne : 2 * Real.pi * Real.exp 1 ≠ 0 := ne_of_gt h2pie_pos
      have hl : 2 * Real.pi * Real.exp 1 *
          (1 / (2 * Real.pi * Real.exp 1) * Real.exp (2 * diffEntropy (Y₁ u)) + (N₂ - N₁)) =
          Real.exp (2 * diffEntropy (Y₁ u)) + cΔ := by
        dsimp only [cΔ]; field_simp [h2pie_ne]
      have hr : 2 * Real.pi * Real.exp 1 *
          (1 / (2 * Real.pi * Real.exp 1) * Real.exp (2 * diffEntropy (Y₂ u))) =
          Real.exp (2 * diffEntropy (Y₂ u)) := by
        field_simp [h2pie_ne]
      linarith
    have hlog := Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos _) hcΔ) hmul
    rw [Real.log_exp] at hlog
    dsimp only [ψ]
    linarith
  -- Step 4: Choose `α ∈ [0, 1]` matching `N(Y₁ | U) = α P + N₁`.
  by_cases hP0 : P = 0
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · rw [hP0, mul_zero, zero_div, add_zero, Real.log_one, mul_zero,
        diffEntropy_gaussianDensity1D hN₁]
      rw [hP0, zero_add] at hY1_hi
      linarith
    · rw [hP0, mul_zero, zero_div, add_zero, Real.log_one, mul_zero]
      rw [hP0, zero_add] at hY2_hi
      have hY2_lo : (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * N₂) ≤ hY₂_given_U := by
        have h1 : 2 * Real.pi * Real.exp 1 * N₁ ≤ Real.exp (2 * hY₁_given_U) := by
          have := Real.exp_le_exp.mpr (show Real.log (2 * Real.pi * Real.exp 1 * N₁) ≤ 2 * hY₁_given_U by linarith)
          rwa [Real.exp_log (by positivity)] at this
        have h2 : 2 * Real.pi * Real.exp 1 * N₂ ≤
            Real.exp (2 * hY₁_given_U) + 2 * Real.pi * Real.exp 1 * (N₂ - N₁) := by linarith
        have h3 := Real.log_le_log (by positivity) h2
        linarith
      linarith
  · have hP_pos : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
    set N_cond : ℝ := (1 / (2 * Real.pi * Real.exp 1)) * Real.exp (2 * hY₁_given_U)
    have hN_lo : N₁ ≤ N_cond := by
      have hexp := Real.exp_le_exp.mpr (show Real.log (2 * Real.pi * Real.exp 1 * N₁) ≤ 2 * hY₁_given_U by linarith)
      rw [Real.exp_log (by positivity)] at hexp
      have hmul := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi * Real.exp 1))
      have hne : 2 * Real.pi * Real.exp 1 ≠ 0 := ne_of_gt h2pie_pos
      have hl : 1 / (2 * Real.pi * Real.exp 1) * (2 * Real.pi * Real.exp 1 * N₁) = N₁ := by field_simp [hne]
      linarith
    have hN_hi : N_cond ≤ P + N₁ := by
      have hexp := Real.exp_le_exp.mpr (show 2 * hY₁_given_U ≤ Real.log (2 * Real.pi * Real.exp 1 * (P + N₁)) by linarith)
      rw [Real.exp_log (by positivity)] at hexp
      have hmul := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi * Real.exp 1))
      have hne : 2 * Real.pi * Real.exp 1 ≠ 0 := ne_of_gt h2pie_pos
      have hr : 1 / (2 * Real.pi * Real.exp 1) * (2 * Real.pi * Real.exp 1 * (P + N₁)) = P + N₁ := by field_simp [hne]
      linarith
    set α : ℝ := (N_cond - N₁) / P
    have hα0 : 0 ≤ α := div_nonneg (by linarith) hP
    have hα1 : α ≤ 1 := (div_le_one hP_pos).mpr (by linarith)
    have hαP : α * P + N₁ = N_cond := by
      dsimp only [α]; rw [div_mul_cancel₀ _ (ne_of_gt hP_pos)]; ring
    have hexp_eq : Real.exp (2 * hY₁_given_U) = 2 * Real.pi * Real.exp 1 * (α * P + N₁) := by
      rw [hαP]; dsimp only [N_cond]; field_simp [ne_of_gt h2pie_pos]
    have hh1_eq : hY₁_given_U = (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (α * P + N₁)) := by
      have h := congrArg Real.log hexp_eq
      rw [Real.log_exp] at h
      linarith
    refine ⟨α, ⟨hα0, hα1⟩, ?_, ?_⟩
    · rw [hh1_eq, diffEntropy_gaussianDensity1D hN₁]
      have hlog : Real.log (2 * Real.pi * Real.exp 1 * (α * P + N₁)) -
          Real.log (2 * Real.pi * Real.exp 1 * N₁) = Real.log (1 + α * P / N₁) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp [ne_of_gt h2pie_pos, ne_of_gt hN₁]; ring
      linarith
    · have hY2_lo : (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (α * P + N₂)) ≤ hY₂_given_U := by
        have hsum : Real.exp (2 * hY₁_given_U) + 2 * Real.pi * Real.exp 1 * (N₂ - N₁) =
            2 * Real.pi * Real.exp 1 * (α * P + N₂) := by rw [hexp_eq]; ring
        rwa [hsum] at hY2_epi
      have hlog : Real.log (2 * Real.pi * Real.exp 1 * (P + N₂)) -
          Real.log (2 * Real.pi * Real.exp 1 * (α * P + N₂)) =
          Real.log (1 + (1 - α) * P / (α * P + N₂)) := by
        have hden : 0 < α * P + N₂ := by nlinarith
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp [ne_of_gt h2pie_pos, ne_of_gt hden]; ring
      linarith

end InfoTheory.Bridge
