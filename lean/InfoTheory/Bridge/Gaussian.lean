import InfoTheory.Core
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Bridge Between `InfoTheory.Core` Continuous Densities and Mathlib's Gaussian Distributions

Purely additive bridge connecting `InfoTheory.Core.Entropy`'s continuous definitions
(`gaussianPdf1D`, `Density 1`, `diffEntropy`, `entropyPower`, `HasFiniteDiffEntropy`,
`HasFiniteSecondMoment`) to Mathlib's `ProbabilityTheory.gaussianPDFReal`,
`ProbabilityTheory.gaussianReal`, and `InformationTheory.klFun`:

- `gaussianPdf1D_eq_gaussianPDFReal`: exact equality with Mathlib's `gaussianPDFReal 0 ⟨v, _⟩`
- `gaussianDensity1D`: bundled `Density 1` for `N(0, v)` with `v > 0`
- `gaussianDensity1D_secondMoment`: `∫ x, (x 0)^2 * (gaussianDensity1D v hv).pdf x = v`
- `diffEntropy_gaussianDensity1D`: **Gaussian Differential Entropy** (Cover & Thomas, Thm. 8.4.1):
  `h(N(0, v)) = ½ ln(2π e v)`
- `entropyPower_gaussianDensity1D`: `N(N(0, v)) = v`
- `diffEntropy_le_gaussian`: **Gaussian Maximizes Differential Entropy** (Cover & Thomas, Thm. 8.6.5):
  for any 1D density `f` with finite differential entropy and second moment `≤ v`,
  `h(f) ≤ ½ ln(2π e v)` (proved directly via Mathlib's `InformationTheory.klFun_nonneg`).

Leaves `Core/`, `Problems/`, `STATEMENT_LOCK.json`, and `Known/` completely untouched.
-/

open scoped BigOperators NNReal Real
open MeasureTheory ProbabilityTheory InfoTheory

namespace InfoTheory.Bridge

/-- Helper equivalence `Fin 1 → ℝ ≃ᵐ ℝ` preserving Lebesgue `volume`. -/
lemma integral_fin1_eq (g : ℝ → ℝ) :
    ∫ x : Fin 1 → ℝ, g (x 0) = ∫ t : ℝ, g t := by
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  exact hmp.integral_comp' g

lemma integrable_fin1_iff (g : ℝ → ℝ) :
    Integrable (fun x : Fin 1 → ℝ => g (x 0)) volume ↔ Integrable g volume := by
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  exact hmp.integrable_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding

/-- Exact equality between `InfoTheory.gaussianPdf1D v` and Mathlib's `gaussianPDFReal 0 ⟨v, _⟩`. -/
lemma gaussianPdf1D_eq_gaussianPDFReal {v : ℝ} (hv : 0 ≤ v) (x : ℝ) :
    gaussianPdf1D v x = ProbabilityTheory.gaussianPDFReal 0 ⟨v, hv⟩ x := by
  unfold gaussianPdf1D ProbabilityTheory.gaussianPDFReal
  simp [one_div]
  rfl

lemma gaussianPdf1D_pos {v : ℝ} (hv : 0 < v) (x : ℝ) : 0 < gaussianPdf1D v x := by
  rw [gaussianPdf1D_eq_gaussianPDFReal hv.le]
  exact gaussianPDFReal_pos 0 ⟨v, hv.le⟩ x (NNReal.coe_ne_zero.mp (ne_of_gt hv))

lemma gaussianPdf1D_nonneg {v : ℝ} (hv : 0 ≤ v) (x : ℝ) : 0 ≤ gaussianPdf1D v x := by
  rw [gaussianPdf1D_eq_gaussianPDFReal hv]
  exact gaussianPDFReal_nonneg 0 ⟨v, hv⟩ x

/-- The 1D centered Gaussian `N(0, v)` packaged as an `InfoTheory.Density 1`. -/
noncomputable def gaussianDensity1D (v : ℝ) (hv : 0 < v) : Density 1 where
  pdf := fun x => gaussianPdf1D v (x 0)
  nonneg := fun x => gaussianPdf1D_nonneg hv.le (x 0)
  integrable := by
    rw [integrable_fin1_iff]
    have heq : gaussianPdf1D v = gaussianPDFReal 0 ⟨v, hv.le⟩ :=
      funext (gaussianPdf1D_eq_gaussianPDFReal hv.le)
    rw [heq]
    exact integrable_gaussianPDFReal 0 ⟨v, hv.le⟩
  integral_one := by
    rw [integral_fin1_eq]
    have heq : gaussianPdf1D v = gaussianPDFReal 0 ⟨v, hv.le⟩ :=
      funext (gaussianPdf1D_eq_gaussianPDFReal hv.le)
    rw [heq]
    exact integral_gaussianPDFReal_eq_one 0 (NNReal.coe_ne_zero.mp (ne_of_gt hv))

lemma integrable_sq_mul_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    Integrable (fun t : ℝ => t ^ 2 * gaussianPdf1D v t) volume := by
  let vn : ℝ≥0 := ⟨v, hv.le⟩
  have hvn : vn ≠ 0 := NNReal.coe_ne_zero.mp (ne_of_gt hv)
  have hmem : MemLp (fun t : ℝ => t) 2 (gaussianReal 0 vn) := memLp_id_gaussianReal 2
  have hint_g : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 vn) := by
    simpa [pow_two] using hmem.integrable_sq
  rw [gaussianReal_of_var_ne_zero 0 hvn] at hint_g
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 vn)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hint_g
  refine hint_g.congr (ae_of_all _ fun t => ?_)
  dsimp only
  rw [toReal_gaussianPDF, gaussianPdf1D_eq_gaussianPDFReal hv.le]

/-- Second moment of `N(0, v)` equals `v`, inherited directly from Mathlib's
    `variance_fun_id_gaussianReal`. -/
lemma integral_sq_mul_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    ∫ t : ℝ, t ^ 2 * gaussianPdf1D v t = v := by
  let vn : ℝ≥0 := ⟨v, hv.le⟩
  have hvn : vn ≠ 0 := NNReal.coe_ne_zero.mp (ne_of_gt hv)
  have hvar : Var[fun t : ℝ => t; gaussianReal 0 vn] = (vn : ℝ) := variance_fun_id_gaussianReal
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  simp only [sub_zero] at hvar
  rw [integral_gaussianReal_eq_integral_smul hvn] at hvar
  trans (∫ t : ℝ, gaussianPDFReal 0 vn t • t ^ 2)
  · refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only
    rw [gaussianPdf1D_eq_gaussianPDFReal hv.le, smul_eq_mul, mul_comm]
  · exact hvar

lemma gaussianDensity1D_secondMoment {v : ℝ} (hv : 0 < v) :
    ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * (gaussianDensity1D v hv).pdf x = v := by
  change ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * gaussianPdf1D v (x 0) = v
  rw [integral_fin1_eq (fun t => t ^ 2 * gaussianPdf1D v t)]
  exact integral_sq_mul_gaussianPdf1D hv

lemma log_gaussianPdf1D {v : ℝ} (hv : 0 < v) (t : ℝ) :
    Real.log (gaussianPdf1D v t) =
      -((1 / 2 : ℝ) * Real.log (2 * Real.pi * v)) - t ^ 2 / (2 * v) := by
  unfold gaussianPdf1D
  have h2piv : 0 < 2 * Real.pi * v := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr h2piv
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_div one_ne_zero (ne_of_gt hsqrt), Real.log_one, zero_sub,
    Real.log_sqrt h2piv.le, Real.log_exp]
  ring

/-- **Differential Entropy of a 1D Gaussian** (Cover & Thomas, Theorem 8.4.1):
    `h(N(0, v)) = ½ ln(2π e v)`. -/
theorem diffEntropy_gaussianDensity1D {v : ℝ} (hv : 0 < v) :
    diffEntropy (gaussianDensity1D v hv) =
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  unfold diffEntropy
  have hpoint : ∀ x : Fin 1 → ℝ,
      (if (gaussianDensity1D v hv).pdf x ≤ 0 then (0 : ℝ)
       else -(gaussianDensity1D v hv).pdf x * Real.log ((gaussianDensity1D v hv).pdf x)) =
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * gaussianPdf1D v (x 0) +
        (1 / (2 * v)) * ((x 0) ^ 2 * gaussianPdf1D v (x 0)) := by
    intro x
    have hpos : 0 < gaussianPdf1D v (x 0) := gaussianPdf1D_pos hv (x 0)
    change (if gaussianPdf1D v (x 0) ≤ 0 then 0 else -gaussianPdf1D v (x 0) * Real.log (gaussianPdf1D v (x 0))) = _
    rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hpos)), log_gaussianPdf1D hv]
    ring
  simp_rw [hpoint]
  have hint1 : Integrable (fun x : Fin 1 → ℝ =>
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * gaussianPdf1D v (x 0)) volume :=
    (gaussianDensity1D v hv).integrable.const_mul _
  have hint2 : Integrable (fun x : Fin 1 → ℝ =>
      (1 / (2 * v)) * ((x 0) ^ 2 * gaussianPdf1D v (x 0))) volume := by
    refine Integrable.const_mul ?_ _
    rw [integrable_fin1_iff (fun t => t ^ 2 * gaussianPdf1D v t)]
    exact integrable_sq_mul_gaussianPdf1D hv
  rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul]
  have h1 : ∫ x : Fin 1 → ℝ, gaussianPdf1D v (x 0) = 1 := (gaussianDensity1D v hv).integral_one
  have h2 : ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * gaussianPdf1D v (x 0) = v := gaussianDensity1D_secondMoment hv
  rw [h1, h2, mul_one]
  have h2piv : 0 < 2 * Real.pi * v := by positivity
  have hlog : Real.log (2 * Real.pi * Real.exp 1 * v) = Real.log (2 * Real.pi * v) + 1 := by
    have hrew : 2 * Real.pi * Real.exp 1 * v = (2 * Real.pi * v) * Real.exp 1 := by ring
    rw [hrew, Real.log_mul (ne_of_gt h2piv) (Real.exp_ne_zero 1), Real.log_exp]
  rw [hlog]
  have hvne : v ≠ 0 := ne_of_gt hv
  field_simp [hvne]

/-- **Entropy Power of a 1D Gaussian**: `N(N(0, v)) = v`. -/
theorem entropyPower_gaussianDensity1D {v : ℝ} (hv : 0 < v) :
    entropyPower (gaussianDensity1D v hv) = v := by
  unfold entropyPower
  rw [diffEntropy_gaussianDensity1D hv]
  have hpos : 0 < 2 * Real.pi * Real.exp 1 * v := by positivity
  have h2pie : 2 * Real.pi * Real.exp 1 ≠ 0 := by positivity
  have hexp : 2 * ((1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * v)) / (1 : ℝ) =
      Real.log (2 * Real.pi * Real.exp 1 * v) := by ring
  simp only [Nat.cast_one]
  rw [hexp, Real.exp_log hpos]
  field_simp [h2pie]

/-- **Gaussian Maximizes Differential Entropy** (Cover & Thomas, Theorem 8.6.5):
    for any 1D probability density `f` with finite differential entropy, finite second moment,
    and `∫ x, (x 0)² f(x) dx ≤ v` (`v > 0`),
    `h(f) ≤ ½ ln(2π e v)`.

    Proved directly via Mathlib's `InformationTheory.klFun_nonneg`. -/
theorem diffEntropy_le_gaussian (f : Density 1) (hf : HasFiniteDiffEntropy f)
    (hm2 : HasFiniteSecondMoment f) {v : ℝ} (hv : 0 < v)
    (hvar : ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x ≤ v) :
    diffEntropy f ≤ (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  let g : (Fin 1 → ℝ) → ℝ := (gaussianDensity1D v hv).pdf
  have hpoint : ∀ x : Fin 1 → ℝ,
      (if f.pdf x ≤ 0 then (0 : ℝ) else -f.pdf x * Real.log (f.pdf x)) ≤
        (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * f.pdf x +
          (1 / (2 * v)) * ((x 0) ^ 2 * f.pdf x) + g x - f.pdf x := by
    intro x
    have hgpos : 0 < g x := gaussianPdf1D_pos hv (x 0)
    have hlogg : Real.log (g x) = -((1 / 2 : ℝ) * Real.log (2 * Real.pi * v)) - (x 0) ^ 2 / (2 * v) :=
      log_gaussianPdf1D hv (x 0)
    by_cases hfx : f.pdf x ≤ 0
    · have hf0 : f.pdf x = 0 := le_antisymm hfx (f.nonneg x)
      simp only [hf0, le_refl, ↓reduceIte, mul_zero, add_zero, zero_add, sub_zero]
      exact le_of_lt hgpos
    · have hfpos : 0 < f.pdf x := lt_of_not_ge hfx
      have hkl : 0 ≤ InformationTheory.klFun (f.pdf x / g x) :=
        InformationTheory.klFun_nonneg (div_nonneg (f.nonneg x) (le_of_lt hgpos))
      unfold InformationTheory.klFun at hkl
      have hmul := mul_nonneg (le_of_lt hgpos) hkl
      have hne : g x ≠ 0 := ne_of_gt hgpos
      have hident : g x * (f.pdf x / g x * Real.log (f.pdf x / g x) + 1 - f.pdf x / g x) =
          f.pdf x * Real.log (f.pdf x) - f.pdf x * Real.log (g x) + g x - f.pdf x := by
        rw [Real.log_div (ne_of_gt hfpos) hne]
        field_simp [hne]
      rw [hident, hlogg] at hmul
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hfx)]
      have hvne : v ≠ 0 := ne_of_gt hv
      have hrew : -f.pdf x * (-((1 / 2 : ℝ) * Real.log (2 * Real.pi * v)) - (x 0) ^ 2 / (2 * v)) =
          (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * f.pdf x +
            (1 / (2 * v)) * ((x 0) ^ 2 * f.pdf x) := by
        field_simp [hvne]
        ring
      linarith
  have hm2' : Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x) volume := by
    simpa [HasFiniteSecondMoment, Fin.sum_univ_one] using hm2
  have h1 : Integrable (fun x : Fin 1 → ℝ => (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * f.pdf x) volume :=
    f.integrable.const_mul _
  have h2 : Integrable (fun x : Fin 1 → ℝ => (1 / (2 * v)) * ((x 0) ^ 2 * f.pdf x)) volume :=
    hm2'.const_mul _
  have h3 : Integrable g volume := (gaussianDensity1D v hv).integrable
  have h12 : Integrable (fun x : Fin 1 → ℝ =>
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * f.pdf x +
        (1 / (2 * v)) * ((x 0) ^ 2 * f.pdf x)) volume := h1.add h2
  have h123 : Integrable (fun x : Fin 1 → ℝ =>
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * f.pdf x +
        (1 / (2 * v)) * ((x 0) ^ 2 * f.pdf x) + g x) volume := h12.add h3
  have hint_rhs : Integrable (fun x : Fin 1 → ℝ =>
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * f.pdf x +
        (1 / (2 * v)) * ((x 0) ^ 2 * f.pdf x) + g x - f.pdf x) volume := h123.sub f.integrable
  have hmono := integral_mono hf hint_rhs hpoint
  rw [integral_sub h123 f.integrable, integral_add h12 h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul,
    f.integral_one, (gaussianDensity1D v hv).integral_one] at hmono
  have hvar_mul : (1 / (2 * v)) * (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x) ≤ (1 / (2 * v)) * v :=
    mul_le_mul_of_nonneg_left hvar (by positivity)
  have h2piv : 0 < 2 * Real.pi * v := by positivity
  have hlog : Real.log (2 * Real.pi * Real.exp 1 * v) = Real.log (2 * Real.pi * v) + 1 := by
    have hrew : 2 * Real.pi * Real.exp 1 * v = (2 * Real.pi * v) * Real.exp 1 := by ring
    rw [hrew, Real.log_mul (ne_of_gt h2piv) (Real.exp_ne_zero 1), Real.log_exp]
  have hvne : v ≠ 0 := ne_of_gt hv
  have hvsimp : (1 / (2 * v)) * v = 1 / 2 := by field_simp [hvne]
  rw [hvsimp] at hvar_mul
  unfold diffEntropy
  rw [hlog]
  linarith

end InfoTheory.Bridge
