import InfoTheory.Bridge.Gaussian

/-!
# Continuous Information Theory: Cover & Thomas Chapters 8–9

Purely additive Lean 4 formalization of core continuous differential entropy and AWGN channel
theorems (Cover & Thomas, Chapters 8 and 9), building directly on `InfoTheory.Bridge.Gaussian`:

1. **Differential Entropy under Translation & Scaling** (Cover & Thomas, Thms. 8.6.3 & 8.6.4):
   - `translateDensity1D`, `diffEntropy_translateDensity1D`: `h(X + c) = h(X)`
   - `scaleDensity1D`, `diffEntropy_scaleDensity1D`: `h(aX) = h(X) + ln |a|`
   - `entropyPower_scaleDensity1D`: `N(aX) = a² N(X)`

2. **Product Densities & Multivariate Product Gaussian** (Cover & Thomas, Thm. 8.4.1 in `ℝ^d`):
   - `prodDensity`, `diffEntropy_prodDensity`: `h(∏ f_i) = ∑ h(f_i)`
   - `gaussianProductDensity`, `diffEntropy_gaussianProductDensity`:
     `h(N(0, diag(v))) = ½ ∑ ln(2π e v_i)`
   - `diffEntropy_isotropicGaussian`: `h(N(0, v I_d)) = (d / 2) ln(2π e v)`
   - `entropyPower_isotropicGaussian`: `N(N(0, v I_d)) = v` (for `d > 0`)

3. **Single-Letter & Multi-Letter AWGN Capacity** (Cover & Thomas, Ch. 9, Thm. 9.1.1 & §9.2):
   - `awgnOutputDensity`: convolution `X + Z` with `Z ~ N(0, N)` as a bundled `Density 1`
   - `hasFiniteSecondMoment_awgnOutputDensity`, `awgnOutputDensity_secondMoment`:
     `E[(X + Z)²] = E[X²] + N` (without requiring `E[X] = 0`)
   - `awgn_mutualInfo_le_capacity`: `h(X + Z) - h(Z) ≤ ½ ln(1 + P / N)` whenever `E[X²] ≤ P`
   - `awgnOutputDensity_gaussian`, `awgn_mutualInfo_gaussian`:
     `N(0, P) * N(0, N) = N(0, P + N)` and Gaussian inputs achieve equality `½ ln(1 + P / N)`
   - `awgn_multiletter_power_jensen`:
     `(1/n) ∑_i ½ ln(1 + P_i / N) ≤ ½ ln(1 + P / N)` whenever `(1/n) ∑_i P_i ≤ P`
-/

open scoped BigOperators NNReal Real
open MeasureTheory ProbabilityTheory InfoTheory

namespace InfoTheory.Bridge

/-! ### Private 1D and Product-Measure Helpers -/

private lemma fin1_eq_const (x : Fin 1 → ℝ) : x = fun _ => x 0 :=
  funext fun i => by rw [Fin.eq_zero i]

private lemma integral_fin1_apply (h : (Fin 1 → ℝ) → ℝ) :
    ∫ x : Fin 1 → ℝ, h x = ∫ t : ℝ, h (fun _ => t) := by
  have hrew : (fun x : Fin 1 → ℝ => h x) = fun x : Fin 1 → ℝ => h (fun _ => x 0) := by
    funext x
    conv_lhs => rw [fin1_eq_const x]
  rw [hrew, integral_fin1_eq (fun t => h (fun _ => t))]

private lemma integrable_fin1_apply_iff (h : (Fin 1 → ℝ) → ℝ) :
    Integrable h volume ↔ Integrable (fun t : ℝ => h (fun _ => t)) volume := by
  have hrew : h = fun x : Fin 1 → ℝ => h (fun _ => x 0) := by
    funext x
    conv_lhs => rw [fin1_eq_const x]
  conv_lhs => rw [hrew]
  exact integrable_fin1_iff (fun t => h (fun _ => t))

private lemma integrable_fin1_of_congr (g : ℝ → ℝ) {h : (Fin 1 → ℝ) → ℝ}
    (hh : Integrable h volume) (heq : ∀ x : Fin 1 → ℝ, h x = g (x 0)) :
    Integrable g volume :=
  (integrable_fin1_iff g).mp (hh.congr (ae_of_all _ heq))

private lemma integrable_fin1_of {h : (Fin 1 → ℝ) → ℝ} (hh : Integrable h volume) :
    Integrable (fun t : ℝ => h (fun _ => t)) volume :=
  integrable_fin1_of_congr (fun t => h (fun _ => t)) hh
    (fun x => by conv_lhs => rw [fin1_eq_const x])

private lemma continuous_gaussianPdf1D (v : ℝ) : Continuous (gaussianPdf1D v) := by
  unfold gaussianPdf1D
  fun_prop

private lemma integrable_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    Integrable (gaussianPdf1D v) volume := by
  have heq : gaussianPdf1D v = gaussianPDFReal 0 ⟨v, hv.le⟩ :=
    funext (gaussianPdf1D_eq_gaussianPDFReal hv.le)
  rw [heq]
  exact integrable_gaussianPDFReal 0 ⟨v, hv.le⟩

private lemma integral_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    ∫ t : ℝ, gaussianPdf1D v t = 1 := by
  have heq : gaussianPdf1D v = gaussianPDFReal 0 ⟨v, hv.le⟩ :=
    funext (gaussianPdf1D_eq_gaussianPDFReal hv.le)
  rw [heq]
  exact integral_gaussianPDFReal_eq_one 0 (NNReal.coe_ne_zero.mp (ne_of_gt hv))

private lemma integrable_id_mul_gaussianPdf1D {v : ℝ} (hv : 0 < v) :
    Integrable (fun t : ℝ => t * gaussianPdf1D v t) volume := by
  have hdom : Integrable (fun t : ℝ => gaussianPdf1D v t + t ^ 2 * gaussianPdf1D v t) volume :=
    (integrable_gaussianPdf1D hv).add (integrable_sq_mul_gaussianPdf1D hv)
  refine hdom.mono' ((continuous_id.mul (continuous_gaussianPdf1D v)).aestronglyMeasurable)
    (ae_of_all _ fun t => ?_)
  have hg : 0 ≤ gaussianPdf1D v t := gaussianPdf1D_nonneg hv.le t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
  have hle : |t| ≤ 1 + t ^ 2 := by
    have hsq : 0 ≤ (|t| - 1) ^ 2 := sq_nonneg _
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  nlinarith

private lemma integral_id_mul_gaussianPdf1D (v : ℝ) :
    ∫ t : ℝ, t * gaussianPdf1D v t = 0 := by
  have hodd : ∀ t : ℝ, ((-1 : ℝ) * t) * gaussianPdf1D v ((-1 : ℝ) * t) =
      -(t * gaussianPdf1D v t) := by
    intro t
    unfold gaussianPdf1D
    simp
  have hneg := Measure.integral_comp_mul_left (fun t : ℝ => t * gaussianPdf1D v t) (-1 : ℝ)
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul] at hneg
  simp_rw [hodd, integral_neg] at hneg
  linarith

/-! ### Section 1: Differential Entropy under Translation and Scaling (C&T Thms. 8.6.3–8.6.4) -/

/-- Translate a 1D probability density by `c ∈ ℝ`: if `X ~ f`, then `X + c` has density
    `y ↦ f(y - c)`. -/
noncomputable def translateDensity1D (f : Density 1) (c : ℝ) : Density 1 where
  pdf := fun x => f.pdf (fun i => x i - c)
  nonneg := fun x => f.nonneg (fun i => x i - c)
  integrable := by
    have heq : (fun x : Fin 1 → ℝ => f.pdf (fun i => x i - c)) =
        fun x : Fin 1 → ℝ => f.pdf (x - fun _ => c) := rfl
    rw [heq]
    exact f.integrable.comp_sub_right (fun _ => c)
  integral_one := by
    have heq : (fun x : Fin 1 → ℝ => f.pdf (fun i => x i - c)) =
        fun x : Fin 1 → ℝ => f.pdf (x - fun _ => c) := rfl
    rw [heq, integral_sub_right_eq_self f.pdf (fun _ => c)]
    exact f.integral_one

/-- **Translation Invariance of Differential Entropy** (Cover & Thomas, Theorem 8.6.3):
    `h(X + c) = h(X)`. -/
theorem diffEntropy_translateDensity1D (f : Density 1) (c : ℝ) :
    diffEntropy (translateDensity1D f c) = diffEntropy f := by
  unfold diffEntropy translateDensity1D
  rw [integral_fin1_apply, integral_fin1_apply]
  let g1 : ℝ → ℝ := fun t =>
    if f.pdf (fun _ => t) ≤ 0 then 0 else -f.pdf (fun _ => t) * Real.log (f.pdf (fun _ => t))
  exact integral_sub_right_eq_self g1 c

/-- Scale a 1D probability density by `a ≠ 0`: if `X ~ f`, then `a X` has density
    `y ↦ |a|⁻¹ f(a⁻¹ y)`. -/
noncomputable def scaleDensity1D (f : Density 1) {a : ℝ} (ha : a ≠ 0) : Density 1 where
  pdf := fun x => |a|⁻¹ * f.pdf (fun i => a⁻¹ * x i)
  nonneg := fun x => mul_nonneg (inv_nonneg.mpr (abs_nonneg a)) (f.nonneg _)
  integrable := by
    rw [integrable_fin1_apply_iff]
    refine Integrable.const_mul ?_ _
    have hf1 : Integrable (fun t : ℝ => f.pdf (fun _ => t)) volume :=
      (integrable_fin1_apply_iff f.pdf).mp f.integrable
    exact (integrable_comp_mul_left_iff (g := fun t : ℝ => f.pdf (fun _ => t)) (inv_ne_zero ha)).mpr hf1
  integral_one := by
    rw [integral_fin1_apply]
    dsimp only
    rw [integral_const_mul,
      Measure.integral_comp_mul_left (fun t : ℝ => f.pdf (fun _ => t)) a⁻¹]
    simp only [smul_eq_mul, inv_inv]
    have h1 : ∫ t : ℝ, f.pdf (fun _ => t) = 1 := by
      rw [← integral_fin1_apply]
      exact f.integral_one
    rw [h1, mul_one, inv_mul_cancel₀ (abs_ne_zero.mpr ha)]

/-- **Scaling Law for Differential Entropy** (Cover & Thomas, Theorem 8.6.4):
    `h(a X) = h(X) + ln |a|` for `a ≠ 0`. -/
theorem diffEntropy_scaleDensity1D (f : Density 1) {a : ℝ} (ha : a ≠ 0)
    (hf : HasFiniteDiffEntropy f) :
    diffEntropy (scaleDensity1D f ha) = diffEntropy f + Real.log |a| := by
  unfold diffEntropy
  rw [integral_fin1_apply]
  have ha_abs_pos : 0 < |a| := abs_pos.mpr ha
  have ha_inv_pos : 0 < |a|⁻¹ := inv_pos.mpr ha_abs_pos
  let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
  let h1 : ℝ → ℝ := fun t => if f1 t ≤ 0 then 0 else -f1 t * Real.log (f1 t)
  have hpoint : ∀ t : ℝ,
      (if (scaleDensity1D f ha).pdf (fun _ => t) ≤ 0 then (0 : ℝ)
       else -(scaleDensity1D f ha).pdf (fun _ => t) *
         Real.log ((scaleDensity1D f ha).pdf (fun _ => t))) =
      |a|⁻¹ * h1 (a⁻¹ * t) + Real.log |a| * (|a|⁻¹ * f1 (a⁻¹ * t)) := by
    intro t
    change (if |a|⁻¹ * f1 (a⁻¹ * t) ≤ 0 then (0 : ℝ)
        else -(|a|⁻¹ * f1 (a⁻¹ * t)) * Real.log (|a|⁻¹ * f1 (a⁻¹ * t))) = _
    by_cases h0 : f1 (a⁻¹ * t) ≤ 0
    · have hf0 : f1 (a⁻¹ * t) = 0 := le_antisymm h0 (f.nonneg _)
      simp [h1, hf0]
    · have hfpos : 0 < f1 (a⁻¹ * t) := lt_of_not_ge h0
      have hmulpos : 0 < |a|⁻¹ * f1 (a⁻¹ * t) := mul_pos ha_inv_pos hfpos
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hmulpos))]
      simp only [h1, ite_eq_right_iff.mpr (fun h => absurd h h0)]
      rw [Real.log_mul (ne_of_gt ha_inv_pos) (ne_of_gt hfpos), Real.log_inv]
      ring
  simp_rw [hpoint]
  have hh1_int : Integrable h1 volume :=
    integrable_fin1_of_congr h1 hf (fun x => by
      dsimp only [h1, f1]
      conv_lhs => rw [fin1_eq_const x])
  have hf1_int : Integrable f1 volume :=
    integrable_fin1_of_congr f1 f.integrable (fun x => by
      dsimp only [f1]
      conv_lhs => rw [fin1_eq_const x])
  have hint1 : Integrable (fun t : ℝ => |a|⁻¹ * h1 (a⁻¹ * t)) volume :=
    ((integrable_comp_mul_left_iff (g := h1) (inv_ne_zero ha)).mpr hh1_int).const_mul _
  have hint2 : Integrable (fun t : ℝ => Real.log |a| * (|a|⁻¹ * f1 (a⁻¹ * t))) volume :=
    (((integrable_comp_mul_left_iff (g := f1) (inv_ne_zero ha)).mpr hf1_int).const_mul _).const_mul _
  rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul, integral_const_mul,
    Measure.integral_comp_mul_left h1 a⁻¹, Measure.integral_comp_mul_left f1 a⁻¹]
  simp only [smul_eq_mul, inv_inv]
  have hcancel : |a|⁻¹ * (|a| * ∫ t : ℝ, h1 t) = ∫ t : ℝ, h1 t := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha_abs_pos), one_mul]
  have hcancel2 : |a|⁻¹ * (|a| * ∫ t : ℝ, f1 t) = ∫ t : ℝ, f1 t := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha_abs_pos), one_mul]
  have hf1_one : ∫ t : ℝ, f1 t = 1 := by
    rw [← integral_fin1_apply]
    exact f.integral_one
  have hh1_eq : ∫ t : ℝ, h1 t = diffEntropy f := by
    unfold diffEntropy
    rw [integral_fin1_apply]
  rw [hcancel, hcancel2, hf1_one, hh1_eq, mul_one]
  rfl

/-- **Scaling Law for Entropy Power**: `N(a X) = a² N(X)` for `a ≠ 0`. -/
theorem entropyPower_scaleDensity1D (f : Density 1) {a : ℝ} (ha : a ≠ 0)
    (hf : HasFiniteDiffEntropy f) :
    entropyPower (scaleDensity1D f ha) = a ^ 2 * entropyPower f := by
  unfold entropyPower
  rw [diffEntropy_scaleDensity1D f ha hf]
  simp only [Nat.cast_one, div_one]
  have hsplit : 2 * (diffEntropy f + Real.log |a|) =
      2 * diffEntropy f + (Real.log |a| + Real.log |a|) := by ring
  rw [hsplit, Real.exp_add, Real.exp_add, Real.exp_log (abs_pos.mpr ha)]
  have habs_sq : |a| * |a| = a ^ 2 := by rw [← sq, sq_abs]
  rw [habs_sq]
  ring

/-! ### Section 2: Product Densities & Multivariate Product Gaussian (C&T Thm. 8.4.1 in `ℝ^d`) -/

private lemma integrable_pi_fin_prod :
    ∀ {d : ℕ} (g : Fin d → ℝ → ℝ),
      (∀ i, Integrable (g i) volume) →
      Integrable (fun x : Fin d → ℝ => ∏ i : Fin d, g i (x i)) volume
  | 0, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have hvol : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
      have huniv : (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi (fun _ => Set.univ) := by
        ext x; simp
      rw [huniv, Measure.pi_pi]
      simp
    have : IsFiniteMeasure (volume : Measure (Fin 0 → ℝ)) := ⟨by rw [hvol]; exact ENNReal.one_lt_top⟩
    exact integrable_const (1 : ℝ)
  | d + 1, g, hg => by
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have ih := integrable_pi_fin_prod (fun j : Fin d => g j.succ) (fun j => hg j.succ)
    have hprod : Integrable (fun p : ℝ × (Fin d → ℝ) => g 0 p.1 * ∏ j : Fin d, g j.succ (p.2 j))
        (volume.prod volume) := (hg 0).mul_prod ih
    have hcomp := (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).measurableEmbedding).mpr hprod
    refine hcomp.congr (ae_of_all _ fun x => ?_)
    change g 0 (x 0) * ∏ j : Fin d, g j.succ (Fin.removeNth 0 x j) = ∏ i : Fin (d + 1), g i (x i)
    rw [Fin.prod_univ_succ]
    congr 1

private lemma integral_pi_fin_prod :
    ∀ {d : ℕ} (g : Fin d → ℝ → ℝ),
      (∀ i, Integrable (g i) volume) →
      ∫ x : Fin d → ℝ, (∏ i : Fin d, g i (x i)) = ∏ i : Fin d, ∫ t : ℝ, g i t
  | 0, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.prod_empty, integral_const, smul_eq_mul, mul_one]
    have hvol : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
      have huniv : (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi (fun _ => Set.univ) := by
        ext x; simp
      rw [huniv, Measure.pi_pi]
      simp
    simp [Measure.real, hvol]
  | d + 1, g, hg => by
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have ih := integral_pi_fin_prod (fun j : Fin d => g j.succ) (fun j => hg j.succ)
    let F : ℝ × (Fin d → ℝ) → ℝ := fun p => g 0 p.1 * ∏ j : Fin d, g j.succ (p.2 j)
    have hrew : (fun x : Fin (d + 1) → ℝ => ∏ i : Fin (d + 1), g i (x i)) =
        fun x : Fin (d + 1) → ℝ =>
          F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 x) := by
      funext x
      change ∏ i : Fin (d + 1), g i (x i) = g 0 (x 0) * ∏ j : Fin d, g j.succ (Fin.removeNth 0 x j)
      rw [Fin.prod_univ_succ]
      rfl
    rw [hrew, hmp.integral_comp' F]
    change ∫ p : ℝ × (Fin d → ℝ), g 0 p.1 * ∏ j : Fin d, g j.succ (p.2 j) ∂(volume.prod volume) = _
    rw [integral_prod_mul (g 0) (fun y : Fin d → ℝ => ∏ j : Fin d, g j.succ (y j)), ih,
      Fin.prod_univ_succ]

/-- Product density on `ℝ^d` corresponding to independent coordinates `X_i ~ fs i`. -/
noncomputable def prodDensity {d : ℕ} (fs : Fin d → Density 1) : Density d where
  pdf := fun x => ∏ i : Fin d, (fs i).pdf (fun _ => x i)
  nonneg := fun x => Finset.prod_nonneg fun i _ => (fs i).nonneg _
  integrable :=
    integrable_pi_fin_prod (fun i t => (fs i).pdf (fun _ => t))
      (fun i => integrable_fin1_of (fs i).integrable)
  integral_one := by
    rw [integral_pi_fin_prod (fun i t => (fs i).pdf (fun _ => t))
      (fun i => integrable_fin1_of (fs i).integrable)]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← integral_fin1_apply]
    exact (fs i).integral_one

/-- **Additivity of Differential Entropy for Independent Coordinates**:
    `h(∏_i f_i) = ∑_i h(f_i)` whenever each `f_i` has finite differential entropy. -/
theorem diffEntropy_prodDensity {d : ℕ} (fs : Fin d → Density 1)
    (hfs : ∀ i, HasFiniteDiffEntropy (fs i)) :
    diffEntropy (prodDensity fs) = ∑ i : Fin d, diffEntropy (fs i) := by
  let p : Fin d → ℝ → ℝ := fun i t => (fs i).pdf (fun _ => t)
  let h : Fin d → ℝ → ℝ := fun i t => if p i t ≤ 0 then 0 else -p i t * Real.log (p i t)
  let term : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => ∏ j : Fin d, (if j = i then h i (x j) else p j (x j))
  have hpoint : ∀ x : Fin d → ℝ,
      (if (prodDensity fs).pdf x ≤ 0 then (0 : ℝ)
       else -(prodDensity fs).pdf x * Real.log ((prodDensity fs).pdf x)) =
      ∑ i : Fin d, term i x := by
    intro x
    change (if ∏ j : Fin d, p j (x j) ≤ 0 then (0 : ℝ)
        else -(∏ j : Fin d, p j (x j)) * Real.log (∏ j : Fin d, p j (x j))) = _
    by_cases hall : ∀ i : Fin d, 0 < p i (x i)
    · have hprod_pos : 0 < ∏ j : Fin d, p j (x j) := Finset.prod_pos fun j _ => hall j
      rw [ite_eq_right_iff.mpr (fun hc => absurd hc (not_le.mpr hprod_pos))]
      rw [Real.log_prod (fun j _ => ne_of_gt (hall j)), neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hterm_eq : term i x = h i (x i) * ∏ j ∈ Finset.univ.erase i, p j (x j) := by
        dsimp only [term]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        simp only [↓reduceIte]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        simp only [Finset.ne_of_mem_erase hj, ↓reduceIte]
      rw [hterm_eq]
      have hhi : h i (x i) = -p i (x i) * Real.log (p i (x i)) := by
        simp only [h, ite_eq_right_iff.mpr (fun hc => absurd hc (not_le.mpr (hall i)))]
      rw [hhi, ← Finset.mul_prod_erase Finset.univ (fun j => p j (x j)) (Finset.mem_univ i)]
      ring
    · push Not at hall
      rcases hall with ⟨k, hk⟩
      have hk0 : p k (x k) = 0 := le_antisymm hk ((fs k).nonneg _)
      have hprod0 : ∏ j : Fin d, p j (x j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) hk0
      rw [hprod0]
      simp only [le_refl, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hik : k = i
      · subst hik
        refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        simp [h, hk0]
      · refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        simp [hik, hk0]
  unfold diffEntropy
  simp_rw [hpoint]
  have hfactor_int : ∀ i j : Fin d, Integrable (fun t : ℝ => if j = i then h i t else p j t) volume := by
    intro i j
    by_cases hji : j = i
    · subst hji
      simp only [↓reduceIte]
      exact integrable_fin1_of_congr (h j) (hfs j) (fun x => by
        dsimp only [h, p]
        conv_lhs => rw [fin1_eq_const x])
    · simp only [hji, ↓reduceIte]
      exact integrable_fin1_of_congr (p j) (fs j).integrable (fun x => by
        dsimp only [p]
        conv_lhs => rw [fin1_eq_const x])
  have hterm_int : ∀ i : Fin d, Integrable (term i) volume := fun i =>
    integrable_pi_fin_prod (fun j t => if j = i then h i t else p j t) (hfactor_int i)
  have hsum_int : ∀ s : Finset (Fin d),
      Integrable (fun x : Fin d → ℝ => ∑ i ∈ s, term i x) volume ∧
      ∫ x : Fin d → ℝ, ∑ i ∈ s, term i x = ∑ i ∈ s, ∫ x : Fin d → ℝ, term i x := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s _ ih =>
      simp_rw [Finset.sum_cons]
      exact ⟨(hterm_int a).add ih.1, by rw [integral_add (hterm_int a) ih.1, ih.2]⟩
  rw [(hsum_int Finset.univ).2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_pi_fin_prod (fun j t => if j = i then h i t else p j t) (hfactor_int i)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [↓reduceIte]
  have hrest : ∏ j ∈ Finset.univ.erase i, (∫ t : ℝ, if j = i then h i t else p j t) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    simp only [Finset.ne_of_mem_erase hj, ↓reduceIte]
    rw [← integral_fin1_apply]
    exact (fs j).integral_one
  rw [hrest, mul_one, integral_fin1_apply]

/-- Every 1D Gaussian `N(0, v)` (`v > 0`) has finite differential entropy. -/
lemma hasFiniteDiffEntropy_gaussianDensity1D {v : ℝ} (hv : 0 < v) :
    HasFiniteDiffEntropy (gaussianDensity1D v hv) := by
  unfold HasFiniteDiffEntropy
  have hpoint : ∀ x : Fin 1 → ℝ,
      (if (gaussianDensity1D v hv).pdf x ≤ 0 then (0 : ℝ)
       else -(gaussianDensity1D v hv).pdf x * Real.log ((gaussianDensity1D v hv).pdf x)) =
      (1 / 2 : ℝ) * Real.log (2 * Real.pi * v) * gaussianPdf1D v (x 0) +
        (1 / (2 * v)) * ((x 0) ^ 2 * gaussianPdf1D v (x 0)) := by
    intro x
    have hpos : 0 < gaussianPdf1D v (x 0) := gaussianPdf1D_pos hv (x 0)
    change (if gaussianPdf1D v (x 0) ≤ 0 then 0
      else -gaussianPdf1D v (x 0) * Real.log (gaussianPdf1D v (x 0))) = _
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
  exact hint1.add hint2

/-- Multivariate centered Gaussian density on `ℝ^d` with diagonal covariance `diag(v)`. -/
noncomputable def gaussianProductDensity {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, 0 < v i) : Density d :=
  prodDensity (fun i => gaussianDensity1D (v i) (hv i))

/-- **Differential Entropy of a Product Multivariate Gaussian** (Cover & Thomas, Thm. 8.4.1):
    `h(N(0, diag(v))) = ½ ∑_i ln(2π e v_i)`. -/
theorem diffEntropy_gaussianProductDensity {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, 0 < v i) :
    diffEntropy (gaussianProductDensity v hv) =
      (1 / 2 : ℝ) * ∑ i : Fin d, Real.log (2 * Real.pi * Real.exp 1 * v i) := by
  unfold gaussianProductDensity
  rw [diffEntropy_prodDensity _ (fun i => hasFiniteDiffEntropy_gaussianDensity1D (hv i))]
  simp_rw [diffEntropy_gaussianDensity1D]
  rw [← Finset.mul_sum]

/-- **Differential Entropy of an Isotropic `d`-Dimensional Gaussian**:
    `h(N(0, v I_d)) = (d / 2) ln(2π e v)`. -/
theorem diffEntropy_isotropicGaussian {d : ℕ} {v : ℝ} (hv : 0 < v) :
    diffEntropy (gaussianProductDensity (fun _ : Fin d => v) (fun _ => hv)) =
      ((d : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1 * v) := by
  rw [diffEntropy_gaussianProductDensity]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Entropy Power of an Isotropic `d`-Dimensional Gaussian** (`d > 0`):
    `N(N(0, v I_d)) = v`. -/
theorem entropyPower_isotropicGaussian {d : ℕ} (hd : 0 < d) {v : ℝ} (hv : 0 < v) :
    entropyPower (gaussianProductDensity (fun _ : Fin d => v) (fun _ => hv)) = v := by
  unfold entropyPower
  rw [diffEntropy_isotropicGaussian hv]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hpos : 0 < 2 * Real.pi * Real.exp 1 * v := by positivity
  have h2pie : 2 * Real.pi * Real.exp 1 ≠ 0 := by positivity
  have hexp : 2 * (((d : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1 * v)) / (d : ℝ) =
      Real.log (2 * Real.pi * Real.exp 1 * v) := by
    field_simp [hd0]
  rw [hexp, Real.exp_log hpos]
  field_simp [h2pie]

/-! ### Section 3: Single-Letter & Multi-Letter AWGN Channel Capacity (C&T Ch. 9) -/

private lemma integrable_awgn_joint (f : Density 1) {N : ℝ} (hN : 0 < N) :
    Integrable (fun p : ℝ × ℝ => f.pdf (fun _ => p.2) * gaussianPdf1D N (p.1 - p.2))
      (volume.prod volume) := by
  let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
  have hf1_int : Integrable f1 volume := integrable_fin1_of f.integrable
  have hg_int : Integrable (gaussianPdf1D N) volume := integrable_gaussianPdf1D hN
  have hasm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f1 p.2 * gaussianPdf1D N (p.1 - p.2)) (volume.prod volume) :=
    (hf1_int.aestronglyMeasurable.comp_snd).mul
      ((continuous_gaussianPdf1D N).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  rw [integrable_prod_iff' hasm]
  refine ⟨ae_of_all _ fun y => ?_, ?_⟩
  · exact (hg_int.comp_sub_right y).const_mul (f1 y)
  · have hnorm : (fun y : ℝ => ∫ x : ℝ, ‖f1 y * gaussianPdf1D N (x - y)‖) = f1 := by
      funext y
      have hnn : ∀ x : ℝ, ‖f1 y * gaussianPdf1D N (x - y)‖ = f1 y * gaussianPdf1D N (x - y) := by
        intro x
        rw [Real.norm_of_nonneg (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg hN.le _))]
      simp_rw [hnn]
      rw [integral_const_mul, integral_sub_right_eq_self (gaussianPdf1D N) y,
        integral_gaussianPdf1D hN, mul_one]
    rw [hnorm]
    exact hf1_int

/-- Output density of the 1D AWGN channel `Y = X + Z` with input `X ~ f` and independent
    Gaussian noise `Z ~ N(0, N)` (`N > 0`), defined via `densityConv`. -/
noncomputable def awgnOutputDensity (f : Density 1) (N : ℝ) (hN : 0 < N) : Density 1 where
  pdf := densityConv f (gaussianDensity1D N hN)
  nonneg := fun x =>
    integral_nonneg fun y => mul_nonneg (f.nonneg y) ((gaussianDensity1D N hN).nonneg (x - y))
  integrable := by
    rw [integrable_fin1_apply_iff]
    have hrew : (fun t : ℝ => densityConv f (gaussianDensity1D N hN) (fun _ => t)) =
        fun t : ℝ => ∫ s : ℝ, f.pdf (fun _ => s) * gaussianPdf1D N (t - s) := by
      funext t
      unfold densityConv
      rw [integral_fin1_apply]
      rfl
    rw [hrew]
    exact (integrable_awgn_joint f hN).integral_prod_left
  integral_one := by
    rw [integral_fin1_apply]
    have hrew : (fun t : ℝ => densityConv f (gaussianDensity1D N hN) (fun _ => t)) =
        fun t : ℝ => ∫ s : ℝ, f.pdf (fun _ => s) * gaussianPdf1D N (t - s) := by
      funext t
      unfold densityConv
      rw [integral_fin1_apply]
      rfl
    rw [hrew]
    have hjoint := integrable_awgn_joint f hN
    rw [← integral_prod _ hjoint, integral_prod_symm _ hjoint]
    have hinner : ∀ s : ℝ,
        ∫ t : ℝ, f.pdf (fun _ => s) * gaussianPdf1D N (t - s) = f.pdf (fun _ => s) := by
      intro s
      rw [integral_const_mul, integral_sub_right_eq_self (gaussianPdf1D N) s,
        integral_gaussianPdf1D hN, mul_one]
    simp_rw [hinner]
    rw [← integral_fin1_apply]
    exact f.integral_one

private lemma integrable_sq_shift_mul_gaussianPdf1D {N : ℝ} (hN : 0 < N) (s : ℝ) :
    Integrable (fun t : ℝ => t ^ 2 * gaussianPdf1D N (t - s)) volume := by
  have h1 : Integrable (fun u : ℝ => u ^ 2 * gaussianPdf1D N u) volume :=
    integrable_sq_mul_gaussianPdf1D hN
  have h2 : Integrable (fun u : ℝ => (2 * s) * (u * gaussianPdf1D N u)) volume :=
    (integrable_id_mul_gaussianPdf1D hN).const_mul (2 * s)
  have h3 : Integrable (fun u : ℝ => s ^ 2 * gaussianPdf1D N u) volume :=
    (integrable_gaussianPdf1D hN).const_mul (s ^ 2)
  have hsum : Integrable (fun u : ℝ => (u + s) ^ 2 * gaussianPdf1D N u) volume := by
    have h12 : Integrable (fun u : ℝ =>
        u ^ 2 * gaussianPdf1D N u + (2 * s) * (u * gaussianPdf1D N u)) volume := h1.add h2
    have h123 : Integrable (fun u : ℝ =>
        u ^ 2 * gaussianPdf1D N u + (2 * s) * (u * gaussianPdf1D N u) +
          s ^ 2 * gaussianPdf1D N u) volume := h12.add h3
    refine h123.congr (ae_of_all _ fun u => ?_)
    ring
  have hshift := hsum.comp_sub_right s
  refine hshift.congr (ae_of_all _ fun t => ?_)
  simp

private lemma integral_sq_shift_mul_gaussianPdf1D {N : ℝ} (hN : 0 < N) (s : ℝ) :
    ∫ t : ℝ, t ^ 2 * gaussianPdf1D N (t - s) = s ^ 2 + N := by
  have hrew : (fun t : ℝ => t ^ 2 * gaussianPdf1D N (t - s)) =
      fun t : ℝ => ((t - s) + s) ^ 2 * gaussianPdf1D N (t - s) := by
    funext t; ring
  rw [hrew, integral_sub_right_eq_self (fun u : ℝ => (u + s) ^ 2 * gaussianPdf1D N u) s]
  have hexp : (fun u : ℝ => (u + s) ^ 2 * gaussianPdf1D N u) =
      fun u : ℝ => u ^ 2 * gaussianPdf1D N u + (2 * s) * (u * gaussianPdf1D N u) +
        s ^ 2 * gaussianPdf1D N u := by
    funext u; ring
  rw [hexp]
  have h1 : Integrable (fun u : ℝ => u ^ 2 * gaussianPdf1D N u) volume :=
    integrable_sq_mul_gaussianPdf1D hN
  have h2 : Integrable (fun u : ℝ => (2 * s) * (u * gaussianPdf1D N u)) volume :=
    (integrable_id_mul_gaussianPdf1D hN).const_mul (2 * s)
  have h3 : Integrable (fun u : ℝ => s ^ 2 * gaussianPdf1D N u) volume :=
    (integrable_gaussianPdf1D hN).const_mul (s ^ 2)
  have h12 : Integrable (fun u : ℝ =>
      u ^ 2 * gaussianPdf1D N u + (2 * s) * (u * gaussianPdf1D N u)) volume := h1.add h2
  rw [integral_add h12 h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul,
    integral_sq_mul_gaussianPdf1D hN, integral_id_mul_gaussianPdf1D N,
    integral_gaussianPdf1D hN]
  ring

private lemma integrable_awgn_sq_joint (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {N : ℝ} (hN : 0 < N) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * (f.pdf (fun _ => p.2) * gaussianPdf1D N (p.1 - p.2)))
      (volume.prod volume) := by
  let f1 : ℝ → ℝ := fun t => f.pdf (fun _ => t)
  have hf1_int : Integrable f1 volume := integrable_fin1_of f.integrable
  have hm2_1d : Integrable (fun s : ℝ => s ^ 2 * f1 s) volume := by
    have hm2' : Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x) volume := by
      simpa [HasFiniteSecondMoment, Fin.sum_univ_one] using hm2
    exact integrable_fin1_of_congr (fun s => s ^ 2 * f1 s) hm2' (fun x => by
      dsimp only [f1]
      conv_lhs => rw [fin1_eq_const x])
  have hasm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 ^ 2 * (f1 p.2 * gaussianPdf1D N (p.1 - p.2)))
      (volume.prod volume) :=
    ((continuous_fst.pow 2).aestronglyMeasurable).mul
      ((hf1_int.aestronglyMeasurable.comp_snd).mul
        ((continuous_gaussianPdf1D N).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
  rw [integrable_prod_iff' hasm]
  refine ⟨ae_of_all _ fun s => ?_, ?_⟩
  · have hrew : (fun t : ℝ => t ^ 2 * (f1 s * gaussianPdf1D N (t - s))) =
        fun t : ℝ => f1 s * (t ^ 2 * gaussianPdf1D N (t - s)) := by
      funext t; ring
    rw [hrew]
    exact (integrable_sq_shift_mul_gaussianPdf1D hN s).const_mul (f1 s)
  · have hnorm : (fun s : ℝ => ∫ t : ℝ, ‖t ^ 2 * (f1 s * gaussianPdf1D N (t - s))‖) =
        fun s : ℝ => s ^ 2 * f1 s + N * f1 s := by
      funext s
      have hnn : ∀ t : ℝ, ‖t ^ 2 * (f1 s * gaussianPdf1D N (t - s))‖ =
          f1 s * (t ^ 2 * gaussianPdf1D N (t - s)) := by
        intro t
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg t)
          (mul_nonneg (f.nonneg _) (gaussianPdf1D_nonneg hN.le _)))]
        ring
      simp_rw [hnn]
      rw [integral_const_mul, integral_sq_shift_mul_gaussianPdf1D hN s]
      ring
    rw [hnorm]
    exact hm2_1d.add (hf1_int.const_mul N)

/-- If the AWGN input `f` has finite second moment, so does the output `Y = X + Z`. -/
lemma hasFiniteSecondMoment_awgnOutputDensity (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {N : ℝ} (hN : 0 < N) :
    HasFiniteSecondMoment (awgnOutputDensity f N hN) := by
  unfold HasFiniteSecondMoment
  simp only [Fin.sum_univ_one]
  rw [integrable_fin1_apply_iff]
  have hrew : (fun t : ℝ => t ^ 2 * (awgnOutputDensity f N hN).pdf (fun _ => t)) =
      fun t : ℝ => ∫ s : ℝ, t ^ 2 * (f.pdf (fun _ => s) * gaussianPdf1D N (t - s)) := by
    funext t
    change t ^ 2 * (∫ y : Fin 1 → ℝ, f.pdf y * gaussianPdf1D N (t - y 0)) = _
    rw [integral_fin1_apply, ← integral_const_mul]
  rw [hrew]
  exact (integrable_awgn_sq_joint f hm2 hN).integral_prod_left

/-- **Second Moment of AWGN Channel Output**: `E[(X + Z)²] = E[X²] + N` for independent
    `Z ~ N(0, N)` (holds for any input `X` with finite second moment, even if `E[X] ≠ 0`). -/
theorem awgnOutputDensity_secondMoment (f : Density 1) (hm2 : HasFiniteSecondMoment f)
    {N : ℝ} (hN : 0 < N) :
    ∫ y : Fin 1 → ℝ, (y 0) ^ 2 * (awgnOutputDensity f N hN).pdf y =
      (∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x) + N := by
  rw [integral_fin1_apply]
  have hrew : (fun t : ℝ => t ^ 2 * (awgnOutputDensity f N hN).pdf (fun _ => t)) =
      fun t : ℝ => ∫ s : ℝ, t ^ 2 * (f.pdf (fun _ => s) * gaussianPdf1D N (t - s)) := by
    funext t
    change t ^ 2 * (∫ y : Fin 1 → ℝ, f.pdf y * gaussianPdf1D N (t - y 0)) = _
    rw [integral_fin1_apply, ← integral_const_mul]
  rw [hrew]
  have hjoint := integrable_awgn_sq_joint f hm2 hN
  rw [← integral_prod _ hjoint, integral_prod_symm _ hjoint]
  have hinner : ∀ s : ℝ,
      ∫ t : ℝ, t ^ 2 * (f.pdf (fun _ => s) * gaussianPdf1D N (t - s)) =
        s ^ 2 * f.pdf (fun _ => s) + N * f.pdf (fun _ => s) := by
    intro s
    have hpull : (fun t : ℝ => t ^ 2 * (f.pdf (fun _ => s) * gaussianPdf1D N (t - s))) =
        fun t : ℝ => f.pdf (fun _ => s) * (t ^ 2 * gaussianPdf1D N (t - s)) := by
      funext t; ring
    rw [hpull, integral_const_mul, integral_sq_shift_mul_gaussianPdf1D hN s]
    ring
  simp_rw [hinner]
  have hf1_int : Integrable (fun s : ℝ => f.pdf (fun _ => s)) volume :=
    integrable_fin1_of f.integrable
  have hm2_1d : Integrable (fun s : ℝ => s ^ 2 * f.pdf (fun _ => s)) volume := by
    have hm2' : Integrable (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x) volume := by
      simpa [HasFiniteSecondMoment, Fin.sum_univ_one] using hm2
    exact integrable_fin1_of_congr (fun s => s ^ 2 * f.pdf (fun _ => s)) hm2' (fun x => by
      conv_lhs => rw [fin1_eq_const x])
  rw [integral_add hm2_1d (hf1_int.const_mul N), integral_const_mul]
  have h1 : ∫ s : ℝ, f.pdf (fun _ => s) = 1 := by
    rw [← integral_fin1_apply]
    exact f.integral_one
  have h2 : ∫ s : ℝ, s ^ 2 * f.pdf (fun _ => s) = ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x := by
    rw [← integral_fin1_apply (fun x : Fin 1 → ℝ => (x 0) ^ 2 * f.pdf x)]
  rw [h1, h2, mul_one]

/-- **Single-Letter AWGN Mutual Information Upper Bound** (Cover & Thomas, Eq. 9.15 / Thm. 9.1.1):
    For any input density `f` with `E[X²] ≤ P` (`P ≥ 0`) and noise variance `N > 0`,
    `I(X; X + Z) = h(X + Z) - h(Z) ≤ ½ ln(1 + P / N)`. -/
theorem awgn_mutualInfo_le_capacity (f : Density 1) {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (hm2 : HasFiniteSecondMoment f)
    (hY : HasFiniteDiffEntropy (awgnOutputDensity f N hN))
    (hpow : ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x ≤ P) :
    diffEntropy (awgnOutputDensity f N hN) - diffEntropy (gaussianDensity1D N hN) ≤
      (1 / 2 : ℝ) * Real.log (1 + P / N) := by
  have hPN : 0 < P + N := by linarith
  have hm2Y : HasFiniteSecondMoment (awgnOutputDensity f N hN) :=
    hasFiniteSecondMoment_awgnOutputDensity f hm2 hN
  have hvarY : ∫ y : Fin 1 → ℝ, (y 0) ^ 2 * (awgnOutputDensity f N hN).pdf y ≤ P + N := by
    rw [awgnOutputDensity_secondMoment f hm2 hN]
    linarith
  have hle := diffEntropy_le_gaussian (awgnOutputDensity f N hN) hY hm2Y hPN hvarY
  rw [diffEntropy_gaussianDensity1D hN]
  have hlog : Real.log (2 * Real.pi * Real.exp 1 * (P + N)) -
      Real.log (2 * Real.pi * Real.exp 1 * N) = Real.log (1 + P / N) := by
    have h1 : 0 < 2 * Real.pi * Real.exp 1 * (P + N) := by positivity
    have h2 : 0 < 2 * Real.pi * Real.exp 1 * N := by positivity
    rw [← Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
    congr 1
    have h2pie : 2 * Real.pi * Real.exp 1 ≠ 0 := by positivity
    have hN0 : N ≠ 0 := ne_of_gt hN
    field_simp [h2pie, hN0]
    ring
  linarith

/-- **Gaussian Convolution Identity**: `N(0, P) * N(0, N) = N(0, P + N)` for `P, N > 0`. -/
theorem awgnOutputDensity_gaussian {P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    awgnOutputDensity (gaussianDensity1D P hP) N hN =
      gaussianDensity1D (P + N) (add_pos hP hN) := by
  have hpdf : (awgnOutputDensity (gaussianDensity1D P hP) N hN).pdf =
      (gaussianDensity1D (P + N) (add_pos hP hN)).pdf := by
    funext x
    change ∫ y : Fin 1 → ℝ, gaussianPdf1D P (y 0) * gaussianPdf1D N (x 0 - y 0) =
      gaussianPdf1D (P + N) (x 0)
    rw [integral_fin1_eq (fun t => gaussianPdf1D P t * gaussianPdf1D N (x 0 - t))]
    have hPN : 0 < P + N := add_pos hP hN
    let s : ℝ := P * N / (P + N)
    have hs : 0 < s := by positivity
    let μ : ℝ := P / (P + N) * x 0
    have hpoint : ∀ t : ℝ,
        gaussianPdf1D P t * gaussianPdf1D N (x 0 - t) =
          gaussianPdf1D (P + N) (x 0) * gaussianPdf1D s (t - μ) := by
      intro t
      unfold gaussianPdf1D
      have hP0 : P ≠ 0 := ne_of_gt hP
      have hN0 : N ≠ 0 := ne_of_gt hN
      have hPN0 : P + N ≠ 0 := ne_of_gt hPN
      have hsqrt_eq : Real.sqrt (2 * Real.pi * P) * Real.sqrt (2 * Real.pi * N) =
          Real.sqrt (2 * Real.pi * (P + N)) * Real.sqrt (2 * Real.pi * s) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        congr 1
        dsimp only [s]
        field_simp [hPN0]
      have hexp_eq : -(t ^ 2) / (2 * P) + -((x 0 - t) ^ 2) / (2 * N) =
          -((x 0) ^ 2) / (2 * (P + N)) + -((t - μ) ^ 2) / (2 * s) := by
        dsimp only [s, μ]
        field_simp [hP0, hN0, hPN0]
        ring
      have hmul_lhs :
          1 / Real.sqrt (2 * Real.pi * P) * Real.exp (-(t ^ 2) / (2 * P)) *
            (1 / Real.sqrt (2 * Real.pi * N) * Real.exp (-((x 0 - t) ^ 2) / (2 * N))) =
          (1 / (Real.sqrt (2 * Real.pi * P) * Real.sqrt (2 * Real.pi * N))) *
            Real.exp (-(t ^ 2) / (2 * P) + -((x 0 - t) ^ 2) / (2 * N)) := by
        rw [Real.exp_add]
        ring
      have hmul_rhs :
          1 / Real.sqrt (2 * Real.pi * (P + N)) * Real.exp (-((x 0) ^ 2) / (2 * (P + N))) *
            (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-((t - μ) ^ 2) / (2 * s))) =
          (1 / (Real.sqrt (2 * Real.pi * (P + N)) * Real.sqrt (2 * Real.pi * s))) *
            Real.exp (-((x 0) ^ 2) / (2 * (P + N)) + -((t - μ) ^ 2) / (2 * s)) := by
        rw [Real.exp_add]
        ring
      rw [hmul_lhs, hmul_rhs, hsqrt_eq, hexp_eq]
    simp_rw [hpoint]
    rw [integral_const_mul, integral_sub_right_eq_self (gaussianPdf1D s) μ,
      integral_gaussianPdf1D hs, mul_one]
  cases h1 : awgnOutputDensity (gaussianDensity1D P hP) N hN
  cases h2 : gaussianDensity1D (P + N) (add_pos hP hN)
  simp only [h1, h2] at hpdf
  congr

/-- **Gaussian Input Achieves AWGN Capacity** (Cover & Thomas, Thm. 9.1.1 equality case):
    For `X ~ N(0, P)` and independent `Z ~ N(0, N)`,
    `h(X + Z) - h(Z) = ½ ln(1 + P / N)`. -/
theorem awgn_mutualInfo_gaussian {P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    diffEntropy (awgnOutputDensity (gaussianDensity1D P hP) N hN) -
      diffEntropy (gaussianDensity1D N hN) =
      (1 / 2 : ℝ) * Real.log (1 + P / N) := by
  rw [awgnOutputDensity_gaussian hP hN,
    diffEntropy_gaussianDensity1D (add_pos hP hN),
    diffEntropy_gaussianDensity1D hN]
  have h1 : 0 < 2 * Real.pi * Real.exp 1 * (P + N) := by positivity
  have h2 : 0 < 2 * Real.pi * Real.exp 1 * N := by positivity
  have h2pie : 2 * Real.pi * Real.exp 1 ≠ 0 := by positivity
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hlog : Real.log (2 * Real.pi * Real.exp 1 * (P + N)) -
      Real.log (2 * Real.pi * Real.exp 1 * N) = Real.log (1 + P / N) := by
    rw [← Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
    congr 1
    field_simp [h2pie, hN0]
    ring
  linarith

/-- **Multi-Letter AWGN Power-Budget Jensen Bound** (Cover & Thomas, §9.2):
    By concavity of `log`, for any `n ≥ 1`, noise variance `N > 0`, and per-coordinate powers
    `p_i ≥ 0` satisfying `(1 / n) ∑_i p_i ≤ P`,
    `(1 / n) ∑_i ½ ln(1 + p_i / N) ≤ ½ ln(1 + P / N)`. -/
theorem awgn_multiletter_power_jensen {n : ℕ} (hn : 0 < n) {N P : ℝ} (hN : 0 < N)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (havg : (1 / (n : ℝ)) * ∑ i : Fin n, p i ≤ P) :
    (1 / (n : ℝ)) * ∑ i : Fin n, (1 / 2 : ℝ) * Real.log (1 + p i / N) ≤
      (1 / 2 : ℝ) * Real.log (1 + P / N) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hP_nonneg : 0 ≤ P := by
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, p i := Finset.sum_nonneg fun i _ => hp i
    have havg_nonneg : 0 ≤ (1 / (n : ℝ)) * ∑ i : Fin n, p i := by positivity
    linarith
  let c : ℝ := 1 + P / N
  have hc_pos : 0 < c := by
    have : 0 ≤ P / N := div_nonneg hP_nonneg hN.le
    linarith
  have hterm : ∀ i : Fin n,
      Real.log (1 + p i / N) - Real.log c ≤ (1 + p i / N) / c - 1 := by
    intro i
    have hxi_pos : 0 < 1 + p i / N := by
      have : 0 ≤ p i / N := div_nonneg (hp i) hN.le
      linarith
    rw [← Real.log_div (ne_of_gt hxi_pos) (ne_of_gt hc_pos)]
    exact Real.log_le_sub_one_of_pos (div_pos hxi_pos hc_pos)
  have hsum_le :
      ∑ i : Fin n, (Real.log (1 + p i / N) - Real.log c) ≤
        ∑ i : Fin n, ((1 + p i / N) / c - 1) :=
    Finset.sum_le_sum fun i _ => hterm i
  have hsum_lhs :
      ∑ i : Fin n, (Real.log (1 + p i / N) - Real.log c) =
        (∑ i : Fin n, Real.log (1 + p i / N)) - (n : ℝ) * Real.log c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum_rhs :
      ∑ i : Fin n, ((1 + p i / N) / c - 1) =
        ((n : ℝ) + (∑ i : Fin n, p i) / N) / c - (n : ℝ) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hsum_lhs, hsum_rhs] at hsum_le
  have hsum_p_le : ∑ i : Fin n, p i ≤ (n : ℝ) * P := by
    have hmul := mul_le_mul_of_nonneg_left havg hn_pos.le
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hsimp : (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, p i) = ∑ i : Fin n, p i := by
      field_simp [hne]
    linarith
  have hrhs_nonpos : ((n : ℝ) + (∑ i : Fin n, p i) / N) / c - (n : ℝ) ≤ 0 := by
    have hnum : (n : ℝ) + (∑ i : Fin n, p i) / N ≤ (n : ℝ) * c := by
      have hdiv : (∑ i : Fin n, p i) / N ≤ ((n : ℝ) * P) / N :=
        div_le_div_of_nonneg_right hsum_p_le hN.le
      dsimp only [c]
      linarith [show ((n : ℝ) * P) / N = (n : ℝ) * (P / N) by ring]
    have hdiv_le : ((n : ℝ) + (∑ i : Fin n, p i) / N) / c ≤ (n : ℝ) := by
      rw [div_le_iff₀ hc_pos]
      exact hnum
    linarith
  have hlog_sum : ∑ i : Fin n, Real.log (1 + p i / N) ≤ (n : ℝ) * Real.log c := by linarith
  have hmul_half :
      (1 / (n : ℝ)) * ∑ i : Fin n, (1 / 2 : ℝ) * Real.log (1 + p i / N) =
        (1 / 2 : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, Real.log (1 + p i / N)) := by
    rw [← Finset.mul_sum]
    ring
  rw [hmul_half]
  have havg_log : (1 / (n : ℝ)) * ∑ i : Fin n, Real.log (1 + p i / N) ≤ Real.log c := by
    have hmul := mul_le_mul_of_nonneg_left hlog_sum (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hsimp : (1 / (n : ℝ)) * ((n : ℝ) * Real.log c) = Real.log c := by
      field_simp [hne]
    linarith
  linarith

end InfoTheory.Bridge
