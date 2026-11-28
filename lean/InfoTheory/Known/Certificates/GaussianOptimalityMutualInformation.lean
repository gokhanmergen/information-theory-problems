import InfoTheory.Problems.GaussianOptimalityMutualInformation
import InfoTheory.Bridge.EntropyPower

/-!
# Certificate for `InfoTheory.Problems.GaussianOptimalityMutualInformation`

`Statement` asks, for every dimension `d ≥ 1`, every pair of centered Gaussian noises
`g₁, g₂` on `ℝ^d`, every positive-definite covariance bound `K` and every `β ∈ (1, 2)`, for a
centered Gaussian `f*` with `Cov(f*) ⪯ K` maximizing `β h(f) - h(f * g₁) - h(f * g₂)` over all
densities `f` with `E[XXᵀ] ⪯ K` (finite entropies, finite second moment).

All facts below are about the exact objects of `Statement` (`Core` `Density`, `diffEntropy`,
`densityConv`, the statement's `IsCenteredGaussian` and `HasSecondMomentLe`); the 1-D analysis
reuses `Bridge.Gaussian` and Shannon's 1-D EPI from `Bridge.EntropyPower`.

## Certified
* `isCenteredGaussian_standard`, `identity_admissible` — **non-vacuity in every `d`**: the
  standard Gaussian `N(0, I_d)` is an `IsCenteredGaussian d` density and `K = I_d` is an
  admissible bound, so the hypotheses of `Statement` are satisfiable for each `d`.
* `isCenteredGaussian_one_iff` — in `d = 1`, `IsCenteredGaussian 1 g ↔ g = N(0, v)` for some
  `v > 0` (the normalising constant is forced by `∫ g = 1`).
* `hasSecondMomentLe_one_iff` — in `d = 1`, `HasSecondMomentLe 1 f K ↔ E_f[X²] ≤ K₀₀`.
* `gaussian_value` — **Gaussian value**: for `f = N(0, p)`, `g_j = N(0, v_j)`,
  `β h(f) - h(f * g₁) - h(f * g₂) = ψ(p) := (β/2) log(2πe p) - ½ log(2πe(p+v₁)) - ½ log(2πe(p+v₂))`.
* `gaussian_feasible` — the Gaussian input `N(0, p)`, `p ≤ K₀₀`, satisfies every hypothesis of
  the inner quantifier (finite entropies of `f`, `f * g₁`, `f * g₂`, finite second moment,
  covariance constraint); so the supremum is over a nonempty class and is a genuine real value.
* `value_le_psi` — **EPI bound**: every admissible 1-D `f` has
  `β h(f) - h(f * g₁) - h(f * g₂) ≤ ψ(N(f))` (`N(f * g_j) ≥ N(f) + v_j`).
* `entropyPower_le_of_secondMoment` — **max-entropy cap**: `E[X²] ≤ K` ⇒ `N(f) ≤ K`.
* `psi_exists_max` — `ψ` attains its maximum on `(0, K]`.
* `SliceAt`, `statement_iff_forall_slice` — `Statement ↔ ∀ d ≥ 1, SliceAt d` (definitional).
* `statement_d_one` — **the scalar case `d = 1` holds**: `SliceAt 1`, with maximizer
  `f* = N(0, p₀)`, `p₀ = argmax_{(0, K₀₀]} ψ`. This is a certified special case only; it does
  NOT prove `Statement`, whose open content is `d ≥ 2` with non-commuting noise covariances.
-/

open scoped BigOperators Real
open MeasureTheory InfoTheory InfoTheory.Bridge

namespace InfoTheory.Known.Certificates.GaussianOptimalityMutualInformation

open InfoTheory.Problems.GaussianOptimalityMutualInformation

/-- Two densities with the same pdf are equal. -/
lemma density_ext {d : ℕ} {f g : Density d} (h : ∀ x, f.pdf x = g.pdf x) : f = g := by
  cases f; cases g
  simp only [Density.mk.injEq]
  exact funext h

/-- In dimension one, `h(f) = ½ log(2πe · N(f))`. -/
lemma diffEntropy_eq_half_log_entropyPower (f : Density 1) :
    diffEntropy f = (1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * entropyPower f) := by
  unfold entropyPower
  have h2pie : (2 * π * Real.exp 1) ≠ 0 := by positivity
  have h : 2 * π * Real.exp 1 * ((1 / (2 * π * Real.exp 1)) *
      Real.exp (2 * diffEntropy f / ((1 : ℕ) : ℝ))) = Real.exp (2 * diffEntropy f) := by
    field_simp
    simp
  rw [h, Real.log_exp]
  ring

lemma entropyPower_pos' {d : ℕ} (f : Density d) : 0 < entropyPower f := by
  unfold entropyPower
  positivity

/-- The 1-D centered Gaussian `N(0, v)` satisfies the statement's `IsCenteredGaussian 1`. -/
theorem isCenteredGaussian_gaussianDensity1D {v : ℝ} (hv : 0 < v) :
    IsCenteredGaussian 1 (gaussianDensity1D v hv) := by
  refine ⟨1 / Real.sqrt (2 * π * v), fun _ _ => 1 / v, by positivity, fun _ _ => rfl, ?_, ?_⟩
  · rintro w ⟨i, hi⟩
    have hi0 : w 0 ≠ 0 := by rwa [Fin.eq_zero i] at hi
    simp only [Fin.sum_univ_one]
    have : 0 < w 0 * w 0 := mul_self_pos.mpr hi0
    have h1 : 1 / v * w 0 * w 0 = 1 / v * (w 0 * w 0) := by ring
    rw [h1]
    positivity
  · intro x
    change gaussianPdf1D v (x 0) = _
    unfold gaussianPdf1D
    simp only [Fin.sum_univ_one]
    congr 2
    field_simp

/-- Classification: in dimension one, `IsCenteredGaussian 1 g` holds exactly for the
    centered Gaussians `N(0, v)`, `v > 0`. -/
theorem isCenteredGaussian_one_iff (g : Density 1) :
    IsCenteredGaussian 1 g ↔ ∃ (v : ℝ) (hv : 0 < v), g = gaussianDensity1D v hv := by
  constructor
  · rintro ⟨c, Q, hc, _, hpd, hform⟩
    set q := Q 0 0 with hq_def
    have hq : 0 < q := by
      have := hpd (fun _ => 1) ⟨0, one_ne_zero⟩
      simpa using this
    have hform' : ∀ x : Fin 1 → ℝ, g.pdf x = c * Real.exp (-(q / 2) * (x 0) ^ 2) := by
      intro x
      rw [hform x]
      simp only [Fin.sum_univ_one]
      congr 2
      ring
    have hint : (1 : ℝ) = c * Real.sqrt (π / (q / 2)) := by
      have h1 := g.integral_one
      have hfun : g.pdf = fun x : Fin 1 → ℝ => (fun t : ℝ => c * Real.exp (-(q / 2) * t ^ 2)) (x 0) :=
        funext hform'
      rw [hfun, integral_fin1_eq, integral_const_mul, integral_gaussian] at h1
      exact h1.symm
    refine ⟨1 / q, by positivity, density_ext fun x => ?_⟩
    change g.pdf x = gaussianPdf1D (1 / q) (x 0)
    rw [hform']
    unfold gaussianPdf1D
    have hpi : π / (q / 2) = 2 * π * (1 / q) := by field_simp
    rw [hpi] at hint
    have hs : 0 < Real.sqrt (2 * π * (1 / q)) := by positivity
    have hc' : c = 1 / Real.sqrt (2 * π * (1 / q)) := by
      rw [eq_div_iff hs.ne']
      linarith
    rw [hc']
    congr 2
    field_simp
  · rintro ⟨v, hv, rfl⟩
    exact isCenteredGaussian_gaussianDensity1D hv

/-- **Non-vacuity in every dimension.** The standard Gaussian `N(0, I_d)`
    (`Bridge.gaussianProductDensity`) satisfies `IsCenteredGaussian d`, with `Q = I_d`. -/
theorem isCenteredGaussian_standard (d : ℕ) :
    IsCenteredGaussian d
      (gaussianProductDensity (fun _ : Fin d => (1 : ℝ)) (fun _ => one_pos)) := by
  refine ⟨(1 / Real.sqrt (2 * π * 1)) ^ d, fun i j => if i = j then 1 else 0, by positivity,
    fun i j => by simp only [eq_comm], ?_, ?_⟩
  · rintro w ⟨i, hi⟩
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
  · intro x
    change ∏ i : Fin d, gaussianPdf1D 1 (x i) = _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold gaussianPdf1D
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The identity matrix is an admissible covariance bound `K` in every dimension. -/
theorem identity_admissible (d : ℕ) :
    (∀ i j : Fin d, (if i = j then (1 : ℝ) else 0) = if j = i then 1 else 0) ∧
      ∀ v : Fin d → ℝ, (∃ i : Fin d, v i ≠ 0) →
        0 < ∑ i : Fin d, ∑ j : Fin d, (if i = j then (1 : ℝ) else 0) * v i * v j := by
  refine ⟨fun i j => by simp only [eq_comm], ?_⟩
  rintro w ⟨i, hi⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

/-- In dimension one the covariance constraint `E[⟨w, X⟩²] ≤ wᵀ K w` is just `E[X²] ≤ K₀₀`. -/
theorem hasSecondMomentLe_one_iff (f : Density 1) (K : Fin 1 → Fin 1 → ℝ) :
    HasSecondMomentLe 1 f K ↔ ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x ≤ K 0 0 := by
  unfold HasSecondMomentLe
  simp only [Fin.sum_univ_one]
  constructor
  · intro h
    simpa using h (fun _ => 1)
  · intro h w
    have hrew : (fun x : Fin 1 → ℝ => (w 0 * x 0) ^ 2 * f.pdf x) =
        fun x => (w 0) ^ 2 * ((x 0) ^ 2 * f.pdf x) := by
      funext x; ring
    rw [hrew, integral_const_mul]
    have := mul_le_mul_of_nonneg_left h (sq_nonneg (w 0))
    nlinarith


lemma hasFiniteSecondMoment_gaussianDensity1D' {v : ℝ} (hv : 0 < v) :
    HasFiniteSecondMoment (gaussianDensity1D v hv) := by
  unfold HasFiniteSecondMoment
  simp only [Fin.sum_univ_one]
  exact (integrable_fin1_iff (fun t => t ^ 2 * gaussianPdf1D v t)).mpr
    (integrable_sq_mul_gaussianPdf1D hv)

/-- `ψ(p)`: the value of `β h(f) - h(f * g₁) - h(f * g₂)` at the Gaussian input `f = N(0, p)`
    with noises `g_j = N(0, v_j)` (see `gaussian_value`). -/
noncomputable def psi (β v₁ v₂ p : ℝ) : ℝ :=
  β * ((1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * p)) -
    (1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * (p + v₁)) -
    (1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * (p + v₂))

/-- **Gaussian value.** At `f = N(0, p)` the functional equals `ψ(p)` (a finite real number). -/
theorem gaussian_value {p v₁ v₂ : ℝ} (hp : 0 < p) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (β : ℝ) :
    β * diffEntropy (gaussianDensity1D p hp) -
        diffEntropy (awgnOutputDensity (gaussianDensity1D p hp) v₁ hv₁) -
        diffEntropy (awgnOutputDensity (gaussianDensity1D p hp) v₂ hv₂) =
      psi β v₁ v₂ p := by
  rw [awgnOutputDensity_gaussian, awgnOutputDensity_gaussian, diffEntropy_gaussianDensity1D,
    diffEntropy_gaussianDensity1D, diffEntropy_gaussianDensity1D]
  rfl

/-- **Gaussian input is feasible** for the inner quantifier of the statement: finite entropies,
    finite second moment, and the covariance constraint when `p ≤ K₀₀`. -/
theorem gaussian_feasible {p v₁ v₂ : ℝ} (hp : 0 < p) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (K : Fin 1 → Fin 1 → ℝ) (hpK : p ≤ K 0 0) :
    HasFiniteDiffEntropy (gaussianDensity1D p hp) ∧
      HasFiniteDiffEntropy (awgnOutputDensity (gaussianDensity1D p hp) v₁ hv₁) ∧
      HasFiniteDiffEntropy (awgnOutputDensity (gaussianDensity1D p hp) v₂ hv₂) ∧
      HasFiniteSecondMoment (gaussianDensity1D p hp) ∧
      HasSecondMomentLe 1 (gaussianDensity1D p hp) K := by
  refine ⟨hasFiniteDiffEntropy_gaussianDensity1D hp, ?_, ?_,
    hasFiniteSecondMoment_gaussianDensity1D' hp, ?_⟩
  · rw [awgnOutputDensity_gaussian]; exact hasFiniteDiffEntropy_gaussianDensity1D _
  · rw [awgnOutputDensity_gaussian]; exact hasFiniteDiffEntropy_gaussianDensity1D _
  · rw [hasSecondMomentLe_one_iff, gaussianDensity1D_secondMoment]; exact hpK

/-- **EPI upper bound.** For any 1-D input `f` (finite entropy and second moment) and Gaussian
    noises `N(0, v_j)`: `β h(f) - h(f * g₁) - h(f * g₂) ≤ ψ(N(f))`
    (Shannon's EPI `N(f * g_j) ≥ N(f) + v_j`, `Bridge.entropyPower_awgnOutput_ge`). -/
theorem value_le_psi (f : Density 1) (hf : HasFiniteDiffEntropy f)
    (hm2 : HasFiniteSecondMoment f) (β : ℝ) {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    β * diffEntropy f - diffEntropy (awgnOutputDensity f v₁ hv₁) -
        diffEntropy (awgnOutputDensity f v₂ hv₂) ≤
      psi β v₁ v₂ (entropyPower f) := by
  have hN := entropyPower_pos' f
  have h1 := entropyPower_awgnOutput_ge f hf hm2 hv₁
  have h2 := entropyPower_awgnOutput_ge f hf hm2 hv₂
  have hc : 0 < 2 * π * Real.exp 1 := by positivity
  have l1 : Real.log (2 * π * Real.exp 1 * (entropyPower f + v₁)) ≤
      Real.log (2 * π * Real.exp 1 * entropyPower (awgnOutputDensity f v₁ hv₁)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left h1 hc.le)
  have l2 : Real.log (2 * π * Real.exp 1 * (entropyPower f + v₂)) ≤
      Real.log (2 * π * Real.exp 1 * entropyPower (awgnOutputDensity f v₂ hv₂)) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left h2 hc.le)
  rw [diffEntropy_eq_half_log_entropyPower f,
    diffEntropy_eq_half_log_entropyPower (awgnOutputDensity f v₁ hv₁),
    diffEntropy_eq_half_log_entropyPower (awgnOutputDensity f v₂ hv₂)]
  unfold psi
  linarith

/-- **Max-entropy cap.** `E[X²] ≤ K` forces `N(f) ≤ K` (`Bridge.diffEntropy_le_gaussian`). -/
theorem entropyPower_le_of_secondMoment (f : Density 1) (hf : HasFiniteDiffEntropy f)
    (hm2 : HasFiniteSecondMoment f) {K : ℝ} (hK : 0 < K)
    (hvar : ∫ x : Fin 1 → ℝ, (x 0) ^ 2 * f.pdf x ≤ K) :
    entropyPower f ≤ K := by
  have h := diffEntropy_le_gaussian f hf hm2 hK hvar
  rw [diffEntropy_eq_half_log_entropyPower f] at h
  have hc : 0 < 2 * π * Real.exp 1 := by positivity
  have hN := entropyPower_pos' f
  have hlog : Real.log (2 * π * Real.exp 1 * entropyPower f) ≤
      Real.log (2 * π * Real.exp 1 * K) := by linarith
  rw [Real.log_le_log_iff (by positivity) (by positivity)] at hlog
  exact le_of_mul_le_mul_left hlog hc

/-- `ψ` attains its maximum on `(0, K]` (it is continuous and tends to `-∞` at `0⁺`). -/
theorem psi_exists_max {β v₁ v₂ K : ℝ} (hβ : 0 < β) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hK : 0 < K) :
    ∃ p₀ ∈ Set.Ioc (0 : ℝ) K, ∀ p ∈ Set.Ioc (0 : ℝ) K, psi β v₁ v₂ p ≤ psi β v₁ v₂ p₀ := by
  have hc0 : 0 < 2 * π * Real.exp 1 := by positivity
  let C : ℝ := psi β v₁ v₂ K + (1 / 2) * Real.log (2 * π * Real.exp 1 * v₁) +
    (1 / 2) * Real.log (2 * π * Real.exp 1 * v₂)
  let ε : ℝ := min K (Real.exp (2 * C / β) / (2 * π * Real.exp 1))
  have hε : 0 < ε := lt_min hK (by positivity)
  have hεK : ε ≤ K := min_le_left _ _
  have hpos : ∀ p ∈ Set.Icc ε K, 0 < p := fun p hp => hε.trans_le hp.1
  have hcont : ContinuousOn (psi β v₁ v₂) (Set.Icc ε K) := by
    unfold psi
    refine ((continuousOn_const.mul (continuousOn_const.mul ?_)).sub
      (continuousOn_const.mul ?_)).sub (continuousOn_const.mul ?_)
    · exact (continuousOn_const.mul continuousOn_id).log
        (fun p hp => (mul_pos hc0 (hpos p hp)).ne')
    · exact (continuousOn_const.mul (continuousOn_id.add continuousOn_const)).log
        (fun p hp => (mul_pos hc0 (add_pos (hpos p hp) hv₁)).ne')
    · exact (continuousOn_const.mul (continuousOn_id.add continuousOn_const)).log
        (fun p hp => (mul_pos hc0 (add_pos (hpos p hp) hv₂)).ne')
  obtain ⟨p₀, hp₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hεK) hcont
  refine ⟨p₀, ⟨hε.trans_le hp₀.1, hp₀.2⟩, fun p hp => ?_⟩
  by_cases hpe : ε ≤ p
  · exact hmax ⟨hpe, hp.2⟩
  · replace hpe : p < ε := lt_of_not_ge hpe
    have hK' : psi β v₁ v₂ K ≤ psi β v₁ v₂ p₀ := hmax ⟨hεK, le_rfl⟩
    have hp0 := hp.1
    have h1 : Real.log (2 * π * Real.exp 1 * v₁) ≤ Real.log (2 * π * Real.exp 1 * (p + v₁)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log (2 * π * Real.exp 1 * v₂) ≤ Real.log (2 * π * Real.exp 1 * (p + v₂)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hle : 2 * π * Real.exp 1 * p ≤ Real.exp (2 * C / β) := by
      have := hpe.le.trans (min_le_right _ _)
      rw [le_div_iff₀ hc0] at this
      linarith
    have hlog : Real.log (2 * π * Real.exp 1 * p) ≤ 2 * C / β := by
      calc Real.log (2 * π * Real.exp 1 * p) ≤ Real.log (Real.exp (2 * C / β)) :=
            Real.log_le_log (by positivity) hle
        _ = 2 * C / β := Real.log_exp _
    have hβlog : β * Real.log (2 * π * Real.exp 1 * p) ≤ 2 * C := by
      have := mul_le_mul_of_nonneg_left hlog hβ.le
      rwa [mul_div_cancel₀ _ hβ.ne'] at this
    have hpsi : psi β v₁ v₂ p ≤ psi β v₁ v₂ K := by
      have hCdef : C = psi β v₁ v₂ K + (1 / 2) * Real.log (2 * π * Real.exp 1 * v₁) +
          (1 / 2) * Real.log (2 * π * Real.exp 1 * v₂) := rfl
      have hexp : psi β v₁ v₂ p = β * ((1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * p)) -
          (1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * (p + v₁)) -
          (1 / 2 : ℝ) * Real.log (2 * π * Real.exp 1 * (p + v₂)) := rfl
      rw [hexp]
      linarith
    linarith

/-- The `d`-dimensional slice of `Statement` (its body at a fixed `d`). -/
def SliceAt (d : ℕ) : Prop :=
  ∀ (g₁ g₂ : Density d),
    IsCenteredGaussian d g₁ → IsCenteredGaussian d g₂ →
    ∀ (K : Fin d → Fin d → ℝ),
      (∀ i j : Fin d, K i j = K j i) →
      (∀ v : Fin d → ℝ, (∃ i : Fin d, v i ≠ 0) →
        0 < ∑ i : Fin d, ∑ j : Fin d, K i j * v i * v j) →
      ∀ (β : ℝ), 1 < β → β < 2 →
        ∃ (fStar fg₁Star fg₂Star : Density d),
          IsCenteredGaussian d fStar ∧
          HasSecondMomentLe d fStar K ∧
          (∀ x : Fin d → ℝ, fg₁Star.pdf x = densityConv fStar g₁ x) ∧
          (∀ x : Fin d → ℝ, fg₂Star.pdf x = densityConv fStar g₂ x) ∧
          ∀ (f fg₁ fg₂ : Density d),
            HasFiniteDiffEntropy f → HasFiniteDiffEntropy fg₁ → HasFiniteDiffEntropy fg₂ →
            HasFiniteSecondMoment f →
            HasSecondMomentLe d f K →
            (∀ x : Fin d → ℝ, fg₁.pdf x = densityConv f g₁ x) →
            (∀ x : Fin d → ℝ, fg₂.pdf x = densityConv f g₂ x) →
            β * diffEntropy f - diffEntropy fg₁ - diffEntropy fg₂ ≤
              β * diffEntropy fStar - diffEntropy fg₁Star - diffEntropy fg₂Star

/-- `Statement` is exactly "every slice `d ≥ 1` holds" (definitional; checks `SliceAt`). -/
theorem statement_iff_forall_slice : Statement ↔ ∀ d : ℕ, 1 ≤ d → SliceAt d := Iff.rfl

/-- **The scalar case `d = 1` of the conjecture holds** (EPI + Gaussian max-entropy).
    This certifies one slice only; it does NOT prove `Statement` (all `d ≥ 1`). -/
theorem statement_d_one : SliceAt 1 := by
  intro g₁ g₂ hg₁ hg₂ K _ hK β hβ1 _
  obtain ⟨v₁, hv₁, rfl⟩ := (isCenteredGaussian_one_iff g₁).mp hg₁
  obtain ⟨v₂, hv₂, rfl⟩ := (isCenteredGaussian_one_iff g₂).mp hg₂
  have hK0 : 0 < K 0 0 := by simpa using hK (fun _ => 1) ⟨0, one_ne_zero⟩
  obtain ⟨p₀, ⟨hp₀, hp₀K⟩, hmax⟩ := psi_exists_max (by linarith : (0 : ℝ) < β) hv₁ hv₂ hK0
  refine ⟨gaussianDensity1D p₀ hp₀, awgnOutputDensity (gaussianDensity1D p₀ hp₀) v₁ hv₁,
    awgnOutputDensity (gaussianDensity1D p₀ hp₀) v₂ hv₂,
    isCenteredGaussian_gaussianDensity1D hp₀, ?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · rw [hasSecondMomentLe_one_iff, gaussianDensity1D_secondMoment]; exact hp₀K
  · intro f fg₁ fg₂ hf _ _ hm2 hKf h₁ h₂
    have e₁ : fg₁ = awgnOutputDensity f v₁ hv₁ := density_ext h₁
    have e₂ : fg₂ = awgnOutputDensity f v₂ hv₂ := density_ext h₂
    subst e₁ e₂
    rw [gaussian_value hp₀ hv₁ hv₂ β]
    refine (value_le_psi f hf hm2 β hv₁ hv₂).trans (hmax _ ⟨entropyPower_pos' f, ?_⟩)
    exact entropyPower_le_of_secondMoment f hf hm2 hK0 ((hasSecondMomentLe_one_iff f K).mp hKf)

end InfoTheory.Known.Certificates.GaussianOptimalityMutualInformation
