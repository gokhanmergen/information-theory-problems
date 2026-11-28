import InfoTheory.Problems.PoissonChannelDiscreteCapacity
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.PoissonChannelDiscreteCapacity`

The (2026-11-27 fixed) Statement asks whether the capacity-achieving input of the
amplitude-constrained discrete-time Poisson channel has `O(A^{1-δ})` mass points, i.e. whether
`dtpcCapacity lam₀ A A` is attained by some `dtpcDiscreteMI lam₀ k pts w` with
`k ≤ K A^{1-δ}`. This file checks that the objects in the Statement are genuine (no junk
`sSup`/`tsum` values) and reproduce the solved degenerate case. References: Shamai, IEE Proc. I
137(6), 1990; Lapidoth–Moser, IEEE Trans. IT 55(1), 2009; Dytso–Barletta–Shamai, IEEE Trans. IT
2021 (arXiv:2104.14431); Barletta–Dytso–Shamai, arXiv:2401.05045, 2024.

## Certified
* `hasSum_poissonTrans`: **regression** — `poissonTrans lam₀ x` is the Poisson(`x + λ₀`)
  pmf: it sums to `1` (for every real `x + λ₀`, by the exponential series); with
  `poissonTrans_nonneg`, `poissonTrans_le_one` for `x + λ₀ ≥ 0`.
* `mean_le_of_mem_Icc`: any input supported on `[0, A]` satisfies the mean constraint
  `E[X] ≤ A`, so `dtpcCapacity lam₀ A A` is exactly the amplitude-only capacity used in
  the Statement.
* `dtpcDiscreteMI_le`: for inputs on `[0, A]`,
  `I(X; Y) ≤ 4 e^{2(A + λ₀)} / ln 2` (crude, but it rules out the junk-`tsum` and
  unbounded-`sSup` failure modes); hence `capacitySet_bddAbove`.
* `capacitySet_nonempty`, `dtpcCapacity_nonneg`, `le_dtpcCapacity`: the `sSup` is a genuine
  supremum over a nonempty bounded set, `0 ≤ C`, and every feasible input lower-bounds it.
* `dtpcDiscreteMI_const`: a deterministic input carries zero information.
* `dtpcCapacity_zero_amplitude`: **regression** `C_DTPC(λ₀, 0, μ) = 0` for `μ ≥ 0`.

## Not certified
* Shamai's theorem that the optimum is attained by a unique finitely supported input; the
  bounds `Ω(√A) ≤ N(A) ≤ O(A)` on its support size; `C = ½ log A + O(1)`; and the
  two-point optimality for `A + λ₀ < e`. In particular the existence part of the Statement
  is not certified, nor is any value of the capacity for `A > 0`.
-/

open scoped BigOperators Nat

namespace InfoTheory.Known.Certificates.PoissonChannelDiscreteCapacity

open InfoTheory InfoTheory.Problems.PoissonChannelDiscreteCapacity

lemma fact_eq : ∀ n : ℕ, fact n = n !
  | 0 => rfl
  | n + 1 => by rw [fact, fact_eq n, Nat.factorial_succ]

lemma poissonTrans_nonneg {lam₀ x : ℝ} (h : 0 ≤ x + lam₀) (y : ℕ) :
    0 ≤ poissonTrans lam₀ x y := by
  unfold poissonTrans
  have : (0 : ℝ) ≤ (fact y : ℝ) := Nat.cast_nonneg _
  positivity

/-- **Regression.** The transition law is the Poisson(`x + λ₀`) pmf: it sums to one. -/
theorem hasSum_poissonTrans (lam₀ x : ℝ) :
    HasSum (poissonTrans lam₀ x) 1 := by
  have h1 : HasSum (fun n : ℕ => (x + lam₀) ^ n / (n ! : ℝ)) (Real.exp (x + lam₀)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (x + lam₀)
  have h2 := h1.mul_left (Real.exp (-(x + lam₀)))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  convert h2 using 1
  funext y
  simp only [poissonTrans, fact_eq, mul_div_assoc]

lemma poissonTrans_le_one {lam₀ x : ℝ} (h : 0 ≤ x + lam₀) (y : ℕ) :
    poissonTrans lam₀ x y ≤ 1 := by
  have hs := hasSum_poissonTrans lam₀ x
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum y (fun j _ => poissonTrans_nonneg h j)

/-- Inputs on `[0, A]` automatically satisfy `E[X] ≤ A`. -/
theorem mean_le_of_mem_Icc {A : ℝ} {k : ℕ} (pts : Fin k → ℝ) (w : ProbDist (Fin k))
    (hpts : ∀ i, 0 ≤ pts i ∧ pts i ≤ A) : (∑ i : Fin k, w.pmf i * pts i) ≤ A := by
  calc (∑ i : Fin k, w.pmf i * pts i) ≤ ∑ i : Fin k, w.pmf i * A :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpts i).2 (w.nonneg i))
    _ = A := by rw [← Finset.sum_mul, w.sum_one, one_mul]

/-- `-q log₂ q ≤ 2 √q / ln 2` for `q ≥ 0`. -/
private lemma negPLogP_le_sqrt {q : ℝ} (hq : 0 ≤ q) :
    negPLogP q ≤ 2 * Real.sqrt q / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold negPLogP log2
  split_ifs with h
  · positivity
  · have hq' : 0 < q := lt_of_not_ge h
    set s := Real.sqrt q with hsdef
    have hs : 0 < s := Real.sqrt_pos.mpr hq'
    have hsq : s ^ 2 = q := Real.sq_sqrt hq
    have hlog : Real.log q = 2 * Real.log s := by
      rw [← hsq, Real.log_pow]; push_cast; ring
    have h1 : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    rw [Real.log_inv] at h1
    have h2 : -(s * Real.log s) ≤ 1 - s := by
      have := mul_le_mul_of_nonneg_left h1 hs.le
      rw [mul_sub, mul_inv_cancel₀ hs.ne', mul_one] at this
      linarith
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hl2, hlog, ← hsq]
    nlinarith

/-- Pointwise domination of a `[0, A]`-mixture of Poisson laws. -/
private lemma output_le {lam₀ A : ℝ} (hl : 0 ≤ lam₀) {k : ℕ} (pts : Fin k → ℝ)
    (w : ProbDist (Fin k)) (hpts : ∀ i, 0 ≤ pts i ∧ pts i ≤ A) (y : ℕ) :
    (∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y) ≤
      Real.exp (4 * (A + lam₀)) * ((1 : ℝ) / 4) ^ y := by
  have hB : 0 ≤ A + lam₀ := by
    rcases k with _ | k
    · -- no support points: use `w.sum_one` to derive a contradiction
      have := w.sum_one; simp at this
    · linarith [(hpts 0).1, (hpts 0).2]
  have hpt : ∀ i, poissonTrans lam₀ (pts i) y ≤ Real.exp (4 * (A + lam₀)) * ((1 : ℝ) / 4) ^ y := by
    intro i
    have hx0 : 0 ≤ pts i + lam₀ := by linarith [(hpts i).1]
    unfold poissonTrans
    rw [fact_eq]
    have hf : (0 : ℝ) < (y ! : ℝ) := by exact_mod_cast Nat.factorial_pos y
    have he : Real.exp (-(pts i + lam₀)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hp : (pts i + lam₀) ^ y ≤ (A + lam₀) ^ y :=
      pow_le_pow_left₀ hx0 (by linarith [(hpts i).2]) y
    have hexp := Real.pow_div_factorial_le_exp _ (by linarith : (0 : ℝ) ≤ 4 * (A + lam₀)) y
    have key : (A + lam₀) ^ y / (y ! : ℝ) =
        (4 * (A + lam₀)) ^ y / (y ! : ℝ) * ((1 : ℝ) / 4) ^ y := by
      rw [mul_pow, div_pow, one_pow]; field_simp
    calc Real.exp (-(pts i + lam₀)) * (pts i + lam₀) ^ y / (y ! : ℝ)
        ≤ 1 * (A + lam₀) ^ y / (y ! : ℝ) := by
          apply div_le_div_of_nonneg_right _ hf.le
          exact mul_le_mul he hp (by positivity) zero_le_one
      _ = (4 * (A + lam₀)) ^ y / (y ! : ℝ) * ((1 : ℝ) / 4) ^ y := by rw [one_mul, key]
      _ ≤ Real.exp (4 * (A + lam₀)) * ((1 : ℝ) / 4) ^ y :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
  calc (∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y)
      ≤ ∑ i : Fin k, w.pmf i * (Real.exp (4 * (A + lam₀)) * ((1 : ℝ) / 4) ^ y) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpt i) (w.nonneg i))
    _ = Real.exp (4 * (A + lam₀)) * ((1 : ℝ) / 4) ^ y := by
        rw [← Finset.sum_mul, w.sum_one, one_mul]

/-- Crude but junk-proof upper bound on the mutual information of any input on `[0, A]`. -/
theorem dtpcDiscreteMI_le {lam₀ A : ℝ} (hl : 0 ≤ lam₀) {k : ℕ} (pts : Fin k → ℝ)
    (w : ProbDist (Fin k)) (hpts : ∀ i, 0 ≤ pts i ∧ pts i ≤ A) :
    dtpcDiscreteMI lam₀ k pts w ≤ 4 * Real.exp (2 * (A + lam₀)) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold dtpcDiscreteMI
  simp only
  set E := Real.exp (2 * (A + lam₀)) with hE
  -- the conditional entropy term is nonnegative
  have hcond : 0 ≤ ∑ i : Fin k, w.pmf i *
      ∑' y : ℕ, negPLogP (poissonTrans lam₀ (pts i) y) := by
    refine Finset.sum_nonneg (fun i _ => mul_nonneg (w.nonneg i) (tsum_nonneg (fun y => ?_)))
    exact InfoTheory.Bridge.negPLogP_nonneg
      (poissonTrans_le_one (by linarith [(hpts i).1]) y)
  -- termwise bound on the output entropy
  have hterm : ∀ y : ℕ, negPLogP (∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y) ≤
      2 * E / Real.log 2 * ((1 : ℝ) / 2) ^ y := by
    intro y
    have hpy0 : 0 ≤ ∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (w.nonneg i)
        (poissonTrans_nonneg (by linarith [(hpts i).1]) y))
    refine (negPLogP_le_sqrt hpy0).trans ?_
    have hsq : Real.sqrt (∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y) ≤
        E * ((1 : ℝ) / 2) ^ y := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (E * ((1 : ℝ) / 2) ^ y) ^ 2 = Real.exp (4 * (A + lam₀)) * ((1 : ℝ) / 4) ^ y := by
        rw [mul_pow, hE, sq (Real.exp _), ← Real.exp_add, ← pow_mul, mul_comm y 2, pow_mul]
        norm_num
        ring_nf
      rw [this]
      exact output_le hl pts w hpts y
    rw [div_mul_eq_mul_div, mul_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hl2.le
  have hgeo : Summable (fun y : ℕ => 2 * E / Real.log 2 * ((1 : ℝ) / 2) ^ y) :=
    summable_geometric_two.mul_left _
  have hY : (∑' y : ℕ, negPLogP (∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y)) ≤
      4 * E / Real.log 2 := by
    have hval : (∑' y : ℕ, 2 * E / Real.log 2 * ((1 : ℝ) / 2) ^ y) = 4 * E / Real.log 2 := by
      rw [tsum_mul_left, tsum_geometric_two]; ring
    by_cases hs : Summable (fun y : ℕ =>
        negPLogP (∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y))
    · rw [← hval]; exact hs.tsum_le_tsum hterm hgeo
    · rw [tsum_eq_zero_of_not_summable hs]; positivity
  linarith

/-- The feasible set defining `dtpcCapacity`. -/
def capacitySet (lam₀ A mu : ℝ) : Set ℝ :=
  { r : ℝ | ∃ (k : ℕ) (pts : Fin k → ℝ) (w : ProbDist (Fin k)),
    (∀ i : Fin k, 0 ≤ pts i ∧ pts i ≤ A) ∧
    (∑ i : Fin k, w.pmf i * pts i) ≤ mu ∧
    r = dtpcDiscreteMI lam₀ k pts w }

lemma dtpcCapacity_eq (lam₀ A mu : ℝ) : dtpcCapacity lam₀ A mu = sSup (capacitySet lam₀ A mu) :=
  rfl

theorem capacitySet_bddAbove {lam₀ : ℝ} (hl : 0 ≤ lam₀) (A mu : ℝ) :
    BddAbove (capacitySet lam₀ A mu) := by
  refine ⟨4 * Real.exp (2 * (A + lam₀)) / Real.log 2, ?_⟩
  rintro r ⟨k, pts, w, hpts, -, rfl⟩
  exact dtpcDiscreteMI_le hl pts w hpts

/-- A deterministic input (all mass points equal) carries zero information. -/
theorem dtpcDiscreteMI_const (lam₀ c : ℝ) {k : ℕ} (pts : Fin k → ℝ) (w : ProbDist (Fin k))
    (hc : ∀ i, pts i = c) : dtpcDiscreteMI lam₀ k pts w = 0 := by
  unfold dtpcDiscreteMI
  simp only [hc, ← Finset.sum_mul, w.sum_one, one_mul, sub_self]

/-- The point mass on `Fin 1`. -/
def pointMass : ProbDist (Fin 1) where
  pmf := fun _ => 1
  nonneg := fun _ => zero_le_one
  sum_one := by simp

theorem capacitySet_nonempty (lam₀ : ℝ) {A mu : ℝ} (hA : 0 ≤ A) (hmu : 0 ≤ mu) :
    (0 : ℝ) ∈ capacitySet lam₀ A mu :=
  ⟨1, fun _ => 0, pointMass, fun _ => ⟨le_rfl, hA⟩, by simp [pointMass, hmu],
    (dtpcDiscreteMI_const lam₀ 0 _ _ (fun _ => rfl)).symm⟩

theorem dtpcCapacity_nonneg {lam₀ A mu : ℝ} (hl : 0 ≤ lam₀) (hA : 0 ≤ A) (hmu : 0 ≤ mu) :
    0 ≤ dtpcCapacity lam₀ A mu :=
  le_csSup (capacitySet_bddAbove hl A mu) (capacitySet_nonempty lam₀ hA hmu)

theorem le_dtpcCapacity {lam₀ A mu : ℝ} (hl : 0 ≤ lam₀) {k : ℕ} (pts : Fin k → ℝ)
    (w : ProbDist (Fin k)) (hpts : ∀ i, 0 ≤ pts i ∧ pts i ≤ A)
    (hmean : (∑ i : Fin k, w.pmf i * pts i) ≤ mu) :
    dtpcDiscreteMI lam₀ k pts w ≤ dtpcCapacity lam₀ A mu :=
  le_csSup (capacitySet_bddAbove hl A mu) ⟨k, pts, w, hpts, hmean, rfl⟩

/-- **Regression.** With zero peak amplitude the capacity is `0`. -/
theorem dtpcCapacity_zero_amplitude {lam₀ mu : ℝ} (hl : 0 ≤ lam₀) (hmu : 0 ≤ mu) :
    dtpcCapacity lam₀ 0 mu = 0 := by
  refine le_antisymm ?_ (dtpcCapacity_nonneg hl le_rfl hmu)
  refine csSup_le ⟨0, capacitySet_nonempty lam₀ le_rfl hmu⟩ ?_
  rintro r ⟨k, pts, w, hpts, -, rfl⟩
  exact (dtpcDiscreteMI_const lam₀ 0 pts w
    (fun i => le_antisymm (hpts i).2 (hpts i).1)).le

end InfoTheory.Known.Certificates.PoissonChannelDiscreteCapacity
