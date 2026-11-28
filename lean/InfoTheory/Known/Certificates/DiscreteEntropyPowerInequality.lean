import InfoTheory.Problems.DiscreteEntropyPowerInequality
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.DiscreteEntropyPowerInequality`

The frozen statement is Tao's discrete entropy power conjecture
`H(X₁ + ⋯ + X_{n+1}) ≥ H(X₁ + ⋯ + Xₙ) + ½ ln((n+1)/n) - ε` for i.i.d. integer `Xᵢ` of large
entropy (Tao, "Sumset and inverse sumset theory for Shannon entropy", Combin. Probab. Comput.
19, 2010, §1; Gavalakis, "Discrete generalised entropy power inequalities for log-concave
random variables", 2023). This file checks that the auxiliary definitions `intConvPow` and
`intEntropyFn` mean what they should.

## Certified
* `intConvPow_zero`, `intEntropyFn_intConvPow_zero`: `S₀ = 0` is the point mass at `0`, with
  entropy `0`.
* `intConvPow_one`, `intEntropyFn_intConvPow_one`: `S₁ = X₁` (the convolution power is
  correctly normalized: `δ₀ * p = p`, via `tsum_ite_eq`), so for `n = 1` the Statement compares
  `H(X₁ + X₂)` with `H(X₁) = intEntropy P` as intended.
* `pointMass`, `intEntropy_pointMass`, `hasFiniteIntEntropy_pointMass`: a point mass has
  (finite) entropy `0` (Cover–Thomas §2.1), so the hypothesis `M ≤ intEntropy P` with `M > 0`
  genuinely excludes degenerate laws.
* `entropy_gap_pos`: the conjectured gap `½ ln((n+1)/n)` is positive for `n ≥ 1`.

## Regression
* `regression_bernoulli_half`: for i.i.d. fair Bernoulli `X₁, X₂` (`bern`), the exact objects
  `intConvPow`/`intEntropyFn` give `H(X₁+X₂) = (3/2) ln 2 = H(X₁) + ½ ln 2`
  (`conv_bern`: `X₁ + X₂ ~ (1/4, 1/2, 1/4)`), the known textbook value; so at `n = 1` the
  Statement's inequality is an equality with `ε = 0` for this law (the Statement's large-entropy
  hypothesis `M ≤ H` excludes it, so nothing about the Statement is decided).

## Not certified
* Any part of the conjecture (Gavalakis's log-concave case, Tao's asymptotic results); the
  general summability of convolution powers of a PMF.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.DiscreteEntropyPowerInequality

open InfoTheory InfoTheory.Problems.DiscreteEntropyPowerInequality

/-- `S₀` is the point mass at `0`. -/
theorem intConvPow_zero (p : ℤ → ℝ) : intConvPow p 0 = fun k => if k = 0 then 1 else 0 := rfl

/-- The entropy of the point mass `S₀` is `0`. -/
theorem intEntropyFn_intConvPow_zero (p : ℤ → ℝ) : intEntropyFn (intConvPow p 0) = 0 := by
  rw [intConvPow_zero]
  unfold intEntropyFn
  have : ∀ k : ℤ, (if (if k = 0 then (1 : ℝ) else 0) ≤ 0 then 0 else
      -(if k = 0 then (1 : ℝ) else 0) * Real.log (if k = 0 then (1 : ℝ) else 0)) = 0 := by
    intro k; by_cases hk : k = 0 <;> simp [hk]
  simp_rw [this, tsum_zero]

/-- `S₁ = X₁`: convolving with the point mass at `0` is the identity. -/
theorem intConvPow_one (p : ℤ → ℝ) : intConvPow p 1 = p := by
  funext n
  show ∑' k : ℤ, intConvPow p 0 k * p (n - k) = p n
  rw [intConvPow_zero]
  have : ∀ k : ℤ, (if k = 0 then (1 : ℝ) else 0) * p (n - k) = if k = 0 then p n else 0 := by
    intro k; by_cases hk : k = 0 <;> simp [hk]
  simp_rw [this]
  exact tsum_ite_eq (0 : ℤ) (fun _ => p n)

/-- Hence `intEntropyFn (intConvPow P.pmf 1) = intEntropy P`. -/
theorem intEntropyFn_intConvPow_one (P : IntProbDist) :
    intEntropyFn (intConvPow P.pmf 1) = intEntropy P := by
  rw [intConvPow_one]; rfl

/-- The point mass at `a : ℤ`. -/
noncomputable def pointMass (a : ℤ) : IntProbDist where
  pmf := fun k => if k = a then 1 else 0
  nonneg := fun k => by by_cases h : k = a <;> simp [h]
  summable := by
    have h := hasSum_ite_eq a (1 : ℝ)
    exact h.summable
  tsum_one := by
    exact tsum_ite_eq a (fun _ => (1 : ℝ))

private lemma pointMass_term (a k : ℤ) :
    (if (pointMass a).pmf k ≤ 0 then 0 else -(pointMass a).pmf k * Real.log ((pointMass a).pmf k))
      = 0 := by
  by_cases h : k = a <;> simp [pointMass, h]

/-- A point mass has finite entropy. -/
theorem hasFiniteIntEntropy_pointMass (a : ℤ) : HasFiniteIntEntropy (pointMass a) := by
  unfold HasFiniteIntEntropy
  simp_rw [pointMass_term]
  exact summable_zero

/-- A point mass has entropy `0` (Cover–Thomas §2.1). -/
theorem intEntropy_pointMass (a : ℤ) : intEntropy (pointMass a) = 0 := by
  unfold intEntropy
  simp_rw [pointMass_term, tsum_zero]

/-- The conjectured entropy gap `½ ln((n+1)/n)` is positive for `n ≥ 1`. -/
theorem entropy_gap_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (1 / 2 : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine mul_pos (by norm_num) (Real.log_pos ?_)
  rw [one_lt_div (by linarith)]
  linarith

/-! ### Regression: fair Bernoulli -/

/-- The fair Bernoulli PMF on `{0, 1} ⊆ ℤ`. -/
noncomputable def bern : ℤ → ℝ := fun k => if k = 0 ∨ k = 1 then 1 / 2 else 0

/-- `X₁ + X₂` for fair Bernoulli: the `(1/4, 1/2, 1/4)` law. -/
lemma conv_bern (n : ℤ) :
    intConvFn bern bern n = if n = 0 ∨ n = 2 then 1 / 4 else if n = 1 then 1 / 2 else 0 := by
  unfold intConvFn
  rw [tsum_eq_sum (s := {0, 1}) (fun b hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [bern, hb.1, hb.2])]
  rw [Finset.sum_pair (by norm_num)]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ (n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2)) with rfl | rfl | rfl | ⟨h0, h1, h2⟩
  · norm_num [bern]
  · norm_num [bern]
  · norm_num [bern]
  · have h3 : n - 1 ≠ 0 := by omega
    have h4 : n - 1 ≠ 1 := by omega
    simp [bern, h0, h1, h2, h3, h4]

/-- `H(X₁) = ln 2`. -/
lemma entropy_bern : intEntropyFn bern = Real.log 2 := by
  unfold intEntropyFn
  rw [tsum_eq_sum (s := {0, 1}) (fun b hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [bern, hb.1, hb.2])]
  rw [Finset.sum_pair (by norm_num)]
  have l2 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  norm_num [bern]
  rw [l2]; ring

/-- `H(X₁ + X₂) = (3/2) ln 2`. -/
lemma entropy_conv_bern : intEntropyFn (intConvFn bern bern) = 3 / 2 * Real.log 2 := by
  unfold intEntropyFn
  rw [tsum_eq_sum (s := {0, 1, 2}) (fun b hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [conv_bern, hb.1, hb.2.1, hb.2.2])]
  rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)]
  simp only [conv_bern]
  have l2 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  have l4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  norm_num
  rw [l2, l4]; ring

/-- **Regression** (exact Bernoulli(1/2) computation): for i.i.d. fair bits the frozen objects
give `H(X₁ + X₂) = H(X₁) + ½ ln((1+1)/1)` exactly, i.e. the Statement's inequality at `n = 1`
holds with equality and `ε = 0`. -/
theorem regression_bernoulli_half :
    intEntropyFn (intConvPow bern (1 + 1)) =
      intEntropyFn (intConvPow bern 1) +
        (1 / 2 : ℝ) * Real.log ((((1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
  have h2 : intConvPow bern (1 + 1) = intConvFn bern bern := by
    show intConvFn (intConvPow bern 1) bern = _
    rw [intConvPow_one]
  rw [h2, intConvPow_one, entropy_conv_bern, entropy_bern]
  norm_num
  ring

end InfoTheory.Known.Certificates.DiscreteEntropyPowerInequality
