import InfoTheory.Problems.GaussianMultipleDescriptions3

/-!
# Certificate for `InfoTheory.Problems.GaussianMultipleDescriptions3`

The statement asks whether the optimal symmetric per-description rate `gaussMD3SymRate` of
three-description quadratic Gaussian multiple descriptions equals `tmdSymRateLowerBound`, the
optimised Tian–Mohajer–Diggavi (2009) three-level converse, for all `0 < D₃ ≤ D₂ ≤ D₁ ≤ 1`.

## Certified (about exactly these objects, on `0 < D₃ ≤ D₂ ≤ D₁ ≤ 1`)
* `tmdBoundTerm_le_srulp`, `tmdSymRateLowerBound_le_srulp`: the bound never exceeds the
  successive-refinement + MDS rate `½ log₂(1/D₁) + ¼ log₂(D₁/D₂) + ⅙ log₂(D₂/D₃)`
  (Tian–Mohajer–Diggavi 2009, eq. (22), an achievable rate), so it is a sound candidate value.
* `tmdSymRateLowerBound_lt_top`: the right-hand side is finite (not junk `⊤`).
* `half_log_le_tmdSymRateLowerBound`: it is at least Shannon's single-description bound
  `½ log₂(1/D₁)`.
* Regression reductions to solved special cases:
  - `tmdSymRateLowerBound_diag`: `RHS(D, D, D) = ½ log₂(1/D)`, the Gaussian `R(D)` (when only
    individual descriptions matter, each description must be a rate-distortion code).
  - `tmdSymRateLowerBound_pairwise_only`: `RHS(1, D, D) = ¼ log₂(1/D)`, the exact
    pairwise-only symmetric rate, achieved by a `(3,2)` MDS split of a rate-`½ log₂(1/D)` code.
  - `ozarow_pair_le_tmdSymRateLowerBound`: with `b = 0`, the RHS dominates Ozarow's
    two-description sum-rate bound for a pair (Song–Shao–Chen 2014, Cor. 11 with `L = 2`).
  - `wangViswanath_le_tmdSymRateLowerBound`: when `D₂ = D₁`, with `b = a`, it dominates the
    one-auxiliary Wang–Viswanath bound (exact when `D₂` is inactive; Song–Shao–Chen Cor. 12).

## Not certified
* Anything about `gaussMD3SymRate` itself. That needs measurable quantizers with Gaussian
  integrals over `Fin n → ℝ` for achievability, and the Tian–Mohajer–Diggavi remote-source
  converse for lower bounds. Neither is in `Bridge`.
* The closed-form Wang–Viswanath value of the RHS at `D₂ = D₁` (a one-dimensional
  optimisation), and convexity of the RHS in `(D₁, D₂, D₃)`.
-/

open scoped BigOperators ENNReal

namespace InfoTheory.Known.Certificates.GaussianMultipleDescriptions3

open InfoTheory InfoTheory.Problems.GaussianMultipleDescriptions3

theorem md3_log2_div {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    log2 (p / q) = log2 p - log2 q := by
  unfold log2; rw [Real.log_div hp.ne' hq.ne', sub_div]

theorem md3_log2_one : log2 1 = 0 := by unfold log2; simp

theorem md3_log2_le {p q : ℝ} (hp : 0 < p) (h : p ≤ q) : log2 p ≤ log2 q :=
  div_le_div_of_nonneg_right (Real.log_le_log hp h) (Real.log_pos one_lt_two).le

/-- `t + D (1 - t)` lies between `D` and `1`, and is monotone in `D` for `t ≤ 1`. -/
theorem md3_mix_bounds {D t : ℝ} (hD : 0 < D) (hD1 : D ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < t + D * (1 - t) ∧ D ≤ t + D * (1 - t) ∧ t + D * (1 - t) ≤ 1 := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Each member of the family is at most the SR–MDS achievable rate**
    `½ log₂(1/D₁) + ¼ log₂(D₁/D₂) + ⅙ log₂(D₂/D₃)` (Tian–Mohajer–Diggavi 2009, eq. (22)). -/
theorem tmdBoundTerm_le_srulp {D₁ D₂ D₃ a b : ℝ} (h3 : 0 < D₃) (h32 : D₃ ≤ D₂)
    (h21 : D₂ ≤ D₁) (h1 : D₁ ≤ 1) (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    tmdBoundTerm D₁ D₂ D₃ a b ≤
      (1 / 2 : ℝ) * log2 (1 / D₁) + (1 / 4 : ℝ) * log2 (D₁ / D₂) +
        (1 / 6 : ℝ) * log2 (D₂ / D₃) := by
  have h2 : 0 < D₂ := lt_of_lt_of_le h3 h32
  have h1' : 0 < D₁ := lt_of_lt_of_le h2 h21
  have ha0 : 0 ≤ a := le_trans hb hba
  have hb1 : b ≤ 1 := le_trans hba ha
  obtain ⟨hx1, hDx1, -⟩ := md3_mix_bounds h1' h1 ha0 ha
  obtain ⟨hx2, -, -⟩ := md3_mix_bounds h2 (le_trans h21 h1) ha0 ha
  obtain ⟨hy, hDy, -⟩ := md3_mix_bounds h2 (le_trans h21 h1) hb hb1
  obtain ⟨hy3, -, -⟩ := md3_mix_bounds h3 (le_trans h32 (le_trans h21 h1)) hb hb1
  have hx21 : a + D₂ * (1 - a) ≤ a + D₁ * (1 - a) := by nlinarith
  have hy3y : b + D₃ * (1 - b) ≤ b + D₂ * (1 - b) := by nlinarith
  unfold tmdBoundTerm
  rw [md3_log2_div one_pos hx1, md3_log2_div hx2 hy, md3_log2_div hy3 h3,
    md3_log2_div one_pos h1', md3_log2_div h1' h2, md3_log2_div h2 h3]
  have e1 := md3_log2_le hx2 hx21
  have e2 := md3_log2_le hy3 hy3y
  have e3 := md3_log2_le h1' hDx1
  have e4 := md3_log2_le h2 hDy
  linarith

/-- **The right-hand side is at most the SR–MDS achievable rate.** -/
theorem tmdSymRateLowerBound_le_srulp {D₁ D₂ D₃ : ℝ} (h3 : 0 < D₃) (h32 : D₃ ≤ D₂)
    (h21 : D₂ ≤ D₁) (h1 : D₁ ≤ 1) :
    tmdSymRateLowerBound D₁ D₂ D₃ ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 / D₁) + (1 / 4 : ℝ) * log2 (D₁ / D₂) +
        (1 / 6 : ℝ) * log2 (D₂ / D₃)) := by
  unfold tmdSymRateLowerBound
  refine iSup_le fun a => iSup_le fun b => iSup_le fun h => ?_
  exact ENNReal.ofReal_le_ofReal (tmdBoundTerm_le_srulp h3 h32 h21 h1 h.1 h.2.1 h.2.2)

/-- **The right-hand side is finite** (never the junk `⊤`) on the domain of `Statement`. -/
theorem tmdSymRateLowerBound_lt_top {D₁ D₂ D₃ : ℝ} (h3 : 0 < D₃) (h32 : D₃ ≤ D₂)
    (h21 : D₂ ≤ D₁) (h1 : D₁ ≤ 1) : tmdSymRateLowerBound D₁ D₂ D₃ < ⊤ :=
  lt_of_le_of_lt (tmdSymRateLowerBound_le_srulp h3 h32 h21 h1) ENNReal.ofReal_lt_top

/-- Every feasible parameter pair gives a lower estimate of the right-hand side. -/
theorem le_tmdSymRateLowerBound {D₁ D₂ D₃ a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    ENNReal.ofReal (tmdBoundTerm D₁ D₂ D₃ a b) ≤ tmdSymRateLowerBound D₁ D₂ D₃ := by
  unfold tmdSymRateLowerBound
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le ⟨hb, hba, ha⟩ le_rfl))

/-- **Single-description converse**: the right-hand side is at least `½ log₂(1/D₁)`
    (take `a = b = 0`). -/
theorem half_log_le_tmdSymRateLowerBound {D₁ D₂ D₃ : ℝ} (h2 : 0 < D₂) (h3 : 0 < D₃) :
    ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 / D₁)) ≤ tmdSymRateLowerBound D₁ D₂ D₃ := by
  refine le_trans (le_of_eq ?_) (le_tmdSymRateLowerBound (le_refl (0 : ℝ)) le_rfl zero_le_one)
  unfold tmdBoundTerm
  congr 1
  simp only [sub_zero, mul_one, zero_add, div_self h2.ne', div_self h3.ne', md3_log2_one]
  ring

/-- **Regression: individual descriptions only.** `RHS(D, D, D) = ½ log₂(1/D)`, Shannon's
    Gaussian rate–distortion function, which is the exact answer in this case. -/
theorem tmdSymRateLowerBound_diag {D : ℝ} (h0 : 0 < D) (h1 : D ≤ 1) :
    tmdSymRateLowerBound D D D = ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 / D)) := by
  refine le_antisymm (le_trans (tmdSymRateLowerBound_le_srulp h0 le_rfl le_rfl h1)
    (le_of_eq ?_)) (half_log_le_tmdSymRateLowerBound h0 h0)
  rw [div_self h0.ne', md3_log2_one]
  ring_nf

/-- **Regression: pairwise constraint only.** `RHS(1, D, D) = ¼ log₂(1/D)`, the exact
    symmetric rate when only pairs must reach distortion `D`. -/
theorem tmdSymRateLowerBound_pairwise_only {D : ℝ} (h0 : 0 < D) (h1 : D ≤ 1) :
    tmdSymRateLowerBound 1 D D = ENNReal.ofReal ((1 / 4 : ℝ) * log2 (1 / D)) := by
  refine le_antisymm (le_trans (tmdSymRateLowerBound_le_srulp h0 le_rfl h1 le_rfl)
    (le_of_eq ?_)) (le_trans (le_of_eq ?_) (le_tmdSymRateLowerBound (b := 0) (a := 1)
      le_rfl zero_le_one le_rfl))
  · rw [div_self h0.ne', md3_log2_one, div_one, md3_log2_one]
    ring_nf
  · unfold tmdBoundTerm
    congr 1
    simp only [sub_self, mul_zero, add_zero, sub_zero, mul_one, zero_add, div_one,
      div_self h0.ne', md3_log2_one]

/-- **The RHS dominates Ozarow's two-description bound** applied to any pair (the slice
    `b = 0`; in the MMSE parametrisation `a`, this is Song–Shao–Chen 2014, Cor. 11 for `L = 2`,
    i.e. Ozarow's symmetric two-description sum rate, halved). -/
theorem ozarow_pair_le_tmdSymRateLowerBound {D₁ D₂ D₃ a : ℝ} (h3 : 0 < D₃) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) :
    ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 / (a + D₁ * (1 - a))) +
      (1 / 4 : ℝ) * log2 ((a + D₂ * (1 - a)) / D₂)) ≤ tmdSymRateLowerBound D₁ D₂ D₃ := by
  refine le_trans (le_of_eq ?_) (le_tmdSymRateLowerBound (b := 0) le_rfl ha0 ha1)
  unfold tmdBoundTerm
  congr 1
  simp only [sub_zero, mul_one, zero_add, div_self h3.ne', md3_log2_one]
  ring

/-- **The RHS dominates the one-auxiliary Wang–Viswanath bound** when the pairwise constraint
    is inactive (`D₂ = D₁`; the slice `b = a`). That bound is the exact answer there
    (Wang–Viswanath 2007; Chen 2009; Song–Shao–Chen 2014, Cor. 12). -/
theorem wangViswanath_le_tmdSymRateLowerBound {D₁ D₃ a : ℝ} (h1 : 0 < D₁) (h1' : D₁ ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ENNReal.ofReal ((1 / 2 : ℝ) * log2 (1 / (a + D₁ * (1 - a))) +
      (1 / 6 : ℝ) * log2 ((a + D₃ * (1 - a)) / D₃)) ≤ tmdSymRateLowerBound D₁ D₁ D₃ := by
  refine le_trans (le_of_eq ?_) (le_tmdSymRateLowerBound (b := a) ha0 le_rfl ha1)
  obtain ⟨hx, -, -⟩ := md3_mix_bounds h1 h1' ha0 ha1
  unfold tmdBoundTerm
  congr 1
  rw [div_self hx.ne', md3_log2_one]
  ring

end InfoTheory.Known.Certificates.GaussianMultipleDescriptions3
