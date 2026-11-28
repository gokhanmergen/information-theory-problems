import InfoTheory.Problems.CourtadeKumarQary
import InfoTheory.Known.Entropy
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.CourtadeKumarQary`

The frozen statement: `I(f(X); Y) ≤ log₂ q - h(α) - α log₂(q-1)` for every
`f : (Fin q)^n → Fin q` over `QSC(q, α)^n`, `0 ≤ α < 1 - 1/q`. Facts about the *exact*
object `mutualInfoQSC`:

## Certified
* `mutualInfoQSC_nonneg`, `mutualInfoQSC_le_log2`: `0 ≤ I(f(X); Y) ≤ log₂ q`.
* `rhs_nonneg`: the conjectured bound is `≥ 0` on all of `α ∈ [0, 1]` (concavity of `log`), so
  constant functions never refute it.
* `rhs_two`, `qarySC_two_trans` (regression): at `q = 2` the channel is `BSC(α)` and the bound is
  exactly the binary Courtade–Kumar bound `1 - h(α)` — the `q = 2` slice is the binary
  conjecture, proved in Sept. 2026 (`arXiv:2609.24931` and independent proofs).
* `noise_range_nonempty`: the admissible noise range is non-empty for every `q ≥ 2`.

## Not certified
* Equality for dictators (`f(x) = x₀`) for `q ≥ 3`, and the transfer of the binary resolution
  to `mutualInfoQSC 2` (needs `Fin 2 ≃ Bool` invariance of mutual information).
* Numerical evidence (2026-11-27, local search over all `f` for `(q, n) = (3, 2)` exhaustively
  and `(4, 2), (3, 3), (5, 2)` by hill climbing, `α ∈ {0.05, 0.2, 0.4, ~0.9(1-1/q)}`): no
  function beat the dictator.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CourtadeKumarQary

open InfoTheory InfoTheory.Problems.CourtadeKumarQary

/-- `0 ≤ I(f(X); Y)`. -/
theorem mutualInfoQSC_nonneg (q n : ℕ) (hq : 2 ≤ q) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (f : (Fin n → Fin q) → Fin q) : 0 ≤ mutualInfoQSC q n hq α h0 h1 f := by
  unfold mutualInfoQSC
  exact Bridge.mutualInfo_nonneg _

/-- `I(f(X); Y) ≤ H(f(X)) ≤ log₂ q` (Cover–Thomas Thms 2.4.1, 2.6.4). -/
theorem mutualInfoQSC_le_log2 (q n : ℕ) (hq : 2 ≤ q) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (f : (Fin n → Fin q) → Fin q) : mutualInfoQSC q n hq α h0 h1 f ≤ log2 (q : ℝ) := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  unfold mutualInfoQSC
  refine le_trans (Known.mutualInfo_le_entropy_fst _) ?_
  have h := Bridge.shannonEntropy_le_log2_card
    ((((qarySC q hq α h0 h1).power n).joint ProbDist.uniform).map
      (fun xy => (f xy.1, xy.2))).fst
  simpa [Fintype.card_fin] using h

private lemma log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- The conjectured bound is non-negative: `h(α) + α log₂(q-1) ≤ log₂ q` for `α ∈ [0, 1]`
    (the entropy of a `QSC(q, α)` row is at most `log₂ q`). In particular the Statement is not
    refuted by constant functions (which have `I = 0`). -/
theorem rhs_nonneg {q : ℕ} (hq : 2 ≤ q) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    0 ≤ log2 (q : ℝ) - binaryEntropy α - α * log2 ((q : ℝ) - 1) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl2 := log_two_pos
  unfold binaryEntropy negPLogP log2
  rcases h0.eq_or_lt with rfl | ha0
  · simp only [le_refl, ite_true, sub_zero, zero_mul]
    have : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    simp only [this, ite_false, Real.log_one, zero_div, mul_zero, add_zero, sub_zero]
    exact div_nonneg (Real.log_nonneg (by linarith)) hl2.le
  rcases h1.eq_or_lt with rfl | ha1
  · have : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    simp only [this, ite_false, sub_self, le_refl, ite_true, Real.log_one, zero_div, mul_zero,
      neg_zero, add_zero, one_mul, sub_zero]
    rw [sub_nonneg]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hl2.le
  have hn0 : ¬ (α ≤ 0) := not_le.mpr ha0
  have hn1 : ¬ (1 - α ≤ 0) := by linarith
  simp only [hn0, hn1, ite_false]
  -- concavity of `log`: `α log((q-1)/α) + (1-α) log(1/(1-α)) ≤ log q`
  have hx : (0 : ℝ) < ((q : ℝ) - 1) / α := div_pos (by linarith) ha0
  have hy : (0 : ℝ) < 1 / (1 - α) := div_pos one_pos (by linarith)
  have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy)
    h0 (by linarith : (0 : ℝ) ≤ 1 - α) (by ring)
  simp only [smul_eq_mul] at hc
  have hsum : α * (((q : ℝ) - 1) / α) + (1 - α) * (1 / (1 - α)) = q := by
    field_simp; ring
  rw [hsum, Real.log_div (by linarith) ha0.ne', Real.log_div one_ne_zero (by linarith),
    Real.log_one] at hc
  rw [show Real.log q / Real.log 2 - (-α * (Real.log α / Real.log 2) +
      -(1 - α) * (Real.log (1 - α) / Real.log 2)) - α * (Real.log ((q : ℝ) - 1) / Real.log 2)
      = (Real.log q - (α * (Real.log ((q : ℝ) - 1) - Real.log α) +
          (1 - α) * (0 - Real.log (1 - α)))) / Real.log 2 by field_simp; ring]
  exact div_nonneg (by linarith) hl2.le

/-- **Regression.** At `q = 2` the conjectured bound is exactly the binary Courtade–Kumar bound
    `1 - h(α)` (Courtade–Kumar 2014, Conjecture 1; resolved Sept. 2026, `arXiv:2609.24931`). -/
theorem rhs_two (α : ℝ) :
    log2 ((2 : ℕ) : ℝ) - binaryEntropy α - α * log2 (((2 : ℕ) : ℝ) - 1) = 1 - binaryEntropy α := by
  unfold log2
  norm_num [div_self (ne_of_gt log_two_pos)]

/-- At `q = 2` the channel `QSC(2, α)` is the binary symmetric channel: it flips with
    probability `α`. -/
theorem qarySC_two_trans (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (x y : Fin 2) :
    (qarySC 2 le_rfl α h0 h1).trans x y = if y = x then 1 - α else α := by
  simp [qarySC]
  norm_num

/-- The admissible noise range `0 ≤ α < 1 - 1/q` is non-empty for every `q ≥ 2`, so the
    Statement quantifies over a genuine family. -/
theorem noise_range_nonempty {q : ℕ} (hq : 2 ≤ q) : (0 : ℝ) < 1 - 1 / (q : ℝ) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

end InfoTheory.Known.Certificates.CourtadeKumarQary
