import InfoTheory.Problems.SbmMultiCommunityThreshold
import InfoTheory.Known.Channels

/-!
# Certificate for `InfoTheory.Problems.SbmMultiCommunityThreshold`

The frozen statement: for `q = 4` and every `0 < b < a` strictly below the Kesten–Stigum line
`(a-b)² < 4(a+3b)`, weak recovery is impossible. Facts about the *exact* objects:

## Certified
* `sbmCondProb_diag`, `sbmProb_diag` (regression): with `a = b` the SBM *is* `G(n, a/n)`;
  `avg_degree_diag`; `not_distinguishable_diag`: then the SBM is not distinguishable from
  Erdős–Rényi (TV `≡ 0`), as it must be.
* `maxPermOverlap_le_one`, `maxPermOverlap_nonneg`, `maxPermOverlap_self`,
  `maxPermOverlap_relabel`: the overlap is a genuine `[0, 1]`-valued maximum over permutations
  (no `sSup` junk), the exact estimator scores `1`, and so does any relabeling of it.
* `below_KS_example`, `above_KS_example`, `hypothesis_iff_snr_lt_one`: the hypothesis region is
  non-empty, proper, and is exactly `SNR < 1` at `q = 4`.

## Not certified
* Mossel–Neeman–Sly (`q = 2`: no weak recovery below KS) and Mossel–Sly–Sohn (`q = 3, 4`,
  large degree) — deep. Above-KS recovery (Abbe–Sandon, Bordenave–Lelarge–Massoulié).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.SbmMultiCommunityThreshold

open InfoTheory InfoTheory.Problems.SbmMultiCommunityThreshold

/-! ### Zero signal: `a = b` gives exactly Erdős–Rényi -/

theorem sbmCondProb_diag (n q : ℕ) (a : ℝ) (σ : Fin n → Fin q) (G : Graph n) :
    sbmCondProb n q a a σ G = erProb n a G := by
  unfold sbmCondProb erProb
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp only [ite_self]

/-- **Regression.** With `a = b` the SBM marginal *is* `G(n, a/n)`. -/
theorem sbmProb_diag {q : ℕ} (hq : 1 ≤ q) (n : ℕ) (a : ℝ) (G : Graph n) :
    sbmProb n q a a G = erProb n a G := by
  unfold sbmProb
  simp only [sbmCondProb_diag, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]
  have : ((q ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The average degree `(a + (q-1) a)/q` of the zero-signal model is `a`. -/
lemma avg_degree_diag {q : ℕ} (hq : 1 ≤ q) (a : ℝ) :
    (a + ((q - 1 : ℕ) : ℝ) * a) / (q : ℝ) = a := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hq, Nat.cast_one]
  field_simp
  ring

/-- **Regression.** With no community signal (`a = b`) the SBM is *not* distinguishable from
    Erdős–Rényi: the total variation in `sbmDistinguishableFromER` is identically `0`. -/
theorem not_distinguishable_diag {q : ℕ} (hq : 1 ≤ q) (a : ℝ) :
    ¬ sbmDistinguishableFromER q a a := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  have := hN N le_rfl
  simp only [avg_degree_diag hq, sbmProb_diag hq, sub_self, abs_zero,
    Finset.sum_const_zero, mul_zero] at this
  linarith

/-! ### The overlap functional is a genuine `[0, 1]`-valued maximum -/

/-- The set whose supremum is `maxPermOverlap`. -/
def overlapSet {n q : ℕ} (σ τ : Fin n → Fin q) : Set ℝ :=
  { r : ℝ | ∃ (π : Fin q → Fin q), Function.Bijective π ∧
    r = ((1 : ℝ) / (n : ℝ)) * ∑ v : Fin n, if τ v = π (σ v) then (1 : ℝ) else 0 }

lemma agree_sum_le {n q : ℕ} (σ τ : Fin n → Fin q) (π : Fin q → Fin q) :
    ((1 : ℝ) / (n : ℝ)) * ∑ v : Fin n, (if τ v = π (σ v) then (1 : ℝ) else 0) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hs : ∑ v : Fin n, (if τ v = π (σ v) then (1 : ℝ) else 0) ≤ n := by
      calc _ ≤ ∑ _v : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum (fun v _ => by split_ifs <;> norm_num)
        _ = n := by simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_mul_eq_mul_div, one_mul, div_le_one hn']
    exact hs

lemma agree_sum_nonneg {n q : ℕ} (σ τ : Fin n → Fin q) (π : Fin q → Fin q) :
    0 ≤ ((1 : ℝ) / (n : ℝ)) * ∑ v : Fin n, (if τ v = π (σ v) then (1 : ℝ) else 0) :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num))

lemma overlapSet_bddAbove {n q : ℕ} (σ τ : Fin n → Fin q) : BddAbove (overlapSet σ τ) :=
  ⟨1, by rintro r ⟨π, -, rfl⟩; exact agree_sum_le σ τ π⟩

lemma overlapSet_id_mem {n q : ℕ} (σ τ : Fin n → Fin q) :
    ((1 : ℝ) / (n : ℝ)) * ∑ v : Fin n, (if τ v = σ v then (1 : ℝ) else 0) ∈ overlapSet σ τ :=
  ⟨id, Function.bijective_id, rfl⟩

theorem maxPermOverlap_le_one {n q : ℕ} (σ τ : Fin n → Fin q) : maxPermOverlap σ τ ≤ 1 :=
  csSup_le ⟨_, overlapSet_id_mem σ τ⟩ (by rintro r ⟨π, -, rfl⟩; exact agree_sum_le σ τ π)

theorem maxPermOverlap_nonneg {n q : ℕ} (σ τ : Fin n → Fin q) : 0 ≤ maxPermOverlap σ τ :=
  le_trans (agree_sum_nonneg σ τ id) (le_csSup (overlapSet_bddAbove σ τ) (overlapSet_id_mem σ τ))

/-- The exact estimator `τ = σ` has overlap exactly `1` (for `n ≥ 1`). -/
theorem maxPermOverlap_self {n q : ℕ} (hn : 1 ≤ n) (σ : Fin n → Fin q) :
    maxPermOverlap σ σ = 1 := by
  refine le_antisymm (maxPermOverlap_le_one σ σ) ?_
  have h := le_csSup (overlapSet_bddAbove σ σ) (overlapSet_id_mem σ σ)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  rw [one_div, inv_mul_cancel₀ hn'] at h
  exact h

/-- Overlap is invariant under relabeling the estimate by a permutation: relabeled estimates
    have the same score (`π` is absorbed into the maximization). -/
theorem maxPermOverlap_relabel {n q : ℕ} (hn : 1 ≤ n) (σ : Fin n → Fin q) (π : Fin q → Fin q)
    (hπ : Function.Bijective π) : maxPermOverlap σ (π ∘ σ) = 1 := by
  refine le_antisymm (maxPermOverlap_le_one σ _) ?_
  have hmem : ((1 : ℝ) / (n : ℝ)) * ∑ v : Fin n,
      (if (π ∘ σ) v = π (σ v) then (1 : ℝ) else 0) ∈ overlapSet σ (π ∘ σ) := ⟨π, hπ, rfl⟩
  have h := le_csSup (overlapSet_bddAbove σ (π ∘ σ)) hmem
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [one_div, inv_mul_cancel₀ hn'] at h
  exact h

/-! ### The Statement's hypothesis region is non-empty and is exactly "below Kesten–Stigum" -/

/-- `(a, b) = (2, 1)` lies below the `q = 4` Kesten–Stigum line, so the Statement is not
    vacuous. -/
theorem below_KS_example : (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 ∧ ((2 : ℝ) - 1) ^ 2 < 4 * (2 + 3 * 1) := by
  norm_num

/-- `(a, b) = (20, 1)` lies strictly above the `q = 4` KS line (where efficient weak recovery
    is known), so the hypothesis of the Statement is a proper restriction. -/
theorem above_KS_example : ¬ (((20 : ℝ) - 1) ^ 2 < 4 * (20 + 3 * 1)) := by
  norm_num

/-- For `q = 4` the hypothesis `(a-b)² < 4(a+3b)` is the Kesten–Stigum condition
    `SNR = (a-b)²/(q(a+(q-1)b)) < 1` with `q = 4`. -/
theorem hypothesis_iff_snr_lt_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 < 4 * (a + 3 * b) ↔
      (a - b) ^ 2 / ((4 : ℕ) * (a + ((4 - 1 : ℕ) : ℝ) * b)) < 1 := by
  have hpos : (0 : ℝ) < (4 : ℕ) * (a + ((4 - 1 : ℕ) : ℝ) * b) := by
    norm_num; positivity
  rw [div_lt_one hpos]
  norm_num

end InfoTheory.Known.Certificates.SbmMultiCommunityThreshold
