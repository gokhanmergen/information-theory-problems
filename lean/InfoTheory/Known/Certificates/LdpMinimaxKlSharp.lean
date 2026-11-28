import InfoTheory.Problems.LdpMinimaxKlSharp
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.LdpMinimaxKlSharp`

The frozen statement asks whether Subset Selection (SS) mechanisms are exactly
(`1 + o(1)`) minimax-optimal for `ε`-LDP distribution estimation under KL loss, for every
`k ≥ 2`, `ε > 0`. Facts about the *exact* objects `ldpMinimaxKLRisk`,
`subsetSelectionMinimaxKLRisk`, `IsSubsetSelection`:

## Certified
* `kRR_isSubsetSelection`: `k`-ary randomized response is a Subset Selection channel
  (`s = 1`, `S y = {y}`), so the SS family is non-empty for every `k ≥ 2`.
* `isSubsetSelection_isEpsLDP`: every SS channel is `ε`-LDP (`ε ≥ 0`).
* `ldpMinimaxKLRisk_le_subsetSelection`: the SS risk is never below the full LDP risk, so the
  Statement is exactly the (asymptotic) reverse inequality.
* `ldpMinimaxKLRisk_nonneg`, `subsetSelectionMinimaxKLRisk_nonneg`,
  `ldpMinimaxKLRisk_le_log2`, `subsetSelectionMinimaxKLRisk_le_log2`: both infima are taken
  over non-empty sets bounded below, and lie in `[0, log₂ k]` (uniform estimator) — no `sInf ∅`
  or negative-KL junk.

## Not certified
* The `k = 2` case of the Statement, which is a known theorem: binary randomized response
  Blackwell-dominates every binary-input `ε`-LDP channel (Kairouz–Oh–Viswanath 2016), and KL
  risk is convex in the estimate, so SS is exactly optimal at `k = 2`.
* The `Θ(n^{-1/2})` rate of the LDP KL risk (boundary effect) and any exact constant.
-/

open scoped BigOperators
namespace InfoTheory.Known.Certificates.LdpMinimaxKlSharp
open InfoTheory InfoTheory.Problems.LdpMinimaxKlSharp

/-- The constant `c = 1 / (e^ε + k - 1)` of `k`-ary randomized response. -/
noncomputable def rrConst (k : ℕ) (ε : ℝ) : ℝ := 1 / (Real.exp ε + ((k : ℝ) - 1))

lemma rrConst_pos {k : ℕ} (hk : 1 ≤ k) (ε : ℝ) : 0 < rrConst k ε := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold rrConst; have := Real.exp_pos ε; apply div_pos one_pos; linarith

/-- `k`-ary randomized response (Warner 1965), written as a Subset Selection channel with
    singleton subsets `S y = {y}`. -/
noncomputable def kRR (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) : DMC (Fin k) (Fin k) where
  trans x y := if x ∈ ({y} : Finset (Fin k)) then rrConst k ε * Real.exp ε else rrConst k ε
  nonneg x y := by
    have := rrConst_pos hk ε; have := Real.exp_pos ε
    split_ifs <;> positivity
  sum_one x := by
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : Real.exp ε + ((k : ℝ) - 1) ≠ 0 := by have := Real.exp_pos ε; linarith
    have h : ∀ y : Fin k, (if x ∈ ({y} : Finset (Fin k)) then rrConst k ε * Real.exp ε
        else rrConst k ε) = rrConst k ε + (if x = y then rrConst k ε * (Real.exp ε - 1) else 0) := by
      intro y; by_cases hxy : x = y <;> simp [hxy, Finset.mem_singleton]; ring
    rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    unfold rrConst; field_simp; ring

theorem kRR_isSubsetSelection {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) :
    IsSubsetSelection k k 1 ε (kRR k (by omega) ε) :=
  ⟨le_rfl, by omega, fun y => {y}, rrConst k ε, rrConst_pos (by omega) ε,
    fun y => Finset.card_singleton y, fun x y => rfl⟩

/-- Every Subset Selection channel with `ε ≥ 0` is `ε`-LDP. -/
theorem isSubsetSelection_isEpsLDP {k m s : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {Q : DMC (Fin k) (Fin m)}
    (hQ : IsSubsetSelection k m s ε Q) : IsEpsLDP ε Q := by
  obtain ⟨-, -, S, c, hc, -, htr⟩ := hQ
  intro x x' y
  have he : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hce : 0 < c * Real.exp ε := mul_pos hc (Real.exp_pos ε)
  have h1 : c * Real.exp ε ≤ Real.exp ε * (c * Real.exp ε) := by
    have := mul_le_mul_of_nonneg_right he hce.le; linarith
  have h2 : c ≤ c * Real.exp ε := by
    have := mul_le_mul_of_nonneg_left he hc.le; linarith
  rw [htr x y, htr x' y]
  split_ifs
  · exact h1
  · linarith
  · linarith
  · linarith

/-- The set whose infimum is `ldpMinimaxKLRisk`. -/
def ldpSet (k n : ℕ) (ε : ℝ) : Set ℝ :=
  { R : ℝ | ∃ (m : ℕ) (Q : DMC (Fin k) (Fin m))
    (est : (Fin n → Fin m) → ProbDist (Fin k)),
    IsEpsLDP ε Q ∧
    (∀ (y : Fin n → Fin m) (a : Fin k), 0 < (est y).pmf a) ∧
    ∀ P : ProbDist (Fin k),
      let Py := (Q.joint P).snd
      (∑ y : Fin n → Fin m, (∏ i : Fin n, Py.pmf (y i)) * klDivergence P (est y)) ≤ R }

/-- The set whose infimum is `subsetSelectionMinimaxKLRisk`. -/
def ssSet (k n : ℕ) (ε : ℝ) : Set ℝ :=
  { R : ℝ | ∃ (m s : ℕ) (Q : DMC (Fin k) (Fin m))
    (est : (Fin n → Fin m) → ProbDist (Fin k)),
    IsSubsetSelection k m s ε Q ∧
    (∀ (y : Fin n → Fin m) (a : Fin k), 0 < (est y).pmf a) ∧
    ∀ (P : ProbDist (Fin k)),
      let Py := (Q.joint P).snd
      (∑ y : Fin n → Fin m, (∏ i : Fin n, Py.pmf (y i)) * klDivergence P (est y)) ≤ R }

lemma ldpMinimaxKLRisk_eq (k n : ℕ) (ε : ℝ) : ldpMinimaxKLRisk k n ε = sInf (ldpSet k n ε) := rfl
lemma ssRisk_eq (k n : ℕ) (ε : ℝ) :
    subsetSelectionMinimaxKLRisk k n ε = sInf (ssSet k n ε) := rfl

lemma risk_term_nonneg {k m n : ℕ} (Py : ProbDist (Fin m)) (P : ProbDist (Fin k))
    (est : (Fin n → Fin m) → ProbDist (Fin k)) (hest : ∀ y a, 0 < (est y).pmf a) :
    0 ≤ ∑ y : Fin n → Fin m, (∏ i : Fin n, Py.pmf (y i)) * klDivergence P (est y) := by
  refine Finset.sum_nonneg (fun y _ => mul_nonneg
    (Finset.prod_nonneg (fun i _ => Py.nonneg _)) ?_)
  exact Bridge.klDivergence_nonneg P (est y) (fun a h => absurd h (hest y a).ne')

lemma ldpSet_bddBelow {k n : ℕ} (hk : 1 ≤ k) (ε : ℝ) : BddBelow (ldpSet k n ε) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  refine ⟨0, fun R hR => ?_⟩
  obtain ⟨m, Q, est, -, hest, hR⟩ := hR
  exact le_trans (risk_term_nonneg _ ProbDist.uniform est hest) (hR ProbDist.uniform)

lemma ssSet_subset {k n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : ssSet k n ε ⊆ ldpSet k n ε := by
  rintro R ⟨m, s, Q, est, hQ, hest, hR⟩
  exact ⟨m, Q, est, isSubsetSelection_isEpsLDP hε hQ, hest, hR⟩

/-- Product of marginals sums to one. -/
lemma sum_prod_pmf {m n : ℕ} (Py : ProbDist (Fin m)) :
    ∑ y : Fin n → Fin m, ∏ i : Fin n, Py.pmf (y i) = 1 := by
  rw [← Fintype.prod_sum (fun _ b => Py.pmf b)]
  simp [Py.sum_one]

/-- Randomized response with the constant uniform estimator has worst-case KL risk at most
    `log₂ k`, so `log₂ k ∈ ssSet`. -/
theorem log2_mem_ssSet {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (ε : ℝ) :
    log2 (k : ℝ) ∈ ssSet k n ε := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  refine ⟨k, 1, kRR k (by omega) ε, fun _ => ProbDist.uniform, kRR_isSubsetSelection hk ε,
    fun _ _ => ?_, fun P => ?_⟩
  · simp only [ProbDist.uniform, Fintype.card_fin]
    have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  · simp only
    rw [← Finset.sum_mul, sum_prod_pmf, one_mul, Bridge.klDivergence_uniform, Fintype.card_fin]
    linarith [Bridge.shannonEntropy_nonneg P]

theorem ssSet_nonempty {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (ε : ℝ) : (ssSet k n ε).Nonempty :=
  ⟨_, log2_mem_ssSet hk n ε⟩

/-- **Subset Selection is a sub-family of the `ε`-LDP mechanisms**: its minimax KL risk is
    never below the full LDP minimax risk (so the Statement is the reverse inequality up to
    `1 + δ`). -/
theorem ldpMinimaxKLRisk_le_subsetSelection {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) : ldpMinimaxKLRisk k n ε ≤ subsetSelectionMinimaxKLRisk k n ε :=
  csInf_le_csInf (ldpSet_bddBelow (by omega) ε) (ssSet_nonempty hk n ε) (ssSet_subset hε)

/-- Both risks are non-negative (no negative junk: estimators have full support). -/
theorem ldpMinimaxKLRisk_nonneg {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ ldpMinimaxKLRisk k n ε := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  refine le_csInf ⟨_, ssSet_subset hε (log2_mem_ssSet hk n ε)⟩ (fun R hR => ?_)
  obtain ⟨m, Q, est, -, hest, hR⟩ := hR
  exact le_trans (risk_term_nonneg _ ProbDist.uniform est hest) (hR ProbDist.uniform)

theorem subsetSelectionMinimaxKLRisk_nonneg {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) : 0 ≤ subsetSelectionMinimaxKLRisk k n ε :=
  le_trans (ldpMinimaxKLRisk_nonneg hk n hε) (ldpMinimaxKLRisk_le_subsetSelection hk n hε)

/-- Both risks are at most `log₂ k` (the uniform estimator): finite, non-junk values. -/
theorem subsetSelectionMinimaxKLRisk_le_log2 {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) : subsetSelectionMinimaxKLRisk k n ε ≤ log2 (k : ℝ) :=
  csInf_le ((ldpSet_bddBelow (by omega) ε).mono (ssSet_subset hε)) (log2_mem_ssSet hk n ε)

theorem ldpMinimaxKLRisk_le_log2 {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ldpMinimaxKLRisk k n ε ≤ log2 (k : ℝ) :=
  le_trans (ldpMinimaxKLRisk_le_subsetSelection hk n hε)
    (subsetSelectionMinimaxKLRisk_le_log2 hk n hε)

end InfoTheory.Known.Certificates.LdpMinimaxKlSharp
