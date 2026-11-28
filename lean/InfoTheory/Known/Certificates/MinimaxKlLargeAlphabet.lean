import InfoTheory.Problems.MinimaxKlLargeAlphabet
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.MinimaxKlLargeAlphabet`

The frozen statement asks whether the minimax KL risk restricted to the two-parameter
Braess–Sauer add-constant family, `braessSauerKLRisk k n`, matches the unrestricted minimax KL
risk `minimaxKLRisk k n` (Core; an `sInf` over full-support estimators) up to `o(1)` in the
proportional regime `k = max 2 ⌊α n⌋`.

Certified here, about the exact objects of `Statement` (no junk values), for every `k ≥ 1`:
* `minimaxSet_bddBelow`, `minimaxKLRisk_nonneg` — the minimax `sInf` is over a set bounded
  below by `0` (KL against a full-support estimator is a genuine nonnegative number);
* `laplaceEst`, `laplaceEst_isBraessSauer` — the add-one (Laplace) estimator is the member
  `β₀ = β₁ = 1` of the Braess–Sauer family, so the family is nonempty;
* `braessSauer_subset_minimax`, `minimaxKLRisk_le_braessSauerKLRisk` — the family consists of
  full-support estimators, so `minimaxKLRisk ≤ braessSauerKLRisk` (the inequality `Statement`
  asks to reverse up to `ε`);
* `braessSauerKLRisk_le_log2` — `braessSauerKLRisk k n ≤ log₂ (n + k)`, so both risks are
  finite reals in `[0, log₂ (n + k)]`;
* **regression (`n = 0`, no samples)**: `minimaxKLRisk_zero_samples`,
  `braessSauerKLRisk_zero_samples` — both risks equal `log₂ k`, the classical value
  `min_Q max_P D(P ‖ Q) = log₂ k` attained by the uniform estimator (which the Braess–Sauer
  family contains).

Not certified: the Braess–Sauer asymptotics `(k - 1)/(2n)` for fixed `k`, the Paninski /
Kamath–Orlitsky–Pichapati–Suresh asymptotics, or anything about the proportional regime (the
open question). These facts do not settle `Statement`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MinimaxKlLargeAlphabet

open InfoTheory InfoTheory.Problems.MinimaxKlLargeAlphabet

/-! ### Helpers -/

theorem log2_le_log2 {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx h) (Real.log_pos one_lt_two).le

theorem sum_iid_pmf {α : Type*} [Fintype α] (P : ProbDist α) (n : ℕ) :
    ∑ x : Fin n → α, ∏ i : Fin n, P.pmf (x i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => P.pmf a)]
  simp [P.sum_one]

/-- `D(P ‖ Q) ≤ log₂ c` whenever `Q ≥ 1/c` pointwise. -/
theorem kl_le_log2_of_lower {α : Type*} [Fintype α] (P Q : ProbDist α) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ a, 1 / c ≤ Q.pmf a) : klDivergence P Q ≤ log2 c := by
  unfold klDivergence
  calc (∑ a, if P.pmf a ≤ 0 then 0 else P.pmf a * log2 (P.pmf a / Q.pmf a))
      ≤ ∑ a, P.pmf a * log2 c := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        split_ifs with hp
        · rw [le_antisymm hp (P.nonneg a), zero_mul]
        · have hpos : 0 < P.pmf a := lt_of_not_ge hp
          have hq : 0 < Q.pmf a := lt_of_lt_of_le (by positivity) (hQ a)
          refine mul_le_mul_of_nonneg_left (log2_le_log2 (div_pos hpos hq) ?_) hpos.le
          rw [div_le_iff₀ hq]
          have h1 : P.pmf a ≤ 1 := InfoTheory.Bridge.pmf_le_one P a
          have h2 : 1 ≤ c * Q.pmf a := by
            have := mul_le_mul_of_nonneg_left (hQ a) hc.le
            rwa [mul_one_div_cancel hc.ne'] at this
          linarith
    _ = log2 c := by rw [← Finset.sum_mul, P.sum_one, one_mul]

theorem kl_of_indicator {α : Type*} [Fintype α] [DecidableEq α] (P Q : ProbDist α) (a₀ : α)
    (hP : ∀ a, P.pmf a = if a = a₀ then 1 else 0) :
    klDivergence P Q = log2 (1 / Q.pmf a₀) := by
  unfold klDivergence
  rw [Finset.sum_eq_single a₀]
  · simp [hP]
  · intro b _ hb; simp [hP, hb]
  · simp

/-- Point mass at `a`. -/
noncomputable def pointMass {α : Type*} [Fintype α] [DecidableEq α] (a : α) : ProbDist α where
  pmf := fun b => if b = a then 1 else 0
  nonneg := fun b => by split_ifs <;> norm_num
  sum_one := by simp

theorem sum_countOcc {k n : ℕ} (x : Fin n → Fin k) : ∑ a : Fin k, (countOcc x a : ℝ) = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := x) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin k))) (fun i _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  unfold countOcc
  exact_mod_cast h.symm

/-! ### The minimax set is bounded below -/

theorem risk_nonneg {k n : ℕ} (est : (Fin n → Fin k) → ProbDist (Fin k))
    (hfull : ∀ x a, 0 < (est x).pmf a) (P : ProbDist (Fin k)) :
    0 ≤ ∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x) := by
  refine Finset.sum_nonneg (fun x _ => mul_nonneg
    (Finset.prod_nonneg (fun i _ => P.nonneg _)) ?_)
  exact InfoTheory.Bridge.klDivergence_nonneg _ _ (fun a h => absurd h (hfull x a).ne')

theorem minimaxSet_bddBelow (k n : ℕ) (hk : 0 < k) :
    BddBelow { R : ℝ | ∃ (est : (Fin n → Fin k) → ProbDist (Fin k)),
      (∀ (x : Fin n → Fin k) (a : Fin k), 0 < (est x).pmf a) ∧
      ∀ P : ProbDist (Fin k),
        (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x)) ≤ R } := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  refine ⟨0, ?_⟩
  rintro R ⟨est, hfull, hR⟩
  exact le_trans (risk_nonneg est hfull ProbDist.uniform) (hR ProbDist.uniform)

theorem minimaxKLRisk_nonneg (k n : ℕ) (hk : 0 < k) : 0 ≤ minimaxKLRisk k n := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply Real.sInf_nonneg
  rintro R ⟨est, hfull, hR⟩
  exact le_trans (risk_nonneg est hfull ProbDist.uniform) (hR ProbDist.uniform)

/-! ### The Laplace (add-one) member of the Braess–Sauer family -/

/-- Braess–Sauer weight with `β₀ = β₁ = 1`. -/
noncomputable def laplaceWeight {k n : ℕ} (x : Fin n → Fin k) (a : Fin k) : ℝ :=
  if countOcc x a = 0 then 1 else (countOcc x a : ℝ) + 1

theorem laplaceWeight_eq {k n : ℕ} (x : Fin n → Fin k) (a : Fin k) :
    laplaceWeight x a = (countOcc x a : ℝ) + 1 := by
  unfold laplaceWeight; split_ifs with h
  · rw [h]; simp
  · rfl

theorem laplaceWeight_pos {k n : ℕ} (x : Fin n → Fin k) (a : Fin k) : 0 < laplaceWeight x a := by
  rw [laplaceWeight_eq]; positivity

theorem laplaceZ {k n : ℕ} (x : Fin n → Fin k) :
    ∑ a : Fin k, laplaceWeight x a = (n : ℝ) + k := by
  simp only [laplaceWeight_eq, Finset.sum_add_distrib, sum_countOcc, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The add-one (Laplace) estimator `(N_a + 1)/(n + k)`, written in Braess–Sauer form. -/
noncomputable def laplaceEst (k n : ℕ) (hk : 0 < k) : (Fin n → Fin k) → ProbDist (Fin k) :=
  fun x =>
    { pmf := fun a => laplaceWeight x a / ∑ b : Fin k, laplaceWeight x b
      nonneg := fun a => div_nonneg (laplaceWeight_pos x a).le
        (Finset.sum_nonneg (fun b _ => (laplaceWeight_pos x b).le))
      sum_one := by
        rw [← Finset.sum_div, div_self]
        haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
        exact (Finset.sum_pos (fun b _ => laplaceWeight_pos x b) Finset.univ_nonempty).ne' }

theorem laplaceEst_isBraessSauer (k n : ℕ) (hk : 0 < k) :
    IsBraessSauerEst 1 1 (laplaceEst k n hk) :=
  ⟨one_pos, one_pos, fun _ _ => rfl⟩

theorem laplaceEst_lower (k n : ℕ) (hk : 0 < k) (x : Fin n → Fin k) (a : Fin k) :
    1 / ((n : ℝ) + k) ≤ (laplaceEst k n hk x).pmf a := by
  show 1 / ((n : ℝ) + k) ≤ laplaceWeight x a / ∑ b : Fin k, laplaceWeight x b
  rw [laplaceZ]
  have hk' : (0 : ℝ) < (n : ℝ) + k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  apply div_le_div_of_nonneg_right _ hk'.le
  rw [laplaceWeight_eq]; linarith [(Nat.cast_nonneg (countOcc x a) : (0 : ℝ) ≤ _)]

theorem laplace_risk_le (k n : ℕ) (hk : 0 < k) (P : ProbDist (Fin k)) :
    (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (laplaceEst k n hk x)) ≤
      log2 ((n : ℝ) + k) := by
  have hk' : (0 : ℝ) < (n : ℝ) + k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  calc (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (laplaceEst k n hk x))
      ≤ ∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * log2 ((n : ℝ) + k) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
          (kl_le_log2_of_lower _ _ _ hk' (laplaceEst_lower k n hk x))
          (Finset.prod_nonneg (fun i _ => P.nonneg _)))
    _ = log2 ((n : ℝ) + k) := by rw [← Finset.sum_mul, sum_iid_pmf, one_mul]

/-! ### Comparison of the two risks -/

theorem braessSauer_subset_minimax (k n : ℕ) (hk : 0 < k) :
    { R : ℝ | ∃ (β₀ β₁ : ℝ) (est : (Fin n → Fin k) → ProbDist (Fin k)),
      IsBraessSauerEst β₀ β₁ est ∧
      ∀ (P : ProbDist (Fin k)),
        (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x)) ≤ R } ⊆
    { R : ℝ | ∃ (est : (Fin n → Fin k) → ProbDist (Fin k)),
      (∀ (x : Fin n → Fin k) (a : Fin k), 0 < (est x).pmf a) ∧
      ∀ P : ProbDist (Fin k),
        (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x)) ≤ R } := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rintro R ⟨β₀, β₁, est, ⟨h0, h1, hest⟩, hR⟩
  refine ⟨est, fun x a => ?_, hR⟩
  have hw : ∀ b : Fin k,
      0 < (if countOcc x b = 0 then β₀ else (countOcc x b : ℝ) + β₁) := by
    intro b; split_ifs
    · exact h0
    · positivity
  rw [hest x a]
  exact div_pos (hw a) (Finset.sum_pos (fun b _ => hw b) Finset.univ_nonempty)

theorem braessSauerSet_nonempty (k n : ℕ) (hk : 0 < k) :
    (log2 ((n : ℝ) + k)) ∈ { R : ℝ | ∃ (β₀ β₁ : ℝ) (est : (Fin n → Fin k) → ProbDist (Fin k)),
      IsBraessSauerEst β₀ β₁ est ∧
      ∀ (P : ProbDist (Fin k)),
        (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x)) ≤ R } :=
  ⟨1, 1, laplaceEst k n hk, laplaceEst_isBraessSauer k n hk, laplace_risk_le k n hk⟩

theorem minimaxKLRisk_le_braessSauerKLRisk (k n : ℕ) (hk : 0 < k) :
    minimaxKLRisk k n ≤ braessSauerKLRisk k n :=
  csInf_le_csInf (minimaxSet_bddBelow k n hk) ⟨_, braessSauerSet_nonempty k n hk⟩
    (braessSauer_subset_minimax k n hk)

theorem braessSauerKLRisk_le_log2 (k n : ℕ) (hk : 0 < k) :
    braessSauerKLRisk k n ≤ log2 ((n : ℝ) + k) :=
  csInf_le ((minimaxSet_bddBelow k n hk).mono (braessSauer_subset_minimax k n hk))
    (braessSauerSet_nonempty k n hk)

theorem braessSauerKLRisk_nonneg (k n : ℕ) (hk : 0 < k) : 0 ≤ braessSauerKLRisk k n :=
  le_trans (minimaxKLRisk_nonneg k n hk) (minimaxKLRisk_le_braessSauerKLRisk k n hk)

/-! ### Regression: no samples (`n = 0`), both risks equal `log₂ k` -/

theorem log2_k_le_minimaxKLRisk_zero (k : ℕ) (hk : 0 < k) : log2 (k : ℝ) ≤ minimaxKLRisk k 0 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply le_csInf ⟨_, braessSauer_subset_minimax k 0 hk (braessSauerSet_nonempty k 0 hk)⟩
  rintro R ⟨est, hfull, hR⟩
  set Qe := est default
  -- some symbol has estimated mass at most `1/k`
  obtain ⟨a, ha⟩ : ∃ a : Fin k, Qe.pmf a ≤ 1 / k := by
    by_contra h
    push_neg at h
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ => h a)
    rw [Qe.sum_one] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [mul_one_div_cancel hk'.ne'] at this
    exact lt_irrefl _ this
  have hpos : 0 < Qe.pmf a := hfull default a
  have hRP := hR (pointMass a)
  simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul] at hRP
  rw [kl_of_indicator _ _ a (fun _ => rfl)] at hRP
  refine le_trans (log2_le_log2 hk' ?_) hRP
  rw [le_div_iff₀ hpos]
  rw [le_div_iff₀ hk'] at ha
  linarith

theorem minimaxKLRisk_zero_samples (k : ℕ) (hk : 0 < k) : minimaxKLRisk k 0 = log2 (k : ℝ) := by
  apply le_antisymm _ (log2_k_le_minimaxKLRisk_zero k hk)
  have := le_trans (minimaxKLRisk_le_braessSauerKLRisk k 0 hk) (braessSauerKLRisk_le_log2 k 0 hk)
  simpa using this

theorem braessSauerKLRisk_zero_samples (k : ℕ) (hk : 0 < k) :
    braessSauerKLRisk k 0 = log2 (k : ℝ) := by
  apply le_antisymm
  · simpa using braessSauerKLRisk_le_log2 k 0 hk
  · rw [← minimaxKLRisk_zero_samples k hk]
    exact minimaxKLRisk_le_braessSauerKLRisk k 0 hk

end InfoTheory.Known.Certificates.MinimaxKlLargeAlphabet
