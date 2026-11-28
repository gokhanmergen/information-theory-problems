import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.MethodOfTypes
import InfoTheory.Bridge.FeketeAndCopyLemma
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Sharp Entropy Continuity (Fannes–Audenaert / Zhang / Winter) and Shearer–Han Inequalities

Purely additive, kernel-verified foundational theorems of classical information theory built
directly on top of `InfoTheory.Bridge.CoverThomas`, `InfoTheory.Bridge.MethodOfTypes`, and
`InfoTheory.Bridge.FeketeAndCopyLemma`:

1. **Total Variation Distance & Maximal Coupling**:
   - `tvDistance_nonneg`, `tvDistance_le_one`, `tvDistance_comm`, `tvDistance_self`,
     `tvDistance_eq_zero_iff`, `tvDistance_eq_sum_pos`, `tvDistance_eq_sum_neg`,
     `tvDistance_eq_one_sub_sum_min`, `tvDistance_map_le`, `tvDistance_fst_le`, `tvDistance_snd_le`.
   - `maxCoupling P Q : ProbDist (α × α)`: explicit maximal coupling with marginals
     `maxCoupling_fst`, `maxCoupling_snd`, diagonal `maxCoupling_diag`, error probability
     `maxCoupling_estErrorProb` (`Pr[X ≠ Y] = TV(P, Q)`), and optimality
     `tvDistance_le_coupling_error`.
2. **Sharp Fannes–Audenaert / Zhang Continuity of Shannon Entropy**
   (Zhang 2007; Audenaert 2007; strictly sharper than Cover & Thomas, Theorem 17.3.3):
   - `shannonEntropy_continuity_audenaert`: for `2 ≤ |α|`,
     `|H(P) - H(Q)| ≤ TV(P, Q) · log₂(|α| - 1) + h(TV(P, Q))`.
   - `shannonEntropy_eq_zero_of_card_le_one`, `shannonEntropy_continuity_sharp`:
     unified bound for all finite `α` using `log₂(max 1 (|α| - 1))`.
3. **Concavity, Almost-Convexity, and Winter (2016) Tight Continuity of `H(X | Y)` and `I(X; Y)`**:
   - `shannonEntropy_almost_convex`, `condEntropy_concave`, `condEntropy_almost_convex`.
   - `condEntropy_continuity`: alphabet-independent-in-`β` bound
     `|H(X | Y)_P - H(X | Y)_Q| ≤ T · log₂|α| + (1 + T) · h(T / (1 + T))` where `T = TV(P, Q)`.
   - `mutualInfo_continuity`, `mutualInfo_continuity_min`:
     `|I(X; Y)_P - I(X; Y)_Q| ≤ 2 T · log₂(min(|α|, |β|)) + 2 (1 + T) · h(T / (1 + T))`.
4. **Shearer's Lemma, Han's Inequality, and Arbitrary-Alphabet Zhang–Yeung**
   (Chung–Graham–Frankl–Shearer 1986; Cover & Thomas, Theorem 17.6.1):
   - `subsetEntropy` on arbitrary dependent finite products `ProbDist (∀ i : Fin n, α i)`
     (definitionally agreeing with `subsetEntropyVec` on `Fin n → Fin k`), with
     `subsetEntropy_univ` and `subsetEntropy_isPolymatroid`.
   - `polymatroid_shearer_weighted`, `polymatroid_shearer` (fractional & integer Shearer for any
     polymatroid `h ∈ Γ_n`).
   - `shearer_inequality_weighted`, `shearer_inequality`, `shearer_inequality_multiset`.
   - `han_inequality_leave_one_out`, `han_inequality`, `han_inequality_avg`,
     `han_average_antitone_step` (full monotonicity chain `h_n ≤ h_{n-1} ≤ ⋯ ≤ h_1`).
   - `shannonEntropy_map_injective` and `zhang_yeung_subsetEntropy` (lifting
     `zhang_yeung_subsetEntropyVec` to arbitrary finite alphabets).

All theorems leave `Core/`, `Problems/`, `STATEMENT_LOCK.json`, `Known/`, and all other
`Bridge/` files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Total Variation Distance & Maximal Coupling -/

section TVAndCoupling

variable {α β : Type*} [Fintype α] [Fintype β]

/-- `InfoTheory.log2` coincides with Mathlib's `Real.logb 2`. -/
lemma log2_eq_logb (x : ℝ) : log2 x = Real.logb 2 x := rfl

private lemma probDist_ext' {ι : Type*} [Fintype ι] {P Q : ProbDist ι}
    (h : ∀ x, P.pmf x = Q.pmf x) : P = Q := by
  cases P; cases Q; congr; funext x; exact h x

private lemma nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have h := P.sum_one
  simp at h

/-- Total variation distance is nonnegative: `0 ≤ TV(P, Q)`. -/
theorem tvDistance_nonneg (P Q : ProbDist α) : 0 ≤ tvDistance P Q := by
  unfold tvDistance
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => abs_nonneg _)

/-- Total variation distance is at most `1`: `TV(P, Q) ≤ 1`. -/
theorem tvDistance_le_one (P Q : ProbDist α) : tvDistance P Q ≤ 1 := by
  unfold tvDistance
  have hsum : ∑ a : α, |P.pmf a - Q.pmf a| ≤ 2 := by
    calc ∑ a : α, |P.pmf a - Q.pmf a|
      _ ≤ ∑ a : α, (P.pmf a + Q.pmf a) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_le]
          constructor <;> linarith [P.nonneg a, Q.nonneg a]
      _ = (∑ a : α, P.pmf a) + ∑ a : α, Q.pmf a := Finset.sum_add_distrib
      _ = 1 + 1 := by rw [P.sum_one, Q.sum_one]
      _ = 2 := by norm_num
  linarith

/-- Symmetry of total variation distance: `TV(P, Q) = TV(Q, P)`. -/
theorem tvDistance_comm (P Q : ProbDist α) : tvDistance P Q = tvDistance Q P := by
  unfold tvDistance
  congr 1
  exact Finset.sum_congr rfl fun a _ => abs_sub_comm (P.pmf a) (Q.pmf a)

/-- Reflexivity of total variation distance: `TV(P, P) = 0`. -/
theorem tvDistance_self (P : ProbDist α) : tvDistance P P = 0 := by
  simp [tvDistance]

/-- Total variation distance vanishes iff the distributions are equal. -/
theorem tvDistance_eq_zero_iff (P Q : ProbDist α) : tvDistance P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    unfold tvDistance at h
    have hsum : ∑ a : α, |P.pmf a - Q.pmf a| = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => abs_nonneg _)).mp hsum
    refine probDist_ext' fun a => ?_
    have ha := abs_eq_zero.mp (hall a (Finset.mem_univ a))
    linarith
  · rintro rfl
    exact tvDistance_self P

/-- Positive-part representation of total variation distance:
    `TV(P, Q) = ∑ a, max (P(a) - Q(a)) 0`. -/
theorem tvDistance_eq_sum_pos (P Q : ProbDist α) :
    tvDistance P Q = ∑ a : α, max (P.pmf a - Q.pmf a) 0 := by
  have hdiff : ∑ a : α, (P.pmf a - Q.pmf a) = 0 := by
    rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one, sub_self]
  have hpoint : ∀ a : α, |P.pmf a - Q.pmf a| + (P.pmf a - Q.pmf a) =
      2 * max (P.pmf a - Q.pmf a) 0 := by
    intro a
    by_cases h : 0 ≤ P.pmf a - Q.pmf a
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · have hlt : P.pmf a - Q.pmf a < 0 := lt_of_not_ge h
      rw [abs_of_neg hlt, max_eq_right (le_of_lt hlt)]; ring
  have hsum : (∑ a : α, |P.pmf a - Q.pmf a|) + ∑ a : α, (P.pmf a - Q.pmf a) =
      2 * ∑ a : α, max (P.pmf a - Q.pmf a) 0 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => hpoint a
  rw [hdiff, add_zero] at hsum
  unfold tvDistance
  linarith

/-- Negative-part representation of total variation distance:
    `TV(P, Q) = ∑ a, max (Q(a) - P(a)) 0`. -/
theorem tvDistance_eq_sum_neg (P Q : ProbDist α) :
    tvDistance P Q = ∑ a : α, max (Q.pmf a - P.pmf a) 0 := by
  rw [tvDistance_comm, tvDistance_eq_sum_pos]

/-- Overlap representation of total variation distance:
    `TV(P, Q) = 1 - ∑ a, min (P(a)) (Q(a))`. -/
theorem tvDistance_eq_one_sub_sum_min (P Q : ProbDist α) :
    tvDistance P Q = 1 - ∑ a : α, min (P.pmf a) (Q.pmf a) := by
  rw [tvDistance_eq_sum_pos]
  have hpoint : ∀ a : α, min (P.pmf a) (Q.pmf a) + max (P.pmf a - Q.pmf a) 0 = P.pmf a := by
    intro a
    by_cases h : Q.pmf a ≤ P.pmf a
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    · have hlt : P.pmf a < Q.pmf a := lt_of_not_ge h
      rw [min_eq_left (le_of_lt hlt), max_eq_right (by linarith)]; ring
  have hsum : (∑ a : α, min (P.pmf a) (Q.pmf a)) + ∑ a : α, max (P.pmf a - Q.pmf a) 0 = 1 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hpoint]
    exact P.sum_one
  linarith

/-- **Data Processing Inequality for Total Variation Distance**:
    pushing forward by any deterministic map cannot increase total variation distance. -/
theorem tvDistance_map_le (f : α → β) (P Q : ProbDist α) :
    tvDistance (P.map f) (Q.map f) ≤ tvDistance P Q := by
  classical
  unfold tvDistance
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hpoint : ∀ b : β, |(P.map f).pmf b - (Q.map f).pmf b| ≤
      ∑ a : α, if f a = b then |P.pmf a - Q.pmf a| else 0 := by
    intro b
    unfold ProbDist.map
    dsimp only
    rw [← Finset.sum_sub_distrib]
    calc |∑ a : α, ((if f a = b then P.pmf a else 0) - (if f a = b then Q.pmf a else 0))|
      _ ≤ ∑ a : α, |(if f a = b then P.pmf a else 0) - (if f a = b then Q.pmf a else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : α, if f a = b then |P.pmf a - Q.pmf a| else 0 :=
          Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
  calc ∑ b : β, |(P.map f).pmf b - (Q.map f).pmf b|
    _ ≤ ∑ b : β, ∑ a : α, if f a = b then |P.pmf a - Q.pmf a| else 0 :=
        Finset.sum_le_sum fun b _ => hpoint b
    _ = ∑ a : α, ∑ b : β, if f a = b then |P.pmf a - Q.pmf a| else 0 := Finset.sum_comm
    _ = ∑ a : α, |P.pmf a - Q.pmf a| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single (f a)]
        · simp
        · intro b _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h

private lemma fst_eq_map_fst' (P : ProbDist (α × β)) : P.fst = P.map Prod.fst := by
  classical
  refine probDist_ext' fun a => ?_
  unfold ProbDist.fst ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type]
  trans (∑ a' : α, if a' = a then ∑ b : β, P.pmf (a, b) else 0)
  · simp
  · refine Finset.sum_congr rfl fun a' _ => ?_
    by_cases h : a' = a
    · subst h; simp
    · simp [h]

private lemma snd_eq_map_snd' (P : ProbDist (α × β)) : P.snd = P.map Prod.snd := by
  classical
  refine probDist_ext' fun b => ?_
  unfold ProbDist.snd ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type_right]
  trans (∑ b' : β, if b' = b then ∑ a : α, P.pmf (a, b) else 0)
  · simp
  · refine Finset.sum_congr rfl fun b' _ => ?_
    by_cases h : b' = b
    · subst h; simp
    · simp [h]

/-- Taking the first marginal cannot increase total variation distance. -/
theorem tvDistance_fst_le (P Q : ProbDist (α × β)) :
    tvDistance P.fst Q.fst ≤ tvDistance P Q := by
  rw [fst_eq_map_fst' P, fst_eq_map_fst' Q]
  exact tvDistance_map_le Prod.fst P Q

/-- Taking the second marginal cannot increase total variation distance. -/
theorem tvDistance_snd_le (P Q : ProbDist (α × β)) :
    tvDistance P.snd Q.snd ≤ tvDistance P Q := by
  rw [snd_eq_map_snd' P, snd_eq_map_snd' Q]
  exact tvDistance_map_le Prod.snd P Q

/-- **Explicit Maximal Coupling** of two finite distributions `P, Q : ProbDist α`.
    Places mass `min(P(x), Q(x))` on the diagonal `(x, x)` and distributes the remaining
    total variation mass `T = TV(P, Q)` independently as
    `max(P(x) - Q(x), 0) · max(Q(y) - P(y), 0) / T` (which vanishes automatically when `T = 0`). -/
noncomputable def maxCoupling (P Q : ProbDist α) : ProbDist (α × α) := by
  classical
  exact
    { pmf := fun xy =>
        (if xy.1 = xy.2 then min (P.pmf xy.1) (Q.pmf xy.1) else 0) +
          max (P.pmf xy.1 - Q.pmf xy.1) 0 * max (Q.pmf xy.2 - P.pmf xy.2) 0 / tvDistance P Q
      nonneg := fun xy => by
        refine add_nonneg ?_ ?_
        · split_ifs
          · exact le_min (P.nonneg xy.1) (Q.nonneg xy.1)
          · exact le_rfl
        · exact div_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _))
            (tvDistance_nonneg P Q)
      sum_one := by
        rw [Fintype.sum_prod_type]
        have hrow : ∀ x : α,
            ∑ y : α, ((if x = y then min (P.pmf x) (Q.pmf x) else 0) +
              max (P.pmf x - Q.pmf x) 0 * max (Q.pmf y - P.pmf y) 0 / tvDistance P Q) =
            P.pmf x := by
          intro x
          rw [Finset.sum_add_distrib]
          have hdiag : (∑ y : α, if x = y then min (P.pmf x) (Q.pmf x) else 0) =
              min (P.pmf x) (Q.pmf x) := by
            rw [Finset.sum_eq_single x]
            · simp
            · intro y _ hne; simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hdiag, ← Finset.sum_div, ← Finset.mul_sum, ← tvDistance_eq_sum_neg P Q]
          by_cases hT : tvDistance P Q = 0
          · have hPQ : P = Q := (tvDistance_eq_zero_iff P Q).mp hT
            subst hPQ
            simp [hT]
          · rw [mul_div_cancel_right₀ _ hT]
            by_cases h : Q.pmf x ≤ P.pmf x
            · rw [min_eq_right h, max_eq_left (by linarith)]; ring
            · have hlt : P.pmf x < Q.pmf x := lt_of_not_ge h
              rw [min_eq_left (le_of_lt hlt), max_eq_right (by linarith)]; ring
        simp_rw [hrow]
        exact P.sum_one }

/-- First marginal of the maximal coupling is `P`. -/
theorem maxCoupling_fst (P Q : ProbDist α) : (maxCoupling P Q).fst = P := by
  classical
  refine probDist_ext' fun x => ?_
  change ∑ y : α, ((if x = y then min (P.pmf x) (Q.pmf x) else 0) +
    max (P.pmf x - Q.pmf x) 0 * max (Q.pmf y - P.pmf y) 0 / tvDistance P Q) = P.pmf x
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ y : α, if x = y then min (P.pmf x) (Q.pmf x) else 0) =
      min (P.pmf x) (Q.pmf x) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdiag, ← Finset.sum_div, ← Finset.mul_sum, ← tvDistance_eq_sum_neg P Q]
  by_cases hT : tvDistance P Q = 0
  · have hPQ : P = Q := (tvDistance_eq_zero_iff P Q).mp hT
    subst hPQ
    simp [hT]
  · rw [mul_div_cancel_right₀ _ hT]
    by_cases h : Q.pmf x ≤ P.pmf x
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    · have hlt : P.pmf x < Q.pmf x := lt_of_not_ge h
      rw [min_eq_left (le_of_lt hlt), max_eq_right (by linarith)]; ring

/-- Second marginal of the maximal coupling is `Q`. -/
theorem maxCoupling_snd (P Q : ProbDist α) : (maxCoupling P Q).snd = Q := by
  classical
  refine probDist_ext' fun y => ?_
  change ∑ x : α, ((if x = y then min (P.pmf x) (Q.pmf x) else 0) +
    max (P.pmf x - Q.pmf x) 0 * max (Q.pmf y - P.pmf y) 0 / tvDistance P Q) = Q.pmf y
  rw [Finset.sum_add_distrib]
  have hdiag : (∑ x : α, if x = y then min (P.pmf x) (Q.pmf x) else 0) =
      min (P.pmf y) (Q.pmf y) := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdiag, ← Finset.sum_div, ← Finset.sum_mul, ← tvDistance_eq_sum_pos P Q]
  by_cases hT : tvDistance P Q = 0
  · have hPQ : P = Q := (tvDistance_eq_zero_iff P Q).mp hT
    subst hPQ
    simp [hT]
  · rw [mul_div_cancel_left₀ _ hT]
    by_cases h : P.pmf y ≤ Q.pmf y
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · have hlt : Q.pmf y < P.pmf y := lt_of_not_ge h
      rw [min_eq_right (le_of_lt hlt), max_eq_right (by linarith)]; ring

/-- On the diagonal `(a, a)`, the maximal coupling assigns mass `min(P(a), Q(a))`. -/
theorem maxCoupling_diag (P Q : ProbDist α) (a : α) :
    (maxCoupling P Q).pmf (a, a) = min (P.pmf a) (Q.pmf a) := by
  classical
  change (if a = a then min (P.pmf a) (Q.pmf a) else 0) +
    max (P.pmf a - Q.pmf a) 0 * max (Q.pmf a - P.pmf a) 0 / tvDistance P Q =
    min (P.pmf a) (Q.pmf a)
  simp only [↓reduceIte]
  have hzero : max (P.pmf a - Q.pmf a) 0 * max (Q.pmf a - P.pmf a) 0 = 0 := by
    by_cases h : P.pmf a ≤ Q.pmf a
    · rw [max_eq_right (by linarith : P.pmf a - Q.pmf a ≤ 0), zero_mul]
    · rw [max_eq_right (by linarith : Q.pmf a - P.pmf a ≤ 0), mul_zero]
  rw [hzero, zero_div, add_zero]

/-- The maximal coupling achieves disagreement probability `Pr[X ≠ Y] = TV(P, Q)`. -/
theorem maxCoupling_estErrorProb (P Q : ProbDist α) :
    estErrorProb (maxCoupling P Q) id = tvDistance P Q := by
  have h1 := one_sub_estErrorProb (maxCoupling P Q) id
  simp only [id_eq, maxCoupling_diag] at h1
  rw [tvDistance_eq_one_sub_sum_min]
  linarith

/-- **Coupling Lower Bound for Total Variation Distance**:
    every coupling `R` of `P` and `Q` satisfies `TV(P, Q) ≤ Pr_R[X ≠ Y]`. -/
theorem tvDistance_le_coupling_error (R : ProbDist (α × α)) (P Q : ProbDist α)
    (hfst : R.fst = P) (hsnd : R.snd = Q) :
    tvDistance P Q ≤ estErrorProb R id := by
  have h1 := one_sub_estErrorProb R id
  simp only [id_eq] at h1
  have hmin : ∀ a : α, R.pmf (a, a) ≤ min (P.pmf a) (Q.pmf a) := by
    intro a
    refine le_min ?_ ?_
    · rw [← hfst]
      exact Finset.single_le_sum (fun b _ => R.nonneg (a, b)) (Finset.mem_univ a)
    · rw [← hsnd]
      exact Finset.single_le_sum (fun b _ => R.nonneg (b, a)) (Finset.mem_univ a)
  have hsum : ∑ a : α, R.pmf (a, a) ≤ ∑ a : α, min (P.pmf a) (Q.pmf a) :=
    Finset.sum_le_sum fun a _ => hmin a
  rw [tvDistance_eq_one_sub_sum_min]
  linarith

end TVAndCoupling

/-! ### 2. Sharp Fannes–Audenaert / Zhang Continuity of Shannon Entropy -/

section AudenaertContinuity

variable {α : Type*} [Fintype α]

/-- Any distribution on an alphabet of size `≤ 1` has zero Shannon entropy. -/
theorem shannonEntropy_eq_zero_of_card_le_one (P : ProbDist α) (hcard : Fintype.card α ≤ 1) :
    shannonEntropy P = 0 := by
  have hne : Nonempty α := nonempty_of_probDist P
  have h1 : Fintype.card α = 1 := le_antisymm hcard Fintype.card_pos
  have hle := shannonEntropy_le_log2_card P
  have hge := shannonEntropy_nonneg P
  rw [h1] at hle
  simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
  exact le_antisymm hle hge

private lemma shannonEntropy_sub_le_audenaert (P Q : ProbDist α) (hcard : 2 ≤ Fintype.card α) :
    shannonEntropy P - shannonEntropy Q ≤
      tvDistance P Q * Real.logb 2 ((Fintype.card α : ℝ) - 1) +
        binaryEntropy (tvDistance P Q) := by
  let R := maxCoupling P Q
  have hfst : R.fst = P := maxCoupling_fst P Q
  have hsnd : R.snd = Q := maxCoupling_snd P Q
  have herr : estErrorProb R id = tvDistance P Q := maxCoupling_estErrorProb P Q
  have hle_joint : shannonEntropy P ≤ shannonEntropy R := by
    rw [← hfst, fst_eq_map_fst']
    exact shannonEntropy_map_le Prod.fst R
  have hfano := fano_inequality R id hcard
  rw [herr, log2_eq_logb] at hfano
  unfold condEntropy at hfano
  rw [hsnd] at hfano
  linarith

/-- **Sharp Fannes–Audenaert / Zhang Continuity of Shannon Entropy**
    (Zhang 2007; Audenaert 2007; strictly sharper than Cover & Thomas, Theorem 17.3.3):
    for any two distributions `P, Q` on a finite alphabet `α` with `2 ≤ |α|`,
    `|H(P) - H(Q)| ≤ TV(P, Q) · log₂(|α| - 1) + h(TV(P, Q))`.

    Proved by applying Fano's inequality (`fano_inequality`) to the explicit maximal
    coupling `maxCoupling P Q`. -/
theorem shannonEntropy_continuity_audenaert (P Q : ProbDist α) (hcard : 2 ≤ Fintype.card α) :
    |shannonEntropy P - shannonEntropy Q| ≤
      tvDistance P Q * Real.logb 2 ((Fintype.card α : ℝ) - 1) +
        binaryEntropy (tvDistance P Q) := by
  rw [abs_le]
  constructor
  · have h := shannonEntropy_sub_le_audenaert Q P hcard
    rw [tvDistance_comm Q P] at h
    linarith
  · exact shannonEntropy_sub_le_audenaert P Q hcard

/-- **Unified Sharp Continuity of Shannon Entropy** for ALL finite alphabets `α`:
    `|H(P) - H(Q)| ≤ TV(P, Q) · log₂(max 1 (|α| - 1)) + h(TV(P, Q))`. -/
theorem shannonEntropy_continuity_sharp (P Q : ProbDist α) :
    |shannonEntropy P - shannonEntropy Q| ≤
      tvDistance P Q * Real.logb 2 (max 1 ((Fintype.card α : ℝ) - 1)) +
        binaryEntropy (tvDistance P Q) := by
  by_cases hcard : 2 ≤ Fintype.card α
  · have hmax : max (1 : ℝ) ((Fintype.card α : ℝ) - 1) = (Fintype.card α : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard
      exact max_eq_right (by linarith)
    rw [hmax]
    exact shannonEntropy_continuity_audenaert P Q hcard
  · have hle1 : Fintype.card α ≤ 1 := by omega
    rw [shannonEntropy_eq_zero_of_card_le_one P hle1,
      shannonEntropy_eq_zero_of_card_le_one Q hle1, sub_self, abs_zero]
    have hT0 : 0 ≤ tvDistance P Q := tvDistance_nonneg P Q
    have hT1 : tvDistance P Q ≤ 1 := tvDistance_le_one P Q
    have hbin : 0 ≤ binaryEntropy (tvDistance P Q) :=
      add_nonneg (negPLogP_nonneg hT1) (negPLogP_nonneg (by linarith))
    have hlog : 0 ≤ Real.logb 2 (max 1 ((Fintype.card α : ℝ) - 1)) := by
      rw [← log2_eq_logb]
      unfold log2
      exact div_nonneg (Real.log_nonneg (le_max_left _ _)) (le_of_lt (Real.log_pos (by norm_num)))
    exact add_nonneg (mul_nonneg hT0 hlog) hbin

end AudenaertContinuity

/-! ### 3. Concavity, Almost-Convexity & Winter Tight Continuity for `H(X | Y)` and `I(X; Y)` -/

section ConditionalAndMIContinuity

variable {α β : Type*} [Fintype α] [Fintype β]

private lemma binaryEntropy_symm' (p : ℝ) : binaryEntropy p = binaryEntropy (1 - p) := by
  unfold binaryEntropy
  rw [sub_sub_cancel, add_comm]

private lemma binaryEntropy_nonneg' {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryEntropy p :=
  add_nonneg (negPLogP_nonneg hp1) (negPLogP_nonneg (by linarith))

private lemma binaryEntropy_zero' : binaryEntropy 0 = 0 := by
  unfold binaryEntropy negPLogP log2
  simp

private lemma shannonEntropy_bernoulli' (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    shannonEntropy (ProbDist.bernoulli p hp0 hp1) = binaryEntropy p := by
  unfold shannonEntropy ProbDist.bernoulli binaryEntropy
  rw [Fintype.sum_bool]
  simp

/-- Scaling identity for `negPLogP` summed over a probability distribution:
    `∑ a, negPLogP (c * P(a)) = negPLogP c + c * H(P)` for `0 ≤ c`. -/
private lemma sum_negPLogP_mul {γ : Type*} [Fintype γ] {c : ℝ} (hc : 0 ≤ c) (P : ProbDist γ) :
    ∑ a : γ, negPLogP (c * P.pmf a) = negPLogP c + c * shannonEntropy P := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp [negPLogP]
  · have hterm : ∀ a : γ, negPLogP (c * P.pmf a) =
        P.pmf a * negPLogP c + c * negPLogP (P.pmf a) := by
      intro a
      by_cases hp : P.pmf a ≤ 0
      · have hp0 : P.pmf a = 0 := le_antisymm hp (P.nonneg a)
        simp [hp0, negPLogP]
      · have hppos : 0 < P.pmf a := lt_of_not_ge hp
        have hcp : ¬ (c * P.pmf a ≤ 0) := not_le.mpr (mul_pos hcpos hppos)
        have hcnot : ¬ (c ≤ 0) := not_le.mpr hcpos
        unfold negPLogP
        simp only [ite_eq_right_iff.mpr (fun h => absurd h hcp),
          ite_eq_right_iff.mpr (fun h => absurd h hcnot),
          ite_eq_right_iff.mpr (fun h => absurd h hp)]
        rw [log2_mul_pos hcpos hppos]
        ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, one_mul, ← Finset.mul_sum]
    rfl

/-- Flagged mixture distribution on `γ × Bool` coupling `P₁` (on `true`, weight `t`) and
    `P₂` (on `false`, weight `1 - t`). -/
private def probMixFlag {γ : Type*} [Fintype γ] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist γ) : ProbDist (γ × Bool) where
  pmf := fun xb => if xb.2 then t * P₁.pmf xb.1 else (1 - t) * P₂.pmf xb.1
  nonneg := fun xb => by
    split_ifs
    · exact mul_nonneg ht0 (P₁.nonneg xb.1)
    · exact mul_nonneg (by linarith) (P₂.nonneg xb.1)
  sum_one := by
    rw [Fintype.sum_prod_type_right, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true, ← Finset.mul_sum, P₁.sum_one, P₂.sum_one]
    ring

private lemma probMixFlag_fst {γ : Type*} [Fintype γ] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist γ) :
    (probMixFlag t ht0 ht1 P₁ P₂).fst = probMix t ht0 ht1 P₁ P₂ := by
  refine probDist_ext' fun x => ?_
  change ∑ b : Bool, (if b then t * P₁.pmf x else (1 - t) * P₂.pmf x) = _
  rw [Fintype.sum_bool]
  simp [probMix]

private lemma probMixFlag_snd {γ : Type*} [Fintype γ] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist γ) :
    (probMixFlag t ht0 ht1 P₁ P₂).snd = ProbDist.bernoulli t ht0 ht1 := by
  refine probDist_ext' fun b => ?_
  cases b <;>
    simp [ProbDist.snd, probMixFlag, ProbDist.bernoulli, ← Finset.mul_sum, P₁.sum_one, P₂.sum_one]

private lemma shannonEntropy_probMixFlag {γ : Type*} [Fintype γ] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist γ) :
    shannonEntropy (probMixFlag t ht0 ht1 P₁ P₂) =
      binaryEntropy t + t * shannonEntropy P₁ + (1 - t) * shannonEntropy P₂ := by
  change (∑ xb : γ × Bool, negPLogP ((probMixFlag t ht0 ht1 P₁ P₂).pmf xb)) = _
  rw [Fintype.sum_prod_type_right, Fintype.sum_bool]
  simp only [probMixFlag, ↓reduceIte, Bool.false_eq_true]
  rw [sum_negPLogP_mul ht0 P₁, sum_negPLogP_mul (by linarith : 0 ≤ 1 - t) P₂]
  unfold binaryEntropy
  ring

/-- **Almost-Convexity of Shannon Entropy**:
    for `t ∈ [0, 1]` and `P₁, P₂ : ProbDist α`,
    `H(t P₁ + (1 - t) P₂) ≤ t H(P₁) + (1 - t) H(P₂) + h(t)`. -/
theorem shannonEntropy_almost_convex (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist α) :
    shannonEntropy (probMix t ht0 ht1 P₁ P₂) ≤
      t * shannonEntropy P₁ + (1 - t) * shannonEntropy P₂ + binaryEntropy t := by
  let F := probMixFlag t ht0 ht1 P₁ P₂
  have hle : shannonEntropy F.fst ≤ shannonEntropy F := by
    rw [fst_eq_map_fst']
    exact shannonEntropy_map_le Prod.fst F
  rw [probMixFlag_fst, shannonEntropy_probMixFlag] at hle
  linarith

/-- Helper expressing the mixture gap of conditional entropy as a conditional mutual information
    `I(X; Z | Y)` on the flagged joint distribution `(X, Z, Y)`. -/
private lemma condEntropy_mix_gap_eq_cmi (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist (α × β)) :
    let F := probMixFlag t ht0 ht1 P₁ P₂
    let Q : ProbDist (α × Bool × β) := F.map (fun w => (w.1.1, w.2, w.1.2))
    condEntropy (probMix t ht0 ht1 P₁ P₂) - (t * condEntropy P₁ + (1 - t) * condEntropy P₂) =
      condMutualInfo Q := by
  classical
  intro F Q
  let e : ((α × β) × Bool) ≃ (α × Bool × β) :=
    { toFun := fun w => (w.1.1, w.2, w.1.2)
      invFun := fun s => ((s.1, s.2.2), s.2.1)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hQ_ent : shannonEntropy Q =
      binaryEntropy t + t * shannonEntropy P₁ + (1 - t) * shannonEntropy P₂ := by
    change shannonEntropy (F.map e) = _
    rw [shannonEntropy_map_equiv e F, shannonEntropy_probMixFlag]
  have hQ_xz : Q.map (fun s => (s.1, s.2.2)) = probMix t ht0 ht1 P₁ P₂ := by
    calc Q.map (fun s => (s.1, s.2.2))
      _ = F.map Prod.fst := by simp only [Q]; rw [map_comp_eq]; rfl
      _ = F.fst := (fst_eq_map_fst' F).symm
      _ = probMix t ht0 ht1 P₁ P₂ := probMixFlag_fst t ht0 ht1 P₁ P₂
  have hQ_yz_swap : (Q.map (fun s => (s.2.1, s.2.2))).map Prod.swap =
      probMixFlag t ht0 ht1 P₁.snd P₂.snd := by
    rw [show (Q.map (fun s => (s.2.1, s.2.2))).map Prod.swap =
        F.map (fun w => (w.1.2, w.2)) by
      simp only [Q]; rw [map_comp_eq, map_comp_eq]; rfl]
    refine probDist_ext' fun ⟨b, z⟩ => ?_
    unfold ProbDist.map
    dsimp only
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    trans (∑ a : α, if z then t * P₁.pmf (a, b) else (1 - t) * P₂.pmf (a, b))
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single z]
        · simp [F, probMixFlag]
        · intro z' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b' _ hne
        exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · cases z <;> simp [probMixFlag, ProbDist.snd, ← Finset.mul_sum]
  have hQ_yz_ent : shannonEntropy (Q.map (fun s => (s.2.1, s.2.2))) =
      binaryEntropy t + t * shannonEntropy P₁.snd + (1 - t) * shannonEntropy P₂.snd := by
    rw [← shannonEntropy_swap (Q.map (fun s => (s.2.1, s.2.2))), hQ_yz_swap,
      shannonEntropy_probMixFlag]
  have hQ_z : Q.map (fun s => s.2.2) = (probMix t ht0 ht1 P₁ P₂).snd := by
    calc Q.map (fun s => s.2.2)
      _ = (Q.map (fun s => (s.1, s.2.2))).map Prod.snd :=
          (map_comp_eq Q (fun s => (s.1, s.2.2)) Prod.snd).symm
      _ = (probMix t ht0 ht1 P₁ P₂).snd := by rw [hQ_xz, snd_eq_map_snd']
  unfold condMutualInfo condEntropy
  dsimp only
  rw [hQ_xz, hQ_yz_ent, hQ_ent, hQ_z]
  ring

/-- **Concavity of Conditional Entropy**:
    for `t ∈ [0, 1]` and `P₁, P₂ : ProbDist (α × β)`,
    `t H(X | Y)_{P₁} + (1 - t) H(X | Y)_{P₂} ≤ H(X | Y)_{t P₁ + (1 - t) P₂}`. -/
theorem condEntropy_concave (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist (α × β)) :
    t * condEntropy P₁ + (1 - t) * condEntropy P₂ ≤
      condEntropy (probMix t ht0 ht1 P₁ P₂) := by
  have hgap := condEntropy_mix_gap_eq_cmi t ht0 ht1 P₁ P₂
  dsimp only at hgap
  have hcmi := condMutualInfo_nonneg
    ((probMixFlag t ht0 ht1 P₁ P₂).map (fun w => (w.1.1, w.2, w.1.2)))
  linarith

/-- Upper bound on conditional mutual information: `I(X; Y | Z) ≤ H(Y)`. -/
private lemma condMutualInfo_le_shannonEntropy_mid {α' β' γ' : Type*} [Fintype α'] [Fintype β']
    [Fintype γ'] (Q : ProbDist (α' × β' × γ')) :
    condMutualInfo Q ≤ shannonEntropy (Q.map (fun s : α' × β' × γ' => s.2.1)) := by
  have h1 : shannonEntropy (Q.map (fun s : α' × β' × γ' => (s.1, s.2.2))) ≤ shannonEntropy Q :=
    shannonEntropy_map_le _ Q
  have h2 : condEntropy (Q.map (fun s : α' × β' × γ' => (s.2.1, s.2.2))) ≤
      shannonEntropy (Q.map (fun s : α' × β' × γ' => (s.2.1, s.2.2))).fst :=
    condEntropy_le_shannonEntropy _
  have hfst : (Q.map (fun s : α' × β' × γ' => (s.2.1, s.2.2))).fst =
      Q.map (fun s : α' × β' × γ' => s.2.1) := by
    rw [fst_eq_map_fst']
    exact map_comp_eq Q (fun s : α' × β' × γ' => (s.2.1, s.2.2)) Prod.fst
  have hsnd : (Q.map (fun s : α' × β' × γ' => (s.2.1, s.2.2))).snd =
      Q.map (fun s : α' × β' × γ' => s.2.2) := by
    rw [snd_eq_map_snd']
    exact map_comp_eq Q (fun s : α' × β' × γ' => (s.2.1, s.2.2)) Prod.snd
  unfold condEntropy at h2
  rw [hfst, hsnd] at h2
  unfold condMutualInfo
  dsimp only
  linarith

/-- **Almost-Convexity of Conditional Entropy** (Winter 2016):
    for `t ∈ [0, 1]` and `P₁, P₂ : ProbDist (α × β)`,
    `H(X | Y)_{t P₁ + (1 - t) P₂} ≤ t H(X | Y)_{P₁} + (1 - t) H(X | Y)_{P₂} + h(t)`. -/
theorem condEntropy_almost_convex (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist (α × β)) :
    condEntropy (probMix t ht0 ht1 P₁ P₂) ≤
      t * condEntropy P₁ + (1 - t) * condEntropy P₂ + binaryEntropy t := by
  let F := probMixFlag t ht0 ht1 P₁ P₂
  let Q : ProbDist (α × Bool × β) := F.map (fun w => (w.1.1, w.2, w.1.2))
  have hgap : condEntropy (probMix t ht0 ht1 P₁ P₂) -
      (t * condEntropy P₁ + (1 - t) * condEntropy P₂) = condMutualInfo Q :=
    condEntropy_mix_gap_eq_cmi t ht0 ht1 P₁ P₂
  have hcmi_le : condMutualInfo Q ≤ shannonEntropy (Q.map (fun s => s.2.1)) :=
    condMutualInfo_le_shannonEntropy_mid Q
  have hZ : Q.map (fun s => s.2.1) = ProbDist.bernoulli t ht0 ht1 := by
    calc Q.map (fun s => s.2.1)
      _ = F.map Prod.snd := map_comp_eq F (fun w => (w.1.1, w.2, w.1.2)) (fun s => s.2.1)
      _ = F.snd := (snd_eq_map_snd' F).symm
      _ = ProbDist.bernoulli t ht0 ht1 := probMixFlag_snd t ht0 ht1 P₁ P₂
  rw [hZ, shannonEntropy_bernoulli'] at hcmi_le
  linarith

/-- Normalized positive-difference distribution `R_+(a) = max(P(a) - Q(a), 0) / TV(P, Q)`
    when `TV(P, Q) > 0`. -/
private noncomputable def posDiffDist {γ : Type*} [Fintype γ] (P Q : ProbDist γ)
    (hT : 0 < tvDistance P Q) : ProbDist γ where
  pmf := fun a => max (P.pmf a - Q.pmf a) 0 / tvDistance P Q
  nonneg := fun a => div_nonneg (le_max_right _ _) (le_of_lt hT)
  sum_one := by
    rw [← Finset.sum_div, ← tvDistance_eq_sum_pos P Q, div_self (ne_of_gt hT)]

/-- Key Winter coupling-in-mixtures identity:
    `(1 / (1 + T)) P + (T / (1 + T)) R_- = (1 / (1 + T)) Q + (T / (1 + T)) R_+`. -/
private lemma probMix_posDiff_eq {γ : Type*} [Fintype γ] (P Q : ProbDist γ)
    (hT : 0 < tvDistance P Q) :
    let T := tvDistance P Q
    let s := 1 / (1 + T)
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by
      dsimp only [s]
      rw [div_le_one (by linarith)]
      linarith
    probMix s hs0 hs1 P (posDiffDist Q P (by rwa [tvDistance_comm])) =
      probMix s hs0 hs1 Q (posDiffDist P Q hT) := by
  intro T s hs0 hs1
  have hTne : T ≠ 0 := ne_of_gt hT
  have h1Tne : 1 + T ≠ 0 := by linarith
  have h1ms : 1 - s = T / (1 + T) := by
    dsimp only [s]
    field_simp [h1Tne]
    ring
  refine probDist_ext' fun a => ?_
  change s * P.pmf a + (1 - s) * (max (Q.pmf a - P.pmf a) 0 / tvDistance Q P) =
    s * Q.pmf a + (1 - s) * (max (P.pmf a - Q.pmf a) 0 / tvDistance P Q)
  rw [tvDistance_comm Q P, h1ms]
  change (1 / (1 + T)) * P.pmf a + (T / (1 + T)) * (max (Q.pmf a - P.pmf a) 0 / T) =
    (1 / (1 + T)) * Q.pmf a + (T / (1 + T)) * (max (P.pmf a - Q.pmf a) 0 / T)
  have hcancel : ∀ x : ℝ, (T / (1 + T)) * (x / T) = x / (1 + T) := fun x => by
    field_simp [hTne, h1Tne]
  rw [hcancel, hcancel]
  by_cases h : P.pmf a ≤ Q.pmf a
  · rw [max_eq_left (by linarith : 0 ≤ Q.pmf a - P.pmf a),
      max_eq_right (by linarith : P.pmf a - Q.pmf a ≤ 0)]
    field_simp [h1Tne]
    ring
  · rw [max_eq_right (by linarith : Q.pmf a - P.pmf a ≤ 0),
      max_eq_left (by linarith : 0 ≤ P.pmf a - Q.pmf a)]
    field_simp [h1Tne]
    ring

private lemma condEntropy_sub_le_winter (P Q : ProbDist (α × β)) :
    condEntropy P - condEntropy Q ≤
      tvDistance P Q * Real.logb 2 (Fintype.card α : ℝ) +
        (1 + tvDistance P Q) * binaryEntropy (tvDistance P Q / (1 + tvDistance P Q)) := by
  have hneαβ : Nonempty (α × β) := nonempty_of_probDist P
  have hneα : Nonempty α := ⟨hneαβ.some.1⟩
  set T := tvDistance P Q
  have hT0 : 0 ≤ T := tvDistance_nonneg P Q
  rcases eq_or_lt_of_le hT0 with hTeq | hTpos
  · have hPQ : P = Q := (tvDistance_eq_zero_iff P Q).mp hTeq.symm
    subst hPQ
    simp [T, ← hTeq, binaryEntropy_zero']
  · set s := 1 / (1 + T)
    have h1Tpos : 0 < 1 + T := by linarith
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by
      dsimp only [s]; rw [div_le_one h1Tpos]; linarith
    have h1ms : 1 - s = T / (1 + T) := by
      dsimp only [s]; field_simp [ne_of_gt h1Tpos]; ring
    let Rneg := posDiffDist Q P (by rwa [tvDistance_comm])
    let Rpos := posDiffDist P Q hTpos
    have hmix : probMix s hs0 hs1 P Rneg = probMix s hs0 hs1 Q Rpos :=
      probMix_posDiff_eq P Q hTpos
    have hlow := condEntropy_concave s hs0 hs1 P Rneg
    have hup := condEntropy_almost_convex s hs0 hs1 Q Rpos
    rw [hmix] at hlow
    have hcomb : s * condEntropy P + (1 - s) * condEntropy Rneg ≤
        s * condEntropy Q + (1 - s) * condEntropy Rpos + binaryEntropy s :=
      le_trans hlow hup
    have hRneg0 : 0 ≤ condEntropy Rneg := condEntropy_nonneg Rneg
    have hRpos_le : condEntropy Rpos ≤ Real.logb 2 (Fintype.card α : ℝ) := by
      rw [← log2_eq_logb]; exact condEntropy_le_log2_card Rpos
    have h1ms_nonneg : 0 ≤ 1 - s := by linarith
    have hdiff : s * (condEntropy P - condEntropy Q) ≤
        (1 - s) * Real.logb 2 (Fintype.card α : ℝ) + binaryEntropy (1 - s) := by
      rw [← binaryEntropy_symm' s]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (le_of_lt h1Tpos)
    have hL : (1 + T) * (s * (condEntropy P - condEntropy Q)) = condEntropy P - condEntropy Q := by
      dsimp only [s]; field_simp [ne_of_gt h1Tpos]
    have hR : (1 + T) * ((1 - s) * Real.logb 2 (Fintype.card α : ℝ) + binaryEntropy (1 - s)) =
        T * Real.logb 2 (Fintype.card α : ℝ) + (1 + T) * binaryEntropy (T / (1 + T)) := by
      rw [h1ms, mul_add]
      congr 1
      field_simp [ne_of_gt h1Tpos]
    rwa [hL, hR] at hmul

/-- **Tight Conditional Entropy Continuity (Alicki–Fannes–Winter, Winter 2016)**:
    for any two joint distributions `P, Q : ProbDist (α × β)`, with `T = TV(P, Q)`,
    `|H(X | Y)_P - H(X | Y)_Q| ≤ T · log₂|α| + (1 + T) · h(T / (1 + T))`.

    Note that this bound depends **only** on `|α|` and `TV(P, Q)` — it is completely
    independent of the conditioning alphabet size `|β|`. -/
theorem condEntropy_continuity (P Q : ProbDist (α × β)) :
    |condEntropy P - condEntropy Q| ≤
      tvDistance P Q * Real.logb 2 (Fintype.card α : ℝ) +
        (1 + tvDistance P Q) * binaryEntropy (tvDistance P Q / (1 + tvDistance P Q)) := by
  rw [abs_le]
  constructor
  · have h := condEntropy_sub_le_winter Q P
    rw [tvDistance_comm Q P] at h
    linarith
  · exact condEntropy_sub_le_winter P Q

private lemma fst_probMix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist (α × β)) :
    (probMix t ht0 ht1 P₁ P₂).fst = probMix t ht0 ht1 P₁.fst P₂.fst := by
  refine probDist_ext' fun a => ?_
  simp [ProbDist.fst, probMix, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma shannonEntropy_fst_sub_le_winter (P Q : ProbDist (α × β)) :
    shannonEntropy P.fst - shannonEntropy Q.fst ≤
      tvDistance P Q * Real.logb 2 (Fintype.card α : ℝ) +
        (1 + tvDistance P Q) * binaryEntropy (tvDistance P Q / (1 + tvDistance P Q)) := by
  have hneαβ : Nonempty (α × β) := nonempty_of_probDist P
  have hneα : Nonempty α := ⟨hneαβ.some.1⟩
  set T := tvDistance P Q
  have hT0 : 0 ≤ T := tvDistance_nonneg P Q
  rcases eq_or_lt_of_le hT0 with hTeq | hTpos
  · have hPQ : P = Q := (tvDistance_eq_zero_iff P Q).mp hTeq.symm
    subst hPQ
    simp [T, ← hTeq, binaryEntropy_zero']
  · set s := 1 / (1 + T)
    have h1Tpos : 0 < 1 + T := by linarith
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by
      dsimp only [s]; rw [div_le_one h1Tpos]; linarith
    have h1ms : 1 - s = T / (1 + T) := by
      dsimp only [s]; field_simp [ne_of_gt h1Tpos]; ring
    let Rneg := posDiffDist Q P (by rwa [tvDistance_comm])
    let Rpos := posDiffDist P Q hTpos
    have hmix_fst : probMix s hs0 hs1 P.fst Rneg.fst = probMix s hs0 hs1 Q.fst Rpos.fst := by
      rw [← fst_probMix, ← fst_probMix, probMix_posDiff_eq P Q hTpos]
    have hlow := shannonEntropy_concave s hs0 hs1 P.fst Rneg.fst
    have hup := shannonEntropy_almost_convex s hs0 hs1 Q.fst Rpos.fst
    rw [hmix_fst] at hlow
    have hcomb := le_trans hlow hup
    have hRneg0 : 0 ≤ shannonEntropy Rneg.fst := shannonEntropy_nonneg Rneg.fst
    have hRpos_le : shannonEntropy Rpos.fst ≤ Real.logb 2 (Fintype.card α : ℝ) := by
      rw [← log2_eq_logb]; exact shannonEntropy_le_log2_card Rpos.fst
    have h1ms_nonneg : 0 ≤ 1 - s := by linarith
    have hdiff : s * (shannonEntropy P.fst - shannonEntropy Q.fst) ≤
        (1 - s) * Real.logb 2 (Fintype.card α : ℝ) + binaryEntropy (1 - s) := by
      rw [← binaryEntropy_symm' s]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdiff (le_of_lt h1Tpos)
    have hL : (1 + T) * (s * (shannonEntropy P.fst - shannonEntropy Q.fst)) =
        shannonEntropy P.fst - shannonEntropy Q.fst := by
      dsimp only [s]; field_simp [ne_of_gt h1Tpos]
    have hR : (1 + T) * ((1 - s) * Real.logb 2 (Fintype.card α : ℝ) + binaryEntropy (1 - s)) =
        T * Real.logb 2 (Fintype.card α : ℝ) + (1 + T) * binaryEntropy (T / (1 + T)) := by
      rw [h1ms, mul_add]
      congr 1
      field_simp [ne_of_gt h1Tpos]
    rwa [hL, hR] at hmul

/-- **Continuity of Mutual Information** (first-alphabet form):
    for any two joint distributions `P, Q : ProbDist (α × β)` with `T = TV(P, Q)`,
    `|I(X; Y)_P - I(X; Y)_Q| ≤ 2 T · log₂|α| + 2 (1 + T) · h(T / (1 + T))`. -/
theorem mutualInfo_continuity (P Q : ProbDist (α × β)) :
    |mutualInfo P - mutualInfo Q| ≤
      2 * tvDistance P Q * Real.logb 2 (Fintype.card α : ℝ) +
        2 * (1 + tvDistance P Q) * binaryEntropy (tvDistance P Q / (1 + tvDistance P Q)) := by
  have hmi_eq : ∀ R : ProbDist (α × β), mutualInfo R = shannonEntropy R.fst - condEntropy R := by
    intro R; unfold mutualInfo condEntropy; ring
  rw [hmi_eq P, hmi_eq Q]
  have hfst : |shannonEntropy P.fst - shannonEntropy Q.fst| ≤
      tvDistance P Q * Real.logb 2 (Fintype.card α : ℝ) +
        (1 + tvDistance P Q) * binaryEntropy (tvDistance P Q / (1 + tvDistance P Q)) := by
    rw [abs_le]
    constructor
    · have h := shannonEntropy_fst_sub_le_winter Q P
      rw [tvDistance_comm Q P] at h
      linarith
    · exact shannonEntropy_fst_sub_le_winter P Q
  have hcond := condEntropy_continuity P Q
  have htri : |(shannonEntropy P.fst - condEntropy P) - (shannonEntropy Q.fst - condEntropy Q)| ≤
      |shannonEntropy P.fst - shannonEntropy Q.fst| + |condEntropy P - condEntropy Q| := by
    have heq : (shannonEntropy P.fst - condEntropy P) - (shannonEntropy Q.fst - condEntropy Q) =
        (shannonEntropy P.fst - shannonEntropy Q.fst) - (condEntropy P - condEntropy Q) := by ring
    rw [heq]
    exact abs_sub _ _
  linarith

/-- **Symmetric Continuity of Mutual Information**:
    depends only on `min(|α|, |β|)` and `T = TV(P, Q)`:
    `|I(X; Y)_P - I(X; Y)_Q| ≤ 2 T · log₂(min(|α|, |β|)) + 2 (1 + T) · h(T / (1 + T))`. -/
theorem mutualInfo_continuity_min (P Q : ProbDist (α × β)) :
    |mutualInfo P - mutualInfo Q| ≤
      2 * tvDistance P Q * Real.logb 2 ((min (Fintype.card α) (Fintype.card β) : ℕ) : ℝ) +
        2 * (1 + tvDistance P Q) * binaryEntropy (tvDistance P Q / (1 + tvDistance P Q)) := by
  by_cases hle : Fintype.card α ≤ Fintype.card β
  · rw [min_eq_left hle]
    exact mutualInfo_continuity P Q
  · have hge : Fintype.card β ≤ Fintype.card α := le_of_not_ge hle
    rw [min_eq_right hge]
    have htv_swap : tvDistance (P.map Prod.swap) (Q.map Prod.swap) = tvDistance P Q := by
      apply le_antisymm (tvDistance_map_le Prod.swap P Q)
      have hback : (P.map Prod.swap).map Prod.swap = P := by
        rw [map_comp_eq]
        have : (Prod.swap ∘ Prod.swap : α × β → α × β) = id := funext fun ⟨_, _⟩ => rfl
        rw [this]
        classical
        refine probDist_ext' fun x => ?_
        unfold ProbDist.map; dsimp only
        rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hbackQ : (Q.map Prod.swap).map Prod.swap = Q := by
        rw [map_comp_eq]
        have : (Prod.swap ∘ Prod.swap : α × β → α × β) = id := funext fun ⟨_, _⟩ => rfl
        rw [this]
        classical
        refine probDist_ext' fun x => ?_
        unfold ProbDist.map; dsimp only
        rw [Finset.sum_eq_single x]
        · simp
        · intro y _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simpa [hback, hbackQ] using tvDistance_map_le Prod.swap (P.map Prod.swap) (Q.map Prod.swap)
    have h := mutualInfo_continuity (P.map Prod.swap) (Q.map Prod.swap)
    rwa [mutualInfo_swap, mutualInfo_swap, htv_swap] at h

end ConditionalAndMIContinuity

/-! ### 4. Subset Entropy, Shearer's Lemma, Han's Inequality, and Arbitrary-Alphabet Zhang–Yeung -/

section ShearerAndHan

/-- Injective deterministic maps preserve Shannon entropy: `H(f(X)) = H(X)`. -/
theorem shannonEntropy_map_injective {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbDist α) {f : α → β} (hf : Function.Injective f) :
    shannonEntropy (P.map f) = shannonEntropy P := by
  classical
  have hpmf : ∀ b : β, (P.map f).pmf b =
      if h : ∃ a : α, f a = b then P.pmf h.choose else 0 := by
    intro b
    unfold ProbDist.map
    dsimp only
    by_cases h : ∃ a : α, f a = b
    · simp only [h, ↓reduceDIte]
      rw [Finset.sum_eq_single h.choose]
      · simp [h.choose_spec]
      · intro a _ hne
        have : f a ≠ b := fun hfa => hne (hf (hfa.trans h.choose_spec.symm))
        simp [this]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · simp only [h, ↓reduceDIte]
      refine Finset.sum_eq_zero fun a _ => ?_
      have : f a ≠ b := fun hfa => h ⟨a, hfa⟩
      simp [this]
  unfold shannonEntropy
  simp_rw [hpmf]
  trans (∑ b ∈ Finset.univ.image f,
      negPLogP (if h : ∃ a : α, f a = b then P.pmf h.choose else 0))
  · symm
    refine Finset.sum_subset (Finset.subset_univ _) fun b _ hnot => ?_
    have hnex : ¬ ∃ a : α, f a = b := fun ⟨a, ha⟩ => hnot (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
    simp [hnex, negPLogP]
  · rw [Finset.sum_image (fun a _ a' _ h => hf h)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hex : ∃ a' : α, f a' = f a := ⟨a, rfl⟩
    simp only [hex, ↓reduceDIte]
    rw [hf hex.choose_spec]

/-- Subset marginal entropy `H(X_S)` for any joint distribution `P` on a dependent product
    `∀ i : Fin n, α i` and any subset `S : Finset (Fin n)`. -/
noncomputable def subsetEntropy {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i)) (S : Finset (Fin n)) : ℝ :=
  shannonEntropy (P.map (fun x (i : S) => x i.1))

/-- On uniform `Fin k`-valued tuples, `subsetEntropy` is definitionally `Core.subsetEntropyVec`. -/
lemma subsetEntropy_eq_subsetEntropyVec {n k : ℕ} (P : ProbDist (Fin n → Fin k))
    (S : Finset (Fin n)) :
    subsetEntropy P S = subsetEntropyVec P S := rfl

/-- The subset entropy of the full coordinate set `Finset.univ` equals `shannonEntropy P`. -/
theorem subsetEntropy_univ {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i)) :
    subsetEntropy P Finset.univ = shannonEntropy P := by
  let e : (∀ i : Fin n, α i) ≃ (∀ i : (Finset.univ : Finset (Fin n)), α i.1) :=
    { toFun := fun x i => x i.1
      invFun := fun f i => f ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold subsetEntropy
  exact shannonEntropy_map_equiv e P

/-- **Every Joint Distribution Induces a Polymatroid** (`subsetEntropy P ∈ Γ_n`):
    for any dependent finite product `∀ i : Fin n, α i` and any `P : ProbDist (∀ i : Fin n, α i)`,
    `S ↦ subsetEntropy P S` satisfies `h(∅) = 0`, monotonicity, and submodularity. -/
theorem subsetEntropy_isPolymatroid {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i)) :
    IsPolymatroid n (subsetEntropy P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- h(∅) = 0
    have _ : Unique (∀ i : (∅ : Finset (Fin n)), α i.1) :=
      ⟨⟨fun i => absurd i.2 (Finset.notMem_empty _)⟩,
       fun f => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
    have hcard : Fintype.card (∀ i : (∅ : Finset (Fin n)), α i.1) = 1 := Fintype.card_unique
    exact shannonEntropy_eq_zero_of_card_le_one _ (le_of_eq hcard)
  · -- Monotonicity: S ⊆ T → H(X_S) ≤ H(X_T)
    intro S T hST
    unfold subsetEntropy
    let proj : (∀ i : T, α i.1) → (∀ i : S, α i.1) := fun y i => y ⟨i.1, hST i.2⟩
    have hcomp : P.map (fun x (i : S) => x i.1) = (P.map (fun x (i : T) => x i.1)).map proj := by
      rw [map_comp_eq]; rfl
    rw [hcomp]
    exact shannonEntropy_map_le proj _
  · -- Submodularity: H(X_{S ∪ T}) + H(X_{S ∩ T}) ≤ H(X_S) + H(X_T)
    intro S T
    unfold subsetEntropy
    let X : (∀ i : Fin n, α i) → (∀ i : (S \ T : Finset (Fin n)), α i.1) := fun x i => x i.1
    let Y : (∀ i : Fin n, α i) → (∀ i : (T \ S : Finset (Fin n)), α i.1) := fun x i => x i.1
    let Z : (∀ i : Fin n, α i) → (∀ i : (S ∩ T : Finset (Fin n)), α i.1) := fun x i => x i.1
    let Q : ProbDist ((∀ i : (S \ T : Finset (Fin n)), α i.1) ×
        (∀ i : (T \ S : Finset (Fin n)), α i.1) ×
        (∀ i : (S ∩ T : Finset (Fin n)), α i.1)) :=
      P.map (fun x => (X x, Y x, Z x))
    have hcmi := condMutualInfo_nonneg Q
    unfold condMutualInfo at hcmi
    let eS : ((∀ i : (S \ T : Finset (Fin n)), α i.1) ×
        (∀ i : (S ∩ T : Finset (Fin n)), α i.1)) ≃ (∀ i : S, α i.1) :=
      { toFun := fun pq i =>
          if h : i.1 ∈ T then pq.2 ⟨i.1, Finset.mem_inter.mpr ⟨i.2, h⟩⟩
          else pq.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩
        invFun := fun f =>
          (fun i => f ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, (Finset.mem_inter.mp i.2).1⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext i
          · simp [(Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_inter.mp i.2).2]
        right_inv := fun f => by
          funext i; dsimp only; split_ifs <;> rfl }
    let eT : ((∀ i : (T \ S : Finset (Fin n)), α i.1) ×
        (∀ i : (S ∩ T : Finset (Fin n)), α i.1)) ≃ (∀ i : T, α i.1) :=
      { toFun := fun pq i =>
          if h : i.1 ∈ S then pq.2 ⟨i.1, Finset.mem_inter.mpr ⟨h, i.2⟩⟩
          else pq.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩
        invFun := fun f =>
          (fun i => f ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, (Finset.mem_inter.mp i.2).2⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext i
          · simp [(Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_inter.mp i.2).1]
        right_inv := fun f => by
          funext i; dsimp only; split_ifs <;> rfl }
    let eU : ((∀ i : (S \ T : Finset (Fin n)), α i.1) ×
        (∀ i : (T \ S : Finset (Fin n)), α i.1) ×
        (∀ i : (S ∩ T : Finset (Fin n)), α i.1)) ≃ (∀ i : (S ∪ T : Finset (Fin n)), α i.1) :=
      { toFun := fun pqr i =>
          if hS : i.1 ∈ S then
            if hT : i.1 ∈ T then pqr.2.2 ⟨i.1, Finset.mem_inter.mpr ⟨hS, hT⟩⟩
            else pqr.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨hS, hT⟩⟩
          else pqr.2.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp i.2).resolve_left hS, hS⟩⟩
        invFun := fun f =>
          (fun i => f ⟨i.1, Finset.mem_union_left T (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, Finset.mem_union_right S (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, Finset.mem_union_left T (Finset.mem_inter.mp i.2).1⟩)
        left_inv := fun ⟨p, q, r⟩ => by
          ext i
          · simp [(Finset.mem_sdiff.mp i.2).1, (Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_inter.mp i.2).1, (Finset.mem_inter.mp i.2).2]
        right_inv := fun f => by
          funext i; dsimp only; split_ifs <;> rfl }
    have hS_eq : shannonEntropy (Q.map (fun t => (t.1, t.2.2))) =
        shannonEntropy (P.map (fun x (i : S) => x i.1)) := by
      rw [← shannonEntropy_map_equiv eS, map_comp_eq, map_comp_eq]
      congr 2; funext x; funext i; dsimp [eS, X, Z]; split_ifs <;> rfl
    have hT_eq : shannonEntropy (Q.map (fun t => (t.2.1, t.2.2))) =
        shannonEntropy (P.map (fun x (i : T) => x i.1)) := by
      rw [← shannonEntropy_map_equiv eT, map_comp_eq, map_comp_eq]
      congr 2; funext x; funext i; dsimp [eT, Y, Z]; split_ifs <;> rfl
    have hU_eq : shannonEntropy Q =
        shannonEntropy (P.map (fun x (i : (S ∪ T : Finset (Fin n))) => x i.1)) := by
      rw [← shannonEntropy_map_equiv eU, map_comp_eq]
      congr 2; funext x; funext i; dsimp [eU, X, Y, Z]; split_ifs <;> rfl
    have hI_eq : shannonEntropy (Q.map (fun t => t.2.2)) =
        shannonEntropy (P.map (fun x (i : (S ∩ T : Finset (Fin n))) => x i.1)) := by
      rw [map_comp_eq]; rfl
    dsimp only at hcmi
    rw [hS_eq, hT_eq, hU_eq, hI_eq] at hcmi
    linarith

/-- Prefix of `Fin n` strictly before coordinate `j`. -/
private def finPrefix {n : ℕ} (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i < j)

/-- Prefix of `S : Finset (Fin n)` of elements with value `< m`. -/
private def prefixFilter {n : ℕ} (S : Finset (Fin n)) (m : ℕ) : Finset (Fin n) :=
  S.filter (fun i : Fin n => i.1 < m)

private lemma prefixFilter_zero {n : ℕ} (S : Finset (Fin n)) : prefixFilter S 0 = ∅ := by
  ext i; simp [prefixFilter]

private lemma prefixFilter_self {n : ℕ} (S : Finset (Fin n)) : prefixFilter S n = S := by
  ext i
  simp only [prefixFilter, Finset.mem_filter, and_iff_left_iff_imp]
  intro _; exact i.2

private lemma prefixFilter_succ_mem {n : ℕ} (S : Finset (Fin n)) {m : ℕ} (hm : m < n)
    (hmem : (⟨m, hm⟩ : Fin n) ∈ S) :
    prefixFilter S (m + 1) = insert ⟨m, hm⟩ (prefixFilter S m) := by
  ext i
  simp only [prefixFilter, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hiS, hilt⟩
    by_cases h : i.1 = m
    · left; exact Fin.ext h
    · right; exact ⟨hiS, by omega⟩
  · rintro (rfl | ⟨hiS, hilt⟩)
    · exact ⟨hmem, Nat.lt_succ_self m⟩
    · exact ⟨hiS, Nat.lt_succ_of_lt hilt⟩

private lemma prefixFilter_succ_notMem {n : ℕ} (S : Finset (Fin n)) {m : ℕ} (hm : m < n)
    (hnot : (⟨m, hm⟩ : Fin n) ∉ S) :
    prefixFilter S (m + 1) = prefixFilter S m := by
  ext i
  simp only [prefixFilter, Finset.mem_filter]
  constructor
  · rintro ⟨hiS, hilt⟩
    refine ⟨hiS, ?_⟩
    by_cases h : i.1 = m
    · have heq : i = ⟨m, hm⟩ := Fin.ext h
      exact absurd (heq ▸ hiS) hnot
    · omega
  · rintro ⟨hiS, hilt⟩
    exact ⟨hiS, Nat.lt_succ_of_lt hilt⟩

private lemma prefixFilter_eq_inter_finPrefix {n : ℕ} (S : Finset (Fin n)) (j : Fin n) :
    prefixFilter S j.1 = S ∩ finPrefix j := by
  ext i
  simp only [prefixFilter, finPrefix, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ,
    true_and, Fin.lt_def]

/-- Telescoping lower bound for any polymatroid `h ∈ Γ_n`:
    `∑ j ∈ S, (h (insert j (I_j)) - h (I_j)) ≤ h S` where `I_j = {i | i < j}`,
    with equality for `S = Finset.univ`. -/
private lemma polymatroid_chain_lower {n : ℕ} {h : Finset (Fin n) → ℝ} (hp : IsPolymatroid n h)
    (S : Finset (Fin n)) :
    ∑ j ∈ S, (h (insert j (finPrefix j)) - h (finPrefix j)) ≤ h S := by
  have htele : h (prefixFilter S n) - h (prefixFilter S 0) =
      ∑ m ∈ Finset.range n, (h (prefixFilter S (m + 1)) - h (prefixFilter S m)) := by
    induction n with
    | zero => simp
    | succ k ih =>
      -- Direct telescoping for general f : ℕ → ℝ
      clear ih
      have hgen : ∀ (f : ℕ → ℝ) (N : ℕ),
          f N - f 0 = ∑ m ∈ Finset.range N, (f (m + 1) - f m) := by
        intro f N
        induction N with
        | zero => simp
        | succ r ihr => rw [Finset.sum_range_succ, ← ihr]; ring
      exact hgen (fun m => h (prefixFilter S m)) (k + 1)
  rw [prefixFilter_self, prefixFilter_zero, hp.1, sub_zero] at htele
  rw [htele, Finset.sum_range]
  have hrewrite : ∑ j ∈ S, (h (insert j (finPrefix j)) - h (finPrefix j)) =
      ∑ j : Fin n, if j ∈ S then (h (insert j (finPrefix j)) - h (finPrefix j)) else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hrewrite]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j ∈ S
  · simp only [hj, ↓reduceIte]
    have hsucc : prefixFilter S (j.1 + 1) = insert j (prefixFilter S j.1) :=
      prefixFilter_succ_mem S j.2 hj
    rw [hsucc, prefixFilter_eq_inter_finPrefix]
    have hsub := hp.2.2 (insert j (S ∩ finPrefix j)) (finPrefix j)
    have hunion : insert j (S ∩ finPrefix j) ∪ finPrefix j = insert j (finPrefix j) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_inter]
      tauto
    have hinter : insert j (S ∩ finPrefix j) ∩ finPrefix j = S ∩ finPrefix j := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | ⟨hiS, _⟩, hiP⟩
        · exact absurd (Finset.mem_filter.mp hiP).2 (lt_irrefl _)
        · exact ⟨hiS, hiP⟩
      · rintro ⟨hiS, hiP⟩
        exact ⟨Or.inr ⟨hiS, hiP⟩, hiP⟩
    rw [hunion, hinter] at hsub
    linarith
  · simp only [hj, ↓reduceIte]
    rw [prefixFilter_succ_notMem S j.2 hj, sub_self]

private lemma polymatroid_chain_univ {n : ℕ} {h : Finset (Fin n) → ℝ} (hp : IsPolymatroid n h) :
    h Finset.univ = ∑ j : Fin n, (h (insert j (finPrefix j)) - h (finPrefix j)) := by
  have hgen : ∀ (f : ℕ → ℝ) (N : ℕ),
      f N - f 0 = ∑ m ∈ Finset.range N, (f (m + 1) - f m) := by
    intro f N
    induction N with
    | zero => simp
    | succ r ihr => rw [Finset.sum_range_succ, ← ihr]; ring
  have htele := hgen (fun m => h (prefixFilter (Finset.univ : Finset (Fin n)) m)) n
  rw [prefixFilter_self, prefixFilter_zero, hp.1, sub_zero, Finset.sum_range] at htele
  rw [htele]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prefixFilter_succ_mem Finset.univ j.2 (Finset.mem_univ j),
    prefixFilter_eq_inter_finPrefix, Finset.univ_inter]

/-- **Fractional / Weighted Shearer's Inequality for Polymatroids**
    (Chung–Graham–Frankl–Shearer 1986; Madiman–Tetali 2010):
    for any polymatroid `h ∈ Γ_n`, indexed family `S : ι → Finset (Fin n)`, and nonnegative
    weights `w : ι → ℝ` covering every coordinate `j : Fin n` with total weight at least `k`,
    `k · h(Finset.univ) ≤ ∑ t, w t · h(S t)`. -/
theorem polymatroid_shearer_weighted {n : ℕ} {h : Finset (Fin n) → ℝ} (hp : IsPolymatroid n h)
    {ι : Type*} [Fintype ι] (S : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ t, 0 ≤ w t)
    (k : ℝ) (hcov : ∀ j : Fin n, k ≤ ∑ t : ι, if j ∈ S t then w t else 0) :
    k * h Finset.univ ≤ ∑ t : ι, w t * h (S t) := by
  let d : Fin n → ℝ := fun j => h (insert j (finPrefix j)) - h (finPrefix j)
  have hd_nonneg : ∀ j : Fin n, 0 ≤ d j := fun j => by
    dsimp only [d]
    have hmono := hp.2.1 (finPrefix j) (insert j (finPrefix j)) (Finset.subset_insert _ _)
    linarith
  calc k * h Finset.univ
    _ = k * ∑ j : Fin n, d j := by rw [polymatroid_chain_univ hp]
    _ = ∑ j : Fin n, k * d j := Finset.mul_sum _ _ _
    _ ≤ ∑ j : Fin n, (∑ t : ι, if j ∈ S t then w t else 0) * d j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcov j) (hd_nonneg j)
    _ = ∑ j : Fin n, ∑ t : ι, (if j ∈ S t then w t * d j else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
    _ = ∑ t : ι, ∑ j : Fin n, (if j ∈ S t then w t * d j else 0) := Finset.sum_comm
    _ = ∑ t : ι, w t * ∑ j ∈ S t, d j := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    _ ≤ ∑ t : ι, w t * h (S t) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (polymatroid_chain_lower hp (S t)) (hw t)

/-- **Shearer's Inequality for Polymatroids** (`k`-covering family):
    if every coordinate `j : Fin n` lies in at least `k` members of `S : ι → Finset (Fin n)`,
    then `k · h(Finset.univ) ≤ ∑ t, h(S t)`. -/
theorem polymatroid_shearer {n : ℕ} {h : Finset (Fin n) → ℝ} (hp : IsPolymatroid n h)
    {ι : Type*} [Fintype ι] (S : ι → Finset (Fin n)) (k : ℕ)
    (hcov : ∀ j : Fin n, k ≤ (Finset.univ.filter (fun t : ι => j ∈ S t)).card) :
    (k : ℝ) * h Finset.univ ≤ ∑ t : ι, h (S t) := by
  have h := polymatroid_shearer_weighted hp S (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (k : ℝ)
    (fun j => by
      have hcard : (∑ t : ι, if j ∈ S t then (1 : ℝ) else 0) =
          ((Finset.univ.filter (fun t : ι => j ∈ S t)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hcard]
      exact_mod_cast hcov j)
  simpa using h

/-- **Weighted / Fractional Shearer's Lemma for Shannon Entropy**:
    for any joint distribution `P` on `∀ i : Fin n, α i`, family `S : ι → Finset (Fin n)`,
    and nonnegative weights `w : ι → ℝ` covering every coordinate `j` with total weight `≥ k`,
    `k · H(X_1, ..., X_n) ≤ ∑ t, w t · H(X_{S t})`. -/
theorem shearer_inequality_weighted {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i))
    {ι : Type*} [Fintype ι] (S : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ t, 0 ≤ w t)
    (k : ℝ) (hcov : ∀ j : Fin n, k ≤ ∑ t : ι, if j ∈ S t then w t else 0) :
    k * shannonEntropy P ≤ ∑ t : ι, w t * subsetEntropy P (S t) := by
  rw [← subsetEntropy_univ P]
  exact polymatroid_shearer_weighted (subsetEntropy_isPolymatroid P) S w hw k hcov

/-- **Shearer's Lemma** (Chung–Graham–Frankl–Shearer 1986):
    for any joint distribution `P` on `∀ i : Fin n, α i` and any family `S : ι → Finset (Fin n)`
    such that every coordinate `j : Fin n` belongs to at least `k` sets `S t`,
    `k · H(X_1, ..., X_n) ≤ ∑ t, H(X_{S t})`. -/
theorem shearer_inequality {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i))
    {ι : Type*} [Fintype ι] (S : ι → Finset (Fin n)) (k : ℕ)
    (hcov : ∀ j : Fin n, k ≤ (Finset.univ.filter (fun t : ι => j ∈ S t)).card) :
    (k : ℝ) * shannonEntropy P ≤ ∑ t : ι, subsetEntropy P (S t) := by
  rw [← subsetEntropy_univ P]
  exact polymatroid_shearer (subsetEntropy_isPolymatroid P) S k hcov

/-- **Shearer's Lemma (Multiset Form)**:
    for any multiset `ℱ` of subsets of `Fin n` such that every coordinate `j : Fin n` belongs to
    at least `k` elements of `ℱ` (counted with multiplicity),
    `k · H(X_1, ..., X_n) ≤ ∑_{S ∈ ℱ} H(X_S)`. -/
theorem shearer_inequality_multiset {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i)) (ℱ : Multiset (Finset (Fin n))) (k : ℕ)
    (hcov : ∀ j : Fin n, k ≤ (ℱ.filter (fun S => j ∈ S)).card) :
    (k : ℝ) * shannonEntropy P ≤ (ℱ.map (subsetEntropy P)).sum := by
  induction ℱ using Quot.inductionOn with
  | _ L =>
    change (k : ℝ) * shannonEntropy P ≤ ((L : Multiset (Finset (Fin n))).map (subsetEntropy P)).sum
    have hsum : ((L : Multiset (Finset (Fin n))).map (subsetEntropy P)).sum =
        ∑ t : Fin L.length, subsetEntropy P (L.get t) := by
      clear hcov
      induction L with
      | nil => simp
      | cons S rest ih =>
        simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.sum_cons,
          List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem] at ih ⊢
        congr 1
    rw [hsum]
    refine shearer_inequality P (fun t : Fin L.length => L.get t) k fun j => ?_
    have hcard_eq : (Finset.univ.filter (fun t : Fin L.length => j ∈ L.get t)).card =
        ((L : Multiset (Finset (Fin n))).filter (fun S => j ∈ S)).card := by
      clear hcov hsum
      induction L with
      | nil => simp
      | cons S rest ih =>
        simp only [Multiset.filter_coe, List.filter_cons]
        have hsplit : (Finset.univ.filter (fun t : Fin (S :: rest).length =>
            j ∈ (S :: rest).get t)).card =
            (if j ∈ S then 1 else 0) +
              (Finset.univ.filter (fun t : Fin rest.length => j ∈ rest.get t)).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          change (∑ t : Fin (rest.length + 1), if j ∈ (S :: rest).get t then 1 else 0) = _
          rw [Fin.sum_univ_succ]
          simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
            Fin.val_zero, Fin.val_succ]
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
          rfl
        rw [hsplit, ih]
        by_cases hj : j ∈ S <;> simp [hj, add_comm]
    rw [hcard_eq]
    exact hcov j

/-- **Leave-One-Out Han's Inequality** (Cover & Thomas, Theorem 17.6.1 base case):
    `(n - 1) · H(X_1, ..., X_n) ≤ ∑ i : Fin n, H(X_{-i})`. -/
theorem han_inequality_leave_one_out {n : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin n, α i)) :
    ((n - 1 : ℕ) : ℝ) * shannonEntropy P ≤
      ∑ i : Fin n, subsetEntropy P (Finset.univ.erase i) := by
  refine shearer_inequality P (fun i : Fin n => Finset.univ.erase i) (n - 1) fun j => ?_
  have hfilt : Finset.univ.filter (fun i : Fin n => j ∈ Finset.univ.erase i) =
      Finset.univ.erase j := by
    ext i
    simp [eq_comm]
  rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]

/-- Combinatorial count: for `1 ≤ k ≤ n` and `j : Fin n`, exactly `C(n - 1, k - 1)` subsets of
    `Fin n` of size `k` contain `j`. -/
private lemma card_powersetCard_mem {n k : ℕ} (hk1 : 1 ≤ k) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).powersetCard k |>.filter (fun S => j ∈ S)).card =
      Nat.choose (n - 1) (k - 1) := by
  have hbij : ((Finset.univ : Finset (Fin n)).powersetCard k |>.filter (fun S => j ∈ S)).card =
      ((Finset.univ.erase j : Finset (Fin n)).powersetCard (k - 1)).card := by
    symm
    refine Finset.card_bij (fun T _ => insert j T) ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      have hjnot : j ∉ T := fun hj => (Finset.mem_erase.mp (hT.1 hj)).1 rfl
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self j T⟩
      rw [Finset.card_insert_of_notMem hjnot, hT.2]
      omega
    · intro T₁ hT₁ T₂ hT₂ heq
      rw [Finset.mem_powersetCard] at hT₁ hT₂
      have hj1 : j ∉ T₁ := fun hj => (Finset.mem_erase.mp (hT₁.1 hj)).1 rfl
      have hj2 : j ∉ T₂ := fun hj => (Finset.mem_erase.mp (hT₂.1 hj)).1 rfl
      have := congrArg (fun S => S.erase j) heq
      simpa [Finset.erase_insert hj1, Finset.erase_insert hj2] using this
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
      refine ⟨S.erase j, ?_, Finset.insert_erase hS.2⟩
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩, ?_⟩
      rw [Finset.card_erase_of_mem hS.2, hS.1.2]
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]

/-- **Han's Inequality (Unnormalized `k`-Subset Form)** (Cover & Thomas, Theorem 17.6.1):
    for any `1 ≤ k ≤ n` and joint distribution `P` on `∀ i : Fin n, α i`,
    `C(n - 1, k - 1) · H(X_1, ..., X_n) ≤ ∑_{|S| = k} H(X_S)`. -/
theorem han_inequality {n k : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (hk1 : 1 ≤ k) (P : ProbDist (∀ i : Fin n, α i)) :
    ((Nat.choose (n - 1) (k - 1) : ℕ) : ℝ) * shannonEntropy P ≤
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetEntropy P S := by
  let fam := (Finset.univ : Finset (Fin n)).powersetCard k
  have h := shearer_inequality P (fun S : fam => S.1) (Nat.choose (n - 1) (k - 1)) fun j => by
    have hcard : (Finset.univ.filter (fun S : fam => j ∈ S.1)).card =
        (fam.filter (fun S => j ∈ S)).card := by
      refine Finset.card_bij (fun S _ => S.1) ?_ ?_ ?_
      · intro S hS
        exact Finset.mem_filter.mpr ⟨S.2, (Finset.mem_filter.mp hS).2⟩
      · intro S₁ _ S₂ _ heq; exact Subtype.ext heq
      · intro S hS
        rw [Finset.mem_filter] at hS
        exact ⟨⟨S, hS.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS.2⟩, rfl⟩
    rw [hcard, card_powersetCard_mem hk1 j]
  have hsum : (∑ S : fam, subsetEntropy P S.1) = ∑ S ∈ fam, subsetEntropy P S :=
    Finset.sum_coe_sort fam (subsetEntropy P)
  rwa [hsum] at h

/-- **Han's Inequality (Normalized Average Form)** (Cover & Thomas, Theorem 17.6.1):
    for `1 ≤ k ≤ n`,
    `(1 / n) · H(X_1, ..., X_n) ≤ (1 / (C(n, k) · k)) · ∑_{|S| = k} H(X_S)`. -/
theorem han_inequality_avg {n k : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (P : ProbDist (∀ i : Fin n, α i)) :
    (1 / (n : ℝ)) * shannonEntropy P ≤
      (1 / ((Nat.choose n k : ℝ) * (k : ℝ))) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetEntropy P S := by
  have hn1 : 1 ≤ n := le_trans hk1 hkn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hch_pos : (0 : ℝ) < (Nat.choose n k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkn
  have hident_nat : k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa [Nat.succ_sub_one, mul_comm] using (Nat.add_one_mul_choose_eq n' k').symm
  have hident : (Nat.choose n k : ℝ) * (k : ℝ) =
      (n : ℝ) * ((Nat.choose (n - 1) (k - 1) : ℕ) : ℝ) := by
    have : ((k * Nat.choose n k : ℕ) : ℝ) = ((n * Nat.choose (n - 1) (k - 1) : ℕ) : ℝ) := by
      exact_mod_cast hident_nat
    push_cast at this
    linarith
  have hhan := han_inequality hk1 P
  have hden_pos : 0 < (Nat.choose n k : ℝ) * (k : ℝ) := mul_pos hch_pos hk_pos
  rw [one_div_mul_eq_div, one_div_mul_eq_div, div_le_div_iff₀ hn_pos hden_pos, hident]
  have := mul_le_mul_of_nonneg_left hhan (le_of_lt hn_pos)
  linarith

/-- **Full Han Monotonicity Step** (Cover & Thomas, Theorem 17.6.1):
    the normalized average `k`-subset entropy
    `h_k := (1 / (C(n, k) · k)) ∑_{|S| = k} H(X_S)` is antitone in `k`:
    `h_{k+1} ≤ h_k` for all `1 ≤ k < n`. -/
theorem han_average_antitone_step {n k : ℕ} {α : Fin n → Type*} [∀ i, Fintype (α i)]
    (hk1 : 1 ≤ k) (hkn : k < n) (P : ProbDist (∀ i : Fin n, α i)) :
    (1 / ((Nat.choose n (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ))) *
        ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1), subsetEntropy P T ≤
      (1 / ((Nat.choose n k : ℝ) * (k : ℝ))) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetEntropy P S := by
  -- Step 1: For each T of size k + 1, k * H(X_T) ≤ ∑_{i ∈ T} H(X_{T \ {i}})
  have hstep : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1),
      (k : ℝ) * subsetEntropy P T ≤ ∑ i ∈ T, subsetEntropy P (T.erase i) := by
    intro T hT
    have hTcard : T.card = k + 1 := (Finset.mem_powersetCard.mp hT).2
    let e : Fin (k + 1) ≃ T := (Fintype.equivFinOfCardEq (by simp [hTcard])).symm
    let eEmb : Fin (k + 1) ↪ Fin n :=
      ⟨fun r => (e r).1, fun r₁ r₂ h => e.injective (Subtype.ext h)⟩
    let hRestr : Finset (Fin (k + 1)) → ℝ := fun A => subsetEntropy P (A.map eEmb)
    have hpoly : IsPolymatroid (k + 1) hRestr := by
      have hp := subsetEntropy_isPolymatroid P
      refine ⟨?_, ?_, ?_⟩
      · simpa [hRestr] using hp.1
      · intro A B hAB
        exact hp.2.1 (A.map eEmb) (B.map eEmb) (Finset.map_subset_map.mpr hAB)
      · intro A B
        have hu : (A ∪ B).map eEmb = A.map eEmb ∪ B.map eEmb := Finset.map_union A B
        have hi : (A ∩ B).map eEmb = A.map eEmb ∩ B.map eEmb := Finset.map_inter A B
        dsimp only [hRestr]
        rw [hu, hi]
        exact hp.2.2 (A.map eEmb) (B.map eEmb)
    have huniv_map : (Finset.univ : Finset (Fin (k + 1))).map eEmb = T := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, eEmb]
      constructor
      · rintro ⟨r, rfl⟩; exact (e r).2
      · intro hx; exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
    have herase_map : ∀ r : Fin (k + 1),
        (Finset.univ.erase r : Finset (Fin (k + 1))).map eEmb = T.erase (e r).1 := by
      intro r
      ext x
      simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true, eEmb]
      constructor
      · rintro ⟨s, hsr, rfl⟩
        exact ⟨fun h => hsr (e.injective (Subtype.ext h)), (e s).2⟩
      · rintro ⟨hxne, hxT⟩
        refine ⟨e.symm ⟨x, hxT⟩, ?_, congrArg Subtype.val (e.apply_symm_apply ⟨x, hxT⟩)⟩
        intro heq
        apply hxne
        have := congrArg e heq
        rw [e.apply_symm_apply] at this
        exact congrArg Subtype.val this
    have hsh := polymatroid_shearer hpoly (fun r : Fin (k + 1) => Finset.univ.erase r) k fun j => by
      have hfilt : Finset.univ.filter (fun r : Fin (k + 1) => j ∈ Finset.univ.erase r) =
          Finset.univ.erase j := by
        ext r; simp [eq_comm]
      rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
      omega
    dsimp only [hRestr] at hsh
    rw [huniv_map] at hsh
    simp_rw [herase_map] at hsh
    have hsum_eq : (∑ r : Fin (k + 1), subsetEntropy P (T.erase (e r).1)) =
        ∑ i ∈ T, subsetEntropy P (T.erase i) := by
      rw [← Finset.sum_coe_sort T (fun i => subsetEntropy P (T.erase i))]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    rwa [hsum_eq] at hsh
  -- Step 2: Sum over all T of size k + 1 and double-count pairs (S, T) with S ⊂ T
  have hsum_step :
      (k : ℝ) * ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1), subsetEntropy P T ≤
        ((n - k : ℕ) : ℝ) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetEntropy P S := by
    rw [Finset.mul_sum]
    calc ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1), (k : ℝ) * subsetEntropy P T
      _ ≤ ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1),
            ∑ i ∈ T, subsetEntropy P (T.erase i) :=
          Finset.sum_le_sum hstep
      _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1),
            ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              if S ⊆ T then subsetEntropy P S else 0 := by
          refine Finset.sum_congr rfl fun T hT => ?_
          have hTcard : T.card = k + 1 := (Finset.mem_powersetCard.mp hT).2
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun i _ => T.erase i) ?_ ?_ ?_ (fun _ _ => rfl)
          · intro i hi
            rw [Finset.mem_filter, Finset.mem_powersetCard]
            exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hi, hTcard]; omega⟩,
              Finset.erase_subset i T⟩
          · intro i₁ hi₁ i₂ hi₂ heq
            by_contra hne
            have h1 : i₁ ∈ T.erase i₂ := Finset.mem_erase.mpr ⟨hne, hi₁⟩
            rw [← heq] at h1
            exact (Finset.mem_erase.mp h1).1 rfl
          · intro S hS
            rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
            have hdiff_card : (T \ S).card = 1 := by
              rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS.2, hTcard, hS.1.2]; omega
            obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdiff_card
            have hiT : i ∈ T := (Finset.mem_sdiff.mp (hi ▸ Finset.mem_singleton_self i)).1
            refine ⟨i, hiT, ?_⟩
            ext x
            simp only [Finset.mem_erase]
            constructor
            · rintro ⟨hxi, hxT⟩
              by_contra hxS
              have hxmem : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hxT, hxS⟩
              rw [hi, Finset.mem_singleton] at hxmem
              exact hxi hxmem
            · intro hxS
              refine ⟨fun hxi => ?_, hS.2 hxS⟩
              have hiS : i ∉ S := (Finset.mem_sdiff.mp (hi ▸ Finset.mem_singleton_self i)).2
              exact hiS (hxi ▸ hxS)
      _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1),
              if S ⊆ T then subsetEntropy P S else 0 := Finset.sum_comm
      _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            ((n - k : ℕ) : ℝ) * subsetEntropy P S := by
          refine Finset.sum_congr rfl fun S hS => ?_
          have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 1
          have hcnt : ((Finset.univ : Finset (Fin n)).powersetCard (k + 1) |>.filter
              (fun T => S ⊆ T)).card = n - k := by
            have hbij : ((Finset.univ : Finset (Fin n)).powersetCard (k + 1) |>.filter
                (fun T => S ⊆ T)).card = (Finset.univ \ S).card := by
              symm
              refine Finset.card_bij (fun i _ => insert i S) ?_ ?_ ?_
              · intro i hi
                have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
                rw [Finset.mem_filter, Finset.mem_powersetCard]
                exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hiS, hScard]⟩,
                  Finset.subset_insert i S⟩
              · intro i₁ hi₁ i₂ hi₂ heq
                have hi₁S : i₁ ∉ S := (Finset.mem_sdiff.mp hi₁).2
                have hmem : i₁ ∈ insert i₂ S := heq ▸ Finset.mem_insert_self i₁ S
                exact (Finset.mem_insert.mp hmem).resolve_right hi₁S
              · intro T hT
                rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
                have hdiff_card : (T \ S).card = 1 := by
                  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT.2, hT.1.2, hScard]; omega
                obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdiff_card
                have hiTS : i ∈ T \ S := hi ▸ Finset.mem_singleton_self i
                refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hiTS).2⟩, ?_⟩
                ext x
                simp only [Finset.mem_insert]
                constructor
                · rintro (rfl | hxS)
                  · exact (Finset.mem_sdiff.mp hiTS).1
                  · exact hT.2 hxS
                · intro hxT
                  by_cases hxS : x ∈ S
                  · exact Or.inr hxS
                  · left
                    have hxTS : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hxT, hxS⟩
                    rw [hi, Finset.mem_singleton] at hxTS
                    exact hxTS
            rw [hbij, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ S),
              Finset.card_univ, Fintype.card_fin, hScard]
          exact_mod_cast hcnt
      _ = ((n - k : ℕ) : ℝ) *
            ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, subsetEntropy P S := by
          rw [Finset.mul_sum]
  -- Step 3: Divide by using (k + 1) * C(n, k + 1) = (n - k) * C(n, k)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
  have hchk_pos : (0 : ℝ) < (Nat.choose n k : ℝ) := by exact_mod_cast Nat.choose_pos (le_of_lt hkn)
  have hchk1_pos : (0 : ℝ) < (Nat.choose n (k + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.succ_le_of_lt hkn)
  have hident_nat : Nat.choose n (k + 1) * (k + 1) = (n - k) * Nat.choose n k := by
    simpa [mul_comm] using Nat.choose_succ_right_eq n k
  have hident : (Nat.choose n (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      ((n - k : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by
    exact_mod_cast hident_nat
  have hden1 : 0 < (Nat.choose n (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := mul_pos hchk1_pos hk1_pos
  have hden2 : 0 < (Nat.choose n k : ℝ) * (k : ℝ) := mul_pos hchk_pos hk_pos
  rw [one_div_mul_eq_div, one_div_mul_eq_div, div_le_div_iff₀ hden1 hden2, hident]
  have hmul := mul_le_mul_of_nonneg_left hsum_step (le_of_lt hchk_pos)
  linarith

/-- **Zhang–Yeung (1998) Inequality on Arbitrary Finite Alphabets**:
    lifts `zhang_yeung_subsetEntropyVec` (from `InfoTheory.Bridge.FeketeAndCopyLemma`) from
    `Fin 4 → Fin k` to any dependent 4-tuple of arbitrary finite types `∀ i : Fin 4, α i`. -/
theorem zhang_yeung_subsetEntropy {α : Fin 4 → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist (∀ i : Fin 4, α i)) :
    let h := subsetEntropy P
    let I (A B : Finset (Fin 4)) : ℝ := h A + h B - h (A ∪ B)
    let cI (A B C : Finset (Fin 4)) : ℝ := h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C
    2 * I {2} {3} ≤ I {0} {1} + I {0} ({2, 3} : Finset (Fin 4)) +
      3 * cI {2} {3} {0} + cI {2} {3} {1} := by
  let k : ℕ := (Finset.univ : Finset (Fin 4)).sup (fun i => Fintype.card (α i))
  let emb : ∀ i : Fin 4, α i → Fin k := fun i a =>
    ⟨((Fintype.equivFin (α i)) a).1,
      lt_of_lt_of_le ((Fintype.equivFin (α i)) a).2
        (Finset.le_sup (f := fun i => Fintype.card (α i)) (Finset.mem_univ i))⟩
  have hemb_inj : ∀ i : Fin 4, Function.Injective (emb i) := fun i a b hab => by
    have hval : (emb i a).1 = (emb i b).1 := congrArg Fin.val hab
    exact (Fintype.equivFin (α i)).injective (Fin.ext hval)
  let Q : ProbDist (Fin 4 → Fin k) := P.map (fun x i => emb i (x i))
  have heq : ∀ S : Finset (Fin 4), subsetEntropyVec Q S = subsetEntropy P S := by
    intro S
    unfold subsetEntropyVec subsetEntropy Q
    rw [map_comp_eq]
    let embS : (∀ i : S, α i.1) → (∀ _ : S, Fin k) := fun f i => emb i.1 (f i)
    have hembS_inj : Function.Injective embS := fun f g hfg => by
      funext i
      exact hemb_inj i.1 (congrFun hfg i)
    have hcomp : P.map ((fun x (i : S) => x i.1) ∘ fun x i => emb i (x i)) =
        (P.map (fun x (i : S) => x i.1)).map embS := by
      rw [map_comp_eq]; rfl
    rw [hcomp]
    exact shannonEntropy_map_injective _ hembS_inj
  have hzy := zhang_yeung_subsetEntropyVec Q
  dsimp only at hzy ⊢
  simp_rw [heq] at hzy
  exact hzy

end ShearerAndHan

end InfoTheory.Bridge
