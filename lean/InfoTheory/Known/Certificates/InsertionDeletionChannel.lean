import InfoTheory.Problems.InsertionDeletionChannel
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.InsertionDeletionChannel`

The Statement asks whether Gallager's binary insertion–deletion capacity
`C_IDS(p_d, p_i) = inf_{n ≥ 1} (1/n) sup_P I(X^n; Y)` (`idsCapacity`) is jointly convex on the
simplex `p_d, p_i ≥ 0, p_d + p_i ≤ 1` (Gallager 1961; Dobrushin 1967; Mitzenmacher, Probab.
Surveys 6, 2009). This file checks that the exact objects of the Statement — the recursive
transition law `idsProb`, the finite-blocklength mutual information `idsMI`, its supremum
`idsMaxMI`, and the `sInf` defining `idsCapacity` — reproduce the two solved corners of the
simplex.

## Certified
* `idsProb_zero_zero`: at `(p_d, p_i) = (0, 0)` the recursion is the identity channel,
  `idsProb 0 0 x y = [x = y]`.
* `idsProb_one_zero`: at `(1, 0)` every bit is deleted, `idsProb 1 0 x y = [y = []]`.
* `idsMI_zero_zero`: on the noiseless channel `I(X^n; Y) = H(P)` for every input law `P`
  (the `Σ`-typed output alphabet of lengths `0..2n` is handled exactly).
* `idsMaxMI_zero_zero`: `sup_P I(X^n; Y) = n` on the noiseless channel (genuine supremum:
  the set is bounded above by `n` and attained by the uniform law).
* `idsCapacity_zero_zero`: **regression** `C_IDS(0, 0) = 1` bit per input bit.
* `idsMI_one_zero`, `idsMaxMI_one_zero`, `idsCapacity_one_zero`: **regression**
  `C_IDS(1, 0) = 0` (the all-deletion channel has zero capacity).

These two values are the endpoints `C(0) = 1`, `C(1) = 0` of the deletion-channel slice
`p_i = 0`, and they show that `idsCapacity` is not a junk `sInf`/`sSup` value there.

## Not certified
* Normalisation `∑_y idsProb pd pi x y = 1` for general `(pd, pi)`, boundedness of
  `idsMI` (hence that `idsMaxMI` is a genuine supremum) off the two corners, and
  Fekete's identification of the `inf` with `lim C_n / n` (subadditivity of `C_n`).
* The genie bound `C_IDS(p_d, p_i) ≤ 1 - p_d - p_i`, Gallager's lower bound, and
  `C_IDS = 0` on the whole edge `p_d + p_i = 1`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.InsertionDeletionChannel

open InfoTheory InfoTheory.Problems.InsertionDeletionChannel

private lemma nplp_zero : negPLogP 0 = 0 := by simp [negPLogP]

private lemma nplp_one : negPLogP 1 = 0 := by simp [negPLogP, log2]

private lemma nplp_ite (c : Prop) [Decidable c] : negPLogP (if c then 1 else 0) = 0 := by
  split_ifs
  · exact nplp_one
  · exact nplp_zero

/-- At `(p_d, p_i) = (0, 0)` the transition law is the identity channel on `{0,1}*`. -/
theorem idsProb_zero_zero :
    ∀ (l l' : List Bool), idsProb 0 0 l l' = if l = l' then 1 else 0
  | [], [] => by simp [idsProb]
  | [], _ :: _ => by simp [idsProb]
  | _ :: xs, [] => by simp [idsProb]
  | a :: xs, [b] => by
      rw [idsProb, idsProb_zero_zero xs []]
      by_cases hab : a = b <;> by_cases hxs : xs = [] <;> simp [hab, hxs]
  | a :: xs, b₁ :: b₂ :: ys => by
      rw [idsProb, idsProb_zero_zero xs (b₂ :: ys)]
      by_cases hab : a = b₁ <;> by_cases hxs : xs = b₂ :: ys <;> simp [hab, hxs]

/-- At `(p_d, p_i) = (1, 0)` every input bit is deleted: the output is empty a.s. -/
theorem idsProb_one_zero :
    ∀ (l l' : List Bool), idsProb 1 0 l l' = if l' = [] then 1 else 0
  | [], [] => by simp [idsProb]
  | [], _ :: _ => by simp [idsProb]
  | _ :: xs, [] => by simp [idsProb, idsProb_one_zero xs []]
  | a :: xs, [b] => by
      rw [idsProb, idsProb_one_zero xs [b]]
      simp
  | a :: xs, b₁ :: b₂ :: ys => by
      rw [idsProb, idsProb_one_zero xs (b₁ :: b₂ :: ys)]
      simp

/-! ### The all-deletion corner `(1, 0)` -/

theorem idsMI_one_zero (n : ℕ) (P : ProbDist (Fin n → Bool)) : idsMI 1 0 n P = 0 := by
  unfold idsMI
  simp only [idsProb_one_zero]
  have h1 : ∀ c : Prop, [Decidable c] →
      (∑ x : Fin n → Bool, P.pmf x * (if c then (1 : ℝ) else 0)) = if c then 1 else 0 := by
    intro c _
    rw [← Finset.sum_mul, P.sum_one, one_mul]
  simp only [h1, nplp_ite, Finset.sum_const_zero, mul_zero, sub_zero]

theorem idsMaxMI_one_zero (n : ℕ) : idsMaxMI 1 0 n = 0 := by
  unfold idsMaxMI
  have : { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = idsMI 1 0 n P } = {0} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, idsMI_one_zero]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨ProbDist.uniform, h⟩⟩
  rw [this, csSup_singleton]

/-- **Regression.** `C_IDS(1, 0) = 0`. -/
theorem idsCapacity_one_zero : idsCapacity 1 0 = 0 := by
  unfold idsCapacity
  have : { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = idsMaxMI 1 0 n / (n : ℝ) } = {0} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, idsMaxMI_one_zero, zero_div]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨1, one_pos, h⟩⟩
  rw [this, csInf_singleton]

/-! ### The noiseless corner `(0, 0)` -/

/-- On the noiseless channel the blocklength-`n` mutual information is the input entropy. -/
theorem idsMI_zero_zero (n : ℕ) (P : ProbDist (Fin n → Bool)) :
    idsMI 0 0 n P = shannonEntropy P := by
  unfold idsMI shannonEntropy
  simp only [idsProb_zero_zero, nplp_ite, Finset.sum_const_zero, mul_zero, sub_zero]
  rw [Fintype.sum_sigma]
  have hn : n < 2 * n + 1 := by omega
  rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin (2 * n + 1))]
  · refine Finset.sum_congr rfl (fun v _ => ?_)
    congr 1
    have : ∀ x : Fin n → Bool,
        (if List.ofFn x = List.ofFn v then (1 : ℝ) else 0) = if x = v then 1 else 0 := by
      intro x
      simp only [List.ofFn_inj]
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · intro k _ hk
    refine Finset.sum_eq_zero (fun v _ => ?_)
    have : ∀ x : Fin n → Bool,
        (if List.ofFn x = List.ofFn v then (1 : ℝ) else 0) = 0 := by
      intro x
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      intro h
      have hl := congrArg List.length h
      simp only [List.length_ofFn] at hl
      exact hk (Fin.ext hl.symm)
    simp only [this, mul_zero, Finset.sum_const_zero, nplp_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma log2_two_pow (n : ℕ) : log2 ((2 : ℝ) ^ n) = n := by
  unfold log2
  rw [Real.log_pow, mul_div_assoc, div_self (ne_of_gt (Real.log_pos one_lt_two)), mul_one]

/-- On the noiseless channel `sup_P I(X^n; Y) = n` (a genuine, attained supremum). -/
theorem idsMaxMI_zero_zero (n : ℕ) : idsMaxMI 0 0 n = n := by
  unfold idsMaxMI
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    simp [Fintype.card_bool, Fintype.card_fin]
  have hub : ∀ m ∈ { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = idsMI 0 0 n P },
      m ≤ n := by
    rintro m ⟨P, rfl⟩
    rw [idsMI_zero_zero]
    have := InfoTheory.Bridge.shannonEntropy_le_log2_card P
    rwa [hcard, log2_two_pow] at this
  have hmem : (n : ℝ) ∈ { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = idsMI 0 0 n P } := by
    refine ⟨ProbDist.uniform, ?_⟩
    rw [idsMI_zero_zero, InfoTheory.Known.shannonEntropy_uniform, hcard, log2_two_pow]
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨n, hub⟩ hmem)

/-- **Regression.** `C_IDS(0, 0) = 1` bit per input bit. -/
theorem idsCapacity_zero_zero : idsCapacity 0 0 = 1 := by
  unfold idsCapacity
  have : { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = idsMaxMI 0 0 n / (n : ℝ) } = {1} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, idsMaxMI_zero_zero]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact div_self (Nat.cast_ne_zero.mpr hn.ne')
    · intro h
      exact ⟨1, one_pos, by rw [h]; norm_num⟩
  rw [this, csInf_singleton]

end InfoTheory.Known.Certificates.InsertionDeletionChannel
