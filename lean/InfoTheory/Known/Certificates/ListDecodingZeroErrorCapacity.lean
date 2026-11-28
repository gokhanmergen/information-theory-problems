import InfoTheory.Problems.ListDecodingZeroErrorCapacity
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ListDecodingZeroErrorCapacity`

The frozen statement is `zeroErrorList2Cap32 < log₂(3/2)`, where `zeroErrorList2Cap32` is the
`sInf` of all eventual upper bounds `r` on the rates `log₂|C|/n` of nonempty trifferent codes
`C ⊆ {0,1,2}^n` (a `limsup`-style definition). The docstring claims
`(1/4) log₂(9/5) ≤ C_{3/2,2} ≤ log₂(3/2)`.

Certified here:
* `card_le_of_isTrifferentCode` — **Elias's bound** `2^n · |C| ≤ 2 · 3^n`, i.e.
  `|C| ≤ 2 (3/2)^n`, for every trifferent code of length `n` (Elias, *Zero error capacity under
  list decoding*, IEEE Trans. Inform. Theory 34 (1988); the proof deletes the first coordinate
  after discarding the codewords with a chosen first symbol);
* `rate_le` — `log₂|C|/n ≤ log₂(3/2) + 1/n` for nonempty trifferent `C`, `n ≥ 1`;
* `capSet_nonempty`, `capSet_bddBelow` — the `sInf` is over a nonempty set bounded below
  (by `0`), so `zeroErrorList2Cap32` is not a junk value;
* `zeroErrorList2Cap32_nonneg` — `0 ≤ zeroErrorList2Cap32`;
* `zeroErrorList2Cap32_le` — `zeroErrorList2Cap32 ≤ log₂(3/2)`, the elementary upper bound
  quoted in the docstring.

* **Regression** (known small values of the maximum trifferent code size `T(n)`; Körner–Marton
  1988, and the docstring's own `T(1) = 3`, `T(2) = 4`): `regression_T1`, `regression_T2`,
  `regression_T3` — the frozen predicate `IsTrifferentCode` gives `T(1) = 3`, `T(2) = 4`,
  `T(3) = 6` (explicit codes checked by `decide`; the matching upper bounds are Elias's bound
  `|C| ≤ 2 (3/2)^n`, which is tight for `n ≤ 3`).

Not certified: the lower bound `(1/4) log₂(9/5) ≤ zeroErrorList2Cap32` (Körner–Marton 1988,
random coding with expurgation). The `Statement` (strict inequality) is not settled by these
facts: it is the well-known open problem of improving Elias's trifferent bound.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ListDecodingZeroErrorCapacity

open InfoTheory InfoTheory.Problems.ListDecodingZeroErrorCapacity

private lemma no_three_avoiding (a x y z : Fin 3) (hx : x ≠ a) (hy : y ≠ a) (hz : z ≠ a) :
    ¬ (x ≠ y ∧ y ≠ z ∧ x ≠ z) := by
  revert a x y z; decide

/-- Codewords whose first symbol avoids `a`. -/
private def avoid {n : ℕ} (C : Finset (Fin (n + 1) → Fin 3)) (a : Fin 3) :
    Finset (Fin (n + 1) → Fin 3) :=
  C.filter (fun x => x 0 ≠ a)

/-- In `avoid C a`, no three distinct codewords are separated at coordinate `0`, so any
separating coordinate is a successor. -/
private lemma sep_succ {n : ℕ} {C : Finset (Fin (n + 1) → Fin 3)} (hC : IsTrifferentCode (n + 1) C)
    {a : Fin 3} {x y z : Fin (n + 1) → Fin 3} (hx : x ∈ avoid C a) (hy : y ∈ avoid C a)
    (hz : z ∈ avoid C a) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∃ j : Fin n, x j.succ ≠ y j.succ ∧ y j.succ ≠ z j.succ ∧ x j.succ ≠ z j.succ := by
  simp only [avoid, Finset.mem_filter] at hx hy hz
  obtain ⟨i, hi⟩ := hC x hx.1 y hy.1 z hz.1 hxy hyz hxz
  cases i using Fin.cases with
  | zero => exact absurd hi (no_three_avoiding a _ _ _ hx.2 hy.2 hz.2)
  | succ j => exact ⟨j, hi⟩

/-- Each `avoid C a` has at most `2 (3/2)^n` words, given Elias's bound in length `n`. -/
private lemma avoid_bound {n : ℕ}
    (ih : ∀ C : Finset (Fin n → Fin 3), IsTrifferentCode n C → 2 ^ n * C.card ≤ 2 * 3 ^ n)
    {C : Finset (Fin (n + 1) → Fin 3)} (hC : IsTrifferentCode (n + 1) C) (a : Fin 3) :
    2 ^ n * (avoid C a).card ≤ 2 * 3 ^ n := by
  classical
  by_cases hsmall : (avoid C a).card ≤ 2
  · calc 2 ^ n * (avoid C a).card ≤ 2 ^ n * 2 := Nat.mul_le_mul_left _ hsmall
      _ ≤ 3 ^ n * 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) n)
      _ = 2 * 3 ^ n := mul_comm _ _
  push Not at hsmall
  have hinj : Set.InjOn (fun x : Fin (n + 1) → Fin 3 => Fin.tail x) (avoid C a : Set _) := by
    intro x hx y hy hxy
    by_contra hne
    have hcard : 0 < (((avoid C a).erase x).erase y).card := by
      have h1 := Finset.card_erase_of_mem (Finset.mem_coe.1 hx)
      have h2 : ((avoid C a).erase x).card - 1 ≤ (((avoid C a).erase x).erase y).card :=
        Finset.pred_card_le_card_erase
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hcard
    simp only [Finset.mem_erase] at hz
    obtain ⟨hzy, hzx, hz⟩ := hz
    obtain ⟨j, hj, -, -⟩ := sep_succ hC (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hy) hz hne
      (Ne.symm hzy) (Ne.symm hzx)
    exact hj (congrFun hxy j)
  have himg : IsTrifferentCode n ((avoid C a).image Fin.tail) := by
    intro x' hx' y' hy' z' hz' hxy hyz hxz
    simp only [Finset.mem_image] at hx' hy' hz'
    obtain ⟨x, hx, rfl⟩ := hx'
    obtain ⟨y, hy, rfl⟩ := hy'
    obtain ⟨z, hz, rfl⟩ := hz'
    have hxy' : x ≠ y := by rintro rfl; exact hxy rfl
    have hyz' : y ≠ z := by rintro rfl; exact hyz rfl
    have hxz' : x ≠ z := by rintro rfl; exact hxz rfl
    exact sep_succ hC hx hy hz hxy' hyz' hxz'
  have := ih _ himg
  rwa [Finset.card_image_of_injOn hinj] at this

/-- **Elias's bound** for trifferent codes: `2^n · |C| ≤ 2 · 3^n`. -/
theorem card_le_of_isTrifferentCode :
    ∀ (n : ℕ) (C : Finset (Fin n → Fin 3)), IsTrifferentCode n C → 2 ^ n * C.card ≤ 2 * 3 ^ n
  | 0, C, _ => by
    have : C.card ≤ 1 := by
      have := Finset.card_le_univ C
      simpa using this
    simp only [pow_zero, one_mul, mul_one]
    omega
  | n + 1, C, hC => by
    classical
    have ih := card_le_of_isTrifferentCode n
    -- `∑_a |avoid C a| = 2 |C|`
    have hsum : ∑ a : Fin 3, (avoid C a).card = 2 * C.card := by
      have hfib : ∑ a : Fin 3, (C.filter (fun x => x 0 = a)).card = C.card :=
        (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (x 0))).symm
      have hsplit : ∀ a : Fin 3, (avoid C a).card + (C.filter (fun x => x 0 = a)).card
          = C.card := by
        intro a
        rw [avoid, add_comm]
        exact Finset.card_filter_add_card_filter_not _
      have h3 := Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin 3)))
        (f := fun a => (avoid C a).card) (g := fun a => (C.filter (fun x => x 0 = a)).card)
      simp only [hsplit, hfib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul] at h3
      omega
    have hb := fun a => avoid_bound ih hC a
    calc 2 ^ (n + 1) * C.card = 2 ^ n * (2 * C.card) := by ring
      _ = ∑ a : Fin 3, 2 ^ n * (avoid C a).card := by rw [← hsum, Finset.mul_sum]
      _ ≤ ∑ _a : Fin 3, 2 * 3 ^ n := Finset.sum_le_sum fun a _ => hb a
      _ = 2 * 3 ^ (n + 1) := by simp [Finset.sum_const]; ring

private lemma log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos one_lt_two).le

/-- Rate bound: `log₂|C|/n ≤ log₂(3/2) + 1/n` for nonempty trifferent `C`, `n ≥ 1`. -/
theorem rate_le {n : ℕ} (hn : 0 < n) {C : Finset (Fin n → Fin 3)} (hne : C.Nonempty)
    (hC : IsTrifferentCode n C) :
    log2 (C.card : ℝ) / n ≤ log2 ((3 : ℝ) / 2) + 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hne.card_pos
  have hb : (C.card : ℝ) ≤ 2 * ((3 : ℝ) / 2) ^ n := by
    have h := card_le_of_isTrifferentCode n C hC
    have h' : (2 : ℝ) ^ n * C.card ≤ 2 * 3 ^ n := by exact_mod_cast h
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity), mul_comm]
    exact h'
  have hl := log2_le_log2 hCpos hb
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e : log2 (2 * ((3 : ℝ) / 2) ^ n) = 1 + n * log2 ((3 : ℝ) / 2) := by
    simp only [log2]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, add_div, div_self hL.ne',
      mul_div_assoc]
  rw [e] at hl
  rw [div_le_iff₀ hnR, add_mul, one_div_mul_cancel hnR.ne']
  linarith

/-- The set whose `sInf` defines `zeroErrorList2Cap32`. -/
abbrev capSet : Set ℝ :=
  { r : ℝ | ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    ∀ C : Finset (Fin n → Fin 3), C.Nonempty → IsTrifferentCode n C →
      log2 (C.card : ℝ) / (n : ℝ) ≤ r }

/-- Any eventual rate bound `r` dominates `log₂(3/2) + 1/n`-type bounds: `log₂(3/2) + ε` is an
eventual bound for every `ε > 0`. -/
theorem add_mem_capSet {ε : ℝ} (hε : 0 < ε) : log2 ((3 : ℝ) / 2) + ε ∈ capSet := by
  refine ⟨⌈1 / ε⌉₊ + 1, Nat.succ_pos _, fun n hn C hne hC => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine (rate_le hn0 hne hC).trans (add_le_add_right ?_ _)
  have h1 : 1 / ε < n := by
    have := Nat.le_ceil (1 / ε)
    have h2 : ((⌈1 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  rw [div_lt_iff₀ hε] at h1
  rw [div_le_iff₀ hnR]
  linarith

theorem capSet_nonempty : capSet.Nonempty := ⟨_, add_mem_capSet one_pos⟩

/-- Every element of the set is `≥ 0` (test against the one-word code). -/
theorem nonneg_of_mem_capSet {r : ℝ} (hr : r ∈ capSet) : 0 ≤ r := by
  obtain ⟨N, hN, h⟩ := hr
  have := h N le_rfl {fun _ => 0} (Finset.singleton_nonempty _) (by
    intro x hx y hy _ _ hxy _ _
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy)
  simpa [log2] using this

theorem capSet_bddBelow : BddBelow capSet := ⟨0, fun _ hr => nonneg_of_mem_capSet hr⟩

/-- `0 ≤ zeroErrorList2Cap32`. -/
theorem zeroErrorList2Cap32_nonneg : 0 ≤ zeroErrorList2Cap32 :=
  le_csInf capSet_nonempty fun _ hr => nonneg_of_mem_capSet hr

/-- **Elias's upper bound**: `zeroErrorList2Cap32 ≤ log₂(3/2)`. -/
theorem zeroErrorList2Cap32_le : zeroErrorList2Cap32 ≤ log2 ((3 : ℝ) / 2) :=
  le_of_forall_pos_le_add fun _ hε => csInf_le capSet_bddBelow (add_mem_capSet hε)

/-- Summary: `0 ≤ zeroErrorList2Cap32 ≤ log₂(3/2)`. -/
theorem known_bounds : 0 ≤ zeroErrorList2Cap32 ∧ zeroErrorList2Cap32 ≤ log2 ((3 : ℝ) / 2) :=
  ⟨zeroErrorList2Cap32_nonneg, zeroErrorList2Cap32_le⟩

/-! ### Regression: known small values `T(1) = 3`, `T(2) = 4`, `T(3) = 6` -/

/-- Decidability of `IsTrifferentCode` (built in stages to keep instance search shallow). -/
@[instance_reducible] def decIsTrifferentCode (n : ℕ) (C : Finset (Fin n → Fin 3)) :
    Decidable (IsTrifferentCode n C) := by
  unfold IsTrifferentCode
  have : ∀ x y : Fin n → Fin 3, Decidable (∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
      ∃ i : Fin n, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i) := fun x y => inferInstance
  have : ∀ x : Fin n → Fin 3, Decidable (∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
      ∃ i : Fin n, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i) := fun x => inferInstance
  infer_instance

attribute [local instance] decIsTrifferentCode

/-- **Regression**: `T(1) = 3` (all three symbols form a trifferent code of length `1`). -/
theorem regression_T1 :
    (∃ C : Finset (Fin 1 → Fin 3), IsTrifferentCode 1 C ∧ C.card = 3) ∧
      ∀ C : Finset (Fin 1 → Fin 3), IsTrifferentCode 1 C → C.card ≤ 3 := by
  refine ⟨⟨{![0], ![1], ![2]}, by decide, by decide⟩, fun C hC => ?_⟩
  have := card_le_of_isTrifferentCode 1 C hC
  omega

/-- **Regression**: `T(2) = 4`, e.g. `{00, 01, 12, 22}`. -/
theorem regression_T2 :
    (∃ C : Finset (Fin 2 → Fin 3), IsTrifferentCode 2 C ∧ C.card = 4) ∧
      ∀ C : Finset (Fin 2 → Fin 3), IsTrifferentCode 2 C → C.card ≤ 4 := by
  refine ⟨⟨{![0, 0], ![0, 1], ![1, 2], ![2, 2]}, by decide,
    by decide⟩, fun C hC => ?_⟩
  have := card_le_of_isTrifferentCode 2 C hC
  omega

/-- **Regression**: `T(3) = 6`, e.g. `{000, 011, 102, 121, 212, 220}`. -/
theorem regression_T3 :
    (∃ C : Finset (Fin 3 → Fin 3), IsTrifferentCode 3 C ∧ C.card = 6) ∧
      ∀ C : Finset (Fin 3 → Fin 3), IsTrifferentCode 3 C → C.card ≤ 6 := by
  refine ⟨⟨{![0, 0, 0], ![0, 1, 1], ![1, 0, 2], ![1, 2, 1], ![2, 1, 2], ![2, 2, 0]},
    by decide, by decide⟩, fun C hC => ?_⟩
  have := card_le_of_isTrifferentCode 3 C hC
  omega

end InfoTheory.Known.Certificates.ListDecodingZeroErrorCapacity
