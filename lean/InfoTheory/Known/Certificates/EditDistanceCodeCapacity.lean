import InfoTheory.Problems.EditDistanceCodeCapacity
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.EditDistanceCodeCapacity`

**Outcome: the definition of `deletionCodeCapacity` is sound.** It takes values in `[0, 1]`,
is antitone in `δ`, equals `1` at `δ = 0`, and equals `0` for `δ ≥ 1/2`. No junk was found.

`deletionCodeCapacity δ` is the `sInf` of eventual upper bounds on
`(1/n) log₂ maxDeletionCodeSize n ⌊δn⌋` (a `limsup`). Both `sSup`/`sInf` layers are checked:
* the `sSup` defining `maxDeletionCodeSize` is over a set that is nonempty and bounded by `2^n`
  (`bddAbove_delCodeSizes`), so it is attained (`exists_delCode_card_eq`), and
  `1 ≤ maxDeletionCodeSize n t ≤ 2^n`;
* the `sInf` set is nonempty (contains `1`) and bounded below by `0` (`capSet_bddBelow`).

Certified:
* `lcsLength_le_left`, `lcsLength_le_right`, `eq_of_lcsLength_eq`, `min_count_le_lcsLength`:
  basic facts about the project's `lcsLength`.
* `maxDeletionCodeSize_zero`: `maxDeletionCodeSize n 0 = 2^n`.
* `maxDeletionCodeSize_le_two`: at most two codewords when `n ≤ 2t + 1`. Proof: two words with
  the same majority symbol have `LCS ≥ ⌈n/2⌉`.
* `deletionCodeCapacity_mem_Icc`: `0 ≤ deletionCodeCapacity δ ≤ 1`.
* `deletionCodeCapacity_antitone`: the capacity is antitone in `δ`.
* `deletionCodeCapacity_of_nonpos`, `deletionCodeCapacity_zero`: `deletionCodeCapacity δ = 1`
  for `δ ≤ 0`.
* `deletionCodeCapacity_of_half_le`: `deletionCodeCapacity δ = 0` for `δ ≥ 1/2`. This is the
  classical trivial zero-rate threshold (Levenshtein 1966; see the survey Mitzenmacher, *A survey
  of results for deletion channels and related synchronization channels*, Probab. Surveys 6
  (2009), and Guruswami–He–Li, *The zero-rate threshold for adversarial bit-deletions is less
  than 1/2*, FOCS 2021, for the improvement to `1/2 - ε₀`).

* `statement_iff_window`: the `Statement` (`∃ δ > √2 - 1` with positive capacity) is
  equivalent to the same claim restricted to the window `(√2 - 1, 1/2)`.
* `sqrt_two_sub_one_lt_half`: that window is nonempty. So the trivial threshold does not
  settle the `Statement`.

Not certified:
* Bukh–Guruswami–Håstad (2017): `deletionCodeCapacity δ > 0` for `δ < √2 - 1`. This needs
  their explicit concatenated construction and an analysis of LCS of random words.
* Guruswami–He–Li (2021): capacity `0` for `δ ≥ 1/2 - ε₀`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.EditDistanceCodeCapacity

open InfoTheory InfoTheory.Known

/-! ### Longest common subsequence -/

theorem lcsLength_le_left (xs ys : List Bool) : lcsLength xs ys ≤ xs.length := by
  induction xs, ys using lcsLength.induct with
  | case1 x => simp [lcsLength]
  | case2 x hx => cases x <;> simp_all [lcsLength]
  | case3 xs b ys ih => simp [lcsLength]; omega
  | case4 a xs b ys hab ih1 ih2 => simp [lcsLength, hab] at ih1 ih2 ⊢; omega

theorem lcsLength_le_right (xs ys : List Bool) : lcsLength xs ys ≤ ys.length := by
  induction xs, ys using lcsLength.induct with
  | case1 x => simp [lcsLength]
  | case2 x hx => cases x <;> simp_all [lcsLength]
  | case3 xs b ys ih => simp [lcsLength]; omega
  | case4 a xs b ys hab ih1 ih2 => simp [lcsLength, hab] at ih1 ih2 ⊢; omega

/-- Equal-length strings with a common subsequence of full length are equal. -/
theorem eq_of_lcsLength_eq (xs ys : List Bool) (hl : xs.length = ys.length)
    (h : lcsLength xs ys = xs.length) : xs = ys := by
  induction xs, ys using lcsLength.induct with
  | case1 x => exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | case2 x hx => simp_all
  | case3 xs b ys ih =>
    simp only [lcsLength, ite_true, List.length_cons] at h hl
    rw [ih (by omega) (by omega)]
  | case4 a xs b ys hab ih1 ih2 =>
    exfalso
    simp only [lcsLength, hab, ite_false, List.length_cons] at h hl
    have h1 := lcsLength_le_left xs (b :: ys)
    have h2 := lcsLength_le_right (a :: xs) ys
    omega

/-- `LCS(x, y) ≥ min(#b in x, #b in y)` for each symbol `b`: `b^min` is a common subsequence. -/
theorem min_count_le_lcsLength (c : Bool) (xs ys : List Bool) :
    min (xs.count c) (ys.count c) ≤ lcsLength xs ys := by
  induction xs, ys using lcsLength.induct with
  | case1 x => simp [lcsLength]
  | case2 x hx => cases x <;> simp_all [lcsLength]
  | case3 xs b ys ih =>
    simp only [lcsLength, ite_true, List.count_cons]
    split_ifs <;> omega
  | case4 a xs b ys hab ih1 ih2 =>
    have hm1 := le_max_left (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys)
    have hm2 := le_max_right (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys)
    have hl : lcsLength (a :: xs) (b :: ys) =
        max (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys) := by simp [lcsLength, hab]
    rw [hl]
    simp only [List.count_cons] at ih1 ih2 ⊢
    cases a <;> cases b <;> cases c <;> simp_all

theorem count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp <;> omega

/-! ### `maxDeletionCodeSize` API -/

/-- The set whose `sSup` defines `maxDeletionCodeSize n t`. -/
def delCodeSizes (n t : ℕ) : Set ℕ :=
  { M : ℕ | ∃ C : Finset (Fin n → Bool),
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → t < deletionDist x y) ∧ C.card = M }

theorem bddAbove_delCodeSizes (n t : ℕ) : BddAbove (delCodeSizes n t) := by
  refine ⟨2 ^ n, ?_⟩
  rintro M ⟨C, -, rfl⟩
  simpa using C.card_le_univ

theorem delCodeSizes_nonempty (n t : ℕ) : (delCodeSizes n t).Nonempty :=
  ⟨0, ∅, by simp, rfl⟩

theorem exists_delCode_card_eq (n t : ℕ) : ∃ C : Finset (Fin n → Bool),
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → t < deletionDist x y) ∧ C.card = maxDeletionCodeSize n t :=
  Nat.sSup_mem (delCodeSizes_nonempty n t) (bddAbove_delCodeSizes n t)

theorem card_le_maxDeletionCodeSize {n t : ℕ} {C : Finset (Fin n → Bool)}
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t < deletionDist x y) :
    C.card ≤ maxDeletionCodeSize n t :=
  le_csSup (bddAbove_delCodeSizes n t) ⟨C, hC, rfl⟩

theorem maxDeletionCodeSize_le_pow (n t : ℕ) : maxDeletionCodeSize n t ≤ 2 ^ n := by
  obtain ⟨C, -, hc⟩ := exists_delCode_card_eq n t
  rw [← hc]; simpa using C.card_le_univ

theorem one_le_maxDeletionCodeSize (n t : ℕ) : 1 ≤ maxDeletionCodeSize n t := by
  have := card_le_maxDeletionCodeSize (n := n) (t := t) (C := {fun _ => false})
    (by
      intro x hx y hy hxy
      simp only [Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy)
  simpa using this

/-- `maxDeletionCodeSize n t` is antitone in `t`. -/
theorem maxDeletionCodeSize_antitone {n t t' : ℕ} (h : t ≤ t') :
    maxDeletionCodeSize n t' ≤ maxDeletionCodeSize n t := by
  obtain ⟨C, hC, hc⟩ := exists_delCode_card_eq n t'
  rw [← hc]
  exact card_le_maxDeletionCodeSize fun x hx y hy hxy => lt_of_le_of_lt h (hC x hx y hy hxy)

/-- With `t = 0` every pair of distinct words is separated: `maxDeletionCodeSize n 0 = 2^n`. -/
theorem maxDeletionCodeSize_zero (n : ℕ) : maxDeletionCodeSize n 0 = 2 ^ n := by
  refine le_antisymm (maxDeletionCodeSize_le_pow n 0) ?_
  have := card_le_maxDeletionCodeSize (n := n) (t := 0)
    (C := (Finset.univ : Finset (Fin n → Bool))) (by
      intro x _ y _ hxy
      unfold deletionDist
      have h1 := lcsLength_le_left (List.ofFn x) (List.ofFn y)
      have h2 : lcsLength (List.ofFn x) (List.ofFn y) ≠ n := by
        intro h
        apply hxy
        apply List.ofFn_injective
        exact eq_of_lcsLength_eq _ _ (by simp) (by simpa using h)
      simp only [List.length_ofFn] at h1
      omega)
  simpa using this

/-- **At most two codewords once `n ≤ 2t + 1`.** Any word has a majority symbol occurring at least
`n/2` times; two words with the same majority symbol have `LCS ≥ ⌈n/2⌉`, hence deletion distance
`≤ ⌊n/2⌋ ≤ t`. So a `t`-deletion-correcting code has at most one word per majority symbol. -/
theorem maxDeletionCodeSize_le_two {n t : ℕ} (h : n ≤ 2 * t + 1) :
    maxDeletionCodeSize n t ≤ 2 := by
  obtain ⟨C, hC, hc⟩ := exists_delCode_card_eq n t
  rw [← hc]
  let maj : (Fin n → Bool) → Bool := fun x => decide (n ≤ 2 * (List.ofFn x).count true)
  have hmaj : ∀ x : Fin n → Bool, n ≤ 2 * (List.ofFn x).count (maj x) := by
    intro x
    have := count_true_add_count_false (List.ofFn x)
    simp only [List.length_ofFn] at this
    by_cases hx : n ≤ 2 * (List.ofFn x).count true
    · simp only [maj, hx, decide_true]
    · simp only [maj, hx, decide_false]; omega
  have hinj : Set.InjOn maj (C : Set (Fin n → Bool)) := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hC x hx y hy hne
    have h2 := min_count_le_lcsLength (maj x) (List.ofFn x) (List.ofFn y)
    have h3 := hmaj x
    have h4 := hmaj y
    rw [← hxy] at h4
    unfold deletionDist at h1
    omega
  have := Finset.card_le_card_of_injOn maj (s := C) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  simpa using this

/-! ### The rate term and the capacity -/

/-- The normalised term `(1/n) log₂ maxDeletionCodeSize n ⌊δn⌋` inside `deletionCodeCapacity`. -/
noncomputable def delTerm (δ : ℝ) (n : ℕ) : ℝ :=
  log2 (maxDeletionCodeSize n (Nat.floor (δ * (n : ℝ))) : ℝ) / (n : ℝ)

/-- The set whose `sInf` is `deletionCodeCapacity δ` (a `limsup`). -/
def capSet (δ : ℝ) : Set ℝ := { r : ℝ | ∃ N : ℕ, ∀ n ≥ N, delTerm δ n ≤ r }

theorem deletionCodeCapacity_eq (δ : ℝ) : deletionCodeCapacity δ = sInf (capSet δ) := rfl

theorem delTerm_nonneg (δ : ℝ) (n : ℕ) : 0 ≤ delTerm δ n := by
  unfold delTerm log2
  have := one_le_maxDeletionCodeSize n (Nat.floor (δ * (n : ℝ)))
  have h0 : 0 ≤ Real.log (maxDeletionCodeSize n (Nat.floor (δ * (n : ℝ))) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast this)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  positivity

/-- `delTerm δ n ≤ log₂ M / n` whenever `maxDeletionCodeSize n ⌊δn⌋ ≤ M`. -/
theorem delTerm_le_of_le {δ : ℝ} {n M : ℕ} (hM : maxDeletionCodeSize n (Nat.floor (δ * n)) ≤ M) :
    delTerm δ n ≤ log2 (M : ℝ) / n := by
  unfold delTerm log2
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 := one_le_maxDeletionCodeSize n (Nat.floor (δ * (n : ℝ)))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply div_le_div_of_nonneg_right _ hl2.le
  exact Real.log_le_log (by exact_mod_cast h1) (by exact_mod_cast hM)

theorem delTerm_le_one (δ : ℝ) (n : ℕ) : delTerm δ n ≤ 1 := by
  refine (delTerm_le_of_le (maxDeletionCodeSize_le_pow n _)).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [log2, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_div_assoc, div_self hl2.ne',
      mul_one, div_self hn'.ne']

theorem capSet_bddBelow (δ : ℝ) : BddBelow (capSet δ) :=
  ⟨0, fun _ ⟨N, hN⟩ => (delTerm_nonneg δ N).trans (hN N le_rfl)⟩

theorem one_mem_capSet (δ : ℝ) : (1 : ℝ) ∈ capSet δ := ⟨0, fun n _ => delTerm_le_one δ n⟩

/-- **The `sInf` is not junk**: `0 ≤ deletionCodeCapacity δ ≤ 1` for every `δ`. -/
theorem deletionCodeCapacity_mem_Icc (δ : ℝ) :
    0 ≤ deletionCodeCapacity δ ∧ deletionCodeCapacity δ ≤ 1 :=
  ⟨le_csInf ⟨1, one_mem_capSet δ⟩ fun _ ⟨N, hN⟩ => (delTerm_nonneg δ N).trans (hN N le_rfl),
    csInf_le (capSet_bddBelow δ) (one_mem_capSet δ)⟩

/-- **Monotonicity**: `deletionCodeCapacity` is antitone in `δ`. -/
theorem deletionCodeCapacity_antitone {δ δ' : ℝ} (h : δ ≤ δ') :
    deletionCodeCapacity δ' ≤ deletionCodeCapacity δ := by
  refine csInf_le_csInf (capSet_bddBelow δ') ⟨1, one_mem_capSet δ⟩ ?_
  rintro r ⟨N, hN⟩
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have ht : Nat.floor (δ * (n : ℝ)) ≤ Nat.floor (δ' * (n : ℝ)) :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n))
  exact delTerm_le_of_le (maxDeletionCodeSize_antitone ht) |>.trans_eq rfl

/-- **Zero deletions**: `deletionCodeCapacity δ = 1` for `δ ≤ 0` (in particular `C(0) = 1`). -/
theorem deletionCodeCapacity_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) : deletionCodeCapacity δ = 1 := by
  have hterm : ∀ n : ℕ, 1 ≤ n → delTerm δ n = 1 := by
    intro n hn
    have hfl : Nat.floor (δ * (n : ℝ)) = 0 :=
      Nat.floor_eq_zero.mpr (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    unfold delTerm log2
    rw [hfl, maxDeletionCodeSize_zero, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
      mul_div_assoc, div_self hl2.ne', mul_one, div_self hn'.ne']
  refine le_antisymm (deletionCodeCapacity_mem_Icc δ).2 ?_
  refine le_csInf ⟨1, one_mem_capSet δ⟩ ?_
  rintro r ⟨N, hN⟩
  have : delTerm δ (max N 1) ≤ r := hN (max N 1) (le_max_left _ _)
  rwa [hterm _ (le_max_right _ _)] at this

theorem deletionCodeCapacity_zero : deletionCodeCapacity 0 = 1 :=
  deletionCodeCapacity_of_nonpos le_rfl

/-- **Trivial zero-rate threshold**: `deletionCodeCapacity δ = 0` for `δ ≥ 1/2`
(codes correcting `⌊n/2⌋` deletions have at most two words). This is the classical upper end of
the zero-rate threshold; Guruswami–He–Li (2021) improved it to `1/2 - ε₀`. -/
theorem deletionCodeCapacity_of_half_le {δ : ℝ} (hδ : 1 / 2 ≤ δ) : deletionCodeCapacity δ = 0 := by
  refine le_antisymm ?_ (deletionCodeCapacity_mem_Icc δ).1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine csInf_le (capSet_bddBelow δ) ⟨N + 1, fun n hn => ?_⟩
  show delTerm δ n ≤ 0 + ε
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht : n ≤ 2 * Nat.floor (δ * (n : ℝ)) + 1 := by
    have h1 : (n : ℝ) / 2 ≤ δ * n := by nlinarith
    have h2 := Nat.lt_floor_add_one (δ * (n : ℝ))
    have h3 : (n : ℝ) < 2 * (Nat.floor (δ * (n : ℝ)) : ℝ) + 2 := by linarith
    have h4 : n < 2 * Nat.floor (δ * (n : ℝ)) + 2 := by exact_mod_cast h3
    omega
  have h := delTerm_le_of_le (maxDeletionCodeSize_le_two ht)
  have hl : log2 ((2 : ℕ) : ℝ) = 1 := by
    rw [log2, Nat.cast_ofNat, div_self (Real.log_pos one_lt_two).ne']
  rw [hl] at h
  have h2 : (1 : ℝ) / n ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hn
  linarith


/-- `√2 - 1 < 1/2`, so the open window `(√2 - 1, 1/2)` is nonempty. -/
theorem sqrt_two_sub_one_lt_half : Real.sqrt 2 - 1 < 1 / 2 := by
  have h : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-- The `Statement` only concerns `δ ∈ (√2 - 1, 1/2)`: capacity vanishes for `δ ≥ 1/2`. -/
theorem statement_iff_window : InfoTheory.Problems.EditDistanceCodeCapacity.Statement ↔
    ∃ δ : ℝ, Real.sqrt 2 - 1 < δ ∧ δ < 1 / 2 ∧ 0 < deletionCodeCapacity δ := by
  constructor
  · rintro ⟨δ, h1, h2⟩
    refine ⟨δ, h1, ?_, h2⟩
    by_contra h
    rw [deletionCodeCapacity_of_half_le (not_lt.mp h)] at h2
    exact lt_irrefl 0 h2
  · rintro ⟨δ, h1, -, h2⟩
    exact ⟨δ, h1, h2⟩

end InfoTheory.Known.Certificates.EditDistanceCodeCapacity
