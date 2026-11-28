import InfoTheory.Problems.RegeneratingCodesExactRepair

/-!
# Certificate for `InfoTheory.Problems.RegeneratingCodesExactRepair`

The frozen statement asks whether, for every `2 ≤ k ≤ d < n`, the Shannon-type (polymatroid)
outer bound `InShannonRepairOuterBound n k d` coincides with the closure of the exact-repair
achievable region `IsExactRepairAchievable n k d` (normalized storage `αBar`, per-helper repair
bandwidth `βBar`, file size normalized to `1`).

Certified here, about the *exact* predicates used in `Statement`:
* `outer_of_one_le` / `achievable_of_one_le` — every point with `αBar ≥ 1`, `βBar ≥ 1`
  (store the whole file at every node, ship the whole node content) lies in **both** sets, so
  neither side of the `↔` is empty (no vacuity);
* **regression (MSR cut-set bound `αBar ≥ B/k`, Dimakis et al. 2010) on both sides:**
  - `outer_one_le_k_mul_alpha` — the polymatroid outer bound forces `1 ≤ k · αBar`
    (subadditivity over a `k`-set of nodes);
  - `achievable_one_le_k_mul_alpha` — every exact-repair code forces `1 ≤ k · αBar`
    (counting: the file is an injective function of `k` node contents);
  - `not_outer_of_small_alpha` / `not_achievable_of_small_alpha` — consequently a point with
    `αBar < 1/k` lies in **neither** set, so both sides are proper subsets of the positive
    quadrant and the `↔` is not trivially true by both sides being everything.

Not certified: the (known) inclusion `IsExactRepairAchievable ⊆ InShannonRepairOuterBound`
(entropic vectors of a code form a polymatroid; needs a compactness/closure argument), the
repair-bandwidth cut-set bounds, Tian's `(4,3,3)` and `(5,4,4)` characterizations, and the
open reverse inclusion. The `Statement` itself is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.RegeneratingCodesExactRepair

open InfoTheory InfoTheory.Problems.RegeneratingCodesExactRepair

private lemma log2_two' : log2 (2 : ℝ) = 1 := div_self (Real.log_pos one_lt_two).ne'

/-! ### The rank-one polymatroid (every node stores the whole file) -/

/-- The rank function of the rank-one uniform matroid on `Fin 1`. -/
noncomputable def rankOne (S : Finset (Fin 1)) : ℝ := if S = ∅ then 0 else 1

theorem rankOne_nonempty {S : Finset (Fin 1)} (hS : S.Nonempty) : rankOne S = 1 := by
  simp [rankOne, hS.ne_empty]

theorem isPolymatroid_rankOne : IsPolymatroid 1 rankOne := by
  refine ⟨by simp [rankOne], ?_, ?_⟩
  · intro S T hST
    rcases S.eq_empty_or_nonempty with rfl | hS
    · unfold rankOne; split_ifs <;> simp_all
    · rw [rankOne_nonempty hS, rankOne_nonempty (hS.mono hST)]
  · intro S T
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [rankOne]
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp [rankOne]
    rw [rankOne_nonempty hS, rankOne_nonempty hT,
      rankOne_nonempty (hS.mono Finset.subset_union_left)]
    unfold rankOne; split_ifs <;> norm_num

/-- Every point with `αBar, βBar ≥ 1` lies in the Shannon outer bound. -/
theorem outer_of_one_le {n k d : ℕ} {αBar βBar : ℝ} (hk : 2 ≤ k) (hkd : k ≤ d) (hdn : d < n)
    (hα : 1 ≤ αBar) (hβ : 1 ≤ βBar) : InShannonRepairOuterBound n k d αBar βBar := by
  have hn : 0 < n := by omega
  refine ⟨by linarith, by linarith, 1, rankOne, fun _ => 0, fun _ _ _ => 0,
    isPolymatroid_rankOne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rankOne_nonempty ⟨0, Finset.mem_image.2 ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  · intro i; rw [rankOne_nonempty (Finset.singleton_nonempty _)]; exact hα
  · intro i H j _ _ _; rw [rankOne_nonempty (Finset.singleton_nonempty _)]; exact hβ
  · intro i H j _ _ _; simp
  · intro i H _ hH
    have hHne : H.Nonempty := Finset.card_pos.1 (by omega)
    rw [rankOne_nonempty (Finset.insert_nonempty _ _), rankOne_nonempty (hHne.image _)]
  · intro S hS
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    rw [rankOne_nonempty (hSne.image _)]

/-- Every point with `αBar, βBar ≥ 1` is exact-repair achievable (uncoded replication). -/
theorem achievable_of_one_le {n k d : ℕ} {αBar βBar : ℝ} (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hα : 1 ≤ αBar) (hβ : 1 ≤ βBar) : IsExactRepairAchievable n k d αBar βBar := by
  refine ⟨by linarith, by linarith, fun ε hε => ⟨2, 2, 2, le_rfl, by norm_num, by norm_num,
    ?_, ?_, fun _ m => m, ?_, ?_⟩⟩
  · push_cast; rw [div_self (by rw [log2_two']; norm_num)]; linarith
  · push_cast; rw [div_self (by rw [log2_two']; norm_num)]; linarith
  · intro S hS m₁ m₂ h
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < S.card by omega)
    exact h i hi
  · intro i H _ hH
    refine ⟨fun _ a => a, fun m₁ m₂ h => ?_⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (show 0 < H.card by omega)
    exact h j hj

/-! ### The MSR cut-set bound `k · αBar ≥ 1` on both sides -/

/-- Subadditivity of a polymatroid over the image of a finset. -/
theorem polymatroid_image_le {N n : ℕ} {h : Finset (Fin N) → ℝ} (hp : IsPolymatroid N h)
    (f : Fin n → Fin N) (S : Finset (Fin n)) :
    h (S.image f) ≤ ∑ i ∈ S, h {f i} := by
  classical
  obtain ⟨h0, hmono, hsub⟩ := hp
  induction S using Finset.induction_on with
  | empty => simp [h0]
  | insert a S ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha, Finset.insert_eq]
    have h1 := hsub {f a} (S.image f)
    have h2 : 0 ≤ h ({f a} ∩ S.image f) := h0 ▸ hmono _ _ (Finset.empty_subset _)
    linarith

theorem outer_one_le_k_mul_alpha {n k d : ℕ} {αBar βBar : ℝ} (hkn : k ≤ n)
    (h : InShannonRepairOuterBound n k d αBar βBar) : 1 ≤ (k : ℝ) * αBar := by
  obtain ⟨-, -, Nvar, hh, nodeIdx, -, hp, -, hstore, -, -, -, hrec⟩ := h
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hkn)
  calc (1 : ℝ) ≤ hh (S.image nodeIdx) := hrec S hS
    _ ≤ ∑ i ∈ S, hh {nodeIdx i} := polymatroid_image_le hp nodeIdx S
    _ ≤ ∑ _i ∈ S, αBar := Finset.sum_le_sum fun i _ => hstore i
    _ = (k : ℝ) * αBar := by rw [Finset.sum_const, hS, nsmul_eq_mul]

theorem achievable_one_le_k_mul_alpha {n k d : ℕ} {αBar βBar : ℝ} (hkn : k ≤ n)
    (h : IsExactRepairAchievable n k d αBar βBar) : 1 ≤ (k : ℝ) * αBar := by
  classical
  obtain ⟨-, -, hcode⟩ := h
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hkn)
  have key : ∀ ε : ℝ, 0 < ε → 1 ≤ (k : ℝ) * (αBar + ε) := by
    intro ε hε
    obtain ⟨M, A, R, hM, hA, -, hAα, -, store, hrec, -⟩ := hcode ε hε
    -- the file is an injective function of the `k` node contents in `S`
    have hinj : Function.Injective (fun m : Fin M => fun i : S => store i.1 m) := by
      intro m₁ m₂ hm
      exact hrec S hS m₁ m₂ fun i hi => congrFun hm ⟨i, hi⟩
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_coe, hS] at hcard
    have hMpos : (0 : ℝ) < log2 (M : ℝ) :=
      div_pos (Real.log_pos (by exact_mod_cast hM)) (Real.log_pos one_lt_two)
    have hlog : log2 (M : ℝ) ≤ (k : ℝ) * log2 (A : ℝ) := by
      have hA' : (0 : ℝ) < A := by exact_mod_cast hA
      have : log2 (M : ℝ) ≤ log2 ((A : ℝ) ^ k) := by
        unfold log2
        exact div_le_div_of_nonneg_right
          (Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hcard))
          (Real.log_pos one_lt_two).le
      unfold log2 at this ⊢
      rwa [Real.log_pow, mul_div_assoc] at this
    have h1 : 1 ≤ (k : ℝ) * (log2 (A : ℝ) / log2 (M : ℝ)) := by
      rw [mul_div_assoc', le_div_iff₀ hMpos, one_mul]; exact hlog
    calc (1 : ℝ) ≤ (k : ℝ) * (log2 (A : ℝ) / log2 (M : ℝ)) := h1
      _ ≤ (k : ℝ) * (αBar + ε) := mul_le_mul_of_nonneg_left hAα (Nat.cast_nonneg k)
  by_contra hlt
  push Not at hlt
  have hkpos : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; have := key 1 one_pos; simp at this; linarith
    · exact_mod_cast hk
  have hε : 0 < (1 - (k : ℝ) * αBar) / (2 * k) := div_pos (by linarith) (by linarith)
  have := key _ hε
  rw [mul_add, mul_div_assoc', show (k : ℝ) * (1 - k * αBar) / (2 * k) = (1 - k * αBar) / 2 by
    field_simp] at this
  linarith

/-- A point with `αBar < 1/k` is outside the Shannon outer bound. -/
theorem not_outer_of_small_alpha {n k d : ℕ} {αBar βBar : ℝ} (hkn : k ≤ n)
    (hα : (k : ℝ) * αBar < 1) : ¬ InShannonRepairOuterBound n k d αBar βBar :=
  fun h => absurd (outer_one_le_k_mul_alpha hkn h) (not_le.2 hα)

/-- A point with `αBar < 1/k` is not exact-repair achievable. -/
theorem not_achievable_of_small_alpha {n k d : ℕ} {αBar βBar : ℝ} (hkn : k ≤ n)
    (hα : (k : ℝ) * αBar < 1) : ¬ IsExactRepairAchievable n k d αBar βBar :=
  fun h => absurd (achievable_one_le_k_mul_alpha hkn h) (not_le.2 hα)

end InfoTheory.Known.Certificates.RegeneratingCodesExactRepair
