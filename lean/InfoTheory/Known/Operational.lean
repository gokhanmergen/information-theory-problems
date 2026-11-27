import InfoTheory.Core
import InfoTheory.Bridge
import InfoTheory.Known.Channels

/-!
# Degenerate-case checks for the multi-user operational definitions

The multi-user capacity regions in `InfoTheory.Core.Channels` are defined operationally
(codes with `M = max 1 ⌊2^{nR}⌋` messages and average error `≤ ε` for all large `n`). This file
machine-checks that these definitions reproduce the textbook answers in degenerate cases, by
reducing them to Shannon's channel coding theorem
(`InfoTheory.Bridge.shannon_channel_coding_theorem`, Cover–Thomas Thm. 7.7.1,
El Gamal–Kim Thm. 3.1). Every check below succeeded; no definition bug was found.

* **Code-shape bridge.** Core's `Nat.max 1 ⌊2^{nR}⌋` is definitionally Bridge's
  `max 1 ⌊2^{nR}⌋`. With one user silenced, the multi-user error expression is exactly
  `dmcAvgError` over the right marginal (`bc_err_single_msg₂`, `relayIgnoringInput_err`, …), so
  `IsBCAchievable W R 0 ↔ IsDmcAchievableRate (marginalFst W) R`
  (`isBCAchievable_zero_right_iff`) and similarly for the IC, the relay channel and the MAC.
* **Broadcast channel** (El Gamal–Kim Ch. 5): the outer bound `C_BC ⊆ [0, C₁] × [0, C₂]`
  (`bcCapacityRegion_subset_Icc_prod_Icc`), the axes `(R₁, 0) ∈ C_BC ↔ 0 ≤ R₁ ≤ C₁`
  (`mk_zero_mem_bcCapacityRegion_iff`), and, for a receiver with a single-symbol output,
  `C_BC = [0, C₁] × {0}` (`bcCapacityRegion_eq_of_unique`).
* **Interference channel without interference** (El Gamal–Kim Ch. 6):
  `icCapacityRegion (W₁ ⊗ W₂) = [0, C(W₁)] × [0, C(W₂)]` (`icCapacityRegion_icProduct`).
* **Relay channel with a useless relay** (El Gamal–Kim Ch. 16): `relayCapacity = C(p(y|x))`
  (`relayCapacity_relayIgnoringInput`, `relayCapacity_useless`), and the cutset bound equals
  the same value (`relayCutsetBound_relayIgnoringInput`).
* **MAC with feedback and a silent user** (El Gamal–Kim Ch. 17):
  `[0, C(V)] × {0} ⊆ C_FB` (`Icc_prod_zero_subset_macFeedbackCapacityRegion`) and
  `C_FB ⊆ [0, ∞) × {0}` (`macFeedbackCapacityRegion_macIgnoringSecond_subset`). This uses the
  normalisation of causal chains (`sum_causal_prod_eq_one`). The missing bound `R₁ ≤ C(V)`
  needs the feedback converse (Cover–Thomas Thm. 7.12.1), which the library does not have yet.

All results assume a nonempty input alphabet where needed. With an empty input alphabet every
operational region is `∅`, while `DMC.capacity = sSup ∅ = 0`. This is a convention mismatch
in a vacuous corner case, not a modelling bug.
-/

open scoped BigOperators

namespace InfoTheory.Known.Operational

open InfoTheory InfoTheory.Bridge

section Marginals

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]

/-- Marginal channel `p(y₁ | x) = ∑_{y₂} p(y₁, y₂ | x)` onto the first output coordinate
    (El Gamal–Kim §5.1: the capacity region of a DM-BC depends only on the marginals). -/
def marginalFst (W : DMC X (A × B)) : DMC X A where
  trans x a := ∑ b, W.trans x (a, b)
  nonneg x a := Finset.sum_nonneg fun b _ => W.nonneg x (a, b)
  sum_one x := by rw [← Fintype.sum_prod_type']; exact W.sum_one x

/-- Marginal channel `p(y₂ | x) = ∑_{y₁} p(y₁, y₂ | x)` onto the second output coordinate
    (El Gamal–Kim §5.1). -/
def marginalSnd (W : DMC X (A × B)) : DMC X B where
  trans x b := ∑ a, W.trans x (a, b)
  nonneg x b := Finset.sum_nonneg fun a _ => W.nonneg x (a, b)
  sum_one x := by rw [Finset.sum_comm, ← Fintype.sum_prod_type']; exact W.sum_one x

/-- Splitting a sum over `n`-tuples of pairs into a double sum over pairs of `n`-tuples
    (Cover–Thomas §7.5). -/
theorem sum_tuple_pair_split {n : ℕ} (F : (Fin n → A × B) → ℝ) :
    ∑ y, F y = ∑ a : Fin n → A, ∑ b : Fin n → B, F (fun i => (a i, b i)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (zipEquiv A B n) (fun p => F (fun i => (p.1 i, p.2 i))) F
    (fun _ => rfl)).symm

/-- The `n`-fold power of the first marginal is the marginal of the `n`-fold power
    (memorylessness; Cover–Thomas §7.5, El Gamal–Kim §3.1). -/
theorem marginalFst_power_trans (W : DMC X (A × B)) {n : ℕ} (x : Fin n → X) (a : Fin n → A) :
    ((marginalFst W).power n).trans x a =
      ∑ b : Fin n → B, (W.power n).trans x (fun i => (a i, b i)) := by
  classical
  simp only [DMC.power, marginalFst]
  exact Fintype.prod_sum (fun i b => W.trans (x i) (a i, b))

/-- The `n`-fold power of the second marginal is the marginal of the `n`-fold power. -/
theorem marginalSnd_power_trans (W : DMC X (A × B)) {n : ℕ} (x : Fin n → X) (b : Fin n → B) :
    ((marginalSnd W).power n).trans x b =
      ∑ a : Fin n → A, (W.power n).trans x (fun i => (a i, b i)) := by
  classical
  simp only [DMC.power, marginalSnd]
  exact Fintype.prod_sum (fun i a => W.trans (x i) (a, b i))

/-- Probability of an event depending only on the first output block, computed through the
    first marginal channel. -/
theorem sum_ite_fst_power (W : DMC X (A × B)) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → A) → Prop) [DecidablePred p] :
    ∑ y : Fin n → A × B, (if p (fun i => (y i).1) then (W.power n).trans x y else 0) =
      ∑ a, if p a then ((marginalFst W).power n).trans x a else 0 := by
  rw [sum_tuple_pair_split]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [marginalFst_power_trans]
  show ∑ b : Fin n → B, (if p a then (W.power n).trans x (fun i => (a i, b i)) else 0) = _
  split_ifs <;> simp

/-- Probability of an event depending only on the second output block, computed through the
    second marginal channel. -/
theorem sum_ite_snd_power (W : DMC X (A × B)) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → B) → Prop) [DecidablePred p] :
    ∑ y : Fin n → A × B, (if p (fun i => (y i).2) then (W.power n).trans x y else 0) =
      ∑ b, if p b then ((marginalSnd W).power n).trans x b else 0 := by
  rw [sum_tuple_pair_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [marginalSnd_power_trans]
  show ∑ a : Fin n → A, (if p b then (W.power n).trans x (fun i => (a i, b i)) else 0) = _
  split_ifs <;> simp

end Marginals

section CodeShape

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- **Closure of the operational rate set** (Cover–Thomas Thm. 7.7.1, El Gamal–Kim Thm. 3.1):
    for a DMC on a nonempty input alphabet, the closure of the set of rates achievable in the
    sense of `IsDmcAchievableRate` is exactly `[0, C]`. -/
theorem closure_dmcAchievable_eq_Icc [Nonempty X] (V : DMC X Y) :
    closure {R | IsDmcAchievableRate V R} = Set.Icc 0 V.capacity := by
  apply le_antisymm
  · refine closure_minimal (fun R hR => ⟨hR.1, shannon_channel_coding_converse V R hR⟩) isClosed_Icc
  · intro R hR
    rcases eq_or_lt_of_le (capacity_nonneg V) with h0 | hpos
    · have hR0 : R = 0 := le_antisymm (h0 ▸ hR.2) hR.1
      subst hR0
      exact subset_closure (isDmcAchievableRate_zero V)
    · have hsub : Set.Ico 0 V.capacity ⊆ {R | IsDmcAchievableRate V R} :=
        fun R hR => shannon_channel_coding_achievability V R hR.1 hR.2
      have h := closure_mono hsub
      rw [closure_Ico hpos.ne] at h
      exact h hR

end CodeShape

section Broadcast

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

private lemma natMax_one_floor_rpow_mul_zero (n : ℕ) :
    Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp

/-- With a single message for receiver 2 (`M₂ = 1`), the DM-BC average error of `IsBCAchievable`
    is exactly the point-to-point average error `dmcAvgError` over receiver 1's marginal channel
    (El Gamal–Kim §5.1). -/
theorem bc_err_single_msg₂ [DecidableEq Y₁] (W : BroadcastChannel X Y₁ Y₂) {n M₁ : ℕ}
    (enc : Fin M₁ → Fin 1 → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin M₁)
    (dec₂ : (Fin n → Y₂) → Fin 1) :
    ((1 : ℝ) / ((M₁ * 1 : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin 1, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
          then (W.power n).trans (enc m₁ m₂) y else 0) =
      dmcAvgError (marginalFst W) n M₁ (fun m => enc m 0) dec₁ := by
  unfold dmcAvgError
  rcases Nat.eq_zero_or_pos M₁ with h | h
  · subst h; simp
  · rw [ite_eq_right h.ne', mul_one]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Fin.sum_univ_one]
    have h2 : ∀ z, ¬ (dec₂ z ≠ 0) := fun z => not_not.mpr (Subsingleton.elim _ _)
    simp only [h2, or_false]
    exact sum_ite_fst_power W (enc m₁ 0) (fun a => dec₁ a ≠ m₁)

/-- With a single message for receiver 1 (`M₁ = 1`), the DM-BC average error is exactly the
    point-to-point average error over receiver 2's marginal channel (El Gamal–Kim §5.1). -/
theorem bc_err_single_msg₁ [DecidableEq Y₂] (W : BroadcastChannel X Y₁ Y₂) {n M₂ : ℕ}
    (enc : Fin 1 → Fin M₂ → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin 1)
    (dec₂ : (Fin n → Y₂) → Fin M₂) :
    ((1 : ℝ) / ((1 * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin 1, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
          then (W.power n).trans (enc m₁ m₂) y else 0) =
      dmcAvgError (marginalSnd W) n M₂ (fun m => enc 0 m) dec₂ := by
  unfold dmcAvgError
  rcases Nat.eq_zero_or_pos M₂ with h | h
  · subst h; simp
  · rw [ite_eq_right h.ne', one_mul]
    congr 1
    rw [Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    have h1 : ∀ z, ¬ (dec₁ z ≠ 0) := fun z => not_not.mpr (Subsingleton.elim _ _)
    simp only [h1, false_or]
    exact sum_ite_snd_power W (enc 0 m₂) (fun b => dec₂ b ≠ m₂)

/-- **Code-shape bridge, BC axis 1** (El Gamal–Kim §5.1, Cover–Thomas §7.5): a rate pair
    `(R₁, 0)` is achievable over a DM-BC in the sense of `IsBCAchievable` iff `R₁` is achievable
    in the sense of `IsDmcAchievableRate` over receiver 1's marginal channel `p(y₁ | x)`. -/
theorem isBCAchievable_zero_right_iff (W : BroadcastChannel X Y₁ Y₂) (R₁ : ℝ) :
    IsBCAchievable W R₁ 0 ↔ IsDmcAchievableRate (marginalFst W) R₁ := by
  classical
  constructor
  · rintro ⟨h0, -, h⟩
    refine ⟨h0, fun δ hδ => ?_⟩
    obtain ⟨N, hN⟩ := h δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have hc := hN n hn
    dsimp only at hc
    rw [natMax_one_floor_rpow_mul_zero] at hc
    obtain ⟨enc, dec₁, dec₂, herr⟩ := hc
    exact ⟨fun m => enc m 0, dec₁, le_of_eq_of_le (bc_err_single_msg₂ W enc dec₁ dec₂).symm herr⟩
  · rintro ⟨h0, h⟩
    refine ⟨h0, le_rfl, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨enc, dec, herr⟩ := hN n hn
    dsimp only
    rw [natMax_one_floor_rpow_mul_zero]
    exact ⟨fun m _ => enc m, dec, fun _ => 0,
      le_of_eq_of_le (bc_err_single_msg₂ W (fun m _ => enc m) dec (fun _ => 0)) herr⟩

/-- **Code-shape bridge, BC axis 2** (El Gamal–Kim §5.1): `(0, R₂)` is `IsBCAchievable` iff
    `R₂` is `IsDmcAchievableRate` over receiver 2's marginal channel `p(y₂ | x)`. -/
theorem isBCAchievable_zero_left_iff (W : BroadcastChannel X Y₁ Y₂) (R₂ : ℝ) :
    IsBCAchievable W 0 R₂ ↔ IsDmcAchievableRate (marginalSnd W) R₂ := by
  classical
  constructor
  · rintro ⟨-, h0, h⟩
    refine ⟨h0, fun δ hδ => ?_⟩
    obtain ⟨N, hN⟩ := h δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have hc := hN n hn
    dsimp only at hc
    rw [natMax_one_floor_rpow_mul_zero] at hc
    obtain ⟨enc, dec₁, dec₂, herr⟩ := hc
    exact ⟨fun m => enc 0 m, dec₂, le_of_eq_of_le (bc_err_single_msg₁ W enc dec₁ dec₂).symm herr⟩
  · rintro ⟨h0, h⟩
    refine ⟨le_rfl, h0, fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨enc, dec, herr⟩ := hN n hn
    dsimp only
    rw [natMax_one_floor_rpow_mul_zero]
    exact ⟨fun _ m => enc m, fun _ => 0, dec,
      le_of_eq_of_le (bc_err_single_msg₁ W (fun _ m => enc m) (fun _ => 0) dec) herr⟩

end Broadcast

section BroadcastDegenerate

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- **Receiver 2 sees nothing**: if `Y₂` has a single symbol, every DM-BC code has average error
    at least `1 - 1/M₂` (receiver 2's decoder is constant, so it guesses `m₂` correctly for only
    one of the `M₂` messages; El Gamal–Kim §5.1, Cover–Thomas §7.5). -/
theorem bc_err_ge_of_unique [Unique Y₂] (W : BroadcastChannel X Y₁ Y₂) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc : Fin M₁ → Fin M₂ → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin M₁)
    (dec₂ : (Fin n → Y₂) → Fin M₂) :
    1 - 1 / (M₂ : ℝ) ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
          then (W.power n).trans (enc m₁ m₂) y else 0) := by
  set c : Fin M₂ := dec₂ default
  have hdec : ∀ z, dec₂ z = c := fun z => congrArg dec₂ (Subsingleton.elim _ _)
  have hinner : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂), (if m₂ = c then (0 : ℝ) else 1) ≤
      ∑ y : Fin n → Y₁ × Y₂,
        (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
        then (W.power n).trans (enc m₁ m₂) y else 0) := by
    intro m₁ m₂
    by_cases hm : m₂ = c
    · rw [ite_eq_left hm]
      exact Finset.sum_nonneg fun y _ => by
        split_ifs
        · exact (W.power n).nonneg _ _
        · exact le_rfl
    · rw [ite_eq_right hm, ← (W.power n).sum_one (enc m₁ m₂)]
      refine le_of_eq (Finset.sum_congr rfl fun y _ => ?_)
      rw [ite_eq_left (Or.inr (by rw [hdec]; exact Ne.symm hm))]
  have hcount : ∑ _m₁ : Fin M₁, ∑ m₂ : Fin M₂, (if m₂ = c then (0 : ℝ) else 1) =
      (M₁ : ℝ) * ((M₂ : ℝ) - 1) := by
    have h1 : ∀ m₂ : Fin M₂, (if m₂ = c then (0 : ℝ) else 1) = 1 - if m₂ = c then 1 else 0 :=
      fun m₂ => by split_ifs <;> norm_num
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hsum := Finset.sum_le_sum fun m₁ (_ : m₁ ∈ Finset.univ) =>
    Finset.sum_le_sum fun m₂ (_ : m₂ ∈ Finset.univ) => hinner m₁ m₂
  rw [hcount] at hsum
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  calc 1 - 1 / (M₂ : ℝ) = ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ((M₁ : ℝ) * ((M₂ : ℝ) - 1)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hpos

/-- **A receiver that sees nothing gets rate 0** (El Gamal–Kim §5.1): if `Y₂` has a single
    symbol, no rate pair with `R₂ > 0` is `IsBCAchievable`. -/
theorem not_isBCAchievable_of_unique [Unique Y₂] (W : BroadcastChannel X Y₁ Y₂) {R₁ R₂ : ℝ}
    (hR₂ : 0 < R₂) : ¬ IsBCAchievable W R₁ R₂ := by
  rintro ⟨-, -, h⟩
  obtain ⟨N, hN⟩ := h (1 / 4) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_ge (1 / R₂)
  have hc := hN (max N K) (le_max_left _ _)
  dsimp only at hc
  obtain ⟨enc, dec₁, dec₂, herr⟩ := hc
  have hnR : 1 ≤ ((max N K : ℕ) : ℝ) * R₂ := by
    have h1 : 1 / R₂ ≤ ((max N K : ℕ) : ℝ) :=
      hK.trans (by exact_mod_cast le_max_right N K)
    rw [div_le_iff₀ hR₂] at h1
    linarith
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (((max N K : ℕ) : ℝ) * R₂) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR
  have hM₂ : 2 ≤ Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N K : ℕ) : ℝ) * R₂))) :=
    le_trans (Nat.le_floor (by exact_mod_cast h2)) (le_max_right _ _)
  have hge := bc_err_ge_of_unique W (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (by omega) enc dec₁ dec₂
  have hinv : (1 : ℝ) / (Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N K : ℕ) : ℝ) * R₂))) : ℕ) ≤
      1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM₂)
  linarith

/-- **Converse slice lemma** (El Gamal–Kim §5.1): from any DM-BC code with average error `≤ δ`
    one can extract, by fixing the best message `m₂`, a point-to-point code for receiver 1's
    marginal channel with the same message count `M₁` and average error `≤ δ`. -/
theorem bc_exists_slice₁ [DecidableEq Y₁] (W : BroadcastChannel X Y₁ Y₂) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc : Fin M₁ → Fin M₂ → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin M₁)
    (dec₂ : (Fin n → Y₂) → Fin M₂) {δ : ℝ}
    (herr : ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
          then (W.power n).trans (enc m₁ m₂) y else 0) ≤ δ) :
    ∃ m₂ : Fin M₂, dmcAvgError (marginalFst W) n M₁ (fun m => enc m m₂) dec₁ ≤ δ := by
  let S : Fin M₁ → Fin M₂ → ℝ := fun m₁ m₂ => ∑ a : Fin n → Y₁,
    if dec₁ a ≠ m₁ then ((marginalFst W).power n).trans (enc m₁ m₂) a else 0
  have hpt : ∀ m₁ m₂, S m₁ m₂ ≤ ∑ y : Fin n → Y₁ × Y₂,
      (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
      then (W.power n).trans (enc m₁ m₂) y else 0) := by
    intro m₁ m₂
    simp only [S]
    rw [← sum_ite_fst_power W (enc m₁ m₂) (fun a => dec₁ a ≠ m₁)]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hA : dec₁ (fun i => (y i).1) ≠ m₁
    · rw [ite_eq_left hA, ite_eq_left (Or.inl hA)]
    · rw [ite_eq_right hA]
      split_ifs
      · exact (W.power n).nonneg _ _
      · exact le_rfl
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have he : ∀ m₂, dmcAvgError (marginalFst W) n M₁ (fun m => enc m m₂) dec₁ =
      (1 / (M₁ : ℝ)) * ∑ m₁, S m₁ m₂ := by
    intro m₂
    unfold dmcAvgError
    simp only [hM₁.ne', ↓reduceIte, S]
  have hsumS : ∑ m₁, ∑ m₂, S m₁ m₂ ≤ (M₁ : ℝ) * M₂ * δ := by
    have h1 := Finset.sum_le_sum fun m₁ (_ : m₁ ∈ Finset.univ) =>
      Finset.sum_le_sum fun m₂ (_ : m₂ ∈ Finset.univ) => hpt m₁ m₂
    have h2 : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := by push_cast; positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h2] at herr
    push_cast at herr
    linarith
  have hsum : ∑ m₂, dmcAvgError (marginalFst W) n M₁ (fun m => enc m m₂) dec₁ ≤
      ∑ _m₂ : Fin M₂, δ := by
    simp only [he, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Finset.sum_comm]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM₁r]
    linarith
  obtain ⟨m₂, -, hm₂⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM₂⟩⟩) hsum
  exact ⟨m₂, hm₂⟩

/-- **Converse slice lemma for receiver 2** (El Gamal–Kim §5.1). -/
theorem bc_exists_slice₂ [DecidableEq Y₂] (W : BroadcastChannel X Y₁ Y₂) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc : Fin M₁ → Fin M₂ → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin M₁)
    (dec₂ : (Fin n → Y₂) → Fin M₂) {δ : ℝ}
    (herr : ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
          then (W.power n).trans (enc m₁ m₂) y else 0) ≤ δ) :
    ∃ m₁ : Fin M₁, dmcAvgError (marginalSnd W) n M₂ (fun m => enc m₁ m) dec₂ ≤ δ := by
  let S : Fin M₁ → Fin M₂ → ℝ := fun m₁ m₂ => ∑ b : Fin n → Y₂,
    if dec₂ b ≠ m₂ then ((marginalSnd W).power n).trans (enc m₁ m₂) b else 0
  have hpt : ∀ m₁ m₂, S m₁ m₂ ≤ ∑ y : Fin n → Y₁ × Y₂,
      (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
      then (W.power n).trans (enc m₁ m₂) y else 0) := by
    intro m₁ m₂
    simp only [S]
    rw [← sum_ite_snd_power W (enc m₁ m₂) (fun b => dec₂ b ≠ m₂)]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hB : dec₂ (fun i => (y i).2) ≠ m₂
    · rw [ite_eq_left hB, ite_eq_left (Or.inr hB)]
    · rw [ite_eq_right hB]
      split_ifs
      · exact (W.power n).nonneg _ _
      · exact le_rfl
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have he : ∀ m₁, dmcAvgError (marginalSnd W) n M₂ (fun m => enc m₁ m) dec₂ =
      (1 / (M₂ : ℝ)) * ∑ m₂, S m₁ m₂ := by
    intro m₁
    unfold dmcAvgError
    simp only [hM₂.ne', ↓reduceIte, S]
  have hsumS : ∑ m₁, ∑ m₂, S m₁ m₂ ≤ (M₁ : ℝ) * M₂ * δ := by
    have h1 := Finset.sum_le_sum fun m₁ (_ : m₁ ∈ Finset.univ) =>
      Finset.sum_le_sum fun m₂ (_ : m₂ ∈ Finset.univ) => hpt m₁ m₂
    have h2 : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := by push_cast; positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h2] at herr
    push_cast at herr
    linarith
  have hsum : ∑ m₁, dmcAvgError (marginalSnd W) n M₂ (fun m => enc m₁ m) dec₂ ≤
      ∑ _m₁ : Fin M₁, δ := by
    simp only [he, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM₂r]
    linarith
  obtain ⟨m₁, -, hm₁⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM₁⟩⟩) hsum
  exact ⟨m₁, hm₁⟩

end BroadcastDegenerate

section BroadcastRegion

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

private lemma natMax_one_pos (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- **Single-user converse for a DM-BC, receiver 1** (El Gamal–Kim §5.1, via the slice lemma):
    if `(R₁, R₂)` is `IsBCAchievable`, then `R₁` is `IsDmcAchievableRate` over the marginal
    `p(y₁ | x)`, hence `R₁ ≤ C(p(y₁ | x))` by the channel coding theorem. -/
theorem isDmcAchievableRate_marginalFst_of_isBCAchievable (W : BroadcastChannel X Y₁ Y₂)
    {R₁ R₂ : ℝ} (h : IsBCAchievable W R₁ R₂) : IsDmcAchievableRate (marginalFst W) R₁ := by
  classical
  obtain ⟨h1, -, h⟩ := h
  refine ⟨h1, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hc := hN n hn
  dsimp only at hc
  obtain ⟨enc, dec₁, dec₂, herr⟩ := hc
  obtain ⟨m₂, hm₂⟩ := bc_exists_slice₁ W (natMax_one_pos _) (natMax_one_pos _) enc dec₁ dec₂ herr
  exact ⟨fun m => enc m m₂, dec₁, hm₂⟩

/-- **Single-user converse for a DM-BC, receiver 2** (El Gamal–Kim §5.1). -/
theorem isDmcAchievableRate_marginalSnd_of_isBCAchievable (W : BroadcastChannel X Y₁ Y₂)
    {R₁ R₂ : ℝ} (h : IsBCAchievable W R₁ R₂) : IsDmcAchievableRate (marginalSnd W) R₂ := by
  classical
  obtain ⟨-, h2, h⟩ := h
  refine ⟨h2, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hc := hN n hn
  dsimp only at hc
  obtain ⟨enc, dec₁, dec₂, herr⟩ := hc
  obtain ⟨m₁, hm₁⟩ := bc_exists_slice₂ W (natMax_one_pos _) (natMax_one_pos _) enc dec₁ dec₂ herr
  exact ⟨fun m => enc m₁ m, dec₂, hm₁⟩

/-- **Trivial outer bound for the DM-BC** (El Gamal–Kim §5.1, eq. (5.1)):
    `C_BC ⊆ [0, C₁] × [0, C₂]`, where `Cⱼ` is the capacity of the marginal `p(yⱼ | x)`. -/
theorem bcCapacityRegion_subset_Icc_prod_Icc (W : BroadcastChannel X Y₁ Y₂) :
    bcCapacityRegion W ⊆
      Set.Icc 0 (marginalFst W).capacity ×ˢ Set.Icc 0 (marginalSnd W).capacity := by
  refine closure_minimal (fun p hp => ?_) (isClosed_Icc.prod isClosed_Icc)
  have h1 := isDmcAchievableRate_marginalFst_of_isBCAchievable W hp
  have h2 := isDmcAchievableRate_marginalSnd_of_isBCAchievable W hp
  exact ⟨⟨h1.1, shannon_channel_coding_converse _ _ h1⟩,
    ⟨h2.1, shannon_channel_coding_converse _ _ h2⟩⟩

/-- **Axis achievability for the DM-BC** (El Gamal–Kim §5.1): sending only to receiver 1
    achieves `[0, C₁] × {0}`. -/
theorem Icc_prod_zero_subset_bcCapacityRegion [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    Set.Icc 0 (marginalFst W).capacity ×ˢ {0} ⊆ bcCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_mono fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp2
  show IsBCAchievable W p.1 p.2
  rw [hp2]
  exact (isBCAchievable_zero_right_iff W p.1).mpr hp1

/-- **Axis achievability for the DM-BC, receiver 2** (El Gamal–Kim §5.1). -/
theorem zero_prod_Icc_subset_bcCapacityRegion [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    {0} ×ˢ Set.Icc 0 (marginalSnd W).capacity ⊆ bcCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_mono fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp1
  show IsBCAchievable W p.1 p.2
  rw [hp1]
  exact (isBCAchievable_zero_left_iff W p.2).mpr hp2

/-- **Degenerate check: the axes of the DM-BC capacity region** (El Gamal–Kim §5.1):
    for every DM-BC on a nonempty input alphabet, `(R₁, 0) ∈ C_BC ↔ 0 ≤ R₁ ≤ C(p(y₁ | x))`. -/
theorem mk_zero_mem_bcCapacityRegion_iff [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) (R₁ : ℝ) :
    (R₁, 0) ∈ bcCapacityRegion W ↔ 0 ≤ R₁ ∧ R₁ ≤ (marginalFst W).capacity := by
  constructor
  · intro h
    exact (bcCapacityRegion_subset_Icc_prod_Icc W h).1
  · intro h
    exact Icc_prod_zero_subset_bcCapacityRegion W ⟨h, rfl⟩

/-- **Degenerate check: the axes of the DM-BC capacity region, receiver 2** (El Gamal–Kim §5.1). -/
theorem zero_mk_mem_bcCapacityRegion_iff [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) (R₂ : ℝ) :
    (0, R₂) ∈ bcCapacityRegion W ↔ 0 ≤ R₂ ∧ R₂ ≤ (marginalSnd W).capacity := by
  constructor
  · intro h
    exact (bcCapacityRegion_subset_Icc_prod_Icc W h).2
  · intro h
    exact zero_prod_Icc_subset_bcCapacityRegion W ⟨rfl, h⟩

/-- **Degenerate check: BC with a useless second receiver** (El Gamal–Kim §5.1; Cover–Thomas
    Thm. 7.7.1): if receiver 2's output alphabet has a single symbol, the DM-BC capacity region
    is exactly `[0, C(p(y₁ | x))] × {0}`. -/
theorem bcCapacityRegion_eq_of_unique [Unique Y₂] [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    bcCapacityRegion W = Set.Icc 0 (marginalFst W).capacity ×ˢ {0} := by
  refine le_antisymm (fun p hp => ?_) (Icc_prod_zero_subset_bcCapacityRegion W)
  have hset : {p : ℝ × ℝ | IsBCAchievable W p.1 p.2} ⊆ Set.univ ×ˢ {0} := by
    rintro ⟨R₁, R₂⟩ h
    refine ⟨trivial, ?_⟩
    rcases eq_or_lt_of_le h.2.1 with h0 | hpos
    · exact h0.symm
    · exact absurd h (not_isBCAchievable_of_unique W hpos)
  have hp2 : p ∈ Set.univ ×ˢ ({0} : Set ℝ) :=
    closure_minimal hset (isClosed_univ.prod isClosed_singleton) hp
  have hp1 := (bcCapacityRegion_subset_Icc_prod_Icc W hp).1
  exact ⟨hp1, hp2.2⟩

end BroadcastRegion

section Interference

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]

/-- Interference channel **without interference**: two independent DMCs side by side,
    `p(y₁, y₂ | x₁, x₂) = W₁(y₁ | x₁) W₂(y₂ | x₂)` (El Gamal–Kim §6.1). -/
def icProduct (W₁ : DMC X₁ Y₁) (W₂ : DMC X₂ Y₂) : InterferenceChannel X₁ X₂ Y₁ Y₂ where
  trans x y := W₁.trans x.1 y.1 * W₂.trans x.2 y.2
  nonneg x y := mul_nonneg (W₁.nonneg _ _) (W₂.nonneg _ _)
  sum_one x := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, W₂.sum_one, mul_one, W₁.sum_one]

/-- Receiver 1's marginal of `W₁ ⊗ W₂` is `W₁`, blockwise (El Gamal–Kim §6.1). -/
theorem icProduct_marginalFst_power (W₁ : DMC X₁ Y₁) (W₂ : DMC X₂ Y₂) {n : ℕ}
    (u : Fin n → X₁) (v : Fin n → X₂) (c : Fin n → Y₁) :
    ((marginalFst (icProduct W₁ W₂)).power n).trans (fun i => (u i, v i)) c =
      (W₁.power n).trans u c := by
  simp only [DMC.power, marginalFst, icProduct, ← Finset.mul_sum, W₂.sum_one, mul_one]

/-- Receiver 2's marginal of `W₁ ⊗ W₂` is `W₂`, blockwise (El Gamal–Kim §6.1). -/
theorem icProduct_marginalSnd_power (W₁ : DMC X₁ Y₁) (W₂ : DMC X₂ Y₂) {n : ℕ}
    (u : Fin n → X₁) (v : Fin n → X₂) (d : Fin n → Y₂) :
    ((marginalSnd (icProduct W₁ W₂)).power n).trans (fun i => (u i, v i)) d =
      (W₂.power n).trans v d := by
  simp only [DMC.power, marginalSnd, icProduct, ← Finset.sum_mul, W₁.sum_one, one_mul]

private lemma ite_le_ite_or_left {P Q : Prop} [Decidable P] [Decidable Q] {w : ℝ} (hw : 0 ≤ w) :
    (if P then w else 0) ≤ (if P ∨ Q then w else 0) := by
  by_cases hP : P
  · rw [ite_eq_left hP, ite_eq_left (Or.inl hP)]
  · rw [ite_eq_right hP]; split_ifs <;> simp [hw]

private lemma ite_le_ite_or_right {P Q : Prop} [Decidable P] [Decidable Q] {w : ℝ} (hw : 0 ≤ w) :
    (if Q then w else 0) ≤ (if P ∨ Q then w else 0) := by
  by_cases hQ : Q
  · rw [ite_eq_left hQ, ite_eq_left (Or.inr hQ)]
  · rw [ite_eq_right hQ]; split_ifs <;> simp [hw]

private lemma ite_or_le_add {P Q : Prop} [Decidable P] [Decidable Q] {w : ℝ} (hw : 0 ≤ w) :
    (if P ∨ Q then w else 0) ≤ (if P then w else 0) + (if Q then w else 0) := by
  split_ifs <;> simp_all

private lemma avg_double_const_right {M₁ M₂ : ℕ} (hM₂ : 0 < M₂) (f : Fin M₁ → ℝ) :
    (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) * ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, f m₁ =
      (1 / (M₁ : ℝ)) * ∑ m₁, f m₁ := by
  have hM₂r : (M₂ : ℝ) ≠ 0 := by exact_mod_cast hM₂.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  push_cast
  rcases Nat.eq_zero_or_pos M₁ with h | h
  · subst h; simp
  · have hM₁r : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

private lemma avg_double_const_left {M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (f : Fin M₂ → ℝ) :
    (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) * ∑ _m₁ : Fin M₁, ∑ m₂ : Fin M₂, f m₂ =
      (1 / (M₂ : ℝ)) * ∑ m₂, f m₂ := by
  have hM₁r : (M₁ : ℝ) ≠ 0 := by exact_mod_cast hM₁.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rcases Nat.eq_zero_or_pos M₂ with h | h
  · subst h; simp
  · have hM₂r : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

/-- **Error sandwich for the interference-free IC** (El Gamal–Kim §6.1; union bound):
    for product codes over `W₁ ⊗ W₂`, the IC average error `P_e` satisfies
    `max(P_e(W₁), P_e(W₂)) ≤ P_e ≤ P_e(W₁) + P_e(W₂)`. -/
theorem icProduct_err_bounds [DecidableEq Y₁] [DecidableEq Y₂]
    (W₁ : DMC X₁ Y₁) (W₂ : DMC X₂ Y₂) {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
    (dec₁ : (Fin n → Y₁) → Fin M₁) (dec₂ : (Fin n → Y₂) → Fin M₂) :
    let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
        then ((icProduct W₁ W₂).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0
    dmcAvgError W₁ n M₁ enc₁ dec₁ ≤ err ∧ dmcAvgError W₂ n M₂ enc₂ dec₂ ≤ err ∧
      err ≤ dmcAvgError W₁ n M₁ enc₁ dec₁ + dmcAvgError W₂ n M₂ enc₂ dec₂ := by
  intro err
  let W := icProduct W₁ W₂
  let S₁ : Fin M₁ → ℝ := fun m₁ => ∑ c : Fin n → Y₁,
    if dec₁ c ≠ m₁ then (W₁.power n).trans (enc₁ m₁) c else 0
  let S₂ : Fin M₂ → ℝ := fun m₂ => ∑ d : Fin n → Y₂,
    if dec₂ d ≠ m₂ then (W₂.power n).trans (enc₂ m₂) d else 0
  let T : Fin M₁ → Fin M₂ → ℝ := fun m₁ m₂ => ∑ y : Fin n → Y₁ × Y₂,
    if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
    then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0
  have hS₁ : ∀ m₁ m₂, ∑ y : Fin n → Y₁ × Y₂, (if dec₁ (fun i => (y i).1) ≠ m₁
      then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) = S₁ m₁ := by
    intro m₁ m₂
    rw [sum_ite_fst_power W _ (fun c => dec₁ c ≠ m₁)]
    simp only [W, S₁, icProduct_marginalFst_power]
  have hS₂ : ∀ m₁ m₂, ∑ y : Fin n → Y₁ × Y₂, (if dec₂ (fun i => (y i).2) ≠ m₂
      then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) = S₂ m₂ := by
    intro m₁ m₂
    rw [sum_ite_snd_power W _ (fun d => dec₂ d ≠ m₂)]
    simp only [W, S₂, icProduct_marginalSnd_power]
  have hl₁ : ∀ m₁ m₂, S₁ m₁ ≤ T m₁ m₂ := fun m₁ m₂ => by
    rw [← hS₁ m₁ m₂]
    exact Finset.sum_le_sum fun y _ => ite_le_ite_or_left ((W.power n).nonneg _ _)
  have hl₂ : ∀ m₁ m₂, S₂ m₂ ≤ T m₁ m₂ := fun m₁ m₂ => by
    rw [← hS₂ m₁ m₂]
    exact Finset.sum_le_sum fun y _ => ite_le_ite_or_right ((W.power n).nonneg _ _)
  have hu : ∀ m₁ m₂, T m₁ m₂ ≤ S₁ m₁ + S₂ m₂ := fun m₁ m₂ => by
    rw [← hS₁ m₁ m₂, ← hS₂ m₁ m₂, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ => ite_or_le_add ((W.power n).nonneg _ _)
  have herr : err = (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) * ∑ m₁, ∑ m₂, T m₁ m₂ := rfl
  have he₁ : dmcAvgError W₁ n M₁ enc₁ dec₁ =
      (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) * ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, S₁ m₁ := by
    rw [avg_double_const_right hM₂]
    unfold dmcAvgError
    simp only [hM₁.ne', ↓reduceIte, S₁]
  have he₂ : dmcAvgError W₂ n M₂ enc₂ dec₂ =
      (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) * ∑ _m₁ : Fin M₁, ∑ m₂ : Fin M₂, S₂ m₂ := by
    rw [avg_double_const_left hM₁]
    unfold dmcAvgError
    simp only [hM₂.ne', ↓reduceIte, S₂]
  have hc : (0 : ℝ) ≤ (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [he₁, herr]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m₁ _ =>
      Finset.sum_le_sum fun m₂ _ => hl₁ m₁ m₂) hc
  · rw [he₂, herr]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m₁ _ =>
      Finset.sum_le_sum fun m₂ _ => hl₂ m₁ m₂) hc
  · rw [he₁, he₂, herr, ← mul_add, ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m₁ _ => ?_) hc
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun m₂ _ => hu m₁ m₂

private lemma natMax_one_pos' (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- **Code-shape bridge for the interference-free IC** (El Gamal–Kim §6.1): the operational
    achievable set inside `icCapacityRegion (W₁ ⊗ W₂)` is exactly the product of the
    `IsDmcAchievableRate` sets of `W₁` and `W₂`. -/
theorem icCapacityRegion_icProduct_eq_closure (W₁ : DMC X₁ Y₁) (W₂ : DMC X₂ Y₂) :
    icCapacityRegion (icProduct W₁ W₂) =
      closure ({R | IsDmcAchievableRate W₁ R} ×ˢ {R | IsDmcAchievableRate W₂ R}) := by
  classical
  unfold icCapacityRegion
  congr 1
  ext ⟨R₁, R₂⟩
  simp only [Set.mem_ofPred_eq, Set.mem_prod]
  constructor
  · rintro ⟨h1, h2, h⟩
    refine ⟨⟨h1, fun δ hδ => ?_⟩, ⟨h2, fun δ hδ => ?_⟩⟩
    · obtain ⟨N, hN⟩ := h δ hδ
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨enc₁, enc₂, dec₁, dec₂, herr⟩ := hN n hn
      exact ⟨enc₁, dec₁, le_trans
        (icProduct_err_bounds W₁ W₂ (natMax_one_pos' _) (natMax_one_pos' _)
          enc₁ enc₂ dec₁ dec₂).1 herr⟩
    · obtain ⟨N, hN⟩ := h δ hδ
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨enc₁, enc₂, dec₁, dec₂, herr⟩ := hN n hn
      exact ⟨enc₂, dec₂, le_trans
        (icProduct_err_bounds W₁ W₂ (natMax_one_pos' _) (natMax_one_pos' _)
          enc₁ enc₂ dec₁ dec₂).2.1 herr⟩
  · rintro ⟨⟨h1, hA⟩, ⟨h2, hB⟩⟩
    refine ⟨h1, h2, fun ε hε => ?_⟩
    obtain ⟨N₁, hN₁⟩ := hA (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := hB (ε / 2) (by linarith)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    obtain ⟨enc₁, dec₁, he₁⟩ := hN₁ n (le_trans (le_max_left _ _) hn)
    obtain ⟨enc₂, dec₂, he₂⟩ := hN₂ n (le_trans (le_max_right _ _) hn)
    refine ⟨enc₁, enc₂, dec₁, dec₂, ?_⟩
    have hb := (icProduct_err_bounds W₁ W₂ (natMax_one_pos' _) (natMax_one_pos' _)
      enc₁ enc₂ dec₁ dec₂).2.2
    exact le_trans hb (by linarith)

/-- **Degenerate check: interference channel without interference** (El Gamal–Kim §6.1;
    Cover–Thomas Thm. 7.7.1): `icCapacityRegion (W₁ ⊗ W₂) = [0, C(W₁)] × [0, C(W₂)]`. -/
theorem icCapacityRegion_icProduct [Nonempty X₁] [Nonempty X₂]
    (W₁ : DMC X₁ Y₁) (W₂ : DMC X₂ Y₂) :
    icCapacityRegion (icProduct W₁ W₂) = Set.Icc 0 W₁.capacity ×ˢ Set.Icc 0 W₂.capacity := by
  rw [icCapacityRegion_icProduct_eq_closure, closure_prod_eq, closure_dmcAchievable_eq_Icc,
    closure_dmcAchievable_eq_Icc]

end Interference

section Relay

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- A relay channel whose law **ignores the relay input**: `p(y, y_r | x, x_r) = U(y, y_r | x)`
    (the relay can still observe `y_r`, but nothing it sends has any effect;
    El Gamal–Kim §16.1). -/
def relayIgnoringInput (U : DMC X (Y × Yr)) : RelayChannel X Xr Y Yr where
  trans x := U.trans x.1
  nonneg x := U.nonneg x.1
  sum_one x := U.sum_one x.1

/-- With a relay that has no effect, the relay-channel average error of `IsRelayAchievable`
    equals the point-to-point average error over the marginal `p(y | x)`, for every causal
    relay strategy (El Gamal–Kim §16.1). -/
theorem relayIgnoringInput_err [DecidableEq Y] (U : DMC X (Y × Yr)) {n M : ℕ}
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
    (dec : (Fin n → Y) → Fin M) :
    ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
      (if dec y ≠ m then ∏ i : Fin n, (relayIgnoringInput (Xr := Xr) U).trans
        (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i) else 0) =
      dmcAvgError (marginalFst U) n M enc dec := by
  unfold dmcAvgError
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · rw [ite_eq_right h.ne']
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [marginalFst_power_trans]
    split_ifs
    · rfl
    · simp

/-- **Code-shape bridge for a useless relay** (El Gamal–Kim §16.1): `R` is `IsRelayAchievable`
    over a relay channel that ignores the relay input iff `R` is `IsDmcAchievableRate` over the
    marginal `p(y | x)`. -/
theorem isRelayAchievable_relayIgnoringInput_iff [Nonempty Xr] (U : DMC X (Y × Yr)) (R : ℝ) :
    IsRelayAchievable (relayIgnoringInput (Xr := Xr) U) R ↔
      IsDmcAchievableRate (marginalFst U) R := by
  classical
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun δ hδ => ?_⟩
    obtain ⟨N, hN⟩ := h δ hδ
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨enc, relay, dec, herr⟩ := hN n hn
    exact ⟨enc, dec, le_of_eq_of_le (relayIgnoringInput_err U enc relay dec).symm herr⟩
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun δ hδ => ?_⟩
    obtain ⟨N, hN⟩ := h δ hδ
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨enc, dec, herr⟩ := hN n hn
    let relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr := fun _ _ => Classical.arbitrary Xr
    exact ⟨enc, relay, dec, le_of_eq_of_le (relayIgnoringInput_err U enc relay dec) herr⟩

/-- **Degenerate check: relay channel with a useless relay** (El Gamal–Kim §16.1;
    Cover–Thomas Thm. 7.7.1): if the channel law ignores the relay input, then
    `relayCapacity = C(p(y | x))`. -/
theorem relayCapacity_relayIgnoringInput [Nonempty Xr] (U : DMC X (Y × Yr)) :
    relayCapacity (relayIgnoringInput (Xr := Xr) U) = (marginalFst U).capacity := by
  rw [← shannon_channel_coding_theorem]
  unfold relayCapacity dmcOperationalCapacity
  congr 1
  ext R
  exact isRelayAchievable_relayIgnoringInput_iff U R

/-- A DMC `V` viewed as a channel with an extra constant (single-symbol) second output
    (El Gamal–Kim §16.1). -/
def withConstObs (V : DMC X Y) : DMC X (Y × Unit) where
  trans x y := V.trans x y.1
  nonneg x y := V.nonneg x y.1
  sum_one x := by rw [Fintype.sum_prod_type]; simpa using V.sum_one x

/-- Dropping a constant output recovers the original channel (Cover–Thomas §7.1). -/
theorem marginalFst_withConstObs (V : DMC X Y) : marginalFst (withConstObs V) = V := by
  cases V
  simp [marginalFst, withConstObs]

/-- **Degenerate check: relay that sees nothing and whose input does nothing**
    (El Gamal–Kim §16.1): for `p(y, y_r | x, x_r) = V(y | x) · 1{y_r = ()}`,
    `relayCapacity = C(V)`. -/
theorem relayCapacity_useless [Nonempty Xr] (V : DMC X Y) :
    relayCapacity (relayIgnoringInput (Xr := Xr) (withConstObs V)) = V.capacity := by
  rw [relayCapacity_relayIgnoringInput, marginalFst_withConstObs]

end Relay

section ProbDistHelpers

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Two finite distributions with the same pmf are equal (Cover–Thomas §2.1). -/
theorem probDist_eq_of_pmf {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q
  congr
  funext a
  exact h a

/-- Entropy is invariant under injective relabelling (Cover–Thomas §2.1, Problem 2.4). -/
theorem shannonEntropy_map_of_injective (f : α → β) (hf : Function.Injective f)
    (P : ProbDist α) : shannonEntropy (P.map f) = shannonEntropy P := by
  classical
  have himg : ∀ a, (P.map f).pmf (f a) = P.pmf a := by
    intro a
    simp only [ProbDist.map]
    rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ hne
      simp [hf.ne hne]
    · simp
  have hout : ∀ b ∉ Finset.univ.image f, (P.map f).pmf b = 0 := by
    intro b hb
    simp only [ProbDist.map]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hne : f a ≠ b := fun h => hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, h⟩)
    simp [hne]
  unfold shannonEntropy
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
    (fun b _ hb => by rw [hout b hb, negPLogP_zero])]
  rw [Finset.sum_image (fun a _ a' _ h => hf h)]
  simp only [himg]

/-- The entropy of a deterministic (constant) random variable is `0` (Cover–Thomas §2.1). -/
theorem shannonEntropy_map_const (P : ProbDist α) (c : β) :
    shannonEntropy (P.map (fun _ => c)) = 0 := by
  classical
  unfold shannonEntropy
  refine Finset.sum_eq_zero fun b _ => ?_
  simp only [ProbDist.map]
  by_cases h : c = b
  · simp [h, P.sum_one, negPLogP, log2]
  · simp [h, negPLogP]

/-- The pushforward along `Prod.fst` is the first marginal (Cover–Thomas §2.2). -/
theorem map_fst_eq_fst (R : ProbDist (α × β)) : R.map Prod.fst = R.fst := by
  classical
  refine probDist_eq_of_pmf fun a => ?_
  simp only [ProbDist.map, ProbDist.fst]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ h; simp [h]
  · simp

/-- The pushforward along `Prod.snd` is the second marginal (Cover–Thomas §2.2). -/
theorem map_snd_eq_snd (R : ProbDist (α × β)) : R.map Prod.snd = R.snd := by
  classical
  refine probDist_eq_of_pmf fun b => ?_
  simp only [ProbDist.map, ProbDist.snd]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]
  · simp
  · intro b' _ h; simp [h]
  · simp

/-- Pushforwards along maps that agree on the support coincide. -/
theorem map_congr_of_support (P : ProbDist α) {f g : α → β}
    (h : ∀ a, P.pmf a ≠ 0 → f a = g a) : P.map f = P.map g := by
  classical
  refine probDist_eq_of_pmf fun b => ?_
  simp only [ProbDist.map]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : P.pmf a = 0
  · simp [ha]
  · rw [h a ha]

/-- **Conditioning on a constant** (Cover–Thomas §2.5): if `Z ≡ c`, then
    `I(X; Y | Z) = I(X; Y)`. -/
theorem condMutualInfo_map_const (R : ProbDist (α × β)) (c : γ) :
    condMutualInfo (R.map (fun ab => (ab.1, ab.2, c))) = mutualInfo R := by
  have hinj : Function.Injective (fun ab : α × β => (ab.1, ab.2, c)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have h1 : (R.map (fun ab => (ab.1, ab.2, c))).map (fun t => (t.1, t.2.2)) =
      (R.map Prod.fst).map (fun a => (a, c)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h2 : (R.map (fun ab => (ab.1, ab.2, c))).map (fun t => (t.2.1, t.2.2)) =
      (R.map Prod.snd).map (fun b => (b, c)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h3 : (R.map (fun ab => (ab.1, ab.2, c))).map (fun t => t.2.2) =
      R.map (fun _ => c) := by
    rw [map_comp_eq]; rfl
  have hc1 : Function.Injective (fun a : α => (a, c)) := fun x y h => (Prod.mk.inj h).1
  have hc2 : Function.Injective (fun b : β => (b, c)) := fun x y h => (Prod.mk.inj h).1
  unfold condMutualInfo
  dsimp only
  rw [h1, h2, h3, shannonEntropy_map_of_injective _ hc1, shannonEntropy_map_of_injective _ hc2,
    shannonEntropy_map_of_injective _ hinj, shannonEntropy_map_const, map_fst_eq_fst,
    map_snd_eq_snd]
  unfold mutualInfo
  ring

/-- Point mass `δ_c`, i.e. a deterministic random variable (Cover–Thomas §2.1). -/
def diracDist [DecidableEq α] (c : α) : ProbDist α where
  pmf a := if a = c then 1 else 0
  nonneg a := by split_ifs <;> norm_num
  sum_one := by simp

/-- The first marginal of `P ⊗ δ_c` is `P` (Cover–Thomas §2.2). -/
theorem prod_dirac_map_fst [DecidableEq β] (P : ProbDist α) (c : β) :
    (P.prod (diracDist c)).map Prod.fst = P := by
  rw [map_fst_eq_fst]
  refine probDist_eq_of_pmf fun a => ?_
  simp [ProbDist.fst, ProbDist.prod, diracDist]

end ProbDistHelpers

section RelayCutset

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- If the relay input has no effect, the law of `((X, X_r), Y)` is the input law composed with
    the marginal `p(y | x)` (El Gamal–Kim §16.1). -/
theorem relayIgnoringInput_joint_map_out (U : DMC X (Y × Yr)) (P : ProbDist (X × Xr)) :
    ((relayIgnoringInput (Xr := Xr) U).joint P).map (fun z => (z.1, z.2.1)) =
      (dmcPrecomp (marginalFst U) Prod.fst).joint P := by
  classical
  refine probDist_eq_of_pmf fun ⟨x', y⟩ => ?_
  simp only [ProbDist.map, DMC.joint, dmcPrecomp, marginalFst, relayIgnoringInput]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x']
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
    · simp [Finset.mul_sum]
    · intro y' _ h; simp [h]
    · simp
  · intro x'' _ h; simp [h]
  · simp

/-- Relabelling the input through `f` commutes with forming the joint law
    (Cover–Thomas §2.8). -/
theorem dmcPrecomp_joint_map {α : Type*} [Fintype α] (V : DMC X Y) (f : α → X)
    (P : ProbDist α) :
    ((dmcPrecomp V f).joint P).map (Prod.map f id) = V.joint (P.map f) := by
  classical
  refine probDist_eq_of_pmf fun ⟨x, y⟩ => ?_
  simp only [ProbDist.map, DMC.joint, dmcPrecomp, Prod.map, id]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single y]
  · by_cases h : f a = x
    · subst h; simp
    · simp [h]
  · intro y' _ h; simp [h]
  · simp

/-- **Degenerate check: cutset bound with a useless relay** (Cover–El Gamal 1979;
    El Gamal–Kim Thm. 16.1): if the relay channel law ignores the relay input, the cutset bound
    `max_{p(x, x_r)} min{I(X; Y, Y_r | X_r), I(X, X_r; Y)}` equals `C(p(y | x))`, so it agrees
    with `relayCapacity` (see `relayCapacity_relayIgnoringInput`). -/
theorem relayCutsetBound_relayIgnoringInput [Nonempty X] [Nonempty Xr] (U : DMC X (Y × Yr)) :
    relayCutsetBound (relayIgnoringInput (Xr := Xr) U) = (marginalFst U).capacity := by
  classical
  set W : RelayChannel X Xr Y Yr := relayIgnoringInput (Xr := Xr) U with hW
  set V : DMC X Y := marginalFst U with hV
  set S : Set ℝ := {r : ℝ | ∃ P : ProbDist (X × Xr),
    r = min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))))
      (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))))} with hS
  have hcut : relayCutsetBound W = sSup S := rfl
  have hB : ∀ P : ProbDist (X × Xr),
      mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) = V.mutualInfo (P.map Prod.fst) := by
    intro P
    rw [hW, relayIgnoringInput_joint_map_out, dmcPrecomp_mutualInfo_eq]
    rfl
  have hbdd : BddAbove S := ⟨V.capacity, by
    rintro r ⟨P, rfl⟩
    exact (min_le_right _ _).trans ((hB P).symm ▸ mutualInfo_le_capacity V _)⟩
  have hne : S.Nonempty := ⟨_, ProbDist.uniform, rfl⟩
  rw [hcut]
  apply le_antisymm
  · refine csSup_le hne fun r ⟨P, hr⟩ => ?_
    rw [hr]
    exact (min_le_right _ _).trans ((hB P).symm ▸ mutualInfo_le_capacity V _)
  · refine csSup_le (capacity_set_nonempty V) fun r ⟨PX, hr⟩ => ?_
    rw [hr]
    let xr₀ : Xr := Classical.arbitrary Xr
    let P : ProbDist (X × Xr) := PX.prod (diracDist xr₀)
    let J := W.joint P
    have hPX : P.map Prod.fst = PX := prod_dirac_map_fst PX xr₀
    have hBP : mutualInfo (J.map (fun z => (z.1, z.2.1))) = V.mutualInfo PX := by
      rw [hB P, hPX]
    -- the relay input is a.s. the constant `xr₀`
    have hsupp : J.map (fun z => (z.1.1, z.2, z.1.2)) =
        (J.map (fun z => (z.1.1, z.2))).map (fun ab => (ab.1, ab.2, xr₀)) := by
      rw [map_comp_eq]
      refine map_congr_of_support J fun z hz => ?_
      have hz2 : z.1.2 = xr₀ := by
        by_contra hne
        apply hz
        simp [J, DMC.joint, P, ProbDist.prod, diracDist, hne]
      simp [hz2]
    have hA : V.mutualInfo PX ≤
        condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) := by
      rw [hsupp, condMutualInfo_map_const]
      refine le_trans (le_of_eq ?_) (mutualInfo_map_right_le _ Prod.fst)
      have hmap : (J.map (fun z => (z.1.1, z.2))).map (Prod.map id Prod.fst) =
          (J.map (fun z => (z.1, z.2.1))).map (Prod.map Prod.fst id) := by
        rw [map_comp_eq, map_comp_eq]; rfl
      have hJ : J.map (fun z => (z.1, z.2.1)) = (dmcPrecomp V Prod.fst).joint P :=
        relayIgnoringInput_joint_map_out U P
      rw [hmap, hJ, dmcPrecomp_joint_map]
      show V.mutualInfo PX = V.mutualInfo (P.map Prod.fst)
      rw [hPX]
    have hmem : min (condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))))
        (mutualInfo (J.map (fun z => (z.1, z.2.1)))) ∈ S := ⟨P, rfl⟩
    exact le_trans (le_min hA hBP.ge) (le_csSup hbdd hmem)

end RelayCutset

section MACFeedback

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- A MAC whose output **ignores user 2's input**: `p(y | x₁, x₂) = V(y | x₁)`
    (El Gamal–Kim §4.1, §17.1). -/
def macIgnoringSecond (V : DMC X₁ Y) : MACChannel X₁ X₂ Y where
  trans x := V.trans x.1
  nonneg x := V.nonneg x.1
  sum_one x := V.sum_one x.1

private lemma natMax_one_floor_rpow_mul_zero' (n : ℕ) :
    Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp

/-- **Point-to-point codes are feedback MAC codes** (El Gamal–Kim §17.1): if `R` is
    `IsDmcAchievableRate` over `V`, then `(R, 0)` is `IsMACFeedbackAchievable` over the MAC
    that ignores user 2 (user 1 ignores the feedback). -/
theorem isMACFeedbackAchievable_macIgnoringSecond [Nonempty X₂] (V : DMC X₁ Y) {R : ℝ}
    (h : IsDmcAchievableRate V R) :
    IsMACFeedbackAchievable (macIgnoringSecond (X₂ := X₂) V) R 0 := by
  classical
  refine ⟨h.1, le_rfl, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_one_floor_rpow_mul_zero']
  refine ⟨fun i m _ => enc m i, fun _ _ _ => Classical.arbitrary X₂, fun y => (dec y, 0), ?_⟩
  refine le_of_eq_of_le ?_ herr
  unfold dmcAvgError
  rcases Nat.eq_zero_or_pos (max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))) with h0 | hpos
  · exact absurd h0 (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  · rw [ite_eq_right hpos.ne', mul_one]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hiff : ((dec y, (0 : Fin 1)) ≠ (m₁, 0)) ↔ dec y ≠ m₁ := by
      simp [Prod.ext_iff]
    by_cases hd : dec y ≠ m₁
    · rw [ite_eq_left (hiff.mpr hd), ite_eq_left hd]
      rfl
    · rw [ite_eq_right (fun h => hd (hiff.mp h)), ite_eq_right hd]

/-- **Axis achievability for the MAC with feedback and a silent user** (El Gamal–Kim §17.1):
    `[0, C(V)] × {0} ⊆ macFeedbackCapacityRegion`. -/
theorem Icc_prod_zero_subset_macFeedbackCapacityRegion [Nonempty X₁] [Nonempty X₂]
    (V : DMC X₁ Y) :
    Set.Icc 0 V.capacity ×ˢ {0} ⊆ macFeedbackCapacityRegion (macIgnoringSecond (X₂ := X₂) V) := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_mono fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp2
  show IsMACFeedbackAchievable _ p.1 p.2
  rw [hp2]
  exact isMACFeedbackAchievable_macIgnoringSecond V hp1

end MACFeedback

section Causal

/-- **Causal chains are probability distributions** (Cover–Thomas §7.12, El Gamal–Kim §17.1):
    for any family of conditional laws `g i (y^{i-1}) (·)` on `Y`, the causal product
    `∏ᵢ g i (y^{i-1}) (yᵢ)` sums to `1` over `Yⁿ`. This is the normalisation behind every
    feedback / causal-relay error expression in `Core.Channels`. -/
theorem sum_causal_prod_eq_one {Y : Type*} [Fintype Y] (n : ℕ)
    (g : ∀ i : Fin n, (Fin i.1 → Y) → Y → ℝ) (h1 : ∀ i h, ∑ b, g i h b = 1) :
    ∑ y : Fin n → Y, ∏ i : Fin n, g i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩) (y i) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Y).sum_comp, Fintype.sum_prod_type]
    have h₀ : ∀ f f' : Fin (0 : Fin (n + 1)).1 → Y, f = f' := fun f f' => by
      funext j; exact (Nat.not_lt_zero _ j.2).elim
    have hstep : ∀ (b : Y) (y' : Fin n → Y),
        ∏ i : Fin (n + 1), g i
          (fun j => (Fin.consEquiv (fun _ => Y) (b, y')) ⟨j.1, Nat.lt_trans j.2 i.2⟩)
          ((Fin.consEquiv (fun _ => Y) (b, y')) i) =
        g 0 (fun j => (Nat.not_lt_zero _ j.2).elim) b *
          ∏ i : Fin n, g i.succ (Fin.cons b (fun j : Fin i.1 => y' ⟨j.1, Nat.lt_trans j.2 i.2⟩))
            (y' i) := by
      intro b y'
      rw [Fin.prod_univ_succ]
      congr 1
      · rw [h₀ (fun j => (Fin.consEquiv (fun _ => Y) (b, y')) ⟨j.1, Nat.lt_trans j.2 (0 : Fin (n + 1)).2⟩)
          (fun j => (Nat.not_lt_zero _ j.2).elim)]
        rfl
      · refine Finset.prod_congr rfl fun i _ => ?_
        congr 1
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · rfl
        · rfl
    simp_rw [hstep, ← Finset.mul_sum]
    have hin : ∀ b : Y, ∑ y' : Fin n → Y, ∏ i : Fin n,
        g i.succ (Fin.cons b (fun j : Fin i.1 => y' ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y' i) = 1 :=
      fun b => ih (fun i h c => g i.succ (Fin.cons b h) c) (fun i h => h1 i.succ _)
    simp_rw [hin, mul_one]
    exact h1 0 _

end Causal

section MACFeedbackSilent

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- **A user whose input does nothing cannot communicate, even with feedback**
    (El Gamal–Kim §17.1): over the MAC that ignores user 2, every feedback code has average
    error at least `1 - 1/M₂`, because the output law does not depend on `m₂`. -/
theorem macIgnoringSecond_err_ge (V : DMC X₁ Y) {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i.1 → Y) → X₁)
    (enc₂ : ∀ i : Fin n, Fin M₂ → (Fin i.1 → Y) → X₂)
    (dec : (Fin n → Y) → Fin M₁ × Fin M₂) :
    1 - 1 / (M₂ : ℝ) ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
        if dec y ≠ (m₁, m₂) then ∏ i : Fin n, (macIgnoringSecond (X₂ := X₂) V).trans
          (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
           enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i) else 0 := by
  let T : Fin M₁ → (Fin n → Y) → ℝ := fun m₁ y => ∏ i : Fin n,
    V.trans (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)
  have hT0 : ∀ m₁ y, 0 ≤ T m₁ y := fun m₁ y => Finset.prod_nonneg fun i _ => V.nonneg _ _
  have hT1 : ∀ m₁, ∑ y, T m₁ y = 1 := fun m₁ =>
    sum_causal_prod_eq_one n (fun i h b => V.trans (enc₁ i m₁ h) b) (fun i h => V.sum_one _)
  have hcount : ∀ c : Fin M₂, ∑ m₂ : Fin M₂, (if c ≠ m₂ then (1 : ℝ) else 0) = (M₂ : ℝ) - 1 := by
    intro c
    have h1 : ∀ m₂ : Fin M₂, (if c ≠ m₂ then (1 : ℝ) else 0) = 1 - if c = m₂ then 1 else 0 :=
      fun m₂ => by split_ifs <;> simp_all
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hinner : ∀ m₁ : Fin M₁, (M₂ : ℝ) - 1 ≤ ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
      (if dec y ≠ (m₁, m₂) then T m₁ y else 0) := by
    intro m₁
    calc (M₂ : ℝ) - 1 = ∑ y, T m₁ y * ((M₂ : ℝ) - 1) := by rw [← Finset.sum_mul, hT1, one_mul]
      _ = ∑ y, ∑ m₂ : Fin M₂, (if (dec y).2 ≠ m₂ then T m₁ y else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← hcount (dec y).2, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m₂ _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ y, ∑ m₂ : Fin M₂, (if dec y ≠ (m₁, m₂) then T m₁ y else 0) := by
          refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun m₂ _ => ?_
          by_cases h : (dec y).2 ≠ m₂
          · rw [ite_eq_left h, ite_eq_left (fun he => h (by rw [he]))]
          · rw [ite_eq_right h]
            split_ifs
            · exact hT0 _ _
            · exact le_rfl
      _ = _ := Finset.sum_comm
  have hsum := Finset.sum_le_sum fun m₁ (_ : m₁ ∈ Finset.univ) => hinner m₁
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  calc 1 - 1 / (M₂ : ℝ) = ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ((M₁ : ℝ) * ((M₂ : ℝ) - 1)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hpos

/-- **Degenerate check: a silent MAC user gets rate 0, even with feedback**
    (El Gamal–Kim §17.1): no pair with `R₂ > 0` is `IsMACFeedbackAchievable` over the MAC that
    ignores user 2. -/
theorem not_isMACFeedbackAchievable_macIgnoringSecond (V : DMC X₁ Y) {R₁ R₂ : ℝ}
    (hR₂ : 0 < R₂) : ¬ IsMACFeedbackAchievable (macIgnoringSecond (X₂ := X₂) V) R₁ R₂ := by
  rintro ⟨-, -, h⟩
  obtain ⟨N, hN⟩ := h (1 / 4) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_ge (1 / R₂)
  have hc := hN (max N K) (le_max_left _ _)
  dsimp only at hc
  obtain ⟨enc₁, enc₂, dec, herr⟩ := hc
  have hnR : 1 ≤ ((max N K : ℕ) : ℝ) * R₂ := by
    have h1 : 1 / R₂ ≤ ((max N K : ℕ) : ℝ) :=
      hK.trans (by exact_mod_cast le_max_right N K)
    rw [div_le_iff₀ hR₂] at h1
    linarith
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (((max N K : ℕ) : ℝ) * R₂) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR
  have hM₂ : 2 ≤ Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N K : ℕ) : ℝ) * R₂))) :=
    le_trans (Nat.le_floor (by exact_mod_cast h2)) (le_max_right _ _)
  have hge := macIgnoringSecond_err_ge V (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (by omega) enc₁ enc₂ dec
  have hinv : (1 : ℝ) / (Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N K : ℕ) : ℝ) * R₂))) : ℕ) ≤
      1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM₂)
  linarith

/-- **MAC with feedback and a silent user, region sandwich** (El Gamal–Kim §17.1):
    `[0, C(V)] × {0} ⊆ macFeedbackCapacityRegion ⊆ [0, ∞) × {0}`. (The missing inclusion
    `R₁ ≤ C(V)` needs the feedback converse, Cover–Thomas Thm. 7.12.1, not yet in the library.) -/
theorem macFeedbackCapacityRegion_macIgnoringSecond_subset (V : DMC X₁ Y) :
    macFeedbackCapacityRegion (macIgnoringSecond (X₂ := X₂) V) ⊆ Set.Ici 0 ×ˢ {0} := by
  refine closure_minimal (fun p hp => ?_) (isClosed_Ici.prod isClosed_singleton)
  refine ⟨hp.1, ?_⟩
  rcases eq_or_lt_of_le hp.2.1 with h0 | hpos
  · exact h0.symm
  · exact absurd hp (not_isMACFeedbackAchievable_macIgnoringSecond V hpos)

end MACFeedbackSilent

end InfoTheory.Known.Operational
