import InfoTheory.Problems.MartonInnerBoundTightness
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.BroadcastChannel

/-!
# Certificate for `InfoTheory.Problems.MartonInnerBoundTightness`

The frozen statement asks whether, for every finite two-receiver DM broadcast channel `W`, the
common-and-private-message capacity region `bcCommonCapacityRegion W ⊆ ℝ³` equals Marton's
five-inequality inner bound `martonCommonInnerBound W`.

## Certified (about exactly these objects)
* `pair_rate_le_capacity` — a Fano-based converse for codes whose message is a pair
  `(m₀, m₁) ∈ [M₀] × [M₁]`: `R₀ + R₁ ≤ C(V)` (from `Bridge.dmcAvgError_rate_converse`).
* `exists_slice₁`, `exists_slice₂` — averaging over the message that a receiver does not
  decode gives a good code for that receiver's marginal channel.
* `bcCommonCapacityRegion_subset` — the **cut-set outer bound** (El Gamal–Kim §5.6, §8.1):
  `C_com(W) ⊆ {R ≥ 0, R₀ + R₁ ≤ C₁, R₀ + R₂ ≤ C₂}` with `Cⱼ = C(p(yⱼ | x))`. In particular
  the operational region is bounded.
* `martonCommonInnerBound_subset` — Marton's region satisfies the same outer bound
  (`R₀ + R₁ ≤ I(W, U₁; Y₁) ≤ C₁` by data processing, certificate `BroadcastChannel`).
* `zero_mem_bcCommonCapacityRegion`, `zero_mem_martonCommonInnerBound` — both sides contain
  the origin. So both sides of the statement are nonempty bounded sets.

* **Regression** `superpositionCommonRegion_subset_martonCommonInnerBound` — with `U₀ = U`,
  `U₁ = X`, `U₂` constant the frozen five-inequality region contains the superposition coding
  region with a common message (`R₁ ≤ I(X;Y₁|U)`, `R₀+R₂ ≤ I(U;Y₂)`, `R₀+R₁+R₂ ≤ I(X;Y₁)`);
  `zero_prod_superposition_mem_martonCommonInnerBound` — its `R₀ = 0` slice contains Bridge's
  `superpositionInnerBound`, and
  `zero_prod_bcCapacityRegion_mem_martonCommonInnerBound_of_degraded` — on physically degraded
  BCs it contains the Bergmans–Gallager capacity region.

## Not certified
* Achievability of Marton's region with a common message (Marton 1979; Liang–Kramer 2007;
  needs mutual covering, not in the library; superposition coding is in `Bridge`, db659ea).
* The individual axes (e.g. `(R₀, 0, 0)` achievable iff `R₀ ≤ max_{p(x)} min(I(X;Y₁), I(X;Y₂))`
  needs compound-channel coding).
* No statement-level conclusion: the problem is open. Huang–Liu–Liu (arXiv:2608.19869, Aug. 2026, not peer reviewed) *claim* a channel on which Marton's bound (with `W`) is strictly suboptimal; unverified — see `problems/marton-inner-bound-tightness.md`.

Sources: Marton, IEEE Trans. IT 1979; Liang–Kramer, IEEE Trans. IT 2007;
El Gamal–Kim, *Network Information Theory*, Thm. 8.3.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MartonInnerBoundTightness

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.MartonInnerBoundTightness
open InfoTheory.Known.Certificates.BroadcastChannel (mi_fst_le_capacity mi_snd_le_capacity
  condMutualInfo_eq_zero_of_subsingleton_fst)

/-! ### A Fano converse for pair-message codes -/

section PairConverse

variable {X Z : Type*} [Fintype X] [Fintype Z]

/-- Average error of a code with message pair `(m₀, m₁)` over a DMC `V`. -/
noncomputable def pairErr (V : DMC X Z) (n M₀ M₁ : ℕ) (enc : Fin M₀ → Fin M₁ → Fin n → X)
    (dec : (Fin n → Z) → Fin M₀ × Fin M₁) : ℝ :=
  ((1 : ℝ) / ((M₀ * M₁ : ℕ) : ℝ)) *
    ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ z : Fin n → Z,
      if dec z ≠ (m₀, m₁) then (V.power n).trans (enc m₀ m₁) z else 0

/-- Re-indexing a pair-message code by `finProdFinEquiv` gives a point-to-point code with
    `M₀ M₁` messages and the same error. -/
theorem dmcAvgError_eq_pairErr [DecidableEq Z] (V : DMC X Z) {n M₀ M₁ : ℕ}
    (h₀ : 0 < M₀) (h₁ : 0 < M₁) (enc : Fin M₀ → Fin M₁ → Fin n → X)
    (dec : (Fin n → Z) → Fin M₀ × Fin M₁) :
    dmcAvgError V n (M₀ * M₁)
        (fun k => enc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        (fun z => finProdFinEquiv (dec z)) = pairErr V n M₀ M₁ enc dec := by
  classical
  have hM : M₀ * M₁ ≠ 0 := (Nat.mul_pos h₀ h₁).ne'
  unfold dmcAvgError pairErr
  rw [ite_eq_right hM]
  congr 1
  rw [← Fintype.sum_prod_type' (fun m₀ m₁ => ∑ z : Fin n → Z,
      if dec z ≠ (m₀, m₁) then (V.power n).trans (enc m₀ m₁) z else 0)]
  rw [← Fintype.sum_equiv finProdFinEquiv (fun p : Fin M₀ × Fin M₁ => ∑ z : Fin n → Z,
      if finProdFinEquiv (dec z) ≠ finProdFinEquiv p then
        (V.power n).trans
          (enc (finProdFinEquiv.symm (finProdFinEquiv p)).1
            (finProdFinEquiv.symm (finProdFinEquiv p)).2) z else 0) _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Equiv.symm_apply_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]

lemma natMax_one_floor_ge (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
  set x : ℝ := (2 : ℝ) ^ ((n : ℝ) * R) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : x / 2 ≤ (Nat.floor x : ℝ) := by
    have h1 : x - 1 < (Nat.floor x : ℝ) := Nat.sub_one_lt_floor x
    by_cases hx2 : x < 2
    · have : (1 : ℝ) ≤ (Nat.floor x : ℝ) := by
        exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx1
      linarith
    · push Not at hx2
      linarith
  have : (Nat.floor x : ℝ) ≤ ((Nat.max 1 (Nat.floor x) : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 1 (Nat.floor x)
  linarith

lemma natMax_one_pos (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

private lemma log2_two_rpow' (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma log2_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log2 a ≤ log2 b := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log ha hab) (Real.log_pos one_lt_two).le

/-- **Fano converse for pair-message codes**: if pair codes of sizes
    `max 1 ⌊2^{nR₀}⌋ × max 1 ⌊2^{nR₁}⌋` with vanishing error exist over `V`,
    then `R₀ + R₁ ≤ C(V)`. -/
theorem pair_rate_le_capacity (V : DMC X Z) {R₀ R₁ : ℝ} (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁)
    (hach : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∃ (enc : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀)))) →
          Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))) → Fin n → X)
        (dec : (Fin n → Z) → Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀)))) ×
          Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))))),
        pairErr V n _ _ enc dec ≤ ε) :
    R₀ + R₁ ≤ V.capacity := by
  classical
  set S := R₀ + R₁ with hS
  set C := V.capacity with hC
  have hC0 : 0 ≤ C := capacity_nonneg _
  by_contra hlt
  push Not at hlt
  have hSpos : 0 < S := lt_of_le_of_lt hC0 hlt
  set ε : ℝ := (S - C) / (2 * S) with hε
  have hεpos : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hε1 : ε ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ (by linarith)]; linarith
  obtain ⟨N, hN⟩ := hach ε hεpos
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (6 / (S - C))
  set n := max N (n₀ + 1) with hn
  have hnN : N ≤ n := le_max_left _ _
  have hn1 : n₀ + 1 ≤ n := le_max_right _ _
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos _) hn1
  have hnr : (6 / (S - C)) < (n : ℝ) := by
    have : (n₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hc := hN n hnN
  have h₀ := natMax_one_pos (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀)))
  have h₁ := natMax_one_pos (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  have a0 := natMax_one_floor_ge n hR₀
  have a1 := natMax_one_floor_ge n hR₁
  generalize Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀))) = M₀ at hc h₀ a0
  generalize Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) = M₁ at hc h₁ a1
  obtain ⟨enc, dec, herr⟩ := hc
  have hprod : (2 : ℝ) ^ ((n : ℝ) * S) / 4 ≤ ((M₀ * M₁ : ℕ) : ℝ) := by
    have e : (2 : ℝ) ^ ((n : ℝ) * S) = (2 : ℝ) ^ ((n : ℝ) * R₀) * (2 : ℝ) ^ ((n : ℝ) * R₁) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; rw [hS]; ring
    push_cast
    rw [e]
    have p1 : 0 ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) / 2 := by positivity
    calc (2 : ℝ) ^ ((n : ℝ) * R₀) * (2 : ℝ) ^ ((n : ℝ) * R₁) / 4
        = ((2 : ℝ) ^ ((n : ℝ) * R₀) / 2) * ((2 : ℝ) ^ ((n : ℝ) * R₁) / 2) := by ring
      _ ≤ (M₀ : ℝ) * (M₁ : ℝ) := mul_le_mul a0 a1 p1 (by positivity)
  have hlogprod : (n : ℝ) * S - 2 ≤ log2 ((M₀ * M₁ : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * S) / 4 := by positivity
    have := log2_mono hpos hprod
    have e2 : log2 ((2 : ℝ) ^ ((n : ℝ) * S) / 4) = (n : ℝ) * S - 2 := by
      have : (2 : ℝ) ^ ((n : ℝ) * S) / 4 = (2 : ℝ) ^ ((n : ℝ) * S - 2) := by
        rw [Real.rpow_sub (by norm_num)]; norm_num
      rw [this, log2_two_rpow']
    linarith
  have hmain : (1 - ε) * ((n : ℝ) * S - 2) ≤ (n : ℝ) * C + 1 := by
    by_cases h2 : 2 ≤ M₀ * M₁
    · have hconv := dmcAvgError_rate_converse V n (M₀ * M₁) hnpos h2
        (fun k => enc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        (fun z => finProdFinEquiv (dec z))
      have hle := dmcAvgError_eq_pairErr V h₀ h₁ enc dec
      set pe := dmcAvgError V n (M₀ * M₁)
        (fun k => enc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        (fun z => finProdFinEquiv (dec z)) with hpe
      have hpeε : pe ≤ ε := hle.le.trans herr
      have hnr' : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hlog0 : 0 ≤ log2 ((M₀ * M₁ : ℕ) : ℝ) := by
        unfold log2
        apply div_nonneg _ (Real.log_pos one_lt_two).le
        apply Real.log_nonneg
        have : 1 ≤ M₀ * M₁ := by omega
        exact_mod_cast this
      have h3 : (1 - pe) * log2 ((M₀ * M₁ : ℕ) : ℝ) ≤ (n : ℝ) * C + 1 := by
        have := mul_le_mul_of_nonneg_right hconv hnr'.le
        rw [mul_assoc, div_mul_cancel₀ _ hnr'.ne', add_mul, one_div, inv_mul_cancel₀ hnr'.ne']
          at this
        linarith
      have h4 : (1 - ε) * log2 ((M₀ * M₁ : ℕ) : ℝ) ≤ (1 - pe) * log2 ((M₀ * M₁ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog0
      have h5 : (1 - ε) * ((n : ℝ) * S - 2) ≤ (1 - ε) * log2 ((M₀ * M₁ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogprod (by linarith)
      linarith
    · push Not at h2
      have h1' : M₀ * M₁ = 1 := by
        have : 1 ≤ M₀ * M₁ := Nat.mul_pos h₀ h₁
        omega
      rw [h1'] at hlogprod
      simp [log2] at hlogprod
      have : (1 - ε) * ((n : ℝ) * S - 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have : (0 : ℝ) ≤ (n : ℝ) * C := mul_nonneg (by positivity) hC0
      linarith
  have hkey : (1 - ε) * S = (S + C) / 2 := by
    rw [hε]; field_simp; ring
  have : (n : ℝ) * ((S - C) / 2) ≤ 3 := by nlinarith
  have hSC : 0 < S - C := by linarith
  rw [div_lt_iff₀ hSC] at hnr
  nlinarith

end PairConverse

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-! ### Slicing a common-message code -/

/-- The common-and-private-message error of `IsBCCommonAchievable`, per message triple. -/
noncomputable abbrev comErr (W : BroadcastChannel X Y₁ Y₂) {n M₀ M₁ M₂ : ℕ}
    (enc : Fin M₀ → Fin M₁ → Fin M₂ → Fin n → X)
    (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁) (dec₂ : (Fin n → Y₂) → Fin M₀ × Fin M₂)
    (m₀ : Fin M₀) (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ :=
  ∑ y : Fin n → Y₁ × Y₂,
    if dec₁ (fun i => (y i).1) ≠ (m₀, m₁) ∨ dec₂ (fun i => (y i).2) ≠ (m₀, m₂)
    then (W.power n).trans (enc m₀ m₁ m₂) y else 0

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

/-- **Slice for receiver 1**: some `m₂` gives a pair code for `p(y₁ | x)` with error `≤ δ`. -/
theorem exists_slice₁ [DecidableEq Y₁] (W : BroadcastChannel X Y₁ Y₂) {n M₀ M₁ M₂ : ℕ}
    (h₀ : 0 < M₀) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (enc : Fin M₀ → Fin M₁ → Fin M₂ → Fin n → X)
    (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁) (dec₂ : (Fin n → Y₂) → Fin M₀ × Fin M₂) {δ : ℝ}
    (herr : ((1 : ℝ) / ((M₀ * M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ ≤ δ) :
    ∃ m₂ : Fin M₂, pairErr (marginalFst W) n M₀ M₁ (fun a b => enc a b m₂) dec₁ ≤ δ := by
  classical
  have hM : (0 : ℝ) < ((M₀ * M₁ * M₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos h₀ h₁) h₂
  have hM01 : (0 : ℝ) < ((M₀ * M₁ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos h₀ h₁
  let G : Fin M₂ → ℝ := fun m₂ => ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ z : Fin n → Y₁,
    if dec₁ z ≠ (m₀, m₁) then ((marginalFst W).power n).trans (enc m₀ m₁ m₂) z else 0
  have hG : ∀ m₂, G m₂ ≤ ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, comErr W enc dec₁ dec₂ m₀ m₁ m₂ := by
    intro m₂
    refine Finset.sum_le_sum fun m₀ _ => Finset.sum_le_sum fun m₁ _ => ?_
    rw [← sum_ite_fst_power W (enc m₀ m₁ m₂) (fun z => dec₁ z ≠ (m₀, m₁))]
    exact Finset.sum_le_sum fun y _ => ite_le_ite_or_left ((W.power n).nonneg _ _)
  have hsum : ∑ m₂ : Fin M₂, G m₂ ≤ ∑ _m₂ : Fin M₂, ((M₀ * M₁ : ℕ) : ℝ) * δ := by
    have h1 : ∑ m₂ : Fin M₂, G m₂ ≤
        ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ := by
      calc ∑ m₂ : Fin M₂, G m₂ ≤ ∑ m₂ : Fin M₂, ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁,
            comErr W enc dec₁ dec₂ m₀ m₁ m₂ := Finset.sum_le_sum fun m₂ _ => hG m₂
        _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m₀ _ => ?_
          rw [Finset.sum_comm]
    have h2 : ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ ≤
        ((M₀ * M₁ * M₂ : ℕ) : ℝ) * δ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM] at herr
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast at h2 ⊢
    linarith
  obtain ⟨m₂, -, hm₂⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty_iff.mpr ⟨⟨0, h₂⟩⟩) hsum
  refine ⟨m₂, ?_⟩
  unfold pairErr
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM01]
  linarith

/-- **Slice for receiver 2**: some `m₁` gives a pair code for `p(y₂ | x)` with error `≤ δ`. -/
theorem exists_slice₂ [DecidableEq Y₂] (W : BroadcastChannel X Y₁ Y₂) {n M₀ M₁ M₂ : ℕ}
    (h₀ : 0 < M₀) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (enc : Fin M₀ → Fin M₁ → Fin M₂ → Fin n → X)
    (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁) (dec₂ : (Fin n → Y₂) → Fin M₀ × Fin M₂) {δ : ℝ}
    (herr : ((1 : ℝ) / ((M₀ * M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ ≤ δ) :
    ∃ m₁ : Fin M₁, pairErr (marginalSnd W) n M₀ M₂ (fun a c => enc a m₁ c) dec₂ ≤ δ := by
  classical
  have hM : (0 : ℝ) < ((M₀ * M₁ * M₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos h₀ h₁) h₂
  have hM02 : (0 : ℝ) < ((M₀ * M₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos h₀ h₂
  let G : Fin M₁ → ℝ := fun m₁ => ∑ m₀ : Fin M₀, ∑ m₂ : Fin M₂, ∑ z : Fin n → Y₂,
    if dec₂ z ≠ (m₀, m₂) then ((marginalSnd W).power n).trans (enc m₀ m₁ m₂) z else 0
  have hG : ∀ m₁, G m₁ ≤ ∑ m₀ : Fin M₀, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ := by
    intro m₁
    refine Finset.sum_le_sum fun m₀ _ => Finset.sum_le_sum fun m₂ _ => ?_
    rw [← sum_ite_snd_power W (enc m₀ m₁ m₂) (fun z => dec₂ z ≠ (m₀, m₂))]
    exact Finset.sum_le_sum fun y _ => ite_le_ite_or_right ((W.power n).nonneg _ _)
  have hsum : ∑ m₁ : Fin M₁, G m₁ ≤ ∑ _m₁ : Fin M₁, ((M₀ * M₂ : ℕ) : ℝ) * δ := by
    have h1 : ∑ m₁ : Fin M₁, G m₁ ≤
        ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ := by
      calc ∑ m₁ : Fin M₁, G m₁ ≤ ∑ m₁ : Fin M₁, ∑ m₀ : Fin M₀, ∑ m₂ : Fin M₂,
            comErr W enc dec₁ dec₂ m₀ m₁ m₂ := Finset.sum_le_sum fun m₁ _ => hG m₁
        _ = _ := Finset.sum_comm
    have h2 : ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, comErr W enc dec₁ dec₂ m₀ m₁ m₂ ≤
        ((M₀ * M₁ * M₂ : ℕ) : ℝ) * δ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM] at herr
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast at h2 ⊢
    linarith
  obtain ⟨m₁, -, hm₁⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty_iff.mpr ⟨⟨0, h₁⟩⟩) hsum
  refine ⟨m₁, ?_⟩
  unfold pairErr
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM02]
  linarith

/-! ### Outer bound on the operational region -/

/-- **Cut-set bounds** for every achievable triple: `R₀ + R₁ ≤ C₁` and `R₀ + R₂ ≤ C₂`. -/
theorem sumRates_le_of_achievable (W : BroadcastChannel X Y₁ Y₂) {R₀ R₁ R₂ : ℝ}
    (h : IsBCCommonAchievable W R₀ R₁ R₂) :
    R₀ + R₁ ≤ (marginalFst W).capacity ∧ R₀ + R₂ ≤ (marginalSnd W).capacity := by
  classical
  obtain ⟨hR₀, hR₁, hR₂, h⟩ := h
  constructor
  · refine pair_rate_le_capacity (marginalFst W) hR₀ hR₁ fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨enc, dec₁, dec₂, herr⟩ := hN n hn
    obtain ⟨m₂, hm₂⟩ := exists_slice₁ W (natMax_one_pos _) (natMax_one_pos _) (natMax_one_pos _)
      enc dec₁ dec₂ herr
    exact ⟨_, dec₁, hm₂⟩
  · refine pair_rate_le_capacity (marginalSnd W) hR₀ hR₂ fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨enc, dec₁, dec₂, herr⟩ := hN n hn
    obtain ⟨m₁, hm₁⟩ := exists_slice₂ W (natMax_one_pos _) (natMax_one_pos _) (natMax_one_pos _)
      enc dec₁ dec₂ herr
    exact ⟨_, dec₂, hm₁⟩

/-- The closed outer-bound set `{R ≥ 0, R₀ + R₁ ≤ C₁, R₀ + R₂ ≤ C₂}`. -/
def cutsetSet (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧ r.1 + r.2.1 ≤ (marginalFst W).capacity ∧
    r.1 + r.2.2 ≤ (marginalSnd W).capacity }

theorem isClosed_cutsetSet (W : BroadcastChannel X Y₁ Y₂) : IsClosed (cutsetSet W) := by
  have c1 : Continuous fun r : ℝ × ℝ × ℝ => r.1 := continuous_fst
  have c2 : Continuous fun r : ℝ × ℝ × ℝ => r.2.1 := continuous_fst.comp continuous_snd
  have c3 : Continuous fun r : ℝ × ℝ × ℝ => r.2.2 := continuous_snd.comp continuous_snd
  exact (isClosed_le continuous_const c1).inter ((isClosed_le continuous_const c2).inter
    ((isClosed_le continuous_const c3).inter ((isClosed_le (c1.add c2) continuous_const).inter
      (isClosed_le (c1.add c3) continuous_const))))

/-- **Outer bound on the operational region**: `C_com(W) ⊆ {R₀ + R₁ ≤ C₁, R₀ + R₂ ≤ C₂}`. -/
theorem bcCommonCapacityRegion_subset (W : BroadcastChannel X Y₁ Y₂) :
    bcCommonCapacityRegion W ⊆ cutsetSet W :=
  closure_minimal (fun r hr => ⟨hr.1, hr.2.1, hr.2.2.1, sumRates_le_of_achievable W hr⟩)
    (isClosed_cutsetSet W)

/-- **Marton's region satisfies the same outer bound.** -/
theorem martonCommonInnerBound_subset (W : BroadcastChannel X Y₁ Y₂) :
    martonCommonInnerBound W ⊆ cutsetSet W := by
  refine closure_minimal (fun r hr => ?_) (isClosed_cutsetSet W)
  obtain ⟨h0, h1, h2, k₀, k₁, k₂, P, hc⟩ := hr
  obtain ⟨c1, c2, -, -, -⟩ := hc
  exact ⟨h0, h1, h2,
    c1.trans (mi_fst_le_capacity W P (fun a => a.2.2.2) _ (fun _ => rfl) (fun a => (a.1, a.2.1))),
    c2.trans (mi_snd_le_capacity W P (fun a => a.2.2.2) _ (fun _ => rfl)
      (fun a => (a.1, a.2.2.1)))⟩

/-! ### Both sides contain the origin -/

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

theorem zero_mem_bcCommonCapacityRegion [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ bcCommonCapacityRegion W := by
  classical
  refine subset_closure ⟨le_rfl, le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  rw [natMax_zero]
  refine ⟨fun _ _ _ _ => Classical.arbitrary X, fun _ => (0, 0), fun _ => (0, 0), ?_⟩
  have : ∀ (m₀ m₁ m₂ : Fin 1) (y : Fin n → Y₁ × Y₂),
      (if ((0 : Fin 1), (0 : Fin 1)) ≠ (m₀, m₁) ∨ ((0 : Fin 1), (0 : Fin 1)) ≠ (m₀, m₂) then
        (W.power n).trans (fun _ => Classical.arbitrary X) y else 0) = 0 := by
    intro m₀ m₁ m₂ y
    rw [ite_eq_right]
    rintro (h | h) <;> exact h (by ext <;> simp [Subsingleton.elim (0 : Fin 1) _])
  simp only [this, Finset.sum_const_zero, mul_zero]
  exact hε.le

theorem zero_mem_martonCommonInnerBound [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ martonCommonInnerBound W := by
  refine subset_closure ⟨le_rfl, le_rfl, le_rfl, 1, 1, 1, ProbDist.uniform, ?_⟩
  intro J I01_Y1 I02_Y2 I1_Y1_0 I2_Y2_0 I12_0
  have z : I12_0 = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have n1 : 0 ≤ I01_Y1 := mutualInfo_nonneg _
  have n2 : 0 ≤ I02_Y2 := mutualInfo_nonneg _
  have n3 : 0 ≤ I1_Y1_0 := condMutualInfo_nonneg _
  have n4 : 0 ≤ I2_Y2_0 := condMutualInfo_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [z]) <;> linarith

/-! ### Regression: superposition coding with a common message

With `U₀ := U`, `U₁ := X`, `U₂` constant, Marton's five inequalities reduce to (a superset of)
the superposition coding region with a common message (El Gamal–Kim §5.3, §8.1):
`R₁ ≤ I(X;Y₁|U)`, `R₀ + R₂ ≤ I(U;Y₂)`, `R₀ + R₁ + R₂ ≤ I(X;Y₁)`. Hence the `R₀ = 0` slice of the
frozen region contains Bridge's `superpositionInnerBound`, and on physically degraded BCs it
contains the Bergmans–Gallager capacity region. -/

section Regression

open InfoTheory.Known.Certificates.BroadcastChannel (joint_eq_map_of_comp
  condMutualInfo_map_fst_injective condMutualInfo_eq_zero_of_subsingleton mi_map_left_le)

/-- The superposition coding region with a common message, for the auxiliary law `Pux`. -/
def superpositionCommonRegion (W : BroadcastChannel X Y₁ Y₂) {kU : ℕ}
    (Pux : ProbDist (Fin kU × X)) : Set (ℝ × ℝ × ℝ) :=
  let J := bcAuxJoint W Pux
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧
    r.2.1 ≤ condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) ∧
    r.1 + r.2.2 ≤ mutualInfo (J.map (fun z => (z.1.1, z.2.2))) ∧
    r.1 + r.2.1 + r.2.2 ≤ mutualInfo (J.map (fun z => (z.1.2, z.2.1))) }

/-- **Regression**: the frozen Marton common-message region contains the superposition coding
    region with a common message (take `U₀ = U`, `U₁ = X`, `U₂` constant). -/
theorem superpositionCommonRegion_subset_martonCommonInnerBound (W : BroadcastChannel X Y₁ Y₂)
    {kU : ℕ} (Pux : ProbDist (Fin kU × X)) :
    superpositionCommonRegion W Pux ⊆ martonCommonInnerBound W := by
  classical
  rintro ⟨R₀, R₁, R₂⟩ ⟨h0, h1, h2, hR₁, hR₀₂, hsum⟩
  apply subset_closure
  let e := Fintype.equivFin X
  let φ : Fin kU × X → Fin kU × Fin (Fintype.card X) × Fin 1 × X :=
    fun a => (a.1, e a.2, 0, a.2)
  refine ⟨h0, h1, h2, kU, Fintype.card X, 1, Pux.map φ, ?_⟩
  intro joint I01 I02 I1 I2 I12
  set J := bcAuxJoint W Pux with hJdef
  have hJ : joint = J.map (fun z => (φ z.1, z.2)) :=
    joint_eq_map_of_comp W Pux (fun a => a.2) φ (fun b => b.2.2.2) (fun _ => rfl) joint
      (fun _ => rfl) J (fun _ => rfl)
  -- `I(X; Y₁) ≤ I(U₀, U₁; Y₁)`
  have hA : mutualInfo (J.map (fun z => (z.1.2, z.2.1))) ≤ I01 := by
    have e1 : I01 = mutualInfo (J.map (fun z => ((z.1.1, e z.1.2), z.2.1))) := by
      change mutualInfo (joint.map _) = _
      rw [hJ, map_comp_eq]; rfl
    rw [e1]
    refine le_trans (le_of_eq ?_) (mi_map_left_le _ (fun b => e.symm b.2))
    rw [map_comp_eq]
    have hf : (fun z : (Fin kU × X) × (Y₁ × Y₂) => (z.1.2, z.2.1)) =
        Prod.map (fun b : Fin kU × Fin (Fintype.card X) => e.symm b.2) id ∘
          fun z => ((z.1.1, e z.1.2), z.2.1) := by
      funext z; simp
    rw [hf]
  -- `I(U; Y₂) ≤ I(U₀, U₂; Y₂)`
  have hB : mutualInfo (J.map (fun z => (z.1.1, z.2.2))) ≤ I02 := by
    have e1 : I02 = mutualInfo (J.map (fun z => ((z.1.1, (0 : Fin 1)), z.2.2))) := by
      change mutualInfo (joint.map _) = _
      rw [hJ, map_comp_eq]; rfl
    rw [e1]
    refine le_trans (le_of_eq ?_) (mi_map_left_le _ Prod.fst)
    rw [map_comp_eq]; rfl
  -- `I(U₁; Y₁ | U₀) = I(X; Y₁ | U)`
  have hC : I1 = condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) := by
    change condMutualInfo (joint.map _) = _
    rw [hJ, map_comp_eq]
    have := condMutualInfo_map_fst_injective (J.map (fun z => (z.1.2, z.2.1, z.1.1))) e
      e.injective
    rw [map_comp_eq] at this
    exact this
  have hD : I12 = 0 := condMutualInfo_eq_zero_of_subsingleton _
  have hE : 0 ≤ I2 := condMutualInfo_nonneg _
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Regression (`R₀ = 0` slice)**: `{0} × superpositionInnerBound W ⊆ martonCommonInnerBound W`. -/
theorem zero_prod_superposition_mem_martonCommonInnerBound (W : BroadcastChannel X Y₁ Y₂)
    {r : ℝ × ℝ} (hr : r ∈ superpositionInnerBound W) :
    ((0 : ℝ), r.1, r.2) ∈ martonCommonInnerBound W := by
  have hc : Continuous (fun r : ℝ × ℝ => ((0 : ℝ), r.1, r.2)) := by fun_prop
  have := map_mem_closure hc hr (t := martonCommonInnerBound W) (fun x hx => by
    obtain ⟨h1, h2, kU, Pux, hR₂, hR₁, hsum⟩ := hx
    exact superpositionCommonRegion_subset_martonCommonInnerBound W Pux
      ⟨le_rfl, h1, h2, hR₁, by simpa using hR₂, by simpa using hsum⟩)
  rwa [martonCommonInnerBound, closure_closure] at this

/-- **Regression (degraded BC)**: on every physically degraded BC, the private-message capacity
    region (Bergmans–Gallager) embeds in the `R₀ = 0` slice of the frozen Marton region. -/
theorem zero_prod_bcCapacityRegion_mem_martonCommonInnerBound_of_degraded
    (W : BroadcastChannel X Y₁ Y₂) (hdeg : IsPhysicallyDegradedBC W) {r : ℝ × ℝ}
    (hr : r ∈ bcCapacityRegion W) : ((0 : ℝ), r.1, r.2) ∈ martonCommonInnerBound W := by
  rw [degradedBC_capacity_theorem W hdeg, ← superpositionInnerBound_eq_degradedBCRegion W hdeg]
    at hr
  exact zero_prod_superposition_mem_martonCommonInnerBound W hr

end Regression

end InfoTheory.Known.Certificates.MartonInnerBoundTightness
