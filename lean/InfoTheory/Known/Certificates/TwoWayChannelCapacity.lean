import InfoTheory.Problems.TwoWayChannelCapacity
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.MacWithFeedback

/-!
# Certificate for `InfoTheory.Problems.TwoWayChannelCapacity`

The frozen statement asks whether, for every finite DM two-way channel `W`, some `k ≥ 1`
satisfies `twcCapacityRegion W = twcKLetterInnerBound k W` (Shannon's `k`-block strategy
inner bound `G_k`).

## Certified (about exactly these objects)
* `twc_err_ge₁`, `twc_err_ge₂` — counting converses valid for every adaptive two-way code:
  average error `≥ 1 - |Y₂|ⁿ / M₁` and `≥ 1 - |Y₁|ⁿ / M₂` (terminal 2 must decode `m₁` from
  `Y₂ⁿ` and its own message; causal-chain normalisation `Known.Operational.sum_causal_prod_eq_one`).
* `twcCapacityRegion_subset_box` — hence `C_TWC(W) ⊆ [0, log₂ |Y₂|] × [0, log₂ |Y₁|]`.
* `Icc_prod_zero_subset_twcCapacityRegion`, `zero_prod_Icc_subset_twcCapacityRegion` —
  **axis achievability** with non-adaptive codes: if terminal 2 sends a fixed `x₂`, user 1
  achieves every rate up to `C(x₁ ↦ p(y₂ | x₁, x₂))` (Shannon's theorem), and symmetrically.
  In particular `C_TWC(W)` contains `(0, 0)`.
* `zero_mem_twcKLetterInnerBound`, `twcKLetterInnerBound_subset_box` — `G_k(W)` contains
  `(0, 0)` (constant strategies) and, for `k ≥ 1`, lies in the same box
  (`(1/k) I(S₁; Y₂ᵏ | S₂, Q) ≤ log₂ |Y₂|`). So both sides of the statement are nonempty bounded
  sets for every `k ≥ 1`.

## Not certified
* Shannon's inner bound `G_k(W) ⊆ C_TWC(W)` (random coding with adaptive strategies) and the
  limit statement `cl ⋃_k G_k = C_TWC` (Shannon 1961, Thm. 1 / Kramer's directed information).
* Shannon's outer bound (`R₁ ≤ I(X₁; Y₂ | X₂)` for some joint `p(x₁, x₂)`): it needs a
  feedback-type converse; `Bridge.dmcFeedback_mutualInfo_le_mul_capacity` (db659ea) is the
  one-way analogue, not yet adapted to two-way codes.
* No statement-level conclusion: the problem is open.

Sources: Shannon, "Two-way communication channels", 1961; El Gamal–Kim §17.5.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.TwoWayChannelCapacity

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.TwoWayChannelCapacity
open InfoTheory.Known.Certificates.MacWithFeedback (sum_success_le_card rate_le_log2_of_counting
  natMax_one_floor_ge natMax_one_pos log2_card_pow)

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]

section Toolkit

/-- `I(A; B | C) ≤ log₂ |B|`. -/
theorem condMutualInfo_le_log2_card {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Nonempty β] (P : ProbDist (α × β × γ)) : condMutualInfo P ≤ log2 (Fintype.card β) := by
  unfold condMutualInfo
  dsimp only
  have h1 : shannonEntropy (P.map (fun t => (t.1, t.2.2))) ≤ shannonEntropy P :=
    shannonEntropy_map_le _ P
  have h2 := shannonEntropy_subadd (P.map (fun t => (t.2.1, t.2.2)))
  rw [← map_fst_eq_fst, ← map_snd_eq_snd, map_comp_eq, map_comp_eq] at h2
  simp only [Function.comp_def] at h2
  have h3 := shannonEntropy_le_log2_card (P.map (fun t => t.2.1))
  linarith

/-- Fixed-message counting: `∑_m ∑_ω 1{dec(π ω) ≠ m} T m ω ≥ M - |Z|`. -/
theorem sum_err_ge {Ω Z : Type*} [Fintype Ω] [Fintype Z] {M : ℕ}
    (T : Fin M → Ω → ℝ) (hT0 : ∀ m ω, 0 ≤ T m ω) (hT1 : ∀ m, ∑ ω, T m ω = 1)
    (π : Ω → Z) (dec : Z → Fin M) :
    (M : ℝ) - Fintype.card Z ≤ ∑ m, ∑ ω, (if dec (π ω) ≠ m then T m ω else 0) := by
  have hS := sum_success_le_card T hT0 hT1 π dec
  have hsplit : ∀ m, ∑ ω, (if dec (π ω) ≠ m then T m ω else 0) =
      1 - ∑ ω, (if dec (π ω) = m then T m ω else 0) := by
    intro m
    rw [← hT1 m, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : dec (π ω) = m <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

end Toolkit

/-! ### Counting outer bound -/

/-- **Counting converse, direction 1 → 2**: average error `≥ 1 - |Y₂|ⁿ / M₁`. -/
theorem twc_err_ge₁ (W : TwoWayChannel X₁ X₂ Y₁ Y₂) {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i.1 → Y₁) → X₁)
    (enc₂ : ∀ i : Fin n, Fin M₂ → (Fin i.1 → Y₂) → X₂)
    (dec₁ : Fin M₁ → (Fin n → Y₁) → Fin M₂) (dec₂ : Fin M₂ → (Fin n → Y₂) → Fin M₁) :
    1 - ((Fintype.card Y₂ : ℝ) ^ n) / M₁ ≤
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        (if dec₁ m₁ (fun i => (y i).1) ≠ m₂ ∨ dec₂ m₂ (fun i => (y i).2) ≠ m₁ then
          ∏ i : Fin n, W.trans
            (enc₁ i m₁ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).1),
             enc₂ i m₂ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).2)) (y i) else 0) := by
  classical
  let T : Fin M₂ → Fin M₁ → (Fin n → Y₁ × Y₂) → ℝ := fun m₂ m₁ y => ∏ i : Fin n, W.trans
    (enc₁ i m₁ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).1),
     enc₂ i m₂ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).2)) (y i)
  have hT0 : ∀ m₂ m₁ y, 0 ≤ T m₂ m₁ y := fun _ _ _ => Finset.prod_nonneg fun i _ => W.nonneg _ _
  have hT1 : ∀ m₂ m₁, ∑ y, T m₂ m₁ y = 1 := fun m₂ m₁ =>
    sum_causal_prod_eq_one n
      (fun i h b => W.trans (enc₁ i m₁ (fun j => (h j).1), enc₂ i m₂ (fun j => (h j).2)) b)
      (fun i h => W.sum_one _)
  have hper : ∀ m₂, (M₁ : ℝ) - (Fintype.card Y₂ : ℝ) ^ n ≤ ∑ m₁ : Fin M₁, ∑ y,
      (if dec₂ m₂ (fun i => (y i).2) ≠ m₁ then T m₂ m₁ y else 0) := by
    intro m₂
    have := sum_err_ge (T m₂) (hT0 m₂) (hT1 m₂) (fun y i => (y i).2) (dec₂ m₂)
    rw [Fintype.card_fun, Fintype.card_fin] at this
    push_cast at this
    exact this
  have hle : ∑ m₂ : Fin M₂, ∑ m₁ : Fin M₁, ∑ y,
      (if dec₂ m₂ (fun i => (y i).2) ≠ m₁ then T m₂ m₁ y else 0) ≤
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        (if dec₁ m₁ (fun i => (y i).1) ≠ m₂ ∨ dec₂ m₂ (fun i => (y i).2) ≠ m₁ then
          T m₂ m₁ y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
      Finset.sum_le_sum fun y _ => ?_
    by_cases h : dec₂ m₂ (fun i => (y i).2) ≠ m₁
    · rw [ite_eq_left h, ite_eq_left (Or.inr h)]
    · rw [ite_eq_right h]; split_ifs <;> simp [hT0]
  have hsum := Finset.sum_le_sum fun m₂ (_ : m₂ ∈ Finset.univ) => hper m₂
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  calc 1 - ((Fintype.card Y₂ : ℝ) ^ n) / M₁ =
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ((M₂ : ℝ) * ((M₁ : ℝ) - (Fintype.card Y₂ : ℝ) ^ n)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.trans hle) hpos

/-- **Counting converse, direction 2 → 1**: average error `≥ 1 - |Y₁|ⁿ / M₂`. -/
theorem twc_err_ge₂ (W : TwoWayChannel X₁ X₂ Y₁ Y₂) {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i.1 → Y₁) → X₁)
    (enc₂ : ∀ i : Fin n, Fin M₂ → (Fin i.1 → Y₂) → X₂)
    (dec₁ : Fin M₁ → (Fin n → Y₁) → Fin M₂) (dec₂ : Fin M₂ → (Fin n → Y₂) → Fin M₁) :
    1 - ((Fintype.card Y₁ : ℝ) ^ n) / M₂ ≤
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        (if dec₁ m₁ (fun i => (y i).1) ≠ m₂ ∨ dec₂ m₂ (fun i => (y i).2) ≠ m₁ then
          ∏ i : Fin n, W.trans
            (enc₁ i m₁ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).1),
             enc₂ i m₂ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).2)) (y i) else 0) := by
  classical
  let T : Fin M₁ → Fin M₂ → (Fin n → Y₁ × Y₂) → ℝ := fun m₁ m₂ y => ∏ i : Fin n, W.trans
    (enc₁ i m₁ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).1),
     enc₂ i m₂ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).2)) (y i)
  have hT0 : ∀ m₁ m₂ y, 0 ≤ T m₁ m₂ y := fun _ _ _ => Finset.prod_nonneg fun i _ => W.nonneg _ _
  have hT1 : ∀ m₁ m₂, ∑ y, T m₁ m₂ y = 1 := fun m₁ m₂ =>
    sum_causal_prod_eq_one n
      (fun i h b => W.trans (enc₁ i m₁ (fun j => (h j).1), enc₂ i m₂ (fun j => (h j).2)) b)
      (fun i h => W.sum_one _)
  have hper : ∀ m₁, (M₂ : ℝ) - (Fintype.card Y₁ : ℝ) ^ n ≤ ∑ m₂ : Fin M₂, ∑ y,
      (if dec₁ m₁ (fun i => (y i).1) ≠ m₂ then T m₁ m₂ y else 0) := by
    intro m₁
    have := sum_err_ge (T m₁) (hT0 m₁) (hT1 m₁) (fun y i => (y i).1) (dec₁ m₁)
    rw [Fintype.card_fun, Fintype.card_fin] at this
    push_cast at this
    exact this
  have hle : ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y,
      (if dec₁ m₁ (fun i => (y i).1) ≠ m₂ then T m₁ m₂ y else 0) ≤
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        (if dec₁ m₁ (fun i => (y i).1) ≠ m₂ ∨ dec₂ m₂ (fun i => (y i).2) ≠ m₁ then
          T m₁ m₂ y else 0) := by
    refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
      Finset.sum_le_sum fun y _ => ?_
    by_cases h : dec₁ m₁ (fun i => (y i).1) ≠ m₂
    · rw [ite_eq_left h, ite_eq_left (Or.inl h)]
    · rw [ite_eq_right h]; split_ifs <;> simp [hT0]
  have hsum := Finset.sum_le_sum fun m₁ (_ : m₁ ∈ Finset.univ) => hper m₁
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  calc 1 - ((Fintype.card Y₁ : ℝ) ^ n) / M₂ =
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ((M₁ : ℝ) * ((M₂ : ℝ) - (Fintype.card Y₁ : ℝ) ^ n)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.trans hle) hpos

theorem le_log2_card_Y₂ [Nonempty Y₂] (W : TwoWayChannel X₁ X₂ Y₁ Y₂) {R₁ R₂ : ℝ}
    (h : IsTWCAchievable W R₁ R₂) : R₁ ≤ log2 (Fintype.card Y₂) := by
  obtain ⟨hR₁, hR₂, h⟩ := h
  refine rate_le_log2_of_counting Fintype.card_pos (by norm_num : (0 : ℝ) < 1 / 2)
    fun ε hε => ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, dec₂, herr⟩ := hN n hn
  refine ⟨((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) : ℕ) : ℝ), ?_,
    le_trans (twc_err_ge₁ W (natMax_one_pos _) (natMax_one_pos _) enc₁ enc₂ dec₁ dec₂) herr⟩
  have := natMax_one_floor_ge n hR₁
  linarith

theorem le_log2_card_Y₁ [Nonempty Y₁] (W : TwoWayChannel X₁ X₂ Y₁ Y₂) {R₁ R₂ : ℝ}
    (h : IsTWCAchievable W R₁ R₂) : R₂ ≤ log2 (Fintype.card Y₁) := by
  obtain ⟨hR₁, hR₂, h⟩ := h
  refine rate_le_log2_of_counting Fintype.card_pos (by norm_num : (0 : ℝ) < 1 / 2)
    fun ε hε => ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, dec₂, herr⟩ := hN n hn
  refine ⟨((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) : ℕ) : ℝ), ?_,
    le_trans (twc_err_ge₂ W (natMax_one_pos _) (natMax_one_pos _) enc₁ enc₂ dec₁ dec₂) herr⟩
  have := natMax_one_floor_ge n hR₂
  linarith

/-- **Counting outer bound**: `C_TWC(W) ⊆ [0, log₂ |Y₂|] × [0, log₂ |Y₁|]`. -/
theorem twcCapacityRegion_subset_box [Nonempty Y₁] [Nonempty Y₂]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) :
    twcCapacityRegion W ⊆
      Set.Icc 0 (log2 (Fintype.card Y₂)) ×ˢ Set.Icc 0 (log2 (Fintype.card Y₁)) :=
  closure_minimal (fun p hp => ⟨⟨hp.1, le_log2_card_Y₂ W hp⟩, ⟨hp.2.1, le_log2_card_Y₁ W hp⟩⟩)
    (isClosed_Icc.prod isClosed_Icc)

/-! ### Axis achievability with non-adaptive codes -/

/-- The channel from terminal 1 to terminal 2 when terminal 2 always sends `x₂`. -/
def ch₁₂ (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (x₂ : X₂) : DMC X₁ Y₂ :=
  marginalSnd (dmcPrecomp W (fun x₁ => (x₁, x₂)))

/-- The channel from terminal 2 to terminal 1 when terminal 1 always sends `x₁`. -/
def ch₂₁ (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) : DMC X₂ Y₁ :=
  marginalFst (dmcPrecomp W (fun x₂ => (x₁, x₂)))

theorem isTWCAchievable_of₁ (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (x₂ : X₂) {R : ℝ}
    (h : IsDmcAchievableRate (ch₁₂ W x₂) R) : IsTWCAchievable W R 0 := by
  classical
  refine ⟨h.1, le_rfl, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero]
  refine ⟨fun i m _ => enc m i, fun _ _ _ => x₂, fun _ _ => 0, fun _ y₂ => dec y₂,
    le_of_eq_of_le ?_ herr⟩
  have hM : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold dmcAvgError
  rw [ite_eq_right hM, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fin.sum_univ_one]
  simp only [ne_eq, not_true_eq_false, false_or]
  exact sum_ite_snd_power (dmcPrecomp W (fun x₁ => (x₁, x₂))) (enc m) (fun b => ¬ dec b = m)

theorem isTWCAchievable_of₂ (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) {R : ℝ}
    (h : IsDmcAchievableRate (ch₂₁ W x₁) R) : IsTWCAchievable W 0 R := by
  classical
  refine ⟨le_rfl, h.1, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero]
  refine ⟨fun _ _ _ => x₁, fun i m _ => enc m i, fun _ y₁ => dec y₁, fun _ _ => 0,
    le_of_eq_of_le ?_ herr⟩
  have hM : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold dmcAvgError
  rw [ite_eq_right hM, one_mul, Fin.sum_univ_one]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [ne_eq, not_true_eq_false, or_false]
  exact sum_ite_fst_power (dmcPrecomp W (fun x₂ => (x₁, x₂))) (enc m) (fun a => ¬ dec a = m)

/-- **Axis achievability, direction 1 → 2**: `[0, C(p(y₂ | x₁, x₂))] × {0} ⊆ C_TWC(W)`. -/
theorem Icc_prod_zero_subset_twcCapacityRegion [Nonempty X₁]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (x₂ : X₂) :
    Set.Icc 0 (ch₁₂ W x₂).capacity ×ˢ {0} ⊆ twcCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_mono fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp2
  show IsTWCAchievable W p.1 p.2
  rw [hp2]
  exact isTWCAchievable_of₁ W x₂ hp1

/-- **Axis achievability, direction 2 → 1**: `{0} × [0, C(p(y₁ | x₁, x₂))] ⊆ C_TWC(W)`. -/
theorem zero_prod_Icc_subset_twcCapacityRegion [Nonempty X₂]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) :
    {0} ×ˢ Set.Icc 0 (ch₂₁ W x₁).capacity ⊆ twcCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_mono fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp1
  show IsTWCAchievable W p.1 p.2
  rw [hp1]
  exact isTWCAchievable_of₂ W x₁ hp2

theorem zero_mem_twcCapacityRegion [Nonempty X₁] [Nonempty X₂]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) : ((0 : ℝ), (0 : ℝ)) ∈ twcCapacityRegion W :=
  subset_closure (isTWCAchievable_of₁ W (Classical.arbitrary X₂) (isDmcAchievableRate_zero _))

/-! ### Shannon's `k`-letter inner bound -/

/-- `(1/k) I(S; Yᵏ | T) ≤ log₂ |Y|` (instances passed implicitly so that they unify with the
    ones baked into the region's definition). -/
theorem scaled_condMI_le {Y : Type*} [Fintype Y] [Nonempty Y] {α γ : Type*} {_i1 : Fintype α}
    {_i2 : Fintype γ} {k : ℕ} (hk : 0 < k) (Q : ProbDist (α × (Fin k → Y) × γ)) :
    (1 / (k : ℝ)) * condMutualInfo Q ≤ log2 (Fintype.card Y) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hb := condMutualInfo_le_log2_card Q
  rw [log2_card_pow] at hb
  calc (1 / (k : ℝ)) * condMutualInfo Q ≤ (1 / (k : ℝ)) * ((k : ℝ) * log2 (Fintype.card Y)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = log2 (Fintype.card Y) := by field_simp

/-- For `k ≥ 1`, `G_k(W) ⊆ [0, log₂ |Y₂|] × [0, log₂ |Y₁|]`. -/
theorem twcKLetterInnerBound_subset_box [Nonempty Y₁] [Nonempty Y₂] {k : ℕ} (hk : 0 < k)
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) :
    twcKLetterInnerBound k W ⊆
      Set.Icc 0 (log2 (Fintype.card Y₂)) ×ˢ Set.Icc 0 (log2 (Fintype.card Y₁)) := by
  refine closure_minimal (fun r hr => ?_) (isClosed_Icc.prod isClosed_Icc)
  obtain ⟨h1, h2, kQ, Pq, Ps₁, Ps₂, J, -, hr1, hr2⟩ := hr
  exact ⟨⟨h1, hr1.trans (scaled_condMI_le hk _)⟩, ⟨h2, hr2.trans (scaled_condMI_le hk _)⟩⟩

open Classical in
/-- `G_k(W)` contains `(0, 0)` (both terminals play constant strategies). -/
theorem zero_mem_twcKLetterInnerBound [Nonempty X₁] [Nonempty X₂] (k : ℕ)
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) : ((0 : ℝ), (0 : ℝ)) ∈ twcKLetterInnerBound k W := by
  let x₁ : X₁ := Classical.arbitrary X₁
  let x₂ : X₂ := Classical.arbitrary X₂
  let s₁ : CausalStrat k X₁ Y₁ := fun _ _ => x₁
  let s₂ : CausalStrat k X₂ Y₂ := fun _ _ => x₂
  let Q : ProbDist (Fin k → Y₁ × Y₂) :=
    { pmf := fun y => (W.power k).trans (fun _ => (x₁, x₂)) y
      nonneg := fun y => (W.power k).nonneg _ y
      sum_one := (W.power k).sum_one _ }
  let J : ProbDist (Fin 1 × CausalStrat k X₁ Y₁ × CausalStrat k X₂ Y₂ × (Fin k → Y₁ × Y₂)) :=
    Q.map (fun y => ((0 : Fin 1), s₁, s₂, y))
  refine subset_closure ⟨le_rfl, le_rfl, 1, ProbDist.uniform, fun _ => diracDist s₁,
    fun _ => diracDist s₂, J, ?_, ?_, ?_⟩
  · intro u t₁ t₂ y
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    simp only [J, ProbDist.map, ProbDist.uniform, diracDist, Fintype.card_fin, Nat.cast_one,
      div_one, one_mul]
    rw [Finset.sum_eq_single y]
    · by_cases h1 : t₁ = s₁
      · by_cases h2 : t₂ = s₂
        · subst h1; subst h2
          simp [Q, DMC.power, s₁, s₂]
        · simp [h2, Ne.symm h2]
      · simp [h1, Ne.symm h1]
    · intro y' _ hy
      simp [hy]
    · simp
  · exact mul_nonneg (by positivity) (condMutualInfo_nonneg _)
  · exact mul_nonneg (by positivity) (condMutualInfo_nonneg _)

end InfoTheory.Known.Certificates.TwoWayChannelCapacity
