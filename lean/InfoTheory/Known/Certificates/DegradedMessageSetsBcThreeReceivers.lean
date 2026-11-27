import InfoTheory.Problems.DegradedMessageSetsBcThreeReceivers
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.DegradedMessageSetsBcThreeReceivers`

The frozen statement asks whether, for every finite 3-receiver DM broadcast channel with a
common message `M₀` (to all receivers) and a private message `M₁` (to `Y₁` only), the operational
capacity region `dms3CapacityRegion W` equals the Nair–El Gamal inner bound
`nairElGamalInnerBound W` (Nair–El Gamal 2009, Prop. 5).

## Certified (about exactly these objects)
* `zero_mem_dms3CapacityRegion`, `zero_mem_nairElGamalInnerBound` — both sets contain `(0, 0)`
  (for a nonempty input alphabet), so neither side of the equation is vacuously empty.
* `dms3CapacityRegion_subset_sumRate` — the receiver-1 cut-set outer bound
  `R₀ + R₁ ≤ C(p(y₁|x))` on the operational region (El Gamal–Kim §8.1: receiver `Y₁` decodes
  both messages), proved from the Fano-based weak converse `dmcAvgError_rate_converse` of
  `InfoTheory.Bridge`. In particular the operational region is bounded.
* `mk_zero_mem_dms3CapacityRegion_iff` — the `R₀ = 0` edge of the operational region is
  exactly `[0, C(p(y₁|x))]`: with no common message the problem is the point-to-point channel
  `X → Y₁` (Shannon), so the operational definition reproduces the known single-user answer.
* `nairElGamalInnerBound_subset` — the inner bound lies in the closed set
  `{R₀, R₁ ≥ 0, R₀ + R₁ ≤ log₂ |Y₁|}`; in particular it is bounded.

## Not certified
* Achievability of the Nair–El Gamal region (`nairElGamalInnerBound W ⊆ dms3CapacityRegion W`)
  and the converses for the known solved classes (multilevel channels; `Y₁` less noisy than
  `Y₂` or `Y₃`): these need joint-typicality machinery for superposition coding, indirect
  decoding and mutual covering that `Bridge` does not provide.
* That the Nair–El Gamal region matches the operational `R₀ = 0` edge (it does: take all
  auxiliaries constant; this would need a chain-rule computation of the mutual informations).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.DegradedMessageSetsBcThreeReceivers

open InfoTheory InfoTheory.Bridge InfoTheory.Problems.DegradedMessageSetsBcThreeReceivers

section Marginal

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]

/-- Marginal channel `p(y₁ | x)` onto the first output coordinate. -/
def marg1 (W : DMC X (A × B)) : DMC X A where
  trans x a := ∑ b, W.trans x (a, b)
  nonneg x a := Finset.sum_nonneg fun b _ => W.nonneg x (a, b)
  sum_one x := by rw [← Fintype.sum_prod_type']; exact W.sum_one x

theorem sum_tuple_pair_split {n : ℕ} (F : (Fin n → A × B) → ℝ) :
    ∑ y, F y = ∑ a : Fin n → A, ∑ b : Fin n → B, F (fun i => (a i, b i)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (zipEquiv A B n) (fun p => F (fun i => (p.1 i, p.2 i))) F
    (fun _ => rfl)).symm

theorem marg1_power_trans (W : DMC X (A × B)) {n : ℕ} (x : Fin n → X) (a : Fin n → A) :
    ((marg1 W).power n).trans x a =
      ∑ b : Fin n → B, (W.power n).trans x (fun i => (a i, b i)) := by
  classical
  simp only [DMC.power, marg1]
  exact Fintype.prod_sum (fun i b => W.trans (x i) (a i, b))

/-- An event depending only on the first output block has the same probability under the
    first marginal channel. -/
theorem sum_ite_fst_power (W : DMC X (A × B)) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → A) → Prop) [DecidablePred p] :
    ∑ y : Fin n → A × B, (if p (fun i => (y i).1) then (W.power n).trans x y else 0) =
      ∑ a, if p a then ((marg1 W).power n).trans x a else 0 := by
  rw [sum_tuple_pair_split]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [marg1_power_trans]
  show ∑ b : Fin n → B, (if p a then (W.power n).trans x (fun i => (a i, b i)) else 0) = _
  split_ifs <;> simp

end Marginal

variable {X Y₁ Y₂ Y₃ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]

/-- The configuration-A error of `IsDMS3Achievable`. -/
noncomputable abbrev dmsErr (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (n M₀ M₁ : ℕ)
    (enc : Fin M₀ → Fin M₁ → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁)
    (dec₂ : (Fin n → Y₂) → Fin M₀) (dec₃ : (Fin n → Y₃) → Fin M₀) : ℝ :=
  ((1 : ℝ) / ((M₀ * M₁ : ℕ) : ℝ)) *
    ∑ m₀ : Fin M₀, ∑ m₁ : Fin M₁, ∑ y : Fin n → Y₁ × Y₂ × Y₃,
      if dec₁ (fun i => (y i).1) ≠ (m₀, m₁) ∨
         dec₂ (fun i => (y i).2.1) ≠ m₀ ∨
         dec₃ (fun i => (y i).2.2) ≠ m₀
      then (W.power n).trans (enc m₀ m₁) y else 0

/-- From a configuration-A code, the product code `(m₀, m₁) ↦ enc m₀ m₁` decoded by `dec₁`
    is a point-to-point code for `p(y₁ | x)` with `M₀ M₁` messages and no larger error. -/
theorem dmcAvgError_le_dmsErr [DecidableEq Y₁] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {n M₀ M₁ : ℕ}
    (h₀ : 0 < M₀) (h₁ : 0 < M₁)
    (enc : Fin M₀ → Fin M₁ → Fin n → X) (dec₁ : (Fin n → Y₁) → Fin M₀ × Fin M₁)
    (dec₂ : (Fin n → Y₂) → Fin M₀) (dec₃ : (Fin n → Y₃) → Fin M₀) :
    dmcAvgError (marg1 W) n (M₀ * M₁)
        (fun k => enc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        (fun a => finProdFinEquiv (dec₁ a)) ≤
      dmsErr W n M₀ M₁ enc dec₁ dec₂ dec₃ := by
  classical
  have hM : M₀ * M₁ ≠ 0 := (Nat.mul_pos h₀ h₁).ne'
  unfold dmcAvgError dmsErr
  rw [ite_eq_right hM]
  have hMr : (0 : ℝ) ≤ (1 : ℝ) / ((M₀ * M₁ : ℕ) : ℝ) := by positivity
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Fintype.sum_prod_type' (fun m₀ m₁ => ∑ y : Fin n → Y₁ × Y₂ × Y₃,
      if dec₁ (fun i => (y i).1) ≠ (m₀, m₁) ∨ dec₂ (fun i => (y i).2.1) ≠ m₀ ∨
        dec₃ (fun i => (y i).2.2) ≠ m₀ then (W.power n).trans (enc m₀ m₁) y else 0)]
  rw [← Fintype.sum_equiv finProdFinEquiv (fun p : Fin M₀ × Fin M₁ => ∑ a : Fin n → Y₁,
      if finProdFinEquiv (dec₁ a) ≠ finProdFinEquiv p then
        ((marg1 W).power n).trans
          (enc (finProdFinEquiv.symm (finProdFinEquiv p)).1
            (finProdFinEquiv.symm (finProdFinEquiv p)).2) a else 0) _ (fun _ => rfl)]
  refine Finset.sum_le_sum fun p _ => ?_
  simp only [Equiv.symm_apply_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  rw [← sum_ite_fst_power W (enc p.1 p.2) (fun a => ¬ dec₁ a = p)]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hA : dec₁ (fun i => (y i).1) = p
  · rw [ite_eq_right (not_not.mpr hA)]
    split_ifs
    · exact (W.power n).nonneg _ _
    · exact le_rfl
  · rw [ite_eq_left hA, ite_eq_left (Or.inl (by rw [Prod.mk.eta]; exact hA))]

private lemma natMax_one_floor_ge (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
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

private lemma log2_two_rpow' (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma log2_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log2 a ≤ log2 b := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log ha hab) (Real.log_pos one_lt_two).le

/-- **Receiver-1 cut-set outer bound** (El Gamal–Kim §8.1): every achievable `(R₀, R₁)` has
    `R₀ + R₁ ≤ C(p(y₁ | x))`. -/
theorem sumRate_le_of_achievable (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {R₀ R₁ : ℝ}
    (h : IsDMS3Achievable W R₀ R₁) : R₀ + R₁ ≤ (marg1 W).capacity := by
  classical
  obtain ⟨hR₀, hR₁, hach⟩ := h
  set S := R₀ + R₁ with hS
  set C := (marg1 W).capacity with hC
  have hC0 : 0 ≤ C := capacity_nonneg _
  by_contra hlt
  push Not at hlt
  have hSpos : 0 < S := lt_of_le_of_lt hC0 hlt
  set ε : ℝ := (S - C) / (2 * S) with hε
  have hεpos : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have hε1 : ε ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ (by linarith)]; linarith
  obtain ⟨N, hN⟩ := hach ε hεpos
  -- a large blocklength
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (6 / (S - C))
  set n := max N (n₀ + 1) with hn
  have hnN : N ≤ n := le_max_left _ _
  have hn1 : n₀ + 1 ≤ n := le_max_right _ _
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos _) hn1
  have hnr : (6 / (S - C)) < (n : ℝ) := by
    have : (n₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hc := hN n hnN
  dsimp only at hc
  have h₀ : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀))) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have h₁ : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have a0 := natMax_one_floor_ge n hR₀
  have a1 := natMax_one_floor_ge n hR₁
  generalize Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀))) = M₀ at hc h₀ a0
  generalize Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) = M₁ at hc h₁ a1
  obtain ⟨enc, dec₁, dec₂, dec₃, herr⟩ := hc
  -- product lower bound `M₀ M₁ ≥ 2^{nS} / 4`
  have hprod : (2 : ℝ) ^ ((n : ℝ) * S) / 4 ≤ ((M₀ * M₁ : ℕ) : ℝ) := by
    have e : (2 : ℝ) ^ ((n : ℝ) * S) = (2 : ℝ) ^ ((n : ℝ) * R₀) * (2 : ℝ) ^ ((n : ℝ) * R₁) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; rw [hS]; ring
    push_cast
    rw [e]
    have p0 : 0 ≤ (2 : ℝ) ^ ((n : ℝ) * R₀) / 2 := by positivity
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
  -- main inequality `(1 - ε) (n S - 2) ≤ n C + 1`
  have hmain : (1 - ε) * ((n : ℝ) * S - 2) ≤ (n : ℝ) * C + 1 := by
    by_cases h2 : 2 ≤ M₀ * M₁
    · have hconv := dmcAvgError_rate_converse (marg1 W) n (M₀ * M₁) hnpos h2
        (fun k => enc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        (fun a => finProdFinEquiv (dec₁ a))
      have hle := dmcAvgError_le_dmsErr W h₀ h₁ enc dec₁ dec₂ dec₃
      set pe := dmcAvgError (marg1 W) n (M₀ * M₁)
        (fun k => enc (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        (fun a => finProdFinEquiv (dec₁ a)) with hpe
      have hpeε : pe ≤ ε := hle.trans herr
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
  -- contradiction for large `n`
  have hkey : (1 - ε) * S = (S + C) / 2 := by
    rw [hε]; field_simp; ring
  have : (n : ℝ) * ((S - C) / 2) ≤ 3 := by nlinarith
  have hSC : 0 < S - C := by linarith
  rw [div_lt_iff₀ hSC] at hnr
  nlinarith

/-- **Outer bound on the operational region**: `C ⊆ {R₀ ≥ 0, R₁ ≥ 0, R₀ + R₁ ≤ C(p(y₁|x))}`. -/
theorem dms3CapacityRegion_subset_sumRate (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    dms3CapacityRegion W ⊆
      { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 + r.2 ≤ (marg1 W).capacity } := by
  refine closure_minimal (fun r hr => ⟨hr.1, hr.2.1, sumRate_le_of_achievable W hr⟩) ?_
  refine (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

/-- With no common message, a point-to-point code for `p(y₁|x)` is a configuration-A code with
    the same error. -/
theorem isDMS3Achievable_zero_of_dmc (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {R₁ : ℝ}
    (h : IsDmcAchievableRate (marg1 W) R₁) : IsDMS3Achievable W 0 R₁ := by
  classical
  obtain ⟨hR₁, hach⟩ := h
  refine ⟨le_rfl, hR₁, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hach ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc', dec', herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero n]
  set M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) with hM₁
  have hM₁pos : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨fun _ m₁ => enc' m₁, fun a => (0, dec' a), fun _ => 0, fun _ => 0, ?_⟩
  refine le_of_eq_of_le ?_ herr
  unfold dmcAvgError
  rw [ite_eq_right hM₁pos.ne', Nat.one_mul, Fin.sum_univ_one]
  congr 1
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  have hsub : ∀ z : Fin 1, ¬ ((fun _ => (0 : Fin 1)) z ≠ (0 : Fin 1)) :=
    fun z => not_not.mpr rfl
  have hiff : ∀ y : Fin n → Y₁ × Y₂ × Y₃,
      ((0 : Fin 1), dec' (fun i => (y i).1)) ≠ (0, m₁) ∨ (0 : Fin 1) ≠ 0 ∨ (0 : Fin 1) ≠ 0 ↔
        dec' (fun i => (y i).1) ≠ m₁ := by
    intro y
    simp
  simp_rw [hiff]
  exact sum_ite_fst_power W (enc' m₁) (fun a => dec' a ≠ m₁)

/-- The trivial code `M₀ = M₁ = 1` shows `(0, 0)` is achievable. -/
theorem isDMS3Achievable_zero [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    IsDMS3Achievable W 0 0 :=
  isDMS3Achievable_zero_of_dmc W (isDmcAchievableRate_zero (marg1 W))

theorem zero_mem_dms3CapacityRegion [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ((0 : ℝ), (0 : ℝ)) ∈ dms3CapacityRegion W :=
  subset_closure (isDMS3Achievable_zero W)

/-- **Single-user edge**: `(0, R₁) ∈ C` iff `0 ≤ R₁ ≤ C(p(y₁|x))` (Shannon's theorem for the
    channel `X → Y₁`). -/
theorem mk_zero_mem_dms3CapacityRegion_iff [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃)
    (R₁ : ℝ) : ((0 : ℝ), R₁) ∈ dms3CapacityRegion W ↔ 0 ≤ R₁ ∧ R₁ ≤ (marg1 W).capacity := by
  constructor
  · intro h
    obtain ⟨-, h2, h3⟩ := dms3CapacityRegion_subset_sumRate W h
    exact ⟨h2, by simpa using h3⟩
  · rintro ⟨h0, h1⟩
    rcases eq_or_lt_of_le (capacity_nonneg (marg1 W)) with hC | hC
    · have : R₁ = 0 := le_antisymm (hC ▸ h1) h0
      subst this
      exact zero_mem_dms3CapacityRegion W
    · have hsub : ({(0 : ℝ)} : Set ℝ) ×ˢ Set.Ico 0 (marg1 W).capacity ⊆
          { r : ℝ × ℝ | IsDMS3Achievable W r.1 r.2 } := by
        rintro ⟨a, b⟩ ⟨ha, hb⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact isDMS3Achievable_zero_of_dmc W
          (shannon_channel_coding_achievability (marg1 W) b hb.1 hb.2)
      have hcl := closure_mono hsub
      rw [closure_prod_eq, closure_singleton, closure_Ico hC.ne] at hcl
      exact hcl ⟨rfl, h0, h1⟩

/-- Shannon entropy of a distribution on a subsingleton type vanishes. -/
theorem shannonEntropy_subsingleton {α : Type*} [Fintype α] [Subsingleton α] (P : ProbDist α) :
    shannonEntropy P = 0 := by
  unfold shannonEntropy
  rcases isEmpty_or_nonempty α with hα | hα
  · simp
  · obtain ⟨a⟩ := hα
    rw [Fintype.sum_subsingleton _ a]
    have h1 : P.pmf a = 1 := by rw [← P.sum_one, Fintype.sum_subsingleton _ a]
    simp [h1, negPLogP, log2]

/-- `(0, 0)` lies in the Nair–El Gamal inner bound (all auxiliaries constant). -/
theorem zero_mem_nairElGamalInnerBound [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ((0 : ℝ), (0 : ℝ)) ∈ nairElGamalInnerBound W := by
  apply subset_closure
  refine ⟨le_rfl, le_rfl, 1, 1, 1, ProbDist.uniform, ?_⟩
  intro J IV2Y2 IV3Y3 IV2V3gU1 IXY1gV2 IXY1gV3 IXY1gU1 IXY1gV23 IXY1
  have hI0 : IV2V3gU1 = 0 := by
    show condMutualInfo _ = 0
    unfold condMutualInfo
    simp only [shannonEntropy_subsingleton, sub_zero, add_zero]
  have a1 : 0 ≤ IV2Y2 := mutualInfo_nonneg _
  have a2 : 0 ≤ IV3Y3 := mutualInfo_nonneg _
  have a3 : 0 ≤ IXY1gV2 := condMutualInfo_nonneg _
  have a4 : 0 ≤ IXY1gV3 := condMutualInfo_nonneg _
  have a5 : 0 ≤ IXY1gU1 := condMutualInfo_nonneg _
  have a6 : 0 ≤ IXY1gV23 := condMutualInfo_nonneg _
  have a7 : 0 ≤ IXY1 := mutualInfo_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end InfoTheory.Known.Certificates.DegradedMessageSetsBcThreeReceivers
