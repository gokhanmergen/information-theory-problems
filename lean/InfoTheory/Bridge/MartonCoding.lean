import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability
import InfoTheory.Bridge.BroadcastCoding
import InfoTheory.Bridge.WynerZiv

/-!
# Marton's Inner Bound with Common Auxiliary `W` (Marton 1979; El Gamal–Kim Ch. 8)

Purely additive, kernel-verified formalization of **Marton's Coding Theorem** for two-receiver
Discrete Memoryless Broadcast Channels (`InfoTheory.BroadcastChannel`, `IsBCAchievable`,
`bcCapacityRegion`, `martonInnerBound`; El Gamal–Kim Lemma 8.1, Prop. 8.1, Thm. 8.3):

1. **Mutual Covering Lemma (El Gamal–Kim Lemma 8.1; Marton 1979)**:
   - `mutual_covering_chebyshev_bound`: exact finite-sum second-moment / Chebyshev bound for
     drawing `L₁` sequences from `Q₁` and `L₂` sequences from `Q₂` independently and testing
     joint membership in `S`.
   - `mutual_covering_lemma`: for any `P : ProbDist (W × U × V)` and `R₁ ≥ 0, R₂ ≥ 0` with
     `I(U; V | W) < R₁ + R₂`, drawing `L₁ = ⌈2^(n R₁)⌉` conditionally i.i.d. `U^n` sequences
     and `L₂ = ⌈2^(n R₂)⌉` conditionally i.i.d. `V^n` sequences given `W^n ~ P_W^n`, the
     probability that no pair `(l₁, l₂)` is jointly strongly `ε`-typical with `W^n` vanishes
     as `n → ∞`.

2. **Fourier–Motzkin Rate Splitting (`marton_rate_splitting`)**:
   - Whenever `I(U; V | W) < I(U; Y₁ | W) + I(V; Y₂ | W)` and `(R₁, R₂) ≥ 0` lies strictly
     inside the Marton pentagon, splits `R₁ = R₁₀ + R₁₁`, `R₂ = R₂₀ + R₂₂` and produces
     binning rates `R₁', R₂' ≥ 0` with `I(U; V | W) < R₁' + R₂'` and all packing inequalities
     strictly satisfied.

3. **Marton's Random Coding Bound, Achievability & Inner Bound**:
   - `martonJoint`: single-letter joint law `((W × U × V × X) × (Y₁ × Y₂))` matching
     `InfoTheory.martonInnerBound`.
   - `marton_random_coding_bound`: finite-blocklength Marton coding existence bound via
     random cloud + conditional `U`/`V` bin codebooks, strong-typicality encoding,
     `WynerZiv.markov_lemma_of_channel` for the true codeword, pointwise conditional/unconditional
     packing bounds for wrong messages, and randomized-to-deterministic encoder averaging over
     `P_{X | W, U, V}^n`.
   - `marton_coding_achievability`: every rate pair `(R₁, R₂) ≥ 0` strictly inside the Marton
     pentagon for a single-letter `Pwuvx : ProbDist (W × U × V × X)` is `IsBCAchievable W R₁ R₂`.
   - `martonInnerBound_subset_bcCapacityRegion`: `martonInnerBound W ⊆ bcCapacityRegion W` for
     every two-receiver DMBC `W`.
-/

open scoped BigOperators Topology
open InfoTheory InfoTheory.Bridge Set Filter

namespace InfoTheory.Bridge

/-! ### 0. Private Helper Lemmas -/

section MartonHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma mc_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

private lemma mc_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma mc_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  apply mc_probDist_ext; intro a
  unfold ProbDist.map ProbDist.fst; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma mc_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  apply mc_probDist_ext; intro b
  unfold ProbDist.map ProbDist.snd; dsimp only
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single b]
  · simp
  · intro b' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma mc_exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (B : ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1)
    (hle : ∑ i : ι, w i * f i ≤ B) :
    ∃ i : ι, f i ≤ B := by
  by_contra hall
  push Not at hall
  have hpos : ∃ i₀ : ι, 0 < w i₀ := by
    by_contra hno
    push Not at hno
    have hzero : ∑ i : ι, w i = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hno i) (hw0 i)
    linarith
  obtain ⟨i₀, hi₀⟩ := hpos
  have hlt : ∑ i : ι, w i * B < ∑ i : ι, w i * f i :=
    Finset.sum_lt_sum
      (fun i _ => mul_le_mul_of_nonneg_left (le_of_lt (hall i)) (hw0 i))
      ⟨i₀, Finset.mem_univ i₀, mul_lt_mul_of_pos_left (hall i₀) hi₀⟩
  have hB : ∑ i : ι, w i * B = B := by rw [← Finset.sum_mul, hw1, one_mul]
  linarith

private lemma mc_two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {n : ℕ} (hn : log2 (1 / c) / ε ≤ (n : ℝ)) :
    (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ c := by
  have h1 : log2 (1 / c) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog : Real.log (1 / c) ≤ (n : ℝ) * ε * Real.log 2 := by
    unfold log2 at h1; exact (div_le_iff₀ hlog2).mp h1
  have hexp : 1 / c ≤ (2 : ℝ) ^ ((n : ℝ) * ε) := by
    calc 1 / c
      _ = Real.exp (Real.log (1 / c)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp ((n : ℝ) * ε * Real.log 2) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (Real.log 2 * ((n : ℝ) * ε)) := by ring_nf
      _ = (2 : ℝ) ^ ((n : ℝ) * ε) := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * ε)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul1 : (2 : ℝ) ^ (-((n : ℝ) * ε)) * (2 : ℝ) ^ ((n : ℝ) * ε) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hmul2 : (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ 1 :=
    calc (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) * (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_right hexp (le_of_lt hpos)
      _ = 1 := by rw [mul_comm, hmul1]
  have hmul3 := mul_le_mul_of_nonneg_left hmul2 (le_of_lt hc)
  have hsimp : c * ((1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))) = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
    field_simp [ne_of_gt hc]
  linarith

private lemma mc_ceil_two_rpow_pos (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 < Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R)) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    have hle := Nat.le_ceil ((2 : ℝ) ^ ((n : ℝ) * R))
    rw [h0, Nat.cast_zero] at hle
    linarith))

private lemma mc_two_rpow_le_ceil (n : ℕ) (R : ℝ) :
    (2 : ℝ) ^ ((n : ℝ) * R) ≤ (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) :=
  Nat.le_ceil _

private lemma mc_ceil_two_rpow_le_two_mul (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hlt : (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

private lemma mc_ceil_two_rpow_zero (n : ℕ) :
    Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ))) = 1 := by
  simp

private lemma mc_max_floor_le_mul_ceil (n : ℕ) {R₁ R₂ : ℝ} (h1 : 0 ≤ R₁) (h2 : 0 ≤ R₂) :
    Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)))) ≤
      Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁)) * Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂)) := by
  have hc1 := mc_ceil_two_rpow_pos n h1
  have hc2 := mc_ceil_two_rpow_pos n h2
  refine max_le (Nat.mul_pos hc1 hc2) ?_
  refine Nat.floor_le_of_le ?_
  rw [Nat.cast_mul]
  calc (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂))
    _ = (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ ((n : ℝ) * R₂) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    _ ≤ (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁)) : ℝ) *
          (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂)) : ℝ) :=
        mul_le_mul (mc_two_rpow_le_ceil n R₁) (mc_two_rpow_le_ceil n R₂)
          (by positivity) (by positivity)

private lemma mc_strongTypicalSet_mono (P : ProbDist α) (n : ℕ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    strongTypicalSet P n ε₁ ⊆ strongTypicalSet P n ε₂ := by
  classical
  intro x hx
  rw [mem_strongTypicalSet] at hx ⊢
  intro a
  exact le_trans (hx a) (mul_le_mul_of_nonneg_right hε (P.nonneg a))

private lemma mc_condChannelOfJoint_power_eq_div (P : ProbDist (α × β)) (n : ℕ)
    (a : Fin n → α) (b : Fin n → β) (ha : (iidDist P.fst n).pmf a ≠ 0) :
    ((condChannelOfJoint P).power n).trans a b =
      (iidDist P n).pmf (fun i => (a i, b i)) / (iidDist P.fst n).pmf a := by
  rw [eq_div_iff ha, mul_comm]
  exact (jointIidDist_eq_fst_mul_condChannelPower P n a b).symm

/-- Conditional mutual information with a `Unit` first argument is identically `0`. -/
private lemma mc_condMutualInfo_unit (Q : ProbDist (Unit × β × γ)) :
    condMutualInfo Q = 0 := by
  let e1 : (Unit × β × γ) ≃ (β × γ) := Equiv.punitProd (β × γ)
  let e2 : (Unit × γ) ≃ γ := Equiv.punitProd γ
  have h1 : Q.map (fun t => (t.2.1, t.2.2)) = Q.map e1 := rfl
  have h2 : Q.map (fun t => t.2.2) = (Q.map (fun t => (t.1, t.2.2))).map e2 := by
    rw [map_comp_eq]; rfl
  unfold condMutualInfo; dsimp only
  rw [h1, h2, shannonEntropy_map_equiv e1 Q, shannonEntropy_map_equiv e2 _]
  ring

open Classical in
/-- **Conditional Typicality Lemma via `markov_lemma`** (El Gamal–Kim §2.5):
    for any joint distribution `P : ProbDist (α × β)`, `0 < n`, `0 ≤ ε₁ < ε₂`, and fixed
    `a ∈ strongTypicalSet P.fst n ε₁`, drawing `B^n ~ P_{B|A}^n(· | a)` fails to be jointly
    strongly `ε₂`-typical with probability at most `(∑_{ab : P(ab) > 0} 1 / P(ab)²) / (n (ε₂ - ε₁)²)`. -/
private lemma mc_cond_typical_prob_not_mem_le (P : ProbDist (α × β)) {n : ℕ} (hn : 0 < n)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε : ε₁ < ε₂)
    {a : Fin n → α} (ha : a ∈ strongTypicalSet P.fst n ε₁) :
    ∑ b : Fin n → β, ((condChannelOfJoint P).power n).trans a b *
        (if (fun i => (a i, b i)) ∉ strongTypicalSet P n ε₂ then (1 : ℝ) else 0) ≤
      (∑ ab : α × β, if 0 < P.pmf ab then 1 / P.pmf ab ^ 2 else 0) /
        ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
  let e : (α × β) ≃ (α × β × Unit) :=
    { toFun := fun ab => (ab.1, ab.2, ())
      invFun := fun t => (t.1, t.2.1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _, ()⟩ => rfl }
  let Q : ProbDist (α × β × Unit) := P.map e
  have hQ_ab : Q.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q; rw [map_comp_eq]
    apply mc_probDist_ext; intro ab
    unfold ProbDist.map; dsimp only [e]; simp
  have hQ_au : Q.map (fun t => (t.1, t.2.2)) = P.fst.map (fun x => (x, ())) := by
    unfold Q; rw [map_comp_eq, ← mc_probDist_map_fst, map_comp_eq]; rfl
  have hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 :=
    mc_condMutualInfo_unit _
  have hau : (fun i => (a i, ())) ∈ strongTypicalSet (Q.map (fun t => (t.1, t.2.2))) n ε₁ := by
    rw [hQ_au]
    exact strongTypicalSet_map P.fst (fun x => (x, ())) n ε₁ ha
  have hmk := markov_lemma Q hmarkov hn hε₁ hε hau
  dsimp only at hmk
  rw [hQ_ab] at hmk
  have hQ_pmf : ∀ ab : α × β, Q.pmf (e ab) = P.pmf ab := fun ab => by
    unfold Q ProbDist.map; dsimp only
    rw [Finset.sum_eq_single ab]
    · simp
    · intro ab' _ hne
      split_ifs with h
      · exact absurd (e.injective h) hne
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  have hconst : (∑ t : α × β × Unit, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) =
      ∑ ab : α × β, if 0 < P.pmf ab then 1 / P.pmf ab ^ 2 else 0 := by
    symm
    exact Fintype.sum_equiv e _ _ (fun ab => by rw [hQ_pmf ab])
  rw [hconst] at hmk
  refine le_trans (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_
    (((condChannelOfJoint P).power n).nonneg a b)) hmk
  by_cases hmem : (fun i => (a i, b i, ())) ∈ strongTypicalSet Q n ε₂
  · have hmap : (fun i => (a i, b i)) ∈ strongTypicalSet P n ε₂ := by
      have hm := strongTypicalSet_map Q (fun t => (t.1, t.2.1)) n ε₂ hmem
      rwa [hQ_ab] at hm
    simp [hmem, hmap]
  · simp only [hmem, not_false_eq_true, ↓reduceIte]
    split_ifs <;> norm_num

open Classical in
/-- **Channel-Parameterized Conditional Typicality Lemma via `markov_lemma_of_channel`**:
    for any input law `P_A : ProbDist α`, DMC `W : DMC α β`, `0 < n`, `0 ≤ ε₁ < ε₂`, and fixed
    `a ∈ strongTypicalSet P_A n ε₁`, `W.power n` produces a jointly strongly `ε₂`-typical pair
    `(a, b)` with failure probability `≤ C / (n (ε₂ - ε₁)²)`. -/
private lemma mc_channel_typical_prob_not_mem_le (P_A : ProbDist α) (W : DMC α β)
    {n : ℕ} (hn : 0 < n) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε : ε₁ < ε₂)
    {a : Fin n → α} (ha : a ∈ strongTypicalSet P_A n ε₁) :
    ∑ b : Fin n → β, (W.power n).trans a b *
        (if (fun i => (a i, b i)) ∉ strongTypicalSet (W.joint P_A) n ε₂ then (1 : ℝ) else 0) ≤
      (∑ ab : α × β, if 0 < (W.joint P_A).pmf ab then 1 / (W.joint P_A).pmf ab ^ 2 else 0) /
        ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
  let P := W.joint P_A
  let e : (α × β) ≃ (α × β × Unit) :=
    { toFun := fun ab => (ab.1, ab.2, ())
      invFun := fun t => (t.1, t.2.1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _, ()⟩ => rfl }
  let Q : ProbDist (α × β × Unit) := P.map e
  have hQ_ab : Q.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q; rw [map_comp_eq]
    apply mc_probDist_ext; intro ab
    unfold ProbDist.map; dsimp only [e]; simp
  have hQ_a : Q.map (fun t => t.1) = P_A := by
    have h1 : Q.map (fun t => t.1) = (Q.map (fun t => (t.1, t.2.1))).map Prod.fst := by
      conv_rhs => rw [map_comp_eq]
      rfl
    rw [h1, hQ_ab, mc_probDist_map_fst, dmc_joint_fst]
  have hQ_au : Q.map (fun t => (t.1, t.2.2)) = P_A.map (fun x => (x, ())) := by
    have h1 : Q.map (fun t => (t.1, t.2.2)) = (Q.map (fun t => t.1)).map (fun x => (x, ())) := by
      conv_rhs => rw [map_comp_eq]
      rfl
    rw [h1, hQ_a]
  have hW : ∀ x y, (Q.map (fun t => (t.1, t.2.1))).pmf (x, y) =
      (Q.map (fun t => t.1)).pmf x * W.trans x y := by
    intro x y; rw [hQ_ab, hQ_a]; rfl
  have hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 :=
    mc_condMutualInfo_unit _
  have hau : (fun i => (a i, ())) ∈ strongTypicalSet (Q.map (fun t => (t.1, t.2.2))) n ε₁ := by
    rw [hQ_au]
    exact strongTypicalSet_map P_A (fun x => (x, ())) n ε₁ ha
  have hmk := markov_lemma_of_channel Q W hW hmarkov hn hε₁ hε hau
  have hQ_pmf : ∀ ab : α × β, Q.pmf (e ab) = P.pmf ab := fun ab => by
    unfold Q ProbDist.map; dsimp only
    rw [Finset.sum_eq_single ab]
    · simp
    · intro ab' _ hne
      split_ifs with h
      · exact absurd (e.injective h) hne
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  have hconst : (∑ t : α × β × Unit, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) =
      ∑ ab : α × β, if 0 < P.pmf ab then 1 / P.pmf ab ^ 2 else 0 := by
    symm
    exact Fintype.sum_equiv e _ _ (fun ab => by rw [hQ_pmf ab])
  rw [hconst] at hmk
  refine le_trans (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_
    ((W.power n).nonneg a b)) hmk
  by_cases hmem : (fun i => (a i, b i, ())) ∈ strongTypicalSet Q n ε₂
  · have hmap : (fun i => (a i, b i)) ∈ strongTypicalSet (W.joint P_A) n ε₂ := by
      have hm := strongTypicalSet_map Q (fun t => (t.1, t.2.1)) n ε₂ hmem
      rwa [hQ_ab] at hm
    simp [hmem, hmap]
  · simp only [hmem, not_false_eq_true, ↓reduceIte]
    split_ifs <;> norm_num

/-- Entropy expansion of `I(U; V | W)` for `P : ProbDist (W × U × V)`. -/
private lemma mc_condMutualInfo_triple_eq {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
    (P : ProbDist (W × U × V)) :
    condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) =
      shannonEntropy (P.map (fun t => (t.1, t.2.1))) +
      shannonEntropy (P.map (fun t => (t.1, t.2.2))) -
      shannonEntropy P -
      shannonEntropy (P.map (fun t => t.1)) := by
  let eAll : (W × U × V) ≃ (U × V × W) :=
    { toFun := fun t => (t.2.1, t.2.2, t.1)
      invFun := fun t => (t.2.2, t.1, t.2.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have h1 : (P.map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => (t.1, t.2.2)) =
      (P.map (fun t => (t.1, t.2.1))).map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h2 : (P.map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => (t.2.1, t.2.2)) =
      (P.map (fun t => (t.1, t.2.2))).map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h3 : (P.map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => t.2.2) =
      P.map (fun t => t.1) := by
    rw [map_comp_eq]; rfl
  have h4 : P.map (fun t => (t.2.1, t.2.2, t.1)) = P.map eAll := rfl
  unfold condMutualInfo; dsimp only
  rw [h1, h2, h3, h4, shannonEntropy_swap, shannonEntropy_swap, shannonEntropy_map_equiv eAll]

/-- Symmetry `I(U; V | W) = I(V; U | W)`. -/
private lemma mc_condMutualInfo_symm {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
    (P : ProbDist (W × U × V)) :
    condMutualInfo (P.map (fun t => (t.2.2, t.2.1, t.1))) =
      condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) := by
  let e : (W × U × V) ≃ (W × V × U) :=
    { toFun := fun t => (t.1, t.2.2, t.2.1)
      invFun := fun t => (t.1, t.2.2, t.2.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have h1 := mc_condMutualInfo_triple_eq (P.map e)
  have h2 := mc_condMutualInfo_triple_eq P
  have hm1 : (P.map e).map (fun t => (t.2.1, t.2.2, t.1)) =
      P.map (fun t => (t.2.2, t.2.1, t.1)) := by rw [map_comp_eq]; rfl
  have hm2 : (P.map e).map (fun t => (t.1, t.2.1)) = P.map (fun t => (t.1, t.2.2)) := by
    rw [map_comp_eq]; rfl
  have hm3 : (P.map e).map (fun t => (t.1, t.2.2)) = P.map (fun t => (t.1, t.2.1)) := by
    rw [map_comp_eq]; rfl
  have hm4 : (P.map e).map (fun t => t.1) = P.map (fun t => t.1) := by
    rw [map_comp_eq]; rfl
  rw [hm1, hm2, hm3, hm4, shannonEntropy_map_equiv e] at h1
  linarith

/-- Chain rule `I(W; Y) + I(U; Y | W) = I(W, U; Y)`. -/
private lemma mc_mutualInfo_chain_rule {W U Y : Type*} [Fintype W] [Fintype U] [Fintype Y]
    (P : ProbDist (W × U × Y)) :
    mutualInfo (P.map (fun t => (t.1, t.2.2))) +
      condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) =
    mutualInfo (P.map (fun t => ((t.1, t.2.1), t.2.2))) := by
  rw [mc_condMutualInfo_triple_eq]
  let e : (W × U × Y) ≃ ((W × U) × Y) :=
    { toFun := fun t => ((t.1, t.2.1), t.2.2)
      invFun := fun t => (t.1.1, t.1.2, t.2)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  have h1 : (P.map (fun t => (t.1, t.2.2))).fst = P.map (fun t => t.1) := by
    rw [← mc_probDist_map_fst, map_comp_eq]; rfl
  have h2 : (P.map (fun t => (t.1, t.2.2))).snd = P.map (fun t => t.2.2) := by
    rw [← mc_probDist_map_snd, map_comp_eq]; rfl
  have h3 : (P.map (fun t => ((t.1, t.2.1), t.2.2))).fst = P.map (fun t => (t.1, t.2.1)) := by
    rw [← mc_probDist_map_fst, map_comp_eq]; rfl
  have h4 : (P.map (fun t => ((t.1, t.2.1), t.2.2))).snd = P.map (fun t => t.2.2) := by
    rw [← mc_probDist_map_snd, map_comp_eq]; rfl
  have h5 : P.map (fun t => ((t.1, t.2.1), t.2.2)) = P.map e := rfl
  unfold mutualInfo
  rw [h1, h2, h3, h4, h5, shannonEntropy_map_equiv e]
  ring

private lemma mc_iidDist_marginal_snd {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
    (P : ProbDist (W × U × V)) (n : ℕ) (w : Fin n → W) (v : Fin n → V) :
    ∑ u : Fin n → U, (iidDist P n).pmf (fun i => (w i, u i, v i)) =
      (iidDist (P.map (fun t => (t.1, t.2.2))) n).pmf (fun i => (w i, v i)) := by
  classical
  unfold iidDist; dsimp only
  rw [← Fintype.prod_sum (fun i u => P.pmf (w i, u, v i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold ProbDist.map; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (w i)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single (v i)]
    · simp
    · intro v' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro w' _ hne
    rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

end MartonHelpers

/-! ### 1. Pointwise Typicality Packing Bounds -/

section PointwisePacking

variable {W A B : Type*} [Fintype W] [Fintype A] [Fintype B]

open Classical in
/-- **Pointwise Unconditional Packing Bound**: for ANY fixed sequence `b : Fin n → B`,
    the `Q_A^n`-probability that an independently drawn `A^n` is jointly weakly `ε`-typical
    with `b` is at most `2^(-n (I(A; B) - 3ε))`. -/
private lemma mc_pointwise_uncond_packing (Q : ProbDist (A × B)) (n : ℕ) (ε : ℝ)
    (b : Fin n → B) :
    ∑ a : Fin n → A,
        (if a ∈ weakTypicalSet Q.fst n ε ∧
            b ∈ weakTypicalSet Q.snd n ε ∧
            (fun i => (a i, b i)) ∈ weakTypicalSet Q n ε
         then (iidDist Q.fst n).pmf a else 0) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) := by
  by_cases hb : b ∈ weakTypicalSet Q.snd n ε
  · have hb_mem := (Finset.mem_filter.mp hb).2
    have hb_pos : 0 < (iidDist Q.snd n).pmf b :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hb_mem.1
    have hmul_le :
        (∑ a : Fin n → A,
          if a ∈ weakTypicalSet Q.fst n ε ∧ b ∈ weakTypicalSet Q.snd n ε ∧
             (fun i => (a i, b i)) ∈ weakTypicalSet Q n ε
          then (iidDist Q.fst n).pmf a else 0) * (iidDist Q.snd n).pmf b ≤
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) * (iidDist Q.snd n).pmf b := by
      rw [Finset.sum_mul]
      have hterm : ∀ a : Fin n → A,
          (if a ∈ weakTypicalSet Q.fst n ε ∧ b ∈ weakTypicalSet Q.snd n ε ∧
              (fun i => (a i, b i)) ∈ weakTypicalSet Q n ε
           then (iidDist Q.fst n).pmf a else 0) * (iidDist Q.snd n).pmf b ≤
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) *
            (iidDist Q n).pmf (fun i => (a i, b i)) := by
        intro a
        split_ifs with h
        · have ha_mem := (Finset.mem_filter.mp h.1).2
          have hab_mem := (Finset.mem_filter.mp h.2.2).2
          calc (iidDist Q.fst n).pmf a * (iidDist Q.snd n).pmf b
            _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q.fst - ε))) *
                (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q.snd - ε))) :=
                mul_le_mul ha_mem.2 hb_mem.2 ((iidDist Q.snd n).nonneg b)
                  (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
            _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) *
                (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q + ε))) := by
                rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
                congr 1; unfold mutualInfo; ring
            _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) *
                (iidDist Q n).pmf (fun i => (a i, b i)) :=
                mul_le_mul_of_nonneg_left hab_mem.1
                  (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
        · rw [zero_mul]
          exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
            ((iidDist Q n).nonneg _)
      calc _ ≤ ∑ a : Fin n → A,
              (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) *
                (iidDist Q n).pmf (fun i => (a i, b i)) := Finset.sum_le_sum fun a _ => hterm a
        _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) *
              ∑ a : Fin n → A, (jointIidDist Q n).pmf (a, b) := by
              rw [← Finset.mul_sum]; rfl
        _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q - 3 * ε))) * (iidDist Q.snd n).pmf b := by
              change _ * (jointIidDist Q n).snd.pmf b = _
              rw [jointIidDist_snd]
    exact le_of_mul_le_mul_right hmul_le hb_pos
  · have hzero : (∑ a : Fin n → A,
        if a ∈ weakTypicalSet Q.fst n ε ∧ b ∈ weakTypicalSet Q.snd n ε ∧
           (fun i => (a i, b i)) ∈ weakTypicalSet Q n ε
        then (iidDist Q.fst n).pmf a else 0) = 0 :=
      Finset.sum_eq_zero fun _ _ => by simp [hb]
    rw [hzero]
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)

open Classical in
/-- **Pointwise Conditional Packing Bound**: for ANY fixed sequences `w : Fin n → W` and
    `b : Fin n → B`, the `P_{A|W}^n(· | w)`-probability that an independently drawn `A^n`
    forms a jointly weakly `ε`-typical triple `(w, A^n, b)` is at most
    `2^(-n (I(A; B | W) - 4ε))`. -/
private lemma mc_pointwise_cond_packing (Q : ProbDist (W × A × B)) (n : ℕ) (ε : ℝ)
    (w : Fin n → W) (b : Fin n → B) :
    let Q_W := Q.map (fun t => t.1)
    let Q_WA := Q.map (fun t => (t.1, t.2.1))
    let Q_WB := Q.map (fun t => (t.1, t.2.2))
    ∑ a : Fin n → A,
        (if w ∈ weakTypicalSet Q_W n ε ∧
            (fun i => (w i, a i)) ∈ weakTypicalSet Q_WA n ε ∧
            (fun i => (w i, b i)) ∈ weakTypicalSet Q_WB n ε ∧
            (fun i => (w i, a i, b i)) ∈ weakTypicalSet Q n ε
         then ((condChannelOfJoint Q_WA).power n).trans w a else 0) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) := by
  dsimp only
  let Q_W := Q.map (fun t => t.1)
  let Q_WA := Q.map (fun t => (t.1, t.2.1))
  let Q_WB := Q.map (fun t => (t.1, t.2.2))
  have hQ_WA_fst : Q_WA.fst = Q_W := by
    rw [← mc_probDist_map_fst]; unfold Q_WA Q_W; rw [map_comp_eq]; rfl
  by_cases hwb : w ∈ weakTypicalSet Q_W n ε ∧ (fun i => (w i, b i)) ∈ weakTypicalSet Q_WB n ε
  · have hw_mem := (Finset.mem_filter.mp hwb.1).2
    have hwb_mem := (Finset.mem_filter.mp hwb.2).2
    have hw_pos : 0 < (iidDist Q_W n).pmf w :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hw_mem.1
    have hwb_pos : 0 < (iidDist Q_WB n).pmf (fun i => (w i, b i)) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hwb_mem.1
    have hcmi := mc_condMutualInfo_triple_eq Q
    have hmul_le :
        (∑ a : Fin n → A,
          if w ∈ weakTypicalSet Q_W n ε ∧
             (fun i => (w i, a i)) ∈ weakTypicalSet Q_WA n ε ∧
             (fun i => (w i, b i)) ∈ weakTypicalSet Q_WB n ε ∧
             (fun i => (w i, a i, b i)) ∈ weakTypicalSet Q n ε
          then ((condChannelOfJoint Q_WA).power n).trans w a else 0) *
          (iidDist Q_WB n).pmf (fun i => (w i, b i)) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
          (iidDist Q_WB n).pmf (fun i => (w i, b i)) := by
      rw [Finset.sum_mul]
      have hterm : ∀ a : Fin n → A,
          (if w ∈ weakTypicalSet Q_W n ε ∧
              (fun i => (w i, a i)) ∈ weakTypicalSet Q_WA n ε ∧
              (fun i => (w i, b i)) ∈ weakTypicalSet Q_WB n ε ∧
              (fun i => (w i, a i, b i)) ∈ weakTypicalSet Q n ε
           then ((condChannelOfJoint Q_WA).power n).trans w a else 0) *
            (iidDist Q_WB n).pmf (fun i => (w i, b i)) ≤
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
            (iidDist Q n).pmf (fun i => (w i, a i, b i)) := by
        intro a
        split_ifs with h
        · have hwa_mem := (Finset.mem_filter.mp h.2.1).2
          have hwab_mem := (Finset.mem_filter.mp h.2.2.2).2
          have hwfst_ne : (iidDist Q_WA.fst n).pmf w ≠ 0 := by
            rw [hQ_WA_fst]; exact hw_pos.ne'
          rw [mc_condChannelOfJoint_power_eq_div Q_WA n w a hwfst_ne, hQ_WA_fst]
          have hdiv : (iidDist Q_WA n).pmf (fun i => (w i, a i)) / (iidDist Q_W n).pmf w ≤
              (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q_WA - ε))) /
              (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q_W + ε))) :=
            div_le_div₀ (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hwa_mem.2
              (Real.rpow_pos_of_pos (by norm_num) _) hw_mem.1
          calc ((iidDist Q_WA n).pmf (fun i => (w i, a i)) / (iidDist Q_W n).pmf w) *
                (iidDist Q_WB n).pmf (fun i => (w i, b i))
            _ ≤ ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q_WA - ε))) /
                 (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q_W + ε)))) *
                (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q_WB - ε))) :=
                mul_le_mul hdiv hwb_mem.2 ((iidDist Q_WB n).nonneg _) (by positivity)
            _ = (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
                (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Q + ε))) := by
                rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
                    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
                congr 1; rw [hcmi]; ring
            _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
                (iidDist Q n).pmf (fun i => (w i, a i, b i)) :=
                mul_le_mul_of_nonneg_left hwab_mem.1
                  (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
        · rw [zero_mul]
          exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
            ((iidDist Q n).nonneg _)
      calc _ ≤ ∑ a : Fin n → A,
              (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
                (iidDist Q n).pmf (fun i => (w i, a i, b i)) := Finset.sum_le_sum fun a _ => hterm a
        _ = (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
              ∑ a : Fin n → A, (iidDist Q n).pmf (fun i => (w i, a i, b i)) := by
              rw [← Finset.mul_sum]
        _ = (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε))) *
              (iidDist Q_WB n).pmf (fun i => (w i, b i)) := by
              rw [mc_iidDist_marginal_snd]
    exact le_of_mul_le_mul_right hmul_le hwb_pos
  · have hzero : (∑ a : Fin n → A,
        if w ∈ weakTypicalSet Q_W n ε ∧
           (fun i => (w i, a i)) ∈ weakTypicalSet Q_WA n ε ∧
           (fun i => (w i, b i)) ∈ weakTypicalSet Q_WB n ε ∧
           (fun i => (w i, a i, b i)) ∈ weakTypicalSet Q n ε
        then ((condChannelOfJoint Q_WA).power n).trans w a else 0) = 0 :=
      Finset.sum_eq_zero fun _ _ => by
        by_cases h1 : w ∈ weakTypicalSet Q_W n ε
        · have h2 : (fun i => (w i, b i)) ∉ weakTypicalSet Q_WB n ε := fun hb => hwb ⟨h1, hb⟩
          simp [h2]
        · simp [h1]
    rw [hzero]
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)

end PointwisePacking

/-! ### 2. Mutual Covering Lemma (El Gamal–Kim Lemma 8.1; Marton 1979) -/

section MutualCovering

variable {α β W U V : Type*} [Fintype α] [Fintype β] [Fintype W] [Fintype U] [Fintype V]

open Classical in
/-- **Finite-Sum 2D Second-Moment / Chebyshev Mutual Covering Bound**:
    given two independent i.i.d. codebooks `C₁ ~ Q₁^{L₁}` and `C₂ ~ Q₂^{L₂}` (`L₁, L₂ > 0`)
    and a target set `S : Finset (α × β)` with positive product probability `p₀ > 0`,
    `Pr[∀ l₁ l₂, (C₁ l₁, C₂ l₂) ∉ S] ≤ 1 / (L₁ L₂ p₀) + p₁ / (L₁ p₀²) + p₂ / (L₂ p₀²)`. -/
theorem mutual_covering_chebyshev_bound (Q₁ : ProbDist α) (Q₂ : ProbDist β)
    {L₁ L₂ : ℕ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (S : Finset (α × β))
    (hp₀ : 0 < ∑ a : α, ∑ b : β, if (a, b) ∈ S then Q₁.pmf a * Q₂.pmf b else 0) :
    let p₀ := ∑ a : α, ∑ b : β, if (a, b) ∈ S then Q₁.pmf a * Q₂.pmf b else 0
    let p₁ := ∑ a : α, Q₁.pmf a * (∑ b : β, if (a, b) ∈ S then Q₂.pmf b else 0) ^ 2
    let p₂ := ∑ b : β, Q₂.pmf b * (∑ a : α, if (a, b) ∈ S then Q₁.pmf a else 0) ^ 2
    ∑ C₁ : Fin L₁ → α, (iidDist Q₁ L₁).pmf C₁ *
      (∑ C₂ : Fin L₂ → β, (iidDist Q₂ L₂).pmf C₂ *
        (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂), (C₁ l₁, C₂ l₂) ∉ S then (1 : ℝ) else 0)) ≤
      1 / ((L₁ : ℝ) * (L₂ : ℝ) * p₀) + p₁ / ((L₁ : ℝ) * p₀ ^ 2) + p₂ / ((L₂ : ℝ) * p₀ ^ 2) := by
  dsimp only
  let ind : α → β → ℝ := fun a b => if (a, b) ∈ S then 1 else 0
  let p₀ := ∑ a : α, ∑ b : β, if (a, b) ∈ S then Q₁.pmf a * Q₂.pmf b else 0
  let p₁ := ∑ a : α, Q₁.pmf a * (∑ b : β, if (a, b) ∈ S then Q₂.pmf b else 0) ^ 2
  let p₂ := ∑ b : β, Q₂.pmf b * (∑ a : α, if (a, b) ∈ S then Q₁.pmf a else 0) ^ 2
  have hp₀_eq : p₀ = ∑ a : α, Q₁.pmf a * (∑ b : β, Q₂.pmf b * ind a b) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by dsimp only [ind]; split_ifs <;> ring
  have hp₁_eq : p₁ = ∑ a : α, Q₁.pmf a * (∑ b : β, Q₂.pmf b * ind a b) ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => congrArg (Q₁.pmf a * · ^ 2)
      (Finset.sum_congr rfl fun b _ => by dsimp only [ind]; split_ifs <;> ring)
  have hp₂_eq : p₂ = ∑ b : β, Q₂.pmf b * (∑ a : α, Q₁.pmf a * ind a b) ^ 2 := by
    refine Finset.sum_congr rfl fun b _ => congrArg (Q₂.pmf b * · ^ 2)
      (Finset.sum_congr rfl fun a _ => by dsimp only [ind]; split_ifs <;> ring)
  have hp₁_nn : 0 ≤ p₁ := Finset.sum_nonneg fun a _ => mul_nonneg (Q₁.nonneg a) (sq_nonneg _)
  have hp₂_nn : 0 ≤ p₂ := Finset.sum_nonneg fun b _ => mul_nonneg (Q₂.nonneg b) (sq_nonneg _)
  let W₁ := iidDist Q₁ L₁
  let W₂ := iidDist Q₂ L₂
  let N : (Fin L₁ → α) → (Fin L₂ → β) → ℝ := fun C₁ C₂ =>
    ∑ l₁ : Fin L₁, ∑ l₂ : Fin L₂, ind (C₁ l₁) (C₂ l₂)
  let μ : ℝ := (L₁ : ℝ) * (L₂ : ℝ) * p₀
  -- Step 1: `E[N] = μ`.
  have hEN : ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * N C₁ C₂) = μ := by
    have h1 : ∀ C₁ : Fin L₁ → α, ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * N C₁ C₂ =
        ∑ l₁ : Fin L₁, ∑ _l₂ : Fin L₂, ∑ b : β, Q₂.pmf b * ind (C₁ l₁) b := fun C₁ => by
      dsimp only [N]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l₂ _ => iidDist_sum_coord Q₂ (fun b => ind (C₁ l₁) b) l₂
    simp_rw [h1]
    have h1' : ∀ C₁ : Fin L₁ → α,
        W₁.pmf C₁ * (∑ l₁ : Fin L₁, ∑ _l₂ : Fin L₂, ∑ b : β, Q₂.pmf b * ind (C₁ l₁) b) =
        ∑ l₁ : Fin L₁, (L₂ : ℝ) * (W₁.pmf C₁ * ∑ b : β, Q₂.pmf b * ind (C₁ l₁) b) := fun C₁ => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l₁ _ => ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    simp_rw [h1']
    rw [Finset.sum_comm]
    have h2 : ∀ l₁ : Fin L₁,
        (∑ C₁ : Fin L₁ → α, (L₂ : ℝ) * (W₁.pmf C₁ * ∑ b : β, Q₂.pmf b * ind (C₁ l₁) b)) =
        (L₂ : ℝ) * p₀ := fun l₁ => by
      rw [← Finset.mul_sum, iidDist_sum_coord Q₁ (fun a => ∑ b : β, Q₂.pmf b * ind a b) l₁, ← hp₀_eq]
    rw [Finset.sum_congr rfl fun l₁ _ => h2 l₁, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    dsimp only [μ]; ring
  -- Step 2: Evaluate `E[I(l₁, l₂) * I(l₁', l₂')]` for each `(l₁, l₁', l₂, l₂')`.
  have hpair_eval : ∀ (l₁ l₁' : Fin L₁) (l₂ l₂' : Fin L₂),
      ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ *
        (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂'))) =
      if l₁ = l₁' then (if l₂ = l₂' then p₀ else p₁) else (if l₂ = l₂' then p₂ else p₀ ^ 2) := by
    intro l₁ l₁' l₂ l₂'
    by_cases h1 : l₁ = l₁'
    · subst h1
      by_cases h2 : l₂ = l₂'
      · subst h2
        simp only [↓reduceIte]
        have hind_sq : ∀ a b, ind a b * ind a b = ind a b := fun a b => by
          dsimp only [ind]; split_ifs <;> ring
        simp_rw [hind_sq]
        have hC2 : ∀ C₁ : Fin L₁ → α, ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * ind (C₁ l₁) (C₂ l₂) =
            ∑ b : β, Q₂.pmf b * ind (C₁ l₁) b := fun C₁ =>
          iidDist_sum_coord Q₂ (fun b => ind (C₁ l₁) b) l₂
        simp_rw [hC2]
        rw [iidDist_sum_coord Q₁ (fun a => ∑ b : β, Q₂.pmf b * ind a b) l₁, ← hp₀_eq]
      · simp only [h2, ↓reduceIte]
        have hC2 : ∀ C₁ : Fin L₁ → α, ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
              (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁) (C₂ l₂')) =
            (∑ b : β, Q₂.pmf b * ind (C₁ l₁) b) ^ 2 := fun C₁ => by
          rw [iidDist_sum_two_coords Q₂ (fun b => ind (C₁ l₁) b) (fun b => ind (C₁ l₁) b) h2, sq]
        simp_rw [hC2]
        rw [iidDist_sum_coord Q₁ (fun a => (∑ b : β, Q₂.pmf b * ind a b) ^ 2) l₁, ← hp₁_eq]
    · by_cases h2 : l₂ = l₂'
      · subst h2
        simp only [h1, ↓reduceIte]
        have hswap : (∑ C₁ : Fin L₁ → α, W₁.pmf C₁ *
              (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂)))) =
            ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
              (∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂))) := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun C₂ _ => Finset.sum_congr rfl fun C₁ _ => by ring
        rw [hswap]
        have hC1 : ∀ C₂ : Fin L₂ → β, ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ *
              (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂)) =
            (∑ a : α, Q₁.pmf a * ind a (C₂ l₂)) ^ 2 := fun C₂ => by
          rw [iidDist_sum_two_coords Q₁ (fun a => ind a (C₂ l₂)) (fun a => ind a (C₂ l₂)) h1, sq]
        simp_rw [hC1]
        rw [iidDist_sum_coord Q₂ (fun b => (∑ a : α, Q₁.pmf a * ind a b) ^ 2) l₂, ← hp₂_eq]
      · simp only [h1, h2, ↓reduceIte]
        have hC2 : ∀ C₁ : Fin L₁ → α, ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
              (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂')) =
            (∑ b : β, Q₂.pmf b * ind (C₁ l₁) b) * (∑ b' : β, Q₂.pmf b' * ind (C₁ l₁') b') := fun C₁ =>
          iidDist_sum_two_coords Q₂ (fun b => ind (C₁ l₁) b) (fun b' => ind (C₁ l₁') b') h2
        simp_rw [hC2]
        rw [iidDist_sum_two_coords Q₁ (fun a => ∑ b : β, Q₂.pmf b * ind a b)
            (fun a' => ∑ b' : β, Q₂.pmf b' * ind a' b') h1, ← hp₀_eq, sq]
  -- Step 3: `E[N²] ≤ L₁ L₂ p₀ + L₁ L₂² p₁ + L₁² L₂ p₂ + μ²`.
  have hEN2 : ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (N C₁ C₂) ^ 2) ≤
      (L₁ : ℝ) * (L₂ : ℝ) * p₀ + (L₁ : ℝ) * (L₂ : ℝ) ^ 2 * p₁ +
      (L₁ : ℝ) ^ 2 * (L₂ : ℝ) * p₂ + μ ^ 2 := by
    have hexpand : ∀ (C₁ : Fin L₁ → α) (C₂ : Fin L₂ → β), (N C₁ C₂) ^ 2 =
        ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
          ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂') := fun C₁ C₂ => by
      dsimp only [N]
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun l₁ _ => ?_
      refine Finset.sum_congr rfl fun l₁' _ => ?_
      rw [Finset.sum_mul_sum]
    simp_rw [hexpand]
    have hpush : (∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
          ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
            ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂'))) =
        ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
          (if l₁ = l₁' then (if l₂ = l₂' then p₀ else p₁) else (if l₂ = l₂' then p₂ else p₀ ^ 2)) := by
      have hinner : ∀ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
            ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
              ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂')) =
          ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
            W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂'))) := by
        intro C₁
        have hstep : ∀ C₂ : Fin L₂ → β, W₂.pmf C₂ *
              ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
                ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂') =
            ∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
              W₂.pmf C₂ * (ind (C₁ l₁) (C₂ l₂) * ind (C₁ l₁') (C₂ l₂')) := fun C₂ => by
          simp_rw [Finset.mul_sum]
        simp_rw [hstep]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l₁ _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l₁' _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l₂ _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
      simp_rw [hinner]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l₁' _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l₂ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l₂' _ => hpair_eval l₁ l₁' l₂ l₂'
    rw [hpush]
    have hsum_l2 : ∀ a b : ℝ,
        (∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂, if l₂ = l₂' then a else b) =
        (L₂ : ℝ) * a + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * b := fun a b => by
      have hrow : ∀ l₂ : Fin L₂,
          (∑ l₂' : Fin L₂, if l₂ = l₂' then a else b) = a + ((L₂ - 1 : ℕ) : ℝ) * b := fun l₂ => by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ l₂)]
        simp only [↓reduceIte]
        congr 1
        have hrest : ∑ l₂' ∈ Finset.univ.erase l₂, (if l₂ = l₂' then a else b) =
            ∑ _l₂' ∈ Finset.univ.erase l₂, b :=
          Finset.sum_congr rfl fun l₂' hl₂' => by simp [(Finset.mem_erase.mp hl₂').1.symm]
        rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l₂),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      ring
    have hsum_all :
        (∑ l₁ : Fin L₁, ∑ l₁' : Fin L₁, ∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
          if l₁ = l₁' then (if l₂ = l₂' then p₀ else p₁) else (if l₂ = l₂' then p₂ else p₀ ^ 2)) =
        (L₁ : ℝ) * ((L₂ : ℝ) * p₀ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₁) +
        (L₁ : ℝ) * ((L₁ - 1 : ℕ) : ℝ) * ((L₂ : ℝ) * p₂ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2) := by
      have h1 : ∀ l₁ l₁' : Fin L₁,
          (∑ l₂ : Fin L₂, ∑ l₂' : Fin L₂,
            if l₁ = l₁' then (if l₂ = l₂' then p₀ else p₁) else (if l₂ = l₂' then p₂ else p₀ ^ 2)) =
          if l₁ = l₁' then ((L₂ : ℝ) * p₀ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₁)
          else ((L₂ : ℝ) * p₂ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2) := fun l₁ l₁' => by
        split_ifs
        · exact hsum_l2 p₀ p₁
        · exact hsum_l2 p₂ (p₀ ^ 2)
      simp_rw [h1]
      have hrow : ∀ l₁ : Fin L₁,
          (∑ l₁' : Fin L₁,
            if l₁ = l₁' then ((L₂ : ℝ) * p₀ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₁)
            else ((L₂ : ℝ) * p₂ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2)) =
          ((L₂ : ℝ) * p₀ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₁) +
          ((L₁ - 1 : ℕ) : ℝ) * ((L₂ : ℝ) * p₂ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2) := fun l₁ => by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ l₁)]
        simp only [↓reduceIte]
        congr 1
        have hrest : ∑ l₁' ∈ Finset.univ.erase l₁,
              (if l₁ = l₁' then ((L₂ : ℝ) * p₀ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₁)
               else ((L₂ : ℝ) * p₂ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2)) =
            ∑ _l₁' ∈ Finset.univ.erase l₁,
              ((L₂ : ℝ) * p₂ + (L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2) :=
          Finset.sum_congr rfl fun l₁' hl₁' => by simp [(Finset.mem_erase.mp hl₁').1.symm]
        rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l₁),
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsum_all]
    have hL1_le : ((L₁ - 1 : ℕ) : ℝ) ≤ (L₁ : ℝ) := Nat.cast_le.mpr (Nat.sub_le L₁ 1)
    have hL2_le : ((L₂ - 1 : ℕ) : ℝ) ≤ (L₂ : ℝ) := Nat.cast_le.mpr (Nat.sub_le L₂ 1)
    have hL1_nn : (0 : ℝ) ≤ (L₁ : ℝ) := Nat.cast_nonneg L₁
    have hL2_nn : (0 : ℝ) ≤ (L₂ : ℝ) := Nat.cast_nonneg L₂
    have hL2m_nn : (0 : ℝ) ≤ ((L₂ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht1 : (L₁ : ℝ) * ((L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₁) ≤ (L₁ : ℝ) * (L₂ : ℝ) ^ 2 * p₁ := by
      have h1 : ((L₂ - 1 : ℕ) : ℝ) * p₁ ≤ (L₂ : ℝ) * p₁ := mul_le_mul_of_nonneg_right hL2_le hp₁_nn
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hL1_nn hL2_nn)
      linarith
    have ht2 : (L₁ : ℝ) * ((L₁ - 1 : ℕ) : ℝ) * ((L₂ : ℝ) * p₂) ≤ (L₁ : ℝ) ^ 2 * (L₂ : ℝ) * p₂ := by
      have h1 : ((L₁ - 1 : ℕ) : ℝ) * p₂ ≤ (L₁ : ℝ) * p₂ := mul_le_mul_of_nonneg_right hL1_le hp₂_nn
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hL1_nn hL2_nn)
      linarith
    have ht3 : (L₁ : ℝ) * ((L₁ - 1 : ℕ) : ℝ) * ((L₂ : ℝ) * ((L₂ - 1 : ℕ) : ℝ) * p₀ ^ 2) ≤ μ ^ 2 := by
      have hprod : ((L₁ - 1 : ℕ) : ℝ) * ((L₂ - 1 : ℕ) : ℝ) ≤ (L₁ : ℝ) * (L₂ : ℝ) :=
        mul_le_mul hL1_le hL2_le hL2m_nn hL1_nn
      have hsq : 0 ≤ (L₁ : ℝ) * (L₂ : ℝ) * p₀ ^ 2 := by positivity
      have hstep := mul_le_mul_of_nonneg_right hprod hsq
      dsimp only [μ]; nlinarith
    linarith
  -- Step 4: Chebyshev inequality `μ² * Pr[N = 0] ≤ E[(N - μ)²] = E[N²] - μ²`.
  have hvar : ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ *
        (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (N C₁ C₂ - μ) ^ 2) =
      (∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (N C₁ C₂) ^ 2)) - μ ^ 2 := by
    have hsq : ∀ (C₁ : Fin L₁ → α) (C₂ : Fin L₂ → β),
        (N C₁ C₂ - μ) ^ 2 = (N C₁ C₂) ^ 2 - 2 * μ * N C₁ C₂ + μ ^ 2 := fun _ _ => by ring
    simp_rw [hsq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∀ C₁ : Fin L₁ → α, ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (2 * μ * N C₁ C₂) =
        2 * μ * ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * N C₁ C₂ := fun C₁ => by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * μ ^ 2 = μ ^ 2 := by
      rw [← Finset.sum_mul, W₂.sum_one, one_mul]
    simp_rw [h1, h2, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h3 : ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (2 * μ * ∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * N C₁ C₂) =
        2 * μ * ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * N C₁ C₂) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have h4 : ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * μ ^ 2 = μ ^ 2 := by
      rw [← Finset.sum_mul, W₁.sum_one, one_mul]
    rw [h3, h4, hEN]; ring
  have hcheb : μ ^ 2 * (∑ C₁ : Fin L₁ → α, W₁.pmf C₁ *
        (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂), (C₁ l₁, C₂ l₂) ∉ S then (1 : ℝ) else 0))) ≤
      (L₁ : ℝ) * (L₂ : ℝ) * p₀ + (L₁ : ℝ) * (L₂ : ℝ) ^ 2 * p₁ + (L₁ : ℝ) ^ 2 * (L₂ : ℝ) * p₂ := by
    have hpt : ∀ (C₁ : Fin L₁ → α) (C₂ : Fin L₂ → β),
        μ ^ 2 * (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂), (C₁ l₁, C₂ l₂) ∉ S then (1 : ℝ) else 0) ≤
        (N C₁ C₂ - μ) ^ 2 := by
      intro C₁ C₂
      split_ifs with h
      · have hN0 : N C₁ C₂ = 0 :=
          Finset.sum_eq_zero fun l₁ _ => Finset.sum_eq_zero fun l₂ _ => by simp [ind, h l₁ l₂]
        rw [hN0, mul_one, zero_sub, neg_sq]
      · rw [mul_zero]; exact sq_nonneg _
    have hsum_le : μ ^ 2 * (∑ C₁ : Fin L₁ → α, W₁.pmf C₁ *
          (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂), (C₁ l₁, C₂ l₂) ∉ S then (1 : ℝ) else 0))) ≤
        ∑ C₁ : Fin L₁ → α, W₁.pmf C₁ * (∑ C₂ : Fin L₂ → β, W₂.pmf C₂ * (N C₁ C₂ - μ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun C₁ _ => ?_
      rw [← mul_assoc, mul_comm (μ ^ 2), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (W₁.nonneg C₁)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun C₂ _ => ?_
      rw [← mul_assoc, mul_comm (μ ^ 2), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpt C₁ C₂) (W₂.nonneg C₂)
    linarith
  have hL1_pos : (0 : ℝ) < (L₁ : ℝ) := Nat.cast_pos.mpr hL₁
  have hL2_pos : (0 : ℝ) < (L₂ : ℝ) := Nat.cast_pos.mpr hL₂
  have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
  have hdiv := (le_div_iff₀' (sq_pos_of_pos hμ_pos)).mpr hcheb
  have hrhs : ((L₁ : ℝ) * (L₂ : ℝ) * p₀ + (L₁ : ℝ) * (L₂ : ℝ) ^ 2 * p₁ +
      (L₁ : ℝ) ^ 2 * (L₂ : ℝ) * p₂) / μ ^ 2 =
      1 / ((L₁ : ℝ) * (L₂ : ℝ) * p₀) + p₁ / ((L₁ : ℝ) * p₀ ^ 2) + p₂ / ((L₂ : ℝ) * p₀ ^ 2) := by
    dsimp only [μ]
    field_simp [hL1_pos.ne', hL2_pos.ne', hp₀.ne']
  linarith

open Classical in
/-- Helper: 1D conditional covering (`R₁ = 0`, `R₂ > I(U; V | W)`). -/
private lemma mc_mutual_covering_one_sided (P : ProbDist (W × U × V))
    {R₂ ε δ : ℝ} (hR₂ : condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) < R₂)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ)))
      let L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
      let P_W := P.map (fun t => t.1)
      let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
      let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
      ∑ w : Fin n → W, (iidDist P_W n).pmf w *
        (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
          (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
                (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
             then (1 : ℝ) else 0))) ≤ δ := by
  let P_W := P.map (fun t => t.1)
  let P_WU := P.map (fun t => (t.1, t.2.1))
  let P_WV := P.map (fun t => (t.1, t.2.2))
  let P_WUV : ProbDist ((W × U) × V) := P.map (fun t => ((t.1, t.2.1), t.2.2))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  let K_V_WU := condChannelOfJoint P_WUV
  let I_UV := condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1)))
  have hI_nn : 0 ≤ I_UV := condMutualInfo_nonneg _
  have hR₂_pos : 0 < R₂ := lt_of_le_of_lt hI_nn hR₂
  let gap : ℝ := R₂ - I_UV
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let Hmax : ℝ := shannonEntropy P_W + shannonEntropy P_WU + shannonEntropy P_WV + shannonEntropy P + 1
  have hHmax : 1 ≤ Hmax := by
    dsimp [Hmax]
    linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WU,
      shannonEntropy_nonneg P_WV, shannonEntropy_nonneg P]
  have hHmax_pos : 0 < Hmax := by linarith
  let εi : ℝ := min ε (gap / (8 * Hmax))
  have hεi : 0 < εi := lt_min hε (by positivity)
  have hεi_le : εi ≤ ε := min_le_left _ _
  let ε' : ℝ := εi * Hmax
  have hε'_le : 4 * ε' ≤ gap / 2 := by
    have h1 : εi ≤ gap / (8 * Hmax) := min_le_right _ _
    have h2 : ε' ≤ gap / 8 := by
      dsimp [ε']
      calc εi * Hmax ≤ (gap / (8 * Hmax)) * Hmax := mul_le_mul_of_nonneg_right h1 hHmax_pos.le
        _ = gap / 8 := by field_simp [hHmax_pos.ne']
    linarith
  let ε₀ : ℝ := εi / 2
  have hε₀ : 0 < ε₀ := half_pos hεi
  have hε₀_lt : ε₀ < εi := by dsimp [ε₀]; linarith
  have hP_WUV_fst : P_WUV.fst = P_WU := by
    rw [← mc_probDist_map_fst]; unfold P_WUV P_WU; rw [map_comp_eq]; rfl
  have hP_WU_fst : P_WU.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_WU P_W; rw [map_comp_eq]; rfl
  have hP_WV_fst : P_WV.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_WV P_W; rw [map_comp_eq]; rfl
  let C_mk : ℝ := ∑ p : (W × U) × V, if 0 < P_WUV.pmf p then 1 / P_WUV.pmf p ^ 2 else 0
  obtain ⟨N₁, hN₁⟩ := strongTypicalSet_prob_tendsto_one P_WU hε₀ (half_pos hδ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * C_mk / (εi - ε₀) ^ 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (8 / (δ * gap * Real.log 2))
  refine ⟨max (max (max N₁ N₂) N₃) 1, fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hn)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ N₃)) (le_trans (le_max_left _ 1) hn)
  have hn2 : 2 * C_mk / (εi - ε₀) ^ 2 < (n : ℝ) := lt_of_lt_of_le hN₂ (by
    exact_mod_cast le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ N₃)) (le_trans (le_max_left _ 1) hn))
  have hn3 : 8 / (δ * gap * Real.log 2) < (n : ℝ) := lt_of_lt_of_le hN₃ (by
    exact_mod_cast le_trans (le_max_right _ N₃) (le_trans (le_max_left _ 1) hn))
  set L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ)))
  set L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
  have hL₁_pos : 0 < L₁ := mc_ceil_two_rpow_pos n le_rfl
  let l₁0 : Fin L₁ := ⟨0, hL₁_pos⟩
  have hstep1 : ∀ w : Fin n → W,
      (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
           then (1 : ℝ) else 0))) ≤
      ∑ u : Fin n → U, (K_U.power n).trans w u *
        (1 - ∑ v : Fin n → V,
          if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
          then (K_V.power n).trans w v else 0) ^ L₂ := by
    intro w
    have hdrop : ∀ C₁ : Fin L₁ → Fin n → U,
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
           then (1 : ℝ) else 0)) ≤
        (1 - ∑ v : Fin n → V,
          if (fun i => (w i, C₁ l₁0 i, v i)) ∈ strongTypicalSet P n εi
          then (K_V.power n).trans w v else 0) ^ L₂ := by
      intro C₁
      let u := C₁ l₁0
      have hind : ∀ C₂ : Fin L₂ → Fin n → V,
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
           then (1 : ℝ) else 0) ≤
          ∏ l₂ : Fin L₂,
            (if (fun i => (w i, u i, C₂ l₂ i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0) := by
        intro C₂
        split_ifs with h
        · have hall : ∀ l₂ : Fin L₂, (fun i => (w i, u i, C₂ l₂ i)) ∉ strongTypicalSet P n εi :=
            fun l₂ hmem => h l₁0 l₂ (mc_strongTypicalSet_mono P n hεi_le hmem)
          rw [Finset.prod_eq_one fun l₂ _ => by simp [hall l₂]]
        · exact Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num
      calc _ ≤ ∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
              ∏ l₂ : Fin L₂,
                (if (fun i => (w i, u i, C₂ l₂ i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun C₂ _ =>
              mul_le_mul_of_nonneg_left (hind C₂) ((iidDist (dmcRow (K_V.power n) w) L₂).nonneg C₂)
        _ = ∏ _l₂ : Fin L₂, ∑ v : Fin n → V, (K_V.power n).trans w v *
              (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0) := by
            have hmul : ∀ C₂ : Fin L₂ → Fin n → V,
                (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
                  ∏ l₂ : Fin L₂, (if (fun i => (w i, u i, C₂ l₂ i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0) =
                ∏ l₂ : Fin L₂, ((K_V.power n).trans w (C₂ l₂) *
                  (if (fun i => (w i, u i, C₂ l₂ i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0)) := fun C₂ => by
              unfold iidDist dmcRow; dsimp only; rw [← Finset.prod_mul_distrib]
            simp_rw [hmul]
            exact (Fintype.prod_sum (fun (_ : Fin L₂) (v : Fin n → V) =>
              (K_V.power n).trans w v *
                (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0))).symm
        _ = (1 - ∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0) ^ L₂ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            congr 1
            have hsplit : ∑ v : Fin n → V, (K_V.power n).trans w v =
                (∑ v : Fin n → V, if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
                  then (K_V.power n).trans w v else 0) +
                (∑ v : Fin n → V, (K_V.power n).trans w v *
                  (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n εi then (1 : ℝ) else 0)) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun v _ => by
                by_cases hm : (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi <;> simp [hm]
            rw [(K_V.power n).sum_one w] at hsplit
            linarith
    calc _ ≤ ∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
            (1 - ∑ v : Fin n → V,
              if (fun i => (w i, C₁ l₁0 i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0) ^ L₂ :=
          Finset.sum_le_sum fun C₁ _ =>
            mul_le_mul_of_nonneg_left (hdrop C₁) ((iidDist (dmcRow (K_U.power n) w) L₁).nonneg C₁)
      _ = _ := iidDist_sum_coord (dmcRow (K_U.power n) w)
            (fun u => (1 - ∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0) ^ L₂) l₁0
  have hgood : ∀ (w : Fin n → W) (u : Fin n → U),
      (fun i => (w i, u i)) ∈ strongTypicalSet P_WU n ε₀ →
      (1 - ∑ v : Fin n → V,
        if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
        then (K_V.power n).trans w v else 0) ^ L₂ ≤ δ / 2 := by
    intro w u hwu
    set q := ∑ v : Fin n → V,
      if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
      then (K_V.power n).trans w v else 0
    have hq_nn : 0 ≤ q := Finset.sum_nonneg fun v _ => by
      split_ifs
      · exact (K_V.power n).nonneg w v
      · exact le_rfl
    have hq_le1 : q ≤ 1 := by
      calc q ≤ ∑ v : Fin n → V, (K_V.power n).trans w v :=
            Finset.sum_le_sum fun v _ => by
              split_ifs
              · exact le_rfl
              · exact (K_V.power n).nonneg w v
        _ = 1 := (K_V.power n).sum_one w
    let eP : (W × U × V) ≃ ((W × U) × V) :=
      { toFun := fun t => ((t.1, t.2.1), t.2.2)
        invFun := fun t => (t.1.1, t.1.2, t.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    have hhwu_fst : (fun i => (w i, u i)) ∈ strongTypicalSet P_WUV.fst n ε₀ := by
      rwa [hP_WUV_fst]
    have hmk := mc_cond_typical_prob_not_mem_le P_WUV hn_pos (le_of_lt hε₀) hε₀_lt hhwu_fst
    have hmk_half : C_mk / ((n : ℝ) * (εi - ε₀) ^ 2) ≤ 1 / 2 := by
      have hdiff : 0 < εi - ε₀ := by linarith
      rw [div_le_iff₀ (by positivity)]
      have h1 := (div_lt_iff₀ (by positivity : 0 < (εi - ε₀) ^ 2)).mp hn2
      linarith
    have hβ_ge : 1 / 2 ≤ ∑ v : Fin n → V,
        if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
        then (K_V_WU.power n).trans (fun i => (w i, u i)) v else 0 := by
      have hsub : ∀ v : Fin n → V,
          (K_V_WU.power n).trans (fun i => (w i, u i)) v *
            (if (fun i => ((w i, u i), v i)) ∉ strongTypicalSet P_WUV n εi then (1 : ℝ) else 0) =
          if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n εi
          then (K_V_WU.power n).trans (fun i => (w i, u i)) v else 0 := by
        intro v
        have heqv : (fun i => ((w i, u i), v i)) ∈ strongTypicalSet P_WUV n εi ↔
            (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi := by
          constructor
          · intro h
            have hm := strongTypicalSet_map P_WUV eP.symm n εi h
            have hmap : P_WUV.map eP.symm = P := by
              unfold P_WUV; rw [map_comp_eq]; apply mc_probDist_ext; intro t
              unfold ProbDist.map; dsimp only [eP]; simp
            rwa [hmap] at hm
          · intro h
            exact strongTypicalSet_map P eP n εi h
        by_cases hm : (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi <;>
          simp [heqv, hm]
      have hsplit : ∑ v : Fin n → V, (K_V_WU.power n).trans (fun i => (w i, u i)) v =
          (∑ v : Fin n → V, if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
            then (K_V_WU.power n).trans (fun i => (w i, u i)) v else 0) +
          (∑ v : Fin n → V, if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n εi
            then (K_V_WU.power n).trans (fun i => (w i, u i)) v else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by
          by_cases hm : (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi <;> simp [hm]
      rw [(K_V_WU.power n).sum_one] at hsplit
      have hmk_le : (∑ v : Fin n → V, if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n εi
            then (K_V_WU.power n).trans (fun i => (w i, u i)) v else 0) ≤ C_mk / ((n : ℝ) * (εi - ε₀) ^ 2) := by
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun v _ => ?_)) hmk
        rw [← hsub v]; congr 1; split_ifs <;> rfl
      linarith
    have hratio : ∀ v : Fin n → V,
        (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi →
        (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) *
          (K_V_WU.power n).trans (fun i => (w i, u i)) v ≤ (K_V.power n).trans w v := by
      intro v hv
      have hw_st := strongTypicalSet_map P (fun t => t.1) n εi hv
      have hwu_st := strongTypicalSet_map P (fun t => (t.1, t.2.1)) n εi hv
      have hwv_st := strongTypicalSet_map P (fun t => (t.1, t.2.2)) n εi hv
      have hle_W : εi * shannonEntropy P_W ≤ ε' := mul_le_mul_of_nonneg_left (by
        dsimp [Hmax]; linarith [shannonEntropy_nonneg P_WU, shannonEntropy_nonneg P_WV, shannonEntropy_nonneg P]) hεi.le
      have hle_WU : εi * shannonEntropy P_WU ≤ ε' := mul_le_mul_of_nonneg_left (by
        dsimp [Hmax]; linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WV, shannonEntropy_nonneg P]) hεi.le
      have hle_WV : εi * shannonEntropy P_WV ≤ ε' := mul_le_mul_of_nonneg_left (by
        dsimp [Hmax]; linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WU, shannonEntropy_nonneg P]) hεi.le
      have hle_P : εi * shannonEntropy P ≤ ε' := mul_le_mul_of_nonneg_left (by
        dsimp [Hmax]; linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WU, shannonEntropy_nonneg P_WV]) hεi.le
      have hw_wk := (Finset.mem_filter.mp (strongTypicalSet_subset_weakTypicalSet P_W hn_pos hεi.le hle_W hw_st)).2
      have hwu_wk := (Finset.mem_filter.mp (strongTypicalSet_subset_weakTypicalSet P_WU hn_pos hεi.le hle_WU hwu_st)).2
      have hwv_wk := (Finset.mem_filter.mp (strongTypicalSet_subset_weakTypicalSet P_WV hn_pos hεi.le hle_WV hwv_st)).2
      have hv_wk := (Finset.mem_filter.mp (strongTypicalSet_subset_weakTypicalSet P hn_pos hεi.le hle_P hv)).2
      have hw_pos : 0 < (iidDist P_W n).pmf w := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hw_wk.1
      have hwu_pos : 0 < (iidDist P_WU n).pmf (fun i => (w i, u i)) :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hwu_wk.1
      have hKV_eq : (K_V.power n).trans w v =
          (iidDist P_WV n).pmf (fun i => (w i, v i)) / (iidDist P_W n).pmf w := by
        have hne : (iidDist P_WV.fst n).pmf w ≠ 0 := by rw [hP_WV_fst]; exact hw_pos.ne'
        simpa [hP_WV_fst] using mc_condChannelOfJoint_power_eq_div P_WV n w v hne
      have hKVWU_eq : (K_V_WU.power n).trans (fun i => (w i, u i)) v =
          (iidDist P n).pmf (fun i => (w i, u i, v i)) / (iidDist P_WU n).pmf (fun i => (w i, u i)) := by
        have hne : (iidDist P_WUV.fst n).pmf (fun i => (w i, u i)) ≠ 0 := by
          rw [hP_WUV_fst]; exact hwu_pos.ne'
        have heq1 := mc_condChannelOfJoint_power_eq_div P_WUV n (fun i => (w i, u i)) v hne
        rw [hP_WUV_fst] at heq1
        rw [heq1]
        congr 1
        unfold iidDist; dsimp only
        refine Finset.prod_congr rfl fun i _ => ?_
        unfold P_WUV ProbDist.map; dsimp only
        rw [Finset.sum_eq_single (w i, u i, v i)]
        · simp
        · intro t _ hne_t
          split_ifs with h
          · exact absurd (eP.injective h) hne_t
          · rfl
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hKV_eq, hKVWU_eq]
      have h1 : (iidDist P n).pmf (fun i => (w i, u i, v i)) / (iidDist P_WU n).pmf (fun i => (w i, u i)) ≤
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε'))) /
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WU + ε'))) :=
        div_le_div₀ (by positivity) hv_wk.2 (Real.rpow_pos_of_pos (by norm_num) _) hwu_wk.1
      have h2 : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WV + ε'))) /
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε'))) ≤
          (iidDist P_WV n).pmf (fun i => (w i, v i)) / (iidDist P_W n).pmf w :=
        div_le_div₀ ((iidDist P_WV n).nonneg _) hwv_wk.1 hw_pos hw_wk.2
      have hmid : (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) *
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε'))) /
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WU + ε')))) =
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WV + ε'))) /
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε'))) := by
        rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; dsimp only [I_UV]; rw [mc_condMutualInfo_triple_eq]; ring
      calc (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) *
            ((iidDist P n).pmf (fun i => (w i, u i, v i)) / (iidDist P_WU n).pmf (fun i => (w i, u i)))
        _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε'))) /
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WU + ε')))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WV + ε'))) /
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε'))) := hmid
        _ ≤ (iidDist P_WV n).pmf (fun i => (w i, v i)) / (iidDist P_W n).pmf w := h2
    have hq_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) ≤ q := by
      calc (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε')))
        _ ≤ (∑ v : Fin n → V, if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V_WU.power n).trans (fun i => (w i, u i)) v else 0) *
            (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) :=
            mul_le_mul_of_nonneg_right hβ_ge (by positivity)
        _ = ∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε'))) *
                (K_V_WU.power n).trans (fun i => (w i, u i)) v
              else 0 := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
        _ ≤ q := Finset.sum_le_sum fun v _ => by
            split_ifs with hv
            · exact hratio v hv
            · exact le_rfl
    have hexp_le : (1 - q) ^ L₂ ≤ Real.exp (-((L₂ : ℝ) * q)) := by
      have h1 : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
      calc (1 - q) ^ L₂
        _ ≤ (Real.exp (-q)) ^ L₂ := pow_le_pow_left₀ (by linarith) h1 L₂
        _ = Real.exp ((L₂ : ℝ) * (-q)) := (Real.exp_nat_mul (-q) L₂).symm
        _ = Real.exp (-((L₂ : ℝ) * q)) := by ring_nf
    have hL2q_ge : 2 / δ ≤ (L₂ : ℝ) * q := by
      have hpow_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (gap / 2)) ≤ (L₂ : ℝ) * q := by
        calc (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (gap / 2))
          _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₂ - (I_UV + 4 * ε'))) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)) (by norm_num)
          _ = (2 : ℝ) ^ ((n : ℝ) * R₂) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 4 * ε')))) := by
              rw [mul_left_comm ((2 : ℝ) ^ _), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 2; ring
          _ ≤ (L₂ : ℝ) * q :=
              mul_le_mul (mc_two_rpow_le_ceil n R₂) hq_ge (by positivity) (by positivity)
      have h2exp : (n : ℝ) * (gap / 2) * Real.log 2 ≤ (2 : ℝ) ^ ((n : ℝ) * (gap / 2)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [Real.add_one_le_exp (Real.log 2 * ((n : ℝ) * (gap / 2)))]
      have hlin : 2 / δ ≤ (1 / 2 : ℝ) * ((n : ℝ) * (gap / 2) * Real.log 2) := by
        have h1 := (div_lt_iff₀ (by positivity : 0 < δ * gap * Real.log 2)).mp hn3
        rw [div_le_iff₀ hδ]
        have heq : (1 / 2 : ℝ) * ((n : ℝ) * (gap / 2) * Real.log 2) * δ =
            (n : ℝ) * (δ * gap * Real.log 2) / 4 := by ring
        linarith
      linarith
    have hexp_ge : 2 / δ ≤ Real.exp ((L₂ : ℝ) * q) := by
      linarith [Real.add_one_le_exp ((L₂ : ℝ) * q)]
    have hinv : Real.exp (-((L₂ : ℝ) * q)) ≤ δ / 2 := by
      rw [Real.exp_neg]
      calc (Real.exp ((L₂ : ℝ) * q))⁻¹ ≤ (2 / δ)⁻¹ := inv_anti₀ (by positivity) hexp_ge
        _ = δ / 2 := by rw [inv_div]
    exact le_trans hexp_le hinv
  calc _ ≤ ∑ w : Fin n → W, (iidDist P_W n).pmf w *
          (∑ u : Fin n → U, (K_U.power n).trans w u *
            (1 - ∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0) ^ L₂) :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hstep1 w) ((iidDist P_W n).nonneg w)
    _ = ∑ wu : (Fin n → W) × (Fin n → U), (jointIidDist P_WU n).pmf wu *
          (1 - ∑ v : Fin n → V,
            if (fun i => (wu.1 i, wu.2 i, v i)) ∈ strongTypicalSet P n εi
            then (K_V.power n).trans wu.1 v else 0) ^ L₂ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← mul_assoc]
        congr 1
        rw [jointIidDist_eq_fst_mul_condChannelPower P_WU n w u, hP_WU_fst]
    _ ≤ ∑ wu : (Fin n → W) × (Fin n → U), (jointIidDist P_WU n).pmf wu *
          ((if zipEquiv W U n wu ∉ strongTypicalSet P_WU n ε₀ then (1 : ℝ) else 0) + δ / 2) := by
        refine Finset.sum_le_sum fun ⟨w, u⟩ _ =>
          mul_le_mul_of_nonneg_left ?_ ((jointIidDist P_WU n).nonneg _)
        by_cases hwu : (fun i => (w i, u i)) ∈ strongTypicalSet P_WU n ε₀
        · have hmem : zipEquiv W U n (w, u) ∈ strongTypicalSet P_WU n ε₀ := hwu
          simp only [hmem, not_true_eq_false, ↓reduceIte, zero_add]
          exact hgood w u hwu
        · have hmem : zipEquiv W U n (w, u) ∉ strongTypicalSet P_WU n ε₀ := hwu
          simp only [hmem, not_false_eq_true, ↓reduceIte]
          have hq0 : 0 ≤ ∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0 :=
            Finset.sum_nonneg fun v _ => by split_ifs; exact (K_V.power n).nonneg w v; exact le_rfl
          have hq1 : (∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0) ≤ 1 := by
            calc _ ≤ ∑ v : Fin n → V, (K_V.power n).trans w v :=
                  Finset.sum_le_sum fun v _ => by split_ifs; exact le_rfl; exact (K_V.power n).nonneg w v
              _ = 1 := (K_V.power n).sum_one w
          have hpow1 : (1 - ∑ v : Fin n → V,
              if (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi
              then (K_V.power n).trans w v else 0) ^ L₂ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
          linarith
    _ = (1 - ∑ z ∈ strongTypicalSet P_WU n ε₀, (iidDist P_WU n).pmf z) + δ / 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (jointIidDist P_WU n).sum_one, one_mul]
        congr 1
        have hrew : (∑ wu : (Fin n → W) × (Fin n → U), (jointIidDist P_WU n).pmf wu *
              (if zipEquiv W U n wu ∉ strongTypicalSet P_WU n ε₀ then (1 : ℝ) else 0)) =
            ∑ z : Fin n → W × U, if z ∉ strongTypicalSet P_WU n ε₀ then (iidDist P_WU n).pmf z else 0 := by
          refine Fintype.sum_equiv (zipEquiv W U n) _ _ fun wu => ?_
          change (iidDist P_WU n).pmf (zipEquiv W U n wu) * _ = _
          split_ifs <;> ring
        rw [hrew]
        have hsplit : ∑ z : Fin n → W × U, (iidDist P_WU n).pmf z =
            (∑ z, if z ∈ strongTypicalSet P_WU n ε₀ then (iidDist P_WU n).pmf z else 0) +
            (∑ z, if z ∉ strongTypicalSet P_WU n ε₀ then (iidDist P_WU n).pmf z else 0) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by
            by_cases hm : z ∈ strongTypicalSet P_WU n ε₀ <;> simp [hm]
        rw [(iidDist P_WU n).sum_one] at hsplit
        have hmem : (∑ z, if z ∈ strongTypicalSet P_WU n ε₀ then (iidDist P_WU n).pmf z else 0) =
            ∑ z ∈ strongTypicalSet P_WU n ε₀, (iidDist P_WU n).pmf z := by
          rw [← Finset.sum_filter]; congr 1; ext z; simp
        linarith
    _ ≤ δ := by linarith [hN₁ n hn1]

open Classical in
/-- Helper: lower bound `p₀ ≥ (1/2) * 2^{-n(I(U;V|W) + 6ε')}` for 2D mutual covering. -/
private lemma mc_two_sided_p0_lower_bound (P : ProbDist (W × U × V))
    {εi ε₀ ε' : ℝ}
    (hεi : 0 < εi) (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < εi)
    (hle_W : εi * shannonEntropy (P.map (fun t => t.1)) ≤ ε')
    (hle_WU : εi * shannonEntropy (P.map (fun t => (t.1, t.2.1))) ≤ ε')
    (hle_WV : εi * shannonEntropy (P.map (fun t => (t.1, t.2.2))) ≤ ε')
    (hle_P : εi * shannonEntropy P ≤ ε')
    {n : ℕ} (hn_pos : 0 < n)
    (hmk_half : (∑ p : W × (U × V),
        if 0 < (P.map (fun t => (t.1, (t.2.1, t.2.2)))).pmf p
        then 1 / (P.map (fun t => (t.1, (t.2.1, t.2.2)))).pmf p ^ 2 else 0) /
        ((n : ℝ) * (εi - ε₀) ^ 2) ≤ 1 / 2)
    (w : Fin n → W) (hw : w ∈ strongTypicalSet (P.map (fun t => t.1)) n ε₀) :
    let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
    let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
    let I_UV := condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1)))
    let S : Finset ((Fin n → U) × (Fin n → V)) :=
      Finset.univ.filter fun uv => (fun i => (w i, uv.1 i, uv.2 i)) ∈ strongTypicalSet P n εi
    (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) ≤
      ∑ u : Fin n → U, ∑ v : Fin n → V,
        if (u, v) ∈ S then (dmcRow (K_U.power n) w).pmf u * (dmcRow (K_V.power n) w).pmf v else 0 := by
  dsimp only
  let P_W := P.map (fun t => t.1)
  let P_WU := P.map (fun t => (t.1, t.2.1))
  let P_WV := P.map (fun t => (t.1, t.2.2))
  let P_W_UV : ProbDist (W × (U × V)) := P.map (fun t => (t.1, (t.2.1, t.2.2)))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  let K_UV := condChannelOfJoint P_W_UV
  let I_UV := condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1)))
  have hP_W_UV_fst : P_W_UV.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_W_UV P_W; rw [map_comp_eq]; rfl
  have hP_WU_fst : P_WU.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_WU P_W; rw [map_comp_eq]; rfl
  have hP_WV_fst : P_WV.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_WV P_W; rw [map_comp_eq]; rfl
  let S : Finset ((Fin n → U) × (Fin n → V)) :=
    Finset.univ.filter fun uv => (fun i => (w i, uv.1 i, uv.2 i)) ∈ strongTypicalSet P n εi
  let Q₁ := dmcRow (K_U.power n) w
  let Q₂ := dmcRow (K_V.power n) w
  let eP : (W × U × V) ≃ (W × (U × V)) :=
    { toFun := fun t => (t.1, (t.2.1, t.2.2))
      invFun := fun t => (t.1, t.2.1, t.2.2)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hw_fst : w ∈ strongTypicalSet P_W_UV.fst n ε₀ := by rwa [hP_W_UV_fst]
  have hmk := mc_cond_typical_prob_not_mem_le P_W_UV hn_pos (le_of_lt hε₀) hε₀_lt hw_fst
  have hα_ge : 1 / 2 ≤ ∑ uv : (Fin n → U) × (Fin n → V),
      if uv ∈ S then (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) else 0 := by
    have hrew : (∑ uv : Fin n → U × V, (K_UV.power n).trans w uv *
          (if (fun i => (w i, uv i)) ∉ strongTypicalSet P_W_UV n εi then (1 : ℝ) else 0)) =
        ∑ uv : (Fin n → U) × (Fin n → V),
          if uv ∉ S then (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) else 0 := by
      symm
      refine Fintype.sum_equiv (zipEquiv U V n) _ _ fun ⟨u, v⟩ => ?_
      have heqv : (u, v) ∈ S ↔ (fun i => (w i, (u i, v i))) ∈ strongTypicalSet P_W_UV n εi := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact strongTypicalSet_map P eP n εi h
        · intro h
          have hm := strongTypicalSet_map P_W_UV eP.symm n εi h
          have hmap : P_W_UV.map eP.symm = P := by
            unfold P_W_UV; rw [map_comp_eq]; apply mc_probDist_ext; intro t
            unfold ProbDist.map; dsimp only [eP]; simp
          rwa [hmap] at hm
      change (if (u, v) ∉ S then (K_UV.power n).trans w (fun i => (u i, v i)) else 0) =
        (K_UV.power n).trans w (fun i => (u i, v i)) *
          (if (fun i => (w i, (u i, v i))) ∉ strongTypicalSet P_W_UV n εi then (1 : ℝ) else 0)
      by_cases hm : (u, v) ∈ S
      · simp [hm, heqv.mp hm]
      · simp [hm, mt heqv.mpr hm]
    have htot : ∑ uv : (Fin n → U) × (Fin n → V),
        (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) = 1 :=
      (Fintype.sum_equiv (zipEquiv U V n)
        (fun uv => (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)))
        (fun uv => (K_UV.power n).trans w uv) (fun _ => rfl)).trans ((K_UV.power n).sum_one w)
    have hsplit : ∑ uv : (Fin n → U) × (Fin n → V),
          (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) =
        (∑ uv, if uv ∈ S then (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) else 0) +
        (∑ uv, if uv ∉ S then (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun uv _ => by by_cases hm : uv ∈ S <;> simp [hm]
    have hmk' : (∑ uv : Fin n → U × V, (K_UV.power n).trans w uv *
          (if (fun i => (w i, uv i)) ∉ strongTypicalSet P_W_UV n εi then (1 : ℝ) else 0)) ≤ 1 / 2 := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun uv _ => ?_)) (le_trans hmk ?_)
      · congr 1; split_ifs <;> rfl
      · exact le_trans (le_of_eq (congrArg (· / _) (Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl))) hmk_half
    rw [htot] at hsplit; rw [hrew] at hmk'; linarith
  have hpt : ∀ (u : Fin n → U) (v : Fin n → V), (u, v) ∈ S →
      (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) *
        (K_UV.power n).trans w (fun i => (u i, v i)) ≤ Q₁.pmf u * Q₂.pmf v := by
    intro u v huv
    have hv : (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi := (Finset.mem_filter.mp huv).2
    have hw_w := strongTypicalSet_subset_weakTypicalSet P_W hn_pos hεi.le hle_W
      (strongTypicalSet_map P (fun t => t.1) n εi hv)
    have hwu_w := strongTypicalSet_subset_weakTypicalSet P_WU hn_pos hεi.le hle_WU
      (strongTypicalSet_map P (fun t => (t.1, t.2.1)) n εi hv)
    have hwv_w := strongTypicalSet_subset_weakTypicalSet P_WV hn_pos hεi.le hle_WV
      (strongTypicalSet_map P (fun t => (t.1, t.2.2)) n εi hv)
    have hv_w := strongTypicalSet_subset_weakTypicalSet P hn_pos hεi.le hle_P hv
    have hw_m := (Finset.mem_filter.mp hw_w).2
    have hwu_m := (Finset.mem_filter.mp hwu_w).2
    have hwv_m := (Finset.mem_filter.mp hwv_w).2
    have hv_m := (Finset.mem_filter.mp hv_w).2
    have hw_pos : 0 < (iidDist P_W n).pmf w := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hw_m.1
    have hQ1 : Q₁.pmf u = (iidDist P_WU n).pmf (fun i => (w i, u i)) / (iidDist P_W n).pmf w := by
      have hne : (iidDist P_WU.fst n).pmf w ≠ 0 := by rw [hP_WU_fst]; exact hw_pos.ne'
      simpa [Q₁, dmcRow, hP_WU_fst] using mc_condChannelOfJoint_power_eq_div P_WU n w u hne
    have hQ2 : Q₂.pmf v = (iidDist P_WV n).pmf (fun i => (w i, v i)) / (iidDist P_W n).pmf w := by
      have hne : (iidDist P_WV.fst n).pmf w ≠ 0 := by rw [hP_WV_fst]; exact hw_pos.ne'
      simpa [Q₂, dmcRow, hP_WV_fst] using mc_condChannelOfJoint_power_eq_div P_WV n w v hne
    have hKUV : (K_UV.power n).trans w (fun i => (u i, v i)) =
        (iidDist P n).pmf (fun i => (w i, u i, v i)) / (iidDist P_W n).pmf w := by
      have hne : (iidDist P_W_UV.fst n).pmf w ≠ 0 := by rw [hP_W_UV_fst]; exact hw_pos.ne'
      have heq := mc_condChannelOfJoint_power_eq_div P_W_UV n w (fun i => (u i, v i)) hne
      rw [hP_W_UV_fst] at heq; rw [heq]; congr 1
      unfold iidDist; dsimp only
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold P_W_UV ProbDist.map; dsimp only
      rw [Finset.sum_eq_single (w i, u i, v i)]
      · simp
      · intro t _ hne_t
        split_ifs with h
        · exact absurd (eP.injective h) hne_t
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hQ1, hQ2, hKUV]
    have hlb1 : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WU + ε'))) /
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε'))) ≤
        (iidDist P_WU n).pmf (fun i => (w i, u i)) / (iidDist P_W n).pmf w :=
      div_le_div₀ ((iidDist P_WU n).nonneg _) hwu_m.1 hw_pos hw_m.2
    have hlb2 : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WV + ε'))) /
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε'))) ≤
        (iidDist P_WV n).pmf (fun i => (w i, v i)) / (iidDist P_W n).pmf w :=
      div_le_div₀ ((iidDist P_WV n).nonneg _) hwv_m.1 hw_pos hw_m.2
    have hub : (iidDist P n).pmf (fun i => (w i, u i, v i)) / (iidDist P_W n).pmf w ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε'))) /
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W + ε'))) :=
      div_le_div₀ (by positivity) hv_m.2 (Real.rpow_pos_of_pos (by norm_num) _) hw_m.1
    have hmid : (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) *
        ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε'))) /
         (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W + ε')))) =
        ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WU + ε'))) /
         (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε')))) *
        ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_WV + ε'))) /
         (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W - ε')))) := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; dsimp only [I_UV]; rw [mc_condMutualInfo_triple_eq]; ring
    calc _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) *
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε'))) /
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_W + ε')))) :=
          mul_le_mul_of_nonneg_left hub (by positivity)
      _ = _ := hmid
      _ ≤ _ := mul_le_mul hlb1 hlb2 (by positivity)
          (div_nonneg ((iidDist P_WU n).nonneg _) hw_pos.le)
  calc (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε')))
    _ ≤ (∑ uv : (Fin n → U) × (Fin n → V),
          if uv ∈ S then (K_UV.power n).trans w (fun i => (uv.1 i, uv.2 i)) else 0) *
        (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) :=
        mul_le_mul_of_nonneg_right hα_ge (by positivity)
    _ = ∑ u : Fin n → U, ∑ v : Fin n → V,
          if (u, v) ∈ S then (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) *
            (K_UV.power n).trans w (fun i => (u i, v i)) else 0 := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
    _ ≤ _ := Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
        split_ifs with huv
        · exact hpt u v huv
        · exact le_rfl

open Classical in
/-- Helper: per-`w` Chebyshev bound for 2D mutual covering. -/
private lemma mc_mutual_covering_two_sided_per_w (P : ProbDist (W × U × V))
    {R₁ R₂ ε εi ε₀ ε' gap δ : ℝ}
    (hR₁_pos : 0 < R₁) (hR₂_pos : 0 < R₂)
    (hgap1 : gap ≤ R₁) (hgap2 : gap ≤ R₂)
    (hgap3 : gap ≤ R₁ + R₂ - condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))))
    (hεi : 0 < εi) (hεi_le : εi ≤ ε)
    (hε₀ : 0 < ε₀) (hε₀_lt : ε₀ < εi)
    (hε'_le : 10 * ε' ≤ gap / 2)
    (hle_W : εi * shannonEntropy (P.map (fun t => t.1)) ≤ ε')
    (hle_WU : εi * shannonEntropy (P.map (fun t => (t.1, t.2.1))) ≤ ε')
    (hle_WV : εi * shannonEntropy (P.map (fun t => (t.1, t.2.2))) ≤ ε')
    (hle_P : εi * shannonEntropy P ≤ ε')
    {n : ℕ} (hn_pos : 0 < n)
    (hmk_half : (∑ p : W × (U × V),
        if 0 < (P.map (fun t => (t.1, (t.2.1, t.2.2)))).pmf p
        then 1 / (P.map (fun t => (t.1, (t.2.1, t.2.2)))).pmf p ^ 2 else 0) /
        ((n : ℝ) * (εi - ε₀) ^ 2) ≤ 1 / 2)
    (hdecay : (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) ≤ δ / 12)
    (w : Fin n → W) (hw : w ∈ strongTypicalSet (P.map (fun t => t.1)) n ε₀) :
    let L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁))
    let L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
    let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
    let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
    ∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
      (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
        (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
         then (1 : ℝ) else 0)) ≤ δ / 2 := by
  dsimp only
  let P_W := P.map (fun t => t.1)
  let P_WU := P.map (fun t => (t.1, t.2.1))
  let P_WV := P.map (fun t => (t.1, t.2.2))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  let I_UV := condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1)))
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  set L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁))
  set L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
  have hL₁_pos : 0 < L₁ := mc_ceil_two_rpow_pos n hR₁_pos.le
  have hL₂_pos : 0 < L₂ := mc_ceil_two_rpow_pos n hR₂_pos.le
  let S : Finset ((Fin n → U) × (Fin n → V)) :=
    Finset.univ.filter fun uv => (fun i => (w i, uv.1 i, uv.2 i)) ∈ strongTypicalSet P n εi
  let Q₁ := dmcRow (K_U.power n) w
  let Q₂ := dmcRow (K_V.power n) w
  let p₀ := ∑ u : Fin n → U, ∑ v : Fin n → V, if (u, v) ∈ S then Q₁.pmf u * Q₂.pmf v else 0
  let p₁ := ∑ u : Fin n → U, Q₁.pmf u * (∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0) ^ 2
  let p₂ := ∑ v : Fin n → V, Q₂.pmf v * (∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0) ^ 2
  have hwk_all : ∀ (u : Fin n → U) (v : Fin n → V), (u, v) ∈ S →
      w ∈ weakTypicalSet P_W n ε' ∧
      (fun i => (w i, u i)) ∈ weakTypicalSet P_WU n ε' ∧
      (fun i => (w i, v i)) ∈ weakTypicalSet P_WV n ε' ∧
      (fun i => (w i, u i, v i)) ∈ weakTypicalSet P n ε' := by
    intro u v huv
    have hv : (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n εi := (Finset.mem_filter.mp huv).2
    exact ⟨strongTypicalSet_subset_weakTypicalSet P_W hn_pos hεi.le hle_W
        (strongTypicalSet_map P (fun t => t.1) n εi hv),
      strongTypicalSet_subset_weakTypicalSet P_WU hn_pos hεi.le hle_WU
        (strongTypicalSet_map P (fun t => (t.1, t.2.1)) n εi hv),
      strongTypicalSet_subset_weakTypicalSet P_WV hn_pos hεi.le hle_WV
        (strongTypicalSet_map P (fun t => (t.1, t.2.2)) n εi hv),
      strongTypicalSet_subset_weakTypicalSet P hn_pos hεi.le hle_P hv⟩
  have hp₀_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε'))) ≤ p₀ :=
    mc_two_sided_p0_lower_bound P hεi hε₀ hε₀_lt hle_W hle_WU hle_WV hle_P hn_pos hmk_half w hw
  have hp₀_pos : 0 < p₀ := lt_of_lt_of_le (by positivity) hp₀_ge
  have hp₁_le : p₁ ≤ p₀ * (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) := by
    have hqV : ∀ u : Fin n → U,
        (∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) := by
      intro u
      let eSwap : (W × U × V) ≃ (W × V × U) :=
        { toFun := fun t => (t.1, t.2.2, t.2.1)
          invFun := fun t => (t.1, t.2.2, t.2.1)
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
      let Ps := P.map eSwap
      have hpack := mc_pointwise_cond_packing Ps n ε' w u
      dsimp only at hpack
      have hI_s : condMutualInfo (Ps.map (fun t => (t.2.1, t.2.2, t.1))) = I_UV := by
        have hm : Ps.map (fun t => (t.2.1, t.2.2, t.1)) = P.map (fun t => (t.2.2, t.2.1, t.1)) := by
          unfold Ps; rw [map_comp_eq]; rfl
        rw [hm, mc_condMutualInfo_symm]
      have hPs_W : Ps.map (fun t => t.1) = P_W := by unfold Ps P_W; rw [map_comp_eq]; rfl
      have hPs_WV : Ps.map (fun t => (t.1, t.2.1)) = P_WV := by unfold Ps P_WV; rw [map_comp_eq]; rfl
      have hPs_WU : Ps.map (fun t => (t.1, t.2.2)) = P_WU := by unfold Ps P_WU; rw [map_comp_eq]; rfl
      rw [hI_s, hPs_W, hPs_WV, hPs_WU] at hpack
      refine le_trans (Finset.sum_le_sum fun v _ => ?_) hpack
      split_ifs with huv hcond
      · exact le_rfl
      · obtain ⟨hw_w, hwu_w, hwv_w, _⟩ := hwk_all u v huv
        have hv_st : (fun i => (w i, v i, u i)) ∈ strongTypicalSet Ps n εi :=
          strongTypicalSet_map P eSwap n εi (Finset.mem_filter.mp huv).2
        have hle_Ps : εi * shannonEntropy Ps ≤ ε' := by
          rw [shannonEntropy_map_equiv eSwap P]; exact hle_P
        have hv_wk := strongTypicalSet_subset_weakTypicalSet Ps hn_pos hεi.le hle_Ps hv_st
        exact absurd ⟨hw_w, hwv_w, hwu_w, hv_wk⟩ hcond
      · exact (K_V.power n).nonneg w v
      · exact le_rfl
    have hp₀_rew : p₀ = ∑ u : Fin n → U, Q₁.pmf u * (∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
    rw [hp₀_rew, Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [sq, mul_assoc]
    have hqnn : 0 ≤ ∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0 :=
      Finset.sum_nonneg fun v _ => by split_ifs; exact Q₂.nonneg v; exact le_rfl
    calc Q₁.pmf u * ((∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0) *
            (∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0))
      _ ≤ Q₁.pmf u * ((∑ v : Fin n → V, if (u, v) ∈ S then Q₂.pmf v else 0) *
            (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε')))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hqV u) hqnn) (Q₁.nonneg u)
      _ = _ := by ring
  have hp₂_le : p₂ ≤ p₀ * (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) := by
    have hqU : ∀ v : Fin n → V,
        (∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) := by
      intro v
      have hpack := mc_pointwise_cond_packing P n ε' w v
      dsimp only at hpack
      refine le_trans (Finset.sum_le_sum fun u _ => ?_) hpack
      split_ifs with huv hcond
      · exact le_rfl
      · exact absurd (hwk_all u v huv) hcond
      · exact (K_U.power n).nonneg w u
      · exact le_rfl
    have hp₀_rew : p₀ = ∑ v : Fin n → V, Q₂.pmf v * (∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0) := by
      dsimp only [p₀]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
    rw [hp₀_rew, Finset.sum_mul]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [sq, mul_assoc]
    have hqnn : 0 ≤ ∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0 :=
      Finset.sum_nonneg fun u _ => by split_ifs; exact Q₁.nonneg u; exact le_rfl
    calc Q₂.pmf v * ((∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0) *
            (∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0))
      _ ≤ Q₂.pmf v * ((∑ u : Fin n → U, if (u, v) ∈ S then Q₁.pmf u else 0) *
            (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε')))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hqU v) hqnn) (Q₂.nonneg v)
      _ = _ := by ring
  have hcheb := mutual_covering_chebyshev_bound Q₁ Q₂ hL₁_pos hL₂_pos S (by convert hp₀_pos)
  dsimp only at hcheb
  have hL1_ge : (2 : ℝ) ^ ((n : ℝ) * R₁) ≤ (L₁ : ℝ) := mc_two_rpow_le_ceil n R₁
  have hL2_ge : (2 : ℝ) ^ ((n : ℝ) * R₂) ≤ (L₂ : ℝ) := mc_two_rpow_le_ceil n R₂
  have hgap3' : gap ≤ R₁ + R₂ - I_UV := hgap3
  have hε'_nn : 0 ≤ ε' := le_trans (mul_nonneg hεi.le (shannonEntropy_nonneg P)) hle_P
  have ht1 : 1 / ((L₁ : ℝ) * (L₂ : ℝ) * p₀) ≤ δ / 6 := by
    have hden : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (gap / 2)) ≤ (L₁ : ℝ) * (L₂ : ℝ) * p₀ := by
      calc (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (gap / 2))
        _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂ - I_UV - 6 * ε')) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hn_r, hgap3', hε'_le, hε'_nn])) (by norm_num)
        _ = ((2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ ((n : ℝ) * R₂)) *
              ((1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε')))) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                mul_left_comm ((2 : ℝ) ^ _), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 2; ring
        _ ≤ ((L₁ : ℝ) * (L₂ : ℝ)) * p₀ :=
            mul_le_mul (mul_le_mul hL1_ge hL2_ge (by positivity) (by positivity))
              hp₀_ge (by positivity) (by positivity)
    calc 1 / ((L₁ : ℝ) * (L₂ : ℝ) * p₀)
      _ ≤ 1 / ((1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (gap / 2))) :=
          one_div_le_one_div_of_le (by positivity) hden
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; field_simp
      _ ≤ δ / 6 := by linarith only [hdecay]
  have ht2 : p₁ / ((L₁ : ℝ) * p₀ ^ 2) ≤ δ / 6 := by
    have h1 : p₁ / ((L₁ : ℝ) * p₀ ^ 2) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) / ((L₁ : ℝ) * p₀) := by
      calc p₁ / ((L₁ : ℝ) * p₀ ^ 2)
        _ ≤ (p₀ * (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε')))) / ((L₁ : ℝ) * p₀ ^ 2) :=
            div_le_div_of_nonneg_right hp₁_le (by positivity)
        _ = (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) / ((L₁ : ℝ) * p₀) := by
            field_simp [hp₀_pos.ne']
    have hden : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₁ - I_UV - 6 * ε')) ≤ (L₁ : ℝ) * p₀ := by
      calc (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₁ - I_UV - 6 * ε'))
        _ = (2 : ℝ) ^ ((n : ℝ) * R₁) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε')))) := by
            rw [mul_left_comm ((2 : ℝ) ^ _), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 2; ring
        _ ≤ (L₁ : ℝ) * p₀ := mul_le_mul hL1_ge hp₀_ge (by positivity) (by positivity)
    calc p₁ / ((L₁ : ℝ) * p₀ ^ 2)
      _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) /
          ((1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₁ - I_UV - 6 * ε'))) :=
          le_trans h1 (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * (R₁ - 10 * ε'))) := by
          rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_comm _ ((1 / 2 : ℝ)⁻¹), mul_assoc,
              ← div_eq_mul_inv, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
          norm_num; congr 2; ring
      _ ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hn_r, hgap1, hε'_le])) (by norm_num)
      _ ≤ δ / 6 := by linarith only [hdecay]
  have ht3 : p₂ / ((L₂ : ℝ) * p₀ ^ 2) ≤ δ / 6 := by
    have h1 : p₂ / ((L₂ : ℝ) * p₀ ^ 2) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) / ((L₂ : ℝ) * p₀) := by
      calc p₂ / ((L₂ : ℝ) * p₀ ^ 2)
        _ ≤ (p₀ * (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε')))) / ((L₂ : ℝ) * p₀ ^ 2) :=
            div_le_div_of_nonneg_right hp₂_le (by positivity)
        _ = (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) / ((L₂ : ℝ) * p₀) := by
            field_simp [hp₀_pos.ne']
    have hden : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₂ - I_UV - 6 * ε')) ≤ (L₂ : ℝ) * p₀ := by
      calc (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₂ - I_UV - 6 * ε'))
        _ = (2 : ℝ) ^ ((n : ℝ) * R₂) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I_UV + 6 * ε')))) := by
            rw [mul_left_comm ((2 : ℝ) ^ _), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 2; ring
        _ ≤ (L₂ : ℝ) * p₀ := mul_le_mul hL2_ge hp₀_ge (by positivity) (by positivity)
    calc p₂ / ((L₂ : ℝ) * p₀ ^ 2)
      _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (I_UV - 4 * ε'))) /
          ((1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (R₂ - I_UV - 6 * ε'))) :=
          le_trans h1 (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * (R₂ - 10 * ε'))) := by
          rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_comm _ ((1 / 2 : ℝ)⁻¹), mul_assoc,
              ← div_eq_mul_inv, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
          norm_num; congr 2; ring
      _ ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hn_r, hgap2, hε'_le])) (by norm_num)
      _ ≤ δ / 6 := by linarith only [hdecay]
  have hsum_bd : 1 / ((L₁ : ℝ) * (L₂ : ℝ) * p₀) + p₁ / ((L₁ : ℝ) * p₀ ^ 2) + p₂ / ((L₂ : ℝ) * p₀ ^ 2) ≤ δ / 2 := by
    linarith only [ht1, ht2, ht3]
  refine le_trans ?_ (le_trans hcheb (by convert hsum_bd))
  refine Finset.sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun C₂ _ =>
    mul_le_mul_of_nonneg_left ?_ ((iidDist Q₂ L₂).nonneg C₂)) ((iidDist Q₁ L₁).nonneg C₁)
  split_ifs with h h'
  · exact le_rfl
  · exact absurd (fun l₁ l₂ (hm : (C₁ l₁, C₂ l₂) ∈ S) =>
      h l₁ l₂ (mc_strongTypicalSet_mono P n hεi_le (Finset.mem_filter.mp hm).2)) h'
  · norm_num
  · exact le_rfl

open Classical in
/-- Helper: 2D mutual covering when both `R₁ > 0` and `R₂ > 0` and `I(U; V | W) < R₁ + R₂`. -/
private lemma mc_mutual_covering_two_sided (P : ProbDist (W × U × V))
    {R₁ R₂ ε δ : ℝ} (hR₁_pos : 0 < R₁) (hR₂_pos : 0 < R₂)
    (hsum : condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) < R₁ + R₂)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁))
      let L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
      let P_W := P.map (fun t => t.1)
      let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
      let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
      ∑ w : Fin n → W, (iidDist P_W n).pmf w *
        (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
          (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
                (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
             then (1 : ℝ) else 0))) ≤ δ := by
  let P_W := P.map (fun t => t.1)
  let P_WU := P.map (fun t => (t.1, t.2.1))
  let P_WV := P.map (fun t => (t.1, t.2.2))
  let P_W_UV : ProbDist (W × (U × V)) := P.map (fun t => (t.1, (t.2.1, t.2.2)))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  let I_UV := condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1)))
  let gap : ℝ := min (min R₁ R₂) (R₁ + R₂ - I_UV)
  have hgap : 0 < gap := lt_min (lt_min hR₁_pos hR₂_pos) (by linarith)
  let Hmax : ℝ := shannonEntropy P_W + shannonEntropy P_WU + shannonEntropy P_WV + shannonEntropy P + 1
  have hHmax : 1 ≤ Hmax := by
    dsimp [Hmax]
    linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WU,
      shannonEntropy_nonneg P_WV, shannonEntropy_nonneg P]
  have hHmax_pos : 0 < Hmax := by linarith
  let εi : ℝ := min ε (gap / (20 * Hmax))
  have hεi : 0 < εi := lt_min hε (by positivity)
  have hεi_le : εi ≤ ε := min_le_left _ _
  let ε' : ℝ := εi * Hmax
  have hε'_le : 10 * ε' ≤ gap / 2 := by
    have h1 : εi ≤ gap / (20 * Hmax) := min_le_right _ _
    have h2 : ε' ≤ gap / 20 := by
      dsimp [ε']
      calc εi * Hmax ≤ (gap / (20 * Hmax)) * Hmax := mul_le_mul_of_nonneg_right h1 hHmax_pos.le
        _ = gap / 20 := by field_simp [hHmax_pos.ne']
    linarith
  let ε₀ : ℝ := εi / 2
  have hε₀ : 0 < ε₀ := half_pos hεi
  have hε₀_lt : ε₀ < εi := by dsimp [ε₀]; linarith
  have hle_W : εi * shannonEntropy P_W ≤ ε' := mul_le_mul_of_nonneg_left (by
    dsimp [Hmax]; linarith [shannonEntropy_nonneg P_WU, shannonEntropy_nonneg P_WV, shannonEntropy_nonneg P]) hεi.le
  have hle_WU : εi * shannonEntropy P_WU ≤ ε' := mul_le_mul_of_nonneg_left (by
    dsimp [Hmax]; linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WV, shannonEntropy_nonneg P]) hεi.le
  have hle_WV : εi * shannonEntropy P_WV ≤ ε' := mul_le_mul_of_nonneg_left (by
    dsimp [Hmax]; linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WU, shannonEntropy_nonneg P]) hεi.le
  have hle_P : εi * shannonEntropy P ≤ ε' := mul_le_mul_of_nonneg_left (by
    dsimp [Hmax]; linarith [shannonEntropy_nonneg P_W, shannonEntropy_nonneg P_WU, shannonEntropy_nonneg P_WV]) hεi.le
  let C_mk : ℝ := ∑ p : W × (U × V), if 0 < P_W_UV.pmf p then 1 / P_W_UV.pmf p ^ 2 else 0
  obtain ⟨N₁, hN₁⟩ := strongTypicalSet_prob_tendsto_one P_W hε₀ (half_pos hδ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * C_mk / (εi - ε₀) ^ 2)
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (log2 (1 / (δ / 12)) / (gap / 2))
  refine ⟨max (max (max N₁ N₂) N₃) 1, fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hn)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ N₃)) (le_trans (le_max_left _ 1) hn)
  have hn2 : 2 * C_mk / (εi - ε₀) ^ 2 < (n : ℝ) := lt_of_lt_of_le hN₂ (by
    exact_mod_cast le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ N₃)) (le_trans (le_max_left _ 1) hn))
  have hn3 : log2 (1 / (δ / 12)) / (gap / 2) ≤ (n : ℝ) := le_trans hN₃ (by
    exact_mod_cast le_trans (le_max_right _ N₃) (le_trans (le_max_left _ 1) hn))
  have hdecay : (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) ≤ δ / 12 :=
    mc_two_rpow_neg_le_of_ge (half_pos hgap) (by positivity) hn3
  have hmk_half : C_mk / ((n : ℝ) * (εi - ε₀) ^ 2) ≤ 1 / 2 := by
    have hdiff : 0 < εi - ε₀ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have h1 := (div_lt_iff₀ (by positivity : 0 < (εi - ε₀) ^ 2)).mp hn2
    linarith
  set L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁))
  set L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
  have hgood : ∀ w : Fin n → W, w ∈ strongTypicalSet P_W n ε₀ →
      (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
           then (1 : ℝ) else 0))) ≤ δ / 2 :=
    fun w hw => mc_mutual_covering_two_sided_per_w P hR₁_pos hR₂_pos
      (le_trans (min_le_left _ _) (min_le_left _ _))
      (le_trans (min_le_left _ _) (min_le_right _ _))
      (min_le_right _ _)
      hεi hεi_le hε₀ hε₀_lt hε'_le hle_W hle_WU hle_WV hle_P hn_pos hmk_half hdecay w hw
  calc _ ≤ ∑ w : Fin n → W, (iidDist P_W n).pmf w *
          ((if w ∉ strongTypicalSet P_W n ε₀ then (1 : ℝ) else 0) + δ / 2) := by
        refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ ((iidDist P_W n).nonneg w)
        by_cases hw : w ∈ strongTypicalSet P_W n ε₀
        · simp only [hw, not_true_eq_false, ↓reduceIte, zero_add]
          exact hgood w hw
        · simp only [hw, not_false_eq_true, ↓reduceIte]
          have hle1 : (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
              (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
                (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
                    (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
                 then (1 : ℝ) else 0))) ≤ 1 := by
            calc _ ≤ ∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
                    (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ * 1) :=
                  Finset.sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left
                    (Finset.sum_le_sum fun C₂ _ => mul_le_mul_of_nonneg_left
                      (by split_ifs <;> norm_num) ((iidDist _ L₂).nonneg C₂))
                    ((iidDist _ L₁).nonneg C₁)
              _ = 1 := by simp [(iidDist _ L₂).sum_one, (iidDist _ L₁).sum_one]
          linarith
    _ = (1 - ∑ w ∈ strongTypicalSet P_W n ε₀, (iidDist P_W n).pmf w) + δ / 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (iidDist P_W n).sum_one, one_mul]
        congr 1
        have hsplit : ∑ w : Fin n → W, (iidDist P_W n).pmf w =
            (∑ w, if w ∈ strongTypicalSet P_W n ε₀ then (iidDist P_W n).pmf w else 0) +
            (∑ w, (iidDist P_W n).pmf w * (if w ∉ strongTypicalSet P_W n ε₀ then (1 : ℝ) else 0)) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by
            by_cases hw : w ∈ strongTypicalSet P_W n ε₀ <;> simp [hw]
        rw [(iidDist P_W n).sum_one] at hsplit
        have hmem : (∑ w, if w ∈ strongTypicalSet P_W n ε₀ then (iidDist P_W n).pmf w else 0) =
            ∑ w ∈ strongTypicalSet P_W n ε₀, (iidDist P_W n).pmf w := by
          rw [← Finset.sum_filter]; congr 1; ext w; simp
        linarith
    _ ≤ δ := by linarith [hN₁ n hn1]

open Classical in
/-- **Mutual Covering Lemma** (El Gamal–Kim Lemma 8.1; Marton 1979):
    given any joint distribution `P : ProbDist (W × U × V)` and rates `R₁ ≥ 0, R₂ ≥ 0` with
    `I(U; V | W) < R₁ + R₂`, drawing `W^n ~ P_W^n`, `L₁ = ⌈2^(n R₁)⌉` conditionally i.i.d.
    sequences `U^n(l₁) ~ P_{U|W}^n(· | W^n)`, and `L₂ = ⌈2^(n R₂)⌉` conditionally i.i.d.
    sequences `V^n(l₂) ~ P_{V|W}^n(· | W^n)` independently given `W^n`, the probability that
    no pair `(l₁, l₂)` is jointly strongly `ε`-typical with `W^n` is at most `δ` for all
    sufficiently large `n`. -/
theorem mutual_covering_lemma (P : ProbDist (W × U × V)) {R₁ R₂ ε δ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hsum : condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) < R₁ + R₂)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁))
      let L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂))
      let P_W := P.map (fun t => t.1)
      let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
      let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
      ∑ w : Fin n → W, (iidDist P_W n).pmf w *
        (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
          (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
                (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
             then (1 : ℝ) else 0))) ≤ δ := by
  rcases hR₁.eq_or_lt with rfl | hR₁_pos
  · rw [zero_add] at hsum
    exact mc_mutual_covering_one_sided P hsum hε hδ
  · rcases hR₂.eq_or_lt with rfl | hR₂_pos
    · rw [add_zero] at hsum
      let eSwap : (W × U × V) ≃ (W × V × U) :=
        { toFun := fun t => (t.1, t.2.2, t.2.1)
          invFun := fun t => (t.1, t.2.2, t.2.1)
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
      let P' : ProbDist (W × V × U) := P.map eSwap
      have hI_eq : condMutualInfo (P'.map (fun t => (t.2.1, t.2.2, t.1))) =
          condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) := by
        have hm : P'.map (fun t => (t.2.1, t.2.2, t.1)) = P.map (fun t => (t.2.2, t.2.1, t.1)) := by
          unfold P'; rw [map_comp_eq]; rfl
        rw [hm, mc_condMutualInfo_symm]
      obtain ⟨N, hN⟩ := mc_mutual_covering_one_sided P' (hI_eq ▸ hsum) hε hδ
      refine ⟨N, fun n hn => ?_⟩
      have hbound := hN n hn
      dsimp only at hbound ⊢
      have hP'W : P'.map (fun t => t.1) = P.map (fun t => t.1) := by
        unfold P'; rw [map_comp_eq]; rfl
      have hP'WV : P'.map (fun t => (t.1, t.2.1)) = P.map (fun t => (t.1, t.2.2)) := by
        unfold P'; rw [map_comp_eq]; rfl
      have hP'WU : P'.map (fun t => (t.1, t.2.2)) = P.map (fun t => (t.1, t.2.1)) := by
        unfold P'; rw [map_comp_eq]; rfl
      rw [hP'W, hP'WV, hP'WU] at hbound
      refine le_trans (le_of_eq ?_) hbound
      refine Finset.sum_congr rfl fun w _ => congrArg _ ?_
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun C₂ _ => Finset.sum_congr rfl fun C₁ _ => ?_
      have heqv : (∀ (l₁ : Fin (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁))))
          (l₂ : Fin (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ))))),
          (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε) ↔
          (∀ (l₂ : Fin (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ)))))
            (l₁ : Fin (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁)))),
          (fun i => (w i, C₂ l₂ i, C₁ l₁ i)) ∉ strongTypicalSet P' n ε) := by
        constructor
        · intro h l₂ l₁ hmem
          have hm := strongTypicalSet_map P' eSwap.symm n ε hmem
          have hmap : P'.map eSwap.symm = P := by
            unfold P'; rw [map_comp_eq]; apply mc_probDist_ext; intro t
            unfold ProbDist.map; dsimp only [eSwap]; simp
          rw [hmap] at hm
          exact h l₁ l₂ hm
        · intro h l₁ l₂ hmem
          exact h l₂ l₁ (strongTypicalSet_map P eSwap n ε hmem)
      split_ifs with h1 h2 h3
      · ring
      · exact absurd (heqv.mp h1) h2
      · exact absurd (heqv.mpr h3) h1
      · ring
    · exact mc_mutual_covering_two_sided P hR₁_pos hR₂_pos hsum hε hδ

open Classical in
/-- Helper: when `R₁' = R₂' = 0` and `I(U; V | W) = 0`, `U ⊥ V | W` so single draws
    `(W^n, U^n(0), V^n(0))` are i.i.d. `P^n`, hence strongly typical with high probability. -/
private lemma mc_covering_cond_indep (P : ProbDist (W × U × V))
    (hci : condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) = 0)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let L := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ)))
      let P_W := P.map (fun t => t.1)
      let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
      let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
      ∑ w : Fin n → W, (iidDist P_W n).pmf w *
        (∑ C₁ : Fin L → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L).pmf C₁ *
          (∑ C₂ : Fin L → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L).pmf C₂ *
            (if ∀ (l₁ : Fin L) (l₂ : Fin L),
                (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
             then (1 : ℝ) else 0))) ≤ δ := by
  let P_W := P.map (fun t => t.1)
  let P_WU := P.map (fun t => (t.1, t.2.1))
  let P_WV := P.map (fun t => (t.1, t.2.2))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  obtain ⟨N₁, hN₁⟩ := strongTypicalSet_prob_tendsto_one P hε hδ
  refine ⟨N₁, fun n hn => ?_⟩
  dsimp only
  have hL1 : Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ))) = 1 := mc_ceil_two_rpow_zero n
  have hfac : ∀ w u v, P_W.pmf w * K_U.trans w u * K_V.trans w v = P.pmf (w, u, v) := by
    intro w u v
    let R := P.map (fun t => (t.2.1, t.2.2, t.1))
    have hRci := (condMutualInfo_eq_zero_iff R).mp hci
    let eR : (W × U × V) ≃ (U × V × W) :=
      { toFun := fun t => (t.2.1, t.2.2, t.1)
        invFun := fun t => (t.2.2, t.1, t.2.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hR_pmf : R.pmf (u, v, w) = P.pmf (w, u, v) := by
      unfold R ProbDist.map; dsimp only
      rw [Finset.sum_eq_single (w, u, v)]
      · simp
      · intro t _ hne
        split_ifs with h
        · exact absurd (eR.injective h) hne
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_xz : (R.map (fun t => (t.1, t.2.2))).pmf (u, w) = P_WU.pmf (w, u) := by
      have hs : R.map (fun t => (t.1, t.2.2)) = P_WU.map Prod.swap := by
        unfold R P_WU; rw [map_comp_eq, map_comp_eq]; rfl
      rw [hs]; unfold ProbDist.map; dsimp only
      rw [Finset.sum_eq_single (w, u)]
      · simp
      · intro p _ hne
        split_ifs with h
        · exact absurd ((Equiv.prodComm W U).injective h) hne
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_yz : (R.map (fun t => (t.2.1, t.2.2))).pmf (v, w) = P_WV.pmf (w, v) := by
      have hs : R.map (fun t => (t.2.1, t.2.2)) = P_WV.map Prod.swap := by
        unfold R P_WV; rw [map_comp_eq, map_comp_eq]; rfl
      rw [hs]; unfold ProbDist.map; dsimp only
      rw [Finset.sum_eq_single (w, v)]
      · simp
      · intro p _ hne
        split_ifs with h
        · exact absurd ((Equiv.prodComm W V).injective h) hne
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_z : R.map (fun t => t.2.2) = P_W := by
      unfold R P_W; rw [map_comp_eq]; rfl
    have h1 := congrArg (fun D : ProbDist (U × V × W) => D.pmf (u, v, w)) hRci
    change R.pmf (u, v, w) = if (R.map (fun t => t.2.2)).pmf w = 0 then 0
      else (R.map (fun t => (t.1, t.2.2))).pmf (u, w) *
        (R.map (fun t => (t.2.1, t.2.2))).pmf (v, w) / (R.map (fun t => t.2.2)).pmf w at h1
    rw [hR_pmf, hR_xz, hR_yz, hR_z] at h1
    have hWU_fst : P_WU.fst = P_W := by
      rw [← mc_probDist_map_fst]; unfold P_WU P_W; rw [map_comp_eq]; rfl
    have hWV_fst : P_WV.fst = P_W := by
      rw [← mc_probDist_map_fst]; unfold P_WV P_W; rw [map_comp_eq]; rfl
    by_cases hw0 : P_W.pmf w = 0
    · simp only [hw0, ↓reduceIte] at h1
      rw [hw0, zero_mul, zero_mul, h1]
    · simp only [hw0, ↓reduceIte] at h1
      have hmU : P_W.pmf w * K_U.trans w u = P_WU.pmf (w, u) := by
        have h := condChannelOfJoint_mul P_WU w u; rwa [hWU_fst] at h
      have hmV : P_W.pmf w * K_V.trans w v = P_WV.pmf (w, v) := by
        have h := condChannelOfJoint_mul P_WV w v; rwa [hWV_fst] at h
      rw [h1, ← hmU, ← hmV]
      field_simp [hw0]
  have hfac_n : ∀ w u v,
      (iidDist P_W n).pmf w * (K_U.power n).trans w u * (K_V.power n).trans w v =
      (iidDist P n).pmf (fun i => (w i, u i, v i)) := fun w u v => by
    unfold iidDist DMC.power; dsimp only
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hfac (w i) (u i) (v i)
  set L := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * (0 : ℝ)))
  have hpos1 : 0 < L := by rw [hL1]; exact Nat.zero_lt_one
  let z0 : Fin L := ⟨0, hpos1⟩
  have hfin_eq : ∀ l : Fin L, l = z0 := fun l =>
    Fin.ext (by have hlt : l.val < 1 := hL1 ▸ l.isLt; omega)
  have hall_eq : ∀ (w : Fin n → W) (C₁ : Fin L → Fin n → U) (C₂ : Fin L → Fin n → V),
      (∀ l₁ l₂, (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε) ↔
      (fun i => (w i, C₁ z0 i, C₂ z0 i)) ∉ strongTypicalSet P n ε := fun w C₁ C₂ =>
    ⟨fun h => h z0 z0, fun h l₁ l₂ => by rw [hfin_eq l₁, hfin_eq l₂]; exact h⟩
  have hinner : ∀ w : Fin n → W,
      (∑ C₁ : Fin L → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L).pmf C₁ *
        (∑ C₂ : Fin L → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L).pmf C₂ *
          (if ∀ l₁ l₂, (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
           then (1 : ℝ) else 0))) =
      ∑ u : Fin n → U, (K_U.power n).trans w u *
        (∑ v : Fin n → V, (K_V.power n).trans w v *
          (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n ε then (1 : ℝ) else 0)) := by
    intro w
    have hC2 : ∀ C₁ : Fin L → Fin n → U,
        (∑ C₂ : Fin L → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L).pmf C₂ *
          (if ∀ l₁ l₂, (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
           then (1 : ℝ) else 0)) =
        ∑ v : Fin n → V, (K_V.power n).trans w v *
          (if (fun i => (w i, C₁ z0 i, v i)) ∉ strongTypicalSet P n ε then (1 : ℝ) else 0) := fun C₁ => by
      simp_rw [hall_eq]
      exact iidDist_sum_coord (dmcRow (K_V.power n) w)
        (fun v : Fin n → V => if (fun i => (w i, C₁ z0 i, v i)) ∉ strongTypicalSet P n ε then (1 : ℝ) else 0) z0
    simp_rw [hC2]
    exact iidDist_sum_coord (dmcRow (K_U.power n) w)
      (fun u : Fin n → U => ∑ v : Fin n → V, (K_V.power n).trans w v *
        (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n ε then (1 : ℝ) else 0)) z0
  have hgoal_eq : (∑ w : Fin n → W, (iidDist (P.map (fun t => t.1)) n).pmf w *
        (∑ C₁ : Fin L → Fin n → U, (iidDist (dmcRow ((condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))).power n) w) L).pmf C₁ *
          (∑ C₂ : Fin L → Fin n → V, (iidDist (dmcRow ((condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))).power n) w) L).pmf C₂ *
            (if ∀ (l₁ : Fin L) (l₂ : Fin L),
                (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P n ε
             then (1 : ℝ) else 0)))) =
      ∑ w : Fin n → W, (iidDist P_W n).pmf w *
        (∑ u : Fin n → U, (K_U.power n).trans w u *
          (∑ v : Fin n → V, (K_V.power n).trans w v *
            (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n ε then (1 : ℝ) else 0))) :=
    Finset.sum_congr rfl fun w _ => congrArg ((iidDist P_W n).pmf w * ·) (hinner w)
  rw [hgoal_eq]
  have hprod : (∑ w : Fin n → W, (iidDist P_W n).pmf w *
        (∑ u : Fin n → U, (K_U.power n).trans w u *
          (∑ v : Fin n → V, (K_V.power n).trans w v *
            (if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n ε then (1 : ℝ) else 0)))) =
      ∑ z : Fin n → W × U × V,
        if z ∉ strongTypicalSet P n ε then (iidDist P n).pmf z else 0 := by
    let e3 : ((Fin n → W) × (Fin n → U) × (Fin n → V)) ≃ (Fin n → W × U × V) :=
      { toFun := fun t i => (t.1 i, t.2.1 i, t.2.2 i)
        invFun := fun z => (fun i => (z i).1, fun i => (z i).2.1, fun i => (z i).2.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun _ => rfl }
    trans (∑ t : (Fin n → W) × (Fin n → U) × (Fin n → V),
        if e3 t ∉ strongTypicalSet P n ε then (iidDist P n).pmf (e3 t) else 0)
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      change _ = if (fun i => (w i, u i, v i)) ∉ strongTypicalSet P n ε
        then (iidDist P n).pmf (fun i => (w i, u i, v i)) else 0
      by_cases hm : (fun i => (w i, u i, v i)) ∈ strongTypicalSet P n ε
      · simp [hm]
      · simp only [hm, not_false_eq_true, ↓reduceIte, mul_one, ← mul_assoc]
        exact hfac_n w u v
    · exact Fintype.sum_equiv e3 _ _ (fun _ => rfl)
  rw [hprod]
  have hsplit : ∑ z : Fin n → W × U × V, (iidDist P n).pmf z =
      (∑ z, if z ∈ strongTypicalSet P n ε then (iidDist P n).pmf z else 0) +
      (∑ z, if z ∉ strongTypicalSet P n ε then (iidDist P n).pmf z else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      by_cases hm : z ∈ strongTypicalSet P n ε <;> simp [hm]
  rw [(iidDist P n).sum_one] at hsplit
  have hmem : (∑ z, if z ∈ strongTypicalSet P n ε then (iidDist P n).pmf z else 0) =
      ∑ z ∈ strongTypicalSet P n ε, (iidDist P n).pmf z := by
    rw [← Finset.sum_filter]; congr 1; ext z; simp
  linarith [hN₁ n hn]

end MutualCovering

/-! ### 3. Fourier–Motzkin Rate Splitting for the Marton Pentagon -/

section RateSplitting

/-- Helper: picking a point `(r₁, r₂)` in a closed box `[x₁, y₁] × [x₂, y₂]` satisfying
    strict bounds `l₁ < r₁ < h₁`, `l₂ < r₂ < h₂`, and `s_lo < r₁ + r₂ < s_hi`. -/
private lemma mc_exists_box_sum {x₁ y₁ l₁ h₁ x₂ y₂ l₂ h₂ s_lo s_hi : ℝ}
    (hxy1 : x₁ ≤ y₁) (hlh1 : l₁ < h₁) (hxl1 : x₁ < h₁) (hly1 : l₁ < y₁)
    (hxy2 : x₂ ≤ y₂) (hlh2 : l₂ < h₂) (hxl2 : x₂ < h₂) (hly2 : l₂ < y₂)
    (hs : s_lo < s_hi)
    (h1 : max x₁ l₁ + max x₂ l₂ < s_hi)
    (h2 : s_lo < min y₁ h₁ + min y₂ h₂) :
    ∃ r₁ r₂ : ℝ,
      x₁ ≤ r₁ ∧ r₁ ≤ y₁ ∧ l₁ < r₁ ∧ r₁ < h₁ ∧
      x₂ ≤ r₂ ∧ r₂ ≤ y₂ ∧ l₂ < r₂ ∧ r₂ < h₂ ∧
      s_lo < r₁ + r₂ ∧ r₁ + r₂ < s_hi := by
  let L₁ : ℝ := max x₁ l₁
  let H₁ : ℝ := min y₁ h₁
  let L₂ : ℝ := max x₂ l₂
  let H₂ : ℝ := min y₂ h₂
  let δ : ℝ := min (s_hi - (L₁ + L₂)) ((H₁ + H₂) - s_lo) / 8
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hp1 : 0 < s_hi - (L₁ + L₂) := by linarith only [h1]
    have hp2 : 0 < (H₁ + H₂) - s_lo := by linarith only [h2]
    positivity
  have hδs1 : δ ≤ (s_hi - (L₁ + L₂)) / 8 := by
    dsimp only [δ]; linarith only [min_le_left (s_hi - (L₁ + L₂)) ((H₁ + H₂) - s_lo)]
  have hδs2 : δ ≤ ((H₁ + H₂) - s_lo) / 8 := by
    dsimp only [δ]; linarith only [min_le_right (s_hi - (L₁ + L₂)) ((H₁ + H₂) - s_lo)]
  let a₁ : ℝ := if x₁ = y₁ then x₁ else min (L₁ + δ) ((L₁ + H₁) / 2)
  let b₁ : ℝ := if x₁ = y₁ then x₁ else max (H₁ - δ) ((L₁ + H₁) / 2)
  let a₂ : ℝ := if x₂ = y₂ then x₂ else min (L₂ + δ) ((L₂ + H₂) / 2)
  let b₂ : ℝ := if x₂ = y₂ then x₂ else max (H₂ - δ) ((L₂ + H₂) / 2)
  have ha1_props : x₁ ≤ a₁ ∧ a₁ ≤ b₁ ∧ b₁ ≤ y₁ ∧ l₁ < a₁ ∧ b₁ < h₁ ∧ a₁ ≤ L₁ + δ ∧ H₁ - δ ≤ b₁ := by
    dsimp only [a₁, b₁]
    by_cases heq : x₁ = y₁
    · simp only [heq, ↓reduceIte]
      have hL1 : L₁ = y₁ := by dsimp [L₁]; rw [heq]; exact max_eq_left (le_of_lt hly1)
      have hH1 : H₁ = y₁ := by dsimp [H₁]; exact min_eq_left (le_of_lt (heq ▸ hxl1))
      refine ⟨le_rfl, le_rfl, le_rfl, hly1, heq ▸ hxl1, ?_, ?_⟩ <;> linarith only [hL1, hH1, hδ, heq]
    · simp only [heq, ↓reduceIte]
      have hlt : x₁ < y₁ := lt_of_le_of_ne hxy1 heq
      have hLH1_lt : L₁ < H₁ := lt_min (max_lt hlt hly1) (max_lt hxl1 hlh1)
      have hL1x : x₁ ≤ L₁ := le_max_left x₁ l₁
      have hL1l : l₁ ≤ L₁ := le_max_right x₁ l₁
      have hH1y : H₁ ≤ y₁ := min_le_left y₁ h₁
      have hH1h : H₁ ≤ h₁ := min_le_right y₁ h₁
      refine ⟨?_, ?_, ?_, ?_, ?_, min_le_left (L₁ + δ) ((L₁ + H₁) / 2), le_max_left (H₁ - δ) ((L₁ + H₁) / 2)⟩
      · exact le_min (by linarith only [hL1x, hδ]) (by linarith only [hL1x, hLH1_lt])
      · exact le_trans (min_le_right (L₁ + δ) ((L₁ + H₁) / 2)) (le_max_right (H₁ - δ) ((L₁ + H₁) / 2))
      · exact max_le (by linarith only [hH1y, hδ]) (by linarith only [hH1y, hLH1_lt])
      · exact lt_min (by linarith only [hL1l, hδ]) (by linarith only [hL1l, hLH1_lt])
      · exact max_lt (by linarith only [hH1h, hδ]) (by linarith only [hH1h, hLH1_lt])
  have ha2_props : x₂ ≤ a₂ ∧ a₂ ≤ b₂ ∧ b₂ ≤ y₂ ∧ l₂ < a₂ ∧ b₂ < h₂ ∧ a₂ ≤ L₂ + δ ∧ H₂ - δ ≤ b₂ := by
    dsimp only [a₂, b₂]
    by_cases heq : x₂ = y₂
    · simp only [heq, ↓reduceIte]
      have hL2 : L₂ = y₂ := by dsimp [L₂]; rw [heq]; exact max_eq_left (le_of_lt hly2)
      have hH2 : H₂ = y₂ := by dsimp [H₂]; exact min_eq_left (le_of_lt (heq ▸ hxl2))
      refine ⟨le_rfl, le_rfl, le_rfl, hly2, heq ▸ hxl2, ?_, ?_⟩ <;> linarith only [hL2, hH2, hδ, heq]
    · simp only [heq, ↓reduceIte]
      have hlt : x₂ < y₂ := lt_of_le_of_ne hxy2 heq
      have hLH2_lt : L₂ < H₂ := lt_min (max_lt hlt hly2) (max_lt hxl2 hlh2)
      have hL2x : x₂ ≤ L₂ := le_max_left x₂ l₂
      have hL2l : l₂ ≤ L₂ := le_max_right x₂ l₂
      have hH2y : H₂ ≤ y₂ := min_le_left y₂ h₂
      have hH2h : H₂ ≤ h₂ := min_le_right y₂ h₂
      refine ⟨?_, ?_, ?_, ?_, ?_, min_le_left (L₂ + δ) ((L₂ + H₂) / 2), le_max_left (H₂ - δ) ((L₂ + H₂) / 2)⟩
      · exact le_min (by linarith only [hL2x, hδ]) (by linarith only [hL2x, hLH2_lt])
      · exact le_trans (min_le_right (L₂ + δ) ((L₂ + H₂) / 2)) (le_max_right (H₂ - δ) ((L₂ + H₂) / 2))
      · exact max_le (by linarith only [hH2y, hδ]) (by linarith only [hH2y, hLH2_lt])
      · exact lt_min (by linarith only [hL2l, hδ]) (by linarith only [hL2l, hLH2_lt])
      · exact max_lt (by linarith only [hH2h, hδ]) (by linarith only [hH2h, hLH2_lt])
  have hab_sum_lt : a₁ + a₂ < s_hi := by linarith only [ha1_props.2.2.2.2.2.1, ha2_props.2.2.2.2.2.1, hδs1, h1]
  have hab_sum_gt : s_lo < b₁ + b₂ := by linarith only [ha1_props.2.2.2.2.2.2, ha2_props.2.2.2.2.2.2, hδs2, h2]
  have hab_le : a₁ + a₂ ≤ b₁ + b₂ := by linarith only [ha1_props.2.1, ha2_props.2.1]
  by_cases hsum_eq : a₁ + a₂ = b₁ + b₂
  · refine ⟨a₁, a₂, ha1_props.1, le_trans ha1_props.2.1 ha1_props.2.2.1, ha1_props.2.2.2.1,
      lt_of_le_of_lt ha1_props.2.1 ha1_props.2.2.2.2.1,
      ha2_props.1, le_trans ha2_props.2.1 ha2_props.2.2.1, ha2_props.2.2.2.1,
      lt_of_le_of_lt ha2_props.2.1 ha2_props.2.2.2.2.1, by linarith only [hab_sum_gt, hsum_eq], hab_sum_lt⟩
  · have hsum_lt : a₁ + a₂ < b₁ + b₂ := lt_of_le_of_ne hab_le hsum_eq
    let s : ℝ := (max (a₁ + a₂) s_lo + min (b₁ + b₂) s_hi) / 2
    have hs_lo_lt : max (a₁ + a₂) s_lo < min (b₁ + b₂) s_hi :=
      lt_min (max_lt hsum_lt hab_sum_gt) (max_lt hab_sum_lt hs)
    have hs1 : a₁ + a₂ < s := lt_of_le_of_lt (le_max_left (a₁ + a₂) s_lo) (by dsimp [s]; linarith only [hs_lo_lt])
    have hs2 : s < b₁ + b₂ := lt_of_lt_of_le (by dsimp [s]; linarith only [hs_lo_lt]) (min_le_left (b₁ + b₂) s_hi)
    have hs3 : s_lo < s := lt_of_le_of_lt (le_max_right (a₁ + a₂) s_lo) (by dsimp [s]; linarith only [hs_lo_lt])
    have hs4 : s < s_hi := lt_of_lt_of_le (by dsimp [s]; linarith only [hs_lo_lt]) (min_le_right (b₁ + b₂) s_hi)
    let t : ℝ := (s - (a₁ + a₂)) / ((b₁ + b₂) - (a₁ + a₂))
    have ht0 : 0 < t := div_pos (by linarith only [hs1]) (by linarith only [hsum_lt])
    have ht1 : t < 1 := (div_lt_one (by linarith only [hsum_lt])).mpr (by linarith only [hs2])
    let r₁ : ℝ := (1 - t) * a₁ + t * b₁
    let r₂ : ℝ := (1 - t) * a₂ + t * b₂
    have hsum_r : r₁ + r₂ = s := by
      dsimp only [r₁, r₂, t]
      have hne : (b₁ + b₂) - (a₁ + a₂) ≠ 0 := by linarith only [hsum_lt]
      field_simp [hne]; ring
    have hr1_ge : a₁ ≤ r₁ := by dsimp [r₁]; nlinarith only [ha1_props.2.1, ht0]
    have hr1_le : r₁ ≤ b₁ := by dsimp [r₁]; nlinarith only [ha1_props.2.1, ht1]
    have hr2_ge : a₂ ≤ r₂ := by dsimp [r₂]; nlinarith only [ha2_props.2.1, ht0]
    have hr2_le : r₂ ≤ b₂ := by dsimp [r₂]; nlinarith only [ha2_props.2.1, ht1]
    exact ⟨r₁, r₂, le_trans ha1_props.1 hr1_ge, le_trans hr1_le ha1_props.2.2.1,
      lt_of_lt_of_le ha1_props.2.2.2.1 hr1_ge, lt_of_le_of_lt hr1_le ha1_props.2.2.2.2.1,
      le_trans ha2_props.1 hr2_ge, le_trans hr2_le ha2_props.2.2.1,
      lt_of_lt_of_le ha2_props.2.2.2.1 hr2_ge, lt_of_le_of_lt hr2_le ha2_props.2.2.2.2.1,
      hsum_r ▸ hs3, hsum_r ▸ hs4⟩

/-- **Fourier–Motzkin Rate Splitting for the Marton Pentagon** (El Gamal–Kim Prop. 8.1 / Thm. 8.3):
    for non-negative single-letter quantities `a₁ = I(W; Y₁)`, `a₂ = I(W; Y₂)`,
    `b₁ = I(U; Y₁ | W)`, `b₂ = I(V; Y₂ | W)`, `c = I(U; V | W)` with `c < b₁ + b₂`,
    any rate pair `(R₁, R₂) ≥ 0` strictly inside the Marton pentagon splits as
    `R₁ = R₁₀ + R₁₁`, `R₂ = R₂₀ + R₂₂` with binning rates `R₁', R₂' ≥ 0` satisfying
    `c < R₁' + R₂'` and all four Marton packing inequalities (allowing `R₁₁ = R₁' = 0` when
    `b₁ = 0`, and `R₂₂ = R₂' = 0` when `b₂ = 0`). -/
theorem marton_rate_splitting {a₁ a₂ b₁ b₂ c R₁ R₂ : ℝ}
    (_ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hc : 0 ≤ c)
    (hbc : c < b₁ + b₂)
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (h1 : R₁ < a₁ + b₁)
    (h2 : R₂ < a₂ + b₂)
    (h3 : R₁ + R₂ < a₁ + b₁ + b₂ - c)
    (h4 : R₁ + R₂ < a₂ + b₁ + b₂ - c) :
    ∃ (R₁₀ R₁₁ R₂₀ R₂₂ R₁' R₂' : ℝ),
      0 ≤ R₁₀ ∧ 0 ≤ R₁₁ ∧ 0 ≤ R₂₀ ∧ 0 ≤ R₂₂ ∧ 0 ≤ R₁' ∧ 0 ≤ R₂' ∧
      R₁₀ + R₁₁ = R₁ ∧ R₂₀ + R₂₂ = R₂ ∧
      c < R₁' + R₂' ∧
      (R₁₁ = 0 ∨ R₁₁ + R₁' < b₁) ∧
      (R₂₂ = 0 ∨ R₂₂ + R₂' < b₂) ∧
      R₁₀ + R₂₀ + R₁₁ + R₁' < a₁ + b₁ ∧
      R₁₀ + R₂₀ + R₂₂ + R₂' < a₂ + b₂ := by
  rcases hb₁.eq_or_lt with rfl | hb₁_pos
  · have hlo_lt_hi : max (0 : ℝ) (R₁ + R₂ - a₁) < min R₂ (b₂ - c) ∨ R₂ = 0 := by
      rcases hR₂0.eq_or_lt with rfl | hR₂_pos
      · exact Or.inr rfl
      · left
        exact lt_min (max_lt hR₂_pos (by linarith)) (max_lt (by linarith) (by linarith))
    rcases hlo_lt_hi with hlt | rfl
    · let R₂₂ : ℝ := (max (0 : ℝ) (R₁ + R₂ - a₁) + min R₂ (b₂ - c)) / 2
      have hR₂₂_0 : 0 ≤ R₂₂ := le_trans (le_max_left (0 : ℝ) (R₁ + R₂ - a₁)) (by dsimp [R₂₂]; linarith only [hlt])
      have hR₂₂_le : R₂₂ ≤ R₂ := le_trans (by dsimp [R₂₂]; linarith only [hlt]) (min_le_left R₂ (b₂ - c))
      have hR₂₂_gt : R₁ + R₂ - a₁ < R₂₂ := lt_of_le_of_lt (le_max_right (0 : ℝ) (R₁ + R₂ - a₁)) (by dsimp [R₂₂]; linarith only [hlt])
      have hR₂₂_lt : R₂₂ < b₂ - c := lt_of_lt_of_le (by dsimp [R₂₂]; linarith only [hlt]) (min_le_right R₂ (b₂ - c))
      let U₂ : ℝ := min (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂)
      have hc_lt : c < U₂ := lt_min (by linarith) (by linarith)
      let R₂' : ℝ := (c + U₂) / 2
      refine ⟨R₁, 0, R₂ - R₂₂, R₂₂, 0, R₂', hR₁0, le_rfl, by linarith, hR₂₂_0, le_rfl,
        by dsimp [R₂']; linarith only [hc, hc_lt], by ring, by ring, by dsimp [R₂']; linarith only [hc_lt],
        Or.inl rfl, Or.inr (by dsimp [R₂']; linarith only [hc_lt, min_le_left (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂)]),
        by linarith, by dsimp [R₂']; linarith only [hc_lt, min_le_right (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂)]⟩
    · let U₂ : ℝ := min b₂ (a₂ + b₂ - R₁)
      have hc_lt : c < U₂ := lt_min (by linarith) (by linarith)
      let R₂' : ℝ := (c + U₂) / 2
      refine ⟨R₁, 0, 0, 0, 0, R₂', hR₁0, le_rfl, le_rfl, le_rfl, le_rfl,
        by dsimp [R₂']; linarith only [hc, hc_lt], by ring, by ring, by dsimp [R₂']; linarith only [hc_lt],
        Or.inl rfl, Or.inl rfl, by linarith,
        by dsimp [R₂']; linarith only [hc_lt, min_le_right b₂ (a₂ + b₂ - R₁)]⟩
  · rcases hb₂.eq_or_lt with rfl | hb₂_pos
    · have hlo_lt_hi : max (0 : ℝ) (R₁ + R₂ - a₂) < min R₁ (b₁ - c) ∨ R₁ = 0 := by
        rcases hR₁0.eq_or_lt with rfl | hR₁_pos
        · exact Or.inr rfl
        · left
          exact lt_min (max_lt hR₁_pos (by linarith)) (max_lt (by linarith) (by linarith))
      rcases hlo_lt_hi with hlt | rfl
      · let R₁₁ : ℝ := (max (0 : ℝ) (R₁ + R₂ - a₂) + min R₁ (b₁ - c)) / 2
        have hR₁₁_0 : 0 ≤ R₁₁ := le_trans (le_max_left (0 : ℝ) (R₁ + R₂ - a₂)) (by dsimp [R₁₁]; linarith only [hlt])
        have hR₁₁_le : R₁₁ ≤ R₁ := le_trans (by dsimp [R₁₁]; linarith only [hlt]) (min_le_left R₁ (b₁ - c))
        have hR₁₁_gt : R₁ + R₂ - a₂ < R₁₁ := lt_of_le_of_lt (le_max_right (0 : ℝ) (R₁ + R₂ - a₂)) (by dsimp [R₁₁]; linarith only [hlt])
        have hR₁₁_lt : R₁₁ < b₁ - c := lt_of_lt_of_le (by dsimp [R₁₁]; linarith only [hlt]) (min_le_right R₁ (b₁ - c))
        let U₁ : ℝ := min (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂)
        have hc_lt : c < U₁ := lt_min (by linarith) (by linarith)
        let R₁' : ℝ := (c + U₁) / 2
        refine ⟨R₁ - R₁₁, R₁₁, R₂, 0, R₁', 0, by linarith, hR₁₁_0, hR₂0, le_rfl,
          by dsimp [R₁']; linarith only [hc, hc_lt], le_rfl, by ring, by ring, by dsimp [R₁']; linarith only [hc_lt],
          Or.inr (by dsimp [R₁']; linarith only [hc_lt, min_le_left (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂)]),
          Or.inl rfl, by dsimp [R₁']; linarith only [hc_lt, min_le_right (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂)],
          by linarith⟩
      · let U₁ : ℝ := min b₁ (a₁ + b₁ - R₂)
        have hc_lt : c < U₁ := lt_min (by linarith) (by linarith)
        let R₁' : ℝ := (c + U₁) / 2
        refine ⟨0, 0, R₂, 0, R₁', 0, le_rfl, le_rfl, hR₂0, le_rfl,
          by dsimp [R₁']; linarith only [hc, hc_lt], le_rfl, by ring, by ring, by dsimp [R₁']; linarith only [hc_lt],
          Or.inl rfl, Or.inl rfl, by dsimp [R₁']; linarith only [hc_lt, min_le_right b₁ (a₁ + b₁ - R₂)],
          by linarith⟩
    · have hbox := mc_exists_box_sum
        (x₁ := 0) (y₁ := R₁) (l₁ := R₁ + R₂ - a₂ - b₂) (h₁ := b₁)
        (x₂ := 0) (y₂ := R₂) (l₂ := R₁ + R₂ - a₁ - b₁) (h₂ := b₂)
        (s_lo := 2 * (R₁ + R₂) + c - a₁ - a₂ - b₁ - b₂) (s_hi := b₁ + b₂ - c)
        hR₁0 (by linarith) hb₁_pos (by linarith)
        hR₂0 (by linarith) hb₂_pos (by linarith)
        (by linarith)
        (by
          rcases le_total (0 : ℝ) (R₁ + R₂ - a₂ - b₂) with hA | hA <;>
          rcases le_total (0 : ℝ) (R₁ + R₂ - a₁ - b₁) with hB | hB
          · rw [max_eq_right hA, max_eq_right hB]; linarith
          · rw [max_eq_right hA, max_eq_left hB]; linarith
          · rw [max_eq_left hA, max_eq_right hB]; linarith
          · rw [max_eq_left hA, max_eq_left hB]; linarith)
        (by
          rcases le_total R₁ b₁ with hA | hA <;>
          rcases le_total R₂ b₂ with hB | hB
          · rw [min_eq_left hA, min_eq_left hB]; linarith
          · rw [min_eq_left hA, min_eq_right hB]; linarith
          · rw [min_eq_right hA, min_eq_left hB]; linarith
          · rw [min_eq_right hA, min_eq_right hB]; linarith)
      obtain ⟨R₁₁, R₂₂, hR11_0, hR11_le, hR11_l, hR11_h, hR22_0, hR22_le, hR22_l, hR22_h, hs_lo, hs_hi⟩ := hbox
      let U₁ : ℝ := min (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂ + R₂₂)
      let U₂ : ℝ := min (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂ + R₁₁)
      have hU₁ : 0 < U₁ := lt_min (by linarith) (by linarith)
      have hU₂ : 0 < U₂ := lt_min (by linarith) (by linarith)
      have hUsum : c < U₁ + U₂ := by
        dsimp only [U₁, U₂]
        rcases le_total (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂ + R₂₂) with hA | hA <;>
        rcases le_total (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂ + R₁₁) with hB | hB
        · rw [min_eq_left hA, min_eq_left hB]; linarith
        · rw [min_eq_left hA, min_eq_right hB]; linarith
        · rw [min_eq_right hA, min_eq_left hB]; linarith
        · rw [min_eq_right hA, min_eq_right hB]; linarith
      let t : ℝ := (1 + max (0 : ℝ) (c / (U₁ + U₂))) / 2
      have hdiv_lt : c / (U₁ + U₂) < 1 := (div_lt_one (by linarith)).mpr hUsum
      have ht0 : 0 < t := by dsimp [t]; linarith only [le_max_left (0 : ℝ) (c / (U₁ + U₂))]
      have ht1 : t < 1 := by dsimp [t]; linarith only [max_lt zero_lt_one hdiv_lt]
      have htc : c / (U₁ + U₂) < t := by dsimp [t]; linarith only [le_max_right (0 : ℝ) (c / (U₁ + U₂)), max_lt zero_lt_one hdiv_lt]
      let R₁' : ℝ := t * U₁
      let R₂' : ℝ := t * U₂
      have hR1'_lt : R₁' < U₁ := by dsimp [R₁']; nlinarith only [hU₁, ht1]
      have hR2'_lt : R₂' < U₂ := by dsimp [R₂']; nlinarith only [hU₂, ht1]
      have hRsum : c < R₁' + R₂' := by
        dsimp only [R₁', R₂']
        have hmul := (div_lt_iff₀ (by linarith only [hU₁, hU₂] : 0 < U₁ + U₂)).mp htc
        nlinarith only [hmul]
      refine ⟨R₁ - R₁₁, R₁₁, R₂ - R₂₂, R₂₂, R₁', R₂', by linarith, hR11_0, by linarith, hR22_0,
        mul_nonneg ht0.le hU₁.le, mul_nonneg ht0.le hU₂.le, by ring, by ring, hRsum,
        Or.inr (by linarith only [hR1'_lt, min_le_left (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂ + R₂₂)]),
        Or.inr (by linarith only [hR2'_lt, min_le_left (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂ + R₁₁)]),
        by linarith only [hR1'_lt, min_le_right (b₁ - R₁₁) (a₁ + b₁ - R₁ - R₂ + R₂₂)],
        by linarith only [hR2'_lt, min_le_right (b₂ - R₂₂) (a₂ + b₂ - R₁ - R₂ + R₁₁)]⟩

end RateSplitting

/-! ### 4. Marton Random Coding Bound -/

section MartonRandomCoding

variable {W_aux U V X Y₁ Y₂ : Type*}
  [Fintype W_aux] [Fintype U] [Fintype V] [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- Joint distribution `((W, U, V, X), (Y₁, Y₂))` matching `InfoTheory.martonInnerBound`. -/
def martonJoint (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) :
    ProbDist ((W_aux × U × V × X) × (Y₁ × Y₂)) where
  pmf := fun z => Pwuvx.pmf z.1 * W.trans z.1.2.2.2 z.2
  nonneg := fun z => mul_nonneg (Pwuvx.nonneg z.1) (W.nonneg z.1.2.2.2 z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, W.sum_one, mul_one, Pwuvx.sum_one]

/-- Effective broadcast channel from `(W, U, V)` to `(Y₁, Y₂)` obtained by composing
    `P_{X | W, U, V}` with `W`. -/
private noncomputable def martonEffChannel (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) :
    BroadcastChannel (W_aux × U × V) Y₁ Y₂ :=
  let P_wuv_x : ProbDist ((W_aux × U × V) × X) :=
    Pwuvx.map (fun t => ((t.1, t.2.1, t.2.2.1), t.2.2.2))
  let K_X := condChannelOfJoint P_wuv_x
  { trans := fun z y => ∑ x : X, K_X.trans z x * W.trans x y
    nonneg := fun z y => Finset.sum_nonneg fun x _ => mul_nonneg (K_X.nonneg z x) (W.nonneg x y)
    sum_one := fun z => by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, W.sum_one, mul_one]
      exact K_X.sum_one z }

private lemma martonEffChannel_power_trans (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) (n : ℕ)
    (z : Fin n → W_aux × U × V) (y : Fin n → Y₁ × Y₂) :
    let P_wuv_x : ProbDist ((W_aux × U × V) × X) :=
      Pwuvx.map (fun t => ((t.1, t.2.1, t.2.2.1), t.2.2.2))
    let K_X := condChannelOfJoint P_wuv_x
    ((martonEffChannel W Pwuvx).power n).trans z y =
      ∑ x : Fin n → X, (K_X.power n).trans z x * (W.power n).trans x y := by
  dsimp only
  unfold DMC.power martonEffChannel; dsimp only
  rw [Fintype.prod_sum (fun i x =>
    (condChannelOfJoint (Pwuvx.map (fun t => ((t.1, t.2.1, t.2.2.1), t.2.2.2)))).trans (z i) x *
      W.trans x (y i))]
  refine Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib

private lemma martonEffChannel_joint_eq (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) :
    (martonEffChannel W Pwuvx).joint (Pwuvx.map (fun t => (t.1, t.2.1, t.2.2.1))) =
      (martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1, z.1.2.2.1), z.2)) := by
  classical
  let P_wuv := Pwuvx.map (fun t => (t.1, t.2.1, t.2.2.1))
  let e4 : (W_aux × U × V × X) ≃ ((W_aux × U × V) × X) :=
    { toFun := fun t => ((t.1, t.2.1, t.2.2.1), t.2.2.2)
      invFun := fun t => (t.1.1, t.1.2.1, t.1.2.2, t.2)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl }
  let P_wuv_x : ProbDist ((W_aux × U × V) × X) := Pwuvx.map e4
  have hfst : P_wuv_x.fst = P_wuv := by
    rw [← mc_probDist_map_fst]; unfold P_wuv_x P_wuv; rw [map_comp_eq]; rfl
  apply mc_probDist_ext; rintro ⟨⟨w, u, v⟩, y⟩
  change P_wuv.pmf (w, u, v) * (∑ x : X, (condChannelOfJoint P_wuv_x).trans (w, u, v) x * W.trans x y) =
    ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1, z.1.2.2.1), z.2))).pmf ((w, u, v), y)
  rw [Finset.mul_sum]
  have hlhs : ∑ x : X, P_wuv.pmf (w, u, v) *
        ((condChannelOfJoint P_wuv_x).trans (w, u, v) x * W.trans x y) =
      ∑ x : X, Pwuvx.pmf (w, u, v, x) * W.trans x y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_assoc]
    congr 1
    have hmul := condChannelOfJoint_mul P_wuv_x (w, u, v) x
    rw [hfst] at hmul
    rw [hmul]
    unfold P_wuv_x ProbDist.map; dsimp only
    rw [Finset.sum_eq_single (w, u, v, x)]
    · simp [e4]
    · intro t _ hne
      split_ifs with h
      · exact absurd (e4.injective h) hne
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hlhs]
  unfold ProbDist.map martonJoint; dsimp only
  rw [Fintype.sum_prod_type]
  have h1 : ∀ t : W_aux × U × V × X,
      (∑ y' : Y₁ × Y₂, if ((t.1, t.2.1, t.2.2.1), y') = ((w, u, v), y)
        then Pwuvx.pmf t * W.trans t.2.2.2 y' else 0) =
      if (t.1, t.2.1, t.2.2.1) = (w, u, v) then Pwuvx.pmf t * W.trans t.2.2.2 y else 0 := fun t => by
    rw [Finset.sum_eq_single y]
    · by_cases h : (t.1, t.2.1, t.2.2.1) = (w, u, v) <;> simp [h]
    · intro y' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [h1]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
      · simp
      · intro v' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro u' _ hne; rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro w' _ hne; rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun _ _ => by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma mc_bc_sum_ite_fst_power {A : Type*} [Fintype A]
    (W : BroadcastChannel A Y₁ Y₂) {n : ℕ} (a : Fin n → A)
    (p : (Fin n → Y₁) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂, (if p (fun i => (y i).1) then (W.power n).trans a y else 0) =
      ∑ y₁ : Fin n → Y₁, ((bcMarginal1 W).power n).trans a y₁ * (if p y₁ then (1 : ℝ) else 0) := by
  have hsplit : ∑ y : Fin n → Y₁ × Y₂, (if p (fun i => (y i).1) then (W.power n).trans a y else 0) =
      ∑ y₁ : Fin n → Y₁, ∑ y₂ : Fin n → Y₂,
        if p y₁ then (W.power n).trans a (fun i => (y₁ i, y₂ i)) else 0 := by
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (zipEquiv Y₁ Y₂ n) _ _ (fun _ => rfl)).symm
  rw [hsplit]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  have hmarg : ((bcMarginal1 W).power n).trans a y₁ =
      ∑ y₂ : Fin n → Y₂, (W.power n).trans a (fun i => (y₁ i, y₂ i)) := by
    simp only [DMC.power, bcMarginal1]
    exact Fintype.prod_sum (fun i y₂ => W.trans (a i) (y₁ i, y₂))
  rw [hmarg]
  split_ifs <;> simp

private lemma mc_bc_sum_ite_snd_power {A : Type*} [Fintype A]
    (W : BroadcastChannel A Y₁ Y₂) {n : ℕ} (a : Fin n → A)
    (p : (Fin n → Y₂) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂, (if p (fun i => (y i).2) then (W.power n).trans a y else 0) =
      ∑ y₂ : Fin n → Y₂, ((bcMarginal2 W).power n).trans a y₂ * (if p y₂ then (1 : ℝ) else 0) := by
  have hsplit : ∑ y : Fin n → Y₁ × Y₂, (if p (fun i => (y i).2) then (W.power n).trans a y else 0) =
      ∑ y₂ : Fin n → Y₂, ∑ y₁ : Fin n → Y₁,
        if p y₂ then (W.power n).trans a (fun i => (y₁ i, y₂ i)) else 0 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (zipEquiv Y₁ Y₂ n) _ _ (fun _ => rfl)).symm
  rw [hsplit]
  refine Finset.sum_congr rfl fun y₂ _ => ?_
  have hmarg : ((bcMarginal2 W).power n).trans a y₂ =
      ∑ y₁ : Fin n → Y₁, (W.power n).trans a (fun i => (y₁ i, y₂ i)) := by
    simp only [DMC.power, bcMarginal2]
    exact Fintype.prod_sum (fun i y₁ => W.trans (a i) (y₁, y₂ i))
  rw [hmarg]
  split_ifs <;> simp

/-- A single Marton cloud for one common message `m₀`: a center `w ∈ W^n`,
    `M₁₁` bins of `L₁` `U`-sequences, and `M₂₂` bins of `L₂` `V`-sequences. -/
private abbrev MartonCloud (W_aux U V : Type*) (n M₁₁ M₂₂ L₁ L₂ : ℕ) :=
  (Fin n → W_aux) × (Fin M₁₁ → Fin L₁ → Fin n → U) × (Fin M₂₂ → Fin L₂ → Fin n → V)

private local instance (priority := high) instFintypeMartonCloud
    {W_aux U V : Type*} [Fintype W_aux] [Fintype U] [Fintype V]
    {n M₁₁ M₂₂ L₁ L₂ : ℕ} :
    Fintype (MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) :=
  @instFintypeProd _ _ Pi.instFintype (@instFintypeProd _ _ Pi.instFintype Pi.instFintype)

/-- Distribution of a single random Marton cloud given `P : ProbDist (W_aux × U × V)`. -/
private noncomputable def martonCloudDist (P : ProbDist (W_aux × U × V))
    (n M₁₁ M₂₂ L₁ L₂ : ℕ) : ProbDist (MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) :=
  let P_W := P.map (fun t => t.1)
  let K_U := condChannelOfJoint (P.map (fun t => (t.1, t.2.1)))
  let K_V := condChannelOfJoint (P.map (fun t => (t.1, t.2.2)))
  { pmf := fun c =>
      (iidDist P_W n).pmf c.1 *
      (iidDist (iidDist (dmcRow (K_U.power n) c.1) L₁) M₁₁).pmf c.2.1 *
      (iidDist (iidDist (dmcRow (K_V.power n) c.1) L₂) M₂₂).pmf c.2.2
    nonneg := fun c => mul_nonneg (mul_nonneg ((iidDist P_W n).nonneg c.1)
      ((iidDist _ M₁₁).nonneg c.2.1)) ((iidDist _ M₂₂).nonneg c.2.2)
    sum_one := by
      rw [Fintype.sum_prod_type]
      have hinner : ∀ w : Fin n → W_aux,
          ∑ uv : (Fin M₁₁ → Fin L₁ → Fin n → U) × (Fin M₂₂ → Fin L₂ → Fin n → V),
            (iidDist P_W n).pmf w *
            (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf uv.1 *
            (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf uv.2 =
          (iidDist P_W n).pmf w := fun w => by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, (iidDist _ M₂₂).sum_one, mul_one,
          ← Finset.mul_sum, (iidDist _ M₁₁).sum_one, mul_one]
      simp_rw [hinner]
      exact (iidDist P_W n).sum_one }

/-- Three-way weak decoding typicality set for a triple `(w, a, y)` under `Q : ProbDist (W_aux × A × Y)`. -/
private noncomputable def martonDecSet {A Y : Type*} [Fintype A] [Fintype Y]
    (Q : ProbDist (W_aux × A × Y)) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → W_aux) × (Fin n → A) × (Fin n → Y)) := by
  classical
  let Q_W := Q.map (fun t => t.1)
  let Q_WA := Q.map (fun t => (t.1, t.2.1))
  let Q_Y := Q.map (fun t => t.2.2)
  let Q_WY := Q.map (fun t => (t.1, t.2.2))
  let Q_WAY := Q.map (fun t => ((t.1, t.2.1), t.2.2))
  exact Finset.univ.filter fun t =>
    t.1 ∈ weakTypicalSet Q_W n ε ∧
    (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Q_WA n ε ∧
    t.2.2 ∈ weakTypicalSet Q_Y n ε ∧
    (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet Q_WY n ε ∧
    (fun i => (t.1 i, t.2.1 i, t.2.2 i)) ∈ weakTypicalSet Q n ε ∧
    (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈ weakTypicalSet Q_WAY n ε

private lemma mem_martonDecSet {A Y : Type*} [Fintype A] [Fintype Y]
    (Q : ProbDist (W_aux × A × Y)) (n : ℕ) (ε : ℝ)
    (t : (Fin n → W_aux) × (Fin n → A) × (Fin n → Y)) :
    t ∈ martonDecSet Q n ε ↔
      t.1 ∈ weakTypicalSet (Q.map (fun z => z.1)) n ε ∧
      (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet (Q.map (fun z => (z.1, z.2.1))) n ε ∧
      t.2.2 ∈ weakTypicalSet (Q.map (fun z => z.2.2)) n ε ∧
      (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet (Q.map (fun z => (z.1, z.2.2))) n ε ∧
      (fun i => (t.1 i, t.2.1 i, t.2.2 i)) ∈ weakTypicalSet Q n ε ∧
      (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈ weakTypicalSet (Q.map (fun z => ((z.1, z.2.1), z.2.2))) n ε := by
  classical
  simp [martonDecSet]

private noncomputable def martonEncPair (P_wuv : ProbDist (W_aux × U × V))
    {n L₁ L₂ : ℕ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (ε₁ : ℝ)
    (w : Fin n → W_aux) (b₁ : Fin L₁ → Fin n → U) (b₂ : Fin L₂ → Fin n → V) :
    Fin L₁ × Fin L₂ := by
  classical
  exact if h : ∃ p : Fin L₁ × Fin L₂,
      (fun i => (w i, b₁ p.1 i, b₂ p.2 i)) ∈ strongTypicalSet P_wuv n ε₁
    then Classical.choose h else (⟨0, hL₁⟩, ⟨0, hL₂⟩)

private noncomputable def martonEncZ (P_wuv : ProbDist (W_aux × U × V))
    {n M₀ M₁₁ M₂₂ L₁ L₂ : ℕ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (ε₁ : ℝ)
    (C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂)
    (m₀ : Fin M₀) (m₁₁ : Fin M₁₁) (m₂₂ : Fin M₂₂) : Fin n → W_aux × U × V :=
  let c := C m₀
  let p := martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)
  fun i => (c.1 i, c.2.1 m₁₁ p.1 i, c.2.2 m₂₂ p.2 i)

private noncomputable def martonRawDec1 {Y : Type*} [Fintype Y]
    (Q : ProbDist (W_aux × U × Y)) {n M₀ M₁₁ M₂₂ L₁ L₂ : ℕ}
    (hM₀ : 0 < M₀) (hM₁₁ : 0 < M₁₁) (ε_d : ℝ)
    (C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) (y : Fin n → Y) :
    Fin M₀ × Fin M₁₁ := by
  classical
  let A := martonDecSet Q n ε_d
  exact if h : ∃! p : Fin M₀ × Fin M₁₁, ∃ l₁ : Fin L₁, ((C p.1).1, (C p.1).2.1 p.2 l₁, y) ∈ A
    then Classical.choose h else (⟨0, hM₀⟩, ⟨0, hM₁₁⟩)

open Classical in
/-- Single-receiver Marton error bound (Receiver 1, decoding `(m₀, m₁₁)` through any marginal
    DMC `W1 : DMC (W_aux × U × V) Y`). Receiver 2 is obtained by applying the exact same lemma
    with `U` and `V` swapped! -/
private lemma mc_marton_single_rx_error_bound {Y : Type*} [Fintype Y]
    (P_wuv : ProbDist (W_aux × U × V)) (W1 : DMC (W_aux × U × V) Y)
    {n M₀ M₁₁ M₂₂ L₁ L₂ : ℕ} (hn : 0 < n) (hM₀ : 0 < M₀) (hM₁₁ : 0 < M₁₁)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {ε₁ ε₂ ε_d : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁₂ : ε₁ < ε₂)
    (hε_d :
      let Q1 := (W1.joint P_wuv).map (fun z => (z.1.1, z.1.2.1, z.2))
      ε₂ * shannonEntropy (Q1.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q1 ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d)
    (m₀ : Fin M₀) (m₁₁ : Fin M₁₁) (m₂₂ : Fin M₂₂) :
    let J1 := W1.joint P_wuv
    let Q1 := J1.map (fun z => (z.1.1, z.1.2.1, z.2))
    let P_W := P_wuv.map (fun t => t.1)
    let K_U := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.1)))
    let K_V := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.2)))
    let Wcode := iidDist (martonCloudDist P_wuv n M₁₁ M₂₂ L₁ L₂) M₀
    let C1 := ∑ p : (W_aux × U × V) × Y, if 0 < J1.pmf p then 1 / J1.pmf p ^ 2 else 0
    let P_cov := ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
      (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0)))
    ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
      (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
        (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y ≠ (m₀, m₁₁) then (1 : ℝ) else 0)) ≤
      P_cov +
      C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) +
      (((M₁₁ - 1 : ℕ) * L₁ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) +
      (((M₀ - 1 : ℕ) * M₁₁ * L₁ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
  dsimp only
  let J1 := W1.joint P_wuv
  let Q1 := J1.map (fun z => (z.1.1, z.1.2.1, z.2))
  let P_W := P_wuv.map (fun t => t.1)
  let P_WU := P_wuv.map (fun t => (t.1, t.2.1))
  let P_WV := P_wuv.map (fun t => (t.1, t.2.2))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  let Qcloud := martonCloudDist P_wuv n M₁₁ M₂₂ L₁ L₂
  let Wcode := iidDist Qcloud M₀
  let A₁ := martonDecSet Q1 n ε_d
  let C1 := ∑ p : (W_aux × U × V) × Y, if 0 < J1.pmf p then 1 / J1.pmf p ^ 2 else 0
  let P_cov := ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
    (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
      (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
        (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
         then (1 : ℝ) else 0)))
  have hQ1_WU : Q1.map (fun t => (t.1, t.2.1)) = P_WU := by
    have h1 : Q1.map (fun t => (t.1, t.2.1)) = (J1.map Prod.fst).map (fun t => (t.1, t.2.1)) := by
      unfold Q1; rw [map_comp_eq, map_comp_eq]; rfl
    rw [h1, mc_probDist_map_fst, dmc_joint_fst]
  have hQ1_WAY_fst : (Q1.map (fun t => ((t.1, t.2.1), t.2.2))).fst = P_WU := by
    rw [← mc_probDist_map_fst, map_comp_eq]; exact hQ1_WU
  have hPWU_fst : P_WU.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_WU P_W; rw [map_comp_eq]; rfl
  let Eenc : (Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) → Prop := fun C =>
    ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
      (fun i => ((C m₀).1 i, (C m₀).2.1 m₁₁ l₁ i, (C m₀).2.2 m₂₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
  have hEenc_avg : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
      Wcode.pmf C * (if Eenc C then (1 : ℝ) else 0) = P_cov := by
    rw [iidDist_sum_coord Qcloud (fun c =>
      if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
        (fun i => (c.1 i, c.2.1 m₁₁ l₁ i, c.2.2 m₂₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
      then (1 : ℝ) else 0) m₀]
    unfold Qcloud martonCloudDist; dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    have hV : ∀ us : Fin M₁₁ → Fin L₁ → Fin n → U,
        (∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
          (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, us m₁₁ l₁ i, vs m₂₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
             then (1 : ℝ) else 0)) =
        ∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, us m₁₁ l₁ i, b₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0) := fun us =>
      iidDist_sum_coord (iidDist (dmcRow (K_V.power n) w) L₂)
        (fun b₂ : Fin L₂ → Fin n → V =>
          if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, us m₁₁ l₁ i, b₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
          then (1 : ℝ) else 0) m₂₂
    refine (Finset.sum_congr rfl fun us _ => congrArg _ (hV us)).trans ?_
    exact iidDist_sum_coord (iidDist (dmcRow (K_U.power n) w) L₁)
      (fun b₁ : Fin L₁ → Fin n → U =>
        ∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, b₁ l₁ i, b₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0)) m₁₁
  have hstrong_to_A1 : ∀ (z : Fin n → W_aux × U × V) (y : Fin n → Y),
      (fun i => (z i, y i)) ∈ strongTypicalSet J1 n ε₂ →
      (fun i => (z i).1, fun i => (z i).2.1, y) ∈ A₁ := by
    intro z y hst
    have hq : (fun i => ((z i).1, (z i).2.1, y i)) ∈ strongTypicalSet Q1 n ε₂ :=
      strongTypicalSet_map J1 (fun t => (t.1.1, t.1.2.1, t.2)) n ε₂ hst
    rw [mem_martonDecSet]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.1
        (strongTypicalSet_map Q1 (fun t => t.1) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.1
        (strongTypicalSet_map Q1 (fun t => (t.1, t.2.1)) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.1
        (strongTypicalSet_map Q1 (fun t => t.2.2) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.2.1
        (strongTypicalSet_map Q1 (fun t => (t.1, t.2.2)) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.2.2.1 hq
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.2.2.2
        (strongTypicalSet_map Q1 (fun t => ((t.1, t.2.1), t.2.2)) n ε₂ hq)
  -- Pointwise indicator decomposition.
  have hind : ∀ (C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) (y : Fin n → Y),
      (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y ≠ (m₀, m₁₁) then (1 : ℝ) else 0) ≤
      (if Eenc C then (1 : ℝ) else 0) +
      (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J1 n ε₂
       then (1 : ℝ) else 0) +
      (∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁,
        if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) +
      (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁,
        if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) := by
    intro C y
    have hnn1 : (0 : ℝ) ≤ ∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁,
        if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hnn2 : (0 : ℝ) ≤ ∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁,
        if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
        split_ifs <;> norm_num
    by_cases herr : martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y ≠ (m₀, m₁₁)
    · rw [ite_eq_left herr]
      by_cases hE : Eenc C
      · simp only [hE, ↓reduceIte, not_true_eq_false, false_and]; linarith
      · simp only [hE, ↓reduceIte, not_false_eq_true, true_and, zero_add]
        by_cases hst : (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∈ strongTypicalSet J1 n ε₂
        · simp only [hst, not_true_eq_false, ↓reduceIte, zero_add]
          have hA1_true : ∃ l₁ : Fin L₁, ((C m₀).1, (C m₀).2.1 m₁₁ l₁, y) ∈ A₁ :=
            ⟨(martonEncPair P_wuv hL₁ hL₂ ε₁ (C m₀).1 ((C m₀).2.1 m₁₁) ((C m₀).2.2 m₂₂)).1,
              hstrong_to_A1 (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y hst⟩
          have hex : ∃ p' : Fin M₀ × Fin M₁₁, p' ≠ (m₀, m₁₁) ∧
              ∃ l₁' : Fin L₁, ((C p'.1).1, (C p'.1).2.1 p'.2 l₁', y) ∈ A₁ := by
            by_contra hnone; push Not at hnone
            have huniq : ∃! p : Fin M₀ × Fin M₁₁,
                ∃ l₁ : Fin L₁, ((C p.1).1, (C p.1).2.1 p.2 l₁, y) ∈ A₁ :=
              ⟨(m₀, m₁₁), hA1_true, fun p ⟨l₁, hl₁⟩ => by
                by_contra hne; exact hnone p hne l₁ hl₁⟩
            have hdec : martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y = (m₀, m₁₁) := by
              unfold martonRawDec1; dsimp only
              rw [dite_eq_left_of_eq_true (eq_true huniq)]
              exact (Classical.choose_spec huniq).2 (m₀, m₁₁) hA1_true |>.symm
            exact herr hdec
          obtain ⟨⟨m₀', m₁₁'⟩, hne, l₁', hmem'⟩ := hex
          dsimp only at hmem'
          by_cases hm0 : m₀' = m₀
          · subst hm0
            have hm11 : m₁₁' ≠ m₁₁ := fun h => hne (by subst h; rfl)
            have hin : (1 : ℝ) ≤ ∑ l : Fin L₁,
                if ((C m₀').1, (C m₀').2.1 m₁₁' l, y) ∈ A₁ then (1 : ℝ) else 0 := by
              have h := Finset.single_le_sum
                (f := fun l : Fin L₁ => if ((C m₀').1, (C m₀').2.1 m₁₁' l, y) ∈ A₁ then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ l₁')
              simpa [hmem'] using h
            have hge1 : (1 : ℝ) ≤ ∑ k ∈ Finset.univ.erase m₁₁, ∑ l : Fin L₁,
                if ((C m₀').1, (C m₀').2.1 k l, y) ∈ A₁ then (1 : ℝ) else 0 :=
              le_trans hin (Finset.single_le_sum
                (f := fun k : Fin M₁₁ => ∑ l : Fin L₁,
                  if ((C m₀').1, (C m₀').2.1 k l, y) ∈ A₁ then (1 : ℝ) else 0)
                (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hm11, Finset.mem_univ m₁₁'⟩))
            linarith
          · have hin1 : (1 : ℝ) ≤ ∑ l : Fin L₁,
                if ((C m₀').1, (C m₀').2.1 m₁₁' l, y) ∈ A₁ then (1 : ℝ) else 0 := by
              have h := Finset.single_le_sum
                (f := fun l : Fin L₁ => if ((C m₀').1, (C m₀').2.1 m₁₁' l, y) ∈ A₁ then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ l₁')
              simpa [hmem'] using h
            have hin2 : (1 : ℝ) ≤ ∑ k₁ : Fin M₁₁, ∑ l : Fin L₁,
                if ((C m₀').1, (C m₀').2.1 k₁ l, y) ∈ A₁ then (1 : ℝ) else 0 :=
              le_trans hin1 (Finset.single_le_sum
                (f := fun k₁ : Fin M₁₁ => ∑ l : Fin L₁,
                  if ((C m₀').1, (C m₀').2.1 k₁ l, y) ∈ A₁ then (1 : ℝ) else 0)
                (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_univ m₁₁'))
            have hge2 : (1 : ℝ) ≤ ∑ k₀ ∈ Finset.univ.erase m₀, ∑ k₁ : Fin M₁₁, ∑ l : Fin L₁,
                if ((C k₀).1, (C k₀).2.1 k₁ l, y) ∈ A₁ then (1 : ℝ) else 0 :=
              le_trans hin2 (Finset.single_le_sum
                (f := fun k₀ : Fin M₀ => ∑ k₁ : Fin M₁₁, ∑ l : Fin L₁,
                  if ((C k₀).1, (C k₀).2.1 k₁ l, y) ∈ A₁ then (1 : ℝ) else 0)
                (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hm0, Finset.mem_univ m₀'⟩))
            linarith
        · simp only [hst, not_false_eq_true, ↓reduceIte]; linarith
    · rw [ite_eq_right herr]
      have h0a : (0 : ℝ) ≤ if Eenc C then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have h0b : (0 : ℝ) ≤ if ¬ Eenc C ∧
          (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J1 n ε₂
          then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      linarith
  -- Term 1 (Eenc): `= P_cov`.
  have hT1 : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0)) = P_cov := by
    have hinner : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0)) = if Eenc C then (1 : ℝ) else 0 := fun C => by
      rw [← Finset.sum_mul, (W1.power n).sum_one, one_mul]
    simp_rw [hinner]
    exact hEenc_avg
  -- Term 2 (Markov): `≤ C1 / (n (ε₂ - ε₁)²)`.
  have hT2 : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J1 n ε₂
           then (1 : ℝ) else 0)) ≤ C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
    have hperC : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J1 n ε₂
           then (1 : ℝ) else 0)) ≤ C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
      intro C
      by_cases hE : Eenc C
      · simp only [hE, not_true_eq_false, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
        have hC1_nn : 0 ≤ C1 := Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
        exact div_nonneg hC1_nn (by positivity)
      · simp only [hE, not_false_eq_true, true_and]
        have hex : ∃ p : Fin L₁ × Fin L₂,
            (fun i => ((C m₀).1 i, (C m₀).2.1 m₁₁ p.1 i, (C m₀).2.2 m₂₂ p.2 i)) ∈ strongTypicalSet P_wuv n ε₁ := by
          by_contra hnone; push Not at hnone
          exact hE fun l₁ l₂ => hnone (l₁, l₂)
        have hz_st : martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ ∈ strongTypicalSet P_wuv n ε₁ := by
          unfold martonEncZ martonEncPair; dsimp only
          simp only [hex, ↓reduceDIte]
          exact Classical.choose_spec hex
        have hmk := mc_channel_typical_prob_not_mem_le P_wuv W1 hn hε₁ hε₁₂ hz_st
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
          (le_trans hmk (le_of_eq (congrArg (· / _) (Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl))))
        congr 1; split_ifs <;> rfl
    calc _ ≤ ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
            Wcode.pmf C * (C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2)) :=
          Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hperC C) (Wcode.nonneg C)
      _ = C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by rw [← Finset.sum_mul, Wcode.sum_one, one_mul]
  -- Term 3 (same `m₀`, wrong `m₁₁' ≠ m₁₁`, any `l₁'`): conditional packing!
  have hT3 : ∀ m₁₁' ∈ Finset.univ.erase m₁₁, ∀ l₁' : Fin L₁,
      ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
    intro m₁₁' hm₁₁' l₁'
    have hne : m₁₁' ≠ m₁₁ := (Finset.mem_erase.mp hm₁₁').1
    dsimp only [Wcode, martonEncZ]
    rw [iidDist_sum_coord Qcloud (fun c =>
      ∑ y : Fin n → Y,
        (W1.power n).trans (fun i => (c.1 i,
          c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
          c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y *
        (if (c.1, c.2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) m₀]
    unfold Qcloud martonCloudDist; dsimp only
    rw [Fintype.sum_prod_type]
    have hper_w : ∀ w : Fin n → W_aux,
        (∑ uv : (Fin M₁₁ → Fin L₁ → Fin n → U) × (Fin M₂₂ → Fin L₂ → Fin n → V),
          (iidDist P_W n).pmf w *
          (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf uv.1 *
          (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf uv.2 *
          (∑ y : Fin n → Y,
            (W1.power n).trans (fun i => (w i,
              uv.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (uv.1 m₁₁) (uv.2 m₂₂)).1 i,
              uv.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (uv.1 m₁₁) (uv.2 m₂₂)).2 i)) y *
            (if (w, uv.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) ≤
        (iidDist P_W n).pmf w *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
      intro w
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      have hpull : ∀ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
          (∑ us : Fin M₁₁ → Fin L₁ → Fin n → U,
            (iidDist P_W n).pmf w *
            (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
            (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (∑ y : Fin n → Y,
              (W1.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
              (if (w, us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) ≤
          (iidDist P_W n).pmf w *
          (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
        intro vs
        have hrew : (∑ us : Fin M₁₁ → Fin L₁ → Fin n → U,
            (iidDist P_W n).pmf w *
            (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
            (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (∑ y : Fin n → Y,
              (W1.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
              (if (w, us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) =
          ((iidDist P_W n).pmf w * (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs) *
          (∑ y : Fin n → Y,
            ∑ us : Fin M₁₁ → Fin L₁ → Fin n → U,
              (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
              ((W1.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
               (if (w, us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          refine Finset.sum_congr rfl fun us _ => by ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ((iidDist P_W n).nonneg w) ((iidDist _ M₂₂).nonneg vs))
        have hper_y : ∀ y : Fin n → Y,
            (∑ us : Fin M₁₁ → Fin L₁ → Fin n → U,
              (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
              ((W1.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
               (if (w, us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) ≤
            (∑ b₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf b₁ *
              (W1.power n).trans (fun i => (w i,
                b₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).2 i)) y) *
            (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
          intro y
          rw [iidDist_sum_two_coords (iidDist (dmcRow (K_U.power n) w) L₁)
            (fun b₁ => (W1.power n).trans (fun i => (w i,
              b₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).1 i,
              vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).2 i)) y)
            (fun b₁' => if (w, b₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) hne.symm]
          refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun b₁ _ =>
            mul_nonneg ((iidDist _ L₁).nonneg b₁) ((W1.power n).nonneg _ y))
          rw [iidDist_sum_coord (dmcRow (K_U.power n) w)
            (fun u' => if (w, u', y) ∈ A₁ then (1 : ℝ) else 0) l₁']
          have hpack := mc_pointwise_cond_packing Q1 n ε_d w y
          dsimp only at hpack
          rw [hQ1_WU] at hpack
          refine le_trans (Finset.sum_le_sum fun u' _ => ?_) hpack
          by_cases hm : (w, u', y) ∈ A₁
          · have hmd := (mem_martonDecSet Q1 n ε_d (w, u', y)).mp hm
            have hcond : w ∈ weakTypicalSet (Q1.map (fun t => t.1)) n ε_d ∧
                (fun i => (w i, u' i)) ∈ weakTypicalSet P_WU n ε_d ∧
                (fun i => (w i, y i)) ∈ weakTypicalSet (Q1.map (fun t => (t.1, t.2.2))) n ε_d ∧
                (fun i => (w i, u' i, y i)) ∈ weakTypicalSet Q1 n ε_d :=
              ⟨hmd.1, hQ1_WU ▸ hmd.2.1, hmd.2.2.2.1, hmd.2.2.2.2.1⟩
            simp only [hm, hcond, ↓reduceIte, mul_one]; exact le_rfl
          · simp only [hm, ↓reduceIte, mul_zero]
            split_ifs
            · exact (K_U.power n).nonneg w u'
            · exact le_rfl
        calc ∑ y : Fin n → Y, _
          _ ≤ ∑ y : Fin n → Y,
                (∑ b₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf b₁ *
                  (W1.power n).trans (fun i => (w i,
                    b₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).1 i,
                    vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).2 i)) y) *
                (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
              Finset.sum_le_sum fun y _ => hper_y y
          _ = (∑ b₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf b₁ *
                (∑ y : Fin n → Y, (W1.power n).trans (fun i => (w i,
                  b₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).1 i,
                  vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w b₁ (vs m₂₂)).2 i)) y)) *
                (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
              rw [← Finset.sum_mul]; congr 1
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun b₁ _ => (Finset.mul_sum _ _ _).symm
          _ = _ := by simp_rw [(W1.power n).sum_one, mul_one, (iidDist _ L₁).sum_one, one_mul]
      calc _ ≤ ∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
            (iidDist P_W n).pmf w * (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
          Finset.sum_le_sum fun vs _ => hpull vs
        _ = (iidDist P_W n).pmf w *
            (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, (iidDist _ M₂₂).sum_one, mul_one]
    calc _ ≤ ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
        Finset.sum_le_sum fun w _ => hper_w w
      _ = _ := by rw [← Finset.sum_mul, (iidDist P_W n).sum_one, one_mul]
  -- Term 4 (wrong `m₀' ≠ m₀`, any `m₁₁', l₁'`): unconditional packing!
  have hT4 : ∀ m₀' ∈ Finset.univ.erase m₀, ∀ (m₁₁' : Fin M₁₁) (l₁' : Fin L₁),
      ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
    intro m₀' hm₀' m₁₁' l₁'
    have hne : m₀' ≠ m₀ := (Finset.mem_erase.mp hm₀').1
    have hswap : (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) =
        ∑ y : Fin n → Y, ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          ((W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
           (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) := by
      simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    rw [hswap]
    have hper_y : ∀ y : Fin n → Y,
        (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          ((W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
           (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) ≤
        (∑ c : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c *
          (W1.power n).trans (fun i => (c.1 i,
            c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
            c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y) *
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
      intro y
      dsimp only [Wcode, martonEncZ]
      rw [iidDist_sum_two_coords Qcloud
        (fun c => (W1.power n).trans (fun i => (c.1 i,
          c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
          c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y)
        (fun c' => if (c'.1, c'.2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) hne.symm]
      refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun c _ =>
        mul_nonneg (Qcloud.nonneg c) ((W1.power n).nonneg _ y))
      have hWU_sum : (∑ c' : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c' *
            (if (c'.1, c'.2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) =
          ∑ wu : Fin n → W_aux × U, (iidDist P_WU n).pmf wu *
            (if (fun i => (wu i).1, fun i => (wu i).2, y) ∈ A₁ then (1 : ℝ) else 0) := by
        unfold Qcloud martonCloudDist; dsimp only
        rw [Fintype.sum_prod_type]
        have h1 : ∀ w' : Fin n → W_aux,
            (∑ uv : (Fin M₁₁ → Fin L₁ → Fin n → U) × (Fin M₂₂ → Fin L₂ → Fin n → V),
              (iidDist P_W n).pmf w' *
              (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf uv.1 *
              (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf uv.2 *
              (if (w', uv.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) =
            ∑ u' : Fin n → U, (iidDist P_WU n).pmf (fun i => (w' i, u' i)) *
              (if (w', u', y) ∈ A₁ then (1 : ℝ) else 0) := fun w' => by
          rw [Fintype.sum_prod_type]
          have hV : ∀ us : Fin M₁₁ → Fin L₁ → Fin n → U,
              (∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
                (iidDist P_W n).pmf w' *
                (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                (if (w', us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) =
              (iidDist P_W n).pmf w' *
              ((iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                (if (w', us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0)) := fun us => by
            have hfac : ∀ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
                (iidDist P_W n).pmf w' *
                (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                (if (w', us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) =
                (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                ((iidDist P_W n).pmf w' *
                 ((iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                  (if (w', us m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) := fun _ => by ring
            simp_rw [hfac, ← Finset.sum_mul, (iidDist _ M₂₂).sum_one, one_mul]
          simp_rw [hV, ← Finset.mul_sum]
          rw [iidDist_sum_coord (iidDist (dmcRow (K_U.power n) w') L₁)
            (fun b₁' => if (w', b₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) m₁₁']
          rw [iidDist_sum_coord (dmcRow (K_U.power n) w')
            (fun u' => if (w', u', y) ∈ A₁ then (1 : ℝ) else 0) l₁']
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u' _ => ?_
          rw [← mul_assoc]
          congr 1
          have hzip := (jointIidDist_eq_fst_mul_condChannelPower P_WU n w' u').symm
          rw [hPWU_fst] at hzip
          exact hzip
        refine (Finset.sum_congr rfl fun w' _ => h1 w').trans ?_
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (zipEquiv W_aux U n) _ _ (fun _ => rfl)
      rw [hWU_sum]
      have hpack := mc_pointwise_uncond_packing (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) n ε_d y
      rw [hQ1_WAY_fst] at hpack
      refine le_trans (Finset.sum_le_sum fun wu _ => ?_) hpack
      by_cases hm : (fun i => (wu i).1, fun i => (wu i).2, y) ∈ A₁
      · have hmd := (mem_martonDecSet Q1 n ε_d (fun i => (wu i).1, fun i => (wu i).2, y)).mp hm
        have hsnd : (Q1.map (fun t => ((t.1, t.2.1), t.2.2))).snd = Q1.map (fun t => t.2.2) := by
          rw [← mc_probDist_map_snd, map_comp_eq]; rfl
        have hcond : wu ∈ weakTypicalSet P_WU n ε_d ∧
            y ∈ weakTypicalSet (Q1.map (fun t => ((t.1, t.2.1), t.2.2))).snd n ε_d ∧
            (fun i => (wu i, y i)) ∈ weakTypicalSet (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) n ε_d :=
          ⟨hQ1_WU ▸ hmd.2.1, hsnd ▸ hmd.2.2.1, hmd.2.2.2.2.2⟩
        simp only [hm, hcond, ↓reduceIte, mul_one]; exact le_rfl
      · simp only [hm, ↓reduceIte, mul_zero]
        split_ifs
        · exact (iidDist P_WU n).nonneg wu
        · exact le_rfl
    calc ∑ y : Fin n → Y, _
      _ ≤ ∑ y : Fin n → Y,
            (∑ c : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c *
              (W1.power n).trans (fun i => (c.1 i,
                c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
                c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y) *
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) :=
          Finset.sum_le_sum fun y _ => hper_y y
      _ = (∑ c : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c *
            (∑ y : Fin n → Y,
              (W1.power n).trans (fun i => (c.1 i,
                c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
                c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y)) *
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
          rw [← Finset.sum_mul]; congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
      _ = _ := by simp_rw [(W1.power n).sum_one, mul_one, Qcloud.sum_one, one_mul]
  -- Assemble all four terms.
  have hsum : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y ≠ (m₀, m₁₁) then (1 : ℝ) else 0)) ≤
      (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0))) +
      (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J1 n ε₂
           then (1 : ℝ) else 0))) +
      (∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) +
      (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) := by
    have hptC : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        Wcode.pmf C * (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y ≠ (m₀, m₁₁) then (1 : ℝ) else 0)) ≤
        Wcode.pmf C * (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0)) +
        Wcode.pmf C * (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J1 n ε₂
           then (1 : ℝ) else 0)) +
        (∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁,
          Wcode.pmf C * (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) +
        (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁,
          Wcode.pmf C * (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) := by
      intro C
      have hy := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (hind C y) ((W1.power n).nonneg (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y)
      have hmul := mul_le_mul_of_nonneg_left hy (Wcode.nonneg C)
      refine le_trans hmul (le_of_eq ?_)
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [mul_add, mul_add, mul_add]
      congr 1
      · congr 1
        · have hswapA : (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
                ∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁,
                  if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) =
              ∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁, ∑ y : Fin n → Y,
                (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
                  (if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          rw [hswapA, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
      · have hswapB : (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
              ∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁,
                if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) =
            ∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁, ∑ y : Fin n → Y,
              (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
                (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0) := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        rw [hswapB, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
    refine le_trans (Finset.sum_le_sum fun C _ => hptC C) (le_of_eq ?_)
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hT3_tot : (∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ l₁' : Fin L₁,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀).1, (C m₀).2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) ≤
      (((M₁₁ - 1 : ℕ) * L₁ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
    calc _ ≤ ∑ m₁₁' ∈ Finset.univ.erase m₁₁, ∑ _l₁' : Fin L₁,
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q1.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
        Finset.sum_le_sum fun m₁₁' hm => Finset.sum_le_sum fun l₁' _ => hT3 m₁₁' hm l₁'
      _ = _ := by
        simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m₁₁), nsmul_eq_mul, mul_assoc]
  have hT4_tot : (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₁₁' : Fin M₁₁, ∑ l₁' : Fin L₁,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.1 m₁₁' l₁', y) ∈ A₁ then (1 : ℝ) else 0))) ≤
      (((M₀ - 1 : ℕ) * M₁₁ * L₁ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
    calc _ ≤ ∑ m₀' ∈ Finset.univ.erase m₀, ∑ _m₁₁' : Fin M₁₁, ∑ _l₁' : Fin L₁,
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) :=
        Finset.sum_le_sum fun m₀' hm => Finset.sum_le_sum fun m₁₁' _ => Finset.sum_le_sum fun l₁' _ =>
          hT4 m₀' hm m₁₁' l₁'
      _ = _ := by
        simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m₀), nsmul_eq_mul, mul_assoc]
  linarith

private noncomputable def martonRawDec2 {Y : Type*} [Fintype Y]
    (Q : ProbDist (W_aux × V × Y)) {n M₀ M₁₁ M₂₂ L₁ L₂ : ℕ}
    (hM₀ : 0 < M₀) (hM₂₂ : 0 < M₂₂) (ε_d : ℝ)
    (C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) (y : Fin n → Y) :
    Fin M₀ × Fin M₂₂ := by
  classical
  let A := martonDecSet Q n ε_d
  exact if h : ∃! p : Fin M₀ × Fin M₂₂, ∃ l₂ : Fin L₂, ((C p.1).1, (C p.1).2.2 p.2 l₂, y) ∈ A
    then Classical.choose h else (⟨0, hM₀⟩, ⟨0, hM₂₂⟩)

open Classical in
/-- Receiver 2's Marton error bound, deduced cleanly from `mc_marton_single_rx_error_bound`
    by swapping `U` and `V`! -/
private lemma mc_marton_rx2_error_bound {Y : Type*} [Fintype Y]
    (P_wuv : ProbDist (W_aux × U × V)) (W2 : DMC (W_aux × U × V) Y)
    {n M₀ M₁₁ M₂₂ L₁ L₂ : ℕ} (hn : 0 < n) (hM₀ : 0 < M₀) (hM₂₂ : 0 < M₂₂)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {ε₁ ε₂ ε_d : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁₂ : ε₁ < ε₂)
    (hε_d :
      let Q2 := (W2.joint P_wuv).map (fun z => (z.1.1, z.1.2.2, z.2))
      ε₂ * shannonEntropy (Q2.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q2 ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d)
    (m₀ : Fin M₀) (m₁₁ : Fin M₁₁) (m₂₂ : Fin M₂₂) :
    let J2 := W2.joint P_wuv
    let Q2 := J2.map (fun z => (z.1.1, z.1.2.2, z.2))
    let P_W := P_wuv.map (fun t => t.1)
    let K_U := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.1)))
    let K_V := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.2)))
    let Wcode := iidDist (martonCloudDist P_wuv n M₁₁ M₂₂ L₁ L₂) M₀
    let C2 := ∑ p : (W_aux × U × V) × Y, if 0 < J2.pmf p then 1 / J2.pmf p ^ 2 else 0
    let P_cov := ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
      (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0)))
    ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
      (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
        (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y ≠ (m₀, m₂₂) then (1 : ℝ) else 0)) ≤
      P_cov +
      C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) +
      (((M₂₂ - 1 : ℕ) * L₂ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) +
      (((M₀ - 1 : ℕ) * M₂₂ * L₂ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
  dsimp only
  -- Note: `martonEncPair` uses `Classical.choose`, so we cannot equate the chosen pair under swap;
  -- instead, mirror `mc_marton_single_rx_error_bound` directly with `c.2.2` and `m₂₂`!
  let J2 := W2.joint P_wuv
  let Q2 := J2.map (fun z => (z.1.1, z.1.2.2, z.2))
  let P_W := P_wuv.map (fun t => t.1)
  let P_WU := P_wuv.map (fun t => (t.1, t.2.1))
  let P_WV := P_wuv.map (fun t => (t.1, t.2.2))
  let K_U := condChannelOfJoint P_WU
  let K_V := condChannelOfJoint P_WV
  let Qcloud := martonCloudDist P_wuv n M₁₁ M₂₂ L₁ L₂
  let Wcode := iidDist Qcloud M₀
  let A₂ := martonDecSet Q2 n ε_d
  let C2 := ∑ p : (W_aux × U × V) × Y, if 0 < J2.pmf p then 1 / J2.pmf p ^ 2 else 0
  let P_cov := ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
    (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
      (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
        (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
         then (1 : ℝ) else 0)))
  have hQ2_WV : Q2.map (fun t => (t.1, t.2.1)) = P_WV := by
    have h1 : Q2.map (fun t => (t.1, t.2.1)) = (J2.map Prod.fst).map (fun t => (t.1, t.2.2)) := by
      unfold Q2; rw [map_comp_eq, map_comp_eq]; rfl
    rw [h1, mc_probDist_map_fst, dmc_joint_fst]
  have hQ2_WAY_fst : (Q2.map (fun t => ((t.1, t.2.1), t.2.2))).fst = P_WV := by
    rw [← mc_probDist_map_fst, map_comp_eq]; exact hQ2_WV
  have hPWV_fst : P_WV.fst = P_W := by
    rw [← mc_probDist_map_fst]; unfold P_WV P_W; rw [map_comp_eq]; rfl
  let Eenc : (Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) → Prop := fun C =>
    ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
      (fun i => ((C m₀).1 i, (C m₀).2.1 m₁₁ l₁ i, (C m₀).2.2 m₂₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
  have hEenc_avg : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
      Wcode.pmf C * (if Eenc C then (1 : ℝ) else 0) = P_cov := by
    rw [iidDist_sum_coord Qcloud (fun c =>
      if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
        (fun i => (c.1 i, c.2.1 m₁₁ l₁ i, c.2.2 m₂₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
      then (1 : ℝ) else 0) m₀]
    unfold Qcloud martonCloudDist; dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    have hV : ∀ us : Fin M₁₁ → Fin L₁ → Fin n → U,
        (∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
          (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, us m₁₁ l₁ i, vs m₂₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
             then (1 : ℝ) else 0)) =
        ∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, us m₁₁ l₁ i, b₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0) := fun us =>
      iidDist_sum_coord (iidDist (dmcRow (K_V.power n) w) L₂)
        (fun b₂ : Fin L₂ → Fin n → V =>
          if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, us m₁₁ l₁ i, b₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
          then (1 : ℝ) else 0) m₂₂
    refine (Finset.sum_congr rfl fun us _ => congrArg _ (hV us)).trans ?_
    exact iidDist_sum_coord (iidDist (dmcRow (K_U.power n) w) L₁)
      (fun b₁ : Fin L₁ → Fin n → U =>
        ∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, b₁ l₁ i, b₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0)) m₁₁
  have hstrong_to_A2 : ∀ (z : Fin n → W_aux × U × V) (y : Fin n → Y),
      (fun i => (z i, y i)) ∈ strongTypicalSet J2 n ε₂ →
      (fun i => (z i).1, fun i => (z i).2.2, y) ∈ A₂ := by
    intro z y hst
    have hq : (fun i => ((z i).1, (z i).2.2, y i)) ∈ strongTypicalSet Q2 n ε₂ :=
      strongTypicalSet_map J2 (fun t => (t.1.1, t.1.2.2, t.2)) n ε₂ hst
    rw [mem_martonDecSet]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.1
        (strongTypicalSet_map Q2 (fun t => t.1) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.1
        (strongTypicalSet_map Q2 (fun t => (t.1, t.2.1)) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.1
        (strongTypicalSet_map Q2 (fun t => t.2.2) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.2.1
        (strongTypicalSet_map Q2 (fun t => (t.1, t.2.2)) n ε₂ hq)
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.2.2.1 hq
    · exact strongTypicalSet_subset_weakTypicalSet _ hn (le_trans hε₁ hε₁₂.le) hε_d.2.2.2.2.2
        (strongTypicalSet_map Q2 (fun t => ((t.1, t.2.1), t.2.2)) n ε₂ hq)
  have hind : ∀ (C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) (y : Fin n → Y),
      (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y ≠ (m₀, m₂₂) then (1 : ℝ) else 0) ≤
      (if Eenc C then (1 : ℝ) else 0) +
      (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J2 n ε₂
       then (1 : ℝ) else 0) +
      (∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂,
        if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) +
      (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂,
        if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) := by
    intro C y
    have hnn1 : (0 : ℝ) ≤ ∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂,
        if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hnn2 : (0 : ℝ) ≤ ∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂,
        if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
        split_ifs <;> norm_num
    by_cases herr : martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y ≠ (m₀, m₂₂)
    · rw [ite_eq_left herr]
      by_cases hE : Eenc C
      · simp only [hE, ↓reduceIte, not_true_eq_false, false_and]; linarith
      · simp only [hE, ↓reduceIte, not_false_eq_true, true_and, zero_add]
        by_cases hst : (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∈ strongTypicalSet J2 n ε₂
        · simp only [hst, not_true_eq_false, ↓reduceIte, zero_add]
          have hA2_true : ∃ l₂ : Fin L₂, ((C m₀).1, (C m₀).2.2 m₂₂ l₂, y) ∈ A₂ :=
            ⟨(martonEncPair P_wuv hL₁ hL₂ ε₁ (C m₀).1 ((C m₀).2.1 m₁₁) ((C m₀).2.2 m₂₂)).2,
              hstrong_to_A2 (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y hst⟩
          have hex : ∃ p' : Fin M₀ × Fin M₂₂, p' ≠ (m₀, m₂₂) ∧
              ∃ l₂' : Fin L₂, ((C p'.1).1, (C p'.1).2.2 p'.2 l₂', y) ∈ A₂ := by
            by_contra hnone; push Not at hnone
            have huniq : ∃! p : Fin M₀ × Fin M₂₂,
                ∃ l₂ : Fin L₂, ((C p.1).1, (C p.1).2.2 p.2 l₂, y) ∈ A₂ :=
              ⟨(m₀, m₂₂), hA2_true, fun p ⟨l₂, hl₂⟩ => by
                by_contra hne; exact hnone p hne l₂ hl₂⟩
            have hdec : martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y = (m₀, m₂₂) := by
              unfold martonRawDec2; dsimp only
              rw [dite_eq_left_of_eq_true (eq_true huniq)]
              exact (Classical.choose_spec huniq).2 (m₀, m₂₂) hA2_true |>.symm
            exact herr hdec
          obtain ⟨⟨m₀', m₂₂'⟩, hne, l₂', hmem'⟩ := hex
          dsimp only at hmem'
          by_cases hm0 : m₀' = m₀
          · subst hm0
            have hm22 : m₂₂' ≠ m₂₂ := fun h => hne (by subst h; rfl)
            have hin : (1 : ℝ) ≤ ∑ l : Fin L₂,
                if ((C m₀').1, (C m₀').2.2 m₂₂' l, y) ∈ A₂ then (1 : ℝ) else 0 := by
              have h := Finset.single_le_sum
                (f := fun l : Fin L₂ => if ((C m₀').1, (C m₀').2.2 m₂₂' l, y) ∈ A₂ then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ l₂')
              simpa [hmem'] using h
            have hge1 : (1 : ℝ) ≤ ∑ k ∈ Finset.univ.erase m₂₂, ∑ l : Fin L₂,
                if ((C m₀').1, (C m₀').2.2 k l, y) ∈ A₂ then (1 : ℝ) else 0 :=
              le_trans hin (Finset.single_le_sum
                (f := fun k : Fin M₂₂ => ∑ l : Fin L₂,
                  if ((C m₀').1, (C m₀').2.2 k l, y) ∈ A₂ then (1 : ℝ) else 0)
                (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hm22, Finset.mem_univ m₂₂'⟩))
            linarith
          · have hin1 : (1 : ℝ) ≤ ∑ l : Fin L₂,
                if ((C m₀').1, (C m₀').2.2 m₂₂' l, y) ∈ A₂ then (1 : ℝ) else 0 := by
              have h := Finset.single_le_sum
                (f := fun l : Fin L₂ => if ((C m₀').1, (C m₀').2.2 m₂₂' l, y) ∈ A₂ then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ l₂')
              simpa [hmem'] using h
            have hin2 : (1 : ℝ) ≤ ∑ k₂ : Fin M₂₂, ∑ l : Fin L₂,
                if ((C m₀').1, (C m₀').2.2 k₂ l, y) ∈ A₂ then (1 : ℝ) else 0 :=
              le_trans hin1 (Finset.single_le_sum
                (f := fun k₂ : Fin M₂₂ => ∑ l : Fin L₂,
                  if ((C m₀').1, (C m₀').2.2 k₂ l, y) ∈ A₂ then (1 : ℝ) else 0)
                (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_univ m₂₂'))
            have hge2 : (1 : ℝ) ≤ ∑ k₀ ∈ Finset.univ.erase m₀, ∑ k₂ : Fin M₂₂, ∑ l : Fin L₂,
                if ((C k₀).1, (C k₀).2.2 k₂ l, y) ∈ A₂ then (1 : ℝ) else 0 :=
              le_trans hin2 (Finset.single_le_sum
                (f := fun k₀ : Fin M₀ => ∑ k₂ : Fin M₂₂, ∑ l : Fin L₂,
                  if ((C k₀).1, (C k₀).2.2 k₂ l, y) ∈ A₂ then (1 : ℝ) else 0)
                (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hm0, Finset.mem_univ m₀'⟩))
            linarith
        · simp only [hst, not_false_eq_true, ↓reduceIte]; linarith
    · rw [ite_eq_right herr]
      have h0a : (0 : ℝ) ≤ if Eenc C then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      have h0b : (0 : ℝ) ≤ if ¬ Eenc C ∧
          (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J2 n ε₂
          then (1 : ℝ) else 0 := by split_ifs <;> norm_num
      linarith
  have hT1 : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0)) = P_cov := by
    have hinner : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0)) = if Eenc C then (1 : ℝ) else 0 := fun C => by
      rw [← Finset.sum_mul, (W2.power n).sum_one, one_mul]
    simp_rw [hinner]
    exact hEenc_avg
  have hT2 : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J2 n ε₂
           then (1 : ℝ) else 0)) ≤ C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
    have hperC : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J2 n ε₂
           then (1 : ℝ) else 0)) ≤ C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
      intro C
      by_cases hE : Eenc C
      · simp only [hE, not_true_eq_false, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
        have hC2_nn : 0 ≤ C2 := Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
        exact div_nonneg hC2_nn (by positivity)
      · simp only [hE, not_false_eq_true, true_and]
        have hex : ∃ p : Fin L₁ × Fin L₂,
            (fun i => ((C m₀).1 i, (C m₀).2.1 m₁₁ p.1 i, (C m₀).2.2 m₂₂ p.2 i)) ∈ strongTypicalSet P_wuv n ε₁ := by
          by_contra hnone; push Not at hnone
          exact hE fun l₁ l₂ => hnone (l₁, l₂)
        have hz_st : martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ ∈ strongTypicalSet P_wuv n ε₁ := by
          unfold martonEncZ martonEncPair; dsimp only
          simp only [hex, ↓reduceDIte]
          exact Classical.choose_spec hex
        have hmk := mc_channel_typical_prob_not_mem_le P_wuv W2 hn hε₁ hε₁₂ hz_st
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
          (le_trans hmk (le_of_eq (congrArg (· / _) (Finset.sum_congr rfl fun p _ => by split_ifs <;> rfl))))
        congr 1; split_ifs <;> rfl
    calc _ ≤ ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
            Wcode.pmf C * (C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2)) :=
          Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hperC C) (Wcode.nonneg C)
      _ = C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by rw [← Finset.sum_mul, Wcode.sum_one, one_mul]
  have hT3 : ∀ m₂₂' ∈ Finset.univ.erase m₂₂, ∀ l₂' : Fin L₂,
      ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
    intro m₂₂' hm₂₂' l₂'
    have hne : m₂₂' ≠ m₂₂ := (Finset.mem_erase.mp hm₂₂').1
    dsimp only [Wcode, martonEncZ]
    rw [iidDist_sum_coord Qcloud (fun c =>
      ∑ y : Fin n → Y,
        (W2.power n).trans (fun i => (c.1 i,
          c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
          c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y *
        (if (c.1, c.2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) m₀]
    unfold Qcloud martonCloudDist; dsimp only
    rw [Fintype.sum_prod_type]
    have hper_w : ∀ w : Fin n → W_aux,
        (∑ uv : (Fin M₁₁ → Fin L₁ → Fin n → U) × (Fin M₂₂ → Fin L₂ → Fin n → V),
          (iidDist P_W n).pmf w *
          (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf uv.1 *
          (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf uv.2 *
          (∑ y : Fin n → Y,
            (W2.power n).trans (fun i => (w i,
              uv.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (uv.1 m₁₁) (uv.2 m₂₂)).1 i,
              uv.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (uv.1 m₁₁) (uv.2 m₂₂)).2 i)) y *
            (if (w, uv.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) ≤
        (iidDist P_W n).pmf w *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
      intro w
      rw [Fintype.sum_prod_type]
      have hpull : ∀ us : Fin M₁₁ → Fin L₁ → Fin n → U,
          (∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
            (iidDist P_W n).pmf w *
            (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
            (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (∑ y : Fin n → Y,
              (W2.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
              (if (w, vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) ≤
          (iidDist P_W n).pmf w *
          (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
        intro us
        have hrew : (∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
            (iidDist P_W n).pmf w *
            (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
            (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
            (∑ y : Fin n → Y,
              (W2.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
              (if (w, vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) =
          ((iidDist P_W n).pmf w * (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us) *
          (∑ y : Fin n → Y,
            ∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
              (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
              ((W2.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
               (if (w, vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          refine Finset.sum_congr rfl fun vs _ => by ring
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ((iidDist P_W n).nonneg w) ((iidDist _ M₁₁).nonneg us))
        have hper_y : ∀ y : Fin n → Y,
            (∑ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
              (iidDist (iidDist (dmcRow (K_V.power n) w) L₂) M₂₂).pmf vs *
              ((W2.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).1 i,
                vs m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) (vs m₂₂)).2 i)) y *
               (if (w, vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) ≤
            (∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
              (W2.power n).trans (fun i => (w i,
                us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).1 i,
                b₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).2 i)) y) *
            (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
          intro y
          rw [iidDist_sum_two_coords (iidDist (dmcRow (K_V.power n) w) L₂)
            (fun b₂ => (W2.power n).trans (fun i => (w i,
              us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).1 i,
              b₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).2 i)) y)
            (fun b₂' => if (w, b₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) hne.symm]
          refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun b₂ _ =>
            mul_nonneg ((iidDist _ L₂).nonneg b₂) ((W2.power n).nonneg _ y))
          rw [iidDist_sum_coord (dmcRow (K_V.power n) w)
            (fun v' => if (w, v', y) ∈ A₂ then (1 : ℝ) else 0) l₂']
          have hpack := mc_pointwise_cond_packing Q2 n ε_d w y
          dsimp only at hpack
          rw [hQ2_WV] at hpack
          refine le_trans (Finset.sum_le_sum fun v' _ => ?_) hpack
          by_cases hm : (w, v', y) ∈ A₂
          · have hmd := (mem_martonDecSet Q2 n ε_d (w, v', y)).mp hm
            have hcond : w ∈ weakTypicalSet (Q2.map (fun t => t.1)) n ε_d ∧
                (fun i => (w i, v' i)) ∈ weakTypicalSet P_WV n ε_d ∧
                (fun i => (w i, y i)) ∈ weakTypicalSet (Q2.map (fun t => (t.1, t.2.2))) n ε_d ∧
                (fun i => (w i, v' i, y i)) ∈ weakTypicalSet Q2 n ε_d :=
              ⟨hmd.1, hQ2_WV ▸ hmd.2.1, hmd.2.2.2.1, hmd.2.2.2.2.1⟩
            simp only [hm, hcond, ↓reduceIte, mul_one]; exact le_rfl
          · simp only [hm, ↓reduceIte, mul_zero]
            split_ifs
            · exact (K_V.power n).nonneg w v'
            · exact le_rfl
        calc ∑ y : Fin n → Y, _
          _ ≤ ∑ y : Fin n → Y,
                (∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
                  (W2.power n).trans (fun i => (w i,
                    us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).1 i,
                    b₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).2 i)) y) *
                (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
              Finset.sum_le_sum fun y _ => hper_y y
          _ = (∑ b₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf b₂ *
                (∑ y : Fin n → Y, (W2.power n).trans (fun i => (w i,
                  us m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).1 i,
                  b₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ w (us m₁₁) b₂).2 i)) y)) *
                (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
              rw [← Finset.sum_mul]; congr 1
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun b₂ _ => (Finset.mul_sum _ _ _).symm
          _ = _ := by simp_rw [(W2.power n).sum_one, mul_one, (iidDist _ L₂).sum_one, one_mul]
      calc _ ≤ ∑ us : Fin M₁₁ → Fin L₁ → Fin n → U,
            (iidDist P_W n).pmf w * (iidDist (iidDist (dmcRow (K_U.power n) w) L₁) M₁₁).pmf us *
            (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
          Finset.sum_le_sum fun us _ => hpull us
        _ = (iidDist P_W n).pmf w *
            (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, (iidDist _ M₁₁).sum_one, mul_one]
    calc _ ≤ ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
        Finset.sum_le_sum fun w _ => hper_w w
      _ = _ := by rw [← Finset.sum_mul, (iidDist P_W n).sum_one, one_mul]
  have hT4 : ∀ m₀' ∈ Finset.univ.erase m₀, ∀ (m₂₂' : Fin M₂₂) (l₂' : Fin L₂),
      ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
    intro m₀' hm₀' m₂₂' l₂'
    have hne : m₀' ≠ m₀ := (Finset.mem_erase.mp hm₀').1
    have hswap : (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) =
        ∑ y : Fin n → Y, ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          ((W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
           (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) := by
      simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    rw [hswap]
    have hper_y : ∀ y : Fin n → Y,
        (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          ((W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
           (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) ≤
        (∑ c : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c *
          (W2.power n).trans (fun i => (c.1 i,
            c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
            c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y) *
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
      intro y
      dsimp only [Wcode, martonEncZ]
      rw [iidDist_sum_two_coords Qcloud
        (fun c => (W2.power n).trans (fun i => (c.1 i,
          c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
          c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y)
        (fun c' => if (c'.1, c'.2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) hne.symm]
      refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun c _ =>
        mul_nonneg (Qcloud.nonneg c) ((W2.power n).nonneg _ y))
      have hWV_sum : (∑ c' : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c' *
            (if (c'.1, c'.2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) =
          ∑ wv : Fin n → W_aux × V, (iidDist P_WV n).pmf wv *
            (if (fun i => (wv i).1, fun i => (wv i).2, y) ∈ A₂ then (1 : ℝ) else 0) := by
        unfold Qcloud martonCloudDist; dsimp only
        rw [Fintype.sum_prod_type]
        have h1 : ∀ w' : Fin n → W_aux,
            (∑ uv : (Fin M₁₁ → Fin L₁ → Fin n → U) × (Fin M₂₂ → Fin L₂ → Fin n → V),
              (iidDist P_W n).pmf w' *
              (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf uv.1 *
              (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf uv.2 *
              (if (w', uv.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) =
            ∑ v' : Fin n → V, (iidDist P_WV n).pmf (fun i => (w' i, v' i)) *
              (if (w', v', y) ∈ A₂ then (1 : ℝ) else 0) := fun w' => by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          have hU : ∀ vs : Fin M₂₂ → Fin L₂ → Fin n → V,
              (∑ us : Fin M₁₁ → Fin L₁ → Fin n → U,
                (iidDist P_W n).pmf w' *
                (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                (if (w', vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) =
              (iidDist P_W n).pmf w' *
              ((iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                (if (w', vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0)) := fun vs => by
            have hfac : ∀ us : Fin M₁₁ → Fin L₁ → Fin n → U,
                (iidDist P_W n).pmf w' *
                (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                (iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                (if (w', vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) =
                (iidDist (iidDist (dmcRow (K_U.power n) w') L₁) M₁₁).pmf us *
                ((iidDist P_W n).pmf w' *
                 ((iidDist (iidDist (dmcRow (K_V.power n) w') L₂) M₂₂).pmf vs *
                  (if (w', vs m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) := fun _ => by ring
            simp_rw [hfac, ← Finset.sum_mul, (iidDist _ M₁₁).sum_one, one_mul]
          simp_rw [hU, ← Finset.mul_sum]
          rw [iidDist_sum_coord (iidDist (dmcRow (K_V.power n) w') L₂)
            (fun b₂' => if (w', b₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) m₂₂']
          rw [iidDist_sum_coord (dmcRow (K_V.power n) w')
            (fun v' => if (w', v', y) ∈ A₂ then (1 : ℝ) else 0) l₂']
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v' _ => ?_
          rw [← mul_assoc]
          congr 1
          have hzip := (jointIidDist_eq_fst_mul_condChannelPower P_WV n w' v').symm
          rw [hPWV_fst] at hzip
          exact hzip
        refine (Finset.sum_congr rfl fun w' _ => h1 w').trans ?_
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (zipEquiv W_aux V n) _ _ (fun _ => rfl)
      rw [hWV_sum]
      have hpack := mc_pointwise_uncond_packing (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) n ε_d y
      rw [hQ2_WAY_fst] at hpack
      refine le_trans (Finset.sum_le_sum fun wv _ => ?_) hpack
      by_cases hm : (fun i => (wv i).1, fun i => (wv i).2, y) ∈ A₂
      · have hmd := (mem_martonDecSet Q2 n ε_d (fun i => (wv i).1, fun i => (wv i).2, y)).mp hm
        have hsnd : (Q2.map (fun t => ((t.1, t.2.1), t.2.2))).snd = Q2.map (fun t => t.2.2) := by
          rw [← mc_probDist_map_snd, map_comp_eq]; rfl
        have hcond : wv ∈ weakTypicalSet P_WV n ε_d ∧
            y ∈ weakTypicalSet (Q2.map (fun t => ((t.1, t.2.1), t.2.2))).snd n ε_d ∧
            (fun i => (wv i, y i)) ∈ weakTypicalSet (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) n ε_d :=
          ⟨hQ2_WV ▸ hmd.2.1, hsnd ▸ hmd.2.2.1, hmd.2.2.2.2.2⟩
        simp only [hm, hcond, ↓reduceIte, mul_one]; exact le_rfl
      · simp only [hm, ↓reduceIte, mul_zero]
        split_ifs
        · exact (iidDist P_WV n).nonneg wv
        · exact le_rfl
    calc ∑ y : Fin n → Y, _
      _ ≤ ∑ y : Fin n → Y,
            (∑ c : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c *
              (W2.power n).trans (fun i => (c.1 i,
                c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
                c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y) *
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) :=
          Finset.sum_le_sum fun y _ => hper_y y
      _ = (∑ c : MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Qcloud.pmf c *
            (∑ y : Fin n → Y,
              (W2.power n).trans (fun i => (c.1 i,
                c.2.1 m₁₁ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).1 i,
                c.2.2 m₂₂ (martonEncPair P_wuv hL₁ hL₂ ε₁ c.1 (c.2.1 m₁₁) (c.2.2 m₂₂)).2 i)) y)) *
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
          rw [← Finset.sum_mul]; congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
      _ = _ := by simp_rw [(W2.power n).sum_one, mul_one, Qcloud.sum_one, one_mul]
  have hsum : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y ≠ (m₀, m₂₂) then (1 : ℝ) else 0)) ≤
      (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0))) +
      (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J2 n ε₂
           then (1 : ℝ) else 0))) +
      (∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) +
      (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) := by
    have hptC : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        Wcode.pmf C * (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y ≠ (m₀, m₂₂) then (1 : ℝ) else 0)) ≤
        Wcode.pmf C * (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if Eenc C then (1 : ℝ) else 0)) +
        Wcode.pmf C * (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
          (if ¬ Eenc C ∧ (fun i => (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂ i, y i)) ∉ strongTypicalSet J2 n ε₂
           then (1 : ℝ) else 0)) +
        (∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂,
          Wcode.pmf C * (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) +
        (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂,
          Wcode.pmf C * (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) := by
      intro C
      have hy := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (hind C y) ((W2.power n).nonneg (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y)
      have hmul := mul_le_mul_of_nonneg_left hy (Wcode.nonneg C)
      refine le_trans hmul (le_of_eq ?_)
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [mul_add, mul_add, mul_add]
      congr 1
      · congr 1
        · have hswapA : (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
                ∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂,
                  if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) =
              ∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂, ∑ y : Fin n → Y,
                (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
                  (if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) := by
            simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          rw [hswapA, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
      · have hswapB : (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
              ∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂,
                if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) =
            ∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂, ∑ y : Fin n → Y,
              (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
                (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0) := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        rw [hswapB, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
    refine le_trans (Finset.sum_le_sum fun C _ => hptC C) (le_of_eq ?_)
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hT3_tot : (∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ l₂' : Fin L₂,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀).1, (C m₀).2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) ≤
      (((M₂₂ - 1 : ℕ) * L₂ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) := by
    calc _ ≤ ∑ m₂₂' ∈ Finset.univ.erase m₂₂, ∑ _l₂' : Fin L₂,
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (Q2.map (fun t => (t.2.1, t.2.2, t.1))) - 4 * ε_d))) :=
        Finset.sum_le_sum fun m₂₂' hm => Finset.sum_le_sum fun l₂' _ => hT3 m₂₂' hm l₂'
      _ = _ := by
        simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m₂₂), nsmul_eq_mul, mul_assoc]
  have hT4_tot : (∑ m₀' ∈ Finset.univ.erase m₀, ∑ m₂₂' : Fin M₂₂, ∑ l₂' : Fin L₂,
        ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
          (∑ y : Fin n → Y, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y *
            (if ((C m₀').1, (C m₀').2.2 m₂₂' l₂', y) ∈ A₂ then (1 : ℝ) else 0))) ≤
      (((M₀ - 1 : ℕ) * M₂₂ * L₂ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) := by
    calc _ ≤ ∑ m₀' ∈ Finset.univ.erase m₀, ∑ _m₂₂' : Fin M₂₂, ∑ _l₂' : Fin L₂,
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) - 3 * ε_d))) :=
        Finset.sum_le_sum fun m₀' hm => Finset.sum_le_sum fun m₂₂' _ => Finset.sum_le_sum fun l₂' _ =>
          hT4 m₀' hm m₂₂' l₂'
      _ = _ := by
        simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m₀), nsmul_eq_mul, mul_assoc]
  linarith

open Classical in
/-- **Marton Finite-Blocklength Random-Coding Existence Bound** (El Gamal–Kim Thm. 8.3):
    for any DMBC `W`, single-letter `Pwuvx : ProbDist (W_aux × U × V × X)`, blocklength `n > 0`,
    rate-splitting sizes `M₁₀, M₁₁, M₂₀, M₂₂, L₁, L₂ > 0` with `M₁ ≤ M₁₀ * M₁₁` and `M₂ ≤ M₂₀ * M₂₂`,
    and typicality parameters `0 < ε₁ < ε₂` with `ε_d` dominating `ε₂ * H(·)` on all relevant marginals,
    there exists a deterministic broadcast code `(enc, dec₁, dec₂)` of size `(M₁, M₂)` over `W`
    whose average error is bounded by the covering, Markov, and four Marton packing terms. -/
theorem marton_random_coding_bound (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X))
    {n M₁ M₂ M₁₀ M₁₁ M₂₀ M₂₂ L₁ L₂ : ℕ}
    (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₁₀ : 0 < M₁₀) (hM₁₁ : 0 < M₁₁) (hM₂₀ : 0 < M₂₀) (hM₂₂ : 0 < M₂₂)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hle₁ : M₁ ≤ M₁₀ * M₁₁) (hle₂ : M₂ ≤ M₂₀ * M₂₂)
    {ε₁ ε₂ ε_d : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁₂ : ε₁ < ε₂)
    (hε_d :
      let J := martonJoint W Pwuvx
      let Q1 := J.map (fun z => (z.1.1, z.1.2.1, z.2.1))
      let Q2 := J.map (fun z => (z.1.1, z.1.2.2.1, z.2.2))
      ε₂ * shannonEntropy (Q1.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q1 ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q2 ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d) :
    let J := martonJoint W Pwuvx
    let P_wuv := Pwuvx.map (fun t => (t.1, t.2.1, t.2.2.1))
    let P_W := P_wuv.map (fun t => t.1)
    let K_U := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.1)))
    let K_V := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.2)))
    let IWU_Y1 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.1), z.2.1)))
    let IWV_Y2 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)))
    let IU_Y1_W := condMutualInfo (J.map (fun z => (z.1.2.1, z.2.1, z.1.1)))
    let IV_Y2_W := condMutualInfo (J.map (fun z => (z.1.2.2.1, z.2.2, z.1.1)))
    let J1 := (bcMarginal1 (martonEffChannel W Pwuvx)).joint P_wuv
    let J2 := (bcMarginal2 (martonEffChannel W Pwuvx)).joint P_wuv
    let C1 := ∑ p : (W_aux × U × V) × Y₁, if 0 < J1.pmf p then 1 / J1.pmf p ^ 2 else 0
    let C2 := ∑ p : (W_aux × U × V) × Y₂, if 0 < J2.pmf p then 1 / J2.pmf p ^ 2 else 0
    let P_cov := ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
      (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0)))
    let M₀ := M₁₀ * M₂₀
    ∃ (enc : Fin M₁ → Fin M₂ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₂),
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
           then (W.power n).trans (enc m₁ m₂) y else 0) ≤
        2 * P_cov +
        C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) +
        C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) +
        (((M₁₁ - 1 : ℕ) * L₁ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (IU_Y1_W - 4 * ε_d))) +
        (((M₀ - 1 : ℕ) * M₁₁ * L₁ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (IWU_Y1 - 3 * ε_d))) +
        (((M₂₂ - 1 : ℕ) * L₂ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (IV_Y2_W - 4 * ε_d))) +
        (((M₀ - 1 : ℕ) * M₂₂ * L₂ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (IWV_Y2 - 3 * ε_d))) := by
  dsimp only
  let J := martonJoint W Pwuvx
  let P_wuv := Pwuvx.map (fun t => (t.1, t.2.1, t.2.2.1))
  let W_eff := martonEffChannel W Pwuvx
  let W1 := bcMarginal1 W_eff
  let W2 := bcMarginal2 W_eff
  let J1 := W1.joint P_wuv
  let J2 := W2.joint P_wuv
  let Q1 : ProbDist (W_aux × U × Y₁) := J.map (fun z => (z.1.1, z.1.2.1, z.2.1))
  let Q2 : ProbDist (W_aux × V × Y₂) := J.map (fun z => (z.1.1, z.1.2.2.1, z.2.2))
  have hJ1_eq : J1 = (W_eff.joint P_wuv).map (fun z => (z.1, z.2.1)) := by
    apply mc_probDist_ext; rintro ⟨z, y₁⟩
    unfold J1 W1 DMC.joint bcMarginal1 ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single z]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
      · simp [Finset.mul_sum]
      · intro y₁' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro z' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hJ2_eq : J2 = (W_eff.joint P_wuv).map (fun z => (z.1, z.2.2)) := by
    apply mc_probDist_ext; rintro ⟨z, y₂⟩
    unfold J2 W2 DMC.joint bcMarginal2 ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single z]
    · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y₂]
      · simp [Finset.mul_sum]
      · intro y₂' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro z' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ1_from_J1 : J1.map (fun z => (z.1.1, z.1.2.1, z.2)) = Q1 := by
    rw [hJ1_eq, martonEffChannel_joint_eq W Pwuvx, map_comp_eq, map_comp_eq]; rfl
  have hQ2_from_J2 : J2.map (fun z => (z.1.1, z.1.2.2, z.2)) = Q2 := by
    rw [hJ2_eq, martonEffChannel_joint_eq W Pwuvx, map_comp_eq, map_comp_eq]; rfl
  let M₀ := M₁₀ * M₂₀
  have hM₀ : 0 < M₀ := Nat.mul_pos hM₁₀ hM₂₀
  let split1 : Fin M₁ → Fin M₁₀ × Fin M₁₁ := fun m₁ => finProdFinEquiv.symm (Fin.castLE hle₁ m₁)
  let split2 : Fin M₂ → Fin M₂₀ × Fin M₂₂ := fun m₂ => finProdFinEquiv.symm (Fin.castLE hle₂ m₂)
  let m0Of : Fin M₁ → Fin M₂ → Fin M₀ := fun m₁ m₂ => finProdFinEquiv ((split1 m₁).1, (split2 m₂).1)
  let unsplit1 : Fin M₁₀ × Fin M₁₁ → Fin M₁ := fun p =>
    let k := (finProdFinEquiv p).1
    if h : k < M₁ then ⟨k, h⟩ else ⟨0, hM₁⟩
  let unsplit2 : Fin M₂₀ × Fin M₂₂ → Fin M₂ := fun p =>
    let k := (finProdFinEquiv p).1
    if h : k < M₂ then ⟨k, h⟩ else ⟨0, hM₂⟩
  have hunsplit1_left : ∀ m₁ : Fin M₁, unsplit1 (split1 m₁) = m₁ := fun m₁ => by
    dsimp only [unsplit1, split1]
    rw [Equiv.apply_symm_apply]
    simp [m₁.isLt]
  have hunsplit2_left : ∀ m₂ : Fin M₂, unsplit2 (split2 m₂) = m₂ := fun m₂ => by
    dsimp only [unsplit2, split2]
    rw [Equiv.apply_symm_apply]
    simp [m₂.isLt]
  let Wcode := iidDist (martonCloudDist P_wuv n M₁₁ M₂₂ L₁ L₂) M₀
  let dec1Of : (Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) → (Fin n → Y₁) → Fin M₁ := fun C y₁ =>
    let r := martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y₁
    unsplit1 ((finProdFinEquiv.symm r.1).1, r.2)
  let dec2Of : (Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) → (Fin n → Y₂) → Fin M₂ := fun C y₂ =>
    let r := martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y₂
    unsplit2 ((finProdFinEquiv.symm r.1).2, r.2)
  let effErr : (Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂) → ℝ := fun C =>
    ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
        then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2) y else 0
  let P_W := P_wuv.map (fun t => t.1)
  let K_U := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.1)))
  let K_V := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.2)))
  let C1 := ∑ p : (W_aux × U × V) × Y₁, if 0 < J1.pmf p then 1 / J1.pmf p ^ 2 else 0
  let C2 := ∑ p : (W_aux × U × V) × Y₂, if 0 < J2.pmf p then 1 / J2.pmf p ^ 2 else 0
  let P_cov := ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
    (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
      (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
        (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
            (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
         then (1 : ℝ) else 0)))
  let B : ℝ :=
    2 * P_cov +
    C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) +
    C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) +
    (((M₁₁ - 1 : ℕ) * L₁ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2.1, z.2.1, z.1.1))) - 4 * ε_d))) +
    (((M₀ - 1 : ℕ) * M₁₁ * L₁ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => ((z.1.1, z.1.2.1), z.2.1))) - 3 * ε_d))) +
    (((M₂₂ - 1 : ℕ) * L₂ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2.2.1, z.2.2, z.1.1))) - 4 * ε_d))) +
    (((M₀ - 1 : ℕ) * M₂₂ * L₂ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) - 3 * ε_d)))
  have hε_d1 :
      let Q1' := (W1.joint P_wuv).map (fun z => (z.1.1, z.1.2.1, z.2))
      ε₂ * shannonEntropy (Q1'.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1'.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1'.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1'.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q1' ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1'.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d := by
    dsimp only; rw [hQ1_from_J1]
    exact ⟨hε_d.1, hε_d.2.1, hε_d.2.2.1, hε_d.2.2.2.1, hε_d.2.2.2.2.1, hε_d.2.2.2.2.2.1⟩
  have hε_d2 :
      let Q2' := (W2.joint P_wuv).map (fun z => (z.1.1, z.1.2.2, z.2))
      ε₂ * shannonEntropy (Q2'.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2'.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2'.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2'.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q2' ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2'.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d := by
    dsimp only; rw [hQ2_from_J2]
    exact ⟨hε_d.2.2.2.2.2.2.1, hε_d.2.2.2.2.2.2.2.1, hε_d.2.2.2.2.2.2.2.2.1,
      hε_d.2.2.2.2.2.2.2.2.2.1, hε_d.2.2.2.2.2.2.2.2.2.2.1, hε_d.2.2.2.2.2.2.2.2.2.2.2⟩
  have hpair : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂),
      ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
        (∑ y : Fin n → Y₁ × Y₂,
          if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
          then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2) y else 0) ≤ B := by
    intro m₁ m₂
    let m₀ := m0Of m₁ m₂
    let m₁₁ := (split1 m₁).2
    let m₂₂ := (split2 m₂).2
    have hrx1 := mc_marton_single_rx_error_bound P_wuv W1 hn hM₀ hM₁₁ hL₁ hL₂ hε₁ hε₁₂ hε_d1 m₀ m₁₁ m₂₂
    have hrx2 := mc_marton_rx2_error_bound P_wuv W2 hn hM₀ hM₂₂ hL₁ hL₂ hε₁ hε₁₂ hε_d2 m₀ m₁₁ m₂₂
    dsimp only at hrx1 hrx2
    rw [hQ1_from_J1] at hrx1
    rw [hQ2_from_J2] at hrx2
    have hIWU : Q1.map (fun t => ((t.1, t.2.1), t.2.2)) = J.map (fun z => ((z.1.1, z.1.2.1), z.2.1)) := by
      unfold Q1; rw [map_comp_eq]; rfl
    have hIUW : Q1.map (fun t => (t.2.1, t.2.2, t.1)) = J.map (fun z => (z.1.2.1, z.2.1, z.1.1)) := by
      unfold Q1; rw [map_comp_eq]; rfl
    have hIWV : Q2.map (fun t => ((t.1, t.2.1), t.2.2)) = J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)) := by
      unfold Q2; rw [map_comp_eq]; rfl
    have hIVW : Q2.map (fun t => (t.2.1, t.2.2, t.1)) = J.map (fun z => (z.1.2.2.1, z.2.2, z.1.1)) := by
      unfold Q2; rw [map_comp_eq]; rfl
    rw [hIWU, hIUW] at hrx1
    rw [hIWV, hIVW] at hrx2
    have hsplit_rx : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂,
        (∑ y : Fin n → Y₁ × Y₂,
          if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
          then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y else 0) ≤
        (∑ y₁ : Fin n → Y₁, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y₁ *
          (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y₁ ≠ (m₀, m₁₁) then (1 : ℝ) else 0)) +
        (∑ y₂ : Fin n → Y₂, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y₂ *
          (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y₂ ≠ (m₀, m₂₂) then (1 : ℝ) else 0)) := by
      intro C
      have himp1 : ∀ y₁, dec1Of C y₁ ≠ m₁ → martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y₁ ≠ (m₀, m₁₁) := fun y₁ hne heq => by
        apply hne
        dsimp only [dec1Of]; rw [heq]; dsimp only [m₀, m0Of, m₁₁]
        rw [Equiv.symm_apply_apply]; exact hunsplit1_left m₁
      have himp2 : ∀ y₂, dec2Of C y₂ ≠ m₂ → martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y₂ ≠ (m₀, m₂₂) := fun y₂ hne heq => by
        apply hne
        dsimp only [dec2Of]; rw [heq]; dsimp only [m₀, m0Of, m₂₂]
        rw [Equiv.symm_apply_apply]; exact hunsplit2_left m₂
      have hor : ∀ y : Fin n → Y₁ × Y₂,
          (if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
           then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y else 0) ≤
          (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C (fun i => (y i).1) ≠ (m₀, m₁₁)
           then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y else 0) +
          (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C (fun i => (y i).2) ≠ (m₀, m₂₂)
           then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y else 0) := by
        intro y
        have hnn := (W_eff.power n).nonneg (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y
        by_cases hr1 : martonRawDec1 Q1 hM₀ hM₁₁ ε_d C (fun i => (y i).1) ≠ (m₀, m₁₁)
        · split_ifs <;> linarith
        · by_cases hr2 : martonRawDec2 Q2 hM₀ hM₂₂ ε_d C (fun i => (y i).2) ≠ (m₀, m₂₂)
          · split_ifs <;> linarith
          · have h1 : ¬ dec1Of C (fun i => (y i).1) ≠ m₁ := fun h => hr1 (himp1 _ h)
            have h2 : ¬ dec2Of C (fun i => (y i).2) ≠ m₂ := fun h => hr2 (himp2 _ h)
            split_ifs with hor
            · exact absurd hor (not_or.mpr ⟨h1, h2⟩)
            · linarith
      calc _ ≤ (∑ y : Fin n → Y₁ × Y₂, if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C (fun i => (y i).1) ≠ (m₀, m₁₁)
                  then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y else 0) +
               (∑ y : Fin n → Y₁ × Y₂, if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C (fun i => (y i).2) ≠ (m₀, m₂₂)
                  then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y else 0) := by
            rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun y _ => hor y
        _ = _ := by
            rw [mc_bc_sum_ite_fst_power W_eff (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂)
                  (fun y₁ => martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y₁ ≠ (m₀, m₁₁)),
                mc_bc_sum_ite_snd_power W_eff (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂)
                  (fun y₂ => martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y₂ ≠ (m₀, m₂₂))]
    calc _ ≤ (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
              (∑ y₁ : Fin n → Y₁, (W1.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y₁ *
                (if martonRawDec1 Q1 hM₀ hM₁₁ ε_d C y₁ ≠ (m₀, m₁₁) then (1 : ℝ) else 0))) +
             (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
              (∑ y₂ : Fin n → Y₂, (W2.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C m₀ m₁₁ m₂₂) y₂ *
                (if martonRawDec2 Q2 hM₀ hM₂₂ ε_d C y₂ ≠ (m₀, m₂₂) then (1 : ℝ) else 0))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun C _ => ?_
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hsplit_rx C) (Wcode.nonneg C)
      _ ≤ B := by dsimp only [B]; linarith
  have hexp_le : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C * effErr C ≤ B := by
    have havg : ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C * effErr C =
        ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C *
            (∑ y : Fin n → Y₁ × Y₂,
              if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
              then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2) y else 0) := by
      have h1 : ∀ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, Wcode.pmf C * effErr C =
          ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
            ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, Wcode.pmf C * ∑ y : Fin n → Y₁ × Y₂,
              if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
              then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2) y else 0 := fun C => by
        dsimp only [effErr]
        rw [← mul_assoc, mul_comm (Wcode.pmf C), mul_assoc, Finset.mul_sum]
        congr 1; exact Finset.sum_congr rfl fun m₁ _ => Finset.mul_sum _ _ _
      trans (∑ C : Fin M₀ → MartonCloud W_aux U V n M₁₁ M₂₂ L₁ L₂, ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, Wcode.pmf C * ∑ y : Fin n → Y₁ × Y₂,
            if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
            then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2) y else 0)
      · exact Finset.sum_congr rfl fun C _ => h1 C
      · rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.sum_comm]
    rw [havg]
    have hM12_pos : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hM₁ hM₂
    calc _ ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁, ∑ _m₂ : Fin M₂, B :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => hpair m₁ m₂) (by positivity)
      _ = ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (((M₁ * M₂ : ℕ) : ℝ) * B) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = B := by field_simp [hM12_pos.ne']
  obtain ⟨C, hC⟩ := mc_exists_le_of_weighted_sum_le Wcode.pmf effErr B Wcode.nonneg Wcode.sum_one hexp_le
  let P_wuv_x : ProbDist ((W_aux × U × V) × X) :=
    Pwuvx.map (fun t => ((t.1, t.2.1, t.2.2.1), t.2.2.2))
  let K_X := condChannelOfJoint P_wuv_x
  have hdet : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂),
      ∃ x : Fin n → X,
        (∑ y : Fin n → Y₁ × Y₂,
          if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
          then (W.power n).trans x y else 0) ≤
        ∑ y : Fin n → Y₁ × Y₂,
          if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
          then (W_eff.power n).trans (martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2) y else 0 := by
    intro m₁ m₂
    let z := martonEncZ P_wuv hL₁ hL₂ ε₁ C (m0Of m₁ m₂) (split1 m₁).2 (split2 m₂).2
    let Qx := dmcRow (K_X.power n) z
    refine mc_exists_le_of_weighted_sum_le Qx.pmf
      (fun x => ∑ y : Fin n → Y₁ × Y₂,
        if dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
        then (W.power n).trans x y else 0)
      _ Qx.nonneg Qx.sum_one (le_of_eq ?_)
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [martonEffChannel_power_trans W Pwuvx n z y]
    by_cases herr : dec1Of C (fun i => (y i).1) ≠ m₁ ∨ dec2Of C (fun i => (y i).2) ≠ m₂
    · simp only [herr, ↓reduceIte]; rfl
    · simp [herr]
  choose enc henc using hdet
  refine ⟨enc, dec1Of C, dec2Of C, le_trans ?_ hC⟩
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => henc m₁ m₂) (by positivity)

end MartonRandomCoding

/-! ### 5. Marton's Coding Achievability & Inner Bound -/

section MartonAchievability

variable {W_aux U V X Y₁ Y₂ : Type*}
  [Fintype W_aux] [Fintype U] [Fintype V] [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- Helper: achievability of `(R₁, R₂)` from explicit Marton split parameters
    `(R₁₀, R₁₁, R₂₀, R₂₂, R₁', R₂')`. -/
private lemma marton_achievable_of_split (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X))
    {R₁ R₂ R₁₀ R₁₁ R₂₀ R₂₂ R₁' R₂' : ℝ}
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (h10 : 0 ≤ R₁₀) (h11 : 0 ≤ R₁₁) (h20 : 0 ≤ R₂₀) (h22 : 0 ≤ R₂₂)
    (h1' : 0 ≤ R₁') (h2' : 0 ≤ R₂')
    (hsum1 : R₁₀ + R₁₁ = R₁) (hsum2 : R₂₀ + R₂₂ = R₂)
    (hcov : condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1))) < R₁' + R₂' ∨
      (R₁' = 0 ∧ R₂' = 0 ∧ condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1))) = 0))
    (hp1 : R₁₁ = 0 ∨ R₁₁ + R₁' < condMutualInfo ((martonJoint W Pwuvx).map (fun z => (z.1.2.1, z.2.1, z.1.1))))
    (hp2 : R₂₂ = 0 ∨ R₂₂ + R₂' < condMutualInfo ((martonJoint W Pwuvx).map (fun z => (z.1.2.2.1, z.2.2, z.1.1))))
    (hp3 : R₁₀ + R₂₀ + R₁₁ + R₁' < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1), z.2.1))))
    (hp4 : R₁₀ + R₂₀ + R₂₂ + R₂' < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)))) :
    IsBCAchievable W R₁ R₂ := by
  classical
  let J := martonJoint W Pwuvx
  let P_wuv := Pwuvx.map (fun t => (t.1, t.2.1, t.2.2.1))
  let P_W := P_wuv.map (fun t => t.1)
  let K_U := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.1)))
  let K_V := condChannelOfJoint (P_wuv.map (fun t => (t.1, t.2.2)))
  let Q1 := J.map (fun z => (z.1.1, z.1.2.1, z.2.1))
  let Q2 := J.map (fun z => (z.1.1, z.1.2.2.1, z.2.2))
  let IWU_Y1 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.1), z.2.1)))
  let IWV_Y2 := mutualInfo (J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)))
  let IU_Y1_W := condMutualInfo (J.map (fun z => (z.1.2.1, z.2.1, z.1.1)))
  let IV_Y2_W := condMutualInfo (J.map (fun z => (z.1.2.2.1, z.2.2, z.1.1)))
  let g1 : ℝ := if R₁₁ = 0 then 1 else IU_Y1_W - (R₁₁ + R₁')
  let g2 : ℝ := if R₂₂ = 0 then 1 else IV_Y2_W - (R₂₂ + R₂')
  let g3 : ℝ := IWU_Y1 - (R₁₀ + R₂₀ + R₁₁ + R₁')
  let g4 : ℝ := IWV_Y2 - (R₁₀ + R₂₀ + R₂₂ + R₂')
  have hg1 : 0 < g1 := by dsimp [g1]; split_ifs with h; exact zero_lt_one; linarith [hp1.resolve_left h]
  have hg2 : 0 < g2 := by dsimp [g2]; split_ifs with h; exact zero_lt_one; linarith [hp2.resolve_left h]
  have hg3 : 0 < g3 := by dsimp [g3]; linarith
  have hg4 : 0 < g4 := by dsimp [g4]; linarith
  let gap : ℝ := min (min g1 g2) (min g3 g4)
  have hgap : 0 < gap := lt_min (lt_min hg1 hg2) (lt_min hg3 hg4)
  let Hmax : ℝ :=
    shannonEntropy (Q1.map (fun t => t.1)) +
    shannonEntropy (Q1.map (fun t => (t.1, t.2.1))) +
    shannonEntropy (Q1.map (fun t => t.2.2)) +
    shannonEntropy (Q1.map (fun t => (t.1, t.2.2))) +
    shannonEntropy Q1 +
    shannonEntropy (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) +
    shannonEntropy (Q2.map (fun t => t.1)) +
    shannonEntropy (Q2.map (fun t => (t.1, t.2.1))) +
    shannonEntropy (Q2.map (fun t => t.2.2)) +
    shannonEntropy (Q2.map (fun t => (t.1, t.2.2))) +
    shannonEntropy Q2 +
    shannonEntropy (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) + 1
  have hHmax : 1 ≤ Hmax := by
    dsimp only [Hmax]
    linarith [shannonEntropy_nonneg (Q1.map (fun t => t.1)),
      shannonEntropy_nonneg (Q1.map (fun t => (t.1, t.2.1))),
      shannonEntropy_nonneg (Q1.map (fun t => t.2.2)),
      shannonEntropy_nonneg (Q1.map (fun t => (t.1, t.2.2))),
      shannonEntropy_nonneg Q1,
      shannonEntropy_nonneg (Q1.map (fun t => ((t.1, t.2.1), t.2.2))),
      shannonEntropy_nonneg (Q2.map (fun t => t.1)),
      shannonEntropy_nonneg (Q2.map (fun t => (t.1, t.2.1))),
      shannonEntropy_nonneg (Q2.map (fun t => t.2.2)),
      shannonEntropy_nonneg (Q2.map (fun t => (t.1, t.2.2))),
      shannonEntropy_nonneg Q2,
      shannonEntropy_nonneg (Q2.map (fun t => ((t.1, t.2.1), t.2.2)))]
  have hHmax_pos : 0 < Hmax := by linarith
  let ε₂ : ℝ := gap / (8 * Hmax)
  have hε₂ : 0 < ε₂ := by positivity
  let ε₁ : ℝ := ε₂ / 2
  have hε₁ : 0 < ε₁ := half_pos hε₂
  have hε₁₂ : ε₁ < ε₂ := by dsimp [ε₁]; linarith
  let ε_d : ℝ := ε₂ * Hmax
  have hε_d_eq : 4 * ε_d = gap / 2 := by
    dsimp only [ε_d, ε₂]; field_simp [hHmax_pos.ne']; ring
  have hε_d_dom :
      ε₂ * shannonEntropy (Q1.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q1 ≤ ε_d ∧
      ε₂ * shannonEntropy (Q1.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => t.1)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => (t.1, t.2.1))) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => t.2.2)) ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => (t.1, t.2.2))) ≤ ε_d ∧
      ε₂ * shannonEntropy Q2 ≤ ε_d ∧
      ε₂ * shannonEntropy (Q2.map (fun t => ((t.1, t.2.1), t.2.2))) ≤ ε_d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact mul_le_mul_of_nonneg_left (by
      dsimp only [Hmax]
      linarith [shannonEntropy_nonneg (Q1.map (fun t => t.1)),
        shannonEntropy_nonneg (Q1.map (fun t => (t.1, t.2.1))),
        shannonEntropy_nonneg (Q1.map (fun t => t.2.2)),
        shannonEntropy_nonneg (Q1.map (fun t => (t.1, t.2.2))),
        shannonEntropy_nonneg Q1,
        shannonEntropy_nonneg (Q1.map (fun t => ((t.1, t.2.1), t.2.2))),
        shannonEntropy_nonneg (Q2.map (fun t => t.1)),
        shannonEntropy_nonneg (Q2.map (fun t => (t.1, t.2.1))),
        shannonEntropy_nonneg (Q2.map (fun t => t.2.2)),
        shannonEntropy_nonneg (Q2.map (fun t => (t.1, t.2.2))),
        shannonEntropy_nonneg Q2,
        shannonEntropy_nonneg (Q2.map (fun t => ((t.1, t.2.1), t.2.2)))]) hε₂.le
  refine ⟨hR₁0, hR₂0, fun δ hδ => ?_⟩
  have hcov_ev : ∃ N₁ : ℕ, ∀ n ≥ N₁,
      let L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁'))
      let L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂'))
      ∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
        (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
          (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
            (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
                (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
             then (1 : ℝ) else 0))) ≤ δ / 16 := by
    rcases hcov with hstrict | ⟨h1'0, h2'0, hci0⟩
    · have hIeq : condMutualInfo (P_wuv.map (fun t => (t.2.1, t.2.2, t.1))) =
          condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1))) := by
        unfold P_wuv; rw [map_comp_eq]; rfl
      exact mutual_covering_lemma P_wuv h1' h2' (hIeq ▸ hstrict) hε₁ (by positivity)
    · subst h1'0; subst h2'0
      have hIeq : condMutualInfo (P_wuv.map (fun t => (t.2.1, t.2.2, t.1))) = 0 := by
        have h : P_wuv.map (fun t => (t.2.1, t.2.2, t.1)) =
            Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1)) := by unfold P_wuv; rw [map_comp_eq]; rfl
        rw [h, hci0]
      exact mc_covering_cond_indep P_wuv hIeq hε₁ (by positivity)
  obtain ⟨N₁, hN₁⟩ := hcov_ev
  let J1 := (bcMarginal1 (martonEffChannel W Pwuvx)).joint P_wuv
  let J2 := (bcMarginal2 (martonEffChannel W Pwuvx)).joint P_wuv
  let C1 := ∑ p : (W_aux × U × V) × Y₁, if 0 < J1.pmf p then 1 / J1.pmf p ^ 2 else 0
  let C2 := ∑ p : (W_aux × U × V) × Y₂, if 0 < J2.pmf p then 1 / J2.pmf p ^ 2 else 0
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((C1 + C2) / ((δ / 8) * (ε₂ - ε₁) ^ 2))
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (log2 (1 / (δ / 128)) / (gap / 2))
  refine ⟨max (max (max N₁ N₂) N₃) 1, fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hn)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ N₃)) (le_trans (le_max_left _ 1) hn)
  have hn2 : (C1 + C2) / ((δ / 8) * (ε₂ - ε₁) ^ 2) < (n : ℝ) := lt_of_lt_of_le hN₂ (by
    exact_mod_cast le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ N₃)) (le_trans (le_max_left _ 1) hn))
  have hn3 : log2 (1 / (δ / 128)) / (gap / 2) ≤ (n : ℝ) := le_trans hN₃ (by
    exact_mod_cast le_trans (le_max_right _ N₃) (le_trans (le_max_left _ 1) hn))
  have hdecay : (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) ≤ δ / 128 :=
    mc_two_rpow_neg_le_of_ge (half_pos hgap) (by positivity) hn3
  set M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  set M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  set M₁₀ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁₀))
  set M₁₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁₁))
  set M₂₀ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂₀))
  set M₂₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂₂))
  set L₁ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₁'))
  set L₂ := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R₂'))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hM₁₀ : 0 < M₁₀ := mc_ceil_two_rpow_pos n h10
  have hM₁₁ : 0 < M₁₁ := mc_ceil_two_rpow_pos n h11
  have hM₂₀ : 0 < M₂₀ := mc_ceil_two_rpow_pos n h20
  have hM₂₂ : 0 < M₂₂ := mc_ceil_two_rpow_pos n h22
  have hL₁ : 0 < L₁ := mc_ceil_two_rpow_pos n h1'
  have hL₂ : 0 < L₂ := mc_ceil_two_rpow_pos n h2'
  have hle₁ : M₁ ≤ M₁₀ * M₁₁ := by
    dsimp only [M₁, M₁₀, M₁₁]; rw [← hsum1]; exact mc_max_floor_le_mul_ceil n h10 h11
  have hle₂ : M₂ ≤ M₂₀ * M₂₂ := by
    dsimp only [M₂, M₂₀, M₂₂]; rw [← hsum2]; exact mc_max_floor_le_mul_ceil n h20 h22
  obtain ⟨enc, dec₁, dec₂, hbound⟩ := marton_random_coding_bound W Pwuvx
    hn_pos hM₁ hM₂ hM₁₀ hM₁₁ hM₂₀ hM₂₂ hL₁ hL₂ hle₁ hle₂ hε₁.le hε₁₂ hε_d_dom
  refine ⟨enc, dec₁, dec₂, ?_⟩
  have hb_cov : 2 * (∑ w : Fin n → W_aux, (iidDist P_W n).pmf w *
      (∑ C₁ : Fin L₁ → Fin n → U, (iidDist (dmcRow (K_U.power n) w) L₁).pmf C₁ *
        (∑ C₂ : Fin L₂ → Fin n → V, (iidDist (dmcRow (K_V.power n) w) L₂).pmf C₂ *
          (if ∀ (l₁ : Fin L₁) (l₂ : Fin L₂),
              (fun i => (w i, C₁ l₁ i, C₂ l₂ i)) ∉ strongTypicalSet P_wuv n ε₁
           then (1 : ℝ) else 0)))) ≤ δ / 8 := by
    have := hN₁ n hn1; dsimp only at this; linarith only [this]
  have hb_mk : C1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) + C2 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) ≤ δ / 8 := by
    rw [← add_div]
    have hdiff : 0 < ε₂ - ε₁ := by linarith only [hε₁₂]
    rw [div_le_iff₀ (by positivity)]
    have h1 := (div_lt_iff₀ (by positivity : 0 < (δ / 8) * (ε₂ - ε₁) ^ 2)).mp hn2
    linarith only [h1]
  have hb_p1 : (((M₁₁ - 1 : ℕ) * L₁ : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (IU_Y1_W - 4 * ε_d))) ≤ δ / 8 := by
    by_cases h0 : R₁₁ = 0
    · have hM11_eq : M₁₁ = 1 := by dsimp only [M₁₁]; rw [h0]; exact mc_ceil_two_rpow_zero n
      rw [hM11_eq]; simp; linarith only [hδ]
    · have hgap1 : gap ≤ IU_Y1_W - (R₁₁ + R₁') := by
        have h1 : gap ≤ g1 := le_trans (min_le_left (min g1 g2) (min g3 g4)) (min_le_left g1 g2)
        dsimp only [g1] at h1; split_ifs at h1; exact h1
      have hM : (((M₁₁ - 1 : ℕ) * L₁ : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ ((n : ℝ) * (R₁₁ + R₁')) := by
        rw [Nat.cast_mul]
        calc ((M₁₁ - 1 : ℕ) : ℝ) * (L₁ : ℝ)
          _ ≤ (M₁₁ : ℝ) * (L₁ : ℝ) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ 1)) (Nat.cast_nonneg _)
          _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * R₁₁)) * (2 * (2 : ℝ) ^ ((n : ℝ) * R₁')) :=
              mul_le_mul (mc_ceil_two_rpow_le_two_mul n h11) (mc_ceil_two_rpow_le_two_mul n h1')
                (Nat.cast_nonneg _) (by positivity)
          _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (R₁₁ + R₁')) := by
              rw [mul_mul_mul_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num; congr 2; ring
      have hexp : (n : ℝ) * (R₁₁ + R₁') + -((n : ℝ) * (IU_Y1_W - 4 * ε_d)) ≤ -((n : ℝ) * (gap / 2)) := by
        nlinarith only [hn_r, hgap1, hε_d_eq]
      calc _ ≤ 4 * (2 : ℝ) ^ ((n : ℝ) * (R₁₁ + R₁')) * (2 : ℝ) ^ (-((n : ℝ) * (IU_Y1_W - 4 * ε_d))) :=
            mul_le_mul_of_nonneg_right hM (by positivity)
        _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (R₁₁ + R₁') + -((n : ℝ) * (IU_Y1_W - 4 * ε_d))) := by
            rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by norm_num)
        _ ≤ δ / 8 := by linarith only [hdecay, hδ]
  have hb_p2 : (((M₁₀ * M₂₀ - 1 : ℕ) * M₁₁ * L₁ : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (IWU_Y1 - 3 * ε_d))) ≤ δ / 8 := by
    have hgap3 : gap ≤ IWU_Y1 - (R₁₀ + R₂₀ + R₁₁ + R₁') :=
      le_trans (min_le_right (min g1 g2) (min g3 g4)) (min_le_left g3 g4)
    have hM : (((M₁₀ * M₂₀ - 1 : ℕ) * M₁₁ * L₁ : ℕ) : ℝ) ≤
        16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₁₁ + R₁')) := by
      rw [Nat.cast_mul, Nat.cast_mul]
      have hsub : ((M₁₀ * M₂₀ - 1 : ℕ) : ℝ) ≤ (M₁₀ : ℝ) * (M₂₀ : ℝ) := by
        exact_mod_cast Nat.sub_le (M₁₀ * M₂₀) 1
      calc ((M₁₀ * M₂₀ - 1 : ℕ) : ℝ) * (M₁₁ : ℝ) * (L₁ : ℝ)
        _ ≤ (M₁₀ : ℝ) * (M₂₀ : ℝ) * (M₁₁ : ℝ) * (L₁ : ℝ) := by gcongr
        _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * R₁₀)) * (2 * (2 : ℝ) ^ ((n : ℝ) * R₂₀)) *
            (2 * (2 : ℝ) ^ ((n : ℝ) * R₁₁)) * (2 * (2 : ℝ) ^ ((n : ℝ) * R₁')) := by
            have h1 := mc_ceil_two_rpow_le_two_mul n h10
            have h2 := mc_ceil_two_rpow_le_two_mul n h20
            have h3 := mc_ceil_two_rpow_le_two_mul n h11
            have h4 := mc_ceil_two_rpow_le_two_mul n h1'
            gcongr
        _ = 16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₁₁ + R₁')) := by
            have hpow : (2 : ℝ) ^ ((n : ℝ) * R₁₀) * (2 : ℝ) ^ ((n : ℝ) * R₂₀) *
                (2 : ℝ) ^ ((n : ℝ) * R₁₁) * (2 : ℝ) ^ ((n : ℝ) * R₁') =
                (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₁₁ + R₁')) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                  ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                  ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 1; ring
            linarith only [hpow]
    have h34 : 3 * ε_d ≤ 4 * ε_d := by
      have hnn : 0 ≤ ε_d := by dsimp [ε_d]; positivity
      linarith only [hnn]
    have hexp : (n : ℝ) * (R₁₀ + R₂₀ + R₁₁ + R₁') + -((n : ℝ) * (IWU_Y1 - 3 * ε_d)) ≤ -((n : ℝ) * (gap / 2)) := by
      nlinarith only [hn_r, hgap3, hε_d_eq, h34]
    calc _ ≤ 16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₁₁ + R₁')) *
            (2 : ℝ) ^ (-((n : ℝ) * (IWU_Y1 - 3 * ε_d))) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₁₁ + R₁') + -((n : ℝ) * (IWU_Y1 - 3 * ε_d))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 16 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by norm_num)
      _ ≤ δ / 8 := by linarith only [hdecay, hδ]
  have hb_p3 : (((M₂₂ - 1 : ℕ) * L₂ : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (IV_Y2_W - 4 * ε_d))) ≤ δ / 8 := by
    by_cases h0 : R₂₂ = 0
    · have hM22_eq : M₂₂ = 1 := by dsimp only [M₂₂]; rw [h0]; exact mc_ceil_two_rpow_zero n
      rw [hM22_eq]; simp; linarith only [hδ]
    · have hgap2 : gap ≤ IV_Y2_W - (R₂₂ + R₂') := by
        have h1 : gap ≤ g2 := le_trans (min_le_left (min g1 g2) (min g3 g4)) (min_le_right g1 g2)
        dsimp only [g2] at h1; split_ifs at h1; exact h1
      have hM : (((M₂₂ - 1 : ℕ) * L₂ : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ ((n : ℝ) * (R₂₂ + R₂')) := by
        rw [Nat.cast_mul]
        calc ((M₂₂ - 1 : ℕ) : ℝ) * (L₂ : ℝ)
          _ ≤ (M₂₂ : ℝ) * (L₂ : ℝ) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ 1)) (Nat.cast_nonneg _)
          _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * R₂₂)) * (2 * (2 : ℝ) ^ ((n : ℝ) * R₂')) :=
              mul_le_mul (mc_ceil_two_rpow_le_two_mul n h22) (mc_ceil_two_rpow_le_two_mul n h2')
                (Nat.cast_nonneg _) (by positivity)
          _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (R₂₂ + R₂')) := by
              rw [mul_mul_mul_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num; congr 2; ring
      have hexp : (n : ℝ) * (R₂₂ + R₂') + -((n : ℝ) * (IV_Y2_W - 4 * ε_d)) ≤ -((n : ℝ) * (gap / 2)) := by
        nlinarith only [hn_r, hgap2, hε_d_eq]
      calc _ ≤ 4 * (2 : ℝ) ^ ((n : ℝ) * (R₂₂ + R₂')) * (2 : ℝ) ^ (-((n : ℝ) * (IV_Y2_W - 4 * ε_d))) :=
            mul_le_mul_of_nonneg_right hM (by positivity)
        _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (R₂₂ + R₂') + -((n : ℝ) * (IV_Y2_W - 4 * ε_d))) := by
            rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by norm_num)
        _ ≤ δ / 8 := by linarith only [hdecay, hδ]
  have hb_p4 : (((M₁₀ * M₂₀ - 1 : ℕ) * M₂₂ * L₂ : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (IWV_Y2 - 3 * ε_d))) ≤ δ / 8 := by
    have hgap4 : gap ≤ IWV_Y2 - (R₁₀ + R₂₀ + R₂₂ + R₂') :=
      le_trans (min_le_right (min g1 g2) (min g3 g4)) (min_le_right g3 g4)
    have hM : (((M₁₀ * M₂₀ - 1 : ℕ) * M₂₂ * L₂ : ℕ) : ℝ) ≤
        16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₂₂ + R₂')) := by
      rw [Nat.cast_mul, Nat.cast_mul]
      have hsub : ((M₁₀ * M₂₀ - 1 : ℕ) : ℝ) ≤ (M₁₀ : ℝ) * (M₂₀ : ℝ) := by
        exact_mod_cast Nat.sub_le (M₁₀ * M₂₀) 1
      calc ((M₁₀ * M₂₀ - 1 : ℕ) : ℝ) * (M₂₂ : ℝ) * (L₂ : ℝ)
        _ ≤ (M₁₀ : ℝ) * (M₂₀ : ℝ) * (M₂₂ : ℝ) * (L₂ : ℝ) := by gcongr
        _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * R₁₀)) * (2 * (2 : ℝ) ^ ((n : ℝ) * R₂₀)) *
            (2 * (2 : ℝ) ^ ((n : ℝ) * R₂₂)) * (2 * (2 : ℝ) ^ ((n : ℝ) * R₂')) := by
            have h1 := mc_ceil_two_rpow_le_two_mul n h10
            have h2 := mc_ceil_two_rpow_le_two_mul n h20
            have h3 := mc_ceil_two_rpow_le_two_mul n h22
            have h4 := mc_ceil_two_rpow_le_two_mul n h2'
            gcongr
        _ = 16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₂₂ + R₂')) := by
            have hpow : (2 : ℝ) ^ ((n : ℝ) * R₁₀) * (2 : ℝ) ^ ((n : ℝ) * R₂₀) *
                (2 : ℝ) ^ ((n : ℝ) * R₂₂) * (2 : ℝ) ^ ((n : ℝ) * R₂') =
                (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₂₂ + R₂')) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                  ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                  ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 1; ring
            linarith only [hpow]
    have h34 : 3 * ε_d ≤ 4 * ε_d := by
      have hnn : 0 ≤ ε_d := by dsimp [ε_d]; positivity
      linarith only [hnn]
    have hexp : (n : ℝ) * (R₁₀ + R₂₀ + R₂₂ + R₂') + -((n : ℝ) * (IWV_Y2 - 3 * ε_d)) ≤ -((n : ℝ) * (gap / 2)) := by
      nlinarith only [hn_r, hgap4, hε_d_eq, h34]
    calc _ ≤ 16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₂₂ + R₂')) *
            (2 : ℝ) ^ (-((n : ℝ) * (IWV_Y2 - 3 * ε_d))) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = 16 * (2 : ℝ) ^ ((n : ℝ) * (R₁₀ + R₂₀ + R₂₂ + R₂') + -((n : ℝ) * (IWV_Y2 - 3 * ε_d))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 16 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by norm_num)
      _ ≤ δ / 8 := by linarith only [hdecay, hδ]
  linarith only [hbound, hb_cov, hb_mk, hb_p1, hb_p2, hb_p3, hb_p4, hδ]

/-- **Marton's Coding Achievability Theorem** (Marton 1979; El Gamal–Kim Thm. 8.3):
    for any two-receiver DMBC `W`, any finite auxiliaries `W_aux, U, V`, and any single-letter
    joint distribution `Pwuvx : ProbDist (W_aux × U × V × X)`, every rate pair `(R₁, R₂) ≥ 0`
    strictly inside the Marton pentagon is operationally achievable (`IsBCAchievable W R₁ R₂`). -/
theorem marton_coding_achievability (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) {R₁ R₂ : ℝ}
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (h1 : R₁ < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1), z.2.1))))
    (h2 : R₂ < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))))
    (h3 : R₁ + R₂ < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1), z.2.1))) +
      condMutualInfo ((martonJoint W Pwuvx).map (fun z => (z.1.2.2.1, z.2.2, z.1.1))) -
      condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1))))
    (h4 : R₁ + R₂ < condMutualInfo ((martonJoint W Pwuvx).map (fun z => (z.1.2.1, z.2.1, z.1.1))) +
      mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) -
      condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1)))) :
    IsBCAchievable W R₁ R₂ := by
  let J := martonJoint W Pwuvx
  let a₁ := mutualInfo (J.map (fun z => (z.1.1, z.2.1)))
  let a₂ := mutualInfo (J.map (fun z => (z.1.1, z.2.2)))
  let b₁ := condMutualInfo (J.map (fun z => (z.1.2.1, z.2.1, z.1.1)))
  let b₂ := condMutualInfo (J.map (fun z => (z.1.2.2.1, z.2.2, z.1.1)))
  let c := condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1)))
  have hchain1 : a₁ + b₁ = mutualInfo (J.map (fun z => ((z.1.1, z.1.2.1), z.2.1))) := by
    have h := mc_mutualInfo_chain_rule (J.map (fun z => (z.1.1, z.1.2.1, z.2.1)))
    simpa [a₁, b₁, map_comp_eq, Function.comp_def] using h
  have hchain2 : a₂ + b₂ = mutualInfo (J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) := by
    have h := mc_mutualInfo_chain_rule (J.map (fun z => (z.1.1, z.1.2.2.1, z.2.2)))
    simpa [a₂, b₂, map_comp_eq, Function.comp_def] using h
  by_cases hbc : c < b₁ + b₂
  · obtain ⟨R₁₀, R₁₁, R₂₀, R₂₂, R₁', R₂', h10, h11, h20, h22, h1', h2', hs1, hs2, hcov, hp1, hp2, hp3, hp4⟩ :=
      marton_rate_splitting (mutualInfo_nonneg _) (mutualInfo_nonneg _) (condMutualInfo_nonneg _)
        (condMutualInfo_nonneg _) (condMutualInfo_nonneg _) hbc hR₁0 hR₂0
        (hchain1.symm ▸ h1) (hchain2.symm ▸ h2)
        (by linarith [hchain1]) (by linarith [hchain2])
    exact marton_achievable_of_split W Pwuvx hR₁0 hR₂0 h10 h11 h20 h22 h1' h2' hs1 hs2
      (Or.inl hcov) hp1 hp2 (hchain1 ▸ hp3) (hchain2 ▸ hp4)
  · push Not at hbc
    have hR_lt1 : R₁ + R₂ < a₁ := by linarith
    have hR_lt2 : R₁ + R₂ < a₂ := by linarith
    let P' : ProbDist (W_aux × Unit × Unit × X) := Pwuvx.map (fun t => (t.1, (), (), t.2.2.2))
    have hJ'_marg : ∀ (y : Y₁ × Y₂) (w : W_aux),
        ∑ x : X, (martonJoint W P').pmf ((w, (), (), x), y) =
        ∑ u : U, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), y) := fun y w => by
      classical
      have hP' : ∀ x : X, P'.pmf (w, (), (), x) = ∑ u : U, ∑ v : V, Pwuvx.pmf (w, u, v, x) := fun x => by
        unfold P' ProbDist.map; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
        · rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_eq_single x]
          · simp
          · intro x' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro w' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun _ _ => by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      unfold martonJoint J; dsimp only
      simp_rw [hP', Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      rfl
    have hJ'1 : (martonJoint W P').map (fun z => (z.1.1, z.2.1)) = J.map (fun z => (z.1.1, z.2.1)) := by
      classical
      apply mc_probDist_ext; rintro ⟨w, y₁⟩
      unfold ProbDist.map; dsimp only
      have hl : (∑ t : W_aux × Unit × Unit × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.1) = (w, y₁) then (martonJoint W P').pmf (t, y) else 0) =
          ∑ y₂ : Y₂, ∑ x : X, (martonJoint W P').pmf ((w, (), (), x), (y₁, y₂)) := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
        · rw [Fintype.sum_prod_type]; simp only [Fintype.sum_unique, PUnit.default_eq_unit]
          rw [Fintype.sum_prod_type]; simp only [Fintype.sum_unique, PUnit.default_eq_unit]
          rw [Finset.sum_comm]
          rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
          · simp
          · intro y₁' _ hne; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro w' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun _ _ => by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
              Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hr : (∑ t : W_aux × U × V × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.1) = (w, y₁) then J.pmf (t, y) else 0) =
          ∑ y₂ : Y₂, ∑ u : U, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
        · trans (∑ u : U, ∑ v : V, ∑ x : X, ∑ y₂ : Y₂, J.pmf ((w, u, v, x), (y₁, y₂)))
          · rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun v _ => ?_
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
            · simp
            · intro y₁' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · calc (∑ u : U, ∑ v : V, ∑ x : X, ∑ y₂ : Y₂, J.pmf ((w, u, v, x), (y₁, y₂)))
              _ = ∑ u : U, ∑ v : V, ∑ y₂ : Y₂, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) :=
                  Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_comm
              _ = ∑ u : U, ∑ y₂ : Y₂, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) :=
                  Finset.sum_congr rfl fun u _ => Finset.sum_comm
              _ = ∑ y₂ : Y₂, ∑ u : U, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) :=
                  Finset.sum_comm
        · intro w' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun _ _ => by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
              Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hmain : (∑ t : W_aux × Unit × Unit × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.1) = (w, y₁) then (martonJoint W P').pmf (t, y) else 0) =
          ∑ t : W_aux × U × V × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.1) = (w, y₁) then J.pmf (t, y) else 0 := by
        rw [hl, hr]
        exact Finset.sum_congr rfl fun y₂ _ => hJ'_marg (y₁, y₂) w
      rw [Fintype.sum_prod_type]
      conv_rhs => rw [Fintype.sum_prod_type]
      dsimp only
      convert hmain
    have hJ'2 : (martonJoint W P').map (fun z => (z.1.1, z.2.2)) = J.map (fun z => (z.1.1, z.2.2)) := by
      classical
      apply mc_probDist_ext; rintro ⟨w, y₂⟩
      unfold ProbDist.map; dsimp only
      have hl : (∑ t : W_aux × Unit × Unit × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.2) = (w, y₂) then (martonJoint W P').pmf (t, y) else 0) =
          ∑ y₁ : Y₁, ∑ x : X, (martonJoint W P').pmf ((w, (), (), x), (y₁, y₂)) := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
        · rw [Fintype.sum_prod_type]; simp only [Fintype.sum_unique, PUnit.default_eq_unit]
          rw [Fintype.sum_prod_type]; simp only [Fintype.sum_unique, PUnit.default_eq_unit]
          rw [Finset.sum_comm]
          rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y₂]
          · simp
          · intro y₂' _ hne; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro w' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun _ _ => by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
              Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hr : (∑ t : W_aux × U × V × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.2) = (w, y₂) then J.pmf (t, y) else 0) =
          ∑ y₁ : Y₁, ∑ u : U, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single w]
        · trans (∑ u : U, ∑ v : V, ∑ x : X, ∑ y₁ : Y₁, J.pmf ((w, u, v, x), (y₁, y₂)))
          · rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun v _ => ?_
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y₂]
            · simp
            · intro y₂' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · calc (∑ u : U, ∑ v : V, ∑ x : X, ∑ y₁ : Y₁, J.pmf ((w, u, v, x), (y₁, y₂)))
              _ = ∑ u : U, ∑ v : V, ∑ y₁ : Y₁, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) :=
                  Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_comm
              _ = ∑ u : U, ∑ y₁ : Y₁, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) :=
                  Finset.sum_congr rfl fun u _ => Finset.sum_comm
              _ = ∑ y₁ : Y₁, ∑ u : U, ∑ v : V, ∑ x : X, J.pmf ((w, u, v, x), (y₁, y₂)) :=
                  Finset.sum_comm
        · intro w' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun _ _ => by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
              Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hmain : (∑ t : W_aux × Unit × Unit × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.2) = (w, y₂) then (martonJoint W P').pmf (t, y) else 0) =
          ∑ t : W_aux × U × V × X, ∑ y : Y₁ × Y₂,
            if (t.1, y.2) = (w, y₂) then J.pmf (t, y) else 0 := by
        rw [hl, hr]
        exact Finset.sum_congr rfl fun y₁ _ => hJ'_marg (y₁, y₂) w
      rw [Fintype.sum_prod_type]
      conv_rhs => rw [Fintype.sum_prod_type]
      dsimp only
      convert hmain
    have hMI1' : mutualInfo ((martonJoint W P').map (fun z => ((z.1.1, z.1.2.1), z.2.1))) = a₁ := by
      have hch := mc_mutualInfo_chain_rule ((martonJoint W P').map (fun z => (z.1.1, z.1.2.1, z.2.1)))
      have hc0 : condMutualInfo (((martonJoint W P').map (fun z => (z.1.1, z.1.2.1, z.2.1))).map
          (fun t => (t.2.1, t.2.2, t.1))) = 0 := mc_condMutualInfo_unit _
      rw [hc0, add_zero] at hch
      have hl : ((martonJoint W P').map (fun z => (z.1.1, z.1.2.1, z.2.1))).map (fun t => (t.1, t.2.2)) =
          J.map (fun z => (z.1.1, z.2.1)) := by rw [map_comp_eq]; exact hJ'1
      have hr : ((martonJoint W P').map (fun z => (z.1.1, z.1.2.1, z.2.1))).map (fun t => ((t.1, t.2.1), t.2.2)) =
          (martonJoint W P').map (fun z => ((z.1.1, z.1.2.1), z.2.1)) := by rw [map_comp_eq]; rfl
      rw [hl, hr] at hch
      exact hch.symm
    have hMI2' : mutualInfo ((martonJoint W P').map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) = a₂ := by
      have hch := mc_mutualInfo_chain_rule ((martonJoint W P').map (fun z => (z.1.1, z.1.2.2.1, z.2.2)))
      have hc0 : condMutualInfo (((martonJoint W P').map (fun z => (z.1.1, z.1.2.2.1, z.2.2))).map
          (fun t => (t.2.1, t.2.2, t.1))) = 0 := mc_condMutualInfo_unit _
      rw [hc0, add_zero] at hch
      have hl : ((martonJoint W P').map (fun z => (z.1.1, z.1.2.2.1, z.2.2))).map (fun t => (t.1, t.2.2)) =
          J.map (fun z => (z.1.1, z.2.2)) := by rw [map_comp_eq]; exact hJ'2
      have hr : ((martonJoint W P').map (fun z => (z.1.1, z.1.2.2.1, z.2.2))).map (fun t => ((t.1, t.2.1), t.2.2)) =
          (martonJoint W P').map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)) := by rw [map_comp_eq]; rfl
      rw [hl, hr] at hch
      exact hch.symm
    exact marton_achievable_of_split W P' hR₁0 hR₂0 hR₁0 le_rfl hR₂0 le_rfl le_rfl le_rfl
      (add_zero R₁) (add_zero R₂) (Or.inr ⟨rfl, rfl, mc_condMutualInfo_unit _⟩)
      (Or.inl rfl) (Or.inl rfl) (by linarith [hMI1']) (by linarith [hMI2'])

/-- Zero rate pair `(0, 0)` is achievable over any DMBC on a nonempty input alphabet. -/
private lemma mc_isBCAchievable_zero_zero [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    IsBCAchievable W 0 0 := by
  refine ⟨le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  have h1 : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  rw [h1]
  refine ⟨fun _ _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0, ?_⟩
  have hzero : ((1 : ℝ) / ((1 * 1 : ℕ) : ℝ)) *
      ∑ m₁ : Fin 1, ∑ m₂ : Fin 1, ∑ y : Fin n → Y₁ × Y₂,
        (if (0 : Fin 1) ≠ m₁ ∨ (0 : Fin 1) ≠ m₂ then (W.power n).trans (fun _ => Classical.arbitrary X) y else 0) = 0 :=
    mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ =>
      Finset.sum_eq_zero fun y _ => by
        have hm1 : m₁ = 0 := Subsingleton.elim _ _
        have hm2 : m₂ = 0 := Subsingleton.elim _ _
        simp [hm1, hm2])
  linarith

/-- Axis achievability `(R₁, 0)` whenever `0 ≤ R₁ < I(X; Y₁)` via `dmc_achievable_lt_mutualInfo`. -/
private lemma mc_isBCAchievable_axis1 (W : BroadcastChannel X Y₁ Y₂)
    (Px : ProbDist X) {R₁ : ℝ} (hR₁0 : 0 ≤ R₁) (hR₁ : R₁ < (bcMarginal1 W).mutualInfo Px) :
    IsBCAchievable W R₁ 0 := by
  classical
  refine ⟨hR₁0, le_rfl, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := dmc_achievable_lt_mutualInfo (bcMarginal1 W) Px hR₁0 hR₁ hε
  refine ⟨N, fun n hn => ?_⟩
  dsimp only
  have hM2 : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  rw [hM2]
  obtain ⟨enc₁, dec₁, herr⟩ := hN n hn
  refine ⟨fun m₁ _ => enc₁ m₁, dec₁, fun _ => 0, ?_⟩
  have hM1 : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) :=
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have heq : ((1 : ℝ) / ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) * 1 : ℕ) : ℝ)) *
        ∑ m₁ : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))), ∑ m₂ : Fin 1, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ (0 : Fin 1) ≠ m₂ then (W.power n).trans (enc₁ m₁) y else 0) =
      dmcAvgError (bcMarginal1 W) n (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))) enc₁ dec₁ := by
    unfold dmcAvgError
    have hne : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) ≠ 0 := hM1.ne'
    simp only [hne, ↓reduceIte, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Fintype.sum_unique]
    have h0 : (0 : Fin 1) = default := Subsingleton.elim _ _
    simp only [← h0, ne_eq, not_true_eq_false, or_false]
    rw [mc_bc_sum_ite_fst_power W (enc₁ m₁) (fun y₁ => dec₁ y₁ ≠ m₁)]
    refine Finset.sum_congr rfl fun y₁ _ => by split_ifs <;> ring
  rw [heq]
  exact herr

/-- Axis achievability `(0, R₂)` whenever `0 ≤ R₂ < I(X; Y₂)` via `dmc_achievable_lt_mutualInfo`. -/
private lemma mc_isBCAchievable_axis2 (W : BroadcastChannel X Y₁ Y₂)
    (Px : ProbDist X) {R₂ : ℝ} (hR₂0 : 0 ≤ R₂) (hR₂ : R₂ < (bcMarginal2 W).mutualInfo Px) :
    IsBCAchievable W 0 R₂ := by
  classical
  refine ⟨le_rfl, hR₂0, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := dmc_achievable_lt_mutualInfo (bcMarginal2 W) Px hR₂0 hR₂ hε
  refine ⟨N, fun n hn => ?_⟩
  dsimp only
  have hM1 : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  rw [hM1]
  obtain ⟨enc₂, dec₂, herr⟩ := hN n hn
  refine ⟨fun _ m₂ => enc₂ m₂, fun _ => 0, dec₂, ?_⟩
  have hM2 : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) :=
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have heq : ((1 : ℝ) / ((1 * Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) : ℕ) : ℝ)) *
        ∑ m₁ : Fin 1, ∑ m₂ : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))), ∑ y : Fin n → Y₁ × Y₂,
          (if (0 : Fin 1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂ then (W.power n).trans (enc₂ m₂) y else 0) =
      dmcAvgError (bcMarginal2 W) n (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))) enc₂ dec₂ := by
    unfold dmcAvgError
    have hne : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) ≠ 0 := hM2.ne'
    simp only [hne, ↓reduceIte, one_mul]
    congr 1
    rw [Fintype.sum_unique]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    have h0 : (0 : Fin 1) = default := Subsingleton.elim _ _
    simp only [← h0, ne_eq, not_true_eq_false, false_or]
    rw [mc_bc_sum_ite_snd_power W (enc₂ m₂) (fun y₂ => dec₂ y₂ ≠ m₂)]
    refine Finset.sum_congr rfl fun y₂ _ => by split_ifs <;> ring
  rw [heq]
  exact herr

/-- Data processing inequality: `I(W, U; Y₁) ≤ I(X; Y₁)` and `I(W, V; Y₂) ≤ I(X; Y₂)`
    under the Markov chain `(W, U, V) — X — (Y₁, Y₂)`. -/
private lemma mc_marton_dpi_Y1 (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) :
    mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1), z.2.1))) ≤
      (bcMarginal1 W).mutualInfo (Pwuvx.map (fun t => t.2.2.2)) := by
  let J := martonJoint W Pwuvx
  let P_all_Y1 := (dmcPrecomp (bcMarginal1 W) (fun t : W_aux × U × V × X => t.2.2.2)).joint Pwuvx
  have h1 : J.map (fun z => (z.1, z.2.1)) = P_all_Y1 := by
    classical
    apply mc_probDist_ext; rintro ⟨t, y₁⟩
    unfold J P_all_Y1 ProbDist.map martonJoint DMC.joint dmcPrecomp bcMarginal1; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
      · simp [Finset.mul_sum]
      · intro y₁' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : J.map (fun z => ((z.1.1, z.1.2.1), z.2.1)) =
      P_all_Y1.map (Prod.map (fun t : W_aux × U × V × X => (t.1, t.2.1)) id) := by
    rw [← h1, map_comp_eq]; rfl
  rw [h2]
  have hdpi : mutualInfo (P_all_Y1.map (Prod.map (fun t : W_aux × U × V × X => (t.1, t.2.1)) id)) ≤
      mutualInfo P_all_Y1 := by
    rw [← mutualInfo_swap (P_all_Y1.map _), ← mutualInfo_swap P_all_Y1]
    have hm : (P_all_Y1.map (Prod.map (fun t : W_aux × U × V × X => (t.1, t.2.1)) id)).map Prod.swap =
        (P_all_Y1.map Prod.swap).map (Prod.map id (fun t : W_aux × U × V × X => (t.1, t.2.1))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [hm]
    exact mutualInfo_map_right_le (P_all_Y1.map Prod.swap) (fun t : W_aux × U × V × X => (t.1, t.2.1))
  have hpre := dmcPrecomp_mutualInfo_eq (bcMarginal1 W) Pwuvx (fun t : W_aux × U × V × X => t.2.2.2)
  exact le_trans hdpi (le_of_eq hpre)

private lemma mc_marton_dpi_Y2 (W : BroadcastChannel X Y₁ Y₂)
    (Pwuvx : ProbDist (W_aux × U × V × X)) :
    mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) ≤
      (bcMarginal2 W).mutualInfo (Pwuvx.map (fun t => t.2.2.2)) := by
  let J := martonJoint W Pwuvx
  let P_all_Y2 := (dmcPrecomp (bcMarginal2 W) (fun t : W_aux × U × V × X => t.2.2.2)).joint Pwuvx
  have h1 : J.map (fun z => (z.1, z.2.2)) = P_all_Y2 := by
    classical
    apply mc_probDist_ext; rintro ⟨t, y₂⟩
    unfold J P_all_Y2 ProbDist.map martonJoint DMC.joint dmcPrecomp bcMarginal2; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
    · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y₂]
      · simp [Finset.mul_sum]
      · intro y₂' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : J.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)) =
      P_all_Y2.map (Prod.map (fun t : W_aux × U × V × X => (t.1, t.2.2.1)) id) := by
    rw [← h1, map_comp_eq]; rfl
  rw [h2]
  have hdpi : mutualInfo (P_all_Y2.map (Prod.map (fun t : W_aux × U × V × X => (t.1, t.2.2.1)) id)) ≤
      mutualInfo P_all_Y2 := by
    rw [← mutualInfo_swap (P_all_Y2.map _), ← mutualInfo_swap P_all_Y2]
    have hm : (P_all_Y2.map (Prod.map (fun t : W_aux × U × V × X => (t.1, t.2.2.1)) id)).map Prod.swap =
        (P_all_Y2.map Prod.swap).map (Prod.map id (fun t : W_aux × U × V × X => (t.1, t.2.2.1))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [hm]
    exact mutualInfo_map_right_le (P_all_Y2.map Prod.swap) (fun t : W_aux × U × V × X => (t.1, t.2.2.1))
  have hpre := dmcPrecomp_mutualInfo_eq (bcMarginal2 W) Pwuvx (fun t : W_aux × U × V × X => t.2.2.2)
  exact le_trans hdpi (le_of_eq hpre)

/-- **Marton's Inner Bound Theorem** (Marton 1979; El Gamal–Kim Prop. 8.1 & Thm. 8.3):
    for every two-receiver Discrete Memoryless Broadcast Channel `W`, Marton's full
    single-letter inner bound with common auxiliary `W` is contained in the operational
    broadcast capacity region: `martonInnerBound W ⊆ bcCapacityRegion W`. -/
theorem martonInnerBound_subset_bcCapacityRegion (W : BroadcastChannel X Y₁ Y₂) :
    martonInnerBound W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ isClosed_closure
  rintro ⟨R₁, R₂⟩ ⟨hR₁0, hR₂0, kW, kU, kV, Pwuvx, h1, h2, h3, h4⟩
  have hne : Nonempty (Fin kW × Fin kU × Fin kV × X) := mc_nonempty_of_probDist Pwuvx
  have : Nonempty X := ⟨hne.some.2.2.2⟩
  unfold bcCapacityRegion
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hR₁0.eq_or_lt with rfl | hR₁pos
  · rcases hR₂0.eq_or_lt with rfl | hR₂pos
    · exact ⟨(0, 0), mc_isBCAchievable_zero_zero W, by simp [hε]⟩
    · let lam : ℝ := max 0 (1 - ε / (2 * R₂))
      have hlam0 : 0 ≤ lam := le_max_left _ _
      have hlam1 : lam < 1 := max_lt zero_lt_one (sub_lt_self 1 (by positivity))
      have hR₂'_lt : lam * R₂ < (bcMarginal2 W).mutualInfo (Pwuvx.map (fun t => t.2.2.2)) :=
        lt_of_lt_of_le (by nlinarith) (le_trans h2 (mc_marton_dpi_Y2 W Pwuvx))
      refine ⟨(0, lam * R₂), mc_isBCAchievable_axis2 W _ (mul_nonneg hlam0 hR₂pos.le) hR₂'_lt, ?_⟩
      rw [dist_comm, Prod.dist_eq]
      have hdist2 : dist (lam * R₂) R₂ < ε := by
        rw [Real.dist_eq, abs_of_nonpos (by nlinarith)]
        have h1' : 1 - ε / (2 * R₂) ≤ lam := le_max_right _ _
        have h2' : (1 - lam) * R₂ ≤ (ε / (2 * R₂)) * R₂ := mul_le_mul_of_nonneg_right (by linarith) hR₂pos.le
        have h3' : (ε / (2 * R₂)) * R₂ = ε / 2 := by field_simp [hR₂pos.ne']
        linarith
      simpa using max_lt hε hdist2
  · rcases hR₂0.eq_or_lt with rfl | hR₂pos
    · let lam : ℝ := max 0 (1 - ε / (2 * R₁))
      have hlam0 : 0 ≤ lam := le_max_left _ _
      have hlam1 : lam < 1 := max_lt zero_lt_one (sub_lt_self 1 (by positivity))
      have hR₁'_lt : lam * R₁ < (bcMarginal1 W).mutualInfo (Pwuvx.map (fun t => t.2.2.2)) :=
        lt_of_lt_of_le (by nlinarith) (le_trans h1 (mc_marton_dpi_Y1 W Pwuvx))
      refine ⟨(lam * R₁, 0), mc_isBCAchievable_axis1 W _ (mul_nonneg hlam0 hR₁pos.le) hR₁'_lt, ?_⟩
      rw [dist_comm, Prod.dist_eq]
      have hdist1 : dist (lam * R₁) R₁ < ε := by
        rw [Real.dist_eq, abs_of_nonpos (by nlinarith)]
        have h1' : 1 - ε / (2 * R₁) ≤ lam := le_max_right _ _
        have h2' : (1 - lam) * R₁ ≤ (ε / (2 * R₁)) * R₁ := mul_le_mul_of_nonneg_right (by linarith) hR₁pos.le
        have h3' : (ε / (2 * R₁)) * R₁ = ε / 2 := by field_simp [hR₁pos.ne']
        linarith
      simpa using max_lt hdist1 hε
    · let lam : ℝ := max 0 (1 - ε / (2 * (R₁ + R₂)))
      have hlam0 : 0 ≤ lam := le_max_left _ _
      have hlam1 : lam < 1 := max_lt zero_lt_one (sub_lt_self 1 (by positivity))
      have hstrict1 : lam * R₁ < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1), z.2.1))) :=
        lt_of_lt_of_le (by nlinarith) h1
      have hstrict2 : lam * R₂ < mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) :=
        lt_of_lt_of_le (by nlinarith) h2
      have hstrict3 : lam * R₁ + lam * R₂ <
          mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.1), z.2.1))) +
          condMutualInfo ((martonJoint W Pwuvx).map (fun z => (z.1.2.2.1, z.2.2, z.1.1))) -
          condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1))) :=
        lt_of_lt_of_le (by nlinarith) h3
      have hstrict4 : lam * R₁ + lam * R₂ <
          condMutualInfo ((martonJoint W Pwuvx).map (fun z => (z.1.2.1, z.2.1, z.1.1))) +
          mutualInfo ((martonJoint W Pwuvx).map (fun z => ((z.1.1, z.1.2.2.1), z.2.2))) -
          condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1))) :=
        lt_of_lt_of_le (by nlinarith) h4
      refine ⟨(lam * R₁, lam * R₂),
        marton_coding_achievability W Pwuvx (mul_nonneg hlam0 hR₁pos.le) (mul_nonneg hlam0 hR₂pos.le)
          hstrict1 hstrict2 hstrict3 hstrict4, ?_⟩
      rw [dist_comm, Prod.dist_eq]
      have h1' : 1 - ε / (2 * (R₁ + R₂)) ≤ lam := le_max_right _ _
      have hsum_bd : (1 - lam) * (R₁ + R₂) ≤ ε / 2 := by
        have h2' : (1 - lam) * (R₁ + R₂) ≤ (ε / (2 * (R₁ + R₂))) * (R₁ + R₂) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have h3' : (ε / (2 * (R₁ + R₂))) * (R₁ + R₂) = ε / 2 := by
          have hpos : R₁ + R₂ ≠ 0 := by linarith
          field_simp [hpos]
        linarith
      have hd1 : dist (lam * R₁) R₁ < ε := by
        rw [Real.dist_eq, abs_of_nonpos (by nlinarith)]
        nlinarith
      have hd2 : dist (lam * R₂) R₂ < ε := by
        rw [Real.dist_eq, abs_of_nonpos (by nlinarith)]
        nlinarith
      exact max_lt hd1 hd2

end MartonAchievability

end InfoTheory.Bridge
