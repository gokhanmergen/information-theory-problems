import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability
import InfoTheory.Bridge.MrsGerber

/-!
# Broadcast Channel Coding: Superposition Coding, Degraded BC Capacity Region, and Operational Bergmans Theorem

Purely additive, kernel-verified formalization of the foundational theorems for two-receiver
Discrete Memoryless Broadcast Channels (`InfoTheory.BroadcastChannel`, `IsBCAchievable`,
`bcCapacityRegion`; Cover & Thomas §15.6; El Gamal–Kim Ch. 5):

1. **Superposition Coding Achievability Inner Bound** (Cover 1972; Cover & Thomas §15.6;
   El Gamal–Kim Thm. 5.1):
   - `bcMarginal1`, `bcMarginal2`, `bcAuxJoint`
   - `superpositionInnerBound`
   - `superposition_random_coding_bound` (random cloud-center + conditional satellite codebook
     with 2-way joint-typicality decoding at Receiver 2 and 3-way joint-typicality decoding at
     Receiver 1)
   - `superposition_coding_achievability` and `superpositionInnerBound_subset_bcCapacityRegion`

2. **Degraded Broadcast Channel Capacity Region Theorem** (Bergmans 1973; Gallager 1974;
   Cover & Thomas Thm. 15.6.2; El Gamal–Kim Thm. 5.2):
   - `IsPhysicallyDegradedBC`, `degradedBCRegion`
   - `superpositionInnerBound_eq_degradedBCRegion` (DPI `I(U; Y₂) ≤ I(U; Y₁)` collapses the
     sum-rate constraint)
   - `degradedBC_converse` (Fano's inequality + Gallager auxiliary `U_i = (M₂, Y₁^{<i})` +
     physical degradedness DPI + time-sharing)
   - `degradedBC_capacity_theorem`: `bcCapacityRegion W = degradedBCRegion W`

3. **Full Operational Bergmans Capacity Region for the Binary Symmetric Degraded BC**
   (Bergmans 1973; Wyner & Ziv 1973; Cover & Thomas §15.6.2):
   - `bergmansBSDBCRegion`, `degradedBSC_isPhysicallyDegraded`
   - `degradedBSC_operational_capacity_region`: upgrades `Bridge/MrsGerber.lean`'s
     single-letter Bergmans theorem to the full operational `bcCapacityRegion`.
-/

open scoped BigOperators Topology
open InfoTheory InfoTheory.Bridge Set Filter

namespace InfoTheory.Bridge

/-! ### 0. Shared Private Helper Lemmas -/

section BCHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma bc_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

private lemma bc_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma bc_probDist_map_id (P : ProbDist α) : P.map id = P := by
  classical
  apply bc_probDist_ext; intro a
  unfold ProbDist.map; simp

private lemma bc_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  apply bc_probDist_ext; intro a
  unfold ProbDist.map ProbDist.fst; dsimp only
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; exact Finset.sum_eq_zero fun b _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bc_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  apply bc_probDist_ext; intro b
  unfold ProbDist.map ProbDist.snd; dsimp only
  rw [Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne; exact Finset.sum_eq_zero fun a _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bc_shannonEntropy_map_eq_of_factors (P : ProbDist α)
    (f : α → β) (g : α → γ) (h₁ : β → γ) (h₂ : γ → β)
    (h12 : ∀ a, h₁ (f a) = g a) (h21 : ∀ a, h₂ (g a) = f a) :
    shannonEntropy (P.map f) = shannonEntropy (P.map g) := by
  have hg : P.map g = (P.map f).map h₁ := by
    rw [map_comp_eq]; congr 1; funext a; exact (h12 a).symm
  have hf : P.map f = (P.map g).map h₂ := by
    rw [map_comp_eq]; congr 1; funext a; exact (h21 a).symm
  exact le_antisymm (hf ▸ shannonEntropy_map_le h₂ (P.map g))
    (hg ▸ shannonEntropy_map_le h₁ (P.map f))

private lemma bc_exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
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

private lemma bc_sum_pi_prod_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ProbDist α) (i₀ : ι) (f : α → ℝ) :
    ∑ g : ι → α, (∏ i : ι, Q.pmf (g i)) * f (g i₀) = ∑ x : α, Q.pmf x * f x := by
  let F : ι → α → ℝ := fun i x => if i = i₀ then Q.pmf x * f x else Q.pmf x
  have hfun : ∀ g : ι → α,
      (∏ i : ι, Q.pmf (g i)) * f (g i₀) = ∏ i : ι, F i (g i) := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ (fun i => Q.pmf (g i)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase Finset.univ (fun i => F i (g i)) (Finset.mem_univ i₀)]
    have hrest : ∏ i ∈ Finset.univ.erase i₀, F i (g i) =
        ∏ i ∈ Finset.univ.erase i₀, Q.pmf (g i) :=
      Finset.prod_congr rfl fun i hi => by simp [F, (Finset.mem_erase.mp hi).1]
    rw [hrest]; simp only [F, ↓reduceIte]; ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x : α, F i x) (Finset.mem_univ i₀)]
  have hi₀ : ∑ x : α, F i₀ x = ∑ x : α, Q.pmf x * f x := by simp [F]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ∑ x : α, F i x = 1 :=
    Finset.prod_eq_one fun i hi => by
      simp only [F, (Finset.mem_erase.mp hi).1, ↓reduceIte]; exact Q.sum_one
  rw [hi₀, hrest, mul_one]

private lemma bc_sum_pi_prod_mul_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ProbDist α) (i₀ i₁ : ι) (hne : i₁ ≠ i₀) (f h : α → ℝ) :
    ∑ g : ι → α, (∏ i : ι, Q.pmf (g i)) * (f (g i₀) * h (g i₁)) =
      (∑ x : α, Q.pmf x * f x) * (∑ x' : α, Q.pmf x' * h x') := by
  let F : ι → α → ℝ := fun i x =>
    if i = i₀ then Q.pmf x * f x else if i = i₁ then Q.pmf x * h x else Q.pmf x
  have hi₁_mem : i₁ ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩
  have hfun : ∀ g : ι → α,
      (∏ i : ι, Q.pmf (g i)) * (f (g i₀) * h (g i₁)) = ∏ i : ι, F i (g i) := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ (fun i => Q.pmf (g i)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => Q.pmf (g i)) hi₁_mem,
        ← Finset.mul_prod_erase Finset.univ (fun i => F i (g i)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => F i (g i)) hi₁_mem]
    have hrest : ∏ i ∈ (Finset.univ.erase i₀).erase i₁, F i (g i) =
        ∏ i ∈ (Finset.univ.erase i₀).erase i₁, Q.pmf (g i) :=
      Finset.prod_congr rfl fun i hi => by
        have h1 : i ≠ i₁ := (Finset.mem_erase.mp hi).1
        have h2 : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [F, h1, h2]
    rw [hrest]; simp only [F, hne, ↓reduceIte]; ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x : α, F i x) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => ∑ x : α, F i x) hi₁_mem]
  have hi₀_sum : ∑ x : α, F i₀ x = ∑ x : α, Q.pmf x * f x := by simp [F]
  have hi₁_sum : ∑ x : α, F i₁ x = ∑ x : α, Q.pmf x * h x := by simp [F, hne]
  have hrest : ∏ i ∈ (Finset.univ.erase i₀).erase i₁, ∑ x : α, F i x = 1 :=
    Finset.prod_eq_one fun i hi => by
      have h1 : i ≠ i₁ := (Finset.mem_erase.mp hi).1
      have h2 : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp only [F, h1, h2, ↓reduceIte]; exact Q.sum_one
  rw [hi₀_sum, hi₁_sum, hrest, mul_one]

private lemma bc_two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
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

private lemma bc_max_one_floor_two_rpow_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
  have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hfl : 1 ≤ Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := Nat.le_floor (by exact_mod_cast hge1)
  change ((max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ _
  rw [max_eq_right hfl]
  exact Nat.floor_le (by positivity)

private lemma bc_sub_one_max_floor_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) - 1 : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ ((n : ℝ) * R) := by
  have hle : ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) - 1 : ℕ) : ℝ) ≤
      ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le _ 1)
  exact le_trans hle (bc_max_one_floor_two_rpow_le n hR)

private lemma bc_log2_two_rpow (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma bc_log2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma bc_iidDist_map_comp (P : ProbDist α) (n : ℕ) (g : α → γ) :
    (iidDist P n).map (fun z i => g (z i)) = iidDist (P.map g) n := by
  classical
  apply bc_probDist_ext; intro u
  unfold ProbDist.map iidDist; dsimp only
  trans (∑ z : Fin n → α, ∏ i : Fin n, if g (z i) = u i then P.pmf (z i) else 0)
  · refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : (fun i => g (z i)) = u
    · subst h; simp
    · simp only [h, ↓reduceIte]
      have hex : ∃ i : Fin n, g (z i) ≠ u i := by
        by_contra hall; push Not at hall; exact h (funext hall)
      obtain ⟨i, hi⟩ := hex
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  · refine (Fintype.prod_sum (fun i a => if g a = u i then P.pmf a else 0)).symm.trans ?_
    exact Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by
      by_cases h : g a = u i <;> simp [h]

private lemma bc_sum_not_mem_of_map [DecidableEq γ]
    (Q : ProbDist α) (f : α → γ) (S : Finset γ) (R : ProbDist γ) (hR : Q.map f = R) :
    (∑ t, if f t ∉ S then Q.pmf t else 0) = 1 - ∑ z ∈ S, R.pmf z := by
  classical
  have h1 := sum_pmf_mul_comp Q f (fun z => if z ∉ S then (1 : ℝ) else 0)
  rw [hR] at h1
  have hl : (∑ t, Q.pmf t * (if f t ∉ S then (1 : ℝ) else 0)) =
      ∑ t, if f t ∉ S then Q.pmf t else 0 := Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
  have hr : (∑ z, R.pmf z * (if z ∉ S then (1 : ℝ) else 0)) =
      ∑ z, if z ∉ S then R.pmf z else 0 := Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
  have hsplit : ∑ z, R.pmf z =
      (∑ z, if z ∈ S then R.pmf z else 0) + (∑ z, if z ∉ S then R.pmf z else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by by_cases h : z ∈ S <;> simp [h]
  rw [R.sum_one] at hsplit
  have hmem : (∑ z, if z ∈ S then R.pmf z else 0) = ∑ z ∈ S, R.pmf z := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  linarith

private lemma bc_estErrorProb_map_pair (Q : ProbDist γ) (h : γ → α) (k : γ → β) (g : β → α) :
    estErrorProb (Q.map (fun z => (h z, k z))) g =
      by classical exact ∑ z : γ, if g (k z) ≠ h z then Q.pmf z else 0 := by
  classical
  unfold estErrorProb
  have h1 := sum_pmf_mul_comp Q (fun z => (h z, k z))
    (fun ab : α × β => if g ab.2 ≠ ab.1 then (1 : ℝ) else 0)
  have h2 : ∑ z : γ, Q.pmf z * (if g (k z) ≠ h z then (1 : ℝ) else 0) =
      ∑ z : γ, if g (k z) ≠ h z then Q.pmf z else 0 :=
    Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
  have h3 : ∑ ab : α × β, (Q.map (fun z => (h z, k z))).pmf ab *
        (if g ab.2 ≠ ab.1 then (1 : ℝ) else 0) =
      ∑ ab : α × β, if g ab.2 ≠ ab.1 then (Q.map (fun z => (h z, k z))).pmf ab else 0 :=
    Finset.sum_congr rfl fun ab _ => by split_ifs <;> ring
  linarith

end BCHelpers

/-! ### 1. Broadcast Channel Marginals, Physical Degradedness & Single-Letter Regions -/

section BCDefinitions

variable {U X Y₁ Y₂ : Type*} [Fintype U] [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- Marginal DMC `p(y₁ | x) = ∑_{y₂} W(y₁, y₂ | x)` seen by Receiver 1 of a DMBC `W`. -/
def bcMarginal1 (W : BroadcastChannel X Y₁ Y₂) : DMC X Y₁ where
  trans := fun x y₁ => ∑ y₂ : Y₂, W.trans x (y₁, y₂)
  nonneg := fun x y₁ => Finset.sum_nonneg fun y₂ _ => W.nonneg x (y₁, y₂)
  sum_one := fun x => by rw [← Fintype.sum_prod_type']; exact W.sum_one x

/-- Marginal DMC `p(y₂ | x) = ∑_{y₁} W(y₁, y₂ | x)` seen by Receiver 2 of a DMBC `W`. -/
def bcMarginal2 (W : BroadcastChannel X Y₁ Y₂) : DMC X Y₂ where
  trans := fun x y₂ => ∑ y₁ : Y₁, W.trans x (y₁, y₂)
  nonneg := fun x y₂ => Finset.sum_nonneg fun y₁ _ => W.nonneg x (y₁, y₂)
  sum_one := fun x => by rw [Finset.sum_comm, ← Fintype.sum_prod_type']; exact W.sum_one x

/-- Joint distribution of `((U, X), (Y₁, Y₂))` forming the Markov chain `U — X — (Y₁, Y₂)`
    across a 2-receiver DMBC `W` with input law `Pux` on `U × X`. -/
def bcAuxJoint (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X)) :
    ProbDist ((U × X) × (Y₁ × Y₂)) where
  pmf := fun z => Pux.pmf z.1 * W.trans z.1.2 z.2
  nonneg := fun z => mul_nonneg (Pux.nonneg z.1) (W.nonneg z.1.2 z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, W.sum_one, mul_one, Pux.sum_one]

/-- A two-receiver DMBC `W(y₁, y₂ | x)` is **physically degraded** (`X — Y₁ — Y₂`) if there
    exists a DMC `K : DMC Y₁ Y₂` such that `W(y₁, y₂ | x) = W₁(y₁ | x) · K(y₂ | y₁)`. -/
def IsPhysicallyDegradedBC (W : BroadcastChannel X Y₁ Y₂) : Prop :=
  ∃ K : DMC Y₁ Y₂, ∀ x y₁ y₂,
    W.trans x (y₁, y₂) = (∑ y₂' : Y₂, W.trans x (y₁, y₂')) * K.trans y₁ y₂

/-- **Superposition Coding Inner Bound** for a 2-receiver DMBC `W`
    (Cover 1972; Cover & Thomas §15.6; El Gamal–Kim Thm. 5.1):
    closure of rate pairs `(R₁, R₂) ≥ 0` with `R₂ ≤ I(U; Y₂)`, `R₁ ≤ I(X; Y₁ | U)`, and
    `R₁ + R₂ ≤ I(X; Y₁)` for some auxiliary `U — X — (Y₁, Y₂)`. -/
def superpositionInnerBound (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU : ℕ) (Pux : ProbDist (Fin kU × X)),
      let J := bcAuxJoint W Pux
      r.2 ≤ mutualInfo (J.map (fun z => (z.1.1, z.2.2))) ∧
      r.1 ≤ condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) ∧
      r.1 + r.2 ≤ mutualInfo (J.map (fun z => (z.1.2, z.2.1))) }

/-- **Single-Letter Degraded Broadcast Channel Capacity Region**
    (Bergmans 1973; Gallager 1974; Cover & Thomas Thm. 15.6.2; El Gamal–Kim Thm. 5.2):
    closure of rate pairs `(R₁, R₂) ≥ 0` with `R₂ ≤ I(U; Y₂)` and `R₁ ≤ I(X; Y₁ | U)` for
    some auxiliary `U — X — (Y₁, Y₂)`. -/
def degradedBCRegion (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU : ℕ) (Pux : ProbDist (Fin kU × X)),
      let J := bcAuxJoint W Pux
      r.2 ≤ mutualInfo (J.map (fun z => (z.1.1, z.2.2))) ∧
      r.1 ≤ condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) }

private lemma bcMarginal1_power_trans (W : BroadcastChannel X Y₁ Y₂) {n : ℕ}
    (x : Fin n → X) (y₁ : Fin n → Y₁) :
    ((bcMarginal1 W).power n).trans x y₁ =
      ∑ y₂ : Fin n → Y₂, (W.power n).trans x (fun i => (y₁ i, y₂ i)) := by
  classical
  simp only [DMC.power, bcMarginal1]
  exact Fintype.prod_sum (fun i y₂ => W.trans (x i) (y₁ i, y₂))

private lemma bcMarginal2_power_trans (W : BroadcastChannel X Y₁ Y₂) {n : ℕ}
    (x : Fin n → X) (y₂ : Fin n → Y₂) :
    ((bcMarginal2 W).power n).trans x y₂ =
      ∑ y₁ : Fin n → Y₁, (W.power n).trans x (fun i => (y₁ i, y₂ i)) := by
  classical
  simp only [DMC.power, bcMarginal2]
  exact Fintype.prod_sum (fun i y₁ => W.trans (x i) (y₁, y₂ i))

private lemma bc_sum_tuple_pair_split {n : ℕ} (F : (Fin n → Y₁ × Y₂) → ℝ) :
    ∑ y : Fin n → Y₁ × Y₂, F y =
      ∑ y₁ : Fin n → Y₁, ∑ y₂ : Fin n → Y₂, F (fun i => (y₁ i, y₂ i)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (zipEquiv Y₁ Y₂ n) (fun p => F (fun i => (p.1 i, p.2 i))) F
    (fun _ => rfl)).symm

private lemma bc_sum_ite_fst_power (W : BroadcastChannel X Y₁ Y₂) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → Y₁) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂, (if p (fun i => (y i).1) then (W.power n).trans x y else 0) =
      ∑ y₁ : Fin n → Y₁, if p y₁ then ((bcMarginal1 W).power n).trans x y₁ else 0 := by
  rw [bc_sum_tuple_pair_split]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [bcMarginal1_power_trans]
  show ∑ y₂ : Fin n → Y₂, (if p y₁ then (W.power n).trans x (fun i => (y₁ i, y₂ i)) else 0) = _
  split_ifs <;> simp

private lemma bc_sum_ite_snd_power (W : BroadcastChannel X Y₁ Y₂) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → Y₂) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂, (if p (fun i => (y i).2) then (W.power n).trans x y else 0) =
      ∑ y₂ : Fin n → Y₂, if p y₂ then ((bcMarginal2 W).power n).trans x y₂ else 0 := by
  rw [bc_sum_tuple_pair_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₂ _ => ?_
  rw [bcMarginal2_power_trans]
  show ∑ y₁ : Fin n → Y₁, (if p y₂ then (W.power n).trans x (fun i => (y₁ i, y₂ i)) else 0) = _
  split_ifs <;> simp

private lemma bcAuxJoint_map_UXY1 (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X)) :
    (bcAuxJoint W Pux).map (fun z => (z.1, z.2.1)) =
      (dmcPrecomp (bcMarginal1 W) Prod.snd).joint Pux := by
  classical
  apply bc_probDist_ext; rintro ⟨⟨u, x⟩, y₁⟩
  unfold ProbDist.map bcAuxJoint DMC.joint dmcPrecomp bcMarginal1; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (u, x)]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
    · simp [Finset.mul_sum]
    · intro y₁' _ hne; exact Finset.sum_eq_zero fun y₂ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro ux' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bcAuxJoint_map_XY1 (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X)) :
    (bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1)) =
      (bcMarginal1 W).joint Pux.snd := by
  classical
  apply bc_probDist_ext; rintro ⟨x, y₁⟩
  unfold ProbDist.map bcAuxJoint DMC.joint ProbDist.snd bcMarginal1; dsimp only
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type_right, Finset.sum_eq_single x]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
    · simp [Finset.mul_sum]
    · intro y₁' _ hne; exact Finset.sum_eq_zero fun y₂ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro x' _ hne; exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun y _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bcAuxJoint_map_UY1_pmf (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (u : U) (y₁ : Y₁) :
    ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))).pmf (u, y₁) =
      ∑ x : X, Pux.pmf (u, x) * (bcMarginal1 W).trans x y₁ := by
  classical
  unfold ProbDist.map bcAuxJoint bcMarginal1; dsimp only
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single u]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
    · simp [Finset.mul_sum]
    · intro y₁' _ hne; exact Finset.sum_eq_zero fun y₂ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro u' _ hne; exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bcAuxJoint_map_UY2_pmf (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (u : U) (y₂ : Y₂) :
    ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))).pmf (u, y₂) =
      ∑ x : X, Pux.pmf (u, x) * (bcMarginal2 W).trans x y₂ := by
  classical
  unfold ProbDist.map bcAuxJoint bcMarginal2; dsimp only
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single u]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y₂]
    · simp [Finset.mul_sum]
    · intro y₂' _ hne; exact Finset.sum_eq_zero fun y₁ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro u' _ hne; exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Markov chain `U — X — Y₁` implies `I(U, X; Y₁) = I(X; Y₁)`. -/
private lemma bcAuxJoint_mutualInfo_UX_Y1_eq (W : BroadcastChannel X Y₁ Y₂)
    (Pux : ProbDist (U × X)) :
    mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1, z.2.1))) =
      mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1))) := by
  rw [bcAuxJoint_map_UXY1, bcAuxJoint_map_XY1]
  have h := dmcPrecomp_mutualInfo_eq (bcMarginal1 W) Pux Prod.snd
  rwa [bc_probDist_map_snd] at h

/-- Chain rule `I(U; Y₁) + I(X; Y₁ | U) = I(X; Y₁)` for `U — X — (Y₁, Y₂)`. -/
private lemma bcAuxJoint_chain_Y1 (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X)) :
    mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))) +
      condMutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1, z.1.1))) =
    mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1))) := by
  rw [← bcAuxJoint_mutualInfo_UX_Y1_eq]
  set J := bcAuxJoint W Pux
  have h1 : (J.map (fun z => (z.1.1, z.2.1))).fst = J.map (fun z => z.1.1) := by
    rw [← bc_probDist_map_fst, map_comp_eq]; rfl
  have h2 : (J.map (fun z => (z.1.1, z.2.1))).snd = J.map (fun z => z.2.1) := by
    rw [← bc_probDist_map_snd, map_comp_eq]; rfl
  have h3 : (J.map (fun z => (z.1, z.2.1))).fst = J.map (fun z => z.1) := by
    rw [← bc_probDist_map_fst, map_comp_eq]; rfl
  have h4 : (J.map (fun z => (z.1, z.2.1))).snd = J.map (fun z => z.2.1) := by
    rw [← bc_probDist_map_snd, map_comp_eq]; rfl
  have h5 : (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.1, t.2.2)) =
      (J.map (fun z => z.1)).map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h6 : (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.2.1, t.2.2)) =
      (J.map (fun z => (z.1.1, z.2.1))).map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h7 : (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => t.2.2) =
      J.map (fun z => z.1.1) := by
    rw [map_comp_eq]; rfl
  let e : ((U × X) × Y₁) ≃ (X × Y₁ × U) :=
    { toFun := fun t => (t.1.2, t.2, t.1.1)
      invFun := fun t => ((t.2.2, t.1), t.2.1)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have h8 : J.map (fun z => (z.1.2, z.2.1, z.1.1)) = (J.map (fun z => (z.1, z.2.1))).map e := by
    rw [map_comp_eq]; rfl
  unfold mutualInfo condMutualInfo; dsimp only
  rw [h1, h2, h3, h4, h5, h6, h7, h8,
      shannonEntropy_swap, shannonEntropy_swap, shannonEntropy_map_equiv e]
  ring

/-- Data Processing Inequality for physically degraded BCs: `I(U; Y₂) ≤ I(U; Y₁)`. -/
private lemma bcAuxJoint_dpi_U_Y2_le (W : BroadcastChannel X Y₁ Y₂)
    (hdeg : IsPhysicallyDegradedBC W) (Pux : ProbDist (U × X)) :
    mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))) ≤
      mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))) := by
  obtain ⟨K, hK⟩ := hdeg
  have heq : (bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2)) =
      ((dmcLiftRight (α := U) K).joint ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1)))).snd := by
    classical
    apply bc_probDist_ext; rintro ⟨u, y₂⟩
    rw [bcAuxJoint_map_UY2_pmf]
    unfold ProbDist.snd DMC.joint dmcLiftRight; dsimp only
    rw [Fintype.sum_prod_type]
    have hinner : ∀ u' : U, ∑ y₁ : Y₁,
        ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))).pmf (u', y₁) *
          (if u' = u then K.trans y₁ y₂ else 0) =
        if u' = u then ∑ y₁ : Y₁,
          ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))).pmf (u, y₁) * K.trans y₁ y₂ else 0 := by
      intro u'
      by_cases hu : u' = u
      · subst hu; simp
      · simp [hu]
    simp_rw [hinner]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp_rw [bcAuxJoint_map_UY1_pmf, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold bcMarginal2 bcMarginal1; dsimp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    rw [hK x y₁ y₂]; ring
  rw [heq]
  exact mutualInfo_channel_right_le _ K

/-- Relabeling the auxiliary variable `U` along a bijection preserves all BC information quantities. -/
private lemma bcAuxJoint_relabel {U' : Type*} [Fintype U']
    (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X)) (e : U ≃ U') :
    let Pux' : ProbDist (U' × X) := Pux.map (fun ux => (e ux.1, ux.2))
    let J := bcAuxJoint W Pux
    let J' := bcAuxJoint W Pux'
    mutualInfo (J'.map (fun z => (z.1.1, z.2.2))) = mutualInfo (J.map (fun z => (z.1.1, z.2.2))) ∧
    condMutualInfo (J'.map (fun z => (z.1.2, z.2.1, z.1.1))) =
      condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) ∧
    mutualInfo (J'.map (fun z => (z.1.2, z.2.1))) =
      mutualInfo (J.map (fun z => (z.1.2, z.2.1))) := by
  classical
  intro Pux' J J'
  let eAll : ((U × X) × (Y₁ × Y₂)) ≃ ((U' × X) × (Y₁ × Y₂)) :=
    (e.prodCongr (Equiv.refl X)).prodCongr (Equiv.refl (Y₁ × Y₂))
  have hJ' : J' = J.map eAll := by
    apply bc_probDist_ext; rintro ⟨⟨u', x⟩, y⟩
    unfold J' J Pux' bcAuxJoint ProbDist.map; dsimp only
    rw [Finset.sum_eq_single ((e.symm u', x), y)]
    · simp only [eAll, Equiv.prodCongr_apply, Prod.map_apply, Equiv.apply_symm_apply,
        Equiv.refl_apply, ↓reduceIte]
      rw [Finset.sum_eq_single (e.symm u', x)]
      · simp
      · intro ux' _ hne
        have : (e ux'.1, ux'.2) ≠ (u', x) := fun h => hne (by
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          exact Prod.ext (e.symm_apply_eq.mpr h1.symm).symm h2)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro z _ hne
      have : eAll z ≠ ((u', x), y) := fun h => hne (eAll.symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨?_, ?_, ?_⟩
  · have hm : J'.map (fun z => (z.1.1, z.2.2)) =
        (J.map (fun z => (z.1.1, z.2.2))).map (e.prodCongr (Equiv.refl Y₂)) := by
      rw [hJ', map_comp_eq, map_comp_eq]; rfl
    rw [hm]
    have hfst : ((J.map (fun z => (z.1.1, z.2.2))).map (e.prodCongr (Equiv.refl Y₂))).fst =
        (J.map (fun z => (z.1.1, z.2.2))).fst.map e := by
      rw [← bc_probDist_map_fst, ← bc_probDist_map_fst, map_comp_eq, map_comp_eq, map_comp_eq,
          map_comp_eq]; rfl
    have hsnd : ((J.map (fun z => (z.1.1, z.2.2))).map (e.prodCongr (Equiv.refl Y₂))).snd =
        (J.map (fun z => (z.1.1, z.2.2))).snd := by
      rw [← bc_probDist_map_snd, ← bc_probDist_map_snd, map_comp_eq]; rfl
    unfold mutualInfo
    rw [hfst, hsnd, shannonEntropy_map_equiv e, shannonEntropy_map_equiv (e.prodCongr (Equiv.refl Y₂))]
  · have h3 : J'.map (fun z => (z.1.2, z.2.1, z.1.1)) =
        (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map ((Equiv.refl X).prodCongr ((Equiv.refl Y₁).prodCongr e)) := by
      rw [hJ', map_comp_eq, map_comp_eq]; rfl
    rw [h3]
    set Q := J.map (fun z => (z.1.2, z.2.1, z.1.1))
    let e3 : (X × Y₁ × U) ≃ (X × Y₁ × U') := (Equiv.refl X).prodCongr ((Equiv.refl Y₁).prodCongr e)
    have hxz : (Q.map e3).map (fun t => (t.1, t.2.2)) =
        (Q.map (fun t => (t.1, t.2.2))).map ((Equiv.refl X).prodCongr e) := by
      rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
    have hyz : (Q.map e3).map (fun t => (t.2.1, t.2.2)) =
        (Q.map (fun t => (t.2.1, t.2.2))).map ((Equiv.refl Y₁).prodCongr e) := by
      rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
    have hz : (Q.map e3).map (fun t => t.2.2) = (Q.map (fun t => t.2.2)).map e := by
      rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
    unfold condMutualInfo; dsimp only
    rw [hxz, hyz, hz,
        shannonEntropy_map_equiv ((Equiv.refl X).prodCongr e),
        shannonEntropy_map_equiv ((Equiv.refl Y₁).prodCongr e),
        shannonEntropy_map_equiv e3,
        shannonEntropy_map_equiv e]
  · have hm : J'.map (fun z => (z.1.2, z.2.1)) = J.map (fun z => (z.1.2, z.2.1)) := by
      rw [hJ', map_comp_eq]; rfl
    rw [hm]

end BCDefinitions

/-! ### 2. Superposition Coding Achievability (Cover & Thomas §15.6; El Gamal–Kim Thm. 5.1) -/

section SuperpositionAchievability

variable {U X Y₁ Y₂ : Type*} [Fintype U] [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- Conditional channel `P_{X|U}(x | u)` extracted from a joint law `Pux : ProbDist (U × X)`.
    Satisfies `P_U(u) · P_{X|U}(x | u) = P_{UX}(u, x)` identically. -/
private noncomputable def condChannel [Nonempty X] (Pux : ProbDist (U × X)) : DMC U X := by
  classical
  exact
    { trans := fun u x =>
        if Pux.fst.pmf u = 0 then (if x = Classical.arbitrary X then 1 else 0)
        else Pux.pmf (u, x) / Pux.fst.pmf u
      nonneg := fun u x => by
        split_ifs
        · exact zero_le_one
        · exact le_rfl
        · exact div_nonneg (Pux.nonneg (u, x)) (Pux.fst.nonneg u)
      sum_one := fun u => by
        by_cases h : Pux.fst.pmf u = 0
        · simp [h]
        · simp only [h, ↓reduceIte]
          rw [← Finset.sum_div]
          exact div_self h }

private lemma condChannel_mul_fst [Nonempty X] (Pux : ProbDist (U × X)) (u : U) (x : X) :
    Pux.fst.pmf u * (condChannel Pux).trans u x = Pux.pmf (u, x) := by
  classical
  unfold condChannel; dsimp only
  by_cases h : Pux.fst.pmf u = 0
  · rw [h, zero_mul]
    have hle : Pux.pmf (u, x) ≤ Pux.fst.pmf u :=
      Finset.single_le_sum (fun x' _ => Pux.nonneg (u, x')) (Finset.mem_univ x)
    exact (le_antisymm (by linarith) (Pux.nonneg (u, x))).symm
  · simp only [h, ↓reduceIte]
    exact mul_div_cancel₀ _ h

private lemma condChannel_power_mul_iid [Nonempty X] (Pux : ProbDist (U × X)) (n : ℕ)
    (u : Fin n → U) (x : Fin n → X) :
    (iidDist Pux.fst n).pmf u * ((condChannel Pux).power n).trans u x =
      (iidDist Pux n).pmf (fun i => (u i, x i)) := by
  unfold iidDist DMC.power; dsimp only
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => condChannel_mul_fst Pux (u i) (x i)

private lemma condChannel_power_eq_div [Nonempty X] (Pux : ProbDist (U × X)) (n : ℕ)
    (u : Fin n → U) (x : Fin n → X) (hu : (iidDist Pux.fst n).pmf u ≠ 0) :
    ((condChannel Pux).power n).trans u x =
      (iidDist Pux n).pmf (fun i => (u i, x i)) / (iidDist Pux.fst n).pmf u := by
  rw [eq_div_iff hu, mul_comm, condChannel_power_mul_iid]

/-- A single cloud in a superposition codebook: cloud center `u ∈ U^n` together with `M₁`
    satellite codewords `xs : Fin M₁ → X^n`. -/
private abbrev CloudCode (U X : Type*) (n M₁ : ℕ) :=
  (Fin n → U) × (Fin M₁ → Fin n → X)

/-- Distribution of a single random cloud `(U^n, (X^n(1), …, X^n(M₁)))` where `U^n ~ P_U^n`
    and each satellite `X^n(m₁)` is drawn conditionally i.i.d. `~ P_{X|U}^n(· | U^n)`. -/
private noncomputable def cloudDist [Nonempty X] (Pux : ProbDist (U × X)) (n M₁ : ℕ) :
    ProbDist (CloudCode U X n M₁) where
  pmf := fun c => (iidDist Pux.fst n).pmf c.1 *
    ∏ m₁ : Fin M₁, ((condChannel Pux).power n).trans c.1 (c.2 m₁)
  nonneg := fun c => mul_nonneg ((iidDist Pux.fst n).nonneg c.1)
    (Finset.prod_nonneg fun m₁ _ => ((condChannel Pux).power n).nonneg c.1 (c.2 m₁))
  sum_one := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ u : Fin n → U,
        ∑ xs : Fin M₁ → Fin n → X,
          (iidDist Pux.fst n).pmf u *
            ∏ m₁ : Fin M₁, ((condChannel Pux).power n).trans u (xs m₁) =
        (iidDist Pux.fst n).pmf u := fun u => by
      rw [← Finset.mul_sum, ← Fintype.prod_sum]
      have h1 : ∏ _m₁ : Fin M₁, ∑ x : Fin n → X, ((condChannel Pux).power n).trans u x = 1 :=
        Finset.prod_eq_one fun _ _ => ((condChannel Pux).power n).sum_one u
      rw [h1, mul_one]
    simp_rw [hinner]
    exact (iidDist Pux.fst n).sum_one

private lemma cloudDist_sum_single_sat [Nonempty X] (Pux : ProbDist (U × X)) (n M₁ : ℕ)
    (m₁ : Fin M₁) (f : (Fin n → U) → (Fin n → X) → ℝ) :
    ∑ c : CloudCode U X n M₁, (cloudDist Pux n M₁).pmf c * f c.1 (c.2 m₁) =
      ∑ u : Fin n → U, ∑ x : Fin n → X, (iidDist Pux n).pmf (fun i => (u i, x i)) * f u x := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp_rw [cloudDist, mul_assoc]
  rw [← Finset.mul_sum]
  let Q : ProbDist (Fin n → X) := dmcRow ((condChannel Pux).power n) u
  have hQ := bc_sum_pi_prod_mul_single Q m₁ (fun x => f u x)
  dsimp only [Q, dmcRow] at hQ
  rw [hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, condChannel_power_mul_iid]

private lemma cloudDist_sum_pair_sat [Nonempty X] (Pux : ProbDist (U × X)) (n M₁ : ℕ)
    (m₁ m₁' : Fin M₁) (hne : m₁' ≠ m₁) (f g : (Fin n → U) → (Fin n → X) → ℝ) :
    ∑ c : CloudCode U X n M₁, (cloudDist Pux n M₁).pmf c * (f c.1 (c.2 m₁) * g c.1 (c.2 m₁')) =
      ∑ u : Fin n → U,
        (∑ x : Fin n → X, (iidDist Pux n).pmf (fun i => (u i, x i)) * f u x) *
        (∑ x' : Fin n → X, ((condChannel Pux).power n).trans u x' * g u x') := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp_rw [cloudDist, mul_assoc]
  rw [← Finset.mul_sum]
  let Q : ProbDist (Fin n → X) := dmcRow ((condChannel Pux).power n) u
  have hQ := bc_sum_pi_prod_mul_pair Q m₁ m₁' hne (fun x => f u x) (fun x' => g u x')
  dsimp only [Q, dmcRow] at hQ
  rw [hQ, ← mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, condChannel_power_mul_iid]

private lemma cloudDist_sum_center_only [Nonempty X] (Pux : ProbDist (U × X)) (n M₁ : ℕ)
    (f : (Fin n → U) → ℝ) :
    ∑ c : CloudCode U X n M₁, (cloudDist Pux n M₁).pmf c * f c.1 =
      ∑ u : Fin n → U, (iidDist Pux.fst n).pmf u * f u := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp_rw [cloudDist, mul_right_comm ((iidDist Pux.fst n).pmf u), ← Finset.mul_sum]
  have h1 : ∑ xs : Fin M₁ → Fin n → X,
      ∏ m₁ : Fin M₁, ((condChannel Pux).power n).trans u (xs m₁) = 1 := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun _ _ => ((condChannel Pux).power n).sum_one u
  rw [h1, mul_one]

/-- **Three-Way Jointly Weakly Typical Set** `A_ε^(n)(U, X, Y₁)` for superposition decoding at
    Receiver 1 (Cover & Thomas §15.6; El Gamal–Kim §5.3). -/
noncomputable def supTypicalSet (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (ε : ℝ) : Finset ((Fin n → U) × (Fin n → X) × (Fin n → Y₁)) := by
  classical
  let J := bcAuxJoint W Pux
  let P_Y1 := J.map (fun z => z.2.1)
  let P_UY1 := J.map (fun z => (z.1.1, z.2.1))
  let P_UXY1 := J.map (fun z => (z.1, z.2.1))
  exact Finset.univ.filter fun t =>
    t.1 ∈ weakTypicalSet Pux.fst n ε ∧
    (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Pux n ε ∧
    t.2.2 ∈ weakTypicalSet P_Y1 n ε ∧
    (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet P_UY1 n ε ∧
    (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈ weakTypicalSet P_UXY1 n ε

lemma mem_supTypicalSet (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (ε : ℝ) (t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁)) :
    let J := bcAuxJoint W Pux
    t ∈ supTypicalSet W Pux n ε ↔
      t.1 ∈ weakTypicalSet Pux.fst n ε ∧
      (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Pux n ε ∧
      t.2.2 ∈ weakTypicalSet (J.map (fun z => z.2.1)) n ε ∧
      (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet (J.map (fun z => (z.1.1, z.2.1))) n ε ∧
      (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈
        weakTypicalSet (J.map (fun z => (z.1, z.2.1))) n ε := by
  classical
  simp [supTypicalSet]

/-- Equivalence zipping a triple of length-`n` sequences `(u^n, x^n, y₁^n)` into
    a length-`n` sequence of triples `((u_i, x_i), y_{1,i})`. -/
def supZipEquiv (U X Y₁ : Type*) (n : ℕ) :
    ((Fin n → U) × (Fin n → X) × (Fin n → Y₁)) ≃ (Fin n → (U × X) × Y₁) where
  toFun := fun t i => ((t.1 i, t.2.1 i), t.2.2 i)
  invFun := fun z => (fun i => (z i).1.1, fun i => (z i).1.2, fun i => (z i).2)
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun _ => rfl

private lemma supIid_UXY1_pmf (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (u : Fin n → U) (x : Fin n → X) (y₁ : Fin n → Y₁) :
    (iidDist Pux n).pmf (fun i => (u i, x i)) * ((bcMarginal1 W).power n).trans x y₁ =
      (iidDist ((bcAuxJoint W Pux).map (fun z => (z.1, z.2.1))) n).pmf
        (supZipEquiv U X Y₁ n (u, x, y₁)) := by
  rw [bcAuxJoint_map_UXY1]
  unfold iidDist DMC.power DMC.joint dmcPrecomp
  simp only [supZipEquiv, Equiv.coe_fn_mk]
  rw [← Finset.prod_mul_distrib]

private lemma supIid_UY1_marginal (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (u : Fin n → U) (y₁ : Fin n → Y₁) :
    ∑ x : Fin n → X, (iidDist Pux n).pmf (fun i => (u i, x i)) *
        ((bcMarginal1 W).power n).trans x y₁ =
      (iidDist ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))) n).pmf
        (fun i => (u i, y₁ i)) := by
  have hfun : ∀ x : Fin n → X,
      (iidDist Pux n).pmf (fun i => (u i, x i)) * ((bcMarginal1 W).power n).trans x y₁ =
        ∏ i : Fin n, Pux.pmf (u i, x i) * (bcMarginal1 W).trans (x i) (y₁ i) := fun x => by
    unfold iidDist DMC.power; dsimp only; rw [← Finset.prod_mul_distrib]
  simp_rw [hfun]
  rw [← Fintype.prod_sum (fun i x => Pux.pmf (u i, x) * (bcMarginal1 W).trans x (y₁ i))]
  unfold iidDist; dsimp only
  exact Finset.prod_congr rfl fun i _ => (bcAuxJoint_map_UY1_pmf W Pux (u i) (y₁ i)).symm

private lemma supIid_Y1_marginal (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (y₁ : Fin n → Y₁) :
    ∑ u : Fin n → U, ∑ x : Fin n → X,
        (iidDist Pux n).pmf (fun i => (u i, x i)) * ((bcMarginal1 W).power n).trans x y₁ =
      (iidDist ((bcAuxJoint W Pux).map (fun z => z.2.1)) n).pmf y₁ := by
  simp_rw [supIid_UY1_marginal]
  change (jointIidDist ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))) n).snd.pmf y₁ = _
  rw [jointIidDist_snd]
  have hsnd : ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.1))).snd =
      (bcAuxJoint W Pux).map (fun z => z.2.1) := by
    rw [← bc_probDist_map_snd, map_comp_eq]; rfl
  rw [hsnd]

private lemma supIid_UY2_marginal (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (u : Fin n → U) (y₂ : Fin n → Y₂) :
    ∑ x : Fin n → X, (iidDist Pux n).pmf (fun i => (u i, x i)) *
        ((bcMarginal2 W).power n).trans x y₂ =
      (jointIidDist ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))) n).pmf (u, y₂) := by
  have hfun : ∀ x : Fin n → X,
      (iidDist Pux n).pmf (fun i => (u i, x i)) * ((bcMarginal2 W).power n).trans x y₂ =
        ∏ i : Fin n, Pux.pmf (u i, x i) * (bcMarginal2 W).trans (x i) (y₂ i) := fun x => by
    unfold iidDist DMC.power; dsimp only; rw [← Finset.prod_mul_distrib]
  simp_rw [hfun]
  rw [← Fintype.prod_sum (fun i x => Pux.pmf (u i, x) * (bcMarginal2 W).trans x (y₂ i))]
  unfold jointIidDist; dsimp only
  exact Finset.prod_congr rfl fun i _ => (bcAuxJoint_map_UY2_pmf W Pux (u i) (y₂ i)).symm

private lemma supIid_Y2_marginal (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (y₂ : Fin n → Y₂) :
    ∑ u : Fin n → U, ∑ x : Fin n → X,
        (iidDist Pux n).pmf (fun i => (u i, x i)) * ((bcMarginal2 W).power n).trans x y₂ =
      (iidDist ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))).snd n).pmf y₂ := by
  simp_rw [supIid_UY2_marginal]
  change (jointIidDist ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))) n).snd.pmf y₂ = _
  rw [jointIidDist_snd]

private lemma supTypicalSet_card_le (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n : ℕ) (ε : ℝ) :
    ((supTypicalSet W Pux n ε).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy ((bcAuxJoint W Pux).map (fun z => (z.1, z.2.1))) + ε)) := by
  classical
  have hle : (supTypicalSet W Pux n ε).card ≤
      (weakTypicalSet ((bcAuxJoint W Pux).map (fun z => (z.1, z.2.1))) n ε).card := by
    refine Finset.card_le_card_of_injOn (supZipEquiv U X Y₁ n) ?_ ?_
    · intro t ht; exact ((mem_supTypicalSet W Pux n ε t).mp ht).2.2.2.2
    · intro t₁ _ t₂ _ h; exact (supZipEquiv U X Y₁ n).injective h
  exact le_trans (by exact_mod_cast hle) (weakTypicalSet_card_le _ n ε)

lemma sup_aep_prob_tendsto_one (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    let P_UXY1 := (bcAuxJoint W Pux).map (fun z => (z.1, z.2.1))
    ∃ N : ℕ, ∀ n ≥ N,
      1 - δ ≤ ∑ t ∈ supTypicalSet W Pux n ε,
        (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) := by
  classical
  dsimp only
  let J := bcAuxJoint W Pux
  let P_Y1 := J.map (fun z => z.2.1)
  let P_UY1 := J.map (fun z => (z.1.1, z.2.1))
  let P_UXY1 := J.map (fun z => (z.1, z.2.1))
  have hδ5 : 0 < δ / 5 := by linarith
  obtain ⟨N₁, hN₁⟩ := aep_typical_prob_tendsto_one Pux.fst hε hδ5
  obtain ⟨N₂, hN₂⟩ := aep_typical_prob_tendsto_one Pux hε hδ5
  obtain ⟨N₃, hN₃⟩ := aep_typical_prob_tendsto_one P_Y1 hε hδ5
  obtain ⟨N₄, hN₄⟩ := aep_typical_prob_tendsto_one P_UY1 hε hδ5
  obtain ⟨N₅, hN₅⟩ := aep_typical_prob_tendsto_one P_UXY1 hε hδ5
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) N₅, fun n hn => ?_⟩
  let Q : ProbDist ((Fin n → U) × (Fin n → X) × (Fin n → Y₁)) :=
    { pmf := fun t => (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t)
      nonneg := fun t => (iidDist P_UXY1 n).nonneg _
      sum_one := by
        rw [Fintype.sum_equiv (supZipEquiv U X Y₁ n) _ (fun z => (iidDist P_UXY1 n).pmf z) (fun _ => rfl)]
        exact (iidDist P_UXY1 n).sum_one }
  have hQ_zip : Q.map (supZipEquiv U X Y₁ n) = iidDist P_UXY1 n := by
    apply bc_probDist_ext; intro z
    unfold ProbDist.map; dsimp only [Q]
    rw [Finset.sum_eq_single ((supZipEquiv U X Y₁ n).symm z)]
    · simp
    · intro t _ hne
      have : supZipEquiv U X Y₁ n t ≠ z := fun h =>
        hne ((supZipEquiv U X Y₁ n).symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hUXY1_fst : P_UXY1.map Prod.fst = Pux := by
    rw [bc_probDist_map_fst]; dsimp only [P_UXY1, J]; rw [bcAuxJoint_map_UXY1, dmc_joint_fst]
  have hmap1 : Q.map (fun t => t.1) = iidDist Pux.fst n := by
    have h : (fun t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁) => t.1) =
        (fun z i => (z i).1.1) ∘ supZipEquiv U X Y₁ n := rfl
    rw [h, ← map_comp_eq, hQ_zip, bc_iidDist_map_comp P_UXY1 n (fun z => z.1.1)]
    congr 1
    change P_UXY1.map (Prod.fst ∘ Prod.fst) = Pux.fst
    rw [← map_comp_eq, hUXY1_fst, bc_probDist_map_fst]
  have hmap2 : Q.map (fun t i => (t.1 i, t.2.1 i)) = iidDist Pux n := by
    have h : (fun (t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁)) i => (t.1 i, t.2.1 i)) =
        (fun z i => (z i).1) ∘ supZipEquiv U X Y₁ n := rfl
    rw [h, ← map_comp_eq, hQ_zip, bc_iidDist_map_comp P_UXY1 n Prod.fst, hUXY1_fst]
  have hmap3 : Q.map (fun t => t.2.2) = iidDist P_Y1 n := by
    have h : (fun t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁) => t.2.2) =
        (fun z i => (z i).2) ∘ supZipEquiv U X Y₁ n := rfl
    rw [h, ← map_comp_eq, hQ_zip, bc_iidDist_map_comp P_UXY1 n Prod.snd]
    congr 1
    change (J.map (fun z => (z.1, z.2.1))).map Prod.snd = P_Y1
    rw [map_comp_eq]; rfl
  have hmap4 : Q.map (fun t i => (t.1 i, t.2.2 i)) = iidDist P_UY1 n := by
    have h : (fun (t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁)) i => (t.1 i, t.2.2 i)) =
        (fun z i => ((z i).1.1, (z i).2)) ∘ supZipEquiv U X Y₁ n := rfl
    rw [h, ← map_comp_eq, hQ_zip, bc_iidDist_map_comp P_UXY1 n (fun z => (z.1.1, z.2))]
    congr 1
    change (J.map (fun z => (z.1, z.2.1))).map (fun z => (z.1.1, z.2)) = P_UY1
    rw [map_comp_eq]; rfl
  let A := supTypicalSet W Pux n ε
  have hunion : ∀ t, (if t ∉ A then Q.pmf t else 0) ≤
      (if t.1 ∉ weakTypicalSet Pux.fst n ε then Q.pmf t else 0) +
      (if (fun i => (t.1 i, t.2.1 i)) ∉ weakTypicalSet Pux n ε then Q.pmf t else 0) +
      (if t.2.2 ∉ weakTypicalSet P_Y1 n ε then Q.pmf t else 0) +
      (if (fun i => (t.1 i, t.2.2 i)) ∉ weakTypicalSet P_UY1 n ε then Q.pmf t else 0) +
      (if supZipEquiv U X Y₁ n t ∉ weakTypicalSet P_UXY1 n ε then Q.pmf t else 0) := by
    intro t
    have hq0 := Q.nonneg t
    by_cases h1 : t.1 ∈ weakTypicalSet Pux.fst n ε <;>
    by_cases h2 : (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Pux n ε <;>
    by_cases h3 : t.2.2 ∈ weakTypicalSet P_Y1 n ε <;>
    by_cases h4 : (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet P_UY1 n ε <;>
    by_cases h5 : supZipEquiv U X Y₁ n t ∈ weakTypicalSet P_UXY1 n ε
    · have hmem : t ∈ A := (mem_supTypicalSet W Pux n ε t).mpr ⟨h1, h2, h3, h4, h5⟩
      simp [hmem, h1, h2, h3, h4, h5]
    all_goals
      simp only [h1, h2, h3, h4, h5, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      split_ifs <;> linarith
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hunion t
  simp_rw [Finset.sum_add_distrib] at hsum
  have hcomp : (∑ t, if t ∉ A then Q.pmf t else 0) = 1 - ∑ t ∈ A, Q.pmf t := by
    have hsplit : ∑ t, Q.pmf t =
        (∑ t, if t ∈ A then Q.pmf t else 0) + (∑ t, if t ∉ A then Q.pmf t else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by by_cases h : t ∈ A <;> simp [h]
    rw [Q.sum_one] at hsplit
    have hmem : (∑ t, if t ∈ A then Q.pmf t else 0) = ∑ t ∈ A, Q.pmf t := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    linarith
  have hs1 := bc_sum_not_mem_of_map Q (fun t => t.1) (weakTypicalSet Pux.fst n ε) (iidDist Pux.fst n) hmap1
  have hs2 := bc_sum_not_mem_of_map Q (fun t i => (t.1 i, t.2.1 i)) (weakTypicalSet Pux n ε) (iidDist Pux n) hmap2
  have hs3 := bc_sum_not_mem_of_map Q (fun t => t.2.2) (weakTypicalSet P_Y1 n ε) (iidDist P_Y1 n) hmap3
  have hs4 := bc_sum_not_mem_of_map Q (fun t i => (t.1 i, t.2.2 i)) (weakTypicalSet P_UY1 n ε) (iidDist P_UY1 n) hmap4
  have hs5 := bc_sum_not_mem_of_map Q (supZipEquiv U X Y₁ n) (weakTypicalSet P_UXY1 n ε) (iidDist P_UXY1 n) hQ_zip
  rw [hcomp, hs1, hs2, hs3, hs4, hs5] at hsum
  have hp1 := hN₁ n (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hn)
  have hp2 := hN₂ n (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hn)
  have hp3 := hN₃ n (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hn)
  have hp4 := hN₄ n (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hn)
  have hp5 := hN₅ n (le_trans (le_max_right _ _) hn)
  linarith

/-- Packing-lemma upper bounds for the two wrong-message events in Receiver 1's 3-way
    superposition decoding:
    1. Same cloud `m₂`, wrong satellite `m₁' ≠ m₁`: `≤ 2^(-n (I(X; Y₁ | U) - 4ε))`
    2. Wrong cloud `m₂' ≠ m₂`, any `m₁'`: `≤ 2^(-n (I(X; Y₁) - 3ε))`. -/
private lemma supTypicalSet_indep_bounds [Nonempty X]
    (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X)) (n : ℕ) (ε : ℝ) :
    let J := bcAuxJoint W Pux
    let P_Y1 := J.map (fun z => z.2.1)
    let P_UY1 := J.map (fun z => (z.1.1, z.2.1))
    let A := supTypicalSet W Pux n ε
    (∑ t ∈ A, (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) *
        ((condChannel Pux).power n).trans t.1 t.2.1 ≤
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) - 4 * ε)))) ∧
    (∑ t ∈ A, (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => (z.1.2, z.2.1))) - 3 * ε)))) := by
  classical
  dsimp only
  let J := bcAuxJoint W Pux
  let P_Y1 := J.map (fun z => z.2.1)
  let P_UY1 := J.map (fun z => (z.1.1, z.2.1))
  let P_UXY1 := J.map (fun z => (z.1, z.2.1))
  let A := supTypicalSet W Pux n ε
  constructor
  · -- Event E₁: same cloud, wrong satellite
    have hterm : ∀ t ∈ A,
        (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) *
          ((condChannel Pux).power n).trans t.1 t.2.1 ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_UY1 - ε))) *
        ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) /
         (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux.fst + ε)))) := by
      intro t ht
      have hm := (mem_supTypicalSet W Pux n ε t).mp ht
      have hu := hm.1
      have hux := hm.2.1
      have huy1 := hm.2.2.2.1
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu hux huy1
      have hupos : 0 < (iidDist Pux.fst n).pmf t.1 :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hu.1
      rw [condChannel_power_eq_div Pux n t.1 t.2.1 hupos.ne']
      have hdiv : (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) / (iidDist Pux.fst n).pmf t.1 ≤
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) /
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux.fst + ε))) :=
        div_le_div₀ (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hux.2
          (Real.rpow_pos_of_pos (by norm_num) _) hu.1
      exact mul_le_mul huy1.2 hdiv (div_nonneg ((iidDist Pux n).nonneg _) hupos.le)
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    have hcmi_eq : condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) =
        shannonEntropy Pux + shannonEntropy P_UY1 - shannonEntropy P_UXY1 - shannonEntropy Pux.fst := by
      let e : ((U × X) × Y₁) ≃ (X × Y₁ × U) :=
        { toFun := fun t => (t.1.2, t.2, t.1.1)
          invFun := fun t => ((t.2.2, t.1), t.2.1)
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
      have h1 : (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.1, t.2.2)) =
          Pux.map Prod.swap := by
        rw [map_comp_eq]
        have hJux : J.map (fun z => z.1) = Pux := by
          have : J.map (fun z => z.1) = P_UXY1.map Prod.fst := by rw [map_comp_eq]; rfl
          rw [this, bc_probDist_map_fst]; dsimp only [P_UXY1, J]; rw [bcAuxJoint_map_UXY1, dmc_joint_fst]
        rw [← hJux, map_comp_eq]; rfl
      have h2 : (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.2.1, t.2.2)) =
          P_UY1.map Prod.swap := by
        rw [map_comp_eq, map_comp_eq]; rfl
      have h3 : (J.map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => t.2.2) = Pux.fst := by
        rw [map_comp_eq]
        have hJux : J.map (fun z => z.1) = Pux := by
          have : J.map (fun z => z.1) = P_UXY1.map Prod.fst := by rw [map_comp_eq]; rfl
          rw [this, bc_probDist_map_fst]; dsimp only [P_UXY1, J]; rw [bcAuxJoint_map_UXY1, dmc_joint_fst]
        rw [← bc_probDist_map_fst, ← hJux, map_comp_eq]; rfl
      have h4 : J.map (fun z => (z.1.2, z.2.1, z.1.1)) = P_UXY1.map e := by
        rw [map_comp_eq]; rfl
      unfold condMutualInfo; dsimp only
      rw [h1, h2, h3, h4, shannonEntropy_swap, shannonEntropy_swap, shannonEntropy_map_equiv e]
    calc ∑ t ∈ A, (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) *
            ((condChannel Pux).power n).trans t.1 t.2.1
      _ ≤ ∑ _t ∈ A, ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_UY1 - ε))) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) /
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux.fst + ε))))) := Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_UY1 - ε))) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) /
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux.fst + ε))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P_UXY1 + ε)) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_UY1 - ε))) *
             ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) /
              (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux.fst + ε))))) :=
          mul_le_mul_of_nonneg_right (supTypicalSet_card_le W Pux n ε) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) *
            (condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) - 4 * ε))) := by
          rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; rw [hcmi_eq]; ring
  · -- Event E₂: wrong cloud, any satellite
    have hterm : ∀ t ∈ A,
        (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_Y1 - ε))) := by
      intro t ht
      have hm := (mem_supTypicalSet W Pux n ε t).mp ht
      have hux := hm.2.1
      have hy1 := hm.2.2.1
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hux hy1
      exact mul_le_mul hux.2 hy1.2 ((iidDist P_Y1 n).nonneg _)
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    have hmi_eq : mutualInfo (J.map (fun z => (z.1.2, z.2.1))) =
        shannonEntropy Pux + shannonEntropy P_Y1 - shannonEntropy P_UXY1 := by
      rw [← bcAuxJoint_mutualInfo_UX_Y1_eq]
      have hfst : P_UXY1.fst = Pux := by
        dsimp only [P_UXY1, J]; rw [bcAuxJoint_map_UXY1, dmc_joint_fst]
      have hsnd : P_UXY1.snd = P_Y1 := by
        rw [← bc_probDist_map_snd, map_comp_eq]; rfl
      unfold mutualInfo
      change shannonEntropy P_UXY1.fst + shannonEntropy P_UXY1.snd - shannonEntropy P_UXY1 = _
      rw [hfst, hsnd]
    calc ∑ t ∈ A, (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2
      _ ≤ ∑ _t ∈ A, ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_Y1 - ε)))) := Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_Y1 - ε)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P_UXY1 + ε)) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy Pux - ε))) *
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P_Y1 - ε)))) :=
          mul_le_mul_of_nonneg_right (supTypicalSet_card_le W Pux n ε) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => (z.1.2, z.2.1))) - 3 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; rw [hmi_eq]; ring

/-- Receiver 1's joint-typicality superposition decoder: outputs the unique pair `(m₁, m₂)`
    such that `(u(m₂), x(m₂, m₁), y₁) ∈ supTypicalSet W Pux n ε`, or `(0, 0)` otherwise. -/
private noncomputable def supTypicalDec1 (W : BroadcastChannel X Y₁ Y₂) (Pux : ProbDist (U × X))
    (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (clouds : Fin M₂ → CloudCode U X n M₁) (y₁ : Fin n → Y₁) : Fin M₁ × Fin M₂ := by
  classical
  exact if h : ∃! m : Fin M₁ × Fin M₂,
      ((clouds m.2).1, (clouds m.2).2 m.1, y₁) ∈ supTypicalSet W Pux n ε then
    Classical.choose h
  else
    (⟨0, hM₁⟩, ⟨0, hM₂⟩)

open Classical in
private lemma supTypicalDec1_err_indicator_le (W : BroadcastChannel X Y₁ Y₂)
    (Pux : ProbDist (U × X)) (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (clouds : Fin M₂ → CloudCode U X n M₁) (y₁ : Fin n → Y₁) (m₁ : Fin M₁) (m₂ : Fin M₂) :
    let A := supTypicalSet W Pux n ε
    (if (supTypicalDec1 W Pux n M₁ M₂ hM₁ hM₂ ε clouds y₁).1 ≠ m₁ then (1 : ℝ) else 0) ≤
      (if ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∉ A then (1 : ℝ) else 0) +
      (∑ m₁' ∈ Finset.univ.erase m₁,
        if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A then (1 : ℝ) else 0) +
      (∑ m₂' ∈ Finset.univ.erase m₂, ∑ m₁' : Fin M₁,
        if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A then (1 : ℝ) else 0) := by
  dsimp only
  let A := supTypicalSet W Pux n ε
  have hnn1 : (0 : ℝ) ≤ ∑ m₁' ∈ Finset.univ.erase m₁,
      if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hnn2 : (0 : ℝ) ≤ ∑ m₂' ∈ Finset.univ.erase m₂, ∑ m₁' : Fin M₁,
      if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases herr : (supTypicalDec1 W Pux n M₁ M₂ hM₁ hM₂ ε clouds y₁).1 ≠ m₁
  · rw [ite_eq_left herr]
    by_cases hm : ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∈ A
    · rw [ite_eq_right (not_not.mpr hm), zero_add]
      have hex : ∃ m' : Fin M₁ × Fin M₂, m' ≠ (m₁, m₂) ∧
          ((clouds m'.2).1, (clouds m'.2).2 m'.1, y₁) ∈ A := by
        by_contra hnone; push Not at hnone
        have huniq : ∃! m : Fin M₁ × Fin M₂, ((clouds m.2).1, (clouds m.2).2 m.1, y₁) ∈ A :=
          ⟨(m₁, m₂), hm, fun m hm' => by by_contra hne; exact hnone m hne hm'⟩
        have hdec : supTypicalDec1 W Pux n M₁ M₂ hM₁ hM₂ ε clouds y₁ = (m₁, m₂) := by
          unfold supTypicalDec1
          split_ifs with h'
          · have hspec := Classical.choose_spec h'
            by_contra hne; exact hnone _ hne hspec.1
          · exact absurd huniq h'
        exact herr (by rw [hdec])
      obtain ⟨⟨m₁', m₂'⟩, hne, hmem'⟩ := hex
      by_cases hm2 : m₂' = m₂
      · subst hm2
        have hm1 : m₁' ≠ m₁ := fun h => hne (by subst h; rfl)
        have h1 : (1 : ℝ) ≤ ∑ k ∈ Finset.univ.erase m₁,
            if ((clouds m₂').1, (clouds m₂').2 k, y₁) ∈ A then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A then (1 : ℝ) else 0) := by
                rw [ite_eq_left hmem']
            _ ≤ _ := Finset.single_le_sum
                (f := fun k => if ((clouds m₂').1, (clouds m₂').2 k, y₁) ∈ A then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hm1, Finset.mem_univ m₁'⟩)
        linarith
      · have h2 : (1 : ℝ) ≤ ∑ k₂ ∈ Finset.univ.erase m₂, ∑ k₁ : Fin M₁,
            if ((clouds k₂).1, (clouds k₂).2 k₁, y₁) ∈ A then (1 : ℝ) else 0 := by
          have hin : (1 : ℝ) ≤ ∑ k₁ : Fin M₁,
              if ((clouds m₂').1, (clouds m₂').2 k₁, y₁) ∈ A then (1 : ℝ) else 0 := by
            calc (1 : ℝ) = (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A then (1 : ℝ) else 0) := by
                  rw [ite_eq_left hmem']
              _ ≤ _ := Finset.single_le_sum
                  (f := fun k₁ => if ((clouds m₂').1, (clouds m₂').2 k₁, y₁) ∈ A then (1 : ℝ) else 0)
                  (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ m₁')
          exact le_trans hin (Finset.single_le_sum
            (f := fun k₂ => ∑ k₁ : Fin M₁, if ((clouds k₂).1, (clouds k₂).2 k₁, y₁) ∈ A then (1 : ℝ) else 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_erase.mpr ⟨hm2, Finset.mem_univ m₂'⟩))
        linarith
    · rw [ite_eq_left hm]; linarith
  · rw [ite_eq_right herr]
    have h0 : (0 : ℝ) ≤ if ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∉ A then (1 : ℝ) else 0 := by
      split_ifs <;> norm_num
    linarith

open Classical in
private lemma supTypicalDec2_err_indicator_le (P_UY2 : ProbDist (U × Y₂))
    (n M₂ : ℕ) (hM₂ : 0 < M₂) (ε : ℝ)
    (uCode : Fin M₂ → Fin n → U) (y₂ : Fin n → Y₂) (m₂ : Fin M₂) :
    let A₂ := jointTypicalSet P_UY2 n ε
    (if jointTypicalDec P_UY2 n M₂ hM₂ ε uCode y₂ ≠ m₂ then (1 : ℝ) else 0) ≤
      (if (uCode m₂, y₂) ∉ A₂ then (1 : ℝ) else 0) +
      ∑ m₂' ∈ Finset.univ.erase m₂,
        (if (uCode m₂', y₂) ∈ A₂ then (1 : ℝ) else 0) := by
  dsimp only
  let A₂ := jointTypicalSet P_UY2 n ε
  have hnn : (0 : ℝ) ≤ ∑ m₂' ∈ Finset.univ.erase m₂,
      if (uCode m₂', y₂) ∈ A₂ then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases herr : jointTypicalDec P_UY2 n M₂ hM₂ ε uCode y₂ ≠ m₂
  · rw [ite_eq_left herr]
    by_cases hm : (uCode m₂, y₂) ∈ A₂
    · rw [ite_eq_right (not_not.mpr hm), zero_add]
      have hex : ∃ m₂' : Fin M₂, m₂' ≠ m₂ ∧ (uCode m₂', y₂) ∈ A₂ := by
        by_contra hnone; push Not at hnone
        have huniq : ∃! k : Fin M₂, (uCode k, y₂) ∈ A₂ :=
          ⟨m₂, hm, fun k hk => by by_contra hne; exact hnone k hne hk⟩
        have hdec : jointTypicalDec P_UY2 n M₂ hM₂ ε uCode y₂ = m₂ := by
          unfold jointTypicalDec
          split_ifs with h'
          · have hspec := Classical.choose_spec h'
            by_contra hne; exact hnone _ hne hspec.1
          · exact absurd huniq h'
        exact herr hdec
      obtain ⟨m₂', hm2', hmem'⟩ := hex
      calc (1 : ℝ) = (if (uCode m₂', y₂) ∈ A₂ then (1 : ℝ) else 0) := by rw [ite_eq_left hmem']
        _ ≤ _ := Finset.single_le_sum
            (f := fun k => if (uCode k, y₂) ∈ A₂ then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_erase.mpr ⟨hm2', Finset.mem_univ m₂'⟩)
    · rw [ite_eq_left hm]; linarith
  · rw [ite_eq_right herr]
    have h0 : (0 : ℝ) ≤ if (uCode m₂, y₂) ∉ A₂ then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    linarith

/-- **Superposition Coding Random-Coding Existence Bound** (Cover & Thomas §15.6;
    El Gamal–Kim Thm. 5.1): for any DMBC `W`, auxiliary distribution `Pux : ProbDist (U × X)`,
    blocklength `n`, message counts `M₁, M₂ > 0`, and typicality tolerance `ε`, there exists a
    deterministic broadcast code `(enc, dec₁, dec₂)` with average joint error bounded by the five
    typicality + packing terms. -/
theorem superposition_random_coding_bound (W : BroadcastChannel X Y₁ Y₂)
    (Pux : ProbDist (U × X)) (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ) :
    let J := bcAuxJoint W Pux
    let P_UY2 := J.map (fun z => (z.1.1, z.2.2))
    let P_UXY1 := J.map (fun z => (z.1, z.2.1))
    ∃ (enc : Fin M₁ → Fin M₂ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₂),
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          (if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
           then (W.power n).trans (enc m₁ m₂) y else 0) ≤
        (1 - ∑ t ∈ supTypicalSet W Pux n ε, (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t)) +
        (1 - ∑ xy ∈ jointTypicalSet P_UY2 n ε, (jointIidDist P_UY2 n).pmf xy) +
        ((M₁ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) - 4 * ε))) +
        (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => (z.1.2, z.2.1))) - 3 * ε))) +
        ((M₂ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P_UY2 - 3 * ε))) := by
  classical
  have hUXne : Nonempty (U × X) := bc_nonempty_of_probDist Pux
  have : Nonempty X := ⟨hUXne.some.2⟩
  dsimp only
  let J := bcAuxJoint W Pux
  let P_UY2 := J.map (fun z => (z.1.1, z.2.2))
  let P_UXY1 := J.map (fun z => (z.1, z.2.1))
  let P_UY1 := J.map (fun z => (z.1.1, z.2.1))
  let P_Y1 := J.map (fun z => z.2.1)
  let A₁ := supTypicalSet W Pux n ε
  let A₂ := jointTypicalSet P_UY2 n ε
  let Q := cloudDist Pux n M₁
  let w : (Fin M₂ → CloudCode U X n M₁) → ℝ := fun clouds => ∏ m₂ : Fin M₂, Q.pmf (clouds m₂)
  have hw0 : ∀ clouds, 0 ≤ w clouds := fun clouds => Finset.prod_nonneg fun m₂ _ => Q.nonneg _
  have hw1 : ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds = 1 := by
    unfold w; rw [← Fintype.prod_sum]; exact Finset.prod_eq_one fun _ _ => Q.sum_one
  let dec₁Of : (Fin M₂ → CloudCode U X n M₁) → (Fin n → Y₁) → Fin M₁ :=
    fun clouds y₁ => (supTypicalDec1 W Pux n M₁ M₂ hM₁ hM₂ ε clouds y₁).1
  let dec₂Of : (Fin M₂ → CloudCode U X n M₁) → (Fin n → Y₂) → Fin M₂ :=
    fun clouds y₂ => jointTypicalDec P_UY2 n M₂ hM₂ ε (fun m₂ => (clouds m₂).1) y₂
  let bcErr : (Fin M₂ → CloudCode U X n M₁) → ℝ := fun clouds =>
    ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
        then (W.power n).trans ((clouds m₂).2 m₁) y else 0
  let B : ℝ :=
    (1 - ∑ t ∈ A₁, (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t)) +
    (1 - ∑ xy ∈ A₂, (jointIidDist P_UY2 n).pmf xy) +
    ((M₁ - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) - 4 * ε))) +
    (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => (z.1.2, z.2.1))) - 3 * ε))) +
    ((M₂ - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P_UY2 - 3 * ε)))
  -- Bound the expected error for any fixed message pair `(m₁, m₂)`
  have hpair : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂),
      ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
        (∑ y : Fin n → Y₁ × Y₂,
          if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
          then (W.power n).trans ((clouds m₂).2 m₁) y else 0) ≤ B := by
    intro m₁ m₂
    -- Step 1: Union bound splitting into Receiver 1 error + Receiver 2 error
    have hsplit_rx : ∀ clouds : Fin M₂ → CloudCode U X n M₁,
        (∑ y : Fin n → Y₁ × Y₂,
          if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
          then (W.power n).trans ((clouds m₂).2 m₁) y else 0) ≤
        (∑ y₁ : Fin n → Y₁,
          ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0)) +
        (∑ y₂ : Fin n → Y₂,
          ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
            (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0)) := by
      intro clouds
      have hor : ∀ y : Fin n → Y₁ × Y₂,
          (if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
           then (W.power n).trans ((clouds m₂).2 m₁) y else 0) ≤
          (if dec₁Of clouds (fun i => (y i).1) ≠ m₁ then (W.power n).trans ((clouds m₂).2 m₁) y else 0) +
          (if dec₂Of clouds (fun i => (y i).2) ≠ m₂ then (W.power n).trans ((clouds m₂).2 m₁) y else 0) := by
        intro y; have hnn := (W.power n).nonneg ((clouds m₂).2 m₁) y
        by_cases h1 : dec₁Of clouds (fun i => (y i).1) ≠ m₁ <;>
        by_cases h2 : dec₂Of clouds (fun i => (y i).2) ≠ m₂ <;>
        simp [h1, h2, hnn]
      calc _ ≤ (∑ y, if dec₁Of clouds (fun i => (y i).1) ≠ m₁ then (W.power n).trans ((clouds m₂).2 m₁) y else 0) +
               (∑ y, if dec₂Of clouds (fun i => (y i).2) ≠ m₂ then (W.power n).trans ((clouds m₂).2 m₁) y else 0) := by
            rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun y _ => hor y
        _ = (∑ y₁, if dec₁Of clouds y₁ ≠ m₁ then ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ else 0) +
            (∑ y₂, if dec₂Of clouds y₂ ≠ m₂ then ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ else 0) := by
            rw [bc_sum_ite_fst_power W ((clouds m₂).2 m₁) (fun y₁ => dec₁Of clouds y₁ ≠ m₁),
                bc_sum_ite_snd_power W ((clouds m₂).2 m₁) (fun y₂ => dec₂Of clouds y₂ ≠ m₂)]
        _ = _ := by
            congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring
    -- Step 2: Evaluate the 5 ensemble averages
    -- Term 1a (E₀ for Rx 1): true triple not in A₁
    have hE10 : (∑ y₁ : Fin n → Y₁, ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
        (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
          (if ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∉ A₁ then (1 : ℝ) else 0))) =
        1 - ∑ t ∈ A₁, (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) := by
      have hinner : ∀ y₁ : Fin n → Y₁,
          (∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∉ A₁ then (1 : ℝ) else 0))) =
          ∑ u : Fin n → U, ∑ x : Fin n → X,
            if (u, x, y₁) ∉ A₁ then (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n (u, x, y₁)) else 0 := by
        intro y₁
        rw [bc_sum_pi_prod_mul_single Q m₂
          (fun c => ((bcMarginal1 W).power n).trans (c.2 m₁) y₁ * (if (c.1, c.2 m₁, y₁) ∉ A₁ then (1 : ℝ) else 0))]
        dsimp only [Q]
        rw [cloudDist_sum_single_sat Pux n M₁ m₁
          (fun u x => ((bcMarginal1 W).power n).trans x y₁ * (if (u, x, y₁) ∉ A₁ then (1 : ℝ) else 0))]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
        rw [← mul_assoc, supIid_UXY1_pmf]; split_ifs <;> ring
      simp_rw [hinner]
      have hprod : ∑ y₁ : Fin n → Y₁, ∑ u : Fin n → U, ∑ x : Fin n → X,
            (if (u, x, y₁) ∉ A₁ then (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n (u, x, y₁)) else 0) =
          ∑ t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁),
            if t ∉ A₁ then (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) else 0 := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
      rw [hprod]
      have htot : ∑ t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁),
          (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) = 1 := by
        rw [Fintype.sum_equiv (supZipEquiv U X Y₁ n) _ (fun z => (iidDist P_UXY1 n).pmf z) (fun _ => rfl)]
        exact (iidDist P_UXY1 n).sum_one
      have hsplit : ∑ t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁),
          (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) =
          (∑ t, if t ∈ A₁ then (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) else 0) +
          (∑ t, if t ∉ A₁ then (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => by by_cases h : t ∈ A₁ <;> simp [h]
      have hmem : (∑ t, if t ∈ A₁ then (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) else 0) =
          ∑ t ∈ A₁, (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      linarith
    -- Term 1b (E₁ for Rx 1): same cloud m₂, wrong satellite m₁' ≠ m₁
    have hE11 : ∀ m₁' ∈ Finset.univ.erase m₁,
        (∑ y₁ : Fin n → Y₁, ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
          (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
        ∑ t ∈ A₁, (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) *
          ((condChannel Pux).power n).trans t.1 t.2.1 := by
      intro m₁' hm₁'
      have hne : m₁' ≠ m₁ := (Finset.mem_erase.mp hm₁').1
      have hinner : ∀ y₁ : Fin n → Y₁,
          (∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
          ∑ u : Fin n → U, ∑ x' : Fin n → X,
            if (u, x', y₁) ∈ A₁ then
              (iidDist P_UY1 n).pmf (fun i => (u i, y₁ i)) * ((condChannel Pux).power n).trans u x'
            else 0 := by
        intro y₁
        rw [bc_sum_pi_prod_mul_single Q m₂
          (fun c => ((bcMarginal1 W).power n).trans (c.2 m₁) y₁ * (if (c.1, c.2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))]
        rw [cloudDist_sum_pair_sat Pux n M₁ m₁ m₁' hne
          (fun _ x => ((bcMarginal1 W).power n).trans x y₁)
          (fun u x' => if (u, x', y₁) ∈ A₁ then (1 : ℝ) else 0)]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [supIid_UY1_marginal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x' _ => by split_ifs <;> ring
      simp_rw [hinner]
      have hprod : ∑ y₁ : Fin n → Y₁, ∑ u : Fin n → U, ∑ x' : Fin n → X,
            (if (u, x', y₁) ∈ A₁ then
              (iidDist P_UY1 n).pmf (fun i => (u i, y₁ i)) * ((condChannel Pux).power n).trans u x' else 0) =
          ∑ t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁),
            if t ∈ A₁ then
              (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) * ((condChannel Pux).power n).trans t.1 t.2.1
            else 0 := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
      rw [hprod, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    -- Term 1c (E₂ for Rx 1): wrong cloud m₂' ≠ m₂, any m₁'
    have hE12 : ∀ m₂' ∈ Finset.univ.erase m₂, ∀ m₁' : Fin M₁,
        (∑ y₁ : Fin n → Y₁, ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
          (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
        ∑ t ∈ A₁, (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 := by
      intro m₂' hm₂' m₁'
      have hne : m₂' ≠ m₂ := (Finset.mem_erase.mp hm₂').1
      have hinner : ∀ y₁ : Fin n → Y₁,
          (∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
          ∑ u' : Fin n → U, ∑ x' : Fin n → X,
            if (u', x', y₁) ∈ A₁ then
              (iidDist Pux n).pmf (fun i => (u' i, x' i)) * (iidDist P_Y1 n).pmf y₁
            else 0 := by
        intro y₁
        rw [bc_sum_pi_prod_mul_pair Q m₂ m₂' hne
          (fun c => ((bcMarginal1 W).power n).trans (c.2 m₁) y₁)
          (fun c' => if (c'.1, c'.2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0)]
        rw [cloudDist_sum_single_sat Pux n M₁ m₁ (fun _ x => ((bcMarginal1 W).power n).trans x y₁),
            supIid_Y1_marginal,
            cloudDist_sum_single_sat Pux n M₁ m₁' (fun u' x' => if (u', x', y₁) ∈ A₁ then (1 : ℝ) else 0)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x' _ => by split_ifs <;> ring
      simp_rw [hinner]
      have hprod : ∑ y₁ : Fin n → Y₁, ∑ u' : Fin n → U, ∑ x' : Fin n → X,
            (if (u', x', y₁) ∈ A₁ then
              (iidDist Pux n).pmf (fun i => (u' i, x' i)) * (iidDist P_Y1 n).pmf y₁ else 0) =
          ∑ t : (Fin n → U) × (Fin n → X) × (Fin n → Y₁),
            if t ∈ A₁ then
              (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 else 0 := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u' _ => Finset.sum_comm
      rw [hprod, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    -- Term 2a (F₀ for Rx 2): true pair not in A₂
    have hE20 : (∑ y₂ : Fin n → Y₂, ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
        (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
          (if ((clouds m₂).1, y₂) ∉ A₂ then (1 : ℝ) else 0))) =
        1 - ∑ xy ∈ A₂, (jointIidDist P_UY2 n).pmf xy := by
      have hinner : ∀ y₂ : Fin n → Y₂,
          (∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
            (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if ((clouds m₂).1, y₂) ∉ A₂ then (1 : ℝ) else 0))) =
          ∑ u : Fin n → U, if (u, y₂) ∉ A₂ then (jointIidDist P_UY2 n).pmf (u, y₂) else 0 := by
        intro y₂
        rw [bc_sum_pi_prod_mul_single Q m₂
          (fun c => ((bcMarginal2 W).power n).trans (c.2 m₁) y₂ * (if (c.1, y₂) ∉ A₂ then (1 : ℝ) else 0))]
        dsimp only [Q]
        rw [cloudDist_sum_single_sat Pux n M₁ m₁
          (fun u x => ((bcMarginal2 W).power n).trans x y₂ * (if (u, y₂) ∉ A₂ then (1 : ℝ) else 0))]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hpull : ∑ x : Fin n → X,
            (iidDist Pux n).pmf (fun i => (u i, x i)) *
              (((bcMarginal2 W).power n).trans x y₂ * (if (u, y₂) ∉ A₂ then (1 : ℝ) else 0)) =
            (∑ x : Fin n → X, (iidDist Pux n).pmf (fun i => (u i, x i)) *
              ((bcMarginal2 W).power n).trans x y₂) * (if (u, y₂) ∉ A₂ then (1 : ℝ) else 0) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring
        rw [hpull, supIid_UY2_marginal]; split_ifs <;> ring
      simp_rw [hinner]
      rw [← Fintype.sum_prod_type_right (fun xy : (Fin n → U) × (Fin n → Y₂) =>
        if xy ∉ A₂ then (jointIidDist P_UY2 n).pmf xy else 0)]
      have hsplit : ∑ xy : (Fin n → U) × (Fin n → Y₂), (jointIidDist P_UY2 n).pmf xy =
          (∑ xy, if xy ∈ A₂ then (jointIidDist P_UY2 n).pmf xy else 0) +
          (∑ xy, if xy ∉ A₂ then (jointIidDist P_UY2 n).pmf xy else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun xy _ => by by_cases h : xy ∈ A₂ <;> simp [h]
      rw [(jointIidDist P_UY2 n).sum_one] at hsplit
      have hmem : (∑ xy, if xy ∈ A₂ then (jointIidDist P_UY2 n).pmf xy else 0) =
          ∑ xy ∈ A₂, (jointIidDist P_UY2 n).pmf xy := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      linarith
    -- Term 2b (F₁ for Rx 2): wrong cloud m₂' ≠ m₂
    have hE21 : ∀ m₂' ∈ Finset.univ.erase m₂,
        (∑ y₂ : Fin n → Y₂, ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
          (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
            (if ((clouds m₂').1, y₂) ∈ A₂ then (1 : ℝ) else 0))) =
        ∑ xy ∈ A₂, ((iidDist P_UY2.fst n).prod (iidDist P_UY2.snd n)).pmf xy := by
      intro m₂' hm₂'
      have hne : m₂' ≠ m₂ := (Finset.mem_erase.mp hm₂').1
      have hfst : P_UY2.fst = Pux.fst := by
        rw [← bc_probDist_map_fst, map_comp_eq]
        have hJux : J.map (fun z => z.1) = Pux := by
          have : J.map (fun z => z.1) = P_UXY1.map Prod.fst := by rw [map_comp_eq]; rfl
          rw [this, bc_probDist_map_fst]; dsimp only [P_UXY1, J]; rw [bcAuxJoint_map_UXY1, dmc_joint_fst]
        rw [← bc_probDist_map_fst, ← hJux, map_comp_eq]; rfl
      have hinner : ∀ y₂ : Fin n → Y₂,
          (∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
            (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if ((clouds m₂').1, y₂) ∈ A₂ then (1 : ℝ) else 0))) =
          ∑ u' : Fin n → U,
            if (u', y₂) ∈ A₂ then ((iidDist P_UY2.fst n).prod (iidDist P_UY2.snd n)).pmf (u', y₂) else 0 := by
        intro y₂
        rw [bc_sum_pi_prod_mul_pair Q m₂ m₂' hne
          (fun c => ((bcMarginal2 W).power n).trans (c.2 m₁) y₂)
          (fun c' => if (c'.1, y₂) ∈ A₂ then (1 : ℝ) else 0)]
        rw [cloudDist_sum_single_sat Pux n M₁ m₁ (fun _ x => ((bcMarginal2 W).power n).trans x y₂),
            supIid_Y2_marginal,
            cloudDist_sum_center_only Pux n M₁ (fun u' => if (u', y₂) ∈ A₂ then (1 : ℝ) else 0)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u' _ => ?_
        unfold ProbDist.prod; dsimp only; rw [hfst]; split_ifs <;> ring
      simp_rw [hinner]
      rw [← Fintype.sum_prod_type_right (fun xy : (Fin n → U) × (Fin n → Y₂) =>
        if xy ∈ A₂ then ((iidDist P_UY2.fst n).prod (iidDist P_UY2.snd n)).pmf xy else 0),
        ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    -- Step 3: Assemble the union bound over clouds
    have hrx1_le : ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
          (∑ y₁ : Fin n → Y₁, ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0)) ≤
        (1 - ∑ t ∈ A₁, (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t)) +
        ((M₁ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1))) - 4 * ε))) +
        (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo (J.map (fun z => (z.1.2, z.2.1))) - 3 * ε))) := by
      have hpt : ∀ clouds : Fin M₂ → CloudCode U X n M₁,
          w clouds * (∑ y₁ : Fin n → Y₁, ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0)) ≤
          (∑ y₁, w clouds * (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∉ A₁ then (1 : ℝ) else 0))) +
          (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y₁, w clouds * (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) +
          (∑ m₂' ∈ Finset.univ.erase m₂, ∑ m₁' : Fin M₁, ∑ y₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) := by
        intro clouds
        have hs1 : (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y₁, w clouds *
              (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
                (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
            ∑ y₁, ∑ m₁' ∈ Finset.univ.erase m₁, w clouds *
              (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
                (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0)) := Finset.sum_comm
        have hs2 : (∑ m₂' ∈ Finset.univ.erase m₂, ∑ m₁' : Fin M₁, ∑ y₁, w clouds *
              (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
                (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
            ∑ y₁, ∑ m₂' ∈ Finset.univ.erase m₂, ∑ m₁' : Fin M₁, w clouds *
              (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
                (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0)) := by
          trans (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y₁, ∑ m₁' : Fin M₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0)))
          · exact Finset.sum_congr rfl fun m₂' _ => Finset.sum_comm
          · exact Finset.sum_comm
        rw [Finset.mul_sum, hs1, hs2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun y₁ _ => ?_
        have hcoeff : 0 ≤ w clouds * ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ :=
          mul_nonneg (hw0 clouds) (((bcMarginal1 W).power n).nonneg _ _)
        have hind := supTypicalDec1_err_indicator_le W Pux n M₁ M₂ hM₁ hM₂ ε clouds y₁ m₁ m₂
        have hmul := mul_le_mul_of_nonneg_left hind hcoeff
        calc w clouds * (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0))
          _ = (w clouds * ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁) *
              (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0) := by ring
          _ ≤ _ := hmul
          _ = _ := by
              rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
              congr 1
              · congr 1
                · ring
                · exact Finset.sum_congr rfl fun _ _ => by ring
              · refine Finset.sum_congr rfl fun _ _ => ?_
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      have hsum_le := Finset.sum_le_sum fun clouds (_ : clouds ∈ Finset.univ) => hpt clouds
      simp_rw [Finset.sum_add_distrib] at hsum_le
      have hswap0 : (∑ clouds, ∑ y₁, w clouds * (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
            (if ((clouds m₂).1, (clouds m₂).2 m₁, y₁) ∉ A₁ then (1 : ℝ) else 0))) =
          1 - ∑ t ∈ A₁, (iidDist P_UXY1 n).pmf (supZipEquiv U X Y₁ n t) := by
        rw [Finset.sum_comm]; exact hE10
      have hswap1 : (∑ clouds, ∑ m₁' ∈ Finset.univ.erase m₁, ∑ y₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
          ((M₁ - 1 : ℕ) : ℝ) * ∑ t ∈ A₁, (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) *
            ((condChannel Pux).power n).trans t.1 t.2.1 := by
        rw [Finset.sum_comm]
        have hinner : ∀ m₁' ∈ Finset.univ.erase m₁,
            (∑ clouds, ∑ y₁, w clouds * (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂).1, (clouds m₂).2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
            ∑ t ∈ A₁, (iidDist P_UY1 n).pmf (fun i => (t.1 i, t.2.2 i)) *
              ((condChannel Pux).power n).trans t.1 t.2.1 := fun m₁' hm₁' => by
          rw [Finset.sum_comm]; exact hE11 m₁' hm₁'
        rw [Finset.sum_congr rfl hinner, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ m₁), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hswap2 : (∑ clouds, ∑ m₂' ∈ Finset.univ.erase m₂, ∑ m₁' : Fin M₁, ∑ y₁, w clouds *
            (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
          (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) * ∑ t ∈ A₁,
            (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 := by
        rw [Finset.sum_comm]
        have hinner : ∀ m₂' ∈ Finset.univ.erase m₂,
            (∑ clouds, ∑ m₁' : Fin M₁, ∑ y₁, w clouds *
              (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
                (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
            (M₁ : ℝ) * ∑ t ∈ A₁,
              (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 := fun m₂' hm₂' => by
          rw [Finset.sum_comm]
          have hm1 : ∀ m₁' : Fin M₁,
              (∑ clouds, ∑ y₁, w clouds * (((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
                (if ((clouds m₂').1, (clouds m₂').2 m₁', y₁) ∈ A₁ then (1 : ℝ) else 0))) =
              ∑ t ∈ A₁, (iidDist Pux n).pmf (fun i => (t.1 i, t.2.1 i)) * (iidDist P_Y1 n).pmf t.2.2 :=
            fun m₁' => by rw [Finset.sum_comm]; exact hE12 m₂' hm₂' m₁'
          rw [Finset.sum_congr rfl fun m₁' _ => hm1 m₁', Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ m₂), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← mul_assoc, Nat.cast_mul]
      rw [hswap0, hswap1, hswap2] at hsum_le
      have hpack := supTypicalSet_indep_bounds W Pux n ε
      dsimp only at hpack
      have hb1 := mul_le_mul_of_nonneg_left hpack.1 (Nat.cast_nonneg (M₁ - 1))
      have hb2 := mul_le_mul_of_nonneg_left hpack.2 (Nat.cast_nonneg ((M₂ - 1) * M₁))
      linarith
    have hrx2_le : ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
          (∑ y₂ : Fin n → Y₂, ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
            (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0)) ≤
        (1 - ∑ xy ∈ A₂, (jointIidDist P_UY2 n).pmf xy) +
        ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P_UY2 - 3 * ε))) := by
      have hpt : ∀ clouds : Fin M₂ → CloudCode U X n M₁,
          w clouds * (∑ y₂ : Fin n → Y₂, ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
            (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0)) ≤
          (∑ y₂, w clouds * (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
            (if ((clouds m₂).1, y₂) ∉ A₂ then (1 : ℝ) else 0))) +
          (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y₂, w clouds *
            (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if ((clouds m₂').1, y₂) ∈ A₂ then (1 : ℝ) else 0))) := by
        intro clouds
        rw [Finset.mul_sum, Finset.sum_comm (s := Finset.univ.erase m₂), ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun y₂ _ => ?_
        have hcoeff : 0 ≤ w clouds * ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ :=
          mul_nonneg (hw0 clouds) (((bcMarginal2 W).power n).nonneg _ _)
        have hind := supTypicalDec2_err_indicator_le P_UY2 n M₂ hM₂ ε (fun k => (clouds k).1) y₂ m₂
        have hmul := mul_le_mul_of_nonneg_left hind hcoeff
        calc w clouds * (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0))
          _ = (w clouds * ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂) *
              (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0) := by ring
          _ ≤ _ := hmul
          _ = _ := by
              rw [mul_add, Finset.mul_sum]
              congr 1
              · ring
              · exact Finset.sum_congr rfl fun _ _ => by ring
      have hsum_le := Finset.sum_le_sum fun clouds (_ : clouds ∈ Finset.univ) => hpt clouds
      rw [Finset.sum_add_distrib] at hsum_le
      have hswap0 : (∑ clouds, ∑ y₂, w clouds * (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
            (if ((clouds m₂).1, y₂) ∉ A₂ then (1 : ℝ) else 0))) =
          1 - ∑ xy ∈ A₂, (jointIidDist P_UY2 n).pmf xy := by
        rw [Finset.sum_comm]; exact hE20
      have hswap1 : (∑ clouds, ∑ m₂' ∈ Finset.univ.erase m₂, ∑ y₂, w clouds *
            (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if ((clouds m₂').1, y₂) ∈ A₂ then (1 : ℝ) else 0))) =
          ((M₂ - 1 : ℕ) : ℝ) * ∑ xy ∈ A₂, ((iidDist P_UY2.fst n).prod (iidDist P_UY2.snd n)).pmf xy := by
        rw [Finset.sum_comm]
        have hinner : ∀ m₂' ∈ Finset.univ.erase m₂,
            (∑ clouds, ∑ y₂, w clouds * (((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if ((clouds m₂').1, y₂) ∈ A₂ then (1 : ℝ) else 0))) =
            ∑ xy ∈ A₂, ((iidDist P_UY2.fst n).prod (iidDist P_UY2.snd n)).pmf xy := fun m₂' hm₂' => by
          rw [Finset.sum_comm]; exact hE21 m₂' hm₂'
        rw [Finset.sum_congr rfl hinner, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ m₂), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hswap0, hswap1] at hsum_le
      have hpack2 := jointTypicalSet_indep_prob_le P_UY2 n ε
      have hb2 := mul_le_mul_of_nonneg_left hpack2 (Nat.cast_nonneg (M₂ - 1))
      linarith
    calc ∑ clouds, w clouds * (∑ y : Fin n → Y₁ × Y₂,
            if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
            then (W.power n).trans ((clouds m₂).2 m₁) y else 0)
      _ ≤ ∑ clouds, (w clouds * (∑ y₁, ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0)) +
            w clouds * (∑ y₂, ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0))) := by
          refine Finset.sum_le_sum fun clouds _ => ?_
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (hsplit_rx clouds) (hw0 clouds)
      _ = (∑ clouds, w clouds * (∑ y₁, ((bcMarginal1 W).power n).trans ((clouds m₂).2 m₁) y₁ *
              (if dec₁Of clouds y₁ ≠ m₁ then (1 : ℝ) else 0))) +
          (∑ clouds, w clouds * (∑ y₂, ((bcMarginal2 W).power n).trans ((clouds m₂).2 m₁) y₂ *
              (if dec₂Of clouds y₂ ≠ m₂ then (1 : ℝ) else 0))) := Finset.sum_add_distrib
      _ ≤ B := by dsimp only [B]; linarith
  -- Average over `(m₁, m₂)` and extract a deterministic codebook
  have hexp_le : ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds * bcErr clouds ≤ B := by
    have havg : ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds * bcErr clouds =
        ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ clouds : Fin M₂ → CloudCode U X n M₁, w clouds *
            (∑ y : Fin n → Y₁ × Y₂,
              if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
              then (W.power n).trans ((clouds m₂).2 m₁) y else 0) := by
      have h1 : ∀ clouds, w clouds * bcErr clouds =
          ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
            ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, w clouds * ∑ y : Fin n → Y₁ × Y₂,
              if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
              then (W.power n).trans ((clouds m₂).2 m₁) y else 0 := fun clouds => by
        dsimp only [bcErr]
        rw [← mul_assoc, mul_comm (w clouds), mul_assoc, Finset.mul_sum]
        congr 1; exact Finset.sum_congr rfl fun m₁ _ => Finset.mul_sum _ _ _
      simp_rw [h1]
      rw [← Finset.mul_sum]
      congr 1
      trans (∑ m₁ : Fin M₁, ∑ clouds : Fin M₂ → CloudCode U X n M₁, ∑ m₂ : Fin M₂,
          w clouds * ∑ y : Fin n → Y₁ × Y₂,
            if dec₁Of clouds (fun i => (y i).1) ≠ m₁ ∨ dec₂Of clouds (fun i => (y i).2) ≠ m₂
            then (W.power n).trans ((clouds m₂).2 m₁) y else 0)
      · exact Finset.sum_comm
      · exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    rw [havg]
    have hM12_pos : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hM₁ hM₂
    calc ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ clouds, w clouds * _
      _ ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁, ∑ _m₂ : Fin M₂, B :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => hpair m₁ m₂) (by positivity)
      _ = ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (((M₁ * M₂ : ℕ) : ℝ) * B) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = B := by field_simp [hM12_pos.ne']
  obtain ⟨clouds, hclouds⟩ := bc_exists_le_of_weighted_sum_le w bcErr B hw0 hw1 hexp_le
  exact ⟨fun m₁ m₂ => (clouds m₂).2 m₁, dec₁Of clouds, dec₂Of clouds, hclouds⟩

/-- Zero rate pair `(0, 0)` is achievable over any DMBC on a nonempty input alphabet. -/
private lemma isBCAchievable_zero_zero [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) :
    IsBCAchievable W 0 0 := by
  refine ⟨le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  have h1 : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  rw [h1]
  let x₀ : X := Classical.arbitrary X
  refine ⟨fun _ _ _ => x₀, fun _ => 0, fun _ => 0, ?_⟩
  have hz : ∀ (m₁ m₂ : Fin 1) (y : Fin n → Y₁ × Y₂),
      ¬ ((0 : Fin 1) ≠ m₁ ∨ (0 : Fin 1) ≠ m₂) := fun m₁ m₂ _ => by
    have h1 : m₁ = 0 := Subsingleton.elim _ _
    have h2 : m₂ = 0 := Subsingleton.elim _ _
    simp [h1, h2]
  have herr0 : ((1 : ℝ) / ((1 * 1 : ℕ) : ℝ)) *
      ∑ m₁ : Fin 1, ∑ m₂ : Fin 1, ∑ y : Fin n → Y₁ × Y₂,
        (if (0 : Fin 1) ≠ m₁ ∨ (0 : Fin 1) ≠ m₂ then (W.power n).trans (fun _ => x₀) y else 0) = 0 := by
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m₁ _ =>
      Finset.sum_eq_zero fun m₂ _ => Finset.sum_eq_zero fun y _ => by simp [hz m₁ m₂ y])
  linarith

/-- **Unified Superposition Achievability**: covers both strictly interior pairs (`R₁ > 0, R₂ > 0`)
    and axis pairs (`R₁ = 0` or `R₂ = 0`), requiring strict inequality only on positive rates. -/
private lemma superposition_achievable_general (W : BroadcastChannel X Y₁ Y₂)
    (Pux : ProbDist (U × X)) {R₁ R₂ : ℝ} (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (hR₂ : R₂ = 0 ∨ R₂ < mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))))
    (hR₁ : R₁ = 0 ∨ R₁ < condMutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1, z.1.1))))
    (hRsum : R₂ = 0 ∨ R₁ + R₂ < mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1)))) :
    IsBCAchievable W R₁ R₂ := by
  have hUXne : Nonempty (U × X) := bc_nonempty_of_probDist Pux
  have : Nonempty X := ⟨hUXne.some.2⟩
  let J := bcAuxJoint W Pux
  let I2 := mutualInfo (J.map (fun z => (z.1.1, z.2.2)))
  let I1 := condMutualInfo (J.map (fun z => (z.1.2, z.2.1, z.1.1)))
  let Isum := mutualInfo (J.map (fun z => (z.1.2, z.2.1)))
  -- Pick a single positive gap `Δ` across all active (nonzero-rate) constraints
  let g1 : ℝ := if R₁ = 0 then 1 else I1 - R₁
  let g2 : ℝ := if R₂ = 0 then 1 else I2 - R₂
  let g3 : ℝ := if R₂ = 0 then 1 else Isum - (R₁ + R₂)
  have hg1 : 0 < g1 := by
    dsimp only [g1]; split_ifs with h
    · exact zero_lt_one
    · linarith [hR₁.resolve_left h]
  have hg2 : 0 < g2 := by
    dsimp only [g2]; split_ifs with h
    · exact zero_lt_one
    · linarith [hR₂.resolve_left h]
  have hg3 : 0 < g3 := by
    dsimp only [g3]; split_ifs with h
    · exact zero_lt_one
    · linarith [hRsum.resolve_left h]
  let ε : ℝ := min (min g1 g2) g3 / 5
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨hR₁0, hR₂0, fun δ hδ => ?_⟩
  have hδ5 : 0 < δ / 5 := by linarith
  obtain ⟨N₁, hN₁⟩ := sup_aep_prob_tendsto_one W Pux hε hδ5
  obtain ⟨N₂, hN₂⟩ := joint_aep_prob_tendsto_one (J.map (fun z => (z.1.1, z.2.2))) hε hδ5
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (log2 (1 / (δ / 5)) / ε)
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  dsimp only
  let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  obtain ⟨enc, dec₁, dec₂, hbound⟩ := superposition_random_coding_bound W Pux n M₁ M₂ hM₁ hM₂ ε
  refine ⟨enc, dec₁, dec₂, ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ N₃)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ N₃)) hn
  have hn3 : log2 (1 / (δ / 5)) / ε ≤ (n : ℝ) :=
    le_trans hN₃ (by exact_mod_cast le_trans (le_max_right _ N₃) hn)
  have hpow_le : (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ / 5 := bc_two_rpow_neg_le_of_ge hε hδ5 hn3
  have ht1 : 1 - ∑ t ∈ supTypicalSet W Pux n ε,
      (iidDist (J.map (fun z => (z.1, z.2.1))) n).pmf (supZipEquiv U X Y₁ n t) ≤ δ / 5 := by
    have := hN₁ n hn1; linarith
  have ht2 : 1 - ∑ xy ∈ jointTypicalSet (J.map (fun z => (z.1.1, z.2.2))) n ε,
      (jointIidDist (J.map (fun z => (z.1.1, z.2.2))) n).pmf xy ≤ δ / 5 := by
    have := hN₂ n hn2; linarith
  have ht3 : ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I1 - 4 * ε))) ≤ δ / 5 := by
    by_cases h0 : R₁ = 0
    · have hM1_eq : M₁ = 1 := by dsimp only [M₁]; rw [h0]; simp
      rw [hM1_eq]; simp; linarith
    · have hgap : 5 * ε ≤ I1 - R₁ := by
        have h1 : 5 * ε ≤ g1 := by
          dsimp only [ε]
          have := le_trans (min_le_left (min g1 g2) g3) (min_le_left g1 g2)
          linarith
        simpa [g1, h0] using h1
      calc ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I1 - 4 * ε)))
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (I1 - 4 * ε))) :=
            mul_le_mul_of_nonneg_right (bc_sub_one_max_floor_le n hR₁0) (by positivity)
        _ = (2 : ℝ) ^ ((n : ℝ) * R₁ + -((n : ℝ) * (I1 - 4 * ε))) :=
            (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
        _ ≤ (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
        _ ≤ δ / 5 := hpow_le
  have ht4 : (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (Isum - 3 * ε))) ≤ δ / 5 := by
    by_cases h0 : R₂ = 0
    · have hM2_eq : M₂ = 1 := by dsimp only [M₂]; rw [h0]; simp
      rw [hM2_eq]; simp; linarith
    · have hgap : 5 * ε ≤ Isum - (R₁ + R₂) := by
        have h1 : 5 * ε ≤ g3 := by dsimp only [ε]; linarith [min_le_right (min g1 g2) g3]
        simpa [g3, h0] using h1
      have hMprod : (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) := by
        rw [Nat.cast_mul]
        calc ((M₂ - 1 : ℕ) : ℝ) * (M₁ : ℝ)
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ ((n : ℝ) * R₁) :=
              mul_le_mul (bc_sub_one_max_floor_le n hR₂0) (bc_max_one_floor_two_rpow_le n hR₁0)
                (Nat.cast_nonneg _) (by positivity)
          _ = (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      calc (((M₂ - 1 : ℕ) * M₁ : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (Isum - 3 * ε)))
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) * (2 : ℝ) ^ (-((n : ℝ) * (Isum - 3 * ε))) :=
            mul_le_mul_of_nonneg_right hMprod (by positivity)
        _ = (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂) + -((n : ℝ) * (Isum - 3 * ε))) :=
            (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
        _ ≤ (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
        _ ≤ δ / 5 := hpow_le
  have ht5 : ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I2 - 3 * ε))) ≤ δ / 5 := by
    by_cases h0 : R₂ = 0
    · have hM2_eq : M₂ = 1 := by dsimp only [M₂]; rw [h0]; simp
      rw [hM2_eq]; simp; linarith
    · have hgap : 5 * ε ≤ I2 - R₂ := by
        have h1 : 5 * ε ≤ g2 := by
          dsimp only [ε]
          have := le_trans (min_le_left (min g1 g2) g3) (min_le_right g1 g2)
          linarith
        simpa [g2, h0] using h1
      calc ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I2 - 3 * ε)))
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (I2 - 3 * ε))) :=
            mul_le_mul_of_nonneg_right (bc_sub_one_max_floor_le n hR₂0) (by positivity)
        _ = (2 : ℝ) ^ ((n : ℝ) * R₂ + -((n : ℝ) * (I2 - 3 * ε))) :=
            (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
        _ ≤ (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
        _ ≤ δ / 5 := hpow_le
  linarith

/-- **Superposition Coding Achievability Theorem** (Cover 1972; Cover & Thomas §15.6;
    El Gamal–Kim Thm. 5.1): for any 2-receiver DMBC `W`, any finite auxiliary `U` and joint law
    `Pux : ProbDist (U × X)`, every strictly interior rate pair `(R₁, R₂)` with
    `R₂ < I(U; Y₂)`, `R₁ < I(X; Y₁ | U)`, and `R₁ + R₂ < I(X; Y₁)` is operationally achievable. -/
theorem superposition_coding_achievability (W : BroadcastChannel X Y₁ Y₂)
    (Pux : ProbDist (U × X)) {R₁ R₂ : ℝ} (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (hR₂ : R₂ < mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))))
    (hR₁ : R₁ < condMutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1, z.1.1))))
    (hRsum : R₁ + R₂ < mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1)))) :
    IsBCAchievable W R₁ R₂ :=
  superposition_achievable_general W Pux hR₁0 hR₂0 (Or.inr hR₂) (Or.inr hR₁) (Or.inr hRsum)

/-- **Superposition Coding Inner Bound**: `superpositionInnerBound W ⊆ bcCapacityRegion W`
    for every two-receiver DMBC `W`. -/
theorem superpositionInnerBound_subset_bcCapacityRegion (W : BroadcastChannel X Y₁ Y₂) :
    superpositionInnerBound W ⊆ bcCapacityRegion W := by
  refine closure_minimal ?_ isClosed_closure
  rintro ⟨R₁, R₂⟩ ⟨hR₁0, hR₂0, kU, Pux, h2, h1, hsum⟩
  have hUXne : Nonempty (Fin kU × X) := bc_nonempty_of_probDist Pux
  have : Nonempty X := ⟨hUXne.some.2⟩
  unfold bcCapacityRegion
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hR₁0.eq_or_lt with rfl | hR₁pos
  · rcases hR₂0.eq_or_lt with rfl | hR₂pos
    · exact ⟨(0, 0), isBCAchievable_zero_zero W, by simp [hε]⟩
    · let lam : ℝ := max 0 (1 - ε / (2 * R₂))
      have hlam0 : 0 ≤ lam := le_max_left _ _
      have hlam1 : lam < 1 := max_lt zero_lt_one (by have : 0 < ε / (2 * R₂) := by positivity
                                                     linarith)
      refine ⟨(0, lam * R₂), ?_, ?_⟩
      · exact superposition_achievable_general W Pux le_rfl (mul_nonneg hlam0 hR₂0)
          (Or.inr (by nlinarith)) (Or.inl rfl) (Or.inr (by nlinarith))
      · rw [Prod.dist_eq]
        refine max_lt (by simp [hε]) ?_
        rw [Real.dist_eq, abs_of_nonneg (by nlinarith)]
        have hlam_ge : 1 - ε / (2 * R₂) ≤ lam := le_max_right _ _
        have hmul : (1 - ε / (2 * R₂)) * R₂ ≤ lam * R₂ := mul_le_mul_of_nonneg_right hlam_ge hR₂0
        have hsimp : (1 - ε / (2 * R₂)) * R₂ = R₂ - ε / 2 := by field_simp [hR₂pos.ne']
        linarith
  · rcases hR₂0.eq_or_lt with rfl | hR₂pos
    · let lam : ℝ := max 0 (1 - ε / (2 * R₁))
      have hlam0 : 0 ≤ lam := le_max_left _ _
      have hlam1 : lam < 1 := max_lt zero_lt_one (by have : 0 < ε / (2 * R₁) := by positivity
                                                     linarith)
      refine ⟨(lam * R₁, 0), ?_, ?_⟩
      · exact superposition_achievable_general W Pux (mul_nonneg hlam0 hR₁0) le_rfl
          (Or.inl rfl) (Or.inr (by nlinarith)) (Or.inl rfl)
      · rw [Prod.dist_eq]
        refine max_lt ?_ (by simp [hε])
        rw [Real.dist_eq, abs_of_nonneg (by nlinarith)]
        have hlam_ge : 1 - ε / (2 * R₁) ≤ lam := le_max_right _ _
        have hmul : (1 - ε / (2 * R₁)) * R₁ ≤ lam * R₁ := mul_le_mul_of_nonneg_right hlam_ge hR₁0
        have hsimp : (1 - ε / (2 * R₁)) * R₁ = R₁ - ε / 2 := by field_simp [hR₁pos.ne']
        linarith
    · let M : ℝ := max R₁ R₂
      have hMpos : 0 < M := lt_of_lt_of_le hR₁pos (le_max_left _ _)
      let lam : ℝ := max 0 (1 - ε / (2 * M))
      have hlam0 : 0 ≤ lam := le_max_left _ _
      have hlam1 : lam < 1 := max_lt zero_lt_one (by have : 0 < ε / (2 * M) := by positivity
                                                     linarith)
      refine ⟨(lam * R₁, lam * R₂), ?_, ?_⟩
      · exact superposition_coding_achievability W Pux (mul_nonneg hlam0 hR₁0)
          (mul_nonneg hlam0 hR₂0) (by nlinarith) (by nlinarith) (by nlinarith)
      · rw [Prod.dist_eq]
        have hlam_ge : 1 - ε / (2 * M) ≤ lam := le_max_right _ _
        have h1m : 1 - lam ≤ ε / (2 * M) := by linarith
        have hd1 : dist R₁ (lam * R₁) < ε := by
          rw [Real.dist_eq, abs_of_nonneg (by nlinarith)]
          have hle : R₁ - lam * R₁ ≤ (ε / (2 * M)) * M := by
            calc R₁ - lam * R₁ = (1 - lam) * R₁ := by ring
              _ ≤ (ε / (2 * M)) * M := mul_le_mul h1m (le_max_left _ _) hR₁0 (by positivity)
          have hsimp : (ε / (2 * M)) * M = ε / 2 := by field_simp [hMpos.ne']
          linarith
        have hd2 : dist R₂ (lam * R₂) < ε := by
          rw [Real.dist_eq, abs_of_nonneg (by nlinarith)]
          have hle : R₂ - lam * R₂ ≤ (ε / (2 * M)) * M := by
            calc R₂ - lam * R₂ = (1 - lam) * R₂ := by ring
              _ ≤ (ε / (2 * M)) * M := mul_le_mul h1m (le_max_right _ _) hR₂0 (by positivity)
          have hsimp : (ε / (2 * M)) * M = ε / 2 := by field_simp [hMpos.ne']
          linarith
        exact max_lt hd1 hd2

end SuperpositionAchievability

/-! ### 3. Degraded Broadcast Channel Capacity Region Theorem (Cover & Thomas Thm. 15.6.2) -/

section DegradedBCConverse

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-- For a physically degraded DMBC, the sum-rate bound `R₁ + R₂ ≤ I(X; Y₁)` in
    `superpositionInnerBound` is redundant (by DPI `I(U; Y₂) ≤ I(U; Y₁)`), so
    `superpositionInnerBound W = degradedBCRegion W`. -/
theorem superpositionInnerBound_eq_degradedBCRegion (W : BroadcastChannel X Y₁ Y₂)
    (hdeg : IsPhysicallyDegradedBC W) :
    superpositionInnerBound W = degradedBCRegion W := by
  unfold superpositionInnerBound degradedBCRegion
  congr 1; ext r
  constructor
  · rintro ⟨h1, h2, kU, Pux, hr2, hr1, _⟩
    exact ⟨h1, h2, kU, Pux, hr2, hr1⟩
  · rintro ⟨h1, h2, kU, Pux, hr2, hr1⟩
    refine ⟨h1, h2, kU, Pux, hr2, hr1, ?_⟩
    have hdpi := bcAuxJoint_dpi_U_Y2_le W hdeg Pux
    have hchain := bcAuxJoint_chain_Y1 W Pux
    linarith

/-! #### Prefix History Representation & Telescoping Chain Rule -/

/-- Fixed-type representation of the prefix `y^{<k}` as `Fin n → Option A`. -/
private def prefixHist {A : Type*} {n : ℕ} (k : ℕ) (y : Fin n → A) : Fin n → Option A :=
  fun j => if j.1 < k then some (y j) else none

private lemma prefixHist_zero {A : Type*} {n : ℕ} (y : Fin n → A) :
    prefixHist 0 y = fun _ => none := by
  funext j; simp [prefixHist]

private lemma prefixHist_self {A : Type*} {n : ℕ} (y : Fin n → A) :
    prefixHist n y = fun j => some (y j) := by
  funext j; simp [prefixHist, j.2]

private lemma prefixHist_step_entropy {Ω A Z : Type*} [Fintype Ω] [Fintype A] [Fintype Z]
    [Nonempty A] {n : ℕ} (P : ProbDist Ω) (z : Ω → Z) (y : Ω → Fin n → A) (i : Fin n) :
    shannonEntropy (P.map (fun ω => (z ω, prefixHist (i.1 + 1) (y ω)))) =
      shannonEntropy (P.map (fun ω => (z ω, (y ω i, prefixHist i.1 (y ω))))) := by
  let a₀ : A := Classical.arbitrary A
  let h₁ : Z × (Fin n → Option A) → Z × (A × (Fin n → Option A)) :=
    fun p => (p.1, (p.2 i).getD a₀, fun j => if j = i then none else p.2 j)
  let h₂ : Z × (A × (Fin n → Option A)) → Z × (Fin n → Option A) :=
    fun p => (p.1, fun j => if j = i then some p.2.1 else p.2.2 j)
  refine bc_shannonEntropy_map_eq_of_factors P _ _ h₁ h₂ ?_ ?_
  · intro ω
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp [h₁, prefixHist]
    · funext j; dsimp only [h₁, prefixHist]
      by_cases hj : j = i
      · subst hj; simp
      · have hiff : j.1 < i.1 + 1 ↔ j.1 < i.1 := by
          have : j.1 ≠ i.1 := fun h => hj (Fin.ext h)
          omega
        simp [hj, hiff]
  · intro ω
    refine Prod.ext rfl ?_
    funext j; dsimp only [h₂, prefixHist]
    by_cases hj : j = i
    · subst hj; simp
    · have hiff : j.1 < i.1 ↔ j.1 < i.1 + 1 := by
        have : j.1 ≠ i.1 := fun h => hj (Fin.ext h)
        omega
      simp [hj, hiff]

private lemma prefixHist_telescope {Ω A Z : Type*} [Fintype Ω] [Fintype A] [Fintype Z]
    [Nonempty A] {n : ℕ} (P : ProbDist Ω) (z : Ω → Z) (y : Ω → Fin n → A) :
    shannonEntropy (P.map (fun ω => (z ω, y ω))) - shannonEntropy (P.map z) =
      ∑ i : Fin n, condEntropy (P.map (fun ω => (y ω i, (z ω, prefixHist i.1 (y ω))))) := by
  let F : ℕ → ℝ := fun k => shannonEntropy (P.map (fun ω => (z ω, prefixHist k (y ω))))
  have hF0 : F 0 = shannonEntropy (P.map z) := by
    dsimp only [F]
    refine bc_shannonEntropy_map_eq_of_factors P _ _ Prod.fst (fun zv => (zv, fun _ => none))
      (fun _ => rfl) (fun ω => by simp [prefixHist_zero])
  have hFn : F n = shannonEntropy (P.map (fun ω => (z ω, y ω))) := by
    dsimp only [F]
    let a₀ : A := Classical.arbitrary A
    refine bc_shannonEntropy_map_eq_of_factors P _ _
      (fun p => (p.1, fun j => (p.2 j).getD a₀))
      (fun p => (p.1, fun j => some (p.2 j)))
      (fun ω => by ext <;> simp [prefixHist_self])
      (fun ω => by ext <;> simp [prefixHist_self])
  have htele : ∀ m : ℕ, m ≤ n →
      F m - F 0 = ∑ j : Fin m, (F (j.1 + 1) - F j.1) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Fin.sum_univ_castSucc]
      have hprev := ih (Nat.le_of_succ_le hk)
      dsimp only [Fin.val_castSucc, Fin.val_last]
      linarith
  have hstep : ∀ i : Fin n,
      F (i.1 + 1) - F i.1 = condEntropy (P.map (fun ω => (y ω i, (z ω, prefixHist i.1 (y ω))))) := by
    intro i
    dsimp only [F]
    rw [prefixHist_step_entropy P z y i]
    let e : (Z × (A × (Fin n → Option A))) ≃ (A × (Z × (Fin n → Option A))) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, (t.1, t.2.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have h1 : P.map (fun ω => (y ω i, (z ω, prefixHist i.1 (y ω)))) =
        (P.map (fun ω => (z ω, (y ω i, prefixHist i.1 (y ω))))).map e := by
      rw [map_comp_eq]; rfl
    have h2 : (P.map (fun ω => (y ω i, (z ω, prefixHist i.1 (y ω))))).snd =
        P.map (fun ω => (z ω, prefixHist i.1 (y ω))) := by
      rw [← bc_probDist_map_snd, map_comp_eq]; rfl
    unfold condEntropy
    rw [h2, h1, shannonEntropy_map_equiv e]
  rw [← hFn, ← hF0, htele n le_rfl]
  exact Finset.sum_congr rfl fun i _ => hstep i

/-! #### Degraded History Kernel `K_opt` & `K_hist` for Coordinate-Wise DPI -/

/-- Lift a DMC `K : DMC Y₁ Y₂` to `Option Y₁ → Option Y₂` preserving `none` deterministically. -/
private def optionChannel (K : DMC Y₁ Y₂) : DMC (Option Y₁) (Option Y₂) where
  trans := fun o₁ o₂ =>
    match o₁, o₂ with
    | none, none => 1
    | none, some _ => 0
    | some _, none => 0
    | some y₁, some y₂ => K.trans y₁ y₂
  nonneg := fun o₁ o₂ => by
    cases o₁ <;> cases o₂
    · exact zero_le_one
    · exact le_rfl
    · exact le_rfl
    · exact K.nonneg _ _
  sum_one := fun o₁ => by
    cases o₁ with
    | none => simp
    | some y₁ => simp [K.sum_one y₁]

/-- Joint law of a broadcast code `(enc, dec₁, dec₂)` with uniform independent messages
    `(M₁, M₂) ~ Unif(Fin M₁ × Fin M₂)` transmitted over `W^n`. -/
private noncomputable def bcCodeDist (W : BroadcastChannel X Y₁ Y₂) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (enc : Fin M₁ → Fin M₂ → Fin n → X) :
    ProbDist ((Fin M₁ × Fin M₂) × (Fin n → Y₁ × Y₂)) :=
  haveI : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, hM₁⟩, ⟨0, hM₂⟩)⟩
  (dmcPrecomp (W.power n) (fun m => enc m.1 m.2)).joint (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂))

/-- **Fano Bounds for a Broadcast Code**:
    `(1 - err) * log₂ M₂ ≤ I(M₂; Y₂^n) + 1` and `(1 - err) * log₂ M₁ ≤ I(M₁; Y₁^n | M₂) + 1`. -/
private lemma bc_code_fano_bounds (W : BroadcastChannel X Y₁ Y₂) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc : Fin M₁ → Fin M₂ → Fin n → X)
    (dec₁ : (Fin n → Y₁) → Fin M₁) (dec₂ : (Fin n → Y₂) → Fin M₂) :
    let P := bcCodeDist W hM₁ hM₂ enc
    let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
        if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
        then (W.power n).trans (enc m₁ m₂) y else 0
    (1 - err) * log2 (M₂ : ℝ) ≤
      mutualInfo (P.map (fun z => (z.1.2, fun i => (z.2 i).2))) + 1 ∧
    (1 - err) * log2 (M₁ : ℝ) ≤
      condMutualInfo (P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))) + 1 := by
  classical
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, hM₁⟩, ⟨0, hM₂⟩)⟩
  dsimp only
  let P := bcCodeDist W hM₁ hM₂ enc
  let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
    ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
      if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
      then (W.power n).trans (enc m₁ m₂) y else 0
  have hP_pmf : ∀ m₁ m₂ y, P.pmf ((m₁, m₂), y) =
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (W.power n).trans (enc m₁ m₂) y := by
    intro m₁ m₂ y
    unfold P bcCodeDist DMC.joint dmcPrecomp ProbDist.uniform
    simp [Fintype.card_prod, Fintype.card_fin]
  have hlog1_nn : 0 ≤ log2 (M₁ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
    have := bc_log2_mono zero_lt_one h1; simpa [log2] using this
  have hlog2_nn : 0 ≤ log2 (M₂ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM₂
    have := bc_log2_mono zero_lt_one h1; simpa [log2] using this
  -- Marginal of `(M₁, M₂)` is uniform
  have hP_M : P.map Prod.fst = (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)) := by
    rw [bc_probDist_map_fst]; exact dmc_joint_fst _ _
  have hP_M2 : P.map (fun z => z.1.2) = (ProbDist.uniform : ProbDist (Fin M₂)) := by
    have h : P.map (fun z => z.1.2) = (P.map Prod.fst).map Prod.snd := by rw [map_comp_eq]; rfl
    rw [h, hP_M, bc_probDist_map_snd]
    apply bc_probDist_ext; intro m₂
    unfold ProbDist.snd ProbDist.uniform; simp [Fintype.card_prod, Fintype.card_fin]
    have hM1r : (M₁ : ℝ) ≠ 0 := by exact_mod_cast hM₁.ne'
    have hM2r : (M₂ : ℝ) ≠ 0 := by exact_mod_cast hM₂.ne'
    field_simp [hM1r, hM2r]
  have hHM2 : shannonEntropy (P.map (fun z => z.1.2)) = log2 (M₂ : ℝ) := by
    rw [hP_M2, (shannonEntropy_eq_log2_card_iff _).mpr rfl, Fintype.card_fin]
  have hHM12 : shannonEntropy (P.map Prod.fst) = log2 (M₁ : ℝ) + log2 (M₂ : ℝ) := by
    rw [hP_M, (shannonEntropy_eq_log2_card_iff _).mpr rfl, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, Nat.cast_mul, log2_mul_pos (by exact_mod_cast hM₁) (by exact_mod_cast hM₂)]
  constructor
  · -- Receiver 2 Fano
    let P2 := P.map (fun z => (z.1.2, fun i => (z.2 i).2))
    have hfano := fano_inequality_card P2 dec₂
    rw [Fintype.card_fin] at hfano
    have hpe2_le : estErrorProb P2 dec₂ ≤ err := by
      rw [bc_estErrorProb_map_pair]
      dsimp only [err]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_le_sum fun m₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [hP_pmf]
      have hnn : 0 ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (W.power n).trans (enc m₁ m₂) y :=
        mul_nonneg (by positivity) ((W.power n).nonneg _ _)
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (Or.inr h1) h2
      · exact hnn
      · simp
    have hbin : binaryEntropy (estErrorProb P2 dec₂) ≤ 1 :=
      InfoTheory.Known.binaryEntropy_le_one (estErrorProb_nonneg P2 dec₂) (estErrorProb_le_one P2 dec₂)
    have hfst : P2.fst = P.map (fun z => z.1.2) := by
      rw [← bc_probDist_map_fst, map_comp_eq]; rfl
    have hid : mutualInfo P2 = log2 (M₂ : ℝ) - condEntropy P2 := by
      unfold mutualInfo condEntropy; rw [hfst, hHM2]; ring
    have hmul : estErrorProb P2 dec₂ * log2 (M₂ : ℝ) ≤ err * log2 (M₂ : ℝ) :=
      mul_le_mul_of_nonneg_right hpe2_le hlog2_nn
    linarith
  · -- Receiver 1 Fano conditioned on M₂
    let P1 := P.map (fun z => (z.1.1, ((fun i => (z.2 i).1), z.1.2)))
    let g1 : (Fin n → Y₁) × Fin M₂ → Fin M₁ := fun p => dec₁ p.1
    have hfano := fano_inequality_card P1 g1
    rw [Fintype.card_fin] at hfano
    have hpe1_le : estErrorProb P1 g1 ≤ err := by
      rw [bc_estErrorProb_map_pair]
      dsimp only [err, g1]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_le_sum fun m₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [hP_pmf]
      have hnn : 0 ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (W.power n).trans (enc m₁ m₂) y :=
        mul_nonneg (by positivity) ((W.power n).nonneg _ _)
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (Or.inl h1) h2
      · exact hnn
      · simp
    have hbin : binaryEntropy (estErrorProb P1 g1) ≤ 1 :=
      InfoTheory.Known.binaryEntropy_le_one (estErrorProb_nonneg P1 g1) (estErrorProb_le_one P1 g1)
    have hmul : estErrorProb P1 g1 * log2 (M₁ : ℝ) ≤ err * log2 (M₁ : ℝ) :=
      mul_le_mul_of_nonneg_right hpe1_le hlog1_nn
    have hcmi_eq : condMutualInfo (P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))) =
        log2 (M₁ : ℝ) - condEntropy P1 := by
      set Q := P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))
      have h1 : Q.map (fun t => (t.1, t.2.2)) = P.map Prod.fst := by rw [map_comp_eq]; rfl
      have h2 : Q.map (fun t => (t.2.1, t.2.2)) = P1.snd := by
        rw [← bc_probDist_map_snd, map_comp_eq]
      have h3 : Q.map (fun t => t.2.2) = P.map (fun z => z.1.2) := by rw [map_comp_eq]; rfl
      have h4 : Q = P1 := rfl
      unfold condMutualInfo condEntropy; dsimp only
      rw [h1, h2, h3, h4, hHM12, hHM2]; ring
    linarith

/-- Key single-letterization identity: at every coordinate `i : Fin n`, letting
    `U_i = (M₂, prefixHist i Y₁)` and `X_i = enc M₁ M₂ i`, the joint law of
    `((U_i, X_i), (Y_{1,i}, Y_{2,i}))` under `bcCodeDist` equals `bcAuxJoint W P_{U_i X_i}`. -/
private lemma bc_code_coord_joint_eq_bcAuxJoint (W : BroadcastChannel X Y₁ Y₂) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (enc : Fin M₁ → Fin M₂ → Fin n → X) (i : Fin n) :
    let P := bcCodeDist W hM₁ hM₂ enc
    let P_UX_i : ProbDist ((Fin M₂ × (Fin n → Option Y₁)) × X) :=
      P.map (fun z => ((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)), enc z.1.1 z.1.2 i))
    P.map (fun z => (((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)), enc z.1.1 z.1.2 i), z.2 i)) =
      bcAuxJoint W P_UX_i := by
  classical
  intro P P_UX_i
  apply bc_probDist_ext; rintro ⟨⟨⟨m₂₀, h⟩, x₀⟩, y₀⟩
  unfold P_UX_i ProbDist.map bcAuxJoint; dsimp only
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp only
  -- Both sides sum over `y : Fin n → Y₁ × Y₂` for fixed `m = (m₁, m₂)`.
  have hP_factor : ∀ y : Fin n → Y₁ × Y₂,
      P.pmf (m, y) = (1 / ((M₁ * M₂ : ℕ) : ℝ)) * (W.power n).trans (enc m.1 m.2) y := by
    intro y
    unfold P bcCodeDist DMC.joint dmcPrecomp ProbDist.uniform
    simp [Fintype.card_prod, Fintype.card_fin]
  by_cases hm : m.2 = m₂₀ ∧ enc m.1 m.2 i = x₀
  · rcases hm with ⟨hm2, hxi⟩
    by_cases hhi : h i = none
    · -- Valid history at coordinate `i`: `h i = none`, so both sides factor coordinate-by-coordinate.
      let FL : Fin n → Y₁ × Y₂ → ℝ := fun j yj =>
        if j = i then (if yj = y₀ then W.trans (enc m.1 m.2 j) yj else 0)
        else if (if j.1 < i.1 then some yj.1 else none) = h j then W.trans (enc m.1 m.2 j) yj else 0
      let FR : Fin n → Y₁ × Y₂ → ℝ := fun j yj =>
        if j = i then W.trans (enc m.1 m.2 j) yj
        else if (if j.1 < i.1 then some yj.1 else none) = h j then W.trans (enc m.1 m.2 j) yj else 0
      have hL : ∀ y : Fin n → Y₁ × Y₂,
          (if (((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i), y i) = (((m₂₀, h), x₀), y₀)
           then P.pmf (m, y) else 0) =
          (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FL j (y j) := by
        intro y
        rw [hP_factor]
        by_cases hcond : prefixHist i.1 (fun j => (y j).1) = h ∧ y i = y₀
        · have hcond' : (((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i), y i) =
              (((m₂₀, h), x₀), y₀) := by rw [hxi, hm2, hcond.1, hcond.2]
          rw [ite_eq_left hcond']
          congr 1; unfold DMC.power; dsimp only
          refine Finset.prod_congr rfl fun j _ => ?_
          dsimp only [FL]
          by_cases hj : j = i
          · subst hj; simp [hcond.2]
          · have hjh : (if j.1 < i.1 then some (y j).1 else none) = h j := by
              have := congrFun hcond.1 j; simpa [prefixHist] using this
            rw [ite_eq_right hj, ite_eq_left hjh]
        · have hcond' : ¬ ((((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i), y i) =
              (((m₂₀, h), x₀), y₀)) := fun heq => hcond ⟨by
            have := congrArg (fun t => t.1.1.2) heq; exact this,
            congrArg Prod.snd heq⟩
          rw [ite_eq_right hcond']
          have hex : ∃ j : Fin n, FL j (y j) = 0 := by
            by_cases hyi : y i = y₀
            · have hne : prefixHist i.1 (fun j => (y j).1) ≠ h := fun hp => hcond ⟨hp, hyi⟩
              have hexj : ∃ j : Fin n, prefixHist i.1 (fun k => (y k).1) j ≠ h j := by
                by_contra hall; push Not at hall; exact hne (funext hall)
              obtain ⟨j, hj⟩ := hexj
              by_cases hji : j = i
              · subst hji; exfalso; apply hj; simp [prefixHist, hhi]
              · exact ⟨j, by dsimp only [FL]; rw [ite_eq_right hji, ite_eq_right (by exact hj)]⟩
            · exact ⟨i, by simp [FL, hyi]⟩
          obtain ⟨j, hj⟩ := hex
          rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero]
      have hR : ∀ y : Fin n → Y₁ × Y₂,
          (if ((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i) = ((m₂₀, h), x₀)
           then P.pmf (m, y) else 0) =
          (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FR j (y j) := by
        intro y
        rw [hP_factor]
        by_cases hcond : prefixHist i.1 (fun j => (y j).1) = h
        · have hcond' : ((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i) =
              ((m₂₀, h), x₀) := by rw [hxi, hm2, hcond]
          rw [ite_eq_left hcond']
          congr 1; unfold DMC.power; dsimp only
          refine Finset.prod_congr rfl fun j _ => ?_
          dsimp only [FR]
          by_cases hj : j = i
          · subst hj; simp
          · have hjh : (if j.1 < i.1 then some (y j).1 else none) = h j := by
              have := congrFun hcond j; simpa [prefixHist] using this
            rw [ite_eq_right hj, ite_eq_left hjh]
        · have hcond' : ¬ (((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i) =
              ((m₂₀, h), x₀)) := fun heq => hcond (congrArg (fun t => t.1.2) heq)
          rw [ite_eq_right hcond']
          have hexj : ∃ j : Fin n, prefixHist i.1 (fun k => (y k).1) j ≠ h j := by
            by_contra hall; push Not at hall; exact hcond (funext hall)
          obtain ⟨j, hj⟩ := hexj
          have hji : j ≠ i := fun heq => by subst heq; apply hj; simp [prefixHist, hhi]
          have hFR0 : FR j (y j) = 0 := by
            dsimp only [FR]; rw [ite_eq_right hji, ite_eq_right (by exact hj)]
          rw [Finset.prod_eq_zero (Finset.mem_univ j) hFR0, mul_zero]
      calc _ = ∑ y : Fin n → Y₁ × Y₂, (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FL j (y j) :=
            Finset.sum_congr rfl fun y _ => by convert hL y
        _ = (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, ∑ yj, FL j yj := by
            rw [← Finset.mul_sum, ← Fintype.prod_sum]
        _ = ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, ∑ yj, FR j yj) * W.trans x₀ y₀ := by
            rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ yj, FL j yj) (Finset.mem_univ i),
                ← Finset.mul_prod_erase Finset.univ (fun j => ∑ yj, FR j yj) (Finset.mem_univ i)]
            have hrest : ∏ j ∈ Finset.univ.erase i, (∑ yj, FL j yj) =
                ∏ j ∈ Finset.univ.erase i, (∑ yj, FR j yj) :=
              Finset.prod_congr rfl fun j hj => Finset.sum_congr rfl fun yj _ => by
                simp [FL, FR, (Finset.mem_erase.mp hj).1]
            have hLi : ∑ yj : Y₁ × Y₂, FL i yj = W.trans x₀ y₀ := by
              simp [FL, hxi]
            have hRi : ∑ yj : Y₁ × Y₂, FR i yj = 1 := by
              simp [FR, W.sum_one]
            rw [hrest, hLi, hRi, one_mul]; ring
        _ = (∑ y : Fin n → Y₁ × Y₂, (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FR j (y j)) * W.trans x₀ y₀ := by
            rw [← Finset.mul_sum, ← Fintype.prod_sum]
        _ = _ := by
            congr 1
            exact Finset.sum_congr rfl fun y _ => by convert (hR y).symm
    · -- Invalid history at coordinate `i`: `h i ≠ none`, so both sides vanish!
      have hL0 : ∑ y : Fin n → Y₁ × Y₂,
          (if (((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i), y i) = (((m₂₀, h), x₀), y₀)
           then P.pmf (m, y) else 0) = 0 :=
        Finset.sum_eq_zero fun y _ => by
          rw [ite_eq_right]; intro heq; apply hhi
          have := congrFun (congrArg (fun t => t.1.1.2) heq) i
          simpa [prefixHist] using this.symm
      have hR0 : (∑ y : Fin n → Y₁ × Y₂,
          (if ((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i) = ((m₂₀, h), x₀)
           then P.pmf (m, y) else 0)) * W.trans x₀ y₀ = 0 := by
        rw [Finset.sum_eq_zero fun y _ => by
          rw [ite_eq_right]; intro heq; apply hhi
          have := congrFun (congrArg (fun t => t.1.2) heq) i
          simpa [prefixHist] using this.symm, zero_mul]
      convert hL0.trans hR0.symm
  · -- When `m.2 ≠ m₂₀ ∨ enc m.1 m.2 i ≠ x₀`, both sides are 0!
    have hL0 : ∑ y : Fin n → Y₁ × Y₂,
        (if (((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i), y i) = (((m₂₀, h), x₀), y₀)
         then P.pmf (m, y) else 0) = 0 :=
      Finset.sum_eq_zero fun y _ => by
        rw [ite_eq_right]; intro heq; apply hm
        exact ⟨congrArg (fun t => t.1.1.1) heq, congrArg (fun t => t.1.2) heq⟩
    have hR0 : (∑ y : Fin n → Y₁ × Y₂,
        (if ((m.2, prefixHist i.1 (fun j => (y j).1)), enc m.1 m.2 i) = ((m₂₀, h), x₀)
         then P.pmf (m, y) else 0)) * W.trans x₀ y₀ = 0 := by
      rw [Finset.sum_eq_zero fun y _ => by
        rw [ite_eq_right]; intro heq; apply hm
        exact ⟨congrArg (fun t => t.1.1) heq, congrArg Prod.snd heq⟩, zero_mul]
    convert hL0.trans hR0.symm

/-- Single-letter identity for Receiver 1's conditional mutual information:
    `I(M₁; Y₁^n | M₂) = ∑_{i=1}^n I(X_i; Y_{1,i} | U_i)` where `U_i = (M₂, Y₁^{<i})`. -/
private lemma bc_code_I_M1_Y1_given_M2_eq [Nonempty Y₁] (W : BroadcastChannel X Y₁ Y₂)
    {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (enc : Fin M₁ → Fin M₂ → Fin n → X) :
    let P := bcCodeDist W hM₁ hM₂ enc
    let P_UX_i : Fin n → ProbDist ((Fin M₂ × (Fin n → Option Y₁)) × X) :=
      fun i => P.map (fun z => ((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)), enc z.1.1 z.1.2 i))
    condMutualInfo (P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))) =
      ∑ i : Fin n, condMutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.2, z.2.1, z.1.1))) := by
  classical
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, hM₁⟩, ⟨0, hM₂⟩)⟩
  intro P P_UX_i
  -- Rewrite LHS as `[H(M₂, Y₁^n) - H(M₂)] - [H((M₁, M₂), Y₁^n) - H(M₁, M₂)]`
  set Q := P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))
  have hQ_xz : Q.map (fun t => (t.1, t.2.2)) = P.map Prod.fst := by rw [map_comp_eq]; rfl
  have hQ_yz : Q.map (fun t => (t.2.1, t.2.2)) =
      (P.map (fun z => (z.1.2, fun i => (z.2 i).1))).map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have hQ_z : Q.map (fun t => t.2.2) = P.map (fun z => z.1.2) := by rw [map_comp_eq]; rfl
  let eM12 : (Fin M₁ × (Fin n → Y₁) × Fin M₂) ≃ ((Fin M₁ × Fin M₂) × (Fin n → Y₁)) :=
    { toFun := fun t => ((t.1, t.2.2), t.2.1)
      invFun := fun t => (t.1.1, t.2, t.1.2)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  have hQ_all : Q.map eM12 = P.map (fun z => (z.1, fun i => (z.2 i).1)) := by
    rw [map_comp_eq]; rfl
  have hLHS : condMutualInfo Q =
      (shannonEntropy (P.map (fun z => (z.1.2, fun i => (z.2 i).1))) -
        shannonEntropy (P.map (fun z => z.1.2))) -
      (shannonEntropy (P.map (fun z => (z.1, fun i => (z.2 i).1))) -
        shannonEntropy (P.map Prod.fst)) := by
    unfold condMutualInfo; dsimp only
    rw [hQ_xz, hQ_yz, hQ_z, shannonEntropy_swap, ← shannonEntropy_map_equiv eM12 Q, hQ_all]
    ring
  -- First bracket via `prefixHist_telescope`
  have hbr1 : shannonEntropy (P.map (fun z => (z.1.2, fun i => (z.2 i).1))) -
      shannonEntropy (P.map (fun z => z.1.2)) =
      ∑ i : Fin n, condEntropy (P.map (fun z => ((z.2 i).1, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))) :=
    prefixHist_telescope P (fun z => z.1.2) (fun z i => (z.2 i).1)
  -- Second bracket: `P.map (m, y₁)` is `(dmcPrecomp ((bcMarginal1 W).power n) ...).joint Unif`
  have hP_MY1 : P.map (fun z => (z.1, fun i => (z.2 i).1)) =
      (dmcPrecomp ((bcMarginal1 W).power n) (fun m => enc m.1 m.2)).joint
        (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)) := by
    apply bc_probDist_ext; rintro ⟨m, y₁⟩
    unfold ProbDist.map DMC.joint dmcPrecomp P bcCodeDist; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · simp only [Prod.mk.injEq, true_and]
      have hite : ∀ y : Fin n → Y₁ × Y₂,
          (if (fun i => (y i).1) = y₁ then
            (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)).pmf m * (W.power n).trans (enc m.1 m.2) y
           else 0) =
          (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)).pmf m *
            (if (fun i => (y i).1) = y₁ then (W.power n).trans (enc m.1 m.2) y else 0) :=
        fun y => by split_ifs <;> ring
      trans (∑ y : Fin n → Y₁ × Y₂,
          (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)).pmf m *
            (if (fun i => (y i).1) = y₁ then (W.power n).trans (enc m.1 m.2) y else 0))
      · exact Finset.sum_congr rfl fun y _ => hite y
      · rw [← Finset.mul_sum]
        congr 1
        rw [bc_sum_ite_fst_power W (enc m.1 m.2) (fun a => a = y₁)]
        simp
    · intro m' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP_M : P.map Prod.fst = (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)) := by
    rw [bc_probDist_map_fst]; exact dmc_joint_fst _ _
  have hbr2 : shannonEntropy (P.map (fun z => (z.1, fun i => (z.2 i).1))) -
      shannonEntropy (P.map Prod.fst) =
      ∑ i : Fin n, ∑ m : Fin M₁ × Fin M₂,
        (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)).pmf m *
          shannonEntropy (dmcRow (bcMarginal1 W) (enc m.1 m.2 i)) := by
    rw [hP_MY1, hP_M, dmc_joint_shannonEntropy, add_sub_cancel_left]
    have hrow : ∀ m : Fin M₁ × Fin M₂,
        shannonEntropy (dmcRow (dmcPrecomp ((bcMarginal1 W).power n) (fun m => enc m.1 m.2)) m) =
        ∑ i : Fin n, shannonEntropy (dmcRow (bcMarginal1 W) (enc m.1 m.2 i)) := fun m => by
      have heq : dmcRow (dmcPrecomp ((bcMarginal1 W).power n) (fun m => enc m.1 m.2)) m =
          piProdDist (fun i => dmcRow (bcMarginal1 W) (enc m.1 m.2 i)) := rfl
      rw [heq, shannonEntropy_piProdDist]
    simp_rw [hrow, Finset.mul_sum]
    exact Finset.sum_comm
  -- Compute each summand on RHS
  have hterm : ∀ i : Fin n,
      condMutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.2, z.2.1, z.1.1))) =
        condEntropy (P.map (fun z => ((z.2 i).1, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))) -
        ∑ m : Fin M₁ × Fin M₂,
          (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)).pmf m *
            shannonEntropy (dmcRow (bcMarginal1 W) (enc m.1 m.2 i)) := by
    intro i
    set Ji := bcAuxJoint W (P_UX_i i)
    have hJi_eq : Ji = P.map (fun z => (((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)),
        enc z.1.1 z.1.2 i), z.2 i)) :=
      (bc_code_coord_joint_eq_bcAuxJoint W hM₁ hM₂ enc i).symm
    set Ri := Ji.map (fun z => (z.1.2, z.2.1, z.1.1))
    let e3 : (((Fin M₂ × (Fin n → Option Y₁)) × X) × Y₁) ≃
        (X × Y₁ × (Fin M₂ × (Fin n → Option Y₁))) :=
      { toFun := fun t => (t.1.2, t.2, t.1.1)
        invFun := fun t => ((t.2.2, t.1), t.2.1)
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hRi_all : Ri = (Ji.map (fun z => (z.1, z.2.1))).map e3 := by rw [map_comp_eq]; rfl
    have hRi_xz : Ri.map (fun t => (t.1, t.2.2)) = (P_UX_i i).map Prod.swap := by
      rw [map_comp_eq]
      have hJux : Ji.map (fun z => z.1) = P_UX_i i := by
        have : Ji.map (fun z => z.1) = (Ji.map (fun z => (z.1, z.2.1))).map Prod.fst := by
          rw [map_comp_eq]; rfl
        rw [this, bc_probDist_map_fst, bcAuxJoint_map_UXY1, dmc_joint_fst]
      rw [← hJux, map_comp_eq]; rfl
    have hRi_yz : Ri.map (fun t => (t.2.1, t.2.2)) =
        P.map (fun z => ((z.2 i).1, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1)))) := by
      dsimp only [Ri]; rw [hJi_eq, map_comp_eq, map_comp_eq]; rfl
    have hRi_z : Ri.map (fun t => t.2.2) =
        (P.map (fun z => ((z.2 i).1, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))).snd := by
      dsimp only [Ri]; rw [← bc_probDist_map_snd, hJi_eq, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
    have hUXY1_diff : shannonEntropy (Ji.map (fun z => (z.1, z.2.1))) - shannonEntropy (P_UX_i i) =
        ∑ m : Fin M₁ × Fin M₂,
          (ProbDist.uniform : ProbDist (Fin M₁ × Fin M₂)).pmf m *
            shannonEntropy (dmcRow (bcMarginal1 W) (enc m.1 m.2 i)) := by
      rw [bcAuxJoint_map_UXY1, dmc_joint_shannonEntropy, add_sub_cancel_left]
      have h1 := (sum_pmf_mul_comp P
        (fun z => ((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)), enc z.1.1 z.1.2 i))
        (fun ux => shannonEntropy (dmcRow (bcMarginal1 W) ux.2))).symm
      change ∑ ux, (P_UX_i i).pmf ux * shannonEntropy (dmcRow (bcMarginal1 W) ux.2) = _
      rw [h1]
      have h2 := sum_pmf_mul_comp P Prod.fst (fun m => shannonEntropy (dmcRow (bcMarginal1 W) (enc m.1 m.2 i)))
      rw [hP_M] at h2
      exact h2
    unfold condMutualInfo condEntropy; dsimp only
    rw [hRi_xz, hRi_yz, hRi_z, shannonEntropy_swap, hRi_all, shannonEntropy_map_equiv e3]
    linarith
  rw [hLHS, hbr1, hbr2, ← Finset.sum_sub_distrib]
  exact (Finset.sum_congr rfl fun i _ => hterm i).symm

/-- Single-letter upper bound for Receiver 2's mutual information under physical degradedness:
    `I(M₂; Y₂^n) ≤ ∑_{i=1}^n I(U_i; Y_{2,i})` where `U_i = (M₂, Y₁^{<i})`. -/
private lemma bc_code_I_M2_Y2_le [Nonempty Y₂] (W : BroadcastChannel X Y₁ Y₂)
    (hdeg : IsPhysicallyDegradedBC W) {n M₁ M₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (enc : Fin M₁ → Fin M₂ → Fin n → X) :
    let P := bcCodeDist W hM₁ hM₂ enc
    let P_UX_i : Fin n → ProbDist ((Fin M₂ × (Fin n → Option Y₁)) × X) :=
      fun i => P.map (fun z => ((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)), enc z.1.1 z.1.2 i))
    mutualInfo (P.map (fun z => (z.1.2, fun i => (z.2 i).2))) ≤
      ∑ i : Fin n, mutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2))) := by
  classical
  obtain ⟨K, hK⟩ := hdeg
  intro P P_UX_i
  -- Step 1: `I(M₂; Y₂^n) ≤ ∑_i I(Y_{2,i}; (M₂, Y₂^{<i}))`
  have hstep1 : mutualInfo (P.map (fun z => (z.1.2, fun i => (z.2 i).2))) ≤
      ∑ i : Fin n, mutualInfo (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).2))))) := by
    have hfst : (P.map (fun z => (z.1.2, fun i => (z.2 i).2))).fst = P.map (fun z => z.1.2) := by
      rw [← bc_probDist_map_fst, map_comp_eq]; rfl
    have hsnd : (P.map (fun z => (z.1.2, fun i => (z.2 i).2))).snd = P.map (fun z i => (z.2 i).2) := by
      rw [← bc_probDist_map_snd, map_comp_eq]; rfl
    have hsub : shannonEntropy (P.map (fun z i => (z.2 i).2)) ≤
        ∑ i : Fin n, shannonEntropy (P.map (fun z => (z.2 i).2)) := by
      have h := shannonEntropy_pi_le_sum n (P.map (fun z i => (z.2 i).2))
      refine le_trans h (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [map_comp_eq]; rfl
    have htele := prefixHist_telescope P (fun z => z.1.2) (fun z i => (z.2 i).2)
    have hmi_i : ∀ i : Fin n,
        mutualInfo (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).2))))) =
          shannonEntropy (P.map (fun z => (z.2 i).2)) -
            condEntropy (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).2))))) := by
      intro i
      have hf : (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).2))))).fst =
          P.map (fun z => (z.2 i).2) := by rw [← bc_probDist_map_fst, map_comp_eq]; rfl
      unfold mutualInfo condEntropy; rw [hf]; ring
    simp_rw [hmi_i]
    rw [Finset.sum_sub_distrib]
    unfold mutualInfo; rw [hfst, hsnd]
    linarith
  -- Step 2: DPI via `K_pair := dmcLiftRight ((optionChannel K).power n)` for each coordinate `i`
  let K_hist : DMC (Fin n → Option Y₁) (Fin n → Option Y₂) := (optionChannel K).power n
  let K_pair : DMC (Fin M₂ × (Fin n → Option Y₁)) (Fin M₂ × (Fin n → Option Y₂)) :=
    dmcLiftRight (α := Fin M₂) K_hist
  have hstep2 : ∀ i : Fin n,
      mutualInfo (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).2))))) ≤
        mutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2))) := by
    intro i
    have hdpi_dist :
        P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).2)))) =
        ((dmcLiftRight (α := Y₂) K_pair).joint
          (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1)))))).snd := by
      apply bc_probDist_ext; rintro ⟨b, ⟨m₂₀, h₂⟩⟩
      unfold ProbDist.snd DMC.joint dmcLiftRight; dsimp only
      rw [Fintype.sum_prod_type]
      -- Collapse `b' = b`
      have hcol_b : ∀ b' : Y₂, ∑ u₁ : Fin M₂ × (Fin n → Option Y₁),
          (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))).pmf (b', u₁) *
            (if b' = b then K_pair.trans u₁ (m₂₀, h₂) else 0) =
          if b' = b then ∑ u₁ : Fin M₂ × (Fin n → Option Y₁),
            (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))).pmf (b, u₁) *
              K_pair.trans u₁ (m₂₀, h₂) else 0 := fun b' => by
        by_cases hb : b' = b
        · subst hb; simp
        · simp [hb]
      simp_rw [hcol_b]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      -- Collapse `m₂' = m₂₀` inside `K_pair`
      rw [Fintype.sum_prod_type]
      have hcol_m2 : ∀ m₂' : Fin M₂, ∑ h₁ : Fin n → Option Y₁,
          (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))).pmf (b, (m₂', h₁)) *
            K_pair.trans (m₂', h₁) (m₂₀, h₂) =
          if m₂' = m₂₀ then ∑ h₁ : Fin n → Option Y₁,
            (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))).pmf (b, (m₂₀, h₁)) *
              K_hist.trans h₁ h₂ else 0 := fun m₂' => by
        dsimp only [K_pair, dmcLiftRight]
        by_cases hm : m₂' = m₂₀
        · subst hm; simp
        · simp [hm]
      simp_rw [hcol_m2]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      -- Swap sum over `h₁` with sum over `z = (m, y)` in `ProbDist.map`
      unfold ProbDist.map; dsimp only
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      -- Now both sides sum over `z : (Fin M₁ × Fin M₂) × (Fin n → Y₁ × Y₂)`.
      -- Collapse `h₁` on RHS to `prefixHist i.1 (fun j => (z.2 j).1)`!
      have hcol_h1 : ∀ z : (Fin M₁ × Fin M₂) × (Fin n → Y₁ × Y₂),
          ∑ h₁ : Fin n → Option Y₁,
            (if ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))) = (b, (m₂₀, h₁))
             then P.pmf z else 0) * K_hist.trans h₁ h₂ =
          if (z.2 i).2 = b ∧ z.1.2 = m₂₀ then
            P.pmf z * K_hist.trans (prefixHist i.1 (fun j => (z.2 j).1)) h₂ else 0 := fun z => by
        rw [Finset.sum_eq_single (prefixHist i.1 (fun j => (z.2 j).1))]
        · by_cases hc : (z.2 i).2 = b ∧ z.1.2 = m₂₀
          · simp [hc.1, hc.2]
          · have hneq : ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))) ≠
                (b, (m₂₀, prefixHist i.1 (fun j => (z.2 j).1))) := fun h => hc ⟨by
              exact congrArg Prod.fst h, congrArg (fun t => t.2.1) h⟩
            simp [hc, hneq]
        · intro h₁ _ hne
          have hneq : ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))) ≠ (b, (m₂₀, h₁)) :=
            fun h => hne (congrArg (fun t => t.2.2) h).symm
          simp [hneq]
        · intro h; exact absurd (Finset.mem_univ _) h
      trans (∑ z : (Fin M₁ × Fin M₂) × (Fin n → Y₁ × Y₂),
          if (z.2 i).2 = b ∧ z.1.2 = m₂₀ then
            P.pmf z * K_hist.trans (prefixHist i.1 (fun j => (z.2 j).1)) h₂ else 0)
      swap
      · exact (Finset.sum_congr rfl fun z _ => by convert hcol_h1 z).symm
      -- Split `∑ z` into `∑ m, ∑ y` and match each fixed `m = (m₁, m₂)` coordinate-by-coordinate!
      conv_lhs => rw [Fintype.sum_prod_type]
      conv_rhs => rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only
      have hP_factor : ∀ y : Fin n → Y₁ × Y₂,
          P.pmf (m, y) = (1 / ((M₁ * M₂ : ℕ) : ℝ)) * (W.power n).trans (enc m.1 m.2) y := by
        intro y
        unfold P bcCodeDist DMC.joint dmcPrecomp ProbDist.uniform
        simp [Fintype.card_prod, Fintype.card_fin]
      by_cases hm : m.2 = m₂₀
      · subst hm
        let FL : Fin n → Y₁ × Y₂ → ℝ := fun j yj =>
          if j = i then (if yj.2 = b ∧ none = h₂ j then W.trans (enc m.1 m.2 j) yj else 0)
          else if (if j.1 < i.1 then some yj.2 else none) = h₂ j then W.trans (enc m.1 m.2 j) yj else 0
        let FR : Fin n → Y₁ × Y₂ → ℝ := fun j yj =>
          (if j = i then (if yj.2 = b then W.trans (enc m.1 m.2 j) yj else 0)
           else W.trans (enc m.1 m.2 j) yj) *
            (optionChannel K).trans (if j.1 < i.1 then some yj.1 else none) (h₂ j)
        have hL_eq : ∀ y : Fin n → Y₁ × Y₂,
            (if ((y i).2, (m.2, prefixHist i.1 (fun j => (y j).2))) = (b, (m.2, h₂))
             then P.pmf (m, y) else 0) =
            (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FL j (y j) := by
          intro y
          rw [hP_factor]
          by_cases hc : (y i).2 = b ∧ prefixHist i.1 (fun j => (y j).2) = h₂
          · have hc' : ((y i).2, (m.2, prefixHist i.1 (fun j => (y j).2))) = (b, (m.2, h₂)) := by
              rw [hc.1, hc.2]
            rw [ite_eq_left hc']
            congr 1; unfold DMC.power; dsimp only
            refine Finset.prod_congr rfl fun j _ => ?_
            have hjh : (if j.1 < i.1 then some (y j).2 else none) = h₂ j := by
              have := congrFun hc.2 j; simpa [prefixHist] using this
            dsimp only [FL]
            by_cases hj : j = i
            · subst hj; simp only [↓reduceIte, lt_self_iff_false] at hjh ⊢; simp [hc.1, hjh]
            · rw [ite_eq_right hj, ite_eq_left hjh]
          · have hc' : ¬ (((y i).2, (m.2, prefixHist i.1 (fun j => (y j).2))) = (b, (m.2, h₂))) :=
              fun heq => hc ⟨congrArg Prod.fst heq, congrArg (fun t => t.2.2) heq⟩
            rw [ite_eq_right hc']
            have hex : ∃ j : Fin n, FL j (y j) = 0 := by
              by_cases hyi : (y i).2 = b
              · have hne : prefixHist i.1 (fun j => (y j).2) ≠ h₂ := fun hp => hc ⟨hyi, hp⟩
                have hexj : ∃ j : Fin n, prefixHist i.1 (fun k => (y k).2) j ≠ h₂ j := by
                  by_contra hall; push Not at hall; exact hne (funext hall)
                obtain ⟨j, hj⟩ := hexj
                by_cases hji : j = i
                · subst hji
                  have hne_none : none ≠ h₂ j := by simpa [prefixHist] using hj
                  exact ⟨j, by dsimp only [FL]; rw [ite_eq_left rfl, ite_eq_right (fun h => hne_none h.2)]⟩
                · exact ⟨j, by dsimp only [FL]; rw [ite_eq_right hji, ite_eq_right (by exact hj)]⟩
              · exact ⟨i, by simp [FL, hyi]⟩
            obtain ⟨j, hj⟩ := hex
            rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero]
        have hR_eq : ∀ y : Fin n → Y₁ × Y₂,
            (if (y i).2 = b ∧ m.2 = m.2 then
              P.pmf (m, y) * K_hist.trans (prefixHist i.1 (fun j => (y j).1)) h₂ else 0) =
            (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FR j (y j) := by
          intro y
          rw [hP_factor]
          by_cases hyi : (y i).2 = b
          · simp only [hyi, and_self, ↓reduceIte, mul_assoc]
            congr 1
            dsimp only [K_hist, DMC.power, prefixHist]
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun j _ => ?_
            dsimp only [FR]
            by_cases hj : j = i
            · subst hj; simp [hyi]
            · simp [hj]
          · simp only [hyi, false_and, ↓reduceIte]
            have hFR0 : FR i (y i) = 0 := by simp [FR, hyi]
            rw [Finset.prod_eq_zero (Finset.mem_univ i) hFR0, mul_zero]
        calc _ = ∑ y : Fin n → Y₁ × Y₂, (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FL j (y j) :=
              Finset.sum_congr rfl fun y _ => by convert hL_eq y
          _ = (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, ∑ yj, FL j yj := by
              rw [← Finset.mul_sum, ← Fintype.prod_sum]
          _ = (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, ∑ yj, FR j yj := by
              congr 1
              refine Finset.prod_congr rfl fun j _ => ?_
              -- Coordinate `j` equality: `∑ yj, FL j yj = ∑ yj, FR j yj`!
              by_cases hji : j = i
              · subst hji
                dsimp only [FL, FR]
                simp only [↓reduceIte, lt_self_iff_false]
                cases h₂ j with
                | none =>
                  refine Finset.sum_congr rfl fun yj _ => ?_
                  simp [optionChannel]
                | some b₂ =>
                  simp [optionChannel]
              · dsimp only [FL, FR]
                simp only [hji, ↓reduceIte]
                by_cases hlt : j.1 < i.1
                · simp only [hlt, ↓reduceIte]
                  cases h₂ j with
                  | none =>
                    simp [optionChannel]
                  | some b₂ =>
                    simp only [Option.some.injEq, optionChannel]
                    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
                    refine Finset.sum_congr rfl fun y₁ _ => ?_
                    rw [Finset.sum_eq_single b₂]
                    · simp only [↓reduceIte, ← Finset.sum_mul]
                      exact hK (enc m.1 m.2 j) y₁ b₂
                    · intro y₂ _ hne; simp [hne]
                    · intro h; exact absurd (Finset.mem_univ _) h
                · simp only [hlt, ↓reduceIte]
                  cases h₂ j with
                  | none =>
                    refine Finset.sum_congr rfl fun yj _ => ?_
                    simp [optionChannel]
                  | some b₂ =>
                    simp [optionChannel]
          _ = ∑ y : Fin n → Y₁ × Y₂, (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∏ j : Fin n, FR j (y j) := by
              rw [← Finset.mul_sum, ← Fintype.prod_sum]
          _ = _ :=
              Finset.sum_congr rfl fun y _ => by convert (hR_eq y).symm
      · -- `m.2 ≠ m₂₀`: both sides are 0!
        have hL0 : ∑ y : Fin n → Y₁ × Y₂,
            (if ((y i).2, (m.2, prefixHist i.1 (fun j => (y j).2))) = (b, (m₂₀, h₂))
             then P.pmf (m, y) else 0) = 0 :=
          Finset.sum_eq_zero fun y _ => by
            rw [ite_eq_right]; intro heq; exact hm (congrArg (fun t => t.2.1) heq)
        have hR0 : ∑ y : Fin n → Y₁ × Y₂,
            (if (y i).2 = b ∧ m.2 = m₂₀ then
              P.pmf (m, y) * K_hist.trans (prefixHist i.1 (fun j => (y j).1)) h₂ else 0) = 0 :=
          Finset.sum_eq_zero fun y _ => by simp [hm]
        convert hL0.trans hR0.symm
    rw [hdpi_dist]
    have hdpi := mutualInfo_channel_right_le
      (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))) K_pair
    have hswap : mutualInfo (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))) =
        mutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2))) := by
      have hJi := bc_code_coord_joint_eq_bcAuxJoint W hM₁ hM₂ enc i
      dsimp only at hJi
      have hmap : (bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2)) =
          (P.map (fun z => ((z.2 i).2, (z.1.2, prefixHist i.1 (fun j => (z.2 j).1))))).map Prod.swap := by
        rw [← hJi, map_comp_eq, map_comp_eq]; rfl
      rw [hmap, mutualInfo_swap]
    linarith
  exact le_trans hstep1 (Finset.sum_le_sum fun i _ => hstep2 i)

/-! #### Time-Sharing Mixture over Coordinates `Q ~ Unif(Fin n)` -/

/-- Uniform mixture distribution `(Q, Z_Q)` on `Fin n × α` with `Q ~ Unif(Fin n)`. -/
private noncomputable def uniformMixDist {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) : ProbDist (Fin n × α) where
  pmf := fun t => ((1 : ℝ) / (n : ℝ)) * (Q t.1).pmf t.2
  nonneg := fun t => mul_nonneg (by positivity) ((Q t.1).nonneg t.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ i : Fin n, ∑ a : α, ((1 : ℝ) / (n : ℝ)) * (Q i).pmf a = (1 : ℝ) / (n : ℝ) :=
      fun i => by rw [← Finset.mul_sum, (Q i).sum_one, mul_one]
    have hsum : (∑ i : Fin n, ∑ a : α, ((1 : ℝ) / (n : ℝ)) * (Q i).pmf a) =
        ∑ _i : Fin n, ((1 : ℝ) / (n : ℝ)) :=
      Finset.sum_congr rfl fun i _ => hinner i
    change (∑ i : Fin n, ∑ a : α, ((1 : ℝ) / (n : ℝ)) * (Q i).pmf a) = 1
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hnr]

private lemma shannonEntropy_uniformMixDist {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) :
    shannonEntropy (uniformMixDist hn Q) =
      log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, shannonEntropy (Q i) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let W_Q : DMC (Fin n) α :=
    { trans := fun i a => (Q i).pmf a
      nonneg := fun i a => (Q i).nonneg a
      sum_one := fun i => (Q i).sum_one }
  have heq : uniformMixDist hn Q = W_Q.joint (ProbDist.uniform : ProbDist (Fin n)) := by
    apply bc_probDist_ext; rintro ⟨i, a⟩
    unfold uniformMixDist DMC.joint ProbDist.uniform; simp [W_Q, Fintype.card_fin]
  rw [heq, dmc_joint_shannonEntropy, (shannonEntropy_eq_log2_card_iff _).mpr rfl, Fintype.card_fin]
  congr 1
  unfold ProbDist.uniform; simp only [Fintype.card_fin, ← Finset.mul_sum]
  rfl

/-- Time-sharing mixture of `n` auxiliary input distributions `P_i : ProbDist (U × X)` into a
    single auxiliary input distribution on `(Fin n × U) × X`. -/
private noncomputable def timeShareUX {U : Type*} [Fintype U] {n : ℕ} (hn : 0 < n)
    (P_i : Fin n → ProbDist (U × X)) : ProbDist ((Fin n × U) × X) where
  pmf := fun t => ((1 : ℝ) / (n : ℝ)) * (P_i t.1.1).pmf (t.1.2, t.2)
  nonneg := fun t => mul_nonneg (by positivity) ((P_i t.1.1).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hswap : ∑ i : Fin n, ∑ u : U, ∑ x : X, ((1 : ℝ) / (n : ℝ)) * (P_i i).pmf (u, x) =
        ∑ i : Fin n, ((1 : ℝ) / (n : ℝ)) * ∑ ux : U × X, (P_i i).pmf ux := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    rw [hswap]
    have hP1 : ∀ i : Fin n, ∑ ux : U × X, (P_i i).pmf ux = 1 := fun i => (P_i i).sum_one
    simp_rw [hP1, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hnr]

private lemma timeShareUX_map {U α : Type*} [Fintype U] [Fintype α]
    (W : BroadcastChannel X Y₁ Y₂) {n : ℕ} (hn : 0 < n)
    (P_i : Fin n → ProbDist (U × X)) (f : U × X × (Y₁ × Y₂) → α) :
    (bcAuxJoint W (timeShareUX hn P_i)).map (fun z => (z.1.1.1, f (z.1.1.2, z.1.2, z.2))) =
      uniformMixDist hn (fun i => (bcAuxJoint W (P_i i)).map (fun z => f (z.1.1, z.1.2, z.2))) := by
  classical
  apply bc_probDist_ext; rintro ⟨i, a⟩
  unfold ProbDist.map uniformMixDist bcAuxJoint timeShareUX; dsimp only
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp only [Prod.mk.injEq, true_and]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
  · intro i' _ hne
    exact Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun y _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma timeShareUX_bounds {U : Type*} [Fintype U] (W : BroadcastChannel X Y₁ Y₂)
    {n : ℕ} (hn : 0 < n) (P_i : Fin n → ProbDist (U × X)) :
    let J_mix := bcAuxJoint W (timeShareUX hn P_i)
    let J_i := fun i => bcAuxJoint W (P_i i)
    ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n,
        condMutualInfo ((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))) =
      condMutualInfo (J_mix.map (fun z => (z.1.2, z.2.1, z.1.1))) ∧
    ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n,
        mutualInfo ((J_i i).map (fun z => (z.1.1, z.2.2))) ≤
      mutualInfo (J_mix.map (fun z => (z.1.1, z.2.2))) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro J_mix J_i
  constructor
  · -- Exact equality for `I(X; Y₁ | Q, U)`
    set Q := J_mix.map (fun z => (z.1.2, z.2.1, z.1.1))
    let eXZ : (X × (Fin n × U)) ≃ (Fin n × (X × U)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, (t.1, t.2.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    let eYZ : (Y₁ × (Fin n × U)) ≃ (Fin n × (Y₁ × U)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, (t.1, t.2.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    let eXYZ : (X × Y₁ × (Fin n × U)) ≃ (Fin n × (X × Y₁ × U)) :=
      { toFun := fun t => (t.2.2.1, (t.1, t.2.1, t.2.2.2))
        invFun := fun t => (t.2.1, t.2.2.1, (t.1, t.2.2.2))
        left_inv := fun ⟨_, _, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _, _⟩ => rfl }
    have h1 : shannonEntropy (Q.map (fun t => (t.1, t.2.2))) =
        log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, shannonEntropy (((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.1, t.2.2))) := by
      rw [← shannonEntropy_map_equiv eXZ]
      have hm : (Q.map (fun t => (t.1, t.2.2))).map eXZ =
          uniformMixDist hn (fun i => ((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.1, t.2.2))) := by
        rw [map_comp_eq, map_comp_eq]; simp_rw [map_comp_eq]
        exact timeShareUX_map W hn P_i (fun t => (t.2.1, t.1))
      rw [hm, shannonEntropy_uniformMixDist]
    have h2 : shannonEntropy (Q.map (fun t => (t.2.1, t.2.2))) =
        log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, shannonEntropy (((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.2.1, t.2.2))) := by
      rw [← shannonEntropy_map_equiv eYZ]
      have hm : (Q.map (fun t => (t.2.1, t.2.2))).map eYZ =
          uniformMixDist hn (fun i => ((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => (t.2.1, t.2.2))) := by
        rw [map_comp_eq, map_comp_eq]; simp_rw [map_comp_eq]
        exact timeShareUX_map W hn P_i (fun t => (t.2.2.1, t.1))
      rw [hm, shannonEntropy_uniformMixDist]
    have h3 : shannonEntropy Q =
        log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, shannonEntropy ((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))) := by
      rw [← shannonEntropy_map_equiv eXYZ]
      have hm : Q.map eXYZ = uniformMixDist hn (fun i => (J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))) := by
        rw [map_comp_eq]
        exact timeShareUX_map W hn P_i (fun t => (t.2.1, t.2.2.1, t.1))
      rw [hm, shannonEntropy_uniformMixDist]
    have h4 : shannonEntropy (Q.map (fun t => t.2.2)) =
        log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, shannonEntropy (((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => t.2.2)) := by
      have hm : Q.map (fun t => t.2.2) =
          uniformMixDist hn (fun i => ((J_i i).map (fun z => (z.1.2, z.2.1, z.1.1))).map (fun t => t.2.2)) := by
        rw [map_comp_eq]; simp_rw [map_comp_eq]
        exact timeShareUX_map W hn P_i (fun t => t.1)
      rw [hm, shannonEntropy_uniformMixDist]
    unfold condMutualInfo; dsimp only
    rw [h1, h2, h3, h4]
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  · -- Inequality `((1/n) ∑_i I(U_i; Y_{2,i})) ≤ I((Q, U); Y₂)`
    set R := J_mix.map (fun z => (z.1.1, z.2.2))
    let eAll : ((Fin n × U) × Y₂) ≃ (Fin n × (U × Y₂)) := Equiv.prodAssoc (Fin n) U Y₂
    have hfst_mix : R.fst = uniformMixDist hn (fun i => ((J_i i).map (fun z => (z.1.1, z.2.2))).fst) := by
      rw [← bc_probDist_map_fst, map_comp_eq]
      have h : ∀ i : Fin n, ((J_i i).map (fun z => (z.1.1, z.2.2))).fst = (J_i i).map (fun z => z.1.1) :=
        fun i => by rw [← bc_probDist_map_fst, map_comp_eq]; rfl
      simp_rw [h]; exact timeShareUX_map W hn P_i (fun t => t.1)
    have hall_mix : R.map eAll = uniformMixDist hn (fun i => (J_i i).map (fun z => (z.1.1, z.2.2))) := by
      rw [map_comp_eq]; exact timeShareUX_map W hn P_i (fun t => (t.1, t.2.2.2))
    -- `H(Y₂) ≥ H(Y₂ | Q) = (1/n) ∑_i H(Y_{2,i})`
    let P_Y2Q : ProbDist (Y₂ × Fin n) := (uniformMixDist hn (fun i => ((J_i i).map (fun z => (z.1.1, z.2.2))).snd)).map Prod.swap
    have hY2_fst : P_Y2Q.fst = R.snd := by
      rw [fst_map_swap, ← bc_probDist_map_snd, ← bc_probDist_map_snd]
      have h : ∀ i : Fin n, ((J_i i).map (fun z => (z.1.1, z.2.2))).snd = (J_i i).map (fun z => z.2.2) :=
        fun i => by rw [← bc_probDist_map_snd, map_comp_eq]; rfl
      simp_rw [h]
      rw [← timeShareUX_map W hn P_i (fun t => t.2.2.2), map_comp_eq, map_comp_eq]; rfl
    have hY2_snd : P_Y2Q.snd = (ProbDist.uniform : ProbDist (Fin n)) := by
      rw [snd_map_swap]
      apply bc_probDist_ext; intro i
      unfold ProbDist.fst uniformMixDist ProbDist.uniform; dsimp only
      rw [← Finset.mul_sum, ProbDist.sum_one, mul_one, Fintype.card_fin]
    have hY2_ge : ((1 : ℝ) / (n : ℝ)) *
        ∑ i : Fin n, shannonEntropy ((J_i i).map (fun z => (z.1.1, z.2.2))).snd ≤
        shannonEntropy R.snd := by
      have hce := condEntropy_le_shannonEntropy P_Y2Q
      unfold condEntropy at hce
      rw [hY2_fst, hY2_snd, (shannonEntropy_eq_log2_card_iff _).mpr rfl, Fintype.card_fin,
          shannonEntropy_swap, shannonEntropy_uniformMixDist] at hce
      linarith
    have h1 : shannonEntropy R.fst =
        log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, shannonEntropy ((J_i i).map (fun z => (z.1.1, z.2.2))).fst := by
      rw [hfst_mix, shannonEntropy_uniformMixDist]
    have h3 : shannonEntropy R =
        log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, shannonEntropy ((J_i i).map (fun z => (z.1.1, z.2.2))) := by
      rw [← shannonEntropy_map_equiv eAll R, hall_mix, shannonEntropy_uniformMixDist]
    unfold mutualInfo
    simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith

/-- **Degraded Broadcast Channel Converse** (Gallager 1974; Cover & Thomas §15.6.2;
    El Gamal–Kim Thm. 5.2): for every physically degraded DMBC `W`,
    `bcCapacityRegion W ⊆ degradedBCRegion W`. -/
theorem degradedBC_converse (W : BroadcastChannel X Y₁ Y₂)
    (hdeg : IsPhysicallyDegradedBC W) :
    bcCapacityRegion W ⊆ degradedBCRegion W := by
  refine closure_minimal ?_ isClosed_closure
  rintro ⟨R₁, R₂⟩ ⟨hR₁0, hR₂0, hach⟩
  unfold degradedBCRegion
  rw [Metric.mem_closure_iff]
  intro η hη
  -- Extract nonempty `X`, `Y₁`, `Y₂` from an achievability code at blocklength `≥ 1`
  have hnonempty : Nonempty X ∧ Nonempty Y₁ ∧ Nonempty Y₂ := by
    obtain ⟨N0, hN0⟩ := hach 1 zero_lt_one
    obtain ⟨enc, _, _, _⟩ := hN0 (max N0 1) (le_max_left _ _)
    have hM1 : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N0 1 : ℕ) : ℝ) * R₁))) :=
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hM2 : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N0 1 : ℕ) : ℝ) * R₂))) :=
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hn1 : 0 < max N0 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N0 1)
    let x₀ : X := enc ⟨0, hM1⟩ ⟨0, hM2⟩ ⟨0, hn1⟩
    have hYne : Nonempty (Y₁ × Y₂) := by
      by_contra h
      have h0 : ∑ y : Y₁ × Y₂, W.trans x₀ y = 0 := Finset.sum_eq_zero fun y _ => (h ⟨y⟩).elim
      linarith [W.sum_one x₀]
    exact ⟨⟨x₀⟩, ⟨hYne.some.1⟩, ⟨hYne.some.2⟩⟩
  have : Nonempty X := hnonempty.1
  have : Nonempty Y₁ := hnonempty.2.1
  have : Nonempty Y₂ := hnonempty.2.2
  -- Choose `ε > 0` and large `n` so Fano slack is `< η / 2`
  let Rmax : ℝ := max (max R₁ R₂) 1
  have hRmax : 1 ≤ Rmax := le_max_right _ _
  have hRmax_pos : 0 < Rmax := by linarith
  let ε : ℝ := min (1 / 2) (η / (4 * Rmax))
  have hε_pos : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε_half : ε ≤ 1 / 2 := min_le_left _ _
  obtain ⟨N₁, hN₁⟩ := hach ε hε_pos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (8 / η)
  let n : ℕ := max (max N₁ N₂) 1
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ge_N₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ 1)
  have hn_gt : 8 / η < (n : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
  have h2n_lt : 2 / (n : ℝ) < η / 4 := by
    rw [div_lt_iff₀ hn_r]
    have h := (div_lt_iff₀ hη).mp hn_gt
    linarith
  obtain ⟨enc, dec₁, dec₂, herr⟩ := hN₁ n hn_ge_N₁
  let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  -- Lower bound `log2 M_j / n ≥ R_j - 1 / n`
  have hlogM_ge : ∀ (R : ℝ), 0 ≤ R →
      R - 1 / (n : ℝ) ≤ log2 ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) / (n : ℝ) := by
    intro R hR0
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    have hM_ge_half : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ (M : ℝ) := by
      have hhalf : (2 : ℝ) ^ ((n : ℝ) * R - 1) = (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
        calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left 1 _
      have hfl : (2 : ℝ) ^ ((n : ℝ) * R) < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hleM : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast le_max_right 1 _
      linarith
    have hlog : (n : ℝ) * R - 1 ≤ log2 (M : ℝ) := by
      have h1 := bc_log2_mono (Real.rpow_pos_of_pos (by norm_num) _) hM_ge_half
      rwa [bc_log2_two_rpow] at h1
    have hdiv := div_le_div_of_nonneg_right hlog hn_r.le
    have hsimp : ((n : ℝ) * R - 1) / (n : ℝ) = R - 1 / (n : ℝ) := by
      rw [sub_div, mul_div_cancel_left₀ _ hn_r.ne']
    linarith
  -- Apply Fano + single-letterization + time-sharing
  let P := bcCodeDist W hM₁ hM₂ enc
  let P_UX_i : Fin n → ProbDist ((Fin M₂ × (Fin n → Option Y₁)) × X) :=
    fun i => P.map (fun z => ((z.1.2, prefixHist i.1 (fun j => (z.2 j).1)), enc z.1.1 z.1.2 i))
  have hfano := bc_code_fano_bounds W hM₁ hM₂ enc dec₁ dec₂
  have hI1 := bc_code_I_M1_Y1_given_M2_eq W hM₁ hM₂ enc
  have hI2 := bc_code_I_M2_Y2_le W hdeg hM₁ hM₂ enc
  have hts := timeShareUX_bounds W hn_pos P_UX_i
  let P_mix := timeShareUX hn_pos P_UX_i
  -- Reindex `U_mix := Fin n × (Fin M₂ × (Fin n → Option Y₁))` to `Fin kU`
  let U_mix := Fin n × (Fin M₂ × (Fin n → Option Y₁))
  let eU : U_mix ≃ Fin (Fintype.card U_mix) := Fintype.equivFin U_mix
  let P_fin : ProbDist (Fin (Fintype.card U_mix) × X) := P_mix.map (fun ux => (eU ux.1, ux.2))
  have hrel := bcAuxJoint_relabel W P_mix eU
  dsimp only at hfano hI1 hI2 hts hrel
  -- Deduce `R₁ - η / 2 ≤ I(X; Y₁ | U)` and `R₂ - η / 2 ≤ I(U; Y₂)`
  have hrate_bound : ∀ (R I : ℝ) (M : ℕ), 0 ≤ R → R ≤ Rmax →
      R - 1 / (n : ℝ) ≤ log2 (M : ℝ) / (n : ℝ) →
      (1 - ε) * log2 (M : ℝ) ≤ (n : ℝ) * I + 1 →
      0 ≤ log2 (M : ℝ) →
      R - η / 2 ≤ I := by
    intro R I M hR0 hRle hRge hF hlog0
    have hdiv : (1 - ε) * (log2 (M : ℝ) / (n : ℝ)) ≤ I + 1 / (n : ℝ) := by
      have h1 := div_le_div_of_nonneg_right hF hn_r.le
      have hs1 : ((1 - ε) * log2 (M : ℝ)) / (n : ℝ) = (1 - ε) * (log2 (M : ℝ) / (n : ℝ)) := by ring
      have hs2 : ((n : ℝ) * I + 1) / (n : ℝ) = I + 1 / (n : ℝ) := by
        rw [add_div, mul_div_cancel_left₀ _ hn_r.ne']
      linarith
    have h1m : 0 ≤ 1 - ε := by linarith
    have hprod : (1 - ε) * (R - 1 / (n : ℝ)) ≤ (1 - ε) * (log2 (M : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hRge h1m
    have hεR : ε * R ≤ η / 4 := by
      have h1 : ε ≤ η / (4 * Rmax) := min_le_right _ _
      calc ε * R ≤ (η / (4 * Rmax)) * Rmax := mul_le_mul h1 hRle hR0 (by positivity)
        _ = η / 4 := by field_simp [hRmax_pos.ne']
    have hεn : 0 ≤ ε * (1 / (n : ℝ)) := by positivity
    have hexp : (1 - ε) * (R - 1 / (n : ℝ)) = R - 1 / (n : ℝ) - ε * R + ε * (1 / (n : ℝ)) := by ring
    have h2div : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
    linarith
  have hlog1_nn : 0 ≤ log2 (M₁ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
    have := bc_log2_mono zero_lt_one h1; simpa [log2] using this
  have hlog2_nn : 0 ≤ log2 (M₂ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM₂
    have := bc_log2_mono zero_lt_one h1; simpa [log2] using this
  let errVal : ℝ := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
    ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
      if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
      then (W.power n).trans (enc m₁ m₂) y else 0
  have herr_le : errVal ≤ ε := herr
  have hF1 : (1 - ε) * log2 (M₁ : ℝ) ≤
      (n : ℝ) * condMutualInfo ((bcAuxJoint W P_fin).map (fun z => (z.1.2, z.2.1, z.1.1))) + 1 := by
    have h1 : (1 - ε) * log2 (M₁ : ℝ) ≤
        condMutualInfo (P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))) + 1 := by
      have hmul : (1 - ε) * log2 (M₁ : ℝ) ≤ (1 - errVal) * log2 (M₁ : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog1_nn
      have hf2 : (1 - errVal) * log2 (M₁ : ℝ) ≤
          condMutualInfo (P.map (fun z => (z.1.1, (fun i => (z.2 i).1), z.1.2))) + 1 := hfano.2
      linarith
    have hts1 : ∑ i : Fin n, condMutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.2, z.2.1, z.1.1))) =
        (n : ℝ) * condMutualInfo ((bcAuxJoint W P_mix).map (fun z => (z.1.2, z.2.1, z.1.1))) := by
      rw [← hts.1]; field_simp [hn_r.ne']
    rw [hrel.2.1, ← hts1, ← hI1]; exact h1
  have hF2 : (1 - ε) * log2 (M₂ : ℝ) ≤
      (n : ℝ) * mutualInfo ((bcAuxJoint W P_fin).map (fun z => (z.1.1, z.2.2))) + 1 := by
    have h1 : (1 - ε) * log2 (M₂ : ℝ) ≤
        mutualInfo (P.map (fun z => (z.1.2, fun i => (z.2 i).2))) + 1 := by
      have hmul : (1 - ε) * log2 (M₂ : ℝ) ≤ (1 - errVal) * log2 (M₂ : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog2_nn
      have hf1 : (1 - errVal) * log2 (M₂ : ℝ) ≤
          mutualInfo (P.map (fun z => (z.1.2, fun i => (z.2 i).2))) + 1 := hfano.1
      linarith
    have hts2 : ∑ i : Fin n, mutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2))) ≤
        (n : ℝ) * mutualInfo ((bcAuxJoint W P_mix).map (fun z => (z.1.1, z.2.2))) := by
      have hm := mul_le_mul_of_nonneg_left hts.2 hn_r.le
      have hsimp : (n : ℝ) * (((1 : ℝ) / (n : ℝ)) *
          ∑ i : Fin n, mutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2)))) =
          ∑ i : Fin n, mutualInfo ((bcAuxJoint W (P_UX_i i)).map (fun z => (z.1.1, z.2.2))) := by
        field_simp [hn_r.ne']
      linarith
    rw [hrel.1]; linarith
  have hB1 : R₁ - η / 2 ≤ condMutualInfo ((bcAuxJoint W P_fin).map (fun z => (z.1.2, z.2.1, z.1.1))) :=
    hrate_bound R₁ _ M₁ hR₁0 (le_trans (le_max_left R₁ R₂) (le_max_left _ 1))
      (hlogM_ge R₁ hR₁0) hF1 hlog1_nn
  have hB2 : R₂ - η / 2 ≤ mutualInfo ((bcAuxJoint W P_fin).map (fun z => (z.1.1, z.2.2))) :=
    hrate_bound R₂ _ M₂ hR₂0 (le_trans (le_max_right R₁ R₂) (le_max_left _ 1))
      (hlogM_ge R₂ hR₂0) hF2 hlog2_nn
  -- Witness point `(max 0 (R₁ - η / 2), max 0 (R₂ - η / 2))` in the single-letter set
  let r₁ := max 0 (R₁ - η / 2)
  let r₂ := max 0 (R₂ - η / 2)
  refine ⟨(r₁, r₂), ⟨le_max_left _ _, le_max_left _ _, Fintype.card U_mix, P_fin,
    max_le (mutualInfo_nonneg _) hB2, max_le (condMutualInfo_nonneg _) hB1⟩, ?_⟩
  rw [Prod.dist_eq]
  have hd1 : dist R₁ r₁ < η := by
    rw [Real.dist_eq, abs_lt]
    have hle : r₁ ≤ R₁ := max_le hR₁0 (by linarith)
    have hge : R₁ - η / 2 ≤ r₁ := le_max_right _ _
    constructor <;> linarith
  have hd2 : dist R₂ r₂ < η := by
    rw [Real.dist_eq, abs_lt]
    have hle : r₂ ≤ R₂ := max_le hR₂0 (by linarith)
    have hge : R₂ - η / 2 ≤ r₂ := le_max_right _ _
    constructor <;> linarith
  exact max_lt hd1 hd2

/-- **Degraded Broadcast Channel Capacity Region Theorem** (Bergmans 1973; Gallager 1974;
    Cover & Thomas Theorem 15.6.2; El Gamal–Kim Theorem 5.2):
    for every physically degraded two-receiver DMBC `W`, the operational capacity region equals
    the single-letter degraded broadcast channel region:
    `bcCapacityRegion W = degradedBCRegion W`. -/
theorem degradedBC_capacity_theorem (W : BroadcastChannel X Y₁ Y₂)
    (hdeg : IsPhysicallyDegradedBC W) :
    bcCapacityRegion W = degradedBCRegion W :=
  Set.Subset.antisymm
    (degradedBC_converse W hdeg)
    (superpositionInnerBound_eq_degradedBCRegion W hdeg ▸
      superpositionInnerBound_subset_bcCapacityRegion W)

end DegradedBCConverse

/-! ### 4. Operational Bergmans Capacity Region for the Binary Symmetric Degraded BC -/

section OperationalBergmans

/-- **Bergmans–Wyner–Ziv Capacity Region** of the Binary Symmetric Degraded Broadcast Channel
    `BSC(p₁, p₂)` (`0 ≤ p₁ ≤ p₂ ≤ 1/2`; Bergmans 1973; Wyner & Ziv 1973; Cover & Thomas §15.6.2):
    `{ (R₁, R₂) ≥ 0 | ∃ α ∈ [0, 1/2], R₁ ≤ h(α ★ p₁) - h(p₁) ∧ R₂ ≤ 1 - h(α ★ p₂) }`. -/
def bergmansBSDBCRegion (p₁ p₂ : ℝ) : Set (ℝ × ℝ) :=
  { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ α ∈ Set.Icc (0 : ℝ) (1 / 2),
      r.1 ≤ binaryEntropy (binaryConv α p₁) - binaryEntropy p₁ ∧
      r.2 ≤ 1 - binaryEntropy (binaryConv α p₂) }

/-- `degradedBSC p₁ p₂` is physically degraded for all `0 ≤ p₁ ≤ p₂ ≤ 1/2`. -/
theorem degradedBSC_isPhysicallyDegraded {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    IsPhysicallyDegradedBC (degradedBSC p₁ p₂ hp₁ h12 hp₂) := by
  let q : ℝ := if p₁ = 1 / 2 then 0 else (p₂ - p₁) / (1 - 2 * p₁)
  have hq0 : 0 ≤ q := by
    dsimp only [q]; split_ifs with h
    · exact le_rfl
    · have hlt : p₁ < 1 / 2 := lt_of_le_of_ne (le_trans h12 hp₂) h
      exact div_nonneg (by linarith) (by linarith)
  have hq1 : q ≤ 1 := by
    dsimp only [q]; split_ifs with h
    · exact zero_le_one
    · have hlt : p₁ < 1 / 2 := lt_of_le_of_ne (le_trans h12 hp₂) h
      have hden : 0 < 1 - 2 * p₁ := by linarith
      have hhalf : (p₂ - p₁) / (1 - 2 * p₁) ≤ 1 / 2 := by rw [div_le_iff₀ hden]; linarith
      linarith
  refine ⟨bsc q hq0 hq1, fun x y₁ y₂ => ?_⟩
  have htrans : ∀ a b c, (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans a (b, c) =
      (bsc p₁ hp₁ (by linarith)).trans a b * (bsc q hq0 hq1).trans b c := fun _ _ _ => rfl
  simp_rw [htrans, ← Finset.mul_sum, (bsc q hq0 hq1).sum_one, mul_one]

/-- `bergmansBSDBCRegion p₁ p₂` is closed in `ℝ × ℝ` for `0 ≤ p₁ ≤ p₂ ≤ 1/2`
    (by compactness of `[0, 1/2]` and continuity of `α ↦ h(α ★ p)`). -/
theorem isClosed_bergmansBSDBCRegion {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    IsClosed (bergmansBSDBCRegion p₁ p₂) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u r hu hlim
  have hcont : ∀ (p : ℝ), 0 ≤ p → p ≤ 1 / 2 →
      ContinuousOn (fun α => binaryEntropy (binaryConv α p)) (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro p hp0 hp1
    have hconv : Continuous (fun α => binaryConv α p) := by unfold binaryConv; fun_prop
    refine binaryEntropy_continuousOn.comp hconv.continuousOn fun α hα => ?_
    have hm := binaryConv_mem_Icc_half hα.1 hα.2 hp0 hp1
    exact ⟨hm.1, by linarith [hm.2]⟩
  have hc1 := hcont p₁ hp₁ (le_trans h12 hp₂)
  have hc2 := hcont p₂ (le_trans hp₁ h12) hp₂
  choose α hα_mem hα1 hα2 using fun n => (hu n).2.2
  obtain ⟨α₀, hα₀_mem, φ, hφ_mono, hφ_lim⟩ := isCompact_Icc.tendsto_subseq hα_mem
  have hlim_sub : Tendsto (u ∘ φ) atTop (𝓝 r) := hlim.comp hφ_mono.tendsto_atTop
  have hlim1 : Tendsto (fun n => (u (φ n)).1) atTop (𝓝 r.1) := (continuous_fst.tendsto r).comp hlim_sub
  have hlim2 : Tendsto (fun n => (u (φ n)).2) atTop (𝓝 r.2) := (continuous_snd.tendsto r).comp hlim_sub
  have h01 : 0 ≤ r.1 := ge_of_tendsto hlim1 (Eventually.of_forall fun n => (hu (φ n)).1)
  have h02 : 0 ≤ r.2 := ge_of_tendsto hlim2 (Eventually.of_forall fun n => (hu (φ n)).2.1)
  have hf1_lim : Tendsto (fun n => binaryEntropy (binaryConv (α (φ n)) p₁) - binaryEntropy p₁)
      atTop (𝓝 (binaryEntropy (binaryConv α₀ p₁) - binaryEntropy p₁)) :=
    ((hc1.continuousWithinAt hα₀_mem).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_lim
        (Eventually.of_forall fun n => hα_mem (φ n)))).sub_const _
  have hf2_lim : Tendsto (fun n => 1 - binaryEntropy (binaryConv (α (φ n)) p₂))
      atTop (𝓝 (1 - binaryEntropy (binaryConv α₀ p₂))) :=
    ((hc2.continuousWithinAt hα₀_mem).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_lim
        (Eventually.of_forall fun n => hα_mem (φ n)))).const_sub 1
  have hr1 : r.1 ≤ binaryEntropy (binaryConv α₀ p₁) - binaryEntropy p₁ :=
    le_of_tendsto_of_tendsto hlim1 hf1_lim (Eventually.of_forall fun n => hα1 (φ n))
  have hr2 : r.2 ≤ 1 - binaryEntropy (binaryConv α₀ p₂) :=
    le_of_tendsto_of_tendsto hlim2 hf2_lim (Eventually.of_forall fun n => hα2 (φ n))
  exact ⟨h01, h02, α₀, hα₀_mem, hr1, hr2⟩

/-- Matching lemma between `bcAuxJoint` on `U × Bool` and `MrsGerber.lean`'s swapped `Bool × U`
    joint distribution. -/
private lemma bcAuxJoint_swap_match {U : Type*} [Fintype U]
    (W : BroadcastChannel Bool Bool Bool) (Pux : ProbDist (U × Bool)) :
    let P_XU : ProbDist (Bool × U) := Pux.map Prod.swap
    let J_mgl : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * W.trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) (W.nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, W.sum_one, mul_one, P_XU.sum_one] }
    mutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2))) =
      mutualInfo (J_mgl.map (fun z => (z.1.2, z.2.2))) ∧
    condMutualInfo ((bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1, z.1.1))) =
      condMutualInfo (J_mgl.map (fun z => (z.1.1, z.2.1, z.1.2))) := by
  classical
  intro P_XU J_mgl
  let eSwap : ((U × Bool) × (Bool × Bool)) ≃ ((Bool × U) × (Bool × Bool)) :=
    (Equiv.prodComm U Bool).prodCongr (Equiv.refl (Bool × Bool))
  have hJ : J_mgl = (bcAuxJoint W Pux).map eSwap := by
    apply bc_probDist_ext; rintro ⟨⟨x, u⟩, y⟩
    unfold J_mgl P_XU bcAuxJoint ProbDist.map; dsimp only
    rw [Finset.sum_eq_single ((u, x), y)]
    · simp only [eSwap, Equiv.prodCongr_apply, Prod.map_apply, Equiv.prodComm_apply,
        Prod.swap_prod_mk, Equiv.refl_apply, ↓reduceIte]
      rw [Finset.sum_eq_single (u, x)]
      · simp
      · intro ux' _ hne
        have : ux'.swap ≠ (x, u) := fun h => hne (by
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          exact Prod.ext h2 h1)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro z _ hne
      have : eSwap z ≠ ((x, u), y) := fun h => hne (eSwap.symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  constructor
  · have hm : J_mgl.map (fun z => (z.1.2, z.2.2)) =
        (bcAuxJoint W Pux).map (fun z => (z.1.1, z.2.2)) := by
      rw [hJ, map_comp_eq]; rfl
    rw [hm]
  · have hm : J_mgl.map (fun z => (z.1.1, z.2.1, z.1.2)) =
        (bcAuxJoint W Pux).map (fun z => (z.1.2, z.2.1, z.1.1)) := by
      rw [hJ, map_comp_eq]; rfl
    rw [hm]

/-- **Full Operational Bergmans Capacity Region for the Binary Symmetric Degraded Broadcast Channel**
    (Bergmans 1973; Wyner & Ziv 1973; Gallager 1974; Cover & Thomas §15.6.2; El Gamal–Kim §5.3):
    for every `0 ≤ p₁ ≤ p₂ ≤ 1/2`, the operational capacity region `bcCapacityRegion` of
    `degradedBSC p₁ p₂` is exactly
    `{ (R₁, R₂) ≥ 0 | ∃ α ∈ [0, 1/2], R₁ ≤ h(α ★ p₁) - h(p₁) ∧ R₂ ≤ 1 - h(α ★ p₂) }`. -/
theorem degradedBSC_operational_capacity_region {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    bcCapacityRegion (degradedBSC p₁ p₂ hp₁ h12 hp₂) =
      { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
        ∃ α ∈ Set.Icc (0 : ℝ) (1 / 2),
          r.1 ≤ binaryEntropy (binaryConv α p₁) - binaryEntropy p₁ ∧
          r.2 ≤ 1 - binaryEntropy (binaryConv α p₂) } := by
  rw [degradedBC_capacity_theorem _ (degradedBSC_isPhysicallyDegraded hp₁ h12 hp₂)]
  change degradedBCRegion (degradedBSC p₁ p₂ hp₁ h12 hp₂) = bergmansBSDBCRegion p₁ p₂
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ (isClosed_bergmansBSDBCRegion hp₁ h12 hp₂)
    rintro ⟨r₁, r₂⟩ ⟨hr1, hr2, kU, Pux, h2, h1⟩
    have hmatch := bcAuxJoint_swap_match (degradedBSC p₁ p₂ hp₁ h12 hp₂) Pux
    dsimp only at hmatch
    obtain ⟨α, hα_mem, hα2, hα1⟩ :=
      degradedBSC_bergmans_outer_bound (Pux.map Prod.swap) hp₁ h12 hp₂
    rw [hmatch.1] at h2
    rw [hmatch.2] at h1
    exact ⟨hr1, hr2, α, hα_mem, le_trans h1 hα1, le_trans h2 hα2⟩
  · rintro ⟨r₁, r₂⟩ ⟨hr1, hr2, α, hα_mem, h1, h2⟩
    apply subset_closure
    have hach := degradedBSC_bergmans_achievable hp₁ h12 hp₂ hα_mem.1 hα_mem.2
    dsimp only at hach
    let P_UX_bool : ProbDist (Bool × Bool) :=
      (bsc α hα_mem.1 (by linarith [hα_mem.2])).joint (ProbDist.uniform : ProbDist Bool)
    have hswap_eq : P_UX_bool.map Prod.swap =
        ((bsc α hα_mem.1 (by linarith [hα_mem.2])).joint (ProbDist.uniform : ProbDist Bool)).map Prod.swap := rfl
    have hmatch := bcAuxJoint_swap_match (degradedBSC p₁ p₂ hp₁ h12 hp₂) P_UX_bool
    dsimp only at hmatch
    let eBool : Bool ≃ Fin (Fintype.card Bool) := Fintype.equivFin Bool
    let P_fin : ProbDist (Fin (Fintype.card Bool) × Bool) := P_UX_bool.map (fun ux => (eBool ux.1, ux.2))
    have hrel := bcAuxJoint_relabel (degradedBSC p₁ p₂ hp₁ h12 hp₂) P_UX_bool eBool
    dsimp only at hrel
    refine ⟨hr1, hr2, Fintype.card Bool, P_fin, ?_, ?_⟩
    · rw [hrel.1, hmatch.1, hach.1]; exact h2
    · rw [hrel.2.1, hmatch.2, hach.2]; exact h1

end OperationalBergmans

end InfoTheory.Bridge
