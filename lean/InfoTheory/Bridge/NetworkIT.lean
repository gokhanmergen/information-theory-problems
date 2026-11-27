import InfoTheory.Bridge.ChannelAchievability
import Mathlib.Analysis.Convex.Hull

/-!
# Network Information Theory: Slepian–Wolf and Two-User MAC Capacity Region
(Cover & Thomas Ch. 15, Theorems 15.4.1 & 15.3.1; El Gamal–Kim Theorems 10.1 & 4.3)

Purely additive, kernel-verified formalization of the two cornerstone theorems of
Network Information Theory built on top of `InfoTheory.Bridge.ChannelAchievability`:

1. **Slepian–Wolf Distributed Source Coding Theorem** (Cover & Thomas Thm. 15.4.1;
   El Gamal–Kim Thm. 10.1):
   - `slepianWolfError`, `IsSlepianWolfAchievable`, `slepianWolfSingleLetter`
   - `slepianWolf_converse_bounds` and `slepian_wolf_converse` (Fano + subadditivity converse)
   - `slepianWolfDec` and `slepianWolf_random_binning_bound` (uniform random binning +
     unique joint-typicality decoding finite-sum error bound)
   - `slepian_wolf_achievability` (strictly interior rate pairs are operationally achievable)
   - `slepian_wolf_theorem` (`closure { r | IsSlepianWolfAchievable P r.1 r.2 } = slepianWolfSingleLetter P`)

2. **Two-User Discrete Memoryless Multiple-Access Channel Capacity Region**
   (Cover & Thomas Thm. 15.3.1; El Gamal–Kim Thm. 4.3):
   - `macAvgError`, `IsMACAchievable`, `macOperationalRegion`
   - `macPentagon`, `macSingleLetterRegion` (closure of the convex hull of product-input pentagons)
   - `macTypicalSet`, `macTypicalDec`, and `mac_random_coding_bound` (3-way joint typicality
     and independent random coding ensemble error bound)
   - `mac_achievability_pentagon` (every strictly interior rate pair of `macPentagon W P₁ P₂`
     is operationally achievable; plus time-sharing convexity of `macOperationalRegion W`)
   - `mac_converse` (Fano + time-varying memoryless channel tensorization inequalities for
     `R₁`, `R₂`, and `R₁ + R₂`) and `mac_achievable_mem_singleLetter`
   - `mac_capacity_theorem` (`macOperationalRegion W = macSingleLetterRegion W`)

All theorems leave `Core/`, `Problems/`, `Known/`, `Bridge.lean`, and existing `Bridge/*`
files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Shared Private Helper Lemmas -/

section SharedHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma probDist_map_id (P : ProbDist α) : P.map id = P := by
  classical
  cases P with | mk pmf h0 h1 =>
  unfold ProbDist.map
  congr
  funext a
  simp

private lemma shannonEntropy_map_injective (P : ProbDist α) {f : α → β}
    (hf : Function.Injective f) :
    shannonEntropy (P.map f) = shannonEntropy P := by
  have : Nonempty α := nonempty_of_probDist P
  let g : β → α := Function.invFun f
  have hgf : g ∘ f = id := funext (Function.leftInverse_invFun hf)
  have h1 : shannonEntropy (P.map f) ≤ shannonEntropy P := shannonEntropy_map_le f P
  have h2 : shannonEntropy P ≤ shannonEntropy (P.map f) := by
    have heq : (P.map f).map g = P := by
      rw [map_comp_eq, hgf, probDist_map_id]
    calc shannonEntropy P = shannonEntropy ((P.map f).map g) := by rw [heq]
      _ ≤ shannonEntropy (P.map f) := shannonEntropy_map_le g (P.map f)
  exact le_antisymm h1 h2

private lemma probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  unfold ProbDist.map ProbDist.fst
  congr; funext a
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_single a (fun a' _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ _) h)
    |>.trans ?_
  simp

private lemma probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  unfold ProbDist.map ProbDist.snd
  congr; funext b
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_eq_single b (fun b' _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ _) h)
    |>.trans ?_
  simp

private lemma probDist_prod_fst (P : ProbDist α) (Q : ProbDist β) : (P.prod Q).fst = P := by
  unfold ProbDist.fst ProbDist.prod
  congr; funext a; dsimp only
  rw [← Finset.mul_sum, Q.sum_one, mul_one]

private lemma probDist_prod_snd (P : ProbDist α) (Q : ProbDist β) : (P.prod Q).snd = Q := by
  unfold ProbDist.snd ProbDist.prod
  congr; funext b; dsimp only
  rw [← Finset.sum_mul, P.sum_one, one_mul]

private lemma probDist_prod_map_prod (P : ProbDist α) (Q : ProbDist β)
    (f : α → γ) (g : β → δ) :
    (P.prod Q).map (Prod.map f g) = (P.map f).prod (Q.map g) := by
  classical
  unfold ProbDist.map ProbDist.prod
  congr; funext ⟨c, d⟩; dsimp only [Prod.map]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : f a = c <;> by_cases h2 : g b = d <;> simp [h1, h2]

private lemma log2_two_rpow_eq (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma log2_mono_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma log2_pow_nat {x : ℝ} (n : ℕ) :
    log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow, mul_div_assoc]

private lemma two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {n : ℕ} (hn : log2 (1 / c) / ε ≤ (n : ℝ)) :
    (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ c := by
  have h1 : log2 (1 / c) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog : Real.log (1 / c) ≤ (n : ℝ) * ε * Real.log 2 := by
    unfold log2 at h1
    exact (div_le_iff₀ hlog2).mp h1
  have hexp : 1 / c ≤ (2 : ℝ) ^ ((n : ℝ) * ε) := by
    calc 1 / c
      _ = Real.exp (Real.log (1 / c)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp ((n : ℝ) * ε * Real.log 2) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (Real.log 2 * ((n : ℝ) * ε)) := by ring_nf
      _ = (2 : ℝ) ^ ((n : ℝ) * ε) := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * ε)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul1 : (2 : ℝ) ^ (-((n : ℝ) * ε)) * (2 : ℝ) ^ ((n : ℝ) * ε) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hmul2 : (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ 1 := by
    calc (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) * (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_right hexp (le_of_lt hpos)
      _ = 1 := by rw [mul_comm, hmul1]
  have hmul3 := mul_le_mul_of_nonneg_left hmul2 (le_of_lt hc)
  have hsimp : c * ((1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))) = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
    field_simp [ne_of_gt hc]
  linarith

private lemma max_one_floor_two_rpow_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
  have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hfl : 1 ≤ Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := Nat.le_floor (by exact_mod_cast hge1)
  rw [max_eq_right hfl]
  exact Nat.floor_le (by positivity)

private lemma half_two_rpow_le_max_one_floor (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ ((max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
  let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left 1 _
  have hfl : (2 : ℝ) ^ ((n : ℝ) * R) < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hle : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast le_max_right 1 _
  have _ := hR
  linarith

private lemma exists_le_of_weighted_sum_le' {ι : Type*} [Fintype ι]
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

private lemma sum_pi_prod_mul_single' {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Q : ProbDist γ) (i₀ : ι) (f : γ → ℝ) :
    ∑ g : ι → γ, (∏ i : ι, Q.pmf (g i)) * f (g i₀) = ∑ x : γ, Q.pmf x * f x := by
  let F : ι → γ → ℝ := fun i x => if i = i₀ then Q.pmf x * f x else Q.pmf x
  have hfun : ∀ g : ι → γ,
      (∏ i : ι, Q.pmf (g i)) * f (g i₀) = ∏ i : ι, F i (g i) := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ (fun i => Q.pmf (g i)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase Finset.univ (fun i => F i (g i)) (Finset.mem_univ i₀)]
    have hrest : ∏ i ∈ Finset.univ.erase i₀, F i (g i) =
        ∏ i ∈ Finset.univ.erase i₀, Q.pmf (g i) :=
      Finset.prod_congr rfl fun i hi => by simp [F, (Finset.mem_erase.mp hi).1]
    rw [hrest]
    simp only [F, ↓reduceIte]
    ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x : γ, F i x) (Finset.mem_univ i₀)]
  have hi₀ : ∑ x : γ, F i₀ x = ∑ x : γ, Q.pmf x * f x := by simp [F]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ∑ x : γ, F i x = 1 :=
    Finset.prod_eq_one fun i hi => by
      simp only [F, (Finset.mem_erase.mp hi).1, ↓reduceIte]
      exact Q.sum_one
  rw [hi₀, hrest, mul_one]

private lemma sum_pi_prod_mul_pair' {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Q : ProbDist γ) (i₀ i₁ : ι) (hne : i₁ ≠ i₀) (f h : γ → ℝ) :
    ∑ g : ι → γ, (∏ i : ι, Q.pmf (g i)) * (f (g i₀) * h (g i₁)) =
      (∑ x : γ, Q.pmf x * f x) * (∑ x' : γ, Q.pmf x' * h x') := by
  let F : ι → γ → ℝ := fun i x =>
    if i = i₀ then Q.pmf x * f x
    else if i = i₁ then Q.pmf x * h x
    else Q.pmf x
  have hi₁_mem : i₁ ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩
  have hfun : ∀ g : ι → γ,
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
    rw [hrest]
    simp only [F, hne, ↓reduceIte]
    ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x : γ, F i x) (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase (Finset.univ.erase i₀) (fun i => ∑ x : γ, F i x) hi₁_mem]
  have hi₀_sum : ∑ x : γ, F i₀ x = ∑ x : γ, Q.pmf x * f x := by simp [F]
  have hi₁_sum : ∑ x : γ, F i₁ x = ∑ x : γ, Q.pmf x * h x := by simp [F, hne]
  have hrest : ∏ i ∈ (Finset.univ.erase i₀).erase i₁, ∑ x : γ, F i x = 1 :=
    Finset.prod_eq_one fun i hi => by
      have h1 : i ≠ i₁ := (Finset.mem_erase.mp hi).1
      have h2 : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp only [F, h1, h2, ↓reduceIte]
      exact Q.sum_one
  rw [hi₀_sum, hi₁_sum, hrest, mul_one]

private lemma estErrorProb_map_pair (Q : ProbDist γ) (h : γ → α) (k : γ → β) (g : β → α) :
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

/-- Time-varying memoryless product channel `∏_i V_i`. -/
private def piDMC {n : ℕ} (V : Fin n → DMC α β) : DMC (Fin n → α) (Fin n → β) where
  trans := fun x y => ∏ i : Fin n, (V i).trans (x i) (y i)
  nonneg := fun x y => Finset.prod_nonneg fun i _ => (V i).nonneg (x i) (y i)
  sum_one := fun x => by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => (V i).sum_one (x i)

private lemma piDMC_output_coord_marginal {n : ℕ} (V : Fin n → DMC α β)
    (P : ProbDist (Fin n → α)) (i : Fin n) :
    ((piDMC V).joint P).snd.map (fun y => y i) =
      ((V i).joint (P.map (fun x => x i))).snd := by
  classical
  unfold ProbDist.map ProbDist.snd DMC.joint piDMC
  congr; funext b; dsimp only
  have hpush : ∀ y : Fin n → β,
      (if y i = b then ∑ x : Fin n → α, P.pmf x * ∏ j : Fin n, (V j).trans (x j) (y j) else 0) =
        ∑ x : Fin n → α, if y i = b then P.pmf x * ∏ j : Fin n, (V j).trans (x j) (y j) else 0 :=
    fun y => by split_ifs <;> simp
  simp_rw [hpush]
  rw [Finset.sum_comm]
  have hcoord : ∀ x : Fin n → α,
      (∑ y : Fin n → β, if y i = b then P.pmf x * ∏ j : Fin n, (V j).trans (x j) (y j) else 0) =
        P.pmf x * (V i).trans (x i) b := by
    intro x
    let F : Fin n → β → ℝ := fun j yj =>
      if j = i then (if yj = b then (V j).trans (x j) yj else 0) else (V j).trans (x j) yj
    have hfun : ∀ y : Fin n → β,
        (if y i = b then P.pmf x * ∏ j : Fin n, (V j).trans (x j) (y j) else 0) =
          P.pmf x * ∏ j : Fin n, F j (y j) := by
      intro y
      conv_rhs => rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (y j)) (Finset.mem_univ i)]
      have hrest : ∏ j ∈ Finset.univ.erase i, F j (y j) =
          ∏ j ∈ Finset.univ.erase i, (V j).trans (x j) (y j) :=
        Finset.prod_congr rfl fun j hj => by simp [F, (Finset.mem_erase.mp hj).1]
      rw [hrest]
      by_cases hy : y i = b
      · simp only [hy, ↓reduceIte, F]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => (V j).trans (x j) (y j))
          (Finset.mem_univ i), hy]
      · simp [F, hy]
    simp_rw [hfun, ← Finset.mul_sum, ← Fintype.prod_sum F]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ yj : β, F j yj) (Finset.mem_univ i)]
    have hi : ∑ yj : β, F i yj = (V i).trans (x i) b := by simp [F]
    have hrest : ∏ j ∈ Finset.univ.erase i, (∑ yj : β, F j yj) = 1 :=
      Finset.prod_eq_one fun j hj => by
        simp only [F, ite_eq_right_iff.mpr (fun h => absurd h (Finset.mem_erase.mp hj).1)]
        exact (V j).sum_one (x j)
    rw [hi, hrest, mul_one]
  simp_rw [hcoord]
  have h := sum_pmf_mul_comp P (fun x => x i) (fun a => (V i).trans a b)
  simpa [ProbDist.map] using h

private lemma piDMC_mutualInfo_le_sum {n : ℕ} (V : Fin n → DMC α β)
    (P : ProbDist (Fin n → α)) :
    mutualInfo ((piDMC V).joint P) ≤
      ∑ i : Fin n, mutualInfo ((V i).joint (P.map (fun x => x i))) := by
  have hmi_n : mutualInfo ((piDMC V).joint P) =
      shannonEntropy ((piDMC V).joint P).snd -
        ∑ x : Fin n → α, P.pmf x * shannonEntropy (dmcRow (piDMC V) x) := by
    unfold mutualInfo
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]
    ring
  have hrow : ∀ x : Fin n → α,
      shannonEntropy (dmcRow (piDMC V) x) = ∑ i : Fin n, shannonEntropy (dmcRow (V i) (x i)) := by
    intro x
    have heq : dmcRow (piDMC V) x = piProdDist (fun i => dmcRow (V i) (x i)) := rfl
    rw [heq, shannonEntropy_piProdDist]
  have hcond : ∑ x : Fin n → α, P.pmf x * shannonEntropy (dmcRow (piDMC V) x) =
      ∑ i : Fin n, ∑ a : α, (P.map (fun x => x i)).pmf a * shannonEntropy (dmcRow (V i) a) := by
    simp_rw [hrow, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact sum_pmf_mul_comp P (fun x => x i) (fun a => shannonEntropy (dmcRow (V i) a))
  have hout : shannonEntropy ((piDMC V).joint P).snd ≤
      ∑ i : Fin n, shannonEntropy ((V i).joint (P.map (fun x => x i))).snd := by
    calc shannonEntropy ((piDMC V).joint P).snd
      _ ≤ ∑ i : Fin n, shannonEntropy (((piDMC V).joint P).snd.map (fun y => y i)) :=
          shannonEntropy_pi_le_sum n ((piDMC V).joint P).snd
      _ = ∑ i : Fin n, shannonEntropy ((V i).joint (P.map (fun x => x i))).snd := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [piDMC_output_coord_marginal]
  have hmi_i : ∀ i : Fin n,
      mutualInfo ((V i).joint (P.map (fun x => x i))) =
        shannonEntropy ((V i).joint (P.map (fun x => x i))).snd -
          ∑ a : α, (P.map (fun x => x i)).pmf a * shannonEntropy (dmcRow (V i) a) := by
    intro i
    unfold mutualInfo
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]
    ring
  rw [hmi_n, hcond]
  simp_rw [hmi_i, Finset.sum_sub_distrib]
  linarith

/-- Conditional mixture law `M(a, b, c) = Pz(c) * Q_c(a, b)`. -/
private def condMixDist (Pz : ProbDist γ) (Q : γ → ProbDist (α × β)) : ProbDist (α × β × γ) where
  pmf := fun t => Pz.pmf t.2.2 * (Q t.2.2).pmf (t.1, t.2.1)
  nonneg := fun t => mul_nonneg (Pz.nonneg t.2.2) ((Q t.2.2).nonneg (t.1, t.2.1))
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    trans (∑ c : γ, Pz.pmf c * ∑ a : α, ∑ b : β, (Q c).pmf (a, b))
    · trans (∑ a : α, ∑ c : γ, ∑ b : β, Pz.pmf c * (Q c).pmf (a, b))
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    · refine (Finset.sum_congr rfl fun c _ => ?_).trans Pz.sum_one
      rw [← Fintype.sum_prod_type, (Q c).sum_one, mul_one]

private lemma condMixDist_shannonEntropy (Pz : ProbDist γ) (Q : γ → ProbDist (α × β)) :
    shannonEntropy (condMixDist Pz Q) =
      shannonEntropy Pz + ∑ c : γ, Pz.pmf c * shannonEntropy (Q c) := by
  let e : (γ × (α × β)) ≃ (α × β × γ) :=
    { toFun := fun t => (t.2.1, t.2.2, t.1)
      invFun := fun t => (t.2.2, (t.1, t.2.1))
      left_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  let W : DMC γ (α × β) :=
    { trans := fun c ab => (Q c).pmf ab
      nonneg := fun c ab => (Q c).nonneg ab
      sum_one := fun c => (Q c).sum_one }
  have heq : (W.joint Pz).map e = condMixDist Pz Q := by
    classical
    unfold ProbDist.map DMC.joint condMixDist
    congr; funext ⟨a, b, c⟩; dsimp only [W]
    rw [Finset.sum_eq_single (c, (a, b))]
    · simp [e]
    · intro x _ hne
      have : e x ≠ (a, b, c) := fun h => hne (by
        have := congrArg e.symm h
        simpa [e] using this)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← heq, shannonEntropy_map_equiv e (W.joint Pz), dmc_joint_shannonEntropy]
  rfl

private lemma condMixDist_condMutualInfo (Pz : ProbDist γ) (Q : γ → ProbDist (α × β)) :
    condMutualInfo (condMixDist Pz Q) = ∑ c : γ, Pz.pmf c * mutualInfo (Q c) := by
  classical
  let W₁ : DMC γ α :=
    { trans := fun c a => (Q c).fst.pmf a
      nonneg := fun c a => (Q c).fst.nonneg a
      sum_one := fun c => (Q c).fst.sum_one }
  let W₂ : DMC γ β :=
    { trans := fun c b => (Q c).snd.pmf b
      nonneg := fun c b => (Q c).snd.nonneg b
      sum_one := fun c => (Q c).snd.sum_one }
  have hxz : (condMixDist Pz Q).map (fun t => (t.1, t.2.2)) = (W₁.joint Pz).map Prod.swap := by
    unfold ProbDist.map condMixDist DMC.joint
    congr; funext ⟨a, c⟩; dsimp only [W₁, ProbDist.fst]
    rw [Fintype.sum_prod_type]
    have h1 : ∑ a' : α, ∑ bc : β × γ,
        (if (a', bc.2) = (a, c) then Pz.pmf bc.2 * (Q bc.2).pmf (a', bc.1) else 0) =
        Pz.pmf c * ∑ b : β, (Q c).pmf (a, b) := by
      rw [Finset.sum_eq_single a]
      · rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : ∑ ca : γ × α,
        (if (ca.2, ca.1) = (a, c) then Pz.pmf ca.1 * ∑ b : β, (Q ca.1).pmf (ca.2, b) else 0) =
        Pz.pmf c * ∑ b : β, (Q c).pmf (a, b) := by
      rw [Finset.sum_eq_single (c, a)]
      · simp
      · intro ⟨c', a'⟩ _ hne
        have : ¬ (a' = a ∧ c' = c) := fun ⟨ha, hc⟩ => hne (by subst ha; subst hc; rfl)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    dsimp only [Prod.swap]
    convert h1.trans h2.symm
  have hyz : (condMixDist Pz Q).map (fun t => (t.2.1, t.2.2)) = (W₂.joint Pz).map Prod.swap := by
    unfold ProbDist.map condMixDist DMC.joint
    congr; funext ⟨b, c⟩; dsimp only [W₂, ProbDist.snd]
    rw [Fintype.sum_prod_type]
    have h1 : ∑ a : α, ∑ bc : β × γ,
        (if (bc.1, bc.2) = (b, c) then Pz.pmf bc.2 * (Q bc.2).pmf (a, bc.1) else 0) =
        Pz.pmf c * ∑ a : α, (Q c).pmf (a, b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single (b, c)]
      · simp
      · intro bc _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : ∑ cb : γ × β,
        (if (cb.2, cb.1) = (b, c) then Pz.pmf cb.1 * ∑ a : α, (Q cb.1).pmf (a, cb.2) else 0) =
        Pz.pmf c * ∑ a : α, (Q c).pmf (a, b) := by
      rw [Finset.sum_eq_single (c, b)]
      · simp
      · intro ⟨c', b'⟩ _ hne
        have : ¬ (b' = b ∧ c' = c) := fun ⟨hb, hc⟩ => hne (by subst hb; subst hc; rfl)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    dsimp only [Prod.swap]
    convert h1.trans h2.symm
  have hz : (condMixDist Pz Q).map (fun t => t.2.2) = Pz := by
    unfold ProbDist.map condMixDist
    congr; funext c; dsimp only
    rw [Fintype.sum_prod_type]
    have h1 : ∀ a : α, ∑ bc : β × γ,
        (if bc.2 = c then Pz.pmf bc.2 * (Q bc.2).pmf (a, bc.1) else 0) =
        Pz.pmf c * ∑ b : β, (Q c).pmf (a, b) := fun a => by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_eq_single c]
      · simp
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [h1, ← Finset.mul_sum, ← Fintype.sum_prod_type, (Q c).sum_one, mul_one]
  unfold condMutualInfo
  dsimp only
  rw [hxz, hyz, hz, shannonEntropy_swap, shannonEntropy_swap,
      dmc_joint_shannonEntropy W₁ Pz, dmc_joint_shannonEntropy W₂ Pz,
      condMixDist_shannonEntropy Pz Q]
  have hmi : ∑ c : γ, Pz.pmf c * mutualInfo (Q c) =
      (∑ c : γ, Pz.pmf c * shannonEntropy (dmcRow W₁ c)) +
      (∑ c : γ, Pz.pmf c * shannonEntropy (dmcRow W₂ c)) -
      (∑ c : γ, Pz.pmf c * shannonEntropy (Q c)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold mutualInfo
    change Pz.pmf c * (shannonEntropy (Q c).fst + shannonEntropy (Q c).snd - shannonEntropy (Q c)) =
      Pz.pmf c * shannonEntropy (Q c).fst + Pz.pmf c * shannonEntropy (Q c).snd -
        Pz.pmf c * shannonEntropy (Q c)
    ring
  linarith

/-- Convexity preserves uniform averages over `Fin n`. -/
private lemma convex_avg_mem {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) :
    ∀ (n : ℕ), 0 < n → ∀ (v : Fin n → ℝ × ℝ), (∀ i, v i ∈ S) →
      (((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (v i).1,
       ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (v i).2) ∈ S := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _ v hv
    cases k with
    | zero =>
      have h0 : (((1 : ℝ) / ((1 : ℕ) : ℝ)) * ∑ i : Fin 1, (v i).1,
          ((1 : ℝ) / ((1 : ℕ) : ℝ)) * ∑ i : Fin 1, (v i).2) = v 0 := by
        ext <;> simp
      rw [h0]
      exact hv 0
    | succ m =>
      have hkm : 0 < m + 1 := Nat.succ_pos m
      have htail := ih hkm (fun i => v i.succ) (fun i => hv i.succ)
      let p : ℝ × ℝ := v 0
      let q : ℝ × ℝ :=
        (((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) * ∑ i : Fin (m + 1), (v i.succ).1,
         ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) * ∑ i : Fin (m + 1), (v i.succ).2)
      let a : ℝ := (1 : ℝ) / ((m + 2 : ℕ) : ℝ)
      let b : ℝ := ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)
      have ha : 0 ≤ a := by positivity
      have hb : 0 ≤ b := by positivity
      have hab : a + b = 1 := by
        dsimp only [a, b]
        have hpos : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        rw [← add_div]
        have hnum : (1 : ℝ) + ((m + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
        rw [hnum, div_self hpos]
      have hcomb : a • p + b • q ∈ S := hS (hv 0) htail ha hb hab
      have heq : a • p + b • q =
          (((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) * ∑ i : Fin (m + 2), (v i).1,
           ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) * ∑ i : Fin (m + 2), (v i).2) := by
        have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Fin.sum_univ_succ, p, q, a, b]
          field_simp [hm1]
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Fin.sum_univ_succ, p, q, a, b]
          field_simp [hm1]
      rw [← heq]
      exact hcomb

/-- Every point of a polymatroid pentagon lies in any convex set containing its 5 vertices. -/
private lemma mem_convex_of_pentagon_vertices {S : Set (ℝ × ℝ)} (hS : Convex ℝ S)
    {A B C x y : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hAC : A ≤ C) (hBC : B ≤ C) (hCAB : C ≤ A + B)
    (hv0 : (0, 0) ∈ S) (hv1 : (A, 0) ∈ S) (hv2 : (A, C - A) ∈ S)
    (hv3 : (C - B, B) ∈ S) (hv4 : (0, B) ∈ S)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxA : x ≤ A) (hyB : y ≤ B) (hxyC : x + y ≤ C) :
    (x, y) ∈ S := by
  -- Helper: any point in `[0, u] × [0, v]` lies in `S` once its 4 corners do
  have hrect : ∀ (u v s t : ℝ), 0 ≤ u → 0 ≤ v →
      (0, 0) ∈ S → (u, 0) ∈ S → (0, v) ∈ S → (u, v) ∈ S →
      0 ≤ s → s ≤ u → 0 ≤ t → t ≤ v → (s, t) ∈ S := by
    intro u v s t hu hv h00 hu0 h0v huv hs0 hsu ht0 htv
    have h0t : (0, t) ∈ S := by
      by_cases hv0' : v = 0
      · have : t = 0 := by linarith
        subst this; exact h00
      · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0')
        have hcomb := hS h00 h0v (show 0 ≤ 1 - t / v by rw [sub_nonneg, div_le_one hvpos]; exact htv)
          (div_nonneg ht0 (le_of_lt hvpos)) (by ring)
        have heq : (1 - t / v) • ((0 : ℝ), (0 : ℝ)) + (t / v) • ((0 : ℝ), v) = (0, t) := by
          ext <;> simp [div_mul_cancel₀ t (ne_of_gt hvpos)]
        rw [← heq]; exact hcomb
    have hut : (u, t) ∈ S := by
      by_cases hv0' : v = 0
      · have : t = 0 := by linarith
        subst this; exact hu0
      · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0')
        have hcomb := hS hu0 huv (show 0 ≤ 1 - t / v by rw [sub_nonneg, div_le_one hvpos]; exact htv)
          (div_nonneg ht0 (le_of_lt hvpos)) (by ring)
        have heq : (1 - t / v) • (u, (0 : ℝ)) + (t / v) • (u, v) = (u, t) := by
          ext
          · simp; ring
          · simp [div_mul_cancel₀ t (ne_of_gt hvpos)]
        rw [← heq]; exact hcomb
    by_cases hu0' : u = 0
    · have : s = 0 := by linarith
      subst this; exact h0t
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0')
      have hcomb := hS h0t hut (show 0 ≤ 1 - s / u by rw [sub_nonneg, div_le_one hupos]; exact hsu)
        (div_nonneg hs0 (le_of_lt hupos)) (by ring)
      have heq : (1 - s / u) • ((0 : ℝ), t) + (s / u) • (u, t) = (s, t) := by
        ext
        · simp [div_mul_cancel₀ s (ne_of_gt hupos)]
        · simp; ring
      rw [← heq]; exact hcomb
  -- `(C - B, 0) ∈ S` and `(0, C - A) ∈ S`
  have hCB0 : (C - B, 0) ∈ S := by
    by_cases hA : A = 0
    · have : C - B = 0 := by linarith
      rw [this]; exact hv0
    · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
      let t := (C - B) / A
      have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hApos)
      have ht1 : t ≤ 1 := (div_le_one hApos).mpr (by linarith)
      have hcomb := hS hv0 hv1 (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      have heq : (1 - t) • ((0 : ℝ), (0 : ℝ)) + t • (A, (0 : ℝ)) = (C - B, 0) := by
        ext <;> simp [t, div_mul_cancel₀ _ (ne_of_gt hApos)]
      rw [← heq]; exact hcomb
  have h0CA : (0, C - A) ∈ S := by
    by_cases hB : B = 0
    · have : C - A = 0 := by linarith
      rw [this]; exact hv0
    · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
      let t := (C - A) / B
      have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hBpos)
      have ht1 : t ≤ 1 := (div_le_one hBpos).mpr (by linarith)
      have hcomb := hS hv0 hv4 (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      have heq : (1 - t) • ((0 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), B) = (0, C - A) := by
        ext <;> simp [t, div_mul_cancel₀ _ (ne_of_gt hBpos)]
      rw [← heq]; exact hcomb
  by_cases hx_left : x ≤ C - B
  · exact hrect (C - B) B x y (by linarith) hB0 hv0 hCB0 hv4 hv3 hx0 hx_left hy0 hyB
  · by_cases hy_bot : y ≤ C - A
    · exact hrect A (C - A) x y hA0 (by linarith) hv0 hv1 h0CA hv2 hx0 hxA hy0 hy_bot
    · push Not at hx_left hy_bot
      have hp : (C - B, C - A) ∈ S :=
        hrect (C - B) B (C - B) (C - A) (by linarith) hB0 hv0 hCB0 hv4 hv3
          (by linarith) le_rfl (by linarith) (by linarith)
      let d : ℝ := A + B - C
      have hd : 0 < d := by dsimp only [d]; linarith
      have hdne : d ≠ 0 := ne_of_gt hd
      let α : ℝ := (x - (C - B)) / d
      let β : ℝ := (y - (C - A)) / d
      let γ : ℝ := (C - x - y) / d
      have hα : 0 < α := div_pos (by linarith) hd
      have hβ : 0 < β := div_pos (by linarith) hd
      have hγ : 0 ≤ γ := div_nonneg (by linarith) (le_of_lt hd)
      have hsum : α + β + γ = 1 := by
        dsimp only [α, β, γ]
        rw [← add_div, ← add_div, div_eq_one_iff_eq hdne]
        dsimp only [d]; ring
      have hαβ : 0 < α + β := by linarith
      let q : ℝ × ℝ := (α / (α + β)) • (A, C - A) + (β / (α + β)) • (C - B, B)
      have hq : q ∈ S :=
        hS hv2 hv3 (div_nonneg (le_of_lt hα) (le_of_lt hαβ))
          (div_nonneg (le_of_lt hβ) (le_of_lt hαβ))
          (by rw [← add_div, div_self (ne_of_gt hαβ)])
      have hcomb : (α + β) • q + γ • (C - B, C - A) ∈ S :=
        hS hq hp (le_of_lt hαβ) hγ (by linarith)
      have heq : (α + β) • q + γ • (C - B, C - A) = (x, y) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, q]
          have h1 : (α + β) * (α / (α + β) * A + β / (α + β) * (C - B)) =
              α * A + β * (C - B) := by
            field_simp [ne_of_gt hαβ]
          rw [h1]
          dsimp only [α, β, γ]
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
              ← add_div, ← add_div, div_eq_iff hdne]
          dsimp only [d]; ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, q]
          have h1 : (α + β) * (α / (α + β) * (C - A) + β / (α + β) * B) =
              α * (C - A) + β * B := by
            field_simp [ne_of_gt hαβ]
          rw [h1]
          dsimp only [α, β, γ]
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
              ← add_div, ← add_div, div_eq_iff hdne]
          dsimp only [d]; ring
      rw [← heq]
      exact hcomb

end SharedHelpers

/-! ### 1. Slepian–Wolf Theorem (Cover & Thomas Thm. 15.4.1; El Gamal–Kim Thm. 10.1) -/

section SlepianWolf

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Error probability of a blocklength-`n` Slepian–Wolf code `(f₁, f₂, dec)` on an i.i.d.
    correlated source `P` over `α × β`. -/
noncomputable def slepianWolfError (P : ProbDist (α × β)) (n M₁ M₂ : ℕ)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (dec : Fin M₁ → Fin M₂ → (Fin n → α) × (Fin n → β)) : ℝ := by
  classical
  exact ∑ xy : (Fin n → α) × (Fin n → β),
    if dec (f₁ xy.1) (f₂ xy.2) ≠ xy then (jointIidDist P n).pmf xy else 0

/-- Operational achievability of rate pair `(R₁, R₂)` for distributed lossless compression of
    an i.i.d. correlated source `P` (Cover & Thomas §15.4). -/
def IsSlepianWolfAchievable (P : ProbDist (α × β)) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
      (dec : Fin M₁ → Fin M₂ → (Fin n → α) × (Fin n → β)),
      slepianWolfError P n M₁ M₂ f₁ f₂ dec ≤ δ

/-- Single-letter Slepian–Wolf rate region (Cover & Thomas, Theorem 15.4.1):
    `R₁ ≥ H(X | Y)`, `R₂ ≥ H(Y | X)`, `R₁ + R₂ ≥ H(X, Y)`. -/
def slepianWolfSingleLetter (P : ProbDist (α × β)) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
        condEntropy P ≤ r.1 ∧
        condEntropy (P.map Prod.swap) ≤ r.2 ∧
        shannonEntropy P ≤ r.1 + r.2 }

private lemma shannonEntropy_iidDist (P : ProbDist α) (n : ℕ) :
    shannonEntropy (iidDist P n) = (n : ℝ) * shannonEntropy P := by
  have heq : iidDist P n = piProdDist (fun _ : Fin n => P) := rfl
  rw [heq, shannonEntropy_piProdDist]
  simp

private lemma shannonEntropy_jointIidDist (P : ProbDist (α × β)) (n : ℕ) :
    shannonEntropy (jointIidDist P n) = (n : ℝ) * shannonEntropy P := by
  have hmap : (jointIidDist P n).map (zipEquiv α β n) = iidDist P n := by
    classical
    unfold ProbDist.map
    congr; funext z
    rw [Finset.sum_eq_single ((zipEquiv α β n).symm z)]
    · simp [jointIidDist_pmf]; rfl
    · intro xy _ hne
      have : zipEquiv α β n xy ≠ z := fun h =>
        hne ((zipEquiv α β n).symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← shannonEntropy_map_equiv (zipEquiv α β n) (jointIidDist P n), hmap, shannonEntropy_iidDist]

private lemma slepianWolfError_swap (P : ProbDist (α × β)) (n M₁ M₂ : ℕ)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (dec : Fin M₁ → Fin M₂ → (Fin n → α) × (Fin n → β)) :
    slepianWolfError (P.map Prod.swap) n M₂ M₁ f₂ f₁ (fun m₂ m₁ => (dec m₁ m₂).swap) =
      slepianWolfError P n M₁ M₂ f₁ f₂ dec := by
  classical
  have hswap_pmf : ∀ (a : α) (b : β), (P.map Prod.swap).pmf (b, a) = P.pmf (a, b) := by
    intro a b
    unfold ProbDist.map
    dsimp only
    rw [Finset.sum_eq_single (a, b)]
    · simp
    · intro ⟨a', b'⟩ _ hne
      have : (b', a') ≠ (b, a) := fun h => hne (by
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        exact Prod.ext h2 h1)
      simp [Prod.swap, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold slepianWolfError
  refine Fintype.sum_equiv (Equiv.prodComm (Fin n → β) (Fin n → α)) _ _ fun ⟨y, x⟩ => ?_
  have hpmf : (jointIidDist (P.map Prod.swap) n).pmf (y, x) = (jointIidDist P n).pmf (x, y) := by
    unfold jointIidDist; dsimp only
    exact Finset.prod_congr rfl fun i _ => hswap_pmf (x i) (y i)
  have hiff : (dec (f₁ x) (f₂ y)).swap ≠ (y, x) ↔ dec (f₁ x) (f₂ y) ≠ (x, y) := by
    constructor <;> intro h heq <;> apply h
    · rw [heq]; rfl
    · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, hiff, hpmf]
  by_cases h : dec (f₁ x) (f₂ y) = (x, y) <;> simp [h]

private lemma slepianWolf_converse_fst (P : ProbDist (α × β)) {n M₁ M₂ : ℕ}
    (hn : 0 < n) (hM₁ : 0 < M₁)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (dec : Fin M₁ → Fin M₂ → (Fin n → α) × (Fin n → β)) :
    let pe := slepianWolfError P n M₁ M₂ f₁ f₂ dec
    condEntropy P ≤ log2 (M₁ : ℝ) / (n : ℝ) + 1 / (n : ℝ) + pe * log2 (Fintype.card α : ℝ) := by
  classical
  have hne : Nonempty (α × β) := nonempty_of_probDist P
  have : Nonempty α := ⟨hne.some.1⟩
  have : Nonempty (Fin n → α) := ⟨fun _ => Classical.arbitrary α⟩
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  dsimp only
  let Q := jointIidDist P n
  let R₁ := Q.map (fun xy => (xy.1, (f₁ xy.1, xy.2)))
  let g₁ : Fin M₁ × (Fin n → β) → Fin n → α := fun my => (dec my.1 (f₂ my.2)).1
  have hfano := fano_inequality_card R₁ g₁
  have hpe1_le : estErrorProb R₁ g₁ ≤ slepianWolfError P n M₁ M₂ f₁ f₂ dec := by
    rw [estErrorProb_map_pair]
    unfold slepianWolfError
    refine Finset.sum_le_sum fun xy _ => ?_
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h1; dsimp only [g₁]; rw [not_not.mp h2]
    · exact Q.nonneg xy
    · exact le_rfl
  have hbin : binaryEntropy (estErrorProb R₁ g₁) ≤ 1 :=
    InfoTheory.Known.binaryEntropy_le_one (estErrorProb_nonneg R₁ g₁) (estErrorProb_le_one R₁ g₁)
  have hlog_card : log2 (Fintype.card (Fin n → α) : ℝ) = (n : ℝ) * log2 (Fintype.card α : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, log2_pow_nat]
  have hlog_nonneg : 0 ≤ log2 (Fintype.card α : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos (α := α)
    have := log2_mono_le zero_lt_one h1
    simpa [log2] using this
  have hinj : Function.Injective (fun xy : (Fin n → α) × (Fin n → β) => (xy.1, (f₁ xy.1, xy.2))) := by
    intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2
  have hHR1 : shannonEntropy R₁ = (n : ℝ) * shannonEntropy P := by
    rw [shannonEntropy_map_injective Q hinj, shannonEntropy_jointIidDist]
  have hR1_snd : R₁.snd = Q.map (fun xy => (f₁ xy.1, xy.2)) := by
    rw [← probDist_map_snd, map_comp_eq]; rfl
  have hR1_snd_fst : R₁.snd.fst = Q.map (fun xy => f₁ xy.1) := by
    rw [hR1_snd, ← probDist_map_fst, map_comp_eq]; rfl
  have hR1_snd_snd : R₁.snd.snd = iidDist P.snd n := by
    rw [hR1_snd, ← probDist_map_snd, map_comp_eq]
    exact (probDist_map_snd Q).trans (jointIidDist_snd P n)
  have hH_snd : shannonEntropy R₁.snd ≤ log2 (M₁ : ℝ) + (n : ℝ) * shannonEntropy P.snd := by
    have hsub := shannonEntropy_subadd R₁.snd
    have hM1_le : shannonEntropy R₁.snd.fst ≤ log2 (M₁ : ℝ) := by
      have h := shannonEntropy_le_log2_card R₁.snd.fst
      simpa [Fintype.card_fin] using h
    rw [hR1_snd_snd, shannonEntropy_iidDist] at hsub
    linarith
  have hce : (n : ℝ) * condEntropy P - log2 (M₁ : ℝ) ≤ condEntropy R₁ := by
    unfold condEntropy
    rw [hHR1]
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul_pe : estErrorProb R₁ g₁ * ((n : ℝ) * log2 (Fintype.card α : ℝ)) ≤
      slepianWolfError P n M₁ M₂ f₁ f₂ dec * ((n : ℝ) * log2 (Fintype.card α : ℝ)) :=
    mul_le_mul_of_nonneg_right hpe1_le (by positivity)
  rw [hlog_card] at hfano
  have hmain : (n : ℝ) * condEntropy P ≤
      log2 (M₁ : ℝ) + 1 + slepianWolfError P n M₁ M₂ f₁ f₂ dec * ((n : ℝ) * log2 (Fintype.card α : ℝ)) := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
  have hlhs : (n : ℝ) * condEntropy P / (n : ℝ) = condEntropy P :=
    mul_div_cancel_left₀ _ (ne_of_gt hn_pos)
  have hrhs : (log2 (M₁ : ℝ) + 1 +
        slepianWolfError P n M₁ M₂ f₁ f₂ dec * ((n : ℝ) * log2 (Fintype.card α : ℝ))) / (n : ℝ) =
      log2 (M₁ : ℝ) / (n : ℝ) + 1 / (n : ℝ) +
        slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card α : ℝ) := by
    field_simp [ne_of_gt hn_pos]
  linarith

/-- **Finite-Blocklength Slepian–Wolf Converse Inequalities** (Cover & Thomas §15.4):
    for any `(n, M₁, M₂)` code `(f₁, f₂, dec)` with error `P_e`,
    - `H(X | Y) ≤ log₂ M₁ / n + 1 / n + P_e log₂ |α|`
    - `H(Y | X) ≤ log₂ M₂ / n + 1 / n + P_e log₂ |β|`
    - `H(X, Y) ≤ (log₂ M₁ + log₂ M₂) / n + 1 / n + P_e log₂ |α × β|`. -/
theorem slepianWolf_converse_bounds (P : ProbDist (α × β)) {n M₁ M₂ : ℕ}
    (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (dec : Fin M₁ → Fin M₂ → (Fin n → α) × (Fin n → β)) :
    let pe := slepianWolfError P n M₁ M₂ f₁ f₂ dec
    condEntropy P ≤ log2 (M₁ : ℝ) / (n : ℝ) + 1 / (n : ℝ) + pe * log2 (Fintype.card α : ℝ) ∧
    condEntropy (P.map Prod.swap) ≤
      log2 (M₂ : ℝ) / (n : ℝ) + 1 / (n : ℝ) + pe * log2 (Fintype.card β : ℝ) ∧
    shannonEntropy P ≤
      (log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) / (n : ℝ) + 1 / (n : ℝ) +
        pe * log2 (Fintype.card (α × β) : ℝ) := by
  refine ⟨slepianWolf_converse_fst P hn hM₁ f₁ f₂ dec, ?_, ?_⟩
  · have h2 := slepianWolf_converse_fst (P.map Prod.swap) hn hM₂ f₂ f₁
      (fun m₂ m₁ => (dec m₁ m₂).swap)
    dsimp only at h2 ⊢
    rw [slepianWolfError_swap] at h2
    exact h2
  · classical
    have hne : Nonempty (α × β) := nonempty_of_probDist P
    have : Nonempty α := ⟨hne.some.1⟩
    have : Nonempty β := ⟨hne.some.2⟩
    have : Nonempty ((Fin n → α) × (Fin n → β)) :=
      ⟨(fun _ => Classical.arbitrary α, fun _ => Classical.arbitrary β)⟩
    have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, hM₁⟩, ⟨0, hM₂⟩)⟩
    let Q := jointIidDist P n
    let R := Q.map (fun xy => (xy, (f₁ xy.1, f₂ xy.2)))
    let g : Fin M₁ × Fin M₂ → (Fin n → α) × (Fin n → β) := fun m => dec m.1 m.2
    have hfano := fano_inequality_card R g
    have hpe_eq : estErrorProb R g = slepianWolfError P n M₁ M₂ f₁ f₂ dec := by
      rw [estErrorProb_map_pair]
      unfold slepianWolfError
      exact Finset.sum_congr rfl fun xy _ => by
        by_cases h : dec (f₁ xy.1) (f₂ xy.2) = xy <;> simp [g, h, Q, jointIidDist]
    have hbin : binaryEntropy (estErrorProb R g) ≤ 1 :=
      InfoTheory.Known.binaryEntropy_le_one (estErrorProb_nonneg R g) (estErrorProb_le_one R g)
    have hcard_eq : Fintype.card ((Fin n → α) × (Fin n → β)) = (Fintype.card (α × β)) ^ n := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_prod, mul_pow]
    have hlog_card : log2 (Fintype.card ((Fin n → α) × (Fin n → β)) : ℝ) =
        (n : ℝ) * log2 (Fintype.card (α × β) : ℝ) := by
      rw [hcard_eq, Nat.cast_pow, log2_pow_nat]
    have hinj : Function.Injective (fun xy : (Fin n → α) × (Fin n → β) => (xy, (f₁ xy.1, f₂ xy.2))) :=
      fun _ _ h => (Prod.mk.inj h).1
    have hHR : shannonEntropy R = (n : ℝ) * shannonEntropy P := by
      rw [shannonEntropy_map_injective Q hinj, shannonEntropy_jointIidDist]
    have hH_snd : shannonEntropy R.snd ≤ log2 (M₁ : ℝ) + log2 (M₂ : ℝ) := by
      have h := shannonEntropy_le_log2_card R.snd
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul,
          log2_mul_pos (Nat.cast_pos.mpr hM₁) (Nat.cast_pos.mpr hM₂)] at h
      exact h
    have hce : (n : ℝ) * shannonEntropy P - (log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) ≤ condEntropy R := by
      unfold condEntropy; rw [hHR]; linarith
    rw [hpe_eq, hlog_card] at hfano
    rw [hpe_eq] at hbin
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hmain : (n : ℝ) * shannonEntropy P ≤
        (log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) + 1 +
          slepianWolfError P n M₁ M₂ f₁ f₂ dec * ((n : ℝ) * log2 (Fintype.card (α × β) : ℝ)) := by
      linarith
    have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
    have hlhs : (n : ℝ) * shannonEntropy P / (n : ℝ) = shannonEntropy P :=
      mul_div_cancel_left₀ _ (ne_of_gt hn_pos)
    have hrhs : ((log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) + 1 +
          slepianWolfError P n M₁ M₂ f₁ f₂ dec * ((n : ℝ) * log2 (Fintype.card (α × β) : ℝ))) /
            (n : ℝ) =
        (log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) / (n : ℝ) + 1 / (n : ℝ) +
          slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card (α × β) : ℝ) := by
      field_simp [ne_of_gt hn_pos]
    linarith

/-- **Slepian–Wolf Theorem — Converse** (Cover & Thomas, Theorem 15.4.1):
    every operationally achievable rate pair `(R₁, R₂)` lies in `slepianWolfSingleLetter P`. -/
theorem slepian_wolf_converse (P : ProbDist (α × β)) {R₁ R₂ : ℝ}
    (h : IsSlepianWolfAchievable P R₁ R₂) :
    (R₁, R₂) ∈ slepianWolfSingleLetter P := by
  have hne : Nonempty (α × β) := nonempty_of_probDist P
  have : Nonempty α := ⟨hne.some.1⟩
  have : Nonempty β := ⟨hne.some.2⟩
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · -- `condEntropy P ≤ R₁`
    by_contra hlt
    push Not at hlt
    let Δ : ℝ := condEntropy P - R₁
    have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
    let L : ℝ := log2 (Fintype.card α : ℝ) + 1
    have hL : 0 < L := by
      have h1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos (α := α)
      have hlog : 0 ≤ log2 (Fintype.card α : ℝ) := by
        simpa [log2] using log2_mono_le zero_lt_one h1
      dsimp only [L]; linarith
    obtain ⟨N₁, hN₁⟩ := h.2.2 (Δ / (3 * L)) (by positivity)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (3 / Δ)
    let n := max (max N₁ N₂) 1
    have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    obtain ⟨f₁, f₂, dec, herr⟩ := hN₁ n (le_trans (le_max_left N₁ N₂) (le_max_left _ 1))
    let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hb := (slepianWolf_converse_bounds P hn hM₁ hM₂ f₁ f₂ dec).1
    have hlogM₁ : log2 (M₁ : ℝ) / (n : ℝ) ≤ R₁ := by
      have hle : (M₁ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) := max_one_floor_two_rpow_le n h.1
      have hlog := log2_mono_le (Nat.cast_pos.mpr hM₁) hle
      rw [log2_two_rpow_eq] at hlog
      exact (div_le_iff₀ hn_r).mpr (by linarith)
    have h1n : 1 / (n : ℝ) < Δ / 3 := by
      have hn_gt : 3 / Δ < (n : ℝ) :=
        lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
      rw [div_lt_iff₀ hn_r]
      have := (div_lt_iff₀ hΔ).mp hn_gt
      linarith
    have hpe_term : slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card α : ℝ) ≤ Δ / 3 := by
      have h1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos (α := α)
      have hlog0 : 0 ≤ log2 (Fintype.card α : ℝ) := by
        simpa [log2] using log2_mono_le zero_lt_one h1
      have hpe0 : 0 ≤ slepianWolfError P n M₁ M₂ f₁ f₂ dec := by
        classical
        unfold slepianWolfError
        exact Finset.sum_nonneg fun xy _ => by split_ifs; exact (jointIidDist P n).nonneg xy; exact le_rfl
      calc slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card α : ℝ)
        _ ≤ (Δ / (3 * L)) * L := mul_le_mul herr (by dsimp only [L]; linarith) hlog0 (by positivity)
        _ = Δ / 3 := by field_simp [ne_of_gt hL]
    dsimp only [Δ] at h1n hpe_term
    linarith
  · -- `condEntropy (P.map Prod.swap) ≤ R₂`
    by_contra hlt
    push Not at hlt
    let Δ : ℝ := condEntropy (P.map Prod.swap) - R₂
    have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
    let L : ℝ := log2 (Fintype.card β : ℝ) + 1
    have hL : 0 < L := by
      have h1 : (1 : ℝ) ≤ (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos (α := β)
      have hlog : 0 ≤ log2 (Fintype.card β : ℝ) := by
        simpa [log2] using log2_mono_le zero_lt_one h1
      dsimp only [L]; linarith
    obtain ⟨N₁, hN₁⟩ := h.2.2 (Δ / (3 * L)) (by positivity)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (3 / Δ)
    let n := max (max N₁ N₂) 1
    have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    obtain ⟨f₁, f₂, dec, herr⟩ := hN₁ n (le_trans (le_max_left N₁ N₂) (le_max_left _ 1))
    let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hb := (slepianWolf_converse_bounds P hn hM₁ hM₂ f₁ f₂ dec).2.1
    have hlogM₂ : log2 (M₂ : ℝ) / (n : ℝ) ≤ R₂ := by
      have hle : (M₂ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) := max_one_floor_two_rpow_le n h.2.1
      have hlog := log2_mono_le (Nat.cast_pos.mpr hM₂) hle
      rw [log2_two_rpow_eq] at hlog
      exact (div_le_iff₀ hn_r).mpr (by linarith)
    have h1n : 1 / (n : ℝ) < Δ / 3 := by
      have hn_gt : 3 / Δ < (n : ℝ) :=
        lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
      rw [div_lt_iff₀ hn_r]
      have := (div_lt_iff₀ hΔ).mp hn_gt
      linarith
    have hpe_term : slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card β : ℝ) ≤ Δ / 3 := by
      have h1 : (1 : ℝ) ≤ (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos (α := β)
      have hlog0 : 0 ≤ log2 (Fintype.card β : ℝ) := by
        simpa [log2] using log2_mono_le zero_lt_one h1
      calc slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card β : ℝ)
        _ ≤ (Δ / (3 * L)) * L := mul_le_mul herr (by dsimp only [L]; linarith) hlog0 (by positivity)
        _ = Δ / 3 := by field_simp [ne_of_gt hL]
    dsimp only [Δ] at h1n hpe_term
    linarith
  · -- `shannonEntropy P ≤ R₁ + R₂`
    by_contra hlt
    push Not at hlt
    let Δ : ℝ := shannonEntropy P - (R₁ + R₂)
    have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
    let L : ℝ := log2 (Fintype.card (α × β) : ℝ) + 1
    have hL : 0 < L := by
      have h1 : (1 : ℝ) ≤ (Fintype.card (α × β) : ℝ) := by
        exact_mod_cast Fintype.card_pos (α := α × β)
      have hlog : 0 ≤ log2 (Fintype.card (α × β) : ℝ) := by
        simpa [log2] using log2_mono_le zero_lt_one h1
      dsimp only [L]; linarith
    obtain ⟨N₁, hN₁⟩ := h.2.2 (Δ / (3 * L)) (by positivity)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (3 / Δ)
    let n := max (max N₁ N₂) 1
    have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    obtain ⟨f₁, f₂, dec, herr⟩ := hN₁ n (le_trans (le_max_left N₁ N₂) (le_max_left _ 1))
    let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hb := (slepianWolf_converse_bounds P hn hM₁ hM₂ f₁ f₂ dec).2.2
    have hlogM₁ : log2 (M₁ : ℝ) ≤ (n : ℝ) * R₁ := by
      have hle : (M₁ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) := max_one_floor_two_rpow_le n h.1
      simpa [log2_two_rpow_eq] using log2_mono_le (Nat.cast_pos.mpr hM₁) hle
    have hlogM₂ : log2 (M₂ : ℝ) ≤ (n : ℝ) * R₂ := by
      have hle : (M₂ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) := max_one_floor_two_rpow_le n h.2.1
      simpa [log2_two_rpow_eq] using log2_mono_le (Nat.cast_pos.mpr hM₂) hle
    have hrate : (log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) / (n : ℝ) ≤ R₁ + R₂ :=
      (div_le_iff₀ hn_r).mpr (by linarith)
    have h1n : 1 / (n : ℝ) < Δ / 3 := by
      have hn_gt : 3 / Δ < (n : ℝ) :=
        lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
      rw [div_lt_iff₀ hn_r]
      have := (div_lt_iff₀ hΔ).mp hn_gt
      linarith
    have hpe_term :
        slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card (α × β) : ℝ) ≤ Δ / 3 := by
      have h1 : (1 : ℝ) ≤ (Fintype.card (α × β) : ℝ) := by
        exact_mod_cast Fintype.card_pos (α := α × β)
      have hlog0 : 0 ≤ log2 (Fintype.card (α × β) : ℝ) := by
        simpa [log2] using log2_mono_le zero_lt_one h1
      calc slepianWolfError P n M₁ M₂ f₁ f₂ dec * log2 (Fintype.card (α × β) : ℝ)
        _ ≤ (Δ / (3 * L)) * L := mul_le_mul herr (by dsimp only [L]; linarith) hlog0 (by positivity)
        _ = Δ / 3 := by field_simp [ne_of_gt hL]
    dsimp only [Δ] at h1n hpe_term
    linarith

/-! #### Slepian–Wolf Random-Binning Achievability -/

/-- **Unique Joint-Typicality Slepian–Wolf Decoder** (Cover & Thomas §15.4):
    given bin indices `(m₁, m₂)` and binning maps `(f₁, f₂)`, outputs the unique jointly
    typical pair `(x, y) ∈ A_ε^(n)(P)` consistent with `f₁ x = m₁` and `f₂ y = m₂`, if one
    exists, and an arbitrary default pair otherwise. -/
noncomputable def slepianWolfDec (P : ProbDist (α × β)) (n M₁ M₂ : ℕ) (ε : ℝ)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (m₁ : Fin M₁) (m₂ : Fin M₂) : (Fin n → α) × (Fin n → β) := by
  classical
  have hne : Nonempty (α × β) := nonempty_of_probDist P
  exact if h : ∃! xy : (Fin n → α) × (Fin n → β),
      f₁ xy.1 = m₁ ∧ f₂ xy.2 = m₂ ∧ xy ∈ jointTypicalSet P n ε then
    Classical.choose h
  else
    (fun _ => hne.some.1, fun _ => hne.some.2)

private lemma slepianWolfDec_eq_of_unique (P : ProbDist (α × β)) (n M₁ M₂ : ℕ) (ε : ℝ)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (x : Fin n → α) (y : Fin n → β)
    (hxy : (x, y) ∈ jointTypicalSet P n ε)
    (huniq : ∀ xy' : (Fin n → α) × (Fin n → β),
      xy' ≠ (x, y) → ¬ (f₁ xy'.1 = f₁ x ∧ f₂ xy'.2 = f₂ y ∧ xy' ∈ jointTypicalSet P n ε)) :
    slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ x) (f₂ y) = (x, y) := by
  classical
  have hex : ∃! xy' : (Fin n → α) × (Fin n → β),
      f₁ xy'.1 = f₁ x ∧ f₂ xy'.2 = f₂ y ∧ xy' ∈ jointTypicalSet P n ε := by
    refine ⟨(x, y), ⟨rfl, rfl, hxy⟩, fun xy' h => ?_⟩
    by_contra hne
    exact huniq xy' hne h
  simp only [slepianWolfDec, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  by_contra hne
  exact huniq (Classical.choose hex) hne hspec.1

private lemma slepianWolfDec_err_indicator_le [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n M₁ M₂ : ℕ) (ε : ℝ)
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
    (x : Fin n → α) (y : Fin n → β) :
    let A := jointTypicalSet P n ε
    (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ x) (f₂ y) ≠ (x, y) then (1 : ℝ) else 0) ≤
      (if (x, y) ∉ A then (1 : ℝ) else 0) +
      (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0) +
      (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0) +
      (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
        if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then (1 : ℝ) else 0) := by
  dsimp only
  let A := jointTypicalSet P n ε
  have hnn2 : (0 : ℝ) ≤ ∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then 1 else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hnn3 : (0 : ℝ) ≤ ∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then 1 else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hnn4 : (0 : ℝ) ≤ ∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
      if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then 1 else 0 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  split_ifs with herr hmem
  · have hex : ∃ xy' : (Fin n → α) × (Fin n → β),
        xy' ≠ (x, y) ∧ f₁ xy'.1 = f₁ x ∧ f₂ xy'.2 = f₂ y ∧ xy' ∈ A := by
      by_contra hnone
      push Not at hnone
      exact herr (slepianWolfDec_eq_of_unique P n M₁ M₂ ε f₁ f₂ x y hmem
        fun xy' hne ⟨hf1, hf2, hA⟩ => hnone xy' hne hf1 hf2 hA)
    obtain ⟨⟨x', y'⟩, hne, hf1, hf2, hA⟩ := hex
    by_cases hx : x' = x
    · subst hx
      have hy : y' ≠ y := fun hy => hne (by subst hy; rfl)
      have hle : (1 : ℝ) ≤ ∑ y'' ∈ Finset.univ.erase y,
          if f₂ y'' = f₂ y ∧ (x', y'') ∈ A then (1 : ℝ) else 0 := by
        calc (1 : ℝ) = (if f₂ y' = f₂ y ∧ (x', y') ∈ A then (1 : ℝ) else 0) := by simp [hf2, hA]
          _ ≤ _ := Finset.single_le_sum
              (f := fun y'' => if f₂ y'' = f₂ y ∧ (x', y'') ∈ A then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num)
              (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y'⟩)
      linarith
    · by_cases hy : y' = y
      · subst hy
        have hle : (1 : ℝ) ≤ ∑ x'' ∈ Finset.univ.erase x,
            if f₁ x'' = f₁ x ∧ (x'', y') ∈ A then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if f₁ x' = f₁ x ∧ (x', y') ∈ A then (1 : ℝ) else 0) := by simp [hf1, hA]
            _ ≤ _ := Finset.single_le_sum
                (f := fun x'' => if f₁ x'' = f₁ x ∧ (x'', y') ∈ A then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x'⟩)
        linarith
      · have hle_in : (1 : ℝ) ≤ ∑ y'' ∈ Finset.univ.erase y,
            if f₁ x' = f₁ x ∧ f₂ y'' = f₂ y ∧ (x', y'') ∈ A then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then (1 : ℝ) else 0) := by
                simp [hf1, hf2, hA]
            _ ≤ _ := Finset.single_le_sum
                (f := fun y'' => if f₁ x' = f₁ x ∧ f₂ y'' = f₂ y ∧ (x', y'') ∈ A then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y'⟩)
        have hle : (1 : ℝ) ≤ ∑ x'' ∈ Finset.univ.erase x, ∑ y'' ∈ Finset.univ.erase y,
            if f₁ x'' = f₁ x ∧ f₂ y'' = f₂ y ∧ (x'', y'') ∈ A then (1 : ℝ) else 0 :=
          le_trans hle_in (Finset.single_le_sum
            (f := fun x'' => ∑ y'' ∈ Finset.univ.erase y,
              if f₁ x'' = f₁ x ∧ f₂ y'' = f₂ y ∧ (x'', y'') ∈ A then (1 : ℝ) else 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x'⟩))
        linarith
  · linarith
  · linarith
  · linarith

/-- Conditional slice cardinality bound for jointly typical sequences:
    for every `y : Fin n → β`, `|{x : (x, y) ∈ A_ε^(n)}| ≤ 2^(n (H(X | Y) + 2ε))`. -/
private lemma jointTypicalSet_slice_fst_card_le [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ) (y : Fin n → β) :
    ((Finset.univ.filter fun x : Fin n → α => (x, y) ∈ jointTypicalSet P n ε).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) := by
  classical
  let S := Finset.univ.filter fun x : Fin n → α => (x, y) ∈ jointTypicalSet P n ε
  by_cases hy : y ∈ weakTypicalSet P.snd n ε
  · have hy_ub : (iidDist P.snd n).pmf y ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) := by
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy.2
    have hsum_le : ∑ x ∈ S, (jointIidDist P n).pmf (x, y) ≤ (iidDist P.snd n).pmf y := by
      calc ∑ x ∈ S, (jointIidDist P n).pmf (x, y)
        _ ≤ ∑ x : Fin n → α, (jointIidDist P n).pmf (x, y) :=
            Finset.sum_le_univ_sum_of_nonneg fun x => (jointIidDist P n).nonneg (x, y)
        _ = (jointIidDist P n).snd.pmf y := rfl
        _ = (iidDist P.snd n).pmf y := by rw [jointIidDist_snd]
    have hlow : (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤
        ∑ x ∈ S, (jointIidDist P n).pmf (x, y) := by
      calc (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε)))
        _ = ∑ _x ∈ S, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ S, (jointIidDist P n).pmf (x, y) := Finset.sum_le_sum fun x hx => by
            have hmem := (Finset.mem_filter.mp hx).2
            have hz := (mem_jointTypicalSet.mp hmem).2.2
            simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
            exact hz.1
    have hcomb : (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) := le_trans hlow (le_trans hsum_le hy_ub)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_right hcomb (le_of_lt hpos)
    have hlhs : (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) *
          (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) = (S.card : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero,
          mul_one]
    have hrhs : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) *
          (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) =
        (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; unfold condEntropy; ring
    change (S.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε))
    linarith
  · have hempty : S = ∅ := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hmem
      exact hy (mem_jointTypicalSet.mp hmem).2.1
    change (S.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)

/-- Conditional slice cardinality bound in the second coordinate:
    for every `x : Fin n → α`, `|{y : (x, y) ∈ A_ε^(n)}| ≤ 2^(n (H(Y | X) + 2ε))`. -/
private lemma jointTypicalSet_slice_snd_card_le [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    ((Finset.univ.filter fun y : Fin n → β => (x, y) ∈ jointTypicalSet P n ε).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) := by
  classical
  let S := Finset.univ.filter fun y : Fin n → β => (x, y) ∈ jointTypicalSet P n ε
  by_cases hx : x ∈ weakTypicalSet P.fst n ε
  · have hx_ub : (iidDist P.fst n).pmf x ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) := by
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.2
    have hsum_le : ∑ y ∈ S, (jointIidDist P n).pmf (x, y) ≤ (iidDist P.fst n).pmf x := by
      calc ∑ y ∈ S, (jointIidDist P n).pmf (x, y)
        _ ≤ ∑ y : Fin n → β, (jointIidDist P n).pmf (x, y) :=
            Finset.sum_le_univ_sum_of_nonneg fun y => (jointIidDist P n).nonneg (x, y)
        _ = (jointIidDist P n).fst.pmf x := rfl
        _ = (iidDist P.fst n).pmf x := by rw [jointIidDist_fst]
    have hlow : (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤
        ∑ y ∈ S, (jointIidDist P n).pmf (x, y) := by
      calc (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε)))
        _ = ∑ _y ∈ S, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ S, (jointIidDist P n).pmf (x, y) := Finset.sum_le_sum fun y hy => by
            have hmem := (Finset.mem_filter.mp hy).2
            have hz := (mem_jointTypicalSet.mp hmem).2.2
            simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
            exact hz.1
    have hcomb : (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) := le_trans hlow (le_trans hsum_le hx_ub)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_right hcomb (le_of_lt hpos)
    have hlhs : (S.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) *
          (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) = (S.card : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero,
          mul_one]
    have hrhs : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
          (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) =
        (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      unfold condEntropy
      rw [shannonEntropy_swap, snd_map_swap]
      ring
    change (S.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε))
    linarith
  · have hempty : S = ∅ := by
      ext y
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hmem
      exact hx (mem_jointTypicalSet.mp hmem).1
    change (S.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)

/-- Exact collision probability `1 / M` for a uniform random binning map `f : ι → Fin M`. -/
private lemma uniform_binning_collision_prob {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℕ} (hM : 0 < M) (u v : ι) (hne : v ≠ u) :
    letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    let U := ProbDist.uniform (α := Fin M)
    ∑ f : ι → Fin M, (∏ z : ι, U.pmf (f z)) * (if f v = f u then (1 : ℝ) else 0) =
      (1 : ℝ) / (M : ℝ) := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  dsimp only
  let U := ProbDist.uniform (α := Fin M)
  have hind : ∀ f : ι → Fin M,
      (if f v = f u then (1 : ℝ) else 0) =
        ∑ m : Fin M, (if f u = m then (1 : ℝ) else 0) * (if f v = m then (1 : ℝ) else 0) := by
    intro f
    rw [Finset.sum_eq_single (f u)]
    · by_cases h : f v = f u <;> simp [h]
    · intro m _ hne_m; simp [hne_m.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hind, Finset.mul_sum]
  rw [Finset.sum_comm]
  have heach : ∀ m : Fin M,
      ∑ f : ι → Fin M, (∏ z : ι, U.pmf (f z)) *
        ((if f u = m then (1 : ℝ) else 0) * (if f v = m then (1 : ℝ) else 0)) =
      ((1 : ℝ) / (M : ℝ)) * ((1 : ℝ) / (M : ℝ)) := by
    intro m
    rw [sum_pi_prod_mul_pair' U u v hne (fun a => if a = m then (1 : ℝ) else 0)
        (fun a => if a = m then (1 : ℝ) else 0)]
    have hsingle : ∑ a : Fin M, U.pmf a * (if a = m then (1 : ℝ) else 0) = (1 : ℝ) / (M : ℝ) := by
      rw [Finset.sum_eq_single m]
      · simp [U, ProbDist.uniform]
      · intro a _ hne_a; simp [hne_a]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsingle]
  rw [Finset.sum_congr rfl fun m _ => heach m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hMpos : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  field_simp [hMpos]

private lemma slepianWolf_binning_term2 [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (x : Fin n → α) (y : Fin n → β) :
    letI : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
    letI : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
    let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)
    let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z)
    let A := jointTypicalSet P n ε
    ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) / (M₁ : ℝ) := by
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  dsimp only
  let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)
  let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z)
  let A := jointTypicalSet P n ε
  have hw₂1 : ∑ f₂, w₂ f₂ = 1 := by
    dsimp only [w₂]; rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun _ _ => (ProbDist.uniform (α := Fin M₂)).sum_one
  have hM₁_pos : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr hM₁
  have hstep : ∀ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0) =
      ∑ x' ∈ Finset.univ.erase x,
        w₁ f₁ * (if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0) := fun f₁ => by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hw₂1, mul_one, Finset.mul_sum]
  change ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0) ≤ _
  rw [Finset.sum_congr rfl fun f₁ _ => hstep f₁, Finset.sum_comm]
  have heach : ∀ x' ∈ Finset.univ.erase x,
      ∑ f₁, w₁ f₁ * (if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0) =
        if (x', y) ∈ A then (1 : ℝ) / (M₁ : ℝ) else 0 := fun x' hx' => by
    by_cases hA : (x', y) ∈ A
    · simp only [hA, and_true, ↓reduceIte]
      exact uniform_binning_collision_prob hM₁ x x' (Finset.mem_erase.mp hx').1
    · simp [hA]
  rw [Finset.sum_congr rfl heach]
  calc ∑ x' ∈ Finset.univ.erase x, (if (x', y) ∈ A then (1 : ℝ) / (M₁ : ℝ) else 0)
    _ ≤ ∑ x' : Fin n → α, (if (x', y) ∈ A then (1 : ℝ) / (M₁ : ℝ) else 0) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> positivity
    _ = ((Finset.univ.filter fun x' : Fin n → α => (x', y) ∈ A).card : ℝ) / (M₁ : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) / (M₁ : ℝ) :=
        div_le_div_of_nonneg_right (jointTypicalSet_slice_fst_card_le P n ε y) (le_of_lt hM₁_pos)

private lemma slepianWolf_binning_term3 [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (x : Fin n → α) (y : Fin n → β) :
    letI : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
    letI : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
    let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)
    let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z)
    let A := jointTypicalSet P n ε
    ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) / (M₂ : ℝ) := by
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  dsimp only
  let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)
  let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z)
  let A := jointTypicalSet P n ε
  have hw₁1 : ∑ f₁, w₁ f₁ = 1 := by
    dsimp only [w₁]; rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun _ _ => (ProbDist.uniform (α := Fin M₁)).sum_one
  have hM₂_pos : (0 : ℝ) < (M₂ : ℝ) := Nat.cast_pos.mpr hM₂
  change ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0) ≤ _
  rw [Finset.sum_comm]
  have hstep : ∀ f₂, ∑ f₁, (w₁ f₁ * w₂ f₂) *
        (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0) =
      ∑ y' ∈ Finset.univ.erase y,
        w₂ f₂ * (if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0) := fun f₂ => by
    rw [← Finset.sum_mul, ← Finset.sum_mul, hw₁1, one_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun f₂ _ => hstep f₂, Finset.sum_comm]
  have heach : ∀ y' ∈ Finset.univ.erase y,
      ∑ f₂, w₂ f₂ * (if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0) =
        if (x, y') ∈ A then (1 : ℝ) / (M₂ : ℝ) else 0 := fun y' hy' => by
    by_cases hA : (x, y') ∈ A
    · simp only [hA, and_true, ↓reduceIte]
      exact uniform_binning_collision_prob hM₂ y y' (Finset.mem_erase.mp hy').1
    · simp [hA]
  rw [Finset.sum_congr rfl heach]
  calc ∑ y' ∈ Finset.univ.erase y, (if (x, y') ∈ A then (1 : ℝ) / (M₂ : ℝ) else 0)
    _ ≤ ∑ y' : Fin n → β, (if (x, y') ∈ A then (1 : ℝ) / (M₂ : ℝ) else 0) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> positivity
    _ = ((Finset.univ.filter fun y' : Fin n → β => (x, y') ∈ A).card : ℝ) / (M₂ : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) / (M₂ : ℝ) :=
        div_le_div_of_nonneg_right (jointTypicalSet_slice_snd_card_le P n ε x) (le_of_lt hM₂_pos)

private lemma sum_prod_factor_double {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (s₁ : Finset κ₁) (s₂ : Finset κ₂)
    (a : ι₁ → κ₁ → ℝ) (b : ι₂ → κ₂ → ℝ) (c : κ₁ → κ₂ → ℝ) :
    ∑ f₁ : ι₁, ∑ f₂ : ι₂, ∑ x' ∈ s₁, ∑ y' ∈ s₂, a f₁ x' * b f₂ y' * c x' y' =
      ∑ x' ∈ s₁, ∑ y' ∈ s₂, (∑ f₁ : ι₁, a f₁ x') * (∑ f₂ : ι₂, b f₂ y') * c x' y' := by
  have hinner : ∀ f₁ : ι₁,
      ∑ f₂ : ι₂, ∑ x' ∈ s₁, ∑ y' ∈ s₂, a f₁ x' * b f₂ y' * c x' y' =
        ∑ x' ∈ s₁, ∑ y' ∈ s₂, a f₁ x' * (∑ f₂ : ι₂, b f₂ y') * c x' y' := fun f₁ => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun f₁ _ => hinner f₁, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

private lemma ite_and3_mul_eq (a b : ℝ) (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    (a * b) * (if p ∧ q ∧ r then (1 : ℝ) else 0) =
      (a * (if p then (1 : ℝ) else 0)) * (b * (if q then (1 : ℝ) else 0)) *
        (if r then (1 : ℝ) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

private lemma sum_erase_erase_mem_le {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (S : Finset (ι₁ × ι₂)) (x : ι₁) (y : ι₂)
    (c : ℝ) (hc : 0 ≤ c) :
    ∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y, (if (x', y') ∈ S then c else 0) ≤
      (S.card : ℝ) * c := by
  calc ∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y, (if (x', y') ∈ S then c else 0)
    _ ≤ ∑ x' ∈ Finset.univ.erase x, ∑ y' : ι₂, (if (x', y') ∈ S then c else 0) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> linarith
    _ ≤ ∑ x' : ι₁, ∑ y' : ι₂, (if (x', y') ∈ S then c else 0) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> linarith
    _ = ∑ xy' : ι₁ × ι₂, (if xy' ∈ S then c else 0) :=
        (Fintype.sum_prod_type (fun xy' : ι₁ × ι₂ => if xy' ∈ S then c else 0)).symm
    _ = (S.card : ℝ) * c := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul]

private lemma slepianWolf_binning_term4_aux [DecidableEq α] [DecidableEq β]
    {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (S : Finset ((Fin n → α) × (Fin n → β)))
    (x : Fin n → α) (y : Fin n → β) :
    letI : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
    letI : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
    ∑ f₁ : (Fin n → α) → Fin M₁, ∑ f₂ : (Fin n → β) → Fin M₂,
        ((∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)) *
         (∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z))) *
        (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
          if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ S then (1 : ℝ) else 0) ≤
      (S.card : ℝ) / ((M₁ : ℝ) * (M₂ : ℝ)) := by
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)
  let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z)
  have hpush : ∀ f₁ f₂,
      (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
          if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ S then (1 : ℝ) else 0) =
      ∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
        (w₁ f₁ * (if f₁ x' = f₁ x then (1 : ℝ) else 0)) *
        (w₂ f₂ * (if f₂ y' = f₂ y then (1 : ℝ) else 0)) *
        (if (x', y') ∈ S then (1 : ℝ) else 0) := fun f₁ f₂ => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => ite_and3_mul_eq (w₁ f₁) (w₂ f₂) _ _ _
  have hrew : ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
          if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ S then (1 : ℝ) else 0) =
      ∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
        if (x', y') ∈ S then (1 : ℝ) / ((M₁ : ℝ) * (M₂ : ℝ)) else 0 := by
    trans (∑ f₁, ∑ f₂, ∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
        (w₁ f₁ * (if f₁ x' = f₁ x then (1 : ℝ) else 0)) *
        (w₂ f₂ * (if f₂ y' = f₂ y then (1 : ℝ) else 0)) *
        (if (x', y') ∈ S then (1 : ℝ) else 0))
    · exact Finset.sum_congr rfl fun f₁ _ => Finset.sum_congr rfl fun f₂ _ => hpush f₁ f₂
    rw [sum_prod_factor_double (Finset.univ.erase x) (Finset.univ.erase y)
          (fun f₁ x' => w₁ f₁ * (if f₁ x' = f₁ x then (1 : ℝ) else 0))
          (fun f₂ y' => w₂ f₂ * (if f₂ y' = f₂ y then (1 : ℝ) else 0))
          (fun x' y' => if (x', y') ∈ S then (1 : ℝ) else 0)]
    refine Finset.sum_congr rfl fun x' hx' => Finset.sum_congr rfl fun y' hy' => ?_
    have hc1 : (∑ f₁, w₁ f₁ * (if f₁ x' = f₁ x then (1 : ℝ) else 0)) = (1 : ℝ) / (M₁ : ℝ) :=
      uniform_binning_collision_prob hM₁ x x' (Finset.mem_erase.mp hx').1
    have hc2 : (∑ f₂, w₂ f₂ * (if f₂ y' = f₂ y then (1 : ℝ) else 0)) = (1 : ℝ) / (M₂ : ℝ) :=
      uniform_binning_collision_prob hM₂ y y' (Finset.mem_erase.mp hy').1
    rw [hc1, hc2]
    split_ifs <;> ring
  change ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
          if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ S then (1 : ℝ) else 0) ≤ _
  rw [hrew]
  exact (sum_erase_erase_mem_le S x y ((1 : ℝ) / ((M₁ : ℝ) * (M₂ : ℝ))) (by positivity)).trans_eq
    (mul_one_div _ _)

private lemma slepianWolf_binning_term4 [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (x : Fin n → α) (y : Fin n → β) :
    letI : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
    letI : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
    let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ z, (ProbDist.uniform (α := Fin M₁)).pmf (f₁ z)
    let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ z, (ProbDist.uniform (α := Fin M₂)).pmf (f₂ z)
    let A := jointTypicalSet P n ε
    ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
          if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) / ((M₁ : ℝ) * (M₂ : ℝ)) :=
  (slepianWolf_binning_term4_aux hM₁ hM₂ (jointTypicalSet P n ε) x y).trans
    (div_le_div_of_nonneg_right (jointTypicalSet_card_le P n ε) (by positivity))

/-- **Random-Binning Existence Bound for Slepian–Wolf** (Cover & Thomas, §15.4):
    for any correlated source `P`, blocklength `n`, bin counts `M₁, M₂ > 0`, and `ε : ℝ`,
    there exist deterministic binning encoders `(f₁, f₂)` and decoder `dec` satisfying
    `slepianWolfError P n M₁ M₂ f₁ f₂ dec ≤ (1 - P^n(A_ε^(n))) + 2^(n(H(X|Y)+2ε))/M₁ + 2^(n(H(Y|X)+2ε))/M₂ + 2^(n(H(X,Y)+ε))/(M₁ M₂)`. -/
theorem slepianWolf_random_binning_bound (P : ProbDist (α × β)) (n M₁ M₂ : ℕ)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ) :
    ∃ (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂)
      (dec : Fin M₁ → Fin M₂ → (Fin n → α) × (Fin n → β)),
      slepianWolfError P n M₁ M₂ f₁ f₂ dec ≤
        (1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy) +
        (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) / (M₁ : ℝ) +
        (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) / (M₂ : ℝ) +
        (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) / ((M₁ : ℝ) * (M₂ : ℝ)) := by
  classical
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  let U₁ := ProbDist.uniform (α := Fin M₁)
  let U₂ := ProbDist.uniform (α := Fin M₂)
  let w₁ : ((Fin n → α) → Fin M₁) → ℝ := fun f₁ => ∏ x : Fin n → α, U₁.pmf (f₁ x)
  let w₂ : ((Fin n → β) → Fin M₂) → ℝ := fun f₂ => ∏ y : Fin n → β, U₂.pmf (f₂ y)
  have hw₁0 : ∀ f₁, 0 ≤ w₁ f₁ := fun f₁ => Finset.prod_nonneg fun _ _ => U₁.nonneg _
  have hw₂0 : ∀ f₂, 0 ≤ w₂ f₂ := fun f₂ => Finset.prod_nonneg fun _ _ => U₂.nonneg _
  have hw₁1 : ∑ f₁, w₁ f₁ = 1 := by
    dsimp only [w₁]; rw [← Fintype.prod_sum]; exact Finset.prod_eq_one fun _ _ => U₁.sum_one
  have hw₂1 : ∑ f₂, w₂ f₂ = 1 := by
    dsimp only [w₂]; rw [← Fintype.prod_sum]; exact Finset.prod_eq_one fun _ _ => U₂.sum_one
  let A := jointTypicalSet P n ε
  let Q := jointIidDist P n
  let C : ℝ :=
    (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) / (M₁ : ℝ) +
    (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) / (M₂ : ℝ) +
    (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) / ((M₁ : ℝ) * (M₂ : ℝ))
  let B : ℝ := (1 - ∑ xy ∈ A, Q.pmf xy) + C
  have hxy_exp : ∀ xy : (Fin n → α) × (Fin n → β),
      ∑ f₁ : (Fin n → α) → Fin M₁, ∑ f₂ : (Fin n → β) → Fin M₂,
        (w₁ f₁ * w₂ f₂) *
          (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ xy.1) (f₂ xy.2) ≠ xy then (1 : ℝ) else 0) ≤
      (if xy ∉ A then (1 : ℝ) else 0) + C := by
    intro ⟨x, y⟩
    have hpt : ∀ f₁ f₂,
        (w₁ f₁ * w₂ f₂) *
          (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ x) (f₂ y) ≠ (x, y) then (1 : ℝ) else 0) ≤
        (w₁ f₁ * w₂ f₂) * (if (x, y) ∉ A then (1 : ℝ) else 0) +
        (w₁ f₁ * w₂ f₂) * (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then 1 else 0) +
        (w₁ f₁ * w₂ f₂) * (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then 1 else 0) +
        (w₁ f₁ * w₂ f₂) * (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
          if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then 1 else 0) := by
      intro f₁ f₂
      have hind := slepianWolfDec_err_indicator_le P n M₁ M₂ ε f₁ f₂ x y
      dsimp only at hind
      have hmul := mul_le_mul_of_nonneg_left hind (mul_nonneg (hw₁0 f₁) (hw₂0 f₂))
      linarith
    have hsum_le :
        ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
          (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ x) (f₂ y) ≠ (x, y) then (1 : ℝ) else 0) ≤
        (∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) * (if (x, y) ∉ A then (1 : ℝ) else 0)) +
        (∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
          (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then (1 : ℝ) else 0)) +
        (∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
          (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then (1 : ℝ) else 0)) +
        (∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
          (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
            if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then (1 : ℝ) else 0)) := by
      calc ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
            (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ x) (f₂ y) ≠ (x, y) then (1 : ℝ) else 0)
        _ ≤ ∑ f₁, ∑ f₂,
              (((w₁ f₁ * w₂ f₂) * (if (x, y) ∉ A then (1 : ℝ) else 0) +
                (w₁ f₁ * w₂ f₂) * (∑ x' ∈ Finset.univ.erase x, if f₁ x' = f₁ x ∧ (x', y) ∈ A then 1 else 0)) +
                (w₁ f₁ * w₂ f₂) * (∑ y' ∈ Finset.univ.erase y, if f₂ y' = f₂ y ∧ (x, y') ∈ A then 1 else 0) +
                (w₁ f₁ * w₂ f₂) * (∑ x' ∈ Finset.univ.erase x, ∑ y' ∈ Finset.univ.erase y,
                  if f₁ x' = f₁ x ∧ f₂ y' = f₂ y ∧ (x', y') ∈ A then 1 else 0)) :=
            Finset.sum_le_sum fun f₁ _ => Finset.sum_le_sum fun f₂ _ => hpt f₁ f₂
        _ = _ := by simp_rw [Finset.sum_add_distrib]
    have ht1 : ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) * (if (x, y) ∉ A then (1 : ℝ) else 0) =
        if (x, y) ∉ A then (1 : ℝ) else 0 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hw₂1, mul_one, hw₁1, one_mul]
    have ht2 := slepianWolf_binning_term2 P n M₁ M₂ hM₁ hM₂ ε x y
    have ht3 := slepianWolf_binning_term3 P n M₁ M₂ hM₁ hM₂ ε x y
    have ht4 := slepianWolf_binning_term4 P n M₁ M₂ hM₁ hM₂ ε x y
    dsimp only [C] at ht2 ht3 ht4 ⊢
    linarith
  let W : (((Fin n → α) → Fin M₁) × ((Fin n → β) → Fin M₂)) → ℝ := fun f => w₁ f.1 * w₂ f.2
  have hW0 : ∀ f, 0 ≤ W f := fun f => mul_nonneg (hw₁0 f.1) (hw₂0 f.2)
  have hW1 : ∑ f, W f = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [W, ← Finset.mul_sum, hw₂1, mul_one, hw₁1]
  have hexp_le : ∑ f : ((Fin n → α) → Fin M₁) × ((Fin n → β) → Fin M₂),
      W f * slepianWolfError P n M₁ M₂ f.1 f.2 (slepianWolfDec P n M₁ M₂ ε f.1 f.2) ≤ B := by
    rw [Fintype.sum_prod_type]
    have hswap : ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
          slepianWolfError P n M₁ M₂ f₁ f₂ (slepianWolfDec P n M₁ M₂ ε f₁ f₂) =
        ∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy *
          ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
            (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ xy.1) (f₂ xy.2) ≠ xy then (1 : ℝ) else 0) := by
      have h1 : ∀ f₁ f₂, (w₁ f₁ * w₂ f₂) *
            slepianWolfError P n M₁ M₂ f₁ f₂ (slepianWolfDec P n M₁ M₂ ε f₁ f₂) =
          ∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy *
            ((w₁ f₁ * w₂ f₂) *
              (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ xy.1) (f₂ xy.2) ≠ xy then (1 : ℝ) else 0)) := by
        intro f₁ f₂
        unfold slepianWolfError
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun xy _ => by
          by_cases h : slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ xy.1) (f₂ xy.2) = xy
          · simp [Q, h]
          · simp [Q, h]; ring
      rw [Finset.sum_congr rfl fun f₁ _ => Finset.sum_congr rfl fun f₂ _ => h1 f₁ f₂]
      trans (∑ f₁, ∑ xy : (Fin n → α) × (Fin n → β), ∑ f₂, Q.pmf xy *
          ((w₁ f₁ * w₂ f₂) *
            (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ xy.1) (f₂ xy.2) ≠ xy then (1 : ℝ) else 0)))
      · exact Finset.sum_congr rfl fun f₁ _ => Finset.sum_comm
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xy _ => ?_
        simp_rw [← Finset.mul_sum]
    change ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
        slepianWolfError P n M₁ M₂ f₁ f₂ (slepianWolfDec P n M₁ M₂ ε f₁ f₂) ≤ B
    rw [hswap]
    have hcomp : ∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy * (if xy ∉ A then (1 : ℝ) else 0) =
        1 - ∑ xy ∈ A, Q.pmf xy := by
      have hsplit : ∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy =
          (∑ xy : (Fin n → α) × (Fin n → β), if xy ∈ A then Q.pmf xy else 0) +
          (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ A then Q.pmf xy else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun xy _ => by by_cases h : xy ∈ A <;> simp [h]
      rw [Q.sum_one] at hsplit
      have hmem : (∑ xy : (Fin n → α) × (Fin n → β), if xy ∈ A then Q.pmf xy else 0) =
          ∑ xy ∈ A, Q.pmf xy := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      have hnot : (∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy * (if xy ∉ A then (1 : ℝ) else 0)) =
          ∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ A then Q.pmf xy else 0 :=
        Finset.sum_congr rfl fun xy _ => by split_ifs <;> ring
      linarith
    calc ∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy *
            ∑ f₁, ∑ f₂, (w₁ f₁ * w₂ f₂) *
              (if slepianWolfDec P n M₁ M₂ ε f₁ f₂ (f₁ xy.1) (f₂ xy.2) ≠ xy then (1 : ℝ) else 0)
      _ ≤ ∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy * ((if xy ∉ A then (1 : ℝ) else 0) + C) :=
          Finset.sum_le_sum fun xy _ =>
            mul_le_mul_of_nonneg_left (hxy_exp xy) (Q.nonneg xy)
      _ = (∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy * (if xy ∉ A then (1 : ℝ) else 0)) +
          (∑ xy : (Fin n → α) × (Fin n → β), Q.pmf xy * C) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
      _ = (1 - ∑ xy ∈ A, Q.pmf xy) + C := by
          rw [hcomp, ← Finset.sum_mul, Q.sum_one, one_mul]
      _ = B := rfl
  obtain ⟨⟨f₁, f₂⟩, hf⟩ := exists_le_of_weighted_sum_le' W
    (fun f => slepianWolfError P n M₁ M₂ f.1 f.2 (slepianWolfDec P n M₁ M₂ ε f.1 f.2))
    B hW0 hW1 hexp_le
  refine ⟨f₁, f₂, slepianWolfDec P n M₁ M₂ ε f₁ f₂, ?_⟩
  dsimp only [B, C, A, Q] at hf
  linarith

/-- **Slepian–Wolf Theorem — Achievability** (Cover & Thomas, Theorem 15.4.1; El Gamal–Kim Thm. 10.1):
    every rate pair `(R₁, R₂)` strictly inside `slepianWolfSingleLetter P` is operationally
    achievable via random binning and joint-typicality decoding. -/
theorem slepian_wolf_achievability (P : ProbDist (α × β)) {R₁ R₂ : ℝ}
    (h1 : condEntropy P < R₁)
    (h2 : condEntropy (P.map Prod.swap) < R₂)
    (h12 : shannonEntropy P < R₁ + R₂) :
    IsSlepianWolfAchievable P R₁ R₂ := by
  have hR₁0 : 0 ≤ R₁ := le_of_lt (lt_of_le_of_lt (condEntropy_nonneg P) h1)
  have hR₂0 : 0 ≤ R₂ := le_of_lt (lt_of_le_of_lt (condEntropy_nonneg (P.map Prod.swap)) h2)
  refine ⟨hR₁0, hR₂0, fun δ hδ => ?_⟩
  let ε : ℝ := min ((R₁ - condEntropy P) / 3)
    (min ((R₂ - condEntropy (P.map Prod.swap)) / 3) ((R₁ + R₂ - shannonEntropy P) / 2))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε1 : condEntropy P + 2 * ε ≤ R₁ - ε := by
    have : ε ≤ (R₁ - condEntropy P) / 3 := min_le_left _ _
    linarith
  have hε2 : condEntropy (P.map Prod.swap) + 2 * ε ≤ R₂ - ε := by
    have : ε ≤ (R₂ - condEntropy (P.map Prod.swap)) / 3 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hε12 : shannonEntropy P + ε ≤ R₁ + R₂ - ε := by
    have : ε ≤ (R₁ + R₂ - shannonEntropy P) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one P hε (show 0 < δ / 4 by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (1 / (δ / 16)) / ε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  obtain ⟨f₁, f₂, dec, hbound⟩ := slepianWolf_random_binning_bound P n M₁ M₂ hM₁ hM₂ ε
  refine ⟨f₁, f₂, dec, ?_⟩
  have ht1 : 1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy ≤ δ / 4 := by
    have hprob := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    linarith
  have htail : (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ / 16 :=
    two_rpow_neg_le_of_ge hε (by linarith)
      (le_trans hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn))
  have hM₁_lb : (2 : ℝ) ^ ((n : ℝ) * R₁) / 2 ≤ (M₁ : ℝ) := half_two_rpow_le_max_one_floor n hR₁0
  have hM₂_lb : (2 : ℝ) ^ ((n : ℝ) * R₂) / 2 ≤ (M₂ : ℝ) := half_two_rpow_le_max_one_floor n hR₂0
  have hM₁_pos : (0 : ℝ) < (M₁ : ℝ) := Nat.cast_pos.mpr hM₁
  have ht2 : (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) / (M₁ : ℝ) ≤ δ / 4 := by
    calc (2 : ℝ) ^ ((n : ℝ) * (condEntropy P + 2 * ε)) / (M₁ : ℝ)
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ - ε)) / ((2 : ℝ) ^ ((n : ℝ) * R₁) / 2) :=
          div_le_div₀ (by positivity)
            (Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (mul_le_mul_of_nonneg_left hε1 (Nat.cast_nonneg n)))
            (by positivity) hM₁_lb
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          rw [div_div_eq_mul_div, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              mul_right_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_comm _ (2 : ℝ)]
          congr 2; ring
      _ ≤ 2 * (δ / 16) := by linarith
      _ ≤ δ / 4 := by linarith
  have ht3 : (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) / (M₂ : ℝ) ≤ δ / 4 := by
    calc (2 : ℝ) ^ ((n : ℝ) * (condEntropy (P.map Prod.swap) + 2 * ε)) / (M₂ : ℝ)
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₂ - ε)) / ((2 : ℝ) ^ ((n : ℝ) * R₂) / 2) :=
          div_le_div₀ (by positivity)
            (Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (mul_le_mul_of_nonneg_left hε2 (Nat.cast_nonneg n)))
            (by positivity) hM₂_lb
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          rw [div_div_eq_mul_div, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              mul_right_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_comm _ (2 : ℝ)]
          congr 2; ring
      _ ≤ 2 * (δ / 16) := by linarith
      _ ≤ δ / 4 := by linarith
  have ht4 : (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) / ((M₁ : ℝ) * (M₂ : ℝ)) ≤ δ / 4 := by
    have hprod_lb : (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) / 4 ≤ (M₁ : ℝ) * (M₂ : ℝ) := by
      have hmul := mul_le_mul hM₁_lb hM₂_lb (by positivity) (le_of_lt hM₁_pos)
      have heq : ((2 : ℝ) ^ ((n : ℝ) * R₁) / 2) * ((2 : ℝ) ^ ((n : ℝ) * R₂) / 2) =
          (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) / 4 := by
        rw [div_mul_div_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        · congr 1; ring
        · norm_num
      linarith
    calc (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) / ((M₁ : ℝ) * (M₂ : ℝ))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂ - ε)) / ((2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) / 4) :=
          div_le_div₀ (by positivity)
            (Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (mul_le_mul_of_nonneg_left hε12 (Nat.cast_nonneg n)))
            (by positivity) hprod_lb
      _ = 4 * (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          rw [div_div_eq_mul_div, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
              mul_right_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_comm _ (4 : ℝ)]
          congr 2; ring
      _ ≤ 4 * (δ / 16) := by linarith
      _ = δ / 4 := by ring
  linarith

/-- **Slepian–Wolf Theorem** (Cover & Thomas, Theorem 15.4.1; El Gamal–Kim, Theorem 10.1):
    the closure of the operationally achievable rate region for distributed lossless coding
    of an i.i.d. correlated source `P` equals the single-letter Slepian–Wolf region
    `{ (R₁, R₂) | R₁ ≥ H(X | Y), R₂ ≥ H(Y | X), R₁ + R₂ ≥ H(X, Y) }`. -/
theorem slepian_wolf_theorem (P : ProbDist (α × β)) :
    closure { r : ℝ × ℝ | IsSlepianWolfAchievable P r.1 r.2 } = slepianWolfSingleLetter P := by
  apply Set.Subset.antisymm
  · have hclosed : IsClosed (slepianWolfSingleLetter P) := by
      have heq : slepianWolfSingleLetter P =
          ({ r : ℝ × ℝ | (0 : ℝ) ≤ r.1 } ∩ { r : ℝ × ℝ | (0 : ℝ) ≤ r.2 }) ∩
          ({ r : ℝ × ℝ | condEntropy P ≤ r.1 } ∩
            ({ r : ℝ × ℝ | condEntropy (P.map Prod.swap) ≤ r.2 } ∩
              { r : ℝ × ℝ | shannonEntropy P ≤ r.1 + r.2 })) := by
        ext ⟨r₁, r₂⟩
        simp only [slepianWolfSingleLetter, Set.mem_inter_iff, Set.mem_ofPred_eq]
        tauto
      rw [heq]
      exact ((isClosed_le continuous_const continuous_fst).inter
              (isClosed_le continuous_const continuous_snd)).inter
        ((isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le continuous_const (continuous_fst.add continuous_snd))))
    exact closure_minimal (fun r hr => slepian_wolf_converse P hr) hclosed
  · intro ⟨R₁, R₂⟩ ⟨_, _, h1, h2, h12⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(R₁ + ε / 2, R₂ + ε / 2), ?_, ?_⟩
    · exact slepian_wolf_achievability P (by linarith) (by linarith) (by linarith)
    · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have habs : |R₁ - (R₁ + ε / 2)| = ε / 2 := by
        rw [show R₁ - (R₁ + ε / 2) = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      have habs2 : |R₂ - (R₂ + ε / 2)| = ε / 2 := by
        rw [show R₂ - (R₂ + ε / 2) = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      rw [habs, habs2, max_self]
      linarith

end SlepianWolf

/-! ### 2. Two-User Discrete Memoryless MAC Capacity Region
(Cover & Thomas Thm. 15.3.1; El Gamal–Kim Thm. 4.3) -/

section MultipleAccessChannel

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- Average error probability of an `(n, M₁, M₂)` block code `(enc₁, enc₂, dec)` over a
    two-user discrete memoryless multiple-access channel `W : MACChannel X₁ X₂ Y`. -/
noncomputable def macAvgError (W : MACChannel X₁ X₂ Y) (n M₁ M₂ : ℕ)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
    (dec : (Fin n → Y) → Fin M₁ × Fin M₂) : ℝ := by
  classical
  exact if M₁ = 0 ∨ M₂ = 0 then 0 else
    ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
        if dec y ≠ (m₁, m₂) then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0

/-- Operational achievability of rate pair `(R₁, R₂)` over a two-user DM-MAC `W`. -/
def IsMACAchievable (W : MACChannel X₁ X₂ Y) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
      (dec : (Fin n → Y) → Fin M₁ × Fin M₂),
      macAvgError W n M₁ M₂ enc₁ enc₂ dec ≤ δ

/-- Operational capacity region (closed) of a two-user DM-MAC `W`. -/
def macOperationalRegion (W : MACChannel X₁ X₂ Y) : Set (ℝ × ℝ) :=
  closure { r : ℝ × ℝ | IsMACAchievable W r.1 r.2 }

/-- Single-letter MAC pentagon for a fixed product input distribution `P₁ × P₂`:
    `0 ≤ R₁ ≤ I(X₁; Y | X₂)`, `0 ≤ R₂ ≤ I(X₂; Y | X₁)`, `R₁ + R₂ ≤ I(X₁, X₂; Y)`. -/
def macPentagon (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) : Set (ℝ × ℝ) :=
  let J : ProbDist ((X₁ × X₂) × Y) := W.joint (P₁.prod P₂)
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
        r.1 ≤ condMutualInfo (J.map (fun t => (t.1.1, t.2, t.1.2))) ∧
        r.2 ≤ condMutualInfo (J.map (fun t => (t.1.2, t.2, t.1.1))) ∧
        r.1 + r.2 ≤ mutualInfo J }

/-- Single-letter capacity region of a two-user DM-MAC `W` (Cover & Thomas, Theorem 15.3.1):
    closure of the convex hull of the union of all product-input pentagons `macPentagon W P₁ P₂`. -/
def macSingleLetterRegion (W : MACChannel X₁ X₂ Y) : Set (ℝ × ℝ) :=
  closure (convexHull ℝ (⋃ (P₁ : ProbDist X₁) (P₂ : ProbDist X₂), macPentagon W P₁ P₂))

/-! #### 2.1 Product-Input Information Identities -/

private lemma mac_J1Y_marginals (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    let J := W.joint (P₁.prod P₂)
    let J₁Y := J.map (fun t => (t.1.1, t.2))
    J₁Y.fst = P₁ ∧ J₁Y.snd = J.snd := by
  dsimp only
  constructor
  · rw [← probDist_map_fst, map_comp_eq]
    change (W.joint (P₁.prod P₂)).map (Prod.fst ∘ Prod.fst) = P₁
    rw [← map_comp_eq, probDist_map_fst, probDist_map_fst, dmc_joint_fst, probDist_prod_fst]
  · rw [← probDist_map_snd, map_comp_eq]; exact probDist_map_snd _

private lemma mac_J2Y_marginals (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    let J := W.joint (P₁.prod P₂)
    let J₂Y := J.map (fun t => (t.1.2, t.2))
    J₂Y.fst = P₂ ∧ J₂Y.snd = J.snd := by
  dsimp only
  constructor
  · rw [← probDist_map_fst, map_comp_eq]
    change (W.joint (P₁.prod P₂)).map (Prod.snd ∘ Prod.fst) = P₂
    rw [← map_comp_eq, probDist_map_fst, dmc_joint_fst, probDist_map_snd, probDist_prod_snd]
  · rw [← probDist_map_snd, map_comp_eq]; exact probDist_map_snd _

private lemma mac_cmi1_eq (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    let J := W.joint (P₁.prod P₂)
    let J₂Y := J.map (fun t => (t.1.2, t.2))
    condMutualInfo (J.map (fun t => (t.1.1, t.2, t.1.2))) =
      shannonEntropy P₁ + shannonEntropy J₂Y - shannonEntropy J := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₂Y := J.map (fun t => (t.1.2, t.2))
  let e : ((X₁ × X₂) × Y) ≃ (X₁ × Y × X₂) :=
    { toFun := fun t => (t.1.1, t.2, t.1.2)
      invFun := fun t => ((t.1, t.2.2), t.2.1)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  unfold condMutualInfo
  dsimp only
  have h1 : (J.map (fun t => (t.1.1, t.2, t.1.2))).map (fun t => (t.1, t.2.2)) = P₁.prod P₂ := by
    rw [map_comp_eq]
    change J.map Prod.fst = P₁.prod P₂
    rw [probDist_map_fst, dmc_joint_fst]
  have h2 : (J.map (fun t => (t.1.1, t.2, t.1.2))).map (fun t => (t.2.1, t.2.2)) =
      J₂Y.map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h3 : shannonEntropy (J.map (fun t => (t.1.1, t.2, t.1.2))) = shannonEntropy J :=
    shannonEntropy_map_equiv e J
  have h4 : (J.map (fun t => (t.1.1, t.2, t.1.2))).map (fun t => t.2.2) = P₂ := by
    rw [map_comp_eq]
    change J.map (Prod.snd ∘ Prod.fst) = P₂
    rw [← map_comp_eq, probDist_map_fst, dmc_joint_fst, probDist_map_snd, probDist_prod_snd]
  rw [h1, h2, h3, h4, shannonEntropy_prod, shannonEntropy_swap]
  ring

private lemma mac_cmi2_eq (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    let J := W.joint (P₁.prod P₂)
    let J₁Y := J.map (fun t => (t.1.1, t.2))
    condMutualInfo (J.map (fun t => (t.1.2, t.2, t.1.1))) =
      shannonEntropy P₂ + shannonEntropy J₁Y - shannonEntropy J := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun t => (t.1.1, t.2))
  let e : ((X₁ × X₂) × Y) ≃ (X₂ × Y × X₁) :=
    { toFun := fun t => (t.1.2, t.2, t.1.1)
      invFun := fun t => ((t.2.2, t.1), t.2.1)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  unfold condMutualInfo
  dsimp only
  have h1 : (J.map (fun t => (t.1.2, t.2, t.1.1))).map (fun t => (t.1, t.2.2)) =
      (P₁.prod P₂).map Prod.swap := by
    rw [map_comp_eq]
    change J.map (Prod.swap ∘ Prod.fst) = (P₁.prod P₂).map Prod.swap
    rw [← map_comp_eq, probDist_map_fst, dmc_joint_fst]
  have h2 : (J.map (fun t => (t.1.2, t.2, t.1.1))).map (fun t => (t.2.1, t.2.2)) =
      J₁Y.map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have h3 : shannonEntropy (J.map (fun t => (t.1.2, t.2, t.1.1))) = shannonEntropy J :=
    shannonEntropy_map_equiv e J
  have h4 : (J.map (fun t => (t.1.2, t.2, t.1.1))).map (fun t => t.2.2) = P₁ := by
    rw [map_comp_eq]
    change J.map (Prod.fst ∘ Prod.fst) = P₁
    rw [← map_comp_eq, probDist_map_fst, probDist_map_fst, dmc_joint_fst, probDist_prod_fst]
  rw [h1, h2, h3, h4, shannonEntropy_swap, shannonEntropy_prod, shannonEntropy_swap]
  ring

private lemma mac_mi_eq (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    let J := W.joint (P₁.prod P₂)
    mutualInfo J = shannonEntropy P₁ + shannonEntropy P₂ + shannonEntropy J.snd - shannonEntropy J := by
  dsimp only
  unfold mutualInfo
  rw [dmc_joint_fst, shannonEntropy_prod]

private lemma mac_pentagon_polymatroid (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    let J := W.joint (P₁.prod P₂)
    let I₁ := condMutualInfo (J.map (fun t => (t.1.1, t.2, t.1.2)))
    let I₂ := condMutualInfo (J.map (fun t => (t.1.2, t.2, t.1.1)))
    let I₁₂ := mutualInfo J
    0 ≤ I₁ ∧ 0 ≤ I₂ ∧ I₁ ≤ I₁₂ ∧ I₂ ≤ I₁₂ ∧ I₁₂ ≤ I₁ + I₂ := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun t => (t.1.1, t.2))
  let J₂Y := J.map (fun t => (t.1.2, t.2))
  have hc1 := mac_cmi1_eq W P₁ P₂
  have hc2 := mac_cmi2_eq W P₁ P₂
  have hmi := mac_mi_eq W P₁ P₂
  dsimp only at hc1 hc2 hmi
  refine ⟨condMutualInfo_nonneg _, condMutualInfo_nonneg _, ?_, ?_, ?_⟩
  · have hm2 := mutualInfo_nonneg J₂Y
    unfold mutualInfo at hm2
    rw [(mac_J2Y_marginals W P₁ P₂).1, (mac_J2Y_marginals W P₁ P₂).2] at hm2
    linarith
  · have hm1 := mutualInfo_nonneg J₁Y
    unfold mutualInfo at hm1
    rw [(mac_J1Y_marginals W P₁ P₂).1, (mac_J1Y_marginals W P₁ P₂).2] at hm1
    linarith
  · have hc12 := condMutualInfo_nonneg (J.map (fun t => (t.1.1, t.1.2, t.2)))
    unfold condMutualInfo at hc12
    dsimp only at hc12
    have ha : (J.map (fun t => (t.1.1, t.1.2, t.2))).map (fun t => (t.1, t.2.2)) = J₁Y := by
      rw [map_comp_eq]; rfl
    have hb : (J.map (fun t => (t.1.1, t.1.2, t.2))).map (fun t => (t.2.1, t.2.2)) = J₂Y := by
      rw [map_comp_eq]; rfl
    have hc : (J.map (fun t => (t.1.1, t.1.2, t.2))).map (fun t => t.2.2) = J.snd := by
      rw [map_comp_eq]; exact probDist_map_snd J
    let e : ((X₁ × X₂) × Y) ≃ (X₁ × X₂ × Y) := Equiv.prodAssoc X₁ X₂ Y
    have hd : shannonEntropy (J.map (fun t => (t.1.1, t.1.2, t.2))) = shannonEntropy J :=
      shannonEntropy_map_equiv e J
    rw [ha, hb, hc, hd] at hc12
    linarith

/-! #### 2.2 Three-Way Joint Typicality and Random-Coding Bound for MAC -/

/-- **Three-Way Jointly Weakly Typical Set** `A_ε^(n)(X₁, X₂, Y)` for a two-user MAC `W`
    under product input `P₁ × P₂` (Cover & Thomas §15.3.2; El Gamal–Kim §4.5). -/
noncomputable def macTypicalSet (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (ε : ℝ) : Finset ((Fin n → X₁) × (Fin n → X₂) × (Fin n → Y)) := by
  classical
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun t => (t.1.1, t.2))
  let J₂Y := J.map (fun t => (t.1.2, t.2))
  exact Finset.univ.filter fun t =>
    t.1 ∈ weakTypicalSet P₁ n ε ∧
    t.2.1 ∈ weakTypicalSet P₂ n ε ∧
    t.2.2 ∈ weakTypicalSet J.snd n ε ∧
    (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet J₁Y n ε ∧
    (fun i => (t.2.1 i, t.2.2 i)) ∈ weakTypicalSet J₂Y n ε ∧
    (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈ weakTypicalSet J n ε

private lemma mem_macTypicalSet (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (ε : ℝ) (t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y)) :
    let J := W.joint (P₁.prod P₂)
    t ∈ macTypicalSet W P₁ P₂ n ε ↔
      t.1 ∈ weakTypicalSet P₁ n ε ∧
      t.2.1 ∈ weakTypicalSet P₂ n ε ∧
      t.2.2 ∈ weakTypicalSet J.snd n ε ∧
      (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet (J.map (fun z => (z.1.1, z.2))) n ε ∧
      (fun i => (t.2.1 i, t.2.2 i)) ∈ weakTypicalSet (J.map (fun z => (z.1.2, z.2))) n ε ∧
      (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈ weakTypicalSet J n ε := by
  classical
  simp [macTypicalSet]

private def macZipEquiv (X₁ X₂ Y : Type*) (n : ℕ) :
    ((Fin n → X₁) × (Fin n → X₂) × (Fin n → Y)) ≃ (Fin n → (X₁ × X₂) × Y) where
  toFun := fun t i => ((t.1 i, t.2.1 i), t.2.2 i)
  invFun := fun z => (fun i => (z i).1.1, fun i => (z i).1.2, fun i => (z i).2)
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun _ => rfl

private lemma macIid_pmf_eq (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) (y : Fin n → Y) :
    (iidDist P₁ n).pmf x₁ * (iidDist P₂ n).pmf x₂ *
      (W.power n).trans (fun i => (x₁ i, x₂ i)) y =
    (iidDist (W.joint (P₁.prod P₂)) n).pmf (macZipEquiv X₁ X₂ Y n (x₁, x₂, y)) := by
  unfold iidDist DMC.power DMC.joint ProbDist.prod
  simp only [macZipEquiv, Equiv.coe_fn_mk]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

private lemma mac_marginal_J2Y (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (x₂ : Fin n → X₂) (y : Fin n → Y) :
    let J := W.joint (P₁.prod P₂)
    let J₂Y := J.map (fun z => (z.1.2, z.2))
    (iidDist P₂ n).pmf x₂ *
      (∑ x₁ : Fin n → X₁, (iidDist P₁ n).pmf x₁ * (W.power n).trans (fun i => (x₁ i, x₂ i)) y) =
    (iidDist J₂Y n).pmf (fun i => (x₂ i, y i)) := by
  classical
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₂Y := J.map (fun z => (z.1.2, z.2))
  have hcoord : ∀ (a₂ : X₂) (b : Y),
      J₂Y.pmf (a₂, b) = ∑ a₁ : X₁, P₁.pmf a₁ * P₂.pmf a₂ * W.trans (a₁, a₂) b := by
    intro a₂ b
    unfold J₂Y J ProbDist.map DMC.joint ProbDist.prod
    dsimp only
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.sum_eq_single a₂]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a₂' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.mul_sum]
  have hfun : ∀ x₁ : Fin n → X₁,
      (iidDist P₂ n).pmf x₂ * ((iidDist P₁ n).pmf x₁ * (W.power n).trans (fun i => (x₁ i, x₂ i)) y) =
        ∏ i : Fin n, (P₁.pmf (x₁ i) * P₂.pmf (x₂ i) * W.trans (x₁ i, x₂ i) (y i)) := fun x₁ => by
    unfold iidDist DMC.power; dsimp only
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  simp_rw [hfun]
  rw [← Fintype.prod_sum (fun i a₁ => P₁.pmf a₁ * P₂.pmf (x₂ i) * W.trans (a₁, x₂ i) (y i))]
  unfold iidDist; dsimp only
  exact Finset.prod_congr rfl fun i _ => (hcoord (x₂ i) (y i)).symm

private lemma mac_marginal_J1Y (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (x₁ : Fin n → X₁) (y : Fin n → Y) :
    let J := W.joint (P₁.prod P₂)
    let J₁Y := J.map (fun z => (z.1.1, z.2))
    (iidDist P₁ n).pmf x₁ *
      (∑ x₂ : Fin n → X₂, (iidDist P₂ n).pmf x₂ * (W.power n).trans (fun i => (x₁ i, x₂ i)) y) =
    (iidDist J₁Y n).pmf (fun i => (x₁ i, y i)) := by
  classical
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun z => (z.1.1, z.2))
  have hcoord : ∀ (a₁ : X₁) (b : Y),
      J₁Y.pmf (a₁, b) = ∑ a₂ : X₂, P₁.pmf a₁ * P₂.pmf a₂ * W.trans (a₁, a₂) b := by
    intro a₁ b
    unfold J₁Y J ProbDist.map DMC.joint ProbDist.prod
    dsimp only
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a₁]
    · refine Finset.sum_congr rfl fun a₂ _ => ?_
      rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a₁' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.mul_sum]
  have hfun : ∀ x₂ : Fin n → X₂,
      (iidDist P₁ n).pmf x₁ * ((iidDist P₂ n).pmf x₂ * (W.power n).trans (fun i => (x₁ i, x₂ i)) y) =
        ∏ i : Fin n, (P₁.pmf (x₁ i) * P₂.pmf (x₂ i) * W.trans (x₁ i, x₂ i) (y i)) := fun x₂ => by
    unfold iidDist DMC.power; dsimp only
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  simp_rw [hfun]
  rw [← Fintype.prod_sum (fun i a₂ => P₁.pmf (x₁ i) * P₂.pmf a₂ * W.trans (x₁ i, a₂) (y i))]
  unfold iidDist; dsimp only
  exact Finset.prod_congr rfl fun i _ => (hcoord (x₁ i) (y i)).symm

private lemma mac_marginal_JY (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (y : Fin n → Y) :
    ∑ x₁ : Fin n → X₁, ∑ x₂ : Fin n → X₂,
      (iidDist P₁ n).pmf x₁ * (iidDist P₂ n).pmf x₂ *
        (W.power n).trans (fun i => (x₁ i, x₂ i)) y =
    (iidDist (W.joint (P₁.prod P₂)).snd n).pmf y := by
  have h1 : ∀ x₁ : Fin n → X₁, ∑ x₂ : Fin n → X₂,
      (iidDist P₁ n).pmf x₁ * (iidDist P₂ n).pmf x₂ *
        (W.power n).trans (fun i => (x₁ i, x₂ i)) y =
      (iidDist ((W.joint (P₁.prod P₂)).map (fun z => (z.1.1, z.2))) n).pmf
        (fun i => (x₁ i, y i)) := fun x₁ => by
    have h := mac_marginal_J1Y W P₁ P₂ n x₁ y
    dsimp only at h
    rw [Finset.mul_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x₂ _ => by ring
  simp_rw [h1]
  have h2 : ∑ x₁ : Fin n → X₁,
      (iidDist ((W.joint (P₁.prod P₂)).map (fun z => (z.1.1, z.2))) n).pmf (fun i => (x₁ i, y i)) =
      (jointIidDist ((W.joint (P₁.prod P₂)).map (fun z => (z.1.1, z.2))) n).snd.pmf y := rfl
  rw [h2, jointIidDist_snd, (mac_J1Y_marginals W P₁ P₂).2]

private lemma macTypicalSet_card_le (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n : ℕ) (ε : ℝ) :
    ((macTypicalSet W P₁ P₂ n ε).card : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy (W.joint (P₁.prod P₂)) + ε)) := by
  classical
  have hle : (macTypicalSet W P₁ P₂ n ε).card ≤
      (weakTypicalSet (W.joint (P₁.prod P₂)) n ε).card := by
    refine Finset.card_le_card_of_injOn (macZipEquiv X₁ X₂ Y n) ?_ ?_
    · intro t ht
      exact ((mem_macTypicalSet W P₁ P₂ n ε t).mp ht).2.2.2.2.2
    · intro t₁ _ t₂ _ h
      exact (macZipEquiv X₁ X₂ Y n).injective h
  exact le_trans (by exact_mod_cast hle) (weakTypicalSet_card_le _ n ε)

private lemma iidDist_map_comp {α γ : Type*} [Fintype α] [Fintype γ]
    (P : ProbDist α) (n : ℕ) (g : α → γ) :
    (iidDist P n).map (fun z i => g (z i)) = iidDist (P.map g) n := by
  classical
  unfold ProbDist.map iidDist
  congr; funext u; dsimp only
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

private lemma probDist_sum_not_mem_of_map {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
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

private lemma mac_aep_prob_tendsto_one (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    let J := W.joint (P₁.prod P₂)
    ∃ N : ℕ, ∀ n ≥ N,
      1 - δ ≤ ∑ t ∈ macTypicalSet W P₁ P₂ n ε,
        (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) := by
  classical
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun z => (z.1.1, z.2))
  let J₂Y := J.map (fun z => (z.1.2, z.2))
  have hδ6 : 0 < δ / 6 := by linarith
  obtain ⟨N₁, hN₁⟩ := aep_typical_prob_tendsto_one P₁ hε hδ6
  obtain ⟨N₂, hN₂⟩ := aep_typical_prob_tendsto_one P₂ hε hδ6
  obtain ⟨N₃, hN₃⟩ := aep_typical_prob_tendsto_one J.snd hε hδ6
  obtain ⟨N₄, hN₄⟩ := aep_typical_prob_tendsto_one J₁Y hε hδ6
  obtain ⟨N₅, hN₅⟩ := aep_typical_prob_tendsto_one J₂Y hε hδ6
  obtain ⟨N₆, hN₆⟩ := aep_typical_prob_tendsto_one J hε hδ6
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ N₆), fun n hn => ?_⟩
  let Q : ProbDist ((Fin n → X₁) × (Fin n → X₂) × (Fin n → Y)) :=
    { pmf := fun t => (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t)
      nonneg := fun t => (iidDist J n).nonneg _
      sum_one := by
        rw [Fintype.sum_equiv (macZipEquiv X₁ X₂ Y n) _ (fun z => (iidDist J n).pmf z) (fun _ => rfl)]
        exact (iidDist J n).sum_one }
  -- Map `Q` to each of the 6 marginals
  have hQ_zip : Q.map (macZipEquiv X₁ X₂ Y n) = iidDist J n := by
    unfold ProbDist.map; congr; funext z; dsimp only [Q]
    rw [Finset.sum_eq_single ((macZipEquiv X₁ X₂ Y n).symm z)]
    · simp; rfl
    · intro t _ hne
      have : macZipEquiv X₁ X₂ Y n t ≠ z := fun h =>
        hne ((macZipEquiv X₁ X₂ Y n).symm_apply_eq.mpr h.symm).symm
      simp only [this, ↓reduceIte]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hmap1 : Q.map (fun t => t.1) = iidDist P₁ n := by
    have h : (fun t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y) => t.1) =
        (fun z i => (z i).1.1) ∘ macZipEquiv X₁ X₂ Y n := rfl
    rw [h, ← map_comp_eq, hQ_zip, iidDist_map_comp J n (fun z => z.1.1)]
    congr 1
    change J.map (Prod.fst ∘ Prod.fst) = P₁
    rw [← map_comp_eq, probDist_map_fst, probDist_map_fst, dmc_joint_fst, probDist_prod_fst]
  have hmap2 : Q.map (fun t => t.2.1) = iidDist P₂ n := by
    have h : (fun t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y) => t.2.1) =
        (fun z i => (z i).1.2) ∘ macZipEquiv X₁ X₂ Y n := rfl
    rw [h, ← map_comp_eq, hQ_zip, iidDist_map_comp J n (fun z => z.1.2)]
    congr 1
    change J.map (Prod.snd ∘ Prod.fst) = P₂
    rw [← map_comp_eq, probDist_map_fst, dmc_joint_fst, probDist_map_snd, probDist_prod_snd]
  have hmap3 : Q.map (fun t => t.2.2) = iidDist J.snd n := by
    have h : (fun t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y) => t.2.2) =
        (fun z i => (z i).2) ∘ macZipEquiv X₁ X₂ Y n := rfl
    rw [h, ← map_comp_eq, hQ_zip, iidDist_map_comp J n (fun z => z.2), probDist_map_snd]
  have hmap4 : Q.map (fun t i => (t.1 i, t.2.2 i)) = iidDist J₁Y n := by
    have h : (fun (t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y)) i => (t.1 i, t.2.2 i)) =
        (fun z i => ((z i).1.1, (z i).2)) ∘ macZipEquiv X₁ X₂ Y n := rfl
    rw [h, ← map_comp_eq, hQ_zip, iidDist_map_comp J n (fun z => (z.1.1, z.2))]
  have hmap5 : Q.map (fun t i => (t.2.1 i, t.2.2 i)) = iidDist J₂Y n := by
    have h : (fun (t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y)) i => (t.2.1 i, t.2.2 i)) =
        (fun z i => ((z i).1.2, (z i).2)) ∘ macZipEquiv X₁ X₂ Y n := rfl
    rw [h, ← map_comp_eq, hQ_zip, iidDist_map_comp J n (fun z => (z.1.2, z.2))]
  -- Union bound
  let A := macTypicalSet W P₁ P₂ n ε
  have hunion : ∀ t, (if t ∉ A then Q.pmf t else 0) ≤
      (if t.1 ∉ weakTypicalSet P₁ n ε then Q.pmf t else 0) +
      (if t.2.1 ∉ weakTypicalSet P₂ n ε then Q.pmf t else 0) +
      (if t.2.2 ∉ weakTypicalSet J.snd n ε then Q.pmf t else 0) +
      (if (fun i => (t.1 i, t.2.2 i)) ∉ weakTypicalSet J₁Y n ε then Q.pmf t else 0) +
      (if (fun i => (t.2.1 i, t.2.2 i)) ∉ weakTypicalSet J₂Y n ε then Q.pmf t else 0) +
      (if macZipEquiv X₁ X₂ Y n t ∉ weakTypicalSet J n ε then Q.pmf t else 0) := by
    intro t
    have hq0 := Q.nonneg t
    by_cases h1 : t.1 ∈ weakTypicalSet P₁ n ε <;>
    by_cases h2 : t.2.1 ∈ weakTypicalSet P₂ n ε <;>
    by_cases h3 : t.2.2 ∈ weakTypicalSet J.snd n ε <;>
    by_cases h4 : (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet J₁Y n ε <;>
    by_cases h5 : (fun i => (t.2.1 i, t.2.2 i)) ∈ weakTypicalSet J₂Y n ε <;>
    by_cases h6 : macZipEquiv X₁ X₂ Y n t ∈ weakTypicalSet J n ε
    · have hmem : t ∈ A := (mem_macTypicalSet W P₁ P₂ n ε t).mpr ⟨h1, h2, h3, h4, h5, h6⟩
      simp [hmem, h1, h2, h3, h4, h5, h6]
    all_goals
      simp only [h1, h2, h3, h4, h5, h6, not_true_eq_false, not_false_eq_true, ↓reduceIte]
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
  have hs1 := probDist_sum_not_mem_of_map Q (fun t => t.1) (weakTypicalSet P₁ n ε) (iidDist P₁ n) hmap1
  have hs2 := probDist_sum_not_mem_of_map Q (fun t => t.2.1) (weakTypicalSet P₂ n ε) (iidDist P₂ n) hmap2
  have hs3 := probDist_sum_not_mem_of_map Q (fun t => t.2.2) (weakTypicalSet J.snd n ε) (iidDist J.snd n) hmap3
  have hs4 := probDist_sum_not_mem_of_map Q (fun t i => (t.1 i, t.2.2 i)) (weakTypicalSet J₁Y n ε) (iidDist J₁Y n) hmap4
  have hs5 := probDist_sum_not_mem_of_map Q (fun t i => (t.2.1 i, t.2.2 i)) (weakTypicalSet J₂Y n ε) (iidDist J₂Y n) hmap5
  have hs6 := probDist_sum_not_mem_of_map Q (macZipEquiv X₁ X₂ Y n) (weakTypicalSet J n ε) (iidDist J n) hQ_zip
  rw [hcomp, hs1, hs2, hs3, hs4, hs5, hs6] at hsum
  have hp1 := hN₁ n (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hn)
  have hp2 := hN₂ n (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hn)
  have hp3 := hN₃ n (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hn)
  have hp4 := hN₄ n (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hn)
  have hp5 := hN₅ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hp6 := hN₆ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  linarith

/-- Packing-lemma error bounds for the 3 wrong-message events in 3-way MAC typicality. -/
private lemma macTypicalSet_indep_bounds (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) (n : ℕ) (ε : ℝ) :
    let J := W.joint (P₁.prod P₂)
    let J₁Y := J.map (fun z => (z.1.1, z.2))
    let J₂Y := J.map (fun z => (z.1.2, z.2))
    let A := macTypicalSet W P₁ P₂ n ε
    (∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist J₂Y n).pmf (fun i => (t.2.1 i, t.2.2 i)) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) - 3 * ε)))) ∧
    (∑ t ∈ A, (iidDist P₂ n).pmf t.2.1 * (iidDist J₁Y n).pmf (fun i => (t.1 i, t.2.2 i)) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1))) - 3 * ε)))) ∧
    (∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 * (iidDist J.snd n).pmf t.2.2 ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo J - 4 * ε)))) := by
  classical
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun z => (z.1.1, z.2))
  let J₂Y := J.map (fun z => (z.1.2, z.2))
  let A := macTypicalSet W P₁ P₂ n ε
  refine ⟨?_, ?_, ?_⟩
  · -- Event 2: wrong m₁', same m₂
    have hterm : ∀ t ∈ A,
        (iidDist P₁ n).pmf t.1 * (iidDist J₂Y n).pmf (fun i => (t.2.1 i, t.2.2 i)) ≤
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₂Y - ε))) := by
      intro t ht
      have hm := (mem_macTypicalSet W P₁ P₂ n ε t).mp ht
      have h1 := hm.1
      have h5 := hm.2.2.2.2.1
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h5
      exact mul_le_mul h1.2 h5.2 ((iidDist J₂Y n).nonneg _)
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    calc ∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist J₂Y n).pmf (fun i => (t.2.1 i, t.2.2 i))
      _ ≤ ∑ _t ∈ A, ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₂Y - ε)))) := Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₂Y - ε)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy J + ε)) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₂Y - ε)))) :=
          mul_le_mul_of_nonneg_right (macTypicalSet_card_le W P₁ P₂ n ε) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) - 3 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          have hc := mac_cmi1_eq W P₁ P₂
          dsimp only at hc
          rw [hc]; ring
  · -- Event 3: same m₁, wrong m₂'
    have hterm : ∀ t ∈ A,
        (iidDist P₂ n).pmf t.2.1 * (iidDist J₁Y n).pmf (fun i => (t.1 i, t.2.2 i)) ≤
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₁Y - ε))) := by
      intro t ht
      have hm := (mem_macTypicalSet W P₁ P₂ n ε t).mp ht
      have h2 := hm.2.1
      have h4 := hm.2.2.2.1
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at h2 h4
      exact mul_le_mul h2.2 h4.2 ((iidDist J₁Y n).nonneg _)
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    calc ∑ t ∈ A, (iidDist P₂ n).pmf t.2.1 * (iidDist J₁Y n).pmf (fun i => (t.1 i, t.2.2 i))
      _ ≤ ∑ _t ∈ A, ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₁Y - ε)))) := Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₁Y - ε)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy J + ε)) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J₁Y - ε)))) :=
          mul_le_mul_of_nonneg_right (macTypicalSet_card_le W P₁ P₂ n ε) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1))) - 3 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          have hc := mac_cmi2_eq W P₁ P₂
          dsimp only at hc
          rw [hc]; ring
  · -- Event 4: both m₁' ≠ m₁ and m₂' ≠ m₂
    have hterm : ∀ t ∈ A,
        (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 * (iidDist J.snd n).pmf t.2.2 ≤
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J.snd - ε))) := by
      intro t ht
      have hm := (mem_macTypicalSet W P₁ P₂ n ε t).mp ht
      have h1 := hm.1
      have h2 := hm.2.1
      have h3 := hm.2.2.1
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h3
      have h12 := mul_le_mul h1.2 h2.2 ((iidDist P₂ n).nonneg _)
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      exact mul_le_mul h12 h3.2 ((iidDist J.snd n).nonneg _) (by positivity)
    calc ∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 * (iidDist J.snd n).pmf t.2.2
      _ ≤ ∑ _t ∈ A, ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J.snd - ε)))) := Finset.sum_le_sum hterm
      _ = (A.card : ℝ) * ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J.snd - ε)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy J + ε)) *
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₁ - ε))) *
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P₂ - ε))) *
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy J.snd - ε)))) :=
          mul_le_mul_of_nonneg_right (macTypicalSet_card_le W P₁ P₂ n ε) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo J - 4 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          have hmi := mac_mi_eq W P₁ P₂
          dsimp only at hmi
          rw [hmi]; ring

/-- **Three-Way Joint-Typicality MAC Decoder** (Cover & Thomas §15.3.2):
    outputs the unique pair `(m₁, m₂)` such that `(enc₁ m₁, enc₂ m₂, y) ∈ macTypicalSet W P₁ P₂ n ε`,
    if one exists, and `(⟨0, hM₁⟩, ⟨0, hM₂⟩)` otherwise. -/
noncomputable def macTypicalDec (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂) (y : Fin n → Y) :
    Fin M₁ × Fin M₂ := by
  classical
  exact if h : ∃! m : Fin M₁ × Fin M₂, (enc₁ m.1, enc₂ m.2, y) ∈ macTypicalSet W P₁ P₂ n ε then
    Classical.choose h
  else
    (⟨0, hM₁⟩, ⟨0, hM₂⟩)

private lemma macTypicalDec_eq_of_unique (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂) (y : Fin n → Y)
    (m₁ : Fin M₁) (m₂ : Fin M₂)
    (hm : (enc₁ m₁, enc₂ m₂, y) ∈ macTypicalSet W P₁ P₂ n ε)
    (huniq : ∀ m' : Fin M₁ × Fin M₂, m' ≠ (m₁, m₂) →
      (enc₁ m'.1, enc₂ m'.2, y) ∉ macTypicalSet W P₁ P₂ n ε) :
    macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y = (m₁, m₂) := by
  classical
  have hex : ∃! m : Fin M₁ × Fin M₂, (enc₁ m.1, enc₂ m.2, y) ∈ macTypicalSet W P₁ P₂ n ε := by
    refine ⟨(m₁, m₂), hm, fun m' h => ?_⟩
    by_contra hne
    exact huniq m' hne h
  simp only [macTypicalDec, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  by_contra hne
  exact huniq (Classical.choose hex) hne hspec.1

private lemma macTypicalDec_err_indicator_le [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]
    (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂) (y : Fin n → Y)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    let A := macTypicalSet W P₁ P₂ n ε
    (if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂) then (1 : ℝ) else 0) ≤
      (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0) +
      (∑ m₁' ∈ Finset.univ.erase m₁, if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0) +
      (∑ m₂' ∈ Finset.univ.erase m₂, if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0) +
      (∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
        if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0) := by
  dsimp only
  let A := macTypicalSet W P₁ P₂ n ε
  have hnn2 : (0 : ℝ) ≤ ∑ m₁' ∈ Finset.univ.erase m₁, if (enc₁ m₁', enc₂ m₂, y) ∈ A then 1 else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hnn3 : (0 : ℝ) ≤ ∑ m₂' ∈ Finset.univ.erase m₂, if (enc₁ m₁, enc₂ m₂', y) ∈ A then 1 else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hnn4 : (0 : ℝ) ≤ ∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
      if (enc₁ m₁', enc₂ m₂', y) ∈ A then 1 else 0 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  split_ifs with herr hmem
  · have hex : ∃ m' : Fin M₁ × Fin M₂, m' ≠ (m₁, m₂) ∧ (enc₁ m'.1, enc₂ m'.2, y) ∈ A := by
      by_contra hnone
      push Not at hnone
      exact herr (macTypicalDec_eq_of_unique W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y m₁ m₂ hmem hnone)
    obtain ⟨⟨m₁', m₂'⟩, hne, hA⟩ := hex
    by_cases h1 : m₁' = m₁
    · subst h1
      have h2 : m₂' ≠ m₂ := fun h2 => hne (by subst h2; rfl)
      have hle : (1 : ℝ) ≤ ∑ k₂ ∈ Finset.univ.erase m₂,
          if (enc₁ m₁', enc₂ k₂, y) ∈ A then (1 : ℝ) else 0 := by
        calc (1 : ℝ) = (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0) := by simp [hA]
          _ ≤ _ := Finset.single_le_sum
              (f := fun k₂ => if (enc₁ m₁', enc₂ k₂, y) ∈ A then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num)
              (Finset.mem_erase.mpr ⟨h2, Finset.mem_univ m₂'⟩)
      linarith
    · by_cases h2 : m₂' = m₂
      · subst h2
        have hle : (1 : ℝ) ≤ ∑ k₁ ∈ Finset.univ.erase m₁,
            if (enc₁ k₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0) := by simp [hA]
            _ ≤ _ := Finset.single_le_sum
                (f := fun k₁ => if (enc₁ k₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨h1, Finset.mem_univ m₁'⟩)
        linarith
      · have hle_in : (1 : ℝ) ≤ ∑ k₂ ∈ Finset.univ.erase m₂,
            if (enc₁ m₁', enc₂ k₂, y) ∈ A then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0) := by simp [hA]
            _ ≤ _ := Finset.single_le_sum
                (f := fun k₂ => if (enc₁ m₁', enc₂ k₂, y) ∈ A then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num)
                (Finset.mem_erase.mpr ⟨h2, Finset.mem_univ m₂'⟩)
        have hle : (1 : ℝ) ≤ ∑ k₁ ∈ Finset.univ.erase m₁, ∑ k₂ ∈ Finset.univ.erase m₂,
            if (enc₁ k₁, enc₂ k₂, y) ∈ A then (1 : ℝ) else 0 :=
          le_trans hle_in (Finset.single_le_sum
            (f := fun k₁ => ∑ k₂ ∈ Finset.univ.erase m₂,
              if (enc₁ k₁, enc₂ k₂, y) ∈ A then (1 : ℝ) else 0)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_erase.mpr ⟨h1, Finset.mem_univ m₁'⟩))
        linarith
  · linarith
  · linarith
  · linarith

private lemma mac_rc_term1 [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]
    (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (ε : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) :
    let J := W.joint (P₁.prod P₂)
    let A := macTypicalSet W P₁ P₂ n ε
    (∑ y : Fin n → Y, ∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) =
      1 - ∑ t ∈ A, (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let A := macTypicalSet W P₁ P₂ n ε
  have hin : ∀ y : Fin n → Y,
      (∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) =
      ∑ x₁, ∑ x₂, if (x₁, x₂, y) ∉ A
        then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n (x₁, x₂, y)) else 0 := by
    intro y
    have hstep1 : ∀ enc₁ : Fin M₁ → Fin n → X₁,
        (∑ enc₂ : Fin M₂ → Fin n → X₂, (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) =
        codebookProb P₁ n M₁ enc₁ * ∑ x₂, (iidDist P₂ n).pmf x₂ *
          ((W.power n).trans (fun i => (enc₁ m₁ i, x₂ i)) y *
            (if (enc₁ m₁, x₂, y) ∉ A then (1 : ℝ) else 0)) := fun enc₁ => by
      have hrw : ∀ enc₂ : Fin M₂ → Fin n → X₂,
          (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0)) =
          codebookProb P₁ n M₁ enc₁ * (codebookProb P₂ n M₂ enc₂ *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) := fun _ => by ring
      simp_rw [hrw, ← Finset.mul_sum]
      congr 1
      unfold codebookProb
      exact sum_pi_prod_mul_single' (iidDist P₂ n) m₂
        (fun x₂ => (W.power n).trans (fun i => (enc₁ m₁ i, x₂ i)) y *
          (if (enc₁ m₁, x₂, y) ∉ A then (1 : ℝ) else 0))
    rw [Finset.sum_congr rfl fun enc₁ _ => hstep1 enc₁]
    unfold codebookProb
    rw [sum_pi_prod_mul_single' (iidDist P₁ n) m₁
      (fun x₁ => ∑ x₂, (iidDist P₂ n).pmf x₂ *
        ((W.power n).trans (fun i => (x₁ i, x₂ i)) y *
          (if (x₁, x₂, y) ∉ A then (1 : ℝ) else 0)))]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₂ _ => ?_
    have hpmf := macIid_pmf_eq W P₁ P₂ n x₁ x₂ y
    split_ifs <;> linarith
  change ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂,
      (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
        ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
          (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0)) = _
  rw [Finset.sum_congr rfl fun y _ => hin y]
  have htot : (∑ y : Fin n → Y, ∑ x₁, ∑ x₂, if (x₁, x₂, y) ∉ A
        then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n (x₁, x₂, y)) else 0) =
      ∑ t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y),
        if t ∉ A then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    trans (∑ x₁, ∑ y : Fin n → Y, ∑ x₂, if (x₁, x₂, y) ∉ A
        then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n (x₁, x₂, y)) else 0)
    · exact Finset.sum_comm
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [htot]
  have h1 : ∑ t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y),
        (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) = 1 := by
    rw [Fintype.sum_equiv (macZipEquiv X₁ X₂ Y n) _ (fun z => (iidDist J n).pmf z) (fun _ => rfl)]
    exact (iidDist J n).sum_one
  have hsplit : ∑ t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y),
        (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) =
      (∑ t, if t ∈ A then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) else 0) +
      (∑ t, if t ∉ A then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by by_cases h : t ∈ A <;> simp [h]
  have hmem : (∑ t, if t ∈ A then (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) else 0) =
      ∑ t ∈ A, (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  linarith

private lemma mac_rc_term2 [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]
    (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (ε : ℝ) (m₁ m₁' : Fin M₁) (hne : m₁' ≠ m₁) (m₂ : Fin M₂) :
    let J := W.joint (P₁.prod P₂)
    let J₂Y := J.map (fun z => (z.1.2, z.2))
    let A := macTypicalSet W P₁ P₂ n ε
    (∑ y : Fin n → Y, ∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) =
      ∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist J₂Y n).pmf (fun i => (t.2.1 i, t.2.2 i)) := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₂Y := J.map (fun z => (z.1.2, z.2))
  let A := macTypicalSet W P₁ P₂ n ε
  have hin : ∀ y : Fin n → Y,
      (∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) =
      ∑ x₂, ∑ x₁', if (x₁', x₂, y) ∈ A
        then (iidDist P₁ n).pmf x₁' * (iidDist J₂Y n).pmf (fun i => (x₂ i, y i)) else 0 := by
    intro y
    rw [Finset.sum_comm]
    have hstep1 : ∀ enc₂ : Fin M₂ → Fin n → X₂,
        (∑ enc₁ : Fin M₁ → Fin n → X₁, (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) =
        codebookProb P₂ n M₂ enc₂ * ((∑ x₁, (iidDist P₁ n).pmf x₁ *
            (W.power n).trans (fun i => (x₁ i, enc₂ m₂ i)) y) *
          (∑ x₁', (iidDist P₁ n).pmf x₁' *
            (if (x₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) := fun enc₂ => by
      have hrw : ∀ enc₁ : Fin M₁ → Fin n → X₁,
          (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0)) =
          codebookProb P₂ n M₂ enc₂ * (codebookProb P₁ n M₁ enc₁ *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) := fun _ => by ring
      simp_rw [hrw, ← Finset.mul_sum]
      congr 1
      unfold codebookProb
      exact sum_pi_prod_mul_pair' (iidDist P₁ n) m₁ m₁' hne
        (fun x₁ => (W.power n).trans (fun i => (x₁ i, enc₂ m₂ i)) y)
        (fun x₁' => if (x₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0)
    rw [Finset.sum_congr rfl fun enc₂ _ => hstep1 enc₂]
    unfold codebookProb
    rw [sum_pi_prod_mul_single' (iidDist P₂ n) m₂
      (fun x₂ => (∑ x₁, (iidDist P₁ n).pmf x₁ *
          (W.power n).trans (fun i => (x₁ i, x₂ i)) y) *
        (∑ x₁', (iidDist P₁ n).pmf x₁' *
          (if (x₁', x₂, y) ∈ A then (1 : ℝ) else 0)))]
    refine Finset.sum_congr rfl fun x₂ _ => ?_
    have hmarg := mac_marginal_J2Y W P₁ P₂ n x₂ y
    dsimp only at hmarg
    rw [← mul_assoc, hmarg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₁' _ => by split_ifs <;> ring
  change ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂,
      (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
        ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
          (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0)) = _
  rw [Finset.sum_congr rfl fun y _ => hin y]
  have htot : (∑ y : Fin n → Y, ∑ x₂, ∑ x₁', if (x₁', x₂, y) ∈ A
        then (iidDist P₁ n).pmf x₁' * (iidDist J₂Y n).pmf (fun i => (x₂ i, y i)) else 0) =
      ∑ t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y),
        if t ∈ A then (iidDist P₁ n).pmf t.1 * (iidDist J₂Y n).pmf (fun i => (t.2.1 i, t.2.2 i))
        else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    trans (∑ y : Fin n → Y, ∑ x₁', ∑ x₂, if (x₁', x₂, y) ∈ A
        then (iidDist P₁ n).pmf x₁' * (iidDist J₂Y n).pmf (fun i => (x₂ i, y i)) else 0)
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [htot, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

private lemma mac_rc_term3 [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]
    (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (ε : ℝ) (m₁ : Fin M₁) (m₂ m₂' : Fin M₂) (hne : m₂' ≠ m₂) :
    let J := W.joint (P₁.prod P₂)
    let J₁Y := J.map (fun z => (z.1.1, z.2))
    let A := macTypicalSet W P₁ P₂ n ε
    (∑ y : Fin n → Y, ∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
      ∑ t ∈ A, (iidDist P₂ n).pmf t.2.1 * (iidDist J₁Y n).pmf (fun i => (t.1 i, t.2.2 i)) := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let J₁Y := J.map (fun z => (z.1.1, z.2))
  let A := macTypicalSet W P₁ P₂ n ε
  have hin : ∀ y : Fin n → Y,
      (∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
      ∑ x₁, ∑ x₂', if (x₁, x₂', y) ∈ A
        then (iidDist P₂ n).pmf x₂' * (iidDist J₁Y n).pmf (fun i => (x₁ i, y i)) else 0 := by
    intro y
    have hstep1 : ∀ enc₁ : Fin M₁ → Fin n → X₁,
        (∑ enc₂ : Fin M₂ → Fin n → X₂, (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
        codebookProb P₁ n M₁ enc₁ * ((∑ x₂, (iidDist P₂ n).pmf x₂ *
            (W.power n).trans (fun i => (enc₁ m₁ i, x₂ i)) y) *
          (∑ x₂', (iidDist P₂ n).pmf x₂' *
            (if (enc₁ m₁, x₂', y) ∈ A then (1 : ℝ) else 0))) := fun enc₁ => by
      have hrw : ∀ enc₂ : Fin M₂ → Fin n → X₂,
          (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) =
          codebookProb P₁ n M₁ enc₁ * (codebookProb P₂ n M₂ enc₂ *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) := fun _ => by ring
      simp_rw [hrw, ← Finset.mul_sum]
      congr 1
      unfold codebookProb
      exact sum_pi_prod_mul_pair' (iidDist P₂ n) m₂ m₂' hne
        (fun x₂ => (W.power n).trans (fun i => (enc₁ m₁ i, x₂ i)) y)
        (fun x₂' => if (enc₁ m₁, x₂', y) ∈ A then (1 : ℝ) else 0)
    rw [Finset.sum_congr rfl fun enc₁ _ => hstep1 enc₁]
    unfold codebookProb
    rw [sum_pi_prod_mul_single' (iidDist P₁ n) m₁
      (fun x₁ => (∑ x₂, (iidDist P₂ n).pmf x₂ *
          (W.power n).trans (fun i => (x₁ i, x₂ i)) y) *
        (∑ x₂', (iidDist P₂ n).pmf x₂' *
          (if (x₁, x₂', y) ∈ A then (1 : ℝ) else 0)))]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    have hmarg := mac_marginal_J1Y W P₁ P₂ n x₁ y
    dsimp only at hmarg
    rw [← mul_assoc, hmarg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₂' _ => by split_ifs <;> ring
  change ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂,
      (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
        ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
          (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) = _
  rw [Finset.sum_congr rfl fun y _ => hin y]
  have htot : (∑ y : Fin n → Y, ∑ x₁, ∑ x₂', if (x₁, x₂', y) ∈ A
        then (iidDist P₂ n).pmf x₂' * (iidDist J₁Y n).pmf (fun i => (x₁ i, y i)) else 0) =
      ∑ t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y),
        if t ∈ A then (iidDist P₂ n).pmf t.2.1 * (iidDist J₁Y n).pmf (fun i => (t.1 i, t.2.2 i))
        else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [htot, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

private lemma mac_rc_term4 [DecidableEq X₁] [DecidableEq X₂] [DecidableEq Y]
    (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (ε : ℝ) (m₁ m₁' : Fin M₁) (hne1 : m₁' ≠ m₁)
    (m₂ m₂' : Fin M₂) (hne2 : m₂' ≠ m₂) :
    let J := W.joint (P₁.prod P₂)
    let A := macTypicalSet W P₁ P₂ n ε
    (∑ y : Fin n → Y, ∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
      ∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 *
        (iidDist J.snd n).pmf t.2.2 := by
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let A := macTypicalSet W P₁ P₂ n ε
  have hin : ∀ y : Fin n → Y,
      (∑ enc₁ : Fin M₁ → Fin n → X₁, ∑ enc₂ : Fin M₂ → Fin n → X₂,
        (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
      ∑ x₁', ∑ x₂', if (x₁', x₂', y) ∈ A
        then (iidDist P₁ n).pmf x₁' * (iidDist P₂ n).pmf x₂' * (iidDist J.snd n).pmf y else 0 := by
    intro y
    have hstep1 : ∀ enc₁ : Fin M₁ → Fin n → X₁,
        (∑ enc₂ : Fin M₂ → Fin n → X₂, (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
        codebookProb P₁ n M₁ enc₁ * ((∑ x₂, (iidDist P₂ n).pmf x₂ *
            (W.power n).trans (fun i => (enc₁ m₁ i, x₂ i)) y) *
          (∑ x₂', (iidDist P₂ n).pmf x₂' *
            (if (enc₁ m₁', x₂', y) ∈ A then (1 : ℝ) else 0))) := fun enc₁ => by
      have hrw : ∀ enc₂ : Fin M₂ → Fin n → X₂,
          (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) =
          codebookProb P₁ n M₁ enc₁ * (codebookProb P₂ n M₂ enc₂ *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) := fun _ => by ring
      simp_rw [hrw, ← Finset.mul_sum]
      congr 1
      unfold codebookProb
      exact sum_pi_prod_mul_pair' (iidDist P₂ n) m₂ m₂' hne2
        (fun x₂ => (W.power n).trans (fun i => (enc₁ m₁ i, x₂ i)) y)
        (fun x₂' => if (enc₁ m₁', x₂', y) ∈ A then (1 : ℝ) else 0)
    rw [Finset.sum_congr rfl fun enc₁ _ => hstep1 enc₁]
    unfold codebookProb
    rw [sum_pi_prod_mul_pair' (iidDist P₁ n) m₁ m₁' hne1
      (fun x₁ => ∑ x₂, (iidDist P₂ n).pmf x₂ * (W.power n).trans (fun i => (x₁ i, x₂ i)) y)
      (fun x₁' => ∑ x₂', (iidDist P₂ n).pmf x₂' * (if (x₁', x₂', y) ∈ A then (1 : ℝ) else 0))]
    have hmarg : ∑ x₁, (iidDist P₁ n).pmf x₁ *
          (∑ x₂, (iidDist P₂ n).pmf x₂ * (W.power n).trans (fun i => (x₁ i, x₂ i)) y) =
        (iidDist J.snd n).pmf y := by
      rw [← mac_marginal_JY W P₁ P₂ n y]
      refine Finset.sum_congr rfl fun x₁ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x₂ _ => by ring
    rw [hmarg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₁' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x₂' _ => by split_ifs <;> ring
  change ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂,
      (codebookProb P₁ n M₁ enc₁ * codebookProb P₂ n M₂ enc₂) *
        ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
          (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) = _
  rw [Finset.sum_congr rfl fun y _ => hin y]
  have htot : (∑ y : Fin n → Y, ∑ x₁', ∑ x₂', if (x₁', x₂', y) ∈ A
        then (iidDist P₁ n).pmf x₁' * (iidDist P₂ n).pmf x₂' * (iidDist J.snd n).pmf y else 0) =
      ∑ t : (Fin n → X₁) × (Fin n → X₂) × (Fin n → Y),
        if t ∈ A then (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 *
          (iidDist J.snd n).pmf t.2.2 else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [htot, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

private lemma mul_four_sums_distrib {ι₁ ι₂ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a b c : ℝ) (f : ι₁ → ℝ) (g : ι₂ → ℝ) (h : ι₁ → ι₂ → ℝ) :
    (a * b) * (c + (∑ i ∈ s₁, f i) + (∑ j ∈ s₂, g j) + (∑ i ∈ s₁, ∑ j ∈ s₂, h i j)) =
      a * (b * c) + (∑ i ∈ s₁, a * (b * f i)) + (∑ j ∈ s₂, a * (b * g j)) +
        (∑ i ∈ s₁, ∑ j ∈ s₂, a * (b * h i j)) := by
  simp_rw [mul_add, Finset.mul_sum, mul_assoc]

private lemma sum_sum_sum_comm {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (F : α → β → ι → ℝ) :
    ∑ a : α, ∑ b : β, ∑ i : ι, F a b i = ∑ i : ι, ∑ a : α, ∑ b : β, F a b i := by
  trans (∑ a : α, ∑ i : ι, ∑ b : β, F a b i)
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  · exact Finset.sum_comm

private lemma sum_sum_finset_sum_comm {α β ι : Type*} [Fintype α] [Fintype β]
    (s : Finset ι) (F : α → β → ι → ℝ) :
    ∑ a : α, ∑ b : β, ∑ i ∈ s, F a b i = ∑ i ∈ s, ∑ a : α, ∑ b : β, F a b i := by
  trans (∑ a : α, ∑ i ∈ s, ∑ b : β, F a b i)
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  · exact Finset.sum_comm

/-- **Random-Coding Existence Bound for a Two-User DM-MAC** (Cover & Thomas, §15.3.2):
    for any product input `P₁ × P₂`, blocklength `n`, message counts `M₁, M₂ > 0`, and `ε : ℝ`,
    there exists a deterministic `(n, M₁, M₂)` MAC code satisfying
    `P_e ≤ (1 - P^n(A_ε^(n))) + (M₁ - 1) 2^(-n(I(X₁;Y|X₂)-3ε)) + (M₂ - 1) 2^(-n(I(X₂;Y|X₁)-3ε)) + (M₁ - 1)(M₂ - 1) 2^(-n(I(X₁,X₂;Y)-4ε))`. -/
theorem mac_random_coding_bound (W : MACChannel X₁ X₂ Y) (P₁ : ProbDist X₁) (P₂ : ProbDist X₂)
    (n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ) :
    let J := W.joint (P₁.prod P₂)
    ∃ (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
      (dec : (Fin n → Y) → Fin M₁ × Fin M₂),
      macAvgError W n M₁ M₂ enc₁ enc₂ dec ≤
        (1 - ∑ t ∈ macTypicalSet W P₁ P₂ n ε,
            (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t)) +
        ((M₁ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) - 3 * ε))) +
        ((M₂ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1))) - 3 * ε))) +
        ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo J - 4 * ε))) := by
  classical
  dsimp only
  let J := W.joint (P₁.prod P₂)
  let A := macTypicalSet W P₁ P₂ n ε
  let w₁ : (Fin M₁ → Fin n → X₁) → ℝ := codebookProb P₁ n M₁
  let w₂ : (Fin M₂ → Fin n → X₂) → ℝ := codebookProb P₂ n M₂
  let B : ℝ :=
    (1 - ∑ t ∈ A, (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t)) +
    ((M₁ - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) - 3 * ε))) +
    ((M₂ - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1))) - 3 * ε))) +
    ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo J - 4 * ε)))
  have hindep := macTypicalSet_indep_bounds W P₁ P₂ n ε
  dsimp only at hindep
  have hterm_m : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂),
      ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
        (∑ y : Fin n → Y,
          if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
          then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) ≤ B := by
    intro m₁ m₂
    have hpt : ∀ enc₁ enc₂,
        (w₁ enc₁ * w₂ enc₂) *
          (∑ y : Fin n → Y,
            if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
            then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) ≤
        (∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) +
        (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) +
        (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) +
        (∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
          ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) := by
      intro enc₁ enc₂
      rw [Finset.mul_sum]
      have hs2 : (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) =
          ∑ y : Fin n → Y, ∑ m₁' ∈ Finset.univ.erase m₁, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0)) := Finset.sum_comm
      have hs3 : (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
          ∑ y : Fin n → Y, ∑ m₂' ∈ Finset.univ.erase m₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) := Finset.sum_comm
      have hs4 : (∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
            ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
              ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
                (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
          ∑ y : Fin n → Y, ∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
            (w₁ enc₁ * w₂ enc₂) *
              ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
                (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) := by
        trans (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y, ∑ m₂' ∈ Finset.univ.erase m₂,
            (w₁ enc₁ * w₂ enc₂) *
              ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
                (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)))
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        · exact Finset.sum_comm
      rw [hs2, hs3, hs4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ => ?_
      have hind := macTypicalDec_err_indicator_le W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y m₁ m₂
      have hcoeff : 0 ≤ (w₁ enc₁ * w₂ enc₂) *
          (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y :=
        mul_nonneg (mul_nonneg (codebookProb_nonneg P₁ n M₁ enc₁)
          (codebookProb_nonneg P₂ n M₂ enc₂)) ((W.power n).nonneg _ y)
      have hmul := mul_le_mul_of_nonneg_left hind hcoeff
      have hlhs : (w₁ enc₁ * w₂ enc₂) *
            (if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
             then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
          ((w₁ enc₁ * w₂ enc₂) * (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y) *
            (if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
             then (1 : ℝ) else 0) := by split_ifs <;> ring
      have hrhs := mul_four_sums_distrib (Finset.univ.erase m₁) (Finset.univ.erase m₂)
        (w₁ enc₁ * w₂ enc₂) ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y)
        (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0)
        (fun m₁' => if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0)
        (fun m₂' => if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)
        (fun m₁' m₂' => if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)
      rw [hlhs, ← hrhs]
      exact hmul
    have hstep1 :
        ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
          (∑ y : Fin n → Y,
            if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
            then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) ≤
        (∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) +
        (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) +
        (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) +
        (∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
          ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) := by
      have hsum := Finset.sum_le_sum fun enc₁ (_ : enc₁ ∈ Finset.univ) =>
        Finset.sum_le_sum fun enc₂ (_ : enc₂ ∈ Finset.univ) => hpt enc₁ enc₂
      simp_rw [Finset.sum_add_distrib] at hsum
      have h1' : (∑ enc₁, ∑ enc₂, ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0))) =
          ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂, y) ∉ A then (1 : ℝ) else 0)) :=
        sum_sum_sum_comm _
      have h2' : (∑ enc₁, ∑ enc₂, ∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y,
            (w₁ enc₁ * w₂ enc₂) * ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) =
          ∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂,
            (w₁ enc₁ * w₂ enc₂) * ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0)) := by
        rw [sum_sum_finset_sum_comm]
        exact Finset.sum_congr rfl fun _ _ => sum_sum_sum_comm _
      have h3' : (∑ enc₁, ∑ enc₂, ∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y,
            (w₁ enc₁ * w₂ enc₂) * ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
          ∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂,
            (w₁ enc₁ * w₂ enc₂) * ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) := by
        rw [sum_sum_finset_sum_comm]
        exact Finset.sum_congr rfl fun _ _ => sum_sum_sum_comm _
      have h4' : (∑ enc₁, ∑ enc₂, ∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
            ∑ y : Fin n → Y, (w₁ enc₁ * w₂ enc₂) *
              ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
                (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
          ∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
            ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
              ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
                (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0)) := by
        rw [sum_sum_finset_sum_comm]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [sum_sum_finset_sum_comm]
        exact Finset.sum_congr rfl fun _ _ => sum_sum_sum_comm _
      rw [h1', h2', h3', h4'] at hsum
      exact hsum
    have hE1 := mac_rc_term1 W P₁ P₂ n M₁ M₂ ε m₁ m₂
    have hE2 : (∑ m₁' ∈ Finset.univ.erase m₁, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) ≤
        ((M₁ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) - 3 * ε))) := by
      have heach : ∀ m₁' ∈ Finset.univ.erase m₁,
          (∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂, y) ∈ A then (1 : ℝ) else 0))) =
          ∑ t ∈ A, (iidDist P₁ n).pmf t.1 *
            (iidDist (J.map (fun z => (z.1.2, z.2))) n).pmf (fun i => (t.2.1 i, t.2.2 i)) :=
        fun m₁' hm₁' => mac_rc_term2 W P₁ P₂ n M₁ M₂ ε m₁ m₁' (Finset.mem_erase.mp hm₁').1 m₂
      rw [Finset.sum_congr rfl heach, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ m₁), Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left hindep.1 (Nat.cast_nonneg _)
    have hE3 : (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
          ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
            (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) ≤
        ((M₂ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1))) - 3 * ε))) := by
      have heach : ∀ m₂' ∈ Finset.univ.erase m₂,
          (∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁, enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
          ∑ t ∈ A, (iidDist P₂ n).pmf t.2.1 *
            (iidDist (J.map (fun z => (z.1.1, z.2))) n).pmf (fun i => (t.1 i, t.2.2 i)) :=
        fun m₂' hm₂' => mac_rc_term3 W P₁ P₂ n M₁ M₂ ε m₁ m₂ m₂' (Finset.mem_erase.mp hm₂').1
      rw [Finset.sum_congr rfl heach, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ m₂), Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left hindep.2.1 (Nat.cast_nonneg _)
    have hE4 : (∑ m₁' ∈ Finset.univ.erase m₁, ∑ m₂' ∈ Finset.univ.erase m₂,
          ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) ≤
        ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo J - 4 * ε))) := by
      have hinner : ∀ m₁' ∈ Finset.univ.erase m₁,
          (∑ m₂' ∈ Finset.univ.erase m₂, ∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
              (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
          ((M₂ - 1 : ℕ) : ℝ) *
            (∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 *
              (iidDist J.snd n).pmf t.2.2) := fun m₁' hm₁' => by
        have heach : ∀ m₂' ∈ Finset.univ.erase m₂,
            (∑ y : Fin n → Y, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
              ((W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y *
                (if (enc₁ m₁', enc₂ m₂', y) ∈ A then (1 : ℝ) else 0))) =
            ∑ t ∈ A, (iidDist P₁ n).pmf t.1 * (iidDist P₂ n).pmf t.2.1 *
              (iidDist J.snd n).pmf t.2.2 :=
          fun m₂' hm₂' => mac_rc_term4 W P₁ P₂ n M₁ M₂ ε m₁ m₁' (Finset.mem_erase.mp hm₁').1
            m₂ m₂' (Finset.mem_erase.mp hm₂').1
        rw [Finset.sum_congr rfl heach, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ m₂), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ m₁), Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hindep.2.2 (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    dsimp only [B, w₁, w₂, J, A] at hE1 hE2 hE3 hE4 hstep1 ⊢
    linarith
  -- Average over `(m₁, m₂)` and pick the best deterministic codebook pair
  let w : ((Fin M₁ → Fin n → X₁) × (Fin M₂ → Fin n → X₂)) → ℝ := fun e => w₁ e.1 * w₂ e.2
  have hw0 : ∀ e, 0 ≤ w e := fun e =>
    mul_nonneg (codebookProb_nonneg P₁ n M₁ e.1) (codebookProb_nonneg P₂ n M₂ e.2)
  have hw1 : ∑ e, w e = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [w, ← Finset.mul_sum, w₂, codebookProb_sum_one P₂ n M₂, mul_one,
      w₁, codebookProb_sum_one P₁ n M₁]
  have hMne : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
  have hMpos : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hM₁ hM₂)
  have hexp_le : ∑ e : (Fin M₁ → Fin n → X₁) × (Fin M₂ → Fin n → X₂),
      w e * macAvgError W n M₁ M₂ e.1 e.2 (macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε e.1 e.2) ≤ B := by
    rw [Fintype.sum_prod_type]
    have havg : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
          macAvgError W n M₁ M₂ enc₁ enc₂ (macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂) =
        ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            (∑ y : Fin n → Y,
              if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
              then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) := by
      unfold macAvgError
      simp only [hMne, ↓reduceIte]
      have hpush : ∀ enc₁ enc₂, (w₁ enc₁ * w₂ enc₂) *
            (((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
              ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
                if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
                then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
          ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
            ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (w₁ enc₁ * w₂ enc₂) *
              (∑ y : Fin n → Y,
                if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
                then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) := by
        intro enc₁ enc₂
        rw [← mul_assoc, mul_comm (w₁ enc₁ * w₂ enc₂), mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl fun enc₁ _ => Finset.sum_congr rfl fun enc₂ _ => hpush enc₁ enc₂]
      rw [Finset.sum_congr rfl fun enc₁ _ => (Finset.mul_sum _ _ _).symm, ← Finset.mul_sum]
      congr 1
      trans (∑ enc₁, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
          (∑ y : Fin n → Y,
            if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
            then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0))
      · refine Finset.sum_congr rfl fun enc₁ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    change ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
        macAvgError W n M₁ M₂ enc₁ enc₂ (macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂) ≤ B
    rw [havg]
    calc ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
            (∑ y : Fin n → Y,
              if macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂ y ≠ (m₁, m₂)
              then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0)
      _ ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁, ∑ _m₂ : Fin M₂, B :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => hterm_m m₁ m₂)
            (by positivity)
      _ = ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (((M₁ * M₂ : ℕ) : ℝ) * B) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_mul, mul_assoc]
      _ = B := by field_simp [ne_of_gt hMpos]
  obtain ⟨⟨enc₁, enc₂⟩, he⟩ := exists_le_of_weighted_sum_le' w
    (fun e => macAvgError W n M₁ M₂ e.1 e.2 (macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε e.1 e.2))
    B hw0 hw1 hexp_le
  exact ⟨enc₁, enc₂, macTypicalDec W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε enc₁ enc₂, he⟩

/-- **Two-User MAC Achievability for Strictly Interior Pentagon Rate Pairs**
    (Cover & Thomas, Theorem 15.3.1; El Gamal–Kim, Theorem 4.3):
    for any product input `P₁ × P₂` and any `(R₁, R₂)` strictly inside `macPentagon W P₁ P₂`,
    `(R₁, R₂)` is operationally achievable over `W`. -/
theorem mac_achievability_pentagon (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) {R₁ R₂ : ℝ}
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (h1 : R₁ < condMutualInfo ((W.joint (P₁.prod P₂)).map (fun z => (z.1.1, z.2, z.1.2))))
    (h2 : R₂ < condMutualInfo ((W.joint (P₁.prod P₂)).map (fun z => (z.1.2, z.2, z.1.1))))
    (h12 : R₁ + R₂ < mutualInfo (W.joint (P₁.prod P₂))) :
    IsMACAchievable W R₁ R₂ := by
  refine ⟨hR₁0, hR₂0, fun δ hδ => ?_⟩
  let J := W.joint (P₁.prod P₂)
  let I₁ := condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2)))
  let I₂ := condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1)))
  let I₁₂ := mutualInfo J
  let ε : ℝ := min ((I₁ - R₁) / 4) (min ((I₂ - R₂) / 4) ((I₁₂ - (R₁ + R₂)) / 5))
  have hε : 0 < ε := by
    dsimp only [ε, I₁, I₂, I₁₂, J]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε1 : R₁ - (I₁ - 3 * ε) ≤ -ε := by
    have : ε ≤ (I₁ - R₁) / 4 := min_le_left _ _
    linarith
  have hε2 : R₂ - (I₂ - 3 * ε) ≤ -ε := by
    have : ε ≤ (I₂ - R₂) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hε12 : (R₁ + R₂) - (I₁₂ - 4 * ε) ≤ -ε := by
    have : ε ≤ (I₁₂ - (R₁ + R₂)) / 5 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  obtain ⟨N₁, hN₁⟩ := mac_aep_prob_tendsto_one W P₁ P₂ hε (show 0 < δ / 4 by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (1 / (δ / 4)) / ε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  obtain ⟨enc₁, enc₂, dec, hbound⟩ := mac_random_coding_bound W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε
  refine ⟨enc₁, enc₂, dec, ?_⟩
  have ht1 : 1 - ∑ t ∈ macTypicalSet W P₁ P₂ n ε,
      (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) ≤ δ / 4 := by
    have hprob := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    linarith
  have htail : (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ / 4 :=
    two_rpow_neg_le_of_ge hε (by linarith)
      (le_trans hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn))
  have hM₁_ub : ((M₁ - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) :=
    le_trans (Nat.cast_le.mpr (Nat.sub_le M₁ 1)) (max_one_floor_two_rpow_le n hR₁0)
  have hM₂_ub : ((M₂ - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) :=
    le_trans (Nat.cast_le.mpr (Nat.sub_le M₂ 1)) (max_one_floor_two_rpow_le n hR₂0)
  have ht2 : ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₁ - 3 * ε))) ≤ δ / 4 := by
    calc ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₁ - 3 * ε)))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (I₁ - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM₁_ub (by positivity)
      _ = (2 : ℝ) ^ ((n : ℝ) * (R₁ - (I₁ - 3 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have := mul_le_mul_of_nonneg_left hε1 (Nat.cast_nonneg n)
          linarith
      _ ≤ δ / 4 := htail
  have ht3 : ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₂ - 3 * ε))) ≤ δ / 4 := by
    calc ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₂ - 3 * ε)))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (I₂ - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM₂_ub (by positivity)
      _ = (2 : ℝ) ^ ((n : ℝ) * (R₂ - (I₂ - 3 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have := mul_le_mul_of_nonneg_left hε2 (Nat.cast_nonneg n)
          linarith
      _ ≤ δ / 4 := htail
  have ht4 : ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (I₁₂ - 4 * ε))) ≤ δ / 4 := by
    have hprod_ub : ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) := by
      have hm := mul_le_mul hM₁_ub hM₂_ub (Nat.cast_nonneg _) (by positivity)
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hm
      simpa [mul_add] using hm
    calc ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₁₂ - 4 * ε)))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) * (2 : ℝ) ^ (-((n : ℝ) * (I₁₂ - 4 * ε))) :=
          mul_le_mul_of_nonneg_right hprod_ub (by positivity)
      _ = (2 : ℝ) ^ ((n : ℝ) * ((R₁ + R₂) - (I₁₂ - 4 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have := mul_le_mul_of_nonneg_left hε12 (Nat.cast_nonneg n)
          linarith
      _ ≤ δ / 4 := htail
  dsimp only [I₁, I₂, I₁₂, J] at ht1 ht2 ht3 ht4
  linarith

private lemma isMACAchievable_zero [Nonempty X₁] [Nonempty X₂] (W : MACChannel X₁ X₂ Y) :
    IsMACAchievable W 0 0 := by
  classical
  refine ⟨le_rfl, le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))
  have hM₁ : M₁ = 1 := by dsimp only [M₁]; norm_num
  have hM₂ : M₂ = 1 := by dsimp only [M₂]; norm_num
  have h1pos : 0 < M₁ := by omega
  have h2pos : 0 < M₂ := by omega
  refine ⟨fun _ _ => Classical.arbitrary X₁, fun _ _ => Classical.arbitrary X₂,
    fun _ => (⟨0, h1pos⟩, ⟨0, h2pos⟩), ?_⟩
  have herr : macAvgError W n M₁ M₂ (fun _ _ => Classical.arbitrary X₁)
      (fun _ _ => Classical.arbitrary X₂) (fun _ => (⟨0, h1pos⟩, ⟨0, h2pos⟩)) = 0 := by
    unfold macAvgError
    have hne : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
    simp only [hne, ↓reduceIte]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ =>
      Finset.sum_eq_zero fun _ _ => ?_)
    have heq : (⟨0, h1pos⟩, ⟨0, h2pos⟩) = (m₁, m₂) := by
      ext <;> dsimp only <;> omega
    simp [heq]
  linarith

private lemma mac_achievability_axis1 (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) {R₁ : ℝ}
    (hR₁0 : 0 ≤ R₁)
    (h1 : R₁ < condMutualInfo ((W.joint (P₁.prod P₂)).map (fun z => (z.1.1, z.2, z.1.2)))) :
    IsMACAchievable W R₁ 0 := by
  refine ⟨hR₁0, le_rfl, fun δ hδ => ?_⟩
  let J := W.joint (P₁.prod P₂)
  let I₁ := condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2)))
  let ε : ℝ := (I₁ - R₁) / 4
  have hε : 0 < ε := by dsimp only [ε, I₁, J]; linarith
  obtain ⟨N₁, hN₁⟩ := mac_aep_prob_tendsto_one W P₁ P₂ hε (show 0 < δ / 2 by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (1 / (δ / 2)) / ε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂_eq : M₂ = 1 := by dsimp only [M₂]; norm_num
  have hM₂ : 0 < M₂ := by omega
  obtain ⟨enc₁, enc₂, dec, hbound⟩ := mac_random_coding_bound W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε
  refine ⟨enc₁, enc₂, dec, ?_⟩
  have hM₂sub : ((M₂ - 1 : ℕ) : ℝ) = 0 := by rw [hM₂_eq]; simp
  rw [hM₂sub, zero_mul, mul_zero, zero_mul, add_zero, add_zero] at hbound
  have ht1 : 1 - ∑ t ∈ macTypicalSet W P₁ P₂ n ε,
      (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) ≤ δ / 2 := by
    have hprob := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    linarith
  have htail : (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ / 2 :=
    two_rpow_neg_le_of_ge hε (by linarith)
      (le_trans hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn))
  have hM₁_ub : ((M₁ - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) :=
    le_trans (Nat.cast_le.mpr (Nat.sub_le M₁ 1)) (max_one_floor_two_rpow_le n hR₁0)
  have ht2 : ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₁ - 3 * ε))) ≤ δ / 2 := by
    calc ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₁ - 3 * ε)))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (I₁ - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM₁_ub (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε]; ring
      _ ≤ δ / 2 := htail
  dsimp only [I₁, J] at ht1 ht2
  linarith

private lemma mac_achievability_axis2 (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) {R₂ : ℝ}
    (hR₂0 : 0 ≤ R₂)
    (h2 : R₂ < condMutualInfo ((W.joint (P₁.prod P₂)).map (fun z => (z.1.2, z.2, z.1.1)))) :
    IsMACAchievable W 0 R₂ := by
  refine ⟨le_rfl, hR₂0, fun δ hδ => ?_⟩
  let J := W.joint (P₁.prod P₂)
  let I₂ := condMutualInfo (J.map (fun z => (z.1.2, z.2, z.1.1)))
  let ε : ℝ := (I₂ - R₂) / 4
  have hε : 0 < ε := by dsimp only [ε, I₂, J]; linarith
  obtain ⟨N₁, hN₁⟩ := mac_aep_prob_tendsto_one W P₁ P₂ hε (show 0 < δ / 2 by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (1 / (δ / 2)) / ε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁_eq : M₁ = 1 := by dsimp only [M₁]; norm_num
  have hM₁ : 0 < M₁ := by omega
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  obtain ⟨enc₁, enc₂, dec, hbound⟩ := mac_random_coding_bound W P₁ P₂ n M₁ M₂ hM₁ hM₂ ε
  refine ⟨enc₁, enc₂, dec, ?_⟩
  have hM₁sub : ((M₁ - 1 : ℕ) : ℝ) = 0 := by rw [hM₁_eq]; simp
  rw [hM₁sub, zero_mul, zero_mul, zero_mul, add_zero, add_zero] at hbound
  have ht1 : 1 - ∑ t ∈ macTypicalSet W P₁ P₂ n ε,
      (iidDist J n).pmf (macZipEquiv X₁ X₂ Y n t) ≤ δ / 2 := by
    have hprob := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    linarith
  have htail : (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ / 2 :=
    two_rpow_neg_le_of_ge hε (by linarith)
      (le_trans hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn))
  have hM₂_ub : ((M₂ - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) :=
    le_trans (Nat.cast_le.mpr (Nat.sub_le M₂ 1)) (max_one_floor_two_rpow_le n hR₂0)
  have ht3 : ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₂ - 3 * ε))) ≤ δ / 2 := by
    calc ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I₂ - 3 * ε)))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (I₂ - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM₂_ub (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε]; ring
      _ ≤ δ / 2 := htail
  dsimp only [I₂, J] at ht1 ht3
  linarith

private lemma macPentagon_subset_macOperationalRegion (W : MACChannel X₁ X₂ Y)
    (P₁ : ProbDist X₁) (P₂ : ProbDist X₂) :
    macPentagon W P₁ P₂ ⊆ macOperationalRegion W := by
  have : Nonempty X₁ := nonempty_of_probDist P₁
  have : Nonempty X₂ := nonempty_of_probDist P₂
  rintro ⟨R₁, R₂⟩ ⟨hR₁0, hR₂0, h1, h2, h12⟩
  rw [macOperationalRegion, Metric.mem_closure_iff]
  intro ε hε
  by_cases h10 : R₁ = 0
  · subst h10
    by_cases h20 : R₂ = 0
    · subst h20
      exact ⟨(0, 0), isMACAchievable_zero W, by simp [hε]⟩
    · have hR₂pos : 0 < R₂ := lt_of_le_of_ne hR₂0 (Ne.symm h20)
      let t := max 0 (R₂ - ε / 2)
      have ht0 : 0 ≤ t := le_max_left 0 _
      have htlt : t < R₂ := max_lt hR₂pos (by linarith)
      refine ⟨(0, t), mac_achievability_axis2 W P₁ P₂ ht0 (lt_of_lt_of_le htlt h2), ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [sub_self, abs_zero]
      have hdiff : |R₂ - t| ≤ ε / 2 := by
        rw [abs_of_nonneg (by linarith)]
        have : R₂ - ε / 2 ≤ t := le_max_right 0 _
        linarith
      exact max_lt hε (lt_of_le_of_lt hdiff (by linarith))
  · by_cases h20 : R₂ = 0
    · subst h20
      have hR₁pos : 0 < R₁ := lt_of_le_of_ne hR₁0 (Ne.symm h10)
      let t := max 0 (R₁ - ε / 2)
      have ht0 : 0 ≤ t := le_max_left 0 _
      have htlt : t < R₁ := max_lt hR₁pos (by linarith)
      refine ⟨(t, 0), mac_achievability_axis1 W P₁ P₂ ht0 (lt_of_lt_of_le htlt h1), ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [sub_self, abs_zero]
      have hdiff : |R₁ - t| ≤ ε / 2 := by
        rw [abs_of_nonneg (by linarith)]
        have : R₁ - ε / 2 ≤ t := le_max_right 0 _
        linarith
      exact max_lt (lt_of_le_of_lt hdiff (by linarith)) hε
    · have hR₁pos : 0 < R₁ := lt_of_le_of_ne hR₁0 (Ne.symm h10)
      have hR₂pos : 0 < R₂ := lt_of_le_of_ne hR₂0 (Ne.symm h20)
      let M : ℝ := max R₁ R₂
      have hMpos : 0 < M := lt_of_lt_of_le hR₁pos (le_max_left R₁ R₂)
      let η : ℝ := min (1 / 2) (ε / (2 * M))
      have hη_pos : 0 < η := lt_min (by norm_num) (by positivity)
      have hη_lt1 : η < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      let lam : ℝ := 1 - η
      have hlam0 : 0 < lam := by dsimp only [lam]; linarith
      have hlam1 : lam < 1 := by dsimp only [lam]; linarith
      refine ⟨(lam * R₁, lam * R₂), mac_achievability_pentagon W P₁ P₂
          (by positivity) (by positivity)
          (lt_of_lt_of_le (by nlinarith) h1)
          (lt_of_lt_of_le (by nlinarith) h2)
          (lt_of_lt_of_le (by nlinarith) h12), ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have hd1 : |R₁ - lam * R₁| < ε := by
        have hrew : R₁ - lam * R₁ = η * R₁ := by dsimp only [lam]; ring
        rw [hrew, abs_of_pos (mul_pos hη_pos hR₁pos)]
        have hηM : η ≤ ε / (2 * M) := min_le_right _ _
        have hle : η * R₁ ≤ (ε / (2 * M)) * M :=
          mul_le_mul hηM (le_max_left R₁ R₂) (le_of_lt hR₁pos) (by positivity)
        have hsimp : (ε / (2 * M)) * M = ε / 2 := by field_simp [ne_of_gt hMpos]
        linarith
      have hd2 : |R₂ - lam * R₂| < ε := by
        have hrew : R₂ - lam * R₂ = η * R₂ := by dsimp only [lam]; ring
        rw [hrew, abs_of_pos (mul_pos hη_pos hR₂pos)]
        have hηM : η ≤ ε / (2 * M) := min_le_right _ _
        have hle : η * R₂ ≤ (ε / (2 * M)) * M :=
          mul_le_mul hηM (le_max_right R₁ R₂) (le_of_lt hR₂pos) (by positivity)
        have hsimp : (ε / (2 * M)) * M = ε / 2 := by field_simp [ne_of_gt hMpos]
        linarith
      exact max_lt hd1 hd2

/-! #### 2.3 Time-Sharing Convexity of `macOperationalRegion` -/

/-- Downward monotonicity of `macAvgError` via random cyclic message shifts:
    from any `(n, L₁, L₂)` code with `0 < M₁ ≤ L₁` and `0 < M₂ ≤ L₂`, there exists an
    `(n, M₁, M₂)` subcode with average error at most that of the original code. -/
private lemma mac_subcode_le (W : MACChannel X₁ X₂ Y) {n M₁ M₂ L₁ L₂ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (h1 : M₁ ≤ L₁) (h2 : M₂ ≤ L₂)
    (enc₁ : Fin L₁ → Fin n → X₁) (enc₂ : Fin L₂ → Fin n → X₂)
    (dec : (Fin n → Y) → Fin L₁ × Fin L₂) :
    ∃ (enc₁' : Fin M₁ → Fin n → X₁) (enc₂' : Fin M₂ → Fin n → X₂)
      (dec' : (Fin n → Y) → Fin M₁ × Fin M₂),
      macAvgError W n M₁ M₂ enc₁' enc₂' dec' ≤ macAvgError W n L₁ L₂ enc₁ enc₂ dec := by
  classical
  have hL₁ : 0 < L₁ := lt_of_lt_of_le hM₁ h1
  have hL₂ : 0 < L₂ := lt_of_lt_of_le hM₂ h2
  let shift₁ : Fin L₁ → Fin M₁ → Fin L₁ := fun a m₁ => ⟨(m₁.1 + a.1) % L₁, Nat.mod_lt _ hL₁⟩
  let shift₂ : Fin L₂ → Fin M₂ → Fin L₂ := fun b m₂ => ⟨(m₂.1 + b.1) % L₂, Nat.mod_lt _ hL₂⟩
  let unshift₁ (a : Fin L₁) (u : Fin L₁) : Fin M₁ :=
    if h : (u.1 + L₁ - a.1) % L₁ < M₁ then ⟨(u.1 + L₁ - a.1) % L₁, h⟩ else ⟨0, hM₁⟩
  let unshift₂ (b : Fin L₂) (v : Fin L₂) : Fin M₂ :=
    if h : (v.1 + L₂ - b.1) % L₂ < M₂ then ⟨(v.1 + L₂ - b.1) % L₂, h⟩ else ⟨0, hM₂⟩
  have hunshift₁ : ∀ (a : Fin L₁) (m₁ : Fin M₁), unshift₁ a (shift₁ a m₁) = m₁ := by
    intro a m₁
    have hmod : ((m₁.1 + a.1) % L₁ + L₁ - a.1) % L₁ = m₁.1 := by
      have hm_lt : m₁.1 < L₁ := lt_of_lt_of_le m₁.2 h1
      by_cases hlt : m₁.1 + a.1 < L₁
      · rw [Nat.mod_eq_of_lt hlt]
        have heq : m₁.1 + a.1 + L₁ - a.1 = m₁.1 + L₁ := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hm_lt]
      · have hle : L₁ ≤ m₁.1 + a.1 := Nat.le_of_not_lt hlt
        have hlt2 : m₁.1 + a.1 - L₁ < L₁ := by omega
        have hmod1 : (m₁.1 + a.1) % L₁ = m₁.1 + a.1 - L₁ := by
          rw [← Nat.mod_eq_of_lt hlt2]
          conv_lhs => rw [show m₁.1 + a.1 = (m₁.1 + a.1 - L₁) + L₁ by omega]
          exact Nat.add_mod_right _ _
        rw [hmod1]
        have heq : m₁.1 + a.1 - L₁ + L₁ - a.1 = m₁.1 := by omega
        rw [heq, Nat.mod_eq_of_lt hm_lt]
    dsimp only [unshift₁, shift₁]
    rw [hmod]
    simp [m₁.2]
  have hunshift₂ : ∀ (b : Fin L₂) (m₂ : Fin M₂), unshift₂ b (shift₂ b m₂) = m₂ := by
    intro b m₂
    have hmod : ((m₂.1 + b.1) % L₂ + L₂ - b.1) % L₂ = m₂.1 := by
      have hm_lt : m₂.1 < L₂ := lt_of_lt_of_le m₂.2 h2
      by_cases hlt : m₂.1 + b.1 < L₂
      · rw [Nat.mod_eq_of_lt hlt]
        have heq : m₂.1 + b.1 + L₂ - b.1 = m₂.1 + L₂ := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hm_lt]
      · have hle : L₂ ≤ m₂.1 + b.1 := Nat.le_of_not_lt hlt
        have hlt2 : m₂.1 + b.1 - L₂ < L₂ := by omega
        have hmod1 : (m₂.1 + b.1) % L₂ = m₂.1 + b.1 - L₂ := by
          rw [← Nat.mod_eq_of_lt hlt2]
          conv_lhs => rw [show m₂.1 + b.1 = (m₂.1 + b.1 - L₂) + L₂ by omega]
          exact Nat.add_mod_right _ _
        rw [hmod1]
        have heq : m₂.1 + b.1 - L₂ + L₂ - b.1 = m₂.1 := by omega
        rw [heq, Nat.mod_eq_of_lt hm_lt]
    dsimp only [unshift₂, shift₂]
    rw [hmod]
    simp [m₂.2]
  let decS (ab : Fin L₁ × Fin L₂) (y : Fin n → Y) : Fin M₁ × Fin M₂ :=
    (unshift₁ ab.1 (dec y).1, unshift₂ ab.2 (dec y).2)
  let e : Fin L₁ → Fin L₂ → ℝ := fun u v =>
    ∑ y : Fin n → Y, if dec y ≠ (u, v) then (W.power n).trans (fun i => (enc₁ u i, enc₂ v i)) y else 0
  have hsub_le : ∀ ab : Fin L₁ × Fin L₂,
      macAvgError W n M₁ M₂ (fun m₁ => enc₁ (shift₁ ab.1 m₁)) (fun m₂ => enc₂ (shift₂ ab.2 m₂))
        (decS ab) ≤
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, e (shift₁ ab.1 m₁) (shift₂ ab.2 m₂) := by
    intro ⟨a, b⟩
    unfold macAvgError
    have hne : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
    simp only [hne, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
      Finset.sum_le_sum fun y _ => ?_) (by positivity)
    by_cases h : decS (a, b) y ≠ (m₁, m₂)
    · have hne_orig : dec y ≠ (shift₁ a m₁, shift₂ b m₂) := fun heq => h (by
        dsimp only [decS]; rw [heq, hunshift₁, hunshift₂])
      simp [h, hne_orig]
    · simp only [h, ↓reduceIte]
      split_ifs
      · exact (W.power n).nonneg _ y
      · exact le_rfl
  -- Average over uniform shifts `ab : Fin L₁ × Fin L₂`
  let w : Fin L₁ × Fin L₂ → ℝ := fun _ => (1 : ℝ) / ((L₁ * L₂ : ℕ) : ℝ)
  have hLpos : (0 : ℝ) < ((L₁ * L₂ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hL₁ hL₂)
  have hMpos : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hM₁ hM₂)
  have hw0 : ∀ ab, 0 ≤ w ab := fun _ => by positivity
  have hw1 : ∑ ab : Fin L₁ × Fin L₂, w ab = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [ne_of_gt hLpos]
  -- Bijection `a ↦ shift₁ a m₁` on `Fin L₁`
  have hbij₁ : ∀ m₁ : Fin M₁, Function.Bijective (fun a : Fin L₁ => shift₁ a m₁) := by
    intro m₁
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a₁ a₂ h => ?_, rfl⟩
    have hm_lt : m₁.1 < L₁ := lt_of_lt_of_le m₁.2 h1
    have hval : (m₁.1 + a₁.1) % L₁ = (m₁.1 + a₂.1) % L₁ := congrArg Fin.val h
    have h1' : ((m₁.1 + a₁.1) % L₁ + L₁ - m₁.1) % L₁ = a₁.1 := by
      by_cases hlt : m₁.1 + a₁.1 < L₁
      · rw [Nat.mod_eq_of_lt hlt, show m₁.1 + a₁.1 + L₁ - m₁.1 = a₁.1 + L₁ by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt a₁.2]
      · have hmod1 : (m₁.1 + a₁.1) % L₁ = m₁.1 + a₁.1 - L₁ := by
          have hlt2 : m₁.1 + a₁.1 - L₁ < L₁ := by omega
          rw [← Nat.mod_eq_of_lt hlt2]
          conv_lhs => rw [show m₁.1 + a₁.1 = (m₁.1 + a₁.1 - L₁) + L₁ by omega]
          exact Nat.add_mod_right _ _
        rw [hmod1, show m₁.1 + a₁.1 - L₁ + L₁ - m₁.1 = a₁.1 by omega, Nat.mod_eq_of_lt a₁.2]
    have h2' : ((m₁.1 + a₂.1) % L₁ + L₁ - m₁.1) % L₁ = a₂.1 := by
      by_cases hlt : m₁.1 + a₂.1 < L₁
      · rw [Nat.mod_eq_of_lt hlt, show m₁.1 + a₂.1 + L₁ - m₁.1 = a₂.1 + L₁ by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt a₂.2]
      · have hmod1 : (m₁.1 + a₂.1) % L₁ = m₁.1 + a₂.1 - L₁ := by
          have hlt2 : m₁.1 + a₂.1 - L₁ < L₁ := by omega
          rw [← Nat.mod_eq_of_lt hlt2]
          conv_lhs => rw [show m₁.1 + a₂.1 = (m₁.1 + a₂.1 - L₁) + L₁ by omega]
          exact Nat.add_mod_right _ _
        rw [hmod1, show m₁.1 + a₂.1 - L₁ + L₁ - m₁.1 = a₂.1 by omega, Nat.mod_eq_of_lt a₂.2]
    exact Fin.ext (by rw [← h1', ← h2', hval])
  have hbij₂ : ∀ m₂ : Fin M₂, Function.Bijective (fun b : Fin L₂ => shift₂ b m₂) := by
    intro m₂
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun b₁ b₂ h => ?_, rfl⟩
    have hm_lt : m₂.1 < L₂ := lt_of_lt_of_le m₂.2 h2
    have hval : (m₂.1 + b₁.1) % L₂ = (m₂.1 + b₂.1) % L₂ := congrArg Fin.val h
    have h1' : ((m₂.1 + b₁.1) % L₂ + L₂ - m₂.1) % L₂ = b₁.1 := by
      by_cases hlt : m₂.1 + b₁.1 < L₂
      · rw [Nat.mod_eq_of_lt hlt, show m₂.1 + b₁.1 + L₂ - m₂.1 = b₁.1 + L₂ by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt b₁.2]
      · have hmod1 : (m₂.1 + b₁.1) % L₂ = m₂.1 + b₁.1 - L₂ := by
          have hlt2 : m₂.1 + b₁.1 - L₂ < L₂ := by omega
          rw [← Nat.mod_eq_of_lt hlt2]
          conv_lhs => rw [show m₂.1 + b₁.1 = (m₂.1 + b₁.1 - L₂) + L₂ by omega]
          exact Nat.add_mod_right _ _
        rw [hmod1, show m₂.1 + b₁.1 - L₂ + L₂ - m₂.1 = b₁.1 by omega, Nat.mod_eq_of_lt b₁.2]
    have h2' : ((m₂.1 + b₂.1) % L₂ + L₂ - m₂.1) % L₂ = b₂.1 := by
      by_cases hlt : m₂.1 + b₂.1 < L₂
      · rw [Nat.mod_eq_of_lt hlt, show m₂.1 + b₂.1 + L₂ - m₂.1 = b₂.1 + L₂ by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt b₂.2]
      · have hmod1 : (m₂.1 + b₂.1) % L₂ = m₂.1 + b₂.1 - L₂ := by
          have hlt2 : m₂.1 + b₂.1 - L₂ < L₂ := by omega
          rw [← Nat.mod_eq_of_lt hlt2]
          conv_lhs => rw [show m₂.1 + b₂.1 = (m₂.1 + b₂.1 - L₂) + L₂ by omega]
          exact Nat.add_mod_right _ _
        rw [hmod1, show m₂.1 + b₂.1 - L₂ + L₂ - m₂.1 = b₂.1 by omega, Nat.mod_eq_of_lt b₂.2]
    exact Fin.ext (by rw [← h1', ← h2', hval])
  have havg_eq : ∑ ab : Fin L₁ × Fin L₂, w ab *
      (((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, e (shift₁ ab.1 m₁) (shift₂ ab.2 m₂)) =
      macAvgError W n L₁ L₂ enc₁ enc₂ dec := by
    have hLne : ¬ (L₁ = 0 ∨ L₂ = 0) := by omega
    unfold macAvgError
    simp only [hLne, ↓reduceIte, w]
    simp_rw [← Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    have hcomm : ∑ a : Fin L₁, ∑ b : Fin L₂, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
        e (shift₁ a m₁) (shift₂ b m₂) =
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ a : Fin L₁, ∑ b : Fin L₂,
          e (shift₁ a m₁) (shift₂ b m₂) := by
      trans (∑ a : Fin L₁, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ b : Fin L₂, e (shift₁ a m₁) (shift₂ b m₂))
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    rw [hcomm]
    have heach : ∀ m₁ m₂, ∑ a : Fin L₁, ∑ b : Fin L₂, e (shift₁ a m₁) (shift₂ b m₂) =
        ∑ u : Fin L₁, ∑ v : Fin L₂, e u v := by
      intro m₁ m₂
      rw [Fintype.sum_bijective (fun a => shift₁ a m₁) (hbij₁ m₁) _
        (fun u => ∑ v : Fin L₂, e u v) (fun a => Fintype.sum_bijective (fun b => shift₂ b m₂)
          (hbij₂ m₂) _ (fun v => e (shift₁ a m₁) v) (fun _ => rfl))]
    simp_rw [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMcast : ((M₁ * M₂ : ℕ) : ℝ) = (M₁ : ℝ) * (M₂ : ℝ) := Nat.cast_mul M₁ M₂
    rw [hMcast]
    have hM1ne : (M₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM₁)
    have hM2ne : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM₂)
    field_simp [hM1ne, hM2ne, ne_of_gt hLpos]
    rfl
  have hexp_le : ∑ ab : Fin L₁ × Fin L₂, w ab *
      macAvgError W n M₁ M₂ (fun m₁ => enc₁ (shift₁ ab.1 m₁)) (fun m₂ => enc₂ (shift₂ ab.2 m₂))
        (decS ab) ≤ macAvgError W n L₁ L₂ enc₁ enc₂ dec := by
    rw [← havg_eq]
    exact Finset.sum_le_sum fun ab _ => mul_le_mul_of_nonneg_left (hsub_le ab) (hw0 ab)
  obtain ⟨ab, hab⟩ := exists_le_of_weighted_sum_le' w
    (fun ab => macAvgError W n M₁ M₂ (fun m₁ => enc₁ (shift₁ ab.1 m₁))
      (fun m₂ => enc₂ (shift₂ ab.2 m₂)) (decS ab))
    (macAvgError W n L₁ L₂ enc₁ enc₂ dec) hw0 hw1 hexp_le
  exact ⟨fun m₁ => enc₁ (shift₁ ab.1 m₁), fun m₂ => enc₂ (shift₂ ab.2 m₂), decS ab, hab⟩

private def macSplitFin {γ : Type*} (n₁ n₂ : ℕ) :
    (Fin (n₁ + n₂) → γ) ≃ (Fin n₁ → γ) × (Fin n₂ → γ) where
  toFun := fun f => (fun i => f (Fin.castAdd n₂ i), fun j => f (Fin.natAdd n₁ j))
  invFun := fun fg => Fin.append fg.1 fg.2
  left_inv := fun f => by
    funext k
    refine Fin.addCases (fun i => by simp) (fun j => by simp) k
  right_inv := fun ⟨f, g⟩ => by
    ext k <;> simp

/-- Block concatenation (time-sharing) of two MAC codes of lengths `n₁` and `n₂`. -/
private lemma mac_concat_code (W : MACChannel X₁ X₂ Y) {n₁ n₂ K₁ K₂ K₁' K₂' : ℕ}
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hK₁' : 0 < K₁') (hK₂' : 0 < K₂')
    (enc₁ : Fin K₁ → Fin n₁ → X₁) (enc₂ : Fin K₂ → Fin n₁ → X₂)
    (dec : (Fin n₁ → Y) → Fin K₁ × Fin K₂)
    (enc₁' : Fin K₁' → Fin n₂ → X₁) (enc₂' : Fin K₂' → Fin n₂ → X₂)
    (dec' : (Fin n₂ → Y) → Fin K₁' × Fin K₂') :
    ∃ (e₁ : Fin (K₁ * K₁') → Fin (n₁ + n₂) → X₁)
      (e₂ : Fin (K₂ * K₂') → Fin (n₁ + n₂) → X₂)
      (d : (Fin (n₁ + n₂) → Y) → Fin (K₁ * K₁') × Fin (K₂ * K₂')),
      macAvgError W (n₁ + n₂) (K₁ * K₁') (K₂ * K₂') e₁ e₂ d ≤
        macAvgError W n₁ K₁ K₂ enc₁ enc₂ dec + macAvgError W n₂ K₁' K₂' enc₁' enc₂' dec' := by
  classical
  let eq₁ : Fin (K₁ * K₁') ≃ Fin K₁ × Fin K₁' := finProdFinEquiv.symm
  let eq₂ : Fin (K₂ * K₂') ≃ Fin K₂ × Fin K₂' := finProdFinEquiv.symm
  let e₁ : Fin (K₁ * K₁') → Fin (n₁ + n₂) → X₁ :=
    fun m => (macSplitFin n₁ n₂).symm (enc₁ (eq₁ m).1, enc₁' (eq₁ m).2)
  let e₂ : Fin (K₂ * K₂') → Fin (n₁ + n₂) → X₂ :=
    fun m => (macSplitFin n₁ n₂).symm (enc₂ (eq₂ m).1, enc₂' (eq₂ m).2)
  let d : (Fin (n₁ + n₂) → Y) → Fin (K₁ * K₁') × Fin (K₂ * K₂') := fun y =>
    let y12 := macSplitFin n₁ n₂ y
    let r1 := dec y12.1
    let r2 := dec' y12.2
    (eq₁.symm (r1.1, r2.1), eq₂.symm (r1.2, r2.2))
  refine ⟨e₁, e₂, d, ?_⟩
  have hne : ¬ (K₁ * K₁' = 0 ∨ K₂ * K₂' = 0) := by
    have := Nat.mul_pos hK₁ hK₁'
    have := Nat.mul_pos hK₂ hK₂'
    omega
  have hne1 : ¬ (K₁ = 0 ∨ K₂ = 0) := by omega
  have hne2 : ¬ (K₁' = 0 ∨ K₂' = 0) := by omega
  unfold macAvgError
  simp only [hne, hne1, hne2, ↓reduceIte]
  have htrans : ∀ (m₁ : Fin K₁ × Fin K₁') (m₂ : Fin K₂ × Fin K₂') (y₁ : Fin n₁ → Y) (y₂ : Fin n₂ → Y),
      (W.power (n₁ + n₂)).trans
        (fun i => (e₁ (eq₁.symm m₁) i, e₂ (eq₂.symm m₂) i)) ((macSplitFin n₁ n₂).symm (y₁, y₂)) =
      (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ *
      (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ := by
    intro m₁ m₂ y₁ y₂
    unfold DMC.power; dsimp only [e₁, e₂, macSplitFin]
    rw [Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => by simp
    · refine Finset.prod_congr rfl fun j _ => by simp
  have hsum_y : ∀ (m₁ : Fin K₁ × Fin K₁') (m₂ : Fin K₂ × Fin K₂'),
      (∑ y : Fin (n₁ + n₂) → Y,
        if d y ≠ (eq₁.symm m₁, eq₂.symm m₂)
        then (W.power (n₁ + n₂)).trans (fun i => (e₁ (eq₁.symm m₁) i, e₂ (eq₂.symm m₂) i)) y
        else 0) ≤
      (∑ y₁ : Fin n₁ → Y,
        if dec y₁ ≠ (m₁.1, m₂.1) then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) +
      (∑ y₂ : Fin n₂ → Y,
        if dec' y₂ ≠ (m₁.2, m₂.2) then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0) := by
    intro m₁ m₂
    rw [Fintype.sum_equiv (macSplitFin n₁ n₂) _
      (fun y12 : (Fin n₁ → Y) × (Fin n₂ → Y) =>
        if d ((macSplitFin n₁ n₂).symm y12) ≠ (eq₁.symm m₁, eq₂.symm m₂)
        then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y12.1 *
             (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y12.2
        else 0)
      (fun y => by
        have hy : (macSplitFin n₁ n₂).symm (macSplitFin n₁ n₂ y) = y := (macSplitFin n₁ n₂).symm_apply_apply y
        rw [← htrans m₁ m₂ (macSplitFin n₁ n₂ y).1 (macSplitFin n₁ n₂ y).2, hy])]
    rw [Fintype.sum_prod_type]
    have hpt : ∀ y₁ y₂,
        (if d ((macSplitFin n₁ n₂).symm (y₁, y₂)) ≠ (eq₁.symm m₁, eq₂.symm m₂)
         then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ *
              (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂
         else 0) ≤
        (if dec y₁ ≠ (m₁.1, m₂.1) then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) *
          (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ +
        (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ *
          (if dec' y₂ ≠ (m₁.2, m₂.2) then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0) := by
      intro y₁ y₂
      have hw1 := (W.power n₁).nonneg (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁
      have hw2 := (W.power n₂).nonneg (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂
      by_cases h1 : dec y₁ = (m₁.1, m₂.1)
      · by_cases h2 : dec' y₂ = (m₁.2, m₂.2)
        · have hd : d ((macSplitFin n₁ n₂).symm (y₁, y₂)) = (eq₁.symm m₁, eq₂.symm m₂) := by
            dsimp only [d]; rw [(macSplitFin n₁ n₂).apply_symm_apply, h1, h2]
          simp [hd, h1, h2]
        · simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, zero_mul, zero_add]
          split_ifs <;> nlinarith
      · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte]
        split_ifs <;> nlinarith
    calc ∑ y₁, ∑ y₂, (if d ((macSplitFin n₁ n₂).symm (y₁, y₂)) ≠ (eq₁.symm m₁, eq₂.symm m₂)
            then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ *
                 (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂
            else 0)
      _ ≤ ∑ y₁, ∑ y₂,
            ((if dec y₁ ≠ (m₁.1, m₂.1) then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) *
              (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ +
             (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ *
              (if dec' y₂ ≠ (m₁.2, m₂.2) then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0)) :=
          Finset.sum_le_sum fun y₁ _ => Finset.sum_le_sum fun y₂ _ => hpt y₁ y₂
      _ = (∑ y₁, ∑ y₂, (if dec y₁ ≠ (m₁.1, m₂.1) then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) *
              (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂) +
          (∑ y₁, ∑ y₂, (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ *
              (if dec' y₂ ≠ (m₁.2, m₂.2) then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0)) := by
          simp_rw [Finset.sum_add_distrib]
      _ = (∑ y₁, if dec y₁ ≠ (m₁.1, m₂.1) then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) +
          (∑ y₂, if dec' y₂ ≠ (m₁.2, m₂.2) then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0) := by
          congr 1
          · refine Finset.sum_congr rfl fun y₁ _ => ?_
            rw [← Finset.mul_sum, (W.power n₂).sum_one, mul_one]
          · rw [← Finset.sum_mul_sum, (W.power n₁).sum_one, one_mul]
  -- Now reindex the outer message sums via `eq₁`, `eq₂`
  have houter :
      (∑ m₁ : Fin (K₁ * K₁'), ∑ m₂ : Fin (K₂ * K₂'), ∑ y : Fin (n₁ + n₂) → Y,
        if d y ≠ (m₁, m₂) then (W.power (n₁ + n₂)).trans (fun i => (e₁ m₁ i, e₂ m₂ i)) y else 0) ≤
      ((K₁' * K₂' : ℕ) : ℝ) * (∑ a₁ : Fin K₁, ∑ a₂ : Fin K₂, ∑ y₁ : Fin n₁ → Y,
        if dec y₁ ≠ (a₁, a₂) then (W.power n₁).trans (fun i => (enc₁ a₁ i, enc₂ a₂ i)) y₁ else 0) +
      ((K₁ * K₂ : ℕ) : ℝ) * (∑ b₁ : Fin K₁', ∑ b₂ : Fin K₂', ∑ y₂ : Fin n₂ → Y,
        if dec' y₂ ≠ (b₁, b₂) then (W.power n₂).trans (fun j => (enc₁' b₁ j, enc₂' b₂ j)) y₂ else 0) := by
    rw [Fintype.sum_equiv eq₁ _ (fun m₁ : Fin K₁ × Fin K₁' =>
        ∑ m₂ : Fin K₂ × Fin K₂', ∑ y : Fin (n₁ + n₂) → Y,
          if d y ≠ (eq₁.symm m₁, eq₂.symm m₂)
          then (W.power (n₁ + n₂)).trans (fun i => (e₁ (eq₁.symm m₁) i, e₂ (eq₂.symm m₂) i)) y
          else 0)
      (fun m₁ => by
        rw [eq₁.symm_apply_apply]
        exact Fintype.sum_equiv eq₂ _ _ (fun m₂ => by rw [eq₂.symm_apply_apply]))]
    calc ∑ m₁ : Fin K₁ × Fin K₁', ∑ m₂ : Fin K₂ × Fin K₂', ∑ y : Fin (n₁ + n₂) → Y,
          if d y ≠ (eq₁.symm m₁, eq₂.symm m₂)
          then (W.power (n₁ + n₂)).trans (fun i => (e₁ (eq₁.symm m₁) i, e₂ (eq₂.symm m₂) i)) y
          else 0
      _ ≤ ∑ m₁ : Fin K₁ × Fin K₁', ∑ m₂ : Fin K₂ × Fin K₂',
            ((∑ y₁ : Fin n₁ → Y, if dec y₁ ≠ (m₁.1, m₂.1)
                then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) +
             (∑ y₂ : Fin n₂ → Y, if dec' y₂ ≠ (m₁.2, m₂.2)
                then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0)) :=
          Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => hsum_y m₁ m₂
      _ = (∑ m₁ : Fin K₁ × Fin K₁', ∑ m₂ : Fin K₂ × Fin K₂', ∑ y₁ : Fin n₁ → Y,
            if dec y₁ ≠ (m₁.1, m₂.1) then (W.power n₁).trans (fun i => (enc₁ m₁.1 i, enc₂ m₂.1 i)) y₁ else 0) +
          (∑ m₁ : Fin K₁ × Fin K₁', ∑ m₂ : Fin K₂ × Fin K₂', ∑ y₂ : Fin n₂ → Y,
            if dec' y₂ ≠ (m₁.2, m₂.2) then (W.power n₂).trans (fun j => (enc₁' m₁.2 j, enc₂' m₂.2 j)) y₂ else 0) := by
          simp_rw [Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          · rw [Fintype.sum_prod_type]
            have h1 : ∀ a₁ : Fin K₁, (∑ _b₁ : Fin K₁', ∑ m₂ : Fin K₂ × Fin K₂',
                ∑ y₁ : Fin n₁ → Y, if dec y₁ ≠ (a₁, m₂.1)
                  then (W.power n₁).trans (fun i => (enc₁ a₁ i, enc₂ m₂.1 i)) y₁ else 0) =
                (K₁' : ℝ) * ((K₂' : ℝ) * ∑ a₂ : Fin K₂, ∑ y₁ : Fin n₁ → Y,
                  if dec y₁ ≠ (a₁, a₂)
                  then (W.power n₁).trans (fun i => (enc₁ a₁ i, enc₂ a₂ i)) y₁ else 0) := fun a₁ => by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              congr 1
              rw [Fintype.sum_prod_type]
              simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← Finset.mul_sum]
            rw [Finset.sum_congr rfl fun a₁ _ => h1 a₁, ← Finset.mul_sum, ← Finset.mul_sum,
                ← mul_assoc, Nat.cast_mul]
          · rw [Fintype.sum_prod_type_right]
            have h2 : ∀ b₁ : Fin K₁', (∑ _a₁ : Fin K₁, ∑ m₂ : Fin K₂ × Fin K₂',
                ∑ y₂ : Fin n₂ → Y, if dec' y₂ ≠ (b₁, m₂.2)
                  then (W.power n₂).trans (fun j => (enc₁' b₁ j, enc₂' m₂.2 j)) y₂ else 0) =
                (K₁ : ℝ) * ((K₂ : ℝ) * ∑ b₂ : Fin K₂', ∑ y₂ : Fin n₂ → Y,
                  if dec' y₂ ≠ (b₁, b₂)
                  then (W.power n₂).trans (fun j => (enc₁' b₁ j, enc₂' b₂ j)) y₂ else 0) := fun b₁ => by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              congr 1
              rw [Fintype.sum_prod_type_right]
              simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← Finset.mul_sum]
            rw [Finset.sum_congr rfl fun b₁ _ => h2 b₁, ← Finset.mul_sum, ← Finset.mul_sum,
                ← mul_assoc, Nat.cast_mul]
  have hKpos : (0 : ℝ) < ((K₁ * K₁' * (K₂ * K₂') : ℕ) : ℝ) := by positivity
  have hK1pos : (0 : ℝ) < ((K₁ * K₂ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hK₁ hK₂)
  have hK2pos : (0 : ℝ) < ((K₁' * K₂' : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hK₁' hK₂')
  have hmul := mul_le_mul_of_nonneg_left houter (show 0 ≤ (1 : ℝ) / ((K₁ * K₁' * (K₂ * K₂') : ℕ) : ℝ) by positivity)
  have hrhs : (1 : ℝ) / ((K₁ * K₁' * (K₂ * K₂') : ℕ) : ℝ) *
      (((K₁' * K₂' : ℕ) : ℝ) * (∑ a₁ : Fin K₁, ∑ a₂ : Fin K₂, ∑ y₁ : Fin n₁ → Y,
        if dec y₁ ≠ (a₁, a₂) then (W.power n₁).trans (fun i => (enc₁ a₁ i, enc₂ a₂ i)) y₁ else 0) +
       ((K₁ * K₂ : ℕ) : ℝ) * (∑ b₁ : Fin K₁', ∑ b₂ : Fin K₂', ∑ y₂ : Fin n₂ → Y,
        if dec' y₂ ≠ (b₁, b₂) then (W.power n₂).trans (fun j => (enc₁' b₁ j, enc₂' b₂ j)) y₂ else 0)) =
      (1 : ℝ) / ((K₁ * K₂ : ℕ) : ℝ) * (∑ a₁ : Fin K₁, ∑ a₂ : Fin K₂, ∑ y₁ : Fin n₁ → Y,
        if dec y₁ ≠ (a₁, a₂) then (W.power n₁).trans (fun i => (enc₁ a₁ i, enc₂ a₂ i)) y₁ else 0) +
      (1 : ℝ) / ((K₁' * K₂' : ℕ) : ℝ) * (∑ b₁ : Fin K₁', ∑ b₂ : Fin K₂', ∑ y₂ : Fin n₂ → Y,
        if dec' y₂ ≠ (b₁, b₂) then (W.power n₂).trans (fun j => (enc₁' b₁ j, enc₂' b₂ j)) y₂ else 0) := by
    have hprod_eq : ((K₁ * K₁' * (K₂ * K₂') : ℕ) : ℝ) =
        ((K₁ * K₂ : ℕ) : ℝ) * ((K₁' * K₂' : ℕ) : ℝ) := by push_cast; ring
    rw [hprod_eq]
    field_simp [ne_of_gt hK1pos, ne_of_gt hK2pos]
  linarith

/-- Time-sharing between two achievable MAC rate pairs: any convex combination lies in
    `macOperationalRegion W`. -/
private lemma mac_time_sharing (W : MACChannel X₁ X₂ Y) {R₁ R₂ R₁' R₂' t : ℝ}
    (h : IsMACAchievable W R₁ R₂) (h' : IsMACAchievable W R₁' R₂')
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) * R₁ + t * R₁', (1 - t) * R₂ + t * R₂') ∈ macOperationalRegion W := by
  by_cases h0 : t = 0
  · subst h0
    have heq : ((1 - (0 : ℝ)) * R₁ + 0 * R₁', (1 - (0 : ℝ)) * R₂ + 0 * R₂') = (R₁, R₂) := by
      ext <;> ring
    rw [heq]; exact subset_closure h
  · by_cases h1 : t = 1
    · subst h1
      have heq : ((1 - (1 : ℝ)) * R₁ + 1 * R₁', (1 - (1 : ℝ)) * R₂ + 1 * R₂') = (R₁', R₂') := by
        ext <;> ring
      rw [heq]; exact subset_closure h'
    · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
      have h1mt_pos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 h1)
      let S₁ : ℝ := (1 - t) * R₁ + t * R₁'
      let S₂ : ℝ := (1 - t) * R₂ + t * R₂'
      have hS₁0 : 0 ≤ S₁ := by dsimp only [S₁]; nlinarith [h.1, h'.1]
      have hS₂0 : 0 ≤ S₂ := by dsimp only [S₂]; nlinarith [h.2.1, h'.2.1]
      -- Show any `(s₁, s₂)` with `0 ≤ s₁`, `s₁ = 0 ∨ s₁ < S₁`, `0 ≤ s₂`, `s₂ = 0 ∨ s₂ < S₂` is achievable
      have hach : ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → 0 ≤ s₂ → (s₁ = 0 ∨ s₁ < S₁) → (s₂ = 0 ∨ s₂ < S₂) →
          IsMACAchievable W s₁ s₂ := by
        intro s₁ s₂ hs₁0 hs₂0 hs₁ hs₂
        refine ⟨hs₁0, hs₂0, fun δ hδ => ?_⟩
        obtain ⟨N₁, hN₁⟩ := h.2.2 (δ / 2) (by linarith)
        obtain ⟨N₂, hN₂⟩ := h'.2.2 (δ / 2) (by linarith)
        obtain ⟨Na, hNa⟩ := exists_nat_ge (((N₁ : ℝ) + 1) / (1 - t))
        obtain ⟨Nb, hNb⟩ := exists_nat_ge ((N₂ : ℝ) / t)
        obtain ⟨Nc, hNc⟩ := exists_nat_ge (if S₁ - s₁ > 0 then (R₁ + 2) / (S₁ - s₁) else 0)
        obtain ⟨Nd, hNd⟩ := exists_nat_ge (if S₂ - s₂ > 0 then (R₂ + 2) / (S₂ - s₂) else 0)
        refine ⟨max (max Na Nb) (max Nc Nd), fun n hn => ?_⟩
        dsimp only
        let n₁ : ℕ := Nat.floor ((1 - t) * (n : ℝ))
        let n₂ : ℕ := n - n₁
        have hn₁_le_n : n₁ ≤ n := by
          have hle : (1 - t) * (n : ℝ) ≤ (n : ℝ) := by nlinarith
          exact Nat.floor_le_of_le (by exact_mod_cast hle)
        have hn_eq : n₁ + n₂ = n := Nat.add_sub_cancel' hn₁_le_n
        have hn₁_ge : N₁ ≤ n₁ := by
          have h1' : ((N₁ : ℝ) + 1) / (1 - t) ≤ (n : ℝ) :=
            le_trans hNa (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
          have h2' : (N₁ : ℝ) + 1 ≤ (1 - t) * (n : ℝ) := by
            linarith [(div_le_iff₀ h1mt_pos).mp h1']
          have h3' : (N₁ : ℝ) ≤ (n₁ : ℝ) := by
            have := Nat.lt_floor_add_one ((1 - t) * (n : ℝ))
            linarith
          exact_mod_cast h3'
        have hn₂_ge : N₂ ≤ n₂ := by
          have h1' : (N₂ : ℝ) / t ≤ (n : ℝ) :=
            le_trans hNb (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
          have h2' : (N₂ : ℝ) ≤ t * (n : ℝ) := by
            linarith [(div_le_iff₀ ht_pos).mp h1']
          have h3' : (n₁ : ℝ) ≤ (1 - t) * (n : ℝ) := Nat.floor_le (by positivity)
          have h4' : (N₂ : ℝ) ≤ (n₂ : ℝ) := by
            have hcast : (n₂ : ℝ) = (n : ℝ) - (n₁ : ℝ) := Nat.cast_sub hn₁_le_n
            linarith
          exact_mod_cast h4'
        obtain ⟨enc₁, enc₂, dec, herr₁⟩ := hN₁ n₁ hn₁_ge
        obtain ⟨enc₁', enc₂', dec', herr₂⟩ := hN₂ n₂ hn₂_ge
        let K₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n₁ : ℝ) * R₁)))
        let K₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n₁ : ℝ) * R₂)))
        let K₁' := max 1 (Nat.floor ((2 : ℝ) ^ ((n₂ : ℝ) * R₁')))
        let K₂' := max 1 (Nat.floor ((2 : ℝ) ^ ((n₂ : ℝ) * R₂')))
        have hK₁ : 0 < K₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
        have hK₂ : 0 < K₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
        have hK₁' : 0 < K₁' := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
        have hK₂' : 0 < K₂' := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
        let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * s₁)))
        let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * s₂)))
        have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
        have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
        have hM₁_le : M₁ ≤ K₁ * K₁' := by
          rcases hs₁ with rfl | hlt
          · have hM1 : M₁ = 1 := by dsimp only [M₁]; norm_num
            rw [hM1]; exact Nat.mul_pos hK₁ hK₁'
          · have hgap : 0 < S₁ - s₁ := by linarith
            have hnc : (R₁ + 2) / (S₁ - s₁) ≤ (n : ℝ) := by
              have hle_n : (Nc : ℝ) ≤ (n : ℝ) :=
                Nat.cast_le.mpr (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
              have h0' := le_trans hNc hle_n
              simpa [hgap] using h0'
            have hexp_le : (n : ℝ) * s₁ ≤ (n₁ : ℝ) * R₁ + (n₂ : ℝ) * R₁' - 2 := by
              have h1' : R₁ + 2 ≤ (n : ℝ) * (S₁ - s₁) := (div_le_iff₀ hgap).mp hnc
              have hn₁_lb : (1 - t) * (n : ℝ) - 1 ≤ (n₁ : ℝ) := by
                linarith [Nat.lt_floor_add_one ((1 - t) * (n : ℝ))]
              have hn₂_lb : t * (n : ℝ) ≤ (n₂ : ℝ) := by
                have hcast : (n₂ : ℝ) = (n : ℝ) - (n₁ : ℝ) := Nat.cast_sub hn₁_le_n
                have hfl : (n₁ : ℝ) ≤ (1 - t) * (n : ℝ) := Nat.floor_le (by positivity)
                linarith
              have hmul1 : ((1 - t) * (n : ℝ) - 1) * R₁ ≤ (n₁ : ℝ) * R₁ :=
                mul_le_mul_of_nonneg_right hn₁_lb h.1
              have hmul2 : (t * (n : ℝ)) * R₁' ≤ (n₂ : ℝ) * R₁' :=
                mul_le_mul_of_nonneg_right hn₂_lb h'.1
              dsimp only [S₁] at h1'
              linarith
            have hpow_le : (2 : ℝ) ^ ((n : ℝ) * s₁) ≤ ((K₁ * K₁' : ℕ) : ℝ) := by
              have hk1 := half_two_rpow_le_max_one_floor n₁ h.1
              have hk1' := half_two_rpow_le_max_one_floor n₂ h'.1
              have hprod : ((2 : ℝ) ^ ((n₁ : ℝ) * R₁) / 2) * ((2 : ℝ) ^ ((n₂ : ℝ) * R₁') / 2) ≤
                  (K₁ : ℝ) * (K₁' : ℝ) :=
                mul_le_mul hk1 hk1' (by positivity) (Nat.cast_nonneg _)
              have heq : ((2 : ℝ) ^ ((n₁ : ℝ) * R₁) / 2) * ((2 : ℝ) ^ ((n₂ : ℝ) * R₁') / 2) =
                  (2 : ℝ) ^ ((n₁ : ℝ) * R₁ + (n₂ : ℝ) * R₁' - 2) := by
                rw [div_mul_div_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                    Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
                norm_num
              have hmono : (2 : ℝ) ^ ((n : ℝ) * s₁) ≤
                  (2 : ℝ) ^ ((n₁ : ℝ) * R₁ + (n₂ : ℝ) * R₁' - 2) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
              rw [Nat.cast_mul]
              linarith
            have hfl_le : Nat.floor ((2 : ℝ) ^ ((n : ℝ) * s₁)) ≤ K₁ * K₁' :=
              Nat.floor_le_of_le hpow_le
            exact max_le (Nat.mul_pos hK₁ hK₁') hfl_le
        have hM₂_le : M₂ ≤ K₂ * K₂' := by
          rcases hs₂ with rfl | hlt
          · have hM2 : M₂ = 1 := by dsimp only [M₂]; norm_num
            rw [hM2]; exact Nat.mul_pos hK₂ hK₂'
          · have hgap : 0 < S₂ - s₂ := by linarith
            have hnd : (R₂ + 2) / (S₂ - s₂) ≤ (n : ℝ) := by
              have hle_n : (Nd : ℝ) ≤ (n : ℝ) :=
                Nat.cast_le.mpr (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
              have h0' := le_trans hNd hle_n
              simpa [hgap] using h0'
            have hexp_le : (n : ℝ) * s₂ ≤ (n₁ : ℝ) * R₂ + (n₂ : ℝ) * R₂' - 2 := by
              have h1' : R₂ + 2 ≤ (n : ℝ) * (S₂ - s₂) := (div_le_iff₀ hgap).mp hnd
              have hn₁_lb : (1 - t) * (n : ℝ) - 1 ≤ (n₁ : ℝ) := by
                linarith [Nat.lt_floor_add_one ((1 - t) * (n : ℝ))]
              have hn₂_lb : t * (n : ℝ) ≤ (n₂ : ℝ) := by
                have hcast : (n₂ : ℝ) = (n : ℝ) - (n₁ : ℝ) := Nat.cast_sub hn₁_le_n
                have hfl : (n₁ : ℝ) ≤ (1 - t) * (n : ℝ) := Nat.floor_le (by positivity)
                linarith
              have hmul1 : ((1 - t) * (n : ℝ) - 1) * R₂ ≤ (n₁ : ℝ) * R₂ :=
                mul_le_mul_of_nonneg_right hn₁_lb h.2.1
              have hmul2 : (t * (n : ℝ)) * R₂' ≤ (n₂ : ℝ) * R₂' :=
                mul_le_mul_of_nonneg_right hn₂_lb h'.2.1
              dsimp only [S₂] at h1'
              linarith
            have hpow_le : (2 : ℝ) ^ ((n : ℝ) * s₂) ≤ ((K₂ * K₂' : ℕ) : ℝ) := by
              have hk2 := half_two_rpow_le_max_one_floor n₁ h.2.1
              have hk2' := half_two_rpow_le_max_one_floor n₂ h'.2.1
              have hprod : ((2 : ℝ) ^ ((n₁ : ℝ) * R₂) / 2) * ((2 : ℝ) ^ ((n₂ : ℝ) * R₂') / 2) ≤
                  (K₂ : ℝ) * (K₂' : ℝ) :=
                mul_le_mul hk2 hk2' (by positivity) (Nat.cast_nonneg _)
              have heq : ((2 : ℝ) ^ ((n₁ : ℝ) * R₂) / 2) * ((2 : ℝ) ^ ((n₂ : ℝ) * R₂') / 2) =
                  (2 : ℝ) ^ ((n₁ : ℝ) * R₂ + (n₂ : ℝ) * R₂' - 2) := by
                rw [div_mul_div_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                    Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
                norm_num
              have hmono : (2 : ℝ) ^ ((n : ℝ) * s₂) ≤
                  (2 : ℝ) ^ ((n₁ : ℝ) * R₂ + (n₂ : ℝ) * R₂' - 2) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
              rw [Nat.cast_mul]
              linarith
            have hfl_le : Nat.floor ((2 : ℝ) ^ ((n : ℝ) * s₂)) ≤ K₂ * K₂' :=
              Nat.floor_le_of_le hpow_le
            exact max_le (Nat.mul_pos hK₂ hK₂') hfl_le
        obtain ⟨e₁, e₂, d, hcat⟩ := mac_concat_code W hK₁ hK₂ hK₁' hK₂' enc₁ enc₂ dec enc₁' enc₂' dec'
        obtain ⟨f₁, f₂, g, hsub⟩ := mac_subcode_le W hM₁ hM₂ hM₁_le hM₂_le e₁ e₂ d
        have hcode : ∃ (f₁ : Fin M₁ → Fin (n₁ + n₂) → X₁) (f₂ : Fin M₂ → Fin (n₁ + n₂) → X₂)
            (g : (Fin (n₁ + n₂) → Y) → Fin M₁ × Fin M₂),
            macAvgError W (n₁ + n₂) M₁ M₂ f₁ f₂ g ≤ δ := ⟨f₁, f₂, g, by linarith⟩
        rw [hn_eq] at hcode
        exact hcode
      -- Approximate `(S₁, S₂)` from below
      rw [macOperationalRegion, Metric.mem_closure_iff]
      intro ε hε
      let s₁ : ℝ := if S₁ = 0 then 0 else max 0 (S₁ - ε / 2)
      let s₂ : ℝ := if S₂ = 0 then 0 else max 0 (S₂ - ε / 2)
      have hs₁0 : 0 ≤ s₁ := by dsimp only [s₁]; split_ifs; exact le_rfl; exact le_max_left 0 _
      have hs₂0 : 0 ≤ s₂ := by dsimp only [s₂]; split_ifs; exact le_rfl; exact le_max_left 0 _
      have hs₁_lt : s₁ = 0 ∨ s₁ < S₁ := by
        dsimp only [s₁]
        split_ifs with h0'
        · exact Or.inl rfl
        · right
          have hpos : 0 < S₁ := lt_of_le_of_ne hS₁0 (Ne.symm h0')
          exact max_lt hpos (by linarith)
      have hs₂_lt : s₂ = 0 ∨ s₂ < S₂ := by
        dsimp only [s₂]
        split_ifs with h0'
        · exact Or.inl rfl
        · right
          have hpos : 0 < S₂ := lt_of_le_of_ne hS₂0 (Ne.symm h0')
          exact max_lt hpos (by linarith)
      refine ⟨(s₁, s₂), hach s₁ s₂ hs₁0 hs₂0 hs₁_lt hs₂_lt, ?_⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have hd1 : |S₁ - s₁| < ε := by
        dsimp only [s₁]
        split_ifs with h0'
        · simp [h0', hε]
        · have hpos : 0 < S₁ := lt_of_le_of_ne hS₁0 (Ne.symm h0')
          have hle : max 0 (S₁ - ε / 2) ≤ S₁ := max_le (le_of_lt hpos) (by linarith)
          rw [abs_of_nonneg (by linarith)]
          have : S₁ - ε / 2 ≤ max 0 (S₁ - ε / 2) := le_max_right 0 _
          linarith
      have hd2 : |S₂ - s₂| < ε := by
        dsimp only [s₂]
        split_ifs with h0'
        · simp [h0', hε]
        · have hpos : 0 < S₂ := lt_of_le_of_ne hS₂0 (Ne.symm h0')
          have hle : max 0 (S₂ - ε / 2) ≤ S₂ := max_le (le_of_lt hpos) (by linarith)
          rw [abs_of_nonneg (by linarith)]
          have : S₂ - ε / 2 ≤ max 0 (S₂ - ε / 2) := le_max_right 0 _
          linarith
      exact max_lt hd1 hd2

private lemma macOperationalRegion_convex (W : MACChannel X₁ X₂ Y) :
    Convex ℝ (macOperationalRegion W) := by
  intro p hp q hq a b ha hb hab
  rw [macOperationalRegion, Metric.mem_closure_iff]
  intro ε hε
  rw [macOperationalRegion, Metric.mem_closure_iff] at hp hq
  obtain ⟨u, hu, hpu⟩ := hp (ε / 2) (by linarith)
  obtain ⟨v, hv, hqv⟩ := hq (ε / 2) (by linarith)
  have hw_mem : (a * u.1 + b * v.1, a * u.2 + b * v.2) ∈ macOperationalRegion W := by
    have ha_eq : a = 1 - b := by linarith
    rw [ha_eq]
    exact mac_time_sharing W hu hv hb (by linarith)
  rw [macOperationalRegion, Metric.mem_closure_iff] at hw_mem
  obtain ⟨z, hz, hwz⟩ := hw_mem (ε / 2) (by linarith)
  refine ⟨z, hz, ?_⟩
  have hdw : dist (a • p + b • q) (a * u.1 + b * v.1, a * u.2 + b * v.2) < ε / 2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hpu hqv ⊢
    have hpu1 : |p.1 - u.1| < ε / 2 := lt_of_le_of_lt (le_max_left _ _) hpu
    have hpu2 : |p.2 - u.2| < ε / 2 := lt_of_le_of_lt (le_max_right _ _) hpu
    have hqv1 : |q.1 - v.1| < ε / 2 := lt_of_le_of_lt (le_max_left _ _) hqv
    have hqv2 : |q.2 - v.2| < ε / 2 := lt_of_le_of_lt (le_max_right _ _) hqv
    have hd1 : |(a • p + b • q).1 - (a * u.1 + b * v.1)| < ε / 2 := by
      have hrew : (a • p + b • q).1 - (a * u.1 + b * v.1) = a * (p.1 - u.1) + b * (q.1 - v.1) := by
        simp; ring
      rw [hrew]
      calc |a * (p.1 - u.1) + b * (q.1 - v.1)|
        _ ≤ |a * (p.1 - u.1)| + |b * (q.1 - v.1)| := abs_add_le _ _
        _ = a * |p.1 - u.1| + b * |q.1 - v.1| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ < a * (ε / 2) + b * (ε / 2) := by
            by_cases ha0 : a = 0
            · subst ha0; have hb1 : b = 1 := by linarith
              subst hb1; linarith
            · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
              nlinarith
        _ = ε / 2 := by rw [← add_mul, hab, one_mul]
    have hd2 : |(a • p + b • q).2 - (a * u.2 + b * v.2)| < ε / 2 := by
      have hrew : (a • p + b • q).2 - (a * u.2 + b * v.2) = a * (p.2 - u.2) + b * (q.2 - v.2) := by
        simp; ring
      rw [hrew]
      calc |a * (p.2 - u.2) + b * (q.2 - v.2)|
        _ ≤ |a * (p.2 - u.2)| + |b * (q.2 - v.2)| := abs_add_le _ _
        _ = a * |p.2 - u.2| + b * |q.2 - v.2| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ < a * (ε / 2) + b * (ε / 2) := by
            by_cases ha0 : a = 0
            · subst ha0; have hb1 : b = 1 := by linarith
              subst hb1; linarith
            · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
              nlinarith
        _ = ε / 2 := by rw [← add_mul, hab, one_mul]
    exact max_lt hd1 hd2
  exact lt_of_le_of_lt (dist_triangle _ _ _) (by linarith)

/-! #### 2.4 MAC Converse (Fano + Multi-Letter Tensorization) -/

private lemma mac_converse_rate1 (W : MACChannel X₁ X₂ Y) {n M₁ M₂ : ℕ}
    (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
    (dec : (Fin n → Y) → Fin M₁ × Fin M₂) :
    letI : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
    letI : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
    let P₁ : Fin n → ProbDist X₁ := fun i => (ProbDist.uniform (α := Fin M₁)).map (fun m₁ => enc₁ m₁ i)
    let P₂ : Fin n → ProbDist X₂ := fun i => (ProbDist.uniform (α := Fin M₂)).map (fun m₂ => enc₂ m₂ i)
    let J : Fin n → ProbDist ((X₁ × X₂) × Y) := fun i => W.joint ((P₁ i).prod (P₂ i))
    let pe := macAvgError W n M₁ M₂ enc₁ enc₂ dec
    (1 - pe) * (log2 (M₁ : ℝ) / (n : ℝ)) ≤
      ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2))) +
        1 / (n : ℝ) := by
  classical
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  dsimp only
  let U₁ := ProbDist.uniform (α := Fin M₁)
  let U₂ := ProbDist.uniform (α := Fin M₂)
  let P_M := U₁.prod U₂
  let enc : Fin M₁ × Fin M₂ → Fin n → X₁ × X₂ := fun m i => (enc₁ m.1 i, enc₂ m.2 i)
  let P_MY := (dmcPrecomp (W.power n) enc).joint P_M
  let P_X₁ : ProbDist (Fin n → X₁) := U₁.map enc₁
  let P₁ : Fin n → ProbDist X₁ := fun i => U₁.map (fun m₁ => enc₁ m₁ i)
  let P₂ : Fin n → ProbDist X₂ := fun i => U₂.map (fun m₂ => enc₂ m₂ i)
  let J : Fin n → ProbDist ((X₁ × X₂) × Y) := fun i => W.joint ((P₁ i).prod (P₂ i))
  -- Slice channel given `x₂ : X₂`
  let Wslice (a₂ : X₂) : DMC X₁ Y :=
    { trans := fun a₁ y => W.trans (a₁, a₂) y
      nonneg := fun a₁ y => W.nonneg (a₁, a₂) y
      sum_one := fun a₁ => W.sum_one (a₁, a₂) }
  -- Time-varying channel given `m₂ : Fin M₂`
  let Wm2 (m₂ : Fin M₂) : DMC (Fin n → X₁) (Fin n → Y) := piDMC (fun i => Wslice (enc₂ m₂ i))
  let Q (m₂ : Fin M₂) : ProbDist (Fin M₁ × (Fin n → Y)) := (dmcPrecomp (Wm2 m₂) enc₁).joint U₁
  -- Identify `condMixDist U₂ Q` with `P_MY.map (fun t => (t.1.1, t.2, t.1.2))`
  let mix := condMixDist U₂ Q
  have hmix_eq : P_MY.map (fun t => (t.1.1, t.2, t.1.2)) = mix := by
    let e : ((Fin M₁ × Fin M₂) × (Fin n → Y)) ≃ (Fin M₁ × (Fin n → Y) × Fin M₂) :=
      { toFun := fun t => (t.1.1, t.2, t.1.2)
        invFun := fun t => ((t.1, t.2.2), t.2.1)
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    unfold ProbDist.map
    congr; funext ⟨m₁, y, m₂⟩; dsimp only [mix, condMixDist, Q, P_MY, dmcPrecomp, DMC.joint,
      P_M, ProbDist.prod, Wm2, piDMC, Wslice, DMC.power, enc]
    rw [Finset.sum_eq_single ((m₁, m₂), y)]
    · simp only [↓reduceIte]; ring
    · intro x _ hne
      have hne' : (x.1.1, x.2, x.1.2) ≠ (m₁, y, m₂) := fun h => hne (by
        have := congrArg e.symm h
        simpa [e] using this)
      simp only [hne', ↓reduceIte]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Apply Fano to `R₁ := P_MY.map (fun t => (t.1.1, (t.2, t.1.2)))` with `g₁ (y, m₂) := (dec y).1`
  let R₁ := P_MY.map (fun t => (t.1.1, (t.2, t.1.2)))
  let g₁ : (Fin n → Y) × Fin M₂ → Fin M₁ := fun ym => (dec ym.1).1
  have hfano := fano_inequality_card R₁ g₁
  have hpe_le : estErrorProb R₁ g₁ ≤ macAvgError W n M₁ M₂ enc₁ enc₂ dec := by
    rw [estErrorProb_map_pair]
    unfold macAvgError
    have hMne : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
    simp only [hMne, ↓reduceIte]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun m₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have hpmf : P_MY.pmf ((m₁, m₂), y) =
        ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y := by
      unfold P_MY dmcPrecomp DMC.joint P_M ProbDist.prod U₁ U₂ ProbDist.uniform enc
      dsimp only
      simp only [Fintype.card_fin, Nat.cast_mul]
      ring
    split_ifs with h1 h2
    · rw [hpmf]
    · exfalso; apply h1; dsimp only [g₁]; rw [not_not.mp h2]
    · exact mul_nonneg (by positivity) ((W.power n).nonneg _ y)
    · rw [mul_zero]
  have hbin : binaryEntropy (estErrorProb R₁ g₁) ≤ 1 :=
    InfoTheory.Known.binaryEntropy_le_one (estErrorProb_nonneg R₁ g₁) (estErrorProb_le_one R₁ g₁)
  -- `shannonEntropy R₁.fst = log2 M₁`
  have hR₁_fst : R₁.fst = U₁ := by
    rw [← probDist_map_fst, map_comp_eq]
    change P_MY.map (Prod.fst ∘ Prod.fst) = U₁
    rw [← map_comp_eq, probDist_map_fst, probDist_map_fst, dmc_joint_fst, probDist_prod_fst]
  have hHR1_fst : shannonEntropy R₁.fst = log2 (M₁ : ℝ) := by
    rw [hR₁_fst]
    simpa [Fintype.card_fin] using (shannonEntropy_eq_log2_card_iff U₁).mpr rfl
  -- `mutualInfo R₁ = condMutualInfo mix = ∑ m₂, U₂.pmf m₂ * mutualInfo (Q m₂)`
  have hmi_eq : mutualInfo R₁ = ∑ m₂ : Fin M₂, U₂.pmf m₂ * mutualInfo (Q m₂) := by
    rw [← condMixDist_condMutualInfo U₂ Q]
    unfold mutualInfo condMutualInfo
    dsimp only
    have h1 : shannonEntropy R₁ = shannonEntropy mix := by rw [← hmix_eq]
    have h2 : R₁.snd = mix.map (fun t => (t.2.1, t.2.2)) := by
      rw [← hmix_eq, ← probDist_map_snd]
    have h3 : mix.map (fun t => (t.1, t.2.2)) = U₁.prod U₂ := by
      rw [← hmix_eq, map_comp_eq]
      change P_MY.map Prod.fst = P_M
      rw [probDist_map_fst, dmc_joint_fst]
    have h4 : mix.map (fun t => t.2.2) = U₂ := by
      rw [← hmix_eq, map_comp_eq]
      change P_MY.map (Prod.snd ∘ Prod.fst) = U₂
      rw [← map_comp_eq, probDist_map_fst, dmc_joint_fst, probDist_map_snd, probDist_prod_snd]
    rw [hR₁_fst, h1, h2, h3, h4, shannonEntropy_prod]
    ring
  -- Bound each `mutualInfo (Q m₂)` by `∑ i, mutualInfo ((Wslice (enc₂ m₂ i)).joint (P₁ i))`
  have hQ_le : ∀ m₂ : Fin M₂,
      mutualInfo (Q m₂) ≤ ∑ i : Fin n, mutualInfo ((Wslice (enc₂ m₂ i)).joint (P₁ i)) := by
    intro m₂
    rw [dmcPrecomp_mutualInfo_eq (Wm2 m₂) U₁ enc₁]
    have hsub := piDMC_mutualInfo_le_sum (fun i => Wslice (enc₂ m₂ i)) P_X₁
    have hmarg : ∀ i : Fin n, P_X₁.map (fun x => x i) = P₁ i := fun i => by
      dsimp only [P_X₁, P₁]; rw [map_comp_eq]; rfl
    simp_rw [hmarg] at hsub
    exact hsub
  -- Average over `m₂ ~ U₂` and identify each coordinate sum with `condMutualInfo`
  have hsum_le : mutualInfo R₁ ≤
      ∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2))) := by
    rw [hmi_eq]
    calc ∑ m₂ : Fin M₂, U₂.pmf m₂ * mutualInfo (Q m₂)
      _ ≤ ∑ m₂ : Fin M₂, U₂.pmf m₂ * ∑ i : Fin n, mutualInfo ((Wslice (enc₂ m₂ i)).joint (P₁ i)) :=
          Finset.sum_le_sum fun m₂ _ => mul_le_mul_of_nonneg_left (hQ_le m₂) (U₂.nonneg m₂)
      _ = ∑ i : Fin n, ∑ m₂ : Fin M₂, U₂.pmf m₂ * mutualInfo ((Wslice (enc₂ m₂ i)).joint (P₁ i)) := by
          simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ = ∑ i : Fin n, ∑ a₂ : X₂, (P₂ i).pmf a₂ * mutualInfo ((Wslice a₂).joint (P₁ i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact sum_pmf_mul_comp U₂ (fun m₂ => enc₂ m₂ i) (fun a₂ => mutualInfo ((Wslice a₂).joint (P₁ i)))
      _ = ∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← condMixDist_condMutualInfo (P₂ i) (fun a₂ => (Wslice a₂).joint (P₁ i))]
          congr 1
          let e : ((X₁ × X₂) × Y) ≃ (X₁ × Y × X₂) :=
            { toFun := fun t => (t.1.1, t.2, t.1.2)
              invFun := fun t => ((t.1, t.2.2), t.2.1)
              left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
              right_inv := fun ⟨_, _, _⟩ => rfl }
          unfold ProbDist.map condMixDist
          congr; funext ⟨a₁, b, a₂⟩; dsimp only [J, DMC.joint, ProbDist.prod, Wslice]
          rw [Finset.sum_eq_single ((a₁, a₂), b)]
          · simp only [↓reduceIte]; ring
          · intro x _ hne
            have hne' : (x.1.1, x.2, x.1.2) ≠ (a₁, b, a₂) := fun h => hne (by
              have := congrArg e.symm h
              simpa [e] using this)
            simp only [hne', ↓reduceIte]
          · intro h; exact absurd (Finset.mem_univ _) h
  -- Combine Fano and tensorization
  have hlog0 : 0 ≤ log2 (M₁ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
    simpa [log2] using log2_mono_le zero_lt_one h1
  have hmul_pe : estErrorProb R₁ g₁ * log2 (M₁ : ℝ) ≤
      macAvgError W n M₁ M₂ enc₁ enc₂ dec * log2 (M₁ : ℝ) :=
    mul_le_mul_of_nonneg_right hpe_le hlog0
  have hid : log2 (M₁ : ℝ) = condEntropy R₁ + mutualInfo R₁ := by
    unfold condEntropy mutualInfo; linarith [hHR1_fst]
  rw [Fintype.card_fin] at hfano
  have hmain : (1 - macAvgError W n M₁ M₂ enc₁ enc₂ dec) * log2 (M₁ : ℝ) ≤
      (∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2)))) + 1 := by
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
  have hlhs : (1 - macAvgError W n M₁ M₂ enc₁ enc₂ dec) * log2 (M₁ : ℝ) / (n : ℝ) =
      (1 - macAvgError W n M₁ M₂ enc₁ enc₂ dec) * (log2 (M₁ : ℝ) / (n : ℝ)) := by ring
  have hrhs : ((∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2)))) + 1) / (n : ℝ) =
      ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2))) +
        1 / (n : ℝ) := by ring
  linarith

/-- **Two-User MAC Finite-Blocklength Converse Inequalities** (Cover & Thomas §15.3.4;
    El Gamal–Kim §4.5):
    for any `(n, M₁, M₂)` MAC code with `n, M₁, M₂ > 0` and uniform independent messages,
    the three rate bounds hold with the coordinate product marginals `P_{1,i} × P_{2,i}`. -/
theorem mac_converse (W : MACChannel X₁ X₂ Y) {n M₁ M₂ : ℕ}
    (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
    (dec : (Fin n → Y) → Fin M₁ × Fin M₂) :
    letI : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
    letI : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
    let P₁ : Fin n → ProbDist X₁ := fun i => (ProbDist.uniform (α := Fin M₁)).map (fun m₁ => enc₁ m₁ i)
    let P₂ : Fin n → ProbDist X₂ := fun i => (ProbDist.uniform (α := Fin M₂)).map (fun m₂ => enc₂ m₂ i)
    let J : Fin n → ProbDist ((X₁ × X₂) × Y) := fun i => W.joint ((P₁ i).prod (P₂ i))
    let pe := macAvgError W n M₁ M₂ enc₁ enc₂ dec
    (1 - pe) * (log2 (M₁ : ℝ) / (n : ℝ)) ≤
      ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2))) +
        1 / (n : ℝ) ∧
    (1 - pe) * (log2 (M₂ : ℝ) / (n : ℝ)) ≤
      ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, condMutualInfo ((J i).map (fun t => (t.1.2, t.2, t.1.1))) +
        1 / (n : ℝ) ∧
    (1 - pe) * (log2 ((M₁ * M₂ : ℕ) : ℝ) / (n : ℝ)) ≤
      ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, mutualInfo (J i) +
        1 / (n : ℝ) := by
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  refine ⟨mac_converse_rate1 W hn hM₁ hM₂ enc₁ enc₂ dec, ?_, ?_⟩
  · -- Swap users 1 and 2 and invoke `mac_converse_rate1`
    let Wswap : MACChannel X₂ X₁ Y :=
      { trans := fun x y => W.trans (x.2, x.1) y
        nonneg := fun x y => W.nonneg (x.2, x.1) y
        sum_one := fun x => W.sum_one (x.2, x.1) }
    have h2 := mac_converse_rate1 Wswap hn hM₂ hM₁ enc₂ enc₁ (fun y => (dec y).swap)
    dsimp only at h2 ⊢
    have herr_eq : macAvgError Wswap n M₂ M₁ enc₂ enc₁ (fun y => (dec y).swap) =
        macAvgError W n M₁ M₂ enc₁ enc₂ dec := by
      classical
      unfold macAvgError
      have hne1 : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
      have hne2 : ¬ (M₂ = 0 ∨ M₁ = 0) := by omega
      simp only [hne1, hne2, ↓reduceIte]
      rw [Nat.mul_comm M₂ M₁, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
        Finset.sum_congr rfl fun y _ => ?_
      have hiff : (dec y).swap ≠ (m₂, m₁) ↔ dec y ≠ (m₁, m₂) := by
        constructor <;> intro h heq <;> apply h
        · rw [heq]; rfl
        · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
      simp [Wswap, DMC.power, hiff]
    have hcmi_eq : ∀ i : Fin n,
        condMutualInfo ((Wswap.joint (((ProbDist.uniform (α := Fin M₂)).map (fun m₂ => enc₂ m₂ i)).prod
          ((ProbDist.uniform (α := Fin M₁)).map (fun m₁ => enc₁ m₁ i)))).map (fun t => (t.1.1, t.2, t.1.2))) =
        condMutualInfo ((W.joint (((ProbDist.uniform (α := Fin M₁)).map (fun m₁ => enc₁ m₁ i)).prod
          ((ProbDist.uniform (α := Fin M₂)).map (fun m₂ => enc₂ m₂ i)))).map (fun t => (t.1.2, t.2, t.1.1))) := by
      intro i
      congr 1
      classical
      unfold ProbDist.map DMC.joint ProbDist.prod Wswap
      congr; funext ⟨a₂, b, a₁⟩; dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single a₂]
      · rw [Finset.sum_eq_single a₁]
        · rw [Finset.sum_eq_single b]
          · rw [Finset.sum_eq_single a₁]
            · rw [Finset.sum_eq_single a₂]
              · rw [Finset.sum_eq_single b]
                · simp only [↓reduceIte]; ring
                · intro b' _ hne; simp [hne]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro a₂' _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro a₁' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro b' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro a₁' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a₂' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [herr_eq] at h2
    simp_rw [hcmi_eq] at h2
    exact h2
  · -- Sum-rate bound via `fano_inequality_card` + `dmcPower_mutualInfo_le_sum`
    classical
    let U₁ := ProbDist.uniform (α := Fin M₁)
    let U₂ := ProbDist.uniform (α := Fin M₂)
    let P_M := U₁.prod U₂
    let enc : Fin M₁ × Fin M₂ → Fin n → X₁ × X₂ := fun m i => (enc₁ m.1 i, enc₂ m.2 i)
    let P_MY := (dmcPrecomp (W.power n) enc).joint P_M
    have hfano := fano_inequality_card P_MY dec
    have hpe_eq : estErrorProb P_MY dec = macAvgError W n M₁ M₂ enc₁ enc₂ dec := by
      unfold estErrorProb macAvgError P_MY dmcPrecomp DMC.joint P_M ProbDist.prod U₁ U₂ ProbDist.uniform enc
      have hMne : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
      simp only [hMne, ↓reduceIte, Fintype.card_fin, Nat.cast_mul]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
    have hbin : binaryEntropy (estErrorProb P_MY dec) ≤ 1 :=
      InfoTheory.Known.binaryEntropy_le_one (estErrorProb_nonneg P_MY dec) (estErrorProb_le_one P_MY dec)
    have hHM : shannonEntropy P_MY.fst = log2 ((M₁ * M₂ : ℕ) : ℝ) := by
      change shannonEntropy ((dmcPrecomp (W.power n) enc).joint P_M).fst = _
      rw [dmc_joint_fst, shannonEntropy_prod]
      have h1 : shannonEntropy U₁ = log2 (M₁ : ℝ) := by
        simpa [Fintype.card_fin] using (shannonEntropy_eq_log2_card_iff U₁).mpr rfl
      have h2 : shannonEntropy U₂ = log2 (M₂ : ℝ) := by
        simpa [Fintype.card_fin] using (shannonEntropy_eq_log2_card_iff U₂).mpr rfl
      rw [h1, h2, Nat.cast_mul, log2_mul_pos (Nat.cast_pos.mpr hM₁) (Nat.cast_pos.mpr hM₂)]
    have hmi_le : mutualInfo P_MY ≤
        ∑ i : Fin n, mutualInfo (W.joint ((U₁.map (fun m₁ => enc₁ m₁ i)).prod
          (U₂.map (fun m₂ => enc₂ m₂ i)))) := by
      rw [dmcPrecomp_mutualInfo_eq (W.power n) P_M enc]
      have hsub := dmcPower_mutualInfo_le_sum W n (P_M.map enc)
      have hcoord : ∀ i : Fin n, (P_M.map enc).map (fun x => x i) =
          (U₁.map (fun m₁ => enc₁ m₁ i)).prod (U₂.map (fun m₂ => enc₂ m₂ i)) := fun i => by
        rw [map_comp_eq]
        exact probDist_prod_map_prod U₁ U₂ (fun m₁ => enc₁ m₁ i) (fun m₂ => enc₂ m₂ i)
      simp_rw [hcoord] at hsub
      exact hsub
    have hid : log2 ((M₁ * M₂ : ℕ) : ℝ) = condEntropy P_MY + mutualInfo P_MY := by
      unfold condEntropy mutualInfo; linarith [hHM]
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hpe_eq] at hfano
    rw [hpe_eq] at hbin
    have hmain : (1 - macAvgError W n M₁ M₂ enc₁ enc₂ dec) * log2 ((M₁ * M₂ : ℕ) : ℝ) ≤
        (∑ i : Fin n, mutualInfo (W.joint ((U₁.map (fun m₁ => enc₁ m₁ i)).prod
          (U₂.map (fun m₂ => enc₂ m₂ i))))) + 1 := by
      linarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hdiv := div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
    have hlhs : (1 - macAvgError W n M₁ M₂ enc₁ enc₂ dec) * log2 ((M₁ * M₂ : ℕ) : ℝ) / (n : ℝ) =
        (1 - macAvgError W n M₁ M₂ enc₁ enc₂ dec) * (log2 ((M₁ * M₂ : ℕ) : ℝ) / (n : ℝ)) := by ring
    have hrhs : ((∑ i : Fin n, mutualInfo (W.joint ((U₁.map (fun m₁ => enc₁ m₁ i)).prod
          (U₂.map (fun m₂ => enc₂ m₂ i))))) + 1) / (n : ℝ) =
        ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, mutualInfo (W.joint ((U₁.map (fun m₁ => enc₁ m₁ i)).prod
          (U₂.map (fun m₂ => enc₂ m₂ i)))) + 1 / (n : ℝ) := by ring
    linarith

/-- Every operationally achievable rate pair `(R₁, R₂)` over a DM-MAC `W` belongs to the
    single-letter capacity region `macSingleLetterRegion W`. -/
theorem mac_achievable_mem_singleLetter (W : MACChannel X₁ X₂ Y) {R₁ R₂ : ℝ}
    (h : IsMACAchievable W R₁ R₂) :
    (R₁, R₂) ∈ macSingleLetterRegion W := by
  let S := convexHull ℝ (⋃ (P₁ : ProbDist X₁) (P₂ : ProbDist X₂), macPentagon W P₁ P₂)
  have hS_conv : Convex ℝ S := convex_convexHull ℝ _
  rw [macSingleLetterRegion, Metric.mem_closure_iff]
  intro ε hε
  let M : ℝ := max R₁ R₂ + 1
  have hMpos : 0 < M := by dsimp only [M]; linarith [le_max_left R₁ R₂, h.1]
  let δ : ℝ := min (1 / 2) (ε / (4 * M))
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨N₁, hN₁⟩ := h.2.2 δ hδpos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 / ε)
  let n : ℕ := max (max N₁ N₂) 1
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨enc₁, enc₂, dec, herr⟩ := hN₁ n (le_trans (le_max_left N₁ N₂) (le_max_left _ 1))
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  let P₁ : Fin n → ProbDist X₁ := fun i => (ProbDist.uniform (α := Fin M₁)).map (fun m₁ => enc₁ m₁ i)
  let P₂ : Fin n → ProbDist X₂ := fun i => (ProbDist.uniform (α := Fin M₂)).map (fun m₂ => enc₂ m₂ i)
  let J : Fin n → ProbDist ((X₁ × X₂) × Y) := fun i => W.joint ((P₁ i).prod (P₂ i))
  let I₁ : Fin n → ℝ := fun i => condMutualInfo ((J i).map (fun t => (t.1.1, t.2, t.1.2)))
  let I₂ : Fin n → ℝ := fun i => condMutualInfo ((J i).map (fun t => (t.1.2, t.2, t.1.1)))
  let I₁₂ : Fin n → ℝ := fun i => mutualInfo (J i)
  let A : ℝ := ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, I₁ i
  let B : ℝ := ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, I₂ i
  let C : ℝ := ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, I₁₂ i
  have hpoly : ∀ i : Fin n, 0 ≤ I₁ i ∧ 0 ≤ I₂ i ∧ I₁ i ≤ I₁₂ i ∧ I₂ i ≤ I₁₂ i ∧ I₁₂ i ≤ I₁ i + I₂ i :=
    fun i => mac_pentagon_polymatroid W (P₁ i) (P₂ i)
  -- The 5 vertices of each coordinate pentagon lie in `S`
  have hsub_i : ∀ i : Fin n, macPentagon W (P₁ i) (P₂ i) ⊆ S := fun i =>
    Set.Subset.trans (Set.subset_iUnion_of_subset (P₁ i) (Set.subset_iUnion (macPentagon W (P₁ i)) (P₂ i)))
      (subset_convexHull ℝ _)
  have hv0 : (0, 0) ∈ S := by
    have h0 := convex_avg_mem hS_conv n hn (fun _ => ((0 : ℝ), (0 : ℝ))) fun i =>
      hsub_i i ⟨le_rfl, le_rfl, (hpoly i).1, (hpoly i).2.1, by simp; exact le_trans (hpoly i).1 (hpoly i).2.2.1⟩
    simpa using h0
  have hv1 : (A, 0) ∈ S := by
    have h1 := convex_avg_mem hS_conv n hn (fun i => (I₁ i, (0 : ℝ))) fun i =>
      hsub_i i ⟨(hpoly i).1, le_rfl, le_rfl, (hpoly i).2.1, by linarith [(hpoly i).2.2.1]⟩
    simpa [A] using h1
  have hv2 : (A, C - A) ∈ S := by
    have h2 := convex_avg_mem hS_conv n hn (fun i => (I₁ i, I₁₂ i - I₁ i)) fun i =>
      hsub_i i ⟨(hpoly i).1, by linarith [(hpoly i).2.2.1], le_rfl, by linarith [(hpoly i).2.2.2.2],
        by ring_nf; exact le_rfl⟩
    have heq : (((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, I₁ i,
        ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (I₁₂ i - I₁ i)) = (A, C - A) := by
      ext
      · rfl
      · dsimp only [A, C]; rw [Finset.sum_sub_distrib, mul_sub]
    rw [← heq]; exact h2
  have hv3 : (C - B, B) ∈ S := by
    have h3 := convex_avg_mem hS_conv n hn (fun i => (I₁₂ i - I₂ i, I₂ i)) fun i =>
      hsub_i i ⟨by linarith [(hpoly i).2.2.2.1], (hpoly i).2.1, by linarith [(hpoly i).2.2.2.2],
        le_rfl, by ring_nf; exact le_rfl⟩
    have heq : (((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (I₁₂ i - I₂ i),
        ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, I₂ i) = (C - B, B) := by
      ext
      · dsimp only [B, C]; rw [Finset.sum_sub_distrib, mul_sub]
      · rfl
    rw [← heq]; exact h3
  have hv4 : (0, B) ∈ S := by
    have h4 := convex_avg_mem hS_conv n hn (fun i => ((0 : ℝ), I₂ i)) fun i =>
      hsub_i i ⟨le_rfl, (hpoly i).2.1, (hpoly i).1, le_rfl, by linarith [(hpoly i).2.2.2.1]⟩
    simpa [B] using h4
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hpoly i).1)
  have hB0 : 0 ≤ B := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hpoly i).2.1)
  have hAC : A ≤ C := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => (hpoly i).2.2.1) (by positivity)
  have hBC : B ≤ C := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => (hpoly i).2.2.2.1) (by positivity)
  have hCAB : C ≤ A + B := by
    dsimp only [A, B, C]
    rw [← mul_add, ← Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hpoly i).2.2.2.2) (by positivity)
  -- Construct `(r₁, r₂)` from `mac_converse`
  let pe := macAvgError W n M₁ M₂ enc₁ enc₂ dec
  have hconv := mac_converse W hn hM₁ hM₂ enc₁ enc₂ dec
  dsimp only at hconv
  let r₁ : ℝ := max 0 ((1 - pe) * (log2 (M₁ : ℝ) / (n : ℝ)) - 1 / (n : ℝ))
  let r₂ : ℝ := max 0 ((1 - pe) * (log2 (M₂ : ℝ) / (n : ℝ)) - 1 / (n : ℝ))
  have hr₁0 : 0 ≤ r₁ := le_max_left 0 _
  have hr₂0 : 0 ≤ r₂ := le_max_left 0 _
  have hr₁A : r₁ ≤ A := max_le hA0 (by linarith [hconv.1])
  have hr₂B : r₂ ≤ B := max_le hB0 (by linarith [hconv.2.1])
  have hr12C : r₁ + r₂ ≤ C := by
    have hlogprod : log2 ((M₁ * M₂ : ℕ) : ℝ) = log2 (M₁ : ℝ) + log2 (M₂ : ℝ) := by
      rw [Nat.cast_mul, log2_mul_pos (Nat.cast_pos.mpr hM₁) (Nat.cast_pos.mpr hM₂)]
    by_cases h1 : (1 - pe) * (log2 (M₁ : ℝ) / (n : ℝ)) - 1 / (n : ℝ) ≤ 0
    · have hr1z : r₁ = 0 := max_eq_left h1
      rw [hr1z, zero_add]; exact le_trans hr₂B hBC
    · by_cases h2 : (1 - pe) * (log2 (M₂ : ℝ) / (n : ℝ)) - 1 / (n : ℝ) ≤ 0
      · have hr2z : r₂ = 0 := max_eq_left h2
        rw [hr2z, add_zero]; exact le_trans hr₁A hAC
      · push Not at h1 h2
        have hr1e : r₁ = (1 - pe) * (log2 (M₁ : ℝ) / (n : ℝ)) - 1 / (n : ℝ) :=
          max_eq_right (le_of_lt h1)
        have hr2e : r₂ = (1 - pe) * (log2 (M₂ : ℝ) / (n : ℝ)) - 1 / (n : ℝ) :=
          max_eq_right (le_of_lt h2)
        have hsum_eq : (1 - pe) * (log2 (M₁ : ℝ) / (n : ℝ)) + (1 - pe) * (log2 (M₂ : ℝ) / (n : ℝ)) =
            (1 - pe) * (log2 ((M₁ * M₂ : ℕ) : ℝ) / (n : ℝ)) := by
          rw [hlogprod]; ring
        have h1n_pos : 0 < 1 / (n : ℝ) := by positivity
        linarith [hconv.2.2]
  have hr_mem : (r₁, r₂) ∈ S :=
    mem_convex_of_pentagon_vertices hS_conv hA0 hB0 hAC hBC hCAB hv0 hv1 hv2 hv3 hv4
      hr₁0 hr₂0 hr₁A hr₂B hr12C
  refine ⟨(r₁, r₂), hr_mem, ?_⟩
  -- Bound `dist (R₁, R₂) (r₁, r₂) < ε`
  have hpe0 : 0 ≤ pe := by
    classical
    unfold pe macAvgError
    have hMne : ¬ (M₁ = 0 ∨ M₂ = 0) := by omega
    simp only [hMne, ↓reduceIte]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => by split_ifs; exact (W.power n).nonneg _ _; exact le_rfl)
  have hpe_le : pe ≤ δ := herr
  have h1n_lt : 1 / (n : ℝ) < ε / 4 := by
    have hn_gt : 4 / ε < (n : ℝ) :=
      lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
    rw [div_lt_iff₀ hn_r]
    have := (div_lt_iff₀ hε).mp hn_gt
    linarith
  have hlogM_bounds : ∀ {R : ℝ}, 0 ≤ R →
      let K := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      R - 1 / (n : ℝ) ≤ log2 (K : ℝ) / (n : ℝ) ∧ log2 (K : ℝ) / (n : ℝ) ≤ R := by
    intro R hR
    dsimp only
    let K := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    have hKpos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    constructor
    · have hlb : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ (K : ℝ) := by
        have h1 := half_two_rpow_le_max_one_floor n hR
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        exact h1
      have hlog := log2_mono_le (Real.rpow_pos_of_pos (by norm_num) _) hlb
      rw [log2_two_rpow_eq] at hlog
      have hdiv := div_le_div_of_nonneg_right hlog (le_of_lt hn_r)
      have hsimp : ((n : ℝ) * R - 1) / (n : ℝ) = R - 1 / (n : ℝ) := by
        rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hn_r)]
      linarith
    · have hub : (K : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := max_one_floor_two_rpow_le n hR
      have hlog := log2_mono_le (Nat.cast_pos.mpr hKpos) hub
      rw [log2_two_rpow_eq] at hlog
      exact (div_le_iff₀ hn_r).mpr (by linarith)
  have hdist_coord : ∀ {R : ℝ} {K : ℕ}, 0 ≤ R → R ≤ M →
      R - 1 / (n : ℝ) ≤ log2 (K : ℝ) / (n : ℝ) → log2 (K : ℝ) / (n : ℝ) ≤ R →
      |R - max 0 ((1 - pe) * (log2 (K : ℝ) / (n : ℝ)) - 1 / (n : ℝ))| < ε := by
    intro R K hR hRM hlb hub
    have hleR : max 0 ((1 - pe) * (log2 (K : ℝ) / (n : ℝ)) - 1 / (n : ℝ)) ≤ R := by
      refine max_le hR ?_
      have h1 : (1 - pe) * (log2 (K : ℝ) / (n : ℝ)) ≤ 1 * R := by
        by_cases hlog0 : log2 (K : ℝ) / (n : ℝ) ≤ 0
        · have h1mpe : 0 ≤ 1 - pe := by
            have : δ ≤ 1 / 2 := min_le_left _ _
            linarith
          have : (1 - pe) * (log2 (K : ℝ) / (n : ℝ)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos h1mpe hlog0
          linarith
        · push Not at hlog0
          exact mul_le_mul (by linarith) hub (le_of_lt hlog0) zero_le_one
      have h1n0 : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
    rw [abs_of_nonneg (by linarith)]
    have hge : (1 - pe) * (log2 (K : ℝ) / (n : ℝ)) - 1 / (n : ℝ) ≤
        max 0 ((1 - pe) * (log2 (K : ℝ) / (n : ℝ)) - 1 / (n : ℝ)) := le_max_right 0 _
    have hpeR : pe * R ≤ ε / 4 := by
      have hδM : δ ≤ ε / (4 * M) := min_le_right _ _
      calc pe * R ≤ δ * M := mul_le_mul hpe_le hRM hR (le_of_lt hδpos)
        _ ≤ (ε / (4 * M)) * M := mul_le_mul_of_nonneg_right hδM (le_of_lt hMpos)
        _ = ε / 4 := by field_simp [ne_of_gt hMpos]
    have h1mpe_lb : (1 - pe) * (R - 1 / (n : ℝ)) ≤ (1 - pe) * (log2 (K : ℝ) / (n : ℝ)) := by
      have h1mpe0 : 0 ≤ 1 - pe := by
        have : δ ≤ 1 / 2 := min_le_left _ _
        linarith
      exact mul_le_mul_of_nonneg_left hlb h1mpe0
    have hpe1n : 0 ≤ pe * (1 / (n : ℝ)) := mul_nonneg hpe0 (by positivity)
    linarith
  have hb1 := hlogM_bounds h.1
  have hb2 := hlogM_bounds h.2.1
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt
    (hdist_coord h.1 (by dsimp only [M]; linarith [le_max_left R₁ R₂]) hb1.1 hb1.2)
    (hdist_coord h.2.1 (by dsimp only [M]; linarith [le_max_right R₁ R₂]) hb2.1 hb2.2)

/-- **Two-User Discrete Memoryless MAC Capacity Region Theorem**
    (Cover & Thomas, Theorem 15.3.1; El Gamal–Kim, Theorem 4.3):
    the operational capacity region of any two-user DM-MAC `W` equals the closure of the
    convex hull of the union of all product-input pentagons `macPentagon W P₁ P₂`. -/
theorem mac_capacity_theorem (W : MACChannel X₁ X₂ Y) :
    macOperationalRegion W = macSingleLetterRegion W := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun r hr => mac_achievable_mem_singleLetter W hr) isClosed_closure
  · refine closure_minimal (convexHull_min ?_ (macOperationalRegion_convex W)) isClosed_closure
    intro r hr
    rcases Set.mem_iUnion.mp hr with ⟨P₁, hr₁⟩
    rcases Set.mem_iUnion.mp hr₁ with ⟨P₂, hr₂⟩
    exact macPentagon_subset_macOperationalRegion W P₁ P₂ hr₂

end MultipleAccessChannel

end InfoTheory.Bridge
