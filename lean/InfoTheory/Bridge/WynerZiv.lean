import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.RateDistortion
import InfoTheory.Bridge.NetworkIT

/-!
# Wyner–Ziv Lossy Source Coding with Decoder Side Information
(Cover & Thomas §15.9, Theorem 15.9.1; El Gamal–Kim §11.3, Theorem 11.3 & Lemma 12.1)

Purely additive, kernel-verified formalization of the Wyner–Ziv theorem for discrete memoryless
correlated sources `(X, Y) ~ P` with decoder side information `Y`, built on top of
`InfoTheory.Bridge.CoverThomas`, `InfoTheory.Bridge.ChannelCoding`,
`InfoTheory.Bridge.RateDistortion`, and `InfoTheory.Bridge.NetworkIT`:

1. **Single-Letter Wyner–Ziv Rate–Distortion Function & Convexity**:
   - `wynerZivRateDistortion`, `IsWynerZivFeasible`, `IsWynerZivAchievable`,
     `operationalWynerZivRate`
   - `wynerZivRateDistortion_nonneg`, `wynerZivRateDistortion_le`,
     `wynerZivRateDistortion_antitone`
   - `wynerZivRateDistortion_convex` (exact convexity via disjoint-union time-sharing)
   - `wynerZivRateDistortion_rightContinuous` (right-continuity at every strictly feasible
     distortion `D > D_min`)

2. **Wyner–Ziv Converse (Cover & Thomas §15.9; El Gamal–Kim §11.3)**:
   - `wynerZiv_converse`: for any `(n, M)` block code `(enc, dec)` (`n ≥ 1, M ≥ 1`) with
     expected per-symbol distortion `≤ D`,
     `wynerZivRateDistortion P d D ≤ log₂ M / n`

3. **Strong (Robust) Typicality & The Markov Lemma (El Gamal–Kim §2.4 & Lemma 12.1)**:
   - `empFreq`, `strongTypicalSet`
   - `strongTypicalSet_map` (exact closure under deterministic maps / marginals)
   - `strongTypicalSet_subset_weakTypicalSet` (robust typicality implies weak typicality)
   - `strongTypicalSet_prob_not_mem_le`, `strongTypicalSet_prob_tendsto_one`
   - `markov_lemma` (uniform `O(1 / (n (ε₂ - ε₁)²))` Chebyshev tail bound for Markov chains
     `U — X — Y` conditioned on a fixed strongly typical `(x^n, u^n)`)

4. **Wyner–Ziv Achievability & Operational Equality (Cover & Thomas Thm. 15.9.1;
   El Gamal–Kim Thm. 11.3)**:
   - `wynerZiv_achievability_of_dist` (covering lemma + Markov lemma + random binning)
   - `wynerZiv_achievability`
   - `wynerZiv_operational_achievability`, `wynerZiv_operational_converse`
   - `wyner_ziv_theorem` (`operationalWynerZivRate P d D = wynerZivRateDistortion P d D`
     at every strictly feasible distortion `D`)

All theorems leave `Core/`, `Problems/`, `Known/`, `Bridge.lean`, and all existing `Bridge/*`
files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Shared Private Helper Lemmas -/

section SharedHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma wz_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma wz_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; funext a; exact h a

private lemma wz_probDist_map_id (P : ProbDist α) : P.map id = P := by
  classical
  cases P with | mk pmf h0 h1 =>
  unfold ProbDist.map
  congr
  funext a
  simp

private lemma wz_probDist_map_equiv_pmf (e : α ≃ β) (P : ProbDist α) (b : β) :
    (P.map e).pmf b = P.pmf (e.symm b) := by
  classical
  unfold ProbDist.map
  dsimp only
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ hne
    have : e a ≠ b := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma wz_shannonEntropy_map_injective (P : ProbDist α) {f : α → β}
    (hf : Function.Injective f) :
    shannonEntropy (P.map f) = shannonEntropy P := by
  have : Nonempty α := wz_nonempty_of_probDist P
  let g : β → α := Function.invFun f
  have hgf : g ∘ f = id := funext (Function.leftInverse_invFun hf)
  have h1 : shannonEntropy (P.map f) ≤ shannonEntropy P := shannonEntropy_map_le f P
  have h2 : shannonEntropy P ≤ shannonEntropy (P.map f) := by
    have heq : (P.map f).map g = P := by
      rw [map_comp_eq, hgf, wz_probDist_map_id]
    calc shannonEntropy P = shannonEntropy ((P.map f).map g) := by rw [heq]
      _ ≤ shannonEntropy (P.map f) := shannonEntropy_map_le g (P.map f)
  exact le_antisymm h1 h2

private lemma wz_condMutualInfo_map_fst_equiv (Q : ProbDist (α × β × γ)) (e : α ≃ δ) :
    condMutualInfo (Q.map (fun t => (e t.1, t.2.1, t.2.2))) = condMutualInfo Q := by
  let eAll : (α × β × γ) ≃ (δ × β × γ) :=
    { toFun := fun t => (e t.1, t.2.1, t.2.2)
      invFun := fun t => (e.symm t.1, t.2.1, t.2.2)
      left_inv := fun ⟨a, b, c⟩ => by simp
      right_inv := fun ⟨d, b, c⟩ => by simp }
  let eXZ : (α × γ) ≃ (δ × γ) :=
    { toFun := fun p => (e p.1, p.2)
      invFun := fun p => (e.symm p.1, p.2)
      left_inv := fun ⟨a, c⟩ => by simp
      right_inv := fun ⟨d, c⟩ => by simp }
  unfold condMutualInfo
  have hAll : shannonEntropy (Q.map (fun t => (e t.1, t.2.1, t.2.2))) = shannonEntropy Q :=
    shannonEntropy_map_equiv eAll Q
  have hXZ : shannonEntropy ((Q.map (fun t => (e t.1, t.2.1, t.2.2))).map (fun t => (t.1, t.2.2))) =
      shannonEntropy (Q.map (fun t => (t.1, t.2.2))) := by
    rw [map_comp_eq]
    have hcomp : ((fun t : δ × β × γ => (t.1, t.2.2)) ∘ fun t : α × β × γ => (e t.1, t.2.1, t.2.2)) =
        eXZ ∘ (fun t : α × β × γ => (t.1, t.2.2)) := rfl
    rw [hcomp, ← map_comp_eq, shannonEntropy_map_equiv eXZ]
  have hYZ : (Q.map (fun t => (e t.1, t.2.1, t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      Q.map (fun t => (t.2.1, t.2.2)) := by
    rw [map_comp_eq]; rfl
  have hZ : (Q.map (fun t => (e t.1, t.2.1, t.2.2))).map (fun t => t.2.2) =
      Q.map (fun t => t.2.2) := by
    rw [map_comp_eq]; rfl
  dsimp only
  rw [hAll, hXZ, hYZ, hZ]

private lemma wz_condMutualInfo_map_snd_equiv (Q : ProbDist (α × β × γ)) (e : β ≃ δ) :
    condMutualInfo (Q.map (fun t => (t.1, e t.2.1, t.2.2))) = condMutualInfo Q := by
  let eAll : (α × β × γ) ≃ (α × δ × γ) :=
    { toFun := fun t => (t.1, e t.2.1, t.2.2)
      invFun := fun t => (t.1, e.symm t.2.1, t.2.2)
      left_inv := fun ⟨a, b, c⟩ => by simp
      right_inv := fun ⟨a, d, c⟩ => by simp }
  let eYZ : (β × γ) ≃ (δ × γ) :=
    { toFun := fun p => (e p.1, p.2)
      invFun := fun p => (e.symm p.1, p.2)
      left_inv := fun ⟨b, c⟩ => by simp
      right_inv := fun ⟨d, c⟩ => by simp }
  unfold condMutualInfo
  have hAll : shannonEntropy (Q.map (fun t => (t.1, e t.2.1, t.2.2))) = shannonEntropy Q :=
    shannonEntropy_map_equiv eAll Q
  have hXZ : (Q.map (fun t => (t.1, e t.2.1, t.2.2))).map (fun t => (t.1, t.2.2)) =
      Q.map (fun t => (t.1, t.2.2)) := by
    rw [map_comp_eq]; rfl
  have hYZ : shannonEntropy ((Q.map (fun t => (t.1, e t.2.1, t.2.2))).map (fun t => (t.2.1, t.2.2))) =
      shannonEntropy (Q.map (fun t => (t.2.1, t.2.2))) := by
    rw [map_comp_eq]
    have hcomp : ((fun t : α × δ × γ => (t.2.1, t.2.2)) ∘ fun t : α × β × γ => (t.1, e t.2.1, t.2.2)) =
        eYZ ∘ (fun t : α × β × γ => (t.2.1, t.2.2)) := rfl
    rw [hcomp, ← map_comp_eq, shannonEntropy_map_equiv eYZ]
  have hZ : (Q.map (fun t => (t.1, e t.2.1, t.2.2))).map (fun t => t.2.2) =
      Q.map (fun t => t.2.2) := by
    rw [map_comp_eq]; rfl
  dsimp only
  rw [hAll, hXZ, hYZ, hZ]

private lemma wz_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  unfold ProbDist.map ProbDist.fst
  congr; funext a
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_single a (fun a' _ hne => by simp [hne])
    (fun h => absurd (Finset.mem_univ _) h) |>.trans ?_
  simp

private lemma wz_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  unfold ProbDist.map ProbDist.snd
  congr; funext b
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_eq_single b (fun b' _ hne => by simp [hne])
    (fun h => absurd (Finset.mem_univ _) h) |>.trans ?_
  simp

private lemma wz_iidDist_map_coord (P : ProbDist α) {n : ℕ} (i : Fin n) :
    (iidDist P n).map (fun x => x i) = P := by
  classical
  unfold ProbDist.map
  congr; funext a; dsimp only
  have h1 : (∑ x : Fin n → α, if x i = a then (iidDist P n).pmf x else 0) =
      ∑ x : Fin n → α, (iidDist P n).pmf x * (if x i = a then 1 else 0) :=
    Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
  rw [h1, iidDist_sum_coord P (fun b => if b = a then 1 else 0) i]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma wz_piProdDist_sum_coord {n : ℕ} (V : Fin n → ProbDist α) (f : α → ℝ) (i : Fin n) :
    ∑ x : Fin n → α, (piProdDist V).pmf x * f (x i) = ∑ a : α, (V i).pmf a * f a := by
  classical
  let F : Fin n → α → ℝ := fun j a => if j = i then (V j).pmf a * f a else (V j).pmf a
  have hfun : ∀ x : Fin n → α, (piProdDist V).pmf x * f (x i) = ∏ j : Fin n, F j (x j) := by
    intro x
    unfold piProdDist; dsimp only
    conv_rhs => rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (x j)) (Finset.mem_univ i)]
    conv_lhs => rw [← Finset.mul_prod_erase Finset.univ (fun j => (V j).pmf (x j)) (Finset.mem_univ i)]
    have hi : F i (x i) = (V i).pmf (x i) * f (x i) := by simp [F]
    have heq : ∏ j ∈ Finset.univ.erase i, F j (x j) =
        ∏ j ∈ Finset.univ.erase i, (V j).pmf (x j) :=
      Finset.prod_congr rfl fun j hj => by simp [F, (Finset.mem_erase.mp hj).1]
    rw [hi, heq]; ring
  simp_rw [hfun]
  rw [← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ a : α, F j a) (Finset.mem_univ i)]
  have hi : ∑ a : α, F i a = ∑ a : α, (V i).pmf a * f a := by simp [F]
  have hrest : ∏ j ∈ Finset.univ.erase i, (∑ a : α, F j a) = 1 :=
    Finset.prod_eq_one fun j hj => by
      simp only [F, ite_eq_right_iff.mpr (fun h => absurd h (Finset.mem_erase.mp hj).1)]
      exact (V j).sum_one
  rw [hi, hrest, mul_one]

private lemma wz_piProdDist_sum_two_coords {n : ℕ} (V : Fin n → ProbDist α)
    (f g : α → ℝ) {i j : Fin n} (hij : i ≠ j) :
    ∑ x : Fin n → α, (piProdDist V).pmf x * (f (x i) * g (x j)) =
      (∑ a : α, (V i).pmf a * f a) * (∑ a : α, (V j).pmf a * g a) := by
  classical
  let F : Fin n → α → ℝ := fun k a =>
    if k = i then (V k).pmf a * f a else if k = j then (V k).pmf a * g a else (V k).pmf a
  have hfun : ∀ x : Fin n → α,
      (piProdDist V).pmf x * (f (x i) * g (x j)) = ∏ k : Fin n, F k (x k) := by
    intro x
    unfold piProdDist; dsimp only
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun k => F k (x k)) (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => F k (x k)) hj_mem]
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun k => (V k).pmf (x k)) (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => (V k).pmf (x k)) hj_mem]
    have hi : F i (x i) = (V i).pmf (x i) * f (x i) := by simp [F]
    have hj : F j (x j) = (V j).pmf (x j) * g (x j) := by simp [F, hij.symm]
    have heq : ∏ k ∈ (Finset.univ.erase i).erase j, F k (x k) =
        ∏ k ∈ (Finset.univ.erase i).erase j, (V k).pmf (x k) :=
      Finset.prod_congr rfl fun k hk => by
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        simp [F, hki, hkj]
    rw [hi, hj, heq]; ring
  simp_rw [hfun]
  rw [← Fintype.prod_sum F]
  have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ a : α, F k a) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => ∑ a : α, F k a) hj_mem]
  have hi : ∑ a : α, F i a = ∑ a : α, (V i).pmf a * f a := by simp [F]
  have hj : ∑ a : α, F j a = ∑ a : α, (V j).pmf a * g a := by simp [F, hij.symm]
  have hrest : ∏ k ∈ (Finset.univ.erase i).erase j, (∑ a : α, F k a) = 1 :=
    Finset.prod_eq_one fun k hk => by
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp only [F, hki, hkj, ↓reduceIte]
      exact (V k).sum_one
  rw [hi, hj, hrest, mul_one]

private lemma wz_uniform_binning_collision_prob {M_c M_b : ℕ} (hMb : 0 < M_b)
    (u v : Fin M_c) (hne : v ≠ u) :
    letI : Nonempty (Fin M_b) := ⟨⟨0, hMb⟩⟩
    let U := ProbDist.uniform (α := Fin M_b)
    ∑ b : Fin M_c → Fin M_b, (iidDist U M_c).pmf b * (if b v = b u then (1 : ℝ) else 0) =
      (1 : ℝ) / (M_b : ℝ) := by
  have : Nonempty (Fin M_b) := ⟨⟨0, hMb⟩⟩
  dsimp only
  let U := ProbDist.uniform (α := Fin M_b)
  have hind : ∀ b : Fin M_c → Fin M_b,
      (if b v = b u then (1 : ℝ) else 0) =
        ∑ m : Fin M_b, (if b u = m then (1 : ℝ) else 0) * (if b v = m then (1 : ℝ) else 0) := by
    intro b
    rw [Finset.sum_eq_single (b u)]
    · by_cases h : b v = b u <;> simp [h]
    · intro m _ hne_m; simp [hne_m.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hind, Finset.mul_sum]
  rw [Finset.sum_comm]
  have heach : ∀ m : Fin M_b,
      ∑ b : Fin M_c → Fin M_b, (iidDist U M_c).pmf b *
        ((if b u = m then (1 : ℝ) else 0) * (if b v = m then (1 : ℝ) else 0)) =
      ((1 : ℝ) / (M_b : ℝ)) * ((1 : ℝ) / (M_b : ℝ)) := by
    intro m
    rw [iidDist_sum_two_coords U (fun a => if a = m then (1 : ℝ) else 0)
        (fun a => if a = m then (1 : ℝ) else 0) hne.symm]
    have hsingle : ∑ a : Fin M_b, U.pmf a * (if a = m then (1 : ℝ) else 0) = (1 : ℝ) / (M_b : ℝ) := by
      rw [Finset.sum_eq_single m]
      · simp [U, ProbDist.uniform]
      · intro a _ hne_a; simp [hne_a]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsingle]
  rw [Finset.sum_congr rfl fun m _ => heach m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hMpos : (M_b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hMb)
  field_simp [hMpos]

private lemma wz_exists_le_of_expectation_le {Ω : Type*} [Fintype Ω] (W : ProbDist Ω)
    (f : Ω → ℝ) {B : ℝ} (h : ∑ ω : Ω, W.pmf ω * f ω ≤ B) :
    ∃ ω : Ω, f ω ≤ B := by
  by_contra hall
  push Not at hall
  have hex_pos : ∃ ω₀ : Ω, 0 < W.pmf ω₀ := by
    by_contra hnone
    push Not at hnone
    have hzero : ∑ ω : Ω, W.pmf ω = 0 :=
      Finset.sum_eq_zero fun ω _ => le_antisymm (hnone ω) (W.nonneg ω)
    linarith [W.sum_one]
  rcases hex_pos with ⟨ω₀, hω₀⟩
  have hlt : B < ∑ ω : Ω, W.pmf ω * f ω := by
    have hB : B = ∑ ω : Ω, W.pmf ω * B := by rw [← Finset.sum_mul, W.sum_one, one_mul]
    rw [hB]
    refine Finset.sum_lt_sum
      (fun ω _ => mul_le_mul_of_nonneg_left (le_of_lt (hall ω)) (W.nonneg ω))
      ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (hall ω₀) hω₀⟩
  linarith

private lemma wz_max_one_floor_two_rpow_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
  have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hfl : 1 ≤ Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := Nat.le_floor (by exact_mod_cast hge1)
  have hmax : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) =
      Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := Nat.max_eq_right hfl
  rw [hmax]
  exact Nat.floor_le (by positivity)

private lemma wz_half_two_rpow_le_max_one_floor (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
  let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.le_max_left 1 _
  have hfl : (2 : ℝ) ^ ((n : ℝ) * R) < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hle : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.le_max_right 1 _
  have _ := hR
  linarith

private lemma wz_covering_exp_le {I R ε c : ℝ} (hI : 0 ≤ I) (hε : 0 ≤ ε)
    (hR : I + 3 * ε < R) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))))) ≤ c := by
  have hR_pos : 0 < R := by linarith
  let η : ℝ := R - (I + 3 * ε)
  have hη : 0 < η := by dsimp [η]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / R)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / (c * η * Real.log 2))
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  set M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hn1 : 1 / R < (n : ℝ) :=
    lt_of_lt_of_le hN₁ (by exact_mod_cast le_trans (le_max_left N₁ N₂) hn)
  have hn2 : 2 / (c * η * Real.log 2) < (n : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn)
  have hnR : 1 ≤ (n : ℝ) * R := by
    have := (div_lt_iff₀ hR_pos).mp hn1; linarith
  have h2R : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR
  have hM_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * R) ≤ (M : ℝ) := by
    have hfl : (2 : ℝ) ^ ((n : ℝ) * R) - 1 < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) :=
      Nat.sub_one_lt_floor _
    have hleM : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast Nat.le_max_right 1 _
    linarith
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hprod_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * η) ≤
      (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by
    calc (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * η)
      _ = ((1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * R)) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2; dsimp [η]; ring
      _ ≤ (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM_ge (le_of_lt hpow_pos)
  have h2η : (n : ℝ) * η * Real.log 2 ≤ (2 : ℝ) ^ ((n : ℝ) * η) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := Real.add_one_le_exp (Real.log 2 * ((n : ℝ) * η))
    linarith
  have hlin : 1 / c ≤ (1 / 2 : ℝ) * ((n : ℝ) * η * Real.log 2) := by
    have h1 := (div_lt_iff₀ (by positivity : 0 < c * η * Real.log 2)).mp hn2
    rw [div_le_iff₀ hc]
    linarith
  have ht_ge : 1 / c ≤ (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by linarith
  have hexp_ge : 1 / c ≤ Real.exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))) := by
    have h := Real.add_one_le_exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))))
    linarith
  rw [Real.exp_neg]
  have hpos_inv : (0 : ℝ) < 1 / c := by positivity
  calc (Real.exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))))⁻¹
    _ ≤ (1 / c)⁻¹ := inv_anti₀ hpos_inv hexp_ge
    _ = c := by rw [one_div, inv_inv]

private lemma wz_two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
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

/-- Under the Markov chain `U — X — Y` (`I(U; Y | X) = 0`), we have the exact identity
    `I(X; U | Y) = I(X; U) - I(U; Y)`. -/
private lemma wz_condMutualInfo_eq_sub_of_markov {X Y U : Type*}
    [Fintype X] [Fintype Y] [Fintype U]
    (Q : ProbDist (X × Y × U))
    (hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0) :
    condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) =
      mutualInfo (Q.map (fun t => (t.1, t.2.2))) -
      mutualInfo (Q.map (fun t => (t.2.2, t.2.1))) := by
  let e1 : (X × Y × U) ≃ (U × Y × X) :=
    { toFun := fun t => (t.2.2, t.2.1, t.1)
      invFun := fun t => (t.2.2, t.2.1, t.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  let e2 : (X × Y × U) ≃ (X × U × Y) :=
    { toFun := fun t => (t.1, t.2.2, t.2.1)
      invFun := fun t => (t.1, t.2.2, t.2.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  set R1 : ProbDist (U × Y × X) := Q.map (fun t => (t.2.2, t.2.1, t.1))
  set R2 : ProbDist (X × U × Y) := Q.map (fun t => (t.1, t.2.2, t.2.1))
  set Qxu : ProbDist (X × U) := Q.map (fun t => (t.1, t.2.2))
  set Quy : ProbDist (U × Y) := Q.map (fun t => (t.2.2, t.2.1))
  set Qxy : ProbDist (X × Y) := Q.map (fun t => (t.1, t.2.1))
  have hQ1 : shannonEntropy R1 = shannonEntropy Q := shannonEntropy_map_equiv e1 Q
  have hQ2 : shannonEntropy R2 = shannonEntropy Q := shannonEntropy_map_equiv e2 Q
  have hUX : shannonEntropy (R1.map (fun t => (t.1, t.2.2))) = shannonEntropy Qxu := by
    have hswap : R1.map (fun t => (t.1, t.2.2)) = Qxu.map Prod.swap := by
      dsimp only [R1, Qxu]; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hswap, shannonEntropy_swap]
  have hYX : shannonEntropy (R1.map (fun t => (t.2.1, t.2.2))) = shannonEntropy Qxy := by
    have hswap : R1.map (fun t => (t.2.1, t.2.2)) = Qxy.map Prod.swap := by
      dsimp only [R1, Qxy]; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hswap, shannonEntropy_swap]
  have hXY2 : R2.map (fun t => (t.1, t.2.2)) = Qxy := by
    dsimp only [R2, Qxy]; rw [map_comp_eq]; rfl
  have hX1 : R1.map (fun t => t.2.2) = Qxu.fst := by
    rw [← wz_probDist_map_fst]; dsimp only [R1, Qxu]; rw [map_comp_eq, map_comp_eq]; rfl
  have hY2 : R2.map (fun t => t.2.2) = Quy.snd := by
    rw [← wz_probDist_map_snd]; dsimp only [R2, Quy]; rw [map_comp_eq, map_comp_eq]; rfl
  have hUY2 : R2.map (fun t => (t.2.1, t.2.2)) = Quy := by
    dsimp only [R2, Quy]; rw [map_comp_eq]; rfl
  have hU_eq : Qxu.snd = Quy.fst := by
    rw [← wz_probDist_map_snd, ← wz_probDist_map_fst]
    dsimp only [Qxu, Quy]; rw [map_comp_eq, map_comp_eq]; rfl
  have hm1 : shannonEntropy (R1.map (fun t => (t.1, t.2.2))) +
      shannonEntropy (R1.map (fun t => (t.2.1, t.2.2))) -
      shannonEntropy R1 - shannonEntropy (R1.map (fun t => t.2.2)) = 0 := hmarkov
  rw [hUX, hYX, hQ1, hX1] at hm1
  have hm2 : condMutualInfo R2 =
      shannonEntropy (R2.map (fun t => (t.1, t.2.2))) +
      shannonEntropy (R2.map (fun t => (t.2.1, t.2.2))) -
      shannonEntropy R2 - shannonEntropy (R2.map (fun t => t.2.2)) := rfl
  rw [hm2, hXY2, hUY2, hQ2, hY2]
  unfold mutualInfo
  rw [hU_eq]
  linarith

end SharedHelpers

/-! ### 1. Wyner–Ziv Rate–Distortion Function: Definitions, Basic Properties & Convexity -/

section WynerZivBasics

/-- **Single-Letter Wyner–Ziv Rate–Distortion Function** (Cover & Thomas Eq. 15.164;
    El Gamal–Kim Theorem 11.3):
    `R_WZ(D) = inf { I(X; U | Y) : U — X — Y, ∃ g, E[d(X, g(U, Y))] ≤ D }`. -/
noncomputable def wynerZivRateDistortion {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
    0 < kU ∧
    Q.map (fun t => (t.1, t.2.1)) = P ∧
    condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
    (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D ∧
    r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) }

/-- Feasibility predicate for a distortion level `D` in the Wyner–Ziv problem. -/
def IsWynerZivFeasible {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) : Prop :=
  ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
    0 < kU ∧
    Q.map (fun t => (t.1, t.2.1)) = P ∧
    condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
    (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D

/-- **Operational Wyner–Ziv Achievability** (Cover & Thomas §15.9; El Gamal–Kim §11.3):
    rate `R ≥ 0` is achievable at distortion `D` if for every `δ > 0`, eventually for all
    `n ≥ N` (`N > 0`) there exist an encoder `enc : (Fin n → X) → Fin M` and decoder
    `dec : Fin M → (Fin n → Y) → (Fin n → Xhat)` with `M = max 1 ⌊2^(n R)⌋` achieving
    expected per-symbol distortion at most `D + δ`. -/
def IsWynerZivAchievable {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ δ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : (Fin n → X) → Fin M) (dec : Fin M → (Fin n → Y) → (Fin n → Xhat)),
      ∑ xy : Fin n → X × Y, (iidDist P n).pmf xy *
        blockDist d (fun i => (xy i).1)
          (dec (enc (fun i => (xy i).1)) (fun i => (xy i).2)) ≤ D + δ

/-- **Operational Wyner–Ziv Rate–Distortion Function**: infimum of all operationally
    achievable rates at distortion level `D`. -/
noncomputable def operationalWynerZivRate {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]
    (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) : ℝ :=
  sInf { R : ℝ | IsWynerZivAchievable P d D R }

variable {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]

/-- Non-negativity of the Wyner–Ziv rate–distortion function: `R_WZ(D) ≥ 0`. -/
theorem wynerZivRateDistortion_nonneg (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) :
    0 ≤ wynerZivRateDistortion P d D := by
  unfold wynerZivRateDistortion
  refine Real.sInf_nonneg ?_
  rintro r ⟨_, Q, _, _, _, _, _, rfl⟩
  exact condMutualInfo_nonneg _

/-- Any valid single-letter witness `(kU, Q, g)` upper-bounds `wynerZivRateDistortion P d D`. -/
theorem wynerZivRateDistortion_le {P : ProbDist (X × Y)} {d : Distortion X Xhat} {D : ℝ}
    {kU : ℕ} {Q : ProbDist (X × Y × Fin kU)} {g : Fin kU × Y → Xhat}
    (hk : 0 < kU)
    (hmarg : Q.map (fun t => (t.1, t.2.1)) = P)
    (hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0)
    (hdist : (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D) :
    wynerZivRateDistortion P d D ≤ condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) := by
  unfold wynerZivRateDistortion
  refine csInf_le ⟨0, ?_⟩ ⟨kU, Q, g, hk, hmarg, hmarkov, hdist, rfl⟩
  rintro r ⟨_, Q', _, _, _, _, _, rfl⟩
  exact condMutualInfo_nonneg _

/-- Monotonicity (antitonicity) of `R_WZ(D)`: if `D₁` is feasible and `D₁ ≤ D₂`,
    then `R_WZ(D₂) ≤ R_WZ(D₁)`. -/
theorem wynerZivRateDistortion_antitone {P : ProbDist (X × Y)} {d : Distortion X Xhat}
    {D₁ D₂ : ℝ} (hfeas : IsWynerZivFeasible P d D₁) (hD : D₁ ≤ D₂) :
    wynerZivRateDistortion P d D₂ ≤ wynerZivRateDistortion P d D₁ := by
  unfold wynerZivRateDistortion
  refine csInf_le_csInf ⟨0, ?_⟩ ?_ ?_
  · rintro r ⟨_, Q', _, _, _, _, _, rfl⟩; exact condMutualInfo_nonneg _
  · rcases hfeas with ⟨kU, Q, g, hk, hmarg, hmarkov, hdist⟩
    exact ⟨_, kU, Q, g, hk, hmarg, hmarkov, hdist, rfl⟩
  · rintro r ⟨kU, Q, g, hk, hmarg, hmarkov, hdist, rfl⟩
    exact ⟨kU, Q, g, hk, hmarg, hmarkov, le_trans hdist hD, rfl⟩

/-- **Convexity of the Wyner–Ziv Rate–Distortion Function** (Cover & Thomas §15.9):
    for any `λ ∈ [0, 1]` and feasible distortions `D₁, D₂`,
    `R_WZ(λ D₁ + (1 - λ) D₂) ≤ λ R_WZ(D₁) + (1 - λ) R_WZ(D₂)`.

    Proved via disjoint-union time-sharing `U = U₁ ⊕ U₂` (embedded via `finSumFinEquiv`),
    which preserves `U — X — Y` and satisfies exact linearity of `I(X; U | Y)` and `E[d]`. -/
theorem wynerZivRateDistortion_convex {P : ProbDist (X × Y)} {d : Distortion X Xhat}
    {D₁ D₂ lam : ℝ}
    (hfeas₁ : IsWynerZivFeasible P d D₁) (hfeas₂ : IsWynerZivFeasible P d D₂)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    wynerZivRateDistortion P d (lam * D₁ + (1 - lam) * D₂) ≤
      lam * wynerZivRateDistortion P d D₁ + (1 - lam) * wynerZivRateDistortion P d D₂ := by
  classical
  have hbdd : ∀ D : ℝ, BddBelow { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU))
      (g : Fin kU × Y → Xhat), 0 < kU ∧ Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
      (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D ∧
      r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) } := fun _ =>
    ⟨0, by rintro r ⟨_, Q, _, _, _, _, _, rfl⟩; exact condMutualInfo_nonneg _⟩
  have hne₁ : { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
      0 < kU ∧ Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
      (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D₁ ∧
      r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) }.Nonempty := by
    rcases hfeas₁ with ⟨kU, Q, g, hk, hm, hmk, hd⟩
    exact ⟨_, kU, Q, g, hk, hm, hmk, hd, rfl⟩
  have hne₂ : { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
      0 < kU ∧ Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
      (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D₂ ∧
      r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) }.Nonempty := by
    rcases hfeas₂ with ⟨kU, Q, g, hk, hm, hmk, hd⟩
    exact ⟨_, kU, Q, g, hk, hm, hmk, hd, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨r₁, ⟨k₁, Q₁, g₁, hk₁, hm₁, hmk₁, hd₁, rfl⟩, hr₁⟩ :=
    (csInf_lt_iff (hbdd D₁) hne₁).mp (show wynerZivRateDistortion P d D₁ < wynerZivRateDistortion P d D₁ + ε by linarith)
  obtain ⟨r₂, ⟨k₂, Q₂, g₂, hk₂, hm₂, hmk₂, hd₂, rfl⟩, hr₂⟩ :=
    (csInf_lt_iff (hbdd D₂) hne₂).mp (show wynerZivRateDistortion P d D₂ < wynerZivRateDistortion P d D₂ + ε by linarith)
  -- Build disjoint-union mixture `Qsum` on `X × Y × (Fin k₁ ⊕ Fin k₂)`.
  let Qsum : ProbDist (X × Y × (Fin k₁ ⊕ Fin k₂)) :=
    { pmf := fun t => match t.2.2 with
        | Sum.inl u₁ => lam * Q₁.pmf (t.1, t.2.1, u₁)
        | Sum.inr u₂ => (1 - lam) * Q₂.pmf (t.1, t.2.1, u₂)
      nonneg := fun t => by
        cases t.2.2 with
        | inl u₁ => exact mul_nonneg h0 (Q₁.nonneg _)
        | inr u₂ => exact mul_nonneg (by linarith) (Q₂.nonneg _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        have hsum1 : ∑ a : X, ∑ b : Y, ∑ u₁ : Fin k₁, Q₁.pmf (a, b, u₁) = 1 := by
          simpa [Fintype.sum_prod_type] using Q₁.sum_one
        have hsum2 : ∑ a : X, ∑ b : Y, ∑ u₂ : Fin k₂, Q₂.pmf (a, b, u₂) = 1 := by
          simpa [Fintype.sum_prod_type] using Q₂.sum_one
        rw [hsum1, hsum2]; ring }
  -- Helper: `(X, Y)`-marginal pmf of `Q₁` and `Q₂` equals `P.pmf`.
  have hQ₁_xy : ∀ x y, ∑ u₁ : Fin k₁, Q₁.pmf (x, y, u₁) = P.pmf (x, y) := by
    intro x y
    have := congrArg (fun D : ProbDist (X × Y) => D.pmf (x, y)) hm₁
    unfold ProbDist.map at this; dsimp only at this
    rw [← this, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single y]
      · simp
      · intro y' _ hne; exact Finset.sum_eq_zero fun u₁ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro x' _ hne
      rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun u₁ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ₂_xy : ∀ x y, ∑ u₂ : Fin k₂, Q₂.pmf (x, y, u₂) = P.pmf (x, y) := by
    intro x y
    have := congrArg (fun D : ProbDist (X × Y) => D.pmf (x, y)) hm₂
    unfold ProbDist.map at this; dsimp only at this
    rw [← this, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single y]
      · simp
      · intro y' _ hne; exact Finset.sum_eq_zero fun u₂ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro x' _ hne
      rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun u₂ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Embed `Fin k₁ ⊕ Fin k₂ ≃ Fin (k₁ + k₂)`.
  let e : (Fin k₁ ⊕ Fin k₂) ≃ Fin (k₁ + k₂) := finSumFinEquiv
  let Q : ProbDist (X × Y × Fin (k₁ + k₂)) := Qsum.map (fun t => (t.1, t.2.1, e t.2.2))
  let g : Fin (k₁ + k₂) × Y → Xhat := fun uy =>
    match e.symm uy.1 with
    | Sum.inl u₁ => g₁ (u₁, uy.2)
    | Sum.inr u₂ => g₂ (u₂, uy.2)
  have hk_pos : 0 < k₁ + k₂ := by omega
  -- Check 1: `(X, Y)`-marginal of `Q` is `P`.
  have hQsum_marg : Qsum.map (fun t => (t.1, t.2.1)) = P := by
    unfold ProbDist.map
    congr; funext ⟨x, y⟩; dsimp only
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single y]
      · simp only [↓reduceIte, Qsum, Fintype.sum_sum_type, ← Finset.mul_sum, hQ₁_xy, hQ₂_xy]
        ring
      · intro y' _ hne; exact Finset.sum_eq_zero fun u _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro x' _ hne
      rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun u _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ_marg : Q.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q; rw [map_comp_eq]; exact hQsum_marg
  -- Check 2: Markov chain `U — X — Y` holds for `Qsum` (hence for `Q`).
  have hQsum_markov : condMutualInfo (Qsum.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    let R := Qsum.map (fun t => (t.2.2, t.2.1, t.1))
    let R₁ := Q₁.map (fun t => (t.2.2, t.2.1, t.1))
    let R₂ := Q₂.map (fun t => (t.2.2, t.2.1, t.1))
    have hR₁_ci : R₁ = condIndepDist R₁ := (condMutualInfo_eq_zero_iff R₁).mp hmk₁
    have hR₂_ci : R₂ = condIndepDist R₂ := (condMutualInfo_eq_zero_iff R₂).mp hmk₂
    -- Explicit pmfs for `R`, `R₁`, `R₂` and their marginals.
    let eR {U : Type} : (X × Y × U) ≃ (U × Y × X) :=
      { toFun := fun t => (t.2.2, t.2.1, t.1)
        invFun := fun t => (t.2.2, t.2.1, t.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hR_pmf : ∀ u y x, R.pmf (u, y, x) = Qsum.pmf (x, y, u) := fun u y x =>
      wz_probDist_map_equiv_pmf eR Qsum (u, y, x)
    have hR₁_pmf : ∀ u₁ y x, R₁.pmf (u₁, y, x) = Q₁.pmf (x, y, u₁) := fun u₁ y x =>
      wz_probDist_map_equiv_pmf eR Q₁ (u₁, y, x)
    have hR₂_pmf : ∀ u₂ y x, R₂.pmf (u₂, y, x) = Q₂.pmf (x, y, u₂) := fun u₂ y x =>
      wz_probDist_map_equiv_pmf eR Q₂ (u₂, y, x)
    have hR_yz : R.map (fun t => (t.2.1, t.2.2)) = P.map Prod.swap := by
      unfold R; rw [map_comp_eq, ← hQsum_marg, map_comp_eq]; rfl
    have hR₁_yz : R₁.map (fun t => (t.2.1, t.2.2)) = P.map Prod.swap := by
      unfold R₁; rw [map_comp_eq, ← hm₁, map_comp_eq]; rfl
    have hR₂_yz : R₂.map (fun t => (t.2.1, t.2.2)) = P.map Prod.swap := by
      unfold R₂; rw [map_comp_eq, ← hm₂, map_comp_eq]; rfl
    have hR_z : R.map (fun t => t.2.2) = P.fst := by
      unfold R; rw [map_comp_eq, ← wz_probDist_map_fst, ← hQsum_marg, map_comp_eq]; rfl
    have hR₁_z : R₁.map (fun t => t.2.2) = P.fst := by
      unfold R₁; rw [map_comp_eq, ← wz_probDist_map_fst, ← hm₁, map_comp_eq]; rfl
    have hR₂_z : R₂.map (fun t => t.2.2) = P.fst := by
      unfold R₂; rw [map_comp_eq, ← wz_probDist_map_fst, ← hm₂, map_comp_eq]; rfl
    have hR_xz_inl : ∀ u₁ x, (R.map (fun t => (t.1, t.2.2))).pmf (Sum.inl u₁, x) =
        lam * (R₁.map (fun t => (t.1, t.2.2))).pmf (u₁, x) := by
      intro u₁ x
      unfold ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (Sum.inl u₁)]
      · rw [Finset.sum_eq_single u₁]
        · rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x' _ => ?_
          by_cases hx : x' = x
          · simp [hx, hR_pmf, hR₁_pmf, Qsum]
          · simp [hx]
        · intro u₁' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x' _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro u' _ hne; rw [Fintype.sum_prod_type]
        exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x' _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_xz_inr : ∀ u₂ x, (R.map (fun t => (t.1, t.2.2))).pmf (Sum.inr u₂, x) =
        (1 - lam) * (R₂.map (fun t => (t.1, t.2.2))).pmf (u₂, x) := by
      intro u₂ x
      unfold ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (Sum.inr u₂)]
      · rw [Finset.sum_eq_single u₂]
        · rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x' _ => ?_
          by_cases hx : x' = x
          · simp [hx, hR_pmf, hR₂_pmf, Qsum]
          · simp [hx]
        · intro u₂' _ hne; rw [Fintype.sum_prod_type]
          exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x' _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro u' _ hne; rw [Fintype.sum_prod_type]
        exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x' _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [condMutualInfo_eq_zero_iff]
    refine wz_probDist_ext fun ⟨u, y, x⟩ => ?_
    change R.pmf (u, y, x) = if (R.map (fun t => t.2.2)).pmf x = 0 then 0
      else (R.map (fun t => (t.1, t.2.2))).pmf (u, x) *
        (R.map (fun t => (t.2.1, t.2.2))).pmf (y, x) / (R.map (fun t => t.2.2)).pmf x
    cases u with
    | inl u₁ =>
      have h1 := congrArg (fun D : ProbDist (Fin k₁ × Y × X) => D.pmf (u₁, y, x)) hR₁_ci
      change R₁.pmf (u₁, y, x) = if (R₁.map (fun t => t.2.2)).pmf x = 0 then 0
        else (R₁.map (fun t => (t.1, t.2.2))).pmf (u₁, x) *
          (R₁.map (fun t => (t.2.1, t.2.2))).pmf (y, x) / (R₁.map (fun t => t.2.2)).pmf x at h1
      rw [hR_pmf, hR_xz_inl, hR_yz, hR_z]
      rw [hR₁_pmf, hR₁_yz, hR₁_z] at h1
      dsimp only [Qsum]
      rw [h1]
      split_ifs <;> ring
    | inr u₂ =>
      have h2 := congrArg (fun D : ProbDist (Fin k₂ × Y × X) => D.pmf (u₂, y, x)) hR₂_ci
      change R₂.pmf (u₂, y, x) = if (R₂.map (fun t => t.2.2)).pmf x = 0 then 0
        else (R₂.map (fun t => (t.1, t.2.2))).pmf (u₂, x) *
          (R₂.map (fun t => (t.2.1, t.2.2))).pmf (y, x) / (R₂.map (fun t => t.2.2)).pmf x at h2
      rw [hR_pmf, hR_xz_inr, hR_yz, hR_z]
      rw [hR₂_pmf, hR₂_yz, hR₂_z] at h2
      dsimp only [Qsum]
      rw [h2]
      split_ifs <;> ring
  have hQ_markov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    unfold Q
    rw [map_comp_eq]
    have hcomp : ((fun t : X × Y × Fin (k₁ + k₂) => (t.2.2, t.2.1, t.1)) ∘
        fun t : X × Y × (Fin k₁ ⊕ Fin k₂) => (t.1, t.2.1, e t.2.2)) =
        (fun t : (Fin k₁ ⊕ Fin k₂) × Y × X => (e t.1, t.2.1, t.2.2)) ∘
          fun t : X × Y × (Fin k₁ ⊕ Fin k₂) => (t.2.2, t.2.1, t.1) := rfl
    rw [hcomp, ← map_comp_eq, wz_condMutualInfo_map_fst_equiv, hQsum_markov]
  -- Check 3: Expected distortion of `(Q, g)` is `≤ lam * D₁ + (1 - lam) * D₂`.
  have hQ_dist : (∑ t : X × Y × Fin (k₁ + k₂), Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤
      lam * D₁ + (1 - lam) * D₂ := by
    unfold Q
    rw [← sum_pmf_mul_comp Qsum (fun t => (t.1, t.2.1, e t.2.2))
      (fun t => d.dist t.1 (g (t.2.2, t.2.1)))]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Finset.sum_add_distrib]
    have hsum1 : ∑ a : X, ∑ b : Y, ∑ u₁ : Fin k₁,
        Qsum.pmf (a, b, Sum.inl u₁) * d.dist a (g (e (Sum.inl u₁), b)) =
        lam * ∑ t : X × Y × Fin k₁, Q₁.pmf t * d.dist t.1 (g₁ (t.2.2, t.2.1)) := by
      rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun u₁ _ => ?_
      simp only [Qsum, g, Equiv.symm_apply_apply]; ring
    have hsum2 : ∑ a : X, ∑ b : Y, ∑ u₂ : Fin k₂,
        Qsum.pmf (a, b, Sum.inr u₂) * d.dist a (g (e (Sum.inr u₂), b)) =
        (1 - lam) * ∑ t : X × Y × Fin k₂, Q₂.pmf t * d.dist t.1 (g₂ (t.2.2, t.2.1)) := by
      rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun u₂ _ => ?_
      simp only [Qsum, g, Equiv.symm_apply_apply]; ring
    rw [hsum1, hsum2]
    have h1' := mul_le_mul_of_nonneg_left hd₁ h0
    have h2' := mul_le_mul_of_nonneg_left hd₂ (show 0 ≤ 1 - lam by linarith)
    linarith
  -- Check 4: Exact linearity `I_{Q}(X; U | Y) = lam * I_{Q₁}(X; U₁ | Y) + (1 - lam) * I_{Q₂}(X; U₂ | Y)`.
  have hQ_cmi : condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) =
      lam * condMutualInfo (Q₁.map (fun t => (t.1, t.2.2, t.2.1))) +
      (1 - lam) * condMutualInfo (Q₂.map (fun t => (t.1, t.2.2, t.2.1))) := by
    have hQ_eq_sum : condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) =
        condMutualInfo (Qsum.map (fun t => (t.1, t.2.2, t.2.1))) := by
      unfold Q; rw [map_comp_eq]
      have hcomp : ((fun t : X × Y × Fin (k₁ + k₂) => (t.1, t.2.2, t.2.1)) ∘
          fun t : X × Y × (Fin k₁ ⊕ Fin k₂) => (t.1, t.2.1, e t.2.2)) =
          (fun t : X × (Fin k₁ ⊕ Fin k₂) × Y => (t.1, e t.2.1, t.2.2)) ∘
            fun t : X × Y × (Fin k₁ ⊕ Fin k₂) => (t.1, t.2.2, t.2.1) := rfl
      rw [hcomp, ← map_comp_eq, wz_condMutualInfo_map_snd_equiv]
    rw [hQ_eq_sum]
    let e2 {U : Type} : (X × Y × U) ≃ (X × U × Y) :=
      { toFun := fun t => (t.1, t.2.2, t.2.1)
        invFun := fun t => (t.1, t.2.2, t.2.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hH_all : shannonEntropy Qsum =
        binaryEntropy lam + lam * shannonEntropy Q₁ + (1 - lam) * shannonEntropy Q₂ := by
      unfold shannonEntropy binaryEntropy
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      change ∑ a : X, ∑ b : Y,
          ((∑ u₁ : Fin k₁, negPLogP (lam * Q₁.pmf (a, b, u₁))) +
           (∑ u₂ : Fin k₂, negPLogP ((1 - lam) * Q₂.pmf (a, b, u₂)))) = _
      simp_rw [Finset.sum_add_distrib]
      have h1_part : ∑ a : X, ∑ b : Y, ∑ u₁ : Fin k₁, negPLogP (lam * Q₁.pmf (a, b, u₁)) =
          negPLogP lam + lam * ∑ a : X, ∑ b : Y, ∑ u₁ : Fin k₁, negPLogP (Q₁.pmf (a, b, u₁)) := by
        simp_rw [negPLogP_mul h0 (Q₁.nonneg _), Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul]
        have hsum1 : ∑ a : X, ∑ b : Y, ∑ u₁ : Fin k₁, Q₁.pmf (a, b, u₁) = 1 := by
          simpa [Fintype.sum_prod_type] using Q₁.sum_one
        rw [hsum1]; ring
      have h2_part : ∑ a : X, ∑ b : Y, ∑ u₂ : Fin k₂, negPLogP ((1 - lam) * Q₂.pmf (a, b, u₂)) =
          negPLogP (1 - lam) + (1 - lam) * ∑ a : X, ∑ b : Y, ∑ u₂ : Fin k₂, negPLogP (Q₂.pmf (a, b, u₂)) := by
        simp_rw [negPLogP_mul (by linarith : 0 ≤ 1 - lam) (Q₂.nonneg _), Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul]
        have hsum2 : ∑ a : X, ∑ b : Y, ∑ u₂ : Fin k₂, Q₂.pmf (a, b, u₂) = 1 := by
          simpa [Fintype.sum_prod_type] using Q₂.sum_one
        rw [hsum2]; ring
      rw [h1_part, h2_part]; ring
    have hH_UY : shannonEntropy (Qsum.map (fun t => (t.2.2, t.2.1))) =
        binaryEntropy lam + lam * shannonEntropy (Q₁.map (fun t => (t.2.2, t.2.1))) +
        (1 - lam) * shannonEntropy (Q₂.map (fun t => (t.2.2, t.2.1))) := by
      have hpmf_inl : ∀ u₁ y, (Qsum.map (fun t => (t.2.2, t.2.1))).pmf (Sum.inl u₁, y) =
          lam * (Q₁.map (fun t => (t.2.2, t.2.1))).pmf (u₁, y) := by
        intro u₁ y
        unfold ProbDist.map; dsimp only
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        by_cases hy : y' = y
        · subst hy
          rw [Finset.sum_eq_single (Sum.inl u₁), Finset.sum_eq_single u₁]
          · simp [Qsum]
          · intro u₁' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
          · intro u' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp [hy]
      have hpmf_inr : ∀ u₂ y, (Qsum.map (fun t => (t.2.2, t.2.1))).pmf (Sum.inr u₂, y) =
          (1 - lam) * (Q₂.map (fun t => (t.2.2, t.2.1))).pmf (u₂, y) := by
        intro u₂ y
        unfold ProbDist.map; dsimp only
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        by_cases hy : y' = y
        · subst hy
          rw [Finset.sum_eq_single (Sum.inr u₂), Finset.sum_eq_single u₂]
          · simp [Qsum]
          · intro u₂' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
          · intro u' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp [hy]
      unfold shannonEntropy binaryEntropy
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
      simp_rw [hpmf_inl, hpmf_inr]
      have h1_part : ∑ u₁ : Fin k₁, ∑ y : Y,
          negPLogP (lam * (Q₁.map (fun t => (t.2.2, t.2.1))).pmf (u₁, y)) =
          negPLogP lam + lam * ∑ uy : Fin k₁ × Y, negPLogP ((Q₁.map (fun t => (t.2.2, t.2.1))).pmf uy) := by
        simp_rw [negPLogP_mul h0 ((Q₁.map (fun t => (t.2.2, t.2.1))).nonneg _),
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        have hsum1 : ∑ u₁ : Fin k₁, ∑ y : Y, (Q₁.map (fun t => (t.2.2, t.2.1))).pmf (u₁, y) = 1 := by
          simpa [Fintype.sum_prod_type] using (Q₁.map (fun t => (t.2.2, t.2.1))).sum_one
        have hsum1' : ∑ u₁ : Fin k₁, ∑ y : Y, negPLogP ((Q₁.map (fun t => (t.2.2, t.2.1))).pmf (u₁, y)) =
            ∑ uy : Fin k₁ × Y, negPLogP ((Q₁.map (fun t => (t.2.2, t.2.1))).pmf uy) := by
          simp [Fintype.sum_prod_type]
        rw [hsum1, hsum1']; ring
      have h2_part : ∑ u₂ : Fin k₂, ∑ y : Y,
          negPLogP ((1 - lam) * (Q₂.map (fun t => (t.2.2, t.2.1))).pmf (u₂, y)) =
          negPLogP (1 - lam) + (1 - lam) * ∑ uy : Fin k₂ × Y, negPLogP ((Q₂.map (fun t => (t.2.2, t.2.1))).pmf uy) := by
        simp_rw [negPLogP_mul (by linarith : 0 ≤ 1 - lam) ((Q₂.map (fun t => (t.2.2, t.2.1))).nonneg _),
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        have hsum2 : ∑ u₂ : Fin k₂, ∑ y : Y, (Q₂.map (fun t => (t.2.2, t.2.1))).pmf (u₂, y) = 1 := by
          simpa [Fintype.sum_prod_type] using (Q₂.map (fun t => (t.2.2, t.2.1))).sum_one
        have hsum2' : ∑ u₂ : Fin k₂, ∑ y : Y, negPLogP ((Q₂.map (fun t => (t.2.2, t.2.1))).pmf (u₂, y)) =
            ∑ uy : Fin k₂ × Y, negPLogP ((Q₂.map (fun t => (t.2.2, t.2.1))).pmf uy) := by
          simp [Fintype.sum_prod_type]
        rw [hsum2, hsum2']; ring
      rw [h1_part, h2_part]; ring
    unfold condMutualInfo
    dsimp only
    rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq,
      map_comp_eq, map_comp_eq, map_comp_eq]
    have hxy_s : Qsum.map ((fun t : X × (Fin k₁ ⊕ Fin k₂) × Y => (t.1, t.2.2)) ∘
        fun t => (t.1, t.2.2, t.2.1)) = P := hQsum_marg
    have hxy_1 : Q₁.map ((fun t : X × Fin k₁ × Y => (t.1, t.2.2)) ∘
        fun t => (t.1, t.2.2, t.2.1)) = P := hm₁
    have hxy_2 : Q₂.map ((fun t : X × Fin k₂ × Y => (t.1, t.2.2)) ∘
        fun t => (t.1, t.2.2, t.2.1)) = P := hm₂
    have hy_s : Qsum.map ((fun t : X × (Fin k₁ ⊕ Fin k₂) × Y => t.2.2) ∘
        fun t => (t.1, t.2.2, t.2.1)) = P.snd := by
      rw [← wz_probDist_map_snd, ← hQsum_marg, map_comp_eq]; rfl
    have hy_1 : Q₁.map ((fun t : X × Fin k₁ × Y => t.2.2) ∘
        fun t => (t.1, t.2.2, t.2.1)) = P.snd := by
      rw [← wz_probDist_map_snd, ← hm₁, map_comp_eq]; rfl
    have hy_2 : Q₂.map ((fun t : X × Fin k₂ × Y => t.2.2) ∘
        fun t => (t.1, t.2.2, t.2.1)) = P.snd := by
      rw [← wz_probDist_map_snd, ← hm₂, map_comp_eq]; rfl
    have hE_s : shannonEntropy (Qsum.map (fun t => (t.1, t.2.2, t.2.1))) = shannonEntropy Qsum :=
      shannonEntropy_map_equiv e2 Qsum
    have hE_1 : shannonEntropy (Q₁.map (fun t => (t.1, t.2.2, t.2.1))) = shannonEntropy Q₁ :=
      shannonEntropy_map_equiv e2 Q₁
    have hE_2 : shannonEntropy (Q₂.map (fun t => (t.1, t.2.2, t.2.1))) = shannonEntropy Q₂ :=
      shannonEntropy_map_equiv e2 Q₂
    rw [hxy_s, hxy_1, hxy_2, hy_s, hy_1, hy_2, hE_s, hE_1, hE_2, hH_all]
    change shannonEntropy P + shannonEntropy (Qsum.map (fun t => (t.2.2, t.2.1))) -
        (binaryEntropy lam + lam * shannonEntropy Q₁ + (1 - lam) * shannonEntropy Q₂) -
        shannonEntropy P.snd =
      lam * (shannonEntropy P + shannonEntropy (Q₁.map (fun t => (t.2.2, t.2.1))) -
        shannonEntropy Q₁ - shannonEntropy P.snd) +
      (1 - lam) * (shannonEntropy P + shannonEntropy (Q₂.map (fun t => (t.2.2, t.2.1))) -
        shannonEntropy Q₂ - shannonEntropy P.snd)
    rw [hH_UY]; ring
  have hle_Q : wynerZivRateDistortion P d (lam * D₁ + (1 - lam) * D₂) ≤
      condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) :=
    wynerZivRateDistortion_le hk_pos hQ_marg hQ_markov hQ_dist
  rw [hQ_cmi] at hle_Q
  have h1' : lam * condMutualInfo (Q₁.map (fun t => (t.1, t.2.2, t.2.1))) ≤
      lam * (wynerZivRateDistortion P d D₁ + ε) :=
    mul_le_mul_of_nonneg_left (le_of_lt hr₁) h0
  have h2' : (1 - lam) * condMutualInfo (Q₂.map (fun t => (t.1, t.2.2, t.2.1))) ≤
      (1 - lam) * (wynerZivRateDistortion P d D₂ + ε) :=
    mul_le_mul_of_nonneg_left (le_of_lt hr₂) (by linarith)
  linarith

/-- **Right-Continuity of `R_WZ(D)` at Every Strictly Feasible Distortion** (`D > D_min`):
    if there exists `D₀ < D` with `IsWynerZivFeasible P d D₀`, then for every `ε > 0`
    there exists `δ > 0` such that `R_WZ(D) - ε ≤ R_WZ(D + δ)`. -/
theorem wynerZivRateDistortion_rightContinuous (P : ProbDist (X × Y)) (d : Distortion X Xhat)
    {D : ℝ} (hstrict : ∃ D₀ : ℝ, D₀ < D ∧ IsWynerZivFeasible P d D₀) :
    ∀ ε > 0, ∃ δ > 0, wynerZivRateDistortion P d D - ε ≤ wynerZivRateDistortion P d (D + δ) := by
  rcases hstrict with ⟨D₀, hD₀_lt, hfeas₀⟩
  intro ε hε
  have hgap : 0 < D - D₀ := by linarith
  let R₀ := wynerZivRateDistortion P d D₀
  have hR₀0 : 0 ≤ R₀ := wynerZivRateDistortion_nonneg P d D₀
  let δ : ℝ := ε * (D - D₀) / (R₀ + 1)
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, ?_⟩
  have hfeas_plus : IsWynerZivFeasible P d (D + δ) := by
    rcases hfeas₀ with ⟨kU, Q, g, hk, hm, hmk, hd⟩
    exact ⟨kU, Q, g, hk, hm, hmk, by linarith⟩
  let lam : ℝ := (D - D₀) / (D + δ - D₀)
  have hden : 0 < D + δ - D₀ := by linarith
  have hlam0 : 0 ≤ lam := div_nonneg (le_of_lt hgap) (le_of_lt hden)
  have hlam1 : lam ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hconv_D : lam * (D + δ) + (1 - lam) * D₀ = D := by
    dsimp only [lam]
    field_simp [ne_of_gt hden]
    ring
  have hconv := wynerZivRateDistortion_convex hfeas_plus hfeas₀ hlam0 hlam1
  rw [hconv_D] at hconv
  have hRplus0 : 0 ≤ wynerZivRateDistortion P d (D + δ) :=
    wynerZivRateDistortion_nonneg P d (D + δ)
  have hterm1 : lam * wynerZivRateDistortion P d (D + δ) ≤ wynerZivRateDistortion P d (D + δ) := by
    nlinarith
  have h1mlam : 1 - lam = δ / (D + δ - D₀) := by
    dsimp only [lam]
    field_simp [ne_of_gt hden]
    ring
  have hterm2 : (1 - lam) * R₀ ≤ ε := by
    rw [h1mlam]
    have hle1 : δ / (D + δ - D₀) ≤ δ / (D - D₀) :=
      div_le_div_of_nonneg_left (le_of_lt hδ) hgap (by linarith)
    have hle2 : (δ / (D - D₀)) * R₀ ≤ ε := by
      dsimp only [δ]
      have heq : (ε * (D - D₀) / (R₀ + 1) / (D - D₀)) * R₀ = ε * (R₀ / (R₀ + 1)) := by
        field_simp [ne_of_gt hgap, show R₀ + 1 ≠ 0 by linarith]
      rw [heq]
      have hfrac : R₀ / (R₀ + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      nlinarith
    have hle3 : (δ / (D + δ - D₀)) * R₀ ≤ (δ / (D - D₀)) * R₀ :=
      mul_le_mul_of_nonneg_right hle1 hR₀0
    linarith
  linarith

end WynerZivBasics

/-! ### 2. Wyner–Ziv Converse (Cover & Thomas §15.9; El Gamal–Kim §11.3) -/

section WynerZivConverse

/-- Erase coordinate `i` of a vector `y : Fin n → Y`, recording all other coordinates
    `y^{\setminus i}` in an `i`-independent finite type `Fin n → Option Y`. -/
private def otherY {Y : Type*} {n : ℕ} (i : Fin n) (y : Fin n → Y) : Fin n → Option Y :=
  fun j => if j = i then none else some (y j)

/-- Reconstruct the full vector `y : Fin n → Y` from `(i, otherY i y, y i)`. -/
private def reconstructY {Y : Type*} {n : ℕ} (i : Fin n) (o : Fin n → Option Y) (yi : Y) :
    Fin n → Y :=
  fun j => if j = i then yi else (o j).getD yi

private lemma reconstructY_otherY {Y : Type*} {n : ℕ} (i : Fin n) (y : Fin n → Y) :
    reconstructY i (otherY i y) (y i) = y := by
  funext j
  unfold reconstructY otherY
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Equivalence splitting `Fin n → α` into coordinate `i` and `{ j : Fin n // j ≠ i } → α`. -/
private def splitCoordEquiv {α : Type*} {n : ℕ} (i : Fin n) :
    (Fin n → α) ≃ (α × ({ j : Fin n // j ≠ i } → α)) where
  toFun := fun z => (z i, fun j => z j.1)
  invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
  left_inv := fun z => by
    funext j; dsimp only; split_ifs with h
    · subst h; rfl
    · rfl
  right_inv := fun ⟨a, r⟩ => by
    ext
    · simp
    · rename_i j; simp [j.2]

variable {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]

/-- **Wyner–Ziv Converse** (Cover & Thomas §15.9, Theorem 15.9.1 converse;
    El Gamal–Kim §11.3, Theorem 11.3 converse):
    for any blocklength `n ≥ 1`, rate index size `M ≥ 1`, encoder `enc : (Fin n → X) → Fin M`,
    and decoder `dec : Fin M → (Fin n → Y) → (Fin n → Xhat)` achieving expected per-symbol
    distortion `≤ D` on an i.i.d. correlated source `P`,
    `wynerZivRateDistortion P d D ≤ log₂ M / n`. -/
theorem wynerZiv_converse (P : ProbDist (X × Y)) (d : Distortion X Xhat) {n M : ℕ}
    (hn : 0 < n) (hM : 0 < M)
    (enc : (Fin n → X) → Fin M) (dec : Fin M → (Fin n → Y) → (Fin n → Xhat)) {D : ℝ}
    (hdist : ∑ xy : Fin n → X × Y, (iidDist P n).pmf xy *
      blockDist d (fun i => (xy i).1)
        (dec (enc (fun i => (xy i).1)) (fun i => (xy i).2)) ≤ D) :
    wynerZivRateDistortion P d D ≤ log2 (M : ℝ) / (n : ℝ) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let Pn : ProbDist (Fin n → X × Y) := iidDist P n
  let xs : (Fin n → X × Y) → (Fin n → X) := fun z i => (z i).1
  let ys : (Fin n → X × Y) → (Fin n → Y) := fun z i => (z i).2
  let Uraw := Fin n × Fin M × (Fin n → Option Y)
  have hUraw_ne : Nonempty Uraw := ⟨(⟨0, hn⟩, ⟨0, hM⟩, fun _ => none)⟩
  let kU : ℕ := Fintype.card Uraw
  have hkU : 0 < kU := Fintype.card_pos
  let eU : Uraw ≃ Fin kU := Fintype.equivFin Uraw
  let UnifN : ProbDist (Fin n) := ProbDist.uniform
  let Qraw : ProbDist (X × Y × Uraw) :=
    (UnifN.prod Pn).map (fun qz => ((qz.2 qz.1).1, (qz.2 qz.1).2,
      (qz.1, enc (xs qz.2), otherY qz.1 (ys qz.2))))
  let Q : ProbDist (X × Y × Fin kU) := Qraw.map (fun t => (t.1, t.2.1, eU t.2.2))
  let g : Fin kU × Y → Xhat := fun uy =>
    let u := eU.symm uy.1
    dec u.2.1 (reconstructY u.1 u.2.2 uy.2) u.1
  -- Step 1: `(X_Q, Y_Q) ~ P`.
  have hQraw_marg : Qraw.map (fun t => (t.1, t.2.1)) = P := by
    unfold Qraw; rw [map_comp_eq]
    unfold ProbDist.map ProbDist.prod
    congr; funext xy; dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ q : Fin n,
        (∑ z : Fin n → X × Y, if ((z q).1, (z q).2) = xy then UnifN.pmf q * Pn.pmf z else 0) =
          UnifN.pmf q * P.pmf xy := fun q => by
      have h1 : (∑ z : Fin n → X × Y, if ((z q).1, (z q).2) = xy then UnifN.pmf q * Pn.pmf z else 0) =
          UnifN.pmf q * (Pn.map (fun z => z q)).pmf xy := by
        unfold ProbDist.map; dsimp only; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by
          have heta : ((z q).1, (z q).2) = z q := Prod.mk.eta
          rw [heta]; split_ifs <;> ring
      rw [h1, wz_iidDist_map_coord]
    simp_rw [hinner]
    rw [← Finset.sum_mul, UnifN.sum_one, one_mul]
  have hQ_marg : Q.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q; rw [map_comp_eq]; exact hQraw_marg
  -- Step 2: Expected distortion `E_Q[d(X_Q, g(U, Y_Q))] ≤ D`.
  have hQ_dist : (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D := by
    unfold Q Qraw
    rw [map_comp_eq, ← sum_pmf_mul_comp (UnifN.prod Pn)]
    dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hrew : (∑ z : Fin n → X × Y, ∑ q : Fin n,
        (UnifN.prod Pn).pmf (q, z) *
          d.dist (z q).1 (g (eU (q, enc (xs z), otherY q (ys z)), (z q).2))) =
        ∑ z : Fin n → X × Y, Pn.pmf z * blockDist d (xs z) (dec (enc (xs z)) (ys z)) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      unfold blockDist
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hg_eq : g (eU (q, enc (xs z), otherY q (ys z)), (z q).2) =
          dec (enc (xs z)) (ys z) q := by
        dsimp only [g]
        rw [Equiv.symm_apply_apply]
        change dec (enc (xs z)) (reconstructY q (otherY q (ys z)) (ys z q)) q = _
        rw [reconstructY_otherY]
      rw [hg_eq]
      dsimp only [ProbDist.prod, UnifN, ProbDist.uniform, xs]
      rw [Fintype.card_fin]
      ring
    exact le_trans (le_of_eq hrew) hdist
  -- Step 3: Markov chain `U — X_Q — Y_Q`, i.e., `I(U; Y_Q | X_Q) = 0`.
  have hQraw_markov : condMutualInfo (Qraw.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    let R := Qraw.map (fun t => (t.2.2, t.2.1, t.1))
    -- Factor `R.pmf ((i, t, o), y, x) = UnifN.pmf i * P.pmf (x, y) * S(i, t, o, x)`.
    let restSum (i : Fin n) (t : Fin M) (o : Fin n → Option Y) (x : X) : ℝ :=
      ∑ r : { j : Fin n // j ≠ i } → X × Y,
        if enc (fun j => if h : j = i then x else (r ⟨j, h⟩).1) = t ∧
           (fun j => if h : j = i then (none : Option Y) else some (r ⟨j, h⟩).2) = o
        then ∏ j : { j : Fin n // j ≠ i }, P.pmf (r j) else 0
    have hR_pmf : ∀ (i : Fin n) (t : Fin M) (o : Fin n → Option Y) (y : Y) (x : X),
        R.pmf ((i, t, o), y, x) = UnifN.pmf i * P.pmf (x, y) * restSum i t o x := by
      intro i t o y x
      unfold R Qraw
      rw [map_comp_eq]
      unfold ProbDist.map ProbDist.prod
      dsimp only
      rw [Fintype.sum_prod_type]
      dsimp only [Function.comp_apply]
      rw [Finset.sum_eq_single i]
      · -- Evaluate sum over `z : Fin n → X × Y` via `splitCoordEquiv i`.
        have hsum_z := Fintype.sum_equiv (splitCoordEquiv (α := X × Y) i)
          (fun z : Fin n → X × Y =>
            if ((i, enc (xs z), otherY i (ys z)), (z i).2, (z i).1) = ((i, t, o), y, x)
            then UnifN.pmf i * Pn.pmf z else 0)
          (fun pr : (X × Y) × ({ j : Fin n // j ≠ i } → X × Y) =>
            let z := (splitCoordEquiv (α := X × Y) i).symm pr
            if ((i, enc (xs z), otherY i (ys z)), (z i).2, (z i).1) = ((i, t, o), y, x)
            then UnifN.pmf i * Pn.pmf z else 0)
          (fun z => by simp)
        trans (∑ z : Fin n → X × Y,
            if ((i, enc (xs z), otherY i (ys z)), (z i).2, (z i).1) = ((i, t, o), y, x)
            then UnifN.pmf i * Pn.pmf z else 0)
        · refine Finset.sum_congr rfl fun z _ => ?_
          by_cases h : ((i, enc (xs z), otherY i (ys z)), (z i).2, (z i).1) = ((i, t, o), y, x) <;>
            simp [h]
        rw [hsum_z, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single (x, y)]
        · unfold restSum
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          set z := (splitCoordEquiv (α := X × Y) i).symm ((x, y), r)
          have hzi : z i = (x, y) := by simp [z, splitCoordEquiv]
          have hxs : xs z = fun j => if h : j = i then x else (r ⟨j, h⟩).1 := by
            funext j; by_cases h : j = i <;> simp [xs, z, splitCoordEquiv, h]
          have hoy : otherY i (ys z) =
              fun j => if h : j = i then (none : Option Y) else some (r ⟨j, h⟩).2 := by
            funext j; by_cases h : j = i <;> simp [otherY, ys, z, splitCoordEquiv, h]
          have hPn : Pn.pmf z = P.pmf (x, y) * ∏ j : { j : Fin n // j ≠ i }, P.pmf (r j) := by
            unfold Pn iidDist; dsimp only
            rw [← Finset.mul_prod_erase Finset.univ (fun j => P.pmf (z j)) (Finset.mem_univ i),
              hzi]
            congr 1
            let eErase : { j : Fin n // j ≠ i } ≃ Finset.univ.erase i :=
              { toFun := fun j => ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ j.1⟩⟩
                invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
                left_inv := fun ⟨_, _⟩ => rfl
                right_inv := fun ⟨_, _⟩ => rfl }
            rw [← Finset.prod_coe_sort (Finset.univ.erase i)]
            exact (Fintype.prod_equiv eErase _ _ (fun j => by
              simp [eErase, z, splitCoordEquiv, j.2])).symm
          have hiff : (((i, enc (xs z), otherY i (ys z)), (z i).2, (z i).1) = ((i, t, o), y, x)) ↔
              (enc (fun j => if h : j = i then x else (r ⟨j, h⟩).1) = t ∧
               (fun j => if h : j = i then (none : Option Y) else some (r ⟨j, h⟩).2) = o) := by
            rw [hzi, hxs, hoy]; simp
          rw [if_congr hiff rfl rfl, hPn]
          split_ifs <;> ring
        · intro ⟨x', y'⟩ _ hne
          refine Finset.sum_eq_zero fun r _ => ?_
          have hzi : (splitCoordEquiv (α := X × Y) i).symm ((x', y'), r) i = (x', y') := by
            simp [splitCoordEquiv]
          have hne' : ¬ ((y' = y) ∧ (x' = x)) := fun ⟨hy, hx⟩ => hne (Prod.ext hx hy)
          simp [hzi, hne']
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro q _ hne
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases h : ((q, enc (xs z), otherY q (ys z)), (z q).2, (z q).1) = ((i, t, o), y, x)
        · exact absurd (congrArg (fun a => a.1.1) h) hne
        · simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_xz : ∀ (i : Fin n) (t : Fin M) (o : Fin n → Option Y) (x : X),
        (R.map (fun s => (s.1, s.2.2))).pmf ((i, t, o), x) =
          UnifN.pmf i * P.fst.pmf x * restSum i t o x := by
      intro i t o x
      unfold ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single (i, t, o)]
      · rw [Fintype.sum_prod_type]
        have hinner : ∀ y : Y,
            (∑ x' : X, if x' = x then R.pmf ((i, t, o), y, x') else 0) =
              UnifN.pmf i * P.pmf (x, y) * restSum i t o x := fun y => by
          rw [Finset.sum_eq_single x]
          · simp [hR_pmf]
          · intro x' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Prod.mk.injEq, true_and, hinner]
        have hfac : ∑ y : Y, UnifN.pmf i * P.pmf (x, y) * restSum i t o x =
            UnifN.pmf i * (∑ y : Y, P.pmf (x, y)) * restSum i t o x := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [hfac]; rfl
      · intro u' _ hne
        rw [Fintype.sum_prod_type]
        exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x' _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_yz : R.map (fun s => (s.2.1, s.2.2)) = P.map Prod.swap := by
      unfold R; rw [map_comp_eq Qraw, ← hQraw_marg, map_comp_eq Qraw]; rfl
    have hR_yz_pmf : ∀ y x, (R.map (fun s => (s.2.1, s.2.2))).pmf (y, x) = P.pmf (x, y) := by
      intro y x
      rw [hR_yz]
      exact wz_probDist_map_equiv_pmf (Equiv.prodComm X Y) P (y, x)
    have hR_z : R.map (fun s => s.2.2) = P.fst := by
      unfold R; rw [map_comp_eq Qraw, ← wz_probDist_map_fst, ← hQraw_marg, map_comp_eq Qraw]; rfl
    rw [condMutualInfo_eq_zero_iff]
    refine wz_probDist_ext fun ⟨⟨i, t, o⟩, y, x⟩ => ?_
    change R.pmf ((i, t, o), y, x) = if (R.map (fun s => s.2.2)).pmf x = 0 then 0
      else (R.map (fun s => (s.1, s.2.2))).pmf ((i, t, o), x) *
        (R.map (fun s => (s.2.1, s.2.2))).pmf (y, x) / (R.map (fun s => s.2.2)).pmf x
    rw [hR_pmf, hR_xz, hR_yz_pmf, hR_z]
    by_cases hpx : P.fst.pmf x = 0
    · simp only [hpx, ↓reduceIte]
      have hpxy0 : P.pmf (x, y) = 0 := by
        have hle : P.pmf (x, y) ≤ P.fst.pmf x :=
          Finset.single_le_sum (fun y' _ => P.nonneg (x, y')) (Finset.mem_univ y)
        exact le_antisymm (by linarith) (P.nonneg (x, y))
      simp [hpxy0]
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hpx)]
      field_simp [hpx]
  have hQ_markov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    unfold Q; rw [map_comp_eq]
    have hcomp : ((fun t : X × Y × Fin kU => (t.2.2, t.2.1, t.1)) ∘
        fun t : X × Y × Uraw => (t.1, t.2.1, eU t.2.2)) =
        (fun t : Uraw × Y × X => (eU t.1, t.2.1, t.2.2)) ∘
          fun t : X × Y × Uraw => (t.2.2, t.2.1, t.1) := rfl
    rw [hcomp, ← map_comp_eq, wz_condMutualInfo_map_fst_equiv, hQraw_markov]
  -- Step 4: Rate bound `I(X_Q; U | Y_Q) ≤ log₂ M / n`.
  have hQ_cmi_eq : condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) =
      condMutualInfo (Qraw.map (fun t => (t.1, t.2.2, t.2.1))) := by
    unfold Q; rw [map_comp_eq]
    have hcomp : ((fun t : X × Y × Fin kU => (t.1, t.2.2, t.2.1)) ∘
        fun t : X × Y × Uraw => (t.1, t.2.1, eU t.2.2)) =
        (fun t : X × Uraw × Y => (t.1, eU t.2.1, t.2.2)) ∘
          fun t : X × Y × Uraw => (t.1, t.2.2, t.2.1) := rfl
    rw [hcomp, ← map_comp_eq, wz_condMutualInfo_map_snd_equiv]
  -- Decompose `Qraw` by time-sharing index `q : Fin n`.
  let J : Fin n → ProbDist (X × (Fin M × (Fin n → Option Y)) × Y) :=
    fun q => Pn.map (fun z => ((z q).1, (enc (xs z), otherY q (ys z)), (z q).2))
  -- Entropy of `Qraw.map (X, Uraw, Y)` equals `H(UnifN) + (1/n) ∑_q H(J q)`.
  have hH_all : shannonEntropy (Qraw.map (fun t => (t.1, t.2.2, t.2.1))) =
      shannonEntropy UnifN + ∑ q : Fin n, UnifN.pmf q * shannonEntropy (J q) := by
    let eSplit : (X × Uraw × Y) ≃ (Fin n × (X × (Fin M × (Fin n → Option Y)) × Y)) :=
      { toFun := fun t => (t.2.1.1, (t.1, t.2.1.2, t.2.2))
        invFun := fun s => (s.2.1, (s.1, s.2.2.1), s.2.2.2)
        left_inv := fun ⟨_, ⟨_, _, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, ⟨_, _⟩, _⟩⟩ => rfl }
    let W : DMC (Fin n) (X × (Fin M × (Fin n → Option Y)) × Y) :=
      { trans := fun q a => (J q).pmf a
        nonneg := fun q a => (J q).nonneg a
        sum_one := fun q => (J q).sum_one }
    have hmap_W : (Qraw.map (fun t => (t.1, t.2.2, t.2.1))).map eSplit = W.joint UnifN := by
      unfold Qraw; rw [map_comp_eq, map_comp_eq]
      unfold DMC.joint W J
      unfold ProbDist.map ProbDist.prod
      congr; funext ⟨q, a⟩
      dsimp only
      rw [Fintype.sum_prod_type]
      dsimp only [eSplit, Function.comp_apply]
      rw [Finset.sum_eq_single q]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by split_ifs <;> simp_all
      · intro q' _ hne
        exact Finset.sum_eq_zero fun z _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← shannonEntropy_map_equiv eSplit, hmap_W, dmc_joint_shannonEntropy]
    rfl
  -- Entropy of `(Uraw, Y_Q)` equals `H(UnifN) + (1/n) ∑_q H((J q).map (U_q, Y_q))`.
  have hH_UY : shannonEntropy ((Qraw.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => (t.2.1, t.2.2))) =
      shannonEntropy UnifN +
        ∑ q : Fin n, UnifN.pmf q * shannonEntropy ((J q).map (fun t => (t.2.1, t.2.2))) := by
    let eSplit : (Uraw × Y) ≃ (Fin n × ((Fin M × (Fin n → Option Y)) × Y)) :=
      { toFun := fun p => (p.1.1, (p.1.2, p.2))
        invFun := fun s => ((s.1, s.2.1), s.2.2)
        left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, ⟨⟨_, _⟩, _⟩⟩ => rfl }
    let W : DMC (Fin n) ((Fin M × (Fin n → Option Y)) × Y) :=
      { trans := fun q a => ((J q).map (fun t => (t.2.1, t.2.2))).pmf a
        nonneg := fun q a => ((J q).map (fun t => (t.2.1, t.2.2))).nonneg a
        sum_one := fun q => ((J q).map (fun t => (t.2.1, t.2.2))).sum_one }
    have hmap_W : ((Qraw.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => (t.2.1, t.2.2))).map eSplit =
        W.joint UnifN := by
      unfold Qraw; rw [map_comp_eq, map_comp_eq, map_comp_eq]
      unfold ProbDist.map ProbDist.prod DMC.joint W
      congr; funext ⟨q, a⟩; dsimp only [eSplit, J]
      rw [map_comp_eq]
      unfold ProbDist.map
      dsimp only
      rw [Fintype.sum_prod_type]
      dsimp only [Function.comp_apply]
      rw [Finset.sum_eq_single q]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by split_ifs <;> simp_all
      · intro q' _ hne
        exact Finset.sum_eq_zero fun z _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← shannonEntropy_map_equiv eSplit, hmap_W, dmc_joint_shannonEntropy]
    rfl
  -- Identify `H(J q)` and `H((J q).map (U_q, Y_q))` with `H(X_q, T, Y^n)` and `H(T, Y^n)`.
  let D_XTY : ProbDist ((Fin n → X) × (Fin M × (Fin n → Y))) :=
    Pn.map (fun z => (xs z, (enc (xs z), ys z)))
  let D_TY : ProbDist (Fin M × (Fin n → Y)) := Pn.map (fun z => (enc (xs z), ys z))
  have hJ_ent : ∀ q : Fin n,
      shannonEntropy (J q) = shannonEntropy (D_XTY.map (fun p => (p.1 q, p.2))) := by
    intro q
    let f : (X × (Fin M × (Fin n → Y))) → (X × (Fin M × (Fin n → Option Y)) × Y) :=
      fun p => (p.1, (p.2.1, otherY q p.2.2), p.2.2 q)
    have hf_inj : Function.Injective f := by
      rintro ⟨x₁, t₁, y₁⟩ ⟨x₂, t₂, y₂⟩ h
      have hx : x₁ = x₂ := congrArg Prod.fst h
      have ht : t₁ = t₂ := congrArg (fun a => a.2.1.1) h
      have ho : otherY q y₁ = otherY q y₂ := congrArg (fun a => a.2.1.2) h
      have hyq : y₁ q = y₂ q := congrArg (fun a => a.2.2) h
      have hy : y₁ = y₂ := by
        rw [← reconstructY_otherY q y₁, ← reconstructY_otherY q y₂, ho, hyq]
      subst hx; subst ht; subst hy; rfl
    have hcomp : J q = (D_XTY.map (fun p => (p.1 q, p.2))).map f := by
      unfold J D_XTY; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hcomp, wz_shannonEntropy_map_injective _ hf_inj]
  have hJ_UY_ent : ∀ q : Fin n,
      shannonEntropy ((J q).map (fun t => (t.2.1, t.2.2))) = shannonEntropy D_TY := by
    intro q
    let f : (Fin M × (Fin n → Y)) → ((Fin M × (Fin n → Option Y)) × Y) :=
      fun p => ((p.1, otherY q p.2), p.2 q)
    have hf_inj : Function.Injective f := by
      rintro ⟨t₁, y₁⟩ ⟨t₂, y₂⟩ h
      have ht : t₁ = t₂ := congrArg (fun a => a.1.1) h
      have ho : otherY q y₁ = otherY q y₂ := congrArg (fun a => a.1.2) h
      have hyq : y₁ q = y₂ q := congrArg Prod.snd h
      have hy : y₁ = y₂ := by
        rw [← reconstructY_otherY q y₁, ← reconstructY_otherY q y₂, ho, hyq]
      subst ht; subst hy; rfl
    have hcomp : (J q).map (fun t => (t.2.1, t.2.2)) = D_TY.map f := by
      unfold J D_TY; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hcomp, wz_shannonEntropy_map_injective _ hf_inj]
  -- Express `condMutualInfo` of `Qraw` as `H(X | Y) - (1/n) ∑_q H(X_q | T, Y^n)`.
  have hD_XTY_snd : ∀ q : Fin n, (D_XTY.map (fun p => (p.1 q, p.2))).snd = D_TY := by
    intro q
    rw [← wz_probDist_map_snd, map_comp_eq]
    unfold D_XTY D_TY; rw [map_comp_eq]; rfl
  have hD_XTY_snd' : D_XTY.snd = D_TY := by
    rw [← wz_probDist_map_snd]
    unfold D_XTY D_TY; rw [map_comp_eq]; rfl
  have hQraw_cmi : condMutualInfo (Qraw.map (fun t => (t.1, t.2.2, t.2.1))) =
      condEntropy P - (1 / (n : ℝ)) *
        ∑ q : Fin n, condEntropy (D_XTY.map (fun p => (p.1 q, p.2))) := by
    unfold condMutualInfo
    dsimp only
    have hxy : (Qraw.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => (t.1, t.2.2)) = P := by
      rw [map_comp_eq Qraw]; exact hQraw_marg
    have hy : (Qraw.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => t.2.2) = P.snd := by
      rw [← wz_probDist_map_snd, ← hQraw_marg, map_comp_eq Qraw, map_comp_eq Qraw]; rfl
    rw [hxy, hy, hH_all, hH_UY]
    simp_rw [hJ_ent, hJ_UY_ent]
    have hUnif_pmf : ∀ q : Fin n, UnifN.pmf q = 1 / (n : ℝ) := fun q => by
      dsimp only [UnifN, ProbDist.uniform]; rw [Fintype.card_fin]
    simp_rw [hUnif_pmf]
    have hsum : ∑ q : Fin n, (1 / (n : ℝ)) * shannonEntropy D_TY -
        ∑ q : Fin n, (1 / (n : ℝ)) * shannonEntropy (D_XTY.map (fun p => (p.1 q, p.2))) =
        -((1 / (n : ℝ)) * ∑ q : Fin n, condEntropy (D_XTY.map (fun p => (p.1 q, p.2)))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      unfold condEntropy
      rw [hD_XTY_snd q]
      ring
    have hceP : condEntropy P = shannonEntropy P - shannonEntropy P.snd := rfl
    linarith [hsum, hceP]
  -- Subadditivity: `H(X^n | T, Y^n) ≤ ∑_q H(X_q | T, Y^n)`.
  have hsub : condEntropy D_XTY ≤
      ∑ q : Fin n, condEntropy (D_XTY.map (fun p => (p.1 q, p.2))) :=
    condEntropy_pi_le_sum n D_XTY
  -- Exact entropies: `H(X^n, T, Y^n) = H(X^n, Y^n) = n H(P)`, `H(Y^n) = n H(P.snd)`.
  have hH_XTY : shannonEntropy D_XTY = (n : ℝ) * shannonEntropy P := by
    have hinj : Function.Injective (fun z : Fin n → X × Y => (xs z, (enc (xs z), ys z))) := by
      intro z₁ z₂ h
      have h1 : xs z₁ = xs z₂ := congrArg Prod.fst h
      have h2 : ys z₁ = ys z₂ := congrArg (fun p => p.2.2) h
      funext i
      exact Prod.ext (congrFun h1 i) (congrFun h2 i)
    unfold D_XTY
    rw [wz_shannonEntropy_map_injective Pn hinj]
    have heq : Pn = piProdDist (fun _ : Fin n => P) := rfl
    rw [heq, shannonEntropy_piProdDist]; simp
  have hD_TY_snd : D_TY.snd = iidDist P.snd n := by
    rw [← wz_probDist_map_snd]
    unfold D_TY; rw [map_comp_eq]
    have hcomp : (Prod.snd ∘ fun z : Fin n → X × Y => (enc (xs z), ys z)) = ys := rfl
    rw [hcomp]
    have heq : Pn.map ys = (jointIidDist P n).snd := by
      unfold Pn
      have hzip : (jointIidDist P n).map (zipEquiv X Y n) = iidDist P n := by
        unfold ProbDist.map; congr; funext z
        rw [Finset.sum_eq_single ((zipEquiv X Y n).symm z)]
        · simp [jointIidDist_pmf]; rfl
        · intro xy _ hne
          have : zipEquiv X Y n xy ≠ z := fun h =>
            hne ((zipEquiv X Y n).symm_apply_eq.mpr h.symm).symm
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [← hzip, map_comp_eq, ← wz_probDist_map_snd]
      rfl
    rw [heq, jointIidDist_snd]
  have hH_Yn : shannonEntropy D_TY.snd = (n : ℝ) * shannonEntropy P.snd := by
    rw [hD_TY_snd]
    have heq : iidDist P.snd n = piProdDist (fun _ : Fin n => P.snd) := rfl
    rw [heq, shannonEntropy_piProdDist]; simp
  have hH_TY_le : condEntropy D_TY ≤ log2 (M : ℝ) := by
    calc condEntropy D_TY
      _ ≤ shannonEntropy D_TY.fst := condEntropy_le_shannonEntropy D_TY
      _ ≤ log2 (Fintype.card (Fin M) : ℝ) := shannonEntropy_le_log2_card D_TY.fst
      _ = log2 (M : ℝ) := by rw [Fintype.card_fin]
  have hsum_bound : (n : ℝ) * condEntropy P - condEntropy D_XTY ≤ log2 (M : ℝ) := by
    unfold condEntropy at hH_TY_le ⊢
    rw [hD_XTY_snd', hH_XTY]
    linarith [hH_Yn]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrate_le : condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) ≤
      log2 (M : ℝ) / (n : ℝ) := by
    rw [hQ_cmi_eq, hQraw_cmi]
    have hstep1 : (n : ℝ) * condEntropy P -
        ∑ q : Fin n, condEntropy (D_XTY.map (fun p => (p.1 q, p.2))) ≤ log2 (M : ℝ) := by
      linarith
    have hdiv := div_le_div_of_nonneg_right hstep1 (le_of_lt hn_pos)
    have hlhs : ((n : ℝ) * condEntropy P -
        ∑ q : Fin n, condEntropy (D_XTY.map (fun p => (p.1 q, p.2)))) / (n : ℝ) =
        condEntropy P - (1 / (n : ℝ)) *
          ∑ q : Fin n, condEntropy (D_XTY.map (fun p => (p.1 q, p.2))) := by
      field_simp [ne_of_gt hn_pos]
    linarith
  exact le_trans (wynerZivRateDistortion_le hkU hQ_marg hQ_markov hQ_dist) hrate_le

end WynerZivConverse

/-! ### 3. Strong (Robust) Typicality & The Markov Lemma (El Gamal–Kim §2.4 & Lemma 12.1) -/

section StrongTypicalityAndMarkov

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Empirical relative frequency `π(a | x^n) = |{i : x_i = a}| / n`. -/
noncomputable def empFreq [DecidableEq α] {n : ℕ} (x : Fin n → α) (a : α) : ℝ :=
  ((Finset.univ.filter fun i : Fin n => x i = a).card : ℝ) / (n : ℝ)

/-- **Strongly (Robustly) Typical Set** `T_ε^(n)(P)` (El Gamal–Kim §2.4):
    sequences `x : Fin n → α` satisfying `|π(a | x^n) - P(a)| ≤ ε · P(a)` for every `a : α`.
    In particular, zero-probability symbols never occur (`P(a) = 0 → π(a | x^n) = 0`). -/
noncomputable def strongTypicalSet (P : ProbDist α) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter fun x => ∀ a : α, |empFreq x a - P.pmf a| ≤ ε * P.pmf a

private lemma mem_strongTypicalSet [DecidableEq α] {P : ProbDist α} {n : ℕ} {ε : ℝ}
    {x : Fin n → α} :
    x ∈ strongTypicalSet P n ε ↔ ∀ a : α, |empFreq x a - P.pmf a| ≤ ε * P.pmf a := by
  classical
  simp only [strongTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h a <;> convert h a

private lemma empFreq_map {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] {n : ℕ}
    (f : α → β) (x : Fin n → α) (b : β) :
    empFreq (fun i => f (x i)) b = ∑ a : α, if f a = b then empFreq x a else 0 := by
  unfold empFreq
  have hcard : ((Finset.univ.filter fun i : Fin n => f (x i) = b).card : ℝ) =
      ∑ a : α, if f a = b then ((Finset.univ.filter fun i : Fin n => x i = a).card : ℝ) else 0 := by
    have hnat : (Finset.univ.filter fun i : Fin n => f (x i) = b).card =
        ∑ a ∈ Finset.univ.filter (fun a : α => f a = b),
          (Finset.univ.filter fun i : Fin n => x i = a).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext i; simp
      · intro a₁ _ a₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro i hi₁ hi₂
        exact hne ((Finset.mem_filter.mp hi₁).2.symm.trans (Finset.mem_filter.mp hi₂).2)
    rw [hnat, Nat.cast_sum, Finset.sum_filter]
  rw [hcard, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- **Closure of Strong Typicality under Deterministic Maps** (El Gamal–Kim §2.4):
    if `x ∈ T_ε^(n)(P)`, then `f ∘ x ∈ T_ε^(n)(P.map f)` with the exact same tolerance `ε`. -/
theorem strongTypicalSet_map (P : ProbDist α) (f : α → β) (n : ℕ) (ε : ℝ)
    {x : Fin n → α} (hx : x ∈ strongTypicalSet P n ε) :
    (fun i => f (x i)) ∈ strongTypicalSet (P.map f) n ε := by
  classical
  rw [mem_strongTypicalSet] at hx ⊢
  intro b
  rw [empFreq_map]
  have hpmf : (P.map f).pmf b = ∑ a : α, if f a = b then P.pmf a else 0 := rfl
  rw [hpmf, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc |∑ a : α, ((if f a = b then empFreq x a else 0) - (if f a = b then P.pmf a else 0))|
    _ ≤ ∑ a : α, |(if f a = b then empFreq x a else 0) - (if f a = b then P.pmf a else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : α, ε * (if f a = b then P.pmf a else 0) := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases h : f a = b
        · simp [h, hx a]
        · simp [h]

/-- **Typical Average Lemma** (El Gamal–Kim §2.4):
    for any `0 < n`, `x ∈ T_ε^(n)(P)`, and nonnegative `f : α → ℝ`,
    `(1 / n) ∑_i f(x_i) ≤ (1 + ε) ∑_a P(a) f(a)`. -/
private lemma strongTypicalSet_typical_average (P : ProbDist α) {n : ℕ} (hn : 0 < n) {ε : ℝ}
    {x : Fin n → α} (hx : x ∈ strongTypicalSet P n ε)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (1 / (n : ℝ)) * ∑ i : Fin n, f (x i) ≤ (1 + ε) * ∑ a : α, P.pmf a * f a := by
  classical
  rw [mem_strongTypicalSet] at hx
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hgroup : (1 / (n : ℝ)) * ∑ i : Fin n, f (x i) = ∑ a : α, empFreq x a * f a := by
    have hsum_i : ∑ i : Fin n, f (x i) =
        ∑ a : α, ((Finset.univ.filter fun i : Fin n => x i = a).card : ℝ) * f a := by
      have h1 : ∀ i : Fin n, f (x i) = ∑ a : α, if x i = a then f a else 0 := fun i => by
        rw [Finset.sum_eq_single (x i)]
        · simp
        · intro a _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold empFreq; ring
  rw [hgroup, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have hle : empFreq x a ≤ (1 + ε) * P.pmf a := by
    have := (abs_le.mp (hx a)).2; linarith
  have hmul := mul_le_mul_of_nonneg_right hle (hf a)
  linarith

/-- **Strong Typicality Implies Weak Typicality** (El Gamal–Kim §2.4):
    for `0 < n`, `0 ≤ ε`, and `ε * H(P) ≤ ε'`,
    `strongTypicalSet P n ε ⊆ weakTypicalSet P n ε'`. -/
theorem strongTypicalSet_subset_weakTypicalSet (P : ProbDist α) {n : ℕ} (hn : 0 < n)
    {ε ε' : ℝ} (_hε : 0 ≤ ε) (hε' : ε * shannonEntropy P ≤ ε') :
    strongTypicalSet P n ε ⊆ weakTypicalSet P n ε' := by
  classical
  intro x hx
  rw [mem_strongTypicalSet] at hx
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- Every symbol occurring in `x` has strictly positive probability under `P`.
  have hcoord_pos : ∀ i : Fin n, 0 < P.pmf (x i) := by
    intro i
    by_contra hle
    have h0 : P.pmf (x i) = 0 := le_antisymm (not_lt.mp hle) (P.nonneg _)
    have hfi := hx (x i)
    rw [h0, sub_zero, mul_zero] at hfi
    have hfreq0 : empFreq x (x i) = 0 := abs_nonpos_iff.mp hfi
    have hcard_pos : 0 < (Finset.univ.filter fun j : Fin n => x j = x i).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
    have hfreq_pos : 0 < empFreq x (x i) := div_pos (Nat.cast_pos.mpr hcard_pos) hn_pos
    linarith
  have hpx_pos : 0 < (iidDist P n).pmf x := by
    unfold iidDist; dsimp only; exact Finset.prod_pos fun i _ => hcoord_pos i
  -- Express `-log₂ P^n(x)` via `empFreq` and `selfInfo`.
  have hneg_log : -log2 ((iidDist P n).pmf x) = (n : ℝ) * ∑ a : α, empFreq x a * selfInfo P a := by
    have hlog_prod : log2 ((iidDist P n).pmf x) = ∑ i : Fin n, log2 (P.pmf (x i)) := by
      unfold iidDist log2; dsimp only
      rw [Real.log_prod (fun i _ => ne_of_gt (hcoord_pos i)), Finset.sum_div]
    rw [hlog_prod, ← Finset.sum_neg_distrib]
    have hsi : ∑ i : Fin n, -log2 (P.pmf (x i)) = ∑ i : Fin n, selfInfo P (x i) :=
      Finset.sum_congr rfl fun i _ => by
        unfold selfInfo
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr (hcoord_pos i)))]
    rw [hsi]
    have h1 : ∀ i : Fin n, selfInfo P (x i) = ∑ a : α, if x i = a then selfInfo P a else 0 :=
      fun i => by
        rw [Finset.sum_eq_single (x i)]
        · simp
        · intro a _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    unfold empFreq
    field_simp [ne_of_gt hn_pos]
  -- Non-negativity of `selfInfo P a`.
  have hsi_nonneg : ∀ a : α, 0 ≤ selfInfo P a := by
    intro a
    unfold selfInfo
    by_cases hp : P.pmf a ≤ 0
    · simp [hp]
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hp)]
      have hpos : 0 < P.pmf a := lt_of_not_ge hp
      have hle1 : P.pmf a ≤ 1 := by
        calc P.pmf a ≤ ∑ b : α, P.pmf b :=
              Finset.single_le_sum (fun b _ => P.nonneg b) (Finset.mem_univ a)
          _ = 1 := P.sum_one
      have hlog : Real.log (P.pmf a) ≤ 0 := Real.log_nonpos (le_of_lt hpos) hle1
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have : log2 (P.pmf a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hlog2)
      linarith
  have hsum_le : ∑ a : α, empFreq x a * selfInfo P a ≤ (1 + ε) * shannonEntropy P := by
    rw [← expected_selfInfo P, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := (abs_le.mp (hx a)).2
    have := mul_le_mul_of_nonneg_right (show empFreq x a ≤ (1 + ε) * P.pmf a by linarith)
      (hsi_nonneg a)
    linarith
  have hsum_ge : (1 - ε) * shannonEntropy P ≤ ∑ a : α, empFreq x a * selfInfo P a := by
    rw [← expected_selfInfo P, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h := (abs_le.mp (hx a)).1
    have := mul_le_mul_of_nonneg_right (show (1 - ε) * P.pmf a ≤ empFreq x a by linarith)
      (hsi_nonneg a)
    linarith
  have hH_le : -log2 ((iidDist P n).pmf x) ≤ (n : ℝ) * (shannonEntropy P + ε') := by
    rw [hneg_log]
    have h1 : ∑ a : α, empFreq x a * selfInfo P a ≤ shannonEntropy P + ε' := by linarith
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hn_pos)
  have hH_ge : (n : ℝ) * (shannonEntropy P - ε') ≤ -log2 ((iidDist P n).pmf x) := by
    rw [hneg_log]
    have h1 : shannonEntropy P - ε' ≤ ∑ a : α, empFreq x a * selfInfo P a := by linarith
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hn_pos)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2eq : ∀ t : ℝ, (2 : ℝ) ^ t = Real.exp (t * Real.log 2) := fun t => by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rw [h2eq, ← Real.exp_log hpx_pos]
    apply Real.exp_le_exp.mpr
    unfold log2 at hH_le
    have h1 : -((n : ℝ) * (shannonEntropy P + ε')) ≤ Real.log ((iidDist P n).pmf x) / Real.log 2 := by
      linarith
    exact (le_div_iff₀ hlog2_pos).mp h1
  · rw [h2eq, ← Real.exp_log hpx_pos]
    apply Real.exp_le_exp.mpr
    unfold log2 at hH_ge
    have h1 : Real.log ((iidDist P n).pmf x) / Real.log 2 ≤ -((n : ℝ) * (shannonEntropy P - ε')) := by
      linarith
    exact (div_le_iff₀ hlog2_pos).mp h1

/-- Strongly typical pairs are jointly weakly typical for scaled tolerance `ε'`. -/
private lemma strongTypicalSet_mem_jointTypicalSet (Q : ProbDist (α × β)) {n : ℕ} (hn : 0 < n)
    {ε ε' : ℝ} (hε : 0 ≤ ε)
    (h1 : ε * shannonEntropy Q.fst ≤ ε')
    (h2 : ε * shannonEntropy Q.snd ≤ ε')
    (h3 : ε * shannonEntropy Q ≤ ε')
    {xy : (Fin n → α) × (Fin n → β)}
    (hxy : zipEquiv α β n xy ∈ strongTypicalSet Q n ε) :
    xy ∈ jointTypicalSet Q n ε' := by
  rw [mem_jointTypicalSet]
  refine ⟨?_, ?_, ?_⟩
  · have hfst := strongTypicalSet_map Q Prod.fst n ε hxy
    rw [wz_probDist_map_fst] at hfst
    exact strongTypicalSet_subset_weakTypicalSet Q.fst hn hε h1 hfst
  · have hsnd := strongTypicalSet_map Q Prod.snd n ε hxy
    rw [wz_probDist_map_snd] at hsnd
    exact strongTypicalSet_subset_weakTypicalSet Q.snd hn hε h2 hsnd
  · exact strongTypicalSet_subset_weakTypicalSet Q hn hε h3 hxy

/-- **Explicit Chebyshev–Union Tail Bound for Strong Typicality**:
    for `n ≥ 1` and `ε > 0`,
    `1 - P^n(T_ε^(n)(P)) ≤ (∑_{a : P(a) > 0} 1 / P(a)) / (n ε²)`. -/
theorem strongTypicalSet_prob_not_mem_le (P : ProbDist α) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    1 - ∑ x ∈ strongTypicalSet P n ε, (iidDist P n).pmf x ≤
      (∑ a : α, if 0 < P.pmf a then 1 / P.pmf a else 0) / ((n : ℝ) * ε ^ 2) := by
  classical
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcomp : 1 - ∑ x ∈ strongTypicalSet P n ε, (iidDist P n).pmf x =
      ∑ x : Fin n → α, if x ∉ strongTypicalSet P n ε then (iidDist P n).pmf x else 0 := by
    have hsplit : ∑ x : Fin n → α, (iidDist P n).pmf x =
        (∑ x : Fin n → α, if x ∈ strongTypicalSet P n ε then (iidDist P n).pmf x else 0) +
        (∑ x : Fin n → α, if x ∉ strongTypicalSet P n ε then (iidDist P n).pmf x else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by by_cases h : x ∈ strongTypicalSet P n ε <;> simp [h]
    rw [(iidDist P n).sum_one] at hsplit
    have hmem : (∑ x : Fin n → α, if x ∈ strongTypicalSet P n ε then (iidDist P n).pmf x else 0) =
        ∑ x ∈ strongTypicalSet P n ε, (iidDist P n).pmf x := by
      rw [← Finset.sum_filter]; congr 1; ext x; simp
    linarith
  rw [hcomp]
  -- Union bound over `a : α`.
  have hunion : ∀ x : Fin n → α,
      (if x ∉ strongTypicalSet P n ε then (iidDist P n).pmf x else 0) ≤
        ∑ a : α, if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0 := by
    intro x
    by_cases hmem : x ∈ strongTypicalSet P n ε
    · simp only [hmem, not_true_eq_false, ↓reduceIte]
      exact Finset.sum_nonneg fun a _ => by
        by_cases h : |empFreq x a - P.pmf a| ≤ ε * P.pmf a
        · simp [h]
        · simp [h, (iidDist P n).nonneg x]
    · simp only [hmem, not_false_eq_true, ↓reduceIte]
      rw [mem_strongTypicalSet] at hmem
      push Not at hmem
      rcases hmem with ⟨a₀, ha₀⟩
      have hnot : ¬ (|empFreq x a₀ - P.pmf a₀| ≤ ε * P.pmf a₀) := not_le.mpr ha₀
      calc (iidDist P n).pmf x
        _ = (if ¬ (|empFreq x a₀ - P.pmf a₀| ≤ ε * P.pmf a₀) then (iidDist P n).pmf x else 0) := by
            simp [hnot]
        _ ≤ _ := Finset.single_le_sum
            (f := fun a => if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0)
            (fun a _ => by
              by_cases h : |empFreq x a - P.pmf a| ≤ ε * P.pmf a
              · simp [h]
              · simp [h, (iidDist P n).nonneg x])
            (Finset.mem_univ a₀)
  -- Per-symbol Chebyshev bound.
  have hper_a : ∀ a : α,
      (∑ x : Fin n → α, if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0) ≤
        (if 0 < P.pmf a then 1 / P.pmf a else 0) / ((n : ℝ) * ε ^ 2) := by
    intro a
    by_cases hpa : 0 < P.pmf a
    · simp only [hpa, ↓reduceIte]
      let Z : α → ℝ := fun b => (if b = a then 1 else 0) - P.pmf a
      have hEZ : ∑ b : α, P.pmf b * Z b = 0 := by
        simp_rw [Z, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hEZ2 : ∑ b : α, P.pmf b * (Z b * Z b) ≤ P.pmf a := by
        have heq : ∑ b : α, P.pmf b * (Z b * Z b) = P.pmf a * (1 - P.pmf a) := by
          have h1 : ∀ b : α, P.pmf b * (Z b * Z b) =
              (if b = a then P.pmf b else 0) - 2 * P.pmf a * (if b = a then P.pmf b else 0) +
                P.pmf a ^ 2 * P.pmf b := fun b => by
            dsimp only [Z]; split_ifs <;> ring
          simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            P.sum_one, mul_one]
          have hsingle : (∑ b : α, if b = a then P.pmf b else 0) = P.pmf a := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro b _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hsingle]; ring
        rw [heq]
        nlinarith [P.nonneg a]
      have hVar : ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 ≤
          (n : ℝ) * P.pmf a := by
        have hsq : ∀ x : Fin n → α,
            (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
              ∑ i : Fin n, ∑ j : Fin n, (iidDist P n).pmf x * (Z (x i) * Z (x j)) := by
          intro x; rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.mul_sum ..
        simp_rw [hsq]
        rw [Finset.sum_comm]
        trans (∑ i : Fin n, ∑ j : Fin n,
            ∑ x : Fin n → α, (iidDist P n).pmf x * (Z (x i) * Z (x j)))
        · exact le_of_eq (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
        · calc ∑ i : Fin n, ∑ j : Fin n,
                ∑ x : Fin n → α, (iidDist P n).pmf x * (Z (x i) * Z (x j))
            _ = ∑ i : Fin n, ∑ b : α, P.pmf b * (Z b * Z b) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.sum_eq_single i]
                · exact iidDist_sum_coord P (fun b => Z b * Z b) i
                · intro j _ hji
                  rw [iidDist_sum_two_coords P Z Z hji.symm, hEZ, mul_zero]
                · intro h; exact absurd (Finset.mem_univ _) h
            _ ≤ ∑ _i : Fin n, P.pmf a := Finset.sum_le_sum fun _ _ => hEZ2
            _ = (n : ℝ) * P.pmf a := by simp
      have hcheb : ((n : ℝ) * (ε * P.pmf a)) ^ 2 *
          (∑ x : Fin n → α, if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0) ≤
          (n : ℝ) * P.pmf a := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum fun x _ => ?_) hVar
        by_cases hle : |empFreq x a - P.pmf a| ≤ ε * P.pmf a
        · simp only [hle, not_true_eq_false, ↓reduceIte, mul_zero]
          exact mul_nonneg ((iidDist P n).nonneg x) (sq_nonneg _)
        · simp only [hle, not_false_eq_true, ↓reduceIte]
          have hgt : ε * P.pmf a < |empFreq x a - P.pmf a| := lt_of_not_ge hle
          have hsumZ : ∑ i : Fin n, Z (x i) = (n : ℝ) * (empFreq x a - P.pmf a) := by
            unfold Z empFreq
            rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_sub]
            congr 1
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
            field_simp [ne_of_gt hn_pos]
          have habs : (n : ℝ) * (ε * P.pmf a) < |∑ i : Fin n, Z (x i)| := by
            rw [hsumZ, abs_mul, abs_of_pos hn_pos]
            exact mul_lt_mul_of_pos_left hgt hn_pos
          have hsq : ((n : ℝ) * (ε * P.pmf a)) ^ 2 ≤ (∑ i : Fin n, Z (x i)) ^ 2 := by
            rw [← sq_abs (∑ i : Fin n, Z (x i))]
            have hne0 : 0 ≤ (n : ℝ) * (ε * P.pmf a) := by positivity
            nlinarith
          nlinarith [(iidDist P n).nonneg x]
      have hden_pos : (0 : ℝ) < ((n : ℝ) * (ε * P.pmf a)) ^ 2 := by positivity
      have h1 : (∑ x : Fin n → α, if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0) ≤
          ((n : ℝ) * P.pmf a) / ((n : ℝ) * (ε * P.pmf a)) ^ 2 :=
        (le_div_iff₀' hden_pos).mpr hcheb
      have hsimp : ((n : ℝ) * P.pmf a) / ((n : ℝ) * (ε * P.pmf a)) ^ 2 =
          (1 / P.pmf a) / ((n : ℝ) * ε ^ 2) := by
        field_simp [ne_of_gt hn_pos, ne_of_gt hε, ne_of_gt hpa]
      linarith
    · simp only [hpa, ↓reduceIte, zero_div]
      have hpa0 : P.pmf a = 0 := le_antisymm (not_lt.mp hpa) (P.nonneg a)
      have hzero : ∑ x : Fin n → α,
          (if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hle : |empFreq x a - P.pmf a| ≤ ε * P.pmf a
        · simp [hle]
        · simp only [hle, not_false_eq_true, ↓reduceIte]
          rw [hpa0, sub_zero, mul_zero] at hle
          have hne0 : empFreq x a ≠ 0 := fun h0 => hle (by simp [h0])
          have hcard_pos : 0 < (Finset.univ.filter fun i : Fin n => x i = a).card := by
            by_contra hc
            have hc0 : (Finset.univ.filter fun i : Fin n => x i = a).card = 0 := Nat.eq_zero_of_not_pos hc
            exact hne0 (by simp [empFreq, hc0])
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard_pos
          have hxi : x i = a := (Finset.mem_filter.mp hi).2
          unfold iidDist; dsimp only
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hxi, hpa0])
      linarith
  calc ∑ x : Fin n → α, if x ∉ strongTypicalSet P n ε then (iidDist P n).pmf x else 0
    _ ≤ ∑ x : Fin n → α, ∑ a : α,
          if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0 :=
        Finset.sum_le_sum fun x _ => hunion x
    _ = ∑ a : α, ∑ x : Fin n → α,
          if ¬ (|empFreq x a - P.pmf a| ≤ ε * P.pmf a) then (iidDist P n).pmf x else 0 :=
        Finset.sum_comm
    _ ≤ ∑ a : α, (if 0 < P.pmf a then 1 / P.pmf a else 0) / ((n : ℝ) * ε ^ 2) :=
        Finset.sum_le_sum fun a _ => hper_a a
    _ = (∑ a : α, if 0 < P.pmf a then 1 / P.pmf a else 0) / ((n : ℝ) * ε ^ 2) := by
        rw [Finset.sum_div]

/-- **Strong Typicality Probability Approaches 1** (El Gamal–Kim §2.4):
    for every `ε > 0` and `δ > 0`, eventually `P^n(T_ε^(n)(P)) ≥ 1 - δ`. -/
theorem strongTypicalSet_prob_tendsto_one (P : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, 1 - δ ≤ ∑ x ∈ strongTypicalSet P n ε, (iidDist P n).pmf x := by
  let C : ℝ := ∑ a : α, if 0 < P.pmf a then 1 / P.pmf a else 0
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (δ * ε ^ 2))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hn)
  have htail := strongTypicalSet_prob_not_mem_le P hn_pos hε
  have hn_gt : C / (δ * ε ^ 2) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast le_trans (le_max_left N 1) hn)
  have hbound : C / ((n : ℝ) * ε ^ 2) ≤ δ := by
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [div_le_iff₀ (by positivity)]
    have h1 := (div_lt_iff₀ (by positivity : 0 < δ * ε ^ 2)).mp hn_gt
    linarith
  change 1 - ∑ x ∈ strongTypicalSet P n ε, (iidDist P n).pmf x ≤ C / ((n : ℝ) * ε ^ 2) at htail
  linarith

/-- Conditional channel `W_{Y|X} : DMC X Y` extracted from a joint distribution `P : ProbDist (X × Y)`
    (with an arbitrary uniform row on zero-mass `x`). -/
private noncomputable def condChannelOfJoint (P : ProbDist (α × β)) : DMC α β := by
  classical
  have hne : Nonempty (α × β) := wz_nonempty_of_probDist P
  have : Nonempty β := ⟨hne.some.2⟩
  exact
    { trans := fun a b =>
        if P.fst.pmf a = 0 then (ProbDist.uniform (α := β)).pmf b
        else P.pmf (a, b) / P.fst.pmf a
      nonneg := fun a b => by
        split_ifs
        · exact (ProbDist.uniform (α := β)).nonneg b
        · exact div_nonneg (P.nonneg (a, b)) (P.fst.nonneg a)
      sum_one := fun a => by
        by_cases ha : P.fst.pmf a = 0
        · simp only [ha, ↓reduceIte]
          exact (ProbDist.uniform (α := β)).sum_one
        · simp only [ite_eq_right_iff.mpr (fun h => absurd h ha), ← Finset.sum_div]
          exact div_self ha }

private lemma condChannelOfJoint_mul (P : ProbDist (α × β)) (a : α) (b : β) :
    P.fst.pmf a * (condChannelOfJoint P).trans a b = P.pmf (a, b) := by
  classical
  unfold condChannelOfJoint; dsimp only
  by_cases ha : P.fst.pmf a = 0
  · simp only [ha, ↓reduceIte, zero_mul]
    have hle : P.pmf (a, b) ≤ P.fst.pmf a :=
      Finset.single_le_sum (fun b' _ => P.nonneg (a, b')) (Finset.mem_univ b)
    exact (le_antisymm (by linarith) (P.nonneg (a, b))).symm
  · simp only [ite_eq_right_iff.mpr (fun h => absurd h ha)]
    exact mul_div_cancel₀ _ ha

private lemma jointIidDist_eq_fst_mul_condChannelPower (P : ProbDist (α × β)) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) :
    (jointIidDist P n).pmf (x, y) =
      (iidDist P.fst n).pmf x * ((condChannelOfJoint P).power n).trans x y := by
  unfold jointIidDist iidDist DMC.power; dsimp only
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (condChannelOfJoint_mul P (x i) (y i)).symm

/-- Factorization of a Markov triple `U — X — Y`: `Q(x, y, u) = Q_{XU}(x, u) · W_{Y|X}(y | x)`. -/
private lemma markov_factorization {X Y U : Type*} [Fintype X] [Fintype Y] [Fintype U]
    (Q : ProbDist (X × Y × U))
    (hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0)
    (a : X) (b : Y) (c : U) :
    Q.pmf (a, b, c) =
      (Q.map (fun t => (t.1, t.2.2))).pmf (a, c) *
        (condChannelOfJoint (Q.map (fun t => (t.1, t.2.1)))).trans a b := by
  classical
  let P := Q.map (fun t => (t.1, t.2.1))
  let Qxu := Q.map (fun t => (t.1, t.2.2))
  let R := Q.map (fun t => (t.2.2, t.2.1, t.1))
  have hci : R = condIndepDist R := (condMutualInfo_eq_zero_iff R).mp hmarkov
  let eR : (X × Y × U) ≃ (U × Y × X) :=
    { toFun := fun t => (t.2.2, t.2.1, t.1)
      invFun := fun t => (t.2.2, t.2.1, t.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hR_pmf : R.pmf (c, b, a) = Q.pmf (a, b, c) := wz_probDist_map_equiv_pmf eR Q (c, b, a)
  have hR_xz : (R.map (fun t => (t.1, t.2.2))).pmf (c, a) = Qxu.pmf (a, c) := by
    have hswap : R.map (fun t => (t.1, t.2.2)) = Qxu.map Prod.swap := by
      unfold R Qxu; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hswap]
    exact wz_probDist_map_equiv_pmf (Equiv.prodComm X U) Qxu (c, a)
  have hR_yz : (R.map (fun t => (t.2.1, t.2.2))).pmf (b, a) = P.pmf (a, b) := by
    have hswap : R.map (fun t => (t.2.1, t.2.2)) = P.map Prod.swap := by
      unfold R P; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hswap]
    exact wz_probDist_map_equiv_pmf (Equiv.prodComm X Y) P (b, a)
  have hR_z : R.map (fun t => t.2.2) = P.fst := by
    unfold R P; rw [map_comp_eq, ← wz_probDist_map_fst, map_comp_eq]; rfl
  have hQxu_fst : Qxu.fst = P.fst := by
    rw [← wz_probDist_map_fst, ← wz_probDist_map_fst]
    unfold Qxu P; rw [map_comp_eq, map_comp_eq]; rfl
  have h1 := congrArg (fun D : ProbDist (U × Y × X) => D.pmf (c, b, a)) hci
  change R.pmf (c, b, a) = if (R.map (fun t => t.2.2)).pmf a = 0 then 0
    else (R.map (fun t => (t.1, t.2.2))).pmf (c, a) *
      (R.map (fun t => (t.2.1, t.2.2))).pmf (b, a) / (R.map (fun t => t.2.2)).pmf a at h1
  rw [hR_pmf, hR_xz, hR_yz, hR_z] at h1
  change Q.pmf (a, b, c) = Qxu.pmf (a, c) * (condChannelOfJoint P).trans a b
  unfold condChannelOfJoint; dsimp only
  by_cases ha : P.fst.pmf a = 0
  · simp only [ha, ↓reduceIte] at h1 ⊢
    have hQxu0 : Qxu.pmf (a, c) = 0 := by
      have hle : Qxu.pmf (a, c) ≤ Qxu.fst.pmf a :=
        Finset.single_le_sum (fun c' _ => Qxu.nonneg (a, c')) (Finset.mem_univ c)
      rw [hQxu_fst, ha] at hle
      exact le_antisymm hle (Qxu.nonneg (a, c))
    rw [h1, hQxu0, zero_mul]
  · simp only [ite_eq_right_iff.mpr (fun h => absurd h ha)] at h1 ⊢
    rw [h1]; ring

open Classical in
/-- **The Markov Lemma** (El Gamal–Kim Lemma 12.1; Cover & Thomas Lemma 15.8.1):
    for any joint distribution `Q` on `X × Y × U` forming a Markov chain `U — X — Y`
    (`I(U; Y | X) = 0`), any `0 < n`, any `0 ≤ ε₁ < ε₂`, and any **fixed** strongly typical
    pair `(x, u)` with `zip x u ∈ T_{ε₁}^(n)(Q_{XU})`, if `Y^n` is drawn from the memoryless
    conditional channel `W_{Y|X}^n(· | x)`, then the probability that `(x, Y^n, u)` fails to be
    strongly `ε₂`-typical under `Q` satisfies the uniform explicit bound
    `P_{Y^n|X^n}((x, Y^n, u) ∉ T_{ε₂}^(n)(Q) | x) ≤ (∑_{t : Q(t) > 0} 1 / Q(t)²) / (n (ε₂ - ε₁)²)`. -/
theorem markov_lemma {X Y U : Type*} [Fintype X] [Fintype Y] [Fintype U]
    (Q : ProbDist (X × Y × U))
    (hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0)
    {n : ℕ} (hn : 0 < n) {ε₁ ε₂ : ℝ} (_hε₁ : 0 ≤ ε₁) (hε : ε₁ < ε₂)
    {x : Fin n → X} {u : Fin n → U}
    (hxu : (fun i => (x i, u i)) ∈ strongTypicalSet (Q.map (fun t => (t.1, t.2.2))) n ε₁) :
    let W := condChannelOfJoint (Q.map (fun t => (t.1, t.2.1)))
    ∑ y : Fin n → Y, (W.power n).trans x y *
        (if (fun i => (x i, y i, u i)) ∉ strongTypicalSet Q n ε₂ then (1 : ℝ) else 0) ≤
      (∑ t : X × Y × U, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
        ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
  classical
  dsimp only
  let P := Q.map (fun t => (t.1, t.2.1))
  let Qxu := Q.map (fun t => (t.1, t.2.2))
  let W := condChannelOfJoint P
  let Vy : ProbDist (Fin n → Y) := piProdDist (fun i => dmcRow W (x i))
  have hVy_pmf : ∀ y : Fin n → Y, Vy.pmf y = (W.power n).trans x y := fun _ => rfl
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiff_pos : 0 < ε₂ - ε₁ := by linarith
  rw [mem_strongTypicalSet] at hxu
  -- Union bound over triples `t = (a, b, c) : X × Y × U`.
  have hunion : ∀ y : Fin n → Y,
      (if (fun i => (x i, y i, u i)) ∉ strongTypicalSet Q n ε₂ then (1 : ℝ) else 0) ≤
        ∑ t : X × Y × U,
          if ¬ (|empFreq (fun i => (x i, y i, u i)) t - Q.pmf t| ≤ ε₂ * Q.pmf t)
          then (1 : ℝ) else 0 := by
    intro y
    by_cases hmem : (fun i => (x i, y i, u i)) ∈ strongTypicalSet Q n ε₂
    · simp only [hmem, not_true_eq_false, ↓reduceIte]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · simp only [hmem, not_false_eq_true, ↓reduceIte]
      rw [mem_strongTypicalSet] at hmem
      push Not at hmem
      rcases hmem with ⟨t₀, ht₀⟩
      have hnot : ¬ (|empFreq (fun i => (x i, y i, u i)) t₀ - Q.pmf t₀| ≤ ε₂ * Q.pmf t₀) :=
        not_le.mpr ht₀
      calc (1 : ℝ)
        _ = (if ¬ (|empFreq (fun i => (x i, y i, u i)) t₀ - Q.pmf t₀| ≤ ε₂ * Q.pmf t₀)
              then (1 : ℝ) else 0) := by simp [hnot]
        _ ≤ _ := Finset.single_le_sum
            (f := fun t => if ¬ (|empFreq (fun i => (x i, y i, u i)) t - Q.pmf t| ≤ ε₂ * Q.pmf t)
              then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ t₀)
  -- Per-triple bound.
  have hper_t : ∀ t : X × Y × U,
      ∑ y : Fin n → Y, Vy.pmf y *
          (if ¬ (|empFreq (fun i => (x i, y i, u i)) t - Q.pmf t| ≤ ε₂ * Q.pmf t)
           then (1 : ℝ) else 0) ≤
        (if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
    rintro ⟨a, b, c⟩
    have hfac : Q.pmf (a, b, c) = Qxu.pmf (a, c) * W.trans a b :=
      markov_factorization Q hmarkov a b c
    by_cases hqt : 0 < Q.pmf (a, b, c)
    · simp only [hqt, ↓reduceIte]
      -- Centered independent coordinate indicators `Z_i(y_i)` on `{i : x_i = a ∧ u_i = c}`.
      let Z : Fin n → Y → ℝ := fun i yi =>
        if x i = a ∧ u i = c then (if yi = b then 1 else 0) - W.trans a b else 0
      have hEZ : ∀ i : Fin n, ∑ yi : Y, (dmcRow W (x i)).pmf yi * Z i yi = 0 := by
        intro i
        dsimp only [Z]
        by_cases hiu : x i = a ∧ u i = c
        · simp only [hiu.1, hiu.2, and_self, ↓reduceIte, mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (dmcRow W a).sum_one, one_mul]
          have h1 : (∑ yi : Y, (dmcRow W a).pmf yi * (if yi = b then (1 : ℝ) else 0)) =
              W.trans a b := by
            rw [Finset.sum_eq_single b]
            · simp [dmcRow]
            · intro yi _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [h1, sub_self]
        · simp [hiu]
      have hEZ2 : ∀ i : Fin n, ∑ yi : Y, (dmcRow W (x i)).pmf yi * (Z i yi * Z i yi) ≤ 1 := by
        intro i
        have hle1 : ∀ yi : Y, Z i yi * Z i yi ≤ 1 := by
          intro yi
          dsimp only [Z]
          by_cases hiu : x i = a ∧ u i = c
          · simp only [hiu.1, hiu.2, and_self, ↓reduceIte]
            have hw0 : 0 ≤ W.trans a b := W.nonneg a b
            have hw1 : W.trans a b ≤ 1 := by
              calc W.trans a b ≤ ∑ b' : Y, W.trans a b' :=
                    Finset.single_le_sum (fun b' _ => W.nonneg a b') (Finset.mem_univ b)
                _ = 1 := W.sum_one a
            by_cases hy : yi = b
            · simp only [hy, ↓reduceIte]; nlinarith
            · simp only [hy, ↓reduceIte]; nlinarith
          · simp only [ite_eq_right_iff.mpr (fun h => absurd h hiu)]; norm_num
        calc ∑ yi : Y, (dmcRow W (x i)).pmf yi * (Z i yi * Z i yi)
          _ ≤ ∑ yi : Y, (dmcRow W (x i)).pmf yi * 1 :=
              Finset.sum_le_sum fun yi _ =>
                mul_le_mul_of_nonneg_left (hle1 yi) ((dmcRow W (x i)).nonneg yi)
          _ = 1 := by simp [(dmcRow W (x i)).sum_one]
      have hVar : ∑ y : Fin n → Y, Vy.pmf y * (∑ i : Fin n, Z i (y i)) ^ 2 ≤ (n : ℝ) := by
        have hsq : ∀ y : Fin n → Y,
            Vy.pmf y * (∑ i : Fin n, Z i (y i)) ^ 2 =
              ∑ i : Fin n, ∑ j : Fin n, Vy.pmf y * (Z i (y i) * Z j (y j)) := by
          intro y; rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.mul_sum ..
        simp_rw [hsq]
        rw [Finset.sum_comm]
        trans (∑ i : Fin n, ∑ j : Fin n,
            ∑ y : Fin n → Y, Vy.pmf y * (Z i (y i) * Z j (y j)))
        · exact le_of_eq (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
        · calc ∑ i : Fin n, ∑ j : Fin n,
                ∑ y : Fin n → Y, Vy.pmf y * (Z i (y i) * Z j (y j))
            _ = ∑ i : Fin n, ∑ yi : Y, (dmcRow W (x i)).pmf yi * (Z i yi * Z i yi) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.sum_eq_single i]
                · exact wz_piProdDist_sum_coord (fun k => dmcRow W (x k))
                    (fun yi => Z i yi * Z i yi) i
                · intro j _ hji
                  rw [wz_piProdDist_sum_two_coords (fun k => dmcRow W (x k)) (Z i) (Z j) hji.symm,
                    hEZ i, zero_mul]
                · intro h; exact absurd (Finset.mem_univ _) h
            _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hEZ2 i
            _ = (n : ℝ) := by simp
      -- Relate `∑_i Z_i(y_i)` to `empFreq (x, y, u) (a, b, c) - empFreq (x, u) (a, c) * W(b | a)`.
      have hsumZ : ∀ y : Fin n → Y,
          ∑ i : Fin n, Z i (y i) =
            (n : ℝ) * (empFreq (fun i => (x i, y i, u i)) (a, b, c) -
              empFreq (fun i => (x i, u i)) (a, c) * W.trans a b) := by
        intro y
        have h1 : ∑ i : Fin n, Z i (y i) =
            (∑ i : Fin n, if x i = a ∧ y i = b ∧ u i = c then (1 : ℝ) else 0) -
            (∑ i : Fin n, if x i = a ∧ u i = c then (1 : ℝ) else 0) * W.trans a b := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp only [Z]
          by_cases hiu : x i = a ∧ u i = c
          · by_cases hy : y i = b <;> simp [hiu, hy]
          · have hnot : ¬ (x i = a ∧ y i = b ∧ u i = c) := fun ⟨hx, _, hu⟩ => hiu ⟨hx, hu⟩
            simp [hiu, hnot]
        have hc1 : (∑ i : Fin n, if x i = a ∧ y i = b ∧ u i = c then (1 : ℝ) else 0) =
            (n : ℝ) * empFreq (fun i => (x i, y i, u i)) (a, b, c) := by
          unfold empFreq
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
            mul_div_cancel₀ _ (ne_of_gt hn_pos)]
          have hfilt : (Finset.univ.filter fun i : Fin n => x i = a ∧ y i = b ∧ u i = c) =
              Finset.univ.filter fun i : Fin n => (x i, y i, u i) = (a, b, c) := by
            ext i; simp
          rw [hfilt]
        have hc2 : (∑ i : Fin n, if x i = a ∧ u i = c then (1 : ℝ) else 0) =
            (n : ℝ) * empFreq (fun i => (x i, u i)) (a, c) := by
          unfold empFreq
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
            mul_div_cancel₀ _ (ne_of_gt hn_pos)]
          have hfilt : (Finset.univ.filter fun i : Fin n => x i = a ∧ u i = c) =
              Finset.univ.filter fun i : Fin n => (x i, u i) = (a, c) := by
            ext i; simp
          rw [hfilt]
        rw [h1, hc1, hc2]; ring
      -- Chebyshev inequality on the bad event.
      have hcheb : ((n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c))) ^ 2 *
          (∑ y : Fin n → Y, Vy.pmf y *
            (if ¬ (|empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| ≤
                ε₂ * Q.pmf (a, b, c)) then (1 : ℝ) else 0)) ≤ (n : ℝ) := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum fun y _ => ?_) hVar
        by_cases hle : |empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| ≤
            ε₂ * Q.pmf (a, b, c)
        · simp only [hle, not_true_eq_false, ↓reduceIte, mul_zero]
          exact mul_nonneg (Vy.nonneg y) (sq_nonneg _)
        · simp only [hle, not_false_eq_true, ↓reduceIte, mul_one]
          have hgt : ε₂ * Q.pmf (a, b, c) <
              |empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| := lt_of_not_ge hle
          have htri : |empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| ≤
              |empFreq (fun i => (x i, y i, u i)) (a, b, c) -
                empFreq (fun i => (x i, u i)) (a, c) * W.trans a b| +
              |empFreq (fun i => (x i, u i)) (a, c) - Qxu.pmf (a, c)| * W.trans a b := by
            have hsub : empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c) =
                (empFreq (fun i => (x i, y i, u i)) (a, b, c) -
                  empFreq (fun i => (x i, u i)) (a, c) * W.trans a b) +
                (empFreq (fun i => (x i, u i)) (a, c) - Qxu.pmf (a, c)) * W.trans a b := by
              rw [hfac]; ring
            rw [hsub]
            calc |(_ : ℝ) + _|
              _ ≤ |empFreq (fun i => (x i, y i, u i)) (a, b, c) -
                    empFreq (fun i => (x i, u i)) (a, c) * W.trans a b| +
                  |(empFreq (fun i => (x i, u i)) (a, c) - Qxu.pmf (a, c)) * W.trans a b| :=
                  abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_of_nonneg (W.nonneg a b)]
          have hxu_ac : |empFreq (fun i => (x i, u i)) (a, c) - Qxu.pmf (a, c)| * W.trans a b ≤
              ε₁ * Q.pmf (a, b, c) := by
            rw [hfac]
            have h1 := mul_le_mul_of_nonneg_right (hxu (a, c)) (W.nonneg a b)
            linarith
          have hdev : (ε₂ - ε₁) * Q.pmf (a, b, c) <
              |empFreq (fun i => (x i, y i, u i)) (a, b, c) -
                empFreq (fun i => (x i, u i)) (a, c) * W.trans a b| := by linarith
          have habs : (n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c)) < |∑ i : Fin n, Z i (y i)| := by
            rw [hsumZ y, abs_mul, abs_of_pos hn_pos]
            exact mul_lt_mul_of_pos_left hdev hn_pos
          have hsq : ((n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c))) ^ 2 ≤
              (∑ i : Fin n, Z i (y i)) ^ 2 := by
            rw [← sq_abs (∑ i : Fin n, Z i (y i))]
            have hne0 : 0 ≤ (n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c)) := by positivity
            nlinarith
          nlinarith [Vy.nonneg y]
      have hden_pos : (0 : ℝ) < ((n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c))) ^ 2 := by positivity
      have h1 : (∑ y : Fin n → Y, Vy.pmf y *
          (if ¬ (|empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| ≤
              ε₂ * Q.pmf (a, b, c)) then (1 : ℝ) else 0)) ≤
          (n : ℝ) / ((n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c))) ^ 2 :=
        (le_div_iff₀' hden_pos).mpr hcheb
      have hsimp : (n : ℝ) / ((n : ℝ) * ((ε₂ - ε₁) * Q.pmf (a, b, c))) ^ 2 =
          (1 / Q.pmf (a, b, c) ^ 2) / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
        field_simp [ne_of_gt hn_pos, ne_of_gt hdiff_pos, ne_of_gt hqt]
      linarith
    · -- Zero-probability triple: probability of occurring is identically 0.
      simp only [hqt, ↓reduceIte, zero_div]
      have hqt0 : Q.pmf (a, b, c) = 0 := le_antisymm (not_lt.mp hqt) (Q.nonneg _)
      have hzero : ∑ y : Fin n → Y, Vy.pmf y *
          (if ¬ (|empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| ≤
              ε₂ * Q.pmf (a, b, c)) then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        by_cases hle : |empFreq (fun i => (x i, y i, u i)) (a, b, c) - Q.pmf (a, b, c)| ≤
            ε₂ * Q.pmf (a, b, c)
        · simp [hle]
        · simp only [hle, not_false_eq_true, ↓reduceIte, mul_one]
          rw [hqt0, sub_zero, mul_zero] at hle
          have hne0 : empFreq (fun i => (x i, y i, u i)) (a, b, c) ≠ 0 :=
            fun h0 => hle (by simp [h0])
          have hcard_pos : 0 < (Finset.univ.filter fun i : Fin n => (x i, y i, u i) = (a, b, c)).card := by
            by_contra hc
            have hc0 : (Finset.univ.filter fun i : Fin n => (x i, y i, u i) = (a, b, c)).card = 0 :=
              Nat.eq_zero_of_not_pos hc
            apply hne0
            unfold empFreq
            rw [hc0]; simp
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard_pos
          have hxyu : (x i, y i, u i) = (a, b, c) := (Finset.mem_filter.mp hi).2
          have hxi : x i = a := congrArg Prod.fst hxyu
          have hyi : y i = b := congrArg (fun t => t.2.1) hxyu
          have hui : u i = c := congrArg (fun t => t.2.2) hxyu
          rw [hqt0] at hfac
          rcases mul_eq_zero.mp hfac.symm with hQxu0 | hW0
          · -- Contradicts `(x, u) ∈ strongTypicalSet Qxu n ε₁`.
            exfalso
            have hxu_ac := hxu (a, c)
            rw [hQxu0, sub_zero, mul_zero] at hxu_ac
            have hf0 : empFreq (fun j => (x j, u j)) (a, c) = 0 := abs_nonpos_iff.mp hxu_ac
            have hc_pos : 0 < (Finset.univ.filter fun j : Fin n => (x j, u j) = (a, c)).card :=
              Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Prod.ext hxi hui⟩⟩
            have hf_pos : 0 < empFreq (fun j => (x j, u j)) (a, c) :=
              div_pos (Nat.cast_pos.mpr hc_pos) hn_pos
            linarith
          · -- `Vy.pmf y = 0` because coordinate `i` has `W.trans a b = 0`.
            unfold Vy piProdDist dmcRow; dsimp only
            exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hxi, hyi, hW0])
      linarith
  change ∑ y : Fin n → Y, Vy.pmf y *
      (if (fun i => (x i, y i, u i)) ∉ strongTypicalSet Q n ε₂ then (1 : ℝ) else 0) ≤ _
  calc ∑ y : Fin n → Y, Vy.pmf y *
        (if (fun i => (x i, y i, u i)) ∉ strongTypicalSet Q n ε₂ then (1 : ℝ) else 0)
    _ ≤ ∑ y : Fin n → Y, Vy.pmf y *
          (∑ t : X × Y × U,
            if ¬ (|empFreq (fun i => (x i, y i, u i)) t - Q.pmf t| ≤ ε₂ * Q.pmf t)
            then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hunion y) (Vy.nonneg y)
    _ = ∑ t : X × Y × U, ∑ y : Fin n → Y, Vy.pmf y *
          (if ¬ (|empFreq (fun i => (x i, y i, u i)) t - Q.pmf t| ≤ ε₂ * Q.pmf t)
           then (1 : ℝ) else 0) := by
        simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    _ ≤ ∑ t : X × Y × U, (if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
          ((n : ℝ) * (ε₂ - ε₁) ^ 2) :=
        Finset.sum_le_sum fun t _ => hper_t t
    _ = (∑ t : X × Y × U, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
          ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
        rw [Finset.sum_div]

end StrongTypicalityAndMarkov

/-! ### 4. Wyner–Ziv Achievability & Operational Equality
(Cover & Thomas Theorem 15.9.1; El Gamal–Kim Theorem 11.3) -/

section WynerZivAchievability

variable {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]

/-- **Single-Witness Wyner–Ziv Achievability** (Cover & Thomas §15.9; El Gamal–Kim §11.3):
    for any valid single-letter witness `(kU, Q, g)` with `Q.map (X, Y) = P` and `U — X — Y`,
    any rate `R > I(X; U | Y)`, and any `δ > 0`, for all sufficiently large `n` there exist
    `enc : (Fin n → X) → Fin M` and `dec : Fin M → (Fin n → Y) → (Fin n → Xhat)` with
    `M = max 1 ⌊2^(n R)⌋` achieving expected per-symbol distortion at most `E_Q[d(X, g(U, Y))] + δ`. -/
theorem wynerZiv_achievability_of_dist (P : ProbDist (X × Y)) (d : Distortion X Xhat)
    {kU : ℕ} (_hk : 0 < kU) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat)
    (hmarg : Q.map (fun t => (t.1, t.2.1)) = P)
    (hmarkov : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0)
    {R δ : ℝ}
    (hR : condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : (Fin n → X) → Fin M) (dec : Fin M → (Fin n → Y) → (Fin n → Xhat)),
        ∑ xy : Fin n → X × Y, (iidDist P n).pmf xy *
          blockDist d (fun i => (xy i).1)
            (dec (enc (fun i => (xy i).1)) (fun i => (xy i).2)) ≤
          (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) + δ := by
  classical
  -- Marginals and key mutual-information identity `I(X; U | Y) = I(X; U) - I(U; Y)`.
  let Qxu : ProbDist (X × Fin kU) := Q.map (fun t => (t.1, t.2.2))
  let Quy : ProbDist (Fin kU × Y) := Q.map (fun t => (t.2.2, t.2.1))
  let Qu : ProbDist (Fin kU) := Qxu.snd
  have hQxu_fst : Qxu.fst = P.fst := by
    rw [← wz_probDist_map_fst, ← wz_probDist_map_fst, ← hmarg]
    unfold Qxu; rw [map_comp_eq, map_comp_eq]; rfl
  have hQuy_fst : Quy.fst = Qu := by
    unfold Qu; rw [← wz_probDist_map_fst, ← wz_probDist_map_snd]
    unfold Quy Qxu; rw [map_comp_eq, map_comp_eq]; rfl
  have hQuy_snd : Quy.snd = P.snd := by
    rw [← wz_probDist_map_snd, ← wz_probDist_map_snd, ← hmarg]
    unfold Quy; rw [map_comp_eq, map_comp_eq]; rfl
  have hI_eq : condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) =
      mutualInfo Qxu - mutualInfo Quy :=
    wz_condMutualInfo_eq_sub_of_markov Q hmarkov
  have hI_nonneg : 0 ≤ condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) :=
    condMutualInfo_nonneg _
  have hR_pos : 0 < R := lt_of_le_of_lt hI_nonneg hR
  -- Parameters `gap, E_d, dmax, Hmax, ε₂, ε₁, ε_c, ε_b, R_c`.
  let gap : ℝ := R - condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1)))
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let Ed : ℝ := ∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))
  have hEd0 : 0 ≤ Ed := Finset.sum_nonneg fun t _ => mul_nonneg (Q.nonneg t) (d.nonneg _ _)
  let dmax : ℝ := ∑ xy : X × Xhat, d.dist xy.1 xy.2
  have hdmax0 : 0 ≤ dmax := Finset.sum_nonneg fun xy _ => d.nonneg xy.1 xy.2
  have hd_le : ∀ x xh, d.dist x xh ≤ dmax := fun x xh =>
    Finset.single_le_sum (fun xy _ => d.nonneg xy.1 xy.2) (Finset.mem_univ (x, xh))
  let B : ℝ := dmax + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let Hmax : ℝ := shannonEntropy Qxu.fst + shannonEntropy Qxu.snd + shannonEntropy Qxu +
    shannonEntropy Quy.fst + shannonEntropy Quy.snd + shannonEntropy Quy + 1
  have hHmax : 1 ≤ Hmax := by
    dsimp [Hmax]
    linarith [shannonEntropy_nonneg Qxu.fst, shannonEntropy_nonneg Qxu.snd,
      shannonEntropy_nonneg Qxu, shannonEntropy_nonneg Quy.fst,
      shannonEntropy_nonneg Quy.snd, shannonEntropy_nonneg Quy]
  have hHmax_pos : 0 < Hmax := by linarith
  let ε₂ : ℝ := min (δ / (2 * (Ed + 1))) (gap / (20 * Hmax))
  have hε₂ : 0 < ε₂ := lt_min (by positivity) (by positivity)
  have hε₂_Ed : ε₂ * Ed ≤ δ / 2 := by
    have h1 : ε₂ ≤ δ / (2 * (Ed + 1)) := min_le_left _ _
    have h2 : ε₂ * (Ed + 1) ≤ δ / 2 := by
      have hpos : (0 : ℝ) < Ed + 1 := by linarith
      calc ε₂ * (Ed + 1) ≤ (δ / (2 * (Ed + 1))) * (Ed + 1) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
        _ = δ / 2 := by field_simp [ne_of_gt hpos]
    nlinarith
  have hε₂_gap : ε₂ * Hmax ≤ gap / 20 := by
    have h1 : ε₂ ≤ gap / (20 * Hmax) := min_le_right _ _
    calc ε₂ * Hmax ≤ (gap / (20 * Hmax)) * Hmax :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hHmax_pos)
      _ = gap / 20 := by field_simp [ne_of_gt hHmax_pos]
  let ε₁ : ℝ := ε₂ / 2
  have hε₁ : 0 < ε₁ := half_pos hε₂
  have hε₁_lt : ε₁ < ε₂ := by dsimp [ε₁]; linarith
  let ε_c : ℝ := ε₁ * Hmax
  let ε_b : ℝ := ε₂ * Hmax
  have hε_c : 0 < ε_c := mul_pos hε₁ hHmax_pos
  have hε_b : 0 < ε_b := mul_pos hε₂ hHmax_pos
  let R_c : ℝ := mutualInfo Qxu + 3 * ε_c + gap / 4
  have hRc_gt : mutualInfo Qxu + 3 * ε_c < R_c := by dsimp [R_c]; linarith
  have hRc_nonneg : 0 ≤ R_c := by
    dsimp [R_c]; linarith [mutualInfo_nonneg Qxu]
  -- Threshold `c := δ / (8 * B)` for each of the 4 error terms (covering tail, covering exp,
  -- Markov tail, binning collision).
  let c : ℝ := δ / (8 * B)
  have hc : 0 < c := by positivity
  -- Thresholds `N₁, N₂, N₃, N₄` for the four decaying terms.
  obtain ⟨N₁, hN₁⟩ := strongTypicalSet_prob_tendsto_one Qxu hε₁ hc
  obtain ⟨N₂, hN₂⟩ := wz_covering_exp_le (mutualInfo_nonneg Qxu) (le_of_lt hε_c) hRc_gt hc
  let C_M : ℝ := ∑ t : X × Y × Fin kU, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (C_M / (c * (ε₂ - ε₁) ^ 2))
  obtain ⟨N₄, hN₄⟩ := exists_nat_gt (log2 (1 / (c / 2)) / (gap / 2))
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) 1, fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hn)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn1 : N₁ ≤ n :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ _)) (le_trans (le_max_left _ 1) hn)
  have hn2 : N₂ ≤ n :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ _)) (le_trans (le_max_left _ 1) hn)
  have hn3 : C_M / (c * (ε₂ - ε₁) ^ 2) < (n : ℝ) := lt_of_lt_of_le hN₃ (by
    exact_mod_cast le_trans (le_trans (le_max_left N₃ N₄) (le_max_right _ _))
      (le_trans (le_max_left _ 1) hn))
  have hn4 : log2 (1 / (c / 2)) / (gap / 2) ≤ (n : ℝ) := le_of_lt (lt_of_lt_of_le hN₄ (by
    exact_mod_cast le_trans (le_trans (le_max_right N₃ N₄) (le_max_right _ _))
      (le_trans (le_max_left _ 1) hn)))
  set M_b := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  set M_c := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R_c)))
  have hMb_pos : 0 < M_b := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hMc_pos : 0 < M_c := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have : Nonempty (Fin M_b) := ⟨⟨0, hMb_pos⟩⟩
  have : Nonempty (Fin M_c) := ⟨⟨0, hMc_pos⟩⟩
  -- Define random-codebook / random-binning ensemble `(C, b)`.
  let W_C : ProbDist (Fin M_c → Fin n → Fin kU) := codebookDist Qu n M_c
  let W_b : ProbDist (Fin M_c → Fin M_b) := iidDist (ProbDist.uniform (α := Fin M_b)) M_c
  let W_ens := W_C.prod W_b
  -- Strongly typical covering set `S ⊆ jointTypicalSet Qxu n ε_c`.
  let S : Finset ((Fin n → X) × (Fin n → Fin kU)) :=
    Finset.univ.filter fun xu => zipEquiv X (Fin kU) n xu ∈ strongTypicalSet Qxu n ε₁
  let A_b : Finset ((Fin n → Fin kU) × (Fin n → Y)) := jointTypicalSet Quy n ε_b
  have hS_sub : S ⊆ jointTypicalSet Qxu n ε_c := by
    intro xu hxu
    have hmem : zipEquiv X (Fin kU) n xu ∈ strongTypicalSet Qxu n ε₁ :=
      (Finset.mem_filter.mp hxu).2
    have hle1 : ε₁ * shannonEntropy Qxu.fst ≤ ε_c := by
      dsimp [ε_c, Hmax]
      have : shannonEntropy Qxu.fst ≤ Hmax := by
        dsimp [Hmax]
        linarith [shannonEntropy_nonneg Qxu.snd, shannonEntropy_nonneg Qxu,
          shannonEntropy_nonneg Quy.fst, shannonEntropy_nonneg Quy.snd,
          shannonEntropy_nonneg Quy]
      exact mul_le_mul_of_nonneg_left this (le_of_lt hε₁)
    have hle2 : ε₁ * shannonEntropy Qxu.snd ≤ ε_c := by
      dsimp [ε_c, Hmax]
      have : shannonEntropy Qxu.snd ≤ Hmax := by
        dsimp [Hmax]
        linarith [shannonEntropy_nonneg Qxu.fst, shannonEntropy_nonneg Qxu,
          shannonEntropy_nonneg Quy.fst, shannonEntropy_nonneg Quy.snd,
          shannonEntropy_nonneg Quy]
      exact mul_le_mul_of_nonneg_left this (le_of_lt hε₁)
    have hle3 : ε₁ * shannonEntropy Qxu ≤ ε_c := by
      dsimp [ε_c, Hmax]
      have : shannonEntropy Qxu ≤ Hmax := by
        dsimp [Hmax]
        linarith [shannonEntropy_nonneg Qxu.fst, shannonEntropy_nonneg Qxu.snd,
          shannonEntropy_nonneg Quy.fst, shannonEntropy_nonneg Quy.snd,
          shannonEntropy_nonneg Quy]
      exact mul_le_mul_of_nonneg_left this (le_of_lt hε₁)
    exact strongTypicalSet_mem_jointTypicalSet Qxu hn_pos (le_of_lt hε₁) hle1 hle2 hle3 hmem
  -- Encoder index `idx C x`, encoder `encOf C b`, decoder `decOf C b`.
  let idx : (Fin M_c → Fin n → Fin kU) → (Fin n → X) → Fin M_c := fun C x =>
    if h : ∃ ℓ : Fin M_c, (x, C ℓ) ∈ S then Classical.choose h else ⟨0, hMc_pos⟩
  let encOf : (Fin M_c → Fin n → Fin kU) → (Fin M_c → Fin M_b) → (Fin n → X) → Fin M_b :=
    fun C b x => b (idx C x)
  let decIdx : (Fin M_c → Fin n → Fin kU) → (Fin M_c → Fin M_b) → Fin M_b → (Fin n → Y) → Fin M_c :=
    fun C b m y =>
      if h : ∃! ℓ' : Fin M_c, b ℓ' = m ∧ (C ℓ', y) ∈ A_b then Classical.choose h else ⟨0, hMc_pos⟩
  let decOf : (Fin M_c → Fin n → Fin kU) → (Fin M_c → Fin M_b) → Fin M_b → (Fin n → Y) → (Fin n → Xhat) :=
    fun C b m y i => g (C (decIdx C b m y) i, y i)
  -- Block distortion upper bound `dmax`.
  have hblock_le : ∀ (x : Fin n → X) (xh : Fin n → Xhat), blockDist d x xh ≤ dmax := fun x xh => by
    unfold blockDist
    calc (1 / (n : ℝ)) * ∑ i : Fin n, d.dist (x i) (xh i)
      _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, dmax :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hd_le (x i) (xh i)) (by positivity)
      _ = dmax := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, one_div_mul_cancel (ne_of_gt hn_r), one_mul]
  -- Expected distortion of a given `(C, b)` expressed over `(Fin n → X) × (Fin n → Y)`.
  let codeDist : ((Fin M_c → Fin n → Fin kU) × (Fin M_c → Fin M_b)) → ℝ := fun Cb =>
    ∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy *
      blockDist d xy.1 (decOf Cb.1 Cb.2 (encOf Cb.1 Cb.2 xy.1) xy.2)
  -- Pointwise decomposition of distortion into `Ed + δ/2` plus `dmax * (E1 + E2 + E3)`.
  let E1 : (Fin M_c → Fin n → Fin kU) → (Fin n → X) → ℝ := fun C x =>
    if ∀ ℓ : Fin M_c, (x, C ℓ) ∉ S then 1 else 0
  let E2 : (Fin M_c → Fin n → Fin kU) → (Fin n → X) → (Fin n → Y) → ℝ := fun C x y =>
    if (x, C (idx C x)) ∈ S ∧
       (fun i => (x i, y i, C (idx C x) i)) ∉ strongTypicalSet Q n ε₂ then 1 else 0
  let E3 : (Fin M_c → Fin n → Fin kU) → (Fin M_c → Fin M_b) → (Fin n → X) → (Fin n → Y) → ℝ :=
    fun C b x y =>
      ∑ ℓ' ∈ Finset.univ.erase (idx C x),
        if b ℓ' = b (idx C x) ∧ (C ℓ', y) ∈ A_b then (1 : ℝ) else 0
  have hpt_dist : ∀ (C : Fin M_c → Fin n → Fin kU) (b : Fin M_c → Fin M_b)
      (x : Fin n → X) (y : Fin n → Y),
      blockDist d x (decOf C b (encOf C b x) y) ≤
        (Ed + δ / 2) + dmax * (E1 C x + E2 C x y + E3 C b x y) := by
    intro C b x y
    have hE1_0 : 0 ≤ E1 C x := by dsimp [E1]; split_ifs <;> norm_num
    have hE2_0 : 0 ≤ E2 C x y := by dsimp [E2]; split_ifs <;> norm_num
    have hE3_0 : 0 ≤ E3 C b x y :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    by_cases h1 : ∀ ℓ : Fin M_c, (x, C ℓ) ∉ S
    · have hE1 : E1 C x = 1 := by simp [E1, h1]
      have hbd := hblock_le x (decOf C b (encOf C b x) y)
      have hge : dmax ≤ dmax * (E1 C x + E2 C x y + E3 C b x y) := by
        rw [hE1]
        have hsum1 : 1 ≤ 1 + E2 C x y + E3 C b x y := by linarith
        simpa using mul_le_mul_of_nonneg_left hsum1 hdmax0
      linarith
    · push Not at h1
      have hmemS : (x, C (idx C x)) ∈ S := by
        simp only [idx, h1, ↓reduceDIte]
        exact Classical.choose_spec h1
      by_cases h2 : (fun i => (x i, y i, C (idx C x) i)) ∈ strongTypicalSet Q n ε₂
      · -- Check whether a colliding codeword `ℓ' ≠ idx C x` exists.
        by_cases h3 : ∃ ℓ' : Fin M_c, ℓ' ≠ idx C x ∧ b ℓ' = b (idx C x) ∧ (C ℓ', y) ∈ A_b
        · rcases h3 with ⟨ℓ', hne, hb_eq, hAb⟩
          have hE3_ge : (1 : ℝ) ≤ E3 C b x y := by
            calc (1 : ℝ) = (if b ℓ' = b (idx C x) ∧ (C ℓ', y) ∈ A_b then (1 : ℝ) else 0) := by
                  simp [hb_eq, hAb]
              _ ≤ E3 C b x y := Finset.single_le_sum
                  (f := fun j => if b j = b (idx C x) ∧ (C j, y) ∈ A_b then (1 : ℝ) else 0)
                  (fun _ _ => by split_ifs <;> norm_num)
                  (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ ℓ'⟩)
          have hbd := hblock_le x (decOf C b (encOf C b x) y)
          have hge : dmax ≤ dmax * (E1 C x + E2 C x y + E3 C b x y) := by
            have hsum1 : 1 ≤ E1 C x + E2 C x y + E3 C b x y := by linarith
            simpa using mul_le_mul_of_nonneg_left hsum1 hdmax0
          linarith
        · push Not at h3
          -- Good event! First show `(C (idx C x), y) ∈ A_b`.
          have hUY_strong : (fun i => (C (idx C x) i, y i)) ∈ strongTypicalSet Quy n ε₂ :=
            strongTypicalSet_map Q (fun t => (t.2.2, t.2.1)) n ε₂ h2
          have hUY_weak : (C (idx C x), y) ∈ A_b := by
            have hle1 : ε₂ * shannonEntropy Quy.fst ≤ ε_b := by
              dsimp [ε_b]
              have : shannonEntropy Quy.fst ≤ Hmax := by
                dsimp [Hmax]
                linarith [shannonEntropy_nonneg Qxu.fst, shannonEntropy_nonneg Qxu.snd,
                  shannonEntropy_nonneg Qxu, shannonEntropy_nonneg Quy.snd,
                  shannonEntropy_nonneg Quy]
              exact mul_le_mul_of_nonneg_left this (le_of_lt hε₂)
            have hle2 : ε₂ * shannonEntropy Quy.snd ≤ ε_b := by
              dsimp [ε_b]
              have : shannonEntropy Quy.snd ≤ Hmax := by
                dsimp [Hmax]
                linarith [shannonEntropy_nonneg Qxu.fst, shannonEntropy_nonneg Qxu.snd,
                  shannonEntropy_nonneg Qxu, shannonEntropy_nonneg Quy.fst,
                  shannonEntropy_nonneg Quy]
              exact mul_le_mul_of_nonneg_left this (le_of_lt hε₂)
            have hle3 : ε₂ * shannonEntropy Quy ≤ ε_b := by
              dsimp [ε_b]
              have : shannonEntropy Quy ≤ Hmax := by
                dsimp [Hmax]
                linarith [shannonEntropy_nonneg Qxu.fst, shannonEntropy_nonneg Qxu.snd,
                  shannonEntropy_nonneg Qxu, shannonEntropy_nonneg Quy.fst,
                  shannonEntropy_nonneg Quy.snd]
              exact mul_le_mul_of_nonneg_left this (le_of_lt hε₂)
            exact strongTypicalSet_mem_jointTypicalSet Quy hn_pos (le_of_lt hε₂) hle1 hle2 hle3 hUY_strong
          -- Uniqueness implies `decIdx C b (encOf C b x) y = idx C x`.
          have huniq : ∃! ℓ' : Fin M_c, b ℓ' = encOf C b x ∧ (C ℓ', y) ∈ A_b := by
            refine ⟨idx C x, ⟨rfl, hUY_weak⟩, fun ℓ' ⟨hb', hAb'⟩ => ?_⟩
            by_contra hne
            exact h3 ℓ' hne hb' hAb'
          have hdec_eq : decIdx C b (encOf C b x) y = idx C x := by
            simp only [decIdx, huniq, ↓reduceDIte]
            have hspec := Classical.choose_spec huniq
            exact hspec.2 (idx C x) ⟨rfl, hUY_weak⟩ |>.symm
          have hdec_fun : decOf C b (encOf C b x) y = fun i => g (C (idx C x) i, y i) := by
            funext i; dsimp only [decOf]; rw [hdec_eq]
          rw [hdec_fun]
          have havg := strongTypicalSet_typical_average Q hn_pos h2
            (fun t : X × Y × Fin kU => d.dist t.1 (g (t.2.2, t.2.1)))
            (fun t => d.nonneg _ _)
          have hbd : blockDist d x (fun i => g (C (idx C x) i, y i)) ≤ Ed + ε₂ * Ed := by
            have h1' : (1 + ε₂) * Ed = Ed + ε₂ * Ed := by ring
            exact le_trans havg (le_of_eq h1')
          have hnn : 0 ≤ dmax * (E1 C x + E2 C x y + E3 C b x y) :=
            mul_nonneg hdmax0 (by linarith)
          linarith
      · have hE2 : E2 C x y = 1 := by simp [E2, hmemS, h2]
        have hbd := hblock_le x (decOf C b (encOf C b x) y)
        have hge : dmax ≤ dmax * (E1 C x + E2 C x y + E3 C b x y) := by
          rw [hE2]
          have hsum1 : 1 ≤ E1 C x + 1 + E3 C b x y := by linarith
          simpa using mul_le_mul_of_nonneg_left hsum1 hdmax0
        linarith
  -- Bound the three ensemble-averaged error sums.
  -- Term 1: Covering failure `E_{C,b}[E1] ≤ c + c`.
  have hAvg1 : ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
      (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E1 C xy.1) ≤ c + c := by
    have hxy_to_x : ∀ C,
        (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E1 C xy.1) =
          ∑ x : Fin n → X, (iidDist Qxu.fst n).pmf x * E1 C x := fun C => by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only
      rw [← Finset.sum_mul]
      change (jointIidDist P n).fst.pmf x * E1 C x = (iidDist Qxu.fst n).pmf x * E1 C x
      rw [jointIidDist_fst, hQxu_fst]
    simp_rw [hxy_to_x]
    have hcov := covering_lemma_subset Qxu n M_c (le_of_lt hε_c) S hS_sub
    have hS_prob : ∑ xu ∈ S, (jointIidDist Qxu n).pmf xu =
        ∑ z ∈ strongTypicalSet Qxu n ε₁, (iidDist Qxu n).pmf z := by
      have h1 : (∑ xu ∈ S, (jointIidDist Qxu n).pmf xu) =
          ∑ xu : (Fin n → X) × (Fin n → Fin kU),
            if zipEquiv X (Fin kU) n xu ∈ strongTypicalSet Qxu n ε₁
            then (jointIidDist Qxu n).pmf xu else 0 := by
        rw [← Finset.sum_filter]
      have h2 : (∑ z ∈ strongTypicalSet Qxu n ε₁, (iidDist Qxu n).pmf z) =
          ∑ z : Fin n → X × Fin kU,
            if z ∈ strongTypicalSet Qxu n ε₁ then (iidDist Qxu n).pmf z else 0 := by
        rw [← Finset.sum_filter]; congr 1; ext z; simp
      rw [h1, h2]
      exact Fintype.sum_equiv (zipEquiv X (Fin kU) n) _ _ (fun _ => rfl)
    have htail1 : 1 - ∑ xu ∈ S, (jointIidDist Qxu n).pmf xu ≤ c := by
      rw [hS_prob]; linarith [hN₁ n hn1]
    have hexp1 : Real.exp (-((M_c : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Qxu + 3 * ε_c))))) ≤ c :=
      hN₂ n hn2
    have hcov' : ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
        (∑ x : Fin n → X, (iidDist Qxu.fst n).pmf x * E1 C x) ≤
        (1 - ∑ xu ∈ S, (jointIidDist Qxu n).pmf xu) +
          Real.exp (-((M_c : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Qxu + 3 * ε_c))))) := by
      refine le_trans (le_of_eq ?_) hcov
      refine Finset.sum_congr rfl fun C _ => congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
      congr 1; dsimp only [E1]; split_ifs <;> rfl
    linarith
  -- Term 2: Markov failure `P(E2 | C) ≤ c` for EVERY fixed codebook `C`.
  have hAvg2 : ∀ C : Fin M_c → Fin n → Fin kU,
      (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E2 C xy.1 xy.2) ≤ c := by
    intro C
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x : Fin n → X,
        (∑ y : Fin n → Y, (jointIidDist P n).pmf (x, y) * E2 C x y) ≤
          (iidDist P.fst n).pmf x * c := by
      intro x
      simp_rw [jointIidDist_eq_fst_mul_condChannelPower P n x, mul_assoc, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ ((iidDist P.fst n).nonneg x)
      by_cases hmemS : (x, C (idx C x)) ∈ S
      · have hxu_strong : (fun i => (x i, C (idx C x) i)) ∈ strongTypicalSet Qxu n ε₁ :=
          (Finset.mem_filter.mp hmemS).2
        have hmk := markov_lemma Q hmarkov hn_pos (le_of_lt hε₁) hε₁_lt hxu_strong
        dsimp only at hmk
        have hW_eq : condChannelOfJoint (Q.map (fun t => (t.1, t.2.1))) = condChannelOfJoint P := by
          rw [hmarg]
        rw [hW_eq] at hmk
        have hE2_eq : ∀ y, E2 C x y =
            if (fun i => (x i, y i, C (idx C x) i)) ∉ strongTypicalSet Q n ε₂ then (1 : ℝ) else 0 :=
          fun y => by simp [E2, hmemS]
        simp_rw [hE2_eq]
        have hCM_le : C_M / ((n : ℝ) * (ε₂ - ε₁) ^ 2) ≤ c := by
          have hdiff : 0 < ε₂ - ε₁ := by linarith
          rw [div_le_iff₀ (by positivity)]
          have h1 := (div_lt_iff₀ (by positivity : 0 < c * (ε₂ - ε₁) ^ 2)).mp hn3
          linarith
        have hmk' : (∑ y : Fin n → Y, ((condChannelOfJoint P).power n).trans x y *
            (if (fun i => (x i, y i, C (idx C x) i)) ∉ strongTypicalSet Q n ε₂ then (1 : ℝ) else 0)) ≤
            C_M / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
          refine le_trans (le_of_eq ?_) (le_trans hmk (le_of_eq ?_))
          · refine Finset.sum_congr rfl fun y _ => congrArg _ (by split_ifs <;> rfl)
          · congr 1
        exact le_trans hmk' hCM_le
      · have hE2_0 : ∀ y, E2 C x y = 0 := fun y => by simp [E2, hmemS]
        simp_rw [hE2_0, mul_zero, Finset.sum_const_zero]
        exact le_of_lt hc
    calc ∑ x : Fin n → X, ∑ y : Fin n → Y, (jointIidDist P n).pmf (x, y) * E2 C x y
      _ ≤ ∑ x : Fin n → X, (iidDist P.fst n).pmf x * c := Finset.sum_le_sum fun x _ => hinner x
      _ = c := by rw [← Finset.sum_mul, (iidDist P.fst n).sum_one, one_mul]
  -- Term 3: Binning collision `E_{C,b}[E3] ≤ c`.
  have hAvg3 : ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
      (∑ b : Fin M_c → Fin M_b, W_b.pmf b *
        (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2)) ≤ c := by
    -- Step 3a: Average over `b` first for fixed `(C, x, y)`.
    have hinner_b : ∀ (C : Fin M_c → Fin n → Fin kU) (x : Fin n → X) (y : Fin n → Y),
        (∑ b : Fin M_c → Fin M_b, W_b.pmf b * E3 C b x y) ≤
          (1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0 := by
      intro C x y
      dsimp only [E3]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have heach : ∀ ℓ' ∈ Finset.univ.erase (idx C x),
          ∑ b : Fin M_c → Fin M_b, W_b.pmf b *
              (if b ℓ' = b (idx C x) ∧ (C ℓ', y) ∈ A_b then (1 : ℝ) else 0) =
            if (C ℓ', y) ∈ A_b then (1 : ℝ) / (M_b : ℝ) else 0 := fun ℓ' hℓ' => by
        by_cases hAb : (C ℓ', y) ∈ A_b
        · simp only [hAb, and_true, ↓reduceIte]
          exact wz_uniform_binning_collision_prob hMb_pos (idx C x) ℓ' (Finset.mem_erase.mp hℓ').1
        · simp [hAb]
      rw [Finset.sum_congr rfl heach]
      calc ∑ ℓ' ∈ Finset.univ.erase (idx C x),
            (if (C ℓ', y) ∈ A_b then (1 : ℝ) / (M_b : ℝ) else 0)
        _ ≤ ∑ ℓ' : Fin M_c, (if (C ℓ', y) ∈ A_b then (1 : ℝ) / (M_b : ℝ) else 0) :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> positivity
        _ = ∑ ℓ' : Fin M_c, (1 / (M_b : ℝ)) * (if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring
    -- Step 3b: Average over `(x, y)` and `C`, reducing to `jointTypicalSet_indep_prob_le`.
    have hstep_C : ∀ C : Fin M_c → Fin n → Fin kU,
        (∑ b : Fin M_c → Fin M_b, W_b.pmf b *
          (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2)) ≤
        (1 / (M_b : ℝ)) * ∑ y : Fin n → Y, (iidDist P.snd n).pmf y *
          (∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0) := by
      intro C
      have hswap : (∑ b : Fin M_c → Fin M_b, W_b.pmf b *
          (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2)) =
          ∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy *
            (∑ b : Fin M_c → Fin M_b, W_b.pmf b * E3 C b xy.1 xy.2) := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xy _ => Finset.sum_congr rfl fun b _ => by ring
      rw [hswap]
      calc ∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy *
            (∑ b : Fin M_c → Fin M_b, W_b.pmf b * E3 C b xy.1 xy.2)
        _ ≤ ∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy *
              ((1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if (C ℓ', xy.2) ∈ A_b then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun xy _ =>
              mul_le_mul_of_nonneg_left (hinner_b C xy.1 xy.2) ((jointIidDist P n).nonneg xy)
        _ = (1 / (M_b : ℝ)) * ∑ y : Fin n → Y, (iidDist P.snd n).pmf y *
              (∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0) := by
            rw [Fintype.sum_prod_type_right, Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            change (∑ x : Fin n → X, (jointIidDist P n).pmf (x, y) *
                ((1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0)) = _
            rw [← Finset.sum_mul]
            change (jointIidDist P n).snd.pmf y * _ = _
            rw [jointIidDist_snd]; ring
    have hC_eval :
        (∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
          ((1 / (M_b : ℝ)) * ∑ y : Fin n → Y, (iidDist P.snd n).pmf y *
            (∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0))) =
        ((M_c : ℝ) / (M_b : ℝ)) *
          ∑ uy ∈ A_b, ((iidDist Quy.fst n).prod (iidDist Quy.snd n)).pmf uy := by
      -- Swap `∑ C` inside `∑ y` and `∑ ℓ'`.
      have h1 : (∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
          ((1 / (M_b : ℝ)) * ∑ y : Fin n → Y, (iidDist P.snd n).pmf y *
            (∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0))) =
          (1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, ∑ y : Fin n → Y, (iidDist P.snd n).pmf y *
            (∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
              (if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0)) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        trans (∑ y : Fin n → Y, ∑ ℓ' : Fin M_c, ∑ C : Fin M_c → Fin n → Fin kU,
            (1 / (M_b : ℝ)) * ((iidDist P.snd n).pmf y *
              (W_C.pmf C * (if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0))))
        · refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ℓ' _ => Finset.sum_congr rfl fun C _ => by ring
        · exact Finset.sum_comm
      rw [h1]
      have hcoord : ∀ (ℓ' : Fin M_c) (y : Fin n → Y),
          (∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C * (if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0)) =
            ∑ u : Fin n → Fin kU, (iidDist Qu n).pmf u * (if (u, y) ∈ A_b then (1 : ℝ) else 0) :=
        fun ℓ' y => iidDist_sum_coord (iidDist Qu n) (fun u => if (u, y) ∈ A_b then (1 : ℝ) else 0) ℓ'
      simp_rw [hcoord, ← hQuy_fst, ← hQuy_snd]
      have hsum_uy : (∑ y : Fin n → Y, (iidDist Quy.snd n).pmf y *
          (∑ u : Fin n → Fin kU, (iidDist Quy.fst n).pmf u * (if (u, y) ∈ A_b then (1 : ℝ) else 0))) =
          ∑ uy ∈ A_b, ((iidDist Quy.fst n).prod (iidDist Quy.snd n)).pmf uy := by
        have hrew : (∑ uy ∈ A_b, ((iidDist Quy.fst n).prod (iidDist Quy.snd n)).pmf uy) =
            ∑ uy : (Fin n → Fin kU) × (Fin n → Y),
              if uy ∈ A_b then ((iidDist Quy.fst n).prod (iidDist Quy.snd n)).pmf uy else 0 := by
          rw [← Finset.sum_filter]; congr 1; ext uy; simp
        rw [hrew, Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => by
          dsimp only [ProbDist.prod]; split_ifs <;> ring
      simp_rw [hsum_uy, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    -- Step 3c: Quantitative bound `((M_c : ℝ) / (M_b : ℝ)) * 2^(-n(I(U;Y) - 3ε_b)) ≤ c`.
    have hMc_le : (M_c : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R_c) :=
      wz_max_one_floor_two_rpow_le n hRc_nonneg
    have hMb_ge : (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ (M_b : ℝ) :=
      wz_half_two_rpow_le_max_one_floor n (le_of_lt hR_pos)
    have hMb_pos_r : (0 : ℝ) < (M_b : ℝ) := Nat.cast_pos.mpr hMb_pos
    have hratio : (M_c : ℝ) / (M_b : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * (R_c - R)) := by
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R) := Real.rpow_pos_of_pos (by norm_num) _
      have h1 : (M_c : ℝ) / (M_b : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R_c) / ((2 : ℝ) ^ ((n : ℝ) * R) / 2) :=
        div_le_div₀ (by positivity) hMc_le (by positivity) hMb_ge
      have h2 : (2 : ℝ) ^ ((n : ℝ) * R_c) / ((2 : ℝ) ^ ((n : ℝ) * R) / 2) =
          2 * (2 : ℝ) ^ ((n : ℝ) * (R_c - R)) := by
        rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
        congr 2; ring
      linarith
    have hpack := jointTypicalSet_indep_prob_le Quy n ε_b
    have hexp_le : (n : ℝ) * (R_c - R) + -((n : ℝ) * (mutualInfo Quy - 3 * ε_b)) ≤
        -((n : ℝ) * (gap / 2)) := by
      have hcoef : R_c - R - (mutualInfo Quy - 3 * ε_b) ≤ -(gap / 2) := by
        dsimp only [R_c, ε_c, ε_b, ε₁, gap]
        rw [hI_eq]
        linarith [hε₂_gap]
      have hmul := mul_le_mul_of_nonneg_left hcoef (le_of_lt hn_r)
      linarith
    have hdecay : 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) ≤ c := by
      have h2 := wz_two_rpow_neg_le_of_ge (half_pos hgap) (half_pos hc) hn4
      linarith
    calc ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
          (∑ b : Fin M_c → Fin M_b, W_b.pmf b *
            (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2))
      _ ≤ ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
            ((1 / (M_b : ℝ)) * ∑ y : Fin n → Y, (iidDist P.snd n).pmf y *
              (∑ ℓ' : Fin M_c, if (C ℓ', y) ∈ A_b then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hstep_C C) (W_C.nonneg C)
      _ = ((M_c : ℝ) / (M_b : ℝ)) *
            ∑ uy ∈ A_b, ((iidDist Quy.fst n).prod (iidDist Quy.snd n)).pmf uy := hC_eval
      _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * (R_c - R))) *
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Quy - 3 * ε_b))) := by
          refine mul_le_mul hratio hpack ?_ (by positivity)
          exact Finset.sum_nonneg fun uy _ => ((iidDist Quy.fst n).prod (iidDist Quy.snd n)).nonneg uy
      _ = 2 * (2 : ℝ) ^ ((n : ℝ) * (R_c - R) + -((n : ℝ) * (mutualInfo Quy - 3 * ε_b))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
            (by norm_num)
      _ ≤ c := hdecay
  -- Combine all three bounds over the ensemble `W_ens = W_C.prod W_b`.
  have havg_total : ∑ Cb : (Fin M_c → Fin n → Fin kU) × (Fin M_c → Fin M_b),
      W_ens.pmf Cb * codeDist Cb ≤ Ed + δ := by
    have hper_Cb : ∀ Cb : (Fin M_c → Fin n → Fin kU) × (Fin M_c → Fin M_b),
        codeDist Cb ≤ (Ed + δ / 2) +
          dmax * ((∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E1 Cb.1 xy.1) +
                  (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E2 Cb.1 xy.1 xy.2) +
                  (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 Cb.1 Cb.2 xy.1 xy.2)) := by
      rintro ⟨C, b⟩
      calc codeDist (C, b)
        _ ≤ ∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy *
              ((Ed + δ / 2) + dmax * (E1 C xy.1 + E2 C xy.1 xy.2 + E3 C b xy.1 xy.2)) :=
            Finset.sum_le_sum fun xy _ =>
              mul_le_mul_of_nonneg_left (hpt_dist C b xy.1 xy.2) ((jointIidDist P n).nonneg xy)
        _ = (Ed + δ / 2) +
            dmax * ((∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E1 C xy.1) +
                    (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E2 C xy.1 xy.2) +
                    (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2)) := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
              (jointIidDist P n).sum_one, one_mul, Finset.mul_sum]
            congr 1
            congr 1
            · congr 1
              · exact Finset.sum_congr rfl fun xy _ => by ring
              · exact Finset.sum_congr rfl fun xy _ => by ring
            · exact Finset.sum_congr rfl fun xy _ => by ring
    have hsum2 : ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
        (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E2 C xy.1 xy.2) ≤ c := by
      calc ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C *
            (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E2 C xy.1 xy.2)
        _ ≤ ∑ C : Fin M_c → Fin n → Fin kU, W_C.pmf C * c :=
            Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hAvg2 C) (W_C.nonneg C)
        _ = c := by rw [← Finset.sum_mul, W_C.sum_one, one_mul]
    calc ∑ Cb, W_ens.pmf Cb * codeDist Cb
      _ ≤ ∑ Cb, W_ens.pmf Cb * ((Ed + δ / 2) +
            dmax * ((∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E1 Cb.1 xy.1) +
                    (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E2 Cb.1 xy.1 xy.2) +
                    (∑ xy : (Fin n → X) × (Fin n → Y), (jointIidDist P n).pmf xy * E3 Cb.1 Cb.2 xy.1 xy.2))) :=
          Finset.sum_le_sum fun Cb _ => mul_le_mul_of_nonneg_left (hper_Cb Cb) (W_ens.nonneg Cb)
      _ = (Ed + δ / 2) +
          dmax * ((∑ C, W_C.pmf C * (∑ xy, (jointIidDist P n).pmf xy * E1 C xy.1)) +
                  (∑ C, W_C.pmf C * (∑ xy, (jointIidDist P n).pmf xy * E2 C xy.1 xy.2)) +
                  (∑ C, W_C.pmf C * (∑ b, W_b.pmf b * (∑ xy, (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2)))) := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, W_ens.sum_one, one_mul]
          congr 1
          have hE1_b : ∑ Cb : (Fin M_c → Fin n → Fin kU) × (Fin M_c → Fin M_b),
              W_ens.pmf Cb * (dmax * ∑ xy, (jointIidDist P n).pmf xy * E1 Cb.1 xy.1) =
              dmax * ∑ C, W_C.pmf C * (∑ xy, (jointIidDist P n).pmf xy * E1 C xy.1) := by
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            refine Finset.sum_congr rfl fun C _ => ?_
            have hfac : ∀ b, W_ens.pmf (C, b) * (dmax * ∑ xy, (jointIidDist P n).pmf xy * E1 C xy.1) =
                W_b.pmf b * (dmax * (W_C.pmf C * ∑ xy, (jointIidDist P n).pmf xy * E1 C xy.1)) := by
              intro b; dsimp [W_ens, ProbDist.prod]; ring
            simp_rw [hfac, ← Finset.sum_mul, W_b.sum_one, one_mul]
          have hE2_b : ∑ Cb : (Fin M_c → Fin n → Fin kU) × (Fin M_c → Fin M_b),
              W_ens.pmf Cb * (dmax * ∑ xy, (jointIidDist P n).pmf xy * E2 Cb.1 xy.1 xy.2) =
              dmax * ∑ C, W_C.pmf C * (∑ xy, (jointIidDist P n).pmf xy * E2 C xy.1 xy.2) := by
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            refine Finset.sum_congr rfl fun C _ => ?_
            have hfac : ∀ b, W_ens.pmf (C, b) * (dmax * ∑ xy, (jointIidDist P n).pmf xy * E2 C xy.1 xy.2) =
                W_b.pmf b * (dmax * (W_C.pmf C * ∑ xy, (jointIidDist P n).pmf xy * E2 C xy.1 xy.2)) := by
              intro b; dsimp [W_ens, ProbDist.prod]; ring
            simp_rw [hfac, ← Finset.sum_mul, W_b.sum_one, one_mul]
          have hE3_b : ∑ Cb : (Fin M_c → Fin n → Fin kU) × (Fin M_c → Fin M_b),
              W_ens.pmf Cb * (dmax * ∑ xy, (jointIidDist P n).pmf xy * E3 Cb.1 Cb.2 xy.1 xy.2) =
              dmax * ∑ C, W_C.pmf C * (∑ b, W_b.pmf b * (∑ xy, (jointIidDist P n).pmf xy * E3 C b xy.1 xy.2)) := by
            rw [Fintype.sum_prod_type, Finset.mul_sum]
            refine Finset.sum_congr rfl fun C _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by dsimp [W_ens, ProbDist.prod]; ring
          rw [hE1_b, hE2_b, hE3_b]
      _ ≤ (Ed + δ / 2) + dmax * ((c + c) + c + c) :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hAvg1 hsum2) hAvg3) hdmax0)
      _ ≤ (Ed + δ / 2) + B * (4 * c) := by
          have hdB : dmax ≤ B := le_add_of_nonneg_right zero_le_one
          have h4c : 0 ≤ 4 * c := mul_nonneg (by norm_num) (le_of_lt hc)
          have hsum4 : (c + c) + c + c = 4 * c := by ring
          rw [hsum4]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hdB h4c)
      _ ≤ Ed + δ := by
          have hBc : B * (4 * c) = δ / 2 := by
            dsimp only [c]; field_simp [ne_of_gt hB]; ring
          rw [hBc]
          exact le_of_eq (by ring)
  -- Extract a deterministic codebook and binning pair `(C, b)` via the probabilistic method.
  obtain ⟨⟨C, b⟩, hCb⟩ := wz_exists_le_of_expectation_le W_ens codeDist havg_total
  refine ⟨encOf C b, decOf C b, ?_⟩
  have heq : (∑ xy : Fin n → X × Y, (iidDist P n).pmf xy *
      blockDist d (fun i => (xy i).1)
        (decOf C b (encOf C b (fun i => (xy i).1)) (fun i => (xy i).2))) = codeDist (C, b) :=
    (Fintype.sum_equiv (zipEquiv X Y n) _ _ (fun _ => rfl)).symm
  rw [heq]
  exact hCb

/-- **Wyner–Ziv Achievability** (Cover & Thomas Theorem 15.9.1; El Gamal–Kim Theorem 11.3):
    for any feasible distortion level `D`, any rate `R > wynerZivRateDistortion P d D`, and
    any `δ > 0`, for all sufficiently large `n` there exist an encoder and decoder of size
    `M = max 1 ⌊2^(n R)⌋` achieving expected per-symbol distortion at most `D + δ`. -/
theorem wynerZiv_achievability (P : ProbDist (X × Y)) (d : Distortion X Xhat) {D R δ : ℝ}
    (hfeas : IsWynerZivFeasible P d D)
    (hR : wynerZivRateDistortion P d D < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : (Fin n → X) → Fin M) (dec : Fin M → (Fin n → Y) → (Fin n → Xhat)),
        ∑ xy : Fin n → X × Y, (iidDist P n).pmf xy *
          blockDist d (fun i => (xy i).1)
            (dec (enc (fun i => (xy i).1)) (fun i => (xy i).2)) ≤ D + δ := by
  have hbdd : BddBelow { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU))
      (g : Fin kU × Y → Xhat), 0 < kU ∧ Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
      (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D ∧
      r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) } :=
    ⟨0, by rintro r ⟨_, Q, _, _, _, _, _, rfl⟩; exact condMutualInfo_nonneg _⟩
  have hne : { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat),
      0 < kU ∧ Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
      (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D ∧
      r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) }.Nonempty := by
    rcases hfeas with ⟨kU, Q, g, hk, hm, hmk, hd⟩
    exact ⟨_, kU, Q, g, hk, hm, hmk, hd, rfl⟩
  obtain ⟨r, ⟨kU, Q, g, hk, hm, hmk, hd, rfl⟩, hI_lt⟩ := (csInf_lt_iff hbdd hne).mp hR
  obtain ⟨N, hN⟩ := wynerZiv_achievability_of_dist P d hk Q g hm hmk hI_lt hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, hcode⟩ := hN n hn
  exact ⟨enc, dec, le_trans hcode (by linarith)⟩

/-- **Operational Wyner–Ziv Achievability**: for any feasible distortion `D`,
    every rate `R > wynerZivRateDistortion P d D` is operationally achievable. -/
theorem wynerZiv_operational_achievability (P : ProbDist (X × Y)) (d : Distortion X Xhat)
    {D R : ℝ} (hfeas : IsWynerZivFeasible P d D)
    (hR : wynerZivRateDistortion P d D < R) :
    IsWynerZivAchievable P d D R := by
  refine ⟨le_of_lt (lt_of_le_of_lt (wynerZivRateDistortion_nonneg P d D) hR), fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := wynerZiv_achievability P d hfeas hR hδ
  exact ⟨max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1),
    fun n hn => hN n (le_trans (le_max_left N 1) hn)⟩

/-- **Operational Wyner–Ziv Converse**: at any strictly feasible distortion `D`
    (`∃ D₀ < D, IsWynerZivFeasible P d D₀`), every operationally achievable rate `R`
    satisfies `wynerZivRateDistortion P d D ≤ R`. -/
theorem wynerZiv_operational_converse (P : ProbDist (X × Y)) (d : Distortion X Xhat)
    {D R : ℝ} (hstrict : ∃ D₀ : ℝ, D₀ < D ∧ IsWynerZivFeasible P d D₀)
    (hach : IsWynerZivAchievable P d D R) :
    wynerZivRateDistortion P d D ≤ R := by
  have hR_nonneg : 0 ≤ R := hach.1
  have hle_plus : ∀ δ > 0, wynerZivRateDistortion P d (D + δ) ≤ R := by
    intro δ hδ
    obtain ⟨N, hN_pos, hN⟩ := hach.2 δ hδ
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((N : ℝ) * R)))
    obtain ⟨enc, dec, hcode⟩ := hN N le_rfl
    have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    have hconv : wynerZivRateDistortion P d (D + δ) ≤ log2 (M : ℝ) / (N : ℝ) :=
      wynerZiv_converse P d hN_pos hM_pos enc dec hcode
    have hM_le_pow : (M : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * R) :=
      wz_max_one_floor_two_rpow_le N hR_nonneg
    have hM_pos_r : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogM_le : log2 (M : ℝ) ≤ (N : ℝ) * R := by
      unfold log2
      rw [div_le_iff₀ hlog2_pos]
      calc Real.log (M : ℝ)
        _ ≤ Real.log ((2 : ℝ) ^ ((N : ℝ) * R)) := Real.log_le_log hM_pos_r hM_le_pow
        _ = ((N : ℝ) * R) * Real.log 2 := Real.log_rpow (by norm_num : (0 : ℝ) < 2) _
    have hN_pos_r : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    have hdiv_le : log2 (M : ℝ) / (N : ℝ) ≤ R := (div_le_iff₀ hN_pos_r).mpr (by linarith)
    exact le_trans hconv hdiv_le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hrc⟩ := wynerZivRateDistortion_rightContinuous P d hstrict ε hε
  have hR_ge := hle_plus δ hδ
  linarith

/-- **The Wyner–Ziv Theorem** (Cover & Thomas, Theorem 15.9.1; El Gamal–Kim, Theorem 11.3):
    for any discrete memoryless correlated source `P : ProbDist (X × Y)`, distortion measure
    `d : Distortion X Xhat`, and strictly feasible distortion level `D`
    (`∃ D₀ < D, IsWynerZivFeasible P d D₀`), the operational Wyner–Ziv rate–distortion
    function equals the single-letter Wyner–Ziv rate–distortion function:
    `operationalWynerZivRate P d D = wynerZivRateDistortion P d D`. -/
theorem wyner_ziv_theorem (P : ProbDist (X × Y)) (d : Distortion X Xhat) {D : ℝ}
    (hstrict : ∃ D₀ : ℝ, D₀ < D ∧ IsWynerZivFeasible P d D₀) :
    operationalWynerZivRate P d D = wynerZivRateDistortion P d D := by
  have hfeas : IsWynerZivFeasible P d D := by
    rcases hstrict with ⟨D₀, hlt, kU, Q, g, hk, hm, hmk, hd⟩
    exact ⟨kU, Q, g, hk, hm, hmk, by linarith⟩
  unfold operationalWynerZivRate
  have hbdd : BddBelow { R : ℝ | IsWynerZivAchievable P d D R } :=
    ⟨0, fun _ hR => hR.1⟩
  have hne : { R : ℝ | IsWynerZivAchievable P d D R }.Nonempty :=
    ⟨wynerZivRateDistortion P d D + 1,
      wynerZiv_operational_achievability P d hfeas (by linarith)⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd (wynerZiv_operational_achievability P d hfeas (by linarith))
  · exact le_csInf hne fun R hR => wynerZiv_operational_converse P d hstrict hR

end WynerZivAchievability

end InfoTheory.Bridge
