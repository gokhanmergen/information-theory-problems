import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability
import InfoTheory.Bridge.RelayCoding

/-!
# Decode-and-Forward Achievability & Degraded Relay Channel Capacity Theorem
(Cover & El Gamal 1979, Theorem 1; Cover & Thomas Theorem 15.10.2; El Gamal & Kim Theorems 16.2–16.3)

Purely additive, kernel-verified formalization of the Cover–El Gamal Decode-and-Forward (DF)
achievability theorem and the exact capacity theorem for physically degraded discrete memoryless
relay channels, directly against `InfoTheory.Core.Channels.{RelayChannel, IsRelayAchievable,
relayCapacity, relayCutsetBound}`:

1. **Relay `Y_r`-Marginal & Decode-and-Forward Rate (`relayYrChannel`, `relayDFRate`)**:
   - `relayDFRate W := sup_{P(x, x_r)} min { I(X; Y_r | X_r), I(X, X_r; Y) }`.
   - `relayDFRate_bddAbove`, `relayDFRate_nonneg`, `relayDFRate_le_cutsetBound`.

2. **Block-Markov Superposition Coding & Decode-and-Forward Achievability**:
   - Single-block superposition codebook `(X_r^k(w_prev), X^k(w_prev, w_curr))` with
     3-way joint-typicality decoding at the relay (`I(X; Y_r | X_r)`) and 2-way joint-typicality
     backward decoding at the destination (`I(X, X_r; Y)`).
   - Strictly causal block-Markov relay strategy over `B` blocks of length `k` (with padding to
     arbitrary blocklengths `n ≥ B * k`).
   - `isRelayAchievable_zero`, `relayDF_achievable`, `relayDFRate_le_relayCapacity`.

3. **Physically Degraded Relay Channel Capacity Theorem (Cover & El Gamal 1979, Theorem 1)**:
   - `IsPhysicallyDegradedRelay`: `p(y, y_r | x, x_r) = p(y_r | x, x_r) · D(y | y_r, x_r)`.
   - `degradedRelay_cmi_eq`: `I(X; Y, Y_r | X_r) = I(X; Y_r | X_r)` via Markov chain `X — (Y_r, X_r) — Y`.
   - `degradedRelay_cutset_eq_df`: `relayCutsetBound W = relayDFRate W`.
   - `degradedRelay_capacity_theorem`: `relayCapacity W = relayCutsetBound W`.
   - `degradedRelay_capacity_eq_df`: `relayCapacity W = relayDFRate W`.

All theorems are purely additive and leave `Core/`, `Problems/`, `STATEMENT_LOCK.json`,
and `Known/` untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Shared Private Helpers -/

section Helpers

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

private lemma ra_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

private lemma ra_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma ra_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  apply ra_probDist_ext; intro a
  unfold ProbDist.map ProbDist.fst; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma ra_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  apply ra_probDist_ext; intro b
  unfold ProbDist.map ProbDist.snd; dsimp only
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single b]
  · simp
  · intro b' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma ra_exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
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

private lemma ra_sum_pi_prod_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private lemma ra_sum_pi_prod_mul_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private lemma ra_two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
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

private lemma ra_iidDist_map_comp (P : ProbDist α) (n : ℕ) (g : α → γ) :
    (iidDist P n).map (fun z i => g (z i)) = iidDist (P.map g) n := by
  classical
  apply ra_probDist_ext; intro u
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

private lemma ra_sum_not_mem_of_map [DecidableEq γ]
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

/-- Non-dependent `Fin.snoc` appending a single element to `Fin n → α`. -/
private abbrev raSnocVec {n : ℕ} (xs : Fin n → α) (a : α) : Fin (n + 1) → α :=
  Fin.snoc (α := fun _ => α) xs a

/-- Equivalence separating the prefix `Fin n` from the last coordinate `Fin.last n`. -/
private def raPiSnocEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α where
  toFun := fun x => (fun i => x i.castSucc, x (Fin.last n))
  invFun := fun p => raSnocVec p.1 p.2
  left_inv := fun x => by
    funext i
    refine Fin.lastCases ?_ ?_ i <;> simp [raSnocVec]
  right_inv := fun ⟨_, _⟩ => Prod.ext (funext fun _ => by simp [raSnocVec]) (by simp [raSnocVec])

/-- Explicit equivalence `(Fin B × Fin k) ≃ Fin (B * k)` preserving block order:
    `(b, j) ↦ b * k + j`. -/
private def raBlockEquiv (B k : ℕ) (hk : 0 < k) : (Fin B × Fin k) ≃ Fin (B * k) where
  toFun := fun p => ⟨p.1.1 * k + p.2.1, by
    have h1 : (p.1.1 + 1) * k ≤ B * k := Nat.mul_le_mul_right k p.1.2
    linarith [p.2.2]⟩
  invFun := fun i =>
    (⟨i.1 / k, Nat.div_lt_of_lt_mul (by have := i.2; nlinarith)⟩,
     ⟨i.1 % k, Nat.mod_lt _ hk⟩)
  left_inv := fun ⟨b, j⟩ => by
    ext
    · dsimp only
      rw [mul_comm b.1 k, Nat.mul_add_div hk, Nat.div_eq_of_lt j.2, add_zero]
    · dsimp only
      rw [mul_comm b.1 k, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
  right_inv := fun i => by
    ext
    dsimp only
    rw [mul_comm, Nat.div_add_mod]

/-- Equivalence splitting a length-`(B * k)` vector into `B` blocks of length `k`. -/
private def raUnblockEquiv (α : Type*) (B k : ℕ) (hk : 0 < k) :
    (Fin (B * k) → α) ≃ (Fin B → Fin k → α) where
  toFun := fun f b j => f (raBlockEquiv B k hk (b, j))
  invFun := fun g i => g ((raBlockEquiv B k hk).symm i).1 ((raBlockEquiv B k hk).symm i).2
  left_inv := fun f => by
    funext i
    simp
  right_inv := fun g => by
    funext b j
    simp

/-- Conditional channel `P_{X|U}(x | u)` extracted from a joint distribution `Pux : ProbDist (U × X)`. -/
private noncomputable def raCondChannel {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) : DMC U X := by
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

private lemma raCondChannel_mul_fst {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) (u : U) (x : X) :
    Pux.fst.pmf u * (raCondChannel Pux).trans u x = Pux.pmf (u, x) := by
  classical
  unfold raCondChannel; dsimp only
  by_cases h : Pux.fst.pmf u = 0
  · rw [h, zero_mul]
    have hle : Pux.pmf (u, x) ≤ Pux.fst.pmf u :=
      Finset.single_le_sum (fun x' _ => Pux.nonneg (u, x')) (Finset.mem_univ x)
    exact (le_antisymm (by linarith) (Pux.nonneg (u, x))).symm
  · simp only [h, ↓reduceIte]
    exact mul_div_cancel₀ _ h

private lemma raCondChannel_power_mul_iid {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) (k : ℕ) (u : Fin k → U) (x : Fin k → X) :
    (iidDist Pux.fst k).pmf u * ((raCondChannel Pux).power k).trans u x =
      (iidDist Pux k).pmf (fun i => (u i, x i)) := by
  unfold iidDist DMC.power; dsimp only
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => raCondChannel_mul_fst Pux (u i) (x i)

private lemma raCondChannel_power_eq_div {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) (k : ℕ) (u : Fin k → U) (x : Fin k → X)
    (hu : (iidDist Pux.fst k).pmf u ≠ 0) :
    ((raCondChannel Pux).power k).trans u x =
      (iidDist Pux k).pmf (fun i => (u i, x i)) / (iidDist Pux.fst k).pmf u := by
  rw [eq_div_iff hu, mul_comm, raCondChannel_power_mul_iid]

/-- A single superposition cloud: cloud center `u ∈ U^k` and `M` satellites `xs : Fin M → X^k`. -/
private abbrev RaCloudCode (U X : Type*) (k M : ℕ) :=
  (Fin k → U) × (Fin M → Fin k → X)

/-- Random cloud law: `U^k ~ P_U^k`, and each satellite `X^k(m) | U^k ~ P_{X|U}^k` independently. -/
private noncomputable def raCloudDist {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) (k M : ℕ) : ProbDist (RaCloudCode U X k M) where
  pmf := fun c => (iidDist Pux.fst k).pmf c.1 *
    ∏ m : Fin M, ((raCondChannel Pux).power k).trans c.1 (c.2 m)
  nonneg := fun c => mul_nonneg ((iidDist Pux.fst k).nonneg c.1)
    (Finset.prod_nonneg fun m _ => ((raCondChannel Pux).power k).nonneg c.1 (c.2 m))
  sum_one := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ u : Fin k → U,
        ∑ xs : Fin M → Fin k → X,
          (iidDist Pux.fst k).pmf u *
            ∏ m : Fin M, ((raCondChannel Pux).power k).trans u (xs m) =
        (iidDist Pux.fst k).pmf u := fun u => by
      rw [← Finset.mul_sum, ← Fintype.prod_sum]
      have h1 : ∏ _m : Fin M, ∑ x : Fin k → X, ((raCondChannel Pux).power k).trans u x = 1 :=
        Finset.prod_eq_one fun _ _ => ((raCondChannel Pux).power k).sum_one u
      rw [h1, mul_one]
    simp_rw [hinner]
    exact (iidDist Pux.fst k).sum_one

private lemma raCloudDist_sum_single_sat {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) (k M : ℕ) (m : Fin M) (f : (Fin k → U) → (Fin k → X) → ℝ) :
    ∑ c : RaCloudCode U X k M, (raCloudDist Pux k M).pmf c * f c.1 (c.2 m) =
      ∑ u : Fin k → U, ∑ x : Fin k → X, (iidDist Pux k).pmf (fun i => (u i, x i)) * f u x := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp_rw [raCloudDist, mul_assoc]
  rw [← Finset.mul_sum]
  let Q : ProbDist (Fin k → X) := dmcRow ((raCondChannel Pux).power k) u
  have hQ := ra_sum_pi_prod_mul_single Q m (fun x => f u x)
  dsimp only [Q, dmcRow] at hQ
  rw [hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, raCondChannel_power_mul_iid]

private lemma raCloudDist_sum_pair_sat {U X : Type*} [Fintype U] [Fintype X] [Nonempty X]
    (Pux : ProbDist (U × X)) (k M : ℕ) (m m' : Fin M) (hne : m' ≠ m)
    (f g : (Fin k → U) → (Fin k → X) → ℝ) :
    ∑ c : RaCloudCode U X k M, (raCloudDist Pux k M).pmf c * (f c.1 (c.2 m) * g c.1 (c.2 m')) =
      ∑ u : Fin k → U,
        (∑ x : Fin k → X, (iidDist Pux k).pmf (fun i => (u i, x i)) * f u x) *
        (∑ x' : Fin k → X, ((raCondChannel Pux).power k).trans u x' * g u x') := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp_rw [raCloudDist, mul_assoc]
  rw [← Finset.mul_sum]
  let Q : ProbDist (Fin k → X) := dmcRow ((raCondChannel Pux).power k) u
  have hQ := ra_sum_pi_prod_mul_pair Q m m' hne (fun x => f u x) (fun x' => g u x')
  dsimp only [Q, dmcRow] at hQ
  rw [hQ, ← mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, raCondChannel_power_mul_iid]

end Helpers

/-! ### 1. Relay `Y_r`-Marginal, Decode-and-Forward Rate, and Cut-Set Comparison -/

section DFRate

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- Relay-observation marginal DMC `p(y_r | x, x_r) = ∑_y W(y, y_r | x, x_r)` of a relay channel `W`. -/
def relayYrChannel (W : RelayChannel X Xr Y Yr) : DMC (X × Xr) Yr where
  trans := fun xxr yr => ∑ y : Y, W.trans xxr (y, yr)
  nonneg := fun xxr yr => Finset.sum_nonneg fun y _ => W.nonneg xxr (y, yr)
  sum_one := fun xxr => by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact W.sum_one xxr

/-- **Decode-and-Forward Achievable Rate** (Cover & El Gamal 1979; Cover & Thomas §15.10;
    El Gamal & Kim Theorem 16.2):
    `R_DF(W) = sup_{P(x, x_r)} min { I(X; Y_r | X_r), I(X, X_r; Y) }`. -/
noncomputable def relayDFRate (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { r : ℝ | ∃ P : ProbDist (X × Xr),
    let J := W.joint P
    let I_X_Yr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
    let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
    r = min I_X_Yr_given_Xr I_XXr_Y }

/-- Chain rule for conditional mutual information on a relay channel:
    `I(X; Y, Y_r | X_r) = I(X; Y_r | X_r) + I(X; Y | Y_r, X_r)`. -/
private lemma relay_cmi_chain_rule (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) :
    let J := W.joint P
    condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2))) =
      condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) +
      condMutualInfo (J.map (fun z => (z.1.1, z.2.1, (z.2.2, z.1.2)))) := by
  dsimp only
  let J := W.joint P
  let Q₁ := J.map (fun z => (z.1.1, z.2, z.1.2))
  let Q₂ := J.map (fun z => (z.1.1, z.2.2, z.1.2))
  let Q₃ := J.map (fun z => (z.1.1, z.2.1, (z.2.2, z.1.2)))
  let e_xz : (X × (Yr × Xr)) ≃ (X × Yr × Xr) :=
    { toFun := fun t => (t.1, t.2.1, t.2.2)
      invFun := fun t => (t.1, (t.2.1, t.2.2))
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  let e_yz : (Y × (Yr × Xr)) ≃ ((Y × Yr) × Xr) :=
    { toFun := fun t => ((t.1, t.2.1), t.2.2)
      invFun := fun t => (t.1.1, (t.1.2, t.2))
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  let e_all : (X × Y × (Yr × Xr)) ≃ (X × (Y × Yr) × Xr) :=
    { toFun := fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2)
      invFun := fun t => (t.1, t.2.1.1, (t.2.1.2, t.2.2))
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl }
  have h1 : Q₁.map (fun t => (t.1, t.2.2)) = Q₂.map (fun t => (t.1, t.2.2)) := by
    dsimp only [Q₁, Q₂]; rw [map_comp_eq, map_comp_eq]; rfl
  have h2 : Q₁.map (fun t => t.2.2) = Q₂.map (fun t => t.2.2) := by
    dsimp only [Q₁, Q₂]; rw [map_comp_eq, map_comp_eq]; rfl
  have h3 : Q₂.map (fun t => (t.2.1, t.2.2)) = Q₃.map (fun t => t.2.2) := by
    dsimp only [Q₂, Q₃]; rw [map_comp_eq, map_comp_eq]; rfl
  have h4 : (Q₃.map (fun t => (t.1, t.2.2))).map e_xz = Q₂ := by
    dsimp only [Q₂, Q₃]; rw [map_comp_eq, map_comp_eq]; rfl
  have h5 : (Q₃.map (fun t => (t.2.1, t.2.2))).map e_yz = Q₁.map (fun t => (t.2.1, t.2.2)) := by
    dsimp only [Q₁, Q₃]; rw [map_comp_eq, map_comp_eq, map_comp_eq]; rfl
  have h6 : Q₃.map e_all = Q₁ := by
    dsimp only [Q₁, Q₃]; rw [map_comp_eq]; rfl
  have he4 : shannonEntropy (Q₃.map (fun t => (t.1, t.2.2))) = shannonEntropy Q₂ := by
    rw [← h4, shannonEntropy_map_equiv e_xz]
  have he5 : shannonEntropy (Q₃.map (fun t => (t.2.1, t.2.2))) =
      shannonEntropy (Q₁.map (fun t => (t.2.1, t.2.2))) := by
    rw [← h5, shannonEntropy_map_equiv e_yz]
  have he6 : shannonEntropy Q₃ = shannonEntropy Q₁ := by
    rw [← h6, shannonEntropy_map_equiv e_all]
  unfold condMutualInfo
  dsimp only
  change shannonEntropy (Q₁.map (fun t => (t.1, t.2.2))) +
      shannonEntropy (Q₁.map (fun t => (t.2.1, t.2.2))) -
      shannonEntropy Q₁ - shannonEntropy (Q₁.map (fun t => t.2.2)) =
    (shannonEntropy (Q₂.map (fun t => (t.1, t.2.2))) +
      shannonEntropy (Q₂.map (fun t => (t.2.1, t.2.2))) -
      shannonEntropy Q₂ - shannonEntropy (Q₂.map (fun t => t.2.2))) +
    (shannonEntropy (Q₃.map (fun t => (t.1, t.2.2))) +
      shannonEntropy (Q₃.map (fun t => (t.2.1, t.2.2))) -
      shannonEntropy Q₃ - shannonEntropy (Q₃.map (fun t => t.2.2)))
  rw [h1, h2, h3, he4, he5, he6]
  ring

private lemma relay_cmi_Yr_le_YYr (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) :
    condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.2, z.1.2))) ≤
      condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))) := by
  have hchain := relay_cmi_chain_rule W P
  dsimp only at hchain
  have hnn : 0 ≤ condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.1, (z.2.2, z.1.2)))) :=
    condMutualInfo_nonneg _
  linarith

/-- The set of single-letter DF rates over all `P ∈ Δ(X × X_r)` is bounded above. -/
theorem relayDFRate_bddAbove (W : RelayChannel X Xr Y Yr) :
    BddAbove { r : ℝ | ∃ P : ProbDist (X × Xr),
      let J := W.joint P
      let I_X_Yr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
      let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
      r = min I_X_Yr_given_Xr I_XXr_Y } := by
  refine ⟨relayCutsetBound W, ?_⟩
  rintro r ⟨P, rfl⟩
  have h1 : min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.2, z.1.2))))
      (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1)))) ≤
    min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))))
      (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1)))) :=
    min_le_min_right _ (relay_cmi_Yr_le_YYr W P)
  exact le_trans h1 (le_csSup (relayCutsetBound_bddAbove W) ⟨P, rfl⟩)

/-- The Decode-and-Forward rate is nonnegative whenever the input alphabets are nonempty. -/
theorem relayDFRate_nonneg [Nonempty X] [Nonempty Xr] (W : RelayChannel X Xr Y Yr) :
    0 ≤ relayDFRate W := by
  let P : ProbDist (X × Xr) := ProbDist.uniform
  have h1 : 0 ≤ condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.2, z.1.2))) :=
    condMutualInfo_nonneg _
  have h2 : 0 ≤ mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) :=
    mutualInfo_nonneg _
  exact le_trans (le_min h1 h2) (le_csSup (relayDFRate_bddAbove W) ⟨P, rfl⟩)

/-- The Decode-and-Forward rate never exceeds the cut-set upper bound:
    `relayDFRate W ≤ relayCutsetBound W`. -/
theorem relayDFRate_le_cutsetBound (W : RelayChannel X Xr Y Yr) :
    relayDFRate W ≤ relayCutsetBound W := by
  by_cases hne : Nonempty (X × Xr)
  · have : Nonempty X := ⟨hne.some.1⟩
    have : Nonempty Xr := ⟨hne.some.2⟩
    unfold relayDFRate
    refine Real.sSup_le ?_ (relayCutsetBound_nonneg W)
    rintro r ⟨P, rfl⟩
    have h1 : min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.2, z.1.2))))
        (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1)))) ≤
      min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))))
        (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1)))) :=
      min_le_min_right _ (relay_cmi_Yr_le_YYr W P)
    exact le_trans h1 (le_csSup (relayCutsetBound_bddAbove W) ⟨P, rfl⟩)
  · have hemp₁ : { r : ℝ | ∃ P : ProbDist (X × Xr),
        let J := W.joint P
        let I_X_Yr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
        let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
        r = min I_X_Yr_given_Xr I_XXr_Y } = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, _⟩
      exact hne (ra_nonempty_of_probDist P)
    have hemp₂ : { r : ℝ | ∃ P : ProbDist (X × Xr),
        let J := W.joint P
        let I_X_YYr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2)))
        let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
        r = min I_X_YYr_given_Xr I_XXr_Y } = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, _⟩
      exact hne (ra_nonempty_of_probDist P)
    unfold relayDFRate relayCutsetBound
    rw [hemp₁, hemp₂, Real.sSup_empty]

end DFRate

/-! ### 2. Single-Block Relay & Destination Typicality and Random-Coding Bounds -/

section SingleBlockRandomCoding

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- Equivalence zipping `(xr^k, x^k, yr^k)` into a length-`k` sequence of `((xr_i, x_i), yr_i)`. -/
private def relayZipEquiv (Xr X Yr : Type*) (k : ℕ) :
    ((Fin k → Xr) × (Fin k → X) × (Fin k → Yr)) ≃ (Fin k → (Xr × X) × Yr) where
  toFun := fun t i => ((t.1 i, t.2.1 i), t.2.2 i)
  invFun := fun z => (fun i => (z i).1.1, fun i => (z i).1.2, fun i => (z i).2)
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun _ => rfl

private lemma relayYChannel_joint_eq' (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) :
    (W.joint P).map (fun z => (z.1, z.2.1)) = (relayYChannel W).joint P := by
  classical
  apply ra_probDist_ext; rintro ⟨xxr, y⟩
  unfold ProbDist.map DMC.joint relayYChannel; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single xxr]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
    · simp [Finset.mul_sum]
    · intro y' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro xxr' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma relayYrChannel_joint_eq (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) :
    (W.joint P).map (fun z => (z.1, z.2.2)) = (relayYrChannel W).joint P := by
  classical
  apply ra_probDist_ext; rintro ⟨xxr, yr⟩
  unfold ProbDist.map DMC.joint relayYrChannel; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single xxr]
  · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single yr]
    · simp [Finset.mul_sum]
    · intro yr' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro xxr' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma relay_Pswap_pmf (P : ProbDist (X × Xr)) (xr : Xr) (x : X) :
    (P.map Prod.swap).pmf (xr, x) = P.pmf (x, xr) := by
  classical
  unfold ProbDist.map; dsimp only
  rw [Finset.sum_eq_single (x, xr)]
  · simp
  · intro p _ hne
    have : Prod.swap p ≠ (xr, x) := fun h => hne (by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext h2 h1)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma relay_P_XrXYr_pmf (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (xr : Xr) (x : X) (yr : Yr) :
    ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))).pmf ((xr, x), yr) =
      (P.map Prod.swap).pmf (xr, x) * (relayYrChannel W).trans (x, xr) yr := by
  classical
  rw [relay_Pswap_pmf]
  unfold ProbDist.map DMC.joint relayYrChannel; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (x, xr)]
  · rw [Fintype.sum_prod_type_right, Finset.sum_eq_single yr]
    · simp [Finset.mul_sum]
    · intro yr' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro xxr' _ hne
    refine Finset.sum_eq_zero fun yyr _ => ?_
    have : ((xxr'.2, xxr'.1), yyr.2) ≠ ((xr, x), yr) := fun h => hne (by
      have h1 := congrArg (fun t => t.1.2) h
      have h2 := congrArg (fun t => t.1.1) h
      exact Prod.ext h1 h2)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma relay_P_XrYr_pmf (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (xr : Xr) (yr : Yr) :
    ((W.joint P).map (fun z => (z.1.2, z.2.2))).pmf (xr, yr) =
      ∑ x : X, (P.map Prod.swap).pmf (xr, x) * (relayYrChannel W).trans (x, xr) yr := by
  classical
  have h1 : (W.joint P).map (fun z => (z.1.2, z.2.2)) =
      ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))).map (fun t => (t.1.1, t.2)) := by
    rw [map_comp_eq]; rfl
  rw [h1]
  unfold ProbDist.map; dsimp only
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single xr]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single yr]
    · simp only [↓reduceIte]
      exact relay_P_XrXYr_pmf W P xr x yr
    · intro yr' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro xr' _ hne; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma relayIid_XrXYr_pmf (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) (k : ℕ)
    (xr : Fin k → Xr) (x : Fin k → X) (yr : Fin k → Yr) :
    (iidDist (P.map Prod.swap) k).pmf (fun i => (xr i, x i)) *
        ((relayYrChannel W).power k).trans (fun i => (x i, xr i)) yr =
      (iidDist ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))) k).pmf
        (relayZipEquiv Xr X Yr k (xr, x, yr)) := by
  unfold iidDist DMC.power; dsimp only [relayZipEquiv, Equiv.coe_fn_mk]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (relay_P_XrXYr_pmf W P (xr i) (x i) (yr i)).symm

private lemma relayIid_XrYr_marginal (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) (k : ℕ)
    (xr : Fin k → Xr) (yr : Fin k → Yr) :
    ∑ x : Fin k → X, (iidDist (P.map Prod.swap) k).pmf (fun i => (xr i, x i)) *
        ((relayYrChannel W).power k).trans (fun i => (x i, xr i)) yr =
      (iidDist ((W.joint P).map (fun z => (z.1.2, z.2.2))) k).pmf (fun i => (xr i, yr i)) := by
  have hfun : ∀ x : Fin k → X,
      (iidDist (P.map Prod.swap) k).pmf (fun i => (xr i, x i)) *
          ((relayYrChannel W).power k).trans (fun i => (x i, xr i)) yr =
        ∏ i : Fin k, (P.map Prod.swap).pmf (xr i, x i) * (relayYrChannel W).trans (x i, xr i) (yr i) :=
    fun x => by unfold iidDist DMC.power; dsimp only; rw [← Finset.prod_mul_distrib]
  simp_rw [hfun]
  rw [← Fintype.prod_sum (fun i x => (P.map Prod.swap).pmf (xr i, x) * (relayYrChannel W).trans (x, xr i) (yr i))]
  unfold iidDist; dsimp only
  exact Finset.prod_congr rfl fun i _ => (relay_P_XrYr_pmf W P (xr i) (yr i)).symm

/-- **Three-Way Jointly Weakly Typical Set** `A_ε^(k)(X_r, X, Y_r)` for relay decoding. -/
private noncomputable def relayTypicalSet (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k : ℕ) (ε : ℝ) : Finset ((Fin k → Xr) × (Fin k → X) × (Fin k → Yr)) := by
  classical
  let Pswap := P.map Prod.swap
  let J := W.joint P
  let P_Yr := J.map (fun z => z.2.2)
  let P_XrYr := J.map (fun z => (z.1.2, z.2.2))
  let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
  exact Finset.univ.filter fun t =>
    t.1 ∈ weakTypicalSet Pswap.fst k ε ∧
    (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Pswap k ε ∧
    t.2.2 ∈ weakTypicalSet P_Yr k ε ∧
    (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet P_XrYr k ε ∧
    (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈ weakTypicalSet P_XrXYr k ε

private lemma mem_relayTypicalSet (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k : ℕ) (ε : ℝ) (t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr)) :
    let Pswap := P.map Prod.swap
    let J := W.joint P
    t ∈ relayTypicalSet W P k ε ↔
      t.1 ∈ weakTypicalSet Pswap.fst k ε ∧
      (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Pswap k ε ∧
      t.2.2 ∈ weakTypicalSet (J.map (fun z => z.2.2)) k ε ∧
      (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet (J.map (fun z => (z.1.2, z.2.2))) k ε ∧
      (fun i => ((t.1 i, t.2.1 i), t.2.2 i)) ∈
        weakTypicalSet (J.map (fun z => ((z.1.2, z.1.1), z.2.2))) k ε := by
  classical
  simp [relayTypicalSet]

private lemma relayTypicalSet_card_le (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k : ℕ) (ε : ℝ) :
    ((relayTypicalSet W P k ε).card : ℝ) ≤
      (2 : ℝ) ^ ((k : ℝ) * (shannonEntropy ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))) + ε)) := by
  classical
  have hle : (relayTypicalSet W P k ε).card ≤
      (weakTypicalSet ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))) k ε).card := by
    refine Finset.card_le_card_of_injOn (relayZipEquiv Xr X Yr k) ?_ ?_
    · intro t ht; exact ((mem_relayTypicalSet W P k ε t).mp ht).2.2.2.2
    · intro t₁ _ t₂ _ h; exact (relayZipEquiv Xr X Yr k).injective h
  exact le_trans (by exact_mod_cast hle) (weakTypicalSet_card_le _ k ε)

private lemma relay_aep_prob_tendsto_one (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    let P_XrXYr := (W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))
    ∃ K : ℕ, ∀ k ≥ K,
      1 - δ ≤ ∑ t ∈ relayTypicalSet W P k ε,
        (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) := by
  classical
  dsimp only
  let Pswap := P.map Prod.swap
  let J := W.joint P
  let P_Yr := J.map (fun z => z.2.2)
  let P_XrYr := J.map (fun z => (z.1.2, z.2.2))
  let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
  have hδ5 : 0 < δ / 5 := by linarith
  obtain ⟨N₁, hN₁⟩ := aep_typical_prob_tendsto_one Pswap.fst hε hδ5
  obtain ⟨N₂, hN₂⟩ := aep_typical_prob_tendsto_one Pswap hε hδ5
  obtain ⟨N₃, hN₃⟩ := aep_typical_prob_tendsto_one P_Yr hε hδ5
  obtain ⟨N₄, hN₄⟩ := aep_typical_prob_tendsto_one P_XrYr hε hδ5
  obtain ⟨N₅, hN₅⟩ := aep_typical_prob_tendsto_one P_XrXYr hε hδ5
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) N₅, fun k hk => ?_⟩
  let Q : ProbDist ((Fin k → Xr) × (Fin k → X) × (Fin k → Yr)) :=
    { pmf := fun t => (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t)
      nonneg := fun t => (iidDist P_XrXYr k).nonneg _
      sum_one := by
        rw [Fintype.sum_equiv (relayZipEquiv Xr X Yr k) _ (fun z => (iidDist P_XrXYr k).pmf z) (fun _ => rfl)]
        exact (iidDist P_XrXYr k).sum_one }
  have hQ_zip : Q.map (relayZipEquiv Xr X Yr k) = iidDist P_XrXYr k := by
    apply ra_probDist_ext; intro z
    unfold ProbDist.map; dsimp only [Q]
    rw [Finset.sum_eq_single ((relayZipEquiv Xr X Yr k).symm z)]
    · simp
    · intro t _ hne
      have : relayZipEquiv Xr X Yr k t ≠ z := fun h =>
        hne ((relayZipEquiv Xr X Yr k).symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hXrXYr_fst : P_XrXYr.map Prod.fst = Pswap := by
    have hJfst : J.map Prod.fst = P := by rw [ra_probDist_map_fst, dmc_joint_fst]
    calc P_XrXYr.map Prod.fst
      _ = J.map (Prod.swap ∘ Prod.fst) := by dsimp only [P_XrXYr]; rw [map_comp_eq]; rfl
      _ = (J.map Prod.fst).map Prod.swap := (map_comp_eq J Prod.fst Prod.swap).symm
      _ = Pswap := by rw [hJfst]
  have hmap1 : Q.map (fun t => t.1) = iidDist Pswap.fst k := by
    have h : (fun t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr) => t.1) =
        (fun z i => (z i).1.1) ∘ relayZipEquiv Xr X Yr k := rfl
    rw [h, ← map_comp_eq, hQ_zip, ra_iidDist_map_comp P_XrXYr k (fun z => z.1.1)]
    congr 1
    change P_XrXYr.map (Prod.fst ∘ Prod.fst) = Pswap.fst
    rw [← map_comp_eq, hXrXYr_fst, ra_probDist_map_fst]
  have hmap2 : Q.map (fun t i => (t.1 i, t.2.1 i)) = iidDist Pswap k := by
    have h : (fun (t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr)) i => (t.1 i, t.2.1 i)) =
        (fun z i => (z i).1) ∘ relayZipEquiv Xr X Yr k := rfl
    rw [h, ← map_comp_eq, hQ_zip, ra_iidDist_map_comp P_XrXYr k Prod.fst, hXrXYr_fst]
  have hmap3 : Q.map (fun t => t.2.2) = iidDist P_Yr k := by
    have h : (fun t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr) => t.2.2) =
        (fun z i => (z i).2) ∘ relayZipEquiv Xr X Yr k := rfl
    rw [h, ← map_comp_eq, hQ_zip, ra_iidDist_map_comp P_XrXYr k Prod.snd]
    congr 1
    change (J.map (fun z => ((z.1.2, z.1.1), z.2.2))).map Prod.snd = P_Yr
    rw [map_comp_eq]; rfl
  have hmap4 : Q.map (fun t i => (t.1 i, t.2.2 i)) = iidDist P_XrYr k := by
    have h : (fun (t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr)) i => (t.1 i, t.2.2 i)) =
        (fun z i => ((z i).1.1, (z i).2)) ∘ relayZipEquiv Xr X Yr k := rfl
    rw [h, ← map_comp_eq, hQ_zip, ra_iidDist_map_comp P_XrXYr k (fun z => (z.1.1, z.2))]
    congr 1
    change (J.map (fun z => ((z.1.2, z.1.1), z.2.2))).map (fun z => (z.1.1, z.2)) = P_XrYr
    rw [map_comp_eq]; rfl
  let A := relayTypicalSet W P k ε
  have hunion : ∀ t, (if t ∉ A then Q.pmf t else 0) ≤
      (if t.1 ∉ weakTypicalSet Pswap.fst k ε then Q.pmf t else 0) +
      (if (fun i => (t.1 i, t.2.1 i)) ∉ weakTypicalSet Pswap k ε then Q.pmf t else 0) +
      (if t.2.2 ∉ weakTypicalSet P_Yr k ε then Q.pmf t else 0) +
      (if (fun i => (t.1 i, t.2.2 i)) ∉ weakTypicalSet P_XrYr k ε then Q.pmf t else 0) +
      (if relayZipEquiv Xr X Yr k t ∉ weakTypicalSet P_XrXYr k ε then Q.pmf t else 0) := by
    intro t
    have hq0 := Q.nonneg t
    by_cases h1 : t.1 ∈ weakTypicalSet Pswap.fst k ε <;>
    by_cases h2 : (fun i => (t.1 i, t.2.1 i)) ∈ weakTypicalSet Pswap k ε <;>
    by_cases h3 : t.2.2 ∈ weakTypicalSet P_Yr k ε <;>
    by_cases h4 : (fun i => (t.1 i, t.2.2 i)) ∈ weakTypicalSet P_XrYr k ε <;>
    by_cases h5 : relayZipEquiv Xr X Yr k t ∈ weakTypicalSet P_XrXYr k ε
    · have hmem : t ∈ A := (mem_relayTypicalSet W P k ε t).mpr ⟨h1, h2, h3, h4, h5⟩
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
  have hs1 := ra_sum_not_mem_of_map Q (fun t => t.1) (weakTypicalSet Pswap.fst k ε) (iidDist Pswap.fst k) hmap1
  have hs2 := ra_sum_not_mem_of_map Q (fun t i => (t.1 i, t.2.1 i)) (weakTypicalSet Pswap k ε) (iidDist Pswap k) hmap2
  have hs3 := ra_sum_not_mem_of_map Q (fun t => t.2.2) (weakTypicalSet P_Yr k ε) (iidDist P_Yr k) hmap3
  have hs4 := ra_sum_not_mem_of_map Q (fun t i => (t.1 i, t.2.2 i)) (weakTypicalSet P_XrYr k ε) (iidDist P_XrYr k) hmap4
  have hs5 := ra_sum_not_mem_of_map Q (relayZipEquiv Xr X Yr k) (weakTypicalSet P_XrXYr k ε) (iidDist P_XrXYr k) hQ_zip
  rw [hcomp, hs1, hs2, hs3, hs4, hs5] at hsum
  have hp1 := hN₁ k (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hk)
  have hp2 := hN₂ k (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hk)
  have hp3 := hN₃ k (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hk)
  have hp4 := hN₄ k (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hk)
  have hp5 := hN₅ k (le_trans (le_max_right _ _) hk)
  linarith

/-- Packing-lemma bound for the relay's conditional decoding event:
    wrong satellite `X^k(w_prev, w')` given the true cloud center `X_r^k(w_prev)`. -/
private lemma relayTypicalSet_cond_indep_le [Nonempty X]
    (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) (k : ℕ) (ε : ℝ) :
    let Pswap := P.map Prod.swap
    let J := W.joint P
    let P_XrYr := J.map (fun z => (z.1.2, z.2.2))
    ∑ t ∈ relayTypicalSet W P k ε,
      (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) *
        ((raCondChannel Pswap).power k).trans t.1 t.2.1 ≤
      (2 : ℝ) ^ (-((k : ℝ) *
        (condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) - 4 * ε))) := by
  classical
  dsimp only
  let Pswap := P.map Prod.swap
  let J := W.joint P
  let P_XrYr := J.map (fun z => (z.1.2, z.2.2))
  let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
  let A := relayTypicalSet W P k ε
  have hterm : ∀ t ∈ A,
      (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) *
        ((raCondChannel Pswap).power k).trans t.1 t.2.1 ≤
      (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy P_XrYr - ε))) *
      ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap - ε))) /
       (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap.fst + ε)))) := by
    intro t ht
    have hm := (mem_relayTypicalSet W P k ε t).mp ht
    have hxr := hm.1
    have hxrx := hm.2.1
    have hxryr := hm.2.2.2.1
    simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxr hxrx hxryr
    have hxrpos : 0 < (iidDist Pswap.fst k).pmf t.1 :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hxr.1
    rw [raCondChannel_power_eq_div Pswap k t.1 t.2.1 hxrpos.ne']
    have hdiv : (iidDist Pswap k).pmf (fun i => (t.1 i, t.2.1 i)) / (iidDist Pswap.fst k).pmf t.1 ≤
        (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap - ε))) /
        (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap.fst + ε))) :=
      div_le_div₀ (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) hxrx.2
        (Real.rpow_pos_of_pos (by norm_num) _) hxr.1
    exact mul_le_mul hxryr.2 hdiv (div_nonneg ((iidDist Pswap k).nonneg _) hxrpos.le)
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  have hcmi_eq : condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) =
      shannonEntropy Pswap + shannonEntropy P_XrYr - shannonEntropy P_XrXYr - shannonEntropy Pswap.fst := by
    let e : ((Xr × X) × Yr) ≃ (X × Yr × Xr) :=
      { toFun := fun t => (t.1.2, t.2, t.1.1)
        invFun := fun t => ((t.2.2, t.1), t.2.1)
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have hJfst : J.map Prod.fst = P := by rw [ra_probDist_map_fst, dmc_joint_fst]
    have h1 : (J.map (fun z => (z.1.1, z.2.2, z.1.2))).map (fun t => (t.1, t.2.2)) = P := by
      rw [map_comp_eq]
      have hfn : ((fun t : X × Yr × Xr => (t.1, t.2.2)) ∘
          (fun z : (X × Xr) × (Y × Yr) => (z.1.1, z.2.2, z.1.2))) = Prod.fst := by
        funext ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
      rw [hfn, hJfst]
    have h1' : shannonEntropy P = shannonEntropy Pswap := by
      dsimp only [Pswap]; rw [shannonEntropy_swap]
    have h2 : (J.map (fun z => (z.1.1, z.2.2, z.1.2))).map (fun t => (t.2.1, t.2.2)) =
        P_XrYr.map Prod.swap := by
      rw [map_comp_eq, map_comp_eq]; rfl
    have h3 : (J.map (fun z => (z.1.1, z.2.2, z.1.2))).map (fun t => t.2.2) = Pswap.fst := by
      calc (J.map (fun z => (z.1.1, z.2.2, z.1.2))).map (fun t => t.2.2)
        _ = (J.map Prod.fst).map (Prod.fst ∘ Prod.swap) := by rw [map_comp_eq, map_comp_eq]; rfl
        _ = Pswap.fst := by rw [hJfst, ← map_comp_eq, ra_probDist_map_fst]
    have h4 : J.map (fun z => (z.1.1, z.2.2, z.1.2)) = P_XrXYr.map e := by
      rw [map_comp_eq]; rfl
    unfold condMutualInfo; dsimp only
    rw [h1, h1', h2, h3, h4, shannonEntropy_swap P_XrYr, shannonEntropy_map_equiv e]
  calc ∑ t ∈ A, (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) *
          ((raCondChannel Pswap).power k).trans t.1 t.2.1
    _ ≤ ∑ _t ∈ A, ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy P_XrYr - ε))) *
          ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap - ε))) /
           (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap.fst + ε))))) := Finset.sum_le_sum hterm
    _ = (A.card : ℝ) * ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy P_XrYr - ε))) *
          ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap - ε))) /
           (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap.fst + ε))))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ ((k : ℝ) * (shannonEntropy P_XrXYr + ε)) *
          ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy P_XrYr - ε))) *
           ((2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap - ε))) /
            (2 : ℝ) ^ (-((k : ℝ) * (shannonEntropy Pswap.fst + ε))))) :=
        mul_le_mul_of_nonneg_right (relayTypicalSet_card_le W P k ε) (by positivity)
    _ = (2 : ℝ) ^ (-((k : ℝ) *
          (condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) - 4 * ε))) := by
        rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; rw [hcmi_eq]; ring

/-- Single-block relay decoder: given `w_prev` and `yr^k`, outputs the unique `w_curr` such that
    `(X_r^k(w_prev), X^k(w_prev, w_curr), yr^k) ∈ relayTypicalSet W P k ε`, else `0`. -/
private noncomputable def relayBlockDec (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (w_prev : Fin M) (yr : Fin k → Yr) : Fin M := by
  classical
  exact if h : ∃! w_curr : Fin M,
      ((C w_prev).1, (C w_prev).2 w_curr, yr) ∈ relayTypicalSet W P k ε then
    Classical.choose h
  else
    ⟨0, hM⟩

open Classical in
private lemma relayBlockDec_err_indicator_le (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (w_prev w_curr : Fin M) (yr : Fin k → Yr) :
    let A := relayTypicalSet W P k ε
    (if relayBlockDec W P k M hM ε C w_prev yr ≠ w_curr then (1 : ℝ) else 0) ≤
      (if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0) +
      ∑ w' ∈ Finset.univ.erase w_curr,
        (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0) := by
  dsimp only
  let A := relayTypicalSet W P k ε
  have hnn : (0 : ℝ) ≤ ∑ w' ∈ Finset.univ.erase w_curr,
      if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases herr : relayBlockDec W P k M hM ε C w_prev yr ≠ w_curr
  · rw [ite_eq_left herr]
    by_cases hm : ((C w_prev).1, (C w_prev).2 w_curr, yr) ∈ A
    · rw [ite_eq_right (not_not.mpr hm), zero_add]
      have hex : ∃ w' : Fin M, w' ≠ w_curr ∧ ((C w_prev).1, (C w_prev).2 w', yr) ∈ A := by
        by_contra hnone; push Not at hnone
        have huniq : ∃! w : Fin M, ((C w_prev).1, (C w_prev).2 w, yr) ∈ A :=
          ⟨w_curr, hm, fun w hw => by by_contra hne; exact hnone w hne hw⟩
        have hdec : relayBlockDec W P k M hM ε C w_prev yr = w_curr := by
          unfold relayBlockDec
          split_ifs with h'
          · have hspec := Classical.choose_spec h'
            by_contra hne; exact hnone _ hne hspec.1
          · exact absurd huniq h'
        exact herr hdec
      obtain ⟨w', hw', hmem'⟩ := hex
      calc (1 : ℝ) = (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0) := by
            rw [ite_eq_left hmem']
        _ ≤ _ := Finset.single_le_sum
            (f := fun w => if ((C w_prev).1, (C w_prev).2 w, yr) ∈ A then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_erase.mpr ⟨hw', Finset.mem_univ w'⟩)
    · rw [ite_eq_left hm]; linarith
  · rw [ite_eq_right herr]
    have h0 : (0 : ℝ) ≤ if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0 := by
      split_ifs <;> norm_num
    linarith

/-- Single-block relay error probability for a fixed codebook `C` and pair `(w_prev, w_curr)`. -/
private noncomputable def relayBlockErr (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (w_prev w_curr : Fin M) : ℝ :=
  by classical
  exact ∑ yr : Fin k → Yr,
    if relayBlockDec W P k M hM ε C w_prev yr ≠ w_curr then
      ((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr
    else 0

/-- Single-block destination backward decoder: given `w_curr` and `y^k`, outputs the unique `w_prev`
    such that `((X^k(w_prev, w_curr), X_r^k(w_prev)), y^k) ∈ jointTypicalSet ((relayYChannel W).joint P) k ε`. -/
private noncomputable def destBlockDec (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (w_curr : Fin M) (y : Fin k → Y) : Fin M :=
  jointTypicalDec ((relayYChannel W).joint P) k M hM ε
    (fun w_prev i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y

open Classical in
private lemma destBlockDec_err_indicator_le (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (w_prev w_curr : Fin M) (y : Fin k → Y) :
    let A := jointTypicalSet ((relayYChannel W).joint P) k ε
    (if destBlockDec W P k M hM ε C w_curr y ≠ w_prev then (1 : ℝ) else 0) ≤
      (if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0) +
      ∑ w' ∈ Finset.univ.erase w_prev,
        (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0) := by
  dsimp only
  let P_Y := (relayYChannel W).joint P
  let A := jointTypicalSet P_Y k ε
  let encW : Fin M → Fin k → X × Xr := fun w i => ((C w).2 w_curr i, (C w).1 i)
  have hnn : (0 : ℝ) ≤ ∑ w' ∈ Finset.univ.erase w_prev,
      if (encW w', y) ∈ A then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases herr : destBlockDec W P k M hM ε C w_curr y ≠ w_prev
  · rw [ite_eq_left herr]
    by_cases hm : (encW w_prev, y) ∈ A
    · rw [ite_eq_right (not_not.mpr hm), zero_add]
      have hex : ∃ w' : Fin M, w' ≠ w_prev ∧ (encW w', y) ∈ A := by
        by_contra hnone; push Not at hnone
        have huniq : ∃! w : Fin M, (encW w, y) ∈ A :=
          ⟨w_prev, hm, fun w hw => by by_contra hne; exact hnone w hne hw⟩
        have hdec : destBlockDec W P k M hM ε C w_curr y = w_prev := by
          unfold destBlockDec jointTypicalDec
          split_ifs with h'
          · have hspec := Classical.choose_spec h'
            by_contra hne; exact hnone _ hne hspec.1
          · exact absurd huniq h'
        exact herr hdec
      obtain ⟨w', hw', hmem'⟩ := hex
      calc (1 : ℝ) = (if (encW w', y) ∈ A then (1 : ℝ) else 0) := by rw [ite_eq_left hmem']
        _ ≤ _ := Finset.single_le_sum
            (f := fun w => if (encW w, y) ∈ A then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num)
            (Finset.mem_erase.mpr ⟨hw', Finset.mem_univ w'⟩)
    · rw [ite_eq_left hm]; linarith
  · rw [ite_eq_right herr]
    have h0 : (0 : ℝ) ≤ if (encW w_prev, y) ∉ A then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    linarith

/-- Single-block destination backward-decoding error probability for fixed `C` and `(w_prev, w_curr)`. -/
private noncomputable def destBlockErr (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (w_prev w_curr : Fin M) : ℝ :=
  by classical
  exact ∑ y : Fin k → Y,
    if destBlockDec W P k M hM ε C w_curr y ≠ w_prev then
      ((relayYChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y
    else 0

/-- Ensemble probability weight of a superposition relay codebook `C : Fin M → RaCloudCode Xr X k M`. -/
private noncomputable def relayCodeWeight [Nonempty X] (P : ProbDist (X × Xr)) (k M : ℕ)
    (C : Fin M → RaCloudCode Xr X k M) : ℝ :=
  ∏ w : Fin M, (raCloudDist (P.map Prod.swap) k M).pmf (C w)

private lemma relayCodeWeight_nonneg [Nonempty X] (P : ProbDist (X × Xr)) (k M : ℕ)
    (C : Fin M → RaCloudCode Xr X k M) :
    0 ≤ relayCodeWeight P k M C :=
  Finset.prod_nonneg fun _ _ => (raCloudDist (P.map Prod.swap) k M).nonneg _

private lemma relayCodeWeight_sum_one [Nonempty X] (P : ProbDist (X × Xr)) (k M : ℕ) :
    ∑ C : Fin M → RaCloudCode Xr X k M, relayCodeWeight P k M C = 1 := by
  unfold relayCodeWeight
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun _ _ => (raCloudDist (P.map Prod.swap) k M).sum_one

/-- Ensemble expectation bound for `relayBlockErr` (uniform over all `w_prev, w_curr : Fin M`). -/
private lemma expected_relayBlockErr_le [Nonempty X]
    (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (w_prev w_curr : Fin M) :
    let J := W.joint P
    let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
    ∑ C : Fin M → RaCloudCode Xr X k M,
      relayCodeWeight P k M C * relayBlockErr W P k M hM ε C w_prev w_curr ≤
      (1 - ∑ t ∈ relayTypicalSet W P k ε, (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t)) +
      ((M - 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((k : ℝ) *
          (condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) - 4 * ε))) := by
  classical
  dsimp only
  let Pswap := P.map Prod.swap
  let J := W.joint P
  let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
  let P_XrYr := J.map (fun z => (z.1.2, z.2.2))
  let A := relayTypicalSet W P k ε
  let Q := raCloudDist Pswap k M
  -- Step 1: Indicator bound + Fubini swap
  have hstep1 :
      ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C * relayBlockErr W P k M hM ε C w_prev w_curr ≤
      (∑ yr : Fin k → Yr, ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
            (if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0))) +
      ∑ w' ∈ Finset.univ.erase w_curr,
        ∑ yr : Fin k → Yr, ∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0)) := by
    have hpt : ∀ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C * relayBlockErr W P k M hM ε C w_prev w_curr ≤
        (∑ yr : Fin k → Yr, relayCodeWeight P k M C *
          (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
            (if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0))) +
        ∑ w' ∈ Finset.univ.erase w_curr, ∑ yr : Fin k → Yr, relayCodeWeight P k M C *
          (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
            (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0)) := by
      intro C
      unfold relayBlockErr
      rw [Finset.mul_sum]
      have hswap : (∑ w' ∈ Finset.univ.erase w_curr, ∑ yr : Fin k → Yr,
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0))) =
        ∑ yr : Fin k → Yr, ∑ w' ∈ Finset.univ.erase w_curr,
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0)) := Finset.sum_comm
      rw [hswap, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun yr _ => ?_
      have hind := relayBlockDec_err_indicator_le W P k M hM ε C w_prev w_curr yr
      have hcoeff : 0 ≤ relayCodeWeight P k M C *
          ((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr :=
        mul_nonneg (relayCodeWeight_nonneg P k M C) ((relayYrChannel W).power k |>.nonneg _ _)
      have hmul := mul_le_mul_of_nonneg_left hind hcoeff
      have hlhs : relayCodeWeight P k M C *
            (if relayBlockDec W P k M hM ε C w_prev yr ≠ w_curr then
              ((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr
            else 0) =
          (relayCodeWeight P k M C *
            ((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr) *
            (if relayBlockDec W P k M hM ε C w_prev yr ≠ w_curr then (1 : ℝ) else 0) := by
        split_ifs <;> ring
      have hrhs : (relayCodeWeight P k M C *
            ((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr) *
            ((if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0) +
              ∑ w' ∈ Finset.univ.erase w_curr,
                if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0) =
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0)) +
          ∑ w' ∈ Finset.univ.erase w_curr,
            relayCodeWeight P k M C *
              (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
                (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0)) := by
        rw [mul_add, Finset.mul_sum]; congr 1
        · ring
        · exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hlhs, ← hrhs]
      exact hmul
    calc _ ≤ ∑ C, _ := Finset.sum_le_sum fun C _ => hpt C
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_comm
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  -- Step 2: Evaluate Term 1 (true triple not in A)
  have hterm1 :
      (∑ yr : Fin k → Yr, ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
            (if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0))) =
      1 - ∑ t ∈ A, (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) := by
    have hinner : ∀ yr : Fin k → Yr,
        (∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w_curr, yr) ∉ A then (1 : ℝ) else 0))) =
        ∑ xr : Fin k → Xr, ∑ x : Fin k → X,
          if (xr, x, yr) ∉ A then (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k (xr, x, yr)) else 0 := by
      intro yr
      unfold relayCodeWeight
      rw [ra_sum_pi_prod_mul_single Q w_prev
        (fun c => ((relayYrChannel W).power k).trans (fun i => (c.2 w_curr i, c.1 i)) yr *
          (if (c.1, c.2 w_curr, yr) ∉ A then (1 : ℝ) else 0))]
      dsimp only [Q]
      rw [raCloudDist_sum_single_sat Pswap k M w_curr
        (fun xr x => ((relayYrChannel W).power k).trans (fun i => (x i, xr i)) yr *
          (if (xr, x, yr) ∉ A then (1 : ℝ) else 0))]
      refine Finset.sum_congr rfl fun xr _ => Finset.sum_congr rfl fun x _ => ?_
      rw [← mul_assoc, relayIid_XrXYr_pmf]; split_ifs <;> ring
    simp_rw [hinner]
    have hprod : ∑ yr : Fin k → Yr, ∑ xr : Fin k → Xr, ∑ x : Fin k → X,
          (if (xr, x, yr) ∉ A then (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k (xr, x, yr)) else 0) =
        ∑ t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr),
          if t ∉ A then (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) else 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hprod]
    have htot : ∑ t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr),
        (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) = 1 := by
      rw [Fintype.sum_equiv (relayZipEquiv Xr X Yr k) _ (fun z => (iidDist P_XrXYr k).pmf z) (fun _ => rfl)]
      exact (iidDist P_XrXYr k).sum_one
    have hsplit : ∑ t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr),
        (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) =
        (∑ t, if t ∈ A then (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) else 0) +
        (∑ t, if t ∉ A then (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by by_cases h : t ∈ A <;> simp [h]
    have hmem : (∑ t, if t ∈ A then (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) else 0) =
        ∑ t ∈ A, (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t) := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    linarith
  -- Step 3: Evaluate Term 2 (wrong satellite w' ≠ w_curr in same cloud w_prev)
  have hterm2_each : ∀ w' ∈ Finset.univ.erase w_curr,
      (∑ yr : Fin k → Yr, ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
            (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0))) =
      ∑ t ∈ A, (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) *
        ((raCondChannel Pswap).power k).trans t.1 t.2.1 := by
    intro w' hw'
    have hne : w' ≠ w_curr := (Finset.mem_erase.mp hw').1
    have hinner : ∀ yr : Fin k → Yr,
        (∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0))) =
        ∑ xr : Fin k → Xr, ∑ x' : Fin k → X,
          if (xr, x', yr) ∈ A then
            (iidDist P_XrYr k).pmf (fun i => (xr i, yr i)) * ((raCondChannel Pswap).power k).trans xr x'
          else 0 := by
      intro yr
      unfold relayCodeWeight
      rw [ra_sum_pi_prod_mul_single Q w_prev
        (fun c => ((relayYrChannel W).power k).trans (fun i => (c.2 w_curr i, c.1 i)) yr *
          (if (c.1, c.2 w', yr) ∈ A then (1 : ℝ) else 0))]
      dsimp only [Q]
      rw [raCloudDist_sum_pair_sat Pswap k M w_curr w' hne
        (fun xr x => ((relayYrChannel W).power k).trans (fun i => (x i, xr i)) yr)
        (fun xr x' => if (xr, x', yr) ∈ A then (1 : ℝ) else 0)]
      refine Finset.sum_congr rfl fun xr _ => ?_
      rw [relayIid_XrYr_marginal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x' _ => by split_ifs <;> ring
    simp_rw [hinner]
    have hprod : ∑ yr : Fin k → Yr, ∑ xr : Fin k → Xr, ∑ x' : Fin k → X,
          (if (xr, x', yr) ∈ A then
            (iidDist P_XrYr k).pmf (fun i => (xr i, yr i)) * ((raCondChannel Pswap).power k).trans xr x'
          else 0) =
        ∑ t : (Fin k → Xr) × (Fin k → X) × (Fin k → Yr),
          if t ∈ A then
            (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) * ((raCondChannel Pswap).power k).trans t.1 t.2.1
          else 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hprod, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hterm2_sum :
      (∑ w' ∈ Finset.univ.erase w_curr,
        ∑ yr : Fin k → Yr, ∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            (((relayYrChannel W).power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) yr *
              (if ((C w_prev).1, (C w_prev).2 w', yr) ∈ A then (1 : ℝ) else 0))) =
      ((M - 1 : ℕ) : ℝ) *
        (∑ t ∈ A, (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) *
          ((raCondChannel Pswap).power k).trans t.1 t.2.1) := by
    rw [Finset.sum_congr rfl hterm2_each, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ w_curr), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  rw [hterm1, hterm2_sum] at hstep1
  have hpack := relayTypicalSet_cond_indep_le W P k ε
  dsimp only at hpack
  have hmul : ((M - 1 : ℕ) : ℝ) *
        (∑ t ∈ A, (iidDist P_XrYr k).pmf (fun i => (t.1 i, t.2.2 i)) *
          ((raCondChannel Pswap).power k).trans t.1 t.2.1) ≤
      ((M - 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((k : ℝ) *
          (condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) - 4 * ε))) :=
    mul_le_mul_of_nonneg_left hpack (Nat.cast_nonneg _)
  linarith

private lemma relayIid_Pswap_eq_P (P : ProbDist (X × Xr)) (k : ℕ)
    (xr : Fin k → Xr) (x : Fin k → X) :
    (iidDist (P.map Prod.swap) k).pmf (fun i => (xr i, x i)) =
      (iidDist P k).pmf (fun i => (x i, xr i)) := by
  unfold iidDist; dsimp only
  exact Finset.prod_congr rfl fun i _ => relay_Pswap_pmf P (xr i) (x i)

private lemma relay_sum_xr_x_eq_xxr (k : ℕ) (f : (Fin k → X × Xr) → ℝ) :
    ∑ xr : Fin k → Xr, ∑ x : Fin k → X, f (fun i => (x i, xr i)) =
      ∑ xxr : Fin k → X × Xr, f xxr := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (zipEquiv X Xr k) (fun p => f (fun i => (p.1 i, p.2 i))) f (fun _ => rfl)

/-- Ensemble expectation bound for `destBlockErr` (uniform over all `w_prev, w_curr : Fin M`). -/
private lemma expected_destBlockErr_le [Nonempty X]
    (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) (k M : ℕ) (hM : 0 < M) (ε : ℝ)
    (w_prev w_curr : Fin M) :
    let P_Y := (relayYChannel W).joint P
    ∑ C : Fin M → RaCloudCode Xr X k M,
      relayCodeWeight P k M C * destBlockErr W P k M hM ε C w_prev w_curr ≤
      (1 - ∑ xy ∈ jointTypicalSet P_Y k ε, (jointIidDist P_Y k).pmf xy) +
      ((M - 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((k : ℝ) *
          (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) - 3 * ε))) := by
  classical
  dsimp only
  let Pswap := P.map Prod.swap
  let V := relayYChannel W
  let P_Y := V.joint P
  let A := jointTypicalSet P_Y k ε
  let Q := raCloudDist Pswap k M
  -- Step 1: Indicator bound + Fubini swap
  have hstep1 :
      ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C * destBlockErr W P k M hM ε C w_prev w_curr ≤
      (∑ y : Fin k → Y, ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
            (if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0))) +
      ∑ w' ∈ Finset.univ.erase w_prev,
        ∑ y : Fin k → Y, ∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0)) := by
    have hpt : ∀ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C * destBlockErr W P k M hM ε C w_prev w_curr ≤
        (∑ y : Fin k → Y, relayCodeWeight P k M C *
          ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
            (if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0))) +
        ∑ w' ∈ Finset.univ.erase w_prev, ∑ y : Fin k → Y, relayCodeWeight P k M C *
          ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
            (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0)) := by
      intro C
      unfold destBlockErr
      rw [Finset.mul_sum]
      have hswap : (∑ w' ∈ Finset.univ.erase w_prev, ∑ y : Fin k → Y,
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0))) =
        ∑ y : Fin k → Y, ∑ w' ∈ Finset.univ.erase w_prev,
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0)) :=
        Finset.sum_comm
      rw [hswap, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ => ?_
      have hind := destBlockDec_err_indicator_le W P k M hM ε C w_prev w_curr y
      have hcoeff : 0 ≤ relayCodeWeight P k M C *
          (V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y :=
        mul_nonneg (relayCodeWeight_nonneg P k M C) ((V.power k).nonneg _ _)
      have hmul := mul_le_mul_of_nonneg_left hind hcoeff
      have hlhs : relayCodeWeight P k M C *
            (if destBlockDec W P k M hM ε C w_curr y ≠ w_prev then
              (V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y
            else 0) =
          (relayCodeWeight P k M C *
            (V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y) *
            (if destBlockDec W P k M hM ε C w_curr y ≠ w_prev then (1 : ℝ) else 0) := by
        split_ifs <;> ring
      have hrhs : (relayCodeWeight P k M C *
            (V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y) *
            ((if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0) +
              ∑ w' ∈ Finset.univ.erase w_prev,
                if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0) =
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0)) +
          ∑ w' ∈ Finset.univ.erase w_prev,
            relayCodeWeight P k M C *
              ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
                (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0)) := by
        rw [mul_add, Finset.mul_sum]; congr 1
        · ring
        · exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hlhs, ← hrhs]
      exact hmul
    calc _ ≤ ∑ C, _ := Finset.sum_le_sum fun C _ => hpt C
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_comm
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  -- Helper identity for `jointIidDist P_Y k`
  have hjoint_pmf : ∀ (xxr : Fin k → X × Xr) (y : Fin k → Y),
      (iidDist P k).pmf xxr * (V.power k).trans xxr y = (jointIidDist P_Y k).pmf (xxr, y) := by
    intro xxr y
    unfold iidDist DMC.power jointIidDist P_Y DMC.joint; dsimp only
    rw [← Finset.prod_mul_distrib]
  -- Step 2: Evaluate Term 1 (true pair not in A)
  have hterm1 :
      (∑ y : Fin k → Y, ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
            (if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0))) =
      1 - ∑ xy ∈ A, (jointIidDist P_Y k).pmf xy := by
    have hinner : ∀ y : Fin k → Y,
        (∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)), y) ∉ A then (1 : ℝ) else 0))) =
        ∑ xxr : Fin k → X × Xr, if (xxr, y) ∉ A then (jointIidDist P_Y k).pmf (xxr, y) else 0 := by
      intro y
      unfold relayCodeWeight
      rw [ra_sum_pi_prod_mul_single Q w_prev
        (fun c => (V.power k).trans (fun i => (c.2 w_curr i, c.1 i)) y *
          (if ((fun i => (c.2 w_curr i, c.1 i)), y) ∉ A then (1 : ℝ) else 0))]
      dsimp only [Q]
      rw [raCloudDist_sum_single_sat Pswap k M w_curr
        (fun xr x => (V.power k).trans (fun i => (x i, xr i)) y *
          (if ((fun i => (x i, xr i)), y) ∉ A then (1 : ℝ) else 0))]
      dsimp only [Pswap]
      simp_rw [relayIid_Pswap_eq_P]
      rw [relay_sum_xr_x_eq_xxr k (fun xxr => (iidDist P k).pmf xxr *
        ((V.power k).trans xxr y * (if (xxr, y) ∉ A then (1 : ℝ) else 0)))]
      refine Finset.sum_congr rfl fun xxr _ => ?_
      rw [← mul_assoc, hjoint_pmf]; split_ifs <;> ring
    simp_rw [hinner]
    rw [← Fintype.sum_prod_type_right
      (fun xy : (Fin k → X × Xr) × (Fin k → Y) => if xy ∉ A then (jointIidDist P_Y k).pmf xy else 0)]
    have hsplit : ∑ xy : (Fin k → X × Xr) × (Fin k → Y), (jointIidDist P_Y k).pmf xy =
        (∑ xy, if xy ∈ A then (jointIidDist P_Y k).pmf xy else 0) +
        (∑ xy, if xy ∉ A then (jointIidDist P_Y k).pmf xy else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun xy _ => by by_cases h : xy ∈ A <;> simp [h]
    rw [(jointIidDist P_Y k).sum_one] at hsplit
    have hmem : (∑ xy, if xy ∈ A then (jointIidDist P_Y k).pmf xy else 0) =
        ∑ xy ∈ A, (jointIidDist P_Y k).pmf xy := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    linarith
  -- Step 3: Evaluate Term 2 (wrong cloud w' ≠ w_prev)
  have hterm2_each : ∀ w' ∈ Finset.univ.erase w_prev,
      (∑ y : Fin k → Y, ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
            (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0))) =
      ∑ xy ∈ A, ((iidDist P_Y.fst k).prod (iidDist P_Y.snd k)).pmf xy := by
    intro w' hw'
    have hne : w' ≠ w_prev := (Finset.mem_erase.mp hw').1
    have hfst : P_Y.fst = P := dmc_joint_fst V P
    have hinner : ∀ y : Fin k → Y,
        (∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0))) =
        ∑ xxr' : Fin k → X × Xr,
          if (xxr', y) ∈ A then ((iidDist P_Y.fst k).prod (iidDist P_Y.snd k)).pmf (xxr', y) else 0 := by
      intro y
      unfold relayCodeWeight
      rw [ra_sum_pi_prod_mul_pair Q w_prev w' hne
        (fun c => (V.power k).trans (fun i => (c.2 w_curr i, c.1 i)) y)
        (fun c' => if ((fun i => (c'.2 w_curr i, c'.1 i)), y) ∈ A then (1 : ℝ) else 0)]
      dsimp only [Q]
      rw [raCloudDist_sum_single_sat Pswap k M w_curr
            (fun xr x => (V.power k).trans (fun i => (x i, xr i)) y),
          raCloudDist_sum_single_sat Pswap k M w_curr
            (fun xr' x' => if ((fun i => (x' i, xr' i)), y) ∈ A then (1 : ℝ) else 0)]
      dsimp only [Pswap]
      simp_rw [relayIid_Pswap_eq_P]
      rw [relay_sum_xr_x_eq_xxr k (fun xxr => (iidDist P k).pmf xxr * (V.power k).trans xxr y),
          relay_sum_xr_x_eq_xxr k (fun xxr' => (iidDist P k).pmf xxr' * (if (xxr', y) ∈ A then (1 : ℝ) else 0))]
      have hy_marg : ∑ xxr : Fin k → X × Xr, (iidDist P k).pmf xxr * (V.power k).trans xxr y =
          (iidDist P_Y.snd k).pmf y := by
        simp_rw [hjoint_pmf]
        change (jointIidDist P_Y k).snd.pmf y = _
        rw [jointIidDist_snd]
      rw [hy_marg, Finset.mul_sum]
      refine Finset.sum_congr rfl fun xxr' _ => ?_
      unfold ProbDist.prod; dsimp only; rw [hfst]; split_ifs <;> ring
    simp_rw [hinner]
    rw [← Fintype.sum_prod_type_right
      (fun xy : (Fin k → X × Xr) × (Fin k → Y) =>
        if xy ∈ A then ((iidDist P_Y.fst k).prod (iidDist P_Y.snd k)).pmf xy else 0),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hterm2_sum :
      (∑ w' ∈ Finset.univ.erase w_prev,
        ∑ y : Fin k → Y, ∑ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C *
            ((V.power k).trans (fun i => ((C w_prev).2 w_curr i, (C w_prev).1 i)) y *
              (if ((fun i => ((C w').2 w_curr i, (C w').1 i)), y) ∈ A then (1 : ℝ) else 0))) =
      ((M - 1 : ℕ) : ℝ) *
        (∑ xy ∈ A, ((iidDist P_Y.fst k).prod (iidDist P_Y.snd k)).pmf xy) := by
    rw [Finset.sum_congr rfl hterm2_each, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ w_prev), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
  rw [hterm1, hterm2_sum] at hstep1
  have hpack := jointTypicalSet_indep_prob_le P_Y k ε
  have hmi_eq : mutualInfo P_Y = mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) := by
    dsimp only [P_Y, V]; rw [relayYChannel_joint_eq']
  rw [hmi_eq] at hpack
  have hmul : ((M - 1 : ℕ) : ℝ) *
        (∑ xy ∈ A, ((iidDist P_Y.fst k).prod (iidDist P_Y.snd k)).pmf xy) ≤
      ((M - 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((k : ℝ) *
          (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) - 3 * ε))) :=
    mul_le_mul_of_nonneg_left hpack (Nat.cast_nonneg _)
  linarith

end SingleBlockRandomCoding

/-! ### 3. Block-Markov Superposition Coding, Deterministic Decomposition & Padding -/

section BlockMarkov

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- Extended message sequence for `B` blocks carrying `B - 1` messages `μ : Fin (B - 1) → Fin M`,
    padded with dummy message `0` at positions `0` and `B`. -/
private def bmExtMsg (B M : ℕ) (hM : 0 < M) (μ : Fin (B - 1) → Fin M) (t : ℕ) : Fin M :=
  if h : 1 ≤ t ∧ t ≤ B - 1 then μ ⟨t - 1, by omega⟩ else ⟨0, hM⟩

private def bmPrevMsg (B M : ℕ) (hM : 0 < M) (μ : Fin (B - 1) → Fin M) (b : Fin B) : Fin M :=
  bmExtMsg B M hM μ b.1

private def bmCurrMsg (B M : ℕ) (hM : 0 < M) (μ : Fin (B - 1) → Fin M) (b : Fin B) : Fin M :=
  bmExtMsg B M hM μ (b.1 + 1)

private lemma bmPrevMsg_zero (B M : ℕ) (hB : 0 < B) (hM : 0 < M) (μ : Fin (B - 1) → Fin M) :
    bmPrevMsg B M hM μ ⟨0, hB⟩ = ⟨0, hM⟩ := by
  simp [bmPrevMsg, bmExtMsg]

private lemma bmCurrMsg_last (B M : ℕ) (hB : 0 < B) (hM : 0 < M) (μ : Fin (B - 1) → Fin M) :
    bmCurrMsg B M hM μ ⟨B - 1, by omega⟩ = ⟨0, hM⟩ := by
  simp [bmCurrMsg, bmExtMsg]

private lemma bmPrevMsg_succ_eq_currMsg (B M : ℕ) (hM : 0 < M) (μ : Fin (B - 1) → Fin M)
    (b : Fin B) (hb : b.1 + 1 < B) :
    bmPrevMsg B M hM μ ⟨b.1 + 1, hb⟩ = bmCurrMsg B M hM μ b := rfl

private lemma bmPrevMsg_succ_eq_msg (B M : ℕ) (hM : 0 < M) (μ : Fin (B - 1) → Fin M)
    (r : Fin (B - 1)) :
    bmPrevMsg B M hM μ ⟨r.1 + 1, by omega⟩ = μ r := by
  unfold bmPrevMsg bmExtMsg
  have hcond : 1 ≤ r.1 + 1 ∧ r.1 + 1 ≤ B - 1 := by omega
  simp only [hcond, and_self, ↓reduceDIte]
  congr 1

/-- Relay's causal recursive estimate of `prevMsg` at the start of block `b`, given any
    block-indexed sequence `yr : Fin t → Fin k → Yr` (using only blocks `< b`). -/
private noncomputable def bmRelayState (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    {t : ℕ} (yr : Fin t → Fin k → Yr) : ℕ → Fin M
  | 0 => ⟨0, hM⟩
  | b + 1 =>
    if h : b < t then
      relayBlockDec W P k M hM ε C (bmRelayState W P k M hM ε C yr b) (yr ⟨b, h⟩)
    else
      ⟨0, hM⟩

private lemma bmRelayState_congr (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    {t₁ t₂ : ℕ} (yr₁ : Fin t₁ → Fin k → Yr) (yr₂ : Fin t₂ → Fin k → Yr)
    (b : ℕ) (ht₁ : b ≤ t₁) (ht₂ : b ≤ t₂)
    (heq : ∀ (j : ℕ) (hj₁ : j < t₁) (hj₂ : j < t₂), j < b → yr₁ ⟨j, hj₁⟩ = yr₂ ⟨j, hj₂⟩) :
    bmRelayState W P k M hM ε C yr₁ b = bmRelayState W P k M hM ε C yr₂ b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hb₁ : b < t₁ := by omega
    have hb₂ : b < t₂ := by omega
    simp only [bmRelayState, hb₁, hb₂, ↓reduceDIte]
    rw [ih (by omega) (by omega) (fun j hj₁ hj₂ hlt => heq j hj₁ hj₂ (by omega)),
        heq b hb₁ hb₂ (Nat.lt_succ_self b)]

/-- Strictly causal relay state computed from a prefix history `hist : Fin i.1 → Yr`
    for any block `b` with `b * k ≤ i.1`. -/
private noncomputable def bmRelayStateFromHist (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (i : Fin (B * k)) (hist : Fin i.1 → Yr) : (b : ℕ) → b * k ≤ i.1 → Fin M
  | 0, _ => ⟨0, hM⟩
  | b + 1, hb =>
    relayBlockDec W P k M hM ε C
      (bmRelayStateFromHist W P B k M hM ε C i hist b (by nlinarith))
      (fun j : Fin k => hist ⟨b * k + j.1, by nlinarith [j.2]⟩)

private lemma bmRelayStateFromHist_eq (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hk : 0 < k) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (yr : Fin (B * k) → Yr) (i : Fin (B * k)) (b : ℕ) (hb : b * k ≤ i.1) :
    bmRelayStateFromHist W P B k M hM ε C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩) b hb =
      bmRelayState W P k M hM ε C (raUnblockEquiv Yr B k hk yr) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hbB : b < B := by
      have h1 : (b + 1) * k ≤ B * k := le_trans hb (le_of_lt i.2)
      have h2 : b + 1 ≤ B := Nat.le_of_mul_le_mul_right h1 hk
      omega
    simp only [bmRelayStateFromHist, bmRelayState, hbB, ↓reduceDIte]
    rw [ih (by nlinarith)]
    congr 1

/-- Destination backward decoder state `bmDestStateAux d` computes the estimate of `prevMsg` at
    block `B - 1 - d`, recursing from `d = 0` (last block `B - 1`) upward. -/
private noncomputable def bmDestStateAux (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hB : 0 < B) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (y : Fin B → Fin k → Y) : ℕ → Fin M
  | 0 => destBlockDec W P k M hM ε C ⟨0, hM⟩ (y ⟨B - 1, by omega⟩)
  | d + 1 =>
    if h : d + 1 < B then
      destBlockDec W P k M hM ε C
        (bmDestStateAux W P B k M hB hM ε C y d)
        (y ⟨B - 1 - (d + 1), by omega⟩)
    else
      ⟨0, hM⟩

private noncomputable def bmDestState (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hB : 0 < B) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (y : Fin B → Fin k → Y) (b : Fin B) : Fin M :=
  bmDestStateAux W P B k M hB hM ε C y (B - 1 - b.1)

private noncomputable def bmDecTuple (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hB : 0 < B) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (y : Fin B → Fin k → Y) : Fin (B - 1) → Fin M :=
  fun r => bmDestState W P B k M hB hM ε C y ⟨r.1 + 1, by omega⟩

private lemma bmDestState_last (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hB : 0 < B) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (y : Fin B → Fin k → Y) :
    bmDestState W P B k M hB hM ε C y ⟨B - 1, by omega⟩ =
      destBlockDec W P k M hM ε C ⟨0, hM⟩ (y ⟨B - 1, by omega⟩) := by
  unfold bmDestState
  have h0 : B - 1 - (B - 1) = 0 := Nat.sub_self _
  rw [h0]
  rfl

private lemma bmDestState_step (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hB : 0 < B) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (y : Fin B → Fin k → Y) (b : Fin B) (hb : b.1 + 1 < B) :
    bmDestState W P B k M hB hM ε C y b =
      destBlockDec W P k M hM ε C
        (bmDestState W P B k M hB hM ε C y ⟨b.1 + 1, hb⟩) (y b) := by
  unfold bmDestState
  have hstep : B - 1 - b.1 = (B - 1 - (b.1 + 1)) + 1 := by omega
  have hlt : (B - 1 - (b.1 + 1)) + 1 < B := by omega
  rw [hstep]
  simp only [bmDestStateAux, hlt, ↓reduceDIte]
  congr 2
  ext; dsimp only; omega

/-- Prefix block-Markov channel transition probability over the first `t ≤ B` blocks. -/
private noncomputable def bmPrefixTrans (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (μ : Fin (B - 1) → Fin M) {t : ℕ} (ht : t ≤ B)
    (y : Fin t → Fin k → Y) (yr : Fin t → Fin k → Yr) : ℝ :=
  ∏ b : Fin t,
    (W.power k).trans
      (fun j => ((C (bmPrevMsg B M hM μ ⟨b.1, lt_of_lt_of_le b.2 ht⟩)).2
                    (bmCurrMsg B M hM μ ⟨b.1, lt_of_lt_of_le b.2 ht⟩) j,
                 (C (bmRelayState W P k M hM ε C yr b.1)).1 j))
      (fun j => (y b j, yr b j))

private lemma bmPrefixTrans_nonneg (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (μ : Fin (B - 1) → Fin M) {t : ℕ} (ht : t ≤ B)
    (y : Fin t → Fin k → Y) (yr : Fin t → Fin k → Yr) :
    0 ≤ bmPrefixTrans W P B k M hM ε C μ ht y yr :=
  Finset.prod_nonneg fun _ _ => (W.power k).nonneg _ _

/-- One-step causal marginalization: summing out the last block `t` of `bmPrefixTrans` at `t + 1`
    against any function of the prefix `Fin t` leaves `bmPrefixTrans` at `t`. -/
private lemma bmPrefixTrans_sum_snoc (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (μ : Fin (B - 1) → Fin M) {t : ℕ} (ht : t + 1 ≤ B)
    (f : (Fin t → Fin k → Y) → (Fin t → Fin k → Yr) → ℝ) :
    ∑ yr : Fin (t + 1) → Fin k → Yr, ∑ y : Fin (t + 1) → Fin k → Y,
      bmPrefixTrans W P B k M hM ε C μ ht y yr *
        f (fun b => y b.castSucc) (fun b => yr b.castSucc) =
    ∑ yr : Fin t → Fin k → Yr, ∑ y : Fin t → Fin k → Y,
      bmPrefixTrans W P B k M hM ε C μ (Nat.le_of_succ_le ht) y yr * f y yr := by
  have hsnoc : ∀ (y_init : Fin t → Fin k → Y) (y_last : Fin k → Y)
      (yr_init : Fin t → Fin k → Yr) (yr_last : Fin k → Yr),
      bmPrefixTrans W P B k M hM ε C μ ht (raSnocVec y_init y_last) (raSnocVec yr_init yr_last) =
        bmPrefixTrans W P B k M hM ε C μ (Nat.le_of_succ_le ht) y_init yr_init *
          (W.power k).trans
            (fun j => ((C (bmPrevMsg B M hM μ ⟨t, ht⟩)).2 (bmCurrMsg B M hM μ ⟨t, ht⟩) j,
                       (C (bmRelayState W P k M hM ε C yr_init t)).1 j))
            (fun j => (y_last j, yr_last j)) := by
    intro y_init y_last yr_init yr_last
    unfold bmPrefixTrans
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun b _ => ?_
      have hst : bmRelayState W P k M hM ε C (raSnocVec yr_init yr_last) b.1 =
          bmRelayState W P k M hM ε C yr_init b.1 :=
        bmRelayState_congr W P k M hM ε C _ _ b.1 (by omega) (by omega)
          fun j hj₁ hj₂ hlt => by
            have hidx : (⟨j, hj₁⟩ : Fin (t + 1)) = (⟨j, hj₂⟩ : Fin t).castSucc := Fin.ext rfl
            rw [hidx, raSnocVec, Fin.snoc_castSucc]
      simp only [Fin.val_castSucc, hst, raSnocVec, Fin.snoc_castSucc]
    · have hst : bmRelayState W P k M hM ε C (raSnocVec yr_init yr_last) t =
          bmRelayState W P k M hM ε C yr_init t :=
        bmRelayState_congr W P k M hM ε C _ _ t (by omega) le_rfl
          fun j hj₁ hj₂ hlt => by
            have hidx : (⟨j, hj₁⟩ : Fin (t + 1)) = (⟨j, hj₂⟩ : Fin t).castSucc := Fin.ext rfl
            rw [hidx, raSnocVec, Fin.snoc_castSucc]
      simp only [Fin.val_last, hst, raSnocVec, Fin.snoc_last]
  have hreidx_yr := Fintype.sum_equiv (raPiSnocEquiv (Fin k → Yr) t).symm
    (fun p : (Fin t → Fin k → Yr) × (Fin k → Yr) =>
      ∑ y : Fin (t + 1) → Fin k → Y,
        bmPrefixTrans W P B k M hM ε C μ ht y (raSnocVec p.1 p.2) *
          f (fun b => y b.castSucc) (fun b => (raSnocVec p.1 p.2) b.castSucc))
    (fun yr : Fin (t + 1) → Fin k → Yr =>
      ∑ y : Fin (t + 1) → Fin k → Y,
        bmPrefixTrans W P B k M hM ε C μ ht y yr *
          f (fun b => y b.castSucc) (fun b => yr b.castSucc))
    (fun _ => rfl)
  rw [← hreidx_yr, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun yr_init _ => ?_
  have hinner : ∀ yr_last : Fin k → Yr,
      (∑ y : Fin (t + 1) → Fin k → Y,
        bmPrefixTrans W P B k M hM ε C μ ht y (raSnocVec yr_init yr_last) *
          f (fun b => y b.castSucc) (fun b => (raSnocVec yr_init yr_last) b.castSucc)) =
      ∑ y_init : Fin t → Fin k → Y, ∑ y_last : Fin k → Y,
        (bmPrefixTrans W P B k M hM ε C μ (Nat.le_of_succ_le ht) y_init yr_init * f y_init yr_init) *
          (W.power k).trans
            (fun j => ((C (bmPrevMsg B M hM μ ⟨t, ht⟩)).2 (bmCurrMsg B M hM μ ⟨t, ht⟩) j,
                       (C (bmRelayState W P k M hM ε C yr_init t)).1 j))
            (fun j => (y_last j, yr_last j)) := by
    intro yr_last
    have hreidx_y := Fintype.sum_equiv (raPiSnocEquiv (Fin k → Y) t).symm
      (fun q : (Fin t → Fin k → Y) × (Fin k → Y) =>
        bmPrefixTrans W P B k M hM ε C μ ht (raSnocVec q.1 q.2) (raSnocVec yr_init yr_last) *
          f (fun b => (raSnocVec q.1 q.2) b.castSucc) (fun b => (raSnocVec yr_init yr_last) b.castSucc))
      (fun y : Fin (t + 1) → Fin k → Y =>
        bmPrefixTrans W P B k M hM ε C μ ht y (raSnocVec yr_init yr_last) *
          f (fun b => y b.castSucc) (fun b => (raSnocVec yr_init yr_last) b.castSucc))
      (fun _ => rfl)
    rw [← hreidx_y, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y_init _ => Finset.sum_congr rfl fun y_last _ => ?_
    rw [hsnoc]
    simp only [raSnocVec, Fin.snoc_castSucc]
    ring
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y_init _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum1 : ∑ y_last : Fin k → Y, ∑ yr_last : Fin k → Yr,
      (W.power k).trans
        (fun j => ((C (bmPrevMsg B M hM μ ⟨t, ht⟩)).2 (bmCurrMsg B M hM μ ⟨t, ht⟩) j,
                   (C (bmRelayState W P k M hM ε C yr_init t)).1 j))
        (fun j => (y_last j, yr_last j)) = 1 := by
    rw [← Fintype.sum_prod_type']
    have hzip := Fintype.sum_equiv (zipEquiv Y Yr k)
      (fun p : (Fin k → Y) × (Fin k → Yr) =>
        (W.power k).trans
          (fun j => ((C (bmPrevMsg B M hM μ ⟨t, ht⟩)).2 (bmCurrMsg B M hM μ ⟨t, ht⟩) j,
                     (C (bmRelayState W P k M hM ε C yr_init t)).1 j))
          (fun j => (p.1 j, p.2 j)))
      (fun w : Fin k → Y × Yr =>
        (W.power k).trans
          (fun j => ((C (bmPrevMsg B M hM μ ⟨t, ht⟩)).2 (bmCurrMsg B M hM μ ⟨t, ht⟩) j,
                     (C (bmRelayState W P k M hM ε C yr_init t)).1 j)) w)
      (fun _ => rfl)
    exact hzip.trans ((W.power k).sum_one _)
  rw [hsum1, mul_one]

/-- Multi-step causal marginalization: summing out blocks `t, t + 1, …, s - 1` (`t ≤ s ≤ B`)
    against any function of the first `t` blocks. -/
private lemma bmPrefixTrans_sum_prefix (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hM : 0 < M) (ε : ℝ) (C : Fin M → RaCloudCode Xr X k M)
    (μ : Fin (B - 1) → Fin M) {t s : ℕ} (hts : t ≤ s) (hs : s ≤ B)
    (f : (Fin t → Fin k → Y) → (Fin t → Fin k → Yr) → ℝ) :
    ∑ yr : Fin s → Fin k → Yr, ∑ y : Fin s → Fin k → Y,
      bmPrefixTrans W P B k M hM ε C μ hs y yr *
        f (fun b => y ⟨b.1, lt_of_lt_of_le b.2 hts⟩) (fun b => yr ⟨b.1, lt_of_lt_of_le b.2 hts⟩) =
    ∑ yr : Fin t → Fin k → Yr, ∑ y : Fin t → Fin k → Y,
      bmPrefixTrans W P B k M hM ε C μ (le_trans hts hs) y yr * f y yr := by
  induction s with
  | zero =>
    have ht0 : t = 0 := Nat.le_zero.mp hts
    subst ht0; rfl
  | succ s ih =>
    by_cases heq : t = s + 1
    · subst heq; rfl
    · have hts' : t ≤ s := by omega
      let g : (Fin s → Fin k → Y) → (Fin s → Fin k → Yr) → ℝ :=
        fun y yr => f (fun b => y ⟨b.1, lt_of_lt_of_le b.2 hts'⟩)
                      (fun b => yr ⟨b.1, lt_of_lt_of_le b.2 hts'⟩)
      have hstep := bmPrefixTrans_sum_snoc W P B k M hM ε C μ hs g
      dsimp only [g] at hstep
      exact hstep.trans (ih hts' (Nat.le_of_succ_le hs))

/-- Summing a pure product of `t` memoryless block transitions with a predicate on a single block
    `b₀ : Fin t` collapses all other blocks to `1` and leaves block `b₀`. -/
private lemma prod_block_trans_single (W : RelayChannel X Xr Y Yr) (k t : ℕ)
    (u : Fin t → Fin k → X × Xr) (b₀ : Fin t)
    (g : (Fin k → Y) → (Fin k → Yr) → ℝ) :
    ∑ yr : Fin t → Fin k → Yr, ∑ y : Fin t → Fin k → Y,
      (∏ b : Fin t, (W.power k).trans (u b) (fun j => (y b j, yr b j))) * g (y b₀) (yr b₀) =
    ∑ yr₀ : Fin k → Yr, ∑ y₀ : Fin k → Y,
      (W.power k).trans (u b₀) (fun j => (y₀ j, yr₀ j)) * g y₀ yr₀ := by
  let Q : Fin t → ProbDist ((Fin k → Y) × (Fin k → Yr)) := fun b =>
    { pmf := fun p => (W.power k).trans (u b) (fun j => (p.1 j, p.2 j))
      nonneg := fun p => (W.power k).nonneg _ _
      sum_one :=
        (Fintype.sum_equiv (zipEquiv Y Yr k)
          (fun p : (Fin k → Y) × (Fin k → Yr) => (W.power k).trans (u b) (fun j => (p.1 j, p.2 j)))
          (fun w : Fin k → Y × Yr => (W.power k).trans (u b) w)
          (fun _ => rfl)).trans ((W.power k).sum_one _) }
  let e : ((Fin t → Fin k → Y) × (Fin t → Fin k → Yr)) ≃
      (Fin t → (Fin k → Y) × (Fin k → Yr)) :=
    { toFun := fun p b => (p.1 b, p.2 b)
      invFun := fun h => (fun b => (h b).1, fun b => (h b).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  trans (∑ h : Fin t → (Fin k → Y) × (Fin k → Yr),
    (∏ b : Fin t, (Q b).pmf (h b)) * g (h b₀).1 (h b₀).2)
  · exact Fintype.sum_equiv e
      (fun x : (Fin t → Fin k → Y) × (Fin t → Fin k → Yr) =>
        (∏ b : Fin t, (W.power k).trans (u b) (fun j => (x.1 b j, x.2 b j))) * g (x.1 b₀) (x.2 b₀))
      (fun h : Fin t → (Fin k → Y) × (Fin k → Yr) =>
        (∏ b : Fin t, (Q b).pmf (h b)) * g (h b₀).1 (h b₀).2)
      (fun _ => rfl)
  let F : Fin t → ((Fin k → Y) × (Fin k → Yr)) → ℝ := fun b p =>
    if b = b₀ then (Q b).pmf p * g p.1 p.2 else (Q b).pmf p
  have hfun : ∀ h : Fin t → (Fin k → Y) × (Fin k → Yr),
      (∏ b : Fin t, (Q b).pmf (h b)) * g (h b₀).1 (h b₀).2 = ∏ b : Fin t, F b (h b) := by
    intro h
    rw [← Finset.mul_prod_erase Finset.univ (fun b => (Q b).pmf (h b)) (Finset.mem_univ b₀),
        ← Finset.mul_prod_erase Finset.univ (fun b => F b (h b)) (Finset.mem_univ b₀)]
    have hrest : ∏ b ∈ Finset.univ.erase b₀, F b (h b) =
        ∏ b ∈ Finset.univ.erase b₀, (Q b).pmf (h b) :=
      Finset.prod_congr rfl fun b hb => by simp [F, (Finset.mem_erase.mp hb).1]
    rw [hrest]; simp only [F, ↓reduceIte]; ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun b => ∑ p, F b p) (Finset.mem_univ b₀)]
  have hrest : ∏ b ∈ Finset.univ.erase b₀, ∑ p, F b p = 1 :=
    Finset.prod_eq_one fun b hb => by
      simp only [F, (Finset.mem_erase.mp hb).1, ↓reduceIte]; exact (Q b).sum_one
  rw [hrest, mul_one]
  simp only [F, ↓reduceIte, Q]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

private lemma relayYrChannel_power_trans (W : RelayChannel X Xr Y Yr) (k : ℕ)
    (u : Fin k → X × Xr) (yr : Fin k → Yr) :
    ((relayYrChannel W).power k).trans u yr =
      ∑ y : Fin k → Y, (W.power k).trans u (fun j => (y j, yr j)) := by
  simp only [DMC.power, relayYrChannel]
  exact Fintype.prod_sum (fun j y => W.trans (u j) (y, yr j))

private lemma relayYChannel_power_trans (W : RelayChannel X Xr Y Yr) (k : ℕ)
    (u : Fin k → X × Xr) (y : Fin k → Y) :
    ((relayYChannel W).power k).trans u y =
      ∑ yr : Fin k → Yr, (W.power k).trans u (fun j => (y j, yr j)) := by
  simp only [DMC.power, relayYChannel]
  exact Fintype.prod_sum (fun j yr => W.trans (u j) (y j, yr))

/-- **Deterministic Block-Markov Error Decomposition**:
    for ANY fixed codebook `C` and ANY message tuple `μ : Fin (B - 1) → Fin M`, the full
    block-Markov decoding error probability is bounded above by the sum of the `B - 1` single-block
    relay errors plus the `B - 1` single-block destination backward-decoding errors. -/
private lemma bm_error_le_sum_block_errors (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M : ℕ) (hB : 2 ≤ B) (hM : 0 < M) (ε : ℝ)
    (C : Fin M → RaCloudCode Xr X k M) (μ : Fin (B - 1) → Fin M) :
    by classical
    exact ∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
      (if bmDecTuple W P B k M (by omega) hM ε C y ≠ μ then
        bmPrefixTrans W P B k M hM ε C μ le_rfl y yr
      else 0) ≤
    (∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
      relayBlockErr W P k M hM ε C (bmPrevMsg B M hM μ b) (bmCurrMsg B M hM μ b)) +
    (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
      destBlockErr W P k M hM ε C (bmPrevMsg B M hM μ b) (bmCurrMsg B M hM μ b)) := by
  classical
  have hBpos : 0 < B := by omega
  let GoodUpTo : ℕ → (Fin B → Fin k → Yr) → Prop := fun b₀ yr =>
    ∀ j : Fin B, j.1 ≤ b₀ → bmRelayState W P k M hM ε C yr j.1 = bmPrevMsg B M hM μ j
  let GoodAll : (Fin B → Fin k → Yr) → Prop := fun yr =>
    ∀ j : Fin B, bmRelayState W P k M hM ε C yr j.1 = bmPrevMsg B M hM μ j
  -- Step 1: Pointwise deterministic indicator inequality
  have hind : ∀ (y : Fin B → Fin k → Y) (yr : Fin B → Fin k → Yr),
      (if bmDecTuple W P B k M hBpos hM ε C y ≠ μ then (1 : ℝ) else 0) ≤
      (∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
        if GoodUpTo b.1 yr ∧
            relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
        then (1 : ℝ) else 0) +
      (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
        if GoodAll yr ∧
            destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
        then (1 : ℝ) else 0) := by
    intro y yr
    have hnn1 : (0 : ℝ) ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
        if GoodUpTo b.1 yr ∧
            relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
        then (1 : ℝ) else 0 := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hnn2 : (0 : ℝ) ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
        if GoodAll yr ∧
            destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
        then (1 : ℝ) else 0 := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    by_cases herr : bmDecTuple W P B k M hBpos hM ε C y ≠ μ
    · rw [ite_eq_left herr]
      by_cases hgood : GoodAll yr
      · -- Case B: relay made no error in any block, so destination must err in some block `b ≥ 1`
        have hex : ∃ b : Fin B, 1 ≤ b.1 ∧
            destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b := by
          by_contra hall; push Not at hall
          -- Downward induction on `d` shows `bmDestStateAux d = bmPrevMsg μ ⟨B - 1 - d, _⟩`
          have hdown : ∀ d : ℕ, d < B - 1 →
              bmDestState W P B k M hBpos hM ε C y ⟨B - 1 - d, by omega⟩ =
                bmPrevMsg B M hM μ ⟨B - 1 - d, by omega⟩ := by
            intro d
            induction d with
            | zero =>
              intro _
              simp only [Nat.sub_zero]
              rw [bmDestState_last]
              have hlast := hall ⟨B - 1, by omega⟩ (by dsimp only; omega)
              rw [bmCurrMsg_last B M hBpos hM μ] at hlast
              exact hlast
            | succ d ih =>
              intro hd
              have hprev := ih (by omega)
              let b : Fin B := ⟨B - 1 - (d + 1), by omega⟩
              have hb_succ : b.1 + 1 < B := by dsimp only [b]; omega
              have hstep := bmDestState_step W P B k M hBpos hM ε C y b hb_succ
              have hidx : (⟨b.1 + 1, hb_succ⟩ : Fin B) = ⟨B - 1 - d, by omega⟩ := by
                ext; dsimp only [b]; omega
              rw [hidx, hprev] at hstep
              have hcurr : bmPrevMsg B M hM μ ⟨B - 1 - d, by omega⟩ = bmCurrMsg B M hM μ b := by
                rw [← hidx]; exact bmPrevMsg_succ_eq_currMsg B M hM μ b hb_succ
              rw [hcurr] at hstep
              exact hstep.trans (hall b (by dsimp only [b]; omega))
          have hdec_eq : bmDecTuple W P B k M hBpos hM ε C y = μ := by
            funext r
            unfold bmDecTuple
            have hr_eq : (⟨r.1 + 1, by omega⟩ : Fin B) = ⟨B - 1 - (B - 2 - r.1), by omega⟩ := by
              ext; dsimp only; omega
            rw [hr_eq, hdown (B - 2 - r.1) (by omega), ← hr_eq, bmPrevMsg_succ_eq_msg]
          exact herr hdec_eq
        obtain ⟨b, hb1, hb_err⟩ := hex
        have hmem : b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb1⟩
        have h1 : (1 : ℝ) ≤ ∑ b' ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
            if GoodAll yr ∧
                destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b') (y b') ≠ bmPrevMsg B M hM μ b'
            then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if GoodAll yr ∧
                destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
              then (1 : ℝ) else 0) := by rw [ite_eq_left ⟨hgood, hb_err⟩]
            _ ≤ _ := Finset.single_le_sum
                (f := fun b' => if GoodAll yr ∧
                    destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b') (y b') ≠ bmPrevMsg B M hM μ b'
                  then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) hmem
        linarith
      · -- Case A: relay made an error; pick the FIRST block where `bmRelayState ≠ bmPrevMsg`
        have hex_bad : ∃ n : ℕ, ∃ hn : n < B,
            bmRelayState W P k M hM ε C yr n ≠ bmPrevMsg B M hM μ ⟨n, hn⟩ := by
          unfold GoodAll at hgood; push Not at hgood
          obtain ⟨j, hj⟩ := hgood
          exact ⟨j.1, j.2, hj⟩
        set n0 := Nat.find hex_bad
        obtain ⟨hn_lt, hn_ne⟩ := Nat.find_spec hex_bad
        have hn_pos : 0 < n0 := by
          by_contra h0
          have h0' : n0 = 0 := by omega
          have hzero : bmRelayState W P k M hM ε C yr 0 = bmPrevMsg B M hM μ ⟨0, hBpos⟩ := by
            rw [bmPrevMsg_zero]; rfl
          have hne0 : bmRelayState W P k M hM ε C yr 0 ≠ bmPrevMsg B M hM μ ⟨0, hBpos⟩ := by
            have hn_ne' : bmRelayState W P k M hM ε C yr n0 ≠ bmPrevMsg B M hM μ ⟨n0, hn_lt⟩ := hn_ne
            simpa [h0'] using hn_ne'
          exact hne0 hzero
        let b₀ : Fin B := ⟨n0 - 1, by omega⟩
        have hb₀_lt : b₀.1 + 1 < B := by dsimp only [b₀]; omega
        have hgood_b₀ : GoodUpTo b₀.1 yr := by
          intro j hj
          have hj_lt : j.1 < n0 := by dsimp only [b₀] at hj; omega
          have hmin := Nat.find_min hex_bad hj_lt
          push Not at hmin
          exact hmin j.2
        have hstate_b₀ : bmRelayState W P k M hM ε C yr b₀.1 = bmPrevMsg B M hM μ b₀ :=
          hgood_b₀ b₀ le_rfl
        have hsucc_eq : b₀.1 + 1 = n0 := by dsimp only [b₀]; omega
        have hdec_ne : relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b₀) (yr b₀) ≠
            bmCurrMsg B M hM μ b₀ := by
          have h1 : bmRelayState W P k M hM ε C yr n0 =
              relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b₀) (yr b₀) := by
            rw [← hsucc_eq]
            simp only [bmRelayState, b₀.2, ↓reduceDIte, hstate_b₀]
          have h2 : bmPrevMsg B M hM μ ⟨n0, hn_lt⟩ = bmCurrMsg B M hM μ b₀ := by
            have hidx : (⟨n0, hn_lt⟩ : Fin B) = ⟨b₀.1 + 1, hb₀_lt⟩ := Fin.ext hsucc_eq.symm
            rw [hidx]
            exact bmPrevMsg_succ_eq_currMsg B M hM μ b₀ hb₀_lt
          rw [← h1, ← h2]
          exact hn_ne
        have hmem : b₀ ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ b₀, hb₀_lt⟩
        have h1 : (1 : ℝ) ≤ ∑ b' ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
            if GoodUpTo b'.1 yr ∧
                relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b') (yr b') ≠ bmCurrMsg B M hM μ b'
            then (1 : ℝ) else 0 := by
          calc (1 : ℝ) = (if GoodUpTo b₀.1 yr ∧
                relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b₀) (yr b₀) ≠ bmCurrMsg B M hM μ b₀
              then (1 : ℝ) else 0) := by rw [ite_eq_left ⟨hgood_b₀, hdec_ne⟩]
            _ ≤ _ := Finset.single_le_sum
                (f := fun b' => if GoodUpTo b'.1 yr ∧
                    relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b') (yr b') ≠ bmCurrMsg B M hM μ b'
                  then (1 : ℝ) else 0)
                (fun _ _ => by split_ifs <;> norm_num) hmem
        linarith
    · rw [ite_eq_right herr]; linarith
  -- Step 2: Multiply by `bmPrefixTrans` and sum over `(yr, y)`
  have hsum_split :
      (∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
        if bmDecTuple W P B k M hBpos hM ε C y ≠ μ then
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr
        else 0) ≤
      (∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
        ∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            (if GoodUpTo b.1 yr ∧
                relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
            then (1 : ℝ) else 0)) +
      (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
        ∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            (if GoodAll yr ∧
                destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
            then (1 : ℝ) else 0)) := by
    have hpt : ∀ (yr : Fin B → Fin k → Yr) (y : Fin B → Fin k → Y),
        (if bmDecTuple W P B k M hBpos hM ε C y ≠ μ then
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr
        else 0) ≤
        (∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            (if GoodUpTo b.1 yr ∧
                relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
            then (1 : ℝ) else 0)) +
        (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            (if GoodAll yr ∧
                destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
            then (1 : ℝ) else 0)) := by
      intro yr y
      have hmul := mul_le_mul_of_nonneg_left (hind y yr)
        (bmPrefixTrans_nonneg W P B k M hM ε C μ le_rfl y yr)
      have hlhs : bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            (if bmDecTuple W P B k M hBpos hM ε C y ≠ μ then (1 : ℝ) else 0) =
          if bmDecTuple W P B k M hBpos hM ε C y ≠ μ then
            bmPrefixTrans W P B k M hM ε C μ le_rfl y yr
          else 0 := by split_ifs <;> ring
      rw [hlhs, mul_add, Finset.mul_sum, Finset.mul_sum] at hmul
      exact hmul
    calc _ ≤ ∑ yr, ∑ y, _ := Finset.sum_le_sum fun yr _ => Finset.sum_le_sum fun y _ => hpt yr y
      _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · calc _ = ∑ yr, ∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B), ∑ y,
                bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
                  (if GoodUpTo b.1 yr ∧
                      relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
                  then (1 : ℝ) else 0) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
        · calc _ = ∑ yr, ∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1), ∑ y,
                bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
                  (if GoodAll yr ∧
                      destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
                  then (1 : ℝ) else 0) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
  -- Step 3: Bound each relay term `b` (using causal prefix marginalization at `t = b.1 + 1`)
  have hrelay_le : ∀ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
      (∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
        bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
          (if GoodUpTo b.1 yr ∧
              relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
          then (1 : ℝ) else 0)) ≤
      relayBlockErr W P k M hM ε C (bmPrevMsg B M hM μ b) (bmCurrMsg B M hM μ b) := by
    intro b hb
    have hb_lt : b.1 + 1 ≤ B := le_of_lt (Finset.mem_filter.mp hb).2
    let t := b.1 + 1
    let f_pref : (Fin t → Fin k → Y) → (Fin t → Fin k → Yr) → ℝ := fun _ yr_p =>
      if (∀ j : Fin t, bmRelayState W P k M hM ε C yr_p j.1 =
            bmPrevMsg B M hM μ ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩) ∧
          relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr_p ⟨b.1, Nat.lt_succ_self b.1⟩) ≠
            bmCurrMsg B M hM μ b
      then (1 : ℝ) else 0
    have hmatch : ∀ (yr : Fin B → Fin k → Yr) (y : Fin B → Fin k → Y),
        (if GoodUpTo b.1 yr ∧
            relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
        then (1 : ℝ) else 0) =
        f_pref (fun j => y ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩)
               (fun j => yr ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩) := by
      intro yr y
      dsimp only [f_pref, GoodUpTo]
      have hiff : (∀ j : Fin B, j.1 ≤ b.1 → bmRelayState W P k M hM ε C yr j.1 = bmPrevMsg B M hM μ j) ↔
          (∀ j : Fin t, bmRelayState W P k M hM ε C (fun l => yr ⟨l.1, lt_of_lt_of_le l.2 hb_lt⟩) j.1 =
            bmPrevMsg B M hM μ ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩) := by
        constructor
        · intro h j
          rw [bmRelayState_congr W P k M hM ε C
            (fun l : Fin t => yr ⟨l.1, lt_of_lt_of_le l.2 hb_lt⟩) yr j.1 (by omega) (by omega)
            (fun _ _ _ _ => rfl)]
          exact h ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩ (Nat.le_of_lt_succ j.2)
        · intro h j hj
          have hjt : j.1 < t := by omega
          have hthis := h ⟨j.1, hjt⟩
          rw [bmRelayState_congr W P k M hM ε C
            (fun l : Fin t => yr ⟨l.1, lt_of_lt_of_le l.2 hb_lt⟩) yr j.1 (by omega) (by omega)
            (fun _ _ _ _ => rfl)] at hthis
          exact hthis
      exact if_congr (and_congr hiff (by simp only [Fin.eta])) rfl rfl
    have hrew_pref :
        (∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            (if GoodUpTo b.1 yr ∧
                relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr b) ≠ bmCurrMsg B M hM μ b
            then (1 : ℝ) else 0)) =
        ∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
          bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
            f_pref (fun j => y ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩)
                   (fun j => yr ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩) :=
      Finset.sum_congr rfl fun yr _ => Finset.sum_congr rfl fun y _ => by rw [hmatch yr y]
    rw [hrew_pref, bmPrefixTrans_sum_prefix W P B k M hM ε C μ hb_lt le_rfl f_pref]
    -- On `f_pref ≠ 0`, `bmRelayState = bmPrevMsg` for all `j : Fin t`, so replace `bmPrefixTrans` by a pure product
    let u : Fin t → Fin k → X × Xr := fun j i =>
      ((C (bmPrevMsg B M hM μ ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩)).2
          (bmCurrMsg B M hM μ ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩) i,
       (C (bmPrevMsg B M hM μ ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩)).1 i)
    have hdrop : ∀ (yr_p : Fin t → Fin k → Yr) (y_p : Fin t → Fin k → Y),
        bmPrefixTrans W P B k M hM ε C μ hb_lt y_p yr_p * f_pref y_p yr_p ≤
        (∏ j : Fin t, (W.power k).trans (u j) (fun i => (y_p j i, yr_p j i))) *
          (if relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr_p ⟨b.1, Nat.lt_succ_self b.1⟩) ≠
              bmCurrMsg B M hM μ b then (1 : ℝ) else 0) := by
      intro yr_p y_p
      dsimp only [f_pref]
      by_cases hcond : (∀ j : Fin t, bmRelayState W P k M hM ε C yr_p j.1 =
            bmPrevMsg B M hM μ ⟨j.1, lt_of_lt_of_le j.2 hb_lt⟩) ∧
          relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr_p ⟨b.1, Nat.lt_succ_self b.1⟩) ≠
            bmCurrMsg B M hM μ b
      · rw [ite_eq_left hcond, ite_eq_left hcond.2, mul_one, mul_one]
        unfold bmPrefixTrans
        exact le_of_eq (Finset.prod_congr rfl fun j _ => by simp only [hcond.1 j, u])
      · rw [ite_eq_right hcond, mul_zero]
        exact mul_nonneg (Finset.prod_nonneg fun _ _ => (W.power k).nonneg _ _)
          (by split_ifs <;> norm_num)
    calc _ ≤ ∑ yr_p : Fin t → Fin k → Yr, ∑ y_p : Fin t → Fin k → Y,
          (∏ j : Fin t, (W.power k).trans (u j) (fun i => (y_p j i, yr_p j i))) *
            (if relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) (yr_p ⟨b.1, Nat.lt_succ_self b.1⟩) ≠
                bmCurrMsg B M hM μ b then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun yr_p _ => Finset.sum_le_sum fun y_p _ => hdrop yr_p y_p
      _ = ∑ yr₀ : Fin k → Yr, ∑ y₀ : Fin k → Y,
          (W.power k).trans (u ⟨b.1, Nat.lt_succ_self b.1⟩) (fun i => (y₀ i, yr₀ i)) *
            (if relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) yr₀ ≠ bmCurrMsg B M hM μ b
            then (1 : ℝ) else 0) :=
          prod_block_trans_single W k t u ⟨b.1, Nat.lt_succ_self b.1⟩
            (fun _ yr₀ => if relayBlockDec W P k M hM ε C (bmPrevMsg B M hM μ b) yr₀ ≠
              bmCurrMsg B M hM μ b then (1 : ℝ) else 0)
      _ = relayBlockErr W P k M hM ε C (bmPrevMsg B M hM μ b) (bmCurrMsg B M hM μ b) := by
          unfold relayBlockErr
          refine Finset.sum_congr rfl fun yr₀ _ => ?_
          rw [← Finset.sum_mul, ← relayYrChannel_power_trans]
          have hu_eq : u ⟨b.1, Nat.lt_succ_self b.1⟩ =
              fun i => ((C (bmPrevMsg B M hM μ b)).2 (bmCurrMsg B M hM μ b) i,
                        (C (bmPrevMsg B M hM μ b)).1 i) := rfl
          rw [hu_eq]
          split_ifs <;> ring
  -- Step 4: Bound each destination term `b` (on `GoodAll`, every block uses `bmPrevMsg`)
  have hdest_le : ∀ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
      (∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
        bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
          (if GoodAll yr ∧
              destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
          then (1 : ℝ) else 0)) ≤
      destBlockErr W P k M hM ε C (bmPrevMsg B M hM μ b) (bmCurrMsg B M hM μ b) := by
    intro b _
    let u : Fin B → Fin k → X × Xr := fun j i =>
      ((C (bmPrevMsg B M hM μ j)).2 (bmCurrMsg B M hM μ j) i,
       (C (bmPrevMsg B M hM μ j)).1 i)
    have hdrop : ∀ (yr : Fin B → Fin k → Yr) (y : Fin B → Fin k → Y),
        bmPrefixTrans W P B k M hM ε C μ le_rfl y yr *
          (if GoodAll yr ∧
              destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
          then (1 : ℝ) else 0) ≤
        (∏ j : Fin B, (W.power k).trans (u j) (fun i => (y j i, yr j i))) *
          (if destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
          then (1 : ℝ) else 0) := by
      intro yr y
      by_cases hcond : GoodAll yr ∧
          destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
      · rw [ite_eq_left hcond, ite_eq_left hcond.2, mul_one, mul_one]
        unfold bmPrefixTrans
        exact le_of_eq (Finset.prod_congr rfl fun j _ => by simp only [hcond.1 j, u])
      · rw [ite_eq_right hcond, mul_zero]
        exact mul_nonneg (Finset.prod_nonneg fun _ _ => (W.power k).nonneg _ _)
          (by split_ifs <;> norm_num)
    calc _ ≤ ∑ yr : Fin B → Fin k → Yr, ∑ y : Fin B → Fin k → Y,
          (∏ j : Fin B, (W.power k).trans (u j) (fun i => (y j i, yr j i))) *
            (if destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) (y b) ≠ bmPrevMsg B M hM μ b
            then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun yr _ => Finset.sum_le_sum fun y _ => hdrop yr y
      _ = ∑ yr₀ : Fin k → Yr, ∑ y₀ : Fin k → Y,
          (W.power k).trans (u b) (fun i => (y₀ i, yr₀ i)) *
            (if destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) y₀ ≠ bmPrevMsg B M hM μ b
            then (1 : ℝ) else 0) :=
          prod_block_trans_single W k B u b
            (fun y₀ _ => if destBlockDec W P k M hM ε C (bmCurrMsg B M hM μ b) y₀ ≠
              bmPrevMsg B M hM μ b then (1 : ℝ) else 0)
      _ = destBlockErr W P k M hM ε C (bmPrevMsg B M hM μ b) (bmCurrMsg B M hM μ b) := by
          rw [Finset.sum_comm]
          unfold destBlockErr
          refine Finset.sum_congr rfl fun y₀ _ => ?_
          rw [← Finset.sum_mul, ← relayYChannel_power_trans]
          dsimp only [u]
          split_ifs <;> ring
  have hsum1 := Finset.sum_le_sum hrelay_le
  have hsum2 := Finset.sum_le_sum hdest_le
  linarith

/-- Bridge: for a blocklength-`(B * k)` operational relay code built from `(C, φ, ψ)`,
    its average error matches the block-Markov error expression `bmPrefixTrans` averaged over `m`. -/
private lemma bm_operational_code_existence [Nonempty X]
    (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr))
    (B k M M_tot : ℕ) (hB : 2 ≤ B) (hk : 0 < k) (hM : 0 < M) (hM_tot : 0 < M_tot)
    (hle : M_tot ≤ M ^ (B - 1)) (ε : ℝ) :
    let J := W.joint P
    let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
    let P_Y := (relayYChannel W).joint P
    ∃ (enc : Fin M_tot → Fin (B * k) → X)
      (relay : ∀ i : Fin (B * k), (Fin i.1 → Yr) → Xr)
      (dec : (Fin (B * k) → Y) → Fin M_tot),
      ((1 : ℝ) / (M_tot : ℝ)) *
        ∑ m : Fin M_tot, ∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
          (if dec y ≠ m then
            ∏ i : Fin (B * k),
              W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0) ≤
      ((B - 1 : ℕ) : ℝ) *
        (((1 - ∑ t ∈ relayTypicalSet W P k ε, (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t)) +
          ((M - 1 : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((k : ℝ) *
              (condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) - 4 * ε)))) +
         ((1 - ∑ xy ∈ jointTypicalSet P_Y k ε, (jointIidDist P_Y k).pmf xy) +
          ((M - 1 : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((k : ℝ) *
              (mutualInfo (J.map (fun z => (z.1, z.2.1))) - 3 * ε))))) := by
  classical
  dsimp only
  have hBpos : 0 < B := by omega
  let J := W.joint P
  let P_XrXYr := J.map (fun z => ((z.1.2, z.1.1), z.2.2))
  let P_Y := (relayYChannel W).joint P
  let B_relay : ℝ :=
    (1 - ∑ t ∈ relayTypicalSet W P k ε, (iidDist P_XrXYr k).pmf (relayZipEquiv Xr X Yr k t)) +
    ((M - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((k : ℝ) *
        (condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2))) - 4 * ε)))
  let B_dest : ℝ :=
    (1 - ∑ xy ∈ jointTypicalSet P_Y k ε, (jointIidDist P_Y k).pmf xy) +
    ((M - 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((k : ℝ) *
        (mutualInfo (J.map (fun z => (z.1, z.2.1))) - 3 * ε)))
  -- Embed `Fin M_tot` into `Fin (B - 1) → Fin M` with left inverse `ψ`
  have hcard : Fintype.card (Fin (B - 1) → Fin M) = M ^ (B - 1) := by simp
  let eMsg : (Fin (B - 1) → Fin M) ≃ Fin (M ^ (B - 1)) := Fintype.equivFinOfCardEq hcard
  let φ : Fin M_tot → (Fin (B - 1) → Fin M) := fun m => eMsg.symm ⟨m.1, lt_of_lt_of_le m.2 hle⟩
  let ψ : (Fin (B - 1) → Fin M) → Fin M_tot := fun μ =>
    if h : (eMsg μ).1 < M_tot then ⟨(eMsg μ).1, h⟩ else ⟨0, hM_tot⟩
  have hψφ : ∀ m : Fin M_tot, ψ (φ m) = m := by
    intro m
    dsimp only [ψ, φ]
    simp only [Equiv.apply_symm_apply, m.2, ↓reduceDIte, Fin.eta]
  -- Operational code constructors parameterized by codebook `C`
  let encOf : (Fin M → RaCloudCode Xr X k M) → Fin M_tot → Fin (B * k) → X :=
    fun C m i =>
      let bj := (raBlockEquiv B k hk).symm i
      (C (bmPrevMsg B M hM (φ m) bj.1)).2 (bmCurrMsg B M hM (φ m) bj.1) bj.2
  let relayOf : (Fin M → RaCloudCode Xr X k M) → ∀ i : Fin (B * k), (Fin i.1 → Yr) → Xr :=
    fun C i hist =>
      let bj := (raBlockEquiv B k hk).symm i
      have hbk : bj.1.1 * k ≤ i.1 := by
        have h1 : bj.1.1 * k + bj.2.1 = i.1 := by
          have := congrArg Fin.val ((raBlockEquiv B k hk).apply_symm_apply i)
          exact this
        omega
      (C (bmRelayStateFromHist W P B k M hM ε C i hist bj.1.1 hbk)).1 bj.2
  let decOf : (Fin M → RaCloudCode Xr X k M) → (Fin (B * k) → Y) → Fin M_tot :=
    fun C y => ψ (bmDecTuple W P B k M hBpos hM ε C (raUnblockEquiv Y B k hk y))
  let opErr : (Fin M → RaCloudCode Xr X k M) → ℝ := fun C =>
    ((1 : ℝ) / (M_tot : ℝ)) *
      ∑ m : Fin M_tot, ∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
        if decOf C y ≠ m then
          ∏ i : Fin (B * k),
            W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
        else 0
  -- Relate `opErr C` to the block-Markov error for each `(C, m)`
  have hcode_err : ∀ (C : Fin M → RaCloudCode Xr X k M) (m : Fin M_tot),
      (∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
        if decOf C y ≠ m then
          ∏ i : Fin (B * k),
            W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
        else 0) ≤
      (∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
        relayBlockErr W P k M hM ε C (bmPrevMsg B M hM (φ m) b) (bmCurrMsg B M hM (φ m) b)) +
      (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
        destBlockErr W P k M hM ε C (bmPrevMsg B M hM (φ m) b) (bmCurrMsg B M hM (φ m) b)) := by
    intro C m
    have hprod_eq : ∀ (yr : Fin (B * k) → Yr) (y : Fin (B * k) → Y),
        (∏ i : Fin (B * k),
          W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)) =
        bmPrefixTrans W P B k M hM ε C (φ m) le_rfl
          (raUnblockEquiv Y B k hk y) (raUnblockEquiv Yr B k hk yr) := by
      intro yr y
      rw [← Fintype.prod_equiv (raBlockEquiv B k hk)
        (fun p : Fin B × Fin k =>
          let i := raBlockEquiv B k hk p
          W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i))
        _ (fun _ => rfl)]
      rw [Fintype.prod_prod_type]
      unfold bmPrefixTrans DMC.power
      refine Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun j _ => ?_
      dsimp only [encOf, relayOf]
      simp only [Equiv.symm_apply_apply]
      rw [bmRelayStateFromHist_eq W P B k M hk hM ε C yr (raBlockEquiv B k hk (b, j)) b.1]
      rfl
    have hle_ind : ∀ (yr : Fin (B * k) → Yr) (y : Fin (B * k) → Y),
        (if decOf C y ≠ m then
          ∏ i : Fin (B * k),
            W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
        else 0) ≤
        if bmDecTuple W P B k M hBpos hM ε C (raUnblockEquiv Y B k hk y) ≠ φ m then
          bmPrefixTrans W P B k M hM ε C (φ m) le_rfl
            (raUnblockEquiv Y B k hk y) (raUnblockEquiv Yr B k hk yr)
        else 0 := by
      intro yr y
      rw [hprod_eq yr y]
      have hnn := bmPrefixTrans_nonneg W P B k M hM ε C (φ m) le_rfl
        (raUnblockEquiv Y B k hk y) (raUnblockEquiv Yr B k hk yr)
      by_cases h1 : decOf C y ≠ m
      · have h2 : bmDecTuple W P B k M hBpos hM ε C (raUnblockEquiv Y B k hk y) ≠ φ m := by
          intro heq
          apply h1
          dsimp only [decOf]
          rw [heq, hψφ m]
        simp [h1, h2]
      · simp [h1]; split_ifs <;> linarith
    calc _ ≤ ∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
          if bmDecTuple W P B k M hBpos hM ε C (raUnblockEquiv Y B k hk y) ≠ φ m then
            bmPrefixTrans W P B k M hM ε C (φ m) le_rfl
              (raUnblockEquiv Y B k hk y) (raUnblockEquiv Yr B k hk yr)
          else 0 :=
          Finset.sum_le_sum fun yr _ => Finset.sum_le_sum fun y _ => hle_ind yr y
      _ = ∑ yr_b : Fin B → Fin k → Yr, ∑ y_b : Fin B → Fin k → Y,
          if bmDecTuple W P B k M hBpos hM ε C y_b ≠ φ m then
            bmPrefixTrans W P B k M hM ε C (φ m) le_rfl y_b yr_b
          else 0 := by
          rw [Fintype.sum_equiv (raUnblockEquiv Yr B k hk) _
              (fun yr_b => ∑ y : Fin (B * k) → Y,
                if bmDecTuple W P B k M hBpos hM ε C (raUnblockEquiv Y B k hk y) ≠ φ m then
                  bmPrefixTrans W P B k M hM ε C (φ m) le_rfl (raUnblockEquiv Y B k hk y) yr_b
                else 0)
              (fun _ => rfl)]
          refine Finset.sum_congr rfl fun yr_b _ => ?_
          exact Fintype.sum_equiv (raUnblockEquiv Y B k hk) _
            (fun y_b => if bmDecTuple W P B k M hBpos hM ε C y_b ≠ φ m then
              bmPrefixTrans W P B k M hM ε C (φ m) le_rfl y_b yr_b else 0)
            (fun _ => rfl)
      _ ≤ _ := bm_error_le_sum_block_errors W P B k M hB hM ε C (φ m)
  -- Card of the two block index filters
  have hcard1 : (Finset.univ.filter (fun b : Fin B => b.1 + 1 < B)).card = B - 1 := by
    have heq : Finset.univ.filter (fun b : Fin B => b.1 + 1 < B) =
        Finset.univ.erase ⟨B - 1, by omega⟩ := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro h heq; have := congrArg Fin.val heq; dsimp only at this; omega
      · intro h; by_contra hge; apply h; ext; dsimp only; omega
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hcard2 : (Finset.univ.filter (fun b : Fin B => 1 ≤ b.1)).card = B - 1 := by
    have heq : Finset.univ.filter (fun b : Fin B => 1 ≤ b.1) =
        Finset.univ.erase ⟨0, hBpos⟩ := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro h heq; have := congrArg Fin.val heq; dsimp only at this; omega
      · intro h; by_contra hge; apply h; ext; dsimp only; omega
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- Ensemble expectation bound for each fixed `m : Fin M_tot`
  have hexp_m : ∀ m : Fin M_tot,
      ∑ C : Fin M → RaCloudCode Xr X k M,
        relayCodeWeight P k M C *
          (∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
            if decOf C y ≠ m then
              ∏ i : Fin (B * k),
                W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
            else 0) ≤
      ((B - 1 : ℕ) : ℝ) * (B_relay + B_dest) := by
    intro m
    calc _ ≤ ∑ C, relayCodeWeight P k M C *
          ((∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
              relayBlockErr W P k M hM ε C (bmPrevMsg B M hM (φ m) b) (bmCurrMsg B M hM (φ m) b)) +
           (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
              destBlockErr W P k M hM ε C (bmPrevMsg B M hM (φ m) b) (bmCurrMsg B M hM (φ m) b))) :=
          Finset.sum_le_sum fun C _ =>
            mul_le_mul_of_nonneg_left (hcode_err C m) (relayCodeWeight_nonneg P k M C)
      _ = (∑ b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B),
            ∑ C, relayCodeWeight P k M C *
              relayBlockErr W P k M hM ε C (bmPrevMsg B M hM (φ m) b) (bmCurrMsg B M hM (φ m) b)) +
          (∑ b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1),
            ∑ C, relayCodeWeight P k M C *
              destBlockErr W P k M hM ε C (bmPrevMsg B M hM (φ m) b) (bmCurrMsg B M hM (φ m) b)) := by
          simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_comm
      _ ≤ (∑ _b ∈ Finset.univ.filter (fun b : Fin B => b.1 + 1 < B), B_relay) +
          (∑ _b ∈ Finset.univ.filter (fun b : Fin B => 1 ≤ b.1), B_dest) :=
          add_le_add
            (Finset.sum_le_sum fun b _ => expected_relayBlockErr_le W P k M hM ε _ _)
            (Finset.sum_le_sum fun b _ => expected_destBlockErr_le W P k M hM ε _ _)
      _ = ((B - 1 : ℕ) : ℝ) * (B_relay + B_dest) := by
          rw [Finset.sum_const, hcard1, nsmul_eq_mul, Finset.sum_const, hcard2, nsmul_eq_mul]
          ring
  -- Average over `m : Fin M_tot` and extract a deterministic codebook `C`
  have hexp_tot : ∑ C : Fin M → RaCloudCode Xr X k M, relayCodeWeight P k M C * opErr C ≤
      ((B - 1 : ℕ) : ℝ) * (B_relay + B_dest) := by
    have hMpos : (0 : ℝ) < (M_tot : ℝ) := Nat.cast_pos.mpr hM_tot
    have hrew : ∑ C : Fin M → RaCloudCode Xr X k M, relayCodeWeight P k M C * opErr C =
        ((1 : ℝ) / (M_tot : ℝ)) *
          ∑ m : Fin M_tot, ∑ C : Fin M → RaCloudCode Xr X k M,
            relayCodeWeight P k M C *
              (∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
                if decOf C y ≠ m then
                  ∏ i : Fin (B * k),
                    W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
                else 0) := by
      have h1 : ∀ C : Fin M → RaCloudCode Xr X k M,
          relayCodeWeight P k M C * opErr C =
          ((1 : ℝ) / (M_tot : ℝ)) *
            ∑ m : Fin M_tot, relayCodeWeight P k M C *
              (∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
                if decOf C y ≠ m then
                  ∏ i : Fin (B * k),
                    W.trans (encOf C m i, relayOf C i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
                else 0) := by
        intro C
        dsimp only [opErr]
        rw [← mul_assoc, mul_comm (relayCodeWeight P k M C), mul_assoc, Finset.mul_sum]
      simp_rw [h1]
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    rw [hrew]
    calc _ ≤ ((1 : ℝ) / (M_tot : ℝ)) * ∑ _m : Fin M_tot, (((B - 1 : ℕ) : ℝ) * (B_relay + B_dest)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hexp_m m) (by positivity)
      _ = ((1 : ℝ) / (M_tot : ℝ)) * ((M_tot : ℝ) * (((B - 1 : ℕ) : ℝ) * (B_relay + B_dest))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((B - 1 : ℕ) : ℝ) * (B_relay + B_dest) := by field_simp [ne_of_gt hMpos]
  obtain ⟨C, hC⟩ := ra_exists_le_of_weighted_sum_le
    (relayCodeWeight P k M) opErr (((B - 1 : ℕ) : ℝ) * (B_relay + B_dest))
    (relayCodeWeight_nonneg P k M) (relayCodeWeight_sum_one P k M) hexp_tot
  exact ⟨encOf C, relayOf C, decOf C, hC⟩

/-- One-step blocklength padding: extending a blocklength-`n` causal relay code by one unused
    channel use preserves the exact average error probability. -/
private lemma relay_code_pad_succ [Nonempty X] [Nonempty Xr]
    (W : RelayChannel X Xr Y Yr) {n M : ℕ} {ε : ℝ}
    (hcode : ∃ (enc : Fin M → Fin n → X)
      (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
      (dec : (Fin n → Y) → Fin M),
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
          (if dec y ≠ m then
            ∏ i : Fin n, W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0) ≤ ε) :
    ∃ (enc : Fin M → Fin (n + 1) → X)
      (relay : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr)
      (dec : (Fin (n + 1) → Y) → Fin M),
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin (n + 1) → Yr, ∑ y : Fin (n + 1) → Y,
          (if dec y ≠ m then
            ∏ i : Fin (n + 1), W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0) ≤ ε := by
  classical
  obtain ⟨enc₀, relay₀, dec₀, herr₀⟩ := hcode
  let x₀ : X := Classical.arbitrary X
  let xr₀ : Xr := Classical.arbitrary Xr
  let enc₁ : Fin M → Fin (n + 1) → X := fun m i =>
    if h : i.1 < n then enc₀ m ⟨i.1, h⟩ else x₀
  let relay₁ : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr := fun i hist =>
    if h : i.1 < n then relay₀ ⟨i.1, h⟩ hist else xr₀
  let dec₁ : (Fin (n + 1) → Y) → Fin M := fun y => dec₀ (fun i => y i.castSucc)
  refine ⟨enc₁, relay₁, dec₁, ?_⟩
  have hsum_eq : ∀ m : Fin M,
      (∑ yr : Fin (n + 1) → Yr, ∑ y : Fin (n + 1) → Y,
        if dec₁ y ≠ m then
          ∏ i : Fin (n + 1), W.trans (enc₁ m i, relay₁ i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
        else 0) =
      ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
        if dec₀ y ≠ m then
          ∏ i : Fin n, W.trans (enc₀ m i, relay₀ i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
        else 0 := by
    intro m
    have hreidx_yr := Fintype.sum_equiv (raPiSnocEquiv Yr n).symm
      (fun p : (Fin n → Yr) × Yr =>
        ∑ y : Fin (n + 1) → Y,
          if dec₁ y ≠ m then
            ∏ i : Fin (n + 1),
              W.trans (enc₁ m i, relay₁ i (fun j => raSnocVec p.1 p.2 ⟨j.1, Nat.lt_trans j.2 i.2⟩))
                (y i, raSnocVec p.1 p.2 i)
          else 0)
      (fun yr : Fin (n + 1) → Yr =>
        ∑ y : Fin (n + 1) → Y,
          if dec₁ y ≠ m then
            ∏ i : Fin (n + 1),
              W.trans (enc₁ m i, relay₁ i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0)
      (fun _ => rfl)
    rw [← hreidx_yr, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun yr_init _ => ?_
    have hinner : ∀ yr_last : Yr,
        (∑ y : Fin (n + 1) → Y,
          if dec₁ y ≠ m then
            ∏ i : Fin (n + 1),
              W.trans (enc₁ m i, relay₁ i (fun j => raSnocVec yr_init yr_last ⟨j.1, Nat.lt_trans j.2 i.2⟩))
                (y i, raSnocVec yr_init yr_last i)
          else 0) =
        ∑ y_init : Fin n → Y, ∑ y_last : Y,
          (if dec₀ y_init ≠ m then
            ∏ i : Fin n, W.trans (enc₀ m i, relay₀ i (fun j => yr_init ⟨j.1, Nat.lt_trans j.2 i.2⟩))
              (y_init i, yr_init i)
          else 0) * W.trans (x₀, xr₀) (y_last, yr_last) := by
      intro yr_last
      have hreidx_y := Fintype.sum_equiv (raPiSnocEquiv Y n).symm
        (fun q : (Fin n → Y) × Y =>
          if dec₁ (raSnocVec q.1 q.2) ≠ m then
            ∏ i : Fin (n + 1),
              W.trans (enc₁ m i, relay₁ i (fun j => raSnocVec yr_init yr_last ⟨j.1, Nat.lt_trans j.2 i.2⟩))
                (raSnocVec q.1 q.2 i, raSnocVec yr_init yr_last i)
          else 0)
        (fun y : Fin (n + 1) → Y =>
          if dec₁ y ≠ m then
            ∏ i : Fin (n + 1),
              W.trans (enc₁ m i, relay₁ i (fun j => raSnocVec yr_init yr_last ⟨j.1, Nat.lt_trans j.2 i.2⟩))
                (y i, raSnocVec yr_init yr_last i)
          else 0)
        (fun _ => rfl)
      rw [← hreidx_y, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y_init _ => Finset.sum_congr rfl fun y_last _ => ?_
      have hdec : dec₁ (raSnocVec y_init y_last) = dec₀ y_init := by
        dsimp only [dec₁]; congr 1; funext i; simp [raSnocVec]
      rw [hdec]
      have hprod : (∏ i : Fin (n + 1),
            W.trans (enc₁ m i, relay₁ i (fun j => raSnocVec yr_init yr_last ⟨j.1, Nat.lt_trans j.2 i.2⟩))
              (raSnocVec y_init y_last i, raSnocVec yr_init yr_last i)) =
          (∏ i : Fin n, W.trans (enc₀ m i, relay₀ i (fun j => yr_init ⟨j.1, Nat.lt_trans j.2 i.2⟩))
            (y_init i, yr_init i)) * W.trans (x₀, xr₀) (y_last, yr_last) := by
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          have hi : i.castSucc.1 < n := i.2
          dsimp only [enc₁, relay₁]
          simp only [hi, ↓reduceDIte, raSnocVec, Fin.snoc_castSucc]
          congr 2
          · congr 1; funext j
            have hidx : (⟨j.1, Nat.lt_trans j.2 i.castSucc.2⟩ : Fin (n + 1)) =
                (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n).castSucc := Fin.ext rfl
            rw [hidx, Fin.snoc_castSucc]
        · have hnot : ¬ (Fin.last n).1 < n := by simp
          dsimp only [enc₁, relay₁]
          simp only [hnot, ↓reduceDIte, raSnocVec, Fin.snoc_last]
      rw [hprod]
      split_ifs <;> ring
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y_init _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hW1 : ∑ y_last : Y, ∑ yr_last : Yr, W.trans (x₀, xr₀) (y_last, yr_last) = 1 := by
      rw [← Fintype.sum_prod_type]; exact W.sum_one (x₀, xr₀)
    rw [hW1, mul_one]
  simp_rw [hsum_eq]
  exact herr₀

/-- Arbitrary blocklength padding `n₀ ≤ n` preserving average error probability. -/
private lemma relay_code_pad [Nonempty X] [Nonempty Xr]
    (W : RelayChannel X Xr Y Yr) {n₀ n M : ℕ} (hle : n₀ ≤ n) {ε : ℝ}
    (hcode : ∃ (enc : Fin M → Fin n₀ → X)
      (relay : ∀ i : Fin n₀, (Fin i.1 → Yr) → Xr)
      (dec : (Fin n₀ → Y) → Fin M),
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin n₀ → Yr, ∑ y : Fin n₀ → Y,
          (if dec y ≠ m then
            ∏ i : Fin n₀, W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0) ≤ ε) :
    ∃ (enc : Fin M → Fin n → X)
      (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
      (dec : (Fin n → Y) → Fin M),
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
          (if dec y ≠ m then
            ∏ i : Fin n, W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0) ≤ ε := by
  induction n, hle using Nat.le_induction with
  | base => exact hcode
  | succ m _ ih => exact relay_code_pad_succ W ih

end BlockMarkov

/-! ### 4. Decode-and-Forward Operational Achievability (Cover & El Gamal 1979; El Gamal–Kim Thm. 16.2) -/

section DFAchievability

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- Rate `0` is operationally achievable over any discrete memoryless relay channel
    with nonempty input alphabets. -/
theorem isRelayAchievable_zero [Nonempty X] [Nonempty Xr] (W : RelayChannel X Xr Y Yr) :
    IsRelayAchievable W 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  have hM1 : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
    change max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1
    norm_num
  have hMpos : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) := by omega
  let x₀ : X := Classical.arbitrary X
  let xr₀ : Xr := Classical.arbitrary Xr
  refine ⟨fun _ _ => x₀, fun _ _ => xr₀, fun _ => ⟨0, hMpos⟩, ?_⟩
  have hzero : ∀ m : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))),
      (⟨0, hMpos⟩ : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))))) = m := by
    intro m; ext; dsimp only; omega
  have herr : ((1 : ℝ) / ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) : ℕ) : ℝ)) *
      ∑ m : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))),
        ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
          (if (⟨0, hMpos⟩ : Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))))) ≠ m then
            ∏ i : Fin n, W.trans (x₀, xr₀) (y i, yr i) else 0) = 0 := by
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun _ _ =>
      Finset.sum_eq_zero fun _ _ => ?_)
    simp [hzero m]
  linarith

/-- **Cover–El Gamal Decode-and-Forward Achievability** (Cover & El Gamal 1979;
    Cover & Thomas §15.10; El Gamal & Kim Theorem 16.2):
    for any single-letter input distribution `P ∈ Δ(X × X_r)`, every rate
    `0 ≤ R < min { I(X; Y_r | X_r), I(X, X_r; Y) }` is operationally achievable over `W`. -/
theorem relayDF_achievable (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) {R : ℝ}
    (hR0 : 0 ≤ R)
    (hR : R < min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.2, z.1.2))))
                  (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))))) :
    IsRelayAchievable W R := by
  have hne : Nonempty (X × Xr) := ra_nonempty_of_probDist P
  have : Nonempty X := ⟨hne.some.1⟩
  have : Nonempty Xr := ⟨hne.some.2⟩
  refine ⟨hR0, fun δ hδ => ?_⟩
  let J := W.joint P
  let I_relay := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
  let I_dest := mutualInfo (J.map (fun z => (z.1, z.2.1)))
  let I_min := min I_relay I_dest
  have hR_lt_min : R < I_min := hR
  let R_mid : ℝ := (R + I_min) / 2
  have hR_lt_mid : R < R_mid := by dsimp only [R_mid]; linarith
  have hmid_lt_min : R_mid < I_min := by dsimp only [R_mid]; linarith
  have hmid_pos : 0 < R_mid := by linarith
  have hmid_lt_relay : R_mid < I_relay := lt_of_lt_of_le hmid_lt_min (min_le_left _ _)
  have hmid_lt_dest : R_mid < I_dest := lt_of_lt_of_le hmid_lt_min (min_le_right _ _)
  -- Step 1: Choose block count `B ≥ 2` so that `(B - 1) * R_mid - B * R > 0`
  have hgap_R : 0 < R_mid - R := by linarith
  obtain ⟨B₀, hB₀⟩ := exists_nat_gt (R_mid / (R_mid - R))
  let B : ℕ := max B₀ 2
  have hB2 : 2 ≤ B := le_max_right B₀ 2
  have hB_gt : R_mid / (R_mid - R) < (B : ℝ) :=
    lt_of_lt_of_le hB₀ (by exact_mod_cast le_max_left B₀ 2)
  have hB_gap : 0 < ((B - 1 : ℕ) : ℝ) * R_mid - (B : ℝ) * R := by
    have h1 : R_mid < (B : ℝ) * (R_mid - R) := (div_lt_iff₀ hgap_R).mp hB_gt
    have hcast : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_one]
    rw [hcast]; linarith
  have hBsub_pos : (0 : ℝ) < ((B - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Step 2: Choose typicality tolerance `ε` and target per-block error `η = δ / (4 * (B - 1))`
  let ε : ℝ := (I_min - R_mid) / 5
  have hε_pos : 0 < ε := by dsimp only [ε]; linarith
  let η : ℝ := δ / (4 * ((B - 1 : ℕ) : ℝ))
  have hη_pos : 0 < η := by positivity
  -- Step 3: Thresholds on per-block length `k`
  obtain ⟨K₁, hK₁⟩ := relay_aep_prob_tendsto_one W P hε_pos hη_pos
  obtain ⟨K₂, hK₂⟩ := joint_aep_prob_tendsto_one ((relayYChannel W).joint P) hε_pos hη_pos
  obtain ⟨K₃, hK₃⟩ := exists_nat_ge (log2 (1 / η) / ε)
  obtain ⟨K₄, hK₄⟩ := exists_nat_ge (1 / R_mid)
  obtain ⟨K₅, hK₅⟩ := exists_nat_ge
    (((B : ℝ) * R + ((B - 1 : ℕ) : ℝ)) / (((B - 1 : ℕ) : ℝ) * R_mid - (B : ℝ) * R))
  let K : ℕ := max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ 1)
  -- Return total blocklength threshold `N = B * K`
  refine ⟨B * K, fun n hn => ?_⟩
  dsimp only
  let k : ℕ := n / B
  have hk_ge_K : K ≤ k := (Nat.le_div_iff_mul_le (by omega : 0 < B)).mpr (by rw [mul_comm]; exact hn)
  have hk_pos : 0 < k := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one (le_max_right K₅ 1))
    (le_trans (le_max_right _ _) hk_ge_K)
  have hBk_le_n : B * k ≤ n := Nat.mul_div_le n B
  have hn_lt : n < B * (k + 1) := by
    have hmod := Nat.div_add_mod n B
    have hrem := Nat.mod_lt n (by omega : 0 < B)
    dsimp only [k]
    nlinarith
  let M : ℕ := Nat.floor ((2 : ℝ) ^ ((k : ℝ) * R_mid))
  let M_tot : ℕ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hM_tot_pos : 0 < M_tot := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  -- Verify `k * R_mid ≥ 1`, so `M ≥ 1` and `2^(k * R_mid - 1) ≤ M ≤ 2^(k * R_mid)`
  have hkR_ge1 : (1 : ℝ) ≤ (k : ℝ) * R_mid := by
    have hk4 : 1 / R_mid ≤ (k : ℝ) :=
      le_trans hK₄ (by exact_mod_cast le_trans (le_trans (le_trans (le_max_right K₃ K₄) (le_max_right _ _)) (le_max_left _ _)) hk_ge_K)
    exact (div_le_iff₀ hmid_pos).mp hk4
  have hpow_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hkR_ge1
  have hM_ge1 : 1 ≤ M := Nat.le_floor (by norm_num; linarith)
  have hM_pos : 0 < M := by omega
  have hM_le_pow : (M : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) := Nat.floor_le (by positivity)
  have hM_ge_pow : (2 : ℝ) ^ ((k : ℝ) * R_mid - 1) ≤ (M : ℝ) := by
    have hhalf : (2 : ℝ) ^ ((k : ℝ) * R_mid - 1) = (2 : ℝ) ^ ((k : ℝ) * R_mid) / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hfl := Nat.sub_one_lt_floor ((2 : ℝ) ^ ((k : ℝ) * R_mid))
    linarith
  -- Verify `M_tot ≤ M ^ (B - 1)`
  have hMtot_le : M_tot ≤ M ^ (B - 1) := by
    have hk5 : ((B : ℝ) * R + ((B - 1 : ℕ) : ℝ)) / (((B - 1 : ℕ) : ℝ) * R_mid - (B : ℝ) * R) ≤ (k : ℝ) :=
      le_trans hK₅ (by exact_mod_cast le_trans (le_trans (le_max_left K₅ 1) (le_max_right _ _)) hk_ge_K)
    have hexp_le : (n : ℝ) * R ≤ ((B - 1 : ℕ) : ℝ) * ((k : ℝ) * R_mid - 1) := by
      have h1 : (B : ℝ) * R + ((B - 1 : ℕ) : ℝ) ≤ (k : ℝ) * (((B - 1 : ℕ) : ℝ) * R_mid - (B : ℝ) * R) :=
        (div_le_iff₀ hB_gap).mp hk5
      have hn_le : (n : ℝ) ≤ (B : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast le_of_lt hn_lt
      have hnR_le : (n : ℝ) * R ≤ (B : ℝ) * ((k : ℝ) + 1) * R :=
        mul_le_mul_of_nonneg_right hn_le hR0
      linarith
    have hpow_le : (2 : ℝ) ^ ((n : ℝ) * R) ≤ ((M ^ (B - 1) : ℕ) : ℝ) := by
      calc (2 : ℝ) ^ ((n : ℝ) * R)
        _ ≤ (2 : ℝ) ^ (((B - 1 : ℕ) : ℝ) * ((k : ℝ) * R_mid - 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
        _ = ((2 : ℝ) ^ ((k : ℝ) * R_mid - 1)) ^ (B - 1) := by
            rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        _ ≤ (M : ℝ) ^ (B - 1) :=
            pow_le_pow_left₀ (by positivity) hM_ge_pow (B - 1)
        _ = ((M ^ (B - 1) : ℕ) : ℝ) := by rw [Nat.cast_pow]
    have h1_le : 1 ≤ M ^ (B - 1) := Nat.one_le_pow (B - 1) M hM_pos
    have hfl_le : Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) ≤ M ^ (B - 1) :=
      Nat.floor_le_of_le hpow_le
    exact max_le h1_le hfl_le
  -- Obtain blocklength-`(B * k)` code via random coding and pad to `n`
  obtain ⟨enc₀, relay₀, dec₀, hbound⟩ :=
    bm_operational_code_existence W P B k M M_tot hB2 hk_pos hM_pos hM_tot_pos hMtot_le ε
  -- Bound the four per-block error terms by `η` each
  have ht1 : 1 - ∑ t ∈ relayTypicalSet W P k ε,
      (iidDist ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))) k).pmf (relayZipEquiv Xr X Yr k t) ≤ η := by
    have hp := hK₁ k (le_trans (le_trans (le_trans (le_max_left K₁ K₂) (le_max_left _ _)) (le_max_left _ _)) hk_ge_K)
    linarith
  have ht2 : ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * (I_relay - 4 * ε))) ≤ η := by
    have hMsub : ((M - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) :=
      le_trans (Nat.cast_le.mpr (Nat.sub_le M 1)) hM_le_pow
    have hexp_ge : ε ≤ I_relay - 4 * ε - R_mid := by
      have : I_min ≤ I_relay := min_le_left _ _
      dsimp only [ε]; linarith
    have hk3 : log2 (1 / η) / ε ≤ (k : ℝ) :=
      le_trans hK₃ (by exact_mod_cast le_trans (le_trans (le_trans (le_max_left K₃ K₄) (le_max_right _ _)) (le_max_left _ _)) hk_ge_K)
    calc ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * (I_relay - 4 * ε)))
      _ ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) * (2 : ℝ) ^ (-((k : ℝ) * (I_relay - 4 * ε))) :=
          mul_le_mul_of_nonneg_right hMsub (by positivity)
      _ = (2 : ℝ) ^ (-((k : ℝ) * (I_relay - 4 * ε - R_mid))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-((k : ℝ) * ε)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ ≤ η := ra_two_rpow_neg_le_of_ge hε_pos hη_pos hk3
  have ht3 : 1 - ∑ xy ∈ jointTypicalSet ((relayYChannel W).joint P) k ε,
      (jointIidDist ((relayYChannel W).joint P) k).pmf xy ≤ η := by
    have hp := hK₂ k (le_trans (le_trans (le_trans (le_max_right K₁ K₂) (le_max_left _ _)) (le_max_left _ _)) hk_ge_K)
    linarith
  have ht4 : ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * (I_dest - 3 * ε))) ≤ η := by
    have hMsub : ((M - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) :=
      le_trans (Nat.cast_le.mpr (Nat.sub_le M 1)) hM_le_pow
    have hexp_ge : ε ≤ I_dest - 3 * ε - R_mid := by
      have : I_min ≤ I_dest := min_le_right _ _
      dsimp only [ε]; linarith
    have hk3 : log2 (1 / η) / ε ≤ (k : ℝ) :=
      le_trans hK₃ (by exact_mod_cast le_trans (le_trans (le_trans (le_max_left K₃ K₄) (le_max_right _ _)) (le_max_left _ _)) hk_ge_K)
    calc ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * (I_dest - 3 * ε)))
      _ ≤ (2 : ℝ) ^ ((k : ℝ) * R_mid) * (2 : ℝ) ^ (-((k : ℝ) * (I_dest - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hMsub (by positivity)
      _ = (2 : ℝ) ^ (-((k : ℝ) * (I_dest - 3 * ε - R_mid))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-((k : ℝ) * ε)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ ≤ η := ra_two_rpow_neg_le_of_ge hε_pos hη_pos hk3
  have htot_le : ((B - 1 : ℕ) : ℝ) * ((η + η) + (η + η)) = δ := by
    dsimp only [η]
    field_simp [ne_of_gt hBsub_pos]
    ring
  have hcode_le_δ :
      ((1 : ℝ) / (M_tot : ℝ)) *
        ∑ m : Fin M_tot, ∑ yr : Fin (B * k) → Yr, ∑ y : Fin (B * k) → Y,
          (if dec₀ y ≠ m then
            ∏ i : Fin (B * k),
              W.trans (enc₀ m i, relay₀ i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
          else 0) ≤ δ := by
    have hmul : ((B - 1 : ℕ) : ℝ) *
        (((1 - ∑ t ∈ relayTypicalSet W P k ε,
            (iidDist ((W.joint P).map (fun z => ((z.1.2, z.1.1), z.2.2))) k).pmf (relayZipEquiv Xr X Yr k t)) +
          ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * (I_relay - 4 * ε)))) +
         ((1 - ∑ xy ∈ jointTypicalSet ((relayYChannel W).joint P) k ε,
            (jointIidDist ((relayYChannel W).joint P) k).pmf xy) +
          ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((k : ℝ) * (I_dest - 3 * ε))))) ≤
        ((B - 1 : ℕ) : ℝ) * ((η + η) + (η + η)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ht1 ht2) (add_le_add ht3 ht4))
        (le_of_lt hBsub_pos)
    linarith
  exact relay_code_pad W hBk_le_n ⟨enc₀, relay₀, dec₀, hcode_le_δ⟩

/-- **Decode-and-Forward Lower Bound on Relay Capacity** (Cover & El Gamal 1979;
    Cover & Thomas §15.10; El Gamal & Kim Theorem 16.2):
    `relayDFRate W ≤ relayCapacity W` unconditionally for every DM relay channel `W`. -/
theorem relayDFRate_le_relayCapacity (W : RelayChannel X Xr Y Yr) :
    relayDFRate W ≤ relayCapacity W := by
  by_cases hX : Nonempty X
  · by_cases hXr : Nonempty Xr
    · have hSbdd : BddAbove { R : ℝ | IsRelayAchievable W R } :=
        ⟨relayCutsetBound W, fun R hR => isRelayAchievable_le_cutsetBound W hR⟩
      have hcap0 : 0 ≤ relayCapacity W :=
        le_csSup hSbdd (isRelayAchievable_zero W)
      by_contra hlt
      push Not at hlt
      let R : ℝ := (relayCapacity W + relayDFRate W) / 2
      have hR0 : 0 ≤ R := by dsimp only [R]; linarith
      have hRlt : R < relayDFRate W := by dsimp only [R]; linarith
      have hcap_lt_R : relayCapacity W < R := by dsimp only [R]; linarith
      have hSne : { r : ℝ | ∃ P : ProbDist (X × Xr),
          let J := W.joint P
          let I_X_Yr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
          let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
          r = min I_X_Yr_given_Xr I_XXr_Y }.Nonempty :=
        ⟨_, ⟨ProbDist.uniform, rfl⟩⟩
      obtain ⟨r, ⟨P, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne hRlt
      have hach : IsRelayAchievable W R := relayDF_achievable W P hR0 hr
      have hRle : R ≤ relayCapacity W := le_csSup hSbdd hach
      linarith
    · have hemp₁ : { r : ℝ | ∃ P : ProbDist (X × Xr),
          let J := W.joint P
          let I_X_Yr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
          let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
          r = min I_X_Yr_given_Xr I_XXr_Y } = ∅ := by
        ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨P, _⟩; exact hXr ⟨(ra_nonempty_of_probDist P).some.2⟩
      have hemp₂ : { R : ℝ | IsRelayAchievable W R } = ∅ := by
        ext R; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hR
        obtain ⟨N, hN⟩ := hR.2 1 one_pos
        obtain ⟨_, relay, _, _⟩ := hN (max N 1) (le_max_left _ _)
        exact hXr ⟨relay ⟨0, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)⟩
          (fun j => (Nat.not_lt_zero _ j.2).elim)⟩
      unfold relayDFRate relayCapacity
      rw [hemp₁, hemp₂, Real.sSup_empty]
  · have hemp₁ : { r : ℝ | ∃ P : ProbDist (X × Xr),
        let J := W.joint P
        let I_X_Yr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2.2, z.1.2)))
        let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
        r = min I_X_Yr_given_Xr I_XXr_Y } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, _⟩; exact hX ⟨(ra_nonempty_of_probDist P).some.1⟩
    have hemp₂ : { R : ℝ | IsRelayAchievable W R } = ∅ := by
      ext R; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hR
      obtain ⟨N, hN⟩ := hR.2 1 one_pos
      obtain ⟨enc, _, _, _⟩ := hN (max N 1) (le_max_left _ _)
      exact hX ⟨enc ⟨0, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩
        ⟨0, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)⟩⟩
    unfold relayDFRate relayCapacity
    rw [hemp₁, hemp₂, Real.sSup_empty]

end DFAchievability

/-! ### 5. Physically Degraded Relay Channel Capacity Theorem (Cover & El Gamal 1979, Theorem 1) -/

section DegradedRelay

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- A discrete memoryless relay channel `W(y, y_r | x, x_r)` is **physically degraded**
    (Cover & El Gamal 1979, Eq. 8; Cover & Thomas §15.10; El Gamal & Kim Eq. 16.4) if
    `X — (Y_r, X_r) — Y` forms a Markov chain, i.e., there exists a DMC `D(y | y_r, x_r)` such that
    `W(y, y_r | x, x_r) = p(y_r | x, x_r) · D(y | y_r, x_r)`. -/
def IsPhysicallyDegradedRelay (W : RelayChannel X Xr Y Yr) : Prop :=
  ∃ D : DMC (Yr × Xr) Y, ∀ x xr y yr,
    W.trans (x, xr) (y, yr) = (relayYrChannel W).trans (x, xr) yr * D.trans (yr, xr) y

/-- Marginal form of physical degradedness:
    `p(y | x, x_r) = ∑_{y_r} p(y_r | x, x_r) · D(y | y_r, x_r)`. -/
lemma IsPhysicallyDegradedRelay.marginalY_eq {W : RelayChannel X Xr Y Yr}
    (hdeg : IsPhysicallyDegradedRelay W) :
    ∃ D : DMC (Yr × Xr) Y, ∀ x xr y,
      (relayYChannel W).trans (x, xr) y =
        ∑ yr : Yr, (relayYrChannel W).trans (x, xr) yr * D.trans (yr, xr) y := by
  obtain ⟨D, hD⟩ := hdeg
  exact ⟨D, fun x xr y => Finset.sum_congr rfl fun yr _ => hD x xr y yr⟩

/-- Under physical degradedness `X — (Y_r, X_r) — Y`, `I(X; Y | Y_r, X_r) = 0`. -/
private lemma degradedRelay_cmi_zero (W : RelayChannel X Xr Y Yr)
    (hdeg : IsPhysicallyDegradedRelay W) (P : ProbDist (X × Xr)) :
    condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.1, (z.2.2, z.1.2)))) = 0 := by
  classical
  obtain ⟨D, hD⟩ := hdeg
  let Q : ProbDist (X × Y × (Yr × Xr)) :=
    (W.joint P).map (fun z => (z.1.1, z.2.1, (z.2.2, z.1.2)))
  have hQ_pmf : ∀ (x : X) (y : Y) (yr : Yr) (xr : Xr),
      Q.pmf (x, y, (yr, xr)) = P.pmf (x, xr) * W.trans (x, xr) (y, yr) := by
    intro x y yr xr
    unfold Q ProbDist.map DMC.joint; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (x, xr)]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
      · rw [Finset.sum_eq_single yr]
        · simp
        · intro yr' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro xxr' _ hne
      refine Finset.sum_eq_zero fun yyr _ => ?_
      have : (xxr'.1, yyr.1, (yyr.2, xxr'.2)) ≠ (x, y, (yr, xr)) := fun h => hne (by
        have h1 := congrArg Prod.fst h
        have h2 := congrArg (fun t => t.2.2.2) h
        exact Prod.ext h1 h2)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQxz_pmf : ∀ (x : X) (yr : Yr) (xr : Xr),
      (Q.map (fun t => (t.1, t.2.2))).pmf (x, (yr, xr)) =
        P.pmf (x, xr) * (relayYrChannel W).trans (x, xr) yr := by
    intro x yr xr
    unfold ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · rw [Fintype.sum_prod_type]
      trans (∑ y : Y, P.pmf (x, xr) * W.trans (x, xr) (y, yr))
      · refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_eq_single (yr, xr)]
        · simp only [↓reduceIte]; exact hQ_pmf x y yr xr
        · intro c _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [← Finset.mul_sum]; rfl
    · intro x' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQz_pmf : ∀ (yr : Yr) (xr : Xr),
      (Q.map (fun t => t.2.2)).pmf (yr, xr) =
        ∑ x' : X, P.pmf (x', xr) * (relayYrChannel W).trans (x', xr) yr := by
    intro yr xr
    have hcomp : Q.map (fun t => t.2.2) = (Q.map (fun t => (t.1, t.2.2))).map Prod.snd := by
      rw [map_comp_eq Q (fun t => (t.1, t.2.2)) Prod.snd]; rfl
    rw [hcomp, ra_probDist_map_snd]
    unfold ProbDist.snd; dsimp only
    exact Finset.sum_congr rfl fun x' _ => hQxz_pmf x' yr xr
  have hQyz_pmf : ∀ (y : Y) (yr : Yr) (xr : Xr),
      (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, (yr, xr)) =
        (Q.map (fun t => t.2.2)).pmf (yr, xr) * D.trans (yr, xr) y := by
    intro y yr xr
    rw [hQz_pmf]
    unfold ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type]
    trans (∑ x' : X, (P.pmf (x', xr) * (relayYrChannel W).trans (x', xr) yr) * D.trans (yr, xr) y)
    · refine Finset.sum_congr rfl fun x' _ => ?_
      rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
      · rw [Finset.sum_eq_single (yr, xr)]
        · simp only [↓reduceIte]
          rw [hQ_pmf x' y yr xr, hD x' xr y yr, mul_assoc]
        · intro c _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [← Finset.sum_mul]
  rw [condMutualInfo_eq_zero_iff]
  apply ra_probDist_ext
  rintro ⟨x, y, ⟨yr, xr⟩⟩
  change Q.pmf (x, y, (yr, xr)) =
    if (Q.map (fun t => t.2.2)).pmf (yr, xr) = 0 then 0
    else (Q.map (fun t => (t.1, t.2.2))).pmf (x, (yr, xr)) *
         (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, (yr, xr)) /
         (Q.map (fun t => t.2.2)).pmf (yr, xr)
  by_cases hz : (Q.map (fun t => t.2.2)).pmf (yr, xr) = 0
  · simp only [hz, ↓reduceIte]
    have hle : Q.pmf (x, y, (yr, xr)) ≤ (Q.map (fun t => t.2.2)).pmf (yr, xr) := by
      rw [hQ_pmf, hD, hQz_pmf]
      have hD1 : D.trans (yr, xr) y ≤ 1 := by
        calc D.trans (yr, xr) y ≤ ∑ y' : Y, D.trans (yr, xr) y' :=
              Finset.single_le_sum (fun y' _ => D.nonneg (yr, xr) y') (Finset.mem_univ y)
          _ = 1 := D.sum_one (yr, xr)
      have hterm_le : P.pmf (x, xr) * ((relayYrChannel W).trans (x, xr) yr * D.trans (yr, xr) y) ≤
          P.pmf (x, xr) * (relayYrChannel W).trans (x, xr) yr := by
        have hnn : 0 ≤ P.pmf (x, xr) * (relayYrChannel W).trans (x, xr) yr :=
          mul_nonneg (P.nonneg _) ((relayYrChannel W).nonneg _ _)
        nlinarith
      exact le_trans hterm_le (Finset.single_le_sum
        (fun x' _ => mul_nonneg (P.nonneg (x', xr)) ((relayYrChannel W).nonneg (x', xr) yr))
        (Finset.mem_univ x))
    exact le_antisymm (by linarith) (Q.nonneg _)
  · simp only [hz, ↓reduceIte]
    rw [hQ_pmf, hD, hQxz_pmf, hQyz_pmf]
    field_simp [hz]

/-- Under physical degradedness, the broadcast-cut conditional mutual information collapses to
    the relay-decoding conditional mutual information:
    `I(X; Y, Y_r | X_r) = I(X; Y_r | X_r)`. -/
theorem degradedRelay_cmi_eq (W : RelayChannel X Xr Y Yr)
    (hdeg : IsPhysicallyDegradedRelay W) (P : ProbDist (X × Xr)) :
    condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))) =
      condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2.2, z.1.2))) := by
  have hchain := relay_cmi_chain_rule W P
  dsimp only at hchain
  rw [hchain, degradedRelay_cmi_zero W hdeg P, add_zero]

/-- For any physically degraded relay channel, the cut-set upper bound equals the
    Decode-and-Forward achievable rate: `relayCutsetBound W = relayDFRate W`. -/
theorem degradedRelay_cutset_eq_df (W : RelayChannel X Xr Y Yr)
    (hdeg : IsPhysicallyDegradedRelay W) :
    relayCutsetBound W = relayDFRate W := by
  unfold relayCutsetBound relayDFRate
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P, by rw [degradedRelay_cmi_eq W hdeg P]⟩
  · rintro ⟨P, rfl⟩
    exact ⟨P, by rw [degradedRelay_cmi_eq W hdeg P]⟩

/-- **Exact Capacity Theorem for the Physically Degraded Relay Channel**
    (Cover & El Gamal 1979, Theorem 1; Cover & Thomas Theorem 15.10.2; El Gamal & Kim Theorem 16.3):
    for any physically degraded discrete memoryless relay channel `W`, the operational capacity
    equals the cut-set bound:
    `C(W) = sup_{P(x, x_r)} min { I(X; Y, Y_r | X_r), I(X, X_r; Y) }`. -/
theorem degradedRelay_capacity_theorem (W : RelayChannel X Xr Y Yr)
    (hdeg : IsPhysicallyDegradedRelay W) :
    relayCapacity W = relayCutsetBound W :=
  le_antisymm (relayCapacity_le_cutsetBound W)
    (by rw [degradedRelay_cutset_eq_df W hdeg]; exact relayDFRate_le_relayCapacity W)

/-- **Exact Capacity Theorem for the Physically Degraded Relay Channel (DF Form)**
    (Cover & El Gamal 1979, Theorem 1; Cover & Thomas Theorem 15.10.2):
    `C(W) = sup_{P(x, x_r)} min { I(X; Y_r | X_r), I(X, X_r; Y) }`. -/
theorem degradedRelay_capacity_eq_df (W : RelayChannel X Xr Y Yr)
    (hdeg : IsPhysicallyDegradedRelay W) :
    relayCapacity W = relayDFRate W := by
  rw [degradedRelay_capacity_theorem W hdeg, degradedRelay_cutset_eq_df W hdeg]

end DegradedRelay

end InfoTheory.Bridge
