import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.Coding
import InfoTheory.Bridge.MethodOfTypes

/-!
# Universal Lossless Source Coding: Shtarkov NML, Krichevsky–Trofimov Mixture & Minimax Redundancy

Purely additive, kernel-verified foundational theorems for universal lossless data compression
(Cover & Thomas §§13.1–13.2; Krichevsky & Trofimov 1981; Shtarkov 1987; Gallager 1976;
Haussler 1997):

1. **Shtarkov Sum & Minimax Pointwise Regret Identity (Shtarkov 1987)**:
   - `mlProb`, `iidDist_pmf_le_mlProb`: maximum likelihood probability `P̂_x^n(x)` dominates
     every i.i.d. law `P^n(x)`.
   - `shtarkovSum`, `nmlDist`: Normalized Maximum Likelihood (NML) universal distribution.
   - `shtarkov_minimax_regret_ratio`, `shtarkov_minimax_regret`: exact minimax pointwise regret
     equals `log₂ (shtarkovSum α n)`, achieved uniformly by `nmlDist α n`.
   - `shtarkovSum_le_types`: Method-of-Types bound `shtarkovSum α n ≤ (n + 1)^{|α|}`.

2. **Krichevsky–Trofimov (1981) Sequential Universal Mixture & Sharp Regret Bounds**:
   - `ktDist`: sequential KT universal distribution predicting symbol `a` at step `t` with
     probability `(N_a(x^{<t}) + 1/2) / (t + |α|/2)`.
   - `ktDist_pmf_eq_prod`: exact exchangeable rising-factorial (Pochhammer) formula.
   - `kt_binary_ratio_le`: elementary Stirling-free binary KT bound
     `(a/n)^a (b/n)^b / ktProb2 a b ≤ 2 √n`.
   - `kt_ml_ratio_le`, `kt_pointwise_regret_le`, `kt_pointwise_regret_le_card`:
     sharp universal pointwise regret bound for every finite alphabet `α` of size `k ≥ 1` and
     every `n ≥ 1`:
     `log₂ (P^n(x) / ktDist(x)) ≤ ((k - 1)/2) log₂(n + 1) + 2` (and `≤ ((k - 1)/2) log₂(n + 1) + (k - 1)`).
   - `kt_kl_redundancy_le`: universal KL redundancy bound
     `D(P^n ‖ ktDist α n) ≤ ((k - 1)/2) log₂(n + 1) + min(2, k - 1)`.
   - `shannonEntropy_iidDist`, `universal_prefix_code_redundancy_le`: explicit universal binary
     prefix-free code achieving expected length `< n H(P) + ((k - 1)/2) log₂(n + 1) + k`
     simultaneously for all i.i.d. sources `P`.

3. **Capacity–Redundancy Theorem, Matching Lower Bound & Exact Asymptotics**:
   - `jointPrior`, `bayesMixture`, `bayes_kl_decomposition`: Compensation Identity
     `∑_j W(j) D(P_j ‖ Q) = I(Θ; Y) + D(M_W ‖ Q)`.
   - `redundancy_ge_mutualInfo`: Gallager–Haussler Capacity–Redundancy lower bound.
   - `minimaxRedundancy`, `minimaxRedundancy_le_kt`, `minimax_kl_redundancy_ge`:
     matching `((k - 1)/2) log₂ n - C_k` minimax KL redundancy lower bound for every `k ≥ 2`,
     proved via an explicit `√n`-spaced simplex grid, coordinatewise empirical-frequency rounding,
     variance bounds, and Gibbs maximum-entropy bounds on integer rounding errors.
   - `minimax_kl_redundancy_asymptotics`:
     `minimaxRedundancy α n / log₂ n → (|α| - 1) / 2` as `n → ∞` for every nonempty finite `α`.

This module is purely additive and leaves `Core/`, `Problems/`, `STATEMENT_LOCK.json`, `Known/`,
and all existing `Bridge/` files untouched.
-/

open scoped BigOperators Nat
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### Auxiliary Helpers -/

section Helpers

variable {α : Type*} [Fintype α]

private lemma log2_pos_of_gt_one {x : ℝ} (hx : 1 < x) : 0 < log2 x :=
  div_pos (Real.log_pos hx) (Real.log_pos (by norm_num))

private lemma log2_nonneg_of_ge_one {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  div_nonneg (Real.log_nonneg hx) (le_of_lt (Real.log_pos (by norm_num)))

private lemma log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt (Real.log_pos (by norm_num)))

private lemma log2_two : log2 2 = 1 :=
  div_self (ne_of_gt (Real.log_pos (by norm_num)))

private lemma log2_one : log2 1 = 0 := by
  simp [log2]

private lemma log2_pow_nat {x : ℝ} (n : ℕ) : log2 (x ^ n) = (n : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow, mul_div_assoc]

private lemma log2_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log2 (x ^ y) = y * log2 x := by
  unfold log2
  rw [Real.log_rpow hx, mul_div_assoc]

private lemma log2_sqrt {x : ℝ} (hx : 0 ≤ x) : log2 (Real.sqrt x) = log2 x / 2 := by
  unfold log2
  rw [Real.log_sqrt hx]
  ring

private lemma log2_two_rpow (t : ℝ) : log2 ((2 : ℝ) ^ t) = t := by
  rw [log2_rpow (by norm_num : (0 : ℝ) < 2), log2_two, mul_one]

omit [Fintype α] in
private lemma typeCount_eq_card_aux [DecidableEq α] {n : ℕ} (x : Fin n → α) (a : α) :
    typeCount x a = (Finset.univ.filter (fun i : Fin n => x i = a)).card := by
  unfold typeCount; congr

private lemma sum_typeCount_aux {n : ℕ} (x : Fin n → α) :
    ∑ a : α, typeCount x a = n := by
  classical
  simp_rw [typeCount_eq_card_aux]
  rw [← Finset.card_biUnion]
  · have huniv : Finset.univ.biUnion (fun a : α => Finset.univ.filter (fun i : Fin n => x i = a)) =
        (Finset.univ : Finset (Fin n)) := by
      ext i; simp
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hab (ha.symm.trans hb)

private lemma prod_comp_eq_prod_pow_typeCount_aux {n : ℕ} (x : Fin n → α) (f : α → ℝ) :
    ∏ i : Fin n, f (x i) = ∏ a : α, (f a) ^ (typeCount x a) := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset α))
    (g := x) (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [typeCount_eq_card_aux]
  trans (∏ _i ∈ Finset.univ.filter (fun i : Fin n => x i = a), f a)
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hi]
  · rw [Finset.prod_const]

omit [Fintype α] in
private lemma typeCount_self_pos {n : ℕ} (x : Fin n → α) (i : Fin n) :
    0 < typeCount x (x i) := by
  classical
  rw [typeCount_eq_card_aux]
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

private def finSuccEquiv (β : Type*) (n : ℕ) : (Fin (n + 1) → β) ≃ (Fin n → β) × β where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun ya := Fin.snoc ya.1 ya.2
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp
  right_inv ya := by
    cases ya with | mk y a =>
    apply Prod.ext
    · funext i; simp
    · simp

/-- Shannon entropy of an i.i.d. `n`-block equals `n` times the single-letter entropy:
    `H(P^n) = n H(P)`. -/
theorem shannonEntropy_iidDist (P : ProbDist α) (n : ℕ) :
    shannonEntropy (iidDist P n) = (n : ℝ) * shannonEntropy P := by
  induction n with
  | zero =>
    have hle := shannonEntropy_le_log2_card (iidDist P 0)
    have hge := shannonEntropy_nonneg (iidDist P 0)
    rw [Fintype.card_unique] at hle
    simp only [Nat.cast_one, log2_one] at hle
    simp [le_antisymm hle hge]
  | succ m ih =>
    have hmap : (iidDist P (m + 1)).map (finSuccEquiv α m) = (iidDist P m).prod P := by
      classical
      cases h1 : (iidDist P (m + 1)).map (finSuccEquiv α m) with | mk pmf1 _ _ =>
      cases h2 : (iidDist P m).prod P with | mk pmf2 _ _ =>
      congr
      funext ya
      have hp1 : pmf1 ya = ((iidDist P (m + 1)).map (finSuccEquiv α m)).pmf ya :=
        congrArg (fun Q => Q.pmf ya) h1.symm
      have hp2 : pmf2 ya = ((iidDist P m).prod P).pmf ya :=
        congrArg (fun Q => Q.pmf ya) h2.symm
      rw [hp1, hp2]
      unfold ProbDist.map ProbDist.prod iidDist
      dsimp only
      rw [Finset.sum_eq_single ((finSuccEquiv α m).symm ya)]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte, Fin.prod_univ_castSucc]
        simp [finSuccEquiv]
      · intro x _ hne
        have : finSuccEquiv α m x ≠ ya := fun h => hne ((finSuccEquiv α m).symm_apply_eq.mpr h.symm).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hent : shannonEntropy (iidDist P (m + 1)) =
        shannonEntropy ((iidDist P m).prod P) := by
      rw [← hmap, shannonEntropy_map_equiv]
    rw [hent, shannonEntropy_prod, ih, Nat.cast_add, Nat.cast_one]
    ring

end Helpers

/-! ### 1. Shtarkov Sum & Minimax Pointwise Regret Identity (Shtarkov 1987) -/

section ShtarkovNML

variable {α : Type*} [Fintype α]

/-- Maximum-likelihood i.i.d. probability of a length-`n` sequence `x`:
    `mlProb x = ∏ i, (N(x_i | x) / n) = P̂_x^n(x)` (equals `1` for `n = 0`). -/
noncomputable def mlProb {n : ℕ} (x : Fin n → α) : ℝ :=
  ∏ i : Fin n, (typeCount x (x i) : ℝ) / (n : ℝ)

/-- For `n > 0`, `mlProb x` is the probability of `x` under its own empirical distribution. -/
lemma mlProb_eq_empiricalType {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    mlProb x = (iidDist (empiricalType hn x) n).pmf x := rfl

omit [Fintype α] in
/-- `mlProb x` is strictly positive for every sequence `x : Fin n → α`. -/
theorem mlProb_pos {n : ℕ} (x : Fin n → α) : 0 < mlProb x := by
  unfold mlProb
  cases n with
  | zero => simp
  | succ m =>
    refine Finset.prod_pos fun i _ => ?_
    exact div_pos (Nat.cast_pos.mpr (typeCount_self_pos x i)) (Nat.cast_pos.mpr (Nat.succ_pos m))

/-- Maximum-likelihood optimality: for EVERY i.i.d. distribution `P` and every sequence `x`,
    `P^n(x) ≤ mlProb x`. -/
theorem iidDist_pmf_le_mlProb {n : ℕ} (P : ProbDist α) (x : Fin n → α) :
    (iidDist P n).pmf x ≤ mlProb x := by
  cases n with
  | zero =>
    simp [iidDist, mlProb]
  | succ m =>
    have hn : 0 < m + 1 := Nat.succ_pos m
    by_cases hpx : (iidDist P (m + 1)).pmf x = 0
    · rw [hpx]; exact le_of_lt (mlProb_pos x)
    · have hpos : 0 < (iidDist P (m + 1)).pmf x :=
        lt_of_le_of_ne ((iidDist P (m + 1)).nonneg x) (Ne.symm hpx)
      have hac : AbsCont (empiricalType hn x) P := by
        intro a hPa0
        by_contra hne
        have hcnt_pos : 0 < typeCount x a := by
          by_contra hle
          have h0 : typeCount x a = 0 := Nat.eq_zero_of_not_pos hle
          apply hne
          change (typeCount x a : ℝ) / ((m + 1 : ℕ) : ℝ) = 0
          simp [h0]
        classical
        rw [typeCount_eq_card_aux] at hcnt_pos
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hcnt_pos
        have hxi : x i = a := (Finset.mem_filter.mp hi).2
        have hprod0 : (iidDist P (m + 1)).pmf x = 0 := by
          unfold iidDist; dsimp only
          exact Finset.prod_eq_zero (Finset.mem_univ i) (hxi ▸ hPa0)
        linarith
      have hkl_nonneg : 0 ≤ klDivergence (empiricalType hn x) P :=
        klDivergence_nonneg (empiricalType hn x) P hac
      have hkl_self : klDivergence (empiricalType hn x) (empiricalType hn x) = 0 :=
        (klDivergence_eq_zero_iff _ _ (fun _ h => h)).mpr rfl
      rw [mlProb_eq_empiricalType hn x,
        iidDist_pmf_eq_type hn x P hac,
        iidDist_pmf_eq_type hn x (empiricalType hn x) (fun _ h => h),
        hkl_self, add_zero]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by
        have hn0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
        nlinarith)

/-- Shtarkov normalizing sum `S_n(α) = ∑_{x ∈ α^n} max_P P^n(x) = ∑_x mlProb x`. -/
noncomputable def shtarkovSum (α : Type*) [Fintype α] (n : ℕ) : ℝ :=
  ∑ x : Fin n → α, mlProb x

/-- `shtarkovSum α n ≥ 1` for every nonempty finite alphabet `α` and every `n`. -/
theorem one_le_shtarkovSum (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) :
    1 ≤ shtarkovSum α n := by
  let P : ProbDist α := ProbDist.uniform
  calc (1 : ℝ)
    _ = ∑ x : Fin n → α, (iidDist P n).pmf x := (iidDist P n).sum_one.symm
    _ ≤ ∑ x : Fin n → α, mlProb x := Finset.sum_le_sum fun x _ => iidDist_pmf_le_mlProb P x
    _ = shtarkovSum α n := rfl

/-- `shtarkovSum α n > 0` for every nonempty finite alphabet `α` and every `n`. -/
theorem shtarkovSum_pos (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) :
    0 < shtarkovSum α n :=
  lt_of_lt_of_le zero_lt_one (one_le_shtarkovSum α n)

/-- **Normalized Maximum Likelihood (NML) Universal Distribution** (Shtarkov 1987):
    `Q_NML(x) = mlProb x / shtarkovSum α n`. -/
noncomputable def nmlDist (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) : ProbDist (Fin n → α) where
  pmf := fun x => mlProb x / shtarkovSum α n
  nonneg := fun x => div_nonneg (le_of_lt (mlProb_pos x)) (le_of_lt (shtarkovSum_pos α n))
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (shtarkovSum_pos α n))

/-- Every sequence has strictly positive NML probability. -/
theorem nmlDist_pos (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) (x : Fin n → α) :
    0 < (nmlDist α n).pmf x :=
  div_pos (mlProb_pos x) (shtarkovSum_pos α n)

/-- Equalizer property of NML: the pointwise regret of `nmlDist` against the ML probability is
    identically `log₂ (shtarkovSum α n)` for every sequence `x`. -/
theorem nml_pointwise_regret_eq [Nonempty α] (n : ℕ) (x : Fin n → α) :
    log2 (mlProb x / (nmlDist α n).pmf x) = log2 (shtarkovSum α n) := by
  have hS : shtarkovSum α n ≠ 0 := ne_of_gt (shtarkovSum_pos α n)
  have hml : mlProb x ≠ 0 := ne_of_gt (mlProb_pos x)
  change log2 (mlProb x / (mlProb x / shtarkovSum α n)) = log2 (shtarkovSum α n)
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hml]

/-- NML pointwise regret upper bound: for every `P : ProbDist α` and every sequence `x` with
    `P^n(x) > 0`, `log₂ (P^n(x) / Q_NML(x)) ≤ log₂ (shtarkovSum α n)`. -/
theorem nml_pointwise_regret_le [Nonempty α] {n : ℕ} (P : ProbDist α) (x : Fin n → α)
    (hpx : 0 < (iidDist P n).pmf x) :
    log2 ((iidDist P n).pmf x / (nmlDist α n).pmf x) ≤ log2 (shtarkovSum α n) := by
  rw [← nml_pointwise_regret_eq n x]
  exact log2_le_log2 (div_pos hpx (nmlDist_pos α n x))
    (div_le_div_of_nonneg_right (iidDist_pmf_le_mlProb P x) (le_of_lt (nmlDist_pos α n x)))

/-- NML KL redundancy bound: `D(P^n ‖ Q_NML) ≤ log₂ (shtarkovSum α n)` for every `P`. -/
theorem nml_kl_redundancy_le [Nonempty α] {n : ℕ} (P : ProbDist α) :
    klDivergence (iidDist P n) (nmlDist α n) ≤ log2 (shtarkovSum α n) := by
  have hS0 : 0 ≤ log2 (shtarkovSum α n) :=
    log2_nonneg_of_ge_one (one_le_shtarkovSum α n)
  unfold klDivergence
  calc ∑ x : Fin n → α,
        (if (iidDist P n).pmf x ≤ 0 then 0
         else (iidDist P n).pmf x * log2 ((iidDist P n).pmf x / (nmlDist α n).pmf x))
    _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x * log2 (shtarkovSum α n) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : (iidDist P n).pmf x ≤ 0
        · simp only [h, ↓reduceIte]
          exact mul_nonneg ((iidDist P n).nonneg x) hS0
        · simp only [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
          exact mul_le_mul_of_nonneg_left (nml_pointwise_regret_le P x (lt_of_not_ge h))
            ((iidDist P n).nonneg x)
    _ = log2 (shtarkovSum α n) := by
        rw [← Finset.sum_mul, (iidDist P n).sum_one, one_mul]

/-- **Shtarkov Minimax Regret Converse (Ratio Form, Shtarkov 1987)**:
    for EVERY universal distribution `Q : ProbDist (Fin n → α)` (even with zero-mass atoms)
    and `n ≥ 1`, there exist a sequence `x` and an i.i.d. source `P` with
    `Q(x) · shtarkovSum α n ≤ P^n(x)`. -/
theorem shtarkov_minimax_regret_ratio [Nonempty α] {n : ℕ} (hn : 0 < n)
    (Q : ProbDist (Fin n → α)) :
    ∃ (x : Fin n → α) (P : ProbDist α),
      Q.pmf x * shtarkovSum α n ≤ (iidDist P n).pmf x := by
  have hSpos : 0 < shtarkovSum α n := shtarkovSum_pos α n
  have hex : ∃ x : Fin n → α, Q.pmf x ≤ (nmlDist α n).pmf x := by
    by_contra hall
    push Not at hall
    have hne : (Finset.univ : Finset (Fin n → α)).Nonempty := Finset.univ_nonempty
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun x _ => hall x)
    rw [(nmlDist α n).sum_one, Q.sum_one] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, empiricalType hn x, ?_⟩
  rw [← mlProb_eq_empiricalType hn x]
  have hx' : Q.pmf x ≤ mlProb x / shtarkovSum α n := hx
  exact (le_div_iff₀ hSpos).mp hx'

/-- **Shtarkov's Minimax Pointwise Regret Theorem** (Shtarkov 1987):
    for any nonempty finite alphabet `α` and blocklength `n ≥ 1`:
    1. (`nmlDist α n` achievability + equalizer) `Q_NML` is strictly positive, achieves
       `log₂ (P^n(x) / Q_NML(x)) ≤ log₂ (shtarkovSum α n)` for all `P, x` with `P^n(x) > 0`,
       and attains equality at `P = empiricalType hn x` for every `x`.
    2. (universal converse) Every strictly positive `Q : ProbDist (Fin n → α)` suffers
       pointwise regret at least `log₂ (shtarkovSum α n)` on some `(x, P)`. -/
theorem shtarkov_minimax_regret [Nonempty α] {n : ℕ} (hn : 0 < n) :
    ((∀ (P : ProbDist α) (x : Fin n → α), 0 < (iidDist P n).pmf x →
        log2 ((iidDist P n).pmf x / (nmlDist α n).pmf x) ≤ log2 (shtarkovSum α n)) ∧
     (∀ x : Fin n → α,
        log2 ((iidDist (empiricalType hn x) n).pmf x / (nmlDist α n).pmf x) =
          log2 (shtarkovSum α n))) ∧
    (∀ Q : ProbDist (Fin n → α), (∀ x, 0 < Q.pmf x) →
      ∃ (x : Fin n → α) (P : ProbDist α),
        log2 (shtarkovSum α n) ≤ log2 ((iidDist P n).pmf x / Q.pmf x)) := by
  refine ⟨⟨fun P x hpx => nml_pointwise_regret_le P x hpx,
           fun x => by rw [← mlProb_eq_empiricalType hn x]; exact nml_pointwise_regret_eq n x⟩,
          fun Q hQpos => ?_⟩
  obtain ⟨x, P, hratio⟩ := shtarkov_minimax_regret_ratio hn Q
  refine ⟨x, P, ?_⟩
  have hSpos : 0 < shtarkovSum α n := shtarkovSum_pos α n
  have hle : shtarkovSum α n ≤ (iidDist P n).pmf x / Q.pmf x :=
    (le_div_iff₀ (hQpos x)).mpr (by linarith)
  exact log2_le_log2 hSpos hle

/-- **Elementary Method-of-Types Bound on the Shtarkov Sum**:
    `shtarkovSum α n ≤ (n + 1)^{|α|}` for all `n ≥ 1`. -/
theorem shtarkovSum_le_types (α : Type*) [Fintype α] {n : ℕ} (hn : 0 < n) :
    shtarkovSum α n ≤ ((n + 1 : ℕ) : ℝ) ^ (Fintype.card α) := by
  classical
  have hpart : shtarkovSum α n =
      ∑ P ∈ typesSet α hn, ∑ x ∈ typeClass hn P, (iidDist P n).pmf x := by
    unfold shtarkovSum
    rw [← Finset.sum_fiberwise_of_maps_to (t := typesSet α hn) (g := empiricalType hn)
      (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)]
    refine Finset.sum_congr rfl fun P _ => ?_
    change ∑ x ∈ Finset.univ.filter (fun x => empiricalType hn x = P), mlProb x =
      ∑ x ∈ typeClass hn P, (iidDist P n).pmf x
    have htc : Finset.univ.filter (fun x : Fin n → α => empiricalType hn x = P) = typeClass hn P := by
      unfold typeClass; congr
    rw [htc]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← htc] at hx
    have hxP : empiricalType hn x = P := (Finset.mem_filter.mp hx).2
    rw [mlProb_eq_empiricalType hn x, hxP]
  have hle_card : shtarkovSum α n ≤ ((typesSet α hn).card : ℝ) := by
    rw [hpart]
    calc ∑ P ∈ typesSet α hn, ∑ x ∈ typeClass hn P, (iidDist P n).pmf x
      _ ≤ ∑ _P ∈ typesSet α hn, (1 : ℝ) := by
          refine Finset.sum_le_sum fun P _ => ?_
          calc ∑ x ∈ typeClass hn P, (iidDist P n).pmf x
            _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x :=
                Finset.sum_le_univ_sum_of_nonneg fun x => (iidDist P n).nonneg x
            _ = 1 := (iidDist P n).sum_one
      _ = ((typesSet α hn).card : ℝ) := by simp
  calc shtarkovSum α n
    _ ≤ ((typesSet α hn).card : ℝ) := hle_card
    _ ≤ (((n + 1) ^ (Fintype.card α) : ℕ) : ℝ) := by exact_mod_cast card_typesSet_le α hn
    _ = ((n + 1 : ℕ) : ℝ) ^ (Fintype.card α) := by push_cast; rfl

end ShtarkovNML

/-! ### 2. Krichevsky–Trofimov (1981) Universal Mixture & Sharp Regret Bounds -/

section KrichevskyTrofimov

variable {α : Type*} [Fintype α]

/-- Shifted rising factorial `∏_{j=0}^{m-1} (j + r)`. -/
def risingShift (r : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, ((j : ℝ) + r)

lemma risingShift_zero (r : ℝ) : risingShift r 0 = 1 := by
  simp [risingShift]

lemma risingShift_succ (r : ℝ) (m : ℕ) :
    risingShift r (m + 1) = risingShift r m * ((m : ℝ) + r) := by
  simp [risingShift, Finset.prod_range_succ]

lemma risingShift_pos {r : ℝ} (hr : 0 < r) (m : ℕ) : 0 < risingShift r m :=
  Finset.prod_pos fun j _ => by positivity

lemma risingShift_one_eq_factorial (m : ℕ) : risingShift 1 m = (m.factorial : ℝ) := by
  induction m with
  | zero => simp [risingShift]
  | succ k ih =>
    rw [risingShift_succ, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

lemma risingShift_add_one {r : ℝ} (hr : 0 < r) (n : ℕ) :
    risingShift (r + 1) n = (((n : ℝ) + r) / r) * risingShift r n := by
  induction n with
  | zero =>
    simp [risingShift_zero, div_self (ne_of_gt hr)]
  | succ m ih =>
    rw [risingShift_succ, risingShift_succ, ih, Nat.cast_add, Nat.cast_one]
    have hrne : r ≠ 0 := ne_of_gt hr
    have hmne : (m : ℝ) + r ≠ 0 := by positivity
    field_simp [hrne, hmne]
    ring

/-- Prefix count `N(a | x^{<t}) = |{j < t | x_j = a}|` of symbol `a` strictly before index `t`. -/
noncomputable def prefixCount {n : ℕ} (x : Fin n → α) (t : Fin n) (a : α) : ℕ :=
  by classical exact (Finset.univ.filter (fun j : Fin n => j.1 < t.1 ∧ x j = a)).card

/-- Sequential Krichevsky–Trofimov transition probability at position `t`:
    `ktStep x t = (N(x_t | x^{<t}) + 1/2) / (t + |α|/2)`. -/
noncomputable def ktStep {n : ℕ} (x : Fin n → α) (t : Fin n) : ℝ :=
  ((prefixCount x t (x t) : ℝ) + 1 / 2) / ((t.1 : ℝ) + (Fintype.card α : ℝ) / 2)

omit [Fintype α] in
private lemma prefixCount_snoc_castSucc {n : ℕ} (y : Fin n → α) (a : α) (i : Fin n) (b : α) :
    prefixCount (Fin.snoc (α := fun _ => α) y a) i.castSucc b = prefixCount y i b := by
  classical
  unfold prefixCount
  refine Finset.card_bij
    (fun (j : Fin (n + 1)) (hj : j ∈ Finset.univ.filter (fun j : Fin (n + 1) =>
        j.1 < i.castSucc.1 ∧ Fin.snoc (α := fun _ => α) y a j = b)) =>
      (⟨j.1, lt_trans (Finset.mem_filter.mp hj).2.1 i.2⟩ : Fin n)) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have hlt : j.1 < n := lt_trans hj.1 i.2
    have hsnoc : Fin.snoc (α := fun _ => α) y a j = y ⟨j.1, hlt⟩ := by
      have h1 : Fin.snoc (α := fun _ => α) y a j =
          Fin.snoc (α := fun _ => α) y a (⟨j.1, hlt⟩ : Fin n).castSucc :=
        congrArg (Fin.snoc (α := fun _ => α) y a) (Fin.ext rfl)
      exact h1.trans (Fin.snoc_castSucc (α := fun _ => α) a y ⟨j.1, hlt⟩)
    exact hsnoc.symm.trans hj.2
  · intro j₁ _ j₂ _ h
    exact Fin.ext (congrArg (fun k : Fin n => k.1) h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨k.castSucc, ?_, by ext; rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.snoc_castSucc]
    exact hk

omit [Fintype α] in
private lemma prefixCount_snoc_last {n : ℕ} (y : Fin n → α) (a b : α) :
    prefixCount (Fin.snoc (α := fun _ => α) y a) (Fin.last n) b = typeCount y b := by
  classical
  unfold prefixCount typeCount
  refine Finset.card_bij
    (fun (j : Fin (n + 1)) (hj : j ∈ Finset.univ.filter (fun j : Fin (n + 1) =>
        j.1 < (Fin.last n).1 ∧ Fin.snoc (α := fun _ => α) y a j = b)) =>
      (⟨j.1, (Finset.mem_filter.mp hj).2.1⟩ : Fin n)) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last] at hj ⊢
    have hsnoc : Fin.snoc (α := fun _ => α) y a j = y ⟨j.1, hj.1⟩ := by
      have h1 : Fin.snoc (α := fun _ => α) y a j =
          Fin.snoc (α := fun _ => α) y a (⟨j.1, hj.1⟩ : Fin n).castSucc :=
        congrArg (Fin.snoc (α := fun _ => α) y a) (Fin.ext rfl)
      exact h1.trans (Fin.snoc_castSucc (α := fun _ => α) a y ⟨j.1, hj.1⟩)
    exact hsnoc.symm.trans hj.2
  · intro j₁ _ j₂ _ h
    exact Fin.ext (congrArg (fun k : Fin n => k.1) h)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨k.castSucc, ?_, by ext; rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_last,
      Fin.snoc_castSucc]
    exact ⟨k.2, hk⟩

omit [Fintype α] in
private lemma typeCount_snoc [DecidableEq α] {n : ℕ} (y : Fin n → α) (a b : α) :
    typeCount (Fin.snoc (α := fun _ => α) y a) b = typeCount y b + (if a = b then 1 else 0) := by
  rw [typeCount_eq_card_aux, typeCount_eq_card_aux]
  have hsplit : Finset.univ.filter (fun j : Fin (n + 1) => Fin.snoc (α := fun _ => α) y a j = b) =
      (Finset.univ.filter (fun j : Fin (n + 1) => j.1 < n ∧ Fin.snoc (α := fun _ => α) y a j = b)) ∪
      (Finset.univ.filter (fun j : Fin (n + 1) => j = Fin.last n ∧ Fin.snoc (α := fun _ => α) y a j = b)) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_cases hlt : j.1 < n
      · exact Or.inl ⟨hlt, h⟩
      · exact Or.inr ⟨Fin.ext (by simp only [Fin.val_last]; omega), h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have hdisj : Disjoint
      (Finset.univ.filter (fun j : Fin (n + 1) => j.1 < n ∧ Fin.snoc (α := fun _ => α) y a j = b))
      (Finset.univ.filter (fun j : Fin (n + 1) => j = Fin.last n ∧ Fin.snoc (α := fun _ => α) y a j = b)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h2.1, Fin.val_last] at h1
    exact lt_irrefl _ h1.1
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  congr 1
  · have h := prefixCount_snoc_last y a b
    unfold prefixCount at h
    rw [typeCount_eq_card_aux] at h
    convert h using 2
    · ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
  · by_cases hab : a = b
    · subst hab
      have hsing : Finset.univ.filter (fun j : Fin (n + 1) => j = Fin.last n ∧ Fin.snoc (α := fun _ => α) y a j = a) =
          {Fin.last n} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro rfl; exact ⟨rfl, by simp⟩
      rw [hsing, Finset.card_singleton]
      simp
    · have hemp : Finset.univ.filter (fun j : Fin (n + 1) => j = Fin.last n ∧ Fin.snoc (α := fun _ => α) y a j = b) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, h⟩
        rw [Fin.snoc_last] at h
        exact hab h
      rw [hemp, Finset.card_empty]
      simp [hab]

private lemma prod_ktStep_snoc {n : ℕ} (y : Fin n → α) (a : α) :
    ∏ t : Fin (n + 1), ktStep (Fin.snoc y a) t =
      (∏ t : Fin n, ktStep y t) *
        (((typeCount y a : ℝ) + 1 / 2) / ((n : ℝ) + (Fintype.card α : ℝ) / 2)) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    unfold ktStep
    rw [Fin.snoc_castSucc, prefixCount_snoc_castSucc]
    rfl
  · unfold ktStep
    rw [Fin.snoc_last, prefixCount_snoc_last, Fin.val_last]

private lemma sum_prod_ktStep_one [Nonempty α] (n : ℕ) :
    ∑ x : Fin n → α, ∏ t : Fin n, ktStep x t = 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsum : ∑ x : Fin (m + 1) → α, ∏ t : Fin (m + 1), ktStep x t =
        ∑ ya : (Fin m → α) × α, ∏ t : Fin (m + 1), ktStep (Fin.snoc ya.1 ya.2) t := by
      refine Fintype.sum_equiv (finSuccEquiv α m) _ _ fun x => ?_
      change _ = ∏ t : Fin (m + 1), ktStep ((finSuccEquiv α m).symm (finSuccEquiv α m x)) t
      rw [Equiv.symm_apply_apply]
    rw [hsum, Fintype.sum_prod_type]
    simp_rw [prod_ktStep_snoc, ← Finset.mul_sum]
    have hinner : ∀ y : Fin m → α,
        ∑ a : α, ((typeCount y a : ℝ) + 1 / 2) / ((m : ℝ) + (Fintype.card α : ℝ) / 2) = 1 := by
      intro y
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Nat.cast_sum, sum_typeCount_aux,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hden : (m : ℝ) + (Fintype.card α : ℝ) / 2 ≠ 0 := by
        have hk : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
        linarith
      have hnum : (m : ℝ) + (Fintype.card α : ℝ) * (1 / 2 : ℝ) =
          (m : ℝ) + (Fintype.card α : ℝ) / 2 := by ring
      rw [hnum, div_self hden]
    simp_rw [hinner, mul_one]
    exact ih

/-- **Krichevsky–Trofimov (1981) Sequential Universal Mixture** on `Fin n → α`:
    defined sequentially via `P_KT(x_t = a | x^{<t}) = (N(a | x^{<t}) + 1/2) / (t + |α|/2)`. -/
noncomputable def ktDist (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) : ProbDist (Fin n → α) where
  pmf := fun x => ∏ t : Fin n, ktStep x t
  nonneg := fun x => Finset.prod_nonneg fun t _ => by
    unfold ktStep
    have hk : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    positivity
  sum_one := sum_prod_ktStep_one n

/-- Every sequence has strictly positive KT probability. -/
theorem ktDist_pos (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) (x : Fin n → α) :
    0 < (ktDist α n).pmf x := by
  unfold ktDist; dsimp only
  exact Finset.prod_pos fun t _ => by
    unfold ktStep
    have hk : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    positivity

/-- **Exact Exchangeable Rising-Factorial Formula for KT (Krichevsky & Trofimov 1981)**:
    `P_KT(x) = (∏_{a ∈ α} ∏_{j=0}^{N(a|x)-1} (j + 1/2)) / (∏_{t=0}^{n-1} (t + |α|/2))`. -/
theorem ktDist_pmf_eq_prod [Nonempty α] (n : ℕ) (x : Fin n → α) :
    (ktDist α n).pmf x =
      (∏ a : α, risingShift (1 / 2) (typeCount x a)) /
        risingShift ((Fintype.card α : ℝ) / 2) n := by
  induction n with
  | zero =>
    have hcnt0 : ∀ a : α, typeCount x a = 0 := by
      intro a
      classical
      rw [typeCount_eq_card_aux]
      simp
    simp [ktDist, hcnt0, risingShift_zero]
  | succ m ih =>
    let y : Fin m → α := fun i => x i.castSucc
    let a : α := x (Fin.last m)
    have hx : x = Fin.snoc (α := fun _ => α) y a := ((finSuccEquiv α m).left_inv x).symm
    rw [hx]
    change ∏ t : Fin (m + 1), ktStep (Fin.snoc (α := fun _ => α) y a) t = _
    rw [prod_ktStep_snoc, ← show (ktDist α m).pmf y = ∏ t : Fin m, ktStep y t from rfl, ih y]
    rw [risingShift_succ]
    have hnum : ∏ b : α, risingShift (1 / 2) (typeCount (Fin.snoc (α := fun _ => α) y a) b) =
        (∏ b : α, risingShift (1 / 2) (typeCount y b)) * ((typeCount y a : ℝ) + 1 / 2) := by
      classical
      rw [← Finset.mul_prod_erase Finset.univ (fun b => risingShift (1 / 2) (typeCount (Fin.snoc (α := fun _ => α) y a) b))
          (Finset.mem_univ a),
        ← Finset.mul_prod_erase Finset.univ (fun b => risingShift (1 / 2) (typeCount y b))
          (Finset.mem_univ a)]
      have hother : ∏ b ∈ Finset.univ.erase a, risingShift (1 / 2) (typeCount (Fin.snoc (α := fun _ => α) y a) b) =
          ∏ b ∈ Finset.univ.erase a, risingShift (1 / 2) (typeCount y b) := by
        refine Finset.prod_congr rfl fun b hb => ?_
        have hne : a ≠ b := (Finset.mem_erase.mp hb).1.symm
        rw [typeCount_snoc, ite_eq_right_iff.mpr (fun h => absurd h hne), add_zero]
      rw [hother, typeCount_snoc, ite_eq_left_iff.mpr (fun h => absurd rfl h), risingShift_succ]
      ring
    rw [hnum, div_mul_div_comm]

/-! #### Elementary Stirling-Free Rising-Factorial Inequalities -/

/-- Auxiliary calculus inequality: for `0 < u < 1`,
    `(1 + u) log(1 + u) - (1 - u) log(1 - u) ≤ 2 u`. -/
private lemma aux_log_ineq_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (1 + u) * Real.log (1 + u) - (1 - u) * Real.log (1 - u) ≤ 2 * u := by
  let g : ℝ → ℝ := fun t => 2 * t - (1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) u,
      HasDerivAt g (-Real.log (1 + t) - Real.log (1 - t)) t := by
    intro t ht
    have h1pt : 0 < 1 + t := by linarith [ht.1]
    have h1mt : 0 < 1 - t := by linarith [ht.2]
    have hd1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have hadd : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id t)
    have hlog1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      simpa [div_eq_mul_inv] using hadd.log (ne_of_gt h1pt)
    have hd2 : HasDerivAt (fun s : ℝ => (1 + s) * Real.log (1 + s))
        (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t))) t :=
      hadd.mul hlog1
    have hsub : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
    have hlog2 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
      simpa [div_eq_mul_inv] using hsub.log (ne_of_gt h1mt)
    have hd3 : HasDerivAt (fun s : ℝ => (1 - s) * Real.log (1 - s))
        ((-1) * Real.log (1 - t) + (1 - t) * (-1 / (1 - t))) t :=
      hsub.mul hlog2
    convert (hd1.sub hd2).add hd3 using 1
    field_simp [ne_of_gt h1pt, ne_of_gt h1mt]
    ring
  have hcont : ContinuousOn g (Set.Icc 0 u) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g
    (fun t => -Real.log (1 + t) - Real.log (1 - t)) hu0 hcont
    (fun t ht => hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have h1pc : 0 < 1 + c := by linarith [hc.1]
  have h1mc : 0 < 1 - c := by linarith [hc.2]
  have hprod_le : (1 + c) * (1 - c) ≤ 1 := by nlinarith [sq_nonneg c]
  have hlog_nonpos : Real.log ((1 + c) * (1 - c)) ≤ 0 :=
    Real.log_nonpos (le_of_lt (mul_pos h1pc h1mc)) hprod_le
  rw [Real.log_mul (ne_of_gt h1pc) (ne_of_gt h1mc)] at hlog_nonpos
  have hge : 0 ≤ -Real.log (1 + c) - Real.log (1 - c) := by linarith
  rw [hslope] at hge
  have hgu : 0 ≤ g u - g 0 := by
    have hmul := mul_nonneg hge (le_of_lt hu0)
    rwa [sub_zero, div_mul_cancel₀ _ (ne_of_gt hu0)] at hmul
  have hg0 : g 0 = 0 := by simp [g]
  dsimp only [g] at hgu hg0
  linarith

/-- Auxiliary calculus inequality: for `0 < u < 1`,
    `2 u ≤ log(1 + u) - log(1 - u)`. -/
private lemma aux_log_ineq_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    2 * u ≤ Real.log (1 + u) - Real.log (1 - u) := by
  let h : ℝ → ℝ := fun t => Real.log (1 + t) - Real.log (1 - t) - 2 * t
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) u,
      HasDerivAt h (1 / (1 + t) + 1 / (1 - t) - 2) t := by
    intro t ht
    have h1pt : 0 < 1 + t := by linarith [ht.1]
    have h1mt : 0 < 1 - t := by linarith [ht.2]
    have hadd : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id t)
    have hlog1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      simpa [div_eq_mul_inv] using hadd.log (ne_of_gt h1pt)
    have hsub : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
    have hlog2 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
      simpa [div_eq_mul_inv] using hsub.log (ne_of_gt h1mt)
    have hd3 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    convert (hlog1.sub hlog2).sub hd3 using 1
    ring
  have hcont : ContinuousOn h (Set.Icc 0 u) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h
    (fun t => 1 / (1 + t) + 1 / (1 - t) - 2) hu0 hcont
    (fun t ht => hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have h1pc : 0 < 1 + c := by linarith [hc.1]
  have h1mc : 0 < 1 - c := by linarith [hc.2]
  have hge : 0 ≤ 1 / (1 + c) + 1 / (1 - c) - 2 := by
    have heq : 1 / (1 + c) + 1 / (1 - c) - 2 = 2 * c ^ 2 / ((1 + c) * (1 - c)) := by
      field_simp [ne_of_gt h1pc, ne_of_gt h1mc]
      ring
    rw [heq]
    exact div_nonneg (by positivity) (le_of_lt (mul_pos h1pc h1mc))
  rw [hslope] at hge
  have hhu : 0 ≤ h u - h 0 := by
    have hmul := mul_nonneg hge (le_of_lt hu0)
    rwa [sub_zero, div_mul_cancel₀ _ (ne_of_gt hu0)] at hmul
  have hh0 : h 0 = 0 := by simp [h]
  dsimp only [h] at hhu hh0
  linarith

/-- Key monotonicity step: for `m ≥ 1`,
    `(m + 1)^{m + 1} / (e^{m + 1} · risingShift (1/2) (m + 1)) ≤ m^m / (e^m · risingShift (1/2) m)`. -/
private lemma pow_div_exp_risingHalf_antitone {m : ℕ} (hm : 1 ≤ m) :
    ((m + 1 : ℕ) : ℝ) ^ (m + 1) / (Real.exp (m + 1 : ℕ) * risingShift (1 / 2) (m + 1)) ≤
      (m : ℝ) ^ m / (Real.exp m * risingShift (1 / 2) m) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hmhalf : (0 : ℝ) < (m : ℝ) + 1 / 2 := by linarith
  have h2m1pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  set u : ℝ := 1 / (2 * (m : ℝ) + 1)
  have hu0 : 0 < u := div_pos one_pos h2m1pos
  have hu1 : u < 1 := by
    rw [div_lt_one h2m1pos]
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hineq := aux_log_ineq_upper hu0 hu1
  have h1pu : 1 + u = ((m : ℝ) + 1) / ((m : ℝ) + 1 / 2) := by
    dsimp only [u]; field_simp [ne_of_gt h2m1pos, ne_of_gt hmhalf]; ring
  have h1mu : 1 - u = (m : ℝ) / ((m : ℝ) + 1 / 2) := by
    dsimp only [u]; field_simp [ne_of_gt h2m1pos, ne_of_gt hmhalf]; ring
  rw [h1pu, h1mu] at hineq
  have hmul := mul_le_mul_of_nonneg_left hineq (le_of_lt hmhalf)
  have hlhs : ((m : ℝ) + 1 / 2) * (((m : ℝ) + 1) / ((m : ℝ) + 1 / 2) *
      Real.log (((m : ℝ) + 1) / ((m : ℝ) + 1 / 2)) -
      (m : ℝ) / ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) / ((m : ℝ) + 1 / 2))) =
      ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) - (m : ℝ) * Real.log (m : ℝ) -
        Real.log ((m : ℝ) + 1 / 2) := by
    rw [Real.log_div (ne_of_gt hm1pos) (ne_of_gt hmhalf),
      Real.log_div (ne_of_gt hmpos) (ne_of_gt hmhalf)]
    field_simp [ne_of_gt hmhalf]
    ring
  have hrhs : ((m : ℝ) + 1 / 2) * (2 * u) = 1 := by
    dsimp only [u]; field_simp [ne_of_gt h2m1pos]
  rw [hlhs, hrhs] at hmul
  have hlog_step : Real.log (((m : ℝ) + 1) ^ (m + 1) / ((m : ℝ) ^ m * ((m : ℝ) + 1 / 2))) ≤ 1 := by
    rw [Real.log_div (ne_of_gt (pow_pos hm1pos _)) (ne_of_gt (mul_pos (pow_pos hmpos _) hmhalf)),
      Real.log_mul (ne_of_gt (pow_pos hmpos _)) (ne_of_gt hmhalf),
      Real.log_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    linarith
  have hexp_step : ((m : ℝ) + 1) ^ (m + 1) / ((m : ℝ) ^ m * ((m : ℝ) + 1 / 2)) ≤ Real.exp 1 := by
    have hpos_arg : 0 < ((m : ℝ) + 1) ^ (m + 1) / ((m : ℝ) ^ m * ((m : ℝ) + 1 / 2)) := by positivity
    rw [← Real.exp_log hpos_arg]
    exact Real.exp_le_exp.mpr hlog_step
  have hcore : ((m : ℝ) + 1) ^ (m + 1) ≤ Real.exp 1 * ((m : ℝ) ^ m * ((m : ℝ) + 1 / 2)) := by
    rwa [div_le_iff₀ (mul_pos (pow_pos hmpos _) hmhalf)] at hexp_step
  have hris : 0 < risingShift (1 / 2) m := risingShift_pos (by norm_num) m
  have hexpm : 0 < Real.exp m := Real.exp_pos _
  have hexp1 : 0 < Real.exp 1 := Real.exp_pos _
  rw [risingShift_succ, Nat.cast_add, Nat.cast_one, Real.exp_add]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul_core := mul_le_mul_of_nonneg_right hcore (le_of_lt (mul_pos hexpm hris))
  linarith

/-- For every `m ≥ 1`, `m^m / (e^m · risingShift (1/2) m) ≤ 2 / e`. -/
private lemma pow_div_exp_risingHalf_le_two_div_e {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ m / (Real.exp m * risingShift (1 / 2) m) ≤ 2 / Real.exp 1 := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp only [Nat.cast_one, pow_one, risingShift_succ, risingShift_zero,
        Nat.cast_zero, zero_add, one_mul]
      have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
      field_simp [he]
      norm_num
    | succ j =>
      exact le_trans (pow_div_exp_risingHalf_antitone (Nat.succ_le_succ (Nat.zero_le j)))
        (ih (Nat.succ_le_succ (Nat.zero_le j)))

/-- For every `m : ℕ` (including `m = 0`), `m^m / (e^m · risingShift (1/2) m) ≤ 1`. -/
private lemma pow_div_exp_risingHalf_le_one (m : ℕ) :
    (m : ℝ) ^ m / (Real.exp m * risingShift (1 / 2) m) ≤ 1 := by
  cases m with
  | zero => simp [risingShift_zero]
  | succ k =>
    have h1 := pow_div_exp_risingHalf_le_two_div_e (Nat.succ_le_succ (Nat.zero_le k))
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : 2 / Real.exp 1 ≤ 1 := (div_le_one (Real.exp_pos 1)).mpr he2
    exact le_trans h1 h2

/-- Elementary Stirling upper bound: for all `n ≥ 1`, `e^n · n! / n^n ≤ e · √n`. -/
private lemma exp_mul_fact_div_pow_le {n : ℕ} (hn : 1 ≤ n) :
    Real.exp n * (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Real.exp 1 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp
    | succ k =>
      set j : ℕ := k + 1
      have hj : 1 ≤ j := Nat.succ_le_succ (Nat.zero_le k)
      have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
      have hj1pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
      have h2j1pos : (0 : ℝ) < 2 * (j : ℝ) + 1 := by linarith
      set u : ℝ := 1 / (2 * (j : ℝ) + 1)
      have hu0 : 0 < u := div_pos one_pos h2j1pos
      have hu1 : u < 1 := by
        rw [div_lt_one h2j1pos]
        have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        linarith
      have hineq := aux_log_ineq_lower hu0 hu1
      have hratio_u : (1 + u) / (1 - u) = ((j : ℝ) + 1) / (j : ℝ) := by
        dsimp only [u]
        have hne1 : 1 - 1 / (2 * (j : ℝ) + 1) ≠ 0 := by
          have : 1 / (2 * (j : ℝ) + 1) < 1 := hu1
          linarith
        field_simp [ne_of_gt h2j1pos, ne_of_gt hjpos]
        ring
      have hlog_ge : 1 ≤ ((j : ℝ) + 1 / 2) * Real.log (((j : ℝ) + 1) / (j : ℝ)) := by
        rw [← hratio_u, Real.log_div (by linarith) (by linarith)]
        have hmul := mul_le_mul_of_nonneg_left hineq (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1 / 2)
        have hlhs : ((j : ℝ) + 1 / 2) * (2 * u) = 1 := by
          dsimp only [u]; field_simp [ne_of_gt h2j1pos]
        linarith
      have hstep_exp : Real.exp 1 ≤ (((j : ℝ) + 1) / (j : ℝ)) ^ ((j : ℝ) + 1 / 2) := by
        rw [Real.rpow_def_of_pos (div_pos hj1pos hjpos), mul_comm]
        exact Real.exp_le_exp.mpr hlog_ge
      have hstep_split : (((j : ℝ) + 1) / (j : ℝ)) ^ ((j : ℝ) + 1 / 2) =
          (((j : ℝ) + 1) / (j : ℝ)) ^ j * Real.sqrt (((j : ℝ) + 1) / (j : ℝ)) := by
        rw [Real.rpow_add (div_pos hj1pos hjpos), Real.rpow_natCast, Real.sqrt_eq_rpow]
      rw [hstep_split, div_pow, Real.sqrt_div (le_of_lt hj1pos)] at hstep_exp
      have hstep_mul : Real.exp 1 * (j : ℝ) ^ j * Real.sqrt (j : ℝ) ≤
          ((j : ℝ) + 1) ^ j * Real.sqrt ((j : ℝ) + 1) := by
        have hden : 0 < (j : ℝ) ^ j * Real.sqrt (j : ℝ) :=
          mul_pos (pow_pos hjpos _) (Real.sqrt_pos.mpr hjpos)
        have hrew : ((j : ℝ) + 1) ^ j / (j : ℝ) ^ j * (Real.sqrt ((j : ℝ) + 1) / Real.sqrt (j : ℝ)) =
            (((j : ℝ) + 1) ^ j * Real.sqrt ((j : ℝ) + 1)) / ((j : ℝ) ^ j * Real.sqrt (j : ℝ)) := by
          ring
        rw [hrew, le_div_iff₀ hden] at hstep_exp
        linarith
      have hih := ih hj
      have hih_mul : Real.exp j * (j.factorial : ℝ) ≤
          Real.exp 1 * Real.sqrt (j : ℝ) * (j : ℝ) ^ j := by
        rwa [div_le_iff₀ (pow_pos hjpos _)] at hih
      have hj1_cast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
      change Real.exp ((j + 1 : ℕ) : ℝ) * ((j + 1).factorial : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (j + 1) ≤
        Real.exp 1 * Real.sqrt ((j + 1 : ℕ) : ℝ)
      rw [hj1_cast, Real.exp_add, Nat.factorial_succ, Nat.cast_mul, hj1_cast,
        pow_succ, div_le_iff₀ (mul_pos (pow_pos hj1pos _) hj1pos)]
      have hcomb : Real.exp j * Real.exp 1 * (((j : ℝ) + 1) * (j.factorial : ℝ)) =
          Real.exp 1 * ((j : ℝ) + 1) * (Real.exp j * (j.factorial : ℝ)) := by ring
      rw [hcomb]
      calc Real.exp 1 * ((j : ℝ) + 1) * (Real.exp j * (j.factorial : ℝ))
        _ ≤ Real.exp 1 * ((j : ℝ) + 1) * (Real.exp 1 * Real.sqrt (j : ℝ) * (j : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left hih_mul (by positivity)
        _ = Real.exp 1 * ((j : ℝ) + 1) * (Real.exp 1 * (j : ℝ) ^ j * Real.sqrt (j : ℝ)) := by ring
        _ ≤ Real.exp 1 * ((j : ℝ) + 1) * (((j : ℝ) + 1) ^ j * Real.sqrt ((j : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hstep_mul (by positivity)
        _ = Real.exp 1 * Real.sqrt ((j : ℝ) + 1) * (((j : ℝ) + 1) ^ j * ((j : ℝ) + 1)) := by ring

/-- Elementary Wallis upper bound: `(risingShift (1/2) n / n!)^2 ≤ 1 / (2n + 1)`. -/
private lemma risingHalf_div_fact_sq_le (n : ℕ) :
    (risingShift (1 / 2) n / (n.factorial : ℝ)) ^ 2 ≤ 1 / (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp [risingShift_zero]
  | succ m ih =>
    rw [risingShift_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hsplit : risingShift (1 / 2) m * ((m : ℝ) + 1 / 2) / (((m : ℝ) + 1) * (m.factorial : ℝ)) =
        (risingShift (1 / 2) m / (m.factorial : ℝ)) * (((m : ℝ) + 1 / 2) / ((m : ℝ) + 1)) := by
      rw [mul_comm ((m : ℝ) + 1), div_mul_div_comm]
    rw [hsplit, mul_pow]
    have hstep : 1 / (2 * (m : ℝ) + 1) * (((m : ℝ) + 1 / 2) / ((m : ℝ) + 1)) ^ 2 ≤
        1 / (2 * ((m : ℝ) + 1) + 1) := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : 0 < 2 * (m : ℝ) + 1 := by linarith
      have h2 : 0 < (m : ℝ) + 1 := by linarith
      have h3 : 0 < 2 * ((m : ℝ) + 1) + 1 := by linarith
      rw [div_pow, ← mul_div_mul_comm, one_mul, div_le_div_iff₀ (by positivity) h3]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right ih (sq_nonneg _)) hstep

/-- Elementary Wallis upper bound: `risingShift (1/2) n ≤ n! / √(2n + 1)`. -/
private lemma risingHalf_le_fact_div_sqrt (n : ℕ) :
    risingShift (1 / 2) n ≤ (n.factorial : ℝ) / Real.sqrt (2 * (n : ℝ) + 1) := by
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hris : 0 ≤ risingShift (1 / 2) n := le_of_lt (risingShift_pos (by norm_num) n)
  have hsq := risingHalf_div_fact_sq_le n
  have hle : risingShift (1 / 2) n / (n.factorial : ℝ) ≤ 1 / Real.sqrt (2 * (n : ℝ) + 1) := by
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (div_nonneg hris (le_of_lt hfact)), Real.sqrt_div (by norm_num), Real.sqrt_one] at hsqrt
    exact hsqrt
  rw [div_le_iff₀ hfact] at hle
  linarith [show 1 / Real.sqrt (2 * (n : ℝ) + 1) * (n.factorial : ℝ) =
    (n.factorial : ℝ) / Real.sqrt (2 * (n : ℝ) + 1) by ring]

/-- Elementary Wallis lower bound: `(n! / risingShift (1/2) n)^2 ≤ 4n` for `n ≥ 1`. -/
private lemma fact_div_risingHalf_sq_le {n : ℕ} (hn : 1 ≤ n) :
    ((n.factorial : ℝ) / risingShift (1 / 2) n) ^ 2 ≤ 4 * (n : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp only [Nat.factorial_one, Nat.cast_one, risingShift_succ, risingShift_zero,
        Nat.cast_zero, zero_add, one_mul]
      norm_num
    | succ k =>
      set j : ℕ := k + 1
      have hj : 1 ≤ j := Nat.succ_le_succ (Nat.zero_le k)
      have hih := ih hj
      change (((j + 1).factorial : ℝ) / risingShift (1 / 2) (j + 1)) ^ 2 ≤ 4 * ((j + 1 : ℕ) : ℝ)
      rw [Nat.factorial_succ, Nat.cast_mul, risingShift_succ, Nat.cast_add, Nat.cast_one]
      have hsplit : (((j : ℝ) + 1) * (j.factorial : ℝ)) /
          (risingShift (1 / 2) j * ((j : ℝ) + 1 / 2)) =
          ((j.factorial : ℝ) / risingShift (1 / 2) j) * (((j : ℝ) + 1) / ((j : ℝ) + 1 / 2)) := by
        rw [mul_comm ((j : ℝ) + 1), div_mul_div_comm]
      rw [hsplit, mul_pow]
      have hstep : 4 * (j : ℝ) * (((j : ℝ) + 1) / ((j : ℝ) + 1 / 2)) ^ 2 ≤ 4 * ((j : ℝ) + 1) := by
        have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
        have hden : 0 < ((j : ℝ) + 1 / 2) ^ 2 := by positivity
        rw [div_pow, mul_div_assoc', div_le_iff₀ hden]
        nlinarith
      exact le_trans (mul_le_mul_of_nonneg_right hih (sq_nonneg _)) hstep

/-- Binary KT probability for a sequence with `a` ones and `b` zeros:
    `ktProb2 a b = risingShift (1/2) a * risingShift (1/2) b / (a + b)!`. -/
noncomputable def ktProb2 (a b : ℕ) : ℝ :=
  risingShift (1 / 2) a * risingShift (1 / 2) b / ((a + b).factorial : ℝ)

lemma ktProb2_pos (a b : ℕ) : 0 < ktProb2 a b :=
  div_pos (mul_pos (risingShift_pos (by norm_num) a) (risingShift_pos (by norm_num) b))
    (Nat.cast_pos.mpr (Nat.factorial_pos (a + b)))

/-- **Sharp Elementary Binary Krichevsky–Trofimov Inequality** (Krichevsky & Trofimov 1981,
    Lemma 1; Willems–Shtarkov–Tjalkens 1995):
    for all `a, b : ℕ` with `n = a + b ≥ 1`,
    `(a / n)^a (b / n)^b / ktProb2 a b ≤ 2 √n` (hence `≤ 2 √(n + 1)`). -/
theorem kt_binary_ratio_le {a b n : ℕ} (hab : a + b = n) (hn : 1 ≤ n) :
    ((a : ℝ) / (n : ℝ)) ^ a * ((b : ℝ) / (n : ℝ)) ^ b / ktProb2 a b ≤
      2 * Real.sqrt (n : ℝ) := by
  subst hab
  have hnpos : (0 : ℝ) < ((a + b : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfact_pos : (0 : ℝ) < ((a + b).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hra : 0 < risingShift (1 / 2) a := risingShift_pos (by norm_num) a
  have hrb : 0 < risingShift (1 / 2) b := risingShift_pos (by norm_num) b
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- Boundary cases a = 0 or b = 0 via the Wallis lower bound `(n! / risingHalf n)² ≤ 4n`
  by_cases ha : a = 0
  · subst ha
    have hbpos : (0 : ℝ) < (b : ℝ) := by simpa using hnpos
    have hbfact : (0 : ℝ) < (b.factorial : ℝ) := by simpa using hfact_pos
    simp only [Nat.zero_add, Nat.cast_zero, zero_div, pow_zero, one_mul,
      div_self (ne_of_gt hbpos), one_pow, ktProb2, risingShift_zero, one_div_div]
    have hsq := fact_div_risingHalf_sq_le (by simpa using hn : 1 ≤ b)
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (div_nonneg (le_of_lt hbfact) (le_of_lt hrb)),
      Real.sqrt_mul (by norm_num), hsqrt4] at hsqrt
    exact hsqrt
  · by_cases hb : b = 0
    · subst hb
      have hapos : (0 : ℝ) < (a : ℝ) := by simpa using hnpos
      have hafact : (0 : ℝ) < (a.factorial : ℝ) := by simpa using hfact_pos
      simp only [Nat.add_zero, Nat.cast_zero, zero_div, pow_zero, mul_one,
        div_self (ne_of_gt hapos), one_pow, ktProb2, risingShift_zero, one_div_div]
      have hsq := fact_div_risingHalf_sq_le (by simpa using hn : 1 ≤ a)
      have hsqrt := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (div_nonneg (le_of_lt hafact) (le_of_lt hra)),
        Real.sqrt_mul (by norm_num), hsqrt4] at hsqrt
      exact hsqrt
    · -- Interior case `a ≥ 1` and `b ≥ 1`: factor via `e^a, e^b` and cancel `e^n`!
      have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha
      have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb
      have hA := pow_div_exp_risingHalf_le_two_div_e ha1
      have hB := pow_div_exp_risingHalf_le_two_div_e hb1
      have hN := exp_mul_fact_div_pow_le hn
      have hrew : ((a : ℝ) / ((a + b : ℕ) : ℝ)) ^ a * ((b : ℝ) / ((a + b : ℕ) : ℝ)) ^ b /
            ktProb2 a b =
          ((a : ℝ) ^ a / (Real.exp a * risingShift (1 / 2) a)) *
          ((b : ℝ) ^ b / (Real.exp b * risingShift (1 / 2) b)) *
          (Real.exp (a + b : ℕ) * ((a + b).factorial : ℝ) / ((a + b : ℕ) : ℝ) ^ (a + b)) := by
        unfold ktProb2
        rw [div_pow, div_pow, Nat.cast_add, Real.exp_add, pow_add]
        have hexpa : Real.exp a ≠ 0 := ne_of_gt (Real.exp_pos a)
        have hexpb : Real.exp b ≠ 0 := ne_of_gt (Real.exp_pos b)
        have hnpow1 : ((a : ℝ) + (b : ℝ)) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hnpos)
        have hnpow2 : ((a : ℝ) + (b : ℝ)) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast ne_of_gt hnpos)
        field_simp [ne_of_gt hra, ne_of_gt hrb, ne_of_gt hfact_pos, hexpa, hexpb, hnpow1, hnpow2]
      rw [hrew]
      have hAB : ((a : ℝ) ^ a / (Real.exp a * risingShift (1 / 2) a)) *
            ((b : ℝ) ^ b / (Real.exp b * risingShift (1 / 2) b)) ≤
            (2 / Real.exp 1) * (2 / Real.exp 1) :=
        mul_le_mul hA hB (by positivity) (by positivity)
      have hprod := mul_le_mul hAB hN (by positivity) (by positivity)
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hconst : (2 / Real.exp 1) * (2 / Real.exp 1) * (Real.exp 1 * Real.sqrt ((a + b : ℕ) : ℝ)) ≤
          2 * Real.sqrt ((a + b : ℕ) : ℝ) := by
        have hepos : 0 < Real.exp 1 := Real.exp_pos 1
        have hsimp : (2 / Real.exp 1) * (2 / Real.exp 1) * (Real.exp 1 * Real.sqrt ((a + b : ℕ) : ℝ)) =
            (4 / Real.exp 1) * Real.sqrt ((a + b : ℕ) : ℝ) := by
          field_simp [ne_of_gt hepos]; ring
        rw [hsimp]
        have h4e : 4 / Real.exp 1 ≤ 2 := by
          rw [div_le_iff₀ hepos]; linarith
        exact mul_le_mul_of_nonneg_right h4e (Real.sqrt_nonneg _)
      exact le_trans hprod hconst

/-- Upper bound on `risingShift (r + m) n` for `r ≥ 1`:
    `risingShift (r + m) n ≤ (n + 1)^m * risingShift r n`. -/
private lemma risingShift_add_nat_le {r : ℝ} (hr : 1 ≤ r) (m n : ℕ) :
    risingShift (r + (m : ℝ)) n ≤ ((n : ℝ) + 1) ^ m * risingShift r n := by
  induction m with
  | zero => simp
  | succ j ih =>
    have hrj : 1 ≤ r + (j : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hrj_pos : 0 < r + (j : ℝ) := by linarith
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, risingShift_add_one hrj_pos n]
    have hfac : ((n : ℝ) + (r + (j : ℝ))) / (r + (j : ℝ)) ≤ (n : ℝ) + 1 := by
      rw [div_le_iff₀ hrj_pos]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc ((n : ℝ) + (r + (j : ℝ))) / (r + (j : ℝ)) * risingShift (r + (j : ℝ)) n
      _ ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ j * risingShift r n) :=
          mul_le_mul hfac ih (le_of_lt (risingShift_pos hrj_pos n)) (by positivity)
      _ = ((n : ℝ) + 1) ^ (j + 1) * risingShift r n := by rw [pow_succ']; ring

/-- Even-alphabet Pochhammer bound: for `m ≥ 1` and `n ≥ 1`,
    `e^n · risingShift m n / n^n ≤ e · √n · (n + 1)^{m - 1}`. -/
private lemma exp_mul_risingShift_nat_div_pow_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Real.exp n * risingShift (m : ℝ) n / (n : ℝ) ^ n ≤
      Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) ^ (m - 1) := by
  have hm_eq : (m : ℝ) = 1 + ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_one]; ring
  rw [hm_eq]
  have h1 := risingShift_add_nat_le (r := 1) le_rfl (m - 1) n
  rw [risingShift_one_eq_factorial] at h1
  have h2 := exp_mul_fact_div_pow_le hn
  calc Real.exp n * risingShift (1 + ((m - 1 : ℕ) : ℝ)) n / (n : ℝ) ^ n
    _ ≤ Real.exp n * (((n : ℝ) + 1) ^ (m - 1) * (n.factorial : ℝ)) / (n : ℝ) ^ n := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
        · positivity
    _ = (Real.exp n * (n.factorial : ℝ) / (n : ℝ) ^ n) * ((n : ℝ) + 1) ^ (m - 1) := by ring
    _ ≤ (Real.exp 1 * Real.sqrt (n : ℝ)) * ((n : ℝ) + 1) ^ (m - 1) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)

/-- Odd-alphabet Pochhammer bound: for `m ≥ 1` and `n ≥ 1`,
    `e^n · risingShift (m + 1/2) n / n^n ≤ e · √2 · (n + 1)^m`. -/
private lemma exp_mul_risingShift_half_add_div_pow_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Real.exp n * risingShift ((m : ℝ) + 1 / 2) n / (n : ℝ) ^ n ≤
      Real.exp 1 * Real.sqrt 2 * ((n : ℝ) + 1) ^ m := by
  have hm_eq : (m : ℝ) + 1 / 2 = (3 / 2 : ℝ) + ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_one]; ring
  rw [hm_eq]
  have h1 := risingShift_add_nat_le (r := 3 / 2) (by norm_num) (m - 1) n
  have h32 : risingShift (3 / 2 : ℝ) n = (2 * (n : ℝ) + 1) * risingShift (1 / 2) n := by
    have hadd := risingShift_add_one (r := (1 / 2 : ℝ)) (by norm_num) n
    have h12 : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
    rw [h12] at hadd
    rw [hadd]
    ring
  have hris := risingHalf_le_fact_div_sqrt n
  have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have h32_le : risingShift (3 / 2 : ℝ) n ≤ Real.sqrt (2 * (n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [h32]
    calc (2 * (n : ℝ) + 1) * risingShift (1 / 2) n
      _ ≤ (2 * (n : ℝ) + 1) * ((n.factorial : ℝ) / Real.sqrt (2 * (n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hris (le_of_lt h2n1)
      _ = Real.sqrt (2 * (n : ℝ) + 1) * (n.factorial : ℝ) := by
          have hsq : Real.sqrt (2 * (n : ℝ) + 1) * Real.sqrt (2 * (n : ℝ) + 1) = 2 * (n : ℝ) + 1 :=
            Real.mul_self_sqrt (le_of_lt h2n1)
          have hne : Real.sqrt (2 * (n : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2n1)
          field_simp [hne]
          linarith
  have h2 := exp_mul_fact_div_pow_le hn
  have hsqrt_prod : Real.sqrt (n : ℝ) * Real.sqrt (2 * (n : ℝ) + 1) ≤ Real.sqrt 2 * ((n : ℝ) + 1) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
    have hsq_le : (n : ℝ) * (2 * (n : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc Real.sqrt ((n : ℝ) * (2 * (n : ℝ) + 1))
      _ ≤ Real.sqrt (2 * ((n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hsq_le
      _ = Real.sqrt 2 * ((n : ℝ) + 1) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  calc Real.exp n * risingShift ((3 / 2 : ℝ) + ((m - 1 : ℕ) : ℝ)) n / (n : ℝ) ^ n
    _ ≤ Real.exp n * (((n : ℝ) + 1) ^ (m - 1) * (Real.sqrt (2 * (n : ℝ) + 1) * (n.factorial : ℝ))) /
          (n : ℝ) ^ n := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left
            (le_trans h1 (mul_le_mul_of_nonneg_left h32_le (by positivity)))
            (le_of_lt (Real.exp_pos _))
        · positivity
    _ = (Real.exp n * (n.factorial : ℝ) / (n : ℝ) ^ n) *
          Real.sqrt (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1) := by ring
    _ ≤ (Real.exp 1 * Real.sqrt (n : ℝ)) *
          Real.sqrt (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)) (by positivity)
    _ = Real.exp 1 * (Real.sqrt (n : ℝ) * Real.sqrt (2 * (n : ℝ) + 1)) * ((n : ℝ) + 1) ^ (m - 1) := by
        ring
    _ ≤ Real.exp 1 * (Real.sqrt 2 * ((n : ℝ) + 1)) * ((n : ℝ) + 1) ^ (m - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt_prod (le_of_lt (Real.exp_pos 1))) (by positivity)
    _ = Real.exp 1 * Real.sqrt 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1)) := by ring
    _ = Real.exp 1 * Real.sqrt 2 * ((n : ℝ) + 1) ^ m := by
        have hpow : ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1) = ((n : ℝ) + 1) ^ m := by
          conv_rhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
        rw [hpow]

/-- Combined numerator product bound for any sequence `x : Fin n → α` with `n ≥ 1`:
    `∏_a (c_a^{c_a} / risingShift (1/2) c_a) ≤ (2 / e) · e^n`. -/
private lemma prod_typeCount_div_risingHalf_le {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    (∏ a : α, (typeCount x a : ℝ) ^ (typeCount x a) / risingShift (1 / 2) (typeCount x a)) ≤
      (2 / Real.exp 1) * Real.exp n := by
  classical
  have hexp_n : Real.exp n = ∏ a : α, Real.exp (typeCount x a : ℝ) := by
    rw [← Real.exp_sum, ← Nat.cast_sum, sum_typeCount_aux]
  rw [hexp_n]
  have hprod_pos : 0 < ∏ a : α, Real.exp (typeCount x a : ℝ) :=
    Finset.prod_pos fun a _ => Real.exp_pos _
  rw [← div_le_iff₀ hprod_pos, ← Finset.prod_div_distrib]
  have hrew : ∀ a : α,
      (typeCount x a : ℝ) ^ (typeCount x a) / risingShift (1 / 2) (typeCount x a) /
        Real.exp (typeCount x a : ℝ) =
      (typeCount x a : ℝ) ^ (typeCount x a) /
        (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a)) := fun a => by ring
  simp_rw [hrew]
  let a₀ : α := x ⟨0, hn⟩
  have ha₀ : 1 ≤ typeCount x a₀ := typeCount_self_pos x ⟨0, hn⟩
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a₀)]
  have hfirst : (typeCount x a₀ : ℝ) ^ (typeCount x a₀) /
      (Real.exp (typeCount x a₀ : ℝ) * risingShift (1 / 2) (typeCount x a₀)) ≤ 2 / Real.exp 1 :=
    pow_div_exp_risingHalf_le_two_div_e ha₀
  have hrest : ∏ a ∈ Finset.univ.erase a₀,
      (typeCount x a : ℝ) ^ (typeCount x a) /
        (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a)) ≤ 1 := by
    have haux : ∀ (s : Finset α),
        (∀ a ∈ s, 0 ≤ (typeCount x a : ℝ) ^ (typeCount x a) /
          (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a))) →
        (∀ a ∈ s, (typeCount x a : ℝ) ^ (typeCount x a) /
          (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a)) ≤ 1) →
        ∏ a ∈ s, (typeCount x a : ℝ) ^ (typeCount x a) /
          (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a)) ≤ 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intros; simp
      | @insert b s hb ih =>
        intro h0 h1
        rw [Finset.prod_insert hb]
        have hb1 := h1 b (Finset.mem_insert_self b s)
        have hs1 := ih (fun a ha => h0 a (Finset.mem_insert_of_mem ha))
          (fun a ha => h1 a (Finset.mem_insert_of_mem ha))
        have hs0 : 0 ≤ ∏ a ∈ s, (typeCount x a : ℝ) ^ (typeCount x a) /
            (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a)) :=
          Finset.prod_nonneg fun a ha => h0 a (Finset.mem_insert_of_mem ha)
        nlinarith
    exact haux _
      (fun a _ => div_nonneg (by positivity)
        (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (risingShift_pos (by norm_num) _))))
      (fun a _ => pow_div_exp_risingHalf_le_one (typeCount x a))
  have hrest_nonneg : 0 ≤ ∏ a ∈ Finset.univ.erase a₀,
      (typeCount x a : ℝ) ^ (typeCount x a) /
        (Real.exp (typeCount x a : ℝ) * risingShift (1 / 2) (typeCount x a)) :=
    Finset.prod_nonneg fun a _ => div_nonneg (by positivity)
      (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (risingShift_pos (by norm_num) _)))
  calc _ ≤ (2 / Real.exp 1) * 1 := mul_le_mul hfirst hrest hrest_nonneg (by positivity)
    _ = 2 / Real.exp 1 := mul_one _

/-- **Sharp General-Alphabet KT Ratio Upper Bound** (Krichevsky & Trofimov 1981, Theorem 1):
    for every finite nonempty alphabet `α` of size `k`, every `n ≥ 1`, and every sequence `x`:
    - `mlProb x / (ktDist α n).pmf x ≤ 2 √2 · (n + 1)^{(k - 1) / 2}`,
    - and for `k = 1` the ratio equals `1`, while for `k = 2` it is `≤ 2 √n`. -/
theorem kt_ml_ratio_le [Nonempty α] {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    mlProb x / (ktDist α n).pmf x ≤
      (if Fintype.card α = 1 then (1 : ℝ)
       else if Fintype.card α = 2 then 2
       else 2 * Real.sqrt 2) *
        ((n : ℝ) + 1) ^ (((Fintype.card α - 1 : ℕ) : ℝ) / 2) := by
  set k : ℕ := Fintype.card α
  have hkpos : 1 ≤ k := Fintype.card_pos
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- Handle k = 1 separately (ratio is identically 1)
  by_cases hk1 : k = 1
  · simp only [hk1, ↓reduceIte, Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
    have huniq : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hk1)
    have hcnt : ∀ a : α, typeCount x a = n := fun a => by
      classical
      rw [typeCount_eq_card_aux]
      have hall : Finset.univ.filter (fun i : Fin n => x i = a) = Finset.univ := by
        ext i; simp [Subsingleton.elim (x i) a]
      rw [hall, Finset.card_univ, Fintype.card_fin]
    have hml1 : mlProb x = 1 := by
      unfold mlProb
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hcnt, div_self (ne_of_gt hnpos)]
    have hkt1 : (ktDist α n).pmf x = 1 := by
      rw [ktDist_pmf_eq_prod]
      have hcard_eq : Fintype.card α = 1 := hk1
      rw [hcard_eq]
      have hprod : ∏ a : α, risingShift (1 / 2) (typeCount x a) = risingShift (1 / 2) n := by
        obtain ⟨a₀⟩ := ‹Nonempty α›
        rw [Finset.prod_eq_single a₀]
        · rw [hcnt a₀]
        · intro b _ hne; exact absurd (Subsingleton.elim b a₀) hne
        · intro h; exact absurd (Finset.mem_univ a₀) h
      rw [hprod, Nat.cast_one, div_self (ne_of_gt (risingShift_pos (by norm_num) n))]
    rw [hml1, hkt1, div_one]
  · -- Rewrite `mlProb x / (ktDist α n).pmf x` as product over `a` times `risingShift (k/2) n / n^n`
    have hml_eq : mlProb x = (∏ a : α, (typeCount x a : ℝ) ^ (typeCount x a)) / (n : ℝ) ^ n := by
      unfold mlProb
      rw [prod_comp_eq_prod_pow_typeCount_aux x (fun a => (typeCount x a : ℝ) / (n : ℝ))]
      simp_rw [div_pow]
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_typeCount_aux]
    have hratio_eq : mlProb x / (ktDist α n).pmf x =
        (∏ a : α, (typeCount x a : ℝ) ^ (typeCount x a) / risingShift (1 / 2) (typeCount x a)) *
          (risingShift ((k : ℝ) / 2) n / (n : ℝ) ^ n) := by
      rw [hml_eq, ktDist_pmf_eq_prod, Finset.prod_div_distrib]
      have hden1 : ∏ a : α, risingShift (1 / 2) (typeCount x a) ≠ 0 :=
        ne_of_gt (Finset.prod_pos fun a _ => risingShift_pos (by norm_num) _)
      have hden2 : risingShift ((k : ℝ) / 2) n ≠ 0 :=
        ne_of_gt (risingShift_pos (by positivity) n)
      have hden3 : (n : ℝ) ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hnpos)
      change _ = _ * (risingShift ((Fintype.card α : ℝ) / 2) n / (n : ℝ) ^ n)
      field_simp [hden1, hden2, hden3]
    have hnum_le := prod_typeCount_div_risingHalf_le hn x
    have hstep1 : mlProb x / (ktDist α n).pmf x ≤
        (2 / Real.exp 1) * (Real.exp n * risingShift ((k : ℝ) / 2) n / (n : ℝ) ^ n) := by
      rw [hratio_eq]
      calc _ ≤ ((2 / Real.exp 1) * Real.exp n) * (risingShift ((k : ℝ) / 2) n / (n : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_right hnum_le (div_nonneg
              (le_of_lt (risingShift_pos (by positivity) n)) (by positivity))
        _ = (2 / Real.exp 1) * (Real.exp n * risingShift ((k : ℝ) / 2) n / (n : ℝ) ^ n) := by ring
    -- Split by parity of k ≥ 2
    rcases Nat.even_or_odd' k with ⟨m, hk_eq | hk_eq⟩
    · -- Even `k = 2 * m`, `m ≥ 1`
      have hm1 : 1 ≤ m := by omega
      have hk2_eq : (k : ℝ) / 2 = (m : ℝ) := by rw [hk_eq]; push_cast; ring
      have hpoch := exp_mul_risingShift_nat_div_pow_le hm1 hn
      rw [hk2_eq] at hstep1
      have hle2 : mlProb x / (ktDist α n).pmf x ≤
          2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) ^ (m - 1) := by
        have h := le_trans hstep1 (mul_le_mul_of_nonneg_left hpoch (by positivity))
        have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
        have hsimp : (2 / Real.exp 1) * (Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) ^ (m - 1)) =
            2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) ^ (m - 1) := by field_simp [he]
        linarith
      have hpow_eq : Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1) =
          ((n : ℝ) + 1) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((n : ℝ) + 1) (m - 1),
          ← Real.rpow_add (by positivity)]
        congr 1
        rw [hk_eq, Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_sub hm1]
        push_cast
        ring
      have hle_base : mlProb x / (ktDist α n).pmf x ≤
          2 * ((n : ℝ) + 1) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
        calc mlProb x / (ktDist α n).pmf x
          _ ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) + 1) ^ (m - 1) := hle2
          _ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1) := by
              have hs : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
                Real.sqrt_le_sqrt (by linarith)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
                (by positivity)
          _ = 2 * (Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (m - 1)) := by ring
          _ = 2 * ((n : ℝ) + 1) ^ (((k - 1 : ℕ) : ℝ) / 2) := by rw [hpow_eq]
      simp only [hk1, ↓reduceIte]
      split_ifs
      · exact hle_base
      · have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
        exact le_trans hle_base (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · -- Odd `k = 2 * m + 1`, `m ≥ 1` (since `k ≠ 1`)
      have hm1 : 1 ≤ m := by omega
      have hk2 : k ≠ 2 := by omega
      have hk2_eq : (k : ℝ) / 2 = (m : ℝ) + 1 / 2 := by rw [hk_eq]; push_cast; ring
      have hpoch := exp_mul_risingShift_half_add_div_pow_le hm1 hn
      rw [hk2_eq] at hstep1
      have hle2 : mlProb x / (ktDist α n).pmf x ≤
          2 * Real.sqrt 2 * ((n : ℝ) + 1) ^ m := by
        have h := le_trans hstep1 (mul_le_mul_of_nonneg_left hpoch (by positivity))
        have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
        have hsimp : (2 / Real.exp 1) * (Real.exp 1 * Real.sqrt 2 * ((n : ℝ) + 1) ^ m) =
            2 * Real.sqrt 2 * ((n : ℝ) + 1) ^ m := by field_simp [he]
        linarith
      have hpow_eq : ((n : ℝ) + 1) ^ m = ((n : ℝ) + 1) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
        rw [hk_eq, Nat.add_sub_cancel, ← Real.rpow_natCast]
        congr 1
        push_cast; ring
      rw [hpow_eq] at hle2
      simp only [hk1, hk2, ↓reduceIte]
      exact hle2

/-- **Sharp Krichevsky–Trofimov Pointwise Regret Bound (Universal Constant `2`)**:
    for every nonempty finite alphabet `α` of size `k`, every `n ≥ 1`, every i.i.d. source
    `P : ProbDist α`, and every sequence `x` with `P^n(x) > 0`:
    `log₂ (P^n(x) / P_KT(x)) ≤ ((k - 1)/2) log₂(n + 1) + 2`. -/
theorem kt_pointwise_regret_le [Nonempty α] {n : ℕ} (hn : 0 < n)
    (P : ProbDist α) (x : Fin n → α) (hpx : 0 < (iidDist P n).pmf x) :
    log2 ((iidDist P n).pmf x / (ktDist α n).pmf x) ≤
      (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) + 2 := by
  have hkt := ktDist_pos α n x
  have h1 : (iidDist P n).pmf x / (ktDist α n).pmf x ≤ mlProb x / (ktDist α n).pmf x :=
    div_le_div_of_nonneg_right (iidDist_pmf_le_mlProb P x) (le_of_lt hkt)
  have h2 := kt_ml_ratio_le hn x
  have hC_le : (if Fintype.card α = 1 then (1 : ℝ)
      else if Fintype.card α = 2 then 2 else 2 * Real.sqrt 2) ≤ 4 := by
    split_ifs <;> try norm_num
    have hsq2 : Real.sqrt 2 ≤ 2 := by
      have h4 : (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]; exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have h3 : (iidDist P n).pmf x / (ktDist α n).pmf x ≤
      4 * ((n : ℝ) + 1) ^ (((Fintype.card α - 1 : ℕ) : ℝ) / 2) :=
    le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_right hC_le (by positivity)))
  have hlog := log2_le_log2 (div_pos hpx hkt) h3
  rw [log2_mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _),
    log2_rpow (by positivity)] at hlog
  have hlog4 : log2 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, log2_pow_nat, log2_two]; norm_num
  linarith

/-- **Sharp Krichevsky–Trofimov Pointwise Regret Bound (Alphabet-Exact Constant `k - 1`)**:
    for every nonempty finite alphabet `α` of size `k`, every `n ≥ 1`, every `P : ProbDist α`,
    and every `x` with `P^n(x) > 0`:
    `log₂ (P^n(x) / P_KT(x)) ≤ ((k - 1)/2) log₂(n + 1) + (k - 1)`. -/
theorem kt_pointwise_regret_le_card [Nonempty α] {n : ℕ} (hn : 0 < n)
    (P : ProbDist α) (x : Fin n → α) (hpx : 0 < (iidDist P n).pmf x) :
    log2 ((iidDist P n).pmf x / (ktDist α n).pmf x) ≤
      (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) +
        ((Fintype.card α - 1 : ℕ) : ℝ) := by
  have hkt := ktDist_pos α n x
  have h1 : (iidDist P n).pmf x / (ktDist α n).pmf x ≤ mlProb x / (ktDist α n).pmf x :=
    div_le_div_of_nonneg_right (iidDist_pmf_le_mlProb P x) (le_of_lt hkt)
  have h2 := kt_ml_ratio_le hn x
  by_cases hk1 : Fintype.card α = 1
  · simp only [hk1, ↓reduceIte, Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero,
      mul_one] at h2
    have hlog := log2_le_log2 (div_pos hpx hkt) (le_trans h1 h2)
    rw [log2_one] at hlog
    simp only [hk1, Nat.sub_self, Nat.cast_zero, zero_div, zero_mul, add_zero]
    exact hlog
  · by_cases hk2 : Fintype.card α = 2
    · rw [hk2] at h2
      norm_num at h2
      have hlog := log2_le_log2 (div_pos hpx hkt) (le_trans h1 h2)
      rw [log2_mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _),
        log2_two, log2_rpow (by positivity)] at hlog
      simp only [hk2, Nat.reduceSub, Nat.cast_one]
      linarith
    · have hk3 : 3 ≤ Fintype.card α := by
        have := Fintype.card_pos (α := α); omega
      have h2le : (2 : ℝ) ≤ ((Fintype.card α - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 2 ≤ Fintype.card α - 1 by omega)
      linarith [kt_pointwise_regret_le hn P x hpx]

/-- **Universal KL Redundancy Upper Bound (Krichevsky & Trofimov 1981)**:
    for every nonempty finite alphabet `α` of size `k`, every `n ≥ 1`, and EVERY i.i.d. source
    `P : ProbDist α`:
    `D(P^n ‖ P_KT) ≤ ((k - 1)/2) log₂(n + 1) + 2`
    (and also `≤ ((k - 1)/2) log₂(n + 1) + (k - 1)`). -/
theorem kt_kl_redundancy_le [Nonempty α] {n : ℕ} (hn : 0 < n) (P : ProbDist α) :
    klDivergence (iidDist P n) (ktDist α n) ≤
      (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) + 2 := by
  set B : ℝ := (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) + 2
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ log2 ((n : ℝ) + 1) := log2_nonneg_of_ge_one (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  unfold klDivergence
  calc ∑ x : Fin n → α,
        (if (iidDist P n).pmf x ≤ 0 then 0
         else (iidDist P n).pmf x * log2 ((iidDist P n).pmf x / (ktDist α n).pmf x))
    _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x * B := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : (iidDist P n).pmf x ≤ 0
        · simp only [h, ↓reduceIte]
          exact mul_nonneg ((iidDist P n).nonneg x) hB0
        · simp only [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
          exact mul_le_mul_of_nonneg_left (kt_pointwise_regret_le hn P x (lt_of_not_ge h))
            ((iidDist P n).nonneg x)
    _ = B := by rw [← Finset.sum_mul, (iidDist P n).sum_one, one_mul]

/-- Alphabet-exact form of the KT KL redundancy upper bound:
    `D(P^n ‖ P_KT) ≤ ((k - 1)/2) log₂(n + 1) + (k - 1)`. -/
theorem kt_kl_redundancy_le_card [Nonempty α] {n : ℕ} (hn : 0 < n) (P : ProbDist α) :
    klDivergence (iidDist P n) (ktDist α n) ≤
      (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) +
        ((Fintype.card α - 1 : ℕ) : ℝ) := by
  set B : ℝ := (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) +
    ((Fintype.card α - 1 : ℕ) : ℝ)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ log2 ((n : ℝ) + 1) := log2_nonneg_of_ge_one (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  unfold klDivergence
  calc ∑ x : Fin n → α,
        (if (iidDist P n).pmf x ≤ 0 then 0
         else (iidDist P n).pmf x * log2 ((iidDist P n).pmf x / (ktDist α n).pmf x))
    _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x * B := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : (iidDist P n).pmf x ≤ 0
        · simp only [h, ↓reduceIte]
          exact mul_nonneg ((iidDist P n).nonneg x) hB0
        · simp only [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
          exact mul_le_mul_of_nonneg_left (kt_pointwise_regret_le_card hn P x (lt_of_not_ge h))
            ((iidDist P n).nonneg x)
    _ = B := by rw [← Finset.sum_mul, (iidDist P n).sum_one, one_mul]

/-- Cross-entropy identity: for any strictly positive `Q`,
    `∑ a, P(a) (-log₂ Q(a)) = H(P) + D(P ‖ Q)`. -/
private lemma crossEntropy_eq_entropy_add_kl {β : Type*} [Fintype β]
    (P Q : ProbDist β) (hQ : ∀ b, 0 < Q.pmf b) :
    ∑ b : β, P.pmf b * (-log2 (Q.pmf b)) = shannonEntropy P + klDivergence P Q := by
  unfold shannonEntropy klDivergence
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hp : P.pmf b ≤ 0
  · have hp0 : P.pmf b = 0 := le_antisymm hp (P.nonneg b)
    simp [hp0, negPLogP]
  · have hpos : 0 < P.pmf b := lt_of_not_ge hp
    simp only [negPLogP, ite_eq_right_iff.mpr (fun h => absurd h hp)]
    rw [log2_div_pos hpos (hQ b)]
    ring

/-- **Explicit Universal Prefix-Free Source Code** (Cover & Thomas §§13.1–13.2; Krichevsky &
    Trofimov 1981): for any nonempty finite alphabet `α` of size `k` and blocklength `n ≥ 1`,
    there exists a SINGLE injective binary prefix-free code `c : (Fin n → α) → List Bool`
    (independent of `P`) whose expected codeword length satisfies
    `E_{P^n}[|c(X^n)|] < n H(P) + ((k - 1)/2) log₂(n + 1) + k`
    simultaneously for EVERY i.i.d. source `P : ProbDist α`. -/
theorem universal_prefix_code_redundancy_le (α : Type*) [Fintype α] [Nonempty α]
    {n : ℕ} (hn : 0 < n) :
    ∃ c : (Fin n → α) → List Bool,
      Function.Injective c ∧
      InformationTheory.IsPrefixFree ((Finset.univ.image c : Finset (List Bool)) : Set (List Bool)) ∧
      ∀ P : ProbDist α,
        ∑ x : Fin n → α, (iidDist P n).pmf x * ((c x).length : ℝ) <
          (n : ℝ) * shannonEntropy P +
            (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) +
            (Fintype.card α : ℝ) := by
  let Q := ktDist α n
  have hQpos : ∀ x, 0 < Q.pmf x := ktDist_pos α n
  let l : (Fin n → α) → ℕ := fun x => Nat.ceil (-log2 (Q.pmf x))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkraft_term : ∀ x : Fin n → α, (1 / (Fintype.card Bool : ℝ)) ^ (l x) ≤ Q.pmf x := by
    intro x
    have hceil : -log2 (Q.pmf x) ≤ (l x : ℝ) := Nat.le_ceil _
    have hlog_le : Real.log ((1 / (2 : ℝ)) ^ (l x)) ≤ Real.log (Q.pmf x) := by
      rw [Real.log_pow, one_div, Real.log_inv]
      unfold log2 at hceil
      rw [← neg_div] at hceil
      have hmul := (div_le_iff₀ hlog2pos).mp hceil
      linarith
    have h2 : (Fintype.card Bool : ℝ) = 2 := by simp
    rw [h2]
    exact (Real.log_le_log_iff (by positivity) (hQpos x)).mp hlog_le
  have hkraft : ∑ x : Fin n → α, (1 / (Fintype.card Bool : ℝ)) ^ (l x) ≤ 1 := by
    calc ∑ x : Fin n → α, (1 / (Fintype.card Bool : ℝ)) ^ (l x)
      _ ≤ ∑ x : Fin n → α, Q.pmf x := Finset.sum_le_sum fun x _ => hkraft_term x
      _ = 1 := Q.sum_one
  obtain ⟨c, hcinj, hcpf, hclen⟩ := exists_prefixFree_code_of_kraft (β := Bool) l hkraft
  refine ⟨c, hcinj, hcpf, fun P => ?_⟩
  have hlt_each : ∀ x : Fin n → α, ((c x).length : ℝ) < -log2 (Q.pmf x) + 1 := by
    intro x
    rw [hclen x]
    have harg_nonneg : 0 ≤ -log2 (Q.pmf x) := by
      have hle1 : Q.pmf x ≤ 1 := pmf_le_one Q x
      have hlog : Real.log (Q.pmf x) ≤ 0 := Real.log_nonpos (le_of_lt (hQpos x)) hle1
      unfold log2
      have : Real.log (Q.pmf x) / Real.log 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hlog2pos)
      linarith
    exact Nat.ceil_lt_add_one harg_nonneg
  have hex_pos : ∃ x : Fin n → α, 0 < (iidDist P n).pmf x := by
    by_contra hall
    push Not at hall
    have h0 : ∑ x : Fin n → α, (iidDist P n).pmf x = 0 :=
      Finset.sum_eq_zero fun x _ => le_antisymm (hall x) ((iidDist P n).nonneg x)
    rw [(iidDist P n).sum_one] at h0
    norm_num at h0
  have hsum_lt : ∑ x : Fin n → α, (iidDist P n).pmf x * ((c x).length : ℝ) <
      ∑ x : Fin n → α, (iidDist P n).pmf x * (-log2 (Q.pmf x) + 1) := by
    refine Finset.sum_lt_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (le_of_lt (hlt_each x)) ((iidDist P n).nonneg x)) ?_
    obtain ⟨x₀, hx₀⟩ := hex_pos
    exact ⟨x₀, Finset.mem_univ x₀, mul_lt_mul_of_pos_left (hlt_each x₀) hx₀⟩
  have hrhs_eq : ∑ x : Fin n → α, (iidDist P n).pmf x * (-log2 (Q.pmf x) + 1) =
      (n : ℝ) * shannonEntropy P + klDivergence (iidDist P n) Q + 1 := by
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib, (iidDist P n).sum_one]
    rw [crossEntropy_eq_entropy_add_kl (iidDist P n) Q hQpos, shannonEntropy_iidDist]
  have hkl := kt_kl_redundancy_le_card hn P
  have hk_cast : ((Fintype.card α - 1 : ℕ) : ℝ) + 1 = (Fintype.card α : ℝ) := by
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]; ring
  linarith

end KrichevskyTrofimov

/-! ### 3. Capacity–Redundancy Theorem, Minimax Lower Bound & Exact Asymptotics -/

section MinimaxRedundancy

/-! #### 3.1 Capacity–Redundancy Theorem (Gallager 1976 / Haussler 1997) -/

/-- Joint distribution `(Θ, Y)` formed from a prior `W` on `ι` and a family of conditional
    distributions `P : ι → ProbDist β`. -/
def jointPrior {ι β : Type*} [Fintype ι] [Fintype β]
    (W : ProbDist ι) (P : ι → ProbDist β) : ProbDist (ι × β) where
  pmf := fun jy => W.pmf jy.1 * (P jy.1).pmf jy.2
  nonneg := fun jy => mul_nonneg (W.nonneg jy.1) ((P jy.1).nonneg jy.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, fun j => (P j).sum_one, mul_one, W.sum_one]

/-- Bayes mixture marginal `M_W(y) = ∑_j W(j) P_j(y)`. -/
def bayesMixture {ι β : Type*} [Fintype ι] [Fintype β]
    (W : ProbDist ι) (P : ι → ProbDist β) : ProbDist β :=
  (jointPrior W P).snd

lemma jointPrior_fst {ι β : Type*} [Fintype ι] [Fintype β]
    (W : ProbDist ι) (P : ι → ProbDist β) :
    (jointPrior W P).fst = W := by
  unfold ProbDist.fst jointPrior
  congr; funext j
  simp [← Finset.mul_sum, (P j).sum_one]

/-- **Bayes Compensation Identity**:
    for any prior `W` on `ι`, family `P : ι → ProbDist β`, and `Q : ProbDist β` such that
    `W(j) > 0 → P_j ≪ Q`,
    `∑_j W(j) D(P_j ‖ Q) = I(Θ; Y) + D(M_W ‖ Q)`. -/
theorem bayes_kl_decomposition {ι β : Type*} [Fintype ι] [Fintype β]
    (W : ProbDist ι) (P : ι → ProbDist β) (Q : ProbDist β)
    (hac : ∀ j : ι, 0 < W.pmf j → AbsCont (P j) Q) :
    ∑ j : ι, W.pmf j * klDivergence (P j) Q =
      mutualInfo (jointPrior W P) + klDivergence (bayesMixture W P) Q := by
  set J := jointPrior W P
  set M := bayesMixture W P
  have hJfst : J.fst = W := jointPrior_fst W P
  have hJsnd : J.snd = M := rfl
  rw [mutualInfo_eq_klDivergence J, hJfst, hJsnd]
  have hM_pmf : ∀ y : β, M.pmf y = ∑ j : ι, W.pmf j * (P j).pmf y := fun _ => rfl
  -- Expand both sides as double sums over `ι × β`
  have hlhs : ∑ j : ι, W.pmf j * klDivergence (P j) Q =
      ∑ jy : ι × β, if W.pmf jy.1 * (P jy.1).pmf jy.2 ≤ 0 then (0 : ℝ)
        else W.pmf jy.1 * (P jy.1).pmf jy.2 * log2 ((P jy.1).pmf jy.2 / Q.pmf jy.2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold klDivergence
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hw : W.pmf j ≤ 0
    · have hw0 : W.pmf j = 0 := le_antisymm hw (W.nonneg j)
      simp [hw0]
    · have hwpos : 0 < W.pmf j := lt_of_not_ge hw
      by_cases hp : (P j).pmf y ≤ 0
      · have hp0 : (P j).pmf y = 0 := le_antisymm hp ((P j).nonneg y)
        simp [hp0]
      · have hppos : 0 < (P j).pmf y := lt_of_not_ge hp
        have hwp : ¬ (W.pmf j * (P j).pmf y ≤ 0) := not_le.mpr (mul_pos hwpos hppos)
        simp only [ite_eq_right_iff.mpr (fun h => absurd h hp),
          ite_eq_right_iff.mpr (fun h => absurd h hwp)]
        ring
  have hkl2 : klDivergence M Q =
      ∑ jy : ι × β, if W.pmf jy.1 * (P jy.1).pmf jy.2 ≤ 0 then (0 : ℝ)
        else W.pmf jy.1 * (P jy.1).pmf jy.2 * log2 (M.pmf jy.2 / Q.pmf jy.2) := by
    rw [Fintype.sum_prod_type_right]
    unfold klDivergence
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hm : M.pmf y ≤ 0
    · have hm0 : M.pmf y = 0 := le_antisymm hm (M.nonneg y)
      simp only [hm0, le_refl, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have hterm0 : W.pmf j * (P j).pmf y = 0 := by
        have hle : W.pmf j * (P j).pmf y ≤ M.pmf y :=
          Finset.single_le_sum (f := fun j' => W.pmf j' * (P j').pmf y)
            (fun j' _ => mul_nonneg (W.nonneg j') ((P j').nonneg y)) (Finset.mem_univ j)
        linarith [mul_nonneg (W.nonneg j) ((P j).nonneg y)]
      simp [hterm0]
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hm)]
      rw [hM_pmf y, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hwp : W.pmf j * (P j).pmf y ≤ 0
      · have h0 : W.pmf j * (P j).pmf y = 0 :=
          le_antisymm hwp (mul_nonneg (W.nonneg j) ((P j).nonneg y))
        simp [h0]
      · simp [hwp]
  rw [hlhs, hkl2]
  unfold klDivergence
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ⟨j, y⟩ _ => ?_
  change (if W.pmf j * (P j).pmf y ≤ 0 then 0 else _) =
    (if W.pmf j * (P j).pmf y ≤ 0 then 0
     else W.pmf j * (P j).pmf y * log2 ((W.pmf j * (P j).pmf y) / (W.pmf j * M.pmf y))) +
    (if W.pmf j * (P j).pmf y ≤ 0 then 0
     else W.pmf j * (P j).pmf y * log2 (M.pmf y / Q.pmf y))
  by_cases hwp : W.pmf j * (P j).pmf y ≤ 0
  · simp [hwp]
  · have hpos : 0 < W.pmf j * (P j).pmf y := lt_of_not_ge hwp
    have hwpos : 0 < W.pmf j := lt_of_le_of_ne (W.nonneg j) fun h => by
      rw [← h, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hppos : 0 < (P j).pmf y := lt_of_le_of_ne ((P j).nonneg y) fun h => by
      rw [← h, mul_zero] at hpos; exact lt_irrefl _ hpos
    have hmpos : 0 < M.pmf y := lt_of_lt_of_le hpos
      (Finset.single_le_sum (f := fun j' => W.pmf j' * (P j').pmf y)
        (fun j' _ => mul_nonneg (W.nonneg j') ((P j').nonneg y)) (Finset.mem_univ j))
    have hqpos : 0 < Q.pmf y := lt_of_le_of_ne (Q.nonneg y) fun h => by
      have := hac j hwpos y h.symm; linarith
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hwp)]
    rw [mul_div_mul_left _ _ (ne_of_gt hwpos),
      log2_div_pos hppos hqpos, log2_div_pos hppos hmpos, log2_div_pos hmpos hqpos]
    ring

/-- **Capacity–Redundancy Lower Bound** (Gallager 1976 / Haussler 1997):
    for any prior `W` on `ι`, family `P : ι → ProbDist β`, and `Q : ProbDist β` with
    `W(j) > 0 → P_j ≪ Q`:
    1. Average redundancy: `I(Θ; Y) ≤ ∑_j W(j) D(P_j ‖ Q)`.
    2. Worst-case redundancy: there exists `j : ι` with `I(Θ; Y) ≤ D(P_j ‖ Q)`. -/
theorem redundancy_ge_mutualInfo {ι β : Type*} [Fintype ι] [Fintype β]
    (W : ProbDist ι) (P : ι → ProbDist β) (Q : ProbDist β)
    (hac : ∀ j : ι, 0 < W.pmf j → AbsCont (P j) Q) :
    mutualInfo (jointPrior W P) ≤ ∑ j : ι, W.pmf j * klDivergence (P j) Q ∧
    ∃ j : ι, mutualInfo (jointPrior W P) ≤ klDivergence (P j) Q := by
  have hacM : AbsCont (bayesMixture W P) Q := by
    intro y hQ0
    change ∑ j : ι, W.pmf j * (P j).pmf y = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hw : W.pmf j = 0
    · simp [hw]
    · have hwpos : 0 < W.pmf j := lt_of_le_of_ne (W.nonneg j) (Ne.symm hw)
      rw [hac j hwpos y hQ0, mul_zero]
  have hkl_nonneg : 0 ≤ klDivergence (bayesMixture W P) Q :=
    klDivergence_nonneg (bayesMixture W P) Q hacM
  have hdecomp := bayes_kl_decomposition W P Q hac
  have havg : mutualInfo (jointPrior W P) ≤ ∑ j : ι, W.pmf j * klDivergence (P j) Q := by
    linarith
  refine ⟨havg, ?_⟩
  by_contra hall
  push Not at hall
  have hex_w : ∃ j : ι, 0 < W.pmf j := by
    by_contra h0
    push Not at h0
    have hsum0 : ∑ j : ι, W.pmf j = 0 :=
      Finset.sum_eq_zero fun j _ => le_antisymm (h0 j) (W.nonneg j)
    rw [W.sum_one] at hsum0
    norm_num at hsum0
  have hlt : ∑ j : ι, W.pmf j * klDivergence (P j) Q <
      ∑ j : ι, W.pmf j * mutualInfo (jointPrior W P) := by
    refine Finset.sum_lt_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (le_of_lt (hall j)) (W.nonneg j)) ?_
    obtain ⟨j₀, hj₀⟩ := hex_w
    exact ⟨j₀, Finset.mem_univ j₀, mul_lt_mul_of_pos_left (hall j₀) hj₀⟩
  rw [← Finset.sum_mul, W.sum_one, one_mul] at hlt
  linarith

/-! #### 3.2 Minimax KL Redundancy Definition & Upper Bound -/

/-- Worst-case KL redundancy of a universal distribution `Q` over all i.i.d. sources `P`:
    `R_n(Q) = sup_{P ∈ Δ(α)} D(P^n ‖ Q)`. -/
noncomputable def worstCaseRedundancy {α : Type*} [Fintype α] (n : ℕ)
    (Q : ProbDist (Fin n → α)) : ℝ :=
  sSup { r : ℝ | ∃ P : ProbDist α, r = klDivergence (iidDist P n) Q }

/-- Minimax KL redundancy over all strictly positive universal distributions on `α^n`:
    `R*_n(α) = inf_{Q > 0} sup_{P ∈ Δ(α)} D(P^n ‖ Q)`. -/
noncomputable def minimaxRedundancy (α : Type*) [Fintype α] (n : ℕ) : ℝ :=
  sInf { R : ℝ | ∃ Q : ProbDist (Fin n → α),
    (∀ x, 0 < Q.pmf x) ∧ ∀ P : ProbDist α, klDivergence (iidDist P n) Q ≤ R }

private lemma minimaxRedundancy_set_nonempty (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) :
    { R : ℝ | ∃ Q : ProbDist (Fin n → α),
      (∀ x, 0 < Q.pmf x) ∧ ∀ P : ProbDist α, klDivergence (iidDist P n) Q ≤ R }.Nonempty := by
  cases n with
  | zero =>
    refine ⟨0, ktDist α 0, ktDist_pos α 0, fun P => ?_⟩
    have huniq : Unique (Fin 0 → α) := inferInstance
    have heq : iidDist P 0 = ktDist α 0 := by
      cases h1 : iidDist P 0 with | mk p1 _ _ =>
      cases h2 : ktDist α 0 with | mk p2 _ _ =>
      congr; funext x
      have hp1 : p1 x = 1 := by
        have := (iidDist P 0).sum_one
        rw [h1, Fintype.sum_unique] at this
        rwa [Unique.eq_default x]
      have hp2 : p2 x = 1 := by
        have := (ktDist α 0).sum_one
        rw [h2, Fintype.sum_unique] at this
        rwa [Unique.eq_default x]
      rw [hp1, hp2]
    rw [heq, (klDivergence_eq_zero_iff _ _ (fun _ h => h)).mpr rfl]
  | succ m =>
    exact ⟨_, ktDist α (m + 1), ktDist_pos α (m + 1),
      fun P => kt_kl_redundancy_le (Nat.succ_pos m) P⟩

private lemma minimaxRedundancy_set_bddBelow (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) :
    BddBelow { R : ℝ | ∃ Q : ProbDist (Fin n → α),
      (∀ x, 0 < Q.pmf x) ∧ ∀ P : ProbDist α, klDivergence (iidDist P n) Q ≤ R } := by
  refine ⟨0, fun R hR => ?_⟩
  obtain ⟨Q, hQpos, hQle⟩ := hR
  exact le_trans (klDivergence_nonneg (iidDist ProbDist.uniform n) Q
    (absCont_of_pos _ Q hQpos)) (hQle ProbDist.uniform)

theorem minimaxRedundancy_nonneg (α : Type*) [Fintype α] [Nonempty α] (n : ℕ) :
    0 ≤ minimaxRedundancy α n :=
  le_csInf (minimaxRedundancy_set_nonempty α n) fun R hR => by
    obtain ⟨Q, hQpos, hQle⟩ := hR
    exact le_trans (klDivergence_nonneg (iidDist ProbDist.uniform n) Q
      (absCont_of_pos _ Q hQpos)) (hQle ProbDist.uniform)

/-- Minimax KL redundancy upper bound from Krichevsky–Trofimov:
    `minimaxRedundancy α n ≤ ((k - 1)/2) log₂(n + 1) + 2` for all `n ≥ 1`. -/
theorem minimaxRedundancy_le_kt (α : Type*) [Fintype α] [Nonempty α] {n : ℕ} (hn : 0 < n) :
    minimaxRedundancy α n ≤
      (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 ((n : ℝ) + 1) + 2 :=
  csInf_le (minimaxRedundancy_set_bddBelow α n)
    ⟨ktDist α n, ktDist_pos α n, fun P => kt_kl_redundancy_le hn P⟩

/-! #### 3.3 Matching Minimax Redundancy Lower Bound (`((k - 1)/2) log₂ n - C_k`) -/

/-- Subadditivity of entropy over a finite vector of random variables:
    `H(X_0, …, X_{d-1}) ≤ ∑_j H(X_j)`. -/
private lemma shannonEntropy_pi_le_sum {β : Type*} [Fintype β] :
    ∀ (d : ℕ) (P : ProbDist (Fin d → β)),
      shannonEntropy P ≤ ∑ j : Fin d, shannonEntropy (P.map (fun f => f j))
  | 0, P => by
    have hle := shannonEntropy_le_log2_card P
    rw [Fintype.card_unique] at hle
    simp only [Nat.cast_one, log2_one] at hle
    simpa using hle
  | d + 1, P => by
    have hsub := shannonEntropy_subadd (P.map (finSuccEquiv β d))
    rw [shannonEntropy_map_equiv] at hsub
    have hfst : (P.map (finSuccEquiv β d)).fst = P.map (fun f (i : Fin d) => f i.castSucc) := by
      classical
      cases h1 : (P.map (finSuccEquiv β d)).fst with | mk p1 _ _ =>
      cases h2 : P.map (fun f (i : Fin d) => f i.castSucc) with | mk p2 _ _ =>
      congr; funext y
      have hp1 : p1 y = ((P.map (finSuccEquiv β d)).fst).pmf y :=
        congrArg (fun Q => Q.pmf y) h1.symm
      have hp2 : p2 y = (P.map (fun f (i : Fin d) => f i.castSucc)).pmf y :=
        congrArg (fun Q => Q.pmf y) h2.symm
      rw [hp1, hp2]
      unfold ProbDist.fst ProbDist.map; dsimp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (x (Fin.last d))]
      · simp [finSuccEquiv]
      · intro b _ hne
        have : finSuccEquiv β d x ≠ (y, b) := fun h => hne (congrArg Prod.snd h).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsnd : (P.map (finSuccEquiv β d)).snd = P.map (fun f => f (Fin.last d)) := by
      classical
      cases h1 : (P.map (finSuccEquiv β d)).snd with | mk p1 _ _ =>
      cases h2 : P.map (fun f => f (Fin.last d)) with | mk p2 _ _ =>
      congr; funext b
      have hp1 : p1 b = ((P.map (finSuccEquiv β d)).snd).pmf b :=
        congrArg (fun Q => Q.pmf b) h1.symm
      have hp2 : p2 b = (P.map (fun f => f (Fin.last d))).pmf b :=
        congrArg (fun Q => Q.pmf b) h2.symm
      rw [hp1, hp2]
      unfold ProbDist.snd ProbDist.map; dsimp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (fun i : Fin d => x i.castSucc)]
      · simp [finSuccEquiv]
      · intro y _ hne
        have : finSuccEquiv β d x ≠ (y, b) := fun h => hne (congrArg Prod.fst h).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hfst, hsnd] at hsub
    have hih := shannonEntropy_pi_le_sum d (P.map (fun f (i : Fin d) => f i.castSucc))
    simp_rw [map_comp_eq] at hih
    have hsum_eq : ∑ x : Fin d, shannonEntropy (P.map ((fun f => f x) ∘ fun f i => f i.castSucc)) =
        ∑ i : Fin d, shannonEntropy (P.map (fun f => f i.castSucc)) := rfl
    rw [hsum_eq] at hih
    rw [Fin.sum_univ_castSucc]
    linarith

/-- Variance of empirical frequency `f_a(X^n) = N(a | X^n) / n` under `iidDist P n` equals
    `P(a)(1 - P(a)) / n ≤ 1 / (4n)`. -/
private lemma iidDist_empiricalFreq_var {α : Type*} [Fintype α] [DecidableEq α]
    (P : ProbDist α) {n : ℕ} (hn : 0 < n) (a : α) :
    ∑ x : Fin n → α, (iidDist P n).pmf x *
        ((typeCount x a : ℝ) / (n : ℝ) - P.pmf a) ^ 2 ≤ 1 / (4 * (n : ℝ)) := by
  let Z : α → ℝ := fun b => (if b = a then (1 : ℝ) else 0) - P.pmf a
  have hEZ : ∑ b : α, P.pmf b * Z b = 0 := by
    simp_rw [Z, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
    have h1 : ∑ b : α, P.pmf b * (if b = a then (1 : ℝ) else 0) = P.pmf a := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [h1, sub_self]
  have hEZ2 : ∑ b : α, P.pmf b * (Z b * Z b) = P.pmf a * (1 - P.pmf a) := by
    have hterm : ∀ b : α, P.pmf b * (Z b * Z b) =
        (if b = a then P.pmf a * (1 - 2 * P.pmf a) else 0) + P.pmf b * (P.pmf a) ^ 2 := by
      intro b
      by_cases hba : b = a
      · subst hba; simp only [Z, ↓reduceIte]; ring
      · simp only [Z, hba, ↓reduceIte]; ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
    rw [Finset.sum_eq_single a]
    · simp; ring
    · intro b _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hsumZ : ∀ x : Fin n → α,
      ∑ i : Fin n, Z (x i) = (typeCount x a : ℝ) - (n : ℝ) * P.pmf a := by
    intro x
    simp_rw [Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    congr 1
    rw [typeCount_eq_card_aux]
    simp [Finset.sum_boole]
  have hVar : ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
      (n : ℝ) * (P.pmf a * (1 - P.pmf a)) := by
    have hsq : ∀ x : Fin n → α,
        (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
          ∑ i : Fin n, ∑ j : Fin n, (iidDist P n).pmf x * (Z (x i) * Z (x j)) := by
      intro x
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    trans (∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → α, (iidDist P n).pmf x * (Z (x i) * Z (x j)))
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    · trans (∑ _i : Fin n, P.pmf a * (1 - P.pmf a))
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · rw [iidDist_sum_coord P (fun b => Z b * Z b) i, hEZ2]
        · intro j _ hji
          rw [iidDist_sum_two_coords P Z Z hji.symm, hEZ, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrew : ∀ x : Fin n → α,
      (iidDist P n).pmf x * ((typeCount x a : ℝ) / (n : ℝ) - P.pmf a) ^ 2 =
        ((iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2) / (n : ℝ) ^ 2 := by
    intro x
    rw [hsumZ x]
    field_simp [ne_of_gt hnpos]
  simp_rw [hrew]
  rw [← Finset.sum_div, hVar]
  have hpq : P.pmf a * (1 - P.pmf a) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (P.pmf a - 1 / 2)]
  calc (n : ℝ) * (P.pmf a * (1 - P.pmf a)) / (n : ℝ) ^ 2
    _ ≤ (n : ℝ) * (1 / 4) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpq (le_of_lt hnpos)) (by positivity)
    _ = 1 / (4 * (n : ℝ)) := by field_simp [ne_of_gt hnpos]

/-- Geometric tail sum bound: `∑_{z : Fin (2m + 1)} 2^{-|(z : ℤ) - m|} ≤ 3`. -/
private lemma sum_two_neg_abs_le_three (m : ℕ) :
    ∑ z : Fin (2 * m + 1), (2 : ℝ) ^ (-(((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ)) ≤ 3 := by
  have hrange : ∑ z : Fin (2 * m + 1), (2 : ℝ) ^ (-(((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ)) =
      ∑ z ∈ Finset.range (2 * m + 1), (2 : ℝ) ^ (-(((z : ℤ) - (m : ℤ)).natAbs : ℝ)) :=
    Fin.sum_univ_eq_sum_range (fun z : ℕ => (2 : ℝ) ^ (-(((z : ℤ) - (m : ℤ)).natAbs : ℝ))) _
  rw [hrange]
  have hexact : ∀ r : ℕ,
      ∑ z ∈ Finset.range (2 * r + 1), (2 : ℝ) ^ (-(((z : ℤ) - (r : ℤ)).natAbs : ℝ)) =
        3 - 2 * (2 : ℝ) ^ (-(r : ℝ)) := by
    intro r
    induction r with
    | zero => simp; norm_num
    | succ j ihj =>
      have hlen : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by omega
      rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ']
      have hmid : ∑ k ∈ Finset.range (2 * j + 1),
            (2 : ℝ) ^ (-((((k + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)).natAbs : ℝ)) =
          ∑ z ∈ Finset.range (2 * j + 1),
            (2 : ℝ) ^ (-(((z : ℤ) - (j : ℤ)).natAbs : ℝ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hnat : (((k + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)).natAbs =
            ((k : ℤ) - (j : ℤ)).natAbs := by omega
        rw [hnat]
      have h0 : (((0 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)).natAbs = j + 1 := by omega
      have htop : ((((2 * j + 1) + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)).natAbs = j + 1 := by omega
      rw [hmid, h0, htop, ihj]
      have hpow : (2 : ℝ) ^ (-(j : ℝ)) = 2 * (2 : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) := by
        rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_neg_one]
        ring
      linarith
  rw [hexact m]
  have : 0 < (2 : ℝ) ^ (-(m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-- Maximum-entropy bound for an integer-valued random variable on `Fin (2m + 1)` centered at `m`:
    `H(E) ≤ E[|E - m|] + 2`. -/
private lemma shannonEntropy_le_expected_abs_add_two (m : ℕ) (P : ProbDist (Fin (2 * m + 1))) :
    shannonEntropy P ≤
      (∑ z : Fin (2 * m + 1), P.pmf z * (((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ)) + 2 := by
  let w : Fin (2 * m + 1) → ℝ := fun z => (2 : ℝ) ^ (-(((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ))
  set Z : ℝ := ∑ z : Fin (2 * m + 1), w z
  have hZpos : 0 < Z := Finset.sum_pos (fun z _ => Real.rpow_pos_of_pos (by norm_num) _) Finset.univ_nonempty
  have hZle3 : Z ≤ 3 := sum_two_neg_abs_le_three m
  let Q : ProbDist (Fin (2 * m + 1)) :=
    { pmf := fun z => w z / Z
      nonneg := fun z => div_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) (le_of_lt hZpos)
      sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hZpos) }
  have hQpos : ∀ z, 0 < Q.pmf z := fun z => div_pos (Real.rpow_pos_of_pos (by norm_num) _) hZpos
  have hkl : 0 ≤ klDivergence P Q := klDivergence_nonneg P Q (absCont_of_pos P Q hQpos)
  have hcross := crossEntropy_eq_entropy_add_kl P Q hQpos
  have hneglog : ∀ z : Fin (2 * m + 1),
      -log2 (Q.pmf z) = (((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ) + log2 Z := by
    intro z
    change -log2 (w z / Z) = _
    rw [log2_div_pos (Real.rpow_pos_of_pos (by norm_num) _) hZpos, log2_two_rpow]
    ring
  simp_rw [hneglog, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, one_mul] at hcross
  have hlogZ : log2 Z ≤ 2 := by
    calc log2 Z ≤ log2 4 := log2_le_log2 hZpos (by linarith)
      _ = 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, log2_pow_nat, log2_two]; norm_num
  linarith

/-- Rounding-error inequality: for `u < m` and `y ≥ 0`, setting `r = min (m - 1) ⌊y + 1/2⌋₊`,
    `|(u : ℝ) - r| ≤ (u - y)² + 3/4`. -/
private lemma round_abs_le_sq_add (m u : ℕ) (hu : u < m) {y : ℝ} (hy : 0 ≤ y) :
    |(u : ℝ) - (min (m - 1) ⌊y + 1 / 2⌋₊ : ℕ)| ≤ ((u : ℝ) - y) ^ 2 + 3 / 4 := by
  have habs_tri : |(u : ℝ) - (min (m - 1) ⌊y + 1 / 2⌋₊ : ℕ)| ≤ |(u : ℝ) - y| + 1 / 2 := by
    by_cases hle : ⌊y + 1 / 2⌋₊ ≤ m - 1
    · rw [Nat.min_eq_right hle]
      have hfl1 : (⌊y + 1 / 2⌋₊ : ℝ) ≤ y + 1 / 2 := Nat.floor_le (by linarith)
      have hfl2 : y + 1 / 2 < (⌊y + 1 / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (y + 1 / 2)
      have hyr : |y - (⌊y + 1 / 2⌋₊ : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc |(u : ℝ) - (⌊y + 1 / 2⌋₊ : ℝ)|
        _ = |((u : ℝ) - y) + (y - (⌊y + 1 / 2⌋₊ : ℝ))| := by ring_nf
        _ ≤ |(u : ℝ) - y| + |y - (⌊y + 1 / 2⌋₊ : ℝ)| := abs_add_le _ _
        _ ≤ |(u : ℝ) - y| + 1 / 2 := by linarith
    · rw [Nat.min_eq_left (by omega)]
      have hm_le : (m : ℝ) ≤ y + 1 / 2 := by
        have hlt : m - 1 < ⌊y + 1 / 2⌋₊ := by omega
        have hge : m ≤ ⌊y + 1 / 2⌋₊ := by omega
        exact le_trans (by exact_mod_cast hge) (Nat.floor_le (by linarith))
      have hum1 : (u : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show u ≤ m - 1 by omega)
      have hm1_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hm1_cast] at hum1 ⊢
      have h1 : |(u : ℝ) - ((m : ℝ) - 1)| = (m : ℝ) - 1 - (u : ℝ) := by
        rw [abs_of_nonpos (by linarith)]; ring
      have h2 : (m : ℝ) - 1 - (u : ℝ) ≤ y - (u : ℝ) + 1 / 2 := by linarith
      have h3 : y - (u : ℝ) ≤ |(u : ℝ) - y| := by
        rw [abs_sub_comm]; exact le_abs_self _
      linarith
  have hsq : |(u : ℝ) - y| ≤ ((u : ℝ) - y) ^ 2 + 1 / 4 := by
    have h1 := sq_nonneg (|(u : ℝ) - y| - 1 / 2)
    have h2 : |(u : ℝ) - y| ^ 2 = ((u : ℝ) - y) ^ 2 := sq_abs _
    nlinarith
  linarith

/-- **Matching Minimax KL Redundancy Lower Bound**:
    for every finite alphabet `α` with `k = Fintype.card α ≥ 2` and every blocklength `n ≥ 1`,
    `((k - 1)/2) log₂ n - (k - 1)(4 + log₂(k - 1)) ≤ minimaxRedundancy α n`. -/
theorem minimax_kl_redundancy_ge (α : Type*) [Fintype α]
    (hk : 2 ≤ Fintype.card α) {n : ℕ} (hn : 0 < n) :
    (((Fintype.card α - 1 : ℕ) : ℝ) / 2) * log2 (n : ℝ) -
        ((Fintype.card α - 1 : ℕ) : ℝ) * (4 + log2 ((Fintype.card α - 1 : ℕ) : ℝ)) ≤
      minimaxRedundancy α n := by
  classical
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  set d : ℕ := Fintype.card α - 1
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd1
  -- Case 1: small `n < 4 d²`, where the lower bound is ≤ 0 ≤ minimaxRedundancy α n
  by_cases hsmall : n < 4 * d ^ 2
  · have hle : (n : ℝ) ≤ (2 * (d : ℝ)) ^ 2 := by
      have : (n : ℝ) < 4 * (d : ℝ) ^ 2 := by exact_mod_cast hsmall
      nlinarith
    have hlogn : log2 (n : ℝ) ≤ 2 + 2 * log2 (d : ℝ) := by
      have h1 := log2_le_log2 (Nat.cast_pos.mpr hn) hle
      rw [log2_pow_nat, log2_mul_pos (by norm_num) hdpos, log2_two, Nat.cast_ofNat] at h1
      linarith
    have hnonpos : ((d : ℝ) / 2) * log2 (n : ℝ) - (d : ℝ) * (4 + log2 (d : ℝ)) ≤ 0 := by
      nlinarith
    exact le_trans hnonpos (minimaxRedundancy_nonneg α n)
  -- Case 2: `4 d² ≤ n`, construct the `m^d` simplex grid with `m = ⌊√n / d⌋₊ ≥ 2`
  push Not at hsmall
  have hn_ge : 4 * (d : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hsmall
  have hsqrt_ge : 2 * (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hratio_ge : 2 ≤ Real.sqrt (n : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdpos]; linarith
  set m : ℕ := ⌊Real.sqrt (n : ℝ) / (d : ℝ)⌋₊
  have hm2 : 2 ≤ m := Nat.le_floor hratio_ge
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm1
  have hdm_le : (d : ℝ) * (m : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hm_le : (m : ℝ) ≤ Real.sqrt (n : ℝ) / (d : ℝ) := Nat.floor_le (by positivity)
    exact (le_div_iff₀' hdpos).mp hm_le
  have hdm_sq_le : ((d : ℝ) * (m : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hdm0 : 0 ≤ (d : ℝ) * (m : ℝ) := by positivity
    have hsq := sq_le_sq' (by linarith [Real.sqrt_nonneg (n : ℝ)]) hdm_le
    rwa [Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
  have hm_ge_half : Real.sqrt (n : ℝ) / (2 * (d : ℝ)) ≤ (m : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.sqrt (n : ℝ) / (d : ℝ))
    have : Real.sqrt (n : ℝ) / (2 * (d : ℝ)) = (Real.sqrt (n : ℝ) / (d : ℝ)) / 2 := by ring
    linarith
  -- Identify `α ≃ Fin (d + 1)`
  let e : α ≃ Fin (d + 1) := Fintype.equivFinOfCardEq (by omega)
  let aCoord : Fin d → α := fun j => e.symm j.castSucc
  -- Grid family `P_u : ProbDist α` indexed by `u : Fin d → Fin m`
  let Pgrid : (Fin d → Fin m) → ProbDist α := fun u =>
    { pmf := fun a =>
        match Fin.lastCases none (fun j : Fin d => some j) (e a) with
        | some j => (u j : ℝ) / ((d : ℝ) * (m : ℝ))
        | none => 1 - ∑ j : Fin d, (u j : ℝ) / ((d : ℝ) * (m : ℝ))
      nonneg := fun a => by
        split
        · positivity
        · have hsum_le : ∑ j : Fin d, (u j : ℝ) / ((d : ℝ) * (m : ℝ)) ≤ 1 := by
            calc ∑ j : Fin d, (u j : ℝ) / ((d : ℝ) * (m : ℝ))
              _ ≤ ∑ _j : Fin d, (m : ℝ) / ((d : ℝ) * (m : ℝ)) := by
                  refine Finset.sum_le_sum fun j _ =>
                    div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt (u j).2) (by positivity)
              _ = (d : ℝ) * ((m : ℝ) / ((d : ℝ) * (m : ℝ))) := by simp
              _ = 1 := by field_simp [ne_of_gt hdpos, ne_of_gt hmpos]
          linarith
      sum_one := by
        have hrew := Fintype.sum_equiv e
          (fun a => match Fin.lastCases none (fun j : Fin d => some j) (e a) with
            | some j => (u j : ℝ) / ((d : ℝ) * (m : ℝ))
            | none => 1 - ∑ j : Fin d, (u j : ℝ) / ((d : ℝ) * (m : ℝ)))
          (fun i => match Fin.lastCases none (fun j : Fin d => some j) i with
            | some j => (u j : ℝ) / ((d : ℝ) * (m : ℝ))
            | none => 1 - ∑ j : Fin d, (u j : ℝ) / ((d : ℝ) * (m : ℝ)))
          (fun _ => rfl)
        rw [hrew, Fin.sum_univ_castSucc]
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
        ring }
  have hPgrid_coord : ∀ (u : Fin d → Fin m) (j : Fin d),
      (Pgrid u).pmf (aCoord j) = (u j : ℝ) / ((d : ℝ) * (m : ℝ)) := by
    intro u j
    simp [Pgrid, aCoord]
  -- Uniform prior on `Fin d → Fin m` and joint distribution `(Θ, X^n)`
  have : Nonempty (Fin m) := ⟨⟨0, hm1⟩⟩
  let W : ProbDist (Fin d → Fin m) := ProbDist.uniform
  let Pblock : (Fin d → Fin m) → ProbDist (Fin n → α) := fun u => iidDist (Pgrid u) n
  let J : ProbDist ((Fin d → Fin m) × (Fin n → α)) := jointPrior W Pblock
  -- Coordinatewise rounding estimator `g : (Fin n → α) → (Fin d → Fin m)`
  let g : (Fin n → α) → (Fin d → Fin m) := fun x j =>
    ⟨min (m - 1) ⌊(d : ℝ) * (m : ℝ) * ((typeCount x (aCoord j) : ℝ) / (n : ℝ)) + 1 / 2⌋₊,
      by omega⟩
  -- Shifted coordinatewise rounding error `err : (Fin d → Fin m) × (Fin n → α) → (Fin d → Fin (2m + 1))`
  let err : (Fin d → Fin m) × (Fin n → α) → (Fin d → Fin (2 * m + 1)) := fun ux j =>
    ⟨(ux.1 j).1 + m - (g ux.2 j).1, by have := (ux.1 j).2; have := (g ux.2 j).2; omega⟩
  -- Left-invertible encoding `enc(u, x) = (err(u, x), x)` yields `H(Θ, X^n) ≤ H(err(Θ, X^n), X^n)`
  let enc : ((Fin d → Fin m) × (Fin n → α)) → ((Fin d → Fin (2 * m + 1)) × (Fin n → α)) :=
    fun ux => (err ux, ux.2)
  let dec : ((Fin d → Fin (2 * m + 1)) × (Fin n → α)) → ((Fin d → Fin m) × (Fin n → α)) :=
    fun ex => (fun j => ⟨min (m - 1) ((ex.1 j).1 + (g ex.2 j).1 - m), by omega⟩, ex.2)
  have hdec_enc : dec ∘ enc = id := by
    funext ⟨u, x⟩
    simp only [Function.comp_apply, id_eq, enc, dec, err]
    refine Prod.ext ?_ rfl
    funext j; apply Fin.ext; dsimp only
    have hu := (u j).2; have hg := (g x j).2
    omega
  have hH_le_err : shannonEntropy J ≤ shannonEntropy (J.map err) + shannonEntropy J.snd := by
    have h1 : shannonEntropy J ≤ shannonEntropy (J.map enc) := by
      have hcomp : (J.map enc).map dec = J := by
        rw [map_comp_eq, hdec_enc]
        cases hJ : J with | mk pJ _ _ =>
        unfold ProbDist.map; congr; funext ux
        rw [Finset.sum_eq_single ux]
        · simp
        · intro a _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      calc shannonEntropy J
        _ = shannonEntropy ((J.map enc).map dec) := by rw [hcomp]
        _ ≤ shannonEntropy (J.map enc) := shannonEntropy_map_le dec (J.map enc)
    have hsub := shannonEntropy_subadd (J.map enc)
    have hfst : (J.map enc).fst = J.map err := by
      cases h1' : (J.map enc).fst with | mk p1 _ _ =>
      cases h2' : J.map err with | mk p2 _ _ =>
      congr; funext ev
      have hp1 : p1 ev = ((J.map enc).fst).pmf ev := congrArg (fun Q => Q.pmf ev) h1'.symm
      have hp2 : p2 ev = (J.map err).pmf ev := congrArg (fun Q => Q.pmf ev) h2'.symm
      rw [hp1, hp2]
      unfold ProbDist.fst ProbDist.map; dsimp only [enc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ux _ => ?_
      rw [Finset.sum_eq_single ux.2]
      · simp
      · intro x _ hne
        have : (err ux, ux.2) ≠ (ev, x) := fun h => hne (congrArg Prod.snd h).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsnd : (J.map enc).snd = J.snd := by
      cases h1' : (J.map enc).snd with | mk p1 _ _ =>
      cases h2' : J.snd with | mk p2 _ _ =>
      congr; funext x
      have hp1 : p1 x = ((J.map enc).snd).pmf x := congrArg (fun Q => Q.pmf x) h1'.symm
      have hp2 : p2 x = J.snd.pmf x := congrArg (fun Q => Q.pmf x) h2'.symm
      rw [hp1, hp2]
      unfold ProbDist.snd ProbDist.map; dsimp only [enc]
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      trans (∑ u : Fin d → Fin m, ∑ x' : Fin n → α, if x' = x then J.pmf (u, x') else 0)
      · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.sum_eq_single (err (u, x'))]
        · simp
        · intro ev _ hne
          have : (err (u, x'), x') ≠ (ev, x) := fun h => hne (congrArg Prod.fst h).symm
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_eq_single x]
        · simp
        · intro x' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
    rw [hfst, hsnd] at hsub
    exact le_trans h1 hsub
  -- Bound `H(err(Θ, X^n)) ≤ ∑_j H(err_j(Θ, X^n)) ≤ 3 d`
  have hHerr_coord : ∀ j : Fin d,
      shannonEntropy ((J.map err).map (fun ev => ev j)) ≤ 3 := by
    intro j
    have hgibbs := shannonEntropy_le_expected_abs_add_two m ((J.map err).map (fun ev => ev j))
    rw [map_comp_eq] at hgibbs
    -- Expand `∑ z, P(err_j = z) * |z - m|` as expectation over `(u, x) ~ J`
    have hexp_eq : ∑ z : Fin (2 * m + 1),
          (J.map ((fun ev : Fin d → Fin (2 * m + 1) => ev j) ∘ err)).pmf z *
            (((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ) =
        ∑ u : Fin d → Fin m, W.pmf u *
          ∑ x : Fin n → α, (Pblock u).pmf x *
            |(u j : ℝ) - ((g x j).1 : ℝ)| := by
      unfold ProbDist.map; dsimp only [Function.comp_apply]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (err (u, x) j)]
      · simp only [↓reduceIte]
        have habs_eq : ((((err (u, x) j).1 : ℤ) - (m : ℤ)).natAbs : ℝ) =
            |(u j : ℝ) - ((g x j).1 : ℝ)| := by
          have hz : ((err (u, x) j).1 : ℤ) - (m : ℤ) = ((u j).1 : ℤ) - ((g x j).1 : ℤ) := by
            dsimp only [err]; have := (u j).2; have := (g x j).2; omega
          rw [hz, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub,
            Int.cast_natCast, Int.cast_natCast]
        rw [habs_eq]
        change W.pmf u * (Pblock u).pmf x * _ = _
        ring
      · intro z _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    -- For every `u`, `E_{P_u^n}[|u_j - g_j(X^n)|] ≤ 1`
    have hinner_le : ∀ u : Fin d → Fin m,
        ∑ x : Fin n → α, (Pblock u).pmf x * |(u j : ℝ) - ((g x j).1 : ℝ)| ≤ 1 := by
      intro u
      have hpt : ∀ x : Fin n → α,
          |(u j : ℝ) - ((g x j).1 : ℝ)| ≤
            ((d : ℝ) * (m : ℝ)) ^ 2 *
              ((typeCount x (aCoord j) : ℝ) / (n : ℝ) - (Pgrid u).pmf (aCoord j)) ^ 2 + 3 / 4 := by
        intro x
        have hy : 0 ≤ (d : ℝ) * (m : ℝ) * ((typeCount x (aCoord j) : ℝ) / (n : ℝ)) := by positivity
        have hr := round_abs_le_sq_add m (u j).1 (u j).2 hy
        have hsq_eq : ((u j : ℝ) - (d : ℝ) * (m : ℝ) * ((typeCount x (aCoord j) : ℝ) / (n : ℝ))) ^ 2 =
            ((d : ℝ) * (m : ℝ)) ^ 2 *
              ((typeCount x (aCoord j) : ℝ) / (n : ℝ) - (Pgrid u).pmf (aCoord j)) ^ 2 := by
          rw [hPgrid_coord u j]
          field_simp [ne_of_gt hdpos, ne_of_gt hmpos]
          ring
        rw [← hsq_eq]
        exact hr
      calc ∑ x : Fin n → α, (Pblock u).pmf x * |(u j : ℝ) - ((g x j).1 : ℝ)|
        _ ≤ ∑ x : Fin n → α, (Pblock u).pmf x *
              (((d : ℝ) * (m : ℝ)) ^ 2 *
                ((typeCount x (aCoord j) : ℝ) / (n : ℝ) - (Pgrid u).pmf (aCoord j)) ^ 2 + 3 / 4) :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) ((Pblock u).nonneg x)
        _ = ((d : ℝ) * (m : ℝ)) ^ 2 *
              (∑ x : Fin n → α, (Pblock u).pmf x *
                ((typeCount x (aCoord j) : ℝ) / (n : ℝ) - (Pgrid u).pmf (aCoord j)) ^ 2) +
            3 / 4 := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (Pblock u).sum_one, one_mul,
              Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun x _ => by ring
        _ ≤ ((d : ℝ) * (m : ℝ)) ^ 2 * (1 / (4 * (n : ℝ))) + 3 / 4 := by
            have hvar := iidDist_empiricalFreq_var (Pgrid u) hn (aCoord j)
            linarith [mul_le_mul_of_nonneg_left hvar (sq_nonneg ((d : ℝ) * (m : ℝ)))]
        _ ≤ 1 := by
            have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
            have hq : ((d : ℝ) * (m : ℝ)) ^ 2 * (1 / (4 * (n : ℝ))) ≤ 1 / 4 := by
              rw [mul_one_div, div_le_iff₀ (by positivity)]
              linarith
            linarith
    have hE_le : ∑ z : Fin (2 * m + 1),
          (J.map ((fun ev : Fin d → Fin (2 * m + 1) => ev j) ∘ err)).pmf z *
            (((z.1 : ℤ) - (m : ℤ)).natAbs : ℝ) ≤ 1 := by
      rw [hexp_eq]
      calc ∑ u : Fin d → Fin m, W.pmf u *
              ∑ x : Fin n → α, (Pblock u).pmf x * |(u j : ℝ) - ((g x j).1 : ℝ)|
        _ ≤ ∑ u : Fin d → Fin m, W.pmf u * 1 :=
            Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hinner_le u) (W.nonneg u)
        _ = 1 := by simp [W.sum_one]
    rw [map_comp_eq]
    linarith
  have hHerr_le : shannonEntropy (J.map err) ≤ 3 * (d : ℝ) := by
    calc shannonEntropy (J.map err)
      _ ≤ ∑ j : Fin d, shannonEntropy ((J.map err).map (fun ev => ev j)) :=
          shannonEntropy_pi_le_sum d (J.map err)
      _ ≤ ∑ _j : Fin d, (3 : ℝ) := Finset.sum_le_sum fun j _ => hHerr_coord j
      _ = 3 * (d : ℝ) := by simp [mul_comm]
  -- Compute `H(Θ) = d * log2 m`
  have hHW : shannonEntropy J.fst = (d : ℝ) * log2 (m : ℝ) := by
    rw [jointPrior_fst]
    have hcard : Fintype.card (Fin d → Fin m) = m ^ d := by simp
    have huni := (shannonEntropy_eq_log2_card_iff W).mpr rfl
    rw [huni, hcard, Nat.cast_pow, log2_pow_nat]
  -- Lower bound `I(Θ; X^n) = H(Θ) + H(X^n) - H(Θ, X^n) ≥ d * log2 m - 3 d`
  have hMI_ge : ((d : ℝ) / 2) * log2 (n : ℝ) - (d : ℝ) * (4 + log2 (d : ℝ)) ≤ mutualInfo J := by
    have hlogm : log2 (n : ℝ) / 2 - 1 - log2 (d : ℝ) ≤ log2 (m : ℝ) := by
      have h1 := log2_le_log2 (div_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) (by positivity))
        hm_ge_half
      rw [log2_div_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) (by positivity),
        log2_sqrt (Nat.cast_nonneg n), log2_mul_pos (by norm_num) hdpos, log2_two] at h1
      linarith
    have hmi_def : mutualInfo J = shannonEntropy J.fst + shannonEntropy J.snd - shannonEntropy J := rfl
    have hmul_log := mul_le_mul_of_nonneg_left hlogm (le_of_lt hdpos)
    linarith
  -- Apply Capacity–Redundancy (`redundancy_ge_mutualInfo`) to every strictly positive `Q`
  refine le_csInf (minimaxRedundancy_set_nonempty α n) fun R hR => ?_
  obtain ⟨Q, hQpos, hQle⟩ := hR
  obtain ⟨_, u, hu⟩ := redundancy_ge_mutualInfo W Pblock Q (fun _ _ => absCont_of_pos _ Q hQpos)
  exact le_trans hMI_ge (le_trans hu (hQle (Pgrid u)))

/-- Helper: `log2 (n : ℝ) → +∞` as `n → ∞`. -/
private lemma tendsto_log2_nat_atTop :
    Filter.Tendsto (fun n : ℕ => log2 (n : ℝ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Nat.ceil (Real.exp (max M 0 * Real.log 2)) + 1, fun n hn => ?_⟩
  have hexp_le : Real.exp (max M 0 * Real.log 2) ≤ (n : ℝ) := by
    have h1 : Real.exp (max M 0 * Real.log 2) ≤ (Nat.ceil (Real.exp (max M 0 * Real.log 2)) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (max M 0 * Real.log 2)) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (Nat.le_succ _) hn
    linarith
  have hlog_le : max M 0 * Real.log 2 ≤ Real.log (n : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hexp_le
    rwa [Real.log_exp] at this
  have hdiv : max M 0 ≤ log2 (n : ℝ) := (le_div_iff₀ hlog2).mpr hlog_le
  exact le_trans (le_max_left M 0) hdiv

/-- Helper: `C / log2 (n : ℝ) → 0` as `n → ∞`. -/
private lemma tendsto_const_div_log2_atTop (C : ℝ) :
    Filter.Tendsto (fun n : ℕ => C / log2 (n : ℝ)) Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun n : ℕ => (log2 (n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log2_nat_atTop
  have hmul := hinv.const_mul C
  simp only [mul_zero] at hmul
  simpa [div_eq_mul_inv] using hmul

/-- **Exact Asymptotics of Minimax KL Redundancy** (Krichevsky & Trofimov 1981; Rissanen 1984):
    for EVERY nonempty finite alphabet `α` of size `k`,
    `minimaxRedundancy α n / log₂ n → (k - 1) / 2` as `n → ∞`. -/
theorem minimax_kl_redundancy_asymptotics (α : Type*) [Fintype α] [Nonempty α] :
    Filter.Tendsto (fun n : ℕ => minimaxRedundancy α n / log2 (n : ℝ))
      Filter.atTop (nhds (((Fintype.card α - 1 : ℕ) : ℝ) / 2)) := by
  by_cases hk1 : Fintype.card α = 1
  · -- Degenerate alphabet `|α| = 1`: `minimaxRedundancy α n = 0` for all `n ≥ 1`
    have hzero : ∀ n : ℕ, 1 ≤ n → minimaxRedundancy α n = 0 := by
      intro n hn
      have hge := minimaxRedundancy_nonneg α n
      have hle : minimaxRedundancy α n ≤ 0 := by
        refine csInf_le (minimaxRedundancy_set_bddBelow α n) ⟨ktDist α n, ktDist_pos α n, fun P => ?_⟩
        have h := kt_kl_redundancy_le_card hn P
        simp only [hk1, Nat.sub_self, Nat.cast_zero, zero_div, zero_mul, add_zero] at h
        exact h
      exact le_antisymm hle hge
    simp only [hk1, Nat.sub_self, Nat.cast_zero, zero_div]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp [hzero n hn]
  · -- General case `|α| ≥ 2`: squeeze between `minimax_kl_redundancy_ge` and `minimaxRedundancy_le_kt`
    have hk2 : 2 ≤ Fintype.card α := by
      have := Fintype.card_pos (α := α); omega
    set c : ℝ := ((Fintype.card α - 1 : ℕ) : ℝ) / 2
    set C_lo : ℝ := ((Fintype.card α - 1 : ℕ) : ℝ) *
      (4 + log2 ((Fintype.card α - 1 : ℕ) : ℝ))
    set C_hi : ℝ := c + 2
    have hlo_tendsto : Filter.Tendsto (fun n : ℕ => c - C_lo / log2 (n : ℝ))
        Filter.atTop (nhds c) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_log2_atTop C_lo)
    have hhi_tendsto : Filter.Tendsto (fun n : ℕ => c + C_hi / log2 (n : ℝ))
        Filter.atTop (nhds c) := by
      simpa using tendsto_const_nhds.add (tendsto_const_div_log2_atTop C_hi)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_tendsto hhi_tendsto ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn0 : 0 < n := by omega
      have hlogpos : 0 < log2 (n : ℝ) := log2_pos_of_gt_one (by exact_mod_cast (show 1 < n by omega))
      have hge := minimax_kl_redundancy_ge α hk2 hn0
      have hdiv := div_le_div_of_nonneg_right hge (le_of_lt hlogpos)
      rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hlogpos)] at hdiv
      exact hdiv
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn0 : 0 < n := by omega
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
      have hlogpos : 0 < log2 (n : ℝ) := log2_pos_of_gt_one (by exact_mod_cast (show 1 < n by omega))
      have hle := minimaxRedundancy_le_kt α hn0
      have hlog_n1 : log2 ((n : ℝ) + 1) ≤ log2 (n : ℝ) + 1 := by
        have hle2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
          linarith
        calc log2 ((n : ℝ) + 1)
          _ ≤ log2 (2 * (n : ℝ)) := log2_le_log2 (by positivity) hle2n
          _ = log2 2 + log2 (n : ℝ) := log2_mul_pos (by norm_num) hnpos
          _ = log2 (n : ℝ) + 1 := by rw [log2_two]; ring
      have hc0 : 0 ≤ c := by positivity
      have hle' : minimaxRedundancy α n ≤ c * log2 (n : ℝ) + C_hi := by
        have hle_c : minimaxRedundancy α n ≤ c * log2 ((n : ℝ) + 1) + 2 := hle
        dsimp only [C_hi]
        nlinarith
      have hdiv := div_le_div_of_nonneg_right hle' (le_of_lt hlogpos)
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hlogpos)] at hdiv
      exact hdiv

end MinimaxRedundancy

end InfoTheory.Bridge

