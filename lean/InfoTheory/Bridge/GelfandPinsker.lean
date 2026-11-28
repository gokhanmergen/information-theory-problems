import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.MethodOfTypes
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.RateDistortion
import InfoTheory.Bridge.WynerZiv

/-!
# Gelfand–Pinsker Theorem: Channel Coding with Noncausal Transmitter State Information
(Gelfand & Pinsker 1980; El Gamal & Kim Theorem 7.3, §7.4; Cover & Thomas §7.13)

Purely additive, kernel-verified formalization of the Gelfand–Pinsker coding theorem for
discrete memoryless state-dependent channels `W(y | x, s)` with i.i.d. state `S ~ Ps` known
noncausally at the encoder:

1. **State-Dependent Channel Model & Single-Letter Gelfand–Pinsker Capacity**:
   - `StateChannel`, `gpDetJoint`, `gpStochJoint`
   - `gelfandPinskerCapacity`, `gelfandPinskerCapacityStoch`
   - `gelfandPinskerCapacity_ge_det`, `gelfandPinskerCapacity_ge_stoch`
   - `gelfandPinskerCapacity_eq_stochastic` (functional representation via product law on `S → X`)
   - `gelfandPinskerCapacity_nonneg`, `gelfandPinskerCapacity_le_log2_card_output`
   - `gelfandPinskerCapacity_ignore_state` (reduces to standard DMC capacity `W₀.capacity` when
     `W(y | x, s) = W₀(y | x)` ignores the state)

2. **Operational Model & Converse (`gpCode_mutualInfo_le`, `gpCode_rate_converse`,
   `gelfand_pinsker_converse`)**:
   - `GelfandPinskerCode`, `gpCodeJoint`, `gpAvgError`, `IsGPAchievable`, `gpOperationalCapacity`
   - `gpCode_mutualInfo_le`: `I(M; Y^n) ≤ n · gelfandPinskerCapacity Ps W`, proved via forward
     and backward mutual-information chain rules, `csiszar_sum_identity` conditioned on `M`,
     i.i.d. state independence `S_i ⊥ S_{>i}`, and single-letter stochastic identification
     `U_i = (M, Y^{<i}, S_{>i})`
   - `gpCode_rate_converse` (Fano + single-letterization) and `gelfand_pinsker_converse`

3. **Pointwise Slice Packing, Achievability & Exact Coding Theorem**:
   - `jointTypicalSet_slice_indep_prob_le` (for every fixed `y`, `P_X^n({x : (x, y) ∈ A_ε^(n)})
     ≤ 2^{-n(I(X; Y) - 3ε)}`)
   - `isGPAchievable_zero`, `gp_achievable_of_det_aux`, `gelfand_pinsker_achievability`
     (combining `covering_lemma_subset`, `markov_lemma_of_channel`, and
     `jointTypicalSet_slice_indep_prob_le`)
   - `gelfand_pinsker_theorem`: `gpOperationalCapacity Ps W = gelfandPinskerCapacity Ps W`
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Private Helper Lemmas -/

section GPHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma gp_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

private lemma gp_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma gp_probDist_map_id (P : ProbDist α) : P.map id = P := by
  classical
  apply gp_probDist_ext; intro a
  unfold ProbDist.map; dsimp only
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma gp_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  apply gp_probDist_ext; intro a
  unfold ProbDist.map ProbDist.fst; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma gp_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  apply gp_probDist_ext; intro b
  unfold ProbDist.map ProbDist.snd; dsimp only
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single b]
  · simp
  · intro b' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma gp_shannonEntropy_map_eq_of_equiv (P : ProbDist α) (f : α → β) (g : α → γ)
    (e : β ≃ γ) (h : ∀ a, e (f a) = g a) :
    shannonEntropy (P.map f) = shannonEntropy (P.map g) := by
  rw [← shannonEntropy_map_equiv e (P.map f), map_comp_eq]
  congr 2; exact funext h

private lemma gp_shannonEntropy_eq_zero_of_unique [Unique α] (P : ProbDist α) :
    shannonEntropy P = 0 := by
  have hle := shannonEntropy_le_log2_card P
  have hge := shannonEntropy_nonneg P
  rw [Fintype.card_unique] at hle
  simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
  exact le_antisymm hle hge

private lemma gp_mutualInfo_eq_zero_of_unique_left [Unique α] (P : ProbDist (α × β)) :
    mutualInfo P = 0 := by
  have h0 : 0 ≤ mutualInfo P := mutualInfo_nonneg P
  have h1 : shannonEntropy P.fst = 0 := gp_shannonEntropy_eq_zero_of_unique P.fst
  have h2 : 0 ≤ condEntropy P := condEntropy_nonneg P
  unfold mutualInfo condEntropy at *
  linarith

private lemma gp_mutualInfo_map_equiv_left (P : ProbDist (α × β)) (e : α ≃ γ) :
    mutualInfo (P.map (fun ab => (e ab.1, ab.2))) = mutualInfo P := by
  classical
  let eProd : (α × β) ≃ (γ × β) := Equiv.prodCongr e (Equiv.refl β)
  have hAll : shannonEntropy (P.map (fun ab => (e ab.1, ab.2))) = shannonEntropy P :=
    shannonEntropy_map_equiv eProd P
  have hFst : shannonEntropy (P.map (fun ab => (e ab.1, ab.2))).fst = shannonEntropy P.fst := by
    rw [← gp_probDist_map_fst, map_comp_eq]
    have hcomp : (Prod.fst ∘ fun ab : α × β => (e ab.1, ab.2)) = e ∘ Prod.fst := rfl
    rw [hcomp, ← map_comp_eq, gp_probDist_map_fst, shannonEntropy_map_equiv e]
  have hSnd : (P.map (fun ab => (e ab.1, ab.2))).snd = P.snd := by
    rw [← gp_probDist_map_snd, map_comp_eq, ← gp_probDist_map_snd]; rfl
  unfold mutualInfo
  rw [hAll, hFst, hSnd]

private lemma gp_mutualInfo_map_equiv_right (P : ProbDist (α × β)) (e : β ≃ γ) :
    mutualInfo (P.map (fun ab => (ab.1, e ab.2))) = mutualInfo P := by
  have h1 : P.map (fun ab => (ab.1, e ab.2)) =
      ((P.map Prod.swap).map (fun ba => (e ba.1, ba.2))).map Prod.swap := by
    rw [map_comp_eq, map_comp_eq]; rfl
  rw [h1, mutualInfo_swap, gp_mutualInfo_map_equiv_left, mutualInfo_swap]

private lemma gp_mutualInfo_prod_eq_zero (P : ProbDist α) (Q : ProbDist β) :
    mutualInfo (P.prod Q) = 0 := by
  have hfst : (P.prod Q).fst = P := by
    apply gp_probDist_ext; intro a
    unfold ProbDist.fst ProbDist.prod; dsimp only
    rw [← Finset.mul_sum, Q.sum_one, mul_one]
  have hsnd : (P.prod Q).snd = Q := by
    apply gp_probDist_ext; intro b
    unfold ProbDist.snd ProbDist.prod; dsimp only
    rw [← Finset.sum_mul, P.sum_one, one_mul]
  rw [mutualInfo_eq_zero_iff_indep, hfst, hsnd]

private lemma gp_log2_two_rpow (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma gp_log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma gp_binaryEntropy_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p ≤ 1 := by
  let B : ProbDist Bool := ProbDist.bernoulli p hp0 hp1
  have hsh : shannonEntropy B = binaryEntropy p := by
    unfold shannonEntropy binaryEntropy B ProbDist.bernoulli; simp
  have hle := shannonEntropy_le_log2_card B
  rw [hsh, Fintype.card_bool] at hle
  have hlog2 : log2 ((2 : ℕ) : ℝ) = 1 := by
    unfold log2
    simp [div_self (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
  linarith

private lemma gp_sum_fin_telescope (n : ℕ) (h : ℕ → ℝ) :
    ∑ i : Fin n, (h (i.1 + 1) - h i.1) = h n - h 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]; ring

private lemma gp_exists_le_of_expectation_le {Ω : Type*} [Fintype Ω] (W : ProbDist Ω)
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

private lemma gp_max_one_floor_two_rpow_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
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

private lemma gp_covering_exp_le {I R ε c : ℝ} (hI : 0 ≤ I) (hε : 0 ≤ ε)
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
    rw [div_le_iff₀ hc]; linarith
  have ht_ge : 1 / c ≤ (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by linarith
  have hexp_ge : 1 / c ≤ Real.exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))) := by
    have h := Real.add_one_le_exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))))
    linarith
  rw [Real.exp_neg]
  have hpos_inv : (0 : ℝ) < 1 / c := by positivity
  calc (Real.exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))))⁻¹
    _ ≤ (1 / c)⁻¹ := inv_anti₀ hpos_inv hexp_ge
    _ = c := by rw [one_div, inv_inv]

private lemma gp_two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
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
  have hmul2 : (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ 1 := by
    calc (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) * (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_right hexp (le_of_lt hpos)
      _ = 1 := by rw [mul_comm, hmul1]
  have hmul3 := mul_le_mul_of_nonneg_left hmul2 (le_of_lt hc)
  have hsimp : c * ((1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))) = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
    field_simp [ne_of_gt hc]
  linarith

/-- Chain rule for mutual information: `I((A, B); C) = I(A; C) + I(B; C | A)`. -/
private lemma gp_mutualInfo_pair_eq_add_condMutualInfo (P : ProbDist (α × β × γ)) :
    mutualInfo (P.map (fun t => ((t.1, t.2.1), t.2.2))) =
      mutualInfo (P.map (fun t => (t.1, t.2.2))) +
      condMutualInfo (P.map (fun t => (t.2.1, t.2.2, t.1))) := by
  let P1 : ProbDist ((α × β) × γ) := P.map (fun t => ((t.1, t.2.1), t.2.2))
  let P2 : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  let P3 : ProbDist (β × γ × α) := P.map (fun t => (t.2.1, t.2.2, t.1))
  have hP1_ent : shannonEntropy P1 = shannonEntropy P := by
    let e : (α × β × γ) ≃ ((α × β) × γ) :=
      { toFun := fun t => ((t.1, t.2.1), t.2.2)
        invFun := fun t => (t.1.1, t.1.2, t.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    exact shannonEntropy_map_equiv e P
  have hP3_ent : shannonEntropy P3 = shannonEntropy P := by
    let e : (α × β × γ) ≃ (β × γ × α) :=
      { toFun := fun t => (t.2.1, t.2.2, t.1)
        invFun := fun t => (t.2.2, t.1, t.2.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact shannonEntropy_map_equiv e P
  have hP1_fst : shannonEntropy P1.fst = shannonEntropy (P3.map (fun t => (t.1, t.2.2))) := by
    rw [← gp_probDist_map_fst, map_comp_eq, map_comp_eq]
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ (Equiv.prodComm α β) (fun _ => rfl)
  have hP1_snd : P1.snd = P2.snd := by
    rw [← gp_probDist_map_snd, ← gp_probDist_map_snd, map_comp_eq, map_comp_eq]; rfl
  have hP2_fst : P2.fst = P3.map (fun t => t.2.2) := by
    rw [← gp_probDist_map_fst, map_comp_eq, map_comp_eq]; rfl
  have hP3_yz : shannonEntropy (P3.map (fun t => (t.2.1, t.2.2))) = shannonEntropy P2 := by
    rw [map_comp_eq]
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ (Equiv.prodComm γ α) (fun _ => rfl)
  unfold mutualInfo condMutualInfo
  dsimp only
  rw [hP1_ent, hP3_ent, hP1_fst, hP1_snd, hP2_fst, hP3_yz]
  ring

/-- Conditioned mixture distribution `(i, x) ↦ w(i) * (Q i)(x)` on `ι × τ`. -/
private def gpCondMix {ι τ : Type*} [Fintype ι] [Fintype τ]
    (w : ProbDist ι) (Q : ι → ProbDist τ) : ProbDist (ι × τ) where
  pmf := fun it => w.pmf it.1 * (Q it.1).pmf it.2
  nonneg := fun it => mul_nonneg (w.nonneg it.1) ((Q it.1).nonneg it.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (Q _).sum_one, mul_one]
    exact w.sum_one

/-- Entropy of a conditioned mixture `(m, x) ↦ w(m) * (Q m).pmf x` equals
    `H(w) + ∑ m, w(m) * H(Q m)`. -/
private lemma gp_shannonEntropy_condMixture {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (Q : ι → ProbDist α) :
    shannonEntropy (gpCondMix w Q) = shannonEntropy w + ∑ i : ι, w.pmf i * shannonEntropy (Q i) := by
  unfold shannonEntropy gpCondMix
  rw [Fintype.sum_prod_type]
  have hterm : ∀ i : ι, ∑ a : α, negPLogP (w.pmf i * (Q i).pmf a) =
      negPLogP (w.pmf i) + w.pmf i * ∑ a : α, negPLogP ((Q i).pmf a) := fun i => by
    simp_rw [negPLogP_mul (w.nonneg i) ((Q i).nonneg _), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, (Q i).sum_one, one_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]

private lemma gpCondMix_map_ac {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ))
    (J : ProbDist (α × β × (ι × γ)))
    (hJ : ∀ t, J.pmf t = w.pmf t.2.2.1 * (R t.2.2.1).pmf (t.1, t.2.1, t.2.2.2)) :
    (J.map (fun t => (t.1, t.2.2))).map
      (⟨fun t => (t.2.1, (t.1, t.2.2)), fun t => (t.2.1, (t.1, t.2.2)),
        fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩ : (α × (ι × γ)) ≃ (ι × (α × γ))) =
      gpCondMix w (fun i => (R i).map (fun t => (t.1, t.2.2))) := by
  classical
  rw [map_comp_eq]
  apply gp_probDist_ext; rintro ⟨i, a, c⟩
  unfold ProbDist.map gpCondMix; dsimp only [Function.comp_apply]
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
  · conv_lhs => rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · rw [Finset.mul_sum, Finset.sum_eq_single c, Finset.sum_eq_single c]
      · simp [hJ]
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro i' _ hne; exact Finset.sum_eq_zero fun c' _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne; rw [Finset.sum_eq_zero fun _ _ => by simp [hne], mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma gpCondMix_map_bc {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ))
    (J : ProbDist (α × β × (ι × γ)))
    (hJ : ∀ t, J.pmf t = w.pmf t.2.2.1 * (R t.2.2.1).pmf (t.1, t.2.1, t.2.2.2)) :
    (J.map (fun t => (t.2.1, t.2.2))).map
      (⟨fun t => (t.2.1, (t.1, t.2.2)), fun t => (t.2.1, (t.1, t.2.2)),
        fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩ : (β × (ι × γ)) ≃ (ι × (β × γ))) =
      gpCondMix w (fun i => (R i).map (fun t => (t.2.1, t.2.2))) := by
  classical
  rw [map_comp_eq]
  apply gp_probDist_ext; rintro ⟨i, b, c⟩
  unfold ProbDist.map gpCondMix; dsimp only [Function.comp_apply]
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single b]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · rw [Finset.mul_sum, Finset.sum_eq_single c, Finset.sum_eq_single c]
      · simp [hJ]
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro i' _ hne; exact Finset.sum_eq_zero fun c' _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b' _ hne; rw [Finset.sum_eq_zero fun _ _ => by simp [hne], mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma gpCondMix_map_c {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ))
    (J : ProbDist (α × β × (ι × γ)))
    (hJ : ∀ t, J.pmf t = w.pmf t.2.2.1 * (R t.2.2.1).pmf (t.1, t.2.1, t.2.2.2)) :
    J.map (fun t => t.2.2) = gpCondMix w (fun i => (R i).map (fun t => t.2.2)) := by
  classical
  apply gp_probDist_ext; rintro ⟨i, c⟩
  unfold ProbDist.map gpCondMix; dsimp only
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · rw [Finset.mul_sum, Finset.sum_eq_single c, Finset.sum_eq_single c]
    · simp [hJ]
    · intro c' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro c' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i' _ hne; exact Finset.sum_eq_zero fun c' _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Triple conditioned mixture `(a, b, (i, c)) ↦ w(i) * (R i)(a, b, c)` on `α × β × (ι × γ)`. -/
private def gpCondMixTriple {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ)) : ProbDist (α × β × (ι × γ)) where
  pmf := fun t => w.pmf t.2.2.1 * (R t.2.2.1).pmf (t.1, t.2.1, t.2.2.2)
  nonneg := fun t => mul_nonneg (w.nonneg _) ((R _).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    calc ∑ a : α, ∑ b : β, ∑ i : ι, ∑ c : γ, w.pmf i * (R i).pmf (a, b, c)
      _ = ∑ i : ι, w.pmf i * ∑ a : α, ∑ b : β, ∑ c : γ, (R i).pmf (a, b, c) := by
          trans (∑ a : α, ∑ i : ι, ∑ b : β, ∑ c : γ, w.pmf i * (R i).pmf (a, b, c))
          · exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp_rw [← Finset.mul_sum]
      _ = ∑ i : ι, w.pmf i * 1 := by
          refine Finset.sum_congr rfl fun i _ => by
            congr 1; simpa [Fintype.sum_prod_type] using (R i).sum_one
      _ = 1 := by simp [w.sum_one]

private lemma gpCondMix_ent_all {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ)) :
    shannonEntropy (gpCondMixTriple w R) =
      shannonEntropy w + ∑ i : ι, w.pmf i * shannonEntropy (R i) := by
  classical
  let eAll : (α × β × (ι × γ)) ≃ (ι × (α × β × γ)) :=
    { toFun := fun t => (t.2.2.1, (t.1, t.2.1, t.2.2.2))
      invFun := fun t => (t.2.1, t.2.2.1, (t.1, t.2.2.2))
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  have hmap : (gpCondMixTriple w R).map eAll = gpCondMix w R := by
    apply gp_probDist_ext; rintro ⟨i, a, b, c⟩
    unfold ProbDist.map; dsimp only
    rw [Finset.sum_eq_single (a, b, (i, c))]
    · simp [eAll, gpCondMixTriple, gpCondMix]
    · intro t _ hne
      have : eAll t ≠ (i, (a, b, c)) := fun h => hne (eAll.symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← shannonEntropy_map_equiv eAll (gpCondMixTriple w R), hmap]
  exact gp_shannonEntropy_condMixture w R

private lemma gpCondMix_ent_ac {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ)) :
    shannonEntropy ((gpCondMixTriple w R).map (fun t => (t.1, t.2.2))) =
      shannonEntropy w + ∑ i : ι, w.pmf i * shannonEntropy ((R i).map (fun t => (t.1, t.2.2))) := by
  let eAC : (α × (ι × γ)) ≃ (ι × (α × γ)) :=
    ⟨fun t => (t.2.1, (t.1, t.2.2)), fun t => (t.2.1, (t.1, t.2.2)),
     fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
  rw [← shannonEntropy_map_equiv eAC, gpCondMix_map_ac w R (gpCondMixTriple w R) (fun _ => rfl),
      gp_shannonEntropy_condMixture]

private lemma gpCondMix_ent_bc {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ)) :
    shannonEntropy ((gpCondMixTriple w R).map (fun t => (t.2.1, t.2.2))) =
      shannonEntropy w + ∑ i : ι, w.pmf i * shannonEntropy ((R i).map (fun t => (t.2.1, t.2.2))) := by
  let eBC : (β × (ι × γ)) ≃ (ι × (β × γ)) :=
    ⟨fun t => (t.2.1, (t.1, t.2.2)), fun t => (t.2.1, (t.1, t.2.2)),
     fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
  rw [← shannonEntropy_map_equiv eBC, gpCondMix_map_bc w R (gpCondMixTriple w R) (fun _ => rfl),
      gp_shannonEntropy_condMixture]

private lemma gpCondMix_ent_c {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ)) :
    shannonEntropy ((gpCondMixTriple w R).map (fun t => t.2.2)) =
      shannonEntropy w + ∑ i : ι, w.pmf i * shannonEntropy ((R i).map (fun t => t.2.2)) := by
  rw [gpCondMix_map_c w R (gpCondMixTriple w R) (fun _ => rfl), gp_shannonEntropy_condMixture]

/-- Conditional mutual information of a mixture conditioned on the mixture index `ι`:
    if `J = gpCondMixTriple w R`, then `I(A; B | I, C) = ∑ i, w(i) * I_{R i}(A; B | C)`. -/
private lemma gp_condMutualInfo_condMixture {ι : Type*} [Fintype ι]
    (w : ProbDist ι) (R : ι → ProbDist (α × β × γ)) :
    condMutualInfo (gpCondMixTriple w R) = ∑ i : ι, w.pmf i * condMutualInfo (R i) := by
  unfold condMutualInfo
  dsimp only
  rw [gpCondMix_ent_ac w R, gpCondMix_ent_bc w R, gpCondMix_ent_all w R, gpCondMix_ent_c w R]
  have hlin : (∑ i : ι, w.pmf i * shannonEntropy ((R i).map (fun t => (t.1, t.2.2)))) +
      (∑ i : ι, w.pmf i * shannonEntropy ((R i).map (fun t => (t.2.1, t.2.2)))) -
      (∑ i : ι, w.pmf i * shannonEntropy (R i)) -
      (∑ i : ι, w.pmf i * shannonEntropy ((R i).map (fun t => t.2.2))) =
      ∑ i : ι, w.pmf i * (shannonEntropy ((R i).map (fun t => (t.1, t.2.2))) +
        shannonEntropy ((R i).map (fun t => (t.2.1, t.2.2))) -
        shannonEntropy (R i) - shannonEntropy ((R i).map (fun t => t.2.2))) := by
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

end GPHelpers

/-! ### 1. State-Dependent Channel Model & Single-Letter Gelfand–Pinsker Capacity -/

section SingleLetterGP

variable {X S Y U : Type*} [Fintype X] [Fintype S] [Fintype Y] [Fintype U]

/-- A discrete memoryless state-dependent channel `W(y | x, s)` with input `X`,
    state `S`, and output `Y`. -/
abbrev StateChannel (X S Y : Type*) [Fintype X] [Fintype S] [Fintype Y] :=
  DMC (X × S) Y

/-- Single-letter joint distribution on `S × U × Y` induced by a joint `(S, U)` distribution `Psu`,
    deterministic encoding map `f : U × S → X`, and state-dependent channel `W(y | x, s)`. -/
def gpDetJoint (W : StateChannel X S Y) (Psu : ProbDist (S × U)) (f : U × S → X) :
    ProbDist (S × U × Y) where
  pmf := fun t => Psu.pmf (t.1, t.2.1) * W.trans (f (t.2.1, t.1), t.1) t.2.2
  nonneg := fun t => mul_nonneg (Psu.nonneg _) (W.nonneg _ _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, W.sum_one, mul_one]
    simpa [Fintype.sum_prod_type] using Psu.sum_one

/-- Single-letter joint distribution on `S × U × X × Y` induced by a stochastic encoding law
    `Psux : ProbDist (S × U × X)` passed through `W(y | x, s)` (satisfying `U — (X, S) — Y`). -/
def gpStochJoint (W : StateChannel X S Y) (Psux : ProbDist (S × U × X)) :
    ProbDist (S × U × X × Y) where
  pmf := fun t => Psux.pmf (t.1, t.2.1, t.2.2.1) * W.trans (t.2.2.1, t.1) t.2.2.2
  nonneg := fun t => mul_nonneg (Psux.nonneg _) (W.nonneg _ _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, W.sum_one, mul_one]
    simpa [Fintype.sum_prod_type] using Psux.sum_one

/-- **Single-Letter Gelfand–Pinsker Capacity** (Gelfand & Pinsker 1980; El Gamal & Kim Thm. 7.3):
    `C_GP(Ps, W) = sup_{P(u | s), x = f(u, s)} [I(U; Y) - I(U; S)]`. -/
noncomputable def gelfandPinskerCapacity (Ps : ProbDist S) (W : StateChannel X S Y) : ℝ :=
  sSup { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
    Psu.fst = Ps ∧
    r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu }

/-- Equivalent stochastic-encoder formulation of the Gelfand–Pinsker capacity:
    `sup_{P(u, x | s)} [I(U; Y) - I(U; S)]` where `U — (X, S) — Y`. -/
noncomputable def gelfandPinskerCapacityStoch (Ps : ProbDist S) (W : StateChannel X S Y) : ℝ :=
  sSup { r : ℝ | ∃ (kU : ℕ) (Psux : ProbDist (S × Fin kU × X)),
    Psux.map Prod.fst = Ps ∧
    r = mutualInfo ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2))) -
        mutualInfo (Psux.map (fun t => (t.1, t.2.1))) }

private lemma gp_mutualInfo_le_log2_card_right {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (P : ProbDist (α × β)) :
    mutualInfo P ≤ log2 (Fintype.card β : ℝ) := by
  have hce : 0 ≤ condEntropy (P.map Prod.swap) := condEntropy_nonneg _
  unfold condEntropy at hce
  rw [shannonEntropy_swap, snd_map_swap] at hce
  have hH : shannonEntropy P.snd ≤ log2 (Fintype.card β : ℝ) := shannonEntropy_le_log2_card _
  unfold mutualInfo; linarith

private lemma gpDet_set_bddAbove (Ps : ProbDist S) (W : StateChannel X S Y) :
    BddAbove { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
      Psu.fst = Ps ∧
      r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu } := by
  by_cases hY : Nonempty Y
  · refine ⟨log2 (Fintype.card Y : ℝ), ?_⟩
    rintro r ⟨kU, Psu, f, _, rfl⟩
    have h1 := gp_mutualInfo_le_log2_card_right ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2)))
    have h2 : 0 ≤ mutualInfo Psu := mutualInfo_nonneg Psu
    linarith
  · refine ⟨0, ?_⟩
    rintro r ⟨kU, Psu, f, _, _⟩
    exact (hY ⟨(gp_nonempty_of_probDist (gpDetJoint W Psu f)).some.2.2⟩).elim

private lemma gpStoch_set_bddAbove (Ps : ProbDist S) (W : StateChannel X S Y) :
    BddAbove { r : ℝ | ∃ (kU : ℕ) (Psux : ProbDist (S × Fin kU × X)),
      Psux.map Prod.fst = Ps ∧
      r = mutualInfo ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2))) -
          mutualInfo (Psux.map (fun t => (t.1, t.2.1))) } := by
  by_cases hY : Nonempty Y
  · refine ⟨log2 (Fintype.card Y : ℝ), ?_⟩
    rintro r ⟨kU, Psux, _, rfl⟩
    have h1 := gp_mutualInfo_le_log2_card_right ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2)))
    have h2 : 0 ≤ mutualInfo (Psux.map (fun t => (t.1, t.2.1))) := mutualInfo_nonneg _
    linarith
  · refine ⟨0, ?_⟩
    rintro r ⟨kU, Psux, _, _⟩
    exact (hY ⟨(gp_nonempty_of_probDist (gpStochJoint W Psux)).some.2.2.2⟩).elim

/-- Any finite deterministic auxiliary witness `(U, Psu, f)` with `Psu.fst = Ps` lower-bounds
    `gelfandPinskerCapacity Ps W`. -/
theorem gelfandPinskerCapacity_ge_det (Ps : ProbDist S) (W : StateChannel X S Y)
    (Psu : ProbDist (S × U)) (f : U × S → X) (hfst : Psu.fst = Ps) :
    mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu ≤
      gelfandPinskerCapacity Ps W := by
  classical
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let Psu' : ProbDist (S × Fin (Fintype.card U)) := Psu.map (fun su => (su.1, e su.2))
  let f' : Fin (Fintype.card U) × S → X := fun us => f (e.symm us.1, us.2)
  have hfst' : Psu'.fst = Ps := by
    rw [← gp_probDist_map_fst, ← hfst, ← gp_probDist_map_fst]
    unfold Psu'; rw [map_comp_eq]; rfl
  have hPsu'_pmf : ∀ s u', Psu'.pmf (s, u') = Psu.pmf (s, e.symm u') := by
    intro s u'
    unfold Psu' ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · rw [Finset.sum_eq_single (e.symm u')]
      · simp
      · intro u _ hne
        have : e u ≠ u' := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hmi_su : mutualInfo Psu' = mutualInfo Psu := gp_mutualInfo_map_equiv_right Psu e
  have huy_eq : (gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2)) =
      ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))).map (fun uy => (e uy.1, uy.2)) := by
    apply gp_probDist_ext; rintro ⟨u', y⟩
    rw [map_comp_eq]
    unfold ProbDist.map gpDetJoint; dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single u', Finset.sum_eq_single (e.symm u')]
    · rw [Finset.sum_eq_single y, Finset.sum_eq_single y]
      · simp [hPsu'_pmf, f']
      · intro y' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro y' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro u _ hne
      have : e u ≠ u' := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
      exact Finset.sum_eq_zero fun _ _ => by simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro u'' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hmi_uy : mutualInfo ((gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2))) =
      mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) := by
    rw [huy_eq, gp_mutualInfo_map_equiv_left]
  unfold gelfandPinskerCapacity
  refine le_csSup (gpDet_set_bddAbove Ps W) ⟨Fintype.card U, Psu', f', hfst', ?_⟩
  rw [hmi_uy, hmi_su]

/-- **Functional Representation Lemma for Gelfand–Pinsker**:
    every stochastic witness `Psux : ProbDist (S × U × X)` is dominated by a deterministic
    witness on `U' = U × (S → X)` where `g : S → X` is drawn from the product conditional law
    `∏_{s'} P(X = g(s') | U, s')` independently of `S` given `U`. -/
theorem gelfandPinskerCapacity_ge_stoch (Ps : ProbDist S) (W : StateChannel X S Y)
    (Psux : ProbDist (S × U × X)) (hfst : Psux.map Prod.fst = Ps) :
    mutualInfo ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2))) -
      mutualInfo (Psux.map (fun t => (t.1, t.2.1))) ≤
      gelfandPinskerCapacity Ps W := by
  classical
  have hX : Nonempty X := ⟨(gp_nonempty_of_probDist Psux).some.2.2⟩
  let Psu : ProbDist (S × U) := Psux.map (fun t => (t.1, t.2.1))
  have hPsu_pmf : ∀ s u, Psu.pmf (s, u) = ∑ x : X, Psux.pmf (s, u, x) := by
    intro s u
    unfold Psu ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
      · simp
      · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Conditional law `K(u, s)(x) = P(X = x | S = s, U = u)` (uniform on zero-mass `(s, u)`).
  let K : U → S → ProbDist X := fun u s =>
    { pmf := fun x =>
        if Psu.pmf (s, u) = 0 then (ProbDist.uniform (α := X)).pmf x
        else Psux.pmf (s, u, x) / Psu.pmf (s, u)
      nonneg := fun x => by
        split_ifs
        · exact (ProbDist.uniform (α := X)).nonneg x
        · exact div_nonneg (Psux.nonneg _) (Psu.nonneg _)
      sum_one := by
        by_cases h0 : Psu.pmf (s, u) = 0
        · simp only [h0, ↓reduceIte]; exact (ProbDist.uniform (α := X)).sum_one
        · simp only [ite_eq_right_iff.mpr (fun h => absurd h h0), ← Finset.sum_div, ← hPsu_pmf]
          exact div_self h0 }
  have hK_mul : ∀ s u x, Psu.pmf (s, u) * (K u s).pmf x = Psux.pmf (s, u, x) := by
    intro s u x
    dsimp only [K]
    by_cases h0 : Psu.pmf (s, u) = 0
    · simp only [h0, ↓reduceIte, zero_mul]
      have hle : Psux.pmf (s, u, x) ≤ Psu.pmf (s, u) := by
        rw [hPsu_pmf]
        exact Finset.single_le_sum (fun x' _ => Psux.nonneg (s, u, x')) (Finset.mem_univ x)
      exact (le_antisymm (by linarith) (Psux.nonneg _)).symm
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h h0)]
      exact mul_div_cancel₀ _ h0
  -- Product distribution `Qg u` on `S → X` conditioned on `u`: `Qg(u)(g) = ∏_{s'} K(u, s')(g s')`.
  let Qg : U → ProbDist (S → X) := fun u =>
    { pmf := fun g => ∏ s' : S, (K u s').pmf (g s')
      nonneg := fun g => Finset.prod_nonneg fun s' _ => (K u s').nonneg _
      sum_one := by
        rw [← Fintype.prod_sum]
        exact Finset.prod_eq_one fun s' _ => (K u s').sum_one }
  have hQg_marg : ∀ u s x,
      (∑ g : S → X, if g s = x then (Qg u).pmf g else 0) = (K u s).pmf x := by
    intro u s x
    let F : S → X → ℝ := fun s' a =>
      if s' = s then (if a = x then (K u s').pmf a else 0) else (K u s').pmf a
    have hfun : ∀ g : S → X,
        (if g s = x then (Qg u).pmf g else 0) = ∏ s' : S, F s' (g s') := by
      intro g
      dsimp only [Qg]
      conv_rhs => rw [← Finset.mul_prod_erase Finset.univ (fun s' => F s' (g s')) (Finset.mem_univ s)]
      have hrest : ∏ s' ∈ Finset.univ.erase s, F s' (g s') =
          ∏ s' ∈ Finset.univ.erase s, (K u s').pmf (g s') :=
        Finset.prod_congr rfl fun s' hs' => by simp [F, (Finset.mem_erase.mp hs').1]
      rw [hrest]
      by_cases hgx : g s = x
      · simp only [hgx, ↓reduceIte, F]
        rw [← Finset.mul_prod_erase Finset.univ (fun s' => (K u s').pmf (g s')) (Finset.mem_univ s), hgx]
      · simp [F, hgx]
    simp_rw [hfun, ← Fintype.prod_sum F]
    rw [← Finset.mul_prod_erase Finset.univ (fun s' => ∑ a : X, F s' a) (Finset.mem_univ s)]
    have hs : ∑ a : X, F s a = (K u s).pmf x := by simp [F]
    have hrest : ∏ s' ∈ Finset.univ.erase s, (∑ a : X, F s' a) = 1 :=
      Finset.prod_eq_one fun s' hs' => by
        simp only [F, ite_eq_right_iff.mpr (fun h => absurd h (Finset.mem_erase.mp hs').1)]
        exact (K u s').sum_one
    rw [hs, hrest, mul_one]
  -- Deterministic witness on `U' = U × (S → X)` with `f' ((u, g), s) = g s`.
  let U' := U × (S → X)
  let Psu' : ProbDist (S × U') :=
    { pmf := fun p => Psu.pmf (p.1, p.2.1) * (Qg p.2.1).pmf p.2.2
      nonneg := fun p => mul_nonneg (Psu.nonneg _) ((Qg _).nonneg _)
      sum_one := by
        dsimp only [U']
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, (Qg _).sum_one, mul_one]
        simpa [Fintype.sum_prod_type] using Psu.sum_one }
  let f' : U' × S → X := fun p => p.1.2 p.2
  have hfst' : Psu'.fst = Ps := by
    apply gp_probDist_ext; intro s
    rw [← hfst]
    unfold ProbDist.fst Psu'; dsimp only
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (Qg _).sum_one, mul_one]
    change Psu.fst.pmf s = (Psux.map Prod.fst).pmf s
    rw [← gp_probDist_map_fst]; unfold Psu; rw [map_comp_eq]; rfl
  -- Step 1: `I(U'; S) = I(U; S)` since `g ⊥ S | U`.
  have hI_su' : mutualInfo Psu' = mutualInfo Psu := by
    let T : ProbDist (U × (S → X) × S) := Psu'.map (fun p => (p.2.1, p.2.2, p.1))
    have hT_pair : T.map (fun t => ((t.1, t.2.1), t.2.2)) = Psu'.map Prod.swap := by
      unfold T; rw [map_comp_eq]; rfl
    have hT_us : T.map (fun t => (t.1, t.2.2)) = Psu.map Prod.swap := by
      unfold T; rw [map_comp_eq]
      apply gp_probDist_ext; rintro ⟨u, s⟩
      unfold ProbDist.map Psu'; dsimp only [Function.comp_apply]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
        · simp only [↓reduceIte, ← Finset.mul_sum, (Qg u).sum_one, mul_one]
          rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
          · rw [Finset.sum_eq_single u]
            · simp
            · intro u' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hchain := gp_mutualInfo_pair_eq_add_condMutualInfo T
    rw [hT_pair, mutualInfo_swap, hT_us, mutualInfo_swap] at hchain
    -- Show `I(g; S | U) = 0` via `condMutualInfo_eq_zero_iff`.
    let R : ProbDist ((S → X) × S × U) := T.map (fun t => (t.2.1, t.2.2, t.1))
    have hR_pmf : ∀ g s u, R.pmf (g, s, u) = Psu.pmf (s, u) * (Qg u).pmf g := by
      intro g s u
      unfold R T; rw [map_comp_eq]
      unfold ProbDist.map Psu'; dsimp only [Function.comp_apply]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
        · rw [Finset.sum_eq_single g]
          · simp
          · intro g' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_gu : ∀ g u, (R.map (fun t => (t.1, t.2.2))).pmf (g, u) = Psu.snd.pmf u * (Qg u).pmf g := by
      intro g u
      unfold ProbDist.map ProbDist.snd; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
      · rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_eq_single u]
        · simp [hR_pmf]
        · intro u' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro g' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_su : ∀ s u, (R.map (fun t => (t.2.1, t.2.2))).pmf (s, u) = Psu.pmf (s, u) := by
      intro s u
      unfold ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type]
      trans (∑ g : S → X, Psu.pmf (s, u) * (Qg u).pmf g)
      · refine Finset.sum_congr rfl fun g _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
        · rw [Finset.sum_eq_single u]
          · simp [hR_pmf]
          · intro u' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [← Finset.mul_sum, (Qg u).sum_one, mul_one]
    have hR_u : ∀ u, (R.map (fun t => t.2.2)).pmf u = Psu.snd.pmf u := by
      intro u
      have h1 : R.map (fun t => t.2.2) = (R.map (fun t => (t.2.1, t.2.2))).snd := by
        rw [← gp_probDist_map_snd (R.map (fun t => (t.2.1, t.2.2))), map_comp_eq R]; rfl
      rw [h1]
      unfold ProbDist.snd; dsimp only
      exact Finset.sum_congr rfl fun s _ => hR_su s u
    have hcmi_zero : condMutualInfo R = 0 := by
      rw [condMutualInfo_eq_zero_iff]
      apply gp_probDist_ext; rintro ⟨g, s, u⟩
      change R.pmf (g, s, u) = if (R.map (fun t => t.2.2)).pmf u = 0 then 0
        else (R.map (fun t => (t.1, t.2.2))).pmf (g, u) *
          (R.map (fun t => (t.2.1, t.2.2))).pmf (s, u) / (R.map (fun t => t.2.2)).pmf u
      rw [hR_pmf, hR_gu, hR_su, hR_u]
      by_cases hu : Psu.snd.pmf u = 0
      · simp only [hu, ↓reduceIte]
        have hle : Psu.pmf (s, u) ≤ Psu.snd.pmf u :=
          Finset.single_le_sum (fun s' _ => Psu.nonneg (s', u)) (Finset.mem_univ s)
        have h0 : Psu.pmf (s, u) = 0 := le_antisymm (by linarith) (Psu.nonneg _)
        rw [h0, zero_mul]
      · simp only [ite_eq_right_iff.mpr (fun h => absurd h hu)]
        field_simp [hu]
    linarith
  -- Step 2: `I(U; Y) ≤ I(U'; Y)` by data processing (`U` is a function of `U' = (U, g)`),
  -- since the `(U, Y)` marginal of `gpDetJoint W Psu' f'` equals that of `gpStochJoint W Psux`.
  have hUY_eq : ((gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2))).map (Prod.map Prod.fst id) =
      (gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2)) := by
    rw [map_comp_eq]
    apply gp_probDist_ext; rintro ⟨u, y⟩
    unfold ProbDist.map gpDetJoint gpStochJoint Psu'; dsimp only [Function.comp_apply, Prod.map, f']
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single u]
      · -- LHS: `∑ g, ∑ y', if y' = y then Psu(s, u) * Qg(u)(g) * W(g s, s)(y') else 0`
        -- RHS: `∑ x, ∑ y', if y' = y then Psux(s, u, x) * W(x, s)(y') else 0`
        trans (∑ g : S → X, Psu.pmf (s, u) * (Qg u).pmf g * W.trans (g s, s) y)
        · refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_eq_single y]
          · simp
          · intro y' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · symm
          rw [Fintype.sum_prod_type]
          trans (∑ x : X, Psux.pmf (s, u, x) * W.trans (x, s) y)
          · refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_eq_single y]
            · simp
            · intro y' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · symm
            have hpart : ∀ g : S → X,
                Psu.pmf (s, u) * (Qg u).pmf g * W.trans (g s, s) y =
                  ∑ x : X, if g s = x then Psu.pmf (s, u) * (Qg u).pmf g * W.trans (x, s) y else (0 : ℝ) :=
              fun g => by
                rw [Finset.sum_eq_single (g s)]
                · simp
                · intro x _ hne; simp [hne.symm]
                · intro h; exact absurd (Finset.mem_univ _) h
            simp_rw [hpart]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            have hpull : (∑ g : S → X, if g s = x then Psu.pmf (s, u) * (Qg u).pmf g * W.trans (x, s) y else 0) =
                Psu.pmf (s, u) * (∑ g : S → X, if g s = x then (Qg u).pmf g else 0) * W.trans (x, s) y := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun g _ => by split_ifs <;> ring
            rw [hpull, hQg_marg, hK_mul]
      · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hI_uy_le : mutualInfo ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2))) ≤
      mutualInfo ((gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2))) := by
    rw [← hUY_eq]
    have hswap : (((gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2))).map (Prod.map Prod.fst id)) =
        ((((gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2))).map Prod.swap).map
          (Prod.map id Prod.fst)).map Prod.swap := by
      rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq]
      congr 1
    rw [hswap, mutualInfo_swap]
    have hdpi := mutualInfo_map_right_le (((gpDetJoint W Psu' f').map (fun t => (t.2.1, t.2.2))).map Prod.swap)
      Prod.fst
    rwa [mutualInfo_swap] at hdpi
  have hdet := gelfandPinskerCapacity_ge_det Ps W Psu' f' hfst'
  linarith

/-- **Equivalence of Deterministic and Stochastic Single-Letter Formulations**
    (El Gamal & Kim §7.4): `gelfandPinskerCapacity Ps W = gelfandPinskerCapacityStoch Ps W`. -/
theorem gelfandPinskerCapacity_eq_stochastic (Ps : ProbDist S) (W : StateChannel X S Y) :
    gelfandPinskerCapacity Ps W = gelfandPinskerCapacityStoch Ps W := by
  classical
  by_cases hX : Nonempty X
  · have hne_det : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
        Psu.fst = Ps ∧
        r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu }.Nonempty := by
      refine ⟨_, 1, Ps.prod ProbDist.uniform, fun _ => hX.some, ?_, rfl⟩
      apply gp_probDist_ext; intro s
      unfold ProbDist.fst ProbDist.prod; dsimp only
      rw [← Finset.mul_sum, (ProbDist.uniform (α := Fin 1)).sum_one, mul_one]
    have hne_st : { r : ℝ | ∃ (kU : ℕ) (Psux : ProbDist (S × Fin kU × X)),
        Psux.map Prod.fst = Ps ∧
        r = mutualInfo ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2))) -
            mutualInfo (Psux.map (fun t => (t.1, t.2.1))) }.Nonempty := by
      let Psux0 : ProbDist (S × Fin 1 × X) := Ps.map (fun s => (s, (⟨0, Nat.zero_lt_one⟩, hX.some)))
      refine ⟨_, 1, Psux0, ?_, rfl⟩
      unfold Psux0; rw [map_comp_eq]; exact gp_probDist_map_id Ps
    apply le_antisymm
    · refine csSup_le hne_det ?_
      rintro r ⟨kU, Psu, f, hfst, rfl⟩
      let Psux : ProbDist (S × Fin kU × X) := Psu.map (fun su => (su.1, su.2, f (su.2, su.1)))
      have hPsux_fst : Psux.map Prod.fst = Ps := by
        unfold Psux; rw [map_comp_eq, ← hfst, ← gp_probDist_map_fst]; rfl
      have hPsux_su : Psux.map (fun t => (t.1, t.2.1)) = Psu := by
        unfold Psux; rw [map_comp_eq]; exact gp_probDist_map_id Psu
      have hPsux_uy : (gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2)) =
          (gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2)) := by
        apply gp_probDist_ext; rintro ⟨u, y⟩
        unfold ProbDist.map gpStochJoint gpDetJoint Psux; dsimp only
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single u, Finset.sum_eq_single u]
        · rw [Fintype.sum_prod_type]
          trans (∑ x : X, (if f (u, s) = x then Psu.pmf (s, u) else 0) * W.trans (x, s) y)
          · refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_eq_single y]
            · simp only [↓reduceIte]; congr 1
              unfold ProbDist.map; dsimp only
              rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
              · rw [Finset.sum_eq_single u]
                · simp
                · intro u' _ hne; simp [hne]
                · intro h; exact absurd (Finset.mem_univ _) h
              · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro y' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [Finset.sum_eq_single (f (u, s))]
            · symm
              rw [Finset.sum_eq_single y]
              · simp
              · intro y' _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro x _ hne; simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      refine le_csSup (gpStoch_set_bddAbove Ps W) ⟨kU, Psux, hPsux_fst, ?_⟩
      rw [hPsux_uy, hPsux_su]
    · refine csSup_le hne_st ?_
      rintro r ⟨kU, Psux, hfst, rfl⟩
      exact gelfandPinskerCapacity_ge_stoch Ps W Psux hfst
  · have he1 : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
        Psu.fst = Ps ∧
        r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kU, Psu, f, _, _⟩
      have hne := gp_nonempty_of_probDist Psu
      exact hX ⟨f (hne.some.2, hne.some.1)⟩
    have he2 : { r : ℝ | ∃ (kU : ℕ) (Psux : ProbDist (S × Fin kU × X)),
        Psux.map Prod.fst = Ps ∧
        r = mutualInfo ((gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2))) -
            mutualInfo (Psux.map (fun t => (t.1, t.2.1))) } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kU, Psux, _, _⟩
      exact hX ⟨(gp_nonempty_of_probDist Psux).some.2.2⟩
    rw [gelfandPinskerCapacity, gelfandPinskerCapacityStoch, he1, he2]

/-- Non-negativity of Gelfand–Pinsker capacity: `0 ≤ gelfandPinskerCapacity Ps W`. -/
theorem gelfandPinskerCapacity_nonneg (Ps : ProbDist S) (W : StateChannel X S Y) :
    0 ≤ gelfandPinskerCapacity Ps W := by
  by_cases hX : Nonempty X
  · let Psu : ProbDist (S × Fin 1) := Ps.prod ProbDist.uniform
    have hfst : Psu.fst = Ps := by
      apply gp_probDist_ext; intro s
      unfold Psu ProbDist.fst ProbDist.prod; dsimp only
      rw [← Finset.mul_sum, (ProbDist.uniform (α := Fin 1)).sum_one, mul_one]
    have hge := gelfandPinskerCapacity_ge_det Ps W Psu (fun _ => hX.some) hfst
    have h1 : mutualInfo ((gpDetJoint W Psu (fun _ => hX.some)).map (fun t => (t.2.1, t.2.2))) = 0 :=
      gp_mutualInfo_eq_zero_of_unique_left _
    have h2 : mutualInfo Psu = 0 := gp_mutualInfo_prod_eq_zero Ps ProbDist.uniform
    linarith
  · have he : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
        Psu.fst = Ps ∧
        r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kU, Psu, f, _, _⟩
      have hne := gp_nonempty_of_probDist Psu
      exact hX ⟨f (hne.some.2, hne.some.1)⟩
    rw [gelfandPinskerCapacity, he, Real.sSup_empty]

/-- Output-alphabet upper bound: `gelfandPinskerCapacity Ps W ≤ log₂ |Y|`. -/
theorem gelfandPinskerCapacity_le_log2_card_output [Nonempty Y]
    (Ps : ProbDist S) (W : StateChannel X S Y) :
    gelfandPinskerCapacity Ps W ≤ log2 (Fintype.card Y : ℝ) := by
  unfold gelfandPinskerCapacity
  refine Real.sSup_le ?_ ?_
  · rintro r ⟨kU, Psu, f, _, rfl⟩
    have h1 := gp_mutualInfo_le_log2_card_right ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2)))
    have h2 : 0 ≤ mutualInfo Psu := mutualInfo_nonneg Psu
    linarith
  · have h1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos (α := Y)
    unfold log2
    exact div_nonneg (Real.log_nonneg h1) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

/-- **State-Independent Reduction**: when `W(y | x, s) = W₀(y | x)` does not depend on the state `s`,
    the Gelfand–Pinsker capacity reduces identically to the standard DMC capacity `W₀.capacity`. -/
theorem gelfandPinskerCapacity_ignore_state (Ps : ProbDist S) (W : StateChannel X S Y)
    (W₀ : DMC X Y) (hW : ∀ x s y, W.trans (x, s) y = W₀.trans x y) :
    gelfandPinskerCapacity Ps W = W₀.capacity := by
  classical
  by_cases hX : Nonempty X
  · have hne_gp : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
        Psu.fst = Ps ∧
        r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu }.Nonempty := by
      refine ⟨_, 1, Ps.prod ProbDist.uniform, fun _ => hX.some, ?_, rfl⟩
      apply gp_probDist_ext; intro s
      unfold ProbDist.fst ProbDist.prod; dsimp only
      rw [← Finset.mul_sum, (ProbDist.uniform (α := Fin 1)).sum_one, mul_one]
    have hne_c : { r : ℝ | ∃ Px : ProbDist X, r = W₀.mutualInfo Px }.Nonempty :=
      ⟨_, ProbDist.uniform, rfl⟩
    apply le_antisymm
    · -- `C_GP(Ps, W) ≤ C(W₀)`: for any `(Psu, f)`, `U — X — Y` holds because `W` ignores `S`,
      -- so `I(U; Y) - I(U; S) ≤ I(U; Y) ≤ I(X; Y) ≤ W₀.capacity`.
      refine csSup_le hne_gp ?_
      rintro r ⟨kU, Psu, f, _, rfl⟩
      let Pux : ProbDist (Fin kU × X) := Psu.map (fun su => (su.2, f (su.2, su.1)))
      let Q : ProbDist (Fin kU × X × Y) :=
        { pmf := fun t => Pux.pmf (t.1, t.2.1) * W₀.trans t.2.1 t.2.2
          nonneg := fun t => mul_nonneg (Pux.nonneg _) (W₀.nonneg _ _)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, W₀.sum_one, mul_one]
            simpa [Fintype.sum_prod_type] using Pux.sum_one }
      -- Identify `(U, Y)` marginal of `Q` with `(U, Y)` marginal of `gpDetJoint W Psu f`.
      have hQ_uy : Q.map (fun t => (t.1, t.2.2)) =
          (gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2)) := by
        apply gp_probDist_ext; rintro ⟨u, y⟩
        unfold ProbDist.map Q Pux gpDetJoint; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
        · rw [Fintype.sum_prod_type]
          trans (∑ x : X, (∑ s : S, if f (u, s) = x then Psu.pmf (s, u) else 0) * W₀.trans x y)
          · refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_eq_single y]
            · simp only [↓reduceIte]; congr 1
              unfold ProbDist.map; dsimp only
              rw [Fintype.sum_prod_type]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.sum_eq_single u]
              · simp
              · intro u' _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro y' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
            · rw [Finset.sum_eq_single y, Finset.sum_eq_single (f (u, s))]
              · simp [hW]
              · intro x _ hne; simp [hne.symm]
              · intro h; exact absurd (Finset.mem_univ _) h
              · intro y' _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ _) h
            · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      -- Identify `(X, Y)` marginal of `Q` with `W₀.joint Pux.snd`.
      have hQ_xy : Q.map (fun t => (t.2.1, t.2.2)) = W₀.joint Pux.snd := by
        apply gp_probDist_ext; rintro ⟨x, y⟩
        unfold ProbDist.map Q DMC.joint ProbDist.snd; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
        · rw [Finset.sum_eq_single y]
          · simp
          · intro y' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro x' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      -- Markov chain `U — X — Y`: `I(U; Y | X) = 0`.
      let R : ProbDist (Fin kU × Y × X) := Q.map (fun t => (t.1, t.2.2, t.2.1))
      have hR_pmf : ∀ u y x, R.pmf (u, y, x) = Pux.pmf (u, x) * W₀.trans x y := by
        intro u y x
        unfold R ProbDist.map Q; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
        · rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · simp
            · intro y' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro x' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hR_ux : ∀ u x, (R.map (fun t => (t.1, t.2.2))).pmf (u, x) = Pux.pmf (u, x) := by
        intro u x
        unfold ProbDist.map; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
        · rw [Fintype.sum_prod_type]
          trans (∑ y : Y, Pux.pmf (u, x) * W₀.trans x y)
          · refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_eq_single x]
            · simp [hR_pmf]
            · intro x' _ hne; simp [hne]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [← Finset.mul_sum, W₀.sum_one, mul_one]
        · intro u' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hR_yx : ∀ y x, (R.map (fun t => (t.2.1, t.2.2))).pmf (y, x) = Pux.snd.pmf x * W₀.trans x y := by
        intro y x
        unfold ProbDist.map ProbDist.snd; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
        · rw [Finset.sum_eq_single x]
          · simp [hR_pmf]
          · intro x' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro y' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hR_x : ∀ x, (R.map (fun t => t.2.2)).pmf x = Pux.snd.pmf x := by
        intro x
        have h1 : R.map (fun t => t.2.2) = (R.map (fun t => (t.1, t.2.2))).snd := by
          rw [← gp_probDist_map_snd (R.map (fun t => (t.1, t.2.2))), map_comp_eq R]; rfl
        rw [h1]; unfold ProbDist.snd; dsimp only
        exact Finset.sum_congr rfl fun u _ => hR_ux u x
      have hmarkov : condMutualInfo R = 0 := by
        rw [condMutualInfo_eq_zero_iff]
        apply gp_probDist_ext; rintro ⟨u, y, x⟩
        change R.pmf (u, y, x) = if (R.map (fun t => t.2.2)).pmf x = 0 then 0
          else (R.map (fun t => (t.1, t.2.2))).pmf (u, x) *
            (R.map (fun t => (t.2.1, t.2.2))).pmf (y, x) / (R.map (fun t => t.2.2)).pmf x
        rw [hR_pmf, hR_ux, hR_yx, hR_x]
        by_cases hx : Pux.snd.pmf x = 0
        · simp only [hx, ↓reduceIte]
          have hle : Pux.pmf (u, x) ≤ Pux.snd.pmf x :=
            Finset.single_le_sum (fun u' _ => Pux.nonneg (u', x)) (Finset.mem_univ u)
          have h0 : Pux.pmf (u, x) = 0 := le_antisymm (by linarith) (Pux.nonneg _)
          rw [h0, zero_mul]
        · simp only [ite_eq_right_iff.mpr (fun h => absurd h hx)]
          field_simp [hx]
      -- Chain rule both ways: `I(U, X; Y) = I(U; Y) + I(X; Y | U) = I(X; Y) + I(U; Y | X) = I(X; Y)`.
      have hch1 := gp_mutualInfo_pair_eq_add_condMutualInfo Q
      have hch2 := gp_mutualInfo_pair_eq_add_condMutualInfo (Q.map (fun t => (t.2.1, t.1, t.2.2)))
      simp only [map_comp_eq, Function.comp_def] at hch2
      have hpair_eq : mutualInfo (Q.map (fun t => ((t.2.1, t.1), t.2.2))) =
          mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2))) := by
        have hcomp : Q.map (fun t => ((t.2.1, t.1), t.2.2)) =
            (Q.map (fun t => ((t.1, t.2.1), t.2.2))).map
              (fun p => ((Equiv.prodComm (Fin kU) X) p.1, p.2)) := by
          rw [map_comp_eq]; rfl
        rw [hcomp, gp_mutualInfo_map_equiv_left]
      rw [hpair_eq] at hch2
      have hcmi1 : 0 ≤ condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) := condMutualInfo_nonneg _
      have hIUY_le_IXY : mutualInfo (Q.map (fun t => (t.1, t.2.2))) ≤
          mutualInfo (Q.map (fun t => (t.2.1, t.2.2))) := by
        change condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) = 0 at hmarkov
        linarith
      rw [hQ_uy, hQ_xy] at hIUY_le_IXY
      have hcap : mutualInfo (W₀.joint Pux.snd) ≤ W₀.capacity :=
        dmc_mutualInfo_le_capacity W₀ Pux.snd
      have hsu0 : 0 ≤ mutualInfo Psu := mutualInfo_nonneg Psu
      linarith
    · -- `C(W₀) ≤ C_GP(Ps, W)`: take `U = X`, `Psu = Ps × Px`, `f (u, s) = u`.
      refine csSup_le hne_c ?_
      rintro r ⟨Px, rfl⟩
      let Psu : ProbDist (S × X) := Ps.prod Px
      have hfst : Psu.fst = Ps := by
        apply gp_probDist_ext; intro s
        unfold Psu ProbDist.fst ProbDist.prod; dsimp only
        rw [← Finset.mul_sum, Px.sum_one, mul_one]
      have hmi_su : mutualInfo Psu = 0 := gp_mutualInfo_prod_eq_zero Ps Px
      have huy : (gpDetJoint W Psu Prod.fst).map (fun t => (t.2.1, t.2.2)) = W₀.joint Px := by
        apply gp_probDist_ext; rintro ⟨x, y⟩
        unfold ProbDist.map gpDetJoint Psu ProbDist.prod DMC.joint; dsimp only
        rw [Fintype.sum_prod_type]
        have h1 : ∀ s : S, (∑ xy : X × Y, if xy = (x, y) then
            Ps.pmf s * Px.pmf xy.1 * W.trans (xy.1, s) xy.2 else 0) =
            Ps.pmf s * (Px.pmf x * W₀.trans x y) := fun s => by
          rw [Finset.sum_eq_single (x, y)]
          · simp [hW]; ring
          · intro xy _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [h1, ← Finset.sum_mul, Ps.sum_one, one_mul]
      have hge := gelfandPinskerCapacity_ge_det Ps W Psu Prod.fst hfst
      rw [huy, hmi_su, sub_zero] at hge
      exact hge
  · have he1 : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
        Psu.fst = Ps ∧
        r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kU, Psu, f, _, _⟩
      have hne := gp_nonempty_of_probDist Psu
      exact hX ⟨f (hne.some.2, hne.some.1)⟩
    have he2 : { r : ℝ | ∃ Px : ProbDist X, r = W₀.mutualInfo Px } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨Px, _⟩; exact hX (gp_nonempty_of_probDist Px)
    rw [gelfandPinskerCapacity, DMC.capacity, he1, he2]

end SingleLetterGP

/-! ### 2. Operational Model & Gelfand–Pinsker Converse
(Gelfand & Pinsker 1980; El Gamal & Kim §7.4.1) -/

section GelfandPinskerConverse

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- An `(n, M)` noncausal state-dependent channel code (Gelfand–Pinsker code):
    encoder `enc : Fin M → (Fin n → S) → (Fin n → X)` observes the entire state sequence `S^n`
    noncausally, and decoder `dec : (Fin n → Y) → Fin M` estimates the message from `Y^n`. -/
structure GelfandPinskerCode (X S Y : Type*) (n M : ℕ) where
  enc : Fin M → (Fin n → S) → (Fin n → X)
  dec : (Fin n → Y) → Fin M

/-- Joint distribution of `(M, S^n, Y^n)` induced by a Gelfand–Pinsker code with uniform message
    `M ~ Unif(Fin M)`, i.i.d. state `S^n ~ Ps^n`, and memoryless channel `W^n`. -/
noncomputable def gpCodeJoint (Ps : ProbDist S) (W : StateChannel X S Y) {n M : ℕ}
    (hM : 0 < M) (code : GelfandPinskerCode X S Y n M) :
    ProbDist (Fin M × (Fin n → S) × (Fin n → Y)) :=
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  { pmf := fun t =>
      (ProbDist.uniform (α := Fin M)).pmf t.1 *
      (iidDist Ps n).pmf t.2.1 *
      (W.power n).trans (fun i => (code.enc t.1 t.2.1 i, t.2.1 i)) t.2.2
    nonneg := fun t => mul_nonneg (mul_nonneg (ProbDist.uniform.nonneg _) ((iidDist Ps n).nonneg _))
      ((W.power n).nonneg _ _)
    sum_one := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, (W.power n).sum_one, mul_one,
        ← Finset.mul_sum, (iidDist Ps n).sum_one, mul_one]
      exact (ProbDist.uniform (α := Fin M)).sum_one }

/-- Average decoding error probability of a Gelfand–Pinsker code over uniform message `M`
    and i.i.d. state `S^n ~ Ps^n`. -/
noncomputable def gpAvgError (Ps : ProbDist S) (W : StateChannel X S Y) {n M : ℕ}
    (code : GelfandPinskerCode X S Y n M) : ℝ := by
  classical
  exact if M = 0 then 0 else
    ((1 : ℝ) / (M : ℝ)) *
      ∑ m : Fin M, ∑ s : Fin n → S, (iidDist Ps n).pmf s *
        ∑ y : Fin n → Y,
          if code.dec y ≠ m then
            (W.power n).trans (fun i => (code.enc m s i, s i)) y
          else 0

/-- Operational achievability of rate `R ≥ 0` over `(Ps, W)` with noncausal encoder state. -/
def IsGPAchievable (Ps : ProbDist S) (W : StateChannel X S Y) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ code : GelfandPinskerCode X S Y n M, gpAvgError Ps W code ≤ ε

/-- Operational capacity of `(Ps, W)` with noncausal transmitter state information. -/
noncomputable def gpOperationalCapacity (Ps : ProbDist S) (W : StateChannel X S Y) : ℝ :=
  sSup { R : ℝ | IsGPAchievable Ps W R }

/-- Forward chain rule for mutual information:
    `I(A; B^n) = ∑_{i=0}^{n-1} I(A; B_i | B^{<i})`. -/
private lemma gp_mi_chain_forward {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (P : ProbDist (A × (Fin n → B))) :
    mutualInfo P =
      ∑ i : Fin n, condMutualInfo (P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))) := by
  let pref : ∀ (k : ℕ), k ≤ n → (Fin n → B) → (Fin k → B) :=
    fun _ hk b j => b ⟨j.1, lt_of_lt_of_le j.2 hk⟩
  let hB : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun ab => pref k hk ab.2)) else 0
  let hAB : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun ab => (ab.1, pref k hk ab.2))) else 0
  have hterm : ∀ i : Fin n,
      condMutualInfo (P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))) =
        (hB (i.1 + 1) - hB i.1) - (hAB (i.1 + 1) - hAB i.1) := by
    intro i
    have hi : i.1 ≤ n := le_of_lt i.2
    have hi1 : i.1 + 1 ≤ n := i.2
    let ePref : (B × (Fin i.1 → B)) ≃ (Fin (i.1 + 1) → B) :=
      { toFun := fun bf j => if h : j.1 < i.1 then bf.2 ⟨j.1, h⟩ else bf.1
        invFun := fun g => (g ⟨i.1, Nat.lt_succ_self _⟩, fun j => g ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
        left_inv := fun ⟨b, f⟩ => by
          ext
          · simp
          · rename_i j; simp [j.2]
        right_inv := fun g => by
          funext j; dsimp only; split_ifs with h
          · rfl
          · congr 1; apply Fin.ext; dsimp only; omega }
    let eAB : (A × B × (Fin i.1 → B)) ≃ (A × (Fin (i.1 + 1) → B)) :=
      { toFun := fun t => (t.1, ePref (t.2.1, t.2.2))
        invFun := fun p => (p.1, (ePref.symm p.2).1, (ePref.symm p.2).2)
        left_inv := fun ⟨a, b, f⟩ => by simp
        right_inv := fun ⟨a, g⟩ => by simp }
    have h1 : shannonEntropy ((P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))).map
        (fun t => (t.1, t.2.2))) = hAB i.1 := by
      simp only [hAB, hi, ↓reduceDIte]; rw [map_comp_eq]; rfl
    have h2 : shannonEntropy ((P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))).map
        (fun t => (t.2.1, t.2.2))) = hB (i.1 + 1) := by
      simp only [hB, hi1, ↓reduceDIte]; rw [map_comp_eq]
      refine gp_shannonEntropy_map_eq_of_equiv P _ _ ePref fun ab => ?_
      funext j; dsimp [ePref, prefixVec, pref]; split_ifs with h
      · rfl
      · exact congrArg ab.2 (Fin.ext (by dsimp only; omega))
    have h3 : shannonEntropy (P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))) = hAB (i.1 + 1) := by
      simp only [hAB, hi1, ↓reduceDIte]
      refine gp_shannonEntropy_map_eq_of_equiv P _ _ eAB fun ab => ?_
      apply Prod.ext
      · rfl
      · funext j; dsimp [eAB, ePref, prefixVec, pref]; split_ifs with h
        · rfl
        · exact congrArg ab.2 (Fin.ext (by dsimp only; omega))
    have h4 : shannonEntropy ((P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))).map
        (fun t => t.2.2)) = hB i.1 := by
      simp only [hB, hi, ↓reduceDIte]; rw [map_comp_eq]; rfl
    unfold condMutualInfo; dsimp only
    rw [h1, h2, h3, h4]; ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, gp_sum_fin_telescope, gp_sum_fin_telescope]
  have hB0 : hB 0 = 0 := by
    simp only [hB, Nat.zero_le, ↓reduceDIte]; exact gp_shannonEntropy_eq_zero_of_unique _
  have hBn : hB n = shannonEntropy P.snd := by
    simp only [hB, le_refl, ↓reduceDIte]; rw [← gp_probDist_map_snd]
  have hAB0 : hAB 0 = shannonEntropy P.fst := by
    simp only [hAB, Nat.zero_le, ↓reduceDIte]; rw [← gp_probDist_map_fst]
    let e0 : (A × (Fin 0 → B)) ≃ A :=
      { toFun := Prod.fst
        invFun := fun a => (a, fun j => Fin.elim0 j)
        left_inv := fun ⟨_, _⟩ => Prod.ext rfl (funext fun j => Fin.elim0 j)
        right_inv := fun _ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e0 (fun _ => rfl)
  have hABn : hAB n = shannonEntropy P := by
    simp only [hAB, le_refl, ↓reduceDIte]
    have hmap : P.map (fun ab => (ab.1, pref n (le_refl n) ab.2)) = P := by
      have : (fun ab : A × (Fin n → B) => (ab.1, pref n (le_refl n) ab.2)) = id :=
        funext fun ⟨_, _⟩ => Prod.ext rfl (funext fun _ => rfl)
      rw [this]; exact gp_probDist_map_id P
    rw [hmap]
  rw [hB0, hBn, hAB0, hABn]
  unfold mutualInfo; ring

/-- Backward chain rule for mutual information:
    `I(A; C^n) = ∑_{i=0}^{n-1} I(A; C_i | C_{>i})`. -/
private lemma gp_mi_chain_backward {A C : Type*} [Fintype A] [Fintype C] {n : ℕ}
    (P : ProbDist (A × (Fin n → C))) :
    mutualInfo P =
      ∑ i : Fin n, condMutualInfo (P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))) := by
  let suff : ∀ (k : ℕ), k ≤ n → (Fin n → C) → (Fin (n - k) → C) :=
    fun k _ c j => c ⟨k + j.1, by omega⟩
  let hC : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun ac => suff k hk ac.2)) else 0
  let hAC : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun ac => (ac.1, suff k hk ac.2))) else 0
  have hterm : ∀ i : Fin n,
      condMutualInfo (P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))) =
        (hAC (i.1 + 1) - hAC i.1) - (hC (i.1 + 1) - hC i.1) := by
    intro i
    have hi : i.1 ≤ n := le_of_lt i.2
    have hi1 : i.1 + 1 ≤ n := i.2
    let eSuff : (C × (Fin (n - 1 - i.1) → C)) ≃ (Fin (n - i.1) → C) :=
      { toFun := fun cg j => if h : j.1 = 0 then cg.1 else cg.2 ⟨j.1 - 1, by omega⟩
        invFun := fun g => (g ⟨0, by omega⟩, fun j => g ⟨j.1 + 1, by omega⟩)
        left_inv := fun ⟨c, g⟩ => by
          ext
          · simp
          · rename_i j; simp
        right_inv := fun g => by
          funext j; dsimp only; split_ifs with h
          · congr 1; exact Fin.ext h.symm
          · congr 1; apply Fin.ext; dsimp only; omega }
    let eLen : (Fin (n - 1 - i.1) → C) ≃ (Fin (n - (i.1 + 1)) → C) :=
      { toFun := fun g j => g ⟨j.1, by omega⟩
        invFun := fun g j => g ⟨j.1, by omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let eAC1 : (A × (Fin (n - 1 - i.1) → C)) ≃ (A × (Fin (n - (i.1 + 1)) → C)) :=
      Equiv.prodCongr (Equiv.refl A) eLen
    let eAC0 : (A × C × (Fin (n - 1 - i.1) → C)) ≃ (A × (Fin (n - i.1) → C)) :=
      { toFun := fun t => (t.1, eSuff (t.2.1, t.2.2))
        invFun := fun p => (p.1, (eSuff.symm p.2).1, (eSuff.symm p.2).2)
        left_inv := fun ⟨a, c, g⟩ => by simp
        right_inv := fun ⟨a, g⟩ => by simp }
    have h1 : shannonEntropy ((P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))).map
        (fun t => (t.1, t.2.2))) = hAC (i.1 + 1) := by
      simp only [hAC, hi1, ↓reduceDIte]; rw [map_comp_eq]
      exact gp_shannonEntropy_map_eq_of_equiv P _ _ eAC1 (fun _ => rfl)
    have h2 : shannonEntropy ((P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))).map
        (fun t => (t.2.1, t.2.2))) = hC i.1 := by
      simp only [hC, hi, ↓reduceDIte]; rw [map_comp_eq]
      refine gp_shannonEntropy_map_eq_of_equiv P _ _ eSuff fun ac => ?_
      funext j; dsimp [eSuff, suffixVec, suff]; split_ifs with h
      · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
      · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
    have h3 : shannonEntropy (P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))) = hAC i.1 := by
      simp only [hAC, hi, ↓reduceDIte]
      refine gp_shannonEntropy_map_eq_of_equiv P _ _ eAC0 fun ac => ?_
      apply Prod.ext
      · rfl
      · funext j; dsimp [eAC0, eSuff, suffixVec, suff]; split_ifs with h
        · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
        · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
    have h4 : shannonEntropy ((P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))).map
        (fun t => t.2.2)) = hC (i.1 + 1) := by
      simp only [hC, hi1, ↓reduceDIte]; rw [map_comp_eq]
      exact gp_shannonEntropy_map_eq_of_equiv P _ _ eLen (fun _ => rfl)
    unfold condMutualInfo; dsimp only
    rw [h1, h2, h3, h4]; ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, gp_sum_fin_telescope, gp_sum_fin_telescope]
  have hCn : hC n = 0 := by
    simp only [hC, le_refl, ↓reduceDIte]
    have : Unique (Fin (n - n) → C) :=
      ⟨⟨fun j => absurd j.2 (by omega)⟩, fun f => funext fun j => absurd j.2 (by omega)⟩
    exact gp_shannonEntropy_eq_zero_of_unique _
  have hC0 : hC 0 = shannonEntropy P.snd := by
    simp only [hC, Nat.zero_le, ↓reduceDIte]; rw [← gp_probDist_map_snd]
    let e0 : (Fin (n - 0) → C) ≃ (Fin n → C) :=
      { toFun := fun f j => f ⟨j.1, by omega⟩
        invFun := fun f j => f ⟨j.1, by omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine gp_shannonEntropy_map_eq_of_equiv P _ _ e0 fun ac => ?_
    funext j; dsimp [e0, suff]; exact congrArg ac.2 (Fin.ext (by simp))
  have hACn : hAC n = shannonEntropy P.fst := by
    simp only [hAC, le_refl, ↓reduceDIte]; rw [← gp_probDist_map_fst]
    let en : (A × (Fin (n - n) → C)) ≃ A :=
      { toFun := Prod.fst
        invFun := fun a => (a, fun j => absurd j.2 (by omega))
        left_inv := fun ⟨_, _⟩ => Prod.ext rfl (funext fun j => absurd j.2 (by omega))
        right_inv := fun _ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ en (fun _ => rfl)
  have hAC0 : hAC 0 = shannonEntropy P := by
    simp only [hAC, Nat.zero_le, ↓reduceDIte]
    let e0 : (A × (Fin (n - 0) → C)) ≃ (A × (Fin n → C)) :=
      { toFun := fun p => (p.1, fun j => p.2 ⟨j.1, by omega⟩)
        invFun := fun p => (p.1, fun j => p.2 ⟨j.1, by omega⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hmap : P.map (fun ac => (ac.1, suff 0 (Nat.zero_le n) ac.2)) = P.map e0.symm := by
      congr 1; funext ac; apply Prod.ext
      · rfl
      · funext j; dsimp [e0, suff]; exact congrArg ac.2 (Fin.ext (by simp))
    rw [hmap, shannonEntropy_map_equiv e0.symm]
  rw [hCn, hC0, hACn, hAC0]
  unfold mutualInfo; ring

/-- Coordinate-wise entropy identity for Gelfand–Pinsker converse:
    `I(M; Y_i | Y^{<i}) = I((M, Y^{<i}, S_{>i}); Y_i) - I(Y_i; S_{>i} | M, Y^{<i}) - I(Y^{<i}; Y_i)`. -/
private lemma gp_coord_Y_identity {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : ProbDist (A × B × C × D)) :
    condMutualInfo (P.map (fun t => (t.1, t.2.1, t.2.2.1))) =
      mutualInfo (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))) -
      condMutualInfo (P.map (fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) -
      mutualInfo (P.map (fun t => (t.2.2.1, t.2.1))) := by
  unfold condMutualInfo mutualInfo
  dsimp only
  simp only [map_comp_eq, Function.comp_def]
  have h1 : shannonEntropy (P.map (fun t => (t.1, t.2.2.1))) =
      shannonEntropy (P.map (fun t => (t.1, t.2.2.1))) := rfl
  have h2 : shannonEntropy (P.map (fun t => (t.2.1, t.2.2.1))) =
      shannonEntropy (P.map (fun t => (t.2.2.1, t.2.1))) :=
    gp_shannonEntropy_map_eq_of_equiv P _ _ (Equiv.prodComm B C) (fun _ => rfl)
  have h3 : shannonEntropy (P.map (fun t => (t.1, t.2.1, t.2.2.1))) =
      shannonEntropy (P.map (fun t => (t.2.1, (t.1, t.2.2.1)))) := by
    let e : (A × B × C) ≃ (B × (A × C)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, t.1, t.2.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h4 : (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))).fst =
      P.map (fun t => (t.1, t.2.2.1, t.2.2.2)) := by
    rw [← gp_probDist_map_fst, map_comp_eq]; rfl
  have h5 : (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))).snd =
      (P.map (fun t => (t.2.2.1, t.2.1))).snd := by
    rw [← gp_probDist_map_snd, ← gp_probDist_map_snd, map_comp_eq, map_comp_eq]; rfl
  have h6 : (P.map (fun t => (t.2.2.1, t.2.1))).fst = P.map (fun t => t.2.2.1) := by
    rw [← gp_probDist_map_fst, map_comp_eq]; rfl
  have h7 : shannonEntropy (P.map (fun t => (t.1, t.2.2.1, t.2.2.2))) =
      shannonEntropy (P.map (fun t => (t.2.2.2, (t.1, t.2.2.1)))) := by
    let e : (A × C × D) ≃ (D × (A × C)) :=
      { toFun := fun t => (t.2.2, (t.1, t.2.1))
        invFun := fun t => (t.2.1, t.2.2, t.1)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h8 : shannonEntropy (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))) =
      shannonEntropy (P.map (fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) := by
    let e : ((A × C × D) × B) ≃ (B × D × (A × C)) :=
      { toFun := fun t => (t.2, t.1.2.2, (t.1.1, t.1.2.1))
        invFun := fun t => ((t.2.2.1, t.2.2.2, t.2.1), t.1)
        left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, ⟨_, _⟩⟩ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  rw [h2, h3, h4, h5, h6, h7, h8]
  ring

/-- Coordinate-wise entropy identity for the state term in Gelfand–Pinsker converse:
    `I(M; S_i | S_{>i}) = I((M, Y^{<i}, S_{>i}); S_i) - I(Y^{<i}; S_i | M, S_{>i}) - I(S_i; S_{>i})`. -/
private lemma gp_coord_S_identity {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : ProbDist (A × B × C × D)) :
    condMutualInfo (P.map (fun t => (t.1, t.2.1, t.2.2.2))) =
      mutualInfo (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))) -
      condMutualInfo (P.map (fun t => (t.2.2.1, t.2.1, (t.1, t.2.2.2)))) -
      mutualInfo (P.map (fun t => (t.2.1, t.2.2.2))) := by
  unfold condMutualInfo mutualInfo
  dsimp only
  simp only [map_comp_eq, Function.comp_def]
  have h1 : shannonEntropy (P.map (fun t => (t.1, t.2.1, t.2.2.2))) =
      shannonEntropy (P.map (fun t => (t.2.1, (t.1, t.2.2.2)))) := by
    let e : (A × B × D) ≃ (B × (A × D)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, t.1, t.2.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h2 : (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))).fst =
      P.map (fun t => (t.1, t.2.2.1, t.2.2.2)) := by
    rw [← gp_probDist_map_fst, map_comp_eq]; rfl
  have h3 : (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))).snd =
      (P.map (fun t => (t.2.1, t.2.2.2))).fst := by
    rw [← gp_probDist_map_snd, ← gp_probDist_map_fst, map_comp_eq, map_comp_eq]; rfl
  have h4 : (P.map (fun t => (t.2.1, t.2.2.2))).snd = P.map (fun t => t.2.2.2) := by
    rw [← gp_probDist_map_snd, map_comp_eq]; rfl
  have h5 : shannonEntropy (P.map (fun t => (t.1, t.2.2.1, t.2.2.2))) =
      shannonEntropy (P.map (fun t => (t.2.2.1, (t.1, t.2.2.2)))) := by
    let e : (A × C × D) ≃ (C × (A × D)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, t.1, t.2.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h6 : shannonEntropy (P.map (fun t => ((t.1, t.2.2.1, t.2.2.2), t.2.1))) =
      shannonEntropy (P.map (fun t => (t.2.2.1, t.2.1, (t.1, t.2.2.2)))) := by
    let e : ((A × C × D) × B) ≃ (C × B × (A × D)) :=
      { toFun := fun t => (t.1.2.1, t.2, (t.1.1, t.1.2.2))
        invFun := fun t => ((t.2.2.1, t.1, t.2.2.2), t.2.1)
        left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, ⟨_, _⟩⟩ => rfl }
    exact gp_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- **Core Gelfand–Pinsker Converse Single-Letterization Inequality** (El Gamal & Kim §7.4.1):
    for any `(n, M)` Gelfand–Pinsker code (`M > 0`),
    `I(M; Y^n) ≤ n · gelfandPinskerCapacity Ps W`.

    Proved via `csiszar_sum_identity` conditioned on `M`, i.i.d. state independence `S_i ⊥ S_{>i}`,
    memoryless Markov factorization for `U_i = (M, Y^{<i}, S_{>i})`, and
    `gelfandPinskerCapacity_ge_stoch`. -/
theorem gpCode_mutualInfo_le (Ps : ProbDist S) (W : StateChannel X S Y) {n M : ℕ}
    (hM : 0 < M) (code : GelfandPinskerCode X S Y n M) :
    mutualInfo ((gpCodeJoint Ps W hM code).map (fun t => (t.1, t.2.2))) ≤
      (n : ℝ) * gelfandPinskerCapacity Ps W := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let P := gpCodeJoint Ps W hM code
  let UnifM : ProbDist (Fin M) := ProbDist.uniform
  -- 1. `M` and `S^n` are independent, so `I(M; S^n) = 0`.
  have hP_MS : P.map (fun t => (t.1, t.2.1)) = UnifM.prod (iidDist Ps n) := by
    apply gp_probDist_ext; rintro ⟨m, s⟩
    unfold P gpCodeJoint ProbDist.map ProbDist.prod; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
      · dsimp only
        simp only [↓reduceIte, ← Finset.mul_sum, (W.power n).sum_one, mul_one]
        rfl
      · intro s' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro m' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hI_MS : mutualInfo (P.map (fun t => (t.1, t.2.1))) = 0 := by
    rw [hP_MS]; exact gp_mutualInfo_prod_eq_zero UnifM (iidDist Ps n)
  -- 2. Marginal of `S^n` is `iidDist Ps n`.
  have hP_S : P.map (fun t => t.2.1) = iidDist Ps n := by
    have h1 : P.map (fun t => t.2.1) = (P.map (fun t => (t.1, t.2.1))).snd := by
      rw [← gp_probDist_map_snd, map_comp_eq]; rfl
    rw [h1, hP_MS]
    apply gp_probDist_ext; intro s
    unfold ProbDist.snd ProbDist.prod; dsimp only
    rw [← Finset.sum_mul, UnifM.sum_one, one_mul]
  -- 3. `S_i` and `S_{>i}` are independent, so `I(S_i; S_{>i}) = 0`.
  have hI_Si_suff : ∀ i : Fin n,
      mutualInfo (P.map (fun t => (t.2.1 i, suffixVec i t.2.1))) = 0 := by
    intro i
    have hmap : P.map (fun t => (t.2.1 i, suffixVec i t.2.1)) =
        Ps.prod (iidDist Ps (n - 1 - i.1)) := by
      have hcomp : P.map (fun t => (t.2.1 i, suffixVec i t.2.1)) =
          (iidDist Ps n).map (fun s => (s i, suffixVec i s)) := by
        rw [← hP_S, map_comp_eq]; rfl
      rw [hcomp]
      apply gp_probDist_ext; rintro ⟨si, ss⟩
      unfold ProbDist.map ProbDist.prod iidDist; dsimp only
      let F : Fin n → S → ℝ := fun j a =>
        if j = i then (if a = si then Ps.pmf a else 0)
        else if h : i.1 + 1 ≤ j.1 then
          (if a = ss ⟨j.1 - (i.1 + 1), by omega⟩ then Ps.pmf a else 0)
        else Ps.pmf a
      have hfun : ∀ s : Fin n → S,
          (if (s i, suffixVec i s) = (si, ss) then ∏ j : Fin n, Ps.pmf (s j) else 0) =
            ∏ j : Fin n, F j (s j) := by
        intro s
        by_cases h : (s i, suffixVec i s) = (si, ss)
        · have hsi : s i = si := congrArg Prod.fst h
          have hss : suffixVec i s = ss := congrArg Prod.snd h
          simp only [h, ↓reduceIte]
          refine Finset.prod_congr rfl fun j _ => ?_
          dsimp only [F]
          by_cases hji : j = i
          · subst hji; simp [hsi]
          · by_cases hge : i.1 + 1 ≤ j.1
            · simp only [hji, ↓reduceIte, hge, ↓reduceDIte]
              have hval : s j = ss ⟨j.1 - (i.1 + 1), by omega⟩ := by
                have h1 := congrFun hss ⟨j.1 - (i.1 + 1), by omega⟩
                dsimp only [suffixVec] at h1
                rw [← h1]; congr 1; apply Fin.ext; dsimp only; omega
              simp [hval]
            · simp [hji, hge]
        · simp only [h, ↓reduceIte]
          symm
          by_cases hsi : s i = si
          · have hne : suffixVec i s ≠ ss := fun hs => h (Prod.ext hsi hs)
            have hex : ∃ k : Fin (n - 1 - i.1), suffixVec i s k ≠ ss k := by
              by_contra hall; push Not at hall; exact hne (funext hall)
            obtain ⟨k, hk⟩ := hex
            let j : Fin n := ⟨i.1 + 1 + k.1, by omega⟩
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            have hji : j ≠ i := fun heq => by
              have := congrArg Fin.val heq; dsimp [j] at this; omega
            have hge : i.1 + 1 ≤ j.1 := by dsimp [j]; omega
            dsimp only [F]
            simp only [hji, ↓reduceIte, hge, ↓reduceDIte]
            have hidx : (⟨j.1 - (i.1 + 1), by omega⟩ : Fin (n - 1 - i.1)) = k :=
              Fin.ext (by dsimp [j]; omega)
            rw [hidx]
            have hne' : s j ≠ ss k := hk
            simp [hne']
          · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
            simp [F, hsi]
      trans (∑ s : Fin n → S, ∏ j : Fin n, F j (s j))
      · refine Finset.sum_congr rfl fun s _ => by
          convert hfun s
      · rw [← Fintype.prod_sum F]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ a : S, F j a) (Finset.mem_univ i)]
        have hi_term : ∑ a : S, F i a = Ps.pmf si := by simp [F]
        rw [hi_term]
        congr 1
        -- Split `Finset.univ.erase i` into `j > i` and `j < i`.
        have hsplit : (Finset.univ.erase i : Finset (Fin n)) =
            (Finset.univ.filter fun j : Fin n => i.1 + 1 ≤ j.1) ∪
            (Finset.univ.filter fun j : Fin n => j.1 < i.1) := by
          ext j; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
            Finset.mem_filter, true_and]
          constructor
          · intro hne
            have hne_v : j.1 ≠ i.1 := fun h => hne (Fin.ext h)
            omega
          · rintro (h | h) heq <;> subst heq <;> omega
        have hdisj : Disjoint (Finset.univ.filter fun j : Fin n => i.1 + 1 ≤ j.1)
            (Finset.univ.filter fun j : Fin n => j.1 < i.1) := by
          rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
        rw [hsplit, Finset.prod_union hdisj]
        have hlt_one : ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.1 < i.1), ∑ a : S, F j a = 1 :=
          Finset.prod_eq_one fun j hj => by
            have hjlt : j.1 < i.1 := (Finset.mem_filter.mp hj).2
            have hji : j ≠ i := fun h => by subst h; omega
            have hnge : ¬ (i.1 + 1 ≤ j.1) := by omega
            simp only [F, hji, ↓reduceIte, hnge, ↓reduceDIte]
            exact Ps.sum_one
        rw [hlt_one, mul_one]
        refine Finset.prod_bij (fun j hj => (⟨j.1 - (i.1 + 1), by
          have := (Finset.mem_filter.mp hj).2; omega⟩ : Fin (n - 1 - i.1))) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro j₁ hj₁ j₂ hj₂ heq
          have h1 := (Finset.mem_filter.mp hj₁).2
          have h2 := (Finset.mem_filter.mp hj₂).2
          have hv := congrArg Fin.val heq; dsimp only at hv
          exact Fin.ext (by omega)
        · intro k _
          refine ⟨⟨i.1 + 1 + k.1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, ?_⟩
          exact Fin.ext (by dsimp only; omega)
        · intro j hj
          have hjge : i.1 + 1 ≤ j.1 := (Finset.mem_filter.mp hj).2
          have hji : j ≠ i := fun h => by subst h; omega
          simp only [F, hji, ↓reduceIte, hjge, ↓reduceDIte]
          rw [Finset.sum_eq_single (ss ⟨j.1 - (i.1 + 1), by omega⟩)]
          · simp
          · intro a _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
    rw [hmap]
    exact gp_mutualInfo_prod_eq_zero Ps (iidDist Ps (n - 1 - i.1))
  -- 4. Conditional Csiszár sum identity given `M`:
  --    `∑ i, I(Y_i; S_{>i} | M, Y^{<i}) = ∑ i, I(Y^{<i}; S_i | M, S_{>i})`.
  have hcsiszar_M :
      ∑ i : Fin n, condMutualInfo (P.map (fun t => (t.2.2 i, suffixVec i t.2.1, (t.1, prefixVec i t.2.2)))) =
      ∑ i : Fin n, condMutualInfo (P.map (fun t => (prefixVec i t.2.2, t.2.1 i, (t.1, suffixVec i t.2.1)))) := by
    let Qm : Fin M → ProbDist ((Fin n → Y) × (Fin n → S)) := fun m =>
      { pmf := fun ys => (iidDist Ps n).pmf ys.2 *
          (W.power n).trans (fun i => (code.enc m ys.2 i, ys.2 i)) ys.1
        nonneg := fun ys => mul_nonneg ((iidDist Ps n).nonneg _) ((W.power n).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type_right]
          simp_rw [← Finset.mul_sum, (W.power n).sum_one, mul_one]
          exact (iidDist Ps n).sum_one }
    have hL : ∀ i : Fin n,
        condMutualInfo (P.map (fun t => (t.2.2 i, suffixVec i t.2.1, (t.1, prefixVec i t.2.2)))) =
          ∑ m : Fin M, UnifM.pmf m *
            condMutualInfo ((Qm m).map (fun ys => (ys.1 i, suffixVec i ys.2, prefixVec i ys.1))) := by
      intro i
      let Rm : Fin M → ProbDist (Y × (Fin (n - 1 - i.1) → S) × (Fin i.1 → Y)) :=
        fun m => (Qm m).map (fun ys => (ys.1 i, suffixVec i ys.2, prefixVec i ys.1))
      have heq := gp_condMutualInfo_condMixture UnifM Rm
      rw [← heq]
      congr 1
      apply gp_probDist_ext; rintro ⟨yi, ss, m, yp⟩
      unfold gpCondMixTriple; dsimp only [P, Rm, Qm]; unfold gpCodeJoint ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
      · conv_lhs => rw [Fintype.sum_prod_type]
        conv_rhs => rw [Fintype.sum_prod_type_right, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by
          dsimp only
          by_cases h1 : y i = yi ∧ suffixVec i s = ss ∧ prefixVec i y = yp
          · simp only [h1.1, h1.2.1, h1.2.2, ↓reduceIte]; dsimp only [UnifM]; ring
          · have ha : ¬ ((y i, suffixVec i s, (m, prefixVec i y)) = (yi, ss, (m, yp))) := by
              intro h; apply h1
              exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2.2) h⟩
            have hb : ¬ ((y i, suffixVec i s, prefixVec i y) = (yi, ss, yp)) := by
              intro h; apply h1
              exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩
            simp [ha, hb]
      · intro m' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : ∀ i : Fin n,
        condMutualInfo (P.map (fun t => (prefixVec i t.2.2, t.2.1 i, (t.1, suffixVec i t.2.1)))) =
          ∑ m : Fin M, UnifM.pmf m *
            condMutualInfo ((Qm m).map (fun ys => (prefixVec i ys.1, ys.2 i, suffixVec i ys.2))) := by
      intro i
      let Rm : Fin M → ProbDist ((Fin i.1 → Y) × S × (Fin (n - 1 - i.1) → S)) :=
        fun m => (Qm m).map (fun ys => (prefixVec i ys.1, ys.2 i, suffixVec i ys.2))
      have heq := gp_condMutualInfo_condMixture UnifM Rm
      rw [← heq]
      congr 1
      apply gp_probDist_ext; rintro ⟨yp, si, m, ss⟩
      unfold gpCondMixTriple; dsimp only [P, Rm, Qm]; unfold gpCodeJoint ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
      · conv_lhs => rw [Fintype.sum_prod_type]
        conv_rhs => rw [Fintype.sum_prod_type_right, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by
          dsimp only
          by_cases h1 : prefixVec i y = yp ∧ s i = si ∧ suffixVec i s = ss
          · simp only [h1.1, h1.2.1, h1.2.2, ↓reduceIte]; dsimp only [UnifM]; ring
          · have ha : ¬ ((prefixVec i y, s i, (m, suffixVec i s)) = (yp, si, (m, ss))) := by
              intro h; apply h1
              exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2.2) h⟩
            have hb : ¬ ((prefixVec i y, s i, suffixVec i s) = (yp, si, ss)) := by
              intro h; apply h1
              exact ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1) h, congrArg (fun z => z.2.2) h⟩
            simp [ha, hb]
      · intro m' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hL, hR]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [csiszar_sum_identity (Qm m)]
  -- 5. Combine chain rules + coordinate identities + conditional Csiszár:
  --    `I(M; Y^n) ≤ ∑ i, [I(U_i; Y_i) - I(U_i; S_i)]`.
  have hsum_le :
      mutualInfo (P.map (fun t => (t.1, t.2.2))) ≤
        ∑ i : Fin n,
          (mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.2 i))) -
           mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.1 i)))) := by
    have hdiff : mutualInfo (P.map (fun t => (t.1, t.2.2))) =
        mutualInfo (P.map (fun t => (t.1, t.2.2))) - mutualInfo (P.map (fun t => (t.1, t.2.1))) := by
      rw [hI_MS, sub_zero]
    rw [hdiff, gp_mi_chain_forward (P.map (fun t => (t.1, t.2.2))),
        gp_mi_chain_backward (P.map (fun t => (t.1, t.2.1)))]
    simp only [map_comp_eq, Function.comp_def]
    have hY_id : ∀ i : Fin n,
        condMutualInfo (P.map (fun t => (t.1, t.2.2 i, prefixVec i t.2.2))) =
          mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.2 i))) -
          condMutualInfo (P.map (fun t => (t.2.2 i, suffixVec i t.2.1, (t.1, prefixVec i t.2.2)))) -
          mutualInfo (P.map (fun t => (prefixVec i t.2.2, t.2.2 i))) := by
      intro i
      have h := gp_coord_Y_identity (P.map (fun t => (t.1, t.2.2 i, prefixVec i t.2.2, suffixVec i t.2.1)))
      simpa only [map_comp_eq, Function.comp_def] using h
    have hS_id : ∀ i : Fin n,
        condMutualInfo (P.map (fun t => (t.1, t.2.1 i, suffixVec i t.2.1))) =
          mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.1 i))) -
          condMutualInfo (P.map (fun t => (prefixVec i t.2.2, t.2.1 i, (t.1, suffixVec i t.2.1)))) -
          mutualInfo (P.map (fun t => (t.2.1 i, suffixVec i t.2.1))) := by
      intro i
      have h := gp_coord_S_identity (P.map (fun t => (t.1, t.2.1 i, prefixVec i t.2.2, suffixVec i t.2.1)))
      simpa only [map_comp_eq, Function.comp_def] using h
    simp_rw [hY_id, hS_id, hI_Si_suff, sub_zero]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]
    have hnn : 0 ≤ ∑ i : Fin n, mutualInfo (P.map (fun t => (prefixVec i t.2.2, t.2.2 i))) :=
      Finset.sum_nonneg fun i _ => mutualInfo_nonneg _
    linarith
  -- 6. For each coordinate `i : Fin n`, `(S_i, U_i, X_i, Y_i)` is a valid stochastic GP witness!
  have hcoord_le : ∀ i : Fin n,
      mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.2 i))) -
      mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.1 i))) ≤
        gelfandPinskerCapacity Ps W := by
    intro i
    let Ui := Fin M × (Fin i.1 → Y) × (Fin (n - 1 - i.1) → S)
    let Psux : ProbDist (S × Ui × X) :=
      P.map (fun t => (t.2.1 i, (t.1, prefixVec i t.2.2, suffixVec i t.2.1), code.enc t.1 t.2.1 i))
    have hPsux_fst : Psux.map Prod.fst = Ps := by
      unfold Psux; rw [map_comp_eq]
      have h1 : P.map (fun t => t.2.1 i) = (iidDist Ps n).map (fun s => s i) := by
        rw [← hP_S, map_comp_eq]; rfl
      rw [show (Prod.fst ∘ fun t : Fin M × (Fin n → S) × (Fin n → Y) =>
          (t.2.1 i, (t.1, prefixVec i t.2.2, suffixVec i t.2.1), code.enc t.1 t.2.1 i)) =
          fun t => t.2.1 i from rfl, h1]
      apply gp_probDist_ext; intro a
      unfold ProbDist.map; dsimp only
      have h2 : (∑ s : Fin n → S, if s i = a then (iidDist Ps n).pmf s else 0) =
          ∑ s : Fin n → S, (iidDist Ps n).pmf s * (if s i = a then 1 else 0) :=
        Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
      rw [h2, iidDist_sum_coord Ps (fun b => if b = a then 1 else 0) i, Finset.sum_eq_single a]
      · simp
      · intro b _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    -- Key channel Markov factorization: `(S_i, U_i, X_i, Y_i) ~ gpStochJoint W Psux`.
    have hmarkov_i :
        P.map (fun t => (t.2.1 i, (t.1, prefixVec i t.2.2, suffixVec i t.2.1), code.enc t.1 t.2.1 i, t.2.2 i)) =
          gpStochJoint W Psux := by
      apply gp_probDist_ext; rintro ⟨si, ⟨m, yp, ss⟩, xi, yi⟩
      dsimp only [gpStochJoint, Psux, P, gpCodeJoint]; unfold ProbDist.map; dsimp only
      conv_lhs => rw [Fintype.sum_prod_type]
      conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_mul]
      rw [Finset.sum_eq_single m, Finset.sum_eq_single m]
      · conv_lhs => rw [Fintype.sum_prod_type]
        conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hs : s i = si ∧ suffixVec i s = ss ∧ code.enc m s i = xi
        · rcases hs with ⟨hsi, hss, hxi⟩
          -- Factor out `UnifM.pmf m * (iidDist Ps n).pmf s` and evaluate the `y`-sum by `Fintype.prod_sum`.
          trans (UnifM.pmf m * (iidDist Ps n).pmf s *
            ∑ y : Fin n → Y, if prefixVec i y = yp ∧ y i = yi
              then ∏ j : Fin n, W.trans (code.enc m s j, s j) (y j) else 0)
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => by
              simp [hsi, hss, hxi, DMC.power, UnifM]
          · symm
            trans (UnifM.pmf m * (iidDist Ps n).pmf s *
              ((∑ y : Fin n → Y, if prefixVec i y = yp
                  then ∏ j : Fin n, W.trans (code.enc m s j, s j) (y j) else 0) * W.trans (xi, si) yi))
            · conv_lhs => rw [Finset.sum_mul]
              conv_rhs => rw [Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => by
                dsimp only [Ui, DMC.power, UnifM]
                by_cases hyp : prefixVec i y = yp
                · simp [hsi, hss, hxi, hyp]; ring
                · simp [hsi, hss, hxi, hyp]
            · symm; congr 1
              -- Evaluate both `y`-sums using `Fintype.prod_sum`.
              let F₁ : Fin n → Y → ℝ := fun j yj =>
                if h : j.1 < i.1 then (if yj = yp ⟨j.1, h⟩ then W.trans (code.enc m s j, s j) yj else 0)
                else if j = i then (if yj = yi then W.trans (code.enc m s j, s j) yj else 0)
                else W.trans (code.enc m s j, s j) yj
              let F₂ : Fin n → Y → ℝ := fun j yj =>
                if h : j.1 < i.1 then (if yj = yp ⟨j.1, h⟩ then W.trans (code.enc m s j, s j) yj else 0)
                else W.trans (code.enc m s j, s j) yj
              have hF₁ : ∀ y : Fin n → Y,
                  (if prefixVec i y = yp ∧ y i = yi then ∏ j : Fin n, W.trans (code.enc m s j, s j) (y j) else 0) =
                    ∏ j : Fin n, F₁ j (y j) := by
                intro y
                by_cases h : prefixVec i y = yp ∧ y i = yi
                · simp only [h.1, h.2, and_self, ↓reduceIte]
                  refine Finset.prod_congr rfl fun j _ => ?_
                  dsimp only [F₁]
                  by_cases hlt : j.1 < i.1
                  · simp only [hlt, ↓reduceDIte]
                    have := congrFun h.1 ⟨j.1, hlt⟩; simp [prefixVec] at this; simp [this]
                  · by_cases hji : j = i
                    · subst hji; simp [h.2]
                    · simp [hlt, hji]
                · simp only [h, ↓reduceIte]; symm
                  by_cases hyi : y i = yi
                  · have hne : prefixVec i y ≠ yp := fun hp => h ⟨hp, hyi⟩
                    have hex : ∃ k : Fin i.1, prefixVec i y k ≠ yp k := by
                      by_contra hall; push Not at hall; exact hne (funext hall)
                    obtain ⟨k, hk⟩ := hex
                    let j : Fin n := ⟨k.1, lt_trans k.2 i.2⟩
                    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
                    have hjlt : j.1 < i.1 := k.2
                    dsimp only [F₁]; simp only [hjlt, ↓reduceDIte]
                    have hne' : y j ≠ yp ⟨j.1, hjlt⟩ := hk
                    simp [hne']
                  · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
                    dsimp only [F₁]; simp only [lt_irrefl, ↓reduceDIte, ↓reduceIte, hyi]
              have hF₂ : ∀ y : Fin n → Y,
                  (if prefixVec i y = yp then ∏ j : Fin n, W.trans (code.enc m s j, s j) (y j) else 0) =
                    ∏ j : Fin n, F₂ j (y j) := by
                intro y
                by_cases h : prefixVec i y = yp
                · simp only [h, ↓reduceIte]
                  refine Finset.prod_congr rfl fun j _ => ?_
                  dsimp only [F₂]
                  by_cases hlt : j.1 < i.1
                  · simp only [hlt, ↓reduceDIte]
                    have := congrFun h ⟨j.1, hlt⟩; simp [prefixVec] at this; simp [this]
                  · simp [hlt]
                · simp only [h, ↓reduceIte]; symm
                  have hex : ∃ k : Fin i.1, prefixVec i y k ≠ yp k := by
                    by_contra hall; push Not at hall; exact h (funext hall)
                  obtain ⟨k, hk⟩ := hex
                  let j : Fin n := ⟨k.1, lt_trans k.2 i.2⟩
                  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
                  have hjlt : j.1 < i.1 := k.2
                  dsimp only [F₂]; simp only [hjlt, ↓reduceDIte]
                  have hne' : y j ≠ yp ⟨j.1, hjlt⟩ := hk
                  simp [hne']
              simp_rw [hF₁, hF₂, ← Fintype.prod_sum F₁, ← Fintype.prod_sum F₂]
              rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ yj : Y, F₁ j yj) (Finset.mem_univ i),
                  ← Finset.mul_prod_erase Finset.univ (fun j => ∑ yj : Y, F₂ j yj) (Finset.mem_univ i)]
              have hi₁ : ∑ yj : Y, F₁ i yj = W.trans (xi, si) yi := by
                dsimp only [F₁]
                simp only [lt_irrefl, ↓reduceDIte, ↓reduceIte, hxi, hsi]
                rw [Finset.sum_eq_single yi]
                · simp
                · intro y' _ hne; simp [hne]
                · intro h; exact absurd (Finset.mem_univ _) h
              have hi₂ : ∑ yj : Y, F₂ i yj = 1 := by
                dsimp only [F₂]
                simp only [lt_irrefl, ↓reduceDIte]
                exact W.sum_one _
              have hrest : ∏ j ∈ Finset.univ.erase i, (∑ yj : Y, F₁ j yj) =
                  ∏ j ∈ Finset.univ.erase i, (∑ yj : Y, F₂ j yj) :=
                Finset.prod_congr rfl fun j hj => by
                  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
                  refine Finset.sum_congr rfl fun yj _ => ?_
                  dsimp only [F₁, F₂]
                  by_cases hlt : j.1 < i.1
                  · simp [hlt]
                  · simp [hlt, hji]
              rw [hi₁, hi₂, hrest]; ring
        · -- `s` fails one of the constraints: both sides vanish identically.
          have hL0 : ∀ y : Fin n → Y,
              ¬ ((s i, (m, prefixVec i y, suffixVec i s), code.enc m s i, y i) =
                (si, (m, yp, ss), xi, yi)) := fun y h => hs
            ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1.2.2) h, congrArg (fun z => z.2.2.1) h⟩
          have hR0 : ∀ y : Fin n → Y,
              ¬ ((s i, (m, prefixVec i y, suffixVec i s), code.enc m s i) =
                (si, (m, yp, ss), xi)) := fun y h => hs
            ⟨congrArg Prod.fst h, congrArg (fun z => z.2.1.2.2) h, congrArg (fun z => z.2.2) h⟩
          simp [hL0, hR0]
      · intro m' _ hne
        have h0 : ∀ sy : (Fin n → S) × (Fin n → Y),
            ¬ ((sy.1 i, (m', prefixVec i sy.2, suffixVec i sy.1), code.enc m' sy.1 i) =
              (si, (m, yp, ss), xi)) := fun sy h => hne (congrArg (fun z => z.2.1.1) h)
        simp [h0]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro m' _ hne
        have h0 : ∀ sy : (Fin n → S) × (Fin n → Y),
            ¬ ((sy.1 i, (m', prefixVec i sy.2, suffixVec i sy.1), code.enc m' sy.1 i, sy.2 i) =
              (si, (m, yp, ss), xi, yi)) := fun sy h => hne (congrArg (fun z => z.2.1.1) h)
        simp [h0]
      · intro h; exact absurd (Finset.mem_univ _) h
    have huy_eq : (gpStochJoint W Psux).map (fun t => (t.2.1, t.2.2.2)) =
        P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.2 i)) := by
      rw [← hmarkov_i, map_comp_eq]; rfl
    have hsu_eq : Psux.map (fun t => (t.1, t.2.1)) =
        (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.1 i))).map Prod.swap := by
      unfold Psux; rw [map_comp_eq, map_comp_eq]; rfl
    have hge := gelfandPinskerCapacity_ge_stoch Ps W Psux hPsux_fst
    rw [huy_eq, hsu_eq, mutualInfo_swap] at hge
    exact hge
  calc mutualInfo (P.map (fun t => (t.1, t.2.2)))
    _ ≤ ∑ i : Fin n,
          (mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.2 i))) -
           mutualInfo (P.map (fun t => ((t.1, prefixVec i t.2.2, suffixVec i t.2.1), t.2.1 i)))) := hsum_le
    _ ≤ ∑ _i : Fin n, gelfandPinskerCapacity Ps W := Finset.sum_le_sum fun i _ => hcoord_le i
    _ = (n : ℝ) * gelfandPinskerCapacity Ps W := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Fano + Single-Letterization Finite-Blocklength Rate Converse** (El Gamal & Kim §7.4.1):
    for any `(n, M)` Gelfand–Pinsker code (`n ≥ 1, M ≥ 2`),
    `(1 - P_e) · (log₂ M / n) ≤ gelfandPinskerCapacity Ps W + 1 / n`. -/
theorem gpCode_rate_converse (Ps : ProbDist S) (W : StateChannel X S Y) {n M : ℕ}
    (hn : 0 < n) (hM : 2 ≤ M) (code : GelfandPinskerCode X S Y n M) :
    (1 - gpAvgError Ps W code) * (log2 (M : ℝ) / (n : ℝ)) ≤
      gelfandPinskerCapacity Ps W + 1 / (n : ℝ) := by
  have hM_pos : 0 < M := by omega
  have : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
  let P_MY := (gpCodeJoint Ps W hM_pos code).map (fun t => (t.1, t.2.2))
  have herr : estErrorProb P_MY code.dec = gpAvgError Ps W code := by
    classical
    unfold P_MY estErrorProb gpAvgError gpCodeJoint ProbDist.map ProbDist.uniform
    have hMne : M ≠ 0 := by omega
    simp only [hMne, ↓reduceIte, Fintype.card_fin]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : ∀ y : Fin n → Y,
        (if code.dec y ≠ m then
          ∑ x : Fin M × (Fin n → S) × (Fin n → Y),
            if (x.1, x.2.2) = (m, y) then
              1 / (M : ℝ) * (iidDist Ps n).pmf x.2.1 *
                (W.power n).trans (fun i => (code.enc x.1 x.2.1 i, x.2.1 i)) x.2.2
            else 0
        else 0) =
        ∑ s : Fin n → S,
          if code.dec y ≠ m then
            1 / (M : ℝ) * ((iidDist Ps n).pmf s *
              (W.power n).trans (fun i => (code.enc m s i, s i)) y)
          else 0 := fun y => by
      by_cases hdec : code.dec y = m
      · simp [hdec]
      · simp only [hdec, ne_eq, not_false_eq_true, ↓reduceIte]
        rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
        · rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_eq_single y]
          · simp; ring
          · intro y' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro m' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
  have hpe0 : 0 ≤ gpAvgError Ps W code := herr ▸ estErrorProb_nonneg P_MY code.dec
  have hpe1 : gpAvgError Ps W code ≤ 1 := herr ▸ estErrorProb_le_one P_MY code.dec
  have hfano := fano_inequality P_MY code.dec (by simpa using hM)
  rw [herr, Fintype.card_fin] at hfano
  have hP_MY_fst : P_MY.fst = ProbDist.uniform (α := Fin M) := by
    apply gp_probDist_ext; intro m
    rw [← gp_probDist_map_fst]; unfold P_MY; rw [map_comp_eq]
    unfold gpCodeJoint ProbDist.map; dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · simp only [↓reduceIte]
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, (W.power n).sum_one, mul_one, ← Finset.mul_sum,
        (iidDist Ps n).sum_one, mul_one]
    · intro m' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hHM : shannonEntropy P_MY.fst = log2 (M : ℝ) := by
    rw [hP_MY_fst]
    have h := (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin M))).mpr rfl
    simpa using h
  have hmi_le : mutualInfo P_MY ≤ (n : ℝ) * gelfandPinskerCapacity Ps W :=
    gpCode_mutualInfo_le Ps W hM_pos code
  have hid : log2 (M : ℝ) = condEntropy P_MY + mutualInfo P_MY := by
    unfold condEntropy mutualInfo; linarith [hHM]
  have hbin : binaryEntropy (gpAvgError Ps W code) ≤ 1 := gp_binaryEntropy_le_one hpe0 hpe1
  have hlog : log2 ((M : ℝ) - 1) ≤ log2 (M : ℝ) := by
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    exact gp_log2_le_log2 hM1 (by linarith)
  have hmul : gpAvgError Ps W code * log2 ((M : ℝ) - 1) ≤ gpAvgError Ps W code * log2 (M : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hpe0
  have hmain : (1 - gpAvgError Ps W code) * log2 (M : ℝ) ≤
      (n : ℝ) * gelfandPinskerCapacity Ps W + 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc (1 - gpAvgError Ps W code) * (log2 (M : ℝ) / (n : ℝ))
    _ = ((1 - gpAvgError Ps W code) * log2 (M : ℝ)) / (n : ℝ) := by ring
    _ ≤ ((n : ℝ) * gelfandPinskerCapacity Ps W + 1) / (n : ℝ) :=
        div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
    _ = gelfandPinskerCapacity Ps W + 1 / (n : ℝ) := by
        rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hn_pos)]

/-- **Gelfand–Pinsker Weak Converse** (Gelfand & Pinsker 1980; El Gamal & Kim Thm. 7.3 converse):
    every operationally achievable rate satisfies `R ≤ gelfandPinskerCapacity Ps W`. -/
theorem gelfand_pinsker_converse (Ps : ProbDist S) (W : StateChannel X S Y) {R : ℝ}
    (hR : IsGPAchievable Ps W R) :
    R ≤ gelfandPinskerCapacity Ps W := by
  by_contra hlt
  push Not at hlt
  have hcap0 : 0 ≤ gelfandPinskerCapacity Ps W := gelfandPinskerCapacity_nonneg Ps W
  let Δ : ℝ := R - gelfandPinskerCapacity Ps W
  have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
  have hRpos : 0 < R := by linarith
  let δ : ℝ := min (1 / 2) (Δ / (4 * R))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδR : δ * R ≤ Δ / 4 := by
    have h1 : δ ≤ Δ / (4 * R) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hRpos)
    have h3 : Δ / (4 * R) * R = Δ / 4 := by field_simp [ne_of_gt hRpos]
    linarith
  obtain ⟨N₁, hN₁⟩ := hR.2 δ hδ_pos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (max (1 / R) (4 / Δ))
  let n : ℕ := max (max N₁ N₂) 1
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ge_N₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ 1)
  have hn_gt_max : max (1 / R) (4 / Δ) < (n : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
  have hn_gt_1R : 1 / R < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn_gt_max
  have hn_gt_4Δ : 4 / Δ < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn_gt_max
  have hnR_gt1 : 1 < (n : ℝ) * R := by
    have h := (div_lt_iff₀ hRpos).mp hn_gt_1R; linarith
  have h2n_lt : 2 / (n : ℝ) < Δ / 2 := by
    rw [div_lt_iff₀ hn_r]
    have h := (div_lt_iff₀ hΔ).mp hn_gt_4Δ; linarith
  obtain ⟨code, herr⟩ := hN₁ n hn_ge_N₁
  let M : ℕ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have h2pow_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hnR_gt1)
  have hM_ge2 : 2 ≤ M :=
    le_trans (Nat.le_floor (by exact_mod_cast h2pow_ge2)) (Nat.le_max_right 1 _)
  have hM_gt_pow : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ (M : ℝ) := by
    have hhalf : (2 : ℝ) ^ ((n : ℝ) * R - 1) = (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hsub1 : (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ (2 : ℝ) ^ ((n : ℝ) * R) - 1 := by linarith
    have hfloor : (2 : ℝ) ^ ((n : ℝ) * R) - 1 < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((2 : ℝ) ^ ((n : ℝ) * R))]
    have hleM : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) :=
      Nat.cast_le.mpr (Nat.le_max_right 1 _)
    linarith
  have hlogM_ge : (n : ℝ) * R - 1 ≤ log2 (M : ℝ) := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlog_mono := gp_log2_le_log2 hpow_pos hM_gt_pow
    rwa [gp_log2_two_rpow] at hlog_mono
  have hrate_ge : R - 1 / (n : ℝ) ≤ log2 (M : ℝ) / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hlogM_ge (le_of_lt hn_r)
    have hsimp : ((n : ℝ) * R - 1) / (n : ℝ) = R - 1 / (n : ℝ) := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hn_r)]
    linarith
  have hrate_nonneg : 0 ≤ R - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < R := (div_lt_iff₀ hn_r).mpr (by linarith)
    linarith
  have hconv := gpCode_rate_converse Ps W hn_pos hM_ge2 code
  have hprod_le : (1 - δ) * (R - 1 / (n : ℝ)) ≤
      (1 - gpAvgError Ps W code) * (log2 (M : ℝ) / (n : ℝ)) :=
    mul_le_mul (by linarith) hrate_ge hrate_nonneg (by linarith [min_le_left (1 / 2) (Δ / (4 * R))])
  have hcomb : (1 - δ) * (R - 1 / (n : ℝ)) ≤ gelfandPinskerCapacity Ps W + 1 / (n : ℝ) :=
    le_trans hprod_le hconv
  have hδn : 0 ≤ δ * (1 / (n : ℝ)) := by positivity
  have hexpand : (1 - δ) * (R - 1 / (n : ℝ)) = R - 1 / (n : ℝ) - δ * R + δ * (1 / (n : ℝ)) := by
    ring
  have h2div : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
  have hfinal : Δ ≤ δ * R + 2 / (n : ℝ) := by dsimp only [Δ]; linarith
  linarith

end GelfandPinskerConverse

/-! ### 3. Pointwise Slice Packing, Achievability & Gelfand–Pinsker Theorem
(Gelfand & Pinsker 1980; El Gamal & Kim Theorem 7.3) -/

section GelfandPinskerAchievability

variable {α β : Type*} [Fintype α] [Fintype β]

open Classical in
/-- **Pointwise Slice Packing Bound**: for EVERY fixed output sequence `y : Fin n → β`,
    the `P_X^n`-probability that an independent `X^n ~ P_X^n` is jointly weakly `ε`-typical
    with `y` satisfies `P_X^n({x : (x, y) ∈ A_ε^(n)(P)}) ≤ 2^{-n (I(X; Y) - 3ε)}`.

    Unlike the averaged bound `jointTypicalSet_indep_prob_le`, this requires NO assumption
    on the marginal distribution of `y`, which is essential in Gelfand–Pinsker coding where
    `Y^n` is generated from the encoder's chosen bin codeword rather than i.i.d. `P_Y^n`. -/
theorem jointTypicalSet_slice_indep_prob_le (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ)
    (y : Fin n → β) :
    ∑ x : Fin n → α, (iidDist P.fst n).pmf x *
        (if (x, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P - 3 * ε))) := by
  by_cases hy : y ∈ weakTypicalSet P.snd n ε
  · let Fy : Finset (Fin n → α) := Finset.univ.filter fun x => (x, y) ∈ jointTypicalSet P n ε
    have hy_ub : (iidDist P.snd n).pmf y ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) := by
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy.2
    -- Upper bound `|Fy|`: each `x ∈ Fy` contributes `≥ 2^{-n(H(X,Y)+ε)}` to `P_Y^n(y)`.
    have hcard_mul : (Fy.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) := by
      calc (Fy.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε)))
        _ = ∑ _x ∈ Fy, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ Fy, (jointIidDist P n).pmf (x, y) := by
            refine Finset.sum_le_sum fun x hx => ?_
            have hmem := (Finset.mem_filter.mp hx).2
            have hz := (mem_jointTypicalSet.mp hmem).2.2
            simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
            exact hz.1
        _ ≤ ∑ x : Fin n → α, (jointIidDist P n).pmf (x, y) :=
            Finset.sum_le_univ_sum_of_nonneg fun x => (jointIidDist P n).nonneg (x, y)
        _ = (iidDist P.snd n).pmf y := by
            change (jointIidDist P n).snd.pmf y = _; rw [jointIidDist_snd]
        _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) := hy_ub
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hcancel : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) *
        (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
    have hcard_le : (Fy.card : ℝ) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) *
        (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) := by
      have h := mul_le_mul_of_nonneg_right hcard_mul (le_of_lt hpow_pos)
      rw [mul_assoc, hcancel, mul_one] at h
      exact h
    -- Rewrite LHS as sum over `Fy` and apply `P_X^n(x) ≤ 2^{-n(H(X)-ε)}`.
    have hlhs : (∑ x : Fin n → α, (iidDist P.fst n).pmf x *
        (if (x, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0)) =
        ∑ x ∈ Fy, (iidDist P.fst n).pmf x := by
      trans (∑ x : Fin n → α, if (x, y) ∈ jointTypicalSet P n ε then (iidDist P.fst n).pmf x else 0)
      · refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
      · rw [← Finset.sum_filter]
    rw [hlhs]
    have hpx_pos : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    calc ∑ x ∈ Fy, (iidDist P.fst n).pmf x
      _ ≤ ∑ _x ∈ Fy, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hmem := (Finset.mem_filter.mp hx).2
          have hx_typ := (mem_jointTypicalSet.mp hmem).1
          simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx_typ
          exact hx_typ.2
      _ = (Fy.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) *
           (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε))) *
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) :=
          mul_le_mul_of_nonneg_right hcard_le hpx_pos
      _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P - 3 * ε))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; unfold mutualInfo; ring
  · -- If `y ∉ A_ε^(n)(Y)`, no `(x, y)` lies in `jointTypicalSet P n ε`.
    have hzero : ∀ x : Fin n → α, (x, y) ∉ jointTypicalSet P n ε :=
      fun x hmem => hy (mem_jointTypicalSet.mp hmem).2.1
    have hlhs : (∑ x : Fin n → α, (iidDist P.fst n).pmf x *
        (if (x, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0)) = 0 :=
      Finset.sum_eq_zero fun x _ => by simp [hzero x]
    rw [hlhs]
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)

variable {X S Y U : Type*} [Fintype X] [Fintype S] [Fintype Y] [Fintype U]

/-- Zero rate is always operationally achievable whenever `X` is nonempty (using a single
    message `M = 1`, which has zero decoding error). -/
theorem isGPAchievable_zero [Nonempty X] (Ps : ProbDist S) (W : StateChannel X S Y) :
    IsGPAchievable Ps W 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨1, fun n _ => ?_⟩⟩
  have hM : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  dsimp only
  rw [hM]
  let code0 : GelfandPinskerCode X S Y n 1 :=
    ⟨fun _ _ _ => Classical.arbitrary X, fun _ => ⟨0, Nat.zero_lt_one⟩⟩
  refine ⟨code0, ?_⟩
  have herr : gpAvgError Ps W code0 = 0 := by
    classical
    unfold gpAvgError code0
    simp only [Nat.one_ne_zero, ↓reduceIte, Nat.cast_one, div_one, one_mul, Fin.sum_univ_one]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finset.sum_eq_zero fun _ _ => by simp [show (⟨0, Nat.zero_lt_one⟩ : Fin 1) = 0 from rfl],
      mul_zero]
  linarith

/-- **Single-Witness Gelfand–Pinsker Achievability** (Gelfand & Pinsker 1980;
    El Gamal & Kim §7.4.2):
    for any deterministic witness `(U, Psu, f)` with `Psu.fst = Ps`, every rate
    `0 ≤ R < I(U; Y) - I(U; S)` is operationally achievable.

    Uses `covering_lemma_subset` for bin encoding, `markov_lemma_of_channel` for joint
    typicality of `(S^n, U^n, Y^n)`, and `jointTypicalSet_slice_indep_prob_le` for packing
    across wrong message bins. -/
theorem gp_achievable_of_det_aux (Ps : ProbDist S) (W : StateChannel X S Y)
    (Psu : ProbDist (S × U)) (f : U × S → X) (hfst : Psu.fst = Ps)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu) :
    IsGPAchievable Ps W R := by
  classical
  refine ⟨hR0, fun δ hδ => ?_⟩
  let J : ProbDist (S × U × Y) := gpDetJoint W Psu f
  let Puy : ProbDist (U × Y) := J.map (fun t => (t.2.1, t.2.2))
  let Pu : ProbDist U := Psu.snd
  have hPuy_fst : Puy.fst = Pu := by
    apply gp_probDist_ext; intro u
    unfold Puy Pu ProbDist.fst ProbDist.snd ProbDist.map J gpDetJoint; dsimp only
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
    · trans (∑ y' : Y, Psu.pmf (s, u) * W.trans (f (u, s), s) y')
      · refine Finset.sum_congr rfl fun y' _ => ?_
        rw [Finset.sum_eq_single y']
        · simp
        · intro y _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [← Finset.mul_sum, W.sum_one, mul_one]
    · intro u' _ hne
      exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun y' _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Parameters `gap, Hmax, ε₂, ε₁, ε_c, ε_b, R'`.
  let gap : ℝ := (mutualInfo Puy - mutualInfo Psu) - R
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let Hmax : ℝ := shannonEntropy Psu.fst + shannonEntropy Psu.snd + shannonEntropy Psu +
    shannonEntropy Puy.fst + shannonEntropy Puy.snd + shannonEntropy Puy + 1
  have hHmax : 1 ≤ Hmax := by
    dsimp [Hmax]
    linarith [shannonEntropy_nonneg Psu.fst, shannonEntropy_nonneg Psu.snd,
      shannonEntropy_nonneg Psu, shannonEntropy_nonneg Puy.fst,
      shannonEntropy_nonneg Puy.snd, shannonEntropy_nonneg Puy]
  have hHmax_pos : 0 < Hmax := by linarith
  let ε₂ : ℝ := gap / (20 * Hmax)
  have hε₂ : 0 < ε₂ := by positivity
  have hε₂_gap : ε₂ * Hmax = gap / 20 := by
    dsimp [ε₂]; field_simp [ne_of_gt hHmax_pos]
  let ε₁ : ℝ := ε₂ / 2
  have hε₁ : 0 < ε₁ := half_pos hε₂
  have hε₁_lt : ε₁ < ε₂ := by dsimp [ε₁]; linarith
  let ε_c : ℝ := ε₁ * Hmax
  let ε_b : ℝ := ε₂ * Hmax
  have hε_c : 0 < ε_c := mul_pos hε₁ hHmax_pos
  have hε_b : 0 < ε_b := mul_pos hε₂ hHmax_pos
  let R' : ℝ := mutualInfo Psu + 3 * ε_c + gap / 4
  have hR'_gt : mutualInfo Psu + 3 * ε_c < R' := by dsimp [R']; linarith
  have hR'_nonneg : 0 ≤ R' := by dsimp [R']; linarith [mutualInfo_nonneg Psu]
  -- Channel `W_mk : DMC (S × U) Y` and lifted distribution `Q_mk : ProbDist ((S × U) × Y × Unit)`
  -- for invoking `WynerZiv.markov_lemma_of_channel`.
  let W_mk : DMC (S × U) Y :=
    { trans := fun su y => W.trans (f (su.2, su.1), su.1) y
      nonneg := fun su y => W.nonneg _ _
      sum_one := fun su => W.sum_one _ }
  let Q_mk : ProbDist ((S × U) × Y × Unit) :=
    { pmf := fun t => Psu.pmf t.1 * W_mk.trans t.1 t.2.1
      nonneg := fun t => mul_nonneg (Psu.nonneg _) (W_mk.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, Fintype.sum_unique, ← Finset.mul_sum, W_mk.sum_one, mul_one]
        simpa [Fintype.sum_prod_type] using Psu.sum_one }
  have hQmk_W : ∀ (a : S × U) (b : Y),
      (Q_mk.map (fun t => (t.1, t.2.1))).pmf (a, b) =
        (Q_mk.map (fun t => t.1)).pmf a * W_mk.trans a b := by
    intro a b
    have h1 : (Q_mk.map (fun t => (t.1, t.2.1))).pmf (a, b) = Psu.pmf a * W_mk.trans a b := by
      unfold ProbDist.map Q_mk; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
        · simp
        · intro b' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : (Q_mk.map (fun t => t.1)).pmf a = Psu.pmf a := by
      unfold ProbDist.map Q_mk; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
      · rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_unique, ↓reduceIte, ← Finset.mul_sum, W_mk.sum_one, mul_one]
      · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h2]
  have hQmk_markov : condMutualInfo (Q_mk.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    let R0 := Q_mk.map (fun t => (t.2.2, t.2.1, t.1))
    unfold condMutualInfo; dsimp only
    let e1 : (Unit × (S × U)) ≃ (S × U) := Equiv.punitProd (S × U)
    let e2 : (Unit × Y × (S × U)) ≃ (Y × (S × U)) := Equiv.punitProd (Y × (S × U))
    have h1 : shannonEntropy (R0.map (fun t => (t.1, t.2.2))) = shannonEntropy (R0.map (fun t => t.2.2)) :=
      gp_shannonEntropy_map_eq_of_equiv R0 _ _ e1 (fun _ => rfl)
    have h2 : shannonEntropy R0 = shannonEntropy (R0.map (fun t => (t.2.1, t.2.2))) := by
      rw [← shannonEntropy_map_equiv e2 R0]; rfl
    linarith
  have hQmk_xu : Q_mk.map (fun t => (t.1, t.2.2)) = Psu.map (fun su => (su, ())) := by
    apply gp_probDist_ext; rintro ⟨a, ⟨⟩⟩
    unfold ProbDist.map Q_mk; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Finset.sum_eq_single a]
    · rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_unique, ↓reduceIte, ← Finset.mul_sum, W_mk.sum_one, mul_one]
    · intro a' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQmk_J : Q_mk.map (fun t => (t.1.1, t.1.2, t.2.1)) = J := by
    apply gp_probDist_ext; rintro ⟨s, u, y⟩
    unfold ProbDist.map Q_mk J gpDetJoint W_mk; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (s, u)]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
      · simp
      · intro y' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a' _ hne
      have hne' : a'.1 ≠ s ∨ a'.2 ≠ u := by
        by_contra hall; push Not at hall; exact hne (Prod.ext hall.1 hall.2)
      exact Finset.sum_eq_zero fun y' _ => by
        rcases hne' with h1 | h2
        · simp [h1]
        · simp [h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Threshold `c := δ / 4` for the 4 error contributions (covering tail, covering exp, Markov, packing).
  let c : ℝ := δ / 4
  have hc : 0 < c := by positivity
  obtain ⟨N₁, hN₁⟩ := strongTypicalSet_prob_tendsto_one Psu hε₁ hc
  obtain ⟨N₂, hN₂⟩ := gp_covering_exp_le (mutualInfo_nonneg Psu) (le_of_lt hε_c) hR'_gt hc
  let C_M : ℝ := ∑ t : (S × U) × Y × Unit, if 0 < Q_mk.pmf t then 1 / Q_mk.pmf t ^ 2 else 0
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (C_M / (c * (ε₂ - ε₁) ^ 2))
  obtain ⟨N₄, hN₄⟩ := exists_nat_gt (log2 (1 / c) / (gap / 2))
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
  have hn4 : log2 (1 / c) / (gap / 2) ≤ (n : ℝ) := le_of_lt (lt_of_lt_of_le hN₄ (by
    exact_mod_cast le_trans (le_trans (le_max_right N₃ N₄) (le_max_right _ _))
      (le_trans (le_max_left _ 1) hn)))
  set M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  set L := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R')))
  have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hL_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hM_ne : M ≠ 0 := Nat.ne_of_gt hM_pos
  -- Random codebook ensemble `C : Fin M → Fin L → Fin n → U`, with independent sub-codebooks `C m`.
  let W_bin : ProbDist (Fin L → Fin n → U) := codebookDist Pu n L
  let W_C : ProbDist (Fin M → Fin L → Fin n → U) := iidDist W_bin M
  -- Covering set `S_cov ⊆ jointTypicalSet Psu n ε_c` and decoding set `A_b = jointTypicalSet Puy n ε_b`.
  let S_cov : Finset ((Fin n → S) × (Fin n → U)) :=
    Finset.univ.filter fun su => zipEquiv S U n su ∈ strongTypicalSet Psu n ε₁
  let A_b : Finset ((Fin n → U) × (Fin n → Y)) := jointTypicalSet Puy n ε_b
  have hS_sub : S_cov ⊆ jointTypicalSet Psu n ε_c := by
    intro su hsu
    have hmem : zipEquiv S U n su ∈ strongTypicalSet Psu n ε₁ := (Finset.mem_filter.mp hsu).2
    have hle1 : ε₁ * shannonEntropy Psu.fst ≤ ε_c := by
      dsimp [ε_c]
      have : shannonEntropy Psu.fst ≤ Hmax := by
        dsimp [Hmax]
        linarith [shannonEntropy_nonneg Psu.snd, shannonEntropy_nonneg Psu,
          shannonEntropy_nonneg Puy.fst, shannonEntropy_nonneg Puy.snd, shannonEntropy_nonneg Puy]
      exact mul_le_mul_of_nonneg_left this (le_of_lt hε₁)
    have hle2 : ε₁ * shannonEntropy Psu.snd ≤ ε_c := by
      dsimp [ε_c]
      have : shannonEntropy Psu.snd ≤ Hmax := by
        dsimp [Hmax]
        linarith [shannonEntropy_nonneg Psu.fst, shannonEntropy_nonneg Psu,
          shannonEntropy_nonneg Puy.fst, shannonEntropy_nonneg Puy.snd, shannonEntropy_nonneg Puy]
      exact mul_le_mul_of_nonneg_left this (le_of_lt hε₁)
    have hle3 : ε₁ * shannonEntropy Psu ≤ ε_c := by
      dsimp [ε_c]
      have : shannonEntropy Psu ≤ Hmax := by
        dsimp [Hmax]
        linarith [shannonEntropy_nonneg Psu.fst, shannonEntropy_nonneg Psu.snd,
          shannonEntropy_nonneg Puy.fst, shannonEntropy_nonneg Puy.snd, shannonEntropy_nonneg Puy]
      exact mul_le_mul_of_nonneg_left this (le_of_lt hε₁)
    exact strongTypicalSet_mem_jointTypicalSet Psu hn_pos (le_of_lt hε₁) hle1 hle2 hle3 hmem
  -- Bin encoder index, encoder, decoder, and Gelfand–Pinsker code for a fixed codebook `C`.
  let idx : (Fin L → Fin n → U) → (Fin n → S) → Fin L := fun Cm s =>
    if h : ∃ l : Fin L, (s, Cm l) ∈ S_cov then Classical.choose h else ⟨0, hL_pos⟩
  let encBin : (Fin L → Fin n → U) → (Fin n → S) → (Fin n → X) :=
    fun Cm s i => f (Cm (idx Cm s) i, s i)
  let decOf : (Fin M → Fin L → Fin n → U) → (Fin n → Y) → Fin M := fun C y =>
    if h : ∃! m : Fin M, ∃ l : Fin L, (C m l, y) ∈ A_b then Classical.choose h else ⟨0, hM_pos⟩
  let codeOf : (Fin M → Fin L → Fin n → U) → GelfandPinskerCode X S Y n M :=
    fun C => ⟨fun m s => encBin (C m) s, decOf C⟩
  -- Pointwise error indicator decomposition into `E1 + E2 + E3`.
  let E1 : (Fin L → Fin n → U) → (Fin n → S) → ℝ := fun Cm s =>
    if ∀ l : Fin L, (s, Cm l) ∉ S_cov then 1 else 0
  let E2 : (Fin L → Fin n → U) → (Fin n → S) → (Fin n → Y) → ℝ := fun Cm s y =>
    if (s, Cm (idx Cm s)) ∈ S_cov ∧
       (fun i => ((s i, Cm (idx Cm s) i), y i, ())) ∉ strongTypicalSet Q_mk n ε₂
    then 1 else 0
  let E3 : (Fin M → Fin L → Fin n → U) → Fin M → (Fin n → Y) → ℝ := fun C m y =>
    ∑ m' ∈ Finset.univ.erase m, ∑ l' : Fin L, if (C m' l', y) ∈ A_b then (1 : ℝ) else 0
  have hpt_err : ∀ (C : Fin M → Fin L → Fin n → U) (m : Fin M) (s : Fin n → S) (y : Fin n → Y),
      (if decOf C y ≠ m then (1 : ℝ) else 0) ≤ E1 (C m) s + E2 (C m) s y + E3 C m y := by
    intro C m s y
    have hE1_0 : 0 ≤ E1 (C m) s := by dsimp [E1]; split_ifs <;> norm_num
    have hE2_0 : 0 ≤ E2 (C m) s y := by dsimp [E2]; split_ifs <;> norm_num
    have hE3_0 : 0 ≤ E3 C m y :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    by_cases herr : decOf C y = m
    · simp only [herr, ne_eq, not_true_eq_false, ↓reduceIte]; linarith
    · simp only [herr, ne_eq, not_false_eq_true, ↓reduceIte]
      by_cases h1 : ∀ l : Fin L, (s, C m l) ∉ S_cov
      · have : E1 (C m) s = 1 := by simp [E1, h1]
        linarith
      · push Not at h1
        have hmemS : (s, C m (idx (C m) s)) ∈ S_cov := by
          simp only [idx, h1, ↓reduceDIte]; exact Classical.choose_spec h1
        by_cases h2 : (fun i => ((s i, C m (idx (C m) s) i), y i, ())) ∈ strongTypicalSet Q_mk n ε₂
        · -- True `(s, u, y)` is strongly `ε₂`-typical, so `(u, y) ∈ A_b`.
          have hJ_typ : (fun i => (s i, C m (idx (C m) s) i, y i)) ∈ strongTypicalSet J n ε₂ := by
            have hm := strongTypicalSet_map Q_mk (fun t => (t.1.1, t.1.2, t.2.1)) n ε₂ h2
            rwa [hQmk_J] at hm
          have hUY_strong : (fun i => (C m (idx (C m) s) i, y i)) ∈ strongTypicalSet Puy n ε₂ :=
            strongTypicalSet_map J (fun t => (t.2.1, t.2.2)) n ε₂ hJ_typ
          have hUY_weak : (C m (idx (C m) s), y) ∈ A_b := by
            have hle1 : ε₂ * shannonEntropy Puy.fst ≤ ε_b := by
              dsimp [ε_b]
              have : shannonEntropy Puy.fst ≤ Hmax := by
                dsimp [Hmax]
                linarith [shannonEntropy_nonneg Psu.fst, shannonEntropy_nonneg Psu.snd,
                  shannonEntropy_nonneg Psu, shannonEntropy_nonneg Puy.snd, shannonEntropy_nonneg Puy]
              exact mul_le_mul_of_nonneg_left this (le_of_lt hε₂)
            have hle2 : ε₂ * shannonEntropy Puy.snd ≤ ε_b := by
              dsimp [ε_b]
              have : shannonEntropy Puy.snd ≤ Hmax := by
                dsimp [Hmax]
                linarith [shannonEntropy_nonneg Psu.fst, shannonEntropy_nonneg Psu.snd,
                  shannonEntropy_nonneg Psu, shannonEntropy_nonneg Puy.fst, shannonEntropy_nonneg Puy]
              exact mul_le_mul_of_nonneg_left this (le_of_lt hε₂)
            have hle3 : ε₂ * shannonEntropy Puy ≤ ε_b := by
              dsimp [ε_b]
              have : shannonEntropy Puy ≤ Hmax := by
                dsimp [Hmax]
                linarith [shannonEntropy_nonneg Psu.fst, shannonEntropy_nonneg Psu.snd,
                  shannonEntropy_nonneg Psu, shannonEntropy_nonneg Puy.fst, shannonEntropy_nonneg Puy.snd]
              exact mul_le_mul_of_nonneg_left this (le_of_lt hε₂)
            exact strongTypicalSet_mem_jointTypicalSet Puy hn_pos (le_of_lt hε₂) hle1 hle2 hle3 hUY_strong
          -- Since `decOf C y ≠ m` yet `∃ l, (C m l, y) ∈ A_b`, there MUST be a wrong-bin hit `(m', l')`.
          have hcol : ∃ m' : Fin M, m' ≠ m ∧ ∃ l' : Fin L, (C m' l', y) ∈ A_b := by
            by_contra hnone
            push Not at hnone
            have huniq : ∃! k : Fin M, ∃ l : Fin L, (C k l, y) ∈ A_b := by
              refine ⟨m, ⟨idx (C m) s, hUY_weak⟩, fun k ⟨l, hl⟩ => ?_⟩
              by_contra hne
              exact hnone k hne l hl
            have hdec_eq : decOf C y = m := by
              simp only [decOf, huniq, ↓reduceDIte]
              exact (Classical.choose_spec huniq).2 m ⟨idx (C m) s, hUY_weak⟩ |>.symm
            exact herr hdec_eq
          obtain ⟨m', hm'_ne, l', hl'⟩ := hcol
          have hE3_ge : (1 : ℝ) ≤ E3 C m y := by
            calc (1 : ℝ) = (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0) := by simp [hl']
              _ ≤ ∑ l : Fin L, if (C m' l, y) ∈ A_b then (1 : ℝ) else 0 :=
                  Finset.single_le_sum
                    (f := fun l : Fin L => if (C m' l, y) ∈ A_b then (1 : ℝ) else 0)
                    (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ l')
              _ ≤ E3 C m y :=
                  Finset.single_le_sum
                    (f := fun k => ∑ l : Fin L, if (C k l, y) ∈ A_b then (1 : ℝ) else 0)
                    (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                    (Finset.mem_erase.mpr ⟨hm'_ne, Finset.mem_univ m'⟩)
          linarith
        · have : E2 (C m) s y = 1 := by simp [E2, hmemS, h2]
          linarith
  -- Bound the ensemble expectation of each of the 3 terms for a fixed message `m : Fin M`.
  have hAvg1 : ∀ m : Fin M,
      ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
        (∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) ≤
      c + c := by
    intro m
    have hsum_y : ∀ C : Fin M → Fin L → Fin n → U,
        (∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) =
        ∑ s : Fin n → S, (iidDist Psu.fst n).pmf s * E1 (C m) s := fun C => by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_mul, (W.power n).sum_one, one_mul, hfst]
    simp_rw [hsum_y]
    rw [iidDist_sum_coord W_bin (fun Cm => ∑ s : Fin n → S, (iidDist Psu.fst n).pmf s * E1 Cm s) m]
    have hcov := covering_lemma_subset Psu n L (le_of_lt hε_c) S_cov hS_sub
    have hS_prob : ∑ su ∈ S_cov, (jointIidDist Psu n).pmf su =
        ∑ z ∈ strongTypicalSet Psu n ε₁, (iidDist Psu n).pmf z := by
      have h1 : (∑ su ∈ S_cov, (jointIidDist Psu n).pmf su) =
          ∑ su : (Fin n → S) × (Fin n → U),
            if zipEquiv S U n su ∈ strongTypicalSet Psu n ε₁
            then (jointIidDist Psu n).pmf su else 0 := by
        rw [← Finset.sum_filter]
      have h2 : (∑ z ∈ strongTypicalSet Psu n ε₁, (iidDist Psu n).pmf z) =
          ∑ z : Fin n → S × U,
            if z ∈ strongTypicalSet Psu n ε₁ then (iidDist Psu n).pmf z else 0 := by
        rw [← Finset.sum_filter]; congr 1; ext z; simp
      rw [h1, h2]
      exact Fintype.sum_equiv (zipEquiv S U n) _ _ (fun _ => rfl)
    have htail1 : 1 - ∑ su ∈ S_cov, (jointIidDist Psu n).pmf su ≤ c := by
      rw [hS_prob]; linarith [hN₁ n hn1]
    have hexp1 : Real.exp (-((L : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Psu + 3 * ε_c))))) ≤ c :=
      hN₂ n hn2
    have hcov' : ∑ Cm : Fin L → Fin n → U, W_bin.pmf Cm *
        (∑ s : Fin n → S, (iidDist Psu.fst n).pmf s * E1 Cm s) ≤
        (1 - ∑ su ∈ S_cov, (jointIidDist Psu n).pmf su) +
          Real.exp (-((L : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Psu + 3 * ε_c))))) := by
      refine le_trans (le_of_eq ?_) hcov
      refine Finset.sum_congr rfl fun Cm _ => congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
      congr 1
    linarith
  have hAvg2 : ∀ (C : Fin M → Fin L → Fin n → U) (m : Fin M),
      (∑ s : Fin n → S, (iidDist Ps n).pmf s *
        ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) ≤ c := by
    intro C m
    have hinner : ∀ s : Fin n → S,
        (∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) ≤ c := by
      intro s
      by_cases hmemS : (s, C m (idx (C m) s)) ∈ S_cov
      · have hsu_typ : (fun i => (s i, C m (idx (C m) s) i)) ∈ strongTypicalSet Psu n ε₁ :=
          (Finset.mem_filter.mp hmemS).2
        have hlift_typ : (fun i => ((s i, C m (idx (C m) s) i), ())) ∈
            strongTypicalSet (Q_mk.map (fun t => (t.1, t.2.2))) n ε₁ := by
          rw [hQmk_xu]
          exact strongTypicalSet_map Psu (fun su => (su, ())) n ε₁ hsu_typ
        have hmk := markov_lemma_of_channel Q_mk W_mk hQmk_W hQmk_markov hn_pos
          (le_of_lt hε₁) hε₁_lt hlift_typ
        have hCM_le : C_M / ((n : ℝ) * (ε₂ - ε₁) ^ 2) ≤ c := by
          have hdiff : 0 < ε₂ - ε₁ := by linarith
          rw [div_le_iff₀ (by positivity)]
          have h1 := (div_lt_iff₀ (by positivity : 0 < c * (ε₂ - ε₁) ^ 2)).mp hn3
          linarith
        have heq_sum : (∑ y : Fin n → Y,
            (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) =
            ∑ y : Fin n → Y, (W_mk.power n).trans (fun i => (s i, C m (idx (C m) s) i)) y *
              (if (fun i => ((s i, C m (idx (C m) s) i), y i, ())) ∉ strongTypicalSet Q_mk n ε₂
               then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          have hE2 : E2 (C m) s y =
              if (fun i => ((s i, C m (idx (C m) s) i), y i, ())) ∉ strongTypicalSet Q_mk n ε₂
              then (1 : ℝ) else 0 := by simp [E2, hmemS]
          rw [hE2]; rfl
        have hmk' : (∑ y : Fin n → Y,
            (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) ≤
            C_M / ((n : ℝ) * (ε₂ - ε₁) ^ 2) := by
          refine le_trans (le_of_eq heq_sum) (le_trans (le_of_eq ?_) (le_trans hmk (le_of_eq ?_)))
          · refine Finset.sum_congr rfl fun y _ => congrArg _ (by split_ifs <;> rfl)
          · congr 1
        exact le_trans hmk' hCM_le
      · have h0 : ∀ y, E2 (C m) s y = 0 := fun y => by simp [E2, hmemS]
        simp_rw [h0, mul_zero, Finset.sum_const_zero]
        exact le_of_lt hc
    calc ∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y
      _ ≤ ∑ s : Fin n → S, (iidDist Ps n).pmf s * c :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hinner s) ((iidDist Ps n).nonneg s)
      _ = c := by rw [← Finset.sum_mul, (iidDist Ps n).sum_one, one_mul]
  have hAvg3 : ∀ m : Fin M,
      ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
        (∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y) ≤
      c := by
    intro m
    -- Swap sums so `∑ C` is innermost for each fixed `(m', l', s, y)` with `m' ≠ m`.
    have hrew :
        (∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
          (∑ s : Fin n → S, (iidDist Ps n).pmf s *
            ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y)) =
        ∑ m' ∈ Finset.univ.erase m, ∑ l' : Fin L, ∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y,
            ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
              ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
                (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0)) := by
      dsimp only [E3]
      have h1 : ∀ C, W_C.pmf C * (∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
            ∑ m' ∈ Finset.univ.erase m, ∑ l' : Fin L, if (C m' l', y) ∈ A_b then (1 : ℝ) else 0) =
          ∑ m' ∈ Finset.univ.erase m, ∑ l' : Fin L, ∑ s : Fin n → S, ∑ y : Fin n → Y,
            (iidDist Ps n).pmf s * (W_C.pmf C *
              ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
                (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0))) := fun C => by
        simp_rw [Finset.mul_sum]
        trans (∑ s : Fin n → S, ∑ m' ∈ Finset.univ.erase m, ∑ l' : Fin L, ∑ y : Fin n → Y,
            (iidDist Ps n).pmf s * (W_C.pmf C *
              ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
                (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0))))
        · refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m' _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun y _ => by ring
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m' _ => Finset.sum_comm
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    rw [hrew]
    -- Bound each `(m', l')` term using independence of `C m` and `C m'` + pointwise slice packing!
    have heach : ∀ m' ∈ Finset.univ.erase m, ∀ l' : Fin L,
        (∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y,
            ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
              ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
                (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0))) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) := by
      intro m' hm' l'
      have hne : m ≠ m' := (Finset.mem_erase.mp hm').1.symm
      have hC_factor : ∀ (s : Fin n → S) (y : Fin n → Y),
          (∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
            ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
              (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0))) ≤
          (∑ Cm : Fin L → Fin n → U, W_bin.pmf Cm *
            (W.power n).trans (fun i => (encBin Cm s i, s i)) y) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) := by
        intro s y
        rw [iidDist_sum_two_coords W_bin
          (fun Cm => (W.power n).trans (fun i => (encBin Cm s i, s i)) y)
          (fun Cm' => if (Cm' l', y) ∈ A_b then (1 : ℝ) else 0) hne]
        refine mul_le_mul_of_nonneg_left ?_
          (Finset.sum_nonneg fun Cm _ => mul_nonneg (W_bin.nonneg Cm) ((W.power n).nonneg _ _))
        change ∑ a : Fin L → Fin n → U, (iidDist (iidDist Pu n) L).pmf a *
            (if (a l', y) ∈ A_b then (1 : ℝ) else 0) ≤ _
        rw [iidDist_sum_coord (iidDist Pu n) (fun u' => if (u', y) ∈ A_b then (1 : ℝ) else 0) l']
        rw [← hPuy_fst]
        exact jointTypicalSet_slice_indep_prob_le Puy n ε_b y
      calc ∑ s : Fin n → S, (iidDist Ps n).pmf s *
            ∑ y : Fin n → Y, ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
              ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
                (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0))
        _ ≤ ∑ s : Fin n → S, (iidDist Ps n).pmf s *
              ∑ y : Fin n → Y,
                ((∑ Cm : Fin L → Fin n → U, W_bin.pmf Cm *
                  (W.power n).trans (fun i => (encBin Cm s i, s i)) y) *
                 (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b)))) :=
            Finset.sum_le_sum fun s _ =>
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hC_factor s y)
                ((iidDist Ps n).nonneg s)
        _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) := by
            have hinner_s : ∀ s : Fin n → S,
                (∑ y : Fin n → Y,
                  ((∑ Cm : Fin L → Fin n → U, W_bin.pmf Cm *
                    (W.power n).trans (fun i => (encBin Cm s i, s i)) y) *
                   (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))))) =
                (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) := fun s => by
              rw [← Finset.sum_mul, Finset.sum_comm]
              have h1 : (∑ Cm : Fin L → Fin n → U, ∑ y : Fin n → Y,
                  W_bin.pmf Cm * (W.power n).trans (fun i => (encBin Cm s i, s i)) y) = 1 := by
                simp_rw [← Finset.mul_sum, (W.power n).sum_one, mul_one]
                exact W_bin.sum_one
              rw [h1, one_mul]
            simp_rw [hinner_s, ← Finset.sum_mul, (iidDist Ps n).sum_one, one_mul]
    have hM_le : (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := gp_max_one_floor_two_rpow_le n hR0
    have hL_le : (L : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R') := gp_max_one_floor_two_rpow_le n hR'_nonneg
    have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    have hexp_le : (n : ℝ) * R + (n : ℝ) * R' + -((n : ℝ) * (mutualInfo Puy - 3 * ε_b)) ≤
        -((n : ℝ) * (gap / 2)) := by
      have hcoef : R + R' - (mutualInfo Puy - 3 * ε_b) ≤ -(gap / 2) := by
        dsimp only [R', ε_c, ε_b, ε₁, gap]
        linarith [hε₂_gap]
      have hmul := mul_le_mul_of_nonneg_left hcoef (le_of_lt hn_r)
      linarith
    have hcard_erase : (((Finset.univ.erase m : Finset (Fin M)).card : ℕ) : ℝ) ≤ (M : ℝ) := by
      have : (Finset.univ.erase m : Finset (Fin M)).card ≤ M := by
        calc (Finset.univ.erase m : Finset (Fin M)).card
          _ ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_le_card (Finset.erase_subset m _)
          _ = M := by simp
      exact_mod_cast this
    calc ∑ m' ∈ Finset.univ.erase m, ∑ l' : Fin L, ∑ s : Fin n → S, (iidDist Ps n).pmf s *
          ∑ y : Fin n → Y, ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
            ((W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
              (if (C m' l', y) ∈ A_b then (1 : ℝ) else 0))
      _ ≤ ∑ _m' ∈ Finset.univ.erase m, ∑ _l' : Fin L,
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) :=
          Finset.sum_le_sum fun m' hm' => Finset.sum_le_sum fun l' _ => heach m' hm' l'
      _ = (((Finset.univ.erase m : Finset (Fin M)).card : ℕ) : ℝ) *
            ((L : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b)))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * ((L : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b)))) :=
          mul_le_mul_of_nonneg_right hcard_erase (mul_nonneg (Nat.cast_nonneg L) hpow_nonneg)
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) *
            ((2 : ℝ) ^ ((n : ℝ) * R') * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Puy - 3 * ε_b)))) := by
          have h1 := mul_le_mul_of_nonneg_right hL_le hpow_nonneg
          exact mul_le_mul hM_le h1 (mul_nonneg (Nat.cast_nonneg L) hpow_nonneg) (by positivity)
      _ = (2 : ℝ) ^ ((n : ℝ) * R + (n : ℝ) * R' + -((n : ℝ) * (mutualInfo Puy - 3 * ε_b))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
      _ ≤ (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      _ ≤ c := gp_two_rpow_neg_le_of_ge (half_pos hgap) hc hn4
  -- Combine all 3 terms to bound `E_C[gpAvgError Ps W (codeOf C)] ≤ 4 * c = δ`.
  have hAvg_total : ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C * gpAvgError Ps W (codeOf C) ≤ δ := by
    have hperC : ∀ C : Fin M → Fin L → Fin n → U,
        gpAvgError Ps W (codeOf C) ≤
          ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
            ((∑ s : Fin n → S, (iidDist Ps n).pmf s *
                ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) +
             (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) +
             (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y)) := by
      intro C
      unfold gpAvgError codeOf
      simp only [hM_ne, ↓reduceIte]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
      simp_rw [← Finset.sum_add_distrib, ← mul_add]
      refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ ((iidDist Ps n).nonneg s)
      simp_rw [← Finset.sum_add_distrib, ← mul_add]
      refine Finset.sum_le_sum fun y _ => ?_
      have h1 : (if decOf C y ≠ m then (W.power n).trans (fun i => (encBin (C m) s i, s i)) y else 0) =
          (W.power n).trans (fun i => (encBin (C m) s i, s i)) y *
            (if decOf C y ≠ m then (1 : ℝ) else 0) := by split_ifs <;> ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left (hpt_err C m s y) ((W.power n).nonneg _ _)
    have hM_pos_r : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    calc ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C * gpAvgError Ps W (codeOf C)
      _ ≤ ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
            (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
              ((∑ s : Fin n → S, (iidDist Ps n).pmf s *
                  ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) +
               (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                  ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) +
               (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                  ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y))) :=
          Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hperC C) (W_C.nonneg C)
      _ = ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
            ((∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
                ∑ s : Fin n → S, (iidDist Ps n).pmf s *
                  ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) +
             (∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
                ∑ s : Fin n → S, (iidDist Ps n).pmf s *
                  ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) +
             (∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
                ∑ s : Fin n → S, (iidDist Ps n).pmf s *
                  ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y)) := by
          have hpull : ∀ C : Fin M → Fin L → Fin n → U,
              W_C.pmf C * (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
                ((∑ s : Fin n → S, (iidDist Ps n).pmf s *
                    ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) +
                 (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                    ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) +
                 (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                    ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y))) =
              ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
                (W_C.pmf C * (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                    ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E1 (C m) s) +
                 W_C.pmf C * (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                    ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) +
                 W_C.pmf C * (∑ s : Fin n → S, (iidDist Ps n).pmf s *
                    ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E3 C m y)) := by
            intro C
            rw [← mul_assoc, mul_comm (W_C.pmf C), mul_assoc, Finset.mul_sum]
            congr 1; refine Finset.sum_congr rfl fun m _ => by ring
          simp_rw [hpull, ← Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1; refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ ((1 : ℝ) / (M : ℝ)) * ∑ _m : Fin M, ((c + c) + c + c) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
          have h2 : (∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C *
              ∑ s : Fin n → S, (iidDist Ps n).pmf s *
                ∑ y : Fin n → Y, (W.power n).trans (fun i => (encBin (C m) s i, s i)) y * E2 (C m) s y) ≤ c := by
            calc _ ≤ ∑ C : Fin M → Fin L → Fin n → U, W_C.pmf C * c :=
                  Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hAvg2 C m) (W_C.nonneg C)
              _ = c := by rw [← Finset.sum_mul, W_C.sum_one, one_mul]
          linarith [hAvg1 m, hAvg3 m]
      _ = δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, one_div_mul_cancel (ne_of_gt hM_pos_r), one_mul]
          dsimp only [c]; ring
  obtain ⟨C, hC⟩ := gp_exists_le_of_expectation_le W_C (fun C => gpAvgError Ps W (codeOf C)) hAvg_total
  exact ⟨codeOf C, hC⟩

/-- **Gelfand–Pinsker Achievability** (Gelfand & Pinsker 1980; El Gamal & Kim Thm. 7.3):
    every rate `0 ≤ R < gelfandPinskerCapacity Ps W` is operationally achievable. -/
theorem gelfand_pinsker_achievability (Ps : ProbDist S) (W : StateChannel X S Y)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R < gelfandPinskerCapacity Ps W) :
    IsGPAchievable Ps W R := by
  have hne : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
      Psu.fst = Ps ∧
      r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu }.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [gelfandPinskerCapacity, hempty, Real.sSup_empty] at hR
    linarith
  obtain ⟨r, ⟨kU, Psu, f, hfst, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne hR
  exact gp_achievable_of_det_aux Ps W Psu f hfst hR0 hr

/-- **The Gelfand–Pinsker Theorem** (Gelfand & Pinsker 1980; El Gamal & Kim Theorem 7.3;
    Cover & Thomas §7.13):
    the operational capacity of a discrete memoryless state-dependent channel `(Ps, W)` with
    noncausal transmitter state information equals its single-letter Gelfand–Pinsker capacity
    `max_{P(u | s), x = f(u, s)} [I(U; Y) - I(U; S)]`. -/
theorem gelfand_pinsker_theorem (Ps : ProbDist S) (W : StateChannel X S Y) :
    gpOperationalCapacity Ps W = gelfandPinskerCapacity Ps W := by
  by_cases hX : Nonempty X
  · have hne : { R : ℝ | IsGPAchievable Ps W R }.Nonempty :=
      ⟨0, isGPAchievable_zero Ps W⟩
    have hbdd : BddAbove { R : ℝ | IsGPAchievable Ps W R } :=
      ⟨gelfandPinskerCapacity Ps W, fun _ hR => gelfand_pinsker_converse Ps W hR⟩
    have hle : gpOperationalCapacity Ps W ≤ gelfandPinskerCapacity Ps W :=
      csSup_le hne fun _ hR => gelfand_pinsker_converse Ps W hR
    have hge : gelfandPinskerCapacity Ps W ≤ gpOperationalCapacity Ps W := by
      by_contra hlt
      push Not at hlt
      have hop0 : 0 ≤ gpOperationalCapacity Ps W := le_csSup hbdd (isGPAchievable_zero Ps W)
      let R : ℝ := (gpOperationalCapacity Ps W + gelfandPinskerCapacity Ps W) / 2
      have hR0 : 0 ≤ R := by dsimp [R]; linarith
      have hRlt : R < gelfandPinskerCapacity Ps W := by dsimp [R]; linarith
      have hgt : gpOperationalCapacity Ps W < R := by dsimp [R]; linarith
      have hach : IsGPAchievable Ps W R := gelfand_pinsker_achievability Ps W hR0 hRlt
      have hRle : R ≤ gpOperationalCapacity Ps W := le_csSup hbdd hach
      linarith
    exact le_antisymm hle hge
  · have hcap_empty : { r : ℝ | ∃ (kU : ℕ) (Psu : ProbDist (S × Fin kU)) (f : Fin kU × S → X),
        Psu.fst = Ps ∧
        r = mutualInfo ((gpDetJoint W Psu f).map (fun t => (t.2.1, t.2.2))) - mutualInfo Psu } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kU, Psu, f, _, _⟩
      have hne := gp_nonempty_of_probDist Psu
      exact hX ⟨f (hne.some.2, hne.some.1)⟩
    have hop_empty : { R : ℝ | IsGPAchievable Ps W R } = ∅ := by
      ext R; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hR
      obtain ⟨N, hN⟩ := hR.2 1 zero_lt_one
      obtain ⟨code, _⟩ := hN (max N 1) (le_max_left N 1)
      have hMpos : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ (((max N 1 : ℕ) : ℝ) * R))) :=
        lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
      have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
      have hS : Nonempty S := gp_nonempty_of_probDist Ps
      exact hX ⟨code.enc ⟨0, hMpos⟩ (fun _ => hS.some) ⟨0, hn_pos⟩⟩
    rw [gpOperationalCapacity, gelfandPinskerCapacity, hop_empty, hcap_empty]

end GelfandPinskerAchievability

end InfoTheory.Bridge
