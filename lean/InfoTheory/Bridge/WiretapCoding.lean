import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.MethodOfTypes
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability

/-!
# Wyner's Wiretap Channel & Csiszár–Körner Secrecy Capacity Theorem
(Wyner 1975; Csiszár & Körner 1978; El Gamal & Kim Ch. 22, Theorem 22.1)

Purely additive, kernel-verified formalization of the discrete memoryless wiretap channel
coding theorem directly against `InfoTheory.Core.Channels.{WiretapChannel, wiretapSecrecyCapacity}`:

1. **Single-Letter Properties of `wiretapSecrecyCapacity W`**:
   - `dmcComp`, `dmcComp_power` (serial DMC composition and its `n`-fold power factorization)
   - `wiretapBobChannel`, `wiretapEveChannel`, `wiretapAuxJoint`
   - `IsStochasticallyDegradedWiretap`, `IsReverselyDegradedWiretap`, `IsLessNoisyEveWiretap`
   - `wiretapSecrecyCapacity_set_bddAbove`, `wiretapSecrecyCapacity_ge_aux`
   - `wiretapSecrecyCapacity_nonneg`, `wiretapSecrecyCapacity_le_bob`,
     `wiretapSecrecyCapacity_le_log2_card_output`
   - `wiretapSecrecyCapacity_degraded` (Wyner 1975 degraded wiretap formula:
     `C_s(W) = sup_{P_X} (I(X; Y) - I(X; Z))`)
   - `wiretapSecrecyCapacity_eq_zero_of_less_noisy_eve` and
     `wiretapSecrecyCapacity_eq_zero_of_reversely_degraded`

2. **Operational Wiretap Coding Model & Weak-Secrecy Converse (Csiszár–Körner 1978)**:
   - `WiretapCode`, `wiretapCodeJoint`, `wiretapAvgError`, `wiretapLeakage`
   - `IsWiretapWeakAchievable`, `wiretapOperationalCapacity`
   - `wiretapCode_converse_bound` (`I(M; Y^n) - I(M; Z^n) ≤ n · C_s(W)`, proved via
     forward/backward mutual-information chain rules, `csiszar_sum_identity`, and coordinate-wise
     Markov conditioning on `U_i = (Y^{<i}, Z_{>i})`)
   - `wiretapCode_rate_converse` and `wiretap_weak_secrecy_converse`

3. **Operational Wiretap Achievability & Exact Secrecy Capacity Theorem (El Gamal & Kim §22.1)**:
   - `isWiretapWeakAchievable_zero`
   - `wiretap_weak_secrecy_achievability` (random binning + prefix channel `V → X`,
     reusing `dmc_random_coding_expected_error_le` for both Bob's decoding of `(M, L)` and
     Eve's conditional decoding of `L` given `(M, Z^n)` via Fano's inequality)
   - `wiretap_secrecy_capacity_theorem`:
     `wiretapOperationalCapacity W = wiretapSecrecyCapacity W`

All theorems leave `Core/`, `Problems/`, `Known/`, `STATEMENT_LOCK.json`, and all other
`Bridge/` files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Private Information-Theoretic Helper Lemmas -/

section WiretapHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma wt_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

private lemma wt_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma wt_log2_two_rpow (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma wt_log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma wt_binaryEntropy_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p ≤ 1 := by
  let B : ProbDist Bool := ProbDist.bernoulli p hp0 hp1
  have hsh : shannonEntropy B = binaryEntropy p := by
    unfold shannonEntropy binaryEntropy B ProbDist.bernoulli
    simp
  have hle := shannonEntropy_le_log2_card B
  rw [hsh, Fintype.card_bool] at hle
  have hlog2 : log2 ((2 : ℕ) : ℝ) = 1 := by
    unfold log2
    simp [div_self (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
  linarith

private lemma wt_shannonEntropy_eq_zero_of_unique [Unique α] (P : ProbDist α) :
    shannonEntropy P = 0 := by
  have hle := shannonEntropy_le_log2_card P
  have hge := shannonEntropy_nonneg P
  rw [Fintype.card_unique] at hle
  simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
  exact le_antisymm hle hge

private lemma wt_condEntropy_eq_zero_of_unique_left [Unique α] (P : ProbDist (α × β)) :
    condEntropy P = 0 := by
  have hle := condEntropy_le_log2_card P
  have hge := condEntropy_nonneg P
  rw [Fintype.card_unique] at hle
  simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
  exact le_antisymm hle hge

private lemma wt_mutualInfo_eq_zero_of_unique_left [Unique α] (P : ProbDist (α × β)) :
    mutualInfo P = 0 := by
  have h0 : 0 ≤ mutualInfo P := mutualInfo_nonneg P
  have h1 : shannonEntropy P.fst = 0 := wt_shannonEntropy_eq_zero_of_unique P.fst
  have h2 : 0 ≤ condEntropy P := condEntropy_nonneg P
  unfold mutualInfo condEntropy at *
  linarith

private lemma wt_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  apply wt_probDist_ext; intro a
  unfold ProbDist.map ProbDist.fst; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma wt_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  apply wt_probDist_ext; intro b
  unfold ProbDist.map ProbDist.snd; dsimp only
  rw [Fintype.sum_prod_type_right, Finset.sum_eq_single b]
  · simp
  · intro b' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma wt_mutualInfo_map_equiv_left (e : α ≃ γ) (P : ProbDist (α × β)) :
    mutualInfo (P.map (fun ab => (e ab.1, ab.2))) = mutualInfo P := by
  let eProd : (α × β) ≃ (γ × β) := Equiv.prodCongr e (Equiv.refl β)
  have hmap : P.map (fun ab => (e ab.1, ab.2)) = P.map eProd := rfl
  have hfst : (P.map eProd).fst = P.fst.map e := by
    rw [← wt_probDist_map_fst, ← wt_probDist_map_fst, map_comp_eq, map_comp_eq]; rfl
  have hsnd : (P.map eProd).snd = P.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
  rw [hmap]
  unfold mutualInfo
  rw [hfst, hsnd, shannonEntropy_map_equiv e P.fst, shannonEntropy_map_equiv eProd P]

private lemma wt_shannonEntropy_map_eq_of_equiv (P : ProbDist α)
    (f : α → β) (g : α → γ) (e : β ≃ γ) (h : ∀ a, e (f a) = g a) :
    shannonEntropy (P.map f) = shannonEntropy (P.map g) := by
  have hg : P.map g = (P.map f).map e := by
    rw [map_comp_eq]; congr 1; funext a; exact (h a).symm
  rw [hg, shannonEntropy_map_equiv e]

private lemma wt_exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
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

/-- Conditional slice distribution `P_{X | Z = c}` for `c` with `P_Z(c) > 0`. -/
private noncomputable def wtCondSlice (P : ProbDist (α × γ)) (c : γ)
    (hc : 0 < P.snd.pmf c) : ProbDist α where
  pmf := fun a => P.pmf (a, c) / P.snd.pmf c
  nonneg := fun a => div_nonneg (P.nonneg (a, c)) (le_of_lt hc)
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hc)

private lemma wt_condSlice_congr {P Q : ProbDist (α × γ)} (hPQ : P = Q) (c : γ)
    (hc : 0 < P.snd.pmf c) (hc' : 0 < Q.snd.pmf c) :
    wtCondSlice P c hc = wtCondSlice Q c hc' := by
  subst hPQ; rfl

private lemma wt_condSlice_map {P : ProbDist (α × γ)} {Q : ProbDist (β × γ)}
    (f : α → β) (hQ : Q = P.map (fun ac => (f ac.1, ac.2))) (c : γ)
    (hc : 0 < P.snd.pmf c) (hc' : 0 < Q.snd.pmf c) :
    (wtCondSlice P c hc).map f = wtCondSlice Q c hc' := by
  classical
  subst hQ
  have hsnd : (P.map (fun ac => (f ac.1, ac.2))).snd = P.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
  apply wt_probDist_ext; intro b
  change (∑ a : α, if f a = b then P.pmf (a, c) / P.snd.pmf c else 0) =
    (P.map (fun ac => (f ac.1, ac.2))).pmf (b, c) / (P.map (fun ac => (f ac.1, ac.2))).snd.pmf c
  rw [hsnd]
  have hpmf : (P.map (fun ac => (f ac.1, ac.2))).pmf (b, c) =
      ∑ a : α, if f a = b then P.pmf (a, c) else 0 := by
    unfold ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single c]
    · refine Finset.sum_congr rfl fun a _ => by simp
    · intro c' _ hne; exact Finset.sum_eq_zero fun a _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hpmf, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => by split_ifs <;> simp

/-- Conditioning decomposition of conditional entropy:
    `H(X | Z) = ∑_{c : P_Z(c) > 0} P_Z(c) H(X | Z = c)`. -/
private lemma wt_condEntropy_eq_weighted_sum (P : ProbDist (α × γ)) :
    condEntropy P =
      ∑ c : γ, if hc : 0 < P.snd.pmf c then P.snd.pmf c * shannonEntropy (wtCondSlice P c hc) else 0 := by
  unfold condEntropy shannonEntropy
  rw [Fintype.sum_prod_type_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : 0 < P.snd.pmf c
  · simp only [hc, ↓reduceDIte]
    have hmul : ∀ a : α, negPLogP (P.pmf (a, c)) =
        P.snd.pmf c * negPLogP (P.pmf (a, c) / P.snd.pmf c) +
          (P.pmf (a, c) / P.snd.pmf c) * negPLogP (P.snd.pmf c) := by
      intro a
      have heq : P.pmf (a, c) = P.snd.pmf c * (P.pmf (a, c) / P.snd.pmf c) := by
        field_simp [ne_of_gt hc]
      conv_lhs => rw [heq]
      exact negPLogP_mul (le_of_lt hc) (div_nonneg (P.nonneg (a, c)) (le_of_lt hc))
    simp_rw [hmul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div]
    have hdiv : (∑ a : α, P.pmf (a, c)) / P.snd.pmf c = 1 := div_self (ne_of_gt hc)
    rw [hdiv, one_mul]
    unfold wtCondSlice; dsimp only
    ring
  · simp only [hc, ↓reduceDIte]
    have hc0 : P.snd.pmf c = 0 := le_antisymm (not_lt.mp hc) (P.snd.nonneg c)
    have hall : ∀ a : α, P.pmf (a, c) = 0 := fun a => by
      have hle : P.pmf (a, c) ≤ P.snd.pmf c :=
        Finset.single_le_sum (fun a' _ => P.nonneg (a', c)) (Finset.mem_univ a)
      linarith [P.nonneg (a, c)]
    simp [hc0, hall, negPLogP]

/-- Conditioning decomposition of conditional mutual information:
    `I(X; Y | Z) = ∑_{c : P_Z(c) > 0} P_Z(c) I(X; Y | Z = c)`. -/
private lemma wt_condMutualInfo_eq_weighted_sum (P : ProbDist (α × β × γ)) :
    let Q : ProbDist ((α × β) × γ) := P.map (fun t => ((t.1, t.2.1), t.2.2))
    condMutualInfo P =
      ∑ c : γ, if hc : 0 < Q.snd.pmf c then Q.snd.pmf c * mutualInfo (wtCondSlice Q c hc) else 0 := by
  dsimp only
  set Q : ProbDist ((α × β) × γ) := P.map (fun t => ((t.1, t.2.1), t.2.2))
  let Pxz : ProbDist (α × γ) := Q.map (fun ab_c => (ab_c.1.1, ab_c.2))
  let Pyz : ProbDist (β × γ) := Q.map (fun ab_c => (ab_c.1.2, ab_c.2))
  have hPxz_eq : P.map (fun t => (t.1, t.2.2)) = Pxz := by
    dsimp only [Pxz, Q]; rw [map_comp_eq]; rfl
  have hPyz_eq : P.map (fun t => (t.2.1, t.2.2)) = Pyz := by
    dsimp only [Pyz, Q]; rw [map_comp_eq]; rfl
  have hPz_eq : P.map (fun t => t.2.2) = Q.snd := by
    rw [← wt_probDist_map_snd]; dsimp only [Q]; rw [map_comp_eq]; rfl
  have hPxz_snd : Pxz.snd = Q.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd]; dsimp only [Pxz]; rw [map_comp_eq]; rfl
  have hPyz_snd : Pyz.snd = Q.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd]; dsimp only [Pyz]; rw [map_comp_eq]; rfl
  have hQ_ent : shannonEntropy Q = shannonEntropy P := by
    let e : (α × β × γ) ≃ ((α × β) × γ) := (Equiv.prodAssoc α β γ).symm
    exact shannonEntropy_map_equiv e P
  have hcmi_ce : condMutualInfo P = condEntropy Pxz + condEntropy Pyz - condEntropy Q := by
    unfold condMutualInfo condEntropy; dsimp only
    rw [hPxz_eq, hPyz_eq, hPz_eq, hPxz_snd, hPyz_snd, hQ_ent]
    ring
  rw [hcmi_ce, wt_condEntropy_eq_weighted_sum Pxz, wt_condEntropy_eq_weighted_sum Pyz,
    wt_condEntropy_eq_weighted_sum Q, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : 0 < Q.snd.pmf c
  · have hc_xz : 0 < Pxz.snd.pmf c := hPxz_snd ▸ hc
    have hc_yz : 0 < Pyz.snd.pmf c := hPyz_snd ▸ hc
    simp only [hc, hc_xz, hc_yz, ↓reduceDIte]
    have h1 : wtCondSlice Pxz c hc_xz = (wtCondSlice Q c hc).fst := by
      rw [← wt_probDist_map_fst]
      exact (wt_condSlice_map Prod.fst rfl c hc hc_xz).symm
    have h2 : wtCondSlice Pyz c hc_yz = (wtCondSlice Q c hc).snd := by
      rw [← wt_probDist_map_snd]
      exact (wt_condSlice_map Prod.snd rfl c hc hc_yz).symm
    rw [h1, h2, hPxz_snd, hPyz_snd]
    unfold mutualInfo
    ring
  · have hc_xz : ¬ (0 < Pxz.snd.pmf c) := hPxz_snd ▸ hc
    have hc_yz : ¬ (0 < Pyz.snd.pmf c) := hPyz_snd ▸ hc
    simp [hc, hc_xz, hc_yz]

/-- Conditioning decomposition of conditional mutual information with a paired conditioning
    variable: `I(A; B | C, D) = ∑_{c : P_C(c) > 0} P_C(c) I(A; B | D, C = c)`. -/
private lemma wt_condMutualInfo_pair_eq_weighted_sum (P : ProbDist (α × β × γ × δ)) :
    let Q : ProbDist ((α × β × δ) × γ) := P.map (fun t => ((t.1, t.2.1, t.2.2.2), t.2.2.1))
    condMutualInfo (P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      ∑ c : γ, if hc : 0 < Q.snd.pmf c then Q.snd.pmf c * condMutualInfo (wtCondSlice Q c hc) else 0 := by
  dsimp only
  set Q : ProbDist ((α × β × δ) × γ) := P.map (fun t => ((t.1, t.2.1, t.2.2.2), t.2.2.1))
  let Qad : ProbDist ((α × δ) × γ) := Q.map (fun t => ((t.1.1, t.1.2.2), t.2))
  let Qbd : ProbDist ((β × δ) × γ) := Q.map (fun t => ((t.1.2.1, t.1.2.2), t.2))
  let Qd : ProbDist (δ × γ) := Q.map (fun t => (t.1.2.2, t.2))
  have hQad_snd : Qad.snd = Q.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd]; dsimp only [Qad]; rw [map_comp_eq]; rfl
  have hQbd_snd : Qbd.snd = Q.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd]; dsimp only [Qbd]; rw [map_comp_eq]; rfl
  have hQd_snd : Qd.snd = Q.snd := by
    rw [← wt_probDist_map_snd, ← wt_probDist_map_snd]; dsimp only [Qd]; rw [map_comp_eq]; rfl
  have hEnt1 : shannonEntropy ((P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))).map
      (fun t => (t.1, t.2.2))) = shannonEntropy Qad := by
    dsimp only [Qad, Q]; rw [map_comp_eq, map_comp_eq]
    let e : (α × (γ × δ)) ≃ ((α × δ) × γ) :=
      { toFun := fun t => ((t.1, t.2.2), t.2.1)
        invFun := fun t => (t.1.1, (t.2, t.1.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have hEnt2 : shannonEntropy ((P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))).map
      (fun t => (t.2.1, t.2.2))) = shannonEntropy Qbd := by
    dsimp only [Qbd, Q]; rw [map_comp_eq, map_comp_eq]
    let e : (β × (γ × δ)) ≃ ((β × δ) × γ) :=
      { toFun := fun t => ((t.1, t.2.2), t.2.1)
        invFun := fun t => (t.1.1, (t.2, t.1.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have hEnt3 : shannonEntropy (P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      shannonEntropy Q := by
    dsimp only [Q]
    let e : (α × β × (γ × δ)) ≃ ((α × β × δ) × γ) :=
      { toFun := fun t => ((t.1, t.2.1, t.2.2.2), t.2.2.1)
        invFun := fun t => (t.1.1, t.1.2.1, (t.2, t.1.2.2))
        left_inv := fun ⟨_, _, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have hEnt4 : shannonEntropy ((P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))).map
      (fun t => t.2.2)) = shannonEntropy Qd := by
    dsimp only [Qd, Q]; rw [map_comp_eq, map_comp_eq]
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ (Equiv.prodComm γ δ) (fun _ => rfl)
  have hcmi_ce : condMutualInfo (P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      condEntropy Qad + condEntropy Qbd - condEntropy Q - condEntropy Qd := by
    unfold condMutualInfo condEntropy; dsimp only
    rw [hEnt1, hEnt2, hEnt3, hEnt4, hQad_snd, hQbd_snd, hQd_snd]
    ring
  rw [hcmi_ce, wt_condEntropy_eq_weighted_sum Qad, wt_condEntropy_eq_weighted_sum Qbd,
    wt_condEntropy_eq_weighted_sum Q, wt_condEntropy_eq_weighted_sum Qd,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : 0 < Q.snd.pmf c
  · have hc1 : 0 < Qad.snd.pmf c := hQad_snd ▸ hc
    have hc2 : 0 < Qbd.snd.pmf c := hQbd_snd ▸ hc
    have hc3 : 0 < Qd.snd.pmf c := hQd_snd ▸ hc
    simp only [hc, hc1, hc2, hc3, ↓reduceDIte]
    have hQad_eq : Qad = Q.map (fun ac => ((fun t : α × β × δ => (t.1, t.2.2)) ac.1, ac.2)) := by
      dsimp only [Qad]
    have hQbd_eq : Qbd = Q.map (fun ac => ((fun t : α × β × δ => (t.2.1, t.2.2)) ac.1, ac.2)) := by
      dsimp only [Qbd]
    have hQd_eq : Qd = Q.map (fun ac => ((fun t : α × β × δ => t.2.2) ac.1, ac.2)) := by
      dsimp only [Qd]
    have h1 : wtCondSlice Qad c hc1 = (wtCondSlice Q c hc).map (fun t => (t.1, t.2.2)) :=
      (wt_condSlice_map (fun t => (t.1, t.2.2)) hQad_eq c hc hc1).symm
    have h2 : wtCondSlice Qbd c hc2 = (wtCondSlice Q c hc).map (fun t => (t.2.1, t.2.2)) :=
      (wt_condSlice_map (fun t => (t.2.1, t.2.2)) hQbd_eq c hc hc2).symm
    have h3 : wtCondSlice Qd c hc3 = (wtCondSlice Q c hc).map (fun t => t.2.2) :=
      (wt_condSlice_map (fun t => t.2.2) hQd_eq c hc hc3).symm
    rw [h1, h2, h3, hQad_snd, hQbd_snd, hQd_snd]
    unfold condMutualInfo; dsimp only
    ring
  · have hc1 : ¬ (0 < Qad.snd.pmf c) := hQad_snd ▸ hc
    have hc2 : ¬ (0 < Qbd.snd.pmf c) := hQbd_snd ▸ hc
    have hc3 : ¬ (0 < Qd.snd.pmf c) := hQd_snd ▸ hc
    simp [hc, hc1, hc2, hc3]

end WiretapHelpers

/-! ### 1. Single-Letter Properties of `wiretapSecrecyCapacity W` -/

section SingleLetterWiretap

variable {X Y Z V α β γ : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype V]
  [Fintype α] [Fintype β] [Fintype γ]

/-- Serial composition of two DMCs `(W₁ ∘ W₂)(c | a) = ∑_b W₁(b | a) W₂(c | b)`. -/
def dmcComp (W₁ : DMC α β) (W₂ : DMC β γ) : DMC α γ where
  trans := fun a c => ∑ b : β, W₁.trans a b * W₂.trans b c
  nonneg := fun a c => Finset.sum_nonneg fun b _ => mul_nonneg (W₁.nonneg a b) (W₂.nonneg b c)
  sum_one := fun a => by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, W₂.sum_one, mul_one, W₁.sum_one]

/-- The `n`-fold memoryless power distributes over serial DMC composition:
    `(W₁ ∘ W₂)^{⊗ n} = W₁^{⊗ n} ∘ W₂^{⊗ n}`. -/
theorem dmcComp_power (W₁ : DMC α β) (W₂ : DMC β γ) (n : ℕ) :
    (dmcComp W₁ W₂).power n = dmcComp (W₁.power n) (W₂.power n) := by
  cases W₁; cases W₂
  unfold dmcComp DMC.power
  congr
  funext a c
  simp only [← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i b => _ * _)

/-- Bob's marginal DMC `W_B(y | x) = ∑_z W(y, z | x)` of a wiretap channel `W`. -/
def wiretapBobChannel (W : WiretapChannel X Y Z) : DMC X Y where
  trans := fun x y => ∑ z : Z, W.trans x (y, z)
  nonneg := fun x y => Finset.sum_nonneg fun z _ => W.nonneg x (y, z)
  sum_one := fun x => by
    rw [← Fintype.sum_prod_type]
    exact W.sum_one x

/-- Eve's marginal DMC `W_E(z | x) = ∑_y W(y, z | x)` of a wiretap channel `W`. -/
def wiretapEveChannel (W : WiretapChannel X Y Z) : DMC X Z where
  trans := fun x z => ∑ y : Y, W.trans x (y, z)
  nonneg := fun x z => Finset.sum_nonneg fun y _ => W.nonneg x (y, z)
  sum_one := fun x => by
    rw [← Fintype.sum_prod_type_right]
    exact W.sum_one x

/-- Joint distribution `(V, X, Y, Z)` induced by `Pvx : ProbDist (V × X)` and `W`. -/
def wiretapAuxJoint (W : WiretapChannel X Y Z) (Pvx : ProbDist (V × X)) :
    ProbDist (V × X × Y × Z) where
  pmf := fun t => Pvx.pmf (t.1, t.2.1) * W.trans t.2.1 (t.2.2.1, t.2.2.2)
  nonneg := fun t => mul_nonneg (Pvx.nonneg _) (W.nonneg _ _)
  sum_one := by
    simp_rw [Fintype.sum_prod_type]
    have hW : ∀ x, ∑ y : Y, ∑ z : Z, W.trans x (y, z) = 1 := fun x => by
      rw [← Fintype.sum_prod_type]; exact W.sum_one x
    simp_rw [← Finset.mul_sum, hW, mul_one]
    rw [← Fintype.sum_prod_type]; exact Pvx.sum_one

private lemma wiretapSecrecyCapacity_eq_sSup (W : WiretapChannel X Y Z) :
    wiretapSecrecyCapacity W =
      sSup { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } := rfl

/-- Stochastic degradedness of Eve's channel w.r.t. Bob's channel:
    `W_E = W_B ∘ D` for some DMC `D : DMC Y Z`. -/
def IsStochasticallyDegradedWiretap (W : WiretapChannel X Y Z) : Prop :=
  ∃ D : DMC Y Z, wiretapEveChannel W = dmcComp (wiretapBobChannel W) D

/-- Reversely degraded wiretap channel (Bob's channel is stochastically degraded w.r.t. Eve's):
    `W_B = W_E ∘ D` for some DMC `D : DMC Z Y`. -/
def IsReverselyDegradedWiretap (W : WiretapChannel X Y Z) : Prop :=
  ∃ D : DMC Z Y, wiretapBobChannel W = dmcComp (wiretapEveChannel W) D

/-- Eve is less noisy than Bob: `I(V; Y) ≤ I(V; Z)` for every Markov chain `V - X - (Y, Z)`. -/
def IsLessNoisyEveWiretap (W : WiretapChannel X Y Z) : Prop :=
  ∀ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
    mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) ≤
      mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2)))

private lemma wt_auxJoint_bob_pmf (W : WiretapChannel X Y Z) (Pvx : ProbDist (V × X))
    (v : V) (y : Y) :
    ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))).pmf (v, y) =
      ∑ x : X, Pvx.pmf (v, x) * (wiretapBobChannel W).trans x y := by
  classical
  unfold ProbDist.map wiretapAuxJoint wiretapBobChannel; dsimp only
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single y]
    · simp [Finset.mul_sum]
    · intro y' _ hne; exact Finset.sum_eq_zero fun z _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro v' _ hne
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y' _ =>
      Finset.sum_eq_zero fun z _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma wt_auxJoint_eve_pmf (W : WiretapChannel X Y Z) (Pvx : ProbDist (V × X))
    (v : V) (z : Z) :
    ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))).pmf (v, z) =
      ∑ x : X, Pvx.pmf (v, x) * (wiretapEveChannel W).trans x z := by
  classical
  unfold ProbDist.map wiretapAuxJoint wiretapEveChannel; dsimp only
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v]
  · simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single z]
    · simp [Finset.mul_sum]
    · intro z' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro v' _ hne
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun z' _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- For a Markov chain `V - X - B` with channel `C : DMC X B`, we have
    `I(V, X; B) = I(X; B)` and `I(V; B) + I(X; B | V) = I(X; B)`. -/
private lemma wt_markov_chain_rule (C : DMC X β) (Pvx : ProbDist (V × X)) :
    let Q : ProbDist ((V × X) × β) :=
      { pmf := fun t => Pvx.pmf t.1 * C.trans t.1.2 t.2
        nonneg := fun t => mul_nonneg (Pvx.nonneg _) (C.nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, C.sum_one, mul_one, Pvx.sum_one] }
    mutualInfo (Q.map (fun t => (t.1.1, t.2))) +
      condMutualInfo (Q.map (fun t => (t.1.2, t.2, t.1.1))) = C.mutualInfo Pvx.snd := by
  dsimp only
  let Cext : DMC (V × X) β := dmcPrecomp C Prod.snd
  let Q : ProbDist ((V × X) × β) := Cext.joint Pvx
  have hmi_eq : mutualInfo Q = C.mutualInfo Pvx.snd := by
    have h := dmcPrecomp_mutualInfo_eq C Pvx Prod.snd
    rwa [wt_probDist_map_snd] at h
  have hchain : mutualInfo (Q.map (fun t => (t.1.1, t.2))) +
      condMutualInfo (Q.map (fun t => (t.1.2, t.2, t.1.1))) = mutualInfo Q := by
    let Qvb : ProbDist (V × β) := Q.map (fun t => (t.1.1, t.2))
    let Qxvb : ProbDist (X × β × V) := Q.map (fun t => (t.1.2, t.2, t.1.1))
    have hQvb_fst : Qvb.fst = Qxvb.map (fun t => t.2.2) := by
      rw [← wt_probDist_map_fst]; dsimp only [Qvb, Qxvb]; rw [map_comp_eq, map_comp_eq]; rfl
    have hQvb_snd : Qvb.snd = Q.snd := by
      rw [← wt_probDist_map_snd, ← wt_probDist_map_snd]; dsimp only [Qvb]; rw [map_comp_eq]; rfl
    have hQxvb_xz : shannonEntropy (Qxvb.map (fun t => (t.1, t.2.2))) = shannonEntropy Q.fst := by
      dsimp only [Qxvb]; rw [map_comp_eq, ← wt_probDist_map_fst]
      exact wt_shannonEntropy_map_eq_of_equiv Q _ _ (Equiv.prodComm X V) (fun _ => rfl)
    have hQxvb_yz : shannonEntropy (Qxvb.map (fun t => (t.2.1, t.2.2))) = shannonEntropy Qvb := by
      dsimp only [Qxvb, Qvb]; rw [map_comp_eq]
      exact wt_shannonEntropy_map_eq_of_equiv Q _ _ (Equiv.prodComm β V) (fun _ => rfl)
    have hQxvb_all : shannonEntropy Qxvb = shannonEntropy Q := by
      dsimp only [Qxvb]
      let e : ((V × X) × β) ≃ (X × β × V) :=
        { toFun := fun t => (t.1.2, t.2, t.1.1)
          invFun := fun t => ((t.2.2, t.1), t.2.1)
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
      exact shannonEntropy_map_equiv e Q
    unfold mutualInfo condMutualInfo
    change shannonEntropy Qvb.fst + shannonEntropy Qvb.snd - shannonEntropy Qvb +
      (shannonEntropy (Qxvb.map (fun t => (t.1, t.2.2))) +
       shannonEntropy (Qxvb.map (fun t => (t.2.1, t.2.2))) -
       shannonEntropy Qxvb - shannonEntropy (Qxvb.map (fun t => t.2.2))) =
      shannonEntropy Q.fst + shannonEntropy Q.snd - shannonEntropy Q
    rw [hQvb_fst, hQvb_snd, hQxvb_xz, hQxvb_yz, hQxvb_all]
    ring
  exact hchain.trans hmi_eq

/-- Data processing inequality for auxiliary variable `V - X - Y`: `I(V; Y) ≤ I(X; Y)`. -/
private lemma wt_markov_aux_mi_le (C : DMC X β) (Pvx : ProbDist (V × X)) :
    let Q : ProbDist ((V × X) × β) :=
      { pmf := fun t => Pvx.pmf t.1 * C.trans t.1.2 t.2
        nonneg := fun t => mul_nonneg (Pvx.nonneg _) (C.nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, C.sum_one, mul_one, Pvx.sum_one] }
    mutualInfo (Q.map (fun t => (t.1.1, t.2))) ≤ C.mutualInfo Pvx.snd := by
  dsimp only
  set Q : ProbDist ((V × X) × β) :=
    { pmf := fun t => Pvx.pmf t.1 * C.trans t.1.2 t.2
      nonneg := fun t => mul_nonneg (Pvx.nonneg _) (C.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, C.sum_one, mul_one, Pvx.sum_one] }
  have hchain := wt_markov_chain_rule C Pvx
  have hcmi : 0 ≤ condMutualInfo (Q.map (fun t => (t.1.2, t.2, t.1.1))) := condMutualInfo_nonneg _
  dsimp only at hchain
  linarith

/-- The set of single-letter secrecy rates `{I(V; Y) - I(V; Z)}` is bounded above. -/
theorem wiretapSecrecyCapacity_set_bddAbove (W : WiretapChannel X Y Z) :
    BddAbove { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
      r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
          mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } := by
  refine ⟨(wiretapBobChannel W).capacity, ?_⟩
  rintro r ⟨kV, Pvx, rfl⟩
  let C := wiretapBobChannel W
  let Q : ProbDist ((Fin kV × X) × Y) :=
    { pmf := fun t => Pvx.pmf t.1 * C.trans t.1.2 t.2
      nonneg := fun t => mul_nonneg (Pvx.nonneg _) (C.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, C.sum_one, mul_one, Pvx.sum_one] }
  have hQ_vy : Q.map (fun t => (t.1.1, t.2)) =
      (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1)) := by
    classical
    apply wt_probDist_ext; intro ⟨v, y⟩
    rw [wt_auxJoint_bob_pmf]
    unfold ProbDist.map Q; dsimp only
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
      · refine Finset.sum_congr rfl fun x _ => by simp [C]
      · intro v' _ hne; exact Finset.sum_eq_zero fun x _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro y' _ hne; exact Finset.sum_eq_zero fun vx _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 : mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) ≤
      C.mutualInfo Pvx.snd := by
    rw [← hQ_vy]; exact wt_markov_aux_mi_le C Pvx
  have h2 : C.mutualInfo Pvx.snd ≤ C.capacity := dmc_mutualInfo_le_capacity C Pvx.snd
  have h3 : 0 ≤ mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) :=
    mutualInfo_nonneg _
  linarith

/-- Any finite auxiliary variable `V` with `Pvx : ProbDist (V × X)` yields a lower bound
    `I(V; Y) - I(V; Z) ≤ wiretapSecrecyCapacity W`. -/
theorem wiretapSecrecyCapacity_ge_aux (W : WiretapChannel X Y Z) (Pvx : ProbDist (V × X)) :
    mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
      mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) ≤
      wiretapSecrecyCapacity W := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let Pvx' : ProbDist (Fin (Fintype.card V) × X) := Pvx.map (fun vx => (e vx.1, vx.2))
  have hPvx'_pmf : ∀ v' x, Pvx'.pmf (v', x) = Pvx.pmf (e.symm v', x) := by
    classical
    intro v' x
    unfold Pvx' ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (e.symm v')]
    · rw [Finset.sum_eq_single x]
      · simp
      · intro x' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro v _ hne
      have hev : e v ≠ v' := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
      exact Finset.sum_eq_zero fun x' _ => by simp [hev]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hvy : (wiretapAuxJoint W Pvx').map (fun t => (t.1, t.2.2.1)) =
      ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))).map (fun vy => (e vy.1, vy.2)) := by
    classical
    apply wt_probDist_ext; intro ⟨v', y⟩
    rw [wt_auxJoint_bob_pmf]
    let B := (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))
    change (∑ x : X, Pvx'.pmf (v', x) * (wiretapBobChannel W).trans x y) =
      (B.map (fun vy => (e vy.1, vy.2))).pmf (v', y)
    unfold ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (e.symm v')]
    · rw [Finset.sum_eq_single y]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte]
        dsimp only [B]; rw [wt_auxJoint_bob_pmf]
        refine Finset.sum_congr rfl fun x _ => by rw [hPvx'_pmf]
      · intro y' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro v _ hne
      have hev : e v ≠ v' := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
      exact Finset.sum_eq_zero fun y' _ => by simp [hev]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hvz : (wiretapAuxJoint W Pvx').map (fun t => (t.1, t.2.2.2)) =
      ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))).map (fun vz => (e vz.1, vz.2)) := by
    classical
    apply wt_probDist_ext; intro ⟨v', z⟩
    rw [wt_auxJoint_eve_pmf]
    let E := (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))
    change (∑ x : X, Pvx'.pmf (v', x) * (wiretapEveChannel W).trans x z) =
      (E.map (fun vz => (e vz.1, vz.2))).pmf (v', z)
    unfold ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (e.symm v')]
    · rw [Finset.sum_eq_single z]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte]
        dsimp only [E]; rw [wt_auxJoint_eve_pmf]
        refine Finset.sum_congr rfl fun x _ => by rw [hPvx'_pmf]
      · intro z' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro v _ hne
      have hev : e v ≠ v' := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
      exact Finset.sum_eq_zero fun z' _ => by simp [hev]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hmem :
      mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
        mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) ∈
      { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } := by
    refine ⟨Fintype.card V, Pvx', ?_⟩
    rw [hvy, hvz, wt_mutualInfo_map_equiv_left e, wt_mutualInfo_map_equiv_left e]
  rw [wiretapSecrecyCapacity_eq_sSup]
  exact le_csSup (wiretapSecrecyCapacity_set_bddAbove W) hmem

/-- Non-negativity of secrecy capacity: `0 ≤ wiretapSecrecyCapacity W`. -/
theorem wiretapSecrecyCapacity_nonneg (W : WiretapChannel X Y Z) :
    0 ≤ wiretapSecrecyCapacity W := by
  by_cases hX : Nonempty X
  · let Pvx : ProbDist (Fin 1 × X) := (ProbDist.uniform (α := Fin 1)).prod ProbDist.uniform
    have hge := wiretapSecrecyCapacity_ge_aux W Pvx
    have h1 : mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) = 0 :=
      wt_mutualInfo_eq_zero_of_unique_left _
    have h2 : mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) = 0 :=
      wt_mutualInfo_eq_zero_of_unique_left _
    linarith
  · have hempty : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kV, Pvx, _⟩
      exact hX ⟨(wt_nonempty_of_probDist Pvx).some.2⟩
    rw [wiretapSecrecyCapacity_eq_sSup, hempty, Real.sSup_empty]

/-- Secrecy capacity cannot exceed Bob's point-to-point channel capacity:
    `wiretapSecrecyCapacity W ≤ (wiretapBobChannel W).capacity`. -/
theorem wiretapSecrecyCapacity_le_bob (W : WiretapChannel X Y Z) :
    wiretapSecrecyCapacity W ≤ (wiretapBobChannel W).capacity := by
  rw [wiretapSecrecyCapacity_eq_sSup]
  by_cases hX : Nonempty X
  · have hne : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) }.Nonempty :=
      ⟨_, 1, (ProbDist.uniform (α := Fin 1)).prod ProbDist.uniform, rfl⟩
    refine csSup_le hne ?_
    rintro r ⟨kV, Pvx, rfl⟩
    let C := wiretapBobChannel W
    let Q : ProbDist ((Fin kV × X) × Y) :=
      { pmf := fun t => Pvx.pmf t.1 * C.trans t.1.2 t.2
        nonneg := fun t => mul_nonneg (Pvx.nonneg _) (C.nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, C.sum_one, mul_one, Pvx.sum_one] }
    have hQ_vy : Q.map (fun t => (t.1.1, t.2)) =
        (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1)) := by
      classical
      apply wt_probDist_ext; intro ⟨v, y⟩
      rw [wt_auxJoint_bob_pmf]
      unfold ProbDist.map Q; dsimp only
      rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
        · refine Finset.sum_congr rfl fun x _ => by simp [C]
        · intro v' _ hne; exact Finset.sum_eq_zero fun x _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y' _ hne; exact Finset.sum_eq_zero fun vx _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h1 : mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) ≤
        C.mutualInfo Pvx.snd := by
      rw [← hQ_vy]; exact wt_markov_aux_mi_le C Pvx
    have h2 : C.mutualInfo Pvx.snd ≤ C.capacity := dmc_mutualInfo_le_capacity C Pvx.snd
    have h3 : 0 ≤ mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) :=
      mutualInfo_nonneg _
    linarith
  · have hempty1 : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kV, Pvx, _⟩; exact hX ⟨(wt_nonempty_of_probDist Pvx).some.2⟩
    have hempty2 : { r : ℝ | ∃ P : ProbDist X, r = (wiretapBobChannel W).mutualInfo P } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, _⟩; exact hX (wt_nonempty_of_probDist P)
    rw [hempty1, DMC.capacity, hempty2]

/-- Secrecy capacity is bounded above by `log₂ |Y|`. -/
theorem wiretapSecrecyCapacity_le_log2_card_output [Nonempty Y] (W : WiretapChannel X Y Z) :
    wiretapSecrecyCapacity W ≤ log2 (Fintype.card Y : ℝ) := by
  have hle := wiretapSecrecyCapacity_le_bob W
  have hcap : (wiretapBobChannel W).capacity ≤ log2 (Fintype.card Y : ℝ) := by
    refine Real.sSup_le ?_ ?_
    · rintro r ⟨P, rfl⟩
      unfold DMC.mutualInfo mutualInfo
      have hce : 0 ≤ condEntropy (((wiretapBobChannel W).joint P).map Prod.swap) :=
        condEntropy_nonneg _
      unfold condEntropy at hce
      rw [shannonEntropy_swap, snd_map_swap] at hce
      have hent : shannonEntropy ((wiretapBobChannel W).joint P).snd ≤ log2 (Fintype.card Y : ℝ) :=
        shannonEntropy_le_log2_card _
      linarith
    · have h1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos (α := Y)
      unfold log2
      exact div_nonneg (Real.log_nonneg h1) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  linarith

/-- Key degradedness DPI step: if `W_E = W_B ∘ D`, then for any `V - X - (Y, Z)`,
    `I(V; Y) - I(V; Z) ≤ I(X; Y) - I(X; Z)`. -/
private lemma wt_degraded_aux_le (W : WiretapChannel X Y Z)
    (hdeg : IsStochasticallyDegradedWiretap W) (Pvx : ProbDist (V × X)) :
    mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
      mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) ≤
      (wiretapBobChannel W).mutualInfo Pvx.snd - (wiretapEveChannel W).mutualInfo Pvx.snd := by
  obtain ⟨D, hD⟩ := hdeg
  let WB := wiretapBobChannel W
  let WE := wiretapEveChannel W
  let QB : ProbDist ((V × X) × Y) :=
    { pmf := fun t => Pvx.pmf t.1 * WB.trans t.1.2 t.2
      nonneg := fun t => mul_nonneg (Pvx.nonneg _) (WB.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, WB.sum_one, mul_one, Pvx.sum_one] }
  let QE : ProbDist ((V × X) × Z) :=
    { pmf := fun t => Pvx.pmf t.1 * WE.trans t.1.2 t.2
      nonneg := fun t => mul_nonneg (Pvx.nonneg _) (WE.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, WE.sum_one, mul_one, Pvx.sum_one] }
  have hQB_vy : QB.map (fun t => (t.1.1, t.2)) =
      (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1)) := by
    classical
    apply wt_probDist_ext; intro ⟨v, y⟩
    rw [wt_auxJoint_bob_pmf]
    unfold ProbDist.map QB; dsimp only
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
      · refine Finset.sum_congr rfl fun x _ => by simp [WB]
      · intro v' _ hne; exact Finset.sum_eq_zero fun x _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro y' _ hne; exact Finset.sum_eq_zero fun vx _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQE_vz : QE.map (fun t => (t.1.1, t.2)) =
      (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2)) := by
    classical
    apply wt_probDist_ext; intro ⟨v, z⟩
    rw [wt_auxJoint_eve_pmf]
    unfold ProbDist.map QE; dsimp only
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single z]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
      · refine Finset.sum_congr rfl fun x _ => by simp [WE]
      · intro v' _ hne; exact Finset.sum_eq_zero fun x _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro z' _ hne; exact Finset.sum_eq_zero fun vx _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hchainB := wt_markov_chain_rule WB Pvx
  have hchainE := wt_markov_chain_rule WE Pvx
  dsimp only at hchainB hchainE
  rw [show mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) =
      mutualInfo (QB.map (fun t => (t.1.1, t.2))) from congrArg mutualInfo hQB_vy.symm]
  rw [show mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) =
      mutualInfo (QE.map (fun t => (t.1.1, t.2))) from congrArg mutualInfo hQE_vz.symm]
  -- It suffices to show `I(X; Z | V) ≤ I(X; Y | V)`
  have hcmi_le : condMutualInfo (QE.map (fun t => (t.1.2, t.2, t.1.1))) ≤
      condMutualInfo (QB.map (fun t => (t.1.2, t.2, t.1.1))) := by
    rw [wt_condMutualInfo_eq_weighted_sum, wt_condMutualInfo_eq_weighted_sum]
    let SB : ProbDist ((X × Y) × V) := (QB.map (fun t => (t.1.2, t.2, t.1.1))).map (fun t => ((t.1, t.2.1), t.2.2))
    let SE : ProbDist ((X × Z) × V) := (QE.map (fun t => (t.1.2, t.2, t.1.1))).map (fun t => ((t.1, t.2.1), t.2.2))
    have hSB_pmf : ∀ x y v, SB.pmf ((x, y), v) = Pvx.pmf (v, x) * WB.trans x y := by
      classical
      intro x y v
      dsimp only [SB]; rw [map_comp_eq]
      unfold ProbDist.map QB; dsimp only
      rw [Fintype.sum_prod_type_right, Finset.sum_eq_single y]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
        · rw [Finset.sum_eq_single x]
          · simp
          · intro x' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro v' _ hne; exact Finset.sum_eq_zero fun x' _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y' _ hne; exact Finset.sum_eq_zero fun vx _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hSE_pmf : ∀ x z v, SE.pmf ((x, z), v) = Pvx.pmf (v, x) * WE.trans x z := by
      classical
      intro x z v
      dsimp only [SE]; rw [map_comp_eq]
      unfold ProbDist.map QE; dsimp only
      rw [Fintype.sum_prod_type_right, Finset.sum_eq_single z]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
        · rw [Finset.sum_eq_single x]
          · simp
          · intro x' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro v' _ hne; exact Finset.sum_eq_zero fun x' _ => by simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro z' _ hne; exact Finset.sum_eq_zero fun vx _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsnd_eq : SE.snd = SB.snd := by
      apply wt_probDist_ext; intro v
      unfold ProbDist.snd; dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp_rw [hSE_pmf, hSB_pmf, ← Finset.mul_sum, WE.sum_one, WB.sum_one]
    refine Finset.sum_le_sum fun v _ => ?_
    change (if hc : 0 < SE.snd.pmf v then SE.snd.pmf v * mutualInfo (wtCondSlice SE v hc) else 0) ≤
      (if hc : 0 < SB.snd.pmf v then SB.snd.pmf v * mutualInfo (wtCondSlice SB v hc) else 0)
    by_cases hv : 0 < SB.snd.pmf v
    · have hvE : 0 < SE.snd.pmf v := hsnd_eq ▸ hv
      simp only [hv, hvE, ↓reduceDIte]
      have hlift : wtCondSlice SE v hvE = ((dmcLiftRight (α := X) D).joint (wtCondSlice SB v hv)).snd := by
        classical
        apply wt_probDist_ext; intro ⟨x, z⟩
        change SE.pmf ((x, z), v) / SE.snd.pmf v =
          ∑ xy : X × Y, (SB.pmf (xy, v) / SB.snd.pmf v) * (dmcLiftRight (α := X) D).trans xy (x, z)
        rw [hSE_pmf, hsnd_eq, Fintype.sum_prod_type, Finset.sum_eq_single x]
        · have hWE_trans : WE.trans x z = ∑ y : Y, WB.trans x y * D.trans y z := by
            change (wiretapEveChannel W).trans x z = (dmcComp (wiretapBobChannel W) D).trans x z
            rw [hD]
          rw [hWE_trans, Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hSB_pmf]; simp only [dmcLiftRight, ↓reduceIte]; ring
        · intro x' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [dmcLiftRight, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hlift, hsnd_eq]
      exact mul_le_mul_of_nonneg_left (mutualInfo_channel_right_le (wtCondSlice SB v hv) D) (le_of_lt hv)
    · have hvE : ¬ (0 < SE.snd.pmf v) := hsnd_eq ▸ hv
      simp [hv, hvE]
  linarith

/-- **Wyner's Degraded Wiretap Channel Formula (Wyner 1975)**:
    when Eve's channel is stochastically degraded w.r.t. Bob's channel (`W_E = W_B ∘ D`),
    no auxiliary random variable is needed:
    `wiretapSecrecyCapacity W = sup_{P_X} [I(X; Y) - I(X; Z)]`. -/
theorem wiretapSecrecyCapacity_degraded (W : WiretapChannel X Y Z)
    (hdeg : IsStochasticallyDegradedWiretap W) :
    wiretapSecrecyCapacity W =
      sSup { r : ℝ | ∃ Px : ProbDist X,
        r = (wiretapBobChannel W).mutualInfo Px - (wiretapEveChannel W).mutualInfo Px } := by
  by_cases hX : Nonempty X
  · have hS1_ne : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) }.Nonempty :=
      ⟨_, 1, (ProbDist.uniform (α := Fin 1)).prod ProbDist.uniform, rfl⟩
    have hS2_ne : { r : ℝ | ∃ Px : ProbDist X,
        r = (wiretapBobChannel W).mutualInfo Px - (wiretapEveChannel W).mutualInfo Px }.Nonempty :=
      ⟨_, ProbDist.uniform, rfl⟩
    have hS2_bdd : BddAbove { r : ℝ | ∃ Px : ProbDist X,
        r = (wiretapBobChannel W).mutualInfo Px - (wiretapEveChannel W).mutualInfo Px } := by
      refine ⟨(wiretapBobChannel W).capacity, ?_⟩
      rintro r ⟨Px, rfl⟩
      have h1 : (wiretapBobChannel W).mutualInfo Px ≤ (wiretapBobChannel W).capacity :=
        dmc_mutualInfo_le_capacity (wiretapBobChannel W) Px
      have h2 : 0 ≤ (wiretapEveChannel W).mutualInfo Px := mutualInfo_nonneg _
      linarith
    apply le_antisymm
    · rw [wiretapSecrecyCapacity_eq_sSup]
      refine csSup_le hS1_ne ?_
      rintro r ⟨kV, Pvx, rfl⟩
      exact le_trans (wt_degraded_aux_le W hdeg Pvx) (le_csSup hS2_bdd ⟨Pvx.snd, rfl⟩)
    · refine csSup_le hS2_ne ?_
      rintro r ⟨Px, rfl⟩
      classical
      let Pxx : ProbDist (X × X) := Px.map (fun x => (x, x))
      have hPxx_pmf : ∀ x₁ x₂, Pxx.pmf (x₁, x₂) = if x₁ = x₂ then Px.pmf x₁ else 0 := by
        intro x₁ x₂
        unfold Pxx ProbDist.map; dsimp only
        by_cases h : x₁ = x₂
        · subst h
          rw [Finset.sum_eq_single x₁]
          · simp
          · intro x' _ hne; simp [hne]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · simp only [h, ↓reduceIte]
          exact Finset.sum_eq_zero fun x' _ => by
            split_ifs with heq
            · exact absurd ((Prod.mk.inj heq).1.symm.trans (Prod.mk.inj heq).2) h
            · rfl
      have hbob : (wiretapAuxJoint W Pxx).map (fun t => (t.1, t.2.2.1)) =
          (wiretapBobChannel W).joint Px := by
        apply wt_probDist_ext; intro ⟨x, y⟩
        rw [wt_auxJoint_bob_pmf]
        simp_rw [hPxx_pmf]
        rw [Finset.sum_eq_single x]
        · simp [DMC.joint]
        · intro x' _ hne; simp [hne.symm]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      have heve : (wiretapAuxJoint W Pxx).map (fun t => (t.1, t.2.2.2)) =
          (wiretapEveChannel W).joint Px := by
        apply wt_probDist_ext; intro ⟨x, z⟩
        rw [wt_auxJoint_eve_pmf]
        simp_rw [hPxx_pmf]
        rw [Finset.sum_eq_single x]
        · simp [DMC.joint]
        · intro x' _ hne; simp [hne.symm]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      have hge := wiretapSecrecyCapacity_ge_aux W Pxx
      rw [hbob, heve] at hge
      exact hge
  · have hempty1 : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kV, Pvx, _⟩; exact hX ⟨(wt_nonempty_of_probDist Pvx).some.2⟩
    have hempty2 : { r : ℝ | ∃ Px : ProbDist X,
        r = (wiretapBobChannel W).mutualInfo Px - (wiretapEveChannel W).mutualInfo Px } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨Px, _⟩; exact hX (wt_nonempty_of_probDist Px)
    rw [wiretapSecrecyCapacity_eq_sSup, hempty1, hempty2]

/-- If Eve is less noisy than Bob (`I(V; Y) ≤ I(V; Z)` for every `V - X - (Y, Z)`),
    then secrecy capacity is zero: `wiretapSecrecyCapacity W = 0`. -/
theorem wiretapSecrecyCapacity_eq_zero_of_less_noisy_eve (W : WiretapChannel X Y Z)
    (hln : IsLessNoisyEveWiretap W) :
    wiretapSecrecyCapacity W = 0 := by
  apply le_antisymm _ (wiretapSecrecyCapacity_nonneg W)
  rw [wiretapSecrecyCapacity_eq_sSup]
  refine Real.sSup_le ?_ le_rfl
  rintro r ⟨kV, Pvx, rfl⟩
  linarith [hln kV Pvx]

/-- If Bob's channel is stochastically degraded w.r.t. Eve's channel (`W_B = W_E ∘ D`),
    then secrecy capacity is zero: `wiretapSecrecyCapacity W = 0`. -/
theorem wiretapSecrecyCapacity_eq_zero_of_reversely_degraded (W : WiretapChannel X Y Z)
    (hrev : IsReverselyDegradedWiretap W) :
    wiretapSecrecyCapacity W = 0 := by
  obtain ⟨D, hD⟩ := hrev
  refine wiretapSecrecyCapacity_eq_zero_of_less_noisy_eve W fun kV Pvx => ?_
  have hlift : (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1)) =
      ((dmcLiftRight (α := Fin kV) D).joint
        ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2)))).snd := by
    classical
    apply wt_probDist_ext; intro ⟨v, y⟩
    rw [wt_auxJoint_bob_pmf]
    unfold ProbDist.snd DMC.joint dmcLiftRight; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single v]
    · simp only [↓reduceIte]
      simp_rw [wt_auxJoint_eve_pmf, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hWB : (wiretapBobChannel W).trans x y = ∑ z : Z, (wiretapEveChannel W).trans x z * D.trans z y := by
        change (wiretapBobChannel W).trans x y = (dmcComp (wiretapEveChannel W) D).trans x y
        rw [hD]
      rw [hWB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => by ring
    · intro v' _ hne; exact Finset.sum_eq_zero fun z _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hlift]
  exact mutualInfo_channel_right_le _ D

end SingleLetterWiretap

/-! ### 2. Operational Wiretap Channel Coding Model & Weak-Secrecy Converse -/

section WiretapConverse

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- A stochastic `(n, M)` wiretap channel code over `W : WiretapChannel X Y Z`:
    a stochastic encoder `enc : Fin M → ProbDist (Fin n → X)` and
    Bob's deterministic decoder `dec : (Fin n → Y) → Fin M`. -/
structure WiretapCode (W : WiretapChannel X Y Z) (n M : ℕ) where
  enc : Fin M → ProbDist (Fin n → X)
  dec : (Fin n → Y) → Fin M

/-- Joint distribution `(M, X^n, Y^n, Z^n)` induced by a wiretap code `code`
    with uniform message `M ~ Unif(Fin M)`. -/
noncomputable def wiretapCodeJoint (W : WiretapChannel X Y Z) {n M : ℕ} (hM : 0 < M)
    (code : WiretapCode W n M) :
    ProbDist (Fin M × (Fin n → X) × (Fin n → Y) × (Fin n → Z)) where
  pmf := fun t =>
    ((1 : ℝ) / (M : ℝ)) * (code.enc t.1).pmf t.2.1 *
      (W.power n).trans t.2.1 (fun i => (t.2.2.1 i, t.2.2.2 i))
  nonneg := fun t => mul_nonneg (mul_nonneg (by positivity) ((code.enc t.1).nonneg _))
    ((W.power n).nonneg _ _)
  sum_one := by
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
    rw [Fintype.sum_prod_type]
    have hinner : ∀ m : Fin M,
        ∑ t : (Fin n → X) × (Fin n → Y) × (Fin n → Z),
          ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf t.1 *
            (W.power n).trans t.1 (fun i => (t.2.1 i, t.2.2 i)) = (1 : ℝ) / (M : ℝ) := by
      intro m
      rw [Fintype.sum_prod_type]
      have hx : ∀ x : Fin n → X,
          ∑ yz : (Fin n → Y) × (Fin n → Z),
            ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
              (W.power n).trans x (fun i => (yz.1 i, yz.2 i)) =
            ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x := by
        intro x
        rw [← Finset.mul_sum]
        have hsum : ∑ yz : (Fin n → Y) × (Fin n → Z),
            (W.power n).trans x (zipEquiv Y Z n yz) = 1 := by
          rw [Fintype.sum_equiv (zipEquiv Y Z n) _ (fun w => (W.power n).trans x w) (fun _ => rfl)]
          exact (W.power n).sum_one x
        change (((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x) *
            (∑ yz : (Fin n → Y) × (Fin n → Z), (W.power n).trans x (zipEquiv Y Z n yz)) = _
        rw [hsum, mul_one]
      simp_rw [hx, ← Finset.mul_sum, (code.enc m).sum_one, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hMne]

/-- Average decoding error probability at Bob for a wiretap code. -/
noncomputable def wiretapAvgError (W : WiretapChannel X Y Z) {n M : ℕ} (hM : 0 < M)
    (code : WiretapCode W n M) : ℝ :=
  estErrorProb ((wiretapCodeJoint W hM code).map (fun t => (t.1, t.2.2.1))) code.dec

/-- Information leakage `I(M; Z^n)` to Eve for a wiretap code (in bits). -/
noncomputable def wiretapLeakage (W : WiretapChannel X Y Z) {n M : ℕ} (hM : 0 < M)
    (code : WiretapCode W n M) : ℝ :=
  mutualInfo ((wiretapCodeJoint W hM code).map (fun t => (t.1, t.2.2.2)))

/-- Operational weak-secrecy achievability of rate `R` over a DM wiretap channel `W`
    (Wyner 1975; Csiszár–Körner 1978; El Gamal & Kim §22.1):
    `0 ≤ R` and for every `ε > 0`, for all sufficiently large blocklengths `n`, there exists
    an `(n, max 1 ⌊2^{n R}⌋)` stochastic wiretap code with `P_e ≤ ε` and `I(M; Z^n) ≤ n ε`. -/
def IsWiretapWeakAchievable (W : WiretapChannel X Y Z) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ code : WiretapCode W n M,
      wiretapAvgError W (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)) code ≤ ε ∧
      wiretapLeakage W (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)) code ≤ (n : ℝ) * ε

/-- Operational weak-secrecy capacity `C_s^{op}(W)` of a DM wiretap channel. -/
noncomputable def wiretapOperationalCapacity (W : WiretapChannel X Y Z) : ℝ :=
  sSup { R : ℝ | IsWiretapWeakAchievable W R }

private lemma wt_sum_fin_telescope (n : ℕ) (h : ℕ → ℝ) :
    ∑ i : Fin n, (h (i.1 + 1) - h i.1) = h n - h 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]; ring

/-- Forward chain rule for mutual information:
    `I(A; B^n) = ∑_{i=0}^{n-1} I(A; B_i | B^{<i})`. -/
private lemma wt_mi_chain_forward {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
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
      simp only [hB, hi1, ↓reduceDIte]
      rw [map_comp_eq]
      refine wt_shannonEntropy_map_eq_of_equiv P _ _ ePref fun ab => ?_
      funext j; dsimp [ePref, prefixVec, pref]; split_ifs with h
      · rfl
      · exact congrArg ab.2 (Fin.ext (by dsimp only; omega))
    have h3 : shannonEntropy (P.map (fun ab => (ab.1, ab.2 i, prefixVec i ab.2))) = hAB (i.1 + 1) := by
      simp only [hAB, hi1, ↓reduceDIte]
      refine wt_shannonEntropy_map_eq_of_equiv P _ _ eAB fun ab => ?_
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
  rw [Finset.sum_sub_distrib, wt_sum_fin_telescope, wt_sum_fin_telescope]
  have hB0 : hB 0 = 0 := by simp only [hB, Nat.zero_le, ↓reduceDIte]; exact wt_shannonEntropy_eq_zero_of_unique _
  have hBn : hB n = shannonEntropy P.snd := by
    simp only [hB, le_refl, ↓reduceDIte]; rw [← wt_probDist_map_snd]
  have hAB0 : hAB 0 = shannonEntropy P.fst := by
    simp only [hAB, Nat.zero_le, ↓reduceDIte]; rw [← wt_probDist_map_fst]
    let e0 : (A × (Fin 0 → B)) ≃ A :=
      { toFun := Prod.fst
        invFun := fun a => (a, fun j => Fin.elim0 j)
        left_inv := fun ⟨_, _⟩ => Prod.ext rfl (funext fun j => Fin.elim0 j)
        right_inv := fun _ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e0 (fun _ => rfl)
  have hABn : hAB n = shannonEntropy P := by
    simp only [hAB, le_refl, ↓reduceDIte]
    have hmap : P.map (fun ab => (ab.1, pref n (le_refl n) ab.2)) = P := by
      have : (fun ab : A × (Fin n → B) => (ab.1, pref n (le_refl n) ab.2)) = id :=
        funext fun ⟨_, _⟩ => Prod.ext rfl (funext fun _ => rfl)
      rw [this]
      classical
      apply wt_probDist_ext; intro ab; unfold ProbDist.map; dsimp only
      rw [Finset.sum_eq_single ab]
      · simp
      · intro x _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hmap]
  rw [hB0, hBn, hAB0, hABn]
  unfold mutualInfo; ring

/-- Backward chain rule for mutual information:
    `I(A; C^n) = ∑_{i=0}^{n-1} I(A; C_i | C_{>i})`. -/
private lemma wt_mi_chain_backward {A C : Type*} [Fintype A] [Fintype C] {n : ℕ}
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
      exact wt_shannonEntropy_map_eq_of_equiv P _ _ eAC1 (fun _ => rfl)
    have h2 : shannonEntropy ((P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))).map
        (fun t => (t.2.1, t.2.2))) = hC i.1 := by
      simp only [hC, hi, ↓reduceDIte]; rw [map_comp_eq]
      refine wt_shannonEntropy_map_eq_of_equiv P _ _ eSuff fun ac => ?_
      funext j; dsimp [eSuff, suffixVec, suff]; split_ifs with h
      · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
      · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
    have h3 : shannonEntropy (P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))) = hAC i.1 := by
      simp only [hAC, hi, ↓reduceDIte]
      refine wt_shannonEntropy_map_eq_of_equiv P _ _ eAC0 fun ac => ?_
      apply Prod.ext
      · rfl
      · funext j; dsimp [eAC0, eSuff, suffixVec, suff]; split_ifs with h
        · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
        · exact congrArg ac.2 (Fin.ext (by dsimp only; omega))
    have h4 : shannonEntropy ((P.map (fun ac => (ac.1, ac.2 i, suffixVec i ac.2))).map
        (fun t => t.2.2)) = hC (i.1 + 1) := by
      simp only [hC, hi1, ↓reduceDIte]; rw [map_comp_eq]
      exact wt_shannonEntropy_map_eq_of_equiv P _ _ eLen (fun _ => rfl)
    unfold condMutualInfo; dsimp only
    rw [h1, h2, h3, h4]; ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, wt_sum_fin_telescope, wt_sum_fin_telescope]
  have hCn : hC n = 0 := by
    simp only [hC, le_refl, ↓reduceDIte]
    have : Unique (Fin (n - n) → C) :=
      ⟨⟨fun j => absurd j.2 (by omega)⟩, fun f => funext fun j => absurd j.2 (by omega)⟩
    exact wt_shannonEntropy_eq_zero_of_unique _
  have hC0 : hC 0 = shannonEntropy P.snd := by
    simp only [hC, Nat.zero_le, ↓reduceDIte]; rw [← wt_probDist_map_snd]
    let e0 : (Fin (n - 0) → C) ≃ (Fin n → C) :=
      { toFun := fun f j => f ⟨j.1, by omega⟩
        invFun := fun f j => f ⟨j.1, by omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine wt_shannonEntropy_map_eq_of_equiv P _ _ e0 fun ac => ?_
    funext j; dsimp [e0, suff]; exact congrArg ac.2 (Fin.ext (by simp))
  have hACn : hAC n = shannonEntropy P.fst := by
    simp only [hAC, le_refl, ↓reduceDIte]; rw [← wt_probDist_map_fst]
    let en : (A × (Fin (n - n) → C)) ≃ A :=
      { toFun := Prod.fst
        invFun := fun a => (a, fun j => absurd j.2 (by omega))
        left_inv := fun ⟨_, _⟩ => Prod.ext rfl (funext fun j => absurd j.2 (by omega))
        right_inv := fun _ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ en (fun _ => rfl)
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

/-- Conditional Csiszár sum identity given an auxiliary variable `M`:
    `∑_i I(Y_i; Z_{>i} | M, Y^{<i}) = ∑_i I(Y^{<i}; Z_i | M, Z_{>i})`. -/
private lemma wt_csiszar_sum_identity_cond {μ α β : Type*} [Fintype μ] [Fintype α] [Fintype β]
    {n : ℕ} (P : ProbDist (μ × (Fin n → α) × (Fin n → β))) :
    ∑ i : Fin n, condMutualInfo (P.map (fun t => (t.2.1 i, suffixVec i t.2.2, (t.1, prefixVec i t.2.1)))) =
      ∑ i : Fin n, condMutualInfo (P.map (fun t => (prefixVec i t.2.1, t.2.2 i, (t.1, suffixVec i t.2.2)))) := by
  let Q : ProbDist (((Fin n → α) × (Fin n → β)) × μ) := P.map (fun t => ((t.2.1, t.2.2), t.1))
  have hL : ∀ i : Fin n,
      condMutualInfo (P.map (fun t => (t.2.1 i, suffixVec i t.2.2, (t.1, prefixVec i t.2.1)))) =
        ∑ m : μ, if hm : 0 < Q.snd.pmf m then
          Q.snd.pmf m * condMutualInfo ((wtCondSlice Q m hm).map (fun yz => (yz.1 i, suffixVec i yz.2, prefixVec i yz.1)))
        else 0 := by
    intro i
    let Pi : ProbDist (α × (Fin (n - 1 - i.1) → β) × μ × (Fin i.1 → α)) :=
      P.map (fun t => (t.2.1 i, suffixVec i t.2.2, t.1, prefixVec i t.2.1))
    have hmap : P.map (fun t => (t.2.1 i, suffixVec i t.2.2, (t.1, prefixVec i t.2.1))) =
        Pi.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2))) := by
      dsimp only [Pi]; rw [map_comp_eq]; rfl
    rw [hmap, wt_condMutualInfo_pair_eq_weighted_sum Pi]
    set Qi := Pi.map (fun t => ((t.1, t.2.1, t.2.2.2), t.2.2.1))
    have hQi_eq : Qi = Q.map (fun p => ((p.1.1 i, suffixVec i p.1.2, prefixVec i p.1.1), p.2)) := by
      dsimp only [Qi, Pi, Q]; rw [map_comp_eq, map_comp_eq]; rfl
    have hsnd : Qi.snd = Q.snd := by
      rw [hQi_eq, ← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : 0 < Q.snd.pmf m
    · have hm' : 0 < Qi.snd.pmf m := hsnd ▸ hm
      simp only [hm, hm', ↓reduceDIte]
      have hslice : wtCondSlice Qi m hm' =
          (wtCondSlice Q m hm).map (fun yz => (yz.1 i, suffixVec i yz.2, prefixVec i yz.1)) :=
        (wt_condSlice_map (fun yz => (yz.1 i, suffixVec i yz.2, prefixVec i yz.1)) hQi_eq m hm hm').symm
      rw [hslice, hsnd]
    · have hm' : ¬ (0 < Qi.snd.pmf m) := hsnd ▸ hm
      simp [hm, hm']
  have hR : ∀ i : Fin n,
      condMutualInfo (P.map (fun t => (prefixVec i t.2.1, t.2.2 i, (t.1, suffixVec i t.2.2)))) =
        ∑ m : μ, if hm : 0 < Q.snd.pmf m then
          Q.snd.pmf m * condMutualInfo ((wtCondSlice Q m hm).map (fun yz => (prefixVec i yz.1, yz.2 i, suffixVec i yz.2)))
        else 0 := by
    intro i
    let Pi : ProbDist ((Fin i.1 → α) × β × μ × (Fin (n - 1 - i.1) → β)) :=
      P.map (fun t => (prefixVec i t.2.1, t.2.2 i, t.1, suffixVec i t.2.2))
    have hmap : P.map (fun t => (prefixVec i t.2.1, t.2.2 i, (t.1, suffixVec i t.2.2))) =
        Pi.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2))) := by
      dsimp only [Pi]; rw [map_comp_eq]; rfl
    rw [hmap, wt_condMutualInfo_pair_eq_weighted_sum Pi]
    set Qi := Pi.map (fun t => ((t.1, t.2.1, t.2.2.2), t.2.2.1))
    have hQi_eq : Qi = Q.map (fun p => ((prefixVec i p.1.1, p.1.2 i, suffixVec i p.1.2), p.2)) := by
      dsimp only [Qi, Pi, Q]; rw [map_comp_eq, map_comp_eq]; rfl
    have hsnd : Qi.snd = Q.snd := by
      rw [hQi_eq, ← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : 0 < Q.snd.pmf m
    · have hm' : 0 < Qi.snd.pmf m := hsnd ▸ hm
      simp only [hm, hm', ↓reduceDIte]
      have hslice : wtCondSlice Qi m hm' =
          (wtCondSlice Q m hm).map (fun yz => (prefixVec i yz.1, yz.2 i, suffixVec i yz.2)) :=
        (wt_condSlice_map (fun yz => (prefixVec i yz.1, yz.2 i, suffixVec i yz.2)) hQi_eq m hm hm').symm
      rw [hslice, hsnd]
    · have hm' : ¬ (0 < Qi.snd.pmf m) := hsnd ▸ hm
      simp [hm, hm']
  simp_rw [hL, hR]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : 0 < Q.snd.pmf m
  · simp only [hm, ↓reduceDIte, ← Finset.mul_sum]
    rw [csiszar_sum_identity (wtCondSlice Q m hm)]
  · simp [hm]

/-- Chain-rule swap identity for conditional mutual information:
    `I(A; B | C) - I(A; B | C, D) = I(B; D | C) - I(B; D | A, C)`. -/
private lemma wt_cmi_swap_identity {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : ProbDist (A × B × C × D)) :
    condMutualInfo (P.map (fun t => (t.1, t.2.1, t.2.2.1))) -
      condMutualInfo (P.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
    condMutualInfo (P.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) -
      condMutualInfo (P.map (fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) := by
  unfold condMutualInfo
  simp only [map_comp_eq]
  -- Match every entropy pair by coordinate permutations
  have h1 : shannonEntropy (P.map ((fun t : A × B × C => (t.1, t.2.2)) ∘ fun t => (t.1, t.2.1, t.2.2.1))) =
      shannonEntropy (P.map ((fun t : B × D × A × C => t.2.2) ∘ fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) := rfl
  have h2 : shannonEntropy (P.map ((fun t : A × B × C => (t.2.1, t.2.2)) ∘ fun t => (t.1, t.2.1, t.2.2.1))) =
      shannonEntropy (P.map ((fun t : B × D × C => (t.1, t.2.2)) ∘ fun t => (t.2.1, t.2.2.2, t.2.2.1))) := rfl
  have h3 : shannonEntropy (P.map (fun t : A × B × C × D => (t.1, t.2.1, t.2.2.1))) =
      shannonEntropy (P.map ((fun t : B × D × A × C => (t.1, t.2.2)) ∘ fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) := by
    let e : (A × B × C) ≃ (B × (A × C)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, t.1, t.2.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h4 : shannonEntropy (P.map ((fun t : A × B × C => t.2.2) ∘ fun t => (t.1, t.2.1, t.2.2.1))) =
      shannonEntropy (P.map ((fun t : B × D × C => t.2.2) ∘ fun t => (t.2.1, t.2.2.2, t.2.2.1))) := rfl
  have h5 : shannonEntropy (P.map ((fun t : A × B × C × D => (t.1, t.2.2)) ∘ fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      shannonEntropy (P.map ((fun t : B × D × A × C => (t.2.1, t.2.2)) ∘ fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) := by
    let e : (A × (C × D)) ≃ (D × (A × C)) :=
      { toFun := fun t => (t.2.2, (t.1, t.2.1))
        invFun := fun t => (t.2.1, (t.2.2, t.1))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h6 : shannonEntropy (P.map ((fun t : A × B × C × D => (t.2.1, t.2.2)) ∘ fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      shannonEntropy (P.map (fun t : A × B × C × D => (t.2.1, t.2.2.2, t.2.2.1))) := by
    let e : (B × (C × D)) ≃ (B × D × C) :=
      { toFun := fun t => (t.1, t.2.2, t.2.1)
        invFun := fun t => (t.1, (t.2.2, t.2.1))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h7 : shannonEntropy (P.map (fun t : A × B × C × D => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      shannonEntropy (P.map (fun t : A × B × C × D => (t.2.1, t.2.2.2, (t.1, t.2.2.1)))) := by
    let e : (A × B × (C × D)) ≃ (B × D × (A × C)) :=
      { toFun := fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1))
        invFun := fun t => (t.2.2.1, t.1, (t.2.2.2, t.2.1))
        left_inv := fun ⟨_, _, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _, _⟩ => rfl }
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ e (fun _ => rfl)
  have h8 : shannonEntropy (P.map ((fun t : A × B × C × D => t.2.2) ∘ fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) =
      shannonEntropy (P.map ((fun t : B × D × C => (t.2.1, t.2.2)) ∘ fun t => (t.2.1, t.2.2.2, t.2.2.1))) := by
    exact wt_shannonEntropy_map_eq_of_equiv P _ _ (Equiv.prodComm C D) (fun _ => rfl)
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring

/-- **Csiszár–Körner Difference Telescoping Identity**:
    for any joint distribution `P` on `M × Y^n × Z^n`,
    `I(M; Y^n) - I(M; Z^n) = ∑_{i=0}^{n-1} [I(M; Y_i | Y^{<i}, Z_{>i}) - I(M; Z_i | Y^{<i}, Z_{>i})]`. -/
private lemma wt_mi_diff_eq_sum_cond {μ α β : Type*} [Fintype μ] [Fintype α] [Fintype β] {n : ℕ}
    (P : ProbDist (μ × (Fin n → α) × (Fin n → β))) :
    mutualInfo (P.map (fun t => (t.1, t.2.1))) - mutualInfo (P.map (fun t => (t.1, t.2.2))) =
      ∑ i : Fin n,
        (condMutualInfo (P.map (fun t => (t.1, t.2.1 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) -
         condMutualInfo (P.map (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2))))) := by
  rw [wt_mi_chain_forward (P.map (fun t => (t.1, t.2.1))),
    wt_mi_chain_backward (P.map (fun t => (t.1, t.2.2)))]
  simp only [map_comp_eq]
  have hY : ∀ i : Fin n,
      condMutualInfo (P.map ((fun ab : μ × (Fin n → α) => (ab.1, ab.2 i, prefixVec i ab.2)) ∘
        fun t => (t.1, t.2.1))) -
      condMutualInfo (P.map (fun t => (t.1, t.2.1 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) =
      condMutualInfo ((P.map (fun t => (t.2.1, t.2.2))).map (fun yz => (yz.1 i, suffixVec i yz.2, prefixVec i yz.1))) -
      condMutualInfo (P.map (fun t => (t.2.1 i, suffixVec i t.2.2, (t.1, prefixVec i t.2.1)))) := by
    intro i
    have h := wt_cmi_swap_identity (P.map (fun t => (t.1, t.2.1 i, prefixVec i t.2.1, suffixVec i t.2.2)))
    simpa only [map_comp_eq, Function.comp_def] using h
  have hZ : ∀ i : Fin n,
      condMutualInfo (P.map ((fun ac : μ × (Fin n → β) => (ac.1, ac.2 i, suffixVec i ac.2)) ∘
        fun t => (t.1, t.2.2))) -
      condMutualInfo (P.map (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) =
      condMutualInfo ((P.map (fun t => (t.2.1, t.2.2))).map (fun yz => (prefixVec i yz.1, yz.2 i, suffixVec i yz.2))) -
      condMutualInfo (P.map (fun t => (prefixVec i t.2.1, t.2.2 i, (t.1, suffixVec i t.2.2)))) := by
    intro i
    have h := wt_cmi_swap_identity (P.map (fun t => (t.1, t.2.2 i, suffixVec i t.2.2, prefixVec i t.2.1)))
    simp only [map_comp_eq, Function.comp_def] at h
    -- Reorder `(Z_{>i}, Y^{<i})` to `(Y^{<i}, Z_{>i})` and swap `(Z_i, Y^{<i})` to `(Y^{<i}, Z_i)`
    have hswap1 : condMutualInfo (P.map (fun t => (t.1, t.2.2 i, (suffixVec i t.2.2, prefixVec i t.2.1)))) =
        condMutualInfo (P.map (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) := by
      let e := Equiv.prodComm (Fin (n - 1 - i.1) → β) (Fin i.1 → α)
      unfold condMutualInfo; dsimp only; simp only [map_comp_eq, Function.comp_def]
      have ha := wt_shannonEntropy_map_eq_of_equiv P
        (fun t => (t.1, (suffixVec i t.2.2, prefixVec i t.2.1)))
        (fun t => (t.1, (prefixVec i t.2.1, suffixVec i t.2.2)))
        (Equiv.prodCongr (Equiv.refl μ) e) (fun _ => rfl)
      have hb := wt_shannonEntropy_map_eq_of_equiv P
        (fun t => (t.2.2 i, (suffixVec i t.2.2, prefixVec i t.2.1)))
        (fun t => (t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))
        (Equiv.prodCongr (Equiv.refl β) e) (fun _ => rfl)
      have hc := wt_shannonEntropy_map_eq_of_equiv P
        (fun t => (t.1, t.2.2 i, (suffixVec i t.2.2, prefixVec i t.2.1)))
        (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))
        (Equiv.prodCongr (Equiv.refl μ) (Equiv.prodCongr (Equiv.refl β) e)) (fun _ => rfl)
      have hd := wt_shannonEntropy_map_eq_of_equiv P
        (fun t => (suffixVec i t.2.2, prefixVec i t.2.1))
        (fun t => (prefixVec i t.2.1, suffixVec i t.2.2))
        e (fun _ => rfl)
      rw [ha, hb, hc, hd]
    have hswap2 : condMutualInfo (P.map (fun t => (t.2.2 i, prefixVec i t.2.1, suffixVec i t.2.2))) =
        condMutualInfo ((P.map (fun t => (t.2.1, t.2.2))).map (fun yz => (prefixVec i yz.1, yz.2 i, suffixVec i yz.2))) := by
      unfold condMutualInfo; dsimp only; simp only [map_comp_eq, Function.comp_def]
      let e : (β × (Fin i.1 → α) × (Fin (n - 1 - i.1) → β)) ≃
          ((Fin i.1 → α) × β × (Fin (n - 1 - i.1) → β)) :=
        { toFun := fun t => (t.2.1, t.1, t.2.2)
          invFun := fun t => (t.2.1, t.1, t.2.2)
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
      have hc := wt_shannonEntropy_map_eq_of_equiv P
        (fun t => (t.2.2 i, prefixVec i t.2.1, suffixVec i t.2.2))
        (fun t => (prefixVec i t.2.1, t.2.2 i, suffixVec i t.2.2)) e (fun _ => rfl)
      rw [hc]; ring
    have hswap3 : condMutualInfo (P.map (fun t => (t.2.2 i, prefixVec i t.2.1, (t.1, suffixVec i t.2.2)))) =
        condMutualInfo (P.map (fun t => (prefixVec i t.2.1, t.2.2 i, (t.1, suffixVec i t.2.2)))) := by
      unfold condMutualInfo; dsimp only; simp only [map_comp_eq, Function.comp_def]
      let e : (β × (Fin i.1 → α) × (μ × (Fin (n - 1 - i.1) → β))) ≃
          ((Fin i.1 → α) × β × (μ × (Fin (n - 1 - i.1) → β))) :=
        { toFun := fun t => (t.2.1, t.1, t.2.2)
          invFun := fun t => (t.2.1, t.1, t.2.2)
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
      have hc := wt_shannonEntropy_map_eq_of_equiv P
        (fun t => (t.2.2 i, prefixVec i t.2.1, (t.1, suffixVec i t.2.2)))
        (fun t => (prefixVec i t.2.1, t.2.2 i, (t.1, suffixVec i t.2.2))) e (fun _ => rfl)
      rw [hc]; ring
    rw [hswap1, hswap2, hswap3] at h
    simpa only [Function.comp_def] using h
  have hcs1 := csiszar_sum_identity (P.map (fun t => (t.2.1, t.2.2)))
  have hcs2 := wt_csiszar_sum_identity_cond P
  have hsumY := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hY i
  have hsumZ := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hZ i
  simp only [Finset.sum_sub_distrib] at hsumY hsumZ ⊢
  linarith

/-- Splitting a length-`n` vector at coordinate `i` into its `i`-th entry and remaining entries. -/
private def wtSplitAt {α : Type*} {n : ℕ} (i : Fin n) :
    (Fin n → α) ≃ α × ({j : Fin n // j ≠ i} → α) where
  toFun := fun x => (x i, fun j => x j.1)
  invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
  left_inv := fun x => by
    funext j; dsimp only; split_ifs with h
    · subst h; rfl
    · rfl
  right_inv := fun ⟨a, r⟩ => by
    apply Prod.ext
    · simp
    · funext ⟨j, hj⟩; simp [hj]

/-- Coordinate-wise Markov factorization for a memoryless wiretap channel:
    for `Q = wiretapCodeJoint W hM code` and coordinate `i : Fin n`, given `U_i = (Y^{<i}, Z_{>i})`,
    the joint law of `(M, X_i, Y_i, Z_i)` factors as `P(M, X_i | U_i) * W(Y_i, Z_i | X_i)`. -/
private lemma wt_code_coord_markov (W : WiretapChannel X Y Z) {n M : ℕ} (hM : 0 < M)
    (code : WiretapCode W n M) (i : Fin n) :
    let Q := wiretapCodeJoint W hM code
    let U := (Fin i.1 → Y) × (Fin (n - 1 - i.1) → Z)
    let J4 : ProbDist ((Fin M × X × Y × Z) × U) :=
      Q.map (fun t => ((t.1, t.2.1 i, t.2.2.1 i, t.2.2.2 i), (prefixVec i t.2.2.1, suffixVec i t.2.2.2)))
    let J2 : ProbDist ((Fin M × X) × U) :=
      Q.map (fun t => ((t.1, t.2.1 i), (prefixVec i t.2.2.1, suffixVec i t.2.2.2)))
    ∀ (m : Fin M) (xi : X) (yi : Y) (zi : Z) (u : U),
      J4.pmf ((m, xi, yi, zi), u) = J2.pmf ((m, xi), u) * W.trans xi (yi, zi) := by
  classical
  dsimp only
  intro m xi yi zi ⟨u1, u2⟩
  let Q := wiretapCodeJoint W hM code
  let eY := wtSplitAt (α := Y) i
  let eZ := wtSplitAt (α := Z) i
  -- Sum over `(y_rest, z_rest)` weighted by `∏_{j ≠ i} W(y_j, z_j | x_j)`
  let restWeight : (Fin n → X) → ({j : Fin n // j ≠ i} → Y) → ({j : Fin n // j ≠ i} → Z) → ℝ :=
    fun x yr zr =>
      if x i = xi ∧
         (fun j : Fin i.1 => yr ⟨⟨j.1, lt_trans j.2 i.2⟩, ne_of_lt j.2⟩) = u1 ∧
         (fun j : Fin (n - 1 - i.1) => zr ⟨⟨i.1 + 1 + j.1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega⟩) = u2
      then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
        ∏ j : {j : Fin n // j ≠ i}, W.trans (x j.1) (yr j, zr j)
      else 0
  have hprod_split : ∀ (x : Fin n → X) (y0 : Y) (yr : {j : Fin n // j ≠ i} → Y)
      (z0 : Z) (zr : {j : Fin n // j ≠ i} → Z),
      (W.power n).trans x (fun j => (eY.symm (y0, yr) j, eZ.symm (z0, zr) j)) =
        W.trans (x i) (y0, z0) * ∏ j : {j : Fin n // j ≠ i}, W.trans (x j.1) (yr j, zr j) := by
    intro x y0 yr z0 zr
    unfold DMC.power; dsimp only
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [eY, eZ, wtSplitAt]
    · rw [Finset.prod_subtype (Finset.univ.erase i) (p := fun j : Fin n => j ≠ i)
        (fun j => by simp)]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [eY, eZ, wtSplitAt, j.2]
  have hpref_eq : ∀ y0 yr, prefixVec i (eY.symm (y0, yr)) =
      fun j : Fin i.1 => yr ⟨⟨j.1, lt_trans j.2 i.2⟩, ne_of_lt j.2⟩ := by
    intro y0 yr; funext j; dsimp [prefixVec, eY, wtSplitAt]
    have hne : (⟨j.1, lt_trans j.2 i.2⟩ : Fin n) ≠ i := by
      intro h; have := congrArg Fin.val h; dsimp at this; exact absurd this (ne_of_lt j.2)
    simp [hne]
  have hsuff_eq : ∀ z0 zr, suffixVec i (eZ.symm (z0, zr)) =
      fun j : Fin (n - 1 - i.1) => zr ⟨⟨i.1 + 1 + j.1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega⟩ := by
    intro z0 zr; funext j; dsimp [suffixVec, eZ, wtSplitAt]
    have hne : (⟨i.1 + 1 + j.1, by omega⟩ : Fin n) ≠ i := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hne]
  -- Evaluate `J4.pmf ((m, xi, yi, zi), (u1, u2))`
  have hJ4 : (Q.map (fun t => ((t.1, t.2.1 i, t.2.2.1 i, t.2.2.2 i),
        (prefixVec i t.2.2.1, suffixVec i t.2.2.2)))).pmf ((m, xi, yi, zi), (u1, u2)) =
      (∑ x : Fin n → X, ∑ yr : {j : Fin n // j ≠ i} → Y, ∑ zr : {j : Fin n // j ≠ i} → Z,
        restWeight x yr zr) * W.trans xi (yi, zi) := by
    unfold ProbDist.map Q wiretapCodeJoint; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_equiv eY _ (fun p => ∑ z : Fin n → Z,
          if ((m, x i, p.1, z i), (prefixVec i (eY.symm p), suffixVec i z)) =
              ((m, xi, yi, zi), (u1, u2))
          then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
            (W.power n).trans x (fun j => (eY.symm p j, z j)) else 0)
        (fun y => by rw [Equiv.symm_apply_apply]; rfl)]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single yi]
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun yr _ => ?_
        rw [Fintype.sum_equiv eZ _ (fun q =>
            if ((m, x i, yi, q.1), (prefixVec i (eY.symm (yi, yr)), suffixVec i (eZ.symm q))) =
                ((m, xi, yi, zi), (u1, u2))
            then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
              (W.power n).trans x (fun j => (eY.symm (yi, yr) j, eZ.symm q j)) else 0)
          (fun z => by rw [Equiv.symm_apply_apply]; rfl)]
        rw [Fintype.sum_prod_type, Finset.sum_eq_single zi]
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun zr _ => ?_
          rw [hpref_eq, hsuff_eq, hprod_split]
          dsimp only [restWeight]
          by_cases hcond : x i = xi ∧
              (fun j : Fin i.1 => yr ⟨⟨j.1, lt_trans j.2 i.2⟩, ne_of_lt j.2⟩) = u1 ∧
              (fun j : Fin (n - 1 - i.1) => zr ⟨⟨i.1 + 1 + j.1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega⟩) = u2
          · rcases hcond with ⟨hx, hu1, hu2⟩
            simp only [hx, hu1, hu2, and_self, ↓reduceIte]; ring
          · have hneq : ¬ (((m, x i, yi, zi),
                ((fun j : Fin i.1 => yr ⟨⟨j.1, lt_trans j.2 i.2⟩, ne_of_lt j.2⟩),
                 (fun j : Fin (n - 1 - i.1) => zr ⟨⟨i.1 + 1 + j.1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega⟩))) =
                ((m, xi, yi, zi), (u1, u2))) := by
              intro h; apply hcond
              simp only [Prod.mk.injEq, true_and] at h
              exact ⟨h.1.1, h.2.1, h.2.2⟩
            simp [hcond, hneq]
        · intro z0 _ hne; exact Finset.sum_eq_zero fun zr _ => by simp [hne]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro y0 _ hne; exact Finset.sum_eq_zero fun yr _ => Finset.sum_eq_zero fun z _ => by simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · intro m' _ hne
      simp_rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
        Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  -- Evaluate `J2.pmf ((m, xi), (u1, u2))`
  have hJ2 : (Q.map (fun t => ((t.1, t.2.1 i), (prefixVec i t.2.2.1, suffixVec i t.2.2.2)))).pmf
        ((m, xi), (u1, u2)) =
      ∑ x : Fin n → X, ∑ yr : {j : Fin n // j ≠ i} → Y, ∑ zr : {j : Fin n // j ≠ i} → Z,
        restWeight x yr zr := by
    unfold ProbDist.map Q wiretapCodeJoint; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · simp_rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_equiv eY _ (fun p => ∑ z : Fin n → Z,
          if ((m, x i), (prefixVec i (eY.symm p), suffixVec i z)) = ((m, xi), (u1, u2))
          then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
            (W.power n).trans x (fun j => (eY.symm p j, z j)) else 0)
        (fun y => by rw [Equiv.symm_apply_apply])]
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun yr _ => ?_
      have hrewrite : ∀ y0 : Y,
          (∑ z : Fin n → Z,
            if ((m, x i), (prefixVec i (eY.symm (y0, yr)), suffixVec i z)) = ((m, xi), (u1, u2))
            then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
              (W.power n).trans x (fun j => (eY.symm (y0, yr) j, z j)) else 0) =
          ∑ zr : {j : Fin n // j ≠ i} → Z, ∑ z0 : Z,
            restWeight x yr zr * W.trans (x i) (y0, z0) := by
        intro y0
        rw [Fintype.sum_equiv eZ _ (fun q =>
            if ((m, x i), (prefixVec i (eY.symm (y0, yr)), suffixVec i (eZ.symm q))) = ((m, xi), (u1, u2))
            then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
              (W.power n).trans x (fun j => (eY.symm (y0, yr) j, eZ.symm q j)) else 0)
          (fun z => by rw [Equiv.symm_apply_apply])]
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun zr _ => Finset.sum_congr rfl fun z0 _ => ?_
        rw [hpref_eq, hsuff_eq, hprod_split]
        dsimp only [restWeight]
        by_cases hcond : x i = xi ∧
            (fun j : Fin i.1 => yr ⟨⟨j.1, lt_trans j.2 i.2⟩, ne_of_lt j.2⟩) = u1 ∧
            (fun j : Fin (n - 1 - i.1) => zr ⟨⟨i.1 + 1 + j.1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega⟩) = u2
        · rcases hcond with ⟨hx, hu1, hu2⟩
          simp only [hx, hu1, hu2, and_self, ↓reduceIte]; ring
        · have hneq : ¬ (((m, x i),
              ((fun j : Fin i.1 => yr ⟨⟨j.1, lt_trans j.2 i.2⟩, ne_of_lt j.2⟩),
               (fun j : Fin (n - 1 - i.1) => zr ⟨⟨i.1 + 1 + j.1, by omega⟩, by intro h; have := congrArg Fin.val h; dsimp at this; omega⟩))) =
              ((m, xi), (u1, u2))) := by
            intro h; apply hcond
            simp only [Prod.mk.injEq, true_and] at h
            exact ⟨h.1, h.2.1, h.2.2⟩
          simp [hcond, hneq]
      simp_rw [hrewrite]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun zr _ => ?_
      have hW : ∑ y0 : Y, ∑ z0 : Z, W.trans (x i) (y0, z0) = 1 := by
        rw [← Fintype.sum_prod_type]; exact W.sum_one (x i)
      simp_rw [← Finset.mul_sum, hW, mul_one]
    · intro m' _ hne
      simp_rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
        Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hJ4, hJ2]

/-- **Multi-Letter Csiszár–Körner Converse Bound for Any Wiretap Code**:
    for every `(n, M)` stochastic wiretap code `code` with `0 < M`,
    `I(M; Y^n) - I(M; Z^n) ≤ n · wiretapSecrecyCapacity W`. -/
theorem wiretapCode_converse_bound (W : WiretapChannel X Y Z) {n M : ℕ} (hM : 0 < M)
    (code : WiretapCode W n M) :
    mutualInfo ((wiretapCodeJoint W hM code).map (fun t => (t.1, t.2.2.1))) -
      wiretapLeakage W hM code ≤ (n : ℝ) * wiretapSecrecyCapacity W := by
  let Q := wiretapCodeJoint W hM code
  let P_MYZ : ProbDist (Fin M × (Fin n → Y) × (Fin n → Z)) :=
    Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))
  have hMY : P_MYZ.map (fun t => (t.1, t.2.1)) = Q.map (fun t => (t.1, t.2.2.1)) := by
    dsimp only [P_MYZ]; rw [map_comp_eq]; rfl
  have hMZ : P_MYZ.map (fun t => (t.1, t.2.2)) = Q.map (fun t => (t.1, t.2.2.2)) := by
    dsimp only [P_MYZ]; rw [map_comp_eq]; rfl
  unfold wiretapLeakage
  change mutualInfo (Q.map (fun t => (t.1, t.2.2.1))) -
    mutualInfo (Q.map (fun t => (t.1, t.2.2.2))) ≤ _
  rw [← hMY, ← hMZ, wt_mi_diff_eq_sum_cond P_MYZ]
  have hcoord : ∀ i : Fin n,
      condMutualInfo (P_MYZ.map (fun t => (t.1, t.2.1 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) -
      condMutualInfo (P_MYZ.map (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) ≤
      wiretapSecrecyCapacity W := by
    intro i
    let U := (Fin i.1 → Y) × (Fin (n - 1 - i.1) → Z)
    let J4 : ProbDist ((Fin M × X × Y × Z) × U) :=
      Q.map (fun t => ((t.1, t.2.1 i, t.2.2.1 i, t.2.2.2 i), (prefixVec i t.2.2.1, suffixVec i t.2.2.2)))
    let J2 : ProbDist ((Fin M × X) × U) :=
      Q.map (fun t => ((t.1, t.2.1 i), (prefixVec i t.2.2.1, suffixVec i t.2.2.2)))
    let SY : ProbDist ((Fin M × Y) × U) :=
      (P_MYZ.map (fun t => (t.1, t.2.1 i, (prefixVec i t.2.1, suffixVec i t.2.2)))).map
        (fun t => ((t.1, t.2.1), t.2.2))
    let SZ : ProbDist ((Fin M × Z) × U) :=
      (P_MYZ.map (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))).map
        (fun t => ((t.1, t.2.1), t.2.2))
    have hSY_eq : SY = J4.map (fun p => ((p.1.1, p.1.2.2.1), p.2)) := by
      dsimp only [SY, P_MYZ, J4]; rw [map_comp_eq, map_comp_eq, map_comp_eq]; rfl
    have hSZ_eq : SZ = J4.map (fun p => ((p.1.1, p.1.2.2.2), p.2)) := by
      dsimp only [SZ, P_MYZ, J4]; rw [map_comp_eq, map_comp_eq, map_comp_eq]; rfl
    have hJ2_eq : J2 = J4.map (fun p => ((p.1.1, p.1.2.1), p.2)) := by
      dsimp only [J2, J4]; rw [map_comp_eq]; rfl
    have hSY_snd : SY.snd = J4.snd := by
      rw [hSY_eq, ← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
    have hSZ_snd : SZ.snd = J4.snd := by
      rw [hSZ_eq, ← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
    have hJ2_snd : J2.snd = J4.snd := by
      rw [hJ2_eq, ← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
    rw [wt_condMutualInfo_eq_weighted_sum, wt_condMutualInfo_eq_weighted_sum]
    rw [← Finset.sum_sub_distrib]
    calc ∑ u : U,
          ((if hc : 0 < SY.snd.pmf u then SY.snd.pmf u * mutualInfo (wtCondSlice SY u hc) else 0) -
           (if hc : 0 < SZ.snd.pmf u then SZ.snd.pmf u * mutualInfo (wtCondSlice SZ u hc) else 0))
      _ ≤ ∑ u : U, J4.snd.pmf u * wiretapSecrecyCapacity W := by
          refine Finset.sum_le_sum fun u _ => ?_
          by_cases hu : 0 < J4.snd.pmf u
          · have huY : 0 < SY.snd.pmf u := hSY_snd ▸ hu
            have huZ : 0 < SZ.snd.pmf u := hSZ_snd ▸ hu
            have hu2 : 0 < J2.snd.pmf u := hJ2_snd ▸ hu
            simp only [huY, huZ, ↓reduceDIte]
            have hslice4 : wtCondSlice J4 u hu = wiretapAuxJoint W (wtCondSlice J2 u hu2) := by
              apply wt_probDist_ext; intro ⟨m, xi, yi, zi⟩
              unfold wtCondSlice wiretapAuxJoint; dsimp only
              rw [hJ2_snd, wt_code_coord_markov W hM code i m xi yi zi u]
              ring
            have hsliceY : wtCondSlice SY u huY =
                (wiretapAuxJoint W (wtCondSlice J2 u hu2)).map (fun t => (t.1, t.2.2.1)) := by
              rw [← hslice4]
              exact (wt_condSlice_map (fun t => (t.1, t.2.2.1)) hSY_eq u hu huY).symm
            have hsliceZ : wtCondSlice SZ u huZ =
                (wiretapAuxJoint W (wtCondSlice J2 u hu2)).map (fun t => (t.1, t.2.2.2)) := by
              rw [← hslice4]
              exact (wt_condSlice_map (fun t => (t.1, t.2.2.2)) hSZ_eq u hu huZ).symm
            rw [hsliceY, hsliceZ, hSY_snd, hSZ_snd, ← mul_sub]
            exact mul_le_mul_of_nonneg_left (wiretapSecrecyCapacity_ge_aux W (wtCondSlice J2 u hu2)) (le_of_lt hu)
          · have huY : ¬ (0 < SY.snd.pmf u) := hSY_snd ▸ hu
            have huZ : ¬ (0 < SZ.snd.pmf u) := hSZ_snd ▸ hu
            simp only [huY, huZ, ↓reduceDIte, sub_self]
            exact mul_nonneg (J4.snd.nonneg u) (wiretapSecrecyCapacity_nonneg W)
      _ = wiretapSecrecyCapacity W := by
          rw [← Finset.sum_mul, J4.snd.sum_one, one_mul]
  calc ∑ i : Fin n,
        (condMutualInfo (P_MYZ.map (fun t => (t.1, t.2.1 i, (prefixVec i t.2.1, suffixVec i t.2.2)))) -
         condMutualInfo (P_MYZ.map (fun t => (t.1, t.2.2 i, (prefixVec i t.2.1, suffixVec i t.2.2)))))
    _ ≤ ∑ _i : Fin n, wiretapSecrecyCapacity W := Finset.sum_le_sum fun i _ => hcoord i
    _ = (n : ℝ) * wiretapSecrecyCapacity W := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Finite-Blocklength Rate-Error-Leakage Converse** for any `(n, M)` wiretap code
    with `n > 0` and `M ≥ 2`:
    `(1 - P_e) · (log₂ M / n) ≤ C_s(W) + I(M; Z^n) / n + 1 / n`. -/
theorem wiretapCode_rate_converse (W : WiretapChannel X Y Z) {n M : ℕ} (hn : 0 < n) (hM : 2 ≤ M)
    (code : WiretapCode W n M) :
    let hMpos : 0 < M := by omega
    (1 - wiretapAvgError W hMpos code) * (log2 (M : ℝ) / (n : ℝ)) ≤
      wiretapSecrecyCapacity W + wiretapLeakage W hMpos code / (n : ℝ) + 1 / (n : ℝ) := by
  have hMpos : 0 < M := by omega
  have : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
  dsimp only
  let P_MY := (wiretapCodeJoint W hMpos code).map (fun t => (t.1, t.2.2.1))
  have hfst : P_MY.fst = ProbDist.uniform (α := Fin M) := by
    classical
    apply wt_probDist_ext; intro m
    rw [← wt_probDist_map_fst]
    dsimp only [P_MY]; rw [map_comp_eq]
    unfold ProbDist.map ProbDist.uniform wiretapCodeJoint; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
    · simp only [Fintype.card_fin]
      rw [Fintype.sum_prod_type]
      have hx : ∀ x : Fin n → X,
          ∑ yz : (Fin n → Y) × (Fin n → Z),
            ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
              (W.power n).trans x (fun i => (yz.1 i, yz.2 i)) =
            ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x := by
        intro x
        rw [← Finset.mul_sum]
        have hsum : ∑ yz : (Fin n → Y) × (Fin n → Z),
            (W.power n).trans x (zipEquiv Y Z n yz) = 1 := by
          rw [Fintype.sum_equiv (zipEquiv Y Z n) _ (fun w => (W.power n).trans x w) (fun _ => rfl)]
          exact (W.power n).sum_one x
        change (((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x) *
            (∑ yz : (Fin n → Y) × (Fin n → Z), (W.power n).trans x (zipEquiv Y Z n yz)) = _
        rw [hsum, mul_one]
      have hxs : ∑ x : Fin n → X, ∑ yz : (Fin n → Y) × (Fin n → Z),
          (if m = m then ((1 : ℝ) / (M : ℝ)) * (code.enc m).pmf x *
            (W.power n).trans x (fun i => (yz.1 i, yz.2 i)) else 0) = (1 : ℝ) / (M : ℝ) := by
        simp only [↓reduceIte]
        simp_rw [hx]
        rw [← Finset.mul_sum, (code.enc m).sum_one, mul_one]
      simpa using hxs
    · intro m' _ hne; exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hHM : shannonEntropy P_MY.fst = log2 (M : ℝ) := by
    rw [hfst, (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin M))).mpr rfl,
      Fintype.card_fin]
  have hfano := fano_inequality_card P_MY code.dec
  rw [Fintype.card_fin] at hfano
  have hpe0 : 0 ≤ wiretapAvgError W hMpos code := estErrorProb_nonneg P_MY code.dec
  have hpe1 : wiretapAvgError W hMpos code ≤ 1 := estErrorProb_le_one P_MY code.dec
  have hbin : binaryEntropy (wiretapAvgError W hMpos code) ≤ 1 := wt_binaryEntropy_le_one hpe0 hpe1
  have hconv := wiretapCode_converse_bound W hMpos code
  have hid : log2 (M : ℝ) = condEntropy P_MY + mutualInfo P_MY := by
    unfold condEntropy mutualInfo; linarith [hHM]
  have hmain : (1 - wiretapAvgError W hMpos code) * log2 (M : ℝ) ≤
      (n : ℝ) * wiretapSecrecyCapacity W + wiretapLeakage W hMpos code + 1 := by
    change condEntropy P_MY ≤ binaryEntropy (wiretapAvgError W hMpos code) +
      wiretapAvgError W hMpos code * log2 (M : ℝ) at hfano
    change mutualInfo P_MY - wiretapLeakage W hMpos code ≤ (n : ℝ) * wiretapSecrecyCapacity W at hconv
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc (1 - wiretapAvgError W hMpos code) * (log2 (M : ℝ) / (n : ℝ))
    _ = ((1 - wiretapAvgError W hMpos code) * log2 (M : ℝ)) / (n : ℝ) := by ring
    _ ≤ ((n : ℝ) * wiretapSecrecyCapacity W + wiretapLeakage W hMpos code + 1) / (n : ℝ) :=
        div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
    _ = wiretapSecrecyCapacity W + wiretapLeakage W hMpos code / (n : ℝ) + 1 / (n : ℝ) := by
        rw [add_div, add_div, mul_div_cancel_left₀ _ (ne_of_gt hn_pos)]

/-- **Weak-Secrecy Converse (Csiszár–Körner 1978; El Gamal & Kim Thm. 22.1)**:
    every operationally weak-secrecy achievable rate satisfies `R ≤ wiretapSecrecyCapacity W`. -/
theorem wiretap_weak_secrecy_converse (W : WiretapChannel X Y Z) (R : ℝ)
    (hR : IsWiretapWeakAchievable W R) :
    R ≤ wiretapSecrecyCapacity W := by
  by_contra hlt
  push Not at hlt
  have hCs0 : 0 ≤ wiretapSecrecyCapacity W := wiretapSecrecyCapacity_nonneg W
  let Δ : ℝ := R - wiretapSecrecyCapacity W
  have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
  have hRpos : 0 < R := by linarith
  let ε : ℝ := min (1 / 2) (min (Δ / (8 * R)) (Δ / 4))
  have hε_pos : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε_half : ε ≤ 1 / 2 := min_le_left _ _
  have hε_R : ε * R ≤ Δ / 8 := by
    have h1 : ε ≤ Δ / (8 * R) := le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hRpos)
    have h3 : Δ / (8 * R) * R = Δ / 8 := by field_simp [ne_of_gt hRpos]
    linarith
  have hε_Δ : ε ≤ Δ / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hR.2 ε hε_pos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (max (1 / R) (8 / Δ))
  let n : ℕ := max (max N₁ N₂) 1
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ge_N₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ 1)
  have hn_gt_max : max (1 / R) (8 / Δ) < (n : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
  have hn_gt_1R : 1 / R < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn_gt_max
  have hn_gt_8Δ : 8 / Δ < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn_gt_max
  have hnR_gt1 : 1 < (n : ℝ) * R := by
    have h := (div_lt_iff₀ hRpos).mp hn_gt_1R; linarith
  have h2n_lt : 2 / (n : ℝ) < Δ / 4 := by
    rw [div_lt_iff₀ hn_r]
    have h := (div_lt_iff₀ hΔ).mp hn_gt_8Δ; linarith
  obtain ⟨code, herr, hleak⟩ := hN₁ n hn_ge_N₁
  let M : ℕ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have h2pow_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hnR_gt1)
  have hM_ge2 : 2 ≤ M :=
    le_trans (Nat.le_floor (by exact_mod_cast h2pow_ge2)) (le_max_right 1 _)
  have hM_gt_pow : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ (M : ℝ) := by
    have hhalf : (2 : ℝ) ^ ((n : ℝ) * R - 1) = (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hsub1 : (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ (2 : ℝ) ^ ((n : ℝ) * R) - 1 := by linarith
    have hfloor : (2 : ℝ) ^ ((n : ℝ) * R) - 1 < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((2 : ℝ) ^ ((n : ℝ) * R))]
    have hleM : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) :=
      Nat.cast_le.mpr (le_max_right 1 _)
    linarith
  have hlogM_ge : (n : ℝ) * R - 1 ≤ log2 (M : ℝ) := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have hmono := wt_log2_le_log2 hpow_pos hM_gt_pow
    rwa [wt_log2_two_rpow] at hmono
  have hrate_ge : R - 1 / (n : ℝ) ≤ log2 (M : ℝ) / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hlogM_ge (le_of_lt hn_r)
    have hsimp : ((n : ℝ) * R - 1) / (n : ℝ) = R - 1 / (n : ℝ) := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hn_r)]
    linarith
  have hrate_nonneg : 0 ≤ R - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < R := (div_lt_iff₀ hn_r).mpr (by linarith)
    linarith
  have hconv := wiretapCode_rate_converse W hn_pos hM_ge2 code
  dsimp only at hconv
  have hleak_div : wiretapLeakage W (by omega) code / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hn_r]; linarith
  have hprod_le : (1 - ε) * (R - 1 / (n : ℝ)) ≤
      (1 - wiretapAvgError W (by omega) code) * (log2 (M : ℝ) / (n : ℝ)) :=
    mul_le_mul (by linarith) hrate_ge hrate_nonneg (by linarith)
  have hcomb : (1 - ε) * (R - 1 / (n : ℝ)) ≤ wiretapSecrecyCapacity W + ε + 1 / (n : ℝ) := by
    linarith
  have hεn : 0 ≤ ε * (1 / (n : ℝ)) := by positivity
  have hexpand : (1 - ε) * (R - 1 / (n : ℝ)) = R - 1 / (n : ℝ) - ε * R + ε * (1 / (n : ℝ)) := by ring
  have h2div : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
  dsimp only [Δ] at hε_R hε_Δ h2n_lt
  linarith

end WiretapConverse

/-! ### 3. Operational Wiretap Achievability & Exact Secrecy Capacity Theorem -/

section WiretapAchievability

variable {X Y Z V : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype V]

/-- Rate `0` is operationally weak-secrecy achievable over any wiretap channel with nonempty `X`. -/
theorem isWiretapWeakAchievable_zero [Nonempty X] (W : WiretapChannel X Y Z) :
    IsWiretapWeakAchievable W 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))
  have hM1 : M = 1 := by dsimp only [M]; norm_num
  have hMpos : 0 < M := by omega
  let code : WiretapCode W n M :=
    { enc := fun _ => ProbDist.uniform
      dec := fun _ => ⟨0, hMpos⟩ }
  refine ⟨code, ?_, ?_⟩
  · have herr : wiretapAvgError W hMpos code = 0 := by
      classical
      unfold wiretapAvgError estErrorProb
      refine Finset.sum_eq_zero fun my _ => ?_
      have hzero : (⟨0, hMpos⟩ : Fin M) = my.1 := by ext; dsimp only; omega
      simp [code, hzero]
    linarith
  · have hleak : wiretapLeakage W hMpos code = 0 :=
      @wt_mutualInfo_eq_zero_of_unique_left _ _ _ _
        ⟨⟨⟨0, hMpos⟩⟩, fun m => by ext; dsimp only; omega⟩ _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) (le_of_lt hε)
    linarith

/-- Conditional prefix channel `P_{X | V}` extracted from a joint distribution `Pvx : ProbDist (V × X)`. -/
private noncomputable def wtPrefixChannel [Nonempty X] (Pvx : ProbDist (V × X)) : DMC V X where
  trans := fun v x =>
    if Pvx.fst.pmf v = 0 then (ProbDist.uniform (α := X)).pmf x else Pvx.pmf (v, x) / Pvx.fst.pmf v
  nonneg := fun v x => by
    split_ifs
    · exact ProbDist.uniform.nonneg x
    · exact div_nonneg (Pvx.nonneg (v, x)) (Pvx.fst.nonneg v)
  sum_one := fun v => by
    by_cases hv : Pvx.fst.pmf v = 0
    · simp [hv, ProbDist.uniform.sum_one]
    · simp only [hv, ↓reduceIte, ← Finset.sum_div]
      exact div_self hv

private lemma wtPrefixChannel_joint [Nonempty X] (Pvx : ProbDist (V × X)) :
    (wtPrefixChannel Pvx).joint Pvx.fst = Pvx := by
  apply wt_probDist_ext; intro ⟨v, x⟩
  unfold DMC.joint wtPrefixChannel; dsimp only
  by_cases hv : Pvx.fst.pmf v = 0
  · simp only [hv, ↓reduceIte, zero_mul]
    have hle : Pvx.pmf (v, x) ≤ Pvx.fst.pmf v :=
      Finset.single_le_sum (fun x' _ => Pvx.nonneg (v, x')) (Finset.mem_univ x)
    linarith [Pvx.nonneg (v, x)]
  · simp only [hv, ↓reduceIte]
    exact mul_div_cancel₀ _ hv

private lemma wtPrefixChannel_bob_joint [Nonempty X] (W : WiretapChannel X Y Z)
    (Pvx : ProbDist (V × X)) :
    (dmcComp (wtPrefixChannel Pvx) (wiretapBobChannel W)).joint Pvx.fst =
      (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1)) := by
  apply wt_probDist_ext; intro ⟨v, y⟩
  rw [wt_auxJoint_bob_pmf]
  unfold DMC.joint dmcComp; dsimp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrArg (fun P : ProbDist (V × X) => P.pmf (v, x)) (wtPrefixChannel_joint Pvx)
  unfold DMC.joint at h; dsimp only at h
  rw [← mul_assoc, h]

private lemma wtPrefixChannel_eve_joint [Nonempty X] (W : WiretapChannel X Y Z)
    (Pvx : ProbDist (V × X)) :
    (dmcComp (wtPrefixChannel Pvx) (wiretapEveChannel W)).joint Pvx.fst =
      (wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2)) := by
  apply wt_probDist_ext; intro ⟨v, z⟩
  rw [wt_auxJoint_eve_pmf]
  unfold DMC.joint dmcComp; dsimp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrArg (fun P : ProbDist (V × X) => P.pmf (v, x)) (wtPrefixChannel_joint Pvx)
  unfold DMC.joint at h; dsimp only at h
  rw [← mul_assoc, h]

/-- i.i.d. random bin-codebook probability `∏_{m, l} P_V^n(C(m, l))`. -/
private def wtBinCodebookProb (Pv : ProbDist V) (n M L : ℕ)
    (C : Fin M → Fin L → Fin n → V) : ℝ :=
  ∏ m : Fin M, ∏ l : Fin L, (iidDist Pv n).pmf (C m l)

private lemma wtBinCodebookProb_nonneg (Pv : ProbDist V) (n M L : ℕ)
    (C : Fin M → Fin L → Fin n → V) :
    0 ≤ wtBinCodebookProb Pv n M L C :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => (iidDist Pv n).nonneg _

private lemma wtBinCodebookProb_sum_one (Pv : ProbDist V) (n M L : ℕ) :
    ∑ C : Fin M → Fin L → Fin n → V, wtBinCodebookProb Pv n M L C = 1 := by
  unfold wtBinCodebookProb
  rw [← Fintype.prod_sum (fun (_ : Fin M) (c : Fin L → Fin n → V) => ∏ l : Fin L, (iidDist Pv n).pmf (c l))]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [← Fintype.prod_sum (fun (_ : Fin L) (x : Fin n → V) => (iidDist Pv n).pmf x)]
  exact Finset.prod_eq_one fun _ _ => (iidDist Pv n).sum_one

/-- Equivalence flattening a binned codebook `Fin M → Fin L → γ` to `Fin (M * L) → γ`. -/
private def wtFlattenEquiv (γ : Type*) (M L : ℕ) :
    (Fin M → Fin L → γ) ≃ (Fin (M * L) → γ) where
  toFun := fun C k => C (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun := fun enc m l => enc (finProdFinEquiv (m, l))
  left_inv := fun C => by funext m l; simp
  right_inv := fun enc => by funext k; dsimp only; rw [Prod.mk.eta, Equiv.apply_symm_apply]

private lemma wtBinCodebookProb_eq_codebookProb (Pv : ProbDist V) (n M L : ℕ)
    (C : Fin M → Fin L → Fin n → V) :
    wtBinCodebookProb Pv n M L C = codebookProb Pv n (M * L) (wtFlattenEquiv _ M L C) := by
  unfold wtBinCodebookProb codebookProb wtFlattenEquiv
  rw [← Fintype.prod_prod_type']
  exact (Fintype.prod_equiv finProdFinEquiv.symm
    (fun k => (iidDist Pv n).pmf (C (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
    (fun p => (iidDist Pv n).pmf (C p.1 p.2))
    (fun _ => rfl)).symm

/-- Stochastic wiretap code obtained from a binned `V`-codebook `C`, a prefix channel `P_X|V`,
    and a joint-typicality decoder for `(M, L)` at Bob. -/
private noncomputable def wtBinWiretapCode (W : WiretapChannel X Y Z)
    (P_XV : DMC V X) (Pv : ProbDist V) {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₁ : ℝ)
    (C : Fin M → Fin L → Fin n → V) : WiretapCode W n M where
  enc := fun m =>
    { pmf := fun x => ((1 : ℝ) / (L : ℝ)) * ∑ l : Fin L, (P_XV.power n).trans (C m l) x
      nonneg := fun x => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun l _ => (P_XV.power n).nonneg _ _)
      sum_one := by
        have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [(P_XV.power n).sum_one]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp [hLne] }
  dec := fun y =>
    let W_VY := dmcComp P_XV (wiretapBobChannel W)
    let hML : 0 < M * L := Nat.mul_pos hM hL
    (finProdFinEquiv.symm (jointTypicalDec (W_VY.joint Pv) n (M * L) hML ε₁
      (wtFlattenEquiv _ M L C) y)).1

/-- Bob's marginal `(M, Y^n)` under `wtBinWiretapCode` equals the average over `l : Fin L`
    of `(W_VY^n)(y^n | C m l)`. -/
private lemma wtBin_bob_marginal_pmf (W : WiretapChannel X Y Z) (P_XV : DMC V X) (Pv : ProbDist V)
    {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₁ : ℝ) (C : Fin M → Fin L → Fin n → V)
    (m : Fin M) (y : Fin n → Y) :
    ((wiretapCodeJoint W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C)).map
      (fun t => (t.1, t.2.2.1))).pmf (m, y) =
    ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
      ∑ l : Fin L, ((dmcComp P_XV (wiretapBobChannel W)).power n).trans (C m l) y := by
  classical
  unfold ProbDist.map wiretapCodeJoint wtBinWiretapCode; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
  · simp_rw [Fintype.sum_prod_type]
    have hinner : ∀ x : Fin n → X,
        ∑ y' : Fin n → Y, ∑ z : Fin n → Z,
          (if (m, y') = (m, y) then
            ((1 : ℝ) / (M : ℝ)) * (((1 : ℝ) / (L : ℝ)) * ∑ l : Fin L, (P_XV.power n).trans (C m l) x) *
              (W.power n).trans x (fun i => (y' i, z i)) else 0) =
        ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
          ∑ l : Fin L, (P_XV.power n).trans (C m l) x * ((wiretapBobChannel W).power n).trans x y := by
      intro x
      rw [Finset.sum_eq_single y]
      · simp only [↓reduceIte, ← Finset.mul_sum]
        have hW : ∑ z : Fin n → Z, (W.power n).trans x (fun i => (y i, z i)) =
            ((wiretapBobChannel W).power n).trans x y := by
          unfold DMC.power wiretapBobChannel; dsimp only
          exact (Fintype.prod_sum (fun i z => W.trans (x i) (y i, z))).symm
        rw [hW, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast; ring
      · intro y' _ hne; exact Finset.sum_eq_zero fun z _ => by simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    simp_rw [hinner, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dmcComp_power]; rfl
  · intro m' _ hne
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
      Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- Eve's marginal `(M, Z^n)` under `wtBinWiretapCode` equals the average over `l : Fin L`
    of `(W_VZ^n)(z^n | C m l)`. -/
private lemma wtBin_eve_marginal_pmf (W : WiretapChannel X Y Z) (P_XV : DMC V X) (Pv : ProbDist V)
    {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₁ : ℝ) (C : Fin M → Fin L → Fin n → V)
    (m : Fin M) (z : Fin n → Z) :
    ((wiretapCodeJoint W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C)).map
      (fun t => (t.1, t.2.2.2))).pmf (m, z) =
    ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
      ∑ l : Fin L, ((dmcComp P_XV (wiretapEveChannel W)).power n).trans (C m l) z := by
  classical
  unfold ProbDist.map wiretapCodeJoint wtBinWiretapCode; dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
  · simp_rw [Fintype.sum_prod_type]
    have hinner : ∀ x : Fin n → X,
        ∑ y : Fin n → Y, ∑ z' : Fin n → Z,
          (if (m, z') = (m, z) then
            ((1 : ℝ) / (M : ℝ)) * (((1 : ℝ) / (L : ℝ)) * ∑ l : Fin L, (P_XV.power n).trans (C m l) x) *
              (W.power n).trans x (fun i => (y i, z' i)) else 0) =
        ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
          ∑ l : Fin L, (P_XV.power n).trans (C m l) x * ((wiretapEveChannel W).power n).trans x z := by
      intro x
      rw [Finset.sum_comm, Finset.sum_eq_single z]
      · simp only [↓reduceIte, ← Finset.mul_sum]
        have hW : ∑ y : Fin n → Y, (W.power n).trans x (fun i => (y i, z i)) =
            ((wiretapEveChannel W).power n).trans x z := by
          unfold DMC.power wiretapEveChannel; dsimp only
          exact (Fintype.prod_sum (fun i y => W.trans (x i) (y, z i))).symm
        rw [hW, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        push_cast; ring
      · intro z' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    simp_rw [hinner, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dmcComp_power]; rfl
  · intro m' _ hne
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
      Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro hm; exact absurd (Finset.mem_univ _) hm

/-- Bob's average error probability for a binned wiretap code is bounded above by the
    `(M * L)`-message DMC average error probability of the flattened codebook over `W_VY`. -/
private lemma wtBin_bob_error_le_dmcAvgError [DecidableEq Y]
    (W : WiretapChannel X Y Z) (P_XV : DMC V X) (Pv : ProbDist V)
    {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₁ : ℝ) (C : Fin M → Fin L → Fin n → V) :
    let W_VY := dmcComp P_XV (wiretapBobChannel W)
    let hML : 0 < M * L := Nat.mul_pos hM hL
    let enc := wtFlattenEquiv _ M L C
    wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) ≤
      dmcAvgError W_VY n (M * L) enc (jointTypicalDec (W_VY.joint Pv) n (M * L) hML ε₁ enc) := by
  classical
  dsimp only
  let W_VY := dmcComp P_XV (wiretapBobChannel W)
  let hML : 0 < M * L := Nat.mul_pos hM hL
  let enc := wtFlattenEquiv _ M L C
  let decML := jointTypicalDec (W_VY.joint Pv) n (M * L) hML ε₁ enc
  have hlhs : wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) =
      ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
        ∑ m : Fin M, ∑ l : Fin L, ∑ y : Fin n → Y,
          if (finProdFinEquiv.symm (decML y)).1 ≠ m then (W_VY.power n).trans (C m l) y else 0 := by
    unfold wiretapAvgError estErrorProb
    rw [Fintype.sum_prod_type]
    simp_rw [wtBin_bob_marginal_pmf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdec : (wtBinWiretapCode W P_XV Pv hM hL ε₁ C).dec y =
        (finProdFinEquiv.symm (decML y)).1 := rfl
    rw [hdec]
    by_cases h : (finProdFinEquiv.symm (decML y)).1 ≠ m
    · split_ifs; rfl
    · split_ifs; simp
  rw [hlhs]
  unfold dmcAvgError
  have hMLne : M * L ≠ 0 := Nat.ne_of_gt hML
  simp only [hMLne, ↓reduceIte]
  have hrhs : ∑ k : Fin (M * L), ∑ y : Fin n → Y,
        (if decML y ≠ k then (W_VY.power n).trans (enc k) y else 0) =
      ∑ m : Fin M, ∑ l : Fin L, ∑ y : Fin n → Y,
        if decML y ≠ finProdFinEquiv (m, l) then (W_VY.power n).trans (C m l) y else 0 := by
    conv_rhs => rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv finProdFinEquiv
      (fun p => ∑ y : Fin n → Y, if decML y ≠ finProdFinEquiv p then (W_VY.power n).trans (C p.1 p.2) y else 0)
      (fun k => ∑ y : Fin n → Y, if decML y ≠ k then (W_VY.power n).trans (enc k) y else 0)
      (fun p => by dsimp only [enc, wtFlattenEquiv, Equiv.coe_fn_mk]; rw [Equiv.symm_apply_apply])).symm
  rw [hrhs]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun y _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h1; rw [not_not.mp h2]; simp
  · exact (W_VY.power n).nonneg _ _
  · exact le_rfl

/-- Expected Bob decoding error over the i.i.d. random bin codebook. -/
private lemma wtBin_expected_bob_error_le [DecidableEq Y]
    (W : WiretapChannel X Y Z) (P_XV : DMC V X) (Pv : ProbDist V)
    {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₁ : ℝ) :
    let W_VY := dmcComp P_XV (wiretapBobChannel W)
    ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C *
        wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) ≤
      (1 - ∑ xy ∈ jointTypicalSet (W_VY.joint Pv) n ε₁, (jointIidDist (W_VY.joint Pv) n).pmf xy) +
      ((M * L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) := by
  dsimp only
  let W_VY := dmcComp P_XV (wiretapBobChannel W)
  let hML : 0 < M * L := Nat.mul_pos hM hL
  have h1 : ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C *
        wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) ≤
      ∑ enc : Fin (M * L) → Fin n → V,
        codebookProb Pv n (M * L) enc *
          dmcAvgError W_VY n (M * L) enc (jointTypicalDec (W_VY.joint Pv) n (M * L) hML ε₁ enc) := by
    calc ∑ C : Fin M → Fin L → Fin n → V,
          wtBinCodebookProb Pv n M L C *
            wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C)
      _ ≤ ∑ C : Fin M → Fin L → Fin n → V,
            codebookProb Pv n (M * L) (wtFlattenEquiv _ M L C) *
              dmcAvgError W_VY n (M * L) (wtFlattenEquiv _ M L C)
                (jointTypicalDec (W_VY.joint Pv) n (M * L) hML ε₁ (wtFlattenEquiv _ M L C)) := by
          refine Finset.sum_le_sum fun C _ => ?_
          rw [wtBinCodebookProb_eq_codebookProb]
          exact mul_le_mul_of_nonneg_left (wtBin_bob_error_le_dmcAvgError W P_XV Pv hM hL ε₁ C)
            (codebookProb_nonneg Pv n (M * L) _)
      _ = _ := Fintype.sum_equiv (wtFlattenEquiv _ M L) _ _ (fun _ => rfl)
  have h2 := dmc_random_coding_expected_error_le W_VY Pv n (M * L) hML ε₁
  have h3 := jointTypicalSet_indep_prob_le (W_VY.joint Pv) n ε₁
  have hmul : ((M * L - 1 : ℕ) : ℝ) *
      (∑ xy ∈ jointTypicalSet (W_VY.joint Pv) n ε₁,
        ((iidDist (W_VY.joint Pv).fst n).prod (iidDist (W_VY.joint Pv).snd n)).pmf xy) ≤
      ((M * L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  dsimp only at h2
  linarith

/-- Joint distribution `((M, L), Z^n)` at Eve for a fixed binned codebook `C`. -/
private noncomputable def wtBinEveFullJoint (W_VZ : DMC V Z) {n M L : ℕ}
    (hM : 0 < M) (hL : 0 < L) (C : Fin M → Fin L → Fin n → V) :
    ProbDist ((Fin M × Fin L) × (Fin n → Z)) :=
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  (dmcPrecomp (W_VZ.power n) (fun ml : Fin M × Fin L => C ml.1 ml.2)).joint ProbDist.uniform

/-- Conditional joint distribution `(L, Z^n)` at Eve given `M = m` for a fixed binned codebook `C`. -/
private noncomputable def wtBinEveBinJoint (W_VZ : DMC V Z) {n M L : ℕ}
    (hL : 0 < L) (C : Fin M → Fin L → Fin n → V) (m : Fin M) :
    ProbDist (Fin L × (Fin n → Z)) :=
  haveI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  (dmcPrecomp (W_VZ.power n) (C m)).joint ProbDist.uniform

/-- Exact leakage identity for a fixed binned codebook `C`:
    `I(M; Z^n) = I(M, L; Z^n) - log₂ L + (1/M) ∑_m H(L | Z^n, M = m)`. -/
private lemma wtBin_eve_leakage_identity (W : WiretapChannel X Y Z) (P_XV : DMC V X)
    (Pv : ProbDist V) {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₁ : ℝ)
    (C : Fin M → Fin L → Fin n → V) :
    let W_VZ := dmcComp P_XV (wiretapEveChannel W)
    wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) =
      mutualInfo (wtBinEveFullJoint W_VZ hM hL C) - log2 (L : ℝ) +
        ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m) := by
  dsimp only
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let W_VZ := dmcComp P_XV (wiretapEveChannel W)
  let J := wtBinEveFullJoint W_VZ hM hL C
  let P_MZ := (wiretapCodeJoint W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C)).map
    (fun t => (t.1, t.2.2.2))
  have hPMZ_eq : P_MZ = J.map (fun t => (t.1.1, t.2)) := by
    classical
    apply wt_probDist_ext; intro ⟨m, z⟩
    rw [wtBin_eve_marginal_pmf]
    unfold ProbDist.map J wtBinEveFullJoint DMC.joint dmcPrecomp ProbDist.uniform; dsimp only
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single z]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
      · simp only [↓reduceIte, Fintype.card_prod, Fintype.card_fin]
        rw [← Finset.mul_sum]
      · intro m' _ hne; exact Finset.sum_eq_zero fun l _ => by simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · intro z' _ hne; exact Finset.sum_eq_zero fun ml _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hPMZ_fst : P_MZ.fst = ProbDist.uniform (α := Fin M) := by
    rw [hPMZ_eq]
    apply wt_probDist_ext; intro m
    rw [← wt_probDist_map_fst, map_comp_eq]
    unfold ProbDist.map J wtBinEveFullJoint DMC.joint dmcPrecomp ProbDist.uniform; dsimp only
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single m]
    · simp only [Fintype.card_prod, Fintype.card_fin]
      have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
      have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
      have hinner : ∀ l : Fin L,
          ∑ z : Fin n → Z, (1 : ℝ) / ((M * L : ℕ) : ℝ) * (W_VZ.power n).trans (C m l) z =
            (1 : ℝ) / ((M * L : ℕ) : ℝ) := fun l => by
        rw [← Finset.mul_sum, (W_VZ.power n).sum_one, mul_one]
      have hsum : ∑ l : Fin L, ∑ z : Fin n → Z,
          (if m = m then (1 : ℝ) / ((M * L : ℕ) : ℝ) * (W_VZ.power n).trans (C m l) z else 0) =
            (1 : ℝ) / (M : ℝ) := by
        simp only [↓reduceIte]
        simp_rw [hinner]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; field_simp [hLne, hMne]
      simpa using hsum
    · intro m' _ hne; exact Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun z _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hPMZ_snd : P_MZ.snd = J.snd := by
    rw [hPMZ_eq, ← wt_probDist_map_snd, ← wt_probDist_map_snd, map_comp_eq]; rfl
  have hJ_fst : J.fst = ProbDist.uniform (α := Fin M × Fin L) := by
    unfold J wtBinEveFullJoint; exact dmc_joint_fst _ _
  have hH_M : shannonEntropy P_MZ.fst = log2 (M : ℝ) := by
    rw [hPMZ_fst, (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin M))).mpr rfl,
      Fintype.card_fin]
  have hH_ML : shannonEntropy J.fst = log2 (M : ℝ) + log2 (L : ℝ) := by
    rw [hJ_fst, (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin M × Fin L))).mpr rfl,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    exact log2_mul_pos (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr hL)
  -- Express `H(M, L, Z^n) - H(M, Z^n) = (1/M) ∑_m H(L | Z^n, M = m)`
  let J_LMZ : ProbDist ((Fin L × (Fin n → Z)) × Fin M) := J.map (fun t => ((t.1.2, t.2), t.1.1))
  have hJ_LMZ_pmf : ∀ l z m, J_LMZ.pmf ((l, z), m) =
      ((1 : ℝ) / (M : ℝ)) * (wtBinEveBinJoint W_VZ hL C m).pmf (l, z) := by
    classical
    intro l z m
    unfold J_LMZ ProbDist.map J wtBinEveFullJoint wtBinEveBinJoint DMC.joint dmcPrecomp ProbDist.uniform
    dsimp only
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single z]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
      · rw [Finset.sum_eq_single l]
        · simp only [↓reduceIte, Fintype.card_prod, Fintype.card_fin]
          push_cast; ring
        · intro l' _ hne; simp [hne]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro m' _ hne; exact Finset.sum_eq_zero fun l' _ => by simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · intro z' _ hne; exact Finset.sum_eq_zero fun ml _ => by simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hJ_LMZ_snd : J_LMZ.snd = ProbDist.uniform (α := Fin M) := by
    apply wt_probDist_ext; intro m
    unfold ProbDist.snd ProbDist.uniform
    simp_rw [hJ_LMZ_pmf, ← Finset.mul_sum, (wtBinEveBinJoint W_VZ hL C m).sum_one, mul_one,
      Fintype.card_fin]
  have hJ_LMZ_ent : shannonEntropy J_LMZ = shannonEntropy J := by
    let e : ((Fin M × Fin L) × (Fin n → Z)) ≃ ((Fin L × (Fin n → Z)) × Fin M) :=
      { toFun := fun t => ((t.1.2, t.2), t.1.1)
        invFun := fun t => ((t.2, t.1.1), t.1.2)
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    exact shannonEntropy_map_equiv e J
  have hce_J : condEntropy J_LMZ =
      ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, shannonEntropy (wtBinEveBinJoint W_VZ hL C m) := by
    rw [wt_condEntropy_eq_weighted_sum J_LMZ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : 0 < J_LMZ.snd.pmf m := by
      rw [hJ_LMZ_snd]; unfold ProbDist.uniform; simp only [Fintype.card_fin]; positivity
    simp only [hm, ↓reduceDIte]
    have hpmf : J_LMZ.snd.pmf m = (1 : ℝ) / (M : ℝ) := by
      rw [hJ_LMZ_snd]; unfold ProbDist.uniform; simp [Fintype.card_fin]
    have hslice : wtCondSlice J_LMZ m hm = wtBinEveBinJoint W_VZ hL C m := by
      apply wt_probDist_ext; intro ⟨l, z⟩
      unfold wtCondSlice; dsimp only
      rw [hJ_LMZ_pmf, hpmf]
      have hne : ((1 : ℝ) / (M : ℝ)) ≠ 0 := by positivity
      exact mul_div_cancel_left₀ _ hne
    rw [hslice, hpmf]
  let P_ZM : ProbDist ((Fin n → Z) × Fin M) := P_MZ.map Prod.swap
  have hPZM_snd : P_ZM.snd = ProbDist.uniform (α := Fin M) := by
    rw [snd_map_swap, hPMZ_fst]
  have hce_MZ : condEntropy P_ZM =
      ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, shannonEntropy (wtBinEveBinJoint W_VZ hL C m).snd := by
    rw [wt_condEntropy_eq_weighted_sum P_ZM, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : 0 < P_ZM.snd.pmf m := by
      rw [hPZM_snd]; unfold ProbDist.uniform; simp only [Fintype.card_fin]; positivity
    simp only [hm, ↓reduceDIte]
    have hpmf : P_ZM.snd.pmf m = (1 : ℝ) / (M : ℝ) := by
      rw [hPZM_snd]; unfold ProbDist.uniform; simp [Fintype.card_fin]
    have hslice : wtCondSlice P_ZM m hm = (wtBinEveBinJoint W_VZ hL C m).snd := by
      classical
      apply wt_probDist_ext; intro z
      change P_ZM.pmf (z, m) / P_ZM.snd.pmf m = ∑ l : Fin L, (wtBinEveBinJoint W_VZ hL C m).pmf (l, z)
      have hPZM_pmf : P_ZM.pmf (z, m) = P_MZ.pmf (m, z) := by
        unfold P_ZM ProbDist.map; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_eq_single m]
        · rw [Finset.sum_eq_single z]
          · simp
          · intro z' _ hne; simp [Prod.swap, hne]
          · intro hx; exact absurd (Finset.mem_univ _) hx
        · intro m' _ hne; exact Finset.sum_eq_zero fun z' _ => by simp [Prod.swap, hne]
        · intro hx; exact absurd (Finset.mem_univ _) hx
      rw [hPZM_pmf, hpmf, wtBin_eve_marginal_pmf]
      unfold wtBinEveBinJoint DMC.joint dmcPrecomp ProbDist.uniform; dsimp only
      rw [Fintype.card_fin, ← Finset.mul_sum]
      have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
      have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
      push_cast; field_simp [hMne, hLne]; ring
    rw [hslice, hpmf]
  have hdiff : shannonEntropy J - shannonEntropy P_MZ =
      ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m) := by
    have h1 : shannonEntropy J - shannonEntropy J_LMZ.snd = condEntropy J_LMZ := by
      unfold condEntropy; rw [hJ_LMZ_ent]
    have h2 : shannonEntropy P_MZ - shannonEntropy P_ZM.snd = condEntropy P_ZM := by
      unfold condEntropy P_ZM; rw [shannonEntropy_swap]
    rw [hJ_LMZ_snd] at h1
    rw [hPZM_snd] at h2
    have h3 : shannonEntropy J - shannonEntropy P_MZ = condEntropy J_LMZ - condEntropy P_ZM := by linarith
    rw [h3, hce_J, hce_MZ, ← mul_sub, ← Finset.sum_sub_distrib]
    rfl
  change mutualInfo P_MZ = _
  unfold mutualInfo
  rw [hH_M, hH_ML, hPMZ_snd]
  linarith

/-- Expected full mutual information bound over the random bin codebook:
    `E_C[I(M, L; Z^n)] ≤ n · I(V; Z)`. -/
private lemma wtBin_expected_full_mi_le (W_VZ : DMC V Z) (Pv : ProbDist V)
    {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) :
    ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C * mutualInfo (wtBinEveFullJoint W_VZ hM hL C) ≤
      (n : ℝ) * W_VZ.mutualInfo Pv := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  -- For each C, `I(M, L; Z^n) = H(Z^n | C = c) - (1/(M*L)) ∑_{m, l} ∑_i H(W_VZ(· | C m l i))`
  have hmi_C : ∀ C : Fin M → Fin L → Fin n → V,
      mutualInfo (wtBinEveFullJoint W_VZ hM hL C) =
        shannonEntropy (wtBinEveFullJoint W_VZ hM hL C).snd -
          ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
            ∑ m : Fin M, ∑ l : Fin L, ∑ i : Fin n, shannonEntropy (dmcRow W_VZ (C m l i)) := by
    intro C
    unfold mutualInfo wtBinEveFullJoint
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]
    have hsum : ∑ ml : Fin M × Fin L,
        (ProbDist.uniform (α := Fin M × Fin L)).pmf ml *
          shannonEntropy (dmcRow (dmcPrecomp (W_VZ.power n) (fun p : Fin M × Fin L => C p.1 p.2)) ml) =
        ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
          ∑ m : Fin M, ∑ l : Fin L, ∑ i : Fin n, shannonEntropy (dmcRow W_VZ (C m l i)) := by
      rw [Fintype.sum_prod_type]
      unfold ProbDist.uniform
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      have hrow : dmcRow (dmcPrecomp (W_VZ.power n) (fun p : Fin M × Fin L => C p.1 p.2)) (m, l) =
          piProdDist (fun i => dmcRow W_VZ (C m l i)) := rfl
      rw [hrow, shannonEntropy_piProdDist]
    rw [hsum]; ring
  simp_rw [hmi_C, mul_sub, Finset.sum_sub_distrib]
  -- Term 1: `E_C[H(P_{Z^n}(C))] = H(Z^n | C) ≤ H(P_Z^n) = n * H(P_Z)`
  let P_ZC : ProbDist ((Fin n → Z) × (Fin M → Fin L → Fin n → V)) :=
    { pmf := fun zc => wtBinCodebookProb Pv n M L zc.2 * (wtBinEveFullJoint W_VZ hM hL zc.2).snd.pmf zc.1
      nonneg := fun zc => mul_nonneg (wtBinCodebookProb_nonneg Pv n M L zc.2)
        ((wtBinEveFullJoint W_VZ hM hL zc.2).snd.nonneg zc.1)
      sum_one := by
        rw [Fintype.sum_prod_type_right]
        simp_rw [← Finset.mul_sum, (wtBinEveFullJoint W_VZ hM hL _).snd.sum_one, mul_one]
        exact wtBinCodebookProb_sum_one Pv n M L }
  have hPZC_snd : ∀ C, P_ZC.snd.pmf C = wtBinCodebookProb Pv n M L C := by
    intro C
    unfold ProbDist.snd P_ZC; dsimp only
    rw [← Finset.mul_sum, (wtBinEveFullJoint W_VZ hM hL C).snd.sum_one, mul_one]
  have hPZC_fst : P_ZC.fst = iidDist (W_VZ.joint Pv).snd n := by
    apply wt_probDist_ext; intro z
    unfold ProbDist.fst P_ZC; dsimp only
    have hexpand : ∀ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * (wtBinEveFullJoint W_VZ hM hL C).snd.pmf z =
        ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
          ∑ m : Fin M, ∑ l : Fin L,
            wtBinCodebookProb Pv n M L C * (W_VZ.power n).trans (C m l) z := by
      intro C
      unfold wtBinEveFullJoint ProbDist.snd DMC.joint dmcPrecomp ProbDist.uniform; dsimp only
      rw [Fintype.sum_prod_type]
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hexpand]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hsingle : ∀ m : Fin M,
        ∑ C : Fin M → Fin L → Fin n → V, ∑ l : Fin L,
          wtBinCodebookProb Pv n M L C * (W_VZ.power n).trans (C m l) z =
        (L : ℝ) * (iidDist (W_VZ.joint Pv).snd n).pmf z := by
      intro m
      rw [Finset.sum_comm]
      have hl_eq : ∀ l : Fin L,
          ∑ C : Fin M → Fin L → Fin n → V,
            wtBinCodebookProb Pv n M L C * (W_VZ.power n).trans (C m l) z =
          (iidDist (W_VZ.joint Pv).snd n).pmf z := by
        intro l
        have hrew := Fintype.sum_equiv (wtFlattenEquiv _ M L)
          (fun C => wtBinCodebookProb Pv n M L C * (W_VZ.power n).trans (C m l) z)
          (fun enc => codebookProb Pv n (M * L) enc * (W_VZ.power n).trans (enc (finProdFinEquiv (m, l))) z)
          (fun C => by rw [wtBinCodebookProb_eq_codebookProb]; dsimp [wtFlattenEquiv]; simp)
        rw [hrew]
        -- Use marginal of one codeword in `codebookProb`
        set k0 : Fin (M * L) := finProdFinEquiv (m, l)
        let F : Fin (M * L) → (Fin n → V) → ℝ := fun k v =>
          if k = k0 then (iidDist Pv n).pmf v * (W_VZ.power n).trans v z else (iidDist Pv n).pmf v
        have hfun : ∀ enc : Fin (M * L) → Fin n → V,
            codebookProb Pv n (M * L) enc * (W_VZ.power n).trans (enc k0) z =
              ∏ k : Fin (M * L), F k (enc k) := by
          intro enc
          unfold codebookProb
          rw [← Finset.mul_prod_erase Finset.univ (fun k => (iidDist Pv n).pmf (enc k)) (Finset.mem_univ k0),
              ← Finset.mul_prod_erase Finset.univ (fun k => F k (enc k)) (Finset.mem_univ k0)]
          have hrest : ∏ k ∈ Finset.univ.erase k0, F k (enc k) =
              ∏ k ∈ Finset.univ.erase k0, (iidDist Pv n).pmf (enc k) :=
            Finset.prod_congr rfl fun k hk => by simp [F, (Finset.mem_erase.mp hk).1]
          rw [hrest]; simp only [F, ↓reduceIte]; ring
        simp_rw [hfun]
        rw [← Fintype.prod_sum F]
        rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ v, F k v) (Finset.mem_univ k0)]
        have hrest : ∏ k ∈ Finset.univ.erase k0, ∑ v, F k v = 1 :=
          Finset.prod_eq_one fun k hk => by
            simp only [F, (Finset.mem_erase.mp hk).1, ↓reduceIte]; exact (iidDist Pv n).sum_one
        rw [hrest, mul_one]
        simp only [F, ↓reduceIte]
        have hpmf : ∀ v, (iidDist Pv n).pmf v * (W_VZ.power n).trans v z =
            (jointIidDist (W_VZ.joint Pv) n).pmf (v, z) := fun v => by
          unfold iidDist DMC.power jointIidDist DMC.joint; dsimp only
          rw [← Finset.prod_mul_distrib]
        simp_rw [hpmf]
        change (jointIidDist (W_VZ.joint Pv) n).snd.pmf z = _
        rw [jointIidDist_snd]
      simp_rw [hl_eq]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [hsingle]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
    have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
    push_cast; field_simp [hMne, hLne]
  have hterm1 : ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C * shannonEntropy (wtBinEveFullJoint W_VZ hM hL C).snd ≤
      (n : ℝ) * shannonEntropy (W_VZ.joint Pv).snd := by
    have hce_eq : condEntropy P_ZC =
        ∑ C : Fin M → Fin L → Fin n → V,
          wtBinCodebookProb Pv n M L C * shannonEntropy (wtBinEveFullJoint W_VZ hM hL C).snd := by
      rw [wt_condEntropy_eq_weighted_sum P_ZC]
      refine Finset.sum_congr rfl fun C _ => ?_
      by_cases hC : 0 < P_ZC.snd.pmf C
      · simp only [hC, ↓reduceDIte]
        have hslice : wtCondSlice P_ZC C hC = (wtBinEveFullJoint W_VZ hM hL C).snd := by
          apply wt_probDist_ext; intro z
          unfold wtCondSlice P_ZC; dsimp only
          rw [hPZC_snd]
          have hne : wtBinCodebookProb Pv n M L C ≠ 0 := ne_of_gt (hPZC_snd C ▸ hC)
          exact mul_div_cancel_left₀ _ hne
        rw [hslice, hPZC_snd]
      · simp only [hC, ↓reduceDIte]
        have h0 : wtBinCodebookProb Pv n M L C = 0 :=
          le_antisymm (by linarith [hPZC_snd C, not_lt.mp hC]) (wtBinCodebookProb_nonneg Pv n M L C)
        rw [h0, zero_mul]
    have hle := condEntropy_le_shannonEntropy P_ZC
    rw [hce_eq, hPZC_fst] at hle
    have hiid : shannonEntropy (iidDist (W_VZ.joint Pv).snd n) =
        (n : ℝ) * shannonEntropy (W_VZ.joint Pv).snd := by
      have heq : iidDist (W_VZ.joint Pv).snd n = piProdDist (fun _ : Fin n => (W_VZ.joint Pv).snd) := rfl
      rw [heq, shannonEntropy_piProdDist, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  -- Term 2: `E_C[(1/(M*L)) ∑_{m, l} ∑_i H(W_VZ(· | C m l i))] = n * ∑_v Pv(v) H(W_VZ(· | v))`
  have hterm2 : ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C *
        (((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
          ∑ m : Fin M, ∑ l : Fin L, ∑ i : Fin n, shannonEntropy (dmcRow W_VZ (C m l i))) =
      (n : ℝ) * ∑ v : V, Pv.pmf v * shannonEntropy (dmcRow W_VZ v) := by
    have hpull : ∀ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C *
          (((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
            ∑ m : Fin M, ∑ l : Fin L, ∑ i : Fin n, shannonEntropy (dmcRow W_VZ (C m l i))) =
        ((1 : ℝ) / ((M * L : ℕ) : ℝ)) *
          ∑ m : Fin M, ∑ l : Fin L, ∑ i : Fin n,
            wtBinCodebookProb Pv n M L C * shannonEntropy (dmcRow W_VZ (C m l i)) := by
      intro C
      rw [← mul_assoc, mul_comm (wtBinCodebookProb Pv n M L C), mul_assoc, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hpull]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hsingle : ∀ m : Fin M,
        ∑ C : Fin M → Fin L → Fin n → V, ∑ l : Fin L, ∑ i : Fin n,
          wtBinCodebookProb Pv n M L C * shannonEntropy (dmcRow W_VZ (C m l i)) =
        (L : ℝ) * ((n : ℝ) * ∑ v : V, Pv.pmf v * shannonEntropy (dmcRow W_VZ v)) := by
      intro m
      rw [Finset.sum_comm]
      have hl_eq : ∀ l : Fin L,
          ∑ C : Fin M → Fin L → Fin n → V, ∑ i : Fin n,
            wtBinCodebookProb Pv n M L C * shannonEntropy (dmcRow W_VZ (C m l i)) =
          (n : ℝ) * ∑ v : V, Pv.pmf v * shannonEntropy (dmcRow W_VZ v) := by
        intro l
        rw [Finset.sum_comm]
        have hi_eq : ∀ i : Fin n,
            ∑ C : Fin M → Fin L → Fin n → V,
              wtBinCodebookProb Pv n M L C * shannonEntropy (dmcRow W_VZ (C m l i)) =
            ∑ v : V, Pv.pmf v * shannonEntropy (dmcRow W_VZ v) := by
          intro i
          have hrew := Fintype.sum_equiv (wtFlattenEquiv _ M L)
            (fun C => wtBinCodebookProb Pv n M L C * shannonEntropy (dmcRow W_VZ (C m l i)))
            (fun enc => codebookProb Pv n (M * L) enc * shannonEntropy (dmcRow W_VZ (enc (finProdFinEquiv (m, l)) i)))
            (fun C => by rw [wtBinCodebookProb_eq_codebookProb]; dsimp [wtFlattenEquiv]; simp)
          rw [hrew]
          set k0 : Fin (M * L) := finProdFinEquiv (m, l)
          let F : Fin (M * L) → (Fin n → V) → ℝ := fun k v =>
            if k = k0 then (iidDist Pv n).pmf v * shannonEntropy (dmcRow W_VZ (v i))
            else (iidDist Pv n).pmf v
          have hfun : ∀ enc : Fin (M * L) → Fin n → V,
              codebookProb Pv n (M * L) enc * shannonEntropy (dmcRow W_VZ (enc k0 i)) =
                ∏ k : Fin (M * L), F k (enc k) := by
            intro enc
            unfold codebookProb
            rw [← Finset.mul_prod_erase Finset.univ (fun k => (iidDist Pv n).pmf (enc k)) (Finset.mem_univ k0),
                ← Finset.mul_prod_erase Finset.univ (fun k => F k (enc k)) (Finset.mem_univ k0)]
            have hrest : ∏ k ∈ Finset.univ.erase k0, F k (enc k) =
                ∏ k ∈ Finset.univ.erase k0, (iidDist Pv n).pmf (enc k) :=
              Finset.prod_congr rfl fun k hk => by simp [F, (Finset.mem_erase.mp hk).1]
            rw [hrest]; simp only [F, ↓reduceIte]; ring
          simp_rw [hfun]
          rw [← Fintype.prod_sum F]
          rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ v, F k v) (Finset.mem_univ k0)]
          have hrest : ∏ k ∈ Finset.univ.erase k0, ∑ v, F k v = 1 :=
            Finset.prod_eq_one fun k hk => by
              simp only [F, (Finset.mem_erase.mp hk).1, ↓reduceIte]; exact (iidDist Pv n).sum_one
          rw [hrest, mul_one]
          simp only [F, ↓reduceIte]
          -- Now marginalize coordinate `i` of `iidDist Pv n`
          let G : Fin n → V → ℝ := fun j v =>
            if j = i then Pv.pmf v * shannonEntropy (dmcRow W_VZ v) else Pv.pmf v
          have hfun2 : ∀ x : Fin n → V,
              (iidDist Pv n).pmf x * shannonEntropy (dmcRow W_VZ (x i)) = ∏ j : Fin n, G j (x j) := by
            intro x
            unfold iidDist; dsimp only
            rw [← Finset.mul_prod_erase Finset.univ (fun j => Pv.pmf (x j)) (Finset.mem_univ i),
                ← Finset.mul_prod_erase Finset.univ (fun j => G j (x j)) (Finset.mem_univ i)]
            have hrest2 : ∏ j ∈ Finset.univ.erase i, G j (x j) =
                ∏ j ∈ Finset.univ.erase i, Pv.pmf (x j) :=
              Finset.prod_congr rfl fun j hj => by simp [G, (Finset.mem_erase.mp hj).1]
            rw [hrest2]; simp only [G, ↓reduceIte]; ring
          simp_rw [hfun2, ← Fintype.prod_sum G]
          rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ v, G j v) (Finset.mem_univ i)]
          have hrest2 : ∏ j ∈ Finset.univ.erase i, ∑ v, G j v = 1 :=
            Finset.prod_eq_one fun j hj => by
              simp only [G, (Finset.mem_erase.mp hj).1, ↓reduceIte]; exact Pv.sum_one
          rw [hrest2, mul_one]; simp [G]
        simp_rw [hi_eq]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [hl_eq]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [hsingle]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
    have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
    push_cast; field_simp [hMne, hLne]
  have hmi_VZ : W_VZ.mutualInfo Pv =
      shannonEntropy (W_VZ.joint Pv).snd - ∑ v : V, Pv.pmf v * shannonEntropy (dmcRow W_VZ v) := by
    unfold DMC.mutualInfo mutualInfo
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]; ring
  rw [hterm2, hmi_VZ]; linarith

/-- Expected conditional entropy `E_C[(1/M) ∑_m H(L | Z^n, M = m)]` via Fano's inequality and
    Shannon's random coding bound for Eve decoding `L` inside bin `m`. -/
private lemma wtBin_expected_cond_entropy_le [DecidableEq Z]
    (W_VZ : DMC V Z) (Pv : ProbDist V) {n M L : ℕ} (hM : 0 < M) (hL : 0 < L) (ε₂ : ℝ) :
    ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C *
        (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m)) ≤
      1 + ((1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz) +
           ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂)))) *
          log2 (L : ℝ) := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  -- Pull `(1/M) ∑_m` outside the expectation over `C`
  have hswap : ∑ C : Fin M → Fin L → Fin n → V,
      wtBinCodebookProb Pv n M L C *
        (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m)) =
      ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * condEntropy (wtBinEveBinJoint W_VZ hL C m) := by
    have h1 : ∀ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C *
          (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m)) =
        ((1 : ℝ) / (M : ℝ)) *
          ∑ m : Fin M, wtBinCodebookProb Pv n M L C * condEntropy (wtBinEveBinJoint W_VZ hL C m) := by
      intro C
      rw [← mul_assoc, mul_comm (wtBinCodebookProb Pv n M L C), mul_assoc, Finset.mul_sum]
    simp_rw [h1]
    rw [← Finset.mul_sum]
    congr 1; exact Finset.sum_comm
  rw [hswap]
  let B := 1 + ((1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz) +
           ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂)))) *
          log2 (L : ℝ)
  have hterm_m : ∀ m : Fin M,
      ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * condEntropy (wtBinEveBinJoint W_VZ hL C m) ≤ B := by
    intro m
    -- Marginalize out all bins `m' ≠ m`
    let F : Fin M → (Fin L → Fin n → V) → ℝ := fun k c =>
      if k = m then codebookProb Pv n L c * condEntropy ((dmcPrecomp (W_VZ.power n) c).joint ProbDist.uniform)
      else codebookProb Pv n L c
    have hfun : ∀ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * condEntropy (wtBinEveBinJoint W_VZ hL C m) =
          ∏ k : Fin M, F k (C k) := by
      intro C
      unfold wtBinCodebookProb
      rw [← Finset.mul_prod_erase Finset.univ (fun k => ∏ l : Fin L, (iidDist Pv n).pmf (C k l)) (Finset.mem_univ m),
          ← Finset.mul_prod_erase Finset.univ (fun k => F k (C k)) (Finset.mem_univ m)]
      have hrest : ∏ k ∈ Finset.univ.erase m, F k (C k) =
          ∏ k ∈ Finset.univ.erase m, ∏ l : Fin L, (iidDist Pv n).pmf (C k l) :=
        Finset.prod_congr rfl fun k hk => by simp [F, codebookProb, (Finset.mem_erase.mp hk).1]
      rw [hrest]; simp only [F, codebookProb, wtBinEveBinJoint, ↓reduceIte]; ring
    simp_rw [hfun, ← Fintype.prod_sum F]
    rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ c, F k c) (Finset.mem_univ m)]
    have hrest : ∏ k ∈ Finset.univ.erase m, ∑ c, F k c = 1 :=
      Finset.prod_eq_one fun k hk => by
        simp only [F, (Finset.mem_erase.mp hk).1, ↓reduceIte]
        exact codebookProb_sum_one Pv n L
    rw [hrest, mul_one]; simp only [F, ↓reduceIte]
    -- Apply Fano's inequality for each single-bin codebook `c : Fin L → Fin n → V`
    have hfano_c : ∀ c : Fin L → Fin n → V,
        condEntropy ((dmcPrecomp (W_VZ.power n) c).joint (ProbDist.uniform (α := Fin L))) ≤
          1 + dmcAvgError W_VZ n L c (jointTypicalDec (W_VZ.joint Pv) n L hL ε₂ c) * log2 (L : ℝ) := by
      intro c
      let dec := jointTypicalDec (W_VZ.joint Pv) n L hL ε₂ c
      let P_LZ := (dmcPrecomp (W_VZ.power n) c).joint (ProbDist.uniform (α := Fin L))
      have hf := fano_inequality_card P_LZ dec
      rw [Fintype.card_fin] at hf
      have herr : estErrorProb P_LZ dec = dmcAvgError W_VZ n L c dec := by
        classical
        unfold P_LZ estErrorProb dmcAvgError dmcPrecomp DMC.joint ProbDist.uniform
        have hLne : L ≠ 0 := Nat.ne_of_gt hL
        simp only [hLne, ↓reduceIte, Fintype.card_fin]
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
      have hbin : binaryEntropy (estErrorProb P_LZ dec) ≤ 1 :=
        wt_binaryEntropy_le_one (estErrorProb_nonneg P_LZ dec) (estErrorProb_le_one P_LZ dec)
      rw [herr] at hf hbin
      linarith
    have hsum_le : ∑ c : Fin L → Fin n → V,
        codebookProb Pv n L c *
          condEntropy ((dmcPrecomp (W_VZ.power n) c).joint (ProbDist.uniform (α := Fin L))) ≤
        1 + (∑ c : Fin L → Fin n → V,
          codebookProb Pv n L c *
            dmcAvgError W_VZ n L c (jointTypicalDec (W_VZ.joint Pv) n L hL ε₂ c)) * log2 (L : ℝ) := by
      calc ∑ c : Fin L → Fin n → V,
            codebookProb Pv n L c *
              condEntropy ((dmcPrecomp (W_VZ.power n) c).joint (ProbDist.uniform (α := Fin L)))
        _ ≤ ∑ c : Fin L → Fin n → V,
              codebookProb Pv n L c *
                (1 + dmcAvgError W_VZ n L c (jointTypicalDec (W_VZ.joint Pv) n L hL ε₂ c) * log2 (L : ℝ)) :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hfano_c c) (codebookProb_nonneg Pv n L c)
        _ = (∑ c : Fin L → Fin n → V, codebookProb Pv n L c) +
            (∑ c : Fin L → Fin n → V,
              codebookProb Pv n L c *
                dmcAvgError W_VZ n L c (jointTypicalDec (W_VZ.joint Pv) n L hL ε₂ c)) * log2 (L : ℝ) := by
            simp_rw [mul_add, mul_one, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul]
        _ = _ := by rw [codebookProb_sum_one]
    have hrc := dmc_random_coding_expected_error_le W_VZ Pv n L hL ε₂
    have hindep := jointTypicalSet_indep_prob_le (W_VZ.joint Pv) n ε₂
    have hlogL0 : 0 ≤ log2 (L : ℝ) := by
      unfold log2
      have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      exact div_nonneg (Real.log_nonneg h1) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    have hrc' : ∑ c : Fin L → Fin n → V,
        codebookProb Pv n L c *
          dmcAvgError W_VZ n L c (jointTypicalDec (W_VZ.joint Pv) n L hL ε₂ c) ≤
        (1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz) +
        ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) := by
      have hmul : ((L - 1 : ℕ) : ℝ) *
          (∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂,
            ((iidDist (W_VZ.joint Pv).fst n).prod (iidDist (W_VZ.joint Pv).snd n)).pmf xz) ≤
          ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) :=
        mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg _)
      dsimp only at hrc
      linarith
    have hmulL := mul_le_mul_of_nonneg_right hrc' hlogL0
    dsimp only [B]
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  calc ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * condEntropy (wtBinEveBinJoint W_VZ hL C m)
    _ ≤ ((1 : ℝ) / (M : ℝ)) * ∑ _m : Fin M, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hterm_m m) (by positivity)
    _ = ((1 : ℝ) / (M : ℝ)) * ((M : ℝ) * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = B := by field_simp [ne_of_gt hMpos]

/-- Helper bound for exponential tail `2^{-n ε} ≤ δ` once `n ≥ log₂(1/δ) / ε`. -/
private lemma wt_rpow_neg_le {n : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hn : log2 (1 / δ) / ε ≤ (n : ℝ)) :
    (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ := by
  have hlog_le : Real.log (1 / δ) ≤ (n : ℝ) * ε * Real.log 2 := by
    have h1 : log2 (1 / δ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn
    unfold log2 at h1
    exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp h1
  have hexp_le : 1 / δ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) := by
    have h1δ : 0 < 1 / δ := by positivity
    calc 1 / δ
      _ = Real.exp (Real.log (1 / δ)) := (Real.exp_log h1δ).symm
      _ ≤ Real.exp ((n : ℝ) * ε * Real.log 2) := Real.exp_le_exp.mpr hlog_le
      _ = Real.exp (Real.log 2 * ((n : ℝ) * ε)) := by ring_nf
      _ = (2 : ℝ) ^ ((n : ℝ) * ε) := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * ε)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul1 : (2 : ℝ) ^ (-((n : ℝ) * ε)) * (2 : ℝ) ^ ((n : ℝ) * ε) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hmul2 : (1 / δ) * (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ 1 := by
    calc (1 / δ) * (2 : ℝ) ^ (-((n : ℝ) * ε))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) * (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_right hexp_le (le_of_lt hpos)
      _ = 1 := by rw [mul_comm, hmul1]
  have hmul3 := mul_le_mul_of_nonneg_left hmul2 (le_of_lt hδ)
  have hsimp : δ * ((1 / δ) * (2 : ℝ) ^ (-((n : ℝ) * ε))) = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
    field_simp [ne_of_gt hδ]
  linarith

/-- **Wiretap Random-Binning Achievability Below Any Auxiliary Single-Letter Rate**:
    for any `Pvx : ProbDist (V × X)` and `0 ≤ R < I(V; Y) - I(V; Z)`,
    rate `R` is operationally weak-secrecy achievable over `W`. -/
private lemma wt_achievable_lt_aux (W : WiretapChannel X Y Z) (Pvx : ProbDist (V × X))
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : R < mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
              mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2)))) :
    IsWiretapWeakAchievable W R := by
  classical
  have : Nonempty X := ⟨(wt_nonempty_of_probDist Pvx).some.2⟩
  let Pv : ProbDist V := Pvx.fst
  let P_XV : DMC V X := wtPrefixChannel Pvx
  let W_VY : DMC V Y := dmcComp P_XV (wiretapBobChannel W)
  let W_VZ : DMC V Z := dmcComp P_XV (wiretapEveChannel W)
  have hI_VY : W_VY.mutualInfo Pv =
      mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) := by
    unfold DMC.mutualInfo; rw [wtPrefixChannel_bob_joint]
  have hI_VZ : W_VZ.mutualInfo Pv =
      mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) := by
    unfold DMC.mutualInfo; rw [wtPrefixChannel_eve_joint]
  have hR' : R < W_VY.mutualInfo Pv - W_VZ.mutualInfo Pv := by rwa [hI_VY, hI_VZ]
  have hI_VZ_nonneg : 0 ≤ W_VZ.mutualInfo Pv := mutualInfo_nonneg _
  refine ⟨hR0, fun ε hε => ?_⟩
  let Δ : ℝ := (W_VY.mutualInfo Pv - W_VZ.mutualInfo Pv) - R
  have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
  let η : ℝ := min (Δ / 2) (ε / 4)
  have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
  have hη_le_ε4 : η ≤ ε / 4 := min_le_right _ _
  have hη_le_Δ2 : η ≤ Δ / 2 := min_le_left _ _
  by_cases hlow : W_VZ.mutualInfo Pv ≤ η
  · -- Case 1: `I(V; Z) ≤ η ≤ ε/4`. No binning needed (`L = 1`).
    have hR_lt_VY : R < W_VY.mutualInfo Pv := by linarith
    let ε₁ : ℝ := (W_VY.mutualInfo Pv - R) / 4
    have hε₁ : 0 < ε₁ := by dsimp only [ε₁]; linarith
    obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one (W_VY.joint Pv) hε₁ (by positivity : 0 < ε / 4)
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (1 / (ε / 4)) / ε₁)
    refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
    dsimp only
    have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hn)
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hL : (0 : ℕ) < 1 := Nat.zero_lt_one
    have hM_le : (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
      have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
        Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hR0)
      have hfl1 : 1 ≤ Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := Nat.le_floor h1le
      have hMeq : M = Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := max_eq_right hfl1
      rw [hMeq]; exact Nat.floor_le (by linarith)
    have hMsub : ((M * 1 - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
      have hle : ((M * 1 - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.sub_le (M * 1) 1 |> le_trans <| by simp
      linarith
    have hbob_exp := wtBin_expected_bob_error_le (n := n) W P_XV Pv hM hL ε₁
    dsimp only at hbob_exp
    have hbob_t1 : 1 - ∑ xy ∈ jointTypicalSet (W_VY.joint Pv) n ε₁, (jointIidDist (W_VY.joint Pv) n).pmf xy ≤ ε / 4 := by
      have := hN₁ n (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hn)
      linarith
    have hbob_t2 : ((M * 1 - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) ≤ ε / 4 := by
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hprod : (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) =
          (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₁]; ring
      have hn2 : log2 (1 / (ε / 4)) / ε₁ ≤ (n : ℝ) :=
        le_trans hN₂ (by exact_mod_cast le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hn)
      calc ((M * 1 - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁)))
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) :=
            mul_le_mul_of_nonneg_right hMsub (le_of_lt hpow_pos)
        _ = (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := hprod
        _ ≤ ε / 4 := wt_rpow_neg_le hε₁ (by positivity) hn2
    have hbob_le : ∑ C : Fin M → Fin 1 → Fin n → V,
        wtBinCodebookProb Pv n M 1 C * wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) ≤ ε / 2 := by
      linarith
    have hleak_C : ∀ C : Fin M → Fin 1 → Fin n → V,
        wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) =
          mutualInfo (wtBinEveFullJoint W_VZ hM hL C) := by
      intro C
      have hid : wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) =
          mutualInfo (wtBinEveFullJoint W_VZ hM hL C) - log2 ((1 : ℕ) : ℝ) +
            ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m) :=
        wtBin_eve_leakage_identity W P_XV Pv hM hL ε₁ C
      have hce0 : ∀ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m) = 0 := fun m =>
        wt_condEntropy_eq_zero_of_unique_left _
      simp_rw [hce0] at hid
      simp [log2] at hid
      exact hid
    have hleak_exp : ∑ C : Fin M → Fin 1 → Fin n → V,
        wtBinCodebookProb Pv n M 1 C *
          (wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ)) ≤ ε / 4 := by
      have h1 := wtBin_expected_full_mi_le (n := n) W_VZ Pv hM hL
      have hdiv : ∑ C : Fin M → Fin 1 → Fin n → V,
          wtBinCodebookProb Pv n M 1 C *
            (wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ)) =
          (∑ C : Fin M → Fin 1 → Fin n → V,
            wtBinCodebookProb Pv n M 1 C * mutualInfo (wtBinEveFullJoint W_VZ hM hL C)) / (n : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun C _ => by rw [hleak_C C, mul_div_assoc]
      rw [hdiv]
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt hn_r)
      rw [mul_div_cancel_left₀ _ (ne_of_gt hn_r)] at h2
      linarith
    have htot : ∑ C : Fin M → Fin 1 → Fin n → V,
        wtBinCodebookProb Pv n M 1 C *
          (wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) +
           wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ)) ≤ ε := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      linarith
    obtain ⟨C, hC⟩ := wt_exists_le_of_weighted_sum_le
      (wtBinCodebookProb Pv n M 1)
      (fun C => wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) +
                wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ))
      ε
      (wtBinCodebookProb_nonneg Pv n M 1)
      (wtBinCodebookProb_sum_one Pv n M 1)
      htot
    have herr0 : 0 ≤ wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) :=
      estErrorProb_nonneg _ _
    have hleak0 : 0 ≤ wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ) :=
      div_nonneg (mutualInfo_nonneg _) (le_of_lt hn_r)
    refine ⟨wtBinWiretapCode W P_XV Pv hM hL ε₁ C, by linarith, ?_⟩
    have hdiv_le : wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ) ≤ ε := by linarith
    have hmul_le := (div_le_iff₀ hn_r).mp hdiv_le
    linarith
  · -- Case 2: `I(V; Z) > η`. Random binning with rate `R' = I(V; Z) - η > 0`.
    push Not at hlow
    let R' : ℝ := W_VZ.mutualInfo Pv - η
    have hR'_pos : 0 < R' := by dsimp only [R']; linarith
    let ε₁ : ℝ := (W_VY.mutualInfo Pv - (R + R')) / 4
    have hε₁ : 0 < ε₁ := by dsimp only [ε₁, R', Δ]; linarith
    let ε₂ : ℝ := η / 4
    have hε₂ : 0 < ε₂ := by dsimp only [ε₂]; linarith
    have hδ_eve : 0 < ε / (8 * R') := by positivity
    obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one (W_VY.joint Pv) hε₁ (by positivity : 0 < ε / 8)
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (1 / (ε / 8)) / ε₁)
    obtain ⟨N₃, hN₃⟩ := joint_aep_prob_tendsto_one (W_VZ.joint Pv) hε₂ hδ_eve
    obtain ⟨N₄, hN₄⟩ := exists_nat_ge (log2 (1 / (ε / (8 * R'))) / ε₂)
    obtain ⟨N₅, hN₅⟩ := exists_nat_ge (max (1 / R') (8 / ε))
    let N : ℕ := max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1)
    refine ⟨N, fun n hn => ?_⟩
    dsimp only
    have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_trans (le_max_right N₅ 1) (le_max_right _ _)) hn)
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hn_N₁ : N₁ ≤ n := le_trans (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ _)) (le_max_left _ _)) hn
    have hn_N₂ : N₂ ≤ n := le_trans (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ _)) (le_max_left _ _)) hn
    have hn_N₃ : N₃ ≤ n := le_trans (le_trans (le_trans (le_max_left N₃ N₄) (le_max_right _ _)) (le_max_left _ _)) hn
    have hn_N₄ : N₄ ≤ n := le_trans (le_trans (le_trans (le_max_right N₃ N₄) (le_max_right _ _)) (le_max_left _ _)) hn
    have hn_N₅ : N₅ ≤ n := le_trans (le_trans (le_max_left N₅ 1) (le_max_right _ _)) hn
    let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    let L := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R')))
    have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hL : 0 < L := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hM_le : (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
      have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
        Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hR0)
      have hMeq : M = Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := max_eq_right (Nat.le_floor h1le)
      rw [hMeq]; exact Nat.floor_le (by linarith)
    have hL_le : (L : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R') := by
      have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R') :=
        Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hR'_pos))
      have hLeq : L = Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R')) := max_eq_right (Nat.le_floor h1le)
      rw [hLeq]; exact Nat.floor_le (by linarith)
    have hML_le : ((M * L - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (R + R')) := by
      have h1 : ((M * L - 1 : ℕ) : ℝ) ≤ ((M * L : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (M * L) 1
      have h2 : (M : ℝ) * (L : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ ((n : ℝ) * R') :=
        mul_le_mul hM_le hL_le (Nat.cast_nonneg L) (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      have h3 : (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ ((n : ℝ) * R') = (2 : ℝ) ^ ((n : ℝ) * (R + R')) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      push_cast at h1; linarith
    have hLsub_le : ((L - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R') := by
      have h1 : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
      linarith
    have hn_ge_max : max (1 / R') (8 / ε) ≤ (n : ℝ) := le_trans hN₅ (by exact_mod_cast hn_N₅)
    have hnR'_ge1 : 1 ≤ (n : ℝ) * R' := by
      have h1 : 1 / R' ≤ (n : ℝ) := le_trans (le_max_left _ _) hn_ge_max
      have := (div_le_iff₀ hR'_pos).mp h1; linarith
    have h2n_le : 2 / (n : ℝ) ≤ ε / 4 := by
      have h1 : 8 / ε ≤ (n : ℝ) := le_trans (le_max_right _ _) hn_ge_max
      rw [div_le_iff₀ hn_r]
      have := (div_le_iff₀ hε).mp h1; linarith
    have hlogL_ge : (n : ℝ) * R' - 1 ≤ log2 (L : ℝ) := by
      have h2pow_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R') := by
        calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * R') := Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR'_ge1
      have hL_ge_pow : (2 : ℝ) ^ ((n : ℝ) * R' - 1) ≤ (L : ℝ) := by
        have hhalf : (2 : ℝ) ^ ((n : ℝ) * R' - 1) = (2 : ℝ) ^ ((n : ℝ) * R') / 2 := by
          rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        have hfloor : (2 : ℝ) ^ ((n : ℝ) * R') - 1 < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R')) : ℝ) := by
          linarith [Nat.lt_floor_add_one ((2 : ℝ) ^ ((n : ℝ) * R'))]
        have hleL : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R')) : ℝ) ≤ (L : ℝ) :=
          Nat.cast_le.mpr (le_max_right 1 _)
        linarith
      have hmono := wt_log2_le_log2 (Real.rpow_pos_of_pos (by norm_num) _) hL_ge_pow
      rwa [wt_log2_two_rpow] at hmono
    have hlogL_le : log2 (L : ℝ) ≤ (n : ℝ) * R' := by
      have hmono := wt_log2_le_log2 (Nat.cast_pos.mpr hL) hL_le
      rwa [wt_log2_two_rpow] at hmono
    -- Bob's expected error ≤ ε/4
    have hbob_exp := wtBin_expected_bob_error_le (n := n) W P_XV Pv hM hL ε₁
    dsimp only at hbob_exp
    have hbob_t1 : 1 - ∑ xy ∈ jointTypicalSet (W_VY.joint Pv) n ε₁, (jointIidDist (W_VY.joint Pv) n).pmf xy ≤ ε / 8 := by
      linarith [hN₁ n hn_N₁]
    have hbob_t2 : ((M * L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) ≤ ε / 8 := by
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hprod : (2 : ℝ) ^ ((n : ℝ) * (R + R')) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) =
          (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₁]; ring
      have hn2 : log2 (1 / (ε / 8)) / ε₁ ≤ (n : ℝ) := le_trans hN₂ (by exact_mod_cast hn_N₂)
      calc ((M * L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁)))
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R + R')) * (2 : ℝ) ^ (-((n : ℝ) * (W_VY.mutualInfo Pv - 3 * ε₁))) :=
            mul_le_mul_of_nonneg_right hML_le (le_of_lt hpow_pos)
        _ = (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := hprod
        _ ≤ ε / 8 := wt_rpow_neg_le hε₁ (by positivity) hn2
    have hbob_le : ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) ≤ ε / 4 := by
      linarith
    -- Eve's expected normalized leakage ≤ 3ε/4
    have heve_t1 : 1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz ≤ ε / (8 * R') := by
      linarith [hN₃ n hn_N₃]
    have heve_t2 : ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) ≤ ε / (8 * R') := by
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hprod : (2 : ℝ) ^ ((n : ℝ) * R') * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) =
          (2 : ℝ) ^ (-((n : ℝ) * ε₂)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [R', ε₂]; ring
      have hn4 : log2 (1 / (ε / (8 * R'))) / ε₂ ≤ (n : ℝ) := le_trans hN₄ (by exact_mod_cast hn_N₄)
      calc ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂)))
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * R') * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) :=
            mul_le_mul_of_nonneg_right hLsub_le (le_of_lt hpow_pos)
        _ = (2 : ℝ) ^ (-((n : ℝ) * ε₂)) := hprod
        _ ≤ ε / (8 * R') := wt_rpow_neg_le hε₂ hδ_eve hn4
    have heve_err_le :
        (1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz) +
        ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) ≤ ε / (4 * R') := by
      have hadd : ε / (8 * R') + ε / (8 * R') = ε / (4 * R') := by
        field_simp [ne_of_gt hR'_pos]; ring
      linarith
    have heve_err_nonneg : 0 ≤
        (1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz) +
        ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) := by
      have hsum_le1 : ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz ≤ 1 := by
        calc _ ≤ ∑ xz : (Fin n → V) × (Fin n → Z), (jointIidDist (W_VZ.joint Pv) n).pmf xz :=
              Finset.sum_le_univ_sum_of_nonneg fun _ => (jointIidDist (W_VZ.joint Pv) n).nonneg _
          _ = 1 := (jointIidDist (W_VZ.joint Pv) n).sum_one
      have h2pos : 0 ≤ ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂))) :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      linarith
    have hlogL_nonneg : 0 ≤ log2 (L : ℝ) := by
      unfold log2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hL))
        (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    have hce_bound :
        ∑ C : Fin M → Fin L → Fin n → V,
          wtBinCodebookProb Pv n M L C *
            (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m)) ≤
        1 + (n : ℝ) * (ε / 4) := by
      have h1 := wtBin_expected_cond_entropy_le (n := n) W_VZ Pv hM hL ε₂
      have hmul : ((1 - ∑ xz ∈ jointTypicalSet (W_VZ.joint Pv) n ε₂, (jointIidDist (W_VZ.joint Pv) n).pmf xz) +
          ((L - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W_VZ.mutualInfo Pv - 3 * ε₂)))) * log2 (L : ℝ) ≤
          (ε / (4 * R')) * ((n : ℝ) * R') :=
        mul_le_mul heve_err_le hlogL_le hlogL_nonneg (by positivity)
      have hsimp : (ε / (4 * R')) * ((n : ℝ) * R') = (n : ℝ) * (ε / 4) := by
        field_simp [ne_of_gt hR'_pos]
      linarith
    have hfull_mi := wtBin_expected_full_mi_le (n := n) W_VZ Pv hM hL
    have hleak_sum : ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C * wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) ≤
        (n : ℝ) * (3 * ε / 4) := by
      have hrew : ∑ C : Fin M → Fin L → Fin n → V,
          wtBinCodebookProb Pv n M L C * wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) =
          (∑ C : Fin M → Fin L → Fin n → V,
            wtBinCodebookProb Pv n M L C * mutualInfo (wtBinEveFullJoint W_VZ hM hL C)) -
          log2 (L : ℝ) +
          (∑ C : Fin M → Fin L → Fin n → V,
            wtBinCodebookProb Pv n M L C *
              (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m))) := by
        have hid : ∀ C : Fin M → Fin L → Fin n → V,
            wtBinCodebookProb Pv n M L C * wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) =
            wtBinCodebookProb Pv n M L C * mutualInfo (wtBinEveFullJoint W_VZ hM hL C) -
            wtBinCodebookProb Pv n M L C * log2 (L : ℝ) +
            wtBinCodebookProb Pv n M L C *
              (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, condEntropy (wtBinEveBinJoint W_VZ hL C m)) := by
          intro C
          have h := wtBin_eve_leakage_identity W P_XV Pv hM hL ε₁ C
          dsimp only at h; rw [h]; ring
        simp_rw [hid, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          wtBinCodebookProb_sum_one, one_mul]
      rw [hrew]
      have h2_le : (2 : ℝ) ≤ (n : ℝ) * (ε / 4) := by
        have := (div_le_iff₀ hn_r).mp h2n_le; linarith
      have hη_mul : (n : ℝ) * η ≤ (n : ℝ) * (ε / 4) :=
        mul_le_mul_of_nonneg_left hη_le_ε4 (le_of_lt hn_r)
      have hdiff_R : (n : ℝ) * W_VZ.mutualInfo Pv - (n : ℝ) * R' = (n : ℝ) * η := by
        dsimp only [R']; ring
      linarith
    have hleak_div_le : ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C *
          (wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ)) ≤ 3 * ε / 4 := by
      have hdiv : ∑ C : Fin M → Fin L → Fin n → V,
          wtBinCodebookProb Pv n M L C *
            (wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ)) =
          (∑ C : Fin M → Fin L → Fin n → V,
            wtBinCodebookProb Pv n M L C *
              wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C)) / (n : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun C _ => by rw [mul_div_assoc]
      rw [hdiv]
      have h2 := div_le_div_of_nonneg_right hleak_sum (le_of_lt hn_r)
      rwa [mul_div_cancel_left₀ _ (ne_of_gt hn_r)] at h2
    have htot : ∑ C : Fin M → Fin L → Fin n → V,
        wtBinCodebookProb Pv n M L C *
          (wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) +
           wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ)) ≤ ε := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      linarith
    obtain ⟨C, hC⟩ := wt_exists_le_of_weighted_sum_le
      (wtBinCodebookProb Pv n M L)
      (fun C => wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) +
                wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ))
      ε
      (wtBinCodebookProb_nonneg Pv n M L)
      (wtBinCodebookProb_sum_one Pv n M L)
      htot
    have herr0 : 0 ≤ wiretapAvgError W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) :=
      estErrorProb_nonneg _ _
    have hleak0 : 0 ≤ wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ) :=
      div_nonneg (mutualInfo_nonneg _) (le_of_lt hn_r)
    refine ⟨wtBinWiretapCode W P_XV Pv hM hL ε₁ C, by linarith, ?_⟩
    have hdiv_le : wiretapLeakage W hM (wtBinWiretapCode W P_XV Pv hM hL ε₁ C) / (n : ℝ) ≤ ε := by linarith
    have hmul_le := (div_le_iff₀ hn_r).mp hdiv_le
    linarith

/-- **Wiretap Channel Weak-Secrecy Achievability (Wyner 1975; Csiszár–Körner 1978)**:
    every rate `0 ≤ R < wiretapSecrecyCapacity W` is operationally weak-secrecy achievable. -/
theorem wiretap_weak_secrecy_achievability (W : WiretapChannel X Y Z) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : R < wiretapSecrecyCapacity W) :
    IsWiretapWeakAchievable W R := by
  rw [wiretapSecrecyCapacity_eq_sSup] at hR
  have hSne : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
      r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
          mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) }.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Real.sSup_empty] at hR
    linarith
  obtain ⟨r, ⟨kV, Pvx, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne hR
  exact wt_achievable_lt_aux W Pvx hR0 hr

/-- **Wyner–Csiszár–Körner Wiretap Secrecy Capacity Theorem**
    (Wyner 1975; Csiszár & Körner 1978; El Gamal & Kim, Theorem 22.1):
    the operational weak-secrecy capacity of any Discrete Memoryless Wiretap Channel `W`
    equals its single-letter Csiszár–Körner secrecy capacity
    `wiretapSecrecyCapacity W = sup_{V - X - (Y, Z)} [I(V; Y) - I(V; Z)]`. -/
theorem wiretap_secrecy_capacity_theorem (W : WiretapChannel X Y Z) :
    wiretapOperationalCapacity W = wiretapSecrecyCapacity W := by
  by_cases hX : Nonempty X
  · have hSne : { R : ℝ | IsWiretapWeakAchievable W R }.Nonempty :=
      ⟨0, isWiretapWeakAchievable_zero W⟩
    have hSbdd : BddAbove { R : ℝ | IsWiretapWeakAchievable W R } :=
      ⟨wiretapSecrecyCapacity W, fun R hR => wiretap_weak_secrecy_converse W R hR⟩
    have hle : wiretapOperationalCapacity W ≤ wiretapSecrecyCapacity W :=
      csSup_le hSne (fun R hR => wiretap_weak_secrecy_converse W R hR)
    have hge : wiretapSecrecyCapacity W ≤ wiretapOperationalCapacity W := by
      by_contra hlt
      push Not at hlt
      have hop0 : 0 ≤ wiretapOperationalCapacity W :=
        le_csSup hSbdd (isWiretapWeakAchievable_zero W)
      let R : ℝ := (wiretapOperationalCapacity W + wiretapSecrecyCapacity W) / 2
      have hR0 : 0 ≤ R := by dsimp only [R]; linarith
      have hRlt : R < wiretapSecrecyCapacity W := by dsimp only [R]; linarith
      have hgt : wiretapOperationalCapacity W < R := by dsimp only [R]; linarith
      have hach : IsWiretapWeakAchievable W R := wiretap_weak_secrecy_achievability W R hR0 hRlt
      have hRle : R ≤ wiretapOperationalCapacity W := le_csSup hSbdd hach
      linarith
    exact le_antisymm hle hge
  · have hcap_empty : { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
        r = mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.1))) -
            mutualInfo ((wiretapAuxJoint W Pvx).map (fun t => (t.1, t.2.2.2))) } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨kV, Pvx, _⟩; exact hX ⟨(wt_nonempty_of_probDist Pvx).some.2⟩
    have hop_empty : { R : ℝ | IsWiretapWeakAchievable W R } = ∅ := by
      ext R; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hR
      obtain ⟨N, hN⟩ := hR.2 1 zero_lt_one
      obtain ⟨code, _, _⟩ := hN (max N 1) (le_max_left N 1)
      have hMpos : 0 < max 1 (Nat.floor ((2 : ℝ) ^ (((max N 1 : ℕ) : ℝ) * R))) :=
        lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
      have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
      exact hX ⟨(wt_nonempty_of_probDist (code.enc ⟨0, hMpos⟩)).some ⟨0, hn_pos⟩⟩
    rw [wiretapOperationalCapacity, wiretapSecrecyCapacity_eq_sSup, hop_empty, hcap_empty]

end WiretapAchievability

end InfoTheory.Bridge
