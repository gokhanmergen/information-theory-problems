import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding

/-!
# Operational Relay Channel Cut-Set Bound (Cover & Thomas Thm. 15.10.1; El Gamal–Kim Thm. 16.1)

Proves the operational converse for discrete memoryless relay channels directly against
`InfoTheory.Core.Channels.{RelayChannel, IsRelayAchievable, relayCapacity, relayCutsetBound}`:

1. **Causal Relay Block Law (`relayTransSeq`, `relayCodeJoint`, `relayTimeAvgInput`)**:
   - Exact normalization `∑ yr, ∑ y, relayTransSeq W n M enc relay m yr y = 1` by induction on `n`
     via the causal `Fin.snoc` factorization.
   - Joint distribution `relayCodeJoint` of `(M, (Y^n, Y_r^n))` under a uniform message `M ~ Unif(Fin M)`.
   - Time-averaged single-letter input law `relayTimeAvgInput` (`P̄(x, x_r)`).

2. **Broadcast Cut Inequality (`relay_broadcast_cut_le_sum`, `relay_broadcast_cut_single_letter`)**:
   - `I(M; Y^n) ≤ I(M; Y^n, Y_r^n) ≤ ∑_{i : Fin n} I(X_i; Y_i, Y_{r,i} | X_{r,i}) ≤ n · I(X_Q; Y_Q, Y_{r,Q} | X_{r,Q})`.

3. **Multiple-Access (MAC) Cut Inequality (`relay_mac_cut_le_sum`, `relay_mac_cut_single_letter`)**:
   - `I(M; Y^n) ≤ ∑_{i : Fin n} I(X_i, X_{r,i}; Y_i) ≤ n · I(X_Q, X_{r,Q}; Y_Q)` for the **same** `P̄`.

4. **Operational Cut-Set Converse (Cover & Thomas Theorem 15.10.1; El Gamal–Kim Theorem 16.1)**:
   - `relay_code_cutset_converse`: `I(M; Y^n) ≤ n · relayCutsetBound W`.
   - `isRelayAchievable_le_cutsetBound`: `IsRelayAchievable W R → R ≤ relayCutsetBound W`.
   - `relayCapacity_le_cutsetBound`: `relayCapacity W ≤ relayCutsetBound W`.

All theorems are purely additive and leave `Core/`, `Problems/`, `STATEMENT_LOCK.json`,
and `Known/` untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Elementary Entropy, Conditioning, and Time-Sharing Helpers -/

section Helpers

private lemma probDist_ext {α : Type*} [Fintype α] {P Q : ProbDist α}
    (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

private lemma map_equiv_pmf {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : ProbDist α) (b : β) :
    (P.map e).pmf b = P.pmf (e.symm b) := by
  classical
  unfold ProbDist.map
  dsimp only
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ hne
    have : e a ≠ b := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma fst_eq_map_fst {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist (α × β)) :
    P.fst = P.map Prod.fst := by
  classical
  refine probDist_ext fun a => ?_
  unfold ProbDist.fst ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type]
  trans (∑ a' : α, if a' = a then ∑ b : β, P.pmf (a, b) else 0)
  · simp
  · refine Finset.sum_congr rfl fun a' _ => ?_
    by_cases h : a' = a
    · subst h; simp
    · simp [h]

private lemma snd_eq_map_snd {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist (α × β)) :
    P.snd = P.map Prod.snd := by
  classical
  refine probDist_ext fun b => ?_
  unfold ProbDist.snd ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type_right]
  trans (∑ b' : β, if b' = b then ∑ a : α, P.pmf (a, b) else 0)
  · simp
  · refine Finset.sum_congr rfl fun b' _ => ?_
    by_cases h : b' = b
    · subst h; simp
    · simp [h]

/-- **Conditioning Reduces Entropy under Deterministic Processing**:
    `H(X | Y) ≤ H(X | f(Y))`. -/
private lemma condEntropy_map_right_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProbDist (α × β)) (f : β → γ) :
    condEntropy P ≤ condEntropy (P.map (Prod.map id f)) := by
  have hdpi := mutualInfo_map_right_le P f
  have hfst : (P.map (Prod.map id f)).fst = P.fst := by
    rw [fst_eq_map_fst, map_comp_eq, fst_eq_map_fst]
    rfl
  unfold mutualInfo at hdpi
  unfold condEntropy
  rw [hfst] at hdpi
  linarith

private lemma dmcPrecomp_joint_map_in {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (W : DMC β γ) (g : α → β) (P : ProbDist α) :
    ((dmcPrecomp W g).joint P).map (fun ab => (g ab.1, ab.2)) = W.joint (P.map g) := by
  classical
  refine probDist_ext fun ⟨b, c⟩ => ?_
  unfold ProbDist.map DMC.joint dmcPrecomp
  dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single c]
  · by_cases h : g a = b
    · subst h; simp
    · simp [h]
  · intro c' _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma shannonEntropy_unique_zero {α : Type*} [Fintype α] [Unique α] (P : ProbDist α) :
    shannonEntropy P = 0 := by
  have hle := shannonEntropy_le_log2_card P
  have hge := shannonEntropy_nonneg P
  rw [Fintype.card_unique] at hle
  simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
  exact le_antisymm hle hge

private lemma mutualInfo_unique_right {α β : Type*} [Fintype α] [Fintype β] [Unique β]
    (P : ProbDist (α × β)) : mutualInfo P = 0 := by
  have h1 : shannonEntropy P.snd = 0 := shannonEntropy_unique_zero P.snd
  let e : (α × β) ≃ α := Equiv.prodUnique α β
  have h2 : P.fst = P.map e := by
    rw [fst_eq_map_fst]; rfl
  have h3 : shannonEntropy P.fst = shannonEntropy P := by
    rw [h2, shannonEntropy_map_equiv]
  unfold mutualInfo
  linarith

/-- Uniform time-averaged distribution `P̄(a) = (1 / n) ∑_i Q_i(a)`. -/
private noncomputable def uniformTimeAvgDist {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) : ProbDist α where
  pmf := fun a => ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (Q i).pmf a
  nonneg := fun a => mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (Q i).nonneg a)
  sum_one := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(Q _).sum_one]
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    simp [hn_ne]

/-- Joint time-sharing distribution `(Q, A_Q)` with `Q ~ Unif(Fin n)` and `A_Q | (Q = i) ~ Q_i`. -/
private noncomputable def uniformTimeMixDist {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) : ProbDist (Fin n × α) where
  pmf := fun ia => ((1 : ℝ) / (n : ℝ)) * (Q ia.1).pmf ia.2
  nonneg := fun ia => mul_nonneg (by positivity) ((Q ia.1).nonneg ia.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    dsimp only
    simp_rw [← Finset.mul_sum, (Q _).sum_one]
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      one_div_mul_cancel hn_ne]

private lemma uniformTimeMixDist_fst {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) :
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    (uniformTimeMixDist hn Q).fst = ProbDist.uniform := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine probDist_ext fun i => ?_
  unfold ProbDist.fst uniformTimeMixDist ProbDist.uniform
  dsimp only
  rw [← Finset.mul_sum, (Q i).sum_one, mul_one, Fintype.card_fin]

private lemma uniformTimeMixDist_snd {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) :
    (uniformTimeMixDist hn Q).snd = uniformTimeAvgDist hn Q := by
  refine probDist_ext fun a => ?_
  unfold ProbDist.snd uniformTimeMixDist uniformTimeAvgDist
  dsimp only
  rw [← Finset.mul_sum]

private lemma shannonEntropy_uniformTimeMixDist {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) :
    shannonEntropy (uniformTimeMixDist hn Q) =
      log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, shannonEntropy (Q i) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_inv_pos : (0 : ℝ) < (1 : ℝ) / (n : ℝ) := by positivity
  unfold shannonEntropy uniformTimeMixDist
  dsimp only
  rw [Fintype.sum_prod_type]
  have hterm : ∀ i : Fin n, ∑ a : α, negPLogP (((1 : ℝ) / (n : ℝ)) * (Q i).pmf a) =
      ((1 : ℝ) / (n : ℝ)) * (∑ a : α, negPLogP ((Q i).pmf a)) + negPLogP ((1 : ℝ) / (n : ℝ)) := by
    intro i
    simp_rw [negPLogP_mul (le_of_lt hn_inv_pos) ((Q i).nonneg _), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, (Q i).sum_one, one_mul]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlog : ∑ _i : Fin n, negPLogP ((1 : ℝ) / (n : ℝ)) = log2 (n : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold negPLogP
    rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hn_inv_pos)),
      log2_div_pos zero_lt_one hn_pos]
    have hlog1 : log2 1 = 0 := by unfold log2; simp
    rw [hlog1]
    field_simp [ne_of_gt hn_pos]
    ring
  rw [hlog]
  ring

/-- **Concavity of Shannon Entropy under Uniform Time-Sharing**:
    `(1 / n) ∑_i H(Q_i) ≤ H(P̄)`. -/
private lemma avg_shannonEntropy_le_uniformTimeAvg {α : Type*} [Fintype α] {n : ℕ} (hn : 0 < n)
    (Q : Fin n → ProbDist α) :
    ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, shannonEntropy (Q i) ≤
      shannonEntropy (uniformTimeAvgDist hn Q) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let M := uniformTimeMixDist hn Q
  have hce := condEntropy_le_shannonEntropy (M.map Prod.swap)
  unfold condEntropy at hce
  rw [shannonEntropy_swap, fst_map_swap, snd_map_swap] at hce
  have hfst : shannonEntropy M.fst = log2 (n : ℝ) := by
    rw [uniformTimeMixDist_fst hn Q,
      (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin n))).mpr rfl, Fintype.card_fin]
  have hM := shannonEntropy_uniformTimeMixDist hn Q
  have hsnd : M.snd = uniformTimeAvgDist hn Q := uniformTimeMixDist_snd hn Q
  rw [hfst, hM, hsnd] at hce
  linarith

/-- **Concavity of Conditional Entropy under Uniform Time-Sharing**:
    `(1 / n) ∑_i H(A_i | B_i) ≤ H(A_Q | B_Q)`. -/
private lemma avg_condEntropy_le_uniformTimeAvg {α β : Type*} [Fintype α] [Fintype β]
    {n : ℕ} (hn : 0 < n) (Q : Fin n → ProbDist (α × β)) :
    ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, condEntropy (Q i) ≤
      condEntropy (uniformTimeAvgDist hn Q) := by
  let M := uniformTimeMixDist hn Q
  let e : (Fin n × (α × β)) ≃ (α × (β × Fin n)) :=
    { toFun := fun t => (t.2.1, (t.2.2, t.1))
      invFun := fun t => (t.2.2, (t.1, t.2.1))
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  let M' : ProbDist (α × (β × Fin n)) := M.map e
  have hce := condEntropy_map_right_le M' Prod.fst
  have hproj : M'.map (Prod.map id Prod.fst) = uniformTimeAvgDist hn Q := by
    rw [← uniformTimeMixDist_snd hn Q, snd_eq_map_snd]
    dsimp only [M']
    rw [map_comp_eq]
    rfl
  have hM'_ent : shannonEntropy M' =
      log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, shannonEntropy (Q i) := by
    dsimp only [M']
    rw [shannonEntropy_map_equiv, shannonEntropy_uniformTimeMixDist hn Q]
  have hM'_snd : M'.snd = (uniformTimeMixDist hn (fun i => (Q i).snd)).map Prod.swap := by
    classical
    refine probDist_ext fun ⟨b, i⟩ => ?_
    rw [snd_eq_map_snd]
    dsimp only [M']
    rw [map_comp_eq]
    change (M.map (Prod.snd ∘ e)).pmf (b, i) =
      ((uniformTimeMixDist hn (fun i => (Q i).snd)).map (Equiv.prodComm (Fin n) β)).pmf (b, i)
    rw [map_equiv_pmf (Equiv.prodComm (Fin n) β)]
    unfold ProbDist.map uniformTimeMixDist ProbDist.snd
    dsimp only [e, Function.comp_def, Equiv.prodComm]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single b]
      · simp [M, uniformTimeMixDist]
      · intro b' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro i' _ hne
      refine Finset.sum_eq_zero fun ab _ => ?_
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hM'_snd_ent : shannonEntropy M'.snd =
      log2 (n : ℝ) + ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, shannonEntropy (Q i).snd := by
    rw [hM'_snd, shannonEntropy_swap, shannonEntropy_uniformTimeMixDist hn (fun i => (Q i).snd)]
  have hM'_ce : condEntropy M' = ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, condEntropy (Q i) := by
    unfold condEntropy
    rw [hM'_ent, hM'_snd_ent, Finset.sum_sub_distrib]
    ring
  rw [hM'_ce, hproj] at hce
  exact hce

/-- Non-dependent `Fin.snoc` appending a single element to `Fin n → α`. -/
private abbrev snocVec {α : Type*} {n : ℕ} (xs : Fin n → α) (a : α) : Fin (n + 1) → α :=
  Fin.snoc (α := fun _ => α) xs a

/-- Causal `Fin.snoc` equivalence separating the prefix `Fin n` from the last coordinate `Fin.last n`. -/
private def piSnocEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α where
  toFun := fun x => (fun i => x i.castSucc, x (Fin.last n))
  invFun := fun p => snocVec p.1 p.2
  left_inv := fun x => by
    funext i
    refine Fin.lastCases ?_ ?_ i <;> simp [snocVec]
  right_inv := fun ⟨_, _⟩ => Prod.ext (funext fun _ => by simp [snocVec]) (by simp [snocVec])

/-- Equivalence separating `(m, w^{n+1})` into `((m, w^n), w_n)`. -/
private def relaySnocEquiv (M : ℕ) (Y Yr : Type*) (n : ℕ) :
    (Fin M × (Fin (n + 1) → Y × Yr)) ≃ ((Fin M × (Fin n → Y × Yr)) × (Y × Yr)) where
  toFun := fun mw => ((mw.1, fun i => mw.2 i.castSucc), mw.2 (Fin.last n))
  invFun := fun p => (p.1.1, snocVec p.1.2 p.2)
  left_inv := fun ⟨_, _⟩ => by
    refine Prod.ext rfl (funext fun i => ?_)
    refine Fin.lastCases ?_ ?_ i <;> simp [snocVec]
  right_inv := fun ⟨⟨_, _⟩, _⟩ =>
    Prod.ext (Prod.ext rfl (funext fun _ => by simp [snocVec])) (by simp [snocVec])

end Helpers

/-! ### 1. Causal Relay Block Transition Law, Joint Distribution, and Time-Sharing Input -/

section RelayLaw

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- Destination-marginal DMC `p(y | x, x_r) = ∑_{y_r} W(y, y_r | x, x_r)` of a relay channel `W`. -/
def relayYChannel (W : RelayChannel X Xr Y Yr) : DMC (X × Xr) Y where
  trans := fun xxr y => ∑ yr : Yr, W.trans xxr (y, yr)
  nonneg := fun xxr y => Finset.sum_nonneg fun yr _ => W.nonneg xxr (y, yr)
  sum_one := fun xxr => by
    rw [← Fintype.sum_prod_type]
    exact W.sum_one xxr

private lemma relayYChannel_joint_eq (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) :
    (W.joint P).map (fun z => (z.1, z.2.1)) = (relayYChannel W).joint P := by
  classical
  refine probDist_ext fun ⟨xxr, y⟩ => ?_
  unfold ProbDist.map DMC.joint relayYChannel
  dsimp only
  rw [Fintype.sum_prod_type, Finset.sum_eq_single xxr]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
    · simp [Finset.mul_sum]
    · intro y' _ hne
      refine Finset.sum_eq_zero fun yr _ => ?_
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro xxr' _ hne
    refine Finset.sum_eq_zero fun yyr _ => ?_
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Identity expressing `I(X; Y, Y_r | X_r)` for `W.joint P` as `H(Y, Y_r | X_r) - E[H(W(· | X, X_r))]`. -/
private lemma relay_condMutualInfo_eq (W : RelayChannel X Xr Y Yr) (P : ProbDist (X × Xr)) :
    condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))) =
      condEntropy ((W.joint P).map (fun z => (z.2, z.1.2))) -
        ∑ xxr : X × Xr, P.pmf xxr * shannonEntropy (dmcRow W xxr) := by
  let J := W.joint P
  let Q := J.map (fun z => (z.1.1, z.2, z.1.2))
  let eAll : ((X × Xr) × (Y × Yr)) ≃ (X × (Y × Yr) × Xr) :=
    { toFun := fun z => (z.1.1, z.2, z.1.2)
      invFun := fun t => ((t.1, t.2.2), t.2.1)
      left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl }
  have hQ_ent : shannonEntropy Q = shannonEntropy J :=
    shannonEntropy_map_equiv eAll J
  have hQ_xz : Q.map (fun t => (t.1, t.2.2)) = P := by
    calc Q.map (fun t => (t.1, t.2.2))
      _ = J.map Prod.fst := by dsimp only [Q]; rw [map_comp_eq]; rfl
      _ = J.fst := (fst_eq_map_fst J).symm
      _ = P := dmc_joint_fst W P
  have hQ_yz : Q.map (fun t => (t.2.1, t.2.2)) = J.map (fun z => (z.2, z.1.2)) := by
    dsimp only [Q]
    rw [map_comp_eq]
    rfl
  have hQ_z : Q.map (fun t => t.2.2) = (J.map (fun z => (z.2, z.1.2))).snd := by
    rw [snd_eq_map_snd]
    dsimp only [Q]
    rw [map_comp_eq, map_comp_eq]
    rfl
  have hJ_ent : shannonEntropy J =
      shannonEntropy P + ∑ xxr : X × Xr, P.pmf xxr * shannonEntropy (dmcRow W xxr) :=
    dmc_joint_shannonEntropy W P
  unfold condMutualInfo condEntropy
  dsimp only
  change shannonEntropy (Q.map (fun t => (t.1, t.2.2))) +
      shannonEntropy (Q.map (fun t => (t.2.1, t.2.2))) -
      shannonEntropy Q - shannonEntropy (Q.map (fun t => t.2.2)) = _
  rw [hQ_xz, hQ_yz, hQ_ent, hQ_z, hJ_ent]
  ring

/-- Causal `n`-step relay block transition probability `∏_i W(y_i, y_{r,i} | x_i(m), x_{r,i}(y_r^{i-1}))`,
    matching `InfoTheory.Core.Channels.IsRelayAchievable` verbatim. -/
def relayTransSeq (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
    (m : Fin M) (yr : Fin n → Yr) (y : Fin n → Y) : ℝ :=
  ∏ i : Fin n,
    W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)

lemma relayTransSeq_nonneg (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
    (m : Fin M) (yr : Fin n → Yr) (y : Fin n → Y) :
    0 ≤ relayTransSeq W n M enc relay m yr y :=
  Finset.prod_nonneg fun _ _ => W.nonneg _ _

/-- Causal one-step `Fin.snoc` factorization of `relayTransSeq`. -/
private lemma relayTransSeq_snoc (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (enc : Fin M → Fin (n + 1) → X) (relay : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr)
    (m : Fin M) (w_init : Fin n → Y × Yr) (w_last : Y × Yr) :
    relayTransSeq W (n + 1) M enc relay m
        (fun i => (snocVec w_init w_last i).2)
        (fun i => (snocVec w_init w_last i).1) =
      relayTransSeq W n M (fun m' i => enc m' i.castSucc) (fun i => relay i.castSucc) m
          (fun i => (w_init i).2) (fun i => (w_init i).1) *
        W.trans (enc m (Fin.last n), relay (Fin.last n) (fun j => (w_init j).2)) w_last := by
  unfold relayTransSeq
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    congr 1
    · congr 2
      funext j
      have hidx : (⟨j.1, Nat.lt_trans j.2 i.castSucc.2⟩ : Fin (n + 1)) =
          (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n).castSucc := Fin.ext rfl
      rw [hidx, snocVec, Fin.snoc_castSucc]
    · simp [snocVec]
  · dsimp only
    congr 1
    · congr 2
      funext j
      have hidx : (⟨j.1, Nat.lt_trans j.2 (Fin.last n).2⟩ : Fin (n + 1)) = j.castSucc :=
        Fin.ext rfl
      rw [hidx, snocVec, Fin.snoc_castSucc]
    · simp [snocVec]

/-- Normalization of `relayTransSeq` summed over `Fin n → Y × Yr`. -/
theorem relayTransSeq_sum_one_prod (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) (m : Fin M) :
    ∑ w : Fin n → Y × Yr,
      relayTransSeq W n M enc relay m (fun i => (w i).2) (fun i => (w i).1) = 1 := by
  induction n with
  | zero =>
    simp [relayTransSeq]
  | succ n ih =>
    have hreidx := Fintype.sum_equiv (piSnocEquiv (Y × Yr) n).symm
      (fun p : (Fin n → Y × Yr) × (Y × Yr) =>
        relayTransSeq W (n + 1) M enc relay m
          (fun i => (snocVec p.1 p.2 i).2) (fun i => (snocVec p.1 p.2 i).1))
      (fun w : Fin (n + 1) → Y × Yr =>
        relayTransSeq W (n + 1) M enc relay m (fun i => (w i).2) (fun i => (w i).1))
      (fun _ => rfl)
    rw [← hreidx, Fintype.sum_prod_type]
    simp_rw [relayTransSeq_snoc, ← Finset.mul_sum, W.sum_one, mul_one]
    exact ih (fun m' i => enc m' i.castSucc) (fun i => relay i.castSucc)

/-- Normalization of `relayTransSeq` summed over `(y_r^n, y^n)`. -/
theorem relayTransSeq_sum_one (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) (m : Fin M) :
    ∑ yr : Fin n → Yr, ∑ y : Fin n → Y, relayTransSeq W n M enc relay m yr y = 1 := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type (f := fun yyr : (Fin n → Y) × (Fin n → Yr) =>
    relayTransSeq W n M enc relay m yyr.2 yyr.1)]
  have hreidx := Fintype.sum_equiv (zipEquiv Y Yr n)
    (fun yyr : (Fin n → Y) × (Fin n → Yr) => relayTransSeq W n M enc relay m yyr.2 yyr.1)
    (fun w : Fin n → Y × Yr =>
      relayTransSeq W n M enc relay m (fun i => (w i).2) (fun i => (w i).1))
    (fun _ => rfl)
  rw [hreidx]
  exact relayTransSeq_sum_one_prod W n M enc relay m

/-- Joint probability distribution of `(M, (Y^n, Y_r^n))` induced by a uniform message
    `M ~ Unif(Fin M)` and causal relay code `(enc, relay)`. -/
noncomputable def relayCodeJoint (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    ProbDist (Fin M × (Fin n → Y × Yr)) where
  pmf := fun mw => ((1 : ℝ) / (M : ℝ)) *
    relayTransSeq W n M enc relay mw.1 (fun i => (mw.2 i).2) (fun i => (mw.2 i).1)
  nonneg := fun mw => mul_nonneg (by positivity) (relayTransSeq_nonneg W n M enc relay _ _ _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    dsimp only
    simp_rw [← Finset.mul_sum, relayTransSeq_sum_one_prod]
    have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      one_div_mul_cancel hM_ne]

/-- Causal channel input pair `(X_i, X_{r,i})` at time `i : Fin n` as a function of `(m, (y^n, y_r^n))`. -/
def relayInputAt {n M : ℕ} (enc : Fin M → Fin n → X)
    (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) (i : Fin n) :
    Fin M × (Fin n → Y × Yr) → X × Xr :=
  fun mw => (enc mw.1 i, relay i (fun j => (mw.2 ⟨j.1, Nat.lt_trans j.2 i.2⟩).2))

/-- Time-averaged single-letter input distribution `P̄(x, x_r)` of a causal relay code. -/
noncomputable def relayTimeAvgInput (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (hn : 0 < n) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    ProbDist (X × Xr) :=
  uniformTimeAvgDist hn fun i =>
    (relayCodeJoint W n M hM enc relay).map (relayInputAt enc relay i)

private lemma relayCodeJoint_fst (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    (relayCodeJoint W n M hM enc relay).fst = ProbDist.uniform := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  refine probDist_ext fun m => ?_
  unfold ProbDist.fst relayCodeJoint ProbDist.uniform
  dsimp only
  rw [← Finset.mul_sum, relayTransSeq_sum_one_prod, mul_one, Fintype.card_fin]

/-- Causal one-step Markov factorization of `relayCodeJoint` at `n + 1`:
    `(M, W^{n+1}) ≃ ((M, W^n), W_n)` with `W_n | (M, W^n) ~ W(· | enc(M, n), relay_n(Y_r^n))`. -/
private lemma relayCodeJoint_snoc (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin (n + 1) → X) (relay : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr) :
    (relayCodeJoint W (n + 1) M hM enc relay).map (relaySnocEquiv M Y Yr n) =
      (dmcPrecomp W (fun mw : Fin M × (Fin n → Y × Yr) =>
        (enc mw.1 (Fin.last n), relay (Fin.last n) (fun j => (mw.2 j).2)))).joint
        (relayCodeJoint W n M hM (fun m i => enc m i.castSucc) (fun i => relay i.castSucc)) := by
  refine probDist_ext fun ⟨⟨m, w_init⟩, w_last⟩ => ?_
  rw [map_equiv_pmf (relaySnocEquiv M Y Yr n)]
  change ((1 : ℝ) / (M : ℝ)) *
      relayTransSeq W (n + 1) M enc relay m
        (fun i => (snocVec w_init w_last i).2) (fun i => (snocVec w_init w_last i).1) =
    (((1 : ℝ) / (M : ℝ)) *
      relayTransSeq W n M (fun m' i => enc m' i.castSucc) (fun i => relay i.castSucc) m
        (fun i => (w_init i).2) (fun i => (w_init i).1)) *
      W.trans (enc m (Fin.last n), relay (Fin.last n) (fun j => (w_init j).2)) w_last
  rw [relayTransSeq_snoc]
  ring

/-- Prefix marginal of `relayCodeJoint` at `n + 1` is `relayCodeJoint` at `n`. -/
private lemma relayCodeJoint_prefix (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin (n + 1) → X) (relay : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr) :
    (relayCodeJoint W (n + 1) M hM enc relay).map (fun mw => (mw.1, fun i : Fin n => mw.2 i.castSucc)) =
      relayCodeJoint W n M hM (fun m i => enc m i.castSucc) (fun i => relay i.castSucc) := by
  have hfst := congrArg ProbDist.fst (relayCodeJoint_snoc W n M hM enc relay)
  rw [dmc_joint_fst, fst_eq_map_fst, map_comp_eq] at hfst
  exact hfst

/-- Input marginal at any prefix coordinate `i.castSucc` agrees with the `n`-step code. -/
private lemma relayCodeJoint_inputAt_castSucc (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin (n + 1) → X) (relay : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr)
    (i : Fin n) :
    (relayCodeJoint W (n + 1) M hM enc relay).map (relayInputAt enc relay i.castSucc) =
      (relayCodeJoint W n M hM (fun m j => enc m j.castSucc) (fun j => relay j.castSucc)).map
        (relayInputAt (fun m j => enc m j.castSucc) (fun j => relay j.castSucc) i) := by
  rw [← relayCodeJoint_prefix W n M hM enc relay, map_comp_eq]
  rfl

/-- Input marginal at the final coordinate `Fin.last n`. -/
private lemma relayCodeJoint_inputAt_last (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin (n + 1) → X) (relay : ∀ i : Fin (n + 1), (Fin i.1 → Yr) → Xr) :
    (relayCodeJoint W (n + 1) M hM enc relay).map (relayInputAt enc relay (Fin.last n)) =
      (relayCodeJoint W n M hM (fun m j => enc m j.castSucc) (fun j => relay j.castSucc)).map
        (fun mw => (enc mw.1 (Fin.last n), relay (Fin.last n) (fun j => (mw.2 j).2))) := by
  rw [← relayCodeJoint_prefix W n M hM enc relay, map_comp_eq]
  rfl

end RelayLaw

/-! ### 2. Cut-Set Bound Properties (`BddAbove`, Nonnegativity) -/

section CutsetProperties

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- The set of single-letter cut-set values over all `P ∈ Δ(X × X_r)` is bounded above. -/
theorem relayCutsetBound_bddAbove (W : RelayChannel X Xr Y Yr) :
    BddAbove { r : ℝ | ∃ P : ProbDist (X × Xr),
      let J := W.joint P
      let I_X_YYr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2)))
      let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
      r = min I_X_YYr_given_Xr I_XXr_Y } := by
  by_cases hne : Nonempty (X × Xr)
  · refine ⟨log2 (Fintype.card (X × Xr) : ℝ), ?_⟩
    rintro r ⟨P, rfl⟩
    refine le_trans (min_le_right _ _) ?_
    rw [relayYChannel_joint_eq]
    unfold mutualInfo
    have hce : 0 ≤ condEntropy ((relayYChannel W).joint P) :=
      condEntropy_nonneg ((relayYChannel W).joint P)
    unfold condEntropy at hce
    have hent : shannonEntropy ((relayYChannel W).joint P).fst ≤
        log2 (Fintype.card (X × Xr) : ℝ) :=
      shannonEntropy_le_log2_card _
    linarith
  · refine ⟨0, ?_⟩
    rintro r ⟨P, rfl⟩
    exfalso
    have h0 : ∑ a : X × Xr, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (hne ⟨a⟩).elim
    linarith [P.sum_one]

/-- Any single-letter input distribution `P ∈ Δ(X × X_r)` yields a lower bound on `relayCutsetBound W`. -/
private lemma min_cutset_le_relayCutsetBound (W : RelayChannel X Xr Y Yr)
    (P : ProbDist (X × Xr)) :
    min (condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))))
        (mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1)))) ≤
      relayCutsetBound W :=
  le_csSup (relayCutsetBound_bddAbove W) ⟨P, rfl⟩

/-- The relay cut-set bound is nonnegative whenever the input alphabets are nonempty. -/
theorem relayCutsetBound_nonneg [Nonempty X] [Nonempty Xr] (W : RelayChannel X Xr Y Yr) :
    0 ≤ relayCutsetBound W := by
  let P : ProbDist (X × Xr) := ProbDist.uniform
  have h1 : 0 ≤ condMutualInfo ((W.joint P).map (fun z => (z.1.1, z.2, z.1.2))) :=
    condMutualInfo_nonneg _
  have h2 : 0 ≤ mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) :=
    mutualInfo_nonneg _
  exact le_trans (le_min h1 h2) (min_cutset_le_relayCutsetBound W P)

end CutsetProperties

/-! ### 3. Broadcast Cut Inequality (`I(M; Y^n, Y_r^n) ≤ ∑ I(X_i; Y_i, Y_{r,i} | X_{r,i}) ≤ n I_BC(P̄)`) -/

section BroadcastCut

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- **Broadcast Cut Multi-Letter Bound**:
    `I(M; Y^n, Y_r^n) ≤ ∑_{i : Fin n} I(X_i; Y_i, Y_{r,i} | X_{r,i})`. -/
theorem relay_broadcast_cut_le_sum (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    mutualInfo (relayCodeJoint W n M hM enc relay) ≤
      ∑ i : Fin n,
        condMutualInfo ((W.joint ((relayCodeJoint W n M hM enc relay).map (relayInputAt enc relay i))).map
          (fun z => (z.1.1, z.2, z.1.2))) := by
  induction n with
  | zero =>
    rw [mutualInfo_unique_right]
    simp
  | succ n ih =>
    let encInit : Fin M → Fin n → X := fun m i => enc m i.castSucc
    let relayInit : ∀ i : Fin n, (Fin i.1 → Yr) → Xr := fun i => relay i.castSucc
    let P_full := relayCodeJoint W (n + 1) M hM enc relay
    let P_init := relayCodeJoint W n M hM encInit relayInit
    let g_last : Fin M × (Fin n → Y × Yr) → X × Xr :=
      fun mw => (enc mw.1 (Fin.last n), relay (Fin.last n) (fun j => (mw.2 j).2))
    let P_last : ProbDist (X × Xr) := P_init.map g_last
    have hsnoc : P_full.map (relaySnocEquiv M Y Yr n) = (dmcPrecomp W g_last).joint P_init :=
      relayCodeJoint_snoc W n M hM enc relay
    have hpref : P_full.map (fun mw => (mw.1, fun i : Fin n => mw.2 i.castSucc)) = P_init :=
      relayCodeJoint_prefix W n M hM enc relay
    -- Step 1: `H(P_full) - H(P_init) = ∑ P_last(x, xr) H(W(· | x, xr))`
    have hH_joint : shannonEntropy P_full =
        shannonEntropy P_init + ∑ xxr : X × Xr, P_last.pmf xxr * shannonEntropy (dmcRow W xxr) := by
      rw [← shannonEntropy_map_equiv (relaySnocEquiv M Y Yr n) P_full, hsnoc,
        dmc_joint_shannonEntropy]
      congr 1
      exact sum_pmf_mul_comp P_init g_last (fun xxr => shannonEntropy (dmcRow W xxr))
    -- Step 2: `H(W^{n+1}) - H(W^n) ≤ H(W_n | X_{r,n})`
    let eW : (Fin (n + 1) → Y × Yr) ≃ ((Y × Yr) × (Fin n → Y × Yr)) :=
      (piSnocEquiv (Y × Yr) n).trans (Equiv.prodComm (Fin n → Y × Yr) (Y × Yr))
    let Q_w : ProbDist ((Y × Yr) × (Fin n → Y × Yr)) := P_full.snd.map eW
    have hQw_ent : shannonEntropy Q_w = shannonEntropy P_full.snd :=
      shannonEntropy_map_equiv eW P_full.snd
    have hQw_snd : Q_w.snd = P_init.snd := by
      calc Q_w.snd
        _ = P_full.map (fun mw => fun i : Fin n => mw.2 i.castSucc) := by
            rw [snd_eq_map_snd]; dsimp only [Q_w]
            rw [snd_eq_map_snd, map_comp_eq, map_comp_eq]; rfl
        _ = (P_full.map (fun mw => (mw.1, fun i : Fin n => mw.2 i.castSucc))).map Prod.snd := by
            rw [map_comp_eq]; rfl
        _ = P_init.snd := by rw [hpref, ← snd_eq_map_snd]
    let fXr : (Fin n → Y × Yr) → Xr := fun w_init => relay (Fin.last n) (fun j => (w_init j).2)
    have hQw_cond : condEntropy Q_w ≤ condEntropy (Q_w.map (Prod.map id fXr)) :=
      condEntropy_map_right_le Q_w fXr
    have hQw_proj : Q_w.map (Prod.map id fXr) = (W.joint P_last).map (fun z => (z.2, z.1.2)) := by
      calc Q_w.map (Prod.map id fXr)
        _ = (P_full.map (relaySnocEquiv M Y Yr n)).map (fun z => (z.2, (g_last z.1).2)) := by
            dsimp only [Q_w]; rw [snd_eq_map_snd, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
        _ = ((dmcPrecomp W g_last).joint P_init).map (fun z => (z.2, (g_last z.1).2)) := by
            rw [hsnoc]
        _ = (((dmcPrecomp W g_last).joint P_init).map (fun z => (g_last z.1, z.2))).map
              (fun z => (z.2, z.1.2)) := by
            rw [map_comp_eq]; rfl
        _ = (W.joint P_last).map (fun z => (z.2, z.1.2)) := by
            rw [dmcPrecomp_joint_map_in]
    have hH_snd : shannonEntropy P_full.snd - shannonEntropy P_init.snd ≤
        condEntropy ((W.joint P_last).map (fun z => (z.2, z.1.2))) := by
      unfold condEntropy at hQw_cond
      rw [hQw_ent, hQw_snd, hQw_proj] at hQw_cond
      exact hQw_cond
    -- Step 3: Cancel `H(M)` and combine with IH
    have hfst_eq : P_full.fst = P_init.fst := by
      have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
      rw [relayCodeJoint_fst W (n + 1) M hM enc relay, relayCodeJoint_fst W n M hM encInit relayInit]
    have hstep : mutualInfo P_full - mutualInfo P_init ≤
        condMutualInfo ((W.joint P_last).map (fun z => (z.1.1, z.2, z.1.2))) := by
      rw [relay_condMutualInfo_eq]
      unfold mutualInfo
      rw [hfst_eq, hH_joint]
      linarith
    have hih := ih encInit relayInit
    change mutualInfo P_full ≤
      ∑ i : Fin (n + 1),
        condMutualInfo ((W.joint (P_full.map (relayInputAt enc relay i))).map
          (fun z => (z.1.1, z.2, z.1.2)))
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ i : Fin n,
        P_full.map (relayInputAt enc relay i.castSucc) = P_init.map (relayInputAt encInit relayInit i) :=
      fun i => relayCodeJoint_inputAt_castSucc W n M hM enc relay i
    have hlast : P_full.map (relayInputAt enc relay (Fin.last n)) = P_last :=
      relayCodeJoint_inputAt_last W n M hM enc relay
    simp_rw [hcast, hlast]
    linarith

/-- **Broadcast Cut Single-Letter Bound (Time-Sharing Concavity)**:
    `I(M; Y^n) ≤ n · I(X_Q; Y_Q, Y_{r,Q} | X_{r,Q})` under `P̄ = relayTimeAvgInput`. -/
theorem relay_broadcast_cut_single_letter (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (hn : 0 < n) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    mutualInfo ((relayCodeJoint W n M hM enc relay).map (fun mw => (mw.1, fun i => (mw.2 i).1))) ≤
      (n : ℝ) * condMutualInfo
        ((W.joint (relayTimeAvgInput W n M hn hM enc relay)).map (fun z => (z.1.1, z.2, z.1.2))) := by
  let P_full := relayCodeJoint W n M hM enc relay
  let Pi : Fin n → ProbDist (X × Xr) := fun i => P_full.map (relayInputAt enc relay i)
  let Pbar : ProbDist (X × Xr) := relayTimeAvgInput W n M hn hM enc relay
  -- Step 1: DPI `I(M; Y^n) ≤ I(M; Y^n, Y_r^n)`
  have hdpi : mutualInfo (P_full.map (fun mw => (mw.1, fun i => (mw.2 i).1))) ≤
      mutualInfo P_full := by
    have heq : P_full.map (fun mw => (mw.1, fun i => (mw.2 i).1)) =
        P_full.map (Prod.map id (fun w (i : Fin n) => (w i).1)) := rfl
    rw [heq]
    exact mutualInfo_map_right_le P_full (fun w (i : Fin n) => (w i).1)
  -- Step 2: Multi-letter sum bound
  have hsum := relay_broadcast_cut_le_sum W n M hM enc relay
  -- Step 3: Time-sharing concavity of `I(X; Y, Y_r | X_r)`
  let Qi : Fin n → ProbDist ((Y × Yr) × Xr) :=
    fun i => (W.joint (Pi i)).map (fun z => (z.2, z.1.2))
  have hQavg : uniformTimeAvgDist hn Qi = (W.joint Pbar).map (fun z => (z.2, z.1.2)) := by
    classical
    refine probDist_ext fun ⟨w, xr⟩ => ?_
    unfold uniformTimeAvgDist Qi ProbDist.map DMC.joint Pbar relayTimeAvgInput
    dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs
    · rw [← Finset.sum_mul]
      change ((1 : ℝ) / (n : ℝ)) * ((∑ i : Fin n, (Pi i).pmf z.1) * W.trans z.1 z.2) =
        (((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (Pi i).pmf z.1) * W.trans z.1 z.2
      ring
    · simp
  have hce_conc := avg_condEntropy_le_uniformTimeAvg hn Qi
  rw [hQavg] at hce_conc
  have hlin : ((1 : ℝ) / (n : ℝ)) *
      ∑ i : Fin n, ∑ xxr : X × Xr, (Pi i).pmf xxr * shannonEntropy (dmcRow W xxr) =
      ∑ xxr : X × Xr, Pbar.pmf xxr * shannonEntropy (dmcRow W xxr) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun xxr _ => ?_
    rw [← Finset.sum_mul]
    unfold Pbar relayTimeAvgInput uniformTimeAvgDist
    dsimp only
    ring
  have havg_cmi : ((1 : ℝ) / (n : ℝ)) *
      ∑ i : Fin n, condMutualInfo ((W.joint (Pi i)).map (fun z => (z.1.1, z.2, z.1.2))) ≤
      condMutualInfo ((W.joint Pbar).map (fun z => (z.1.1, z.2, z.1.2))) := by
    simp_rw [relay_condMutualInfo_eq]
    rw [Finset.sum_sub_distrib, mul_sub, hlin]
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul := mul_le_mul_of_nonneg_left havg_cmi (le_of_lt hn_pos)
  rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hn_pos), one_mul] at hmul
  exact le_trans hdpi (le_trans hsum hmul)

end BroadcastCut

/-! ### 4. Multiple-Access (MAC) Cut Inequality (`I(M; Y^n) ≤ ∑ I(X_i, X_{r,i}; Y_i) ≤ n I_MAC(P̄)`) -/

section MACCut

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- **MAC Cut Multi-Letter Bound**:
    `I(M; Y^n) ≤ ∑_{i : Fin n} I(X_i, X_{r,i}; Y_i)`. -/
theorem relay_mac_cut_le_sum (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    mutualInfo ((relayCodeJoint W n M hM enc relay).map (fun mw => (mw.1, fun i => (mw.2 i).1))) ≤
      ∑ i : Fin n,
        mutualInfo ((W.joint ((relayCodeJoint W n M hM enc relay).map (relayInputAt enc relay i))).map
          (fun z => (z.1, z.2.1))) := by
  induction n with
  | zero =>
    rw [mutualInfo_unique_right]
    simp
  | succ n ih =>
    let V := relayYChannel W
    let encInit : Fin M → Fin n → X := fun m i => enc m i.castSucc
    let relayInit : ∀ i : Fin n, (Fin i.1 → Yr) → Xr := fun i => relay i.castSucc
    let P_full := relayCodeJoint W (n + 1) M hM enc relay
    let P_init := relayCodeJoint W n M hM encInit relayInit
    let P_full_Y : ProbDist (Fin M × (Fin (n + 1) → Y)) :=
      P_full.map (fun mw => (mw.1, fun i => (mw.2 i).1))
    let P_init_Y : ProbDist (Fin M × (Fin n → Y)) :=
      P_init.map (fun mw => (mw.1, fun i => (mw.2 i).1))
    let g_last : Fin M × (Fin n → Y × Yr) → X × Xr :=
      fun mw => (enc mw.1 (Fin.last n), relay (Fin.last n) (fun j => (mw.2 j).2))
    let P_last : ProbDist (X × Xr) := P_init.map g_last
    have hsnoc : P_full.map (relaySnocEquiv M Y Yr n) = (dmcPrecomp W g_last).joint P_init :=
      relayCodeJoint_snoc W n M hM enc relay
    have hpref : P_full.map (fun mw => (mw.1, fun i : Fin n => mw.2 i.castSucc)) = P_init :=
      relayCodeJoint_prefix W n M hM enc relay
    -- Step 1: `H(Y^{n+1}) ≤ H(Y^n) + H(Y_n)`
    let eY : (Fin (n + 1) → Y) ≃ ((Fin n → Y) × Y) := piSnocEquiv Y n
    have hsub := shannonEntropy_subadd (P_full_Y.snd.map eY)
    have hY_ent : shannonEntropy (P_full_Y.snd.map eY) = shannonEntropy P_full_Y.snd :=
      shannonEntropy_map_equiv eY P_full_Y.snd
    have hY_fst : (P_full_Y.snd.map eY).fst = P_init_Y.snd := by
      calc (P_full_Y.snd.map eY).fst
        _ = (P_full.map (fun mw => (mw.1, fun i : Fin n => mw.2 i.castSucc))).map
              (fun mw => fun i => (mw.2 i).1) := by
            rw [fst_eq_map_fst, snd_eq_map_snd]; dsimp only [P_full_Y]
            rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
        _ = P_init_Y.snd := by
            rw [hpref, snd_eq_map_snd]; dsimp only [P_init_Y]; rw [map_comp_eq]; rfl
    have hY_snd : (P_full_Y.snd.map eY).snd = (V.joint P_last).snd := by
      calc (P_full_Y.snd.map eY).snd
        _ = (P_full.map (relaySnocEquiv M Y Yr n)).map (fun z => z.2.1) := by
            rw [snd_eq_map_snd, snd_eq_map_snd]; dsimp only [P_full_Y]
            rw [map_comp_eq, map_comp_eq, map_comp_eq, map_comp_eq]; rfl
        _ = ((dmcPrecomp W g_last).joint P_init).map (fun z => z.2.1) := by
            rw [hsnoc]
        _ = (((dmcPrecomp W g_last).joint P_init).map (fun z => (g_last z.1, z.2))).map
              (fun z => z.2.1) := by
            rw [map_comp_eq]; rfl
        _ = (W.joint P_last).map (fun z => z.2.1) := by
            rw [dmcPrecomp_joint_map_in]
        _ = (V.joint P_last).snd := by
            rw [snd_eq_map_snd, ← relayYChannel_joint_eq W P_last, map_comp_eq]; rfl
    have hH_Y : shannonEntropy P_full_Y.snd - shannonEntropy P_init_Y.snd ≤
        shannonEntropy (V.joint P_last).snd := by
      rw [hY_ent, hY_fst, hY_snd] at hsub
      linarith
    -- Step 2: `H(M, Y^{n+1}) - H(M, Y^n) = H(Y_n | M, Y^n) ≥ H(Y_n | M, W^n) = ∑ P_last H(V)`
    let eMY : (Fin M × (Fin (n + 1) → Y)) ≃ (Y × (Fin M × (Fin n → Y))) :=
      { toFun := fun my => (my.2 (Fin.last n), (my.1, fun i => my.2 i.castSucc))
        invFun := fun p => (p.2.1, snocVec p.2.2 p.1)
        left_inv := fun ⟨_, _⟩ => by
          refine Prod.ext rfl (funext fun i => ?_)
          refine Fin.lastCases ?_ ?_ i <;> simp [snocVec]
        right_inv := fun ⟨_, ⟨_, _⟩⟩ =>
          Prod.ext (by simp [snocVec]) (Prod.ext rfl (funext fun _ => by simp [snocVec])) }
    let Q_my : ProbDist (Y × (Fin M × (Fin n → Y))) := P_full_Y.map eMY
    let Q_mw : ProbDist (Y × (Fin M × (Fin n → Y × Yr))) :=
      P_full.map (fun mw => ((mw.2 (Fin.last n)).1, (mw.1, fun i => mw.2 i.castSucc)))
    have hQmy_ent : shannonEntropy Q_my = shannonEntropy P_full_Y :=
      shannonEntropy_map_equiv eMY P_full_Y
    have hQmy_snd : Q_my.snd = P_init_Y := by
      calc Q_my.snd
        _ = (P_full.map (fun mw => (mw.1, fun i : Fin n => mw.2 i.castSucc))).map
              (fun mw => (mw.1, fun i => (mw.2 i).1)) := by
            rw [snd_eq_map_snd]; dsimp only [Q_my, P_full_Y]
            rw [map_comp_eq, map_comp_eq, map_comp_eq]; rfl
        _ = P_init_Y := by rw [hpref]
    have hQmy_eq : Q_my = Q_mw.map (Prod.map id (fun mw => (mw.1, fun i => (mw.2 i).1))) := by
      dsimp only [Q_my, Q_mw, P_full_Y]
      rw [map_comp_eq, map_comp_eq]
      rfl
    have hcond_le : condEntropy Q_mw ≤ condEntropy Q_my := by
      rw [hQmy_eq]
      exact condEntropy_map_right_le Q_mw (fun mw => (mw.1, fun i => (mw.2 i).1))
    have hQmw_swap : Q_mw.map Prod.swap = (dmcPrecomp V g_last).joint P_init := by
      have h1 : Q_mw.map Prod.swap =
          (P_full.map (relaySnocEquiv M Y Yr n)).map (fun z => (z.1, z.2.1)) := by
        dsimp only [Q_mw]
        rw [map_comp_eq, map_comp_eq]
        rfl
      rw [h1, hsnoc]
      classical
      refine probDist_ext fun ⟨mw, y⟩ => ?_
      unfold ProbDist.map DMC.joint dmcPrecomp V relayYChannel
      dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single mw]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
        · simp [Finset.mul_sum]
        · intro y' _ hne
          refine Finset.sum_eq_zero fun yr _ => ?_
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro mw' _ hne
        refine Finset.sum_eq_zero fun yyr _ => ?_
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hQmw_ce : condEntropy Q_mw =
        ∑ xxr : X × Xr, P_last.pmf xxr * shannonEntropy (dmcRow V xxr) := by
      have h_ent : shannonEntropy Q_mw = shannonEntropy ((dmcPrecomp V g_last).joint P_init) := by
        rw [← shannonEntropy_swap Q_mw, hQmw_swap]
      have h_snd : Q_mw.snd = P_init := by
        rw [← fst_map_swap Q_mw, hQmw_swap, dmc_joint_fst]
      have hrow : ∀ x, dmcRow (dmcPrecomp V g_last) x = dmcRow V (g_last x) := fun _ => rfl
      unfold condEntropy
      rw [h_ent, h_snd, dmc_joint_shannonEntropy]
      simp_rw [hrow]
      rw [sum_pmf_mul_comp P_init g_last (fun xxr => shannonEntropy (dmcRow V xxr))]
      ring
    have hH_MY : ∑ xxr : X × Xr, P_last.pmf xxr * shannonEntropy (dmcRow V xxr) ≤
        shannonEntropy P_full_Y - shannonEntropy P_init_Y := by
      rw [hQmw_ce] at hcond_le
      unfold condEntropy at hcond_le
      rw [hQmy_ent, hQmy_snd] at hcond_le
      exact hcond_le
    -- Step 3: Cancel `H(M)` and combine with IH
    have hfst_eq : P_full_Y.fst = P_init_Y.fst := by
      have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
      have h1 : P_full_Y.fst = P_full.fst := by
        rw [fst_eq_map_fst, fst_eq_map_fst]
        dsimp only [P_full_Y]
        rw [map_comp_eq]; rfl
      have h2 : P_init_Y.fst = P_init.fst := by
        rw [fst_eq_map_fst, fst_eq_map_fst]
        dsimp only [P_init_Y]
        rw [map_comp_eq]; rfl
      rw [h1, h2, relayCodeJoint_fst W (n + 1) M hM enc relay,
        relayCodeJoint_fst W n M hM encInit relayInit]
    have hmi_V : mutualInfo (V.joint P_last) =
        shannonEntropy (V.joint P_last).snd -
          ∑ xxr : X × Xr, P_last.pmf xxr * shannonEntropy (dmcRow V xxr) := by
      unfold mutualInfo
      rw [dmc_joint_fst, dmc_joint_shannonEntropy]
      ring
    have hstep : mutualInfo P_full_Y - mutualInfo P_init_Y ≤
        mutualInfo ((W.joint P_last).map (fun z => (z.1, z.2.1))) := by
      rw [relayYChannel_joint_eq]
      change mutualInfo P_full_Y - mutualInfo P_init_Y ≤ mutualInfo (V.joint P_last)
      rw [hmi_V]
      unfold mutualInfo
      rw [hfst_eq]
      linarith
    have hih := ih encInit relayInit
    change mutualInfo P_full_Y ≤
      ∑ i : Fin (n + 1),
        mutualInfo ((W.joint (P_full.map (relayInputAt enc relay i))).map (fun z => (z.1, z.2.1)))
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ i : Fin n,
        P_full.map (relayInputAt enc relay i.castSucc) = P_init.map (relayInputAt encInit relayInit i) :=
      fun i => relayCodeJoint_inputAt_castSucc W n M hM enc relay i
    have hlast : P_full.map (relayInputAt enc relay (Fin.last n)) = P_last :=
      relayCodeJoint_inputAt_last W n M hM enc relay
    simp_rw [hcast, hlast]
    linarith

/-- **MAC Cut Single-Letter Bound (Time-Sharing Concavity)**:
    `I(M; Y^n) ≤ n · I(X_Q, X_{r,Q}; Y_Q)` under the **same** `P̄ = relayTimeAvgInput`. -/
theorem relay_mac_cut_single_letter (W : RelayChannel X Xr Y Yr) (n M : ℕ)
    (hn : 0 < n) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    mutualInfo ((relayCodeJoint W n M hM enc relay).map (fun mw => (mw.1, fun i => (mw.2 i).1))) ≤
      (n : ℝ) * mutualInfo
        ((W.joint (relayTimeAvgInput W n M hn hM enc relay)).map (fun z => (z.1, z.2.1))) := by
  let V := relayYChannel W
  let P_full := relayCodeJoint W n M hM enc relay
  let Pi : Fin n → ProbDist (X × Xr) := fun i => P_full.map (relayInputAt enc relay i)
  let Pbar : ProbDist (X × Xr) := relayTimeAvgInput W n M hn hM enc relay
  have hsum := relay_mac_cut_le_sum W n M hM enc relay
  let Yi : Fin n → ProbDist Y := fun i => (V.joint (Pi i)).snd
  have hYavg : uniformTimeAvgDist hn Yi = (V.joint Pbar).snd := by
    refine probDist_ext fun y => ?_
    unfold uniformTimeAvgDist Yi ProbDist.snd DMC.joint Pbar relayTimeAvgInput
    dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun xxr _ => ?_
    rw [← Finset.sum_mul]
    change ((1 : ℝ) / (n : ℝ)) * ((∑ i : Fin n, (Pi i).pmf xxr) * V.trans xxr y) =
      (((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (Pi i).pmf xxr) * V.trans xxr y
    ring
  have hH_conc := avg_shannonEntropy_le_uniformTimeAvg hn Yi
  rw [hYavg] at hH_conc
  have hlin : ((1 : ℝ) / (n : ℝ)) *
      ∑ i : Fin n, ∑ xxr : X × Xr, (Pi i).pmf xxr * shannonEntropy (dmcRow V xxr) =
      ∑ xxr : X × Xr, Pbar.pmf xxr * shannonEntropy (dmcRow V xxr) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun xxr _ => ?_
    rw [← Finset.sum_mul]
    unfold Pbar relayTimeAvgInput uniformTimeAvgDist
    dsimp only
    ring
  have hmi_V : ∀ P : ProbDist (X × Xr),
      mutualInfo ((W.joint P).map (fun z => (z.1, z.2.1))) =
        shannonEntropy (V.joint P).snd -
          ∑ xxr : X × Xr, P.pmf xxr * shannonEntropy (dmcRow V xxr) := by
    intro P
    rw [relayYChannel_joint_eq]
    unfold mutualInfo
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]
    ring
  have havg_mi : ((1 : ℝ) / (n : ℝ)) *
      ∑ i : Fin n, mutualInfo ((W.joint (Pi i)).map (fun z => (z.1, z.2.1))) ≤
      mutualInfo ((W.joint Pbar).map (fun z => (z.1, z.2.1))) := by
    simp_rw [hmi_V]
    rw [Finset.sum_sub_distrib, mul_sub, hlin]
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmul := mul_le_mul_of_nonneg_left havg_mi (le_of_lt hn_pos)
  rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hn_pos), one_mul] at hmul
  exact le_trans hsum hmul

end MACCut

/-! ### 5. Operational Cut-Set Converse (Cover & Thomas Thm. 15.10.1; El Gamal–Kim Thm. 16.1) -/

section OperationalConverse

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-- **Multi-Letter Cut-Set Converse for Any Causal Relay Code**:
    for any causal `(n, M)` relay code `(enc, relay)` with `0 < M`,
    `I(M; Y^n) ≤ n · relayCutsetBound W`. -/
theorem relay_code_cutset_converse (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr) :
    mutualInfo ((relayCodeJoint W n M hM enc relay).map (fun mw => (mw.1, fun i => (mw.2 i).1))) ≤
      (n : ℝ) * relayCutsetBound W := by
  by_cases hn : n = 0
  · subst hn
    rw [mutualInfo_unique_right]
    simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let Pbar := relayTimeAvgInput W n M hn_pos hM enc relay
    have hbc := relay_broadcast_cut_single_letter W n M hn_pos hM enc relay
    have hmac := relay_mac_cut_single_letter W n M hn_pos hM enc relay
    have hmin : mutualInfo ((relayCodeJoint W n M hM enc relay).map
        (fun mw => (mw.1, fun i => (mw.2 i).1))) ≤
        (n : ℝ) * min
          (condMutualInfo ((W.joint Pbar).map (fun z => (z.1.1, z.2, z.1.2))))
          (mutualInfo ((W.joint Pbar).map (fun z => (z.1, z.2.1)))) := by
      rw [mul_min_of_nonneg _ _ (Nat.cast_nonneg n)]
      exact le_min hbc hmac
    exact le_trans hmin (mul_le_mul_of_nonneg_left
      (min_cutset_le_relayCutsetBound W Pbar) (Nat.cast_nonneg n))

/-- Exact bridge between `estErrorProb` on `P_{M, Y^n}` and the operational error expression
    in `InfoTheory.Core.Channels.IsRelayAchievable`. -/
private lemma relay_estErrorProb_eq (W : RelayChannel X Xr Y Yr) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
    (dec : (Fin n → Y) → Fin M) :
    estErrorProb ((relayCodeJoint W n M hM enc relay).map (fun mw => (mw.1, fun i => (mw.2 i).1))) dec =
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
          if dec y ≠ m then relayTransSeq W n M enc relay m yr y else 0 := by
  classical
  unfold estErrorProb ProbDist.map relayCodeJoint
  dsimp only
  trans (∑ my : Fin M × (Fin n → Y),
      ∑ mw : Fin M × (Fin n → Y × Yr),
        if (mw.1, fun i => (mw.2 i).1) = my then
          (if dec my.2 ≠ my.1 then
            ((1 : ℝ) / (M : ℝ)) *
              relayTransSeq W n M enc relay mw.1 (fun i => (mw.2 i).2) (fun i => (mw.2 i).1)
          else 0)
        else 0)
  · refine Finset.sum_congr rfl fun my _ => ?_
    by_cases h : dec my.2 ≠ my.1 <;> simp [h]
  rw [Finset.sum_comm]
  have hcollapse : ∀ mw : Fin M × (Fin n → Y × Yr),
      (∑ my : Fin M × (Fin n → Y),
        if (mw.1, fun i => (mw.2 i).1) = my then
          (if dec my.2 ≠ my.1 then
            ((1 : ℝ) / (M : ℝ)) *
              relayTransSeq W n M enc relay mw.1 (fun i => (mw.2 i).2) (fun i => (mw.2 i).1)
          else 0)
        else 0) =
      ((1 : ℝ) / (M : ℝ)) *
        (if dec (fun i => (mw.2 i).1) ≠ mw.1 then
          relayTransSeq W n M enc relay mw.1 (fun i => (mw.2 i).2) (fun i => (mw.2 i).1)
        else 0) := by
    intro mw
    rw [Finset.sum_eq_single (mw.1, fun i => (mw.2 i).1)]
    · simp only [↓reduceIte]
      split_ifs <;> ring
    · intro my _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hcollapse, Fintype.sum_prod_type, ← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hreidx := Fintype.sum_equiv (zipEquiv Y Yr n).symm
    (fun w : Fin n → Y × Yr =>
      if dec (fun i => (w i).1) ≠ m then
        relayTransSeq W n M enc relay m (fun i => (w i).2) (fun i => (w i).1)
      else 0)
    (fun yyr : (Fin n → Y) × (Fin n → Yr) =>
      if dec yyr.1 ≠ m then relayTransSeq W n M enc relay m yyr.2 yyr.1 else 0)
    (fun _ => rfl)
  rw [hreidx, Fintype.sum_prod_type, Finset.sum_comm]

/-- **Operational Achievability Cut-Set Bound** (Cover & Thomas Theorem 15.10.1;
    El Gamal–Kim Theorem 16.1): every operationally achievable rate `R` over a DM relay
    channel `W` satisfies `R ≤ relayCutsetBound W`. -/
theorem isRelayAchievable_le_cutsetBound (W : RelayChannel X Xr Y Yr) {R : ℝ}
    (hR : IsRelayAchievable W R) : R ≤ relayCutsetBound W := by
  rcases hR with ⟨hR0, hach⟩
  -- Nonemptiness of `X` and `Xr` follows directly from any code at `n ≥ 1`
  obtain ⟨N₀, hN₀⟩ := hach 1 zero_lt_one
  have hn₀ : max N₀ 1 ≥ N₀ := le_max_left N₀ 1
  have hn₀_pos : 0 < max N₀ 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N₀ 1)
  obtain ⟨enc₀, relay₀, _, _⟩ := hN₀ (max N₀ 1) hn₀
  have : Nonempty X := ⟨enc₀ ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)⟩ ⟨0, hn₀_pos⟩⟩
  have : Nonempty Xr := ⟨relay₀ ⟨0, hn₀_pos⟩ (fun j : Fin 0 => Fin.elim0 j)⟩
  have hC0 : 0 ≤ relayCutsetBound W := relayCutsetBound_nonneg W
  by_cases hRzero : R = 0
  · subst hRzero; exact hC0
  · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hRzero)
    by_contra hlt
    have hlt : relayCutsetBound W < R := lt_of_not_ge hlt
    set C := relayCutsetBound W
    set ε : ℝ := min (1 / 2 : ℝ) ((R - C) / (4 * R))
    have hε_pos : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hε_le_half : ε ≤ 1 / 2 := min_le_left _ _
    have hε_mul : ε * R ≤ (R - C) / 4 := by
      have h1 : ε ≤ (R - C) / (4 * R) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hRpos)
      have h3 : (R - C) / (4 * R) * R = (R - C) / 4 := by
        field_simp [ne_of_gt hRpos]
      linarith
    have hgap : (3 / 4 : ℝ) * (R - C) ≤ (1 - ε) * R - C := by linarith
    have hgap_pos : 0 < (1 - ε) * R - C := by linarith
    obtain ⟨N₁, hN₁⟩ := hach ε hε_pos
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / R)
    obtain ⟨N₃, hN₃⟩ := exists_nat_gt (2 / ((1 - ε) * R - C))
    let n : ℕ := max (max N₁ 1) (max N₂ N₃)
    have hn1 : n ≥ N₁ := le_trans (le_max_left N₁ 1) (le_max_left _ _)
    have hn2 : (N₂ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_left N₂ N₃) (le_max_right _ _)
    have hn3 : (N₃ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right N₂ N₃) (le_max_right _ _)
    have hnR_ge2 : (2 : ℝ) ≤ (n : ℝ) * R := by
      have h := lt_of_lt_of_le hN₂ hn2
      exact le_of_lt ((div_lt_iff₀ hRpos).mp h)
    have hngap_gt2 : (2 : ℝ) < (n : ℝ) * ((1 - ε) * R - C) := by
      have h := lt_of_lt_of_le hN₃ hn3
      exact (div_lt_iff₀ hgap_pos).mp h
    set M : ℕ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    obtain ⟨enc, relay, dec, herr⟩ := hN₁ n hn1
    dsimp only at herr
    -- Show `2 ≤ M` and `(2 : ℝ) ^ (n * R - 1) ≤ M`
    have hpow_ge4 : (4 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
      calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR_ge2
    have hhalf_le_floor : (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) := by
      have hfl := Nat.sub_one_lt_floor ((2 : ℝ) ^ ((n : ℝ) * R))
      linarith
    have hfloor_ge2 : 2 ≤ Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := by
      have h2_le : (2 : ℝ) ≤ (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) := by linarith
      exact_mod_cast h2_le
    have hM_ge2 : 2 ≤ M := le_trans hfloor_ge2 (Nat.le_max_right 1 _)
    have hM_pos : 0 < M := by omega
    have hM_ge_pow : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ (M : ℝ) := by
      have hsub : (2 : ℝ) ^ ((n : ℝ) * R - 1) = (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      have hfl_le_M : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.le_max_right 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      linarith
    have hlogM_ge : (n : ℝ) * R - 1 ≤ log2 (M : ℝ) := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R - 1) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hlog_pow : log2 ((2 : ℝ) ^ ((n : ℝ) * R - 1)) = (n : ℝ) * R - 1 := by
        unfold log2
        rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
      rw [← hlog_pow]
      unfold log2
      exact div_le_div_of_nonneg_right (Real.log_le_log hpow_pos hM_ge_pow) (le_of_lt hlog2_pos)
    -- Apply Fano's inequality + cut-set converse to `P_MY`
    let P_MY := (relayCodeJoint W n M hM_pos enc relay).map (fun mw => (mw.1, fun i => (mw.2 i).1))
    have hpe_eq : estErrorProb P_MY dec =
        ((1 : ℝ) / (M : ℝ)) *
          ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
            if dec y ≠ m then relayTransSeq W n M enc relay m yr y else 0 :=
      relay_estErrorProb_eq W n M hM_pos enc relay dec
    have hpe_le : estErrorProb P_MY dec ≤ ε := by
      rw [hpe_eq]
      exact herr
    have hpe0 : 0 ≤ estErrorProb P_MY dec := estErrorProb_nonneg P_MY dec
    have hpe1 : estErrorProb P_MY dec ≤ 1 := estErrorProb_le_one P_MY dec
    have hfano := fano_inequality P_MY dec (by simpa using hM_ge2)
    rw [Fintype.card_fin] at hfano
    have hcut := relay_code_cutset_converse W n M hM_pos enc relay
    have hHM : shannonEntropy P_MY.fst = log2 (M : ℝ) := by
      have : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
      have hfst : P_MY.fst = (relayCodeJoint W n M hM_pos enc relay).fst := by
        rw [fst_eq_map_fst, fst_eq_map_fst]
        dsimp only [P_MY]
        rw [map_comp_eq]; rfl
      rw [hfst, relayCodeJoint_fst W n M hM_pos enc relay,
        (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin M))).mpr rfl, Fintype.card_fin]
    have hid : log2 (M : ℝ) = condEntropy P_MY + mutualInfo P_MY := by
      unfold condEntropy mutualInfo
      linarith [hHM]
    have hbin : binaryEntropy (estErrorProb P_MY dec) ≤ 1 :=
      InfoTheory.Known.binaryEntropy_le_one hpe0 hpe1
    have hlog_sub : log2 ((M : ℝ) - 1) ≤ log2 (M : ℝ) := by
      unfold log2
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge2
        linarith
      exact div_le_div_of_nonneg_right (Real.log_le_log hM1 (by linarith)) (le_of_lt hlog2_pos)
    have hmul_pe : estErrorProb P_MY dec * log2 ((M : ℝ) - 1) ≤
        estErrorProb P_MY dec * log2 (M : ℝ) :=
      mul_le_mul_of_nonneg_left hlog_sub hpe0
    have hlogM_nonneg : 0 ≤ log2 (M : ℝ) := by linarith
    have hmain : (1 - ε) * ((n : ℝ) * R - 1) ≤ (n : ℝ) * C + 1 := by
      have h1 : (1 - estErrorProb P_MY dec) * log2 (M : ℝ) ≤ (n : ℝ) * C + 1 := by
        linarith
      have h2 : (1 - ε) * log2 (M : ℝ) ≤ (1 - estErrorProb P_MY dec) * log2 (M : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogM_nonneg
      have h3 : (1 - ε) * ((n : ℝ) * R - 1) ≤ (1 - ε) * log2 (M : ℝ) :=
        mul_le_mul_of_nonneg_left hlogM_ge (by linarith)
      linarith
    linarith

/-- **Operational Relay Channel Cut-Set Bound** (Cover & Thomas Theorem 15.10.1;
    El Gamal–Kim Theorem 16.1): for any discrete memoryless relay channel `W` with nonempty
    input alphabets, the operational capacity is bounded above by the cut-set bound:
    `C(W) ≤ max_{p(x, x_r)} min{ I(X; Y, Y_r | X_r), I(X, X_r; Y) }`. -/
theorem relayCapacity_le_cutsetBound [Nonempty X] [Nonempty Xr]
    (W : RelayChannel X Xr Y Yr) :
    relayCapacity W ≤ relayCutsetBound W := by
  unfold relayCapacity
  exact Real.sSup_le (fun R hR => isRelayAchievable_le_cutsetBound W hR)
    (relayCutsetBound_nonneg W)

end OperationalConverse

end InfoTheory.Bridge
