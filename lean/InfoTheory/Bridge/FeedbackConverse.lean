import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability

/-!
# Feedback Does Not Increase DMC Capacity (Cover & Thomas, Theorem 7.12.1)

Purely additive, kernel-verified formalization of the feedback channel coding theorem for
Discrete Memoryless Channels (DMCs) and its silent-user MAC-with-feedback converse corollary:

1. **Causal Feedback Codes & Joint Distribution**:
   - `feedbackCausalProd_sum_one`: causal products of conditional laws sum to `1`
   - `dmcFeedbackTrans`, `dmcFeedbackTrans_nonneg`, `dmcFeedbackTrans_sum_one`
   - `dmcFeedbackJoint`, `dmcFeedbackJoint_fst`
   - `dmcFeedbackAvgError`, `IsDmcFeedbackAchievable`, `dmcFeedbackCapacity`

2. **Multi-Letter Feedback Mutual Information Bound & Fano Converse**:
   - `dmcFeedback_mutualInfo_le_mul_capacity`: `I(M; Y^n) ≤ n · C(W)` for any causal feedback
     encoder (proved cleanly by induction on `n`, peeling off the last coordinate `Fin.last n`
     so `H(M, Y^{n+1}) = H(M, Y^n) + H(Y_n | X_n)` and `H(Y^{n+1}) ≤ H(Y^n) + H(Y_n)`)
   - `dmcFeedback_weak_converse`: sharp Fano inequality
     `log₂ M ≤ h(P_e) + P_e log₂(M - 1) + n · C(W)`
   - `dmcFeedback_rate_converse`: `log₂ M ≤ n · C(W) + 1 + P_e log₂ M`

3. **Cover & Thomas Theorem 7.12.1**:
   - `isDmcFeedbackAchievable_zero`, `dmc_feedback_achievability`, `dmc_feedback_converse`
   - `dmc_feedback_capacity_theorem`: `dmcFeedbackCapacity W = W.capacity`

4. **Silent-User MAC-with-Feedback Converse Corollary**:
   - `isDmcFeedbackAchievable_of_isMACFeedbackAchievable_ignores_second`
   - `isMACFeedbackAchievable_le_capacity_of_ignores_second`: if a MAC `W` ignores user 2
     (`W(y | x₁, x₂) = V(y | x₁)`), then every feedback-achievable pair `(R₁, R₂)` satisfies
     `R₁ ≤ C(V)`
   - `macFeedbackCapacityRegion_fst_le_of_ignores_second`: closure corollary on
     `macFeedbackCapacityRegion W`

All theorems leave `Core/`, `Problems/`, `Known/`, `STATEMENT_LOCK.json`, and existing
`Bridge/` files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Causal Feedback Codes and Normalization -/

section FeedbackDefs

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Init-last equivalence `(Fin (n + 1) → β) ≃ (Fin n → β) × β`. -/
private def piSnocEquiv (β : Type*) (n : ℕ) : (Fin (n + 1) → β) ≃ (Fin n → β) × β where
  toFun := fun y => (fun i => y i.castSucc, y (Fin.last n))
  invFun := fun p => Fin.snoc p.1 p.2
  left_inv := fun y => by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp
  right_inv := fun ⟨ys, b⟩ => by
    ext i
    · simp
    · simp

/-- **Causal product normalization**: for any family of conditional distributions
    `g i (y^{i-1}) (·)` on `β`, the causal product `∏ᵢ g i (y^{i-1}) (yᵢ)` sums to `1` over
    `Fin n → β`. -/
theorem feedbackCausalProd_sum_one (n : ℕ)
    (g : ∀ i : Fin n, (Fin i.1 → β) → β → ℝ)
    (h1 : ∀ i h, ∑ b : β, g i h b = 1) :
    ∑ y : Fin n → β,
      ∏ i : Fin n, g i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩) (y i) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let e := piSnocEquiv β n
    rw [← Fintype.sum_equiv e.symm
      (fun p => ∏ i : Fin (n + 1),
        g i (fun j => (e.symm p) ⟨j.1, Nat.lt_trans j.2 i.2⟩) ((e.symm p) i))
      (fun y => ∏ i : Fin (n + 1),
        g i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩) (y i))
      (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hsplit : ∀ (ys : Fin n → β) (b : β),
        ∏ i : Fin (n + 1),
          g i (fun j => (e.symm (ys, b)) ⟨j.1, Nat.lt_trans j.2 i.2⟩) ((e.symm (ys, b)) i) =
        (∏ i : Fin n, g i.castSucc (fun j => ys ⟨j.1, Nat.lt_trans j.2 i.2⟩) (ys i)) *
          g (Fin.last n) ys b := by
      intro ys b
      let y : Fin (n + 1) → β := Fin.snoc ys b
      change ∏ i : Fin (n + 1),
        g i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩) (y i) = _
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have hpref : (fun j : Fin i.castSucc.1 =>
            y ⟨j.1, Nat.lt_trans j.2 i.castSucc.2⟩) =
            (fun j : Fin i.1 => ys ⟨j.1, Nat.lt_trans j.2 i.2⟩) := by
          funext j
          change y (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n).castSucc = _
          simp only [y, Fin.snoc_castSucc]
        have hcur : y i.castSucc = ys i := by simp only [y, Fin.snoc_castSucc]
        rw [hpref, hcur]
        rfl
      · have hpref : (fun j : Fin (Fin.last n).1 =>
            y ⟨j.1, Nat.lt_trans j.2 (Fin.last n).2⟩) = ys := by
          funext j
          change y j.castSucc = ys j
          simp only [y, Fin.snoc_castSucc]
        have hcur : y (Fin.last n) = b := by simp only [y, Fin.snoc_last]
        rw [hpref, hcur]
    simp_rw [hsplit, ← Finset.mul_sum, h1 (Fin.last n), mul_one]
    exact ih (fun i h b => g i.castSucc h b) (fun i h => h1 i.castSucc h)

/-- Transition probability `p(y^n | m)` of an `n`-use DMC `W` driven by a causal feedback
    encoder `enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α`. -/
def dmcFeedbackTrans (W : DMC α β) (n M : ℕ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
    (m : Fin M) (y : Fin n → β) : ℝ :=
  ∏ i : Fin n, W.trans (enc i m (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)

lemma dmcFeedbackTrans_nonneg (W : DMC α β) (n M : ℕ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
    (m : Fin M) (y : Fin n → β) :
    0 ≤ dmcFeedbackTrans W n M enc m y :=
  Finset.prod_nonneg fun _ _ => W.nonneg _ _

/-- For every message `m`, the feedback transition kernel `dmcFeedbackTrans W n M enc m`
    sums to `1` over all output sequences `y : Fin n → β`. -/
theorem dmcFeedbackTrans_sum_one (W : DMC α β) (n M : ℕ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α) (m : Fin M) :
    ∑ y : Fin n → β, dmcFeedbackTrans W n M enc m y = 1 :=
  feedbackCausalProd_sum_one n (fun i h b => W.trans (enc i m h) b) (fun _ _ => W.sum_one _)

/-- Joint distribution `(M, Y^n)` for a uniform message `M ~ Unif(Fin M)` transmitted over
    DMC `W` using a causal feedback encoder `enc`. -/
noncomputable def dmcFeedbackJoint (W : DMC α β) (n M : ℕ) (hM : 0 < M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α) :
    ProbDist (Fin M × (Fin n → β)) where
  pmf := fun my => ((1 : ℝ) / (M : ℝ)) * dmcFeedbackTrans W n M enc my.1 my.2
  nonneg := fun my => mul_nonneg (by positivity) (dmcFeedbackTrans_nonneg W n M enc my.1 my.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    dsimp only
    simp_rw [← Finset.mul_sum, dmcFeedbackTrans_sum_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
    field_simp [hMne]

/-- The message marginal of `dmcFeedbackJoint` is uniform on `Fin M`. -/
lemma dmcFeedbackJoint_fst (W : DMC α β) (n M : ℕ) (hM : 0 < M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α) :
    letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    (dmcFeedbackJoint W n M hM enc).fst = ProbDist.uniform := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  unfold ProbDist.fst dmcFeedbackJoint ProbDist.uniform
  congr
  funext m
  dsimp only
  rw [← Finset.mul_sum, dmcFeedbackTrans_sum_one, mul_one, Fintype.card_fin]

/-- Average error probability of an `(n, M)` feedback code `(enc, dec)` over a DMC `W`. -/
noncomputable def dmcFeedbackAvgError (W : DMC α β) (n M : ℕ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
    (dec : (Fin n → β) → Fin M) : ℝ :=
  if M = 0 then 0 else
    ((1 : ℝ) / (M : ℝ)) *
      ∑ m : Fin M, ∑ y : Fin n → β,
        if dec y ≠ m then dmcFeedbackTrans W n M enc m y else 0

/-- Operational achievability of rate `R` over a DMC `W` with noiseless causal feedback
    (Cover & Thomas, §7.12). -/
def IsDmcFeedbackAchievable (W : DMC α β) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
      (dec : (Fin n → β) → Fin M),
      dmcFeedbackAvgError W n M enc dec ≤ δ

/-- Feedback capacity `C_FB(W)` of a DMC `W`: supremum of all feedback-achievable rates. -/
noncomputable def dmcFeedbackCapacity (W : DMC α β) : ℝ :=
  sSup { R : ℝ | IsDmcFeedbackAchievable W R }

end FeedbackDefs

/-! ### 2. Multi-Letter Feedback Mutual Information Bound and Fano Converse -/

section FeedbackConverseCore

variable {α β : Type*} [Fintype α] [Fintype β]

private lemma dmcFeedbackTrans_snoc (W : DMC α β) {n M : ℕ}
    (enc : ∀ i : Fin (n + 1), Fin M → (Fin i.1 → β) → α)
    (m : Fin M) (ys : Fin n → β) (b : β) :
    dmcFeedbackTrans W (n + 1) M enc m (Fin.snoc ys b) =
      dmcFeedbackTrans W n M (fun i m h => enc i.castSucc m h) m ys *
        W.trans (enc (Fin.last n) m ys) b := by
  unfold dmcFeedbackTrans
  let y : Fin (n + 1) → β := Fin.snoc ys b
  change ∏ i : Fin (n + 1),
    W.trans (enc i m (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i) = _
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hpref : (fun j : Fin i.castSucc.1 =>
        y ⟨j.1, Nat.lt_trans j.2 i.castSucc.2⟩) =
        (fun j : Fin i.1 => ys ⟨j.1, Nat.lt_trans j.2 i.2⟩) := by
      funext j
      change y (⟨j.1, Nat.lt_trans j.2 i.2⟩ : Fin n).castSucc = _
      simp only [y, Fin.snoc_castSucc]
    have hcur : y i.castSucc = ys i := by simp only [y, Fin.snoc_castSucc]
    rw [hpref, hcur]
  · have hpref : (fun j : Fin (Fin.last n).1 =>
        y ⟨j.1, Nat.lt_trans j.2 (Fin.last n).2⟩) = ys := by
      funext j
      change y j.castSucc = ys j
      simp only [y, Fin.snoc_castSucc]
    have hcur : y (Fin.last n) = b := by simp only [y, Fin.snoc_last]
    rw [hpref, hcur]

/-- **Multi-Letter Feedback Mutual Information Bound** (Cover & Thomas, §7.12, eq. (7.143)–(7.149)):
    for any causal feedback encoder over `n` uses of a DMC `W`,
    `I(M; Y^n) ≤ n · C(W)`.

    Proved by induction on `n` peeling off the final channel use `i = Fin.last n`:
    at step `n + 1`, the joint law `(M, Y^n, Y_n)` factors as `(M, Y^n)` followed by the
    memoryless channel `W(· | enc_n(M, Y^n))`, yielding
    - `H(M, Y^{n+1}) = H(M, Y^n) + H(Y_n | X_n)`,
    - `H(Y^{n+1}) ≤ H(Y^n) + H(Y_n)`,
    and hence `I(M; Y^{n+1}) ≤ I(M; Y^n) + I(X_n; Y_n) ≤ n C(W) + C(W)`. -/
theorem dmcFeedback_mutualInfo_le_mul_capacity (W : DMC α β) {n M : ℕ} (hM : 0 < M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α) :
    mutualInfo (dmcFeedbackJoint W n M hM enc) ≤ (n : ℝ) * W.capacity := by
  induction n with
  | zero =>
    let J := dmcFeedbackJoint W 0 M hM enc
    have hcard : Fintype.card (Fin 0 → β) = 1 := Fintype.card_unique
    have hHy : shannonEntropy J.snd ≤ 0 := by
      have hle := shannonEntropy_le_log2_card J.snd
      rw [hcard] at hle
      simpa [log2] using hle
    have hce : 0 ≤ condEntropy (J.map Prod.swap) := condEntropy_nonneg _
    unfold condEntropy at hce
    rw [shannonEntropy_swap, snd_map_swap] at hce
    unfold mutualInfo
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    classical
    let encPrev : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α := fun i m h => enc i.castSucc m h
    let Jprev := dmcFeedbackJoint W n M hM encPrev
    let Jnext := dmcFeedbackJoint W (n + 1) M hM enc
    let g : Fin M × (Fin n → β) → α := fun p => enc (Fin.last n) p.1 p.2
    let PX : ProbDist α := Jprev.map g
    let eJoint : (Fin M × (Fin (n + 1) → β)) ≃ ((Fin M × (Fin n → β)) × β) :=
      (Equiv.prodCongr (Equiv.refl (Fin M)) (piSnocEquiv β n)).trans
        (Equiv.prodAssoc (Fin M) (Fin n → β) β).symm
    -- Identify `Jnext.map eJoint` with `(dmcPrecomp W g).joint Jprev`
    have hmap_joint : Jnext.map eJoint = (dmcPrecomp W g).joint Jprev := by
      unfold ProbDist.map DMC.joint dmcPrecomp
      congr
      funext ⟨⟨m, ys⟩, b⟩
      dsimp only
      rw [Finset.sum_eq_single (m, Fin.snoc ys b)]
      · have he : eJoint (m, Fin.snoc ys b) = ((m, ys), b) := by
          ext i
          · rfl
          · simp [eJoint, piSnocEquiv]
          · simp [eJoint, piSnocEquiv]
        simp only [he, ↓reduceIte]
        change ((1 : ℝ) / (M : ℝ)) * dmcFeedbackTrans W (n + 1) M enc m (Fin.snoc ys b) =
          (((1 : ℝ) / (M : ℝ)) * dmcFeedbackTrans W n M encPrev m ys) *
            W.trans (enc (Fin.last n) m ys) b
        rw [dmcFeedbackTrans_snoc]
        ring
      · intro my _ hne
        have hene : eJoint my ≠ ((m, ys), b) := fun h => by
          apply hne
          have h1 := congrArg eJoint.symm h
          rw [Equiv.symm_apply_apply] at h1
          exact h1
        simp [hene]
      · intro h; exact absurd (Finset.mem_univ _) h
    -- 1. Chain rule for joint entropy: `H(M, Y^{n+1}) = H(M, Y^n) + H(X_n, Y_n) - H(X_n)`
    have hHjoint : shannonEntropy Jnext =
        shannonEntropy Jprev + (shannonEntropy (W.joint PX) - shannonEntropy PX) := by
      rw [← shannonEntropy_map_equiv eJoint Jnext, hmap_joint, dmc_joint_shannonEntropy]
      have hcond : ∑ p : Fin M × (Fin n → β), Jprev.pmf p * shannonEntropy (dmcRow (dmcPrecomp W g) p) =
          ∑ a : α, PX.pmf a * shannonEntropy (dmcRow W a) :=
        sum_pmf_mul_comp Jprev g (fun a => shannonEntropy (dmcRow W a))
      have hdmc := dmc_joint_shannonEntropy W PX
      linarith
    -- 2. Message marginal is unchanged: `H(M)` is the same in `Jnext` and `Jprev`
    have hfst_eq : Jnext.fst = Jprev.fst := by
      have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
      rw [dmcFeedbackJoint_fst, dmcFeedbackJoint_fst]
    -- 3. Output entropy subadditivity: `H(Y^{n+1}) ≤ H(Y^n) + H(Y_n)`
    let R : ProbDist ((Fin n → β) × β) := Jnext.snd.map (piSnocEquiv β n)
    have hR_pmf : ∀ (ys : Fin n → β) (b : β),
        R.pmf (ys, b) = ∑ m : Fin M, Jprev.pmf (m, ys) * W.trans (g (m, ys)) b := by
      intro ys b
      unfold R ProbDist.map ProbDist.snd
      dsimp only
      rw [Finset.sum_eq_single (Fin.snoc ys b)]
      · have he : piSnocEquiv β n (Fin.snoc ys b) = (ys, b) :=
          (piSnocEquiv β n).apply_symm_apply (ys, b)
        simp only [he, ↓reduceIte]
        refine Finset.sum_congr rfl fun m _ => ?_
        change ((1 : ℝ) / (M : ℝ)) * dmcFeedbackTrans W (n + 1) M enc m (Fin.snoc ys b) =
          (((1 : ℝ) / (M : ℝ)) * dmcFeedbackTrans W n M encPrev m ys) *
            W.trans (enc (Fin.last n) m ys) b
        rw [dmcFeedbackTrans_snoc]
        ring
      · intro y _ hne
        have hene : piSnocEquiv β n y ≠ (ys, b) := fun h => by
          apply hne
          have h1 := congrArg (piSnocEquiv β n).symm h
          rw [Equiv.symm_apply_apply] at h1
          exact h1
        simp [hene]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_fst : R.fst = Jprev.snd := by
      unfold ProbDist.fst ProbDist.snd
      congr
      funext ys
      simp_rw [hR_pmf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.mul_sum, W.sum_one, mul_one]
    have hR_snd : R.snd = (W.joint PX).snd := by
      unfold ProbDist.snd DMC.joint
      congr
      funext b
      dsimp only
      simp_rw [hR_pmf]
      rw [← Fintype.sum_prod_type_right
        (f := fun p : Fin M × (Fin n → β) => Jprev.pmf p * W.trans (g p) b)]
      exact sum_pmf_mul_comp Jprev g (fun a => W.trans a b)
    have hHy_le : shannonEntropy Jnext.snd ≤
        shannonEntropy Jprev.snd + shannonEntropy (W.joint PX).snd := by
      rw [← shannonEntropy_map_equiv (piSnocEquiv β n) Jnext.snd]
      have hsub := shannonEntropy_subadd R
      rw [hR_fst, hR_snd] at hsub
      exact hsub
    -- 4. Combine with the induction hypothesis and `I(X_n; Y_n) ≤ C(W)`
    have hih := ih encPrev
    have hcap_last : mutualInfo (W.joint PX) ≤ W.capacity := dmc_mutualInfo_le_capacity W PX
    have hPX_fst : (W.joint PX).fst = PX := dmc_joint_fst W PX
    have hmi_next : mutualInfo Jnext ≤ mutualInfo Jprev + mutualInfo (W.joint PX) := by
      unfold mutualInfo
      rw [hfst_eq, hHjoint, hPX_fst]
      linarith
    push_cast
    linarith

private lemma estErrorProb_dmcFeedbackJoint (W : DMC α β) {n M : ℕ} (hM : 0 < M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
    (dec : (Fin n → β) → Fin M) :
    estErrorProb (dmcFeedbackJoint W n M hM enc) dec = dmcFeedbackAvgError W n M enc dec := by
  classical
  unfold estErrorProb dmcFeedbackAvgError dmcFeedbackJoint
  have hMne : M ≠ 0 := Nat.ne_of_gt hM
  simp only [hMne, ↓reduceIte]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- **Sharp Fano Weak Converse for Feedback Codes** (Cover & Thomas, §7.12):
    for any `(n, M)` causal feedback code with `2 ≤ M` over a DMC `W`,
    `log₂ M ≤ h(P_e) + P_e log₂(M - 1) + n · C(W)`. -/
theorem dmcFeedback_weak_converse (W : DMC α β) {n M : ℕ} (hM : 2 ≤ M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
    (dec : (Fin n → β) → Fin M) :
    log2 (M : ℝ) ≤
      binaryEntropy (dmcFeedbackAvgError W n M enc dec) +
        dmcFeedbackAvgError W n M enc dec * log2 ((M : ℝ) - 1) + (n : ℝ) * W.capacity := by
  have hMpos : 0 < M := by omega
  have : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
  let P_MY := dmcFeedbackJoint W n M hMpos enc
  have hcard : 2 ≤ Fintype.card (Fin M) := by simpa using hM
  have hfano := fano_inequality P_MY dec hcard
  have hcap := dmcFeedback_mutualInfo_le_mul_capacity W hMpos enc
  have hHM : shannonEntropy P_MY.fst = log2 (M : ℝ) := by
    change shannonEntropy (dmcFeedbackJoint W n M hMpos enc).fst = _
    rw [dmcFeedbackJoint_fst]
    simpa [Fintype.card_fin] using (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := Fin M))).mpr rfl
  have hid : log2 (M : ℝ) = condEntropy P_MY + mutualInfo P_MY := by
    unfold condEntropy mutualInfo
    linarith [hHM]
  have herr : estErrorProb P_MY dec = dmcFeedbackAvgError W n M enc dec :=
    estErrorProb_dmcFeedbackJoint W hMpos enc dec
  rw [herr, Fintype.card_fin] at hfano
  linarith

/-- **Linear Fano Rate Converse for Feedback Codes** (Cover & Thomas, §7.12):
    for any `(n, M)` causal feedback code with `2 ≤ M` over a DMC `W`,
    `log₂ M ≤ n · C(W) + 1 + P_e · log₂ M`. -/
theorem dmcFeedback_rate_converse (W : DMC α β) {n M : ℕ} (hM : 2 ≤ M)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → β) → α)
    (dec : (Fin n → β) → Fin M) :
    log2 (M : ℝ) ≤
      (n : ℝ) * W.capacity + 1 + dmcFeedbackAvgError W n M enc dec * log2 (M : ℝ) := by
  have hMpos : 0 < M := by omega
  let P_MY := dmcFeedbackJoint W n M hMpos enc
  have herr : estErrorProb P_MY dec = dmcFeedbackAvgError W n M enc dec :=
    estErrorProb_dmcFeedbackJoint W hMpos enc dec
  have hpe0 : 0 ≤ dmcFeedbackAvgError W n M enc dec := herr ▸ estErrorProb_nonneg P_MY dec
  have hpe1 : dmcFeedbackAvgError W n M enc dec ≤ 1 := herr ▸ estErrorProb_le_one P_MY dec
  have hconv := dmcFeedback_weak_converse W hM enc dec
  have hbin : binaryEntropy (dmcFeedbackAvgError W n M enc dec) ≤ 1 :=
    InfoTheory.Known.binaryEntropy_le_one hpe0 hpe1
  have hlog : log2 ((M : ℝ) - 1) ≤ log2 (M : ℝ) := by
    unfold log2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    exact div_le_div_of_nonneg_right (Real.log_le_log hM1 (by linarith)) (le_of_lt hlog2)
  have hmul : dmcFeedbackAvgError W n M enc dec * log2 ((M : ℝ) - 1) ≤
      dmcFeedbackAvgError W n M enc dec * log2 (M : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hpe0
  linarith

end FeedbackConverseCore

/-! ### 3. Cover & Thomas Theorem 7.12.1: Feedback Does Not Increase DMC Capacity -/

section FeedbackCapacityTheorem

variable {α β : Type*} [Fintype α] [Fintype β]

private lemma log2_two_rpow_fb (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

/-- **Feedback Converse** (Cover & Thomas, Theorem 7.12.1):
    every rate achievable over a DMC `W` with noiseless causal feedback satisfies `R ≤ C(W)`. -/
theorem dmc_feedback_converse (W : DMC α β) {R : ℝ}
    (h : IsDmcFeedbackAchievable W R) : R ≤ W.capacity := by
  by_contra hlt
  push Not at hlt
  have hα : Nonempty α := by
    obtain ⟨N, hN⟩ := h.2 1 zero_lt_one
    obtain ⟨enc, _, _⟩ := hN (max N 1) (le_max_left N 1)
    have hMpos : 0 < max 1 (Nat.floor ((2 : ℝ) ^ (((max N 1 : ℕ) : ℝ) * R))) :=
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
    exact ⟨enc ⟨0, hn_pos⟩ ⟨0, hMpos⟩ (fun j => (Nat.not_lt_zero _ j.2).elim)⟩
  have hcap0 : 0 ≤ W.capacity := by
    have hmi : 0 ≤ mutualInfo (W.joint (ProbDist.uniform (α := α))) := mutualInfo_nonneg _
    exact le_trans hmi (dmc_mutualInfo_le_capacity W ProbDist.uniform)
  let Δ : ℝ := R - W.capacity
  have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
  have hRpos : 0 < R := by linarith
  let δ : ℝ := min (1 / 2) (Δ / (4 * R))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδR : δ * R ≤ Δ / 4 := by
    have h1 : δ ≤ Δ / (4 * R) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hRpos)
    have h3 : Δ / (4 * R) * R = Δ / 4 := by field_simp [ne_of_gt hRpos]
    linarith
  obtain ⟨N₁, hN₁⟩ := h.2 δ hδ_pos
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
    have h1 := (div_lt_iff₀ hRpos).mp hn_gt_1R
    linarith
  have h2n_lt : 2 / (n : ℝ) < Δ / 2 := by
    rw [div_lt_iff₀ hn_r]
    have h1 := (div_lt_iff₀ hΔ).mp hn_gt_4Δ
    linarith
  obtain ⟨enc, dec, herr⟩ := hN₁ n hn_ge_N₁
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
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlog_mono : log2 ((2 : ℝ) ^ ((n : ℝ) * R - 1)) ≤ log2 (M : ℝ) := by
      unfold log2
      exact div_le_div_of_nonneg_right (Real.log_le_log hpow_pos hM_gt_pow)
        (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    rw [log2_two_rpow_fb] at hlog_mono
    exact hlog_mono
  have hrate_ge : R - 1 / (n : ℝ) ≤ log2 (M : ℝ) / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hlogM_ge (le_of_lt hn_r)
    have hsimp : ((n : ℝ) * R - 1) / (n : ℝ) = R - 1 / (n : ℝ) := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hn_r)]
    linarith
  have hrate_nonneg : 0 ≤ R - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < R := (div_lt_iff₀ hn_r).mpr (by linarith)
    linarith
  have hconv_raw := dmcFeedback_rate_converse W hM_ge2 enc dec
  have hconv : (1 - dmcFeedbackAvgError W n M enc dec) * (log2 (M : ℝ) / (n : ℝ)) ≤
      W.capacity + 1 / (n : ℝ) := by
    have hmain : (1 - dmcFeedbackAvgError W n M enc dec) * log2 (M : ℝ) ≤
        (n : ℝ) * W.capacity + 1 := by linarith
    calc (1 - dmcFeedbackAvgError W n M enc dec) * (log2 (M : ℝ) / (n : ℝ))
      _ = ((1 - dmcFeedbackAvgError W n M enc dec) * log2 (M : ℝ)) / (n : ℝ) := by ring
      _ ≤ ((n : ℝ) * W.capacity + 1) / (n : ℝ) :=
          div_le_div_of_nonneg_right hmain (le_of_lt hn_r)
      _ = W.capacity + 1 / (n : ℝ) := by
          rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hn_r)]
  have herr_le : dmcFeedbackAvgError W n M enc dec ≤ δ := herr
  have hprod_le : (1 - δ) * (R - 1 / (n : ℝ)) ≤
      (1 - dmcFeedbackAvgError W n M enc dec) * (log2 (M : ℝ) / (n : ℝ)) :=
    mul_le_mul (by linarith) hrate_ge hrate_nonneg (by linarith)
  have hcomb : (1 - δ) * (R - 1 / (n : ℝ)) ≤ W.capacity + 1 / (n : ℝ) :=
    le_trans hprod_le hconv
  have hδn : 0 ≤ δ * (1 / (n : ℝ)) := by positivity
  have hexpand : (1 - δ) * (R - 1 / (n : ℝ)) = R - 1 / (n : ℝ) - δ * R + δ * (1 / (n : ℝ)) := by
    ring
  have h2div : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
  have hfinal : Δ ≤ δ * R + 2 / (n : ℝ) := by
    dsimp only [Δ]
    linarith
  linarith

/-- Any non-feedback achievable rate is achievable with feedback (by ignoring feedback). -/
private theorem isDmcFeedbackAchievable_of_isDmcAchievableRate (W : DMC α β) {R : ℝ}
    (h : IsDmcAchievableRate W R) : IsDmcFeedbackAchievable W R := by
  classical
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h.2 δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  refine ⟨fun i m _ => enc m i, dec, ?_⟩
  simpa only [dmcFeedbackAvgError, dmcAvgError, dmcFeedbackTrans, DMC.power] using herr

/-- Rate `0` is feedback-achievable over any DMC on a nonempty input alphabet. -/
theorem isDmcFeedbackAchievable_zero [Nonempty α] (W : DMC α β) :
    IsDmcFeedbackAchievable W 0 :=
  isDmcFeedbackAchievable_of_isDmcAchievableRate W (isDmcAchievableRate_zero W)

/-- **Feedback Achievability** (Cover & Thomas, Theorem 7.12.1):
    every rate `0 ≤ R < C(W)` is achievable with feedback (simply by ignoring feedback
    and invoking Shannon's channel coding achievability theorem). -/
theorem dmc_feedback_achievability (W : DMC α β) {R : ℝ}
    (h0 : 0 ≤ R) (hR : R < W.capacity) : IsDmcFeedbackAchievable W R :=
  isDmcFeedbackAchievable_of_isDmcAchievableRate W (shannon_channel_coding_achievability W R h0 hR)

/-- **Cover & Thomas, Theorem 7.12.1 (Feedback Does Not Increase DMC Capacity)**:
    the feedback capacity `C_FB(W)` of any Discrete Memoryless Channel `W` equals its
    non-feedback Shannon capacity `C(W) = sup_{P_X} I(X; Y)`. -/
theorem dmc_feedback_capacity_theorem (W : DMC α β) :
    dmcFeedbackCapacity W = W.capacity := by
  by_cases hα : Nonempty α
  · have hSne : { R : ℝ | IsDmcFeedbackAchievable W R }.Nonempty :=
      ⟨0, isDmcFeedbackAchievable_zero W⟩
    have hSbdd : BddAbove { R : ℝ | IsDmcFeedbackAchievable W R } :=
      ⟨W.capacity, fun _ hR => dmc_feedback_converse W hR⟩
    have hle : dmcFeedbackCapacity W ≤ W.capacity :=
      csSup_le hSne (fun _ hR => dmc_feedback_converse W hR)
    have hge : W.capacity ≤ dmcFeedbackCapacity W := by
      by_contra hlt
      push Not at hlt
      have hop0 : 0 ≤ dmcFeedbackCapacity W :=
        le_csSup hSbdd (isDmcFeedbackAchievable_zero W)
      let R : ℝ := (dmcFeedbackCapacity W + W.capacity) / 2
      have hR0 : 0 ≤ R := by dsimp only [R]; linarith
      have hRlt : R < W.capacity := by dsimp only [R]; linarith
      have hgt : dmcFeedbackCapacity W < R := by dsimp only [R]; linarith
      have hach : IsDmcFeedbackAchievable W R := dmc_feedback_achievability W hR0 hRlt
      have hRle : R ≤ dmcFeedbackCapacity W := le_csSup hSbdd hach
      linarith
    exact le_antisymm hle hge
  · have hcap_empty : { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P } = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, _⟩
      have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (hα ⟨a⟩).elim
      linarith [P.sum_one]
    have hfb_empty : { R : ℝ | IsDmcFeedbackAchievable W R } = ∅ := by
      ext R
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hR
      obtain ⟨N, hN⟩ := hR.2 1 zero_lt_one
      obtain ⟨enc, _, _⟩ := hN (max N 1) (le_max_left N 1)
      have hMpos : 0 < max 1 (Nat.floor ((2 : ℝ) ^ (((max N 1 : ℕ) : ℝ) * R))) :=
        lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
      have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
      exact hα ⟨enc ⟨0, hn_pos⟩ ⟨0, hMpos⟩ (fun j => (Nat.not_lt_zero _ j.2).elim)⟩
    rw [dmcFeedbackCapacity, DMC.capacity, hfb_empty, hcap_empty]

end FeedbackCapacityTheorem

/-! ### 4. Silent-User MAC-with-Feedback Converse Corollary -/

section MACFeedbackSilentConverse

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- **Reduction from a MAC ignoring user 2 to a single-user DMC with feedback**:
    if `W(y | x₁, x₂) = V(y | x₁)` for all `x₁, x₂, y`, then any MAC feedback code achieving
    `(R₁, R₂)` directly induces a single-user DMC feedback code achieving `R₁` over `V`. -/
theorem isDmcFeedbackAchievable_of_isMACFeedbackAchievable_ignores_second
    (V : DMC X₁ Y) (W : MACChannel X₁ X₂ Y)
    (hW : ∀ x₁ x₂ y, W.trans (x₁, x₂) y = V.trans x₁ y)
    {R₁ R₂ : ℝ} (h : IsMACFeedbackAchievable W R₁ R₂) :
    IsDmcFeedbackAchievable V R₁ := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h.2.2 δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hc := hN n hn
  dsimp only at hc
  obtain ⟨enc₁, enc₂, dec, herr⟩ := hc
  let M₁ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  let M₂ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  refine ⟨enc₁, fun y => (dec y).1, ?_⟩
  have htrans : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂) (y : Fin n → Y),
      (∏ i : Fin n, W.trans
        (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
         enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)) =
      dmcFeedbackTrans V n M₁ enc₁ m₁ y := by
    intro m₁ m₂ y
    unfold dmcFeedbackTrans
    refine Finset.prod_congr rfl fun i _ => hW _ _ _
  have hpt : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂) (y : Fin n → Y),
      (if (dec y).1 ≠ m₁ then dmcFeedbackTrans V n M₁ enc₁ m₁ y else 0) ≤
      (if dec y ≠ (m₁, m₂) then
        ∏ i : Fin n, W.trans
          (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
           enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)
        else 0) := by
    intro m₁ m₂ y
    rw [htrans m₁ m₂ y]
    by_cases h1 : (dec y).1 ≠ m₁
    · have hne : dec y ≠ (m₁, m₂) := fun heq => h1 (congrArg Prod.fst heq)
      simp [h1, hne]
    · simp only [h1, ↓reduceIte]
      split_ifs
      · exact dmcFeedbackTrans_nonneg V n M₁ enc₁ m₁ y
      · exact le_rfl
  have hsum_le :
      ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, ∑ y : Fin n → Y,
        (if (dec y).1 ≠ m₁ then dmcFeedbackTrans V n M₁ enc₁ m₁ y else 0) ≤
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
        (if dec y ≠ (m₁, m₂) then
          ∏ i : Fin n, W.trans
            (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
             enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)
          else 0) :=
    Finset.sum_le_sum fun m₁ _ =>
      Finset.sum_le_sum fun m₂ _ =>
        Finset.sum_le_sum fun y _ => hpt m₁ m₂ y
  have havg_eq :
      dmcFeedbackAvgError V n M₁ enc₁ (fun y => (dec y).1) =
        ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, ∑ y : Fin n → Y,
            (if (dec y).1 ≠ m₁ then dmcFeedbackTrans V n M₁ enc₁ m₁ y else 0) := by
    unfold dmcFeedbackAvgError
    have hM₁ne : M₁ ≠ 0 := Nat.ne_of_gt hM₁
    have hM₁r : (M₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM₁ne
    have hM₂r : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM₂)
    simp only [hM₁ne, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    field_simp [hM₁r, hM₂r]
  have hcoeff : (0 : ℝ) ≤ (1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  calc dmcFeedbackAvgError V n M₁ enc₁ (fun y => (dec y).1)
    _ = ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, ∑ y : Fin n → Y,
            (if (dec y).1 ≠ m₁ then dmcFeedbackTrans V n M₁ enc₁ m₁ y else 0) := havg_eq
    _ ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
            (if dec y ≠ (m₁, m₂) then
              ∏ i : Fin n, W.trans
                (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
                 enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)
              else 0) := mul_le_mul_of_nonneg_left hsum_le hcoeff
    _ ≤ δ := herr

/-- **Silent-User MAC-with-Feedback Converse** (Cover & Thomas Thm. 7.12.1; El Gamal–Kim §17.1):
    if a two-user MAC `W` ignores user 2 (`W(y | x₁, x₂) = V(y | x₁)`), then every
    feedback-achievable rate pair `(R₁, R₂)` satisfies `R₁ ≤ C(V)`. -/
theorem isMACFeedbackAchievable_le_capacity_of_ignores_second
    (V : DMC X₁ Y) (W : MACChannel X₁ X₂ Y)
    (hW : ∀ x₁ x₂ y, W.trans (x₁, x₂) y = V.trans x₁ y)
    {R₁ R₂ : ℝ} (h : IsMACFeedbackAchievable W R₁ R₂) :
    R₁ ≤ V.capacity :=
  dmc_feedback_converse V
    (isDmcFeedbackAchievable_of_isMACFeedbackAchievable_ignores_second V W hW h)

/-- **Closure Corollary for `macFeedbackCapacityRegion`**:
    if `W(y | x₁, x₂) = V(y | x₁)`, then every rate pair `p ∈ macFeedbackCapacityRegion W`
    satisfies `p.1 ≤ C(V)`. -/
theorem macFeedbackCapacityRegion_fst_le_of_ignores_second
    (V : DMC X₁ Y) (W : MACChannel X₁ X₂ Y)
    (hW : ∀ x₁ x₂ y, W.trans (x₁, x₂) y = V.trans x₁ y)
    {p : ℝ × ℝ} (hp : p ∈ macFeedbackCapacityRegion W) :
    p.1 ≤ V.capacity := by
  have hsub : { q : ℝ × ℝ | IsMACFeedbackAchievable W q.1 q.2 } ⊆
      { q : ℝ × ℝ | q.1 ≤ V.capacity } :=
    fun _ hq => isMACFeedbackAchievable_le_capacity_of_ignores_second V W hW hq
  have hclosed : IsClosed { q : ℝ × ℝ | q.1 ≤ V.capacity } :=
    isClosed_Iic.preimage continuous_fst
  exact closure_minimal hsub hclosed hp

end MACFeedbackSilentConverse

end InfoTheory.Bridge
