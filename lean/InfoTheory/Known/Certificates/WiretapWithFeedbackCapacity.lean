import InfoTheory.Problems.WiretapWithFeedbackCapacity
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.BroadcastChannel
import InfoTheory.Known.Certificates.MacWithFeedback

/-!
# Certificate for `InfoTheory.Problems.WiretapWithFeedbackCapacity`

The frozen statement asks whether, for every finite DM wiretap channel `W(y, z | x)` with
noiseless secure output feedback, the operational secrecy capacity `wiretapFeedbackCapacity W`
equals the Ahlswede–Cai bound `ahlswedeCaiBound W = max_{P_X} min(I(X; Y), H(Y | Z))`.

## Certified (about exactly these objects)
* `wiretapFeedback_err_ge`, `le_log2_card_of_isWiretapFeedbackAchievable`,
  `wiretapFeedbackCapacity_le_log2_card` — a counting converse valid for every feedback code
  with private randomisation: decoding error `≥ 1 - |Y|ⁿ / M`, hence every achievable secrecy
  rate, and the operational capacity, is `≤ log₂ |Y|`. So the `sSup` is over a set that is
  bounded above (no junk value). `wiretapFeedbackCapacity_nonneg` — and it is `≥ 0`.
* `ahlswedeCaiBound_le_capacity` — the Ahlswede–Cai bound is at most the main channel's
  capacity `C(p(y | x))` (since `min(I(X;Y), H(Y|Z)) ≤ I(X;Y)`); `ahlswedeCaiBound_nonneg` —
  and it is `≥ 0`. So both sides of the statement are finite reals in
  `[0, max(C(p(y|x)), log₂ |Y|)] = [0, log₂ |Y|]`.

* **Regression** `mi_sub_mi_le_ahlswedeCaiBound`, `wynerRate_le_ahlswedeCaiBound` — the frozen
  formula is at least Wyner's no-feedback rate `sup_P [I(X;Y) - I(X;Z)]` (the secrecy capacity
  without feedback of degraded channels), via `I(X;Y) - I(X;Z) ≤ H(Y|Z)`
  (`mi_sub_mi_le_condEntropy`); `ahlswedeCaiBound_eq_capacity_of_subsingleton` — with a trivial
  eavesdropper it equals `C(p(y|x))`; `ahlswedeCaiBound_eq_zero_of_fun` — if `Y` is a function
  of `Z` it is `0`.

## Not certified
* The Ahlswede–Cai converse `C_s^{fb} ≤ ahlswedeCaiBound` and its achievability for degraded
  channels (secret key generation from the feedback + one-time pad), and the sharper
  operational bound `C_s^{fb} ≤ C(p(y|x))` (it needs the feedback converse, Cover–Thomas
  Thm. 7.12.1, not in the library).
* No statement-level conclusion: the problem is open.

Sources: Ahlswede–Cai, "Transmission, identification and common randomness capacities for
wire-tap channels with secure feedback from the decoder", 2006; El Gamal–Kim §22.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.WiretapWithFeedbackCapacity

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.WiretapWithFeedbackCapacity
open InfoTheory.Known.Certificates.BroadcastChannel (mi_fst_le_capacity)
open InfoTheory.Known.Certificates.MacWithFeedback (rate_le_log2_of_counting natMax_one_floor_ge
  natMax_one_pos)

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-! ### Counting converse for feedback wiretap codes -/

/-- **Counting converse**: for every feedback code with private randomness, the decoding error
    `∑ 1{dec(y) ≠ m} Q(m, y, z)` is at least `1 - |Y|ⁿ / M`. -/
theorem wiretapFeedback_err_ge (W : WiretapChannel X Y Z) {n M kR : ℕ} (hM : 0 < M)
    (Prand : ProbDist (Fin kR)) (enc : ∀ i : Fin n, Fin M → Fin kR → (Fin i.1 → Y) → X)
    (dec : (Fin n → Y) → Fin M) (Q : ProbDist (Fin M × (Fin n → Y) × (Fin n → Z)))
    (hQ : ∀ (m : Fin M) (y : Fin n → Y) (z : Fin n → Z),
      Q.pmf (m, y, z) = ((1 : ℝ) / (M : ℝ)) *
        ∑ r : Fin kR, Prand.pmf r *
          ∏ i : Fin n, W.trans (enc i m r (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, z i)) :
    1 - ((Fintype.card Y : ℝ) ^ n) / M ≤
      ∑ t : Fin M × (Fin n → Y) × (Fin n → Z), if dec t.2.1 ≠ t.1 then Q.pmf t else 0 := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  -- per-message total mass is `1/M`
  have hmass : ∀ m : Fin M, ∑ y : Fin n → Y, ∑ z : Fin n → Z, Q.pmf (m, y, z) = 1 / (M : ℝ) := by
    intro m
    have hT : ∀ r : Fin kR, ∑ p : (Fin n → Y) × (Fin n → Z), ∏ i : Fin n,
        W.trans (enc i m r (fun j => p.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (p.1 i, p.2 i) = 1 := by
      intro r
      let e : ((Fin n → Y) × (Fin n → Z)) ≃ (Fin n → Y × Z) :=
        { toFun := fun p i => (p.1 i, p.2 i)
          invFun := fun f => (fun i => (f i).1, fun i => (f i).2)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.sum_equiv e (fun p : (Fin n → Y) × (Fin n → Z) => ∏ i : Fin n,
        W.trans (enc i m r (fun j => p.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (p.1 i, p.2 i))
        (fun w => ∏ i : Fin n,
        W.trans (enc i m r (fun j => (w ⟨j.1, Nat.lt_trans j.2 i.2⟩).1)) (w i)) (fun _ => rfl)]
      exact sum_causal_prod_eq_one n (fun i h b => W.trans (enc i m r (fun j => (h j).1)) b)
        (fun i h => W.sum_one _)
    rw [← Fintype.sum_prod_type']
    simp_rw [hQ]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hT, mul_one, Prand.sum_one, mul_one]
  -- success probability is at most `|Y|ⁿ / M`
  have hsucc : ∑ t : Fin M × (Fin n → Y) × (Fin n → Z), (if dec t.2.1 = t.1 then Q.pmf t else 0)
      ≤ (Fintype.card Y : ℝ) ^ n / M := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc ∑ y : Fin n → Y, ∑ m : Fin M, ∑ z : Fin n → Z,
          (if dec (m, y, z).2.1 = (m, y, z).1 then Q.pmf (m, y, z) else 0)
        = ∑ y : Fin n → Y, ∑ z : Fin n → Z, Q.pmf (dec y, y, z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_eq_single (dec y)]
          · simp
          · intro m _ hm
            exact Finset.sum_eq_zero fun z _ => by simp [Ne.symm hm]
          · simp
      _ ≤ ∑ _y : Fin n → Y, 1 / (M : ℝ) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [← hmass (dec y)]
          calc ∑ z : Fin n → Z, Q.pmf (dec y, y, z)
              ≤ ∑ y' : Fin n → Y, ∑ z : Fin n → Z, Q.pmf (dec y, y', z) :=
                Finset.single_le_sum (f := fun y' => ∑ z : Fin n → Z, Q.pmf (dec y, y', z))
                  (fun y' _ => Finset.sum_nonneg fun z _ => Q.nonneg _) (Finset.mem_univ y)
            _ = _ := rfl
      _ = (Fintype.card Y : ℝ) ^ n / M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hsplit : ∑ t : Fin M × (Fin n → Y) × (Fin n → Z), (if dec t.2.1 ≠ t.1 then Q.pmf t else 0)
      = 1 - ∑ t : Fin M × (Fin n → Y) × (Fin n → Z),
        (if dec t.2.1 = t.1 then Q.pmf t else 0) := by
    rw [← Q.sum_one, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : dec t.2.1 = t.1 <;> simp [h]
  rw [hsplit]
  linarith

/-- Every feedback-achievable secrecy rate satisfies `R ≤ log₂ |Y|`. -/
theorem le_log2_card_of_isWiretapFeedbackAchievable [Nonempty Y] (W : WiretapChannel X Y Z)
    {R : ℝ} (h : IsWiretapFeedbackAchievable W R) : R ≤ log2 (Fintype.card Y) := by
  obtain ⟨hR, h⟩ := h
  refine rate_le_log2_of_counting Fintype.card_pos (by norm_num : (0 : ℝ) < 1 / 2)
    fun ε hε => ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨kR, Prand, enc, dec, Q, hQ, herr, -⟩ := hN n hn
  refine ⟨((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ), ?_,
    le_trans (wiretapFeedback_err_ge W (natMax_one_pos _) Prand enc dec Q hQ) herr⟩
  have := natMax_one_floor_ge n hR
  linarith

theorem wiretapFeedbackCapacity_le_log2_card [Nonempty Y] (W : WiretapChannel X Y Z) :
    wiretapFeedbackCapacity W ≤ log2 (Fintype.card Y) := by
  refine Real.sSup_le (fun R hR => le_log2_card_of_isWiretapFeedbackAchievable W hR) ?_
  unfold log2
  exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos one_lt_two).le

theorem wiretapFeedbackCapacity_nonneg (W : WiretapChannel X Y Z) :
    0 ≤ wiretapFeedbackCapacity W :=
  Real.sSup_nonneg fun _ hR => hR.1

/-! ### The Ahlswede–Cai bound -/

theorem ahlswedeCaiBound_nonneg (W : WiretapChannel X Y Z) : 0 ≤ ahlswedeCaiBound W := by
  unfold ahlswedeCaiBound
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨P, rfl⟩ := hr
  exact le_min (mutualInfo_nonneg _) (condEntropy_nonneg _)

/-- **The Ahlswede–Cai bound is at most the main channel's capacity** `C(p(y | x))`. -/
theorem ahlswedeCaiBound_le_capacity (W : WiretapChannel X Y Z) :
    ahlswedeCaiBound W ≤ (marginalFst W).capacity := by
  unfold ahlswedeCaiBound
  refine Real.sSup_le (fun r hr => ?_) (capacity_nonneg _)
  obtain ⟨P, rfl⟩ := hr
  exact min_le_of_left_le (mi_fst_le_capacity W P id (W.joint P) (fun _ => rfl) id)

theorem ahlswedeCaiBound_le_log2_card (W : WiretapChannel X Y Z) :
    ahlswedeCaiBound W ≤ log2 (Fintype.card Y) :=
  (ahlswedeCaiBound_le_capacity W).trans (capacity_le_log_card_output _)

/-! ### Regression: the frozen Ahlswede–Cai formula in solved cases -/

section Regression

open InfoTheory.Known.Certificates.BroadcastChannel (joint_map_fst_eq)

/-- Entropy bookkeeping for `J = W.joint P` on `X × (Y × Z)`:
    `I(X;Y) - I(X;Z) ≤ H(Y|Z)` (since `I(X;Y) ≤ I(X;Y,Z)` and `H(Y|X,Z) ≥ 0`). -/
theorem mi_sub_mi_le_condEntropy (J : ProbDist (X × (Y × Z))) :
    mutualInfo (J.map (fun t => (t.1, t.2.1))) - mutualInfo (J.map (fun t => (t.1, t.2.2))) ≤
      condEntropy (J.map (fun t => (t.2.1, t.2.2))) := by
  have f1 : (J.map (fun t => (t.1, t.2.1))).fst = J.map (fun t => t.1) := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have f2 : (J.map (fun t => (t.1, t.2.1))).snd = J.map (fun t => t.2.1) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have f3 : (J.map (fun t => (t.1, t.2.2))).fst = J.map (fun t => t.1) := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have f4 : (J.map (fun t => (t.1, t.2.2))).snd = J.map (fun t => t.2.2) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have f5 : (J.map (fun t => (t.2.1, t.2.2))).snd = J.map (fun t => t.2.2) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  -- `I(X; Z | Y) ≥ 0`
  have hc := condMutualInfo_nonneg (J.map (fun t => (t.1, t.2.2, t.2.1)))
  unfold condMutualInfo at hc
  dsimp only at hc
  have g1 : (J.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => (t.1, t.2.2)) =
      J.map (fun t => (t.1, t.2.1)) := by rw [map_comp_eq]; rfl
  have g2 : (J.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => (t.2.1, t.2.2)) =
      (J.map (fun t => (t.2.1, t.2.2))).map Prod.swap := by rw [map_comp_eq, map_comp_eq]; rfl
  have g3 : (J.map (fun t => (t.1, t.2.2, t.2.1))).map (fun t => t.2.2) =
      J.map (fun t => t.2.1) := by rw [map_comp_eq]; rfl
  rw [g1, g2, g3, shannonEntropy_map_of_injective _ Prod.swap_injective] at hc
  -- `H(X, Z, Y) ≥ H(X, Z)`
  have hm := shannonEntropy_map_le (fun p : X × Z × Y => (p.1, p.2.1))
    (J.map (fun t => (t.1, t.2.2, t.2.1)))
  rw [map_comp_eq] at hm
  have hm' : shannonEntropy (J.map ((fun p : X × Z × Y => (p.1, p.2.1)) ∘
      (fun t => (t.1, t.2.2, t.2.1)))) = shannonEntropy (J.map (fun t => (t.1, t.2.2))) := rfl
  rw [hm'] at hm
  unfold mutualInfo condEntropy
  rw [f1, f2, f3, f4, f5]
  linarith

theorem ahlswedeCai_bddAbove (W : WiretapChannel X Y Z) :
    BddAbove { r : ℝ | ∃ (P : ProbDist X),
      r = min (mutualInfo ((W.joint P).map (fun t => (t.1, t.2.1))))
              (condEntropy ((W.joint P).map (fun t => (t.2.1, t.2.2)))) } := by
  refine ⟨(marginalFst W).capacity, fun r hr => ?_⟩
  obtain ⟨P, rfl⟩ := hr
  exact min_le_of_left_le (mi_fst_le_capacity W P id (W.joint P) (fun _ => rfl) id)

/-- **Regression (no feedback, Wyner / Csiszár–Körner)**: for every input law,
    `I(X;Y) - I(X;Z) ≤ ahlswedeCaiBound W`. For a degraded wiretap channel the supremum of the
    left side over `P` is Wyner's secrecy capacity without feedback, so the frozen formula is at
    least the no-feedback secrecy capacity there (feedback cannot hurt). -/
theorem mi_sub_mi_le_ahlswedeCaiBound (W : WiretapChannel X Y Z) (P : ProbDist X) :
    mutualInfo ((W.joint P).map (fun t => (t.1, t.2.1))) -
        mutualInfo ((W.joint P).map (fun t => (t.1, t.2.2))) ≤ ahlswedeCaiBound W := by
  refine le_trans (le_min ?_ (mi_sub_mi_le_condEntropy (W.joint P)))
    (le_csSup (ahlswedeCai_bddAbove W) ⟨P, rfl⟩)
  linarith [mutualInfo_nonneg ((W.joint P).map (fun t => (t.1, t.2.2)))]

/-- The supremum form: Wyner's rate `sup_P [I(X;Y) - I(X;Z)]` is at most the frozen bound. -/
theorem wynerRate_le_ahlswedeCaiBound [Nonempty X] (W : WiretapChannel X Y Z) :
    sSup { r : ℝ | ∃ P : ProbDist X, r = mutualInfo ((W.joint P).map (fun t => (t.1, t.2.1))) -
        mutualInfo ((W.joint P).map (fun t => (t.1, t.2.2))) } ≤ ahlswedeCaiBound W :=
  csSup_le ⟨_, ⟨ProbDist.uniform, rfl⟩⟩ (fun _ ⟨P, hr⟩ => hr ▸ mi_sub_mi_le_ahlswedeCaiBound W P)

/-- **Regression (useless eavesdropper)**: if `Z` is trivial, the frozen formula is exactly the
    main channel's capacity `C(p(y|x))` (the known secrecy capacity, with or without feedback). -/
theorem ahlswedeCaiBound_eq_capacity_of_subsingleton [Nonempty X] [Subsingleton Z]
    [Nonempty Z] (W : WiretapChannel X Y Z) :
    ahlswedeCaiBound W = (marginalFst W).capacity := by
  refine le_antisymm (ahlswedeCaiBound_le_capacity W) ?_
  refine csSup_le ⟨_, ⟨ProbDist.uniform, rfl⟩⟩ (fun r hr => ?_)
  obtain ⟨P, rfl⟩ := hr
  set J := W.joint P
  have hm : (marginalFst W).mutualInfo P = mutualInfo (J.map (fun t => (t.1, t.2.1))) := by
    rw [joint_map_fst_eq W P id J (fun _ => rfl)]; rfl
  rw [hm]
  refine le_trans (le_min le_rfl ?_) (le_csSup (ahlswedeCai_bddAbove W) ⟨P, rfl⟩)
  -- `I(X;Y) ≤ H(Y) ≤ H(Y,Z) = H(Y|Z) + H(Z)` and `H(Z) = 0`
  have hz : (J.map (fun t => (t.2.1, t.2.2))).snd = J.map (fun _ => Classical.arbitrary Z) := by
    rw [← map_snd_eq_snd, map_comp_eq]
    congr 1
    funext t
    exact Subsingleton.elim _ _
  have h1 : (J.map (fun t => (t.1, t.2.1))).fst = J.map (fun t => t.1) := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have h2 : (J.map (fun t => (t.1, t.2.1))).snd = J.map (fun t => t.2.1) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have m1 := shannonEntropy_map_le (fun p : X × Y => p.1) (J.map (fun t => (t.1, t.2.1)))
  have m2 := shannonEntropy_map_le (fun p : Y × Z => p.1) (J.map (fun t => (t.2.1, t.2.2)))
  rw [map_comp_eq] at m1 m2
  have m1' : shannonEntropy (J.map ((fun p : X × Y => p.1) ∘ fun t => (t.1, t.2.1))) =
      shannonEntropy (J.map (fun t => t.1)) := rfl
  have m2' : shannonEntropy (J.map ((fun p : Y × Z => p.1) ∘ fun t => (t.2.1, t.2.2))) =
      shannonEntropy (J.map (fun t => t.2.1)) := rfl
  rw [m1'] at m1
  rw [m2'] at m2
  unfold mutualInfo condEntropy
  rw [hz, shannonEntropy_map_const, h1, h2]
  linarith

/-- **Regression (eavesdropper sees the main output)**: if `Y` is a function of `Z` on the
    support of the channel, the frozen formula is `0` (no secrecy is possible, even with
    feedback: the eavesdropper also sees the feedback signal). -/
theorem ahlswedeCaiBound_eq_zero_of_fun (W : WiretapChannel X Y Z) (ψ : Z → Y)
    (hψ : ∀ x y z, W.trans x (y, z) ≠ 0 → y = ψ z) : ahlswedeCaiBound W = 0 := by
  refine le_antisymm ?_ (ahlswedeCaiBound_nonneg W)
  unfold ahlswedeCaiBound
  refine Real.sSup_nonpos (fun r hr => ?_)
  obtain ⟨P, rfl⟩ := hr
  refine min_le_of_right_le (le_of_eq ?_)
  set J := W.joint P
  have hsupp : J.map (fun t => (t.2.1, t.2.2)) = (J.map (fun t => t.2.2)).map (fun z => (ψ z, z)) := by
    rw [map_comp_eq]
    refine map_congr_of_support J (fun t ht => ?_)
    have hw : W.trans t.1 t.2 ≠ 0 := right_ne_zero_of_mul ht
    have := hψ t.1 t.2.1 t.2.2 hw
    simp only [Function.comp_apply, this]
  have hz : (J.map (fun t => (t.2.1, t.2.2))).snd = J.map (fun t => t.2.2) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  unfold condEntropy
  rw [hz, hsupp, shannonEntropy_map_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
  ring

end Regression

end InfoTheory.Known.Certificates.WiretapWithFeedbackCapacity
