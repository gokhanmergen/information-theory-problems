import InfoTheory.Problems.PrimitiveRelayChannelBsc
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.PrimitiveRelayChannelBsc`

The frozen statement asks whether, for the symmetric primitive BSC relay channel
(`p₁ = p₂ = p ∈ (0, 1/2)`, relay bit-pipe rate `R₀ ≥ 0`), the operational capacity
`primitiveBscRelayCapacity p p R₀` equals the time-shared compress-and-forward rate
`primitiveBscCFRateConcave p p R₀`.

## Certified (about exactly these objects, for all `p₁, p₂ ∈ [0, 1]`)
* `isDmcAchievableRate_of_primitive`, `primitiveBscRelayCapacity_le_cutset` — the
  **broadcast-cut half of the cutset bound** (Cover–El Gamal 1979; El Gamal–Kim §16.2):
  a primitive relay code is a point-to-point code for `X → (Y, Y_r)` (the destination's
  decoder composed with the relay map), so `C_BSC(p₁, p₂, R₀) ≤ C(X → (Y, Y_r))`
  (Shannon converse, `Bridge.shannon_channel_coding_converse`). Also
  `bscRelayBroadcast_capacity_le_one`: this is `≤ 1`.
* `marginalFst_bscRelayBroadcast`, `isPrimitive_of_direct`,
  `one_sub_binaryEntropy_le_primitiveBscRelayCapacity` — the **direct-link lower bound**
  `1 - h(p₁) ≤ C_BSC(p₁, p₂, R₀)` (ignore the relay; Shannon achievability for `BSC(p₁)`
  together with `Known.bsc_capacity`).
* `isPrimitive_of_dmc_of_one_le`, `primitiveBscRelayCapacity_eq_of_one_le` — the **solved
  regime `R₀ ≥ 1`**: the relay forwards `Y_rⁿ` losslessly through the pipe, so
  `C_BSC(p₁, p₂, R₀) = C(X → (Y, Y_r))`. This is the "compress-forward meets the cutset bound"
  regime `R₀ ≥ H(Y_r | Y) = h(p₁ ⋆ p₂)` of the problem file, in the weaker form `R₀ ≥ 1`
  (lossless forwarding without Slepian–Wolf binning).
* `primitiveBscCFRate_le_one`, `one_sub_binaryEntropy_le_primitiveBscCFRate`,
  `primitiveBscCFRateConcave_le_one`, `one_sub_binaryEntropy_le_primitiveBscCFRateConcave` —
  the right-hand side of the statement lies in `[1 - h(p₁), 1]` (lower bound: take the
  compression `U` constant, so the Wyner–Ziv penalty `I(U; Y_r | X, Y)` vanishes and the rate is
  `I(X; Y) = 1 - h(p₁)` for uniform `X`).
* `statement_sides_mem_Icc` — for every instance of the statement, **both sides lie in
  `[1 - h(p), 1]`**, so the equation compares two genuine finite values (no junk).

* **Regression at the solved endpoint `R₀ = 0`** — `primitiveBscRelayCapacity_zero`:
  `C_BSC(p₁, p₂, 0) = 1 - h(p₁)` (a relay index in `Fin 1` carries nothing:
  `isDmcAchievableRate_of_primitive_zero`); `primitiveBscCFRateConcave_zero`: the time-shared CF
  formula at `R₀ = 0` is also `1 - h(p₁)` (`∑ wᵢRᵢ ≤ 0` forces the active `Rᵢ = 0`, and
  `R_CF(0) ≤ I(X;Y) ≤ 1 - h(p₁)`); hence `statement_at_zero`: **the frozen statement holds at
  `R₀ = 0`**.

## Not certified
* The MAC-cut half `C_BSC ≤ 1 - h(p₁) + R₀` of the cutset bound: it needs Fano's inequality
  for a decoder that also sees the relay index (`I(M; Yⁿ, J) ≤ I(Xⁿ; Yⁿ) + log |J|`); the
  library's Fano converse covers only point-to-point codes.
* Achievability of `primitiveBscCFRate` (Wyner–Ziv compress-and-forward) and the
  decode-and-forward regime: Wyner–Ziv source coding (`Bridge.wynerZiv_achievability`) and
  superposition coding are now in `Bridge` (db659ea), but not yet combined into relay codes.
* The exact `R₀ ≥ h(p₁ ⋆ p₂)` threshold (needs Slepian–Wolf binning with side information).
* No statement-level conclusion: the problem is open (El Gamal–Gohari–Nair 2022 and
  Wu–Barnes–Özgür 2019 only show that the cutset bound is loose).

Sources: Cover, "The capacity of the relay channel", 1987; Kim, Allerton 2007;
El Gamal–Kim, *Network Information Theory*, §16.2 and §16.7.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.PrimitiveRelayChannelBsc

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.PrimitiveRelayChannelBsc

section Helpers

lemma natMax_one_pos (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem dmc_ext {α β : Type*} [Fintype α] [Fintype β] {V V' : DMC α β}
    (h : ∀ x y, V.trans x y = V'.trans x y) : V = V' := by
  cases V; cases V'
  congr
  funext x y
  exact h x y

/-- If every `0 ≤ r < C` lies in a set `S` that is bounded above and contains `0`,
    then `C ≤ sSup S`. -/
theorem le_csSup_of_forall_Ico {S : Set ℝ} {C : ℝ} (hb : BddAbove S) (h0 : (0 : ℝ) ∈ S)
    (h : ∀ r, 0 ≤ r → r < C → r ∈ S) : C ≤ sSup S := by
  by_contra hlt
  push Not at hlt
  have hs0 : 0 ≤ sSup S := le_csSup hb h0
  have := le_csSup hb (h ((sSup S + C) / 2) (by linarith) (by linarith))
  linarith

theorem log2_card_bool : log2 (Fintype.card Bool : ℝ) = 1 := by
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  exact div_self (Real.log_pos one_lt_two).ne'

/-- Conditional mutual information vanishes when the first variable is constant. -/
theorem condMutualInfo_eq_zero_of_subsingleton_fst {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Subsingleton α] (P : ProbDist (α × β × γ)) : condMutualInfo P = 0 := by
  classical
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · exfalso
    have : ∑ t : α × β × γ, P.pmf t = 0 :=
      Finset.sum_eq_zero fun t _ => (IsEmpty.false t.1).elim
    linarith [P.sum_one]
  have hc1 : Function.Injective (fun c : γ => (a₀, c)) := fun x y h => (Prod.mk.inj h).2
  have hc2 : Function.Injective (fun bc : β × γ => (a₀, bc.1, bc.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.1 h.2.2
  have h1 : P.map (fun t => (t.1, t.2.2)) = (P.map (fun t => t.2.2)).map (fun c => (a₀, c)) := by
    rw [map_comp_eq]
    congr 1
    funext t
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have h2 : shannonEntropy P =
      shannonEntropy ((P.map (fun t => (t.2.1, t.2.2))).map (fun bc => (a₀, bc.1, bc.2))) := by
    rw [map_comp_eq, ← shannonEntropy_map_equiv (Equiv.refl _) P]
    congr 2
    funext t
    exact Prod.ext (Subsingleton.elim _ _) rfl
  unfold condMutualInfo
  dsimp only
  rw [h1, h2, shannonEntropy_map_of_injective _ hc1, shannonEntropy_map_of_injective _ hc2]
  ring

/-- The trivial test channel into `Fin 1`. -/
def trivialTest (α : Type*) [Fintype α] : DMC α (Fin 1) where
  trans _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

end Helpers

variable {p₁ p₂ : ℝ} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1) (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1)

/-! ### Cutset (broadcast cut) upper bound -/

/-- **Broadcast cut** (Cover–El Gamal 1979): a primitive relay code is a point-to-point code for
    the DMC `X → (Y, Y_r)`, with decoder `y ↦ dec(y₁, relay(y_r))` and the same error. -/
theorem isDmcAchievableRate_of_primitive {R₀ R : ℝ}
    (h : IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 R₀ R) :
    IsDmcAchievableRate (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21) R := by
  classical
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, relay, dec, herr⟩ := hN n hn
  refine ⟨enc, fun y => dec (fun i => (y i).1) (relay (fun i => (y i).2)), le_of_eq_of_le ?_ herr⟩
  have hM : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold dmcAvgError
  rw [ite_eq_right hM]

theorem bscRelayBroadcast_capacity_le_one :
    (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).capacity ≤ 1 :=
  (capacity_le_log_card_input _).trans (le_of_eq log2_card_bool)

/-! ### Direct-link lower bound -/

/-- The destination's marginal of `BSC(p₁) × BSC(p₂)` is `BSC(p₁)`. -/
theorem marginalFst_bscRelayBroadcast :
    marginalFst (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21) = bsc p₁ h10 h11 := by
  refine dmc_ext fun x y => ?_
  simp only [marginalFst, bscRelayBroadcast, bsc, Fintype.sum_bool]
  cases x <;> cases y <;> simp <;> ring

/-- **Direct transmission** (El Gamal–Kim §16.1): a code for `BSC(p₁)` whose decoder ignores
    the relay index is a primitive relay code with the same error. -/
theorem isPrimitive_of_direct {R₀ R : ℝ} (h : IsDmcAchievableRate (bsc p₁ h10 h11) R) :
    IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 R₀ R := by
  classical
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  refine ⟨enc, fun _ => ⟨0, natMax_one_pos _⟩, fun y₁ _ => dec y₁, ?_⟩
  rw [← marginalFst_bscRelayBroadcast h10 h11 h20 h21] at herr
  refine le_of_eq_of_le ?_ herr
  have hM : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold dmcAvgError
  rw [ite_eq_right hM]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  exact sum_ite_fst_power _ (enc m) (fun a => dec a ≠ m)

theorem isPrimitive_zero (R₀ : ℝ) : IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 R₀ 0 :=
  isPrimitive_of_direct h10 h11 h20 h21 (isDmcAchievableRate_zero _)

theorem isPrimitive_bddAbove (R₀ : ℝ) :
    BddAbove { R : ℝ | IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 R₀ R } :=
  ⟨_, fun R hR => shannon_channel_coding_converse _ R
    (isDmcAchievableRate_of_primitive h10 h11 h20 h21 hR)⟩

/-- **Cutset (broadcast cut) upper bound**: `C_BSC(p₁, p₂, R₀) ≤ C(X → (Y, Y_r))`. -/
theorem primitiveBscRelayCapacity_le_cutset (R₀ : ℝ) :
    primitiveBscRelayCapacity p₁ p₂ h10 h11 h20 h21 R₀ ≤
      (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).capacity :=
  csSup_le ⟨0, isPrimitive_zero h10 h11 h20 h21 R₀⟩ fun R hR =>
    shannon_channel_coding_converse _ R (isDmcAchievableRate_of_primitive h10 h11 h20 h21 hR)

theorem primitiveBscRelayCapacity_le_one (R₀ : ℝ) :
    primitiveBscRelayCapacity p₁ p₂ h10 h11 h20 h21 R₀ ≤ 1 :=
  (primitiveBscRelayCapacity_le_cutset h10 h11 h20 h21 R₀).trans
    (bscRelayBroadcast_capacity_le_one h10 h11 h20 h21)

/-- **Direct-link lower bound**: `1 - h(p₁) ≤ C_BSC(p₁, p₂, R₀)`. -/
theorem one_sub_binaryEntropy_le_primitiveBscRelayCapacity (R₀ : ℝ) :
    1 - binaryEntropy p₁ ≤ primitiveBscRelayCapacity p₁ p₂ h10 h11 h20 h21 R₀ := by
  rw [← bsc_capacity h10 h11]
  exact le_csSup_of_forall_Ico (isPrimitive_bddAbove h10 h11 h20 h21 R₀)
    (isPrimitive_zero h10 h11 h20 h21 R₀) fun r hr0 hr =>
      isPrimitive_of_direct h10 h11 h20 h21 (shannon_channel_coding_achievability _ r hr0 hr)

/-! ### The solved regime `R₀ ≥ 1`: lossless forwarding -/

/-- **Lossless forwarding** (El Gamal–Kim §16.7): if `R₀ ≥ 1`, the pipe carries all of `Y_rⁿ`,
    so every point-to-point code for `X → (Y, Y_r)` becomes a primitive relay code. -/
theorem isPrimitive_of_dmc_of_one_le {R₀ R : ℝ} (hR₀ : 1 ≤ R₀)
    (h : IsDmcAchievableRate (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21) R) :
    IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 R₀ R := by
  classical
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  have hcard : Fintype.card (Fin n → Bool) ≤
      Fintype.card (Fin (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₀))))) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
    refine le_trans (Nat.le_floor ?_) (le_max_right _ _)
    push_cast
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hg : ∀ v, Function.invFun f (f v) = v := Function.leftInverse_invFun f.injective
  refine ⟨enc, f, fun y₁ j => dec (fun i => (y₁ i, Function.invFun f j i)), le_of_eq_of_le ?_ herr⟩
  have hM : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold dmcAvgError
  rw [ite_eq_right hM]
  simp only [hg, Prod.mk.eta]

/-- **Solved regime**: for `R₀ ≥ 1`, `C_BSC(p₁, p₂, R₀) = C(X → (Y, Y_r))` (the cutset bound). -/
theorem primitiveBscRelayCapacity_eq_of_one_le {R₀ : ℝ} (hR₀ : 1 ≤ R₀) :
    primitiveBscRelayCapacity p₁ p₂ h10 h11 h20 h21 R₀ =
      (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).capacity :=
  le_antisymm (primitiveBscRelayCapacity_le_cutset h10 h11 h20 h21 R₀)
    (le_csSup_of_forall_Ico (isPrimitive_bddAbove h10 h11 h20 h21 R₀)
      (isPrimitive_zero h10 h11 h20 h21 R₀) fun r hr0 hr =>
        isPrimitive_of_dmc_of_one_le h10 h11 h20 h21 hR₀
          (shannon_channel_coding_achievability _ r hr0 hr))

/-! ### The compress-and-forward side of the statement -/

/-- `I(X; Y) = 1 - h(p₁)` for uniform input to `BSC(p₁)`. -/
theorem bsc_mutualInfo_uniform :
    mutualInfo ((bsc p₁ h10 h11).joint ProbDist.uniform) = 1 - binaryEntropy p₁ := by
  have h := bsc_mutualInfo h10 h11 ProbDist.uniform
  unfold DMC.mutualInfo at h
  rw [h]
  have : shannonEntropy ((bsc p₁ h10 h11).joint ProbDist.uniform).snd = 1 := by
    unfold shannonEntropy
    simp_rw [bsc_joint_uniform_snd_pmf]
    rw [Fintype.sum_bool]
    have := binaryEntropy_half
    unfold binaryEntropy at this
    norm_num at this ⊢
    linarith
  rw [this]

/-- For a CF joint law with uniform input and constant compression, the `(X, Y)` marginal is
    the uniform-input `BSC(p₁)` joint law. -/
theorem cf_map_xy (J : ProbDist (Bool × (Bool × Bool) × Fin 1))
    (hJ : ∀ t, J.pmf t = (ProbDist.uniform : ProbDist Bool).pmf t.1 *
      (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).trans t.1 t.2.1 * 1) :
    J.map (fun t => (t.1, t.2.1.1)) = (bsc p₁ h10 h11).joint ProbDist.uniform := by
  classical
  refine probDist_eq_of_pmf fun xy => ?_
  obtain ⟨x, y⟩ := xy
  simp only [ProbDist.map, hJ, DMC.joint, bsc, bscRelayBroadcast, ProbDist.uniform,
    Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_one, Fintype.card_bool]
  cases x <;> cases y <;> simp <;> ring

/-- The CF objective with uniform input and constant compression is at least `1 - h(p₁)`. -/
theorem cf_lower (J : ProbDist (Bool × (Bool × Bool) × Fin 1))
    (hJ : ∀ t, J.pmf t = (ProbDist.uniform : ProbDist Bool).pmf t.1 *
      (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).trans t.1 t.2.1 * 1) {R : ℝ} (hR : 0 ≤ R) :
    1 - binaryEntropy p₁ ≤ min (mutualInfo (J.map (fun t => (t.1, (t.2.1.1, t.2.2)))))
      (mutualInfo (J.map (fun t => (t.1, t.2.1.1))) + R -
        condMutualInfo (J.map (fun t => (t.2.2, t.2.1.2, (t.1, t.2.1.1))))) := by
  have hxy : mutualInfo (J.map (fun t => (t.1, t.2.1.1))) = 1 - binaryEntropy p₁ := by
    rw [cf_map_xy h10 h11 h20 h21 J hJ, bsc_mutualInfo_uniform]
  have hb1 : mutualInfo (J.map (fun t => (t.1, t.2.1.1))) ≤
      mutualInfo (J.map (fun t => (t.1, (t.2.1.1, t.2.2)))) := by
    have := mutualInfo_map_right_le (J.map (fun t => (t.1, (t.2.1.1, t.2.2)))) Prod.fst
    rw [map_comp_eq] at this
    exact this
  refine le_min (by linarith) ?_
  rw [condMutualInfo_eq_zero_of_subsingleton_fst, sub_zero]
  linarith

theorem primitiveBscCFRate_le_one (R : ℝ) :
    primitiveBscCFRate p₁ p₂ h10 h11 h20 h21 R ≤ 1 := by
  unfold primitiveBscCFRate
  refine Real.sSup_le (fun r hr => ?_) zero_le_one
  obtain ⟨kU, Px, Q, rfl⟩ := hr
  exact min_le_of_left_le ((mutualInfo_le_entropy_fst _).trans
    ((shannonEntropy_le_log2_card _).trans (le_of_eq log2_card_bool)))

/-- **CF with constant compression** gives `I(X; Y) = 1 - h(p₁)`:
    `1 - h(p₁) ≤ R_CF(p₁, p₂, R)` for every `R ≥ 0`. -/
theorem one_sub_binaryEntropy_le_primitiveBscCFRate {R : ℝ} (hR : 0 ≤ R) :
    1 - binaryEntropy p₁ ≤ primitiveBscCFRate p₁ p₂ h10 h11 h20 h21 R := by
  unfold primitiveBscCFRate
  refine le_csSup_of_le ⟨1, fun r hr => ?_⟩ ⟨1, ProbDist.uniform, trivialTest Bool, rfl⟩ ?_
  · obtain ⟨kU, Px, Q, rfl⟩ := hr
    exact min_le_of_left_le ((mutualInfo_le_entropy_fst _).trans
      ((shannonEntropy_le_log2_card _).trans (le_of_eq log2_card_bool)))
  · exact cf_lower h10 h11 h20 h21 _ (fun t => rfl) hR

theorem primitiveBscCFRateConcave_le_one (R₀ : ℝ) :
    primitiveBscCFRateConcave p₁ p₂ h10 h11 h20 h21 R₀ ≤ 1 := by
  unfold primitiveBscCFRateConcave
  refine Real.sSup_le (fun r hr => ?_) zero_le_one
  obtain ⟨m, w, Rs, hw0, hw1, -, -, rfl⟩ := hr
  calc ∑ i : Fin m, w i * primitiveBscCFRate p₁ p₂ h10 h11 h20 h21 (Rs i)
      ≤ ∑ i : Fin m, w i * 1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (primitiveBscCFRate_le_one h10 h11 h20 h21 _) (hw0 i)
    _ = 1 := by simp [hw1]

theorem one_sub_binaryEntropy_le_primitiveBscCFRateConcave {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    1 - binaryEntropy p₁ ≤ primitiveBscCFRateConcave p₁ p₂ h10 h11 h20 h21 R₀ := by
  unfold primitiveBscCFRateConcave
  refine le_csSup_of_le ⟨1, fun r hr => ?_⟩
    ⟨1, fun _ => 1, fun _ => R₀, fun _ => zero_le_one, by simp, fun _ => hR₀, by simp, rfl⟩ ?_
  · obtain ⟨m, w, Rs, hw0, hw1, -, -, rfl⟩ := hr
    calc ∑ i : Fin m, w i * primitiveBscCFRate p₁ p₂ h10 h11 h20 h21 (Rs i)
        ≤ ∑ i : Fin m, w i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (primitiveBscCFRate_le_one h10 h11 h20 h21 _) (hw0 i)
      _ = 1 := by simp [hw1]
  · simpa using one_sub_binaryEntropy_le_primitiveBscCFRate h10 h11 h20 h21 hR₀

/-- **Both sides of the statement lie in `[1 - h(p), 1]`.** -/
theorem statement_sides_mem_Icc (p R₀ : ℝ) (h0 : 0 < p) (h1 : p < 1 / 2) (hR₀ : 0 ≤ R₀) :
    primitiveBscRelayCapacity p p (le_of_lt h0) (by linarith) (le_of_lt h0) (by linarith) R₀ ∈
        Set.Icc (1 - binaryEntropy p) 1 ∧
      primitiveBscCFRateConcave p p (le_of_lt h0) (by linarith) (le_of_lt h0) (by linarith) R₀ ∈
        Set.Icc (1 - binaryEntropy p) 1 :=
  ⟨⟨one_sub_binaryEntropy_le_primitiveBscRelayCapacity _ _ _ _ R₀,
      primitiveBscRelayCapacity_le_one _ _ _ _ R₀⟩,
    ⟨one_sub_binaryEntropy_le_primitiveBscCFRateConcave _ _ _ _ hR₀,
      primitiveBscCFRateConcave_le_one _ _ _ _ R₀⟩⟩

/-! ### Regression: the solved endpoint `R₀ = 0`

With no relay link the channel is the direct link `BSC(p₁)`, whose capacity is `1 - h(p₁)`.
Both sides of the frozen statement reduce to this value: the operational side because a
relay index in `Fin 1` carries nothing, the compress-and-forward side because with
`∑ wᵢ Rᵢ ≤ 0` every active `Rᵢ` is `0` and then `R_CF(0) ≤ I(X; Y) ≤ 1 - h(p₁)`. -/

section Regression

/-- With `R₀ = 0` the relay index is constant, so a primitive relay code is a code for the
    direct link `BSC(p₁)` with the same error. -/
theorem isDmcAchievableRate_of_primitive_zero {R : ℝ}
    (h : IsPrimitiveBscAchievable p₁ p₂ h10 h11 h20 h21 0 R) :
    IsDmcAchievableRate (bsc p₁ h10 h11) R := by
  classical
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, relay, dec, herr⟩ := hN n hn
  have hM0 : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by simp
  have hrel : ∀ v, relay v = ⟨0, natMax_one_pos _⟩ := fun v =>
    Fin.ext (by have h2 : ((relay v) : ℕ) < 1 := lt_of_lt_of_eq (relay v).2 hM0; simp; omega)
  refine ⟨enc, fun y₁ => dec y₁ ⟨0, natMax_one_pos _⟩, ?_⟩
  rw [← marginalFst_bscRelayBroadcast h10 h11 h20 h21]
  refine le_of_eq_of_le ?_ herr
  have hM : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≠ 0 :=
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold dmcAvgError
  rw [ite_eq_right hM]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hrel]
  exact (sum_ite_fst_power _ (enc m) (fun a => dec a ⟨0, natMax_one_pos _⟩ ≠ m)).symm

/-- **Operational side at `R₀ = 0`**: `C_BSC(p₁, p₂, 0) = 1 - h(p₁)`. -/
theorem primitiveBscRelayCapacity_zero :
    primitiveBscRelayCapacity p₁ p₂ h10 h11 h20 h21 0 = 1 - binaryEntropy p₁ := by
  refine le_antisymm ?_ (one_sub_binaryEntropy_le_primitiveBscRelayCapacity h10 h11 h20 h21 0)
  rw [← bsc_capacity h10 h11]
  exact csSup_le ⟨0, isPrimitive_zero h10 h11 h20 h21 0⟩ fun R hR =>
    shannon_channel_coding_converse _ R (isDmcAchievableRate_of_primitive_zero h10 h11 h20 h21 hR)

/-- The `(X, Y)` marginal of any CF joint law is the `BSC(p₁)` joint law of its input. -/
theorem cf_map_xy_general {kU : ℕ} (Px : ProbDist Bool) (Q : DMC Bool (Fin kU))
    (J : ProbDist (Bool × (Bool × Bool) × Fin kU))
    (hJ : ∀ t, J.pmf t = Px.pmf t.1 *
      (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).trans t.1 t.2.1 * Q.trans t.2.1.2 t.2.2) :
    J.map (fun t => (t.1, t.2.1.1)) = (bsc p₁ h10 h11).joint Px := by
  classical
  have hQ : ∀ b, ∑ u, Q.trans b u = 1 := Q.sum_one
  refine probDist_eq_of_pmf fun xy => ?_
  obtain ⟨x, y⟩ := xy
  simp only [ProbDist.map, hJ, DMC.joint, bsc, bscRelayBroadcast, Fintype.sum_prod_type,
    Fintype.sum_bool]
  cases x <;> cases y <;> simp [← Finset.mul_sum, hQ] <;> ring

/-- The CF objective at `R = 0` is at most `I(X; Y) ≤ 1 - h(p₁)`. -/
theorem cf_obj_zero_le {kU : ℕ} (Px : ProbDist Bool) (Q : DMC Bool (Fin kU))
    (J : ProbDist (Bool × (Bool × Bool) × Fin kU))
    (hJ : ∀ t, J.pmf t = Px.pmf t.1 *
      (bscRelayBroadcast p₁ p₂ h10 h11 h20 h21).trans t.1 t.2.1 * Q.trans t.2.1.2 t.2.2) :
    min (mutualInfo (J.map (fun t => (t.1, (t.2.1.1, t.2.2)))))
      (mutualInfo (J.map (fun t => (t.1, t.2.1.1))) + 0 -
        condMutualInfo (J.map (fun t => (t.2.2, t.2.1.2, (t.1, t.2.1.1))))) ≤
      1 - binaryEntropy p₁ := by
  have hxy : mutualInfo (J.map (fun t => (t.1, t.2.1.1))) ≤ 1 - binaryEntropy p₁ := by
    rw [cf_map_xy_general h10 h11 h20 h21 Px Q J hJ, ← bsc_capacity h10 h11]
    exact dmc_mutualInfo_le_capacity _ _
  have hc := condMutualInfo_nonneg (J.map (fun t => (t.2.2, t.2.1.2, (t.1, t.2.1.1))))
  exact min_le_of_right_le (by linarith)

theorem primitiveBscCFRate_zero_le :
    primitiveBscCFRate p₁ p₂ h10 h11 h20 h21 0 ≤ 1 - binaryEntropy p₁ := by
  unfold primitiveBscCFRate
  refine csSup_le ⟨_, 1, ProbDist.uniform, trivialTest Bool, rfl⟩ (fun r hr => ?_)
  obtain ⟨kU, Px, Q, rfl⟩ := hr
  exact cf_obj_zero_le h10 h11 h20 h21 Px Q _ (fun t => rfl)

/-- **CF side at `R₀ = 0`**: `R_CF^{conc}(p₁, p₂, 0) = 1 - h(p₁)`. -/
theorem primitiveBscCFRateConcave_zero :
    primitiveBscCFRateConcave p₁ p₂ h10 h11 h20 h21 0 = 1 - binaryEntropy p₁ := by
  refine le_antisymm ?_ (one_sub_binaryEntropy_le_primitiveBscCFRateConcave h10 h11 h20 h21 le_rfl)
  unfold primitiveBscCFRateConcave
  refine csSup_le ⟨_, 1, fun _ => 1, fun _ => 0, fun _ => zero_le_one, by simp, fun _ => le_rfl,
    by simp, rfl⟩ (fun r hr => ?_)
  obtain ⟨m, w, Rs, hw0, hw1, hRs0, hsum, rfl⟩ := hr
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ w i * Rs i :=
    fun i _ => mul_nonneg (hw0 i) (hRs0 i)
  have hz : ∀ i, w i * Rs i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm hsum (Finset.sum_nonneg hnn)) i (Finset.mem_univ _)
  calc ∑ i : Fin m, w i * primitiveBscCFRate p₁ p₂ h10 h11 h20 h21 (Rs i)
      ≤ ∑ i : Fin m, w i * (1 - binaryEntropy p₁) := Finset.sum_le_sum fun i _ => by
        rcases mul_eq_zero.1 (hz i) with h | h
        · rw [h]; simp
        · rw [h]
          exact mul_le_mul_of_nonneg_left (primitiveBscCFRate_zero_le h10 h11 h20 h21) (hw0 i)
    _ = 1 - binaryEntropy p₁ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Regression: the frozen statement holds at the solved endpoint `R₀ = 0`** (both sides
    equal the direct-link capacity `1 - h(p)`). -/
theorem statement_at_zero (p : ℝ) (h0 : 0 < p) (h1 : p < 1 / 2) :
    primitiveBscRelayCapacity p p (le_of_lt h0) (by linarith) (le_of_lt h0) (by linarith) 0 =
      primitiveBscCFRateConcave p p (le_of_lt h0) (by linarith) (le_of_lt h0) (by linarith) 0 := by
  rw [primitiveBscRelayCapacity_zero, primitiveBscCFRateConcave_zero]

end Regression

end InfoTheory.Known.Certificates.PrimitiveRelayChannelBsc
