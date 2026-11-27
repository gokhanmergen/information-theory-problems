import InfoTheory.Problems.BroadcastChannelThreeReceivers
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.BroadcastChannel

/-!
# Certificate for `InfoTheory.Problems.BroadcastChannelThreeReceivers`

The frozen statement asks whether, for every finite three-receiver DM broadcast channel `W`
with private messages, the operational region `bc3CapacityRegion W ⊆ ℝ³` equals the
three-receiver Marton inner bound `marton3InnerBound W`.

## Certified (about exactly these objects)
* `bc3CapacityRegion_subset_box` — the trivial outer bound
  `C₃(W) ⊆ [0, C₁] × [0, C₂] × [0, C₃]`, `Cⱼ = C(p(yⱼ | x))` (El Gamal–Kim §5.1): averaging over
  the two messages a receiver ignores gives a point-to-point code for its marginal channel
  (`exists_slice`), then Shannon's converse.
* `mutualInfo_add_condMutualInfo` — the chain rule `I(A; Y) + I(B; Y | A) = I(A, B; Y)` for
  pushforwards of one joint law.
* `marton3InnerBound_subset_box` — **the three-receiver Marton region satisfies the same outer
  bound**: e.g. `R₁ ≤ I(W₀; Y₁) + I(V₁; Y₁ | W₀) = I(W₀, V₁; Y₁) ≤ C₁` (chain rule and data
  processing through `p(y₁ | x)`).
* `zero_mem_bc3CapacityRegion`, `zero_mem_marton3InnerBound` — both sides contain the origin.
  So both sides of the statement are nonempty bounded sets.

## Not certified
* Achievability of `marton3InnerBound` (needs multivariate covering; two-receiver
  superposition coding is now in `Bridge.superpositionInnerBound_subset_bcCapacityRegion`), and any converse beyond the box (e.g. Nair–El Gamal's counterexample
  showing that the natural extension of the Körner–Marton region is not tight).
* **Frozen `Statement` is false (on paper; catalog error, statement-fix pending).** Adding a
  constant third output to the Gohari–El Gamal–Anantharam degraded channel (arXiv:1006.5166,
  Claim 1) collapses `marton3InnerBound` to Marton's region without a superposition variable,
  which is certifiably below capacity (`sup(R₁ + 2.35 R₂) ≤ 0.12131588 < 0.12131597`); see
  `problems/broadcast-channel-three-receivers.md` and
  `attempts/broadcast-channel-three-receivers/2026-11-26-claude-opus-5-5-useless-receiver-catalog-error.md`.
  A Lean `statement_false` is very high effort (an upper bound on `marton3InnerBound` over
  auxiliaries of unbounded cardinality). The mathematical problem remains open.

Sources: Nair–El Gamal, IEEE Trans. IT 2009; El Gamal–Kim, *Network Information Theory*,
§5.1, §8.6.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BroadcastChannelThreeReceivers

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.BroadcastChannelThreeReceivers
open InfoTheory.Known.Certificates.BroadcastChannel (mi_map_left_le
  condMutualInfo_eq_zero_of_subsingleton condMutualInfo_eq_zero_of_subsingleton_fst)

/-! ### Toolkit -/

section Toolkit

variable {Ω A B Z X Y : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype Z] [Fintype X]
  [Fintype Y]

theorem ent_congr (J : ProbDist Ω) (f : Ω → A) (g : Ω → B) (e : A ≃ B)
    (h : ∀ t, g t = e (f t)) : shannonEntropy (J.map g) = shannonEntropy (J.map f) := by
  have : J.map g = (J.map f).map e := by
    rw [map_comp_eq]; congr 1; funext t; exact h t
  rw [this, shannonEntropy_map_equiv]

theorem map_pair_fst (J : ProbDist Ω) (f : Ω → A) (g : Ω → B) :
    (J.map (fun t => (f t, g t))).fst = J.map f := by
  rw [← map_fst_eq_fst, map_comp_eq]; rfl

theorem map_pair_snd (J : ProbDist Ω) (f : Ω → A) (g : Ω → B) :
    (J.map (fun t => (f t, g t))).snd = J.map g := by
  rw [← map_snd_eq_snd, map_comp_eq]; rfl

/-- **Chain rule for mutual information**: `I(A; Y) + I(B; Y | A) = I(A, B; Y)`. -/
theorem mutualInfo_add_condMutualInfo (J : ProbDist Ω) (a : Ω → A) (b : Ω → B) (y : Ω → Y) :
    mutualInfo (J.map (fun t => (a t, y t))) + condMutualInfo (J.map (fun t => (b t, y t, a t))) =
      mutualInfo (J.map (fun t => ((a t, b t), y t))) := by
  unfold mutualInfo condMutualInfo
  dsimp only
  simp only [map_pair_fst, map_pair_snd, map_comp_eq, Function.comp_def]
  have e1 : shannonEntropy (J.map (fun t => (y t, a t))) =
      shannonEntropy (J.map (fun t => (a t, y t))) :=
    ent_congr J _ _ (Equiv.prodComm A Y) (fun _ => rfl)
  have e2 : shannonEntropy (J.map (fun t => (b t, a t))) =
      shannonEntropy (J.map (fun t => (a t, b t))) :=
    ent_congr J _ _ (Equiv.prodComm A B) (fun _ => rfl)
  have e3 : shannonEntropy (J.map (fun t => (b t, y t, a t))) =
      shannonEntropy (J.map (fun t => ((a t, b t), y t))) := by
    refine ent_congr J _ _
      { toFun := fun p => (p.1.2, p.2, p.1.1)
        invFun := fun q => ((q.2.2, q.1), q.2.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } (fun _ => rfl)
  rw [e1, e2, e3]
  ring

end Toolkit

variable {X Y₁ Y₂ Y₃ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]

/-! ### Marginal channels -/

/-- Receiver 1's channel `p(y₁ | x)`. -/
def marg₁ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : DMC X Y₁ := marginalFst W
/-- Receiver 2's channel `p(y₂ | x)`. -/
def marg₂ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : DMC X Y₂ := marginalFst (marginalSnd W)
/-- Receiver 3's channel `p(y₃ | x)`. -/
def marg₃ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : DMC X Y₃ := marginalSnd (marginalSnd W)

theorem sum_ite₁ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → Y₁) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂ × Y₃, (if p (fun i => (y i).1) then (W.power n).trans x y else 0) =
      ∑ a, if p a then ((marg₁ W).power n).trans x a else 0 :=
  sum_ite_fst_power W x p

theorem sum_ite₂ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → Y₂) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂ × Y₃, (if p (fun i => (y i).2.1) then (W.power n).trans x y else 0) =
      ∑ a, if p a then ((marg₂ W).power n).trans x a else 0 := by
  rw [sum_ite_snd_power W x (fun b => p (fun i => (b i).1))]
  exact sum_ite_fst_power (marginalSnd W) x p

theorem sum_ite₃ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {n : ℕ} (x : Fin n → X)
    (p : (Fin n → Y₃) → Prop) [DecidablePred p] :
    ∑ y : Fin n → Y₁ × Y₂ × Y₃, (if p (fun i => (y i).2.2) then (W.power n).trans x y else 0) =
      ∑ a, if p a then ((marg₃ W).power n).trans x a else 0 := by
  rw [sum_ite_snd_power W x (fun b => p (fun i => (b i).2))]
  exact sum_ite_snd_power (marginalSnd W) x p

/-! ### Averaging -/

/-- If the average of `f` over `[M₁] × [M₂] × [M₃]` is `≤ δ`, some slice `(m₂, m₃)` has
    average `≤ δ` over `m₁`. -/
theorem exists_slice {M₁ M₂ M₃ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (f : Fin M₁ → Fin M₂ → Fin M₃ → ℝ) {δ : ℝ}
    (h : ((1 : ℝ) / ((M₁ * M₂ * M₃ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ m₃, f m₁ m₂ m₃ ≤ δ) :
    ∃ m₂ m₃, ((1 : ℝ) / (M₁ : ℝ)) * ∑ m₁, f m₁ m₂ m₃ ≤ δ := by
  have hM : (0 : ℝ) < ((M₁ * M₂ * M₃ : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos h₁ h₂) h₃
  have hM₁ : (0 : ℝ) < M₁ := by exact_mod_cast h₁
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM] at h
  have hsum : ∑ q : Fin M₂ × Fin M₃, ∑ m₁, f m₁ q.1 q.2 ≤ ∑ _q : Fin M₂ × Fin M₃, (M₁ : ℝ) * δ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Fintype.sum_prod_type]
    have e2 : ∑ m₂ : Fin M₂, ∑ m₃ : Fin M₃, ∑ m₁ : Fin M₁, f m₁ m₂ m₃ =
        ∑ m₁, ∑ m₂, ∑ m₃, f m₁ m₂ m₃ :=
      calc ∑ m₂ : Fin M₂, ∑ m₃ : Fin M₃, ∑ m₁ : Fin M₁, f m₁ m₂ m₃
          = ∑ m₂ : Fin M₂, ∑ m₁ : Fin M₁, ∑ m₃ : Fin M₃, f m₁ m₂ m₃ :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [e2]
    push_cast at h ⊢
    linarith
  obtain ⟨q, -, hq⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty_iff.mpr ⟨(⟨0, h₂⟩, ⟨0, h₃⟩)⟩) hsum
  refine ⟨q.1, q.2, ?_⟩
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hM₁]
  linarith

private lemma natMax_one_pos (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- Permuted slices: the free index can be any of the three. -/
theorem exists_slice_mono {M₁ M₂ M₃ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (G F : Fin M₁ → Fin M₂ → Fin M₃ → ℝ) (hGF : ∀ a b c, G a b c ≤ F a b c) {δ : ℝ}
    (h : ((1 : ℝ) / ((M₁ * M₂ * M₃ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ m₃, F m₁ m₂ m₃ ≤ δ) :
    ∃ m₂ m₃, ((1 : ℝ) / (M₁ : ℝ)) * ∑ m₁, G m₁ m₂ m₃ ≤ δ := by
  refine exists_slice h₁ h₂ h₃ G (le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) h)
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    Finset.sum_le_sum fun c _ => hGF a b c

theorem exists_slice_mono₂ {M₁ M₂ M₃ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (G F : Fin M₁ → Fin M₂ → Fin M₃ → ℝ) (hGF : ∀ a b c, G a b c ≤ F a b c) {δ : ℝ}
    (h : ((1 : ℝ) / ((M₁ * M₂ * M₃ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ m₃, F m₁ m₂ m₃ ≤ δ) :
    ∃ m₁ m₃, ((1 : ℝ) / (M₂ : ℝ)) * ∑ m₂, G m₁ m₂ m₃ ≤ δ := by
  obtain ⟨m₁, m₃, hs⟩ := exists_slice_mono (δ := δ) h₂ h₁ h₃ (fun b a c => G a b c)
    (fun b a c => F a b c)
    (fun b a c => hGF a b c) (by
      rw [show M₂ * M₁ * M₃ = M₁ * M₂ * M₃ by ring, Finset.sum_comm]
      exact h)
  exact ⟨m₁, m₃, hs⟩

theorem exists_slice_mono₃ {M₁ M₂ M₃ : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (G F : Fin M₁ → Fin M₂ → Fin M₃ → ℝ) (hGF : ∀ a b c, G a b c ≤ F a b c) {δ : ℝ}
    (h : ((1 : ℝ) / ((M₁ * M₂ * M₃ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ m₃, F m₁ m₂ m₃ ≤ δ) :
    ∃ m₁ m₂, ((1 : ℝ) / (M₃ : ℝ)) * ∑ m₃, G m₁ m₂ m₃ ≤ δ := by
  obtain ⟨m₁, m₂, hs⟩ := exists_slice_mono (δ := δ) h₃ h₁ h₂ (fun c a b => G a b c)
    (fun c a b => F a b c)
    (fun c a b => hGF a b c) (by
      have e : ∑ c : Fin M₃, ∑ a : Fin M₁, ∑ b : Fin M₂, F a b c =
          ∑ a : Fin M₁, ∑ b : Fin M₂, ∑ c : Fin M₃, F a b c := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      rw [show M₃ * M₁ * M₂ = M₁ * M₂ * M₃ by ring, e]
      exact h)
  exact ⟨m₁, m₂, hs⟩

/-! ### Outer bound on the operational region -/

theorem isDmcAchievableRate_marg₁ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {R₁ R₂ R₃ : ℝ}
    (h : IsBC3Achievable W R₁ R₂ R₃) : IsDmcAchievableRate (marg₁ W) R₁ := by
  classical
  obtain ⟨h1, -, -, h⟩ := h
  refine ⟨h1, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec₁, dec₂, dec₃, herr⟩ := hN n hn
  obtain ⟨m₂, m₃, hs⟩ := exists_slice_mono (natMax_one_pos _) (natMax_one_pos _)
    (natMax_one_pos _)
    (fun m₁ m₂ m₃ => ∑ a : Fin n → Y₁,
      if dec₁ a ≠ m₁ then ((marg₁ W).power n).trans (enc m₁ m₂ m₃) a else 0)
    (fun m₁ m₂ m₃ => ∑ y : Fin n → Y₁ × Y₂ × Y₃,
      if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2.1) ≠ m₂ ∨
        dec₃ (fun i => (y i).2.2) ≠ m₃ then (W.power n).trans (enc m₁ m₂ m₃) y else 0)
    (fun m₁ m₂ m₃ => by
      rw [← sum_ite₁ W (enc m₁ m₂ m₃) (fun a => dec₁ a ≠ m₁)]
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases hc : dec₁ (fun i => (y i).1) ≠ m₁
      · rw [ite_eq_left hc, ite_eq_left (Or.inl hc)]
      · rw [ite_eq_right hc]; split_ifs <;> simp [(W.power n).nonneg]) herr
  refine ⟨fun m => enc m m₂ m₃, dec₁, le_of_eq_of_le ?_ hs⟩
  unfold dmcAvgError
  rw [ite_eq_right (natMax_one_pos _).ne']

theorem isDmcAchievableRate_marg₂ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {R₁ R₂ R₃ : ℝ}
    (h : IsBC3Achievable W R₁ R₂ R₃) : IsDmcAchievableRate (marg₂ W) R₂ := by
  classical
  obtain ⟨-, h2, -, h⟩ := h
  refine ⟨h2, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec₁, dec₂, dec₃, herr⟩ := hN n hn
  obtain ⟨m₁, m₃, hs⟩ := exists_slice_mono₂ (natMax_one_pos _) (natMax_one_pos _)
    (natMax_one_pos _)
    (fun m₁ m₂ m₃ => ∑ a : Fin n → Y₂,
      if dec₂ a ≠ m₂ then ((marg₂ W).power n).trans (enc m₁ m₂ m₃) a else 0)
    (fun m₁ m₂ m₃ => ∑ y : Fin n → Y₁ × Y₂ × Y₃,
      if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2.1) ≠ m₂ ∨
        dec₃ (fun i => (y i).2.2) ≠ m₃ then (W.power n).trans (enc m₁ m₂ m₃) y else 0)
    (fun m₁ m₂ m₃ => by
      rw [← sum_ite₂ W (enc m₁ m₂ m₃) (fun a => dec₂ a ≠ m₂)]
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases hc : dec₂ (fun i => (y i).2.1) ≠ m₂
      · rw [ite_eq_left hc, ite_eq_left (Or.inr (Or.inl hc))]
      · rw [ite_eq_right hc]; split_ifs <;> simp [(W.power n).nonneg]) herr
  refine ⟨fun m => enc m₁ m m₃, dec₂, le_of_eq_of_le ?_ hs⟩
  unfold dmcAvgError
  rw [ite_eq_right (natMax_one_pos _).ne']

theorem isDmcAchievableRate_marg₃ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {R₁ R₂ R₃ : ℝ}
    (h : IsBC3Achievable W R₁ R₂ R₃) : IsDmcAchievableRate (marg₃ W) R₃ := by
  classical
  obtain ⟨-, -, h3, h⟩ := h
  refine ⟨h3, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec₁, dec₂, dec₃, herr⟩ := hN n hn
  obtain ⟨m₁, m₂, hs⟩ := exists_slice_mono₃ (natMax_one_pos _) (natMax_one_pos _)
    (natMax_one_pos _)
    (fun m₁ m₂ m₃ => ∑ a : Fin n → Y₃,
      if dec₃ a ≠ m₃ then ((marg₃ W).power n).trans (enc m₁ m₂ m₃) a else 0)
    (fun m₁ m₂ m₃ => ∑ y : Fin n → Y₁ × Y₂ × Y₃,
      if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2.1) ≠ m₂ ∨
        dec₃ (fun i => (y i).2.2) ≠ m₃ then (W.power n).trans (enc m₁ m₂ m₃) y else 0)
    (fun m₁ m₂ m₃ => by
      rw [← sum_ite₃ W (enc m₁ m₂ m₃) (fun a => dec₃ a ≠ m₃)]
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases hc : dec₃ (fun i => (y i).2.2) ≠ m₃
      · rw [ite_eq_left hc, ite_eq_left (Or.inr (Or.inr hc))]
      · rw [ite_eq_right hc]; split_ifs <;> simp [(W.power n).nonneg]) herr
  refine ⟨fun m => enc m₁ m₂ m, dec₃, le_of_eq_of_le ?_ hs⟩
  unfold dmcAvgError
  rw [ite_eq_right (natMax_one_pos _).ne']

/-- The closed box `[0, C₁] × [0, C₂] × [0, C₃]`. -/
noncomputable def box3 (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ × ℝ) :=
  Set.Icc 0 (marg₁ W).capacity ×ˢ Set.Icc 0 (marg₂ W).capacity ×ˢ Set.Icc 0 (marg₃ W).capacity

/-- **Trivial outer bound**: `C₃(W) ⊆ [0, C₁] × [0, C₂] × [0, C₃]`. -/
theorem bc3CapacityRegion_subset_box (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    bc3CapacityRegion W ⊆ box3 W := by
  refine closure_minimal (fun r hr => ?_) (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc))
  have h1 := isDmcAchievableRate_marg₁ W hr
  have h2 := isDmcAchievableRate_marg₂ W hr
  have h3 := isDmcAchievableRate_marg₃ W hr
  exact ⟨⟨h1.1, shannon_channel_coding_converse _ _ h1⟩,
    ⟨h2.1, shannon_channel_coding_converse _ _ h2⟩, ⟨h3.1, shannon_channel_coding_converse _ _ h3⟩⟩

/-! ### Marton's three-receiver region satisfies the same bound -/

section Projection

variable {A B C Z Y : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] [Fintype Y]

open Classical in
/-- The `(A, π(Y))` marginal of the joint law `P(a) W(y | f a)` is the joint law of the pushed
    channel `V = π ∘ W`. -/
theorem joint_map_proj_eq (W : DMC X Y) (V : DMC X Z) (π : Y → Z)
    (hV : ∀ x z, V.trans x z = ∑ y, if π y = z then W.trans x y else 0)
    (P : ProbDist A) (f : A → X) (J : ProbDist (A × Y))
    (hJ : ∀ t, J.pmf t = P.pmf t.1 * W.trans (f t.1) t.2) :
    J.map (fun t => (t.1, π t.2)) = (dmcPrecomp V f).joint P := by
  classical
  refine probDist_eq_of_pmf fun ⟨a, z⟩ => ?_
  simp only [ProbDist.map, DMC.joint, dmcPrecomp, hJ, hV, Finset.mul_sum]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : π y = z <;> simp [h]
  · intro a' _ h
    exact Finset.sum_eq_zero fun y _ => by simp [h]
  · simp

open Classical in
/-- **Data processing through a projected channel**: `I(g(A); π(Y)) ≤ C(π ∘ W)`. -/
theorem mi_proj_le_capacity (W : DMC X Y) (V : DMC X Z) (π : Y → Z)
    (hV : ∀ x z, V.trans x z = ∑ y, if π y = z then W.trans x y else 0)
    (P : ProbDist A) (f : A → X) (J : ProbDist (A × Y))
    (hJ : ∀ t, J.pmf t = P.pmf t.1 * W.trans (f t.1) t.2) (g : A → B) :
    mutualInfo (J.map (fun t => (g t.1, π t.2))) ≤ V.capacity := by
  have h1 : J.map (fun t => (g t.1, π t.2)) =
      (J.map (fun t => (t.1, π t.2))).map (Prod.map g id) := by
    rw [map_comp_eq]; rfl
  rw [h1]
  refine (mi_map_left_le _ g).trans ?_
  rw [joint_map_proj_eq W V π hV P f J hJ, dmcPrecomp_mutualInfo_eq]
  exact dmc_mutualInfo_le_capacity _ _

open Classical in
/-- **Chain rule + data processing**: `I(W; π Y) + I(V; π Y | W) ≤ C(π ∘ W)`. -/
theorem chain_le_capacity (W : DMC X Y) (V : DMC X Z) (π : Y → Z)
    (hV : ∀ x z, V.trans x z = ∑ y, if π y = z then W.trans x y else 0)
    (P : ProbDist A) (f : A → X) (J : ProbDist (A × Y))
    (hJ : ∀ t, J.pmf t = P.pmf t.1 * W.trans (f t.1) t.2) (w : A → B) (v : A → C) :
    mutualInfo (J.map (fun t => (w t.1, π t.2))) +
        condMutualInfo (J.map (fun t => (v t.1, π t.2, w t.1))) ≤ V.capacity :=
  calc _ = mutualInfo (J.map (fun t => ((w t.1, v t.1), π t.2))) :=
        mutualInfo_add_condMutualInfo J (fun t => w t.1) (fun t => v t.1) (fun t => π t.2)
    _ ≤ V.capacity := mi_proj_le_capacity W V π hV P f J hJ (fun a => (w a, v a))

end Projection

open Classical in
theorem hV₁ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (x : X) (z : Y₁) :
    (marg₁ W).trans x z = ∑ y : Y₁ × Y₂ × Y₃, if y.1 = z then W.trans x y else 0 := by
  classical
  simp only [marg₁, marginalFst, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [hb]
  · simp

open Classical in
theorem hV₂ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (x : X) (z : Y₂) :
    (marg₂ W).trans x z = ∑ y : Y₁ × Y₂ × Y₃, if y.2.1 = z then W.trans x y else 0 := by
  classical
  simp only [marg₂, marginalFst, marginalSnd, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₁ _ => ?_
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [hb]
  · simp

open Classical in
theorem hV₃ (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (x : X) (z : Y₃) :
    (marg₃ W).trans x z = ∑ y : Y₁ × Y₂ × Y₃, if y.2.2 = z then W.trans x y else 0 := by
  classical
  simp only [marg₃, marginalSnd, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => ?_
  rw [Finset.sum_eq_single z]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- **Marton's three-receiver region satisfies the trivial outer bound.** -/
theorem marton3InnerBound_subset_box (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    marton3InnerBound W ⊆ box3 W := by
  refine closure_minimal (fun r hr => ?_) (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc))
  obtain ⟨h1, h2, h3, k₀, k₁₂, k₁₃, k₂₃, k₁, k₂, k₃, P, r₁₀, r₂₀, r₃₀, r₁₂, r₁₃, r₂₃, r₁₁, r₂₁,
    r₃₁, rp₁, rp₂, rp₃, n10, n20, n30, n12, n13, n23, n11, n21, n31, np1, np2, np3, e1, e2, e3,
    hc⟩ := hr
  obtain ⟨c0, c1, c2, c3, -⟩ := hc
  have m1 := c0.trans (min_le_left _ _)
  have m2 := c0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have m3 := c0.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩, ⟨h3, ?_⟩⟩
  · rw [e1, show r₁₀ + r₁₂ + r₁₃ + r₁₁ = r₁₀ + (r₁₂ + r₁₃ + r₁₁) by ring]
    exact le_trans (add_le_add (by linarith) (by linarith))
      (chain_le_capacity W (marg₁ W) (fun y => y.1) (hV₁ W) P (fun a => a.2.2.2) _
        (fun _ => rfl) (fun a => a.1) (fun t => (t.2.1.1, t.2.1.2.1, t.2.2.1.1)))
  · rw [e2, show r₂₀ + r₂₃ + r₂₁ = r₂₀ + (r₂₃ + r₂₁) by ring]
    exact le_trans (add_le_add (by linarith) (by linarith))
      (chain_le_capacity W (marg₂ W) (fun y => y.2.1) (hV₂ W) P (fun a => a.2.2.2) _
        (fun _ => rfl) (fun a => a.1) (fun t => (t.2.1.1, t.2.1.2.2, t.2.2.1.2.1)))
  · rw [e3]
    exact le_trans (add_le_add (by linarith) (by linarith))
      (chain_le_capacity W (marg₃ W) (fun y => y.2.2) (hV₃ W) P (fun a => a.2.2.2) _
        (fun _ => rfl) (fun a => a.1) (fun t => (t.2.1.2.1, t.2.1.2.2, t.2.2.1.2.2)))

/-! ### Both sides contain the origin -/

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

theorem zero_mem_bc3CapacityRegion [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ bc3CapacityRegion W := by
  classical
  refine subset_closure ⟨le_rfl, le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  rw [natMax_zero]
  refine ⟨fun _ _ _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  have : ∀ (m₁ m₂ m₃ : Fin 1) (y : Fin n → Y₁ × Y₂ × Y₃),
      (if (0 : Fin 1) ≠ m₁ ∨ (0 : Fin 1) ≠ m₂ ∨ (0 : Fin 1) ≠ m₃ then
        (W.power n).trans (fun _ => Classical.arbitrary X) y else 0) = 0 := by
    intro m₁ m₂ m₃ y
    rw [ite_eq_right]
    rintro (h | h | h) <;> exact h (Subsingleton.elim _ _)
  simp only [this, Finset.sum_const_zero, mul_zero]
  exact hε.le

/-- Conditional entropy vanishes when the first variable is constant. -/
theorem condEntropy_eq_zero_of_subsingleton {α β : Type*} [Fintype α] [Fintype β]
    [Subsingleton α] (P : ProbDist (α × β)) : condEntropy P = 0 := by
  classical
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · exfalso
    have : ∑ t : α × β, P.pmf t = 0 := Finset.sum_eq_zero fun t _ => (IsEmpty.false t.1).elim
    linarith [P.sum_one]
  unfold condEntropy
  have : shannonEntropy P = shannonEntropy ((P.map Prod.snd).map (fun b => (a₀, b))) := by
    rw [map_comp_eq, ← shannonEntropy_map_equiv (Equiv.refl _) P]
    congr 2
    funext t
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [this, shannonEntropy_map_of_injective _ (fun x y h => (Prod.mk.inj h).2), map_snd_eq_snd]
  ring

theorem zero_mem_marton3InnerBound [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ marton3InnerBound W := by
  refine subset_closure ⟨le_rfl, le_rfl, le_rfl, 1, 1, 1, 1, 1, 1, 1, ProbDist.uniform,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num, ?_⟩
  intro J IW_Y1 IW_Y2 IW_Y3 V1 V2 V3 IV1_Y1 IV2_Y2 IV3_Y3 I12 I13 I23 HV1 HV2 HV3 HV123
  have z12 : I12 = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z13 : I13 = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z23 : I23 = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have zH1 : HV1 = 0 := condEntropy_eq_zero_of_subsingleton _
  have zH2 : HV2 = 0 := condEntropy_eq_zero_of_subsingleton _
  have zH3 : HV3 = 0 := condEntropy_eq_zero_of_subsingleton _
  have zH : HV123 = 0 := condEntropy_eq_zero_of_subsingleton _
  have n1 : 0 ≤ IW_Y1 := mutualInfo_nonneg _
  have n2 : 0 ≤ IW_Y2 := mutualInfo_nonneg _
  have n3 : 0 ≤ IW_Y3 := mutualInfo_nonneg _
  have n4 : 0 ≤ IV1_Y1 := condMutualInfo_nonneg _
  have n5 : 0 ≤ IV2_Y2 := condMutualInfo_nonneg _
  have n6 : 0 ≤ IV3_Y3 := condMutualInfo_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [add_zero]; exact le_min n1 (le_min n2 n3)
  · simp only [add_zero]; exact n4
  · simp only [add_zero]; exact n5
  · simp only [add_zero]; exact n6
  · rw [z12]; norm_num
  · rw [z13]; norm_num
  · rw [z23]; norm_num
  · rw [zH1, zH2, zH3, zH]; norm_num

end InfoTheory.Known.Certificates.BroadcastChannelThreeReceivers
