import InfoTheory.Problems.BroadcastChannelThreeReceivers
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.BroadcastChannel

/-!
# Certificate for `InfoTheory.Problems.BroadcastChannelThreeReceivers`

The statement (statement-fix 2026-11-27) asks whether, for every finite three-receiver DM
broadcast channel `W` with private messages, the operational region
`bc3CapacityRegion W ⊆ ℝ³` equals the Padakandla–Pradhan UM region `umRegion W`.

## Certified (about exactly these objects)
* `bc3CapacityRegion_subset_box` — the trivial outer bound
  `C₃(W) ⊆ [0, C₁] × [0, C₂] × [0, C₃]`, `Cⱼ = C(p(yⱼ | x))` (El Gamal–Kim §5.1): averaging over
  the two messages a receiver ignores gives a point-to-point code for its marginal channel
  (`exists_slice`), then Shannon's converse.
* `mutualInfo_add_condMutualInfo` — the chain rule `I(A; Y) + I(B; Y | A) = I(A, B; Y)` for
  pushforwards of one joint law; `condMutualInfo_swap` — `I(A; B | C) = I(B; A | C)`.
* `umRate_le_capacity`, `umRegion_subset_box` — **the UM region satisfies the same outer
  bound**: receiver `i`'s packing constraint (11) plus the covering constraint (2) for the
  pair `(U_ki, U_ij)` give `R_i ≤ I(W, U_ij, U_ki, V_i; Y_i | Q) ≤ I(Q, W, U, V; Y_i) ≤ C_i`
  (chain rule and data processing through `p(yᵢ | x)`); the box is closed and convex, so it
  also contains the closed convex hull.
* `zero_mem_bc3CapacityRegion`, `zero_mem_umRegion` — both sides contain the origin.
  So both sides of the statement are nonempty bounded sets.

* **Regression** `superpositionInnerBound_bc12_subset_umRegion` — for every 3-DMBC, every point
  of the superposition coding region (Bridge `superpositionInnerBound`) of the receivers-1,2
  sub-BC `bc12 W`, padded with `R₃ = 0`, lies in `umRegion W` (`Q, W` constant, `U₁₂ := U`,
  `V₁ := X`, `T₁ = R₁`, `L₁₂ = R₂`, all else `0`; every covering term vanishes and each packing
  bound reduces to `I(X; Y₁ | U)`, `I(X; Y₁)` or `I(U; Y₂)`).  Hence
  `bcCapacityRegion_bc12_subset_umRegion_of_degraded`: **if `bc12 W` is physically degraded,
  its capacity region (Bergmans–Gallager) times `{0}` is inside the frozen UM region** — in
  particular the Gohari–El Gamal–Anantharam-type gap that refuted the pre-fix region cannot
  recur on degraded sub-BCs.

* **Regression** `martonInnerBound_bc12_subset_umRegion` — **the full useless-receiver
  inclusion**: for every 3-DMBC, `martonInnerBound (bc12 W) × {0} ⊆ umRegion W` (Marton's
  region *with* the common auxiliary, binning included; `Q, W_UM` constant, `U₁₂ := W`,
  `V₁ := U`, `V₂ := V`; explicit Fourier–Motzkin witnesses in `marton_split_reals`, and `U, V`
  constant when `I(U;V|W) > I(U;Y₁|W) + I(V;Y₂|W)`). Together with
  `Bridge.martonInnerBound_subset_bcCapacityRegion` this says the frozen UM region is at least
  Marton's (achievable) region on the `R₃ = 0` face; the Gohari–El Gamal–Anantharam gap that
  refuted the pre-fix region therefore cannot recur.

## Not certified
* Achievability of `umRegion` (Padakandla–Pradhan, Theorem 2; needs multivariate covering and
  superposition — two-receiver superposition coding is in
  `Bridge.superpositionInnerBound_subset_bcCapacityRegion`), and any converse beyond the box.
* The converse direction of the useless-receiver check (`umRegion W ∩ {R₃ = 0}` no larger than
  Marton's region when `Y₃` is useless; expected, not proved).
* Known suboptimality results: Padakandla–Pradhan (arXiv:1207.3146) prove the UM region is
  strictly suboptimal for some 3-DMBCs *with an input cost*; Huang–Liu–Liu (arXiv:2608.19869,
  unrefereed) claim two-receiver Marton is suboptimal, which via a useless third receiver
  would refute the statement. Neither is formalised.

Sources: Padakandla–Pradhan, arXiv:1207.3146v6, §II-D; Nair–El Gamal, IEEE Trans. IT 2009;
El Gamal–Kim, *Network Information Theory*, §5.1, Ch. 8.
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

/-! ### The UM region satisfies the same bound -/

section UM

variable {Ω A B Z : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype Z]

/-- **Symmetry**: `I(A; B | C) = I(B; A | C)`. -/
theorem condMutualInfo_swap (J : ProbDist Ω) (f : Ω → A) (g : Ω → B) (c : Ω → Z) :
    condMutualInfo (J.map fun t => (g t, f t, c t)) =
      condMutualInfo (J.map fun t => (f t, g t, c t)) := by
  unfold condMutualInfo
  dsimp only
  simp only [map_comp_eq, Function.comp_def]
  have e : shannonEntropy (J.map fun t => (g t, f t, c t)) =
      shannonEntropy (J.map fun t => (f t, g t, c t)) :=
    ent_congr J (fun t => (f t, g t, c t)) _
      { toFun := fun p => (p.2.1, p.1, p.2.2)
        invFun := fun p => (p.2.1, p.1, p.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } (fun _ => rfl)
  rw [e]
  ring

/-- The input-side marginal of the joint law `P(a) W(y | f a)` is `P`. -/
theorem map_fst_of_joint {Yf : Type*} [Fintype Yf] (W : DMC X Yf) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × Yf)) (hJ : ∀ t, J.pmf t = P.pmf t.1 * W.trans (f t.1) t.2) :
    J.map Prod.fst = P := by
  classical
  refine probDist_eq_of_pmf fun a => ?_
  simp only [ProbDist.map, hJ]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [← Finset.mul_sum, W.sum_one]
  · intro b _ hb
    exact Finset.sum_eq_zero fun y _ => by simp [hb]
  · simp

theorem fin3_add_two_add_one (i : Fin 3) : i + 2 + 1 = i := by
  revert i; decide

open Classical in
/-- **Each UM rate is at most the capacity of the receiver's marginal channel.** For receiver
    `i`, packing constraint (11) bounds the sum of all rates it decodes by
    `I(W, U_ij, U_ki, V_i; Y_i | Q) + I(U_ij; U_ki | Q W)`, and covering constraint (2) for the
    pair `(U_ki, U_ij)` pays for the second term with bin rates. -/
theorem umRate_le_capacity {k : ℕ} {Yf : Type*} [Fintype Yf] (W : DMC X Yf) (V : DMC X Z)
    (π : Yf → Z) (hV : ∀ x z, V.trans x z = ∑ y, if π y = z then W.trans x y else 0)
    (P : ProbDist (UMAux k X)) (J : ProbDist (UMAux k X × Yf))
    (hJ : ∀ t, J.pmf t = P.pmf t.1 * W.trans t.1.2.2.2.2 t.2) (i : Fin 3)
    {K Ks L S T Sv : Fin 3 → ℝ}
    (hnn : ∀ i, 0 ≤ K i ∧ 0 ≤ Ks i ∧ 0 ≤ L i ∧ 0 ≤ S i ∧ 0 ≤ T i ∧ 0 ≤ Sv i)
    (hcov : umCoveringConstraints P S Sv)
    (hdec : umDecodingConstraints (J.map fun z => (z.1, π z.2)) i K Ks L S T Sv) :
    T i + Ks i + L (i + 2) + K i ≤ V.capacity := by
  obtain ⟨-, -, -, -, h11⟩ := hdec
  obtain ⟨hc, -, -⟩ := hcov
  have h2 := (hc (i + 2)).1
  rw [fin3_add_two_add_one] at h2
  simp only [map_comp_eq, Function.comp_def] at h11
  -- the covering constraint, rewritten as a function of `J`
  have hP : J.map Prod.fst = P := map_fst_of_joint W P (fun t => t.2.2.2.2) J hJ
  have hIab : condMutualInfo (J.map fun z =>
      (z.1.2.2.1 i, z.1.2.2.1 (i + 2), (z.1.1, z.1.2.1))) ≤ S (i + 2) + S i := by
    rw [← condMutualInfo_swap]
    have : J.map (fun z => (z.1.2.2.1 (i + 2), z.1.2.2.1 i, (z.1.1, z.1.2.1))) =
        P.map (fun t => (t.2.2.1 (i + 2), t.2.2.1 i, (t.1, t.2.1))) := by
      rw [← hP, map_comp_eq]; rfl
    rw [this]
    exact h2
  have hch := chain_le_capacity W V π hV P (fun a => a.2.2.2.2) J hJ (fun t => t.1)
    (fun t => (t.2.1, t.2.2.1 i, t.2.2.1 (i + 2), t.2.2.2.1 i))
  have hmi := mutualInfo_nonneg (J.map fun t => (t.1.1, π t.2))
  obtain ⟨k0, -, -, -, -, -⟩ := hnn 0
  obtain ⟨k1, -, -, -, -, -⟩ := hnn 1
  obtain ⟨k2, -, -, -, -, -⟩ := hnn 2
  obtain ⟨-, -, li, -, -, svi⟩ := hnn i
  obtain ⟨-, ks2, -, -, -, -⟩ := hnn (i + 2)
  have hK : K i ≤ K 0 + K 1 + K 2 := by
    fin_cases i <;> simp <;> linarith
  linarith

/-- **The UM region satisfies the trivial outer bound.** -/
theorem umRegion_subset_box (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    umRegion W ⊆ box3 W := by
  have hconv : Convex ℝ (box3 W) :=
    (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  refine closure_minimal (convexHull_min (fun r hr => ?_) hconv)
    (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc))
  obtain ⟨k, P, K, Ks, L, S, T, Sv, hnn, rfl, hcov, d1, d2, d3⟩ := hr
  have n0 := hnn 0
  have n1 := hnn 1
  have n2 := hnn 2
  refine ⟨⟨by dsimp only; linarith [n0.2.2.1, n2.2.2.1], ?_⟩,
    ⟨by dsimp only; linarith [n1.2.2.1, n0.2.2.1], ?_⟩,
    ⟨by dsimp only; linarith [n2.2.2.1, n1.2.2.1], ?_⟩⟩
  · exact umRate_le_capacity W (marg₁ W) (fun y => y.1) (hV₁ W) P _ (fun _ => rfl) 0 hnn hcov d1
  · exact umRate_le_capacity W (marg₂ W) (fun y => y.2.1) (hV₂ W) P _ (fun _ => rfl) 1 hnn hcov d2
  · exact umRate_le_capacity W (marg₃ W) (fun y => y.2.2) (hV₃ W) P _ (fun _ => rfl) 2 hnn hcov d3

end UM

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

theorem zero_mem_umRegion [Nonempty X] (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ umRegion W := by
  refine subset_closure (subset_convexHull ℝ _ ⟨1, ProbDist.uniform, 0, 0, 0, 0, 0, 0,
    fun _ => by simp, by simp, ?_, ?_⟩)
  · simp [umCoveringConstraints, condMutualInfo_eq_zero_of_subsingleton_fst]
  · simp [umDecodingConstraints, condMutualInfo_eq_zero_of_subsingleton_fst]

/-! ### Regression: superposition coding for receivers 1, 2 lies on the `R₃ = 0` face

For every 3-DMBC `W`, let `bc12 W` be the two-receiver BC seen by receivers 1 and 2.  Every
point of the superposition coding region (Bridge `superpositionInnerBound`) of `bc12 W`, padded
with `R₃ = 0`, lies in the frozen `umRegion W`: take `Q, W` constant, `U₁₂ := U_sc` (carrying
`M₂` as `L₁₂`), `V₁ := X` (carrying `M₁` as `T₁`), all other layers constant and all bin rates
`0`.  With the Bergmans–Gallager theorem this gives: if `bc12 W` is physically degraded, its
capacity region (times `{0}`) is inside `umRegion W`. -/

section Regression

variable {Ω α α' β γ γ' : Type*} [Fintype Ω] [Fintype α] [Fintype α'] [Fintype β] [Fintype γ]
  [Fintype γ']

theorem cmi_zero_of_fst_const (R : ProbDist Ω) (F : Ω → α × β × γ) (c : α)
    (h : ∀ t, (F t).1 = c) : condMutualInfo (R.map F) = 0 := by
  have e : R.map F = R.map (fun t => (c, (F t).2.1, (F t).2.2)) :=
    congrArg (fun G => R.map G) (funext fun t => Prod.ext (h t) rfl)
  rw [e]
  have e0 : R.map (fun t => (c, (F t).2.1, (F t).2.2)) =
      (R.map (fun t => (F t).2)).map (fun yz => (c, yz.1, yz.2)) := by rw [map_comp_eq]; rfl
  have e1 : (R.map (fun t => (c, (F t).2.1, (F t).2.2))).map (fun t => (t.1, t.2.2)) =
      (R.map (fun t => (F t).2.2)).map (fun z => (c, z)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (R.map (fun t => (c, (F t).2.1, (F t).2.2))).map (fun t => (t.2.1, t.2.2)) =
      R.map (fun t => (F t).2) := by rw [map_comp_eq]; rfl
  have e3 : (R.map (fun t => (c, (F t).2.1, (F t).2.2))).map (fun t => t.2.2) =
      R.map (fun t => (F t).2.2) := by rw [map_comp_eq]; rfl
  have i0 : Function.Injective (fun yz : β × γ => (c, yz.1, yz.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2
  have i1 : Function.Injective (fun z : γ => (c, z)) := fun a b h => (Prod.mk.inj h).2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ i0, shannonEntropy_map_of_injective _ i1]
  ring

theorem cmi_zero_of_snd_const (R : ProbDist Ω) (F : Ω → α × β × γ) (c : β)
    (h : ∀ t, (F t).2.1 = c) : condMutualInfo (R.map F) = 0 := by
  have e : R.map F = R.map (fun t => ((F t).1, c, (F t).2.2)) :=
    congrArg (fun G => R.map G) (funext fun t => Prod.ext rfl (Prod.ext (h t) rfl))
  rw [e]
  have e0 : R.map (fun t => ((F t).1, c, (F t).2.2)) =
      (R.map (fun t => ((F t).1, (F t).2.2))).map (fun xz => (xz.1, c, xz.2)) := by
    rw [map_comp_eq]; rfl
  have e1 : (R.map (fun t => ((F t).1, c, (F t).2.2))).map (fun t => (t.1, t.2.2)) =
      R.map (fun t => ((F t).1, (F t).2.2)) := by rw [map_comp_eq]; rfl
  have e2 : (R.map (fun t => ((F t).1, c, (F t).2.2))).map (fun t => (t.2.1, t.2.2)) =
      (R.map (fun t => (F t).2.2)).map (fun z => (c, z)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (R.map (fun t => ((F t).1, c, (F t).2.2))).map (fun t => t.2.2) =
      R.map (fun t => (F t).2.2) := by rw [map_comp_eq]; rfl
  have i0 : Function.Injective (fun xz : α × γ => (xz.1, c, xz.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.2
  have i1 : Function.Injective (fun z : γ => (c, z)) := fun a b h => (Prod.mk.inj h).2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ i0, shannonEntropy_map_of_injective _ i1]
  ring

/-- Relabelling the first and the conditioning variable injectively. -/
theorem cmi_relabel (R : ProbDist Ω) (F : Ω → α' × β × γ') (G : Ω → α × β × γ) (g : α → α')
    (h : γ → γ') (hg : Function.Injective g) (hh : Function.Injective h)
    (hF : ∀ t, F t = (g (G t).1, (G t).2.1, h (G t).2.2)) :
    condMutualInfo (R.map F) = condMutualInfo (R.map G) := by
  have e : R.map F = (R.map G).map (fun t => (g t.1, t.2.1, h t.2.2)) := by
    rw [map_comp_eq]; exact congrArg (fun G => R.map G) (funext hF)
  rw [e]
  generalize R.map G = K
  have hg1 : Function.Injective (fun t : α × γ => (g t.1, h t.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hg hxy.1) (hh hxy.2)
  have hg2 : Function.Injective (fun t : α × β × γ => (g t.1, t.2.1, h t.2.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hg hxy.1) (Prod.ext hxy.2.1 (hh hxy.2.2))
  have hg3 : Function.Injective (fun t : β × γ => (t.1, h t.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (hh hxy.2)
  unfold condMutualInfo
  dsimp only
  have e1 : (K.map (fun t => (g t.1, t.2.1, h t.2.2))).map (fun t => (t.1, t.2.2)) =
      (K.map (fun t => (t.1, t.2.2))).map (fun t => (g t.1, h t.2)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (K.map (fun t => (g t.1, t.2.1, h t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      (K.map (fun t => (t.2.1, t.2.2))).map (fun t => (t.1, h t.2)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (K.map (fun t => (g t.1, t.2.1, h t.2.2))).map (fun t => t.2.2) =
      (K.map (fun t => t.2.2)).map h := by
    rw [map_comp_eq, map_comp_eq]; rfl
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ hg1, shannonEntropy_map_of_injective _ hg2,
    shannonEntropy_map_of_injective _ hg3, shannonEntropy_map_of_injective _ hh]

/-- `I(A; Y) ≤ I(B; Y | c)` when the conditioning variable is constant and `A = hh(B)`. -/
theorem mi_le_cmi_of_const (R : ProbDist Ω) (F : Ω → α' × β × γ) (A : Ω → α) (Y : Ω → β)
    (c : γ) (hh : α' → α) (hc : ∀ t, (F t).2.2 = c) (hA : ∀ t, A t = hh (F t).1)
    (hY : ∀ t, Y t = (F t).2.1) :
    mutualInfo (R.map (fun t => (A t, Y t))) ≤ condMutualInfo (R.map F) := by
  have e : R.map F = (R.map (fun t => ((F t).1, (F t).2.1))).map (fun ab => (ab.1, ab.2, c)) := by
    rw [map_comp_eq]
    exact congrArg (fun G => R.map G) (funext fun t => Prod.ext rfl (Prod.ext rfl (hc t)))
  rw [e, condMutualInfo_map_const]
  refine le_trans (le_of_eq ?_) (mi_map_left_le _ hh)
  rw [map_comp_eq]
  congr 1
  exact congrArg (fun G => R.map G) (funext fun t => Prod.ext (hA t) (hY t))

theorem cmi_const_fst {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (R : ProbDist Ω) (F : Ω → α × β × γ) (h : ∀ t t', (F t).1 = (F t').1) :
    condMutualInfo (R.map F) = 0 := by
  obtain ⟨t₀, -⟩ : ∃ t : Ω, True := by
    by_contra hc; push Not at hc
    have : ∑ t : Ω, R.pmf t = 0 := Finset.sum_eq_zero fun t _ => (hc t).elim
    linarith [R.sum_one]
  exact cmi_zero_of_fst_const R F _ fun t => h t t₀

theorem cmi_const_snd {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (R : ProbDist Ω) (F : Ω → α × β × γ) (h : ∀ t t', (F t).2.1 = (F t').2.1) :
    condMutualInfo (R.map F) = 0 := by
  obtain ⟨t₀, -⟩ : ∃ t : Ω, True := by
    by_contra hc; push Not at hc
    have : ∑ t : Ω, R.pmf t = 0 := Finset.sum_eq_zero fun t _ => (hc t).elim
    linarith [R.sum_one]
  exact cmi_zero_of_snd_const R F _ fun t => h t t₀

/-- The two-receiver BC seen by receivers 1 and 2 of a 3-DMBC. -/
def bc12 (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : BroadcastChannel X Y₁ Y₂ where
  trans x y := ∑ y₃ : Y₃, W.trans x (y.1, y.2, y₃)
  nonneg x y := Finset.sum_nonneg fun y₃ _ => W.nonneg x _
  sum_one x := by simpa [Fintype.sum_prod_type] using W.sum_one x

theorem bcAuxJoint_bc12 (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {U : Type*} [Fintype U]
    (Pux : ProbDist (U × X)) :
    bcAuxJoint (bc12 W) Pux =
      ((dmcPrecomp W Prod.snd).joint Pux).map (fun z => (z.1, (z.2.1, z.2.2.1))) := by
  classical
  refine probDist_eq_of_pmf fun ⟨a, y₁, y₂⟩ => ?_
  simp only [bcAuxJoint, bc12, ProbDist.map, DMC.joint, dmcPrecomp]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_eq_single y₁]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₂]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb; simp [hb]
  · simp

/-- **Superposition point ⇒ UM point** (before closure): `Q, W` constant, `U₁₂ := U`,
    `V₁ := X`, rate split `T₁ = R₁`, `L₁₂ = R₂`, everything else `0`. -/
theorem superposition_pre_mem_umRegion (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {R₁ R₂ : ℝ} {kU : ℕ}
    (Pux : ProbDist (Fin kU × X)) (h1 : 0 ≤ R₁) (h2 : 0 ≤ R₂)
    (hR₂ : R₂ ≤ mutualInfo ((bcAuxJoint (bc12 W) Pux).map (fun z => (z.1.1, z.2.2))))
    (hR₁ : R₁ ≤ condMutualInfo ((bcAuxJoint (bc12 W) Pux).map (fun z => (z.1.2, z.2.1, z.1.1))))
    (hs : R₁ + R₂ ≤ mutualInfo ((bcAuxJoint (bc12 W) Pux).map (fun z => (z.1.2, z.2.1)))) :
    (R₁, R₂, (0 : ℝ)) ∈ umRegion W := by
  classical
  obtain ⟨a₀, -⟩ : ∃ a : Fin kU × X, True := by
    by_contra hc; push Not at hc
    have : ∑ t : Fin kU × X, Pux.pmf t = 0 := Finset.sum_eq_zero fun t _ => (hc t).elim
    linarith [Pux.sum_one]
  have : Nonempty X := ⟨a₀.2⟩
  have : Nonempty (Fin kU) := ⟨a₀.1⟩
  set K3 := (dmcPrecomp W Prod.snd).joint Pux with hK3
  rw [bcAuxJoint_bc12, map_comp_eq] at hR₂ hR₁ hs
  let eX := Fintype.equivFin X
  let ιU : Fin kU → Fin (kU + Fintype.card X + 1) := Fin.castLE (by omega)
  let ιX : X → Fin (kU + Fintype.card X + 1) := fun x => Fin.castLE (by omega) (eX x)
  have hιU : Function.Injective ιU := Fin.castLE_injective _
  have hιX : Function.Injective ιX := (Fin.castLE_injective _).comp eX.injective
  let φ : Fin kU × X → UMAux (kU + Fintype.card X + 1) X := fun a =>
    (0, 0, fun j => if j = 0 then ιU a.1 else 0, fun j => if j = 0 then ιX a.2 else 0, a.2)
  let T : Fin 3 → ℝ := fun j => if j = 0 then R₁ else 0
  let L : Fin 3 → ℝ := fun j => if j = 0 then R₂ else 0
  refine subset_closure (subset_convexHull ℝ _ ⟨_, Pux.map φ, 0, 0, L, 0, T, 0, ?_, ?_, ?_, ?_⟩)
  · intro i
    refine ⟨le_rfl, le_rfl, ?_, le_rfl, ?_, le_rfl⟩ <;> simp only [L, T] <;> split_ifs <;> linarith
  · simp [T, L]
  · unfold umCoveringConstraints
    simp only [map_comp_eq]
    refine ⟨fun i => ?_, ?_, ?_⟩
    · fin_cases i <;>
      · repeat (first | rw [cmi_const_fst _ _ (fun t t' => rfl)] |
          rw [cmi_const_snd _ _ (fun t t' => rfl)])
        simp
    all_goals
      repeat (first | rw [cmi_const_fst _ _ (fun t t' => rfl)] |
        rw [cmi_const_snd _ _ (fun t t' => rfl)])
      simp
  · intro J
    have hJ : J = K3.map (fun z => (φ z.1, z.2)) :=
      InfoTheory.Known.Certificates.BroadcastChannel.joint_eq_map_of_comp W Pux Prod.snd φ (fun t => t.2.2.2.2) (fun _ => rfl) J (fun _ => rfl)
        K3 (fun _ => rfl)
    rw [hJ]
    have hR₁' : R₁ ≤ condMutualInfo (K3.map (fun z => (z.1.2, z.2.1, z.1.1))) := hR₁
    have hR₂' : R₂ ≤ mutualInfo (K3.map (fun z => (z.1.1, z.2.2.1))) := hR₂
    have hs' : R₁ + R₂ ≤ mutualInfo (K3.map (fun z => (z.1.2, z.2.1))) := hs
    refine ⟨?_, ?_, ?_⟩ <;> unfold umDecodingConstraints <;> simp only [map_comp_eq]
    · -- receiver 1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · refine le_trans (le_of_eq (by simp [T])) (le_trans hR₁' (le_of_eq
          (cmi_relabel K3 _ _ ιX (fun u => (((0 : Fin _), (0 : Fin _)), ιU u, (0 : Fin _))) hιX
            (fun a b hab => hιU (by simp only [Prod.mk.injEq] at hab; exact hab.2.1))
            (fun t => rfl)).symm))
      · refine le_trans (le_of_eq (by simp [T, L]; ring)) (le_trans hs'
          (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => z.1.2) (fun z => z.2.1)
            (((0 : Fin _), (0 : Fin _)), (0 : Fin _)) (fun p => Function.invFun ιX p.2)
            (fun t => rfl) (fun t => (Function.leftInverse_invFun hιX t.1.2).symm)
            (fun t => rfl)) (condMutualInfo_nonneg _)))
      · refine le_trans (le_of_eq (by simp [T, L])) (le_trans hR₁' (le_add_of_le_of_nonneg
          (le_of_eq (cmi_relabel K3 _ _ (fun x => ((0 : Fin _), ιX x))
            (fun u => (((0 : Fin _), (0 : Fin _)), ιU u)) 
            (fun a b hab => hιX (by simp only [Prod.mk.injEq] at hab; exact hab.2))
            (fun a b hab => hιU (by simp only [Prod.mk.injEq] at hab; exact hab.2))
            (fun t => rfl)).symm) (condMutualInfo_nonneg _)))
      · refine le_trans (le_of_eq (by simp [T, L]; ring)) (le_trans hs'
          (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => z.1.2) (fun z => z.2.1)
            ((0 : Fin _), (0 : Fin _)) (fun p => Function.invFun ιX p.2.2)
            (fun t => rfl) (fun t => (Function.leftInverse_invFun hιX t.1.2).symm)
            (fun t => rfl)) (condMutualInfo_nonneg _)))
      · refine le_trans (le_of_eq (by simp [T, L]; ring)) (le_trans hs'
          (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => z.1.2) (fun z => z.2.1)
            (0 : Fin _) (fun p => Function.invFun ιX p.2.2.2)
            (fun t => rfl) (fun t => (Function.leftInverse_invFun hιX t.1.2).symm)
            (fun t => rfl)) (condMutualInfo_nonneg _)))
    · -- receiver 2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact le_trans (le_of_eq (by simp [T])) (condMutualInfo_nonneg _)
      · exact le_trans (le_of_eq (by simp [T, L]))
          (add_nonneg (condMutualInfo_nonneg _) (condMutualInfo_nonneg _))
      · refine le_trans (le_of_eq (by simp [T, L])) (le_trans hR₂'
          (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => z.1.1) (fun z => z.2.2.1)
            (((0 : Fin _), (0 : Fin _)), (0 : Fin _)) (fun p => Function.invFun ιU p.1)
            (fun t => rfl) (fun t => (Function.leftInverse_invFun hιU t.1.1).symm)
            (fun t => rfl)) (condMutualInfo_nonneg _)))
      · refine le_trans (le_of_eq (by simp [T, L])) (le_trans hR₂'
          (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => z.1.1) (fun z => z.2.2.1)
            ((0 : Fin _), (0 : Fin _)) (fun p => Function.invFun ιU p.2.1)
            (fun t => rfl) (fun t => (Function.leftInverse_invFun hιU t.1.1).symm)
            (fun t => rfl)) (condMutualInfo_nonneg _)))
      · refine le_trans (le_of_eq (by simp [T, L])) (le_trans hR₂'
          (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => z.1.1) (fun z => z.2.2.1)
            (0 : Fin _) (fun p => Function.invFun ιU p.2.2.1)
            (fun t => rfl) (fun t => (Function.leftInverse_invFun hιU t.1.1).symm)
            (fun t => rfl)) (condMutualInfo_nonneg _)))
    · -- receiver 3: nothing to decode
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact le_trans (le_of_eq (by simp [T])) (condMutualInfo_nonneg _)
      all_goals
        exact le_trans (le_of_eq (by simp [T, L]))
          (add_nonneg (condMutualInfo_nonneg _) (condMutualInfo_nonneg _))

/-- **Regression: the UM region contains the superposition coding region of receivers 1, 2 on its
    `R₃ = 0` face.** -/
theorem superpositionInnerBound_bc12_subset_umRegion (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ∀ r ∈ superpositionInnerBound (bc12 W), (r.1, r.2, (0 : ℝ)) ∈ umRegion W := by
  intro r hr
  have hcl : IsClosed {r : ℝ × ℝ | (r.1, r.2, (0 : ℝ)) ∈ umRegion W} :=
    isClosed_closure.preimage (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  refine closure_minimal (fun p hp => ?_) hcl hr
  obtain ⟨h1, h2, kU, Pux, hR₂, hR₁, hs⟩ := hp
  exact superposition_pre_mem_umRegion W Pux h1 h2 hR₂ hR₁ hs

/-- **Regression (degraded case)**: if the receivers-1,2 sub-BC `bc12 W` is physically degraded,
    its capacity region (Bergmans–Gallager, `Bridge.degradedBC_capacity_theorem`), padded with
    `R₃ = 0`, lies in the frozen `umRegion W`. -/
theorem bcCapacityRegion_bc12_subset_umRegion_of_degraded (W : BroadcastChannel3 X Y₁ Y₂ Y₃)
    (hdeg : IsPhysicallyDegradedBC (bc12 W)) :
    ∀ r ∈ bcCapacityRegion (bc12 W), (r.1, r.2, (0 : ℝ)) ∈ umRegion W := by
  rw [degradedBC_capacity_theorem _ hdeg, ← superpositionInnerBound_eq_degradedBCRegion _ hdeg]
  exact superpositionInnerBound_bc12_subset_umRegion W

end Regression

/-! ### Regression: Marton's region of receivers 1, 2 on the `R₃ = 0` face

The useless-receiver check of the problem file, formalised. Given a Marton auxiliary law
`p(w, u, v, x)` for the sub-BC `bc12 W`, take `Q, W_UM` constant, `U₁₂ := W`, `V₁ := U`,
`V₂ := V` and all other layers constant (`martonUMEmbed`). Every covering term vanishes except
`I(V₁; V₂ | U₁₂) = I(U; V | W)`, and the packing bounds of receivers 1, 2 become
`I(U; Y₁ | W)`, `I(W, U; Y₁)`, `I(V; Y₂ | W)`, `I(W, V; Y₂)` (receiver 3 decodes nothing).
The remaining linear system in the split / bin rates is El Gamal–Kim's rate-split form of
Marton's region; `marton_split_reals` performs the Fourier–Motzkin step with explicit witnesses
when `I(U;V|W) ≤ I(U;Y₁|W) + I(V;Y₂|W)`. In the other case the Marton constraints force
`R₁ + R₂ ≤ min(I(W;Y₁), I(W;Y₂))` and the point is reached with `U, V` constant. -/

section MartonRegression

open InfoTheory.Known.Certificates.BroadcastChannel (joint_eq_map_of_comp)

/-- Fourier–Motzkin step (real arithmetic only). -/
theorem marton_split_reals {R₁ R₂ A₁ A₂ I₁ I₂ B : ℝ} (h1 : 0 ≤ R₁) (h2 : 0 ≤ R₂)
    (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂) (hIA₂ : I₂ ≤ A₂)
    (hB0 : 0 ≤ B) (hB : B ≤ I₁ + I₂) (hR₁ : R₁ ≤ A₁) (hR₂ : R₂ ≤ A₂)
    (hs₁ : R₁ + R₂ ≤ A₁ + I₂ - B) (hs₂ : R₁ + R₂ ≤ I₁ + A₂ - B) :
    ∃ T₀ T₁ c₁ c₂ s₀ s₁ : ℝ, 0 ≤ T₀ ∧ 0 ≤ T₁ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ ∧ 0 ≤ s₀ ∧ 0 ≤ s₁ ∧
      R₁ = T₀ + c₁ ∧ R₂ = T₁ + c₂ ∧ T₀ + s₀ ≤ I₁ ∧ T₁ + s₁ ≤ I₂ ∧
      c₁ + c₂ + T₀ + s₀ ≤ A₁ ∧ c₁ + c₂ + T₁ + s₁ ≤ A₂ ∧ B ≤ s₀ + s₁ := by
  set s₀ := max 0 (max (B - I₂) (B - A₂ + R₂)) with hs₀
  have l0 : 0 ≤ s₀ := le_max_left _ _
  have l1 : B - I₂ ≤ s₀ := (le_max_left _ _).trans (le_max_right _ _)
  have l2 : B - A₂ + R₂ ≤ s₀ := (le_max_right _ _).trans (le_max_right _ _)
  have u1 : s₀ ≤ B := max_le hB0 (max_le (by linarith) (by linarith))
  have u2 : s₀ ≤ I₁ := max_le hI₁ (max_le (by linarith) (by linarith))
  have u3 : s₀ ≤ A₁ - R₁ := max_le (by linarith) (max_le (by linarith) (by linarith))
  refine ⟨min R₁ (I₁ - s₀), min R₂ (I₂ - (B - s₀)), R₁ - min R₁ (I₁ - s₀),
    R₂ - min R₂ (I₂ - (B - s₀)), s₀, B - s₀, le_min h1 (by linarith), le_min h2 (by linarith),
    by linarith [min_le_left R₁ (I₁ - s₀)], by linarith [min_le_left R₂ (I₂ - (B - s₀))], l0,
    by linarith, by ring, by ring, by linarith [min_le_right R₁ (I₁ - s₀)],
    by linarith [min_le_right R₂ (I₂ - (B - s₀))], ?_, ?_, by linarith⟩
  · rcases min_cases R₂ (I₂ - (B - s₀)) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  · rcases min_cases R₁ (I₁ - s₀) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

variable {Ω α α' β β' γ γ' : Type*} [Fintype Ω] [Fintype α] [Fintype α'] [Fintype β]
  [Fintype β'] [Fintype γ] [Fintype γ']

/-- Relabelling all three variables of a conditional mutual information injectively. -/
theorem cmi_relabel3 (R : ProbDist Ω) (a : Ω → α) (b : Ω → β) (c : Ω → γ) (g : α → α')
    (g' : β → β') (h : γ → γ') (hg : Function.Injective g) (hg' : Function.Injective g')
    (hh : Function.Injective h) :
    condMutualInfo (R.map fun t => (g (a t), g' (b t), h (c t))) =
      condMutualInfo (R.map fun t => (a t, b t, c t)) := by
  have e1 := cmi_relabel R (fun t => (g (a t), g' (b t), h (c t))) (fun t => (a t, g' (b t), c t))
    g h hg hh (fun t => rfl)
  have e2 := condMutualInfo_swap R a (fun t => g' (b t)) c
  have e3 := cmi_relabel R (fun t => (g' (b t), a t, c t)) (fun t => (b t, a t, c t)) g' id hg'
    Function.injective_id (fun t => rfl)
  have e4 := condMutualInfo_swap R a b c
  exact e1.trans (e2.symm.trans (e3.trans e4))

/-- The joint law through `bc12 W` is the `(Y₁, Y₂)`-marginal of the joint law through `W`. -/
theorem joint_bc12_eq_map {A : Type*} [Fintype A] (W : BroadcastChannel3 X Y₁ Y₂ Y₃)
    (P : ProbDist A) (f : A → X) (J : ProbDist (A × (Y₁ × Y₂)))
    (hJ : ∀ z, J.pmf z = P.pmf z.1 * (bc12 W).trans (f z.1) z.2)
    (K : ProbDist (A × (Y₁ × Y₂ × Y₃))) (hK : ∀ z, K.pmf z = P.pmf z.1 * W.trans (f z.1) z.2) :
    J = K.map (fun z => (z.1, (z.2.1, z.2.2.1))) := by
  classical
  refine probDist_eq_of_pmf fun ⟨a, y₁, y₂⟩ => ?_
  rw [hJ]
  simp only [bc12, ProbDist.map, hK]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_eq_single y₁]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₂]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb; simp [hb]
  · simp


/-- The UM auxiliary tuple used for a Marton point: `Q, W_UM` constant, `U₁₂ := W`,
    `V₁ := U`, `V₂ := V`, everything else constant. -/
def martonUMEmbed (kW kU kV : ℕ) (t : Fin kW × Fin kU × Fin kV × X) :
    UMAux (kW + kU + kV + 1) X :=
  (0, 0, fun j => if j = 0 then Fin.castLE (by omega) t.1 else 0,
    fun j => if j = 0 then Fin.castLE (by omega) t.2.1 else
      if j = 1 then Fin.castLE (by omega) t.2.2.1 else 0, t.2.2.2)

/-- A rate vector supported on the first two coordinates. -/
def vec2 (a b : ℝ) : Fin 3 → ℝ := fun j => if j = 0 then a else if j = 1 then b else 0

/-- Covering constraints for the Marton embedding: only `I(V₁; V₂ | U₁₂) = I(U; V | W)` survives. -/
theorem martonUM_covering {kW kU kV : ℕ} (P : ProbDist (Fin kW × Fin kU × Fin kV × X))
    {s₀ s₁ : ℝ} (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁)
    (hB : condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) ≤ s₀ + s₁) :
    umCoveringConstraints (P.map (martonUMEmbed kW kU kV)) 0 (vec2 s₀ s₁) := by
  classical
  let k := kW + kU + kV + 1
  have hιC : Function.Injective (Fin.castLE (by omega) : Fin kW → Fin k) := Fin.castLE_injective _
  have hB' : condMutualInfo ((P.map (martonUMEmbed kW kU kV)).map fun t =>
      (t.2.2.2.1 0, t.2.2.2.1 1, ((t.1, t.2.1), t.2.2.1))) =
      condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) := by
    rw [map_comp_eq]
    exact cmi_relabel3 P (fun t => t.2.1) (fun t => t.2.2.1) (fun t => t.1)
      (Fin.castLE (by omega) : Fin kU → Fin k) (Fin.castLE (by omega) : Fin kV → Fin k)
      (fun c => (((0 : Fin k), (0 : Fin k)),
        fun j : Fin 3 => if j = 0 then (Fin.castLE (by omega) c : Fin k) else 0))
      (Fin.castLE_injective _) (Fin.castLE_injective _)
      (fun a b hab => hιC (by simpa using congrFun (congrArg Prod.snd hab) 0))
  unfold umCoveringConstraints
  simp only [map_comp_eq] at hB' ⊢
  generalize condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) = Bv at hB hB' ⊢
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;>
      repeat (first | rw [cmi_const_fst _ _ (fun t t' => rfl)] |
        rw [cmi_const_snd _ _ (fun t t' => rfl)])
    · refine ⟨by simp, by simp [vec2, hs₀], le_trans (le_of_eq ?_) (le_trans hB (le_of_eq ?_))⟩
      · rw [show (0 : ℝ) + 0 + (0 + 0) = 0 by ring, zero_add]
        exact hB'
      · simp [vec2]
    all_goals (simp [vec2]; linarith)
  · rw [cmi_const_snd _ _ (fun t t' => rfl), cmi_const_snd _ _ (fun t t' => rfl)]
    simp
  · rw [hB']
    repeat (first | rw [cmi_const_fst _ _ (fun t t' => rfl)] |
        rw [cmi_const_snd _ _ (fun t t' => rfl)])
    simp [vec2]
    linarith

/-- Decoding constraints of receiver 1 for the Marton embedding. -/
theorem martonUM_decoding₁ {kW kU kV : ℕ}
    [Nonempty (Fin kW)] [Nonempty (Fin kU)]
    (K3 : ProbDist ((Fin kW × Fin kU × Fin kV × X) × (Y₁ × Y₂ × Y₃)))
    {T₀ T₁ c₁ c₂ s₀ s₁ : ℝ}
    (d₁ : T₀ + s₀ ≤ condMutualInfo (K3.map fun z => (z.1.2.1, z.2.1, z.1.1)))
    (d₃ : c₁ + c₂ + T₀ + s₀ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.1), z.2.1))) :
    umDecodingConstraints
      ((K3.map (fun z => (martonUMEmbed kW kU kV z.1, z.2))).map fun z => (z.1, z.2.1)) 0
      0 (vec2 c₁ 0) (vec2 c₂ 0) 0 (vec2 T₀ T₁) (vec2 s₀ s₁) := by
  classical
  let k := kW + kU + kV + 1
  let ιC : Fin kW → Fin k := Fin.castLE (by omega)
  let ιU : Fin kU → Fin k := Fin.castLE (by omega)
  have hιC : Function.Injective ιC := Fin.castLE_injective _
  have hιU : Function.Injective ιU := Fin.castLE_injective _
  have iC2 : Function.Injective (fun c : Fin kW => (((0 : Fin k), (0 : Fin k)), ιC c)) :=
    fun a b hab => hιC (by simp only [Prod.mk.injEq] at hab; exact hab.2)
  unfold umDecodingConstraints
  simp only [map_comp_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_of_eq (by simp [vec2])) (le_trans d₁ (le_of_eq (cmi_relabel K3 _ _ ιU
      (fun c => (((0 : Fin k), (0 : Fin k)), ιC c, (0 : Fin k))) hιU
      (fun a b hab => hιC (by simp only [Prod.mk.injEq] at hab; exact hab.2.1))
      (fun t => rfl)).symm))
  · exact le_trans (le_of_eq (by simp [vec2] )) (le_trans d₃
      (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => (z.1.1, z.1.2.1))
        (fun z => z.2.1) (((0 : Fin k), (0 : Fin k)), (0 : Fin k))
        (fun p => (Function.invFun ιC p.1, Function.invFun ιU p.2)) (fun t => rfl)
        (fun t => Prod.ext (Function.leftInverse_invFun hιC t.1.1).symm
          (Function.leftInverse_invFun hιU t.1.2.1).symm) (fun t => rfl))
        (condMutualInfo_nonneg _)))
  · exact le_trans (le_of_eq (by simp [vec2])) (le_trans d₁ (le_add_of_le_of_nonneg
      (le_of_eq (cmi_relabel K3 _ _ (fun u => ((0 : Fin k), ιU u))
        (fun c => (((0 : Fin k), (0 : Fin k)), ιC c))
        (fun a b hab => hιU (by simp only [Prod.mk.injEq] at hab; exact hab.2)) iC2
        (fun t => rfl)).symm) (condMutualInfo_nonneg _)))
  · exact le_trans (le_of_eq (by simp [vec2] )) (le_trans d₃
      (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => (z.1.1, z.1.2.1))
        (fun z => z.2.1) ((0 : Fin k), (0 : Fin k))
        (fun p => (Function.invFun ιC p.1, Function.invFun ιU p.2.2)) (fun t => rfl)
        (fun t => Prod.ext (Function.leftInverse_invFun hιC t.1.1).symm
          (Function.leftInverse_invFun hιU t.1.2.1).symm) (fun t => rfl))
        (condMutualInfo_nonneg _)))
  · exact le_trans (le_of_eq (by simp [vec2] )) (le_trans d₃
      (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => (z.1.1, z.1.2.1))
        (fun z => z.2.1) (0 : Fin k)
        (fun p => (Function.invFun ιC p.2.1, Function.invFun ιU p.2.2.2)) (fun t => rfl)
        (fun t => Prod.ext (Function.leftInverse_invFun hιC t.1.1).symm
          (Function.leftInverse_invFun hιU t.1.2.1).symm) (fun t => rfl))
        (condMutualInfo_nonneg _)))

/-- Decoding constraints of receiver 2 for the Marton embedding. -/
theorem martonUM_decoding₂ {kW kU kV : ℕ}
    [Nonempty (Fin kW)] [Nonempty (Fin kV)]
    (K3 : ProbDist ((Fin kW × Fin kU × Fin kV × X) × (Y₁ × Y₂ × Y₃)))
    {T₀ T₁ c₁ c₂ s₀ s₁ : ℝ}
    (d₂ : T₁ + s₁ ≤ condMutualInfo (K3.map fun z => (z.1.2.2.1, z.2.2.1, z.1.1)))
    (d₄ : c₁ + c₂ + T₁ + s₁ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.2.1), z.2.2.1))) :
    umDecodingConstraints
      ((K3.map (fun z => (martonUMEmbed kW kU kV z.1, z.2))).map fun z => (z.1, z.2.2.1)) 1
      0 (vec2 c₁ 0) (vec2 c₂ 0) 0 (vec2 T₀ T₁) (vec2 s₀ s₁) := by
  classical
  let k := kW + kU + kV + 1
  let ιC : Fin kW → Fin k := Fin.castLE (by omega)
  let ιV : Fin kV → Fin k := Fin.castLE (by omega)
  have hιC : Function.Injective ιC := Fin.castLE_injective _
  have hιV : Function.Injective ιV := Fin.castLE_injective _
  have iC2 : Function.Injective (fun c : Fin kW => (((0 : Fin k), (0 : Fin k)), ιC c)) :=
    fun a b hab => hιC (by simp only [Prod.mk.injEq] at hab; exact hab.2)
  unfold umDecodingConstraints
  simp only [map_comp_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_of_eq (by simp [vec2])) (le_trans d₂ (le_of_eq (cmi_relabel K3 _ _ ιV
      (fun c => (((0 : Fin k), (0 : Fin k)), (0 : Fin k), ιC c)) hιV
      (fun a b hab => hιC (by simp only [Prod.mk.injEq] at hab; exact hab.2.2))
      (fun t => rfl)).symm))
  · exact le_trans (le_of_eq (by simp [vec2])) (le_trans d₂ (le_add_of_le_of_nonneg
      (le_of_eq (cmi_relabel K3 _ _ (fun v => ((0 : Fin k), ιV v))
        (fun c => (((0 : Fin k), (0 : Fin k)), ιC c))
        (fun a b hab => hιV (by simp only [Prod.mk.injEq] at hab; exact hab.2)) iC2
        (fun t => rfl)).symm) (condMutualInfo_nonneg _)))
  · exact le_trans (le_of_eq (by simp [vec2] )) (le_trans d₄
      (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => (z.1.1, z.1.2.2.1))
        (fun z => z.2.2.1) (((0 : Fin k), (0 : Fin k)), (0 : Fin k))
        (fun p => (Function.invFun ιC p.1, Function.invFun ιV p.2)) (fun t => rfl)
        (fun t => Prod.ext (Function.leftInverse_invFun hιC t.1.1).symm
          (Function.leftInverse_invFun hιV t.1.2.2.1).symm) (fun t => rfl))
        (condMutualInfo_nonneg _)))
  · exact le_trans (le_of_eq (by simp [vec2] )) (le_trans d₄
      (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => (z.1.1, z.1.2.2.1))
        (fun z => z.2.2.1) ((0 : Fin k), (0 : Fin k))
        (fun p => (Function.invFun ιC p.2.1, Function.invFun ιV p.2.2)) (fun t => rfl)
        (fun t => Prod.ext (Function.leftInverse_invFun hιC t.1.1).symm
          (Function.leftInverse_invFun hιV t.1.2.2.1).symm) (fun t => rfl))
        (condMutualInfo_nonneg _)))
  · exact le_trans (le_of_eq (by simp [vec2] )) (le_trans d₄
      (le_add_of_le_of_nonneg (mi_le_cmi_of_const K3 _ (fun z => (z.1.1, z.1.2.2.1))
        (fun z => z.2.2.1) (0 : Fin k)
        (fun p => (Function.invFun ιC p.2.2.1, Function.invFun ιV p.2.2.2)) (fun t => rfl)
        (fun t => Prod.ext (Function.leftInverse_invFun hιC t.1.1).symm
          (Function.leftInverse_invFun hιV t.1.2.2.1).symm) (fun t => rfl))
        (condMutualInfo_nonneg _)))

/-- Decoding constraints of receiver 3 (nothing to decode) for the Marton embedding. -/
theorem martonUM_decoding₃ {kW kU kV : ℕ}
    (K3 : ProbDist ((Fin kW × Fin kU × Fin kV × X) × (Y₁ × Y₂ × Y₃)))
    (T₀ T₁ c₁ c₂ s₀ s₁ : ℝ) :
    umDecodingConstraints
      ((K3.map (fun z => (martonUMEmbed kW kU kV z.1, z.2))).map fun z => (z.1, z.2.2.2)) 2
      0 (vec2 c₁ 0) (vec2 c₂ 0) 0 (vec2 T₀ T₁) (vec2 s₀ s₁) := by
  unfold umDecodingConstraints
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_of_eq (by simp [vec2])) (condMutualInfo_nonneg _)
  all_goals
    exact le_trans (le_of_eq (by simp [vec2]))
      (add_nonneg (condMutualInfo_nonneg _) (condMutualInfo_nonneg _))

/-- **Marton point ⇒ UM point** (before closure), under `I(U;V|W) ≤ I(U;Y₁|W) + I(V;Y₂|W)`:
    Fourier–Motzkin rate split (`marton_split_reals`) plus the embedding `martonUMEmbed`. -/
theorem marton_pre_mem_umRegion (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {kW kU kV : ℕ}
    (P : ProbDist (Fin kW × Fin kU × Fin kV × X))
    (K3 : ProbDist ((Fin kW × Fin kU × Fin kV × X) × (Y₁ × Y₂ × Y₃)))
    (hK : ∀ z, K3.pmf z = P.pmf z.1 * W.trans z.1.2.2.2 z.2) {R₁ R₂ : ℝ}
    (h1 : 0 ≤ R₁) (h2 : 0 ≤ R₂)
    (hB : condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) ≤
      condMutualInfo (K3.map fun z => (z.1.2.1, z.2.1, z.1.1)) +
        condMutualInfo (K3.map fun z => (z.1.2.2.1, z.2.2.1, z.1.1)))
    (hR₁ : R₁ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.1), z.2.1)))
    (hR₂ : R₂ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.2.1), z.2.2.1)))
    (hs₁ : R₁ + R₂ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.1), z.2.1)) +
      condMutualInfo (K3.map fun z => (z.1.2.2.1, z.2.2.1, z.1.1)) -
        condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)))
    (hs₂ : R₁ + R₂ ≤ condMutualInfo (K3.map fun z => (z.1.2.1, z.2.1, z.1.1)) +
      mutualInfo (K3.map fun z => ((z.1.1, z.1.2.2.1), z.2.2.1)) -
        condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1))) :
    (R₁, R₂, (0 : ℝ)) ∈ umRegion W := by
  classical
  obtain ⟨a₀, -⟩ : ∃ a : Fin kW × Fin kU × Fin kV × X, True := by
    by_contra hc; push Not at hc
    have : ∑ t : Fin kW × Fin kU × Fin kV × X, P.pmf t = 0 :=
      Finset.sum_eq_zero fun t _ => (hc t).elim
    linarith [P.sum_one]
  have : Nonempty (Fin kW) := ⟨a₀.1⟩
  have : Nonempty (Fin kU) := ⟨a₀.2.1⟩
  have : Nonempty (Fin kV) := ⟨a₀.2.2.1⟩
  have c₂ := mutualInfo_add_condMutualInfo K3 (fun z => z.1.1) (fun z => z.1.2.2.1)
    (fun z => z.2.2.1)
  have n₂ := mutualInfo_nonneg (K3.map fun z => (z.1.1, z.2.2.1))
  obtain ⟨T₀, T₁, c₁, c₂', s₀, s₁, hT₀, hT₁, hc₁, hc₂, hs₀, hs₁', e₁, e₂, d₁, d₂, d₃, d₄, d₅⟩ :=
    marton_split_reals h1 h2 (condMutualInfo_nonneg _) (condMutualInfo_nonneg _)
      (by linarith) (condMutualInfo_nonneg _) hB hR₁ hR₂ hs₁ hs₂
  refine subset_closure (subset_convexHull ℝ _ ⟨_, P.map (martonUMEmbed kW kU kV), 0,
    vec2 c₁ 0, vec2 c₂' 0, 0, vec2 T₀ T₁, vec2 s₀ s₁, ?_, ?_,
    martonUM_covering P hs₀ hs₁' d₅, ?_⟩)
  · intro i
    refine ⟨le_rfl, ?_, ?_, le_rfl, ?_, ?_⟩ <;> simp only [vec2] <;> split_ifs <;> linarith
  · refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [vec2] <;> linarith
  · intro J
    have hJ : J = K3.map (fun z => (martonUMEmbed kW kU kV z.1, z.2)) :=
      joint_eq_map_of_comp W P (fun t => t.2.2.2) (martonUMEmbed kW kU kV)
        (fun t => t.2.2.2.2) (fun _ => rfl) J (fun _ => rfl) K3 hK
    rw [hJ]
    exact ⟨martonUM_decoding₁ K3 d₁ d₃, martonUM_decoding₂ K3 d₂ d₄,
      martonUM_decoding₃ K3 _ _ _ _ _ _⟩

/-- **Marton point ⇒ UM point** in general: if `I(U;V|W) > I(U;Y₁|W) + I(V;Y₂|W)` the Marton
    constraints force `R₁ + R₂ ≤ min(I(W;Y₁), I(W;Y₂))`, achieved with `U, V` constant. -/
theorem marton_point_mem_umRegion (W : BroadcastChannel3 X Y₁ Y₂ Y₃) {kW kU kV : ℕ}
    (P : ProbDist (Fin kW × Fin kU × Fin kV × X))
    (J : ProbDist ((Fin kW × Fin kU × Fin kV × X) × (Y₁ × Y₂)))
    (hJ : ∀ z, J.pmf z = P.pmf z.1 * (bc12 W).trans z.1.2.2.2 z.2) {R₁ R₂ : ℝ}
    (h1 : 0 ≤ R₁) (h2 : 0 ≤ R₂)
    (ha : R₁ ≤ mutualInfo (J.map fun z => ((z.1.1, z.1.2.1), z.2.1)))
    (hb : R₂ ≤ mutualInfo (J.map fun z => ((z.1.1, z.1.2.2.1), z.2.2)))
    (hc : R₁ + R₂ ≤ mutualInfo (J.map fun z => ((z.1.1, z.1.2.1), z.2.1)) +
      condMutualInfo (J.map fun z => (z.1.2.2.1, z.2.2, z.1.1)) -
        condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)))
    (hd : R₁ + R₂ ≤ condMutualInfo (J.map fun z => (z.1.2.1, z.2.1, z.1.1)) +
      mutualInfo (J.map fun z => ((z.1.1, z.1.2.2.1), z.2.2)) -
        condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1))) :
    (R₁, R₂, (0 : ℝ)) ∈ umRegion W := by
  classical
  set K3 := (dmcPrecomp W (fun t : Fin kW × Fin kU × Fin kV × X => t.2.2.2)).joint P with hK3
  have hK : ∀ z, K3.pmf z = P.pmf z.1 * W.trans z.1.2.2.2 z.2 := fun _ => rfl
  have hJK := joint_bc12_eq_map W P (fun t => t.2.2.2) J hJ K3 hK
  subst hJK
  simp only [map_comp_eq] at ha hb hc hd
  have ha' : R₁ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.1), z.2.1)) := ha
  have hb' : R₂ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.2.1), z.2.2.1)) := hb
  have hc' : R₁ + R₂ ≤ mutualInfo (K3.map fun z => ((z.1.1, z.1.2.1), z.2.1)) +
      condMutualInfo (K3.map fun z => (z.1.2.2.1, z.2.2.1, z.1.1)) -
        condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) := hc
  have hd' : R₁ + R₂ ≤ condMutualInfo (K3.map fun z => (z.1.2.1, z.2.1, z.1.1)) +
      mutualInfo (K3.map fun z => ((z.1.1, z.1.2.2.1), z.2.2.1)) -
        condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) := hd
  by_cases hB : condMutualInfo (P.map fun t => (t.2.1, t.2.2.1, t.1)) ≤
      condMutualInfo (K3.map fun z => (z.1.2.1, z.2.1, z.1.1)) +
        condMutualInfo (K3.map fun z => (z.1.2.2.1, z.2.2.1, z.1.1))
  · exact marton_pre_mem_umRegion W P K3 hK h1 h2 hB ha' hb' hc' hd'
  · push Not at hB
    set P' := P.map (fun t => (t.1, (0 : Fin 1), (0 : Fin 1), t.2.2.2)) with hP'
    set K3' := (dmcPrecomp W (fun t : Fin kW × Fin 1 × Fin 1 × X => t.2.2.2)).joint P'
      with hK3'
    have hK' : ∀ z, K3'.pmf z = P'.pmf z.1 * W.trans z.1.2.2.2 z.2 := fun _ => rfl
    have hKK : K3' = K3.map (fun z => ((z.1.1, (0 : Fin 1), (0 : Fin 1), z.1.2.2.2), z.2)) :=
      joint_eq_map_of_comp W P (fun t => t.2.2.2) (fun t => (t.1, (0 : Fin 1), (0 : Fin 1), t.2.2.2))
        (fun t => t.2.2.2) (fun _ => rfl) K3' (fun _ => rfl) K3 hK
    have z₁ : condMutualInfo (K3'.map fun z => (z.1.2.1, z.2.1, z.1.1)) = 0 :=
      cmi_const_fst _ _ (fun _ _ => Subsingleton.elim _ _)
    have z₂ : condMutualInfo (K3'.map fun z => (z.1.2.2.1, z.2.2.1, z.1.1)) = 0 :=
      cmi_const_fst _ _ (fun _ _ => Subsingleton.elim _ _)
    have z₃ : condMutualInfo (P'.map fun t => (t.2.1, t.2.2.1, t.1)) = 0 :=
      cmi_const_fst _ _ (fun _ _ => Subsingleton.elim _ _)
    have hA₁ : mutualInfo (K3.map fun z => (z.1.1, z.2.1)) ≤
        mutualInfo (K3'.map fun z => ((z.1.1, z.1.2.1), z.2.1)) := by
      rw [hKK, map_comp_eq]
      have := mi_map_left_le (K3.map fun z => ((z.1.1, (0 : Fin 1)), z.2.1)) Prod.fst
      rw [map_comp_eq] at this
      exact this
    have hA₂ : mutualInfo (K3.map fun z => (z.1.1, z.2.2.1)) ≤
        mutualInfo (K3'.map fun z => ((z.1.1, z.1.2.2.1), z.2.2.1)) := by
      rw [hKK, map_comp_eq]
      have := mi_map_left_le (K3.map fun z => ((z.1.1, (0 : Fin 1)), z.2.2.1)) Prod.fst
      rw [map_comp_eq] at this
      exact this
    have c₁ := mutualInfo_add_condMutualInfo K3 (fun z => z.1.1) (fun z => z.1.2.1)
      (fun z => z.2.1)
    have c₂ := mutualInfo_add_condMutualInfo K3 (fun z => z.1.1) (fun z => z.1.2.2.1)
      (fun z => z.2.2.1)
    exact marton_pre_mem_umRegion W P' K3' hK' h1 h2 (by rw [z₁, z₂, z₃]; norm_num)
      (by linarith) (by linarith) (by rw [z₂, z₃]; linarith) (by rw [z₁, z₃]; linarith)

/-- **Regression: the UM region contains Marton's region (with common auxiliary) of
    receivers 1, 2 on its `R₃ = 0` face**: `martonInnerBound (bc12 W) × {0} ⊆ umRegion W`. -/
theorem martonInnerBound_bc12_subset_umRegion (W : BroadcastChannel3 X Y₁ Y₂ Y₃) :
    ∀ r ∈ martonInnerBound (bc12 W), (r.1, r.2, (0 : ℝ)) ∈ umRegion W := by
  intro r hr
  have hcl : IsClosed {r : ℝ × ℝ | (r.1, r.2, (0 : ℝ)) ∈ umRegion W} :=
    isClosed_closure.preimage (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  refine closure_minimal (fun p hp => ?_) hcl hr
  obtain ⟨h1, h2, kW, kU, kV, P, hP⟩ := hp
  obtain ⟨a, b, c, d⟩ := hP
  refine marton_point_mem_umRegion W P _ ?_ h1 h2 a b c d
  intro z
  rfl

end MartonRegression

end InfoTheory.Known.Certificates.BroadcastChannelThreeReceivers

