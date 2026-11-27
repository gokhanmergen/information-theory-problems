import InfoTheory.Problems.BroadcastChannel
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.BroadcastChannel`

The frozen statement asks whether, for every finite two-receiver DM broadcast channel `W`, the
operational capacity region `bcCapacityRegion W` equals Marton's inner bound
`martonInnerBound W` (Core, with the common auxiliary `W`).

## Certified (about exactly these objects)
* `bcCapacityRegion_subset_box` — the trivial outer bound `C(W) ⊆ [0, C₁] × [0, C₂]`
  (`Cⱼ` = capacity of the marginal `p(yⱼ | x)`; reused from
  `Known.Operational.bcCapacityRegion_subset_Icc_prod_Icc`, El Gamal–Kim §5.1).
* `martonInnerBound_subset_box` — **Marton's region satisfies the same outer bound**:
  `martonInnerBound W ⊆ [0, C₁] × [0, C₂]`. Each private-rate constraint
  `R₁ ≤ I(W, U; Y₁)` is bounded by `C₁` through the data-processing inequality for the
  Markov chain `(W, U) → X → Y₁` (`mi_fst_le_capacity`).
* `mk_zero_mem_martonInnerBound_iff`, `zero_mk_mem_martonInnerBound_iff` — on each axis,
  Marton's region is exactly `[0, Cⱼ]` (take `W, V` constant and `U = X`, resp. `V = X`).
* `mk_zero_mem_iff`, `zero_mk_mem_iff` — hence **the two sides of the statement agree on
  both axes** (the operational axes are `Known.Operational.mk_zero_mem_bcCapacityRegion_iff`,
  i.e. Shannon's theorem for each marginal). In particular both sides are nonempty, closed,
  bounded sets, and they contain `(0, 0)` and the corner points `(C₁, 0)`, `(0, C₂)`.

## Not certified
* Achievability of Marton's region (`martonInnerBound W ⊆ bcCapacityRegion W`): Marton coding
  needs the mutual covering lemma, which is not in the library.
* Any outer bound tighter than the box (UV outer bound, degraded / less noisy converses):
  these need Csiszár-sum-identity converses for broadcast codes.
* No statement-level conclusion: the problem is open (Marton's bound is not known to be
  suboptimal for any channel; El Gamal–Kim Ch. 8).

Sources: Marton, IEEE Trans. IT 1979; El Gamal–Kim, *Network Information Theory*, §5.1, §8.4.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BroadcastChannel

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.BroadcastChannel

/-! ### Toolkit: auxiliary-variable mutual informations through a broadcast channel -/

section Toolkit

variable {A B Z X Y₁ Y₂ : Type*} [Fintype A] [Fintype B] [Fintype Z] [Fintype X]
  [Fintype Y₁] [Fintype Y₂]

theorem map_id_eq (P : ProbDist A) : P.map id = P := by
  classical
  refine probDist_eq_of_pmf fun a => ?_
  simp only [ProbDist.map, id]
  rw [Finset.sum_ite_eq']
  simp

/-- Data processing on the left: `I(g(A); Z) ≤ I(A; Z)`. -/
theorem mi_map_left_le (K : ProbDist (A × Z)) (g : A → B) :
    mutualInfo (K.map (Prod.map g id)) ≤ mutualInfo K := by
  rw [← mutualInfo_swap (K.map (Prod.map g id)), ← mutualInfo_swap K]
  have : (K.map (Prod.map g id)).map Prod.swap = (K.map Prod.swap).map (Prod.map id g) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  rw [this]
  exact mutualInfo_map_right_le _ _

/-- The `(A, Y₁)` marginal of the joint law `P(a) W(y₁, y₂ | f a)`. -/
theorem joint_map_fst_eq (W : DMC X (Y₁ × Y₂)) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × (Y₁ × Y₂))) (hJ : ∀ z, J.pmf z = P.pmf z.1 * W.trans (f z.1) z.2) :
    J.map (fun z => (z.1, z.2.1)) = (dmcPrecomp (marginalFst W) f).joint P := by
  classical
  refine probDist_eq_of_pmf fun ⟨a, y⟩ => ?_
  simp only [ProbDist.map, DMC.joint, dmcPrecomp, marginalFst, hJ]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
    · simp [Finset.mul_sum]
    · intro y' _ h; simp [h]
    · simp
  · intro a' _ h; simp [h]
  · simp

/-- The `(A, Y₂)` marginal of the joint law `P(a) W(y₁, y₂ | f a)`. -/
theorem joint_map_snd_eq (W : DMC X (Y₁ × Y₂)) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × (Y₁ × Y₂))) (hJ : ∀ z, J.pmf z = P.pmf z.1 * W.trans (f z.1) z.2) :
    J.map (fun z => (z.1, z.2.2)) = (dmcPrecomp (marginalSnd W) f).joint P := by
  classical
  refine probDist_eq_of_pmf fun ⟨a, y⟩ => ?_
  simp only [ProbDist.map, DMC.joint, dmcPrecomp, marginalSnd, hJ]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single y]
    · simp [Finset.mul_sum]
    · intro y' _ h; simp [h]
    · simp
  · intro a' _ h; simp [h]
  · simp

/-- **Data processing through the channel, receiver 1**: for any auxiliary `g(A)` of an input
    `X = f(A)`, `I(g(A); Y₁) ≤ C(p(y₁ | x))`. -/
theorem mi_fst_le_capacity (W : DMC X (Y₁ × Y₂)) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × (Y₁ × Y₂))) (hJ : ∀ z, J.pmf z = P.pmf z.1 * W.trans (f z.1) z.2)
    (g : A → B) : mutualInfo (J.map (fun z => (g z.1, z.2.1))) ≤ (marginalFst W).capacity := by
  have h1 : J.map (fun z => (g z.1, z.2.1)) = (J.map (fun z => (z.1, z.2.1))).map (Prod.map g id) := by
    rw [map_comp_eq]; rfl
  rw [h1]
  refine (mi_map_left_le _ g).trans ?_
  rw [joint_map_fst_eq W P f J hJ, dmcPrecomp_mutualInfo_eq]
  exact dmc_mutualInfo_le_capacity _ _

/-- **Data processing through the channel, receiver 2**. -/
theorem mi_snd_le_capacity (W : DMC X (Y₁ × Y₂)) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × (Y₁ × Y₂))) (hJ : ∀ z, J.pmf z = P.pmf z.1 * W.trans (f z.1) z.2)
    (g : A → B) : mutualInfo (J.map (fun z => (g z.1, z.2.2))) ≤ (marginalSnd W).capacity := by
  have h1 : J.map (fun z => (g z.1, z.2.2)) = (J.map (fun z => (z.1, z.2.2))).map (Prod.map g id) := by
    rw [map_comp_eq]; rfl
  rw [h1]
  refine (mi_map_left_le _ g).trans ?_
  rw [joint_map_snd_eq W P f J hJ, dmcPrecomp_mutualInfo_eq]
  exact dmc_mutualInfo_le_capacity _ _

/-- If the input `f(A)` is a function `h(g(A))` of the auxiliary on the support, then
    `I(X; Y₁) ≤ I(g(A); Y₁)`. -/
theorem mi_input_le_mi_fst (W : DMC X (Y₁ × Y₂)) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × (Y₁ × Y₂))) (hJ : ∀ z, J.pmf z = P.pmf z.1 * W.trans (f z.1) z.2)
    (g : A → B) (h : B → X) (hgh : ∀ a, P.pmf a ≠ 0 → h (g a) = f a) :
    (marginalFst W).mutualInfo (P.map f) ≤ mutualInfo (J.map (fun z => (g z.1, z.2.1))) := by
  refine le_trans (le_of_eq ?_) (mi_map_left_le _ h)
  have e1 : (J.map (fun z => (g z.1, z.2.1))).map (Prod.map h id) =
      (J.map (fun z => (z.1, z.2.1))).map (Prod.map f id) := by
    rw [map_comp_eq, map_comp_eq]
    refine map_congr_of_support J fun z hz => ?_
    have hP : P.pmf z.1 ≠ 0 := by
      intro h0; apply hz; rw [hJ, h0, zero_mul]
    simp [hgh z.1 hP]
  rw [e1, joint_map_fst_eq W P f J hJ, dmcPrecomp_joint_map]
  rfl

/-- Receiver-2 version of `mi_input_le_mi_fst`. -/
theorem mi_input_le_mi_snd (W : DMC X (Y₁ × Y₂)) (P : ProbDist A) (f : A → X)
    (J : ProbDist (A × (Y₁ × Y₂))) (hJ : ∀ z, J.pmf z = P.pmf z.1 * W.trans (f z.1) z.2)
    (g : A → B) (h : B → X) (hgh : ∀ a, P.pmf a ≠ 0 → h (g a) = f a) :
    (marginalSnd W).mutualInfo (P.map f) ≤ mutualInfo (J.map (fun z => (g z.1, z.2.2))) := by
  refine le_trans (le_of_eq ?_) (mi_map_left_le _ h)
  have e1 : (J.map (fun z => (g z.1, z.2.2))).map (Prod.map h id) =
      (J.map (fun z => (z.1, z.2.2))).map (Prod.map f id) := by
    rw [map_comp_eq, map_comp_eq]
    refine map_congr_of_support J fun z hz => ?_
    have hP : P.pmf z.1 ≠ 0 := by
      intro h0; apply hz; rw [hJ, h0, zero_mul]
    simp [hgh z.1 hP]
  rw [e1, joint_map_snd_eq W P f J hJ, dmcPrecomp_joint_map]
  rfl

/-- The support of a pushforward lies in the image. -/
theorem exists_of_map_pmf_ne_zero (P : ProbDist X) (φ : X → A) {a : A}
    (h : (P.map φ).pmf a ≠ 0) : ∃ x, φ x = a := by
  classical
  by_contra hne
  push Not at hne
  apply h
  simp only [ProbDist.map]
  exact Finset.sum_eq_zero fun x _ => by simp [hne x]

/-- Conditional mutual information vanishes when the middle variable is constant. -/
theorem condMutualInfo_eq_zero_of_subsingleton {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Subsingleton β] (P : ProbDist (α × β × γ)) : condMutualInfo P = 0 := by
  classical
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
  · exfalso
    have : ∑ t : α × β × γ, P.pmf t = 0 :=
      Finset.sum_eq_zero fun t _ => (IsEmpty.false t.2.1).elim
    linarith [P.sum_one]
  have hc1 : Function.Injective (fun c : γ => (b₀, c)) := fun x y h => (Prod.mk.inj h).2
  have hc2 : Function.Injective (fun ac : α × γ => (ac.1, b₀, ac.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2
  have h1 : P.map (fun t => (t.2.1, t.2.2)) = (P.map (fun t => t.2.2)).map (fun c => (b₀, c)) := by
    rw [map_comp_eq]
    congr 1
    funext t
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have h2 : shannonEntropy P =
      shannonEntropy ((P.map (fun t => (t.1, t.2.2))).map (fun ac => (ac.1, b₀, ac.2))) := by
    rw [map_comp_eq, ← shannonEntropy_map_equiv (Equiv.refl _) P]
    congr 2
    funext t
    exact Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) rfl)
  unfold condMutualInfo
  dsimp only
  rw [h1, h2, shannonEntropy_map_of_injective _ hc1, shannonEntropy_map_of_injective _ hc2]
  ring

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

/-- Conditioning on a constant: `I(B; Y | C) = I(B; Y)` when `C` is a.s. constant. -/
theorem condMutualInfo_map_subsingleton {γ : Type*} [Fintype γ] [Subsingleton γ]
    (J : ProbDist A) (u : A → B) (y : A → Z) (c : A → γ) :
    condMutualInfo (J.map (fun a => (u a, y a, c a))) = mutualInfo (J.map (fun a => (u a, y a))) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨c₀⟩⟩
  · exfalso
    obtain ⟨a, -⟩ : ∃ a : A, True := by
      by_contra h
      push Not at h
      have : ∑ a : A, J.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h a).elim
      linarith [J.sum_one]
    exact (IsEmpty.false (c a)).elim
  have : J.map (fun a => (u a, y a, c a)) =
      (J.map (fun a => (u a, y a))).map (fun ab => (ab.1, ab.2, c₀)) := by
    rw [map_comp_eq]
    congr 1
    funext a
    exact Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))
  rw [this, condMutualInfo_map_const]

end Toolkit

variable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]

/-! ### Outer bounds -/

/-- **Trivial outer bound** on the operational region (El Gamal–Kim §5.1). -/
theorem bcCapacityRegion_subset_box (W : BroadcastChannel X Y₁ Y₂) :
    bcCapacityRegion W ⊆
      Set.Icc 0 (marginalFst W).capacity ×ˢ Set.Icc 0 (marginalSnd W).capacity :=
  bcCapacityRegion_subset_Icc_prod_Icc W

/-- **Marton's region satisfies the trivial outer bound**: `R₁ ≤ I(W, U; Y₁) ≤ C₁` and
    `R₂ ≤ I(W, V; Y₂) ≤ C₂` by data processing. -/
theorem martonInnerBound_subset_box (W : BroadcastChannel X Y₁ Y₂) :
    martonInnerBound W ⊆
      Set.Icc 0 (marginalFst W).capacity ×ˢ Set.Icc 0 (marginalSnd W).capacity := by
  refine closure_minimal (fun p hp => ?_) (isClosed_Icc.prod isClosed_Icc)
  obtain ⟨hp1, hp2, kW, kU, kV, P, hc⟩ := hp
  obtain ⟨h1, h2, -, -⟩ := hc
  exact ⟨⟨hp1, h1.trans (mi_fst_le_capacity W P (fun a => a.2.2.2) _ (fun _ => rfl)
      (fun a => (a.1, a.2.1)))⟩,
    ⟨hp2, h2.trans (mi_snd_le_capacity W P (fun a => a.2.2.2) _ (fun _ => rfl)
      (fun a => (a.1, a.2.2.1)))⟩⟩

/-! ### Axes of Marton's region -/

/-- With `W, V` constant and `U = X`, every `(R₁, 0)` with `R₁ ≤ I(X; Y₁)` is in Marton's
    (pre-closure) region. -/
theorem marton_mem_axis₁ (W : BroadcastChannel X Y₁ Y₂) (Px : ProbDist X) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ (marginalFst W).mutualInfo Px) :
    (R, (0 : ℝ)) ∈ martonInnerBound W := by
  classical
  apply subset_closure
  let e := Fintype.equivFin X
  let φ : X → Fin 1 × Fin (Fintype.card X) × Fin 1 × X := fun x => (0, e x, 0, x)
  refine ⟨hR0, le_rfl, 1, Fintype.card X, 1, Px.map φ, ?_⟩
  intro joint IWU_Y1 IWV_Y2 IU_Y1_W IV_Y2_W IUV_W
  have hJ : ∀ z, joint.pmf z = (Px.map φ).pmf z.1 * W.trans ((fun a => a.2.2.2) z.1) z.2 :=
    fun _ => rfl
  have hPf : (Px.map φ).map (fun a => a.2.2.2) = Px := by
    rw [map_comp_eq]; exact map_id_eq Px
  have hsupp : ∀ a, (Px.map φ).pmf a ≠ 0 → e.symm a.2.1 = a.2.2.2 := by
    intro a ha
    obtain ⟨x, rfl⟩ := exists_of_map_pmf_ne_zero Px φ ha
    simp [φ]
  have hA : R ≤ IWU_Y1 := by
    refine hR.trans (le_of_eq_of_le ?_ (mi_input_le_mi_fst W _ _ joint hJ
      (fun a => (a.1, a.2.1)) (fun b => e.symm b.2) hsupp))
    rw [hPf]
  have hB : R ≤ IU_Y1_W := by
    have e1 : IU_Y1_W = mutualInfo (joint.map (fun z => (z.1.2.1, z.2.1))) :=
      condMutualInfo_map_subsingleton joint (fun z => z.1.2.1) (fun z => z.2.1) (fun z => z.1.1)
    rw [e1]
    refine hR.trans (le_of_eq_of_le ?_ (mi_input_le_mi_fst W _ _ joint hJ
      (fun a => a.2.1) (fun b => e.symm b) hsupp))
    rw [hPf]
  have hC : IUV_W = 0 := condMutualInfo_eq_zero_of_subsingleton _
  have n1 : 0 ≤ IWV_Y2 := mutualInfo_nonneg _
  have n2 : 0 ≤ IV_Y2_W := condMutualInfo_nonneg _
  refine ⟨hA, n1, ?_, ?_⟩ <;> simp only [hC] <;> linarith

/-- With `W, U` constant and `V = X`, every `(0, R₂)` with `R₂ ≤ I(X; Y₂)` is in Marton's
    region. -/
theorem marton_mem_axis₂ (W : BroadcastChannel X Y₁ Y₂) (Px : ProbDist X) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ (marginalSnd W).mutualInfo Px) :
    ((0 : ℝ), R) ∈ martonInnerBound W := by
  classical
  apply subset_closure
  let e := Fintype.equivFin X
  let φ : X → Fin 1 × Fin 1 × Fin (Fintype.card X) × X := fun x => (0, 0, e x, x)
  refine ⟨le_rfl, hR0, 1, 1, Fintype.card X, Px.map φ, ?_⟩
  intro joint IWU_Y1 IWV_Y2 IU_Y1_W IV_Y2_W IUV_W
  have hJ : ∀ z, joint.pmf z = (Px.map φ).pmf z.1 * W.trans ((fun a => a.2.2.2) z.1) z.2 :=
    fun _ => rfl
  have hPf : (Px.map φ).map (fun a => a.2.2.2) = Px := by
    rw [map_comp_eq]; exact map_id_eq Px
  have hsupp : ∀ a, (Px.map φ).pmf a ≠ 0 → e.symm a.2.2.1 = a.2.2.2 := by
    intro a ha
    obtain ⟨x, rfl⟩ := exists_of_map_pmf_ne_zero Px φ ha
    simp [φ]
  have hA : R ≤ IWV_Y2 := by
    refine hR.trans (le_of_eq_of_le ?_ (mi_input_le_mi_snd W _ _ joint hJ
      (fun a => (a.1, a.2.2.1)) (fun b => e.symm b.2) hsupp))
    rw [hPf]
  have hB : R ≤ IV_Y2_W := by
    have e1 : IV_Y2_W = mutualInfo (joint.map (fun z => (z.1.2.2.1, z.2.2))) :=
      condMutualInfo_map_subsingleton joint (fun z => z.1.2.2.1) (fun z => z.2.2) (fun z => z.1.1)
    rw [e1]
    refine hR.trans (le_of_eq_of_le ?_ (mi_input_le_mi_snd W _ _ joint hJ
      (fun a => a.2.2.1) (fun b => e.symm b) hsupp))
    rw [hPf]
  have hC : IUV_W = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have n1 : 0 ≤ IWU_Y1 := mutualInfo_nonneg _
  have n2 : 0 ≤ IU_Y1_W := condMutualInfo_nonneg _
  refine ⟨n1, hA, ?_, ?_⟩ <;> simp only [hC] <;> linarith

/-- **Marton's region on the first axis**: `(R₁, 0) ∈ R_Marton ↔ 0 ≤ R₁ ≤ C₁`. -/
theorem mk_zero_mem_martonInnerBound_iff [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) (R : ℝ) :
    (R, (0 : ℝ)) ∈ martonInnerBound W ↔ 0 ≤ R ∧ R ≤ (marginalFst W).capacity := by
  constructor
  · intro h
    exact (martonInnerBound_subset_box W h).1
  · rintro ⟨h0, h1⟩
    rcases eq_or_lt_of_le h1 with hC | hlt
    · -- `R = C₁`: approximate from below and use closedness
      have hsub : Set.Ico 0 (marginalFst W).capacity ×ˢ ({0} : Set ℝ) ⊆ martonInnerBound W := by
        rintro ⟨r, s⟩ ⟨⟨hr0, hr⟩, hs⟩
        rw [Set.mem_singleton_iff] at hs
        subst hs
        obtain ⟨_, ⟨Px, rfl⟩, hlt⟩ :=
          exists_lt_of_lt_csSup (capacity_set_nonempty (marginalFst W)) hr
        exact marton_mem_axis₁ W Px hr0 hlt.le
      rcases eq_or_lt_of_le (capacity_nonneg (marginalFst W)) with h00 | hpos
      · have hR : R = 0 := le_antisymm (h00 ▸ h1) h0
        subst hR
        exact marton_mem_axis₁ W ProbDist.uniform le_rfl (dmc_mutualInfo_nonneg _ _)
      · have hcl := closure_mono hsub
        have hcM : IsClosed (martonInnerBound W) := isClosed_closure
        rw [closure_prod_eq, closure_Ico hpos.ne, closure_singleton, hcM.closure_eq] at hcl
        exact hcl ⟨⟨h0, h1⟩, rfl⟩
    · obtain ⟨_, ⟨Px, rfl⟩, hlt'⟩ :=
        exists_lt_of_lt_csSup (capacity_set_nonempty (marginalFst W)) hlt
      exact marton_mem_axis₁ W Px h0 hlt'.le

/-- **Marton's region on the second axis**: `(0, R₂) ∈ R_Marton ↔ 0 ≤ R₂ ≤ C₂`. -/
theorem zero_mk_mem_martonInnerBound_iff [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) (R : ℝ) :
    ((0 : ℝ), R) ∈ martonInnerBound W ↔ 0 ≤ R ∧ R ≤ (marginalSnd W).capacity := by
  constructor
  · intro h
    exact (martonInnerBound_subset_box W h).2
  · rintro ⟨h0, h1⟩
    rcases eq_or_lt_of_le h1 with hC | hlt
    · have hsub : ({0} : Set ℝ) ×ˢ Set.Ico 0 (marginalSnd W).capacity ⊆ martonInnerBound W := by
        rintro ⟨s, r⟩ ⟨hs, ⟨hr0, hr⟩⟩
        rw [Set.mem_singleton_iff] at hs
        subst hs
        obtain ⟨_, ⟨Px, rfl⟩, hlt⟩ :=
          exists_lt_of_lt_csSup (capacity_set_nonempty (marginalSnd W)) hr
        exact marton_mem_axis₂ W Px hr0 hlt.le
      rcases eq_or_lt_of_le (capacity_nonneg (marginalSnd W)) with h00 | hpos
      · have hR : R = 0 := le_antisymm (h00 ▸ h1) h0
        subst hR
        exact marton_mem_axis₂ W ProbDist.uniform le_rfl (dmc_mutualInfo_nonneg _ _)
      · have hcl := closure_mono hsub
        have hcM : IsClosed (martonInnerBound W) := isClosed_closure
        rw [closure_prod_eq, closure_Ico hpos.ne, closure_singleton, hcM.closure_eq] at hcl
        exact hcl ⟨rfl, ⟨h0, h1⟩⟩
    · obtain ⟨_, ⟨Px, rfl⟩, hlt'⟩ :=
        exists_lt_of_lt_csSup (capacity_set_nonempty (marginalSnd W)) hlt
      exact marton_mem_axis₂ W Px h0 hlt'.le

/-- **The two sides of the statement agree on the first axis.** -/
theorem mk_zero_mem_iff [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) (R : ℝ) :
    (R, (0 : ℝ)) ∈ bcCapacityRegion W ↔ (R, (0 : ℝ)) ∈ martonInnerBound W := by
  rw [mk_zero_mem_bcCapacityRegion_iff, mk_zero_mem_martonInnerBound_iff]

/-- **The two sides of the statement agree on the second axis.** -/
theorem zero_mk_mem_iff [Nonempty X] (W : BroadcastChannel X Y₁ Y₂) (R : ℝ) :
    ((0 : ℝ), R) ∈ bcCapacityRegion W ↔ ((0 : ℝ), R) ∈ martonInnerBound W := by
  rw [zero_mk_mem_bcCapacityRegion_iff, zero_mk_mem_martonInnerBound_iff]

end InfoTheory.Known.Certificates.BroadcastChannel
