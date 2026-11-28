import InfoTheory.Problems.CognitiveInterferenceChannel
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.BroadcastChannel
import InfoTheory.Known.Certificates.DmInterferenceChannelCapacity

/-!
# Certificate for `InfoTheory.Problems.CognitiveInterferenceChannel`

The frozen statement asks whether, for every finite DM cognitive interference channel `W`
(transmitter 2 knows both messages), the operational region `cognitiveICCapacityRegion W`
equals the Rini–Tuninetti–Devroye inner bound `rtdInnerBound W`.

## Certified (about exactly these objects)
* `cognitiveICCapacityRegion_subset_bcCapacityRegion` — a cognitive-IC code is a broadcast
  code for `W` with input `(X₁, X₂)` (encoder `(m₁, m₂) ↦ (enc₁ m₁, enc₂ m₁ m₂)`), hence
  `cognitiveICCapacityRegion_subset_box`:
  `C_cog(W) ⊆ [0, C(X₁X₂ → Y₁)] × [0, C(X₁X₂ → Y₂)]`.
* `mk_zero_mem_cognitiveICCapacityRegion_iff` — **the primary axis is solved exactly**:
  `(R₁, 0) ∈ C_cog(W) ↔ 0 ≤ R₁ ≤ C(X₁X₂ → Y₁)`. With `R₂ = 0` both transmitters know `M₁`
  and act as one encoder for the channel `(X₁, X₂) → Y₁` (Shannon's theorem).
* `zero_prod_Icc_subset_cognitiveICCapacityRegion` — cognitive-axis achievability:
  `{0} × [0, C(p(y₂ | x₁, x₂))] ⊆ C_cog(W)` for every fixed `x₁`.
* `zero_mem_rtdInnerBound` — `(0, 0)` lies in the RTD region (all auxiliaries constant, so all
  binning / covering penalties vanish).
* `rtdInnerBound_subset_box` — `rtdInnerBound W ⊆ [0, log₂ |Y₁|] × [0, log₂ |Y₂|]` (the
  receiver-1 sum constraint and the penalty constraint `R'₁ₚ + R'₂c ≥ I(X₁, U₁ₚ; U₂c | U₀, Q)`
  combine to `R₁ ≤ I(·; Y₁ | Q)`). So both sides of the statement are nonempty bounded sets.

* **Regression** `mk_zero_mem_rtdInnerBound_of`, `Icc_prod_zero_subset_rtdInnerBound` — with
  `U₁ₚ = (X₁, X₂)` and the other auxiliaries constant, every RTD penalty vanishes and the
  receiver-1 constraints reduce to `R₁ ≤ I(X₁X₂;Y₁|Q)`; so the frozen RTD region contains the
  whole known primary axis `[0, C(X₁X₂ → Y₁)] × {0}` (= the operational axis above).

## Not certified
* Achievability of the RTD region (superposition, binning and Gelfand–Pinsker coding are not in
  the library) and the known capacity results for special classes (strong interference,
  "better cognitive decoding", Wu–Vishwanath–Arapostathis): these need converses with
  Csiszár-sum-identity arguments.
* The sharper box `R₁ ≤ C(X₁X₂ → Y₁)` *on the RTD side* (the bound proved there is via
  `log₂ |Y₁|`, which needs only the Shannon inequalities).
* No statement-level conclusion: the problem is open. The statement reduces to the broadcast
  channel at `|X₁| = 1`, so if the Huang–Liu–Liu claim (arXiv:2608.19869, unverified) that
  Marton's bound is suboptimal holds, the frozen `Statement` is false.

Sources: Devroye–Mitran–Tarokh, IEEE Trans. IT 2006; Rini–Tuninetti–Devroye, IEEE Trans. IT
2011/2012; El Gamal–Kim, *Network Information Theory*, §6.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CognitiveInterferenceChannel

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.CognitiveInterferenceChannel
open InfoTheory.Known.Certificates.BroadcastChannel (condMutualInfo_eq_zero_of_subsingleton
  condMutualInfo_eq_zero_of_subsingleton_fst)
open InfoTheory.Known.Certificates.DmInterferenceChannelCapacity (ch₂ condMutualInfo_le_log2_card)

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

/-! ### Outer bound -/

theorem cognitiveICCapacityRegion_subset_bcCapacityRegion (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    cognitiveICCapacityRegion W ⊆ bcCapacityRegion W := by
  refine closure_mono fun p hp => ?_
  obtain ⟨h1, h2, h⟩ := hp
  refine ⟨h1, h2, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, dec₂, herr⟩ := hN n hn
  exact ⟨fun m₁ m₂ i => (enc₁ m₁ i, enc₂ m₁ m₂ i), dec₁, dec₂, herr⟩

/-- **Outer bound**: `C_cog(W) ⊆ [0, C(X₁X₂ → Y₁)] × [0, C(X₁X₂ → Y₂)]`. -/
theorem cognitiveICCapacityRegion_subset_box (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    cognitiveICCapacityRegion W ⊆
      Set.Icc 0 (marginalFst W).capacity ×ˢ Set.Icc 0 (marginalSnd W).capacity :=
  (cognitiveICCapacityRegion_subset_bcCapacityRegion W).trans
    (bcCapacityRegion_subset_Icc_prod_Icc W)

/-! ### Axes -/

/-- With `R₂ = 0`, a point-to-point code for `(X₁, X₂) → Y₁` is a cognitive-IC code. -/
theorem mk_zero_mem_of (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {R : ℝ}
    (h : IsDmcAchievableRate (marginalFst W) R) : (R, (0 : ℝ)) ∈ cognitiveICCapacityRegion W := by
  classical
  refine subset_closure ⟨h.1, le_rfl, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero]
  exact ⟨fun m i => (enc m i).1, fun m _ i => (enc m i).2, dec, fun _ => 0,
    le_of_eq_of_le (bc_err_single_msg₂ W (fun m _ => enc m) dec (fun _ => 0)) herr⟩

/-- With `R₁ = 0` and transmitter 1 sending `x₁`, a code for `p(y₂ | x₁, x₂)` is a
    cognitive-IC code. -/
theorem zero_mk_mem_of (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) {R : ℝ}
    (h : IsDmcAchievableRate (ch₂ W x₁) R) : ((0 : ℝ), R) ∈ cognitiveICCapacityRegion W := by
  classical
  refine subset_closure ⟨le_rfl, h.1, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero]
  exact ⟨fun _ _ => x₁, fun _ m => enc m, fun _ => 0, dec,
    le_of_eq_of_le (bc_err_single_msg₁ (dmcPrecomp W (fun x₂ => (x₁, x₂)))
      (fun _ m => enc m) (fun _ => 0) dec) herr⟩

/-- **The primary axis is exactly `[0, C(X₁X₂ → Y₁)]`.** -/
theorem mk_zero_mem_cognitiveICCapacityRegion_iff [Nonempty X₁] [Nonempty X₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (R : ℝ) :
    (R, (0 : ℝ)) ∈ cognitiveICCapacityRegion W ↔ 0 ≤ R ∧ R ≤ (marginalFst W).capacity := by
  constructor
  · intro h
    exact (cognitiveICCapacityRegion_subset_box W h).1
  · intro h
    have hsub : Set.Icc 0 (marginalFst W).capacity ×ˢ ({0} : Set ℝ) ⊆
        cognitiveICCapacityRegion W := by
      rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
      refine closure_minimal (fun p hp => ?_) isClosed_closure
      obtain ⟨hp1, hp2⟩ := hp
      rw [Set.mem_singleton_iff] at hp2
      have : p = (p.1, 0) := Prod.ext rfl hp2
      rw [this]
      exact mk_zero_mem_of W hp1
    exact hsub ⟨h, rfl⟩

/-- **Cognitive-axis achievability**: `{0} × [0, C(p(y₂ | x₁, x₂))] ⊆ C_cog(W)`. -/
theorem zero_prod_Icc_subset_cognitiveICCapacityRegion [Nonempty X₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) :
    {0} ×ˢ Set.Icc 0 (ch₂ W x₁).capacity ⊆ cognitiveICCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_minimal (fun p hp => ?_) isClosed_closure
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp1
  have : p = (0, p.2) := Prod.ext hp1 rfl
  rw [this]
  exact zero_mk_mem_of W x₁ hp2

/-! ### The RTD inner bound -/

theorem zero_mem_rtdInnerBound [Nonempty X₁] [Nonempty X₂] (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    ((0 : ℝ), (0 : ℝ)) ∈ rtdInnerBound W := by
  refine subset_closure ⟨le_rfl, le_rfl, 1, 1, 1, 1, 1, ProbDist.uniform,
    fun _ => ProbDist.uniform, 0, 0, 0, 0, 0, 0, 0, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl, by norm_num, by norm_num, ?_⟩
  intro J bin2c bin2p bin12p bin2cp bin12cp pen1
  have z1 : bin2c = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z2 : bin2p = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z3 : bin12p = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z4 : bin2cp = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z5 : bin12cp = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z6 : pen1 = 0 := condMutualInfo_eq_zero_of_subsingleton _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [z1, z2, z3, z4, z5, z6, ge_iff_le, le_refl, add_zero] <;>
    exact condMutualInfo_nonneg _

private lemma le_add_bound {a I p L : ℝ} (h : a ≤ I + p) (hI : I ≤ L) : a ≤ L + p := by
  linarith

/-- **Boundedness of the RTD region**: `rtdInnerBound W ⊆ [0, log₂ |Y₁|] × [0, log₂ |Y₂|]`. -/
theorem rtdInnerBound_subset_box [Nonempty Y₁] [Nonempty Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    rtdInnerBound W ⊆
      Set.Icc 0 (log2 (Fintype.card Y₁)) ×ˢ Set.Icc 0 (log2 (Fintype.card Y₂)) := by
  refine closure_minimal (fun r hr => ?_) (isClosed_Icc.prod isClosed_Icc)
  obtain ⟨h1, h2, kQ, k₀, k₁p, k₂c, k₂p, Pq, P, r₁c, r₁p, r₂c, r₂p, rp₁p, rp₂c, rp₂p,
    n1, n2, n3, n4, n5, n6, n7, e1, e2, hc⟩ := hr
  obtain ⟨-, -, c3, -, -, -, -, c8, -, c10, -⟩ := hc
  have b8 := le_add_bound c8 (condMutualInfo_le_log2_card _)
  have b10 := c10.trans (condMutualInfo_le_log2_card _)
  refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
  · rw [e1]; linarith
  · rw [e2]; linarith

/-! ### Regression: the primary axis of the RTD formula

With `R₂ = 0` both transmitters know `M₁`, and the known answer is `R₁ ≤ max I(X₁, X₂; Y₁)`
(`mk_zero_mem_cognitiveICCapacityRegion_iff`). Carrying `M₁` in the private auxiliary
`U₁ₚ := (X₁, X₂)` with all other auxiliaries constant, every binning / covering penalty of the
RTD region vanishes and its three receiver-1 constraints reduce to `R₁ ≤ I(X₁, X₂; Y₁ | Q)`. -/

section Regression

open InfoTheory.Known.Certificates.DmInterferenceChannelCapacity (cmi_relabel)

private theorem pmf_map_inj {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist α) (f : α → β)
    (hf : Function.Injective f) (a : α) : (P.map f).pmf (f a) = P.pmf a := by
  classical
  simp only [ProbDist.map]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne
    simp [hf.ne hne]
  · simp

/-- If the RTD input law is `P(a | q)` pushed along an injective `emb` that remembers the
    channel input, the RTD joint law is the pushforward of the plain joint law
    `p(q) p(x₁, x₂ | q) W(y | x₁, x₂)`. -/
theorem rtd_joint_eq_map (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ k₀ k₁p k₂c k₂p : ℕ}
    (Pq : ProbDist (Fin kQ)) (Pxx : Fin kQ → ProbDist (X₁ × X₂))
    (emb : X₁ × X₂ → Fin k₀ × Fin k₁p × Fin k₂c × Fin k₂p × X₁ × X₂)
    (hemb : Function.Injective emb) (hg : ∀ a, ((emb a).2.2.2.2.1, (emb a).2.2.2.2.2) = a)
    (J : ProbDist (Fin kQ × (Fin k₀ × Fin k₁p × Fin k₂c × Fin k₂p × X₁ × X₂) × (Y₁ × Y₂)))
    (hJ : ∀ z, J.pmf z = Pq.pmf z.1 * ((Pxx z.1).map emb).pmf z.2.1 *
      W.trans (z.2.1.2.2.2.2.1, z.2.1.2.2.2.2.2) z.2.2)
    (K : ProbDist (Fin kQ × (X₁ × X₂) × (Y₁ × Y₂)))
    (hK : ∀ z, K.pmf z = Pq.pmf z.1 * (Pxx z.1).pmf z.2.1 * W.trans z.2.1 z.2.2) :
    J = K.map (fun z => (z.1, emb z.2.1, z.2.2)) := by
  classical
  refine probDist_eq_of_pmf fun ⟨q, b, y⟩ => ?_
  by_cases hb : ∃ a, emb a = b
  · obtain ⟨a, rfl⟩ := hb
    have hinj : Function.Injective
        (fun z : Fin kQ × (X₁ × X₂) × (Y₁ × Y₂) => (z.1, emb z.2.1, z.2.2)) := by
      intro z z' h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext (hemb h.2.1) h.2.2)
    have hr : (K.map (fun z => (z.1, emb z.2.1, z.2.2))).pmf (q, emb a, y) = K.pmf (q, a, y) :=
      pmf_map_inj K _ hinj (q, a, y)
    rw [hr, hJ, hK]
    dsimp only
    rw [pmf_map_inj _ _ hemb, hg]
  · have h0 : ((Pxx q).map emb).pmf b = 0 := by
      simp only [ProbDist.map]
      exact Finset.sum_eq_zero fun a _ => by rw [if_neg (fun h => hb ⟨a, h⟩)]
    rw [hJ]
    dsimp only
    rw [h0, mul_zero, zero_mul]
    simp only [ProbDist.map]
    refine (Finset.sum_eq_zero fun z _ => ?_).symm
    rw [if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hb ⟨z.2.1, h.2.1⟩

/-- **Regression (primary axis)**: for every time-shared joint input law
    `p(q) p(x₁, x₂ | q)`, the frozen RTD region contains `[0, I(X₁, X₂; Y₁ | Q)] × {0}`. -/
theorem mk_zero_mem_rtdInnerBound_of (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ : ℕ}
    (Pq : ProbDist (Fin kQ)) (Pxx : Fin kQ → ProbDist (X₁ × X₂))
    (K : ProbDist (Fin kQ × (X₁ × X₂) × (Y₁ × Y₂)))
    (hK : ∀ z, K.pmf z = Pq.pmf z.1 * (Pxx z.1).pmf z.2.1 * W.trans z.2.1 z.2.2)
    {R : ℝ} (h0 : 0 ≤ R) (hR : R ≤ condMutualInfo (K.map (fun z => (z.2.1, z.2.2.1, z.1)))) :
    (R, (0 : ℝ)) ∈ rtdInnerBound W := by
  let e := Fintype.equivFin (X₁ × X₂)
  let emb : X₁ × X₂ → Fin 1 × Fin (Fintype.card (X₁ × X₂)) × Fin 1 × Fin 1 × X₁ × X₂ :=
    fun a => (0, e a, 0, 0, a.1, a.2)
  have hemb : Function.Injective emb := fun a b h => by
    simp only [emb, Prod.mk.injEq] at h
    exact e.injective h.2.1
  refine subset_closure ⟨h0, le_rfl, kQ, 1, Fintype.card (X₁ × X₂), 1, 1, Pq,
    fun q => (Pxx q).map emb, 0, R, 0, 0, 0, 0, 0, le_rfl, h0, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl, by ring, by ring, ?_⟩
  intro J bin2c bin2p bin12p bin2cp bin12cp pen1
  have hJ : J = K.map (fun z => (z.1, emb z.2.1, z.2.2)) :=
    rtd_joint_eq_map W Pq Pxx emb hemb (fun _ => rfl) J (fun _ => rfl) K hK
  have z1 : bin2c = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z2 : bin2p = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z3 : bin12p = 0 := condMutualInfo_eq_zero_of_subsingleton _
  have z4 : bin2cp = 0 := condMutualInfo_eq_zero_of_subsingleton_fst _
  have z5 : bin12cp = 0 := condMutualInfo_eq_zero_of_subsingleton _
  have z6 : pen1 = 0 := condMutualInfo_eq_zero_of_subsingleton _
  have c6 : condMutualInfo (J.map (fun z =>
      ((z.2.1.2.2.2.2.1, z.2.1.2.1), z.2.2.1, (z.2.1.1, z.2.1.2.2.1, z.1)))) =
      condMutualInfo (K.map (fun z => (z.2.1, z.2.2.1, z.1))) := by
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun z => z.2.1) (fun z => z.2.2.1) (fun z => z.1)
      (fun a => (a.1, e a)) (fun q => ((0 : Fin 1), (0 : Fin 1), q))
      (fun a b h => e.injective (Prod.mk.inj h).2)
      (fun a b h => (Prod.mk.inj (Prod.mk.inj h).2).2)
  have c7 : condMutualInfo (J.map (fun z =>
      ((z.2.1.2.2.2.2.1, z.2.1.2.1, z.2.1.2.2.1), z.2.2.1, (z.2.1.1, z.1)))) =
      condMutualInfo (K.map (fun z => (z.2.1, z.2.2.1, z.1))) := by
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun z => z.2.1) (fun z => z.2.2.1) (fun z => z.1)
      (fun a => (a.1, e a, (0 : Fin 1))) (fun q => ((0 : Fin 1), q))
      (fun a b h => e.injective (Prod.mk.inj (Prod.mk.inj h).2).1)
      (fun a b h => (Prod.mk.inj h).2)
  have c8 : condMutualInfo (J.map (fun z =>
      ((z.2.1.1, z.2.1.2.2.2.2.1, z.2.1.2.1, z.2.1.2.2.1), z.2.2.1, z.1))) =
      condMutualInfo (K.map (fun z => (z.2.1, z.2.2.1, z.1))) := by
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun z => z.2.1) (fun z => z.2.2.1) (fun z => z.1)
      (fun a => ((0 : Fin 1), a.1, e a, (0 : Fin 1))) id
      (fun a b h => e.injective (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1)
      Function.injective_id
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [c6]; linarith
  · rw [c7]; linarith
  · rw [c8]; linarith
  · simp only [add_zero]; exact condMutualInfo_nonneg _
  · simp only [add_zero]; exact condMutualInfo_nonneg _
  · simp only [add_zero]; exact condMutualInfo_nonneg _

/-- **Regression (primary axis, exact)**: the frozen RTD region contains the whole known
    primary axis `[0, C(X₁X₂ → Y₁)] × {0}`, which is exactly the operational axis
    (`mk_zero_mem_cognitiveICCapacityRegion_iff`). So on the `R₂ = 0` axis the frozen formula
    is not too small. -/
theorem Icc_prod_zero_subset_rtdInnerBound [Nonempty X₁] [Nonempty X₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    Set.Icc 0 (marginalFst W).capacity ×ˢ ({0} : Set ℝ) ⊆ rtdInnerBound W := by
  classical
  set T : Set ℝ := {R | (R, (0 : ℝ)) ∈ rtdInnerBound W} with hT
  have hTc : IsClosed T :=
    isClosed_closure.preimage (continuous_id.prodMk continuous_const)
  have hIco : Set.Ico 0 (marginalFst W).capacity ⊆ T := by
    rintro R ⟨h0, hR⟩
    unfold DMC.capacity at hR
    have hne : Set.Nonempty {r : ℝ | ∃ P : ProbDist (X₁ × X₂), r = (marginalFst W).mutualInfo P} :=
      ⟨_, ⟨ProbDist.uniform, rfl⟩⟩
    obtain ⟨r, ⟨P, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hR
    let K : ProbDist (Fin 1 × (X₁ × X₂) × (Y₁ × Y₂)) := (W.joint P).map (fun z => ((0 : Fin 1), z))
    have hinj : Function.Injective (fun z : (X₁ × X₂) × (Y₁ × Y₂) => ((0 : Fin 1), z)) :=
      fun a b h => (Prod.mk.inj h).2
    have hK : ∀ z, K.pmf z = (ProbDist.uniform : ProbDist (Fin 1)).pmf z.1 *
        ((fun _ => P) z.1).pmf z.2.1 * W.trans z.2.1 z.2.2 := by
      rintro ⟨q, a, y⟩
      have hq : q = 0 := Subsingleton.elim _ _
      subst hq
      rw [show (K.pmf ((0 : Fin 1), a, y)) = (W.joint P).pmf (a, y) from pmf_map_inj _ _ hinj (a, y)]
      simp [DMC.joint, ProbDist.uniform]
    have hI : condMutualInfo (K.map (fun z => (z.2.1, z.2.2.1, z.1))) =
        (marginalFst W).mutualInfo P := by
      have h1 : K.map (fun z => (z.2.1, z.2.2.1, z.1)) =
          ((W.joint P).map (fun z => (z.1, z.2.1))).map (fun ab => (ab.1, ab.2, (0 : Fin 1))) := by
        rw [map_comp_eq, map_comp_eq]; rfl
      rw [h1, condMutualInfo_map_const,
        InfoTheory.Known.Certificates.BroadcastChannel.joint_map_fst_eq W P id (W.joint P)
          (fun _ => rfl)]
      rfl
    exact mk_zero_mem_rtdInnerBound_of W ProbDist.uniform (fun _ => P) K hK h0
      (hI ▸ hlt.le)
  rintro ⟨R, z⟩ ⟨hR, hz⟩
  rw [Set.mem_singleton_iff] at hz
  subst hz
  show R ∈ T
  rcases eq_or_lt_of_le (hR.1.trans hR.2) with hC | hC
  · have hR0 : R = 0 := le_antisymm (hC ▸ hR.2) hR.1
    subst hR0
    exact zero_mem_rtdInnerBound W
  · rw [← closure_Ico hC.ne] at hR
    exact closure_minimal hIco hTc hR

end Regression

end InfoTheory.Known.Certificates.CognitiveInterferenceChannel
