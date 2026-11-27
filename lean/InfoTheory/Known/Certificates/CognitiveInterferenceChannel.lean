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

## Not certified
* Achievability of the RTD region (superposition, binning and Gelfand–Pinsker coding are not in
  the library) and the known capacity results for special classes (strong interference,
  "better cognitive decoding", Wu–Vishwanath–Arapostathis): these need converses with
  Csiszár-sum-identity arguments.
* The sharper box `R₁ ≤ C(X₁X₂ → Y₁)` *on the RTD side* (the bound proved there is via
  `log₂ |Y₁|`, which needs only the Shannon inequalities).
* No statement-level conclusion: the problem is open.

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

end InfoTheory.Known.Certificates.CognitiveInterferenceChannel
