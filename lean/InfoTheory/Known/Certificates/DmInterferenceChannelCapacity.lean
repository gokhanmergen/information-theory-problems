import InfoTheory.Problems.DmInterferenceChannelCapacity
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.DmInterferenceChannelCapacity`

The frozen statement asks whether, for every finite two-user DM interference channel `W`,
some `k ≥ 1` satisfies `icCapacityRegion W = hanKobayashiKLetterRegion k W`.

## Certified (about exactly these objects)
* `icCapacityRegion_subset_bcCapacityRegion` — an interference-channel code is a broadcast
  code for `W` viewed as a BC with input `(X₁, X₂)` (encoder `(m₁, m₂) ↦ (enc₁ m₁, enc₂ m₂)`).
* `icCapacityRegion_subset_box` — hence the outer bound
  `C_IC(W) ⊆ [0, C(X₁X₂ → Y₁)] × [0, C(X₁X₂ → Y₂)]` (reusing
  `Known.Operational.bcCapacityRegion_subset_Icc_prod_Icc`). In particular the operational
  region is bounded.
* `Icc_prod_zero_subset_icCapacityRegion`, `zero_prod_Icc_subset_icCapacityRegion` — **axis
  achievability**: if transmitter 2 sends a fixed symbol `x₂`, every rate up to the capacity
  of `x₁ ↦ p(y₁ | x₁, x₂)` is achievable for user 1 (and symmetrically), by Shannon's theorem.
  So `C_IC(W)` contains `(0, 0)` and nontrivial axis segments.
* `zero_mem_hanKobayashiKLetterRegion` — the `k`-letter Han–Kobayashi region contains `(0, 0)`.
* `hanKobayashiKLetterRegion_subset_box` — for `k ≥ 1` it lies in
  `[0, log₂ |Y₁|] × [0, log₂ |Y₂|]` (`I(X₁ᵏ; Y₁ᵏ | U₂, Q) ≤ log₂ |Y₁|ᵏ`). So both sides of the
  statement are nonempty bounded sets for every `k ≥ 1`; neither is junk.

## Not certified
* Achievability of the Han–Kobayashi region (`hanKobayashiKLetterRegion k W ⊆ icCapacityRegion W`):
  it needs rate splitting with superposition coding and simultaneous decoding, which is not in
  the library.
* The sharper axis outer bound `R₁ ≤ max_{x₂} C(p(y₁ | x₁, x₂))`: it needs a converse for a
  time-varying channel (transmitter 2's codeword varies with the time index).
* Any statement-level conclusion: the problem is open (single-letter HK is strictly
  suboptimal, Nair–Xia–Yazdanpanah 2015, which is why the statement uses the `k`-letter
  hierarchy).

Sources: Han–Kobayashi, IEEE Trans. IT 1981; Chong–Motani–Garg–El Gamal 2008;
El Gamal–Kim, *Network Information Theory*, Ch. 6.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.DmInterferenceChannelCapacity

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.DmInterferenceChannelCapacity

section Toolkit

/-- `I(A; B | C) ≤ log₂ |B|`. -/
theorem condMutualInfo_le_log2_card {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Nonempty β] (P : ProbDist (α × β × γ)) : condMutualInfo P ≤ log2 (Fintype.card β) := by
  unfold condMutualInfo
  dsimp only
  have h1 : shannonEntropy (P.map (fun t => (t.1, t.2.2))) ≤ shannonEntropy P :=
    shannonEntropy_map_le _ P
  have h2 := shannonEntropy_subadd (P.map (fun t => (t.2.1, t.2.2)))
  rw [← map_fst_eq_fst, ← map_snd_eq_snd, map_comp_eq, map_comp_eq] at h2
  simp only [Function.comp_def] at h2
  have h3 := shannonEntropy_le_log2_card (P.map (fun t => t.2.1))
  linarith

lemma log2_card_pow (α : Type*) [Fintype α] (k : ℕ) :
    log2 (Fintype.card (Fin k → α) : ℝ) = k * log2 (Fintype.card α) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  unfold log2
  push_cast
  rw [Real.log_pow]
  ring

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

end Toolkit

variable {X₁ X₂ Y₁ Y₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]

/-! ### Outer bound on the operational region -/

/-- An interference-channel code is a broadcast code for `W` with input alphabet `X₁ × X₂`. -/
theorem icCapacityRegion_subset_bcCapacityRegion (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    icCapacityRegion W ⊆ bcCapacityRegion W := by
  refine closure_mono fun p hp => ?_
  obtain ⟨h1, h2, h⟩ := hp
  refine ⟨h1, h2, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, dec₂, herr⟩ := hN n hn
  exact ⟨fun m₁ m₂ i => (enc₁ m₁ i, enc₂ m₂ i), dec₁, dec₂, herr⟩

/-- **Outer bound**: `C_IC(W) ⊆ [0, C(X₁X₂ → Y₁)] × [0, C(X₁X₂ → Y₂)]`. -/
theorem icCapacityRegion_subset_box (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    icCapacityRegion W ⊆
      Set.Icc 0 (marginalFst W).capacity ×ˢ Set.Icc 0 (marginalSnd W).capacity :=
  (icCapacityRegion_subset_bcCapacityRegion W).trans (bcCapacityRegion_subset_Icc_prod_Icc W)

/-! ### Axis achievability -/

/-- User 1's channel when transmitter 2 always sends `x₂`. -/
def ch₁ (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₂ : X₂) : DMC X₁ Y₁ :=
  marginalFst (dmcPrecomp W (fun x₁ => (x₁, x₂)))

/-- User 2's channel when transmitter 1 always sends `x₁`. -/
def ch₂ (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) : DMC X₂ Y₂ :=
  marginalSnd (dmcPrecomp W (fun x₂ => (x₁, x₂)))

theorem mk_zero_mem_icCapacityRegion_of (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₂ : X₂)
    {R : ℝ} (h : IsDmcAchievableRate (ch₁ W x₂) R) : (R, (0 : ℝ)) ∈ icCapacityRegion W := by
  classical
  refine subset_closure ⟨h.1, le_rfl, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero]
  exact ⟨enc, fun _ _ => x₂, dec, fun _ => 0,
    le_of_eq_of_le (bc_err_single_msg₂ (dmcPrecomp W (fun x₁ => (x₁, x₂)))
      (fun m _ => enc m) dec (fun _ => 0)) herr⟩

theorem zero_mk_mem_icCapacityRegion_of (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁)
    {R : ℝ} (h : IsDmcAchievableRate (ch₂ W x₁) R) : ((0 : ℝ), R) ∈ icCapacityRegion W := by
  classical
  refine subset_closure ⟨le_rfl, h.1, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h.2 ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  dsimp only
  rw [natMax_zero]
  exact ⟨fun _ _ => x₁, enc, fun _ => 0, dec,
    le_of_eq_of_le (bc_err_single_msg₁ (dmcPrecomp W (fun x₂ => (x₁, x₂)))
      (fun _ m => enc m) (fun _ => 0) dec) herr⟩

/-- **Axis achievability, user 1** (El Gamal–Kim §6.1): `[0, C(p(y₁|x₁,x₂))] × {0} ⊆ C_IC(W)`
    for every fixed `x₂`. -/
theorem Icc_prod_zero_subset_icCapacityRegion [Nonempty X₁]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₂ : X₂) :
    Set.Icc 0 (ch₁ W x₂).capacity ×ˢ {0} ⊆ icCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_minimal (fun p hp => ?_) isClosed_closure
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp2
  have : p = (p.1, 0) := Prod.ext rfl hp2
  rw [this]
  exact mk_zero_mem_icCapacityRegion_of W x₂ hp1

/-- **Axis achievability, user 2**. -/
theorem zero_prod_Icc_subset_icCapacityRegion [Nonempty X₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) (x₁ : X₁) :
    {0} ×ˢ Set.Icc 0 (ch₂ W x₁).capacity ⊆ icCapacityRegion W := by
  rw [← closure_dmcAchievable_eq_Icc, ← closure_singleton, ← closure_prod_eq]
  refine closure_minimal (fun p hp => ?_) isClosed_closure
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp1
  have : p = (0, p.2) := Prod.ext hp1 rfl
  rw [this]
  exact zero_mk_mem_icCapacityRegion_of W x₁ hp2

theorem zero_mem_icCapacityRegion [Nonempty X₁] [Nonempty X₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : ((0 : ℝ), (0 : ℝ)) ∈ icCapacityRegion W :=
  mk_zero_mem_icCapacityRegion_of W (Classical.arbitrary X₂) (isDmcAchievableRate_zero _)

/-! ### The `k`-letter Han–Kobayashi region -/

theorem zero_mem_hanKobayashiKLetterRegion [Nonempty X₁] [Nonempty X₂] (k : ℕ)
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    ((0 : ℝ), (0 : ℝ)) ∈ hanKobayashiKLetterRegion k W := by
  refine subset_closure ?_
  show (((k : ℝ) * 0, (k : ℝ) * 0) : ℝ × ℝ) ∈ hanKobayashiRegion (icPower W k)
  rw [mul_zero]
  refine ⟨le_rfl, le_rfl, 1, 1, 1, ProbDist.uniform, fun _ => ProbDist.uniform,
    fun _ => ProbDist.uniform, ?_⟩
  intro J a1 a2 b1 b2 c1 c2 d1 d2
  have n1 : 0 ≤ a1 := condMutualInfo_nonneg _
  have n2 : 0 ≤ a2 := condMutualInfo_nonneg _
  have n3 : 0 ≤ b1 := condMutualInfo_nonneg _
  have n4 : 0 ≤ b2 := condMutualInfo_nonneg _
  have n5 : 0 ≤ c1 := condMutualInfo_nonneg _
  have n6 : 0 ≤ c2 := condMutualInfo_nonneg _
  have n7 : 0 ≤ d1 := condMutualInfo_nonneg _
  have n8 : 0 ≤ d2 := condMutualInfo_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> linarith

/-- **Boundedness of the `k`-letter HK region**: for `k ≥ 1`,
    `R_HK^{(k)}(W) ⊆ [0, log₂ |Y₁|] × [0, log₂ |Y₂|]`. -/
theorem hanKobayashiKLetterRegion_subset_box [Nonempty Y₁] [Nonempty Y₂] {k : ℕ} (hk : 0 < k)
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) :
    hanKobayashiKLetterRegion k W ⊆
      Set.Icc 0 (log2 (Fintype.card Y₁)) ×ˢ Set.Icc 0 (log2 (Fintype.card Y₂)) := by
  refine closure_minimal (fun r hr => ?_) (isClosed_Icc.prod isClosed_Icc)
  obtain ⟨h1, h2, kQ, kU₁, kU₂, Pq, P₁, P₂, hc⟩ := hr
  obtain ⟨ha1, ha2, -⟩ := hc
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have b1 := ha1.trans (condMutualInfo_le_log2_card _)
  have b2 := ha2.trans (condMutualInfo_le_log2_card _)
  dsimp only at b1 b2 h1 h2
  rw [log2_card_pow] at b1 b2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact nonneg_of_mul_nonneg_right (by linarith) hkr
  · exact le_of_mul_le_mul_left b1 hkr
  · exact nonneg_of_mul_nonneg_right (by linarith) hkr
  · exact le_of_mul_le_mul_left b2 hkr

end InfoTheory.Known.Certificates.DmInterferenceChannelCapacity
