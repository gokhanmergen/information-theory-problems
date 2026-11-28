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

* **Regression** `costaElGamalRegion_subset_hanKobayashiRegion` — under strong interference
  (`I(X₁;Y₁|X₂,Q) ≤ I(X₁;Y₂|X₂,Q)` and symmetrically, `IsStrongInterferenceAt`) the frozen
  single-letter HK formula (the building block of every level `k`, applied to `icPower W k`)
  contains the Costa–El Gamal / Sato strong-interference capacity region
  `R₁ ≤ I(X₁;Y₁|X₂,Q)`, `R₂ ≤ I(X₂;Y₂|X₁,Q)`, `R₁+R₂ ≤ min(I(X₁X₂;Y₁|Q), I(X₁X₂;Y₂|Q))`
  (`U₁ = X₁`, `U₂ = X₂`); `tinRegion_subset_hanKobayashiRegion` — it contains the
  treat-interference-as-noise region `R₁ ≤ I(X₁;Y₁|Q)`, `R₂ ≤ I(X₂;Y₂|Q)` (`U₁, U₂` constant).
  Generic relabelling tools: `cmi_relabel`, `cmi_eq_zero_of_eq_fun`, `cmi_fst_drop_fun`.

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

/-! ### Regression: the frozen Han–Kobayashi formula in solved cases

We check that the single-letter region `hanKobayashiRegion` (the building block of every level
of the `k`-letter hierarchy: it is stated for an arbitrary channel, in particular for
`icPower W k`) contains the known capacity / achievable regions in two classical cases:

* `U₁ = X₁`, `U₂ = X₂` (both messages common): under strong interference the region contains
  the Costa–El Gamal (1987) / Sato (1981) strong-interference capacity region
  `R₁ ≤ I(X₁;Y₁|X₂,Q)`, `R₂ ≤ I(X₂;Y₂|X₁,Q)`, `R₁ + R₂ ≤ min(I(X₁X₂;Y₁|Q), I(X₁X₂;Y₂|Q))`;
* `U₁, U₂` constant: the region contains the treat-interference-as-noise region
  `R₁ ≤ I(X₁;Y₁|Q)`, `R₂ ≤ I(X₂;Y₂|Q)`.
-/

section Regression

section Relabel

variable {Ω A B C A' C' D : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
  [Fintype A'] [Fintype C'] [Fintype D]

/-- `I(fa(A); B | fc(C)) = I(A; B | C)` for injective `fa`, `fc` (on a joint law). -/
theorem cmi_map_inj (K : ProbDist (A × B × C)) (fa : A → A') (fc : C → C')
    (hfa : Function.Injective fa) (hfc : Function.Injective fc) :
    condMutualInfo (K.map (fun t => (fa t.1, t.2.1, fc t.2.2))) = condMutualInfo K := by
  have hg1 : Function.Injective (fun t : A × C => (fa t.1, fc t.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hfa hxy.1) (hfc hxy.2)
  have hg2 : Function.Injective (fun t : A × B × C => (fa t.1, t.2.1, fc t.2.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (hfa hxy.1) (Prod.ext hxy.2.1 (hfc hxy.2.2))
  have hg3 : Function.Injective (fun t : B × C => (t.1, fc t.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (hfc hxy.2)
  unfold condMutualInfo
  dsimp only
  have e1 : (K.map (fun t => (fa t.1, t.2.1, fc t.2.2))).map (fun t => (t.1, t.2.2)) =
      (K.map (fun t => (t.1, t.2.2))).map (fun t => (fa t.1, fc t.2)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (K.map (fun t => (fa t.1, t.2.1, fc t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      (K.map (fun t => (t.2.1, t.2.2))).map (fun t => (t.1, fc t.2)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (K.map (fun t => (fa t.1, t.2.1, fc t.2.2))).map (fun t => t.2.2) =
      (K.map (fun t => t.2.2)).map fc := by
    rw [map_comp_eq, map_comp_eq]; rfl
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ hg1, shannonEntropy_map_of_injective _ hg2,
    shannonEntropy_map_of_injective _ hg3, shannonEntropy_map_of_injective _ hfc]

/-- `I(fa(A); B | fc(C)) = I(A; B | C)` for injective `fa`, `fc`. -/
theorem cmi_relabel (K : ProbDist Ω) (a : Ω → A) (b : Ω → B) (c : Ω → C)
    (fa : A → A') (fc : C → C') (hfa : Function.Injective fa) (hfc : Function.Injective fc) :
    condMutualInfo (K.map fun ω => (fa (a ω), b ω, fc (c ω))) =
      condMutualInfo (K.map fun ω => (a ω, b ω, c ω)) := by
  have h : (K.map fun ω => (fa (a ω), b ω, fc (c ω))) =
      (K.map fun ω => (a ω, b ω, c ω)).map (fun t => (fa t.1, t.2.1, fc t.2.2)) := by
    rw [map_comp_eq]; rfl
  rw [h]
  exact cmi_map_inj _ fa fc hfa hfc

/-- `I(A; B | C) = 0` when `A = φ(C)`. -/
theorem cmi_eq_zero_of_eq_fun (K : ProbDist Ω) (a : Ω → A) (b : Ω → B) (c : Ω → C)
    (φ : C → A) (h : ∀ ω, a ω = φ (c ω)) :
    condMutualInfo (K.map fun ω => (a ω, b ω, c ω)) = 0 := by
  obtain rfl : a = fun ω => φ (c ω) := funext h
  have hi1 : Function.Injective (fun z : C => (φ z, z)) := fun x y hxy => (Prod.mk.inj hxy).2
  have hi2 : Function.Injective (fun p : B × C => (φ p.2, p.1, p.2)) := fun x y hxy => by
    simp only [Prod.mk.injEq] at hxy; exact Prod.ext hxy.2.1 hxy.2.2
  unfold condMutualInfo
  dsimp only
  have e1 : (K.map fun ω => (φ (c ω), b ω, c ω)).map (fun t => (t.1, t.2.2)) =
      (K.map c).map (fun z => (φ z, z)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (K.map fun ω => (φ (c ω), b ω, c ω)).map (fun t => (t.2.1, t.2.2)) =
      K.map (fun ω => (b ω, c ω)) := by
    rw [map_comp_eq]; rfl
  have e4 : (K.map fun ω => (φ (c ω), b ω, c ω)).map (fun t => t.2.2) = K.map c := by
    rw [map_comp_eq]; rfl
  have e3 : (K.map fun ω => (φ (c ω), b ω, c ω)) =
      (K.map (fun ω => (b ω, c ω))).map (fun p => (φ p.2, p.1, p.2)) := by
    rw [map_comp_eq]; rfl
  rw [e1, e2, e4, e3, shannonEntropy_map_of_injective _ hi1,
    shannonEntropy_map_of_injective _ hi2]
  ring

/-- `I((φ(C), A); B | C) = I(A; B | C)`. -/
theorem cmi_fst_drop_fun (K : ProbDist Ω) (a : Ω → A) (b : Ω → B) (c : Ω → C) (φ : C → D) :
    condMutualInfo (K.map fun ω => ((φ (c ω), a ω), b ω, c ω)) =
      condMutualInfo (K.map fun ω => (a ω, b ω, c ω)) := by
  have hi1 : Function.Injective (fun p : A × C => ((φ p.2, p.1), p.2)) := fun x y hxy => by
    simp only [Prod.mk.injEq] at hxy; exact Prod.ext hxy.1.2 hxy.2
  have hi2 : Function.Injective (fun p : A × B × C => ((φ p.2.2, p.1), p.2.1, p.2.2)) :=
    fun x y hxy => by
      simp only [Prod.mk.injEq] at hxy; exact Prod.ext hxy.1.2 (Prod.ext hxy.2.1 hxy.2.2)
  unfold condMutualInfo
  dsimp only
  have e1 : (K.map fun ω => ((φ (c ω), a ω), b ω, c ω)).map (fun t => (t.1, t.2.2)) =
      ((K.map fun ω => (a ω, b ω, c ω)).map (fun t => (t.1, t.2.2))).map
        (fun p => ((φ p.2, p.1), p.2)) := by
    simp only [map_comp_eq] <;> rfl
  have e2 : (K.map fun ω => ((φ (c ω), a ω), b ω, c ω)).map (fun t => (t.2.1, t.2.2)) =
      (K.map fun ω => (a ω, b ω, c ω)).map (fun t => (t.2.1, t.2.2)) := by
    simp only [map_comp_eq] <;> rfl
  have e4 : (K.map fun ω => ((φ (c ω), a ω), b ω, c ω)).map (fun t => t.2.2) =
      (K.map fun ω => (a ω, b ω, c ω)).map (fun t => t.2.2) := by
    simp only [map_comp_eq] <;> rfl
  have e3 : (K.map fun ω => ((φ (c ω), a ω), b ω, c ω)) =
      (K.map fun ω => (a ω, b ω, c ω)).map (fun p => ((φ p.2.2, p.1), p.2.1, p.2.2)) := by
    simp only [map_comp_eq] <;> rfl
  rw [e1, e2, e4, e3, shannonEntropy_map_of_injective _ hi1,
    shannonEntropy_map_of_injective _ hi2]

end Relabel

/-- The plain joint law `p(q) p(x₁|q) p(x₂|q) W(y₁, y₂ | x₁, x₂)` of a product (time-shared)
    input to the interference channel. -/
def icJoint (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ : ℕ} (Pq : ProbDist (Fin kQ))
    (Px₁ : Fin kQ → ProbDist X₁) (Px₂ : Fin kQ → ProbDist X₂) :
    ProbDist (Fin kQ × X₁ × X₂ × (Y₁ × Y₂)) where
  pmf := fun s => Pq.pmf s.1 * (Px₁ s.1).pmf s.2.1 * (Px₂ s.1).pmf s.2.2.1 *
    W.trans (s.2.1, s.2.2.1) s.2.2.2
  nonneg := fun s => mul_nonneg (mul_nonneg (mul_nonneg (Pq.nonneg _) ((Px₁ _).nonneg _))
    ((Px₂ _).nonneg _)) (W.nonneg _ _)
  sum_one := by
    simp_rw [Fintype.sum_prod_type]
    have hW : ∀ x₁ x₂, ∑ y₁ : Y₁, ∑ y₂ : Y₂, W.trans (x₁, x₂) (y₁, y₂) = 1 :=
      fun x₁ x₂ => by rw [← Fintype.sum_prod_type]; exact W.sum_one (x₁, x₂)
    simp_rw [← Finset.mul_sum, hW, mul_one]
    have h2 : ∀ q, ∑ x₂ : X₂, (Px₂ q).pmf x₂ = 1 := fun q => (Px₂ q).sum_one
    simp_rw [← Finset.mul_sum, h2, mul_one]
    have h1 : ∀ q, ∑ x₁ : X₁, (Px₁ q).pmf x₁ = 1 := fun q => (Px₁ q).sum_one
    simp_rw [← Finset.mul_sum, h1, mul_one, Pq.sum_one]

/-- The embedding `(q, x₁, x₂, y) ↦ (q, (e₁ x₁, x₁), (e₂ x₂, x₂), y)` (the auxiliaries are
    deterministic functions of the inputs). -/
def hkEmbed {kQ kU₁ kU₂ : ℕ} (e₁ : X₁ → Fin kU₁) (e₂ : X₂ → Fin kU₂) :
    Fin kQ × X₁ × X₂ × (Y₁ × Y₂) → Fin kQ × (Fin kU₁ × X₁) × (Fin kU₂ × X₂) × (Y₁ × Y₂) :=
  fun s => (s.1, (e₁ s.2.1, s.2.1), (e₂ s.2.2.1, s.2.2.1), s.2.2.2)

theorem pmf_map_diag {α : Type*} [Fintype α] {k : ℕ} (P : ProbDist α) (e : α → Fin k)
    (u : Fin k) (x : α) :
    (P.map (fun x => (e x, x))).pmf (u, x) = if e x = u then P.pmf x else 0 := by
  classical
  simp only [ProbDist.map]
  rw [Finset.sum_eq_single x]
  · by_cases h : e x = u <;> simp [h]
  · intro b _ hb; simp [hb]
  · simp

theorem inj_zero_left {α : Type*} : Function.Injective (fun p : α => ((0 : Fin 1), p)) :=
  fun _ _ h => (Prod.mk.inj h).2

theorem inj_zero_right {α : Type*} : Function.Injective (fun p : α => (p, (0 : Fin 1))) :=
  fun _ _ h => (Prod.mk.inj h).1

theorem inj_zero_zero_left {α : Type*} :
    Function.Injective (fun p : α => ((0 : Fin 1), (0 : Fin 1), p)) :=
  fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2

/-- With `P(u, x | q) = P(x | q) 1[u = e(x)]`, the Han–Kobayashi joint law is the pushforward
    of `icJoint` along `hkEmbed`. -/
theorem hk_pmf_eq (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ kU₁ kU₂ : ℕ}
    (Pq : ProbDist (Fin kQ)) (Px₁ : Fin kQ → ProbDist X₁) (Px₂ : Fin kQ → ProbDist X₂)
    (e₁ : X₁ → Fin kU₁) (e₂ : X₂ → Fin kU₂)
    (t : Fin kQ × (Fin kU₁ × X₁) × (Fin kU₂ × X₂) × (Y₁ × Y₂)) :
    Pq.pmf t.1 * ((Px₁ t.1).map (fun x => (e₁ x, x))).pmf t.2.1 *
        ((Px₂ t.1).map (fun x => (e₂ x, x))).pmf t.2.2.1 *
        W.trans (t.2.1.2, t.2.2.1.2) t.2.2.2 =
      ((icJoint W Pq Px₁ Px₂).map (hkEmbed e₁ e₂)).pmf t := by
  classical
  obtain ⟨q, ⟨u₁, x₁⟩, ⟨u₂, x₂⟩, y⟩ := t
  dsimp only
  rw [pmf_map_diag, pmf_map_diag]
  simp only [ProbDist.map]
  rw [Finset.sum_eq_single (q, x₁, x₂, y)]
  · by_cases h1 : e₁ x₁ = u₁ <;> by_cases h2 : e₂ x₂ = u₂ <;> simp [h1, h2, hkEmbed, icJoint]
  · rintro ⟨q', x₁', x₂', y'⟩ _ hne
    rw [if_neg]
    intro h
    apply hne
    simp only [hkEmbed, Prod.mk.injEq] at h
    obtain ⟨rfl, ⟨-, rfl⟩, ⟨-, rfl⟩, rfl⟩ := h
    rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The Costa–El Gamal strong-interference region for the time-shared product input
    `(Pq, Px₁, Px₂)`: `R₁ ≤ I(X₁;Y₁|X₂,Q)`, `R₂ ≤ I(X₂;Y₂|X₁,Q)`,
    `R₁ + R₂ ≤ min(I(X₁,X₂;Y₁|Q), I(X₁,X₂;Y₂|Q))`. -/
def costaElGamalRegion (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ : ℕ} (Pq : ProbDist (Fin kQ))
    (Px₁ : Fin kQ → ProbDist X₁) (Px₂ : Fin kQ → ProbDist X₂) : Set (ℝ × ℝ) :=
  let K := icJoint W Pq Px₁ Px₂
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    r.1 ≤ condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, (s.2.2.1, s.1))) ∧
    r.2 ≤ condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, (s.2.1, s.1))) ∧
    r.1 + r.2 ≤ condMutualInfo (K.map fun s => ((s.2.1, s.2.2.1), s.2.2.2.1, s.1)) ∧
    r.1 + r.2 ≤ condMutualInfo (K.map fun s => ((s.2.1, s.2.2.1), s.2.2.2.2, s.1)) }

/-- Strong interference for the input `(Pq, Px₁, Px₂)`: `I(X₁;Y₁|X₂,Q) ≤ I(X₁;Y₂|X₂,Q)` and
    `I(X₂;Y₂|X₁,Q) ≤ I(X₂;Y₁|X₁,Q)` (implied by the Costa–El Gamal condition for all product
    inputs). -/
def IsStrongInterferenceAt (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ : ℕ}
    (Pq : ProbDist (Fin kQ)) (Px₁ : Fin kQ → ProbDist X₁) (Px₂ : Fin kQ → ProbDist X₂) : Prop :=
  let K := icJoint W Pq Px₁ Px₂
  condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, (s.2.2.1, s.1))) ≤
      condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.2, (s.2.2.1, s.1))) ∧
    condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, (s.2.1, s.1))) ≤
      condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.1, (s.2.1, s.1)))

/-- **Regression (strong interference)**: under strong interference the frozen Han–Kobayashi
    formula contains the Costa–El Gamal capacity region (take `U₁ = X₁`, `U₂ = X₂`). -/
theorem costaElGamalRegion_subset_hanKobayashiRegion (W : InterferenceChannel X₁ X₂ Y₁ Y₂)
    {kQ : ℕ} (Pq : ProbDist (Fin kQ)) (Px₁ : Fin kQ → ProbDist X₁)
    (Px₂ : Fin kQ → ProbDist X₂) (hSI : IsStrongInterferenceAt W Pq Px₁ Px₂) :
    costaElGamalRegion W Pq Px₁ Px₂ ⊆ hanKobayashiRegion W := by
  intro r hr
  obtain ⟨hr1, hr2, hI1, hI2, hS1, hS2⟩ := hr
  obtain ⟨hT1, hT2⟩ := hSI
  set K := icJoint W Pq Px₁ Px₂ with hK
  let e₁ := Fintype.equivFin X₁
  let e₂ := Fintype.equivFin X₂
  refine ⟨hr1, hr2, kQ, Fintype.card X₁, Fintype.card X₂, Pq,
    fun q => (Px₁ q).map (fun x => (e₁ x, x)), fun q => (Px₂ q).map (fun x => (e₂ x, x)), ?_⟩
  intro J a1 a2 b1 b2 c1 c2 d1 d2
  have hJ : J = K.map (hkEmbed e₁ e₂) :=
    probDist_eq_of_pmf (fun t => hk_pmf_eq W Pq Px₁ Px₂ e₁ e₂ t)
  have ha1 : a1 = condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, (s.2.2.1, s.1))) := by
    show condMutualInfo (J.map (fun t => (t.2.1.2, t.2.2.2.1, (t.2.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.1) (fun s => s.2.2.2.1) (fun s => (s.2.2.1, s.1)) id
      (fun p => (e₂ p.1, p.2)) Function.injective_id
      (fun x y h => Prod.ext (e₂.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2)
  have ha2 : a2 = condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, (s.2.1, s.1))) := by
    show condMutualInfo (J.map (fun t => (t.2.2.1.2, t.2.2.2.2, (t.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.2.1) (fun s => s.2.2.2.2) (fun s => (s.2.1, s.1)) id
      (fun p => (e₁ p.1, p.2)) Function.injective_id
      (fun x y h => Prod.ext (e₁.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2)
  have hb1 : b1 = condMutualInfo (K.map fun s => ((s.2.1, s.2.2.1), s.2.2.2.1, s.1)) := by
    show condMutualInfo (J.map (fun t => ((t.2.1.2, t.2.2.1.1), t.2.2.2.1, t.1))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => (s.2.1, s.2.2.1)) (fun s => s.2.2.2.1) (fun s => s.1)
      (fun p => (p.1, e₂ p.2)) id
      (fun x y h => Prod.ext (Prod.mk.inj h).1 (e₂.injective (Prod.mk.inj h).2))
      Function.injective_id
  have hb2 : b2 = condMutualInfo (K.map fun s => ((s.2.1, s.2.2.1), s.2.2.2.2, s.1)) := by
    show condMutualInfo (J.map (fun t => ((t.2.2.1.2, t.2.1.1), t.2.2.2.2, t.1))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => (s.2.1, s.2.2.1)) (fun s => s.2.2.2.2) (fun s => s.1)
      (fun p => (p.2, e₁ p.1)) id
      (fun x y h => Prod.ext (e₁.injective (Prod.mk.inj h).2) (Prod.mk.inj h).1)
      Function.injective_id
  have hc1 : c1 = 0 := by
    show condMutualInfo (J.map (fun t => (t.2.1.2, t.2.2.2.1, (t.2.1.1, t.2.2.1.1, t.1)))) = 0
    rw [hJ, map_comp_eq]
    exact cmi_eq_zero_of_eq_fun K (fun s => s.2.1) (fun s => s.2.2.2.1)
      (fun s => (e₁ s.2.1, e₂ s.2.2.1, s.1)) (fun c => e₁.symm c.1) (fun s => by simp)
  have hc2 : c2 = 0 := by
    show condMutualInfo (J.map (fun t => (t.2.2.1.2, t.2.2.2.2, (t.2.1.1, t.2.2.1.1, t.1)))) = 0
    rw [hJ, map_comp_eq]
    exact cmi_eq_zero_of_eq_fun K (fun s => s.2.2.1) (fun s => s.2.2.2.2)
      (fun s => (e₁ s.2.1, e₂ s.2.2.1, s.1)) (fun c => e₂.symm c.2.1) (fun s => by simp)
  have hd1 : d1 = condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.1, (s.2.1, s.1))) := by
    show condMutualInfo (J.map (fun t => ((t.2.1.2, t.2.2.1.1), t.2.2.2.1, (t.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    refine (cmi_relabel K (fun s => (s.2.1, s.2.2.1)) (fun s => s.2.2.2.1)
      (fun s => (s.2.1, s.1)) (fun p => (p.1, e₂ p.2)) (fun p => (e₁ p.1, p.2))
      (fun x y h => Prod.ext (Prod.mk.inj h).1 (e₂.injective (Prod.mk.inj h).2))
      (fun x y h => Prod.ext (e₁.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2)).trans ?_
    exact cmi_fst_drop_fun K (fun s => s.2.2.1) (fun s => s.2.2.2.1) (fun s => (s.2.1, s.1))
      Prod.fst
  have hd2 : d2 = condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.2, (s.2.2.1, s.1))) := by
    show condMutualInfo (J.map (fun t => ((t.2.2.1.2, t.2.1.1), t.2.2.2.2, (t.2.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    refine (cmi_relabel K (fun s => (s.2.2.1, s.2.1)) (fun s => s.2.2.2.2)
      (fun s => (s.2.2.1, s.1)) (fun p => (p.1, e₁ p.2)) (fun p => (e₂ p.1, p.2))
      (fun x y h => Prod.ext (Prod.mk.inj h).1 (e₁.injective (Prod.mk.inj h).2))
      (fun x y h => Prod.ext (e₂.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2)).trans ?_
    exact cmi_fst_drop_fun K (fun s => s.2.1) (fun s => s.2.2.2.2) (fun s => (s.2.2.1, s.1))
      Prod.fst
  rw [ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2]
  refine ⟨hI1, hI2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The treat-interference-as-noise region for the time-shared product input:
    `R₁ ≤ I(X₁;Y₁|Q)`, `R₂ ≤ I(X₂;Y₂|Q)`. -/
def tinRegion (W : InterferenceChannel X₁ X₂ Y₁ Y₂) {kQ : ℕ} (Pq : ProbDist (Fin kQ))
    (Px₁ : Fin kQ → ProbDist X₁) (Px₂ : Fin kQ → ProbDist X₂) : Set (ℝ × ℝ) :=
  let K := icJoint W Pq Px₁ Px₂
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    r.1 ≤ condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, s.1)) ∧
    r.2 ≤ condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, s.1)) }

/-- **Regression (treating interference as noise)**: the frozen Han–Kobayashi formula contains
    the TIN region (take `U₁`, `U₂` constant). -/
theorem tinRegion_subset_hanKobayashiRegion (W : InterferenceChannel X₁ X₂ Y₁ Y₂)
    {kQ : ℕ} (Pq : ProbDist (Fin kQ)) (Px₁ : Fin kQ → ProbDist X₁)
    (Px₂ : Fin kQ → ProbDist X₂) :
    tinRegion W Pq Px₁ Px₂ ⊆ hanKobayashiRegion W := by
  intro r hr
  obtain ⟨hr1, hr2, hA1, hA2⟩ := hr
  set K := icJoint W Pq Px₁ Px₂ with hK
  let e₁ : X₁ → Fin 1 := fun _ => 0
  let e₂ : X₂ → Fin 1 := fun _ => 0
  refine ⟨hr1, hr2, kQ, 1, 1, Pq,
    fun q => (Px₁ q).map (fun x => (e₁ x, x)), fun q => (Px₂ q).map (fun x => (e₂ x, x)), ?_⟩
  intro J a1 a2 b1 b2 c1 c2 d1 d2
  have hJ : J = K.map (hkEmbed e₁ e₂) :=
    probDist_eq_of_pmf (fun t => hk_pmf_eq W Pq Px₁ Px₂ e₁ e₂ t)
  have ha1 : a1 = condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, s.1)) := by
    show condMutualInfo (J.map (fun t => (t.2.1.2, t.2.2.2.1, (t.2.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.1) (fun s => s.2.2.2.1) (fun s => s.1) id (fun p => ((0 : Fin 1), p))
      Function.injective_id inj_zero_left
  have ha2 : a2 = condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, s.1)) := by
    show condMutualInfo (J.map (fun t => (t.2.2.1.2, t.2.2.2.2, (t.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.2.1) (fun s => s.2.2.2.2) (fun s => s.1) id (fun p => ((0 : Fin 1), p))
      Function.injective_id inj_zero_left
  have hb1 : b1 = condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, s.1)) := by
    show condMutualInfo (J.map (fun t => ((t.2.1.2, t.2.2.1.1), t.2.2.2.1, t.1))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.1) (fun s => s.2.2.2.1) (fun s => s.1) (fun p => (p, (0 : Fin 1))) id
      inj_zero_right Function.injective_id
  have hb2 : b2 = condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, s.1)) := by
    show condMutualInfo (J.map (fun t => ((t.2.2.1.2, t.2.1.1), t.2.2.2.2, t.1))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.2.1) (fun s => s.2.2.2.2) (fun s => s.1) (fun p => (p, (0 : Fin 1))) id
      inj_zero_right Function.injective_id
  have hc1 : c1 = condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, s.1)) := by
    show condMutualInfo (J.map (fun t => (t.2.1.2, t.2.2.2.1, (t.2.1.1, t.2.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.1) (fun s => s.2.2.2.1) (fun s => s.1) id (fun p => ((0 : Fin 1), (0 : Fin 1), p))
      Function.injective_id inj_zero_zero_left
  have hc2 : c2 = condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, s.1)) := by
    show condMutualInfo (J.map (fun t => (t.2.2.1.2, t.2.2.2.2, (t.2.1.1, t.2.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.2.1) (fun s => s.2.2.2.2) (fun s => s.1) id (fun p => ((0 : Fin 1), (0 : Fin 1), p))
      Function.injective_id inj_zero_zero_left
  have hd1 : d1 = condMutualInfo (K.map fun s => (s.2.1, s.2.2.2.1, s.1)) := by
    show condMutualInfo (J.map (fun t => ((t.2.1.2, t.2.2.1.1), t.2.2.2.1, (t.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.1) (fun s => s.2.2.2.1) (fun s => s.1) (fun p => (p, (0 : Fin 1)))
      (fun p => ((0 : Fin 1), p)) inj_zero_right inj_zero_left
  have hd2 : d2 = condMutualInfo (K.map fun s => (s.2.2.1, s.2.2.2.2, s.1)) := by
    show condMutualInfo (J.map (fun t => ((t.2.2.1.2, t.2.1.1), t.2.2.2.2, (t.2.2.1.1, t.1)))) = _
    rw [hJ, map_comp_eq]
    exact cmi_relabel K (fun s => s.2.2.1) (fun s => s.2.2.2.2) (fun s => s.1) (fun p => (p, (0 : Fin 1)))
      (fun p => ((0 : Fin 1), p)) inj_zero_right inj_zero_left
  rw [ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2]
  have n1 := condMutualInfo_nonneg (K.map fun s => (s.2.1, s.2.2.2.1, s.1))
  have n2 := condMutualInfo_nonneg (K.map fun s => (s.2.2.1, s.2.2.2.2, s.1))
  refine ⟨hA1, hA2, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Regression

end InfoTheory.Known.Certificates.DmInterferenceChannelCapacity
