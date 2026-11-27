import InfoTheory.Problems.BinarySymmetricZInterferenceChannel
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.DmInterferenceChannelCapacity

/-!
# Certificate for `InfoTheory.Problems.BinarySymmetricZInterferenceChannel`

The frozen statement (status `solved`) says that for all `p₁, p₂ ∈ (0, 1/2)` the operational
capacity region of the binary symmetric Z-interference channel
`Y₁ = X₁ ⊕ X₂ ⊕ N₁`, `Y₂ = X₂ ⊕ N₂` equals the closed form `bsZicClosedFormRegion p₁ p₂`.

## Certified (about exactly these objects)
* `ch₁_bsZic`, `ch₂_bsZic` — with the other transmitter silent (sending `0`), each user sees
  `BSC(pⱼ)`.
* `marginalFst_bsZic_capacity_le`, `marginalSnd_bsZic_capacity_le` — `C(X₁X₂ → Y₁) ≤ 1 - h(p₁)`
  and `C(X₁X₂ → Y₂) ≤ 1 - h(p₂)` (each row of the channel is a binary distribution
  `{p, 1 - p}`, so `H(Y | X) = h(p)` and `I = H(Y) - h(p) ≤ 1 - h(p)`).
* `icCapacityRegion_bsZic_subset_box` — hence the operational region lies in
  `[0, 1 - h(p₁)] × [0, 1 - h(p₂)]`.
* `mk_zero_mem_icCapacityRegion_bsZic_iff`, `zero_mk_mem_icCapacityRegion_bsZic_iff` — the
  operational region's axes are exactly `[0, 1 - h(p₁)]` and `[0, 1 - h(p₂)]` (achievability:
  Shannon's theorem for the BSC with the other user silent, `Known.bsc_capacity`).
* `mk_zero_mem_closedForm_iff`, `zero_mk_mem_closedForm_iff` — the closed form has the same
  axes, in both regimes. In the weak regime this uses `h⁻¹(h(p₂)) = p₂` and
  `q ⋆ p₂ = p₁` for `q = (p₁ - p₂)/(1 - 2p₂)` (`Bridge.invBinaryEntropy_binaryEntropy`).
* `mk_zero_mem_iff`, `zero_mk_mem_iff` — **the two sides of the statement agree on both
  axes**, for every admissible `(p₁, p₂)`. This is consistency evidence for the statement;
  it does not prove it.

## Not certified
* The full equality (the statement itself): the strong-regime sum-rate converse
  `R₁ + R₂ ≤ 1 - h(p₁)` and the weak-regime converse need Mrs. Gerber's lemma applied to the
  multi-letter code (with a Fano argument for the interference channel), and achievability
  needs superposition / successive decoding. `Bridge.MrsGerber` has the scalar and vector
  inequalities but not this converse.
* Whether the closed form lies inside the box in the weak regime off the axes (needs
  monotonicity of `u ↦ h(q ⋆ h⁻¹(u))`).

Sources: Benzel 1979; Sato 1981; Liu–Goldsmith 2009; El Gamal–Kim §6.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BinarySymmetricZInterferenceChannel

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.BinarySymmetricZInterferenceChannel
open InfoTheory.Known.Certificates.DmInterferenceChannelCapacity (ch₁ ch₂
  icCapacityRegion_subset_box Icc_prod_zero_subset_icCapacityRegion
  zero_prod_Icc_subset_icCapacityRegion)

theorem dmc_ext {α β : Type*} [Fintype α] [Fintype β] {V V' : DMC α β}
    (h : ∀ x y, V.trans x y = V'.trans x y) : V = V' := by
  cases V; cases V'
  congr
  funext x y
  exact h x y

lemma log2_card_bool : log2 (Fintype.card Bool : ℝ) = 1 := by
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  exact div_self (Real.log_pos one_lt_two).ne'

variable {p₁ p₂ : ℝ} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1) (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1)

/-! ### Single-user channels -/

theorem ch₁_bsZic : ch₁ (bsZicChannel p₁ p₂ h10 h11 h20 h21) false = bsc p₁ h10 h11 := by
  refine dmc_ext fun x y => ?_
  simp only [ch₁, marginalFst, dmcPrecomp, bsZicChannel, bsc, Fintype.sum_bool]
  cases x <;> cases y <;> simp <;> ring

theorem ch₂_bsZic : ch₂ (bsZicChannel p₁ p₂ h10 h11 h20 h21) false = bsc p₂ h20 h21 := by
  refine dmc_ext fun x y => ?_
  simp only [ch₂, marginalSnd, dmcPrecomp, bsZicChannel, bsc, Fintype.sum_bool]
  cases x <;> cases y <;> simp <;> ring

/-! ### Outer bound -/

theorem marginalFst_bsZic_capacity_le :
    (marginalFst (bsZicChannel p₁ p₂ h10 h11 h20 h21)).capacity ≤ 1 - binaryEntropy p₁ := by
  refine Real.sSup_le (fun r hr => ?_) (by linarith [binaryEntropy_le_one h10 h11])
  obtain ⟨P, rfl⟩ := hr
  rw [mutualInfo_eq_entropy_output_sub]
  have hrow : ∀ x : Bool × Bool, ∑ y, negPLogP
      ((marginalFst (bsZicChannel p₁ p₂ h10 h11 h20 h21)).trans x y) = binaryEntropy p₁ := by
    rintro ⟨a, b⟩
    have e : ∀ y : Bool, (marginalFst (bsZicChannel p₁ p₂ h10 h11 h20 h21)).trans (a, b) y =
        if y = xor a b then 1 - p₁ else p₁ := by
      intro y
      cases a <;> cases b <;> cases y <;> simp [marginalFst, bsZicChannel, Fintype.sum_bool] <;> ring
    simp only [e, Fintype.sum_bool, binaryEntropy]
    cases a <;> cases b <;> simp [add_comm]
  simp_rw [hrow, ← Finset.sum_mul, P.sum_one, one_mul]
  have := shannonEntropy_le_log2_card
    ((marginalFst (bsZicChannel p₁ p₂ h10 h11 h20 h21)).joint P).snd
  rw [log2_card_bool] at this
  linarith

theorem marginalSnd_bsZic_capacity_le :
    (marginalSnd (bsZicChannel p₁ p₂ h10 h11 h20 h21)).capacity ≤ 1 - binaryEntropy p₂ := by
  refine Real.sSup_le (fun r hr => ?_) (by linarith [binaryEntropy_le_one h20 h21])
  obtain ⟨P, rfl⟩ := hr
  rw [mutualInfo_eq_entropy_output_sub]
  have hrow : ∀ x : Bool × Bool, ∑ y, negPLogP
      ((marginalSnd (bsZicChannel p₁ p₂ h10 h11 h20 h21)).trans x y) = binaryEntropy p₂ := by
    rintro ⟨a, b⟩
    have e : ∀ y : Bool, (marginalSnd (bsZicChannel p₁ p₂ h10 h11 h20 h21)).trans (a, b) y =
        if y = b then 1 - p₂ else p₂ := by
      intro y
      cases a <;> cases b <;> cases y <;> simp [marginalSnd, bsZicChannel, Fintype.sum_bool] <;> ring
    simp only [e, Fintype.sum_bool, binaryEntropy]
    cases b <;> simp [add_comm]
  simp_rw [hrow, ← Finset.sum_mul, P.sum_one, one_mul]
  have := shannonEntropy_le_log2_card
    ((marginalSnd (bsZicChannel p₁ p₂ h10 h11 h20 h21)).joint P).snd
  rw [log2_card_bool] at this
  linarith

/-- **Outer bound**: `C(BS-ZIC) ⊆ [0, 1 - h(p₁)] × [0, 1 - h(p₂)]`. -/
theorem icCapacityRegion_bsZic_subset_box :
    icCapacityRegion (bsZicChannel p₁ p₂ h10 h11 h20 h21) ⊆
      Set.Icc 0 (1 - binaryEntropy p₁) ×ˢ Set.Icc 0 (1 - binaryEntropy p₂) := by
  intro r hr
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := icCapacityRegion_subset_box _ hr
  exact ⟨⟨a, b.trans (marginalFst_bsZic_capacity_le h10 h11 h20 h21)⟩,
    ⟨c, d.trans (marginalSnd_bsZic_capacity_le h10 h11 h20 h21)⟩⟩

/-! ### Axes of the operational region -/

theorem mk_zero_mem_icCapacityRegion_bsZic_iff (R : ℝ) :
    (R, (0 : ℝ)) ∈ icCapacityRegion (bsZicChannel p₁ p₂ h10 h11 h20 h21) ↔
      0 ≤ R ∧ R ≤ 1 - binaryEntropy p₁ := by
  constructor
  · intro h
    exact (icCapacityRegion_bsZic_subset_box h10 h11 h20 h21 h).1
  · intro h
    refine Icc_prod_zero_subset_icCapacityRegion _ false ⟨?_, rfl⟩
    rw [ch₁_bsZic, bsc_capacity]
    exact h

theorem zero_mk_mem_icCapacityRegion_bsZic_iff (R : ℝ) :
    ((0 : ℝ), R) ∈ icCapacityRegion (bsZicChannel p₁ p₂ h10 h11 h20 h21) ↔
      0 ≤ R ∧ R ≤ 1 - binaryEntropy p₂ := by
  constructor
  · intro h
    exact (icCapacityRegion_bsZic_subset_box h10 h11 h20 h21 h).2
  · intro h
    refine zero_prod_Icc_subset_icCapacityRegion _ false ⟨rfl, ?_⟩
    rw [ch₂_bsZic, bsc_capacity]
    exact h

/-! ### Axes of the closed form -/

theorem binaryConv_weak {p₁ p₂ : ℝ} (h21 : p₂ < 1 / 2) :
    binaryConv ((p₁ - p₂) / (1 - 2 * p₂)) p₂ = p₁ := by
  unfold binaryConv
  have h : (1 - 2 * p₂) ≠ 0 := by linarith
  have key : (p₁ - p₂) / (1 - 2 * p₂) * (1 - 2 * p₂) = p₁ - p₂ := div_mul_cancel₀ _ h
  linear_combination key

theorem mk_zero_mem_closedForm_iff {p₁ p₂ : ℝ} (h10 : 0 < p₁) (h11 : p₁ < 1 / 2) (h20 : 0 < p₂)
    (h21 : p₂ < 1 / 2) (R : ℝ) :
    (R, (0 : ℝ)) ∈ bsZicClosedFormRegion p₁ p₂ ↔ 0 ≤ R ∧ R ≤ 1 - binaryEntropy p₁ := by
  have hh2 : binaryEntropy p₂ ≤ 1 := binaryEntropy_le_one h20.le (by linarith)
  show (0 ≤ R ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 - binaryEntropy p₂ ∧
    if p₁ ≤ p₂ then R + 0 ≤ 1 - binaryEntropy p₁ else
      R ≤ 1 - binaryEntropy (binaryConv ((p₁ - p₂) / (1 - 2 * p₂))
        (invBinaryEntropy (binaryEntropy p₂ + 0)))) ↔ _
  split_ifs with h
  · constructor
    · rintro ⟨a, -, -, d⟩; exact ⟨a, by linarith⟩
    · rintro ⟨a, b⟩; exact ⟨a, le_rfl, by linarith, by linarith⟩
  · rw [add_zero, invBinaryEntropy_binaryEntropy h20.le h21.le, binaryConv_weak h21]
    constructor
    · rintro ⟨a, -, -, d⟩; exact ⟨a, d⟩
    · rintro ⟨a, b⟩; exact ⟨a, le_rfl, by linarith, b⟩

theorem zero_mk_mem_closedForm_iff {p₁ p₂ : ℝ} (h10 : 0 < p₁) (h11 : p₁ < 1 / 2) (h20 : 0 < p₂)
    (h21 : p₂ < 1 / 2) (R : ℝ) :
    ((0 : ℝ), R) ∈ bsZicClosedFormRegion p₁ p₂ ↔ 0 ≤ R ∧ R ≤ 1 - binaryEntropy p₂ := by
  show (0 ≤ (0 : ℝ) ∧ 0 ≤ R ∧ R ≤ 1 - binaryEntropy p₂ ∧
    if p₁ ≤ p₂ then 0 + R ≤ 1 - binaryEntropy p₁ else
      (0 : ℝ) ≤ 1 - binaryEntropy (binaryConv ((p₁ - p₂) / (1 - 2 * p₂))
        (invBinaryEntropy (binaryEntropy p₂ + R)))) ↔ _
  split_ifs with h
  · have hmono : binaryEntropy p₁ ≤ binaryEntropy p₂ :=
      binaryEntropy_strictMonoOn.monotoneOn ⟨h10.le, h11.le⟩ ⟨h20.le, h21.le⟩ h
    constructor
    · rintro ⟨-, b, c, -⟩; exact ⟨b, c⟩
    · rintro ⟨b, c⟩; exact ⟨le_rfl, b, c, by linarith⟩
  · push Not at h
    constructor
    · rintro ⟨-, b, c, -⟩; exact ⟨b, c⟩
    · rintro ⟨b, c⟩
      refine ⟨le_rfl, b, c, ?_⟩
      have hu := invBinaryEntropy_mem_Icc (u := binaryEntropy p₂ + R)
        (by linarith [binaryEntropy_nonneg h20.le (by linarith : p₂ ≤ 1)]) (by linarith)
      set u := invBinaryEntropy (binaryEntropy p₂ + R)
      set q := (p₁ - p₂) / (1 - 2 * p₂) with hq
      have hd : 0 < 1 - 2 * p₂ := by linarith
      have hq0 : 0 ≤ q := div_nonneg (by linarith) hd.le
      have hq1 : q ≤ 1 := by rw [hq, div_le_one hd]; linarith
      have hc0 : 0 ≤ binaryConv q u := by unfold binaryConv; nlinarith [hu.1, hu.2]
      have hc1 : binaryConv q u ≤ 1 := by unfold binaryConv; nlinarith [hu.1, hu.2]
      linarith [binaryEntropy_le_one hc0 hc1]

/-! ### The two sides of the statement agree on both axes -/

theorem mk_zero_mem_iff {p₁ p₂ : ℝ} (h10 : 0 < p₁) (h11 : p₁ < 1 / 2) (h20 : 0 < p₂)
    (h21 : p₂ < 1 / 2) (R : ℝ) :
    (R, (0 : ℝ)) ∈ icCapacityRegion
        (bsZicChannel p₁ p₂ (le_of_lt h10) (by linarith) (le_of_lt h20) (by linarith)) ↔
      (R, (0 : ℝ)) ∈ bsZicClosedFormRegion p₁ p₂ := by
  rw [mk_zero_mem_icCapacityRegion_bsZic_iff, mk_zero_mem_closedForm_iff h10 h11 h20 h21]

theorem zero_mk_mem_iff {p₁ p₂ : ℝ} (h10 : 0 < p₁) (h11 : p₁ < 1 / 2) (h20 : 0 < p₂)
    (h21 : p₂ < 1 / 2) (R : ℝ) :
    ((0 : ℝ), R) ∈ icCapacityRegion
        (bsZicChannel p₁ p₂ (le_of_lt h10) (by linarith) (le_of_lt h20) (by linarith)) ↔
      ((0 : ℝ), R) ∈ bsZicClosedFormRegion p₁ p₂ := by
  rw [zero_mk_mem_icCapacityRegion_bsZic_iff, zero_mk_mem_closedForm_iff h10 h11 h20 h21]

end InfoTheory.Known.Certificates.BinarySymmetricZInterferenceChannel
