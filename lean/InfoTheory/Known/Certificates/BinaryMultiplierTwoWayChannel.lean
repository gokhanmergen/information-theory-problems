import InfoTheory.Problems.BinaryMultiplierTwoWayChannel
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.TwoWayChannelCapacity

/-!
# Certificate for `InfoTheory.Problems.BinaryMultiplierTwoWayChannel`

The statement (statement-fix 2026-11-27) asks whether the symmetric capacity
`bmcSymmetricCapacity` of Blackwell's binary multiplying channel `Y₁ = Y₂ = X₁ · X₂` equals
`bmcHWParallelChannelBound`, the Hekstra–Willems dependence-balance bound with an adaptive
parallel channel (≈ 0.64628), in the closed form of the problem file.

## Certified (about exactly these objects)
* `isTWCAchievable_timeDivision`, `half_le_bmcSymmetricCapacity` — **time division**: for every
  `R < 1/2` the pair `(R, R)` is achievable with zero error (terminal 1 sends raw bits in the
  first `⌊n/2⌋` slots while terminal 2 sends `1`, then they swap roles), so
  `1/2 ≤ bmcSymmetricCapacity`.
* `bmcSymmetricCapacity_le_one` — `bmcSymmetricCapacity ≤ 1` (counting converse
  `TwoWayChannelCapacity.twcCapacityRegion_subset_box`, `log₂ |Y| = 1`). With the previous item
  the left-hand side lies in `[1/2, 1]`; in particular the `sSup` is over a nonempty set that
  is bounded above.
* `hwBound_set_bddAbove`, `bmcHWParallelChannelBound_le_one` — every element of the set under
  the right-hand `sSup` is at most the `U`-free term `P₂ h(P₁₁ / P₂) ≤ 1`.
* `binaryEntropy_quarter_ge`, `half_le_bmcHWParallelChannelBound` — the point `|U| = 1`,
  `α = β = 1/2` (crossover `1/2`) gives the value `1/2`, because `h(1/4) ≥ 1/2`. So the
  right-hand side also lies in `[1/2, 1]`, and its `sSup` is over a nonempty set that is
  bounded above.
* `schalkwijk_lt_bmcHWParallelChannelBound` — `0.6191 < bmcHWParallelChannelBound`: the point
  `|U| = 2`, `w = (1/2, 1/2)`, `α = (1/2, 5/6)`, `β = (5/6, 1/2)` gives `≈ 0.63629`, using
  `19/12 < log₂ 3 < 8/5`, `log₂ 5 < 7/3`, `log₂ 7 < 17/6`. A sanity check of the closed form:
  Schalkwijk's achievable rate `0.6191` (1982) lower-bounds `C_sym`, so any correct upper
  bound must exceed it.

## Not certified
* Achievability beyond time division: Shannon's inner bound `≈ 0.61695` (the right-hand
  functional at `|U| = 1`, `α = β ≈ 0.70351` also evaluates to it), Schalkwijk's `0.63056`,
  Schalkwijk–Meeuwissen–Bloemen's `0.63072` (no two-way-channel achievability in the library).
* That `bmcHWParallelChannelBound` is an upper bound on `bmcSymmetricCapacity` (the
  Hekstra–Willems converse), and its numerical value `≈ 0.6462832` (reproduced only by floating
  point optimisation, `|U| = 3`, in the attempt below).
* The closed-form reduction of the parallel-channel bound (on paper:
  `attempts/binary-multiplier-two-way-channel/2026-11-26-claude-opus-5-5-db-catalog-error-survey.md`,
  Claim 4), and the fact that the pre-fix plain-DB functional equals `log₂ φ` (Claim 2), which
  made the pre-fix statement false.

Sources: Shannon 1961; Schalkwijk, IEEE Trans. IT 1982/1983; Hekstra–Willems, IEEE Trans. IT
1989; Bloemen, PhD thesis, TU Eindhoven 1996, Ch. 6.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BinaryMultiplierTwoWayChannel

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.BinaryMultiplierTwoWayChannel
open InfoTheory.Known.Certificates.TwoWayChannelCapacity (twcCapacityRegion_subset_box
  condMutualInfo_le_log2_card)

lemma log2_card_bool : log2 (Fintype.card Bool : ℝ) = 1 := by
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  exact div_self (Real.log_pos one_lt_two).ne'

/-! ### Upper bounds -/

theorem bmcSymmetricCapacity_le_one : bmcSymmetricCapacity ≤ 1 := by
  unfold bmcSymmetricCapacity
  refine Real.sSup_le (fun R hR => ?_) zero_le_one
  have := (twcCapacityRegion_subset_box binaryMultiplyingChannel hR).1.2
  rwa [log2_card_bool] at this

/-- Every element of the set under the right-hand `sSup` is at most `1`. -/
theorem hwBound_mem_le_one {r : ℝ}
    (hr : r ∈ { r : ℝ | ∃ (k : ℕ) (w α β : Fin k → ℝ),
      (∀ u, 0 ≤ w u) ∧ (∑ u, w u) = 1 ∧
      (∀ u, 0 ≤ α u ∧ α u ≤ 1) ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧
      let p : Fin k → ℝ := fun u => hwCrossover (α u) (β u)
      let r₁ := ∑ u, w u * (β u * binaryEntropy (α u) + (1 - β u) *
        (binaryEntropy ((1 - α u) * (1 - p u)) - (1 - α u) * binaryEntropy (p u)))
      let r₂ := ∑ u, w u * (α u * binaryEntropy (β u) + (1 - α u) *
        (binaryEntropy ((1 - β u) * p u) - (1 - β u) * binaryEntropy (p u)))
      let P₁ := ∑ u, w u * α u
      let P₂ := ∑ u, w u * β u
      let P₁₁ := ∑ u, w u * (α u * β u)
      r = min (min r₁ (P₂ * binaryEntropy (P₁₁ / P₂)))
              (min r₂ (P₁ * binaryEntropy (P₁₁ / P₁))) }) : r ≤ 1 := by
  obtain ⟨k, w, α, β, hw, hw1, hα, hβ, hr⟩ := hr
  simp only at hr
  rw [hr]
  refine (min_le_left _ _).trans ((min_le_right _ _).trans ?_)
  set P₂ := ∑ u, w u * β u
  set P₁₁ := ∑ u, w u * (α u * β u)
  have hP₂0 : 0 ≤ P₂ := Finset.sum_nonneg fun u _ => mul_nonneg (hw u) (hβ u).1
  have hP₂1 : P₂ ≤ 1 := by
    rw [← hw1]
    exact Finset.sum_le_sum fun u _ => mul_le_of_le_one_right (hw u) (hβ u).2
  have hP₁₁0 : 0 ≤ P₁₁ :=
    Finset.sum_nonneg fun u _ => mul_nonneg (hw u) (mul_nonneg (hα u).1 (hβ u).1)
  have hP₁₁P₂ : P₁₁ ≤ P₂ :=
    Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (hβ u).1 (hα u).2) (hw u)
  have hq0 : 0 ≤ P₁₁ / P₂ := div_nonneg hP₁₁0 hP₂0
  have hq1 : P₁₁ / P₂ ≤ 1 := div_le_one_of_le₀ hP₁₁P₂ hP₂0
  calc P₂ * binaryEntropy (P₁₁ / P₂) ≤ 1 * 1 :=
        mul_le_mul hP₂1 (binaryEntropy_le_one hq0 hq1) (binaryEntropy_nonneg hq0 hq1) zero_le_one
    _ = 1 := one_mul 1

theorem hwBound_set_bddAbove : BddAbove { r : ℝ | ∃ (k : ℕ) (w α β : Fin k → ℝ),
      (∀ u, 0 ≤ w u) ∧ (∑ u, w u) = 1 ∧
      (∀ u, 0 ≤ α u ∧ α u ≤ 1) ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧
      let p : Fin k → ℝ := fun u => hwCrossover (α u) (β u)
      let r₁ := ∑ u, w u * (β u * binaryEntropy (α u) + (1 - β u) *
        (binaryEntropy ((1 - α u) * (1 - p u)) - (1 - α u) * binaryEntropy (p u)))
      let r₂ := ∑ u, w u * (α u * binaryEntropy (β u) + (1 - α u) *
        (binaryEntropy ((1 - β u) * p u) - (1 - β u) * binaryEntropy (p u)))
      let P₁ := ∑ u, w u * α u
      let P₂ := ∑ u, w u * β u
      let P₁₁ := ∑ u, w u * (α u * β u)
      r = min (min r₁ (P₂ * binaryEntropy (P₁₁ / P₂)))
              (min r₂ (P₁ * binaryEntropy (P₁₁ / P₁))) } :=
  ⟨1, fun _ hr => hwBound_mem_le_one hr⟩

theorem bmcHWParallelChannelBound_le_one : bmcHWParallelChannelBound ≤ 1 := by
  unfold bmcHWParallelChannelBound
  exact Real.sSup_le (fun r hr => hwBound_mem_le_one hr) zero_le_one

/-- `h(1/4) = 2 - (3/4) log₂ 3 ≥ 1/2`. -/
theorem binaryEntropy_quarter_ge : 1 / 2 ≤ binaryEntropy (1 / 4) := by
  unfold binaryEntropy negPLogP log2
  simp only [show ¬ ((1 / 4 : ℝ) ≤ 0) by norm_num, show ¬ ((1 - 1 / 4 : ℝ) ≤ 0) by norm_num,
    ↓reduceIte]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e1 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast; ring
  have e2 : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 - 1 / 4 : ℝ) = 3 / (2 : ℝ) ^ 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have : Real.log 3 ≤ Real.log ((2 : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  rw [e1, e2]
  have key : -(1 / 4 : ℝ) * (-(2 * Real.log 2) / Real.log 2) +
      -(1 - 1 / 4) * ((Real.log 3 - 2 * Real.log 2) / Real.log 2) =
      2 - 3 / 4 * (Real.log 3 / Real.log 2) := by
    field_simp; ring
  rw [key]
  have : Real.log 3 / Real.log 2 ≤ 2 := by rw [div_le_iff₀ hl2]; linarith
  linarith

/-- **The right-hand side is at least `1/2`**: the point `|U| = 1`, `α = β = 1/2`. -/
theorem half_le_bmcHWParallelChannelBound : 1 / 2 ≤ bmcHWParallelChannelBound := by
  unfold bmcHWParallelChannelBound
  have hc : hwCrossover (1 / 2) (1 / 2) = 1 / 2 := by unfold hwCrossover; norm_num
  have hq := binaryEntropy_quarter_ge
  refine le_trans ?_ (le_csSup hwBound_set_bddAbove ⟨1, fun _ => 1, fun _ => 1 / 2,
    fun _ => 1 / 2, fun _ => zero_le_one, by simp, fun _ => by norm_num,
    fun _ => by norm_num, rfl⟩)
  simp only [Finset.univ_unique, Finset.sum_singleton, hc, one_mul]
  norm_num [binaryEntropy_half]
  exact hq

/-! ### Consistency with Schalkwijk's achievable rate -/

/-- `h(q)` in nats-over-`log 2` form, with the complement `r = 1 - q` supplied explicitly. -/
private lemma bmc_binaryEntropy_eq {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q + r = 1) :
    binaryEntropy q = -(q * Real.log q + r * Real.log r) / Real.log 2 := by
  have h1 : 1 - q = r := by linarith
  unfold binaryEntropy negPLogP log2
  rw [h1]
  simp only [not_le.mpr hq, not_le.mpr hr, ↓reduceIte]
  ring

private lemma bmc_log_mul_pow (a b : ℝ) (m n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a ^ m * b ^ n) = m * Real.log a + n * Real.log b := by
  rw [Real.log_mul (pow_pos ha m).ne' (pow_pos hb n).ne', Real.log_pow, Real.log_pow]

private lemma bmc_h_five_sixths : binaryEntropy (5 / 6) =
    1 + Real.log 3 / Real.log 2 - 5 / 6 * (Real.log 5 / Real.log 2) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [bmc_binaryEntropy_eq (r := 1 / 6) (by norm_num) (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_one, l6]
  field_simp; ring

private lemma bmc_h_one_sixth : binaryEntropy (1 / 6) =
    1 + Real.log 3 / Real.log 2 - 5 / 6 * (Real.log 5 / Real.log 2) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have l6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [bmc_binaryEntropy_eq (r := 5 / 6) (by norm_num) (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_one, l6]
  field_simp; ring

private lemma bmc_h_five_twelfths : binaryEntropy (5 / 12) =
    2 + Real.log 3 / Real.log 2 - 5 / 12 * (Real.log 5 / Real.log 2)
      - 7 / 12 * (Real.log 7 / Real.log 2) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have l12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 ^ 1 by norm_num, bmc_log_mul_pow _ _ _ _ (by norm_num)
      (by norm_num)]
    push_cast; ring
  rw [bmc_binaryEntropy_eq (r := 7 / 12) (by norm_num) (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), l12]
  field_simp; ring

private lemma bmc_h_one_thirtysixth : binaryEntropy (1 / 36) =
    2 + 2 * (Real.log 3 / Real.log 2) - 35 / 36 * (Real.log 5 / Real.log 2)
      - 35 / 36 * (Real.log 7 / Real.log 2) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have l36 : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
    rw [show (36 : ℝ) = 2 ^ 2 * 3 ^ 2 by norm_num, bmc_log_mul_pow _ _ _ _ (by norm_num)
      (by norm_num)]
    push_cast; ring
  have l35 : Real.log 35 = Real.log 5 + Real.log 7 := by
    rw [show (35 : ℝ) = 5 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [bmc_binaryEntropy_eq (r := 35 / 36) (by norm_num) (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_one, l36, l35]
  field_simp; ring

private lemma bmc_h_five_eighths : binaryEntropy (5 / 8) =
    3 - 3 / 8 * (Real.log 3 / Real.log 2) - 5 / 8 * (Real.log 5 / Real.log 2) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  rw [bmc_binaryEntropy_eq (r := 3 / 8) (by norm_num) (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), l8]
  field_simp; ring

/-- `log₂ a < m / n` from the integer comparison `a ^ n < 2 ^ m`. -/
private lemma bmc_log_div_log_two_lt {a : ℝ} (ha : 0 < a) {m n : ℕ} (hn : 0 < n)
    (h : a ^ n < (2 : ℝ) ^ m) : Real.log a / Real.log 2 < (m : ℝ) / n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have := Real.log_lt_log (pow_pos ha n) h
  rw [Real.log_pow, Real.log_pow] at this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ hl2 hn']
  linarith

/-- `m / n < log₂ a` from the integer comparison `2 ^ m < a ^ n`. -/
private lemma bmc_lt_log_div_log_two {a : ℝ} {m n : ℕ} (hn : 0 < n)
    (h : (2 : ℝ) ^ m < a ^ n) : (m : ℝ) / n < Real.log a / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have := Real.log_lt_log (pow_pos two_pos m) h
  rw [Real.log_pow, Real.log_pow] at this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ hn' hl2]
  linarith

/-- **Consistency with Schalkwijk's achievable rate**: `0.6191 < bmcHWParallelChannelBound`.
    Since `0.6191 ≤ C_sym` (Schalkwijk 1982), the frozen upper-bound formula must exceed it.
    Witness: `|U| = 2`, `w = (1/2, 1/2)`, `α = (1/2, 5/6)`, `β = (5/6, 1/2)` (crossovers `1/6`,
    `5/6`); the terms are `r₁ = r₂ = 5/4 + (3/4) log₂ 3 - (5/12) log₂ 5 - (7/24) log₂ 7 ≈ 0.65244`
    and `(2/3) h(5/8) = 2 - (1/4) log₂ 3 - (5/12) log₂ 5 ≈ 0.63629`. -/
theorem schalkwijk_lt_bmcHWParallelChannelBound : (0.6191 : ℝ) < bmcHWParallelChannelBound := by
  unfold bmcHWParallelChannelBound
  have hc1 : hwCrossover (1 / 2) (5 / 6) = 1 / 6 := by unfold hwCrossover; norm_num
  have hc2 : hwCrossover (5 / 6) (1 / 2) = 5 / 6 := by unfold hwCrossover; norm_num
  refine lt_of_lt_of_le ?_ (le_csSup hwBound_set_bddAbove ⟨2, fun _ => 1 / 2, ![1 / 2, 5 / 6],
    ![5 / 6, 1 / 2], fun _ => by norm_num, by norm_num [Fin.sum_univ_two],
    by simp [Fin.forall_fin_two]; norm_num, by simp [Fin.forall_fin_two]; norm_num, rfl⟩)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hc1, hc2]
  norm_num
  rw [binaryEntropy_half, bmc_h_five_sixths, bmc_h_one_sixth, bmc_h_five_twelfths,
    bmc_h_one_thirtysixth, bmc_h_five_eighths]
  -- `19/12 < log₂ 3 < 8/5`, `log₂ 5 < 7/3`, `log₂ 7 < 17/6`
  have hx1 := bmc_lt_log_div_log_two (a := 3) (m := 19) (n := 12) (by norm_num) (by norm_num)
  have hx2 := bmc_log_div_log_two_lt (a := 3) (m := 8) (n := 5) (by norm_num) (by norm_num)
    (by norm_num)
  have hy := bmc_log_div_log_two_lt (a := 5) (m := 7) (n := 3) (by norm_num) (by norm_num)
    (by norm_num)
  have hz := bmc_log_div_log_two_lt (a := 7) (m := 17) (n := 6) (by norm_num) (by norm_num)
    (by norm_num)
  push_cast at hx1 hx2 hy hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### Time division -/

/-- The binary multiplying channel is deterministic. -/
theorem bmc_trans_ne_zero {x : Bool × Bool} {y : Bool × Bool}
    (h : binaryMultiplyingChannel.trans x y ≠ 0) : y = (x.1 && x.2, x.1 && x.2) := by
  by_contra hne
  exact h (by simp [binaryMultiplyingChannel, hne])

/-- **Time division achieves `(R, R)` for every `R < 1/2`** (zero-error code). -/
theorem isTWCAchievable_timeDivision {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 2) :
    IsTWCAchievable binaryMultiplyingChannel R R := by
  classical
  refine ⟨hR0, hR0, fun ε hε => ?_⟩
  -- large `n`: `2^{nR} ≤ 2^{⌊n/2⌋}`
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 / 2 - R))
  refine ⟨N, fun n hn => ?_⟩
  dsimp only
  set M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  haveI : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
  set h := n / 2 with hh
  have h2h : 2 * h ≤ n := by omega
  have hcard : Fintype.card (Fin M) ≤ Fintype.card (Fin h → Bool) := by
    rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hhr : ((n : ℝ) - 1) / 2 ≤ (h : ℝ) := by
      have : n ≤ 2 * h + 1 := by omega
      have : (n : ℝ) ≤ 2 * (h : ℝ) + 1 := by exact_mod_cast this
      linarith
    have hexp : (n : ℝ) * R ≤ h := by
      have hgap : 0 < 1 / 2 - R := by linarith
      have : 1 < (n : ℝ) * (1 / 2 - R) := by
        rw [div_lt_iff₀ hgap] at hN
        nlinarith
      nlinarith
    apply max_le
    · exact Nat.one_le_two_pow
    · apply Nat.floor_le_of_le
      push_cast
      calc (2 : ℝ) ^ ((n : ℝ) * R) ≤ (2 : ℝ) ^ (h : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (2 : ℝ) ^ h := Real.rpow_natCast 2 h
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hι : ∀ m, Function.invFun ι (ι m) = m := Function.leftInverse_invFun ι.injective
  -- user 1 talks in slots `[0, h)`, user 2 in slots `[h, 2h)`
  let a : Fin M → Fin n → Bool := fun m i => if hi : i.1 < h then ι m ⟨i.1, hi⟩ else true
  let b : Fin M → Fin n → Bool := fun m i =>
    if hi : h ≤ i.1 ∧ i.1 < 2 * h then ι m ⟨i.1 - h, by omega⟩ else true
  refine ⟨fun i m _ => a m i, fun i m _ => b m i,
    fun _ y₁ => Function.invFun ι (fun j : Fin h => y₁ ⟨h + j.1, by omega⟩),
    fun _ y₂ => Function.invFun ι (fun j : Fin h => y₂ ⟨j.1, by omega⟩), ?_⟩
  have hzero : ∀ (m₁ m₂ : Fin M) (y : Fin n → Bool × Bool),
      (if Function.invFun ι (fun j : Fin h => (y ⟨h + j.1, by omega⟩).1) ≠ m₂ ∨
          Function.invFun ι (fun j : Fin h => (y ⟨j.1, by omega⟩).2) ≠ m₁ then
        ∏ i : Fin n, binaryMultiplyingChannel.trans (a m₁ i, b m₂ i) (y i) else 0) = 0 := by
    intro m₁ m₂ y
    split_ifs with hc
    · by_contra hp
      have hy : ∀ i, y i = (a m₁ i && b m₂ i, a m₁ i && b m₂ i) := fun i =>
        bmc_trans_ne_zero (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _))
      rcases hc with hne | hne
      · apply hne
        have : (fun j : Fin h => (y ⟨h + j.1, by omega⟩).1) = ι m₂ := by
          funext j
          rw [hy]
          have h1 : ¬ (h + j.1 < h) := by omega
          have h2 : h ≤ h + j.1 ∧ h + j.1 < 2 * h := by omega
          simp [a, b, h1, h2]
        rw [this, hι]
      · apply hne
        have : (fun j : Fin h => (y ⟨j.1, by omega⟩).2) = ι m₁ := by
          funext j
          rw [hy]
          have h1 : j.1 < h := j.2
          have h2 : ¬ (h ≤ j.1 ∧ j.1 < 2 * h) := by omega
          simp [a, b, h1, h2]
        rw [this, hι]
    · rfl
  have hsum : ∑ m₁ : Fin M, ∑ m₂ : Fin M, ∑ y : Fin n → Bool × Bool,
      (if Function.invFun ι (fun j : Fin h => (y ⟨h + j.1, by omega⟩).1) ≠ m₂ ∨
          Function.invFun ι (fun j : Fin h => (y ⟨j.1, by omega⟩).2) ≠ m₁ then
        ∏ i : Fin n, binaryMultiplyingChannel.trans (a m₁ i, b m₂ i) (y i) else 0) = 0 :=
    Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ =>
      Finset.sum_eq_zero fun y _ => hzero m₁ m₂ y
  refine le_trans (le_of_eq ?_) hε.le
  calc _ = (1 / ((M * M : ℕ) : ℝ)) * 0 := congrArg (HMul.hMul ((1 : ℝ) / ((M * M : ℕ) : ℝ))) hsum
    _ = 0 := mul_zero _

/-- **Time-division lower bound**: `1/2 ≤ bmcSymmetricCapacity`. -/
theorem half_le_bmcSymmetricCapacity : 1 / 2 ≤ bmcSymmetricCapacity := by
  unfold bmcSymmetricCapacity
  have hbdd : BddAbove { R : ℝ | (R, R) ∈ twcCapacityRegion binaryMultiplyingChannel } :=
    ⟨1, fun R hR => by
      have := (twcCapacityRegion_subset_box binaryMultiplyingChannel hR).1.2
      rwa [log2_card_bool] at this⟩
  -- `(R, R)` is achievable for `R < 1/2`, so `(1/2, 1/2)` is in the closed region
  have hmem : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ twcCapacityRegion binaryMultiplyingChannel := by
    have hsub : (fun R : ℝ => (R, R)) '' Set.Ico 0 (1 / 2) ⊆
        { p : ℝ × ℝ | IsTWCAchievable binaryMultiplyingChannel p.1 p.2 } := by
      rintro _ ⟨R, ⟨h0, h1⟩, rfl⟩
      exact isTWCAchievable_timeDivision h0 h1
    have hcont : Continuous (fun R : ℝ => (R, R)) := continuous_id.prodMk continuous_id
    have h1 : (1 / 2 : ℝ) ∈ closure (Set.Ico (0 : ℝ) (1 / 2)) := by
      rw [closure_Ico (by norm_num)]
      exact ⟨by norm_num, le_rfl⟩
    have h2 := map_mem_closure hcont h1 (fun x hx => subset_closure (hsub ⟨x, hx, rfl⟩))
    rw [closure_closure] at h2
    exact h2
  exact le_csSup hbdd hmem

theorem bmcSymmetricCapacity_mem_Icc : bmcSymmetricCapacity ∈ Set.Icc (1 / 2) 1 :=
  ⟨half_le_bmcSymmetricCapacity, bmcSymmetricCapacity_le_one⟩

theorem bmcHWParallelChannelBound_mem_Icc : bmcHWParallelChannelBound ∈ Set.Icc (1 / 2) 1 :=
  ⟨half_le_bmcHWParallelChannelBound, bmcHWParallelChannelBound_le_one⟩

end InfoTheory.Known.Certificates.BinaryMultiplierTwoWayChannel
