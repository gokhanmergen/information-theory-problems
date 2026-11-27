import InfoTheory.Problems.BinaryMultiplierTwoWayChannel
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.TwoWayChannelCapacity

/-!
# Certificate for `InfoTheory.Problems.BinaryMultiplierTwoWayChannel`

The frozen statement asks whether the symmetric capacity `bmcSymmetricCapacity` of Blackwell's
binary multiplying channel `Y₁ = Y₂ = X₁ · X₂` equals the Hekstra–Willems dependence-balance
bound `bmcDependenceBalanceBound`.

**Frozen `Statement` is false (on paper; catalog error, statement-fix pending).** For a
deterministic channel the *plain* dependence-balance constraint is vacuous, so
`bmcDependenceBalanceBound = log₂ φ ≈ 0.69424` (Shannon's outer bound), while
Zhang–Berger–Schalkwijk give `C_sym ≤ 0.64891`. The value `≈ 0.64628` belongs to the
Hekstra–Willems bound *with an adaptive parallel channel*. See
`problems/binary-multiplier-two-way-channel.md` and
`attempts/binary-multiplier-two-way-channel/2026-11-26-claude-opus-5-5-db-catalog-error-survey.md`.
The facts below remain true.

## Certified (about exactly these objects)
* `isTWCAchievable_timeDivision`, `half_le_bmcSymmetricCapacity` — **time division**: for every
  `R < 1/2` the pair `(R, R)` is achievable with zero error (terminal 1 sends raw bits in the
  first `⌊n/2⌋` slots while terminal 2 sends `1`, then they swap roles), so
  `1/2 ≤ bmcSymmetricCapacity`.
* `bmcSymmetricCapacity_le_one` — `bmcSymmetricCapacity ≤ 1` (counting converse
  `TwoWayChannelCapacity.twcCapacityRegion_subset_box`, `log₂ |Y| = 1`). With the previous item
  the left-hand side lies in `[1/2, 1]`; in particular the `sSup` is over a nonempty set that
  is bounded above.
* `bmcDependenceBalanceBound_nonneg`, `bmcDependenceBalanceBound_le_one` — the right-hand side
  lies in `[0, 1]` (it is a supremum of minima of conditional mutual informations of binary
  variables).

## Not certified
* Shannon's inner bound `≥ 0.6160` and Schalkwijk's `0.6191` (adaptive coding strategies; no
  two-way-channel achievability in the library).
* That the dependence-balance bound is a valid upper bound on the symmetric capacity
  (Hekstra–Willems 1989 converse) and its value `log₂ φ ≈ 0.69424`; also the lower bound `≥ 1/2`
  for it (it needs explicit entropy evaluations). A cheap step toward `statement_false`:
  certify `bmcDependenceBalanceBound > 0.649` with an explicit input law (the ZBS upper
  bound `0.64891` on the left-hand side is research-level and not in the library).
* No *Lean* statement-level conclusion; the frozen statement is false on paper (above), and
  the intended mathematical question (tightness of the adaptive Hekstra–Willems bound) is open.

Sources: Shannon 1961; Schalkwijk, IEEE Trans. IT 1982/1983; Hekstra–Willems, IEEE Trans. IT
1989.
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

theorem bmcDependenceBalanceBound_nonneg : 0 ≤ bmcDependenceBalanceBound := by
  unfold bmcDependenceBalanceBound
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨kZ, P, -, rfl⟩ := hr
  exact le_min (condMutualInfo_nonneg _) (condMutualInfo_nonneg _)

theorem bmcDependenceBalanceBound_le_one : bmcDependenceBalanceBound ≤ 1 := by
  unfold bmcDependenceBalanceBound
  refine Real.sSup_le (fun r hr => ?_) zero_le_one
  obtain ⟨kZ, P, -, rfl⟩ := hr
  exact min_le_of_left_le ((condMutualInfo_le_log2_card _).trans (le_of_eq log2_card_bool))

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

theorem bmcDependenceBalanceBound_mem_Icc : bmcDependenceBalanceBound ∈ Set.Icc 0 1 :=
  ⟨bmcDependenceBalanceBound_nonneg, bmcDependenceBalanceBound_le_one⟩

end InfoTheory.Known.Certificates.BinaryMultiplierTwoWayChannel
