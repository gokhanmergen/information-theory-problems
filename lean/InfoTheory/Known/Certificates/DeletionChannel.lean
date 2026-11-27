import InfoTheory.Problems.DeletionChannel
import InfoTheory.Problems.DeletionChannelHighDLimit
import InfoTheory.Problems.DeletionChannelSmallDAsymptotics
import InfoTheory.Known

/-!
# Certificate for the binary deletion channel problems

Shared certificate for `InfoTheory.Problems.DeletionChannel` (convexity of `C(d)`),
`InfoTheory.Problems.DeletionChannelHighDLimit` (`L = inf_{d∈(0,1)} C(d)/(1-d) ≤ 1/4`) and
`InfoTheory.Problems.DeletionChannelSmallDAsymptotics` (power series of `C(d) - (1 - h(d))`
with leading coefficient `kanoriaMontanariC1`). References: Dobrushin, "Shannon's theorems for
channels with synchronization errors", Probl. Inf. Transm. 3(4), 1967; Mitzenmacher, "A survey
of results for deletion channels and related synchronization channels", Probab. Surveys 6,
2009; Kanoria–Montanari, "Optimal coding for the binary deletion channel with small deletion
probability", IEEE Trans. Inf. Theory 59(10), 2013.

## Certified
* `DeletionChannel`: `capacity_mem_Icc` (`0 ≤ C(d) ≤ 1 - d` on `d ≤ 1`, reusing
  `Known.binaryDeletionCapacity_nonneg` / `_le_one_sub`), `capacity_zero` (`C(0) = 1`),
  `capacity_one` (`C(1) = 0`). These are the elementary facts the convexity Statement relies
  on; they show `binaryDeletionCapacity` takes genuine values (not `sInf ∅ = 0` junk) at
  both endpoints.
* `DeletionChannelHighDLimit`: `highDeletionLimit_set_nonempty`, `_set_bddBelow`,
  `highDeletionLimit_le_ratio` (`L ≤ C(d)/(1-d)` for each `d ∈ (0,1)`),
  `highDeletionLimit_nonneg`, `highDeletionLimit_le_one`: `L ∈ [0, 1]`, and the `sInf` is a
  genuine infimum.
* `DeletionChannelSmallDAsymptotics`: `kanoriaMontanari_summable` (the series in
  `kanoriaMontanariC1` converges, so the `tsum` is not the junk value `0`) and
  `kanoriaMontanariC1_pos` (`c₁ > 0`; numerically `c₁ ≈ 0.2885`, Kanoria–Montanari 2013,
  where `A₁ = log₂(2e) - ∑_{ℓ≥1} 2^{-ℓ-1} ℓ log₂ ℓ ≈ 1.1542` and `c₁ = log₂ e - A₁`). With
  junk `tsum = 0` one would get `c₁ = -1`.

## Not certified
* The literature bounds `0.1185 ≤ L ≤ 0.3745` (Drinea–Mitzenmacher 2007; Rahmati–Duman 2015),
  Dalai's identification of `L` with `lim_{d→1} C(d)/(1-d)`, the lower bound
  `C(d) ≥ 1 - h(d)` (Gallager 1961; Zigangirov 1969) and the Kanoria–Montanari expansion
  itself are out of scope.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.DeletionChannel

open InfoTheory

/-! ### `DeletionChannel` -/

/-- `0 ≤ C(d) ≤ 1 - d` for `d ≤ 1` (Mitzenmacher 2009, §2: erasure-channel upper bound). -/
theorem capacity_mem_Icc {d : ℝ} (h1 : d ≤ 1) :
    0 ≤ binaryDeletionCapacity d ∧ binaryDeletionCapacity d ≤ 1 - d :=
  ⟨binaryDeletionCapacity_nonneg d, binaryDeletionCapacity_le_one_sub h1⟩

/-- `C(0) = 1` (noiseless channel). -/
theorem capacity_zero : binaryDeletionCapacity 0 = 1 := binaryDeletionCapacity_zero

/-- `C(1) = 0` (everything is deleted). -/
theorem capacity_one : binaryDeletionCapacity 1 = 0 :=
  le_antisymm (by simpa using binaryDeletionCapacity_le_one_sub (le_refl (1 : ℝ)))
    (binaryDeletionCapacity_nonneg 1)

/-! ### `DeletionChannelHighDLimit` -/

open InfoTheory.Problems.DeletionChannelHighDLimit

/-- The set defining `highDeletionLimit`. -/
def ratioSet : Set ℝ :=
  { r : ℝ | ∃ d : ℝ, 0 < d ∧ d < 1 ∧ r = binaryDeletionCapacity d / (1 - d) }

lemma highDeletionLimit_eq : highDeletionLimit = sInf ratioSet := rfl

theorem highDeletionLimit_set_nonempty : ratioSet.Nonempty :=
  ⟨_, 1 / 2, by norm_num, by norm_num, rfl⟩

lemma ratio_nonneg {d : ℝ} (hd1 : d < 1) : 0 ≤ binaryDeletionCapacity d / (1 - d) :=
  div_nonneg (binaryDeletionCapacity_nonneg d) (by linarith)

lemma ratio_le_one {d : ℝ} (hd1 : d < 1) : binaryDeletionCapacity d / (1 - d) ≤ 1 :=
  (div_le_one (by linarith)).2 (binaryDeletionCapacity_le_one_sub hd1.le)

theorem highDeletionLimit_set_bddBelow : BddBelow ratioSet :=
  ⟨0, fun _ ⟨_, _, hd1, hr⟩ => hr ▸ ratio_nonneg hd1⟩

/-- `L ≤ C(d)/(1-d)` for every `d ∈ (0, 1)`: the `sInf` is a genuine infimum. -/
theorem highDeletionLimit_le_ratio {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) :
    highDeletionLimit ≤ binaryDeletionCapacity d / (1 - d) :=
  csInf_le highDeletionLimit_set_bddBelow ⟨d, hd0, hd1, rfl⟩

/-- `L ≥ 0`. -/
theorem highDeletionLimit_nonneg : 0 ≤ highDeletionLimit :=
  le_csInf highDeletionLimit_set_nonempty (fun _ ⟨_, _, hd1, hr⟩ => hr ▸ ratio_nonneg hd1)

/-- `L ≤ 1` (from `C(d) ≤ 1 - d`). -/
theorem highDeletionLimit_le_one : highDeletionLimit ≤ 1 :=
  (highDeletionLimit_le_ratio (d := 1 / 2) (by norm_num) (by norm_num)).trans
    (ratio_le_one (by norm_num))

/-! ### `DeletionChannelSmallDAsymptotics` -/

open InfoTheory.Problems.DeletionChannelSmallDAsymptotics

/-- The summand of `kanoriaMontanariC1`. -/
noncomputable def kmTerm (l : ℕ) : ℝ :=
  ((1 : ℝ) / ((2 : ℝ) ^ (l + 2))) * ((l + 1 : ℕ) : ℝ) * log2 ((l + 1 : ℕ) : ℝ)

lemma kanoriaMontanariC1_eq : kanoriaMontanariC1 = (∑' l, kmTerm l) - 1 := rfl

private lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num); norm_num at this ⊢
  linarith

lemma log2_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  div_nonneg (Real.log_nonneg hx) (Real.log_pos one_lt_two).le

lemma log2_le_two_mul {x : ℝ} (hx : 1 ≤ x) : log2 x ≤ 2 * x := by
  unfold log2
  have hl2 := log_two_ge_half
  rw [div_le_iff₀ (by linarith)]
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
  nlinarith

lemma kmTerm_nonneg (l : ℕ) : 0 ≤ kmTerm l := by
  unfold kmTerm
  refine mul_nonneg (by positivity) (log2_nonneg_of_one_le ?_)
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le l)

lemma kmTerm_le (l : ℕ) : kmTerm l ≤ ((l : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ l := by
  unfold kmTerm
  have hx : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le l)
  have hlog := log2_le_two_mul hx
  push_cast at hlog ⊢
  have h2 : (0 : ℝ) < 2 ^ (l + 2) := by positivity
  rw [one_div_pow, pow_add]
  have hpos : (0 : ℝ) < 2 ^ l := by positivity
  rw [show (1 : ℝ) / (2 ^ l * 2 ^ 2) * ((l : ℝ) + 1) * log2 ((l : ℝ) + 1) =
    ((l : ℝ) + 1) * log2 ((l : ℝ) + 1) / (4 * 2 ^ l) by field_simp; ring]
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- **The Kanoria–Montanari series converges**, so `kanoriaMontanariC1` is a genuine sum
(not the `tsum` junk value). -/
theorem kanoriaMontanari_summable : Summable kmTerm := by
  have hgeom : Summable (fun l : ℕ => ((l : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ l) := by
    have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
      (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
      (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    have := (h2.add (h1.mul_left 2)).add h0
    refine this.congr (fun l => ?_)
    simp only [pow_zero, one_mul, pow_one]
    ring
  exact Summable.of_nonneg_of_le kmTerm_nonneg kmTerm_le hgeom

/-- **`c₁ > 0`** (Kanoria–Montanari 2013: `c₁ ≈ 0.2885`). Lower bound from the first seven
terms (`ℓ = 2, …, 8`) with `log₂ 2 = 1`, `log₂ 3 ≥ 1`, `log₂ k ≥ 2` for `k ≥ 4`:
`1/4 + 3/16 + 1/4 + 10/64 + 12/128 + 14/256 + 16/512 > 1`. -/
theorem kanoriaMontanariC1_pos : 0 < kanoriaMontanariC1 := by
  rw [kanoriaMontanariC1_eq, sub_pos]
  have hpart : ∑ l ∈ Finset.range 8, kmTerm l ≤ ∑' l, kmTerm l :=
    kanoriaMontanari_summable.sum_le_tsum _ (fun l _ => kmTerm_nonneg l)
  have hl1 : log2 1 = 0 := by simp [log2]
  have hl2 : log2 2 = 1 := div_self (Real.log_pos one_lt_two).ne'
  have hl4 : log2 4 = 2 := by
    unfold log2
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    field_simp [(Real.log_pos one_lt_two).ne']
    norm_num
  have mono : ∀ {x y : ℝ}, 0 < x → x ≤ y → log2 x ≤ log2 y := fun hx hxy =>
    div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos one_lt_two).le
  have h3 : 1 ≤ log2 3 := hl2 ▸ mono (by norm_num) (by norm_num)
  have h5 : 2 ≤ log2 5 := hl4 ▸ mono (by norm_num) (by norm_num)
  have h6 : 2 ≤ log2 6 := hl4 ▸ mono (by norm_num) (by norm_num)
  have h7 : 2 ≤ log2 7 := hl4 ▸ mono (by norm_num) (by norm_num)
  have h8 : 2 ≤ log2 8 := hl4 ▸ mono (by norm_num) (by norm_num)
  have hsum : 1 < ∑ l ∈ Finset.range 8, kmTerm l := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, kmTerm]
    norm_num
    rw [hl1, hl2, hl4]
    nlinarith [h3, h5, h6, h7, h8]
  linarith

end InfoTheory.Known.Certificates.DeletionChannel
