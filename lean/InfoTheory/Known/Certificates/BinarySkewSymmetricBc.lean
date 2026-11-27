import InfoTheory.Problems.BinarySkewSymmetricBc
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.BroadcastChannel

/-!
# Certificate for `InfoTheory.Problems.BinarySkewSymmetricBc`

The frozen statement asks whether the operational sum-rate capacity `bsscSumCapacity` of the
binary skew-symmetric broadcast channel (BSSC) equals the maximal Marton sum rate
`bsscMartonSumRate`.

## Certified (about exactly these objects)
* `zChannel₁_capacity`, `zChannel₂_capacity` — each marginal of `binarySkewSymmetricBC` is a
  Z-channel with capacity **`C_Z = log₂(5/4)`** (problem file, "What is known"; the maximum of
  `h(q/2) - q` at `q = 2/5`). The upper bound is a Gibbs-inequality argument against the
  output law `Bern(1/5)` (`negMulLog_add_le`).
* `bsscSumCapacity_mem_Icc`, `bsscMartonSumRate_mem_Icc` — **both sides of the statement lie
  in `[log₂(5/4), 2 log₂(5/4)] ≈ [0.3219, 0.6439]`**. The lower bounds are the axis corner
  points `(C_Z, 0)` (operational: Shannon's theorem for the marginal,
  `Known.Operational.mk_zero_mem_bcCapacityRegion_iff`; Marton: `U = X`, certificate
  `BroadcastChannel.mk_zero_mem_martonInnerBound_iff`). The upper bounds come from the box
  outer bound `[0, C_Z]²` satisfied by both regions. In particular both `sSup`s are over
  nonempty sets that are bounded above, so neither side is a junk value.

## Not certified
* The value `≈ 0.3616428` of Marton's sum rate (Nair–Wang–Geng 2010; it needs their
  information inequality and a numerical optimisation), and the UV upper bound `≈ 0.37256`.
* That time sharing between the two corners is achievable (would give `≥ log₂(5/4)` only;
  no improvement on the lower bound proved here).
* No statement-level conclusion: the problem is open.

Sources: Hajek–Pursley, IEEE Trans. IT 1979; Nair–Wang–Geng, ISIT 2010;
El Gamal–Kim, *Network Information Theory*, §8.3.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BinarySkewSymmetricBc

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.BinarySkewSymmetricBc
open InfoTheory.Known.Certificates.BroadcastChannel (martonInnerBound_subset_box
  mk_zero_mem_martonInnerBound_iff)

/-! ### Elementary logarithm facts -/

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

lemma log2_five_fourths : log2 (5 / 4) = (Real.log 5 - 2 * Real.log 2) / Real.log 2 := by
  unfold log2
  rw [Real.log_div (by norm_num) (by norm_num), log_four]

lemma log2_five_fourths_pos : 0 < log2 (5 / 4) := by
  unfold log2
  exact div_pos (Real.log_pos (by norm_num)) log_two_pos

lemma negPLogP_half : negPLogP (1 / 2) = 1 / 2 := by
  unfold negPLogP log2
  rw [ite_eq_right (by norm_num : ¬ (1 / 2 : ℝ) ≤ 0), one_div, Real.log_inv]
  field_simp [log_two_pos.ne']

lemma negPLogP_one : negPLogP 1 = 0 := by simp [negPLogP, log2]

lemma negPLogP_zero : negPLogP 0 = 0 := by simp [negPLogP]

/-- **Tilted Gibbs inequality** (nats): for `s ∈ [0, 1]`,
    `-s ln s - (1-s) ln(1-s) ≤ s ln 5 + (1-s) ln(5/4)` (relative entropy to `Bern(1/5)` is
    nonnegative). -/
theorem negMulLog_add_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.negMulLog s + Real.negMulLog (1 - s) ≤
      s * Real.log 5 + (1 - s) * Real.log (5 / 4) := by
  have g1 := gibbs_term (p := s) (q := 1 / 5) (by norm_num) (fun _ => by norm_num)
  have g2 := gibbs_term (p := 1 - s) (q := 4 / 5) (by norm_num) (fun _ => by norm_num)
  have e1 : (if s ≤ 0 then 0 else s * Real.log (s / (1 / 5))) =
      s * (Real.log 5 + Real.log s) := by
    split_ifs with h
    · have : s = 0 := le_antisymm h hs0
      simp [this]
    · have hs : 0 < s := lt_of_not_ge h
      rw [show s / (1 / 5) = 5 * s by ring, Real.log_mul (by norm_num) hs.ne']
  have e2 : (if 1 - s ≤ 0 then 0 else (1 - s) * Real.log ((1 - s) / (4 / 5))) =
      (1 - s) * (Real.log (5 / 4) + Real.log (1 - s)) := by
    split_ifs with h
    · have : 1 - s = 0 := le_antisymm h (by linarith)
      simp [this]
    · have hs : 0 < 1 - s := lt_of_not_ge h
      rw [show (1 - s) / (4 / 5) = 5 / 4 * (1 - s) by ring,
        Real.log_mul (by norm_num) hs.ne']
  rw [e1] at g1
  rw [e2] at g2
  unfold Real.negMulLog
  nlinarith

/-! ### The two Z-channel marginals -/

/-- Receiver 1 sees a Z-channel: `0 → 0`, `1 → Unif{0, 1}`. -/
theorem zChannel₁_trans (x y : Bool) :
    (marginalFst binarySkewSymmetricBC).trans x y =
      if x = false then (if y = false then 1 else 0) else 1 / 2 := by
  cases x <;> cases y <;> simp [marginalFst, binarySkewSymmetricBC] <;> norm_num

/-- Receiver 2 sees the reversed Z-channel: `1 → 1`, `0 → Unif{0, 1}`. -/
theorem zChannel₂_trans (x y : Bool) :
    (marginalSnd binarySkewSymmetricBC).trans x y =
      if x = true then (if y = true then 1 else 0) else 1 / 2 := by
  cases x <;> cases y <;> simp [marginalSnd, binarySkewSymmetricBC]

/-- `I(X; Y₁) = h(q/2) - q` with `q = P(X = 1)`. -/
theorem zChannel₁_mutualInfo (P : ProbDist Bool) :
    (marginalFst binarySkewSymmetricBC).mutualInfo P =
      negPLogP (P.pmf true / 2) + negPLogP (1 - P.pmf true / 2) - P.pmf true := by
  have hs : P.pmf true + P.pmf false = 1 := by rw [← Fintype.sum_bool]; exact P.sum_one
  rw [mutualInfo_eq_entropy_output_sub]
  unfold shannonEntropy
  have hf : P.pmf false = 1 - P.pmf true := by linarith
  simp only [joint_snd_pmf, Fintype.sum_bool, zChannel₁_trans]
  simp only [ite_true, Bool.true_eq_false, ite_false, mul_one, mul_zero,
    zero_add, add_zero, negPLogP_half, negPLogP_one, negPLogP_zero, hf]
  ring_nf

/-- `I(X; Y₂) = h(q'/2) - q'` with `q' = P(X = 0)`. -/
theorem zChannel₂_mutualInfo (P : ProbDist Bool) :
    (marginalSnd binarySkewSymmetricBC).mutualInfo P =
      negPLogP (P.pmf false / 2) + negPLogP (1 - P.pmf false / 2) - P.pmf false := by
  have hs : P.pmf true + P.pmf false = 1 := by rw [← Fintype.sum_bool]; exact P.sum_one
  rw [mutualInfo_eq_entropy_output_sub]
  unfold shannonEntropy
  have ht : P.pmf true = 1 - P.pmf false := by linarith
  simp only [joint_snd_pmf, Fintype.sum_bool, zChannel₂_trans]
  simp only [ite_true, Bool.true_eq_false, ite_false, Bool.false_eq_true, mul_one, mul_zero,
    zero_add, add_zero, negPLogP_half, negPLogP_one, negPLogP_zero, ht]
  ring_nf

/-- The key bound `h(q/2) - q ≤ log₂(5/4)` for `q ∈ [0, 1]`. -/
theorem zObjective_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    negPLogP (q / 2) + negPLogP (1 - q / 2) - q ≤ log2 (5 / 4) := by
  rw [negPLogP_eq_negMulLog (by linarith), negPLogP_eq_negMulLog (by linarith),
    log2_five_fourths]
  have h := negMulLog_add_le (s := q / 2) (by linarith) (by linarith)
  rw [Real.log_div (by norm_num) (by norm_num), log_four] at h
  have key : Real.negMulLog (q / 2) + Real.negMulLog (1 - q / 2) - q * Real.log 2 ≤
      Real.log 5 - 2 * Real.log 2 := by linarith
  rw [show Real.negMulLog (q / 2) / Real.log 2 + Real.negMulLog (1 - q / 2) / Real.log 2 - q =
      (Real.negMulLog (q / 2) + Real.negMulLog (1 - q / 2) - q * Real.log 2) / Real.log 2 by
    field_simp]
  exact div_le_div_of_nonneg_right key log_two_pos.le

/-- The objective at `q = 2/5` equals `log₂(5/4)`. -/
theorem zObjective_two_fifths :
    negPLogP ((2 / 5 : ℝ) / 2) + negPLogP (1 - (2 / 5 : ℝ) / 2) - 2 / 5 = log2 (5 / 4) := by
  rw [show (2 / 5 : ℝ) / 2 = 1 / 5 by norm_num, show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num]
  unfold negPLogP log2
  rw [ite_eq_right (by norm_num : ¬ (1 / 5 : ℝ) ≤ 0), ite_eq_right (by norm_num : ¬ (4 / 5 : ℝ) ≤ 0),
    Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    log_four, Real.log_one]
  field_simp
  ring

/-- **Capacity of receiver 1's Z-channel**: `C_Z = log₂(5/4)`. -/
theorem zChannel₁_capacity : (marginalFst binarySkewSymmetricBC).capacity = log2 (5 / 4) := by
  refine capacity_eq_of_le_of_eq _ (fun P => ?_) (ProbDist.bernoulli (2 / 5) (by norm_num)
    (by norm_num)) ?_
  · rw [zChannel₁_mutualInfo]
    exact zObjective_le (P.nonneg _) (by
      have hs : P.pmf true + P.pmf false = 1 := by rw [← Fintype.sum_bool]; exact P.sum_one
      linarith [P.nonneg false])
  · rw [zChannel₁_mutualInfo]
    simpa [ProbDist.bernoulli] using zObjective_two_fifths

/-- **Capacity of receiver 2's Z-channel**: `C_Z = log₂(5/4)`. -/
theorem zChannel₂_capacity : (marginalSnd binarySkewSymmetricBC).capacity = log2 (5 / 4) := by
  refine capacity_eq_of_le_of_eq _ (fun P => ?_) (ProbDist.bernoulli (3 / 5) (by norm_num)
    (by norm_num)) ?_
  · rw [zChannel₂_mutualInfo]
    exact zObjective_le (P.nonneg _) (by
      have hs : P.pmf true + P.pmf false = 1 := by rw [← Fintype.sum_bool]; exact P.sum_one
      linarith [P.nonneg true])
  · rw [zChannel₂_mutualInfo]
    have : (ProbDist.bernoulli (3 / 5) (by norm_num) (by norm_num)).pmf false = 2 / 5 := by
      simp [ProbDist.bernoulli]; norm_num
    rw [this]
    exact zObjective_two_fifths

/-! ### Both sides of the statement lie in `[C_Z, 2 C_Z]` -/

/-- Both regions lie in the box `[0, C_Z]²`. -/
theorem sum_le_of_mem_box {p : ℝ × ℝ}
    (hp : p ∈ Set.Icc 0 (marginalFst binarySkewSymmetricBC).capacity ×ˢ
      Set.Icc 0 (marginalSnd binarySkewSymmetricBC).capacity) :
    p.1 + p.2 ≤ 2 * log2 (5 / 4) := by
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hp
  rw [zChannel₁_capacity] at h1
  rw [zChannel₂_capacity] at h2
  linarith

theorem bsscSumCapacity_le : bsscSumCapacity ≤ 2 * log2 (5 / 4) := by
  unfold bsscSumCapacity
  refine Real.sSup_le (fun s hs => ?_) (by linarith [log2_five_fourths_pos])
  obtain ⟨p, hp, rfl⟩ := hs
  exact sum_le_of_mem_box (bcCapacityRegion_subset_Icc_prod_Icc _ hp)

theorem le_bsscSumCapacity : log2 (5 / 4) ≤ bsscSumCapacity := by
  unfold bsscSumCapacity
  refine le_csSup ⟨2 * log2 (5 / 4), fun s hs => ?_⟩ ⟨(log2 (5 / 4), 0), ?_, by simp⟩
  · obtain ⟨p, hp, rfl⟩ := hs
    exact sum_le_of_mem_box (bcCapacityRegion_subset_Icc_prod_Icc _ hp)
  · rw [mk_zero_mem_bcCapacityRegion_iff, zChannel₁_capacity]
    exact ⟨log2_five_fourths_pos.le, le_rfl⟩

theorem bsscMartonSumRate_le : bsscMartonSumRate ≤ 2 * log2 (5 / 4) := by
  unfold bsscMartonSumRate
  refine Real.sSup_le (fun s hs => ?_) (by linarith [log2_five_fourths_pos])
  obtain ⟨p, hp, rfl⟩ := hs
  exact sum_le_of_mem_box (martonInnerBound_subset_box _ hp)

theorem le_bsscMartonSumRate : log2 (5 / 4) ≤ bsscMartonSumRate := by
  unfold bsscMartonSumRate
  refine le_csSup ⟨2 * log2 (5 / 4), fun s hs => ?_⟩ ⟨(log2 (5 / 4), 0), ?_, by simp⟩
  · obtain ⟨p, hp, rfl⟩ := hs
    exact sum_le_of_mem_box (martonInnerBound_subset_box _ hp)
  · rw [mk_zero_mem_martonInnerBound_iff, zChannel₁_capacity]
    exact ⟨log2_five_fourths_pos.le, le_rfl⟩

/-- **Both sides of the statement lie in `[log₂(5/4), 2 log₂(5/4)]`.** -/
theorem bsscSumCapacity_mem_Icc : bsscSumCapacity ∈ Set.Icc (log2 (5 / 4)) (2 * log2 (5 / 4)) :=
  ⟨le_bsscSumCapacity, bsscSumCapacity_le⟩

theorem bsscMartonSumRate_mem_Icc :
    bsscMartonSumRate ∈ Set.Icc (log2 (5 / 4)) (2 * log2 (5 / 4)) :=
  ⟨le_bsscMartonSumRate, bsscMartonSumRate_le⟩

end InfoTheory.Known.Certificates.BinarySkewSymmetricBc
