import InfoTheory.Problems.UniversalLossyRedundancy
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.UniversalLossyRedundancy`

The frozen statement asks whether the minimax redundancy of universal
`d`-semifaithful codes on `m`-ary memoryless sources under Hamming distortion satisfies
`(n / log₂ n) · R_n ≤ m/2 + ε` for all large `n`.

## Certified (about exactly these objects)
* `rateDistortion_dirac` — `R(D) = 0` for a point-mass source, `D ≥ 0`.
* `minimaxSet_nonneg`, `minimaxLossyRedundancy_nonneg` — `R_n ≥ 0` for `m ≥ 1`, `D ≥ 0`
  (test any code on a point mass).
* `minimaxLossyRedundancy_le` — the fixed-length lossless code (all `mⁿ` sequences,
  `⌈n log₂ m⌉`-bit codewords, Kraft verified) is `d`-semifaithful, so the defining set is
  nonempty and `R_n ≤ ⌈n log₂ m⌉ / n`. Together: `R_n` is a genuine finite infimum, not a junk
  value, on the whole range of `Statement`.

## Not certified
* The `Θ(log n / n)` order of `R_n` (Yu–Speed 1993; Zhang–Yang–Wei 1997; Yang–Zhang 1999):
  needs type-covering lemmas and the `½ log n / n` known-source lower bound, which are not in
  `Bridge`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.UniversalLossyRedundancy

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.UniversalLossyRedundancy

theorem hammingDist_dist (m : ℕ) (x y : Fin m) :
    (hammingDist m).dist x y = if x = y then 0 else 1 := rfl

/-- `R(D) = 0` for a point-mass source and `D ≥ 0` (reproduce the atom). -/
theorem rateDistortion_dirac {m : ℕ} (a : Fin m) {D : ℝ} (hD : 0 ≤ D) :
    rateDistortion (diracDist a) (hammingDist m) D = 0 :=
  rateDistortion_eq_zero_of_const _ _ ⟨a, by
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun x _ => ?_)) hD
    by_cases h : x = a <;> simp [diracDist, hammingDist_dist, h]⟩

theorem expectedRate_nonneg {m : ℕ} (P : ProbDist (Fin m)) (n M : ℕ)
    (enc : (Fin n → Fin m) → Fin M) (len : Fin M → ℕ) : 0 ≤ expectedRate P n M enc len :=
  div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg
    (Finset.prod_nonneg fun i _ => P.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- Every element of the minimax set is `≥ 0` (test the code on a point-mass source, whose
    rate–distortion function vanishes). -/
theorem minimaxSet_nonneg {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    ∀ r ∈ { r : ℝ | ∃ (M : ℕ) (enc : (Fin n → Fin m) → Fin M)
      (dec : Fin M → (Fin n → Fin m)) (len : Fin M → ℕ),
      IsDSemifaithfulCode m (hammingDist m) D n M enc dec len ∧
      ∀ P : ProbDist (Fin m), expectedRate P n M enc len -
        rateDistortion P (hammingDist m) D ≤ r }, 0 ≤ r := by
  rintro r ⟨M, enc, dec, len, -, hP⟩
  have := hP (diracDist ⟨0, hm⟩)
  rw [rateDistortion_dirac _ hD, sub_zero] at this
  exact le_trans (expectedRate_nonneg _ _ _ _ _) this

/-- **The minimax redundancy is nonnegative** (for `m ≥ 1`, `D ≥ 0`). -/
theorem minimaxLossyRedundancy_nonneg {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    0 ≤ minimaxLossyRedundancy m (hammingDist m) D n :=
  Real.sInf_nonneg (minimaxSet_nonneg hm hD n)

/-- **The minimax redundancy is a genuine finite infimum**: the fixed-length lossless code
    (all `mⁿ` sequences, each with a `⌈n log₂ m⌉`-bit codeword) is `d`-semifaithful and has
    redundancy at most `⌈n log₂ m⌉ / n` against every source, so the defining set is nonempty
    and `R_n ≤ ⌈n log₂ m⌉ / n`. -/
theorem minimaxLossyRedundancy_le {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) {n : ℕ}
    (hn : 0 < n) :
    minimaxLossyRedundancy m (hammingDist m) D n ≤
      (Nat.ceil ((n : ℝ) * log2 (m : ℝ)) : ℝ) / (n : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set L := Nat.ceil ((n : ℝ) * log2 (m : ℝ)) with hL
  let e := Fintype.equivFin (Fin n → Fin m)
  have hlog : (2 : ℝ) ^ (log2 (m : ℝ)) = m := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    unfold log2
    rw [show Real.log 2 * (Real.log (m : ℝ) / Real.log 2) = Real.log (m : ℝ) by
      field_simp [(Real.log_pos one_lt_two).ne'], Real.exp_log (by exact_mod_cast hm)]
  have hpow : (m : ℝ) ^ n ≤ (2 : ℝ) ^ (L : ℝ) := by
    calc (m : ℝ) ^ n = ((2 : ℝ) ^ (log2 (m : ℝ))) ^ n := by rw [hlog]
      _ = (2 : ℝ) ^ ((n : ℝ) * log2 (m : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      _ ≤ (2 : ℝ) ^ (L : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  refine csInf_le ⟨0, minimaxSet_nonneg hm hD n⟩ ⟨_, e, e.symm, fun _ => L,
    ⟨hn, Fintype.card_pos, ?_, fun x => ?_⟩, fun P => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : ((Fintype.card (Fin n → Fin m) : ℕ) : ℝ) = (m : ℝ) ^ n := by
      simp
    rw [hcard]
    calc (m : ℝ) ^ n * (2 : ℝ) ^ (-(L : ℝ)) ≤ (2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-(L : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
  · simp [e, hammingDist_dist, hD]
  · have hrate : expectedRate P n _ e (fun _ => L) = (L : ℝ) / n := by
      show (∑ x : Fin n → Fin m, (iidDist P n).pmf x * (L : ℝ)) / n = (L : ℝ) / n
      rw [← Finset.sum_mul, (iidDist P n).sum_one, one_mul]
    rw [hrate]
    linarith [rateDistortion_nonneg P (hammingDist m) D]

end InfoTheory.Known.Certificates.UniversalLossyRedundancy
