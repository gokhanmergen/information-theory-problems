import InfoTheory.Problems.BinaryDuplicationChannel
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.BinaryDuplicationChannel`

The Statement asks whether the geometric binary duplication (sticky) channel capacity
`C_dup(p) = sup_P I(R; S) / E[R]` (`geometricDuplicationCapacity`, Mitzenmacher, IEEE Trans. IT
54(1), 2008) is convex in `p ∈ (0, 1)`. This file checks the run-length transition law and the
basic shape of the variational set on the exact Statement objects.

## Certified
* `chooseNat_eq`: the self-contained binomial `chooseNat` is Mathlib's `Nat.choose`.
* `hasSum_dupRunTrans`: **regression** — for `0 ≤ p < 1`, `dupRunTrans p r` (input run of
  length `r + 1`, output run of length `s + 1`) is the negative-binomial law of a sum of
  `r + 1` i.i.d. `Geom(1 - p)` copy counts: it sums to `1`. With `dupRunTrans_nonneg`,
  `dupRunTrans_le_one`.
* `dupRunTrans_zero_dup`: at `p = 0` (no duplication) the run-length channel is the
  identity, `W_0(s | r) = [s = r]`.
* `pointMass`, `meanRunLen_pointMass`, `dupRate_pointMass`: the all-runs-of-length-one input
  (alternating `0101…`) has `E[R] = 1` and carries rate `0` — the run lengths are then
  deterministic, so `I(R; S) = 0`; `rateSet_nonempty`.

## Not certified
* Boundedness of the rate set (`I(R; S)/E[R] ≤ 1` bit), hence that the `sSup` is a genuine
  supremum and `0 ≤ C_dup(p) ≤ 1`; this needs a max-entropy bound for countable laws with a
  mean constraint and a `tsum` interchange, which is not yet in `Known`/`Bridge`.
* `C_dup(p) → 1` as `p → 0`, Mitzenmacher's numerical bounds, and Mitzenmacher's reduction
  of the operational capacity to the single-run formula.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BinaryDuplicationChannel

open InfoTheory InfoTheory.Problems.BinaryDuplicationChannel

lemma chooseNat_eq : ∀ n k : ℕ, chooseNat n k = n.choose k
  | _, 0 => by simp [chooseNat]
  | 0, _ + 1 => by simp [chooseNat]
  | n + 1, k + 1 => by
      rw [chooseNat, chooseNat_eq n k, chooseNat_eq n (k + 1), Nat.choose_succ_succ]

lemma dupRunTrans_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (r s : ℕ) :
    0 ≤ dupRunTrans p r s := by
  unfold dupRunTrans binomR
  have : 0 ≤ 1 - p := by linarith
  split_ifs <;> positivity

/-- **Regression.** For `0 ≤ p < 1` the run-length transition law is a probability
distribution (negative binomial series `∑ₙ C(n+r, r) pⁿ = (1 - p)^{-(r+1)}`). -/
theorem hasSum_dupRunTrans {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) (r : ℕ) :
    HasSum (dupRunTrans p r) 1 := by
  rw [← hasSum_nat_add_iff' r]
  have hsum0 : ∑ i ∈ Finset.range r, dupRunTrans p r i = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      have : ¬ r ≤ i := by have := Finset.mem_range.1 hi; omega
      simp [dupRunTrans, this])
  rw [hsum0, sub_zero]
  have hnorm : ‖p‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one r hnorm).mul_left ((1 - p) ^ (r + 1))
  have hne : (1 - p) ^ (r + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [mul_one_div_cancel hne] at hg
  convert hg using 1
  funext n
  have hle : r ≤ n + r := Nat.le_add_left r n
  simp only [dupRunTrans, binomR, chooseNat_eq, hle, ite_true, Nat.add_sub_cancel]
  ring

lemma dupRunTrans_le_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) (r s : ℕ) :
    dupRunTrans p r s ≤ 1 := by
  have hs := hasSum_dupRunTrans h0 h1 r
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum s (fun j _ => dupRunTrans_nonneg h0 h1.le r j)

/-- At `p = 0` no bit is duplicated: the run-length channel is the identity. -/
theorem dupRunTrans_zero_dup (r s : ℕ) : dupRunTrans 0 r s = if s = r then 1 else 0 := by
  unfold dupRunTrans binomR
  by_cases hrs : r ≤ s
  · rcases Nat.eq_or_lt_of_le hrs with h | h
    · subst h; simp [chooseNat_eq]
    · have hne : s ≠ r := by omega
      have hpos : s - r ≠ 0 := by omega
      simp [hrs, hne, zero_pow hpos]
  · have hne : s ≠ r := by omega
    simp [hrs, hne]

private lemma hasSum_delta : HasSum (fun r : ℕ => if r = 0 then (1 : ℝ) else 0) 1 := by
  have := hasSum_single (f := fun r : ℕ => if r = 0 then (1 : ℝ) else 0) 0
    (fun b hb => by simp [hb])
  simpa using this

/-- The input with every run of length one (the alternating sequence `0101…`). -/
noncomputable def pointMass : PosIntDist where
  pmf := fun r => if r = 0 then 1 else 0
  nonneg := fun r => by by_cases h : r = 0 <;> simp [h]
  summable := hasSum_delta.summable
  tsum_one := hasSum_delta.tsum_eq
  mean_summable := by
    have : (fun r : ℕ => ((r + 1 : ℕ) : ℝ) * (if r = 0 then (1 : ℝ) else 0)) =
        fun r => if r = 0 then (1 : ℝ) else 0 := by
      funext r; by_cases h : r = 0 <;> simp [h]
    rw [this]; exact hasSum_delta.summable

lemma pointMass_mul (f : ℕ → ℝ) :
    (fun r : ℕ => pointMass.pmf r * f r) = fun r => if r = 0 then f 0 else 0 := by
  funext r
  simp only [pointMass]
  split_ifs with h <;> simp [h]

theorem meanRunLen_pointMass : meanRunLen pointMass = 1 := by
  unfold meanRunLen
  have := pointMass_mul (fun r => ((r + 1 : ℕ) : ℝ))
  simp only [mul_comm (((_ : ℕ) + 1 : ℕ) : ℝ)] at this ⊢
  rw [this, tsum_ite_eq]
  norm_num

/-- Deterministic run lengths carry no information: the rate of `pointMass` is `0`. -/
theorem dupRate_pointMass (p : ℝ) : dupRate p pointMass = 0 := by
  unfold dupRate
  simp only
  rw [meanRunLen_pointMass]
  have h1 : ∀ s : ℕ, (∑' r : ℕ, pointMass.pmf r * dupRunTrans p r s) = dupRunTrans p 0 s := by
    intro s
    rw [pointMass_mul (fun r => dupRunTrans p r s), tsum_ite_eq]
  simp only [h1]
  rw [pointMass_mul (fun r => ∑' s : ℕ, negPLogP (dupRunTrans p r s)), tsum_ite_eq]
  simp

theorem rateSet_nonempty (p : ℝ) :
    (0 : ℝ) ∈ { r : ℝ | ∃ P : PosIntDist, r = dupRate p P } :=
  ⟨pointMass, (dupRate_pointMass p).symm⟩

end InfoTheory.Known.Certificates.BinaryDuplicationChannel
