import InfoTheory.Problems.WiretapChannelCompoundSecrecy
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.DmInterferenceChannelCapacity

/-!
# Certificate for `InfoTheory.Problems.WiretapChannelCompoundSecrecy`

The frozen statement asks whether, for every finite family `W : Fin kS → WiretapChannel X Y Z`
(`kS ≥ 1`), the regularised compound secrecy capacity `compoundSecrecyCapacity W` equals the
single-letter Liang–Kramer–Poor–Shamai bound `lkpsSingleLetterBound W`.

## Certified (about exactly these objects)
* `compoundWiretapRateN_le` — the `n`-letter secrecy expression satisfies
  `sup_V [min_s I(V; Y_sⁿ) - max_s I(V; Z_sⁿ)] ≤ n log₂ |Y|` (`max_s I(V; Z_sⁿ) ≥ 0` and
  `I(V; Y_sⁿ) ≤ H(Y_sⁿ)`).
* `compoundSecrecyCapacity_le_log2_card` — hence the regularised capacity is `≤ log₂ |Y|`.
* `lkpsSingleLetterBound_le_log2_card` — the single-letter bound is `≤ log₂ |Y|`
  (`I(V; Y_s | U) ≤ log₂ |Y|`).
So both sides of the statement are suprema of sets that are bounded above (they are not the
junk value of an unbounded `sSup`), and both are `≤ log₂ |Y|`.

## Not certified
* Lower bounds (`≥ 0`, attained by constant `U, V`): they need explicit construction of the
  joint laws with their normalisation proofs; not done here.
* `lkpsSingleLetterBound W ≤ compoundSecrecyCapacity W` (achievability, Liang–Kramer–Poor–Shamai
  2009) and the degraded-case equality: these need wiretap coding, not in the library.
* No statement-level conclusion: the problem is open.

Sources: Liang–Kramer–Poor–Shamai, IEEE Trans. IT 2009; Bjelaković–Boche–Sommerfeld, 2013.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.WiretapChannelCompoundSecrecy

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.WiretapChannelCompoundSecrecy
open InfoTheory.Known.Certificates.DmInterferenceChannelCapacity (condMutualInfo_le_log2_card
  log2_card_pow)

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma log2_card_nonneg (α : Type*) [Fintype α] : 0 ≤ log2 (Fintype.card α : ℝ) := by
  unfold log2
  exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos one_lt_two).le

/-- The `n`-letter secrecy expression is at most `n log₂ |Y|`. -/
theorem compoundWiretapRateN_le [Nonempty Y] {kS : ℕ} (hkS : 0 < kS)
    (W : Fin kS → WiretapChannel X Y Z) (n : ℕ) :
    compoundWiretapRateN W n ≤ n * log2 (Fintype.card Y) := by
  unfold compoundWiretapRateN
  refine Real.sSup_le (fun r hr => ?_) (mul_nonneg (Nat.cast_nonneg _) (log2_card_nonneg Y))
  obtain ⟨kV, Pvx, joint, -, rfl⟩ := hr
  have hmax : 0 ≤ sSup { b : ℝ | ∃ s : Fin kS,
      b = mutualInfo ((joint s).map (fun t => (t.1, fun i => (t.2.2 i).2))) } :=
    Real.sSup_nonneg fun b ⟨s, hb⟩ => hb ▸ mutualInfo_nonneg _
  have hmin : sInf { a : ℝ | ∃ s : Fin kS,
      a = mutualInfo ((joint s).map (fun t => (t.1, fun i => (t.2.2 i).1))) } ≤
      n * log2 (Fintype.card Y) := by
    refine csInf_le_of_le ⟨0, fun a ⟨s, ha⟩ => ha ▸ mutualInfo_nonneg _⟩ ⟨⟨0, hkS⟩, rfl⟩ ?_
    have := (mutualInfo_le_entropy_snd _).trans (shannonEntropy_le_log2_card
      ((((joint ⟨0, hkS⟩).map (fun t => (t.1, fun i => (t.2.2 i).1)))).snd))
    rwa [log2_card_pow] at this
  linarith

/-- **Upper bound on the regularised compound secrecy capacity**: `≤ log₂ |Y|`. -/
theorem compoundSecrecyCapacity_le_log2_card [Nonempty Y] {kS : ℕ} (hkS : 0 < kS)
    (W : Fin kS → WiretapChannel X Y Z) :
    compoundSecrecyCapacity W ≤ log2 (Fintype.card Y) := by
  unfold compoundSecrecyCapacity
  refine Real.sSup_le (fun r hr => ?_) (log2_card_nonneg Y)
  obtain ⟨n, hn, rfl⟩ := hr
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnr]
  linarith [compoundWiretapRateN_le hkS W n]

/-- **Upper bound on the LKPS single-letter bound**: `≤ log₂ |Y|`. -/
theorem lkpsSingleLetterBound_le_log2_card [Nonempty Y] {kS : ℕ} (hkS : 0 < kS)
    (W : Fin kS → WiretapChannel X Y Z) :
    lkpsSingleLetterBound W ≤ log2 (Fintype.card Y) := by
  unfold lkpsSingleLetterBound
  refine Real.sSup_le (fun r hr => ?_) (log2_card_nonneg Y)
  obtain ⟨kU, kV, Puvx, joint, -, rfl⟩ := hr
  have hmax : 0 ≤ sSup { b : ℝ | ∃ s : Fin kS,
      b = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.2, t.1))) } :=
    Real.sSup_nonneg fun b ⟨s, hb⟩ => hb ▸ condMutualInfo_nonneg _
  have hmin : sInf { a : ℝ | ∃ s : Fin kS,
      a = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.1, t.1))) } ≤
      log2 (Fintype.card Y) :=
    csInf_le_of_le ⟨0, fun a ⟨s, ha⟩ => ha ▸ condMutualInfo_nonneg _⟩ ⟨⟨0, hkS⟩, rfl⟩
      (condMutualInfo_le_log2_card _)
  linarith

end InfoTheory.Known.Certificates.WiretapChannelCompoundSecrecy
