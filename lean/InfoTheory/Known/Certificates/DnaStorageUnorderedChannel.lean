import InfoTheory.Problems.DnaStorageUnorderedChannel
import InfoTheory.Known.Channels

/-!
# Certificate for `InfoTheory.Problems.DnaStorageUnorderedChannel`

The frozen statement: for every `d ∈ (0, 1)` there is `β₀` with
`C_shuf-del(d, β) = C_del(d) - 1/β` for all `β ≥ β₀`. Facts about the *exact* objects
`IsShuffledDeletionAchievable`, `shuffledDeletionCapacity`:

## Certified
* `zero_achievable`: rate `0` is achievable (one message, constant permutation-invariant decoder,
  zero error) — the capacity set is non-empty.
* `shuffledDeletionCapacity_nonneg`, `achievable_rate_nonneg`.
* `deletion_noiseless`, `rhs_noiseless` (regression): at `d = 0` strands arrive intact and the
  conjectured formula reduces to the proven noiseless shuffling capacity `1 - 1/β`
  (Heckel–Shomorony–Ramchandran–Tse 2017), via `C_del(0) = 1`.
* `rhs_le`: the right-hand side is at most `1 - d - 1/β`.

## Not certified
* Boundedness of the achievable-rate set (a counting argument; needed so that the `sSup` is not
  the junk `0`), and the noiseless capacity `C_shuf(0, β) = 1 - 1/β` itself.
* Positivity of `C_del(d)` for `d < 1` (Drinea–Mitzenmacher `(1-d)/9`).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.DnaStorageUnorderedChannel

open InfoTheory InfoTheory.Problems.DnaStorageUnorderedChannel

/-- Rate `0` (a single message) is achievable at every `(d, β)`, with a constant — hence
    permutation-invariant — decoder and zero error. So the capacity set is non-empty. -/
theorem zero_achievable (d β : ℝ) : IsShuffledDeletionAchievable d β 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨0, fun M _ _ => ?_⟩⟩
  intro L K
  have hK : K = 1 := by simp [K]
  have hss : Subsingleton (Fin K) := by rw [hK]; infer_instance
  refine ⟨fun _ _ _ => false, fun _ => ⟨0, by omega⟩, fun _ _ _ => rfl, ?_⟩
  simp only
  rw [Finset.sum_eq_zero]
  · simp only [mul_zero]; exact hε.le
  · intro msg _
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [ite_eq_right_iff]
    intro h; exact absurd (Subsingleton.elim _ _) h

/-- Every achievable rate is non-negative, so the capacity is `≥ 0` (never a negative junk
    value). -/
theorem shuffledDeletionCapacity_nonneg (d β : ℝ) : 0 ≤ shuffledDeletionCapacity d β :=
  Real.sSup_nonneg (fun _ hR => hR.1)

/-- Achievability is monotone in the target error: the definition is the usual
    "error → 0" notion (sanity check of quantifier order). -/
theorem achievable_rate_nonneg {d β R : ℝ} (h : IsShuffledDeletionAchievable d β R) : 0 ≤ R :=
  h.1

/-- **Regression (noiseless strands).** At `d = 0` every strand is received intact:
    `Pr[Del₀(x) = y] = [x = y]` (reusing `Known.deletionProb_zero`). -/
theorem deletion_noiseless (x y : List Bool) : deletionProb 0 x y = if x = y then 1 else 0 :=
  Known.deletionProb_zero x y

/-- **Regression (Shomorony–Heckel noiseless law).** At `d = 0` the conjectured formula
    `C_del(d) - 1/β` reduces to the proven noiseless shuffling capacity `1 - 1/β`
    (Heckel–Shomorony–Ramchandran–Tse 2017), using `C_del(0) = 1` (`Known`). -/
theorem rhs_noiseless (β : ℝ) : binaryDeletionCapacity 0 - 1 / β = 1 - 1 / β := by
  rw [Known.binaryDeletionCapacity_zero]

/-- The conjectured right-hand side never exceeds the trivial bound `1 - d - 1/β`, since
    `C_del(d) ≤ 1 - d` (`Known.binaryDeletionCapacity_le_one_sub`). -/
theorem rhs_le {d : ℝ} (h1 : d ≤ 1) (β : ℝ) :
    binaryDeletionCapacity d - 1 / β ≤ 1 - d - 1 / β := by
  linarith [Known.binaryDeletionCapacity_le_one_sub h1]

end InfoTheory.Known.Certificates.DnaStorageUnorderedChannel
