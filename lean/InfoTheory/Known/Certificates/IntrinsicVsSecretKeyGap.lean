import InfoTheory.Problems.IntrinsicVsSecretKeyGap
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.SecretKeyCapacityPublicDiscussion

/-!
# Certificate for `InfoTheory.Problems.IntrinsicVsSecretKeyGap`

The frozen statement asks whether some finite source `P_{XYZ}` has `I(X; Y ↓ Z) > 0` but
`S(X; Y ‖ Z) = 0` (classical bound information).

## Certified (about exactly these objects)
* `intrinsicInfo_mem_Icc` — `0 ≤ I(X; Y ↓ Z) ≤ min(I(X; Y), I(X; Y | Z))` (Maurer–Wolf 1999),
  reusing certificate `SecretKeyCapacityPublicDiscussion`.
* `secretKeyCapacity_nonneg` — `S(X; Y ‖ Z) ≥ 0`, so the condition `S = 0` is the extreme
  value of the range, as intended.
* `statement_iff` — the statement is equivalent to the existence of a source with
  `I(X; Y ↓ Z) > 0` and `S(X; Y ‖ Z) ≤ 0`.

## Not certified / caveat (junk-value risk)
* `secretKeyCapacity` is an `sSup`; Lean's `sSup` of a set that is not bounded above is `0`.
  The upper bound `S ≤ I(X; Y)` (Maurer 1993; Ahlswede–Csiszár 1993) needs the
  interactive-communication converse, which the library lacks. So this certificate does
  **not** exclude, inside Lean, that some source has an unbounded secret-key rate set (which
  would make `S = 0` hold vacuously and the statement trivially true). Mathematically the set is
  bounded by `I(X; Y)`, so the formal statement is faithful, but this is not machine-checked.
* No statement-level conclusion: the problem is open (bound information is known to exist in
  the multipartite quantum setting, not in this classical bipartite one).

Sources: Gisin–Wolf, CRYPTO 2000; Renner–Wolf, EUROCRYPT 2003; Maurer–Wolf, IEEE Trans. IT 1999.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.IntrinsicVsSecretKeyGap

open InfoTheory InfoTheory.Bridge InfoTheory.Known
open InfoTheory.Problems.IntrinsicVsSecretKeyGap
open InfoTheory.Known.Certificates.SecretKeyCapacityPublicDiscussion

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- `0 ≤ I(X; Y ↓ Z) ≤ min(I(X; Y), I(X; Y | Z))`. -/
theorem intrinsicInfo_mem_Icc (P : ProbDist (X × Y × Z)) :
    intrinsicInfo P ∈ Set.Icc 0 (min (mutualInfo (P.map (fun t => (t.1, t.2.1))))
      (condMutualInfo P)) :=
  ⟨intrinsicInfo_nonneg P,
    le_min (intrinsicInfo_le_mutualInfo P) (intrinsicInfo_le_condMutualInfo P)⟩

/-- The statement is equivalent to its `≤ 0` form (since `S ≥ 0`). -/
theorem statement_iff : Statement ↔
    ∃ (kX kY kZ : ℕ) (P : ProbDist (Fin kX × Fin kY × Fin kZ)),
      0 < kX ∧ 0 < kY ∧ 0 < kZ ∧ 0 < intrinsicInfo P ∧ secretKeyCapacity P ≤ 0 := by
  constructor
  · rintro ⟨kX, kY, kZ, P, h1, h2, h3, h4, h5⟩
    exact ⟨kX, kY, kZ, P, h1, h2, h3, h4, h5.le⟩
  · rintro ⟨kX, kY, kZ, P, h1, h2, h3, h4, h5⟩
    exact ⟨kX, kY, kZ, P, h1, h2, h3, h4, le_antisymm h5 (secretKeyCapacity_nonneg P)⟩

end InfoTheory.Known.Certificates.IntrinsicVsSecretKeyGap
