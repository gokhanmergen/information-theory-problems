import InfoTheory.Problems.SecretKeyCapacityPublicDiscussion
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.SecretKeyCapacityPublicDiscussion`

The frozen statement asks whether, for every finite source `P_{XYZ}`, the secret key capacity
with unlimited public discussion `secretKeyCapacity P` equals the Gohari–Anantharam bound
`gohariAnantharamBound P = inf_U [I(X; Y ↓ Z U) + I(U; X Y | Z)]`.

## Certified (about exactly these objects)
* `secretKeyCapacity_nonneg` — `S(X; Y ‖ Z) ≥ 0`.
* `intrinsicInfo_nonneg`, `gohariAnantharamBound_nonneg` — both information quantities are
  `≥ 0` (infima of sums of conditional mutual informations).
* `intrinsicInfo_le_mutualInfo` — `I(X; Y ↓ Z) ≤ I(X; Y)` (Maurer–Wolf 1999: take `Z̄`
  constant).
* `intrinsicInfo_le_condMutualInfo` — `I(X; Y ↓ Z) ≤ I(X; Y | Z)` (take `Z̄ = Z`).

## Not certified
* **Boundedness of the secret-key rate set** (hence that `secretKeyCapacity P` is not the junk
  value `sSup` of an unbounded set). The docstring of `Core.secretKeyCapacity` asserts
  `S ≤ I(X; Y)`; the proof needs the Maurer / Ahlswede–Csiszár converse (public interactive
  communication does not increase `I(X Rₐ; Y R_b | T)`, combined with Fano). This lemma is not
  in the library, so the two sides are *not* certified to be comparable finite values from
  above. (For the statement this would matter only if the set were unbounded; mathematically it
  is bounded by `I(X; Y)`.)
* `S ≤ gohariAnantharamBound ≤ I(X; Y ↓ Z)` (Renner–Wolf; Gohari–Anantharam converses).
* No statement-level conclusion: the problem is open.

Sources: Maurer, IEEE Trans. IT 1993; Ahlswede–Csiszár, IEEE Trans. IT 1993; Maurer–Wolf,
IEEE Trans. IT 1999; Gohari–Anantharam, IEEE Trans. IT 2010.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.SecretKeyCapacityPublicDiscussion

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.SecretKeyCapacityPublicDiscussion

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

theorem secretKeyCapacity_nonneg (P : ProbDist (X × Y × Z)) : 0 ≤ secretKeyCapacity P :=
  Real.sSup_nonneg fun _ hR => hR.1

theorem intrinsicInfo_nonneg (P : ProbDist (X × Y × Z)) : 0 ≤ intrinsicInfo P := by
  unfold intrinsicInfo
  refine Real.sInf_nonneg fun r hr => ?_
  obtain ⟨k, W, rfl⟩ := hr
  exact condMutualInfo_nonneg _

theorem gohariAnantharamBound_nonneg (P : ProbDist (X × Y × Z)) :
    0 ≤ gohariAnantharamBound P := by
  unfold gohariAnantharamBound
  refine Real.sInf_nonneg fun r hr => ?_
  obtain ⟨kU, Q, -, rfl⟩ := hr
  exact add_nonneg (intrinsicInfo_nonneg _) (condMutualInfo_nonneg _)

/-- The trivial test channel into `Fin 1`. -/
def constChannel (α : Type*) [Fintype α] : DMC α (Fin 1) where
  trans _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

/-- The identity channel `Z → Fin |Z|` (relabelling). -/
noncomputable def idChannel (α : Type*) [Fintype α] [DecidableEq α] :
    DMC α (Fin (Fintype.card α)) where
  trans z k := if Fintype.equivFin α z = k then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  sum_one z := by simp

theorem intrinsic_Q_const (P : ProbDist (X × Y × Z)) (Q : ProbDist (X × Y × Fin 1))
    (hQ : ∀ t, Q.pmf t = ∑ z : Z, P.pmf (t.1, t.2.1, z) * 1) :
    Q = (P.map (fun t => (t.1, t.2.1))).map (fun ab => (ab.1, ab.2, (0 : Fin 1))) := by
  classical
  rw [map_comp_eq]
  refine probDist_eq_of_pmf fun ⟨x, y, c⟩ => ?_
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  rw [hQ]
  simp only [ProbDist.map, Function.comp, mul_one, Fintype.sum_prod_type, Prod.mk.injEq, and_true]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha; simp [ha]
  · simp

/-- **`I(X; Y ↓ Z) ≤ I(X; Y)`** (Maurer–Wolf 1999): take `Z̄` constant. -/
theorem intrinsicInfo_le_mutualInfo (P : ProbDist (X × Y × Z)) :
    intrinsicInfo P ≤ mutualInfo (P.map (fun t => (t.1, t.2.1))) := by
  unfold intrinsicInfo
  refine csInf_le_of_le ⟨0, fun r hr => ?_⟩ ⟨1, constChannel Z, rfl⟩ (le_of_eq ?_)
  · obtain ⟨k, W, rfl⟩ := hr
    exact condMutualInfo_nonneg _
  · have key : ∀ Q : ProbDist (X × Y × Fin 1), (∀ t, Q.pmf t = ∑ z : Z, P.pmf (t.1, t.2.1, z) * 1) →
        condMutualInfo Q = mutualInfo (P.map (fun t => (t.1, t.2.1))) := by
      intro Q hQ
      rw [intrinsic_Q_const P Q hQ, condMutualInfo_map_const]
    exact key _ (fun t => rfl)

theorem intrinsic_Q_id [DecidableEq Z] (P : ProbDist (X × Y × Z))
    (Q : ProbDist (X × Y × Fin (Fintype.card Z)))
    (hQ : ∀ t, Q.pmf t = ∑ z : Z, P.pmf (t.1, t.2.1, z) * (idChannel Z).trans z t.2.2) :
    Q = P.map (fun t => (t.1, t.2.1, Fintype.equivFin Z t.2.2)) := by
  classical
  refine probDist_eq_of_pmf fun ⟨x, y, k⟩ => ?_
  rw [hQ]
  simp only [ProbDist.map, idChannel, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Prod.mk.injEq]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro a _ ha; simp [ha]
  · simp

/-- **`I(X; Y ↓ Z) ≤ I(X; Y | Z)`**: take `Z̄ = Z` (relabelled into `Fin |Z|`). -/
theorem intrinsicInfo_le_condMutualInfo (P : ProbDist (X × Y × Z)) :
    intrinsicInfo P ≤ condMutualInfo P := by
  classical
  unfold intrinsicInfo
  refine csInf_le_of_le ⟨0, fun r hr => ?_⟩ ⟨Fintype.card Z, idChannel Z, rfl⟩ (le_of_eq ?_)
  · obtain ⟨k, W, rfl⟩ := hr
    exact condMutualInfo_nonneg _
  · have key : ∀ Q : ProbDist (X × Y × Fin (Fintype.card Z)),
        (∀ t, Q.pmf t = ∑ z : Z, P.pmf (t.1, t.2.1, z) * (idChannel Z).trans z t.2.2) →
        condMutualInfo Q = condMutualInfo P := by
      intro Q hQ
      rw [intrinsic_Q_id P Q hQ]
      set e := Fintype.equivFin Z
      unfold condMutualInfo
      dsimp only
      rw [map_comp_eq, map_comp_eq, map_comp_eq]
      have h1 : P.map ((fun t : X × Y × Fin (Fintype.card Z) => (t.1, t.2.2)) ∘
          fun t => (t.1, t.2.1, e t.2.2)) = (P.map (fun t => (t.1, t.2.2))).map
            (Equiv.prodCongr (Equiv.refl X) e) := by
        rw [map_comp_eq]; rfl
      have h2 : P.map ((fun t : X × Y × Fin (Fintype.card Z) => (t.2.1, t.2.2)) ∘
          fun t => (t.1, t.2.1, e t.2.2)) = (P.map (fun t => (t.2.1, t.2.2))).map
            (Equiv.prodCongr (Equiv.refl Y) e) := by
        rw [map_comp_eq]; rfl
      have h3 : P.map ((fun t : X × Y × Fin (Fintype.card Z) => t.2.2) ∘
          fun t => (t.1, t.2.1, e t.2.2)) = (P.map (fun t => t.2.2)).map e := by
        rw [map_comp_eq]; rfl
      have h4 : P.map (fun t => (t.1, t.2.1, e t.2.2)) =
          P.map (Equiv.prodCongr (Equiv.refl X) (Equiv.prodCongr (Equiv.refl Y) e)) := rfl
      rw [h1, h2, h3, h4, shannonEntropy_map_equiv, shannonEntropy_map_equiv,
        shannonEntropy_map_equiv, shannonEntropy_map_equiv]
    exact key _ (fun t => rfl)

end InfoTheory.Known.Certificates.SecretKeyCapacityPublicDiscussion
