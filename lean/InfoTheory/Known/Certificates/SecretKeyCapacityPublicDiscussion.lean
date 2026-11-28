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
* **Regression (upper half of the `Z`-constant case; passes).**
  `gohariAnantharamBound_le_intrinsicInfo` : `GA(P) ≤ I(X; Y ↓ Z)` (take `U` constant;
  `intrinsicInfo_appendConst_le`, `condMutualInfo_map_const_fst`), hence
  `gohariAnantharamBound_le_mutualInfo` : `GA(P) ≤ min(I(X; Y), I(X; Y | Z))`.  When `Z` is
  constant the known answer is `S = I(X; Y)` (Maurer; Ahlswede–Csiszár), so the formula is not
  too large there.  The lower half (`GA(P) ≥ I(X; Y)` for constant `Z`, which needs data
  processing through the test channel) is not certified.

## Not certified
* **Boundedness of the secret-key rate set** (hence that `secretKeyCapacity P` is not the junk
  value `sSup` of an unbounded set). The docstring of `Core.secretKeyCapacity` asserts
  `S ≤ I(X; Y)`; the proof needs the Maurer / Ahlswede–Csiszár converse (public interactive
  communication does not increase `I(X Rₐ; Y R_b | T)`, combined with Fano). This lemma is not
  in the library, so the two sides are *not* certified to be comparable finite values from
  above. (For the statement this would matter only if the set were unbounded; mathematically it
  is bounded by `I(X; Y)`.)
* `S ≤ gohariAnantharamBound` (Renner–Wolf; Gohari–Anantharam converse).
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

/-! ### Regression: `GA ≤ I(X; Y ↓ Z)` (constant `U`), hence `GA ≤ I(X; Y)` -/

/-- `I(X; Y | Z) = 0` when `X` is constant. -/
theorem condMutualInfo_map_const_fst {ι α β γ : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [Fintype γ] (R : ProbDist ι) (c : α) (f : ι → β) (g : ι → γ) :
    condMutualInfo (R.map (fun i => (c, f i, g i))) = 0 := by
  have e0 : R.map (fun i => (c, f i, g i)) =
      (R.map (fun i => (f i, g i))).map (fun yz => (c, yz.1, yz.2)) := by rw [map_comp_eq]; rfl
  have e1 : (R.map (fun i => (c, f i, g i))).map (fun t => (t.1, t.2.2)) =
      (R.map g).map (fun z => (c, z)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (R.map (fun i => (c, f i, g i))).map (fun t => (t.2.1, t.2.2)) =
      R.map (fun i => (f i, g i)) := by rw [map_comp_eq]; rfl
  have e3 : (R.map (fun i => (c, f i, g i))).map (fun t => t.2.2) = R.map g := by
    rw [map_comp_eq]; rfl
  have i0 : Function.Injective (fun yz : β × γ => (c, yz.1, yz.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2
  have i1 : Function.Injective (fun z : γ => (c, z)) := fun a b h => (Prod.mk.inj h).2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ i0, shannonEntropy_map_of_injective _ i1]
  ring

lemma map_pmf_of_injective {α β : Type*} [Fintype α] [Fintype β] {f : α → β}
    (hf : Function.Injective f) (P : ProbDist α) (a : α) : (P.map f).pmf (f a) = P.pmf a := by
  classical
  unfold ProbDist.map
  dsimp only
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hf.ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Appending a constant coordinate to `Z` does not increase the intrinsic information. -/
theorem intrinsicInfo_appendConst_le (P : ProbDist (X × Y × Z)) :
    intrinsicInfo (P.map (fun t => (t.1, t.2.1, (t.2.2, (0 : Fin 1))))) ≤ intrinsicInfo P := by
  classical
  set P' := P.map (fun t => (t.1, t.2.1, (t.2.2, (0 : Fin 1)))) with hP'def
  have hinj : Function.Injective (fun t : X × Y × Z => (t.1, t.2.1, (t.2.2, (0 : Fin 1)))) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2.1)
  have hP' : ∀ x y z (u : Fin 1), P'.pmf (x, y, (z, u)) = P.pmf (x, y, z) := by
    intro x y z u
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    exact map_pmf_of_injective hinj P (x, y, z)
  unfold intrinsicInfo
  refine csInf_le_csInf ⟨0, ?_⟩ ⟨_, 1, constChannel Z, rfl⟩ ?_
  · rintro r ⟨k, W, rfl⟩
    exact condMutualInfo_nonneg _
  · rintro r ⟨k, W, rfl⟩
    let W' : DMC (Z × Fin 1) (Fin k) :=
      { trans := fun p b => W.trans p.1 b
        nonneg := fun p b => W.nonneg _ _
        sum_one := fun p => W.sum_one p.1 }
    refine ⟨k, W', ?_⟩
    congr 1
    refine probDist_eq_of_pmf fun t => ?_
    show ∑ z : Z, P.pmf (t.1, t.2.1, z) * W.trans z t.2.2 =
      ∑ p : Z × Fin 1, P'.pmf (t.1, t.2.1, p) * W'.trans p t.2.2
    rw [Fintype.sum_prod_type]
    simp [hP', W']

/-- **`GA(P) ≤ I(X; Y ↓ Z)`** (Gohari–Anantharam 2010): take `U` constant. -/
theorem gohariAnantharamBound_le_intrinsicInfo (P : ProbDist (X × Y × Z)) :
    gohariAnantharamBound P ≤ intrinsicInfo P := by
  unfold gohariAnantharamBound
  set Q : ProbDist ((X × Y × Z) × Fin 1) := P.map (fun t => (t, (0 : Fin 1))) with hQdef
  have hQ : Q.fst = P := by
    rw [← map_fst_eq_fst, hQdef, map_comp_eq]
    exact probDist_eq_of_pmf fun a => map_pmf_of_injective (f := fun t => t) (fun _ _ h => h) P a
  refine csInf_le_of_le ⟨0, ?_⟩ ⟨1, Q, hQ, rfl⟩ ?_
  · rintro r ⟨kU, Q', -, rfl⟩
    exact add_nonneg (intrinsicInfo_nonneg _) (condMutualInfo_nonneg _)
  have h1 : Q.map (fun t => (t.1.1, t.1.2.1, (t.1.2.2, t.2))) =
      P.map (fun t => (t.1, t.2.1, (t.2.2, (0 : Fin 1)))) := by
    rw [hQdef, map_comp_eq]; rfl
  have h2 : Q.map (fun t => (t.2, (t.1.1, t.1.2.1), t.1.2.2)) =
      P.map (fun t => ((0 : Fin 1), (t.1, t.2.1), t.2.2)) := by
    rw [hQdef, map_comp_eq]; rfl
  rw [h1, h2, condMutualInfo_map_const_fst, add_zero]
  exact intrinsicInfo_appendConst_le P

/-- **Regression (upper half of the `Z`-constant case).**  `GA(P) ≤ I(X; Y)` and
    `GA(P) ≤ I(X; Y | Z)` for every source.  For `Z` constant (or independent of `(X, Y)`) the
    secret-key capacity is `S = I(X; Y)` (Maurer 1993; Ahlswede–Csiszár 1993), so the frozen
    formula is not too large there. -/
theorem gohariAnantharamBound_le_mutualInfo (P : ProbDist (X × Y × Z)) :
    gohariAnantharamBound P ≤ mutualInfo (P.map (fun t => (t.1, t.2.1))) ∧
      gohariAnantharamBound P ≤ condMutualInfo P :=
  ⟨(gohariAnantharamBound_le_intrinsicInfo P).trans (intrinsicInfo_le_mutualInfo P),
    (gohariAnantharamBound_le_intrinsicInfo P).trans (intrinsicInfo_le_condMutualInfo P)⟩

end InfoTheory.Known.Certificates.SecretKeyCapacityPublicDiscussion
