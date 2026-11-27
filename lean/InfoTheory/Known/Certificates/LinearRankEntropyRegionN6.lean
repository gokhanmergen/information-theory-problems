import InfoTheory.Problems.LinearRankEntropyRegionN6
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.LinearRankEntropyRegionN6`

The frozen statement asks whether the closed conic hull of six-variable linear rank vectors,
`InClosedLinearRankCone 6`, is polyhedral (Dougherty–Freiling–Zeger, "Linear rank
inequalities on five or more variables", arXiv:0910.0284, 2009; Dougherty 2014). This file
proves known facts about the *exact* predicate `InClosedLinearRankCone`.

## Certified
* `lin_nonneg_of_cone`: every linear inequality valid on all linear rank vectors is valid on
  the cone (closure under conic combinations and limits), so the predicate really is the
  closed conic hull it claims to be.
* `cone_isPolymatroid`, `cone6_isPolymatroid`: `cl(cone L_n) ⊆ Γ_n` (Hammer–Romashchenko–
  Shen–Vereshchagin, "Inequalities for Shannon entropy and Kolmogorov complexity", JCSS 60,
  2000; via `Known.linearRank_isPolymatroid`).
* `ingletonAt_of_linearRank`, `cone_ingletonAt`, `cone6_ingletonAt`: Ingleton's inequality
  (Ingleton 1971) holds on the cone for *every* choice of four subsets of the 6 coordinates
  (in particular every 4-subset of coordinates), via `Known.ingleton_subspaces`.
* `exists_polymatroid6_not_in_cone`: `cl(cone L_6) ⊊ Γ_6` (lifting the Ingleton-violating
  polymatroid of `Known.exists_polymatroid_not_ingleton`).
* `cone6_ne_univ`, `statement_witness_pos`: the cone is not all of `ℝ^{2^6}`, so the Statement
  is not trivially witnessed by `m = 0`; `linearRank_mem_cone`, `cone6_ne_zero`: the cone
  contains a nonzero vector (rank function of `U_{1,6}` over `GF(2)`).

## Not certified
* The DFZ results themselves (the 24 new inequalities on 5 variables, polyhedrality of
  `cl(L_5)`, infinitely many inequalities needed on 6+ variables in a fixed characteristic)
  are out of scope.

## Remark on the docstring
The problem docstring says "linear rank vectors on `n` subspaces over `ℚ`", but `Core`'s
`IsLinearRankVector` ranges over all finite fields `GF(p^r)`. For the closed cone this is the
standard "all fields" notion of DFZ (char-0 representations reduce mod large primes), so the
Statement is unaffected; only the docstring wording is inaccurate. No trivialization of the
Statement was found.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.LinearRankEntropyRegionN6

open InfoTheory InfoTheory.Problems.LinearRankEntropyRegionN6

/-! ### Linear functionals on set functions and their closure under the cone operations -/

/-- The linear functional `h ↦ ∑_S a(S) h(S)`. -/
noncomputable def lin {n : ℕ} (a h : Finset (Fin n) → ℝ) : ℝ := ∑ S, a S * h S

lemma lin_sum {n k : ℕ} (a : Finset (Fin n) → ℝ) (v : Fin k → Finset (Fin n) → ℝ) :
    lin a (fun S => ∑ j, v j S) = ∑ j, lin a (v j) := by
  unfold lin
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma lin_close {n : ℕ} (a h w : Finset (Fin n) → ℝ) {ε : ℝ} (hw : ∀ S, |h S - w S| < ε) :
    lin a w - (∑ S, |a S|) * ε ≤ lin a h := by
  unfold lin
  rw [Finset.sum_mul, sub_le_iff_le_add, ← sub_le_iff_le_add', ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun S _ => ?_)
  have h1 : |a S * (w S - h S)| ≤ |a S| * ε := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (hw S).le (abs_nonneg _)
  have h2 := le_abs_self (a S * (w S - h S))
  linarith [show a S * w S - a S * h S = a S * (w S - h S) by ring]

/-- **Every linear inequality valid on the linear rank vectors is valid on the closed cone**
`InClosedLinearRankCone n` (conic combinations, then limits). -/
theorem lin_nonneg_of_cone {n : ℕ} (a : Finset (Fin n) → ℝ)
    (ha : ∀ v, IsLinearRankVector n v → 0 ≤ lin a v) {h : Finset (Fin n) → ℝ}
    (hh : InClosedLinearRankCone n h) : 0 ≤ lin a h := by
  by_contra hneg
  rw [not_le] at hneg
  set M : ℝ := ∑ S, |a S| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun S _ => abs_nonneg _)
  obtain ⟨k, v, hv, happrox⟩ := hh (-lin a h / (M + 1)) (div_pos (by linarith) (by linarith))
  have hw : 0 ≤ lin a (fun S => ∑ j, v j S) := by
    rw [lin_sum]; exact Finset.sum_nonneg (fun j _ => ha _ (hv j))
  have key := lin_close a h (fun S => ∑ j, v j S) happrox
  rw [← hM] at key
  have : M * (-lin a h / (M + 1)) < -lin a h := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Indicator coefficient of a single set. -/
noncomputable def e1 {n : ℕ} (T : Finset (Fin n)) : Finset (Fin n) → ℝ :=
  fun S => if S = T then 1 else 0

@[simp] lemma lin_e1 {n : ℕ} (T : Finset (Fin n)) (h : Finset (Fin n) → ℝ) :
    lin (e1 T) h = h T := by
  simp [lin, e1]

@[simp] lemma lin_zero {n : ℕ} (h : Finset (Fin n) → ℝ) : lin 0 h = 0 := by
  simp [lin]

lemma lin_add {n : ℕ} (a b h : Finset (Fin n) → ℝ) : lin (a + b) h = lin a h + lin b h := by
  simp [lin, add_mul, Finset.sum_add_distrib]

lemma lin_sub {n : ℕ} (a b h : Finset (Fin n) → ℝ) : lin (a - b) h = lin a h - lin b h := by
  simp [lin, sub_mul, Finset.sum_sub_distrib]

/-! ### Ingleton for arbitrary subsets (all linear rank vectors) -/

/-- Ingleton's inequality for four subsets `A, B, C, D` of the ground set:
`h(A) + h(B) + h(C∪D) + h(A∪B∪C) + h(A∪B∪D) ≤ h(A∪B) + h(A∪C) + h(A∪D) + h(B∪C) + h(B∪D)`. -/
def IngletonAt {n : ℕ} (h : Finset (Fin n) → ℝ) (A B C D : Finset (Fin n)) : Prop :=
  h A + h B + h (C ∪ D) + h (A ∪ B ∪ C) + h (A ∪ B ∪ D) ≤
    h (A ∪ B) + h (A ∪ C) + h (A ∪ D) + h (B ∪ C) + h (B ∪ D)

/-- Dimension of a subspace as a plain function (avoids dependent rewriting). -/
private noncomputable def fr {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (U : Submodule K E) : ℕ := Module.finrank K U

private lemma ingletonAt_of_subspaceFamily {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] {n : ℕ} (W : Finset (Fin n) → Submodule K E)
    (hW : ∀ S T, W (S ∪ T) = W S ⊔ W T) {c : ℝ} (hc : 0 < c) (h : Finset (Fin n) → ℝ)
    (hV : ∀ S, h S = c * (Module.finrank K (W S) : ℝ)) (A B C D : Finset (Fin n)) :
    IngletonAt h A B C D := by
  have hV' : ∀ S, h S = c * (fr (W S) : ℝ) := hV
  have key := ingleton_subspaces (W A) (W B) (W C) (W D)
  unfold IngletonAt
  simp only [hV', hW, Finset.union_assoc]
  have key' : (fr (W A) : ℝ) + fr (W B) + fr (W C ⊔ W D) + fr (W A ⊔ (W B ⊔ W C)) +
      fr (W A ⊔ (W B ⊔ W D)) ≤ (fr (W A ⊔ W B) : ℝ) + fr (W A ⊔ W C) + fr (W A ⊔ W D) +
      fr (W B ⊔ W C) + fr (W B ⊔ W D) := by
    simp only [fr]; exact_mod_cast key
  nlinarith [key', hc]

/-- **Ingleton's inequality for every linear rank vector on `n` subspaces and every four
subsets** (Ingleton 1971; Hammer–Romashchenko–Shen–Vereshchagin 2000, Thm. 1), from
`Known.ingleton_subspaces` applied to the spans `V_A = ∑_{i∈A} V_i`, etc. -/
theorem ingletonAt_of_linearRank {n : ℕ} {h : Finset (Fin n) → ℝ}
    (hlin : IsLinearRankVector n h) (A B C D : Finset (Fin n)) : IngletonAt h A B C D := by
  obtain ⟨p, r, d, hp, hr, c, V, hc, hV⟩ := hlin
  exact ingletonAt_of_subspaceFamily (fun S => ⨆ i ∈ S, V i) (fun S T => Finset.iSup_union)
    hc h hV A B C D

/-! ### The closed linear rank cone lies in `Γ_n` and satisfies Ingleton -/

/-- Every linear rank vector lies in the closed cone (take `k = 1`). -/
theorem linearRank_mem_cone {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : IsLinearRankVector n v) :
    InClosedLinearRankCone n v :=
  fun ε hε => ⟨1, fun _ => v, fun _ => hv, fun S => by simpa using hε⟩

/-- **`cl(cone L_n) ⊆ Γ_n`**: every vector of `InClosedLinearRankCone n` is a polymatroid
(Hammer–Romashchenko–Shen–Vereshchagin 2000; `Γ_n` is a closed convex cone containing `L_n`,
`Known.linearRank_isPolymatroid`). -/
theorem cone_isPolymatroid {n : ℕ} {h : Finset (Fin n) → ℝ} (hh : InClosedLinearRankCone n h) :
    IsPolymatroid n h := by
  have hpm := fun v (hv : IsLinearRankVector n v) => linearRank_isPolymatroid hv
  refine ⟨?_, ?_, ?_⟩
  · have h1 := lin_nonneg_of_cone (e1 ∅) (fun v hv => by simp [(hpm v hv).1]) hh
    have h2 := lin_nonneg_of_cone (0 - e1 ∅) (fun v hv => by rw [lin_sub]; simp [(hpm v hv).1]) hh
    simp only [lin_e1, lin_sub, lin_zero] at h1 h2
    linarith
  · intro S T hST
    have := lin_nonneg_of_cone (e1 T - e1 S)
      (fun v hv => by simp [lin_sub, (hpm v hv).2.1 S T hST]) hh
    simp only [lin_sub, lin_e1] at this
    linarith
  · intro S T
    have := lin_nonneg_of_cone (e1 S + e1 T - e1 (S ∪ T) - e1 (S ∩ T))
      (fun v hv => by
        have := (hpm v hv).2.2 S T
        simp only [lin_sub, lin_add, lin_e1]; linarith) hh
    simp only [lin_sub, lin_add, lin_e1] at this
    linarith

/-- **Ingleton holds on the closed linear rank cone, for every four subsets**
(Ingleton 1971; Hammer–Romashchenko–Shen–Vereshchagin 2000): Ingleton is a linear inequality
valid on `L_n`, hence on its closed conic hull. -/
theorem cone_ingletonAt {n : ℕ} {h : Finset (Fin n) → ℝ} (hh : InClosedLinearRankCone n h)
    (A B C D : Finset (Fin n)) : IngletonAt h A B C D := by
  have := lin_nonneg_of_cone
    (e1 (A ∪ B) + e1 (A ∪ C) + e1 (A ∪ D) + e1 (B ∪ C) + e1 (B ∪ D) -
      e1 A - e1 B - e1 (C ∪ D) - e1 (A ∪ B ∪ C) - e1 (A ∪ B ∪ D))
    (fun v hv => by
      have := ingletonAt_of_linearRank hv A B C D
      unfold IngletonAt at this
      simp only [lin_sub, lin_add, lin_e1]; linarith) hh
  simp only [lin_sub, lin_add, lin_e1] at this
  unfold IngletonAt
  linarith

/-- The six-variable specialization: every `h ∈ InClosedLinearRankCone 6` is a polymatroid. -/
theorem cone6_isPolymatroid {h : Finset (Fin 6) → ℝ} (hh : InClosedLinearRankCone 6 h) :
    IsPolymatroid 6 h :=
  cone_isPolymatroid hh

/-- The six-variable specialization: every `h ∈ InClosedLinearRankCone 6` satisfies Ingleton
for every choice of four (not necessarily distinct) subsets of the 6 coordinates, in
particular for every 4-subset `{i, j, k, l}` of coordinates. -/
theorem cone6_ingletonAt {h : Finset (Fin 6) → ℝ} (hh : InClosedLinearRankCone 6 h)
    (A B C D : Finset (Fin 6)) : IngletonAt h A B C D :=
  cone_ingletonAt hh A B C D

/-! ### Non-degeneracy: the cone is neither everything nor all of `Γ_6` nor `{0}` -/

/-- The cone is not all of `ℝ^{2^6}` (vectors with `h ∅ ≠ 0` are excluded). -/
theorem cone6_ne_univ : ¬ ∀ h : Finset (Fin 6) → ℝ, InClosedLinearRankCone 6 h := by
  intro hall
  have := (cone6_isPolymatroid (hall fun _ => 1)).1
  norm_num at this

/-- Hence any witness `(m, a)` of the Statement needs `m ≥ 1` inequalities: the Statement is
not settled by the vacuous choice `m = 0`. -/
theorem statement_witness_pos (m : ℕ) (a : Fin m → Finset (Fin 6) → ℝ)
    (hma : ∀ h : Finset (Fin 6) → ℝ,
      InClosedLinearRankCone 6 h ↔ ∀ k : Fin m, 0 ≤ ∑ S : Finset (Fin 6), a k S * h S) :
    0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd (fun h => (hma h).2 (fun k => k.elim0)) cone6_ne_univ
  · exact hm

/-- Restriction of a subset of `Fin 6` to the first four coordinates. -/
def restrict4 (S : Finset (Fin 6)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i : Fin 4 => (Fin.castLE (by norm_num) i : Fin 6) ∈ S)

lemma restrict4_union (S T : Finset (Fin 6)) : restrict4 (S ∪ T) = restrict4 S ∪ restrict4 T := by
  ext i; simp [restrict4]

lemma restrict4_inter (S T : Finset (Fin 6)) : restrict4 (S ∩ T) = restrict4 S ∩ restrict4 T := by
  ext i; simp [restrict4]

lemma restrict4_mono {S T : Finset (Fin 6)} (h : S ⊆ T) : restrict4 S ⊆ restrict4 T := by
  intro i; simp only [restrict4, Finset.mem_filter, Finset.mem_univ, true_and]; exact fun hi => h hi

/-- **`cl(cone L_6) ⊊ Γ_6`**: lifting the 4-element Ingleton-violating polymatroid
(`Known.exists_polymatroid_not_ingleton`) to 6 elements gives a polymatroid outside the cone. -/
theorem exists_polymatroid6_not_in_cone :
    ∃ h : Finset (Fin 6) → ℝ, IsPolymatroid 6 h ∧ ¬ InClosedLinearRankCone 6 h := by
  obtain ⟨g, ⟨hg0, hgm, hgs⟩, hgI⟩ := exists_polymatroid_not_ingleton
  refine ⟨fun S => g (restrict4 S), ⟨?_, ?_, ?_⟩, ?_⟩
  · show g (restrict4 ∅) = 0
    rw [show restrict4 ∅ = ∅ by decide]; exact hg0
  · intro S T hST; exact hgm _ _ (restrict4_mono hST)
  · intro S T
    show g (restrict4 (S ∪ T)) + g (restrict4 (S ∩ T)) ≤ g (restrict4 S) + g (restrict4 T)
    rw [restrict4_union, restrict4_inter]; exact hgs _ _
  · intro hcone
    have := cone6_ingletonAt hcone {0} {1} {2} {3}
    unfold IngletonAt at this
    simp only [show restrict4 {0} = {0} by decide, show restrict4 {1} = {1} by decide,
      show restrict4 ({2} ∪ {3}) = {2, 3} by decide, show restrict4 ({0} ∪ {1}) = {0, 1} by decide,
      show restrict4 ({0} ∪ {1} ∪ {2}) = {0, 1, 2} by decide,
      show restrict4 ({0} ∪ {1} ∪ {3}) = {0, 1, 3} by decide,
      show restrict4 ({0} ∪ {2}) = {0, 2} by decide, show restrict4 ({0} ∪ {3}) = {0, 3} by decide,
      show restrict4 ({1} ∪ {2}) = {1, 2} by decide,
      show restrict4 ({1} ∪ {3}) = {1, 3} by decide] at this
    exact hgI this

/-- A nonzero linear rank vector on 6 variables: all `V_i` equal to `GF(2)^1`, so
`h(S) = 1` for `S ≠ ∅` (the rank function of the rank-1 uniform matroid). -/
theorem isLinearRankVector_uniformRankOne :
    IsLinearRankVector 6 (fun S => if S = ∅ then 0 else 1) := by
  refine ⟨2, 1, 1, ⟨Nat.prime_two⟩, one_pos, 1, fun _ => ⊤, one_pos, fun S => ?_⟩
  beta_reduce
  by_cases hS : S = ∅
  · subst hS
    have hbot : (⨆ j ∈ (∅ : Finset (Fin 6)),
        (⊤ : Submodule (GaloisField 2 1) (Fin 1 → GaloisField 2 1))) = ⊥ := by simp
    rw [hbot]; simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
    have htop : (⨆ j ∈ S, (⊤ : Submodule (GaloisField 2 1) (Fin 1 → GaloisField 2 1))) = ⊤ :=
      top_le_iff.1 (le_iSup₂_of_le i hi le_rfl)
    simp only [hS, ite_false]
    rw [htop, finrank_top, Module.finrank_fin_fun]
    norm_num

/-- The cone contains a nonzero vector. -/
theorem cone6_ne_zero : ∃ h : Finset (Fin 6) → ℝ, InClosedLinearRankCone 6 h ∧ h ≠ 0 :=
  ⟨_, linearRank_mem_cone isLinearRankVector_uniformRankOne, fun h0 => by
    have := congrFun h0 {0}
    simp at this⟩

end InfoTheory.Known.Certificates.LinearRankEntropyRegionN6
