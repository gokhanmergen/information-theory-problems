import InfoTheory.Problems.EntropyRegion
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.EntropyRegion`

The frozen statement asks whether the four-variable almost-entropic cone
`{h | InAlmostEntropicCone 4 h}` = `cl(Γ*_4)` is semialgebraic (`IsSemialgebraic4`). The file
also defines the Zhang–Yeung inequality `satisfiesZhangYeung` (Zhang–Yeung, "On
characterization of entropy function via information inequalities", IEEE Trans. Inf. Theory
44(4), 1998, Thm. 3), which the Statement does not use but whose docstring role is to witness
that `cl(Γ*_4) ⊊ Γ_4`.

## Certified
* `almostEntropic4_subset_polymatroid`: `cl(Γ*_4) ⊆ Γ_4`, the set in the Statement lies in the
  Shannon polymatroid cone (Yeung, *Information Theory and Network Coding*, 2008, Ch. 13–15;
  via `Known.almostEntropic_isPolymatroid`).
* `zero_mem_almostEntropic4`: the set in the Statement is nonempty (it contains the entropy
  vector of a deterministic quadruple), so the Statement is not about an empty set.
* `zyViolator_isPolymatroid`, `zyViolator_not_satisfiesZhangYeung`,
  `exists_polymatroid_not_zhangYeung`: the Zhang–Yeung inequality, as formalized in
  `satisfiesZhangYeung`, is **not** implied by the polymatroid axioms. The witness
  (found by a small LP search) is the integer polymatroid with `h(i) = 2`, `h({0,1}) = 4`,
  `h(ij) = 3` for the other pairs, and `h = 4` on sets of size `≥ 3`; for it the two sides of
  Zhang–Yeung are `2·I(2;3) = 2 > 1 = I(0;1) + I(0;23) + 3 I(2;3|0) + I(2;3|1)`. So the
  formalized inequality is a genuine non-Shannon constraint, as it should be.

## Regression
* `regression_polymatroid_semialgebraic`: the frozen predicate `IsSemialgebraic4` accepts the
  Shannon cone `Γ_4` (a polyhedral cone, hence semialgebraic: one piece cut out by the finitely
  many linear Shannon inequalities, encoded as degree-1 polynomials in the problem's monomial
  format). So the predicate returns the known answer on the solved polyhedral benchmark and is
  not unsatisfiable by construction; `regression_univ_semialgebraic` does the same for `ℝ^{16}`.

## Not certified
* `satisfiesZhangYeung` holds on `Γ*_4` (hence on `cl(Γ*_4)`): this needs the copy lemma
  (Zhang–Yeung 1998; Dougherty–Freiling–Zeger 2011), which `Known` does not provide. It was
  not attempted.
* Matúš's theorem that `cl(Γ*_4)` is not polyhedral (Matúš, "Infinitely many information
  inequalities", ISIT 2007), which is what makes the semialgebraicity question non-trivial.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.EntropyRegion

open InfoTheory InfoTheory.Problems.EntropyRegion

/-- **`cl(Γ*_4) ⊆ Γ_4`** for exactly the set used in the Statement (Yeung 2008, Ch. 13–15;
reuses `Known.almostEntropic_isPolymatroid`). -/
theorem almostEntropic4_subset_polymatroid :
    { h : Finset (Fin 4) → ℝ | InAlmostEntropicCone 4 h } ⊆ { h | IsPolymatroid 4 h } :=
  fun _ hh => almostEntropic_isPolymatroid hh

/-- The zero vector is entropic (four deterministic random variables). -/
theorem zero_isEntropic4 : IsEntropicVector 4 (fun _ => 0) := by
  refine ⟨1, ProbDist.uniform, fun S => ?_⟩
  symm
  exact MapEntropy.entropy_map_eq_zero_of_const _ fun x y => by
    rw [Subsingleton.elim x y]

/-- The set in the Statement is nonempty: it contains `0`. -/
theorem zero_mem_almostEntropic4 : InAlmostEntropicCone 4 (fun _ => 0) :=
  fun _ hε => ⟨_, zero_isEntropic4, fun S => by simpa using hε⟩

/-- An integer polymatroid on 4 elements violating Zhang–Yeung: `h(i) = 2`, `h({0,1}) = 4`,
`h(ij) = 3` for the other five pairs, and `h = 4` on all sets of size `≥ 3`. -/
def zyViolator (S : Finset (Fin 4)) : ℕ :=
  if S.card = 0 then 0 else if S.card = 1 then 2 else if S.card = 2 ∧ S ≠ {0, 1} then 3 else 4

/-- `zyViolator` (cast to `ℝ`) is a polymatroid, checked by `decide` over all pairs of subsets. -/
theorem zyViolator_isPolymatroid : IsPolymatroid 4 (fun S => (zyViolator S : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [zyViolator]
  · have key : ∀ S T : Finset (Fin 4), S ⊆ T → zyViolator S ≤ zyViolator T := by decide
    intro S T hST
    beta_reduce
    exact_mod_cast key S T hST
  · have key : ∀ S T : Finset (Fin 4),
        zyViolator (S ∪ T) + zyViolator (S ∩ T) ≤ zyViolator S + zyViolator T := by decide
    intro S T
    beta_reduce
    exact_mod_cast key S T

/-- `zyViolator` violates the Zhang–Yeung inequality as formalized in the problem file. -/
theorem zyViolator_not_satisfiesZhangYeung :
    ¬ satisfiesZhangYeung (fun S => (zyViolator S : ℝ)) := by
  unfold satisfiesZhangYeung
  have v2 : zyViolator {2} = 2 := by decide
  have v3 : zyViolator {3} = 2 := by decide
  have v0 : zyViolator {0} = 2 := by decide
  have v1 : zyViolator {1} = 2 := by decide
  have v23 : zyViolator ({2} ∪ {3}) = 3 := by decide
  have v01 : zyViolator ({0} ∪ {1}) = 4 := by decide
  have v0_23 : zyViolator ({0} ∪ {2, 3}) = 4 := by decide
  have v023 : zyViolator ({2, 3} : Finset (Fin 4)) = 3 := by decide
  have v20 : zyViolator ({2} ∪ {0}) = 3 := by decide
  have v30 : zyViolator ({3} ∪ {0}) = 3 := by decide
  have v230 : zyViolator ({2} ∪ {3} ∪ {0}) = 4 := by decide
  have v21 : zyViolator ({2} ∪ {1}) = 3 := by decide
  have v31 : zyViolator ({3} ∪ {1}) = 3 := by decide
  have v231 : zyViolator ({2} ∪ {3} ∪ {1}) = 4 := by decide
  simp only [v2, v3, v0, v1, v23, v01, v0_23, v023, v20, v30, v230, v21, v31, v231]
  norm_num

/-- **Zhang–Yeung is not a Shannon inequality** (Zhang–Yeung 1998): there is a polymatroid on
four elements violating `satisfiesZhangYeung`. -/
theorem exists_polymatroid_not_zhangYeung :
    ∃ h : Finset (Fin 4) → ℝ, IsPolymatroid 4 h ∧ ¬ satisfiesZhangYeung h :=
  ⟨_, zyViolator_isPolymatroid, zyViolator_not_satisfiesZhangYeung⟩

/-! ### Regression: `IsSemialgebraic4` accepts polyhedral cones -/

/-- Every affine functional `h ↦ b + ∑_A a(A) h(A)` has the polynomial form used in
`IsSemialgebraic4` (degree `d = 1`). -/
theorem affine_poly (a : Finset (Fin 4) → ℝ) (b : ℝ) :
    ∃ (d : ℕ) (coeff : (Finset (Fin 4) → Fin (d + 1)) → ℝ),
      ∀ h : Finset (Fin 4) → ℝ, b + ∑ A, a A * h A = ∑ e : Finset (Fin 4) → Fin (d + 1),
        coeff e * ∏ A : Finset (Fin 4), (h A) ^ (e A).1 := by
  classical
  refine ⟨1, fun e => (if e = 0 then b else 0) +
    ∑ A, (if e = Pi.single A 1 then a A else 0), fun h => ?_⟩
  have hmono0 : ∏ B : Finset (Fin 4), (h B) ^ ((0 : Finset (Fin 4) → Fin (1 + 1)) B).1 = 1 := by
    simp
  have hmono1 : ∀ A, ∏ B : Finset (Fin 4),
      (h B) ^ ((Pi.single A 1 : Finset (Fin 4) → Fin (1 + 1)) B).1 = h A := by
    intro A
    rw [Finset.prod_eq_single A]
    · simp
    · intro B _ hB; simp [hB]
    · intro hA; exact absurd (Finset.mem_univ A) hA
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hmono0, hmono1, mul_one]

/-- Indicator coefficient. -/
noncomputable def ind (T : Finset (Fin 4)) : Finset (Fin 4) → ℝ := fun A => if A = T then 1 else 0

lemma sum_ind (T : Finset (Fin 4)) (h : Finset (Fin 4) → ℝ) : ∑ A, ind T A * h A = h T := by
  simp [ind]

/-- The Shannon constraints defining `Γ_4`, indexed by
`Bool ⊕ (Finset × Finset) ⊕ (Finset × Finset)`. -/
noncomputable def shannonCoeff :
    Bool ⊕ (Finset (Fin 4) × Finset (Fin 4)) ⊕ (Finset (Fin 4) × Finset (Fin 4)) →
      Finset (Fin 4) → ℝ
  | Sum.inl true => ind ∅
  | Sum.inl false => fun A => - ind ∅ A
  | Sum.inr (Sum.inl (S, T)) => fun A => if S ⊆ T then ind T A - ind S A else 0
  | Sum.inr (Sum.inr (S, T)) => fun A => ind S A + ind T A - ind (S ∪ T) A - ind (S ∩ T) A

lemma polymatroid_iff_shannonCoeff (h : Finset (Fin 4) → ℝ) :
    IsPolymatroid 4 h ↔ ∀ c, 0 ≤ ∑ A, shannonCoeff c A * h A := by
  have e1 : ∑ A, shannonCoeff (Sum.inl true) A * h A = h ∅ := sum_ind _ _
  have e2 : ∑ A, shannonCoeff (Sum.inl false) A * h A = - h ∅ := by
    simp only [shannonCoeff, neg_mul, Finset.sum_neg_distrib, sum_ind]
  have e3 : ∀ S T, ∑ A, shannonCoeff (Sum.inr (Sum.inl (S, T))) A * h A =
      if S ⊆ T then h T - h S else 0 := by
    intro S T
    by_cases hST : S ⊆ T
    · simp only [shannonCoeff, hST, ite_true, sub_mul, Finset.sum_sub_distrib, sum_ind]
    · simp [shannonCoeff, hST]
  have e4 : ∀ S T, ∑ A, shannonCoeff (Sum.inr (Sum.inr (S, T))) A * h A =
      h S + h T - h (S ∪ T) - h (S ∩ T) := by
    intro S T
    simp only [shannonCoeff, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      sum_ind]
  constructor
  · rintro ⟨h0, hmono, hsub⟩ c
    rcases c with (_ | _) | (⟨S, T⟩ | ⟨S, T⟩)
    · rw [e2, h0]; simp
    · rw [e1, h0]
    · rw [e3]; split_ifs with hST
      · linarith [hmono S T hST]
      · exact le_rfl
    · rw [e4]; linarith [hsub S T]
  · intro hc
    refine ⟨?_, fun S T hST => ?_, fun S T => ?_⟩
    · have := hc (Sum.inl true); have := hc (Sum.inl false); rw [e1] at *; rw [e2] at *
      linarith
    · have := hc (Sum.inr (Sum.inl (S, T))); rw [e3] at this; simp only [hST, ite_true] at this; linarith
    · have := hc (Sum.inr (Sum.inr (S, T))); rw [e4] at this; linarith

/-- **Regression**: the polyhedral Shannon cone `Γ_4` is semialgebraic in the sense of the
frozen predicate `IsSemialgebraic4`. -/
theorem regression_polymatroid_semialgebraic :
    IsSemialgebraic4 { h : Finset (Fin 4) → ℝ | IsPolymatroid 4 h } := by
  classical
  let σ := Fintype.equivFin
    (Bool ⊕ (Finset (Fin 4) × Finset (Fin 4)) ⊕ (Finset (Fin 4) × Finset (Fin 4)))
  refine ⟨1, Fintype.card
    (Bool ⊕ (Finset (Fin 4) × Finset (Fin 4)) ⊕ (Finset (Fin 4) × Finset (Fin 4))), fun _ j h => ∑ A, shannonCoeff (σ.symm j) A * h A, fun _ j => ?_, fun h => ?_⟩
  · obtain ⟨d, coeff, hpoly⟩ := affine_poly (shannonCoeff (σ.symm j)) 0
    exact ⟨d, coeff, fun h => by rw [← hpoly, zero_add]⟩
  · simp only [Set.mem_ofPred_eq]
    rw [polymatroid_iff_shannonCoeff]
    constructor
    · intro hc; exact ⟨0, fun j => hc _⟩
    · rintro ⟨_, hj⟩ c
      simpa using hj (σ c)

/-- **Regression**: `ℝ^{16}` itself is semialgebraic (one piece, no constraints). -/
theorem regression_univ_semialgebraic : IsSemialgebraic4 Set.univ :=
  ⟨1, 0, fun _ j => j.elim0, fun _ j => j.elim0, fun h => by simp⟩

end InfoTheory.Known.Certificates.EntropyRegion
