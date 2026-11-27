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

end InfoTheory.Known.Certificates.EntropyRegion
