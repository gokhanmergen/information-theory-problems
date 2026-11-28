import InfoTheory.Problems.EntropyRegionDecidability
import InfoTheory.Known.Entropy
import InfoTheory.Known.EntropyRegion

/-!
# Certificate for `InfoTheory.Problems.EntropyRegionDecidability`

The frozen statement asks for a register machine that, given a nonnegative rational vector
`v : 2^[4] → ℕ × ℕ` (numerator, positive denominator) loaded into registers `0..31`, halts and
answers whether `h = (num / den)_S` lies in the closed almost-entropic cone `cl(Γ*_4)`
(`InAlmostEntropicCone 4 h`). The certificate checks the instance encoding and that the
decision problem is non-degenerate (both answers occur, on the instances one expects).

## Certified
* `subsetOfMask_surjective`, `subsetOfMask_injective`: the 4-bit masks `0..15` enumerate
  the 16 subsets of `{0,1,2,3}` bijectively, so `initRegs` loads **every** coordinate of `h`
  exactly once.
* `initRegs_num`, `initRegs_den`: register `2k` holds the numerator and register `2k+1` the
  denominator of `h(subsetOfMask k)`.
* `query_zero_mem`: the zero vector is a YES instance (four constant random variables).
* `query_diag_mem`: the vector `h(S) = 1` for `S ≠ ∅` (`h(∅) = 0`) is a YES instance: it is
  the entropy vector of four copies of one fair bit (computed from scratch, via
  `Known.shannonEntropy_uniform` and `Known.MapEntropy.entropy_map_eq_of_ker`).
* `query_ones_not_mem`: the all-ones vector (`h(∅) = 1`) is a NO instance.
* `query_nonmono_not_mem`: `h({0}) = 1`, `h = 0` elsewhere is a NO instance (violates
  monotonicity, a Shannon inequality; via `Known.almostEntropic_isPolymatroid`).
* `exists_yes_and_no_instances`: hence the predicate being decided is neither constantly true
  nor constantly false on encodable inputs; the Statement is not trivially satisfied by a
  constant machine.

## Adversarial check (2026-11-27)
The Statement is faithful and open. For `n ≤ 3`, `cl(Γ*_n) = Γ_n` is polyhedral and
membership is trivially decidable; for `n = 4` the cone is not polyhedral (Matúš, ISIT 2007),
and no decision procedure is known. The undecidability results of C. T. Li (IEEE Trans. Inf.
Theory 69(6), 2023, arXiv:2205.11461: network coding, conditional information inequalities,
conditional independence implication) and of Kühne–Yashfe (vector-linear network coding /
matroid representability) need an unbounded number of random variables and constraints of
conditional/affine type; neither settles membership of a rational point in the *fixed*
four-variable cone `cl(Γ*_4)`. The input format (exact nonnegative rationals, unary-free
register encoding) is the standard one for decidability of a subset of `ℚ^16`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.EntropyRegionDecidability

open InfoTheory InfoTheory.Known InfoTheory.Problems.EntropyRegionDecidability

/-- The 16 masks `0..15` hit every subset of `Fin 4`. -/
theorem subsetOfMask_surjective : ∀ S : Finset (Fin 4), ∃ k < 16, subsetOfMask k = S := by
  unfold subsetOfMask
  decide

/-- The 16 masks `0..15` give pairwise distinct subsets. -/
theorem subsetOfMask_injective :
    ∀ k₁ < 16, ∀ k₂ < 16, subsetOfMask k₁ = subsetOfMask k₂ → k₁ = k₂ := by
  unfold subsetOfMask
  decide

/-- Register `2k` holds the numerator of `h(subsetOfMask k)`. -/
theorem initRegs_num (numRegs : ℕ) (hR : 32 ≤ numRegs) (v : Finset (Fin 4) → ℕ × ℕ)
    (k : ℕ) (hk : k < 16) :
    initRegs numRegs v ⟨2 * k, by omega⟩ = (v (subsetOfMask k)).1 := by
  simp only [initRegs]
  rw [if_pos (by omega), if_pos (by omega)]
  congr 3
  omega

/-- Register `2k + 1` holds the denominator of `h(subsetOfMask k)`. -/
theorem initRegs_den (numRegs : ℕ) (hR : 32 ≤ numRegs) (v : Finset (Fin 4) → ℕ × ℕ)
    (k : ℕ) (hk : k < 16) :
    initRegs numRegs v ⟨2 * k + 1, by omega⟩ = (v (subsetOfMask k)).2 := by
  simp only [initRegs]
  rw [if_pos (by omega), if_neg (by omega)]
  congr 3
  omega

/-- The real vector `h` described by a query `v`, exactly as in the Statement. -/
noncomputable def queryVec (v : Finset (Fin 4) → ℕ × ℕ) : Finset (Fin 4) → ℝ :=
  fun S => ((v S).1 : ℝ) / ((v S).2 : ℝ)

/-- **YES instance:** the zero vector. -/
theorem query_zero_mem : InAlmostEntropicCone 4 (queryVec fun _ => (0, 1)) := by
  intro ε hε
  refine ⟨fun _ => 0, ⟨1, ProbDist.uniform, fun S => ?_⟩, fun S => by simpa [queryVec] using hε⟩
  symm
  exact MapEntropy.entropy_map_eq_zero_of_const _ fun x y => by rw [Subsingleton.elim x y]

private lemma map_map {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProbDist α) (f : α → β) (g : β → γ) : (P.map f).map g = P.map (g ∘ f) := by
  classical
  have : ((P.map f).map g).pmf = (P.map (g ∘ f)).pmf := by
    funext c
    simp only [ProbDist.map, Function.comp]
    rw [show (∑ b : β, if g b = c then ∑ a : α, (if f a = b then P.pmf a else 0) else 0)
        = ∑ b : β, ∑ a : α, if f a = b then (if g b = c then P.pmf a else 0) else 0 from by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [*]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  cases h1 : (P.map f).map g
  cases h2 : P.map (g ∘ f)
  rw [h1, h2] at this
  simp only at this
  subst this
  rfl

private lemma entropy_map_id {α : Type*} [Fintype α] (P : ProbDist α) :
    shannonEntropy (P.map id) = shannonEntropy P := by
  classical
  unfold shannonEntropy ProbDist.map
  simp

/-- Four copies of one fair bit. -/
noncomputable def diagDist : ProbDist (Fin 4 → Fin 2) :=
  (ProbDist.uniform : ProbDist (Fin 2)).map (fun b _ => b)

/-- The entropy vector of `diagDist` is `h(S) = 1` for `S ≠ ∅`, `h(∅) = 0`. -/
theorem subsetEntropyVec_diagDist (S : Finset (Fin 4)) :
    subsetEntropyVec diagDist S = if S = ∅ then 0 else 1 := by
  unfold subsetEntropyVec diagDist
  rw [map_map]
  split_ifs with hS
  · exact MapEntropy.entropy_map_eq_zero_of_const _ fun x y => by
      funext i
      exact absurd i.2 (by simp [hS])
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hS
    rw [MapEntropy.entropy_map_eq_of_ker (f := id), entropy_map_id, shannonEntropy_uniform]
    · simp [log2]; norm_num
    · intro x y
      simp only [Function.comp, id]
      constructor
      · rintro rfl; rfl
      · intro h
        exact congrFun h ⟨j, hj⟩

/-- **YES instance:** the entropy vector of four copies of a fair bit. -/
theorem query_diag_mem :
    InAlmostEntropicCone 4 (queryVec fun S => (if S = ∅ then 0 else 1, 1)) := by
  intro ε hε
  refine ⟨subsetEntropyVec diagDist, ⟨2, diagDist, fun S => rfl⟩, fun S => ?_⟩
  rw [subsetEntropyVec_diagDist]
  by_cases hS : S = ∅ <;> simp [queryVec, hS, hε]

/-- **NO instance:** the all-ones vector (`h(∅) = 1 ≠ 0`). -/
theorem query_ones_not_mem : ¬ InAlmostEntropicCone 4 (queryVec fun _ => (1, 1)) := by
  intro h
  have := (almostEntropic_isPolymatroid h).1
  simp [queryVec] at this

/-- **NO instance:** `h({0}) = 1`, `h = 0` elsewhere (violates monotonicity). -/
theorem query_nonmono_not_mem :
    ¬ InAlmostEntropicCone 4 (queryVec fun S => (if S = {0} then 1 else 0, 1)) := by
  intro h
  have := (almostEntropic_isPolymatroid h).2.1 {0} {0, 1} (by decide)
  have h01 : ({0, 1} : Finset (Fin 4)) ≠ {0} := by decide
  simp [queryVec, h01] at this
  exact absurd this (by norm_num)

/-- Both answers occur on encodable inputs with positive denominators: the predicate the
machine must decide is not constant. -/
theorem exists_yes_and_no_instances :
    (∃ v : Finset (Fin 4) → ℕ × ℕ, (∀ S, 0 < (v S).2) ∧ InAlmostEntropicCone 4 (queryVec v)) ∧
    (∃ v : Finset (Fin 4) → ℕ × ℕ, (∀ S, 0 < (v S).2) ∧ ¬ InAlmostEntropicCone 4 (queryVec v)) :=
  ⟨⟨_, fun _ => Nat.one_pos, query_diag_mem⟩, ⟨_, fun _ => Nat.one_pos, query_ones_not_mem⟩⟩

end InfoTheory.Known.Certificates.EntropyRegionDecidability
