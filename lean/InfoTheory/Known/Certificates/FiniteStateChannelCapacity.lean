import InfoTheory.Problems.FiniteStateChannelCapacity
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.FiniteStateChannelCapacity`

The Statement asks whether every indecomposable finite-state channel attains its non-feedback
capacity with a finite-order Markov input (Gallager, *Information Theory and Reliable
Communication*, 1968, §4.6; Vontobel–Kavčić–Arnold–Loeliger, IEEE Trans. IT 54(5), 2008;
widely believed false, unproved either way). This file checks that the hypothesis
`IsIndecomposable` (Gallager's Theorem 4.6.3 criterion) classifies the two textbook cases
correctly, so the Statement's quantifier ranges over the intended class.

## Certified
* `isIndecomposable_single_state`: **regression** — every single-state channel (a DMC) is
  indecomposable.
* `frozenChannel`, `stateReachProb_frozen`, `frozenChannel_not_indecomposable`:
  **regression** — the channel whose state never moves (Gallager's standard decomposable
  example) is *not* indecomposable, for every input/output alphabet size. Hence the
  hypothesis is neither vacuous nor trivially satisfied.

## Not certified
* Normalisation of `blockTrans`, boundedness of `fscMaxMinMI` (so that `fscCapacity` and
  `fscMarkovRate` are genuine `liminf`s rather than junk `sSup` values), Gallager's theorem
  that upper and lower capacities coincide for indecomposable channels, and the DMC special
  case of the Statement (i.i.d. inputs, memory `M = 0`, attain capacity).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.FiniteStateChannelCapacity

open InfoTheory InfoTheory.Problems.FiniteStateChannelCapacity

/-- **Regression.** A single-state channel (a DMC) is indecomposable. -/
theorem isIndecomposable_single_state {kX kY : ℕ} (W : FiniteStateChannel kX kY 1) :
    IsIndecomposable W := by
  refine ⟨1, le_rfl, fun x => ⟨0, fun s₀ => ?_⟩⟩
  have h1 : (W.step (x 0) s₀).snd.pmf 0 = 1 := by
    have := (W.step (x 0) s₀).snd.sum_one
    simpa using this
  simp [stateReachProb, h1]

/-- Point mass on `(0, s)`: output `0`, state unchanged. -/
def frozenStep (kY : ℕ) (s : Fin 2) : ProbDist (Fin (kY + 1) × Fin 2) where
  pmf := fun p => if p = (0, s) then 1 else 0
  nonneg := fun p => by split_ifs <;> norm_num
  sum_one := by simp

/-- The channel whose state never changes: Gallager's decomposable example. -/
def frozenChannel (kX kY : ℕ) : FiniteStateChannel kX (kY + 1) 2 where
  step := fun _ s => frozenStep kY s

lemma frozen_snd (kX kY : ℕ) (a : Fin kX) (s s₁ : Fin 2) :
    ((frozenChannel kX kY).step a s).snd.pmf s₁ = if s₁ = s then 1 else 0 := by
  simp only [frozenChannel, frozenStep, ProbDist.snd, Prod.mk.injEq]
  by_cases h : s₁ = s
  · simp [h]
  · simp [h]

/-- In the frozen channel the state after `N` steps is the initial state. -/
theorem stateReachProb_frozen (kX kY : ℕ) :
    ∀ (N : ℕ) (x : Fin N → Fin kX) (s₀ sF : Fin 2),
      stateReachProb (frozenChannel kX kY) N x s₀ sF = if s₀ = sF then 1 else 0
  | 0, _, _, _ => rfl
  | N + 1, x, s₀, sF => by
      rw [stateReachProb]
      simp only [frozen_snd, stateReachProb_frozen kX kY N, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Regression.** The frozen-state channel is not indecomposable (for `kX ≥ 1`). -/
theorem frozenChannel_not_indecomposable (kX kY : ℕ) :
    ¬ IsIndecomposable (frozenChannel (kX + 1) kY) := by
  rintro ⟨N, -, h⟩
  obtain ⟨sStar, hs⟩ := h (fun _ => 0)
  have h0 := hs 0
  have h1 := hs 1
  rw [stateReachProb_frozen] at h0 h1
  by_cases e0 : (0 : Fin 2) = sStar
  · have e1 : ¬ (1 : Fin 2) = sStar := by rw [← e0]; decide
    simp [e1] at h1
  · simp [e0] at h0

end InfoTheory.Known.Certificates.FiniteStateChannelCapacity
