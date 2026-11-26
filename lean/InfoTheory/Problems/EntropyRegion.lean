import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.EntropyRegion

/-- Zhang–Yeung (1998) non-Shannon inequality for 4 random variables `h : 2^{Fin 4} → ℝ`. -/
def satisfiesZhangYeung (h : Finset (Fin 4) → ℝ) : Prop :=
  let I (A B : Finset (Fin 4)) : ℝ := h A + h B - h (A ∪ B)
  let cI (A B C : Finset (Fin 4)) : ℝ := h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C
  2 * I {2} {3} ≤ I {0} {1} + I {0} ({2, 3} : Finset (Fin 4)) + 3 * cI {2} {3} {0} + cI {2} {3} {1}

/-- Characterizing `cl(Γ*_4)`: whether the almost-entropic cone `cl(Γ*_4)` coincides with
    the closure of the cone of all linearly representable (group/subspace-rank) entropy
    vectors, or equivalently admits a complete copy-lemma / finite-group characterization.
    Here we formalize the famous open conjecture (Chan–Yeung 2002 / Matúš 2007) asking whether
    every vector in `cl(Γ*_4)` is a limit of linear-rank (Ingleton-obeying? No, Ingleton fails
    for non-linear entropic vectors!) — specifically, we formalize the exact open question of
    whether every 4-variable almost-entropic vector satisfies all finite-order copy-lemma
    inequalities AND conversely whether the copy-lemma cone equals `cl(Γ*_4)`:
    framed concretely as whether `cl(Γ*_4)` is a semialgebraic set in `ℝ^{15}`. -/
def IsSemialgebraic4 (S : Set (Finset (Fin 4) → ℝ)) : Prop :=
  ∃ (m k : ℕ) (P : Fin m → Fin k → (Finset (Fin 4) → ℝ) → ℝ),
    (∀ i j, ∃ (d : ℕ) (coeff : (Finset (Fin 4) → Fin (d + 1)) → ℝ),
      ∀ h, P i j h = ∑ e : Finset (Fin 4) → Fin (d + 1),
        coeff e * ∏ A : Finset (Fin 4), (h A) ^ (e A).1) ∧
    ∀ h, h ∈ S ↔ ∃ i : Fin m, ∀ j : Fin k, 0 ≤ P i j h

/-- Open question (Zhang–Yeung 1998; Matúš 2007): Is the 4-variable almost-entropic cone
    `cl(Γ*_4)` a semialgebraic cone in `ℝ^{2^4}`? (Known non-polyhedral by Matúš 2007;
    algebraic/semialgebraic character of its boundary remains open.) -/
def Statement : Prop :=
  IsSemialgebraic4 { h : Finset (Fin 4) → ℝ | InAlmostEntropicCone 4 h }

def problem : OpenProblem where
  id := "entropy-region"
  title := "Characterize the Entropy Region for Four or More Random Variables"
  category := .entropyInequalities
  status := .open
  posedBy := "Zhang and Yeung (explicitly); implicit in Pippenger"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.EntropyRegion
