import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.EntropyRegion

/-- Zhang–Yeung (1998) non-Shannon inequality for 4 random variables `h : 2^{Fin 4} → ℝ`. -/
def satisfiesZhangYeung (h : Finset (Fin 4) → ℝ) : Prop :=
  let I (A B : Finset (Fin 4)) : ℝ := h A + h B - h (A ∪ B)
  let cI (A B C : Finset (Fin 4)) : ℝ := h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C
  2 * I {2} {3} ≤ I {0} {1} + I {0} ({2, 3} : Finset (Fin 4)) + 3 * cI {2} {3} {0} + cI {2} {3} {1}

/-- Characterizing `cl(Γ*_4)` (Zhang–Yeung 1998; Matúš 2007): the almost-entropic cone of four
    random variables is strictly smaller than the Shannon (polymatroid) cone `Γ_4` (Zhang–Yeung)
    and is not polyhedral (Matúš 2007: infinitely many independent linear information
    inequalities). Whether it nonetheless has a finite algebraic description is open
    (Mejía–Montoya, arXiv:1510.02658, claim it does not; the argument is regarded as resting
    on an unproved exponential information inequality — see the catalog entry). We
    formalize this as: is `cl(Γ*_4)` a semialgebraic set in `ℝ^{2^4}`, i.e. a finite union of
    sets cut out by finitely many polynomial inequalities `0 ≤ P(h)`? -/
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
