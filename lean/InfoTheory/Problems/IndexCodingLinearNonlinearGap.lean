import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.IndexCodingLinearNonlinearGap

/-- Achievability of vector linear index coding rate `r` over a finite field `F`. -/
def HasFieldLinearIndexRate (F : Type) [Field F] [Fintype F] {n : ℕ}
    (inst : IndexCodingInstance n) (r : ℝ) : Prop :=
  ∃ (t m : ℕ), 0 < t ∧
    ∃ (enc : (Fin n → Fin t → F) →ₗ[F] (Fin m → F))
      (dec : ∀ i : Fin n, (Fin m → F) → (Fin n → Fin t → F) → (Fin t → F)),
      (∀ i c x y, (∀ j : Fin n, inst.sideInfo i j → x j = y j) → dec i c x = dec i c y) ∧
      (∀ x i, dec i (enc x) x = x i) ∧
      r = (m : ℝ) / (t : ℝ)

/-- Optimal field-independent vector linear index coding rate `β_lin(G)`: infimum over all
    finite fields `F` and vector lengths `t ≥ 1` of the broadcast rate `m / t` of an `F`-linear
    index code for `inst` (generalizing `linearIndexCodingRate` from `𝔽₂` to arbitrary finite
    fields). -/
noncomputable def fieldLinearIndexCodingRate {n : ℕ} (inst : IndexCodingInstance n) : ℝ :=
  sInf { r : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F),
    @HasFieldLinearIndexRate F hF hFin n inst r }

/-- Open problem: Can the multiplicative separation `β_lin(G) / β(G)` between field-independent
    vector linear index coding and nonlinear index coding on `n`-vertex side-information graphs
    reach `Ω(n^(1 - ε))` for every `ε > 0`? -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ (n : ℕ) (inst : IndexCodingInstance n),
    N ≤ n ∧ 0 < n ∧
    (n : ℝ) ^ (1 - ε) * indexCodingBroadcastRate inst ≤ fieldLinearIndexCodingRate inst

def problem : OpenProblem where
  id := "index-coding-linear-nonlinear-gap"
  title := "Optimal Asymptotic Separation Between Linear and Nonlinear Index Coding Rates"
  category := .networkCoding
  status := .partiallySolved
  posedBy := "Erez Lubetzky and Uri Stav; Anna Blasiak, Robert Kleinberg, and Eyal Lubetzky"
  posedYear := 2009
  statement := Statement

end InfoTheory.Problems.IndexCodingLinearNonlinearGap
