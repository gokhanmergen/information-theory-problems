import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ReedMullerCapacityGeneralDmc

/-- Multilinear monomial `∏ j ∈ S, x j` evaluated on `x : Fin m → ZMod 2`. -/
def rmMonomial (m : ℕ) (S : Finset (Fin m)) (x : Fin m → ZMod 2) : ZMod 2 :=
  ∏ j ∈ S, x j

/-- Binary Reed–Muller code `RM(m, r)` of blocklength `2^m` as the `𝔽₂`-subspace of
    Boolean functions spanned by all monomials of degree at most `r`. -/
def reedMullerCode (m r : ℕ) : Submodule (ZMod 2) ((Fin m → ZMod 2) → ZMod 2) :=
  Submodule.span (ZMod 2)
    { f : (Fin m → ZMod 2) → ZMod 2 | ∃ S : Finset (Fin m), S.card ≤ r ∧ f = rmMonomial m S }

/-- Average block decoding error of a finite binary code `C` (of length `2^m`, indexed by
    `Fin m → ZMod 2`) over `2^m` independent uses of a binary-input DMC `W : DMC Bool (Fin k)`
    under a decoder `dec`. -/
noncomputable def rmBlockError {k : ℕ} (W : DMC Bool (Fin k)) (m : ℕ)
    (C : Finset ((Fin m → ZMod 2) → ZMod 2))
    (dec : ((Fin m → ZMod 2) → Fin k) → ((Fin m → ZMod 2) → ZMod 2)) : ℝ :=
  if C.card = 0 then 0 else
    ((1 : ℝ) / (C.card : ℝ)) *
      ∑ c ∈ C, ∑ y : (Fin m → ZMod 2) → Fin k,
        if dec y ≠ c then
          ∏ x : Fin m → ZMod 2, W.trans (decide (c x = 1)) (y x)
        else 0

/-- Open problem: Do binary Reed–Muller codes achieve the uniform-input mutual information
    `I(U; Y)` under block-MAP decoding on every (possibly asymmetric) binary-input DMC `W`?
    (Solved for all BMS channels by Reeves–Pfister 2021 and Abbe–Sandon 2023; open for
    general asymmetric binary-input DMCs.) -/
def Statement : Prop :=
  ∀ (k : ℕ) (W : DMC Bool (Fin k)) (R ε : ℝ),
    0 < k → 0 ≤ R → R < W.mutualInfo ProbDist.uniform → 0 < ε →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (r : ℕ) (C : Finset ((Fin m → ZMod 2) → ZMod 2))
        (dec : ((Fin m → ZMod 2) → Fin k) → ((Fin m → ZMod 2) → ZMod 2)),
        r ≤ m ∧
        (∀ c : (Fin m → ZMod 2) → ZMod 2, c ∈ C ↔ c ∈ reedMullerCode m r) ∧
        R ≤ (Module.finrank (ZMod 2) (reedMullerCode m r) : ℝ) / ((2 ^ m : ℕ) : ℝ) ∧
        rmBlockError W m C dec ≤ ε

def problem : OpenProblem where
  id := "reed-muller-capacity-general-dmc"
  title := "Capacity Achievement of Reed–Muller Codes on General Binary-Input DMCs"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "D. J. Costello; G. D. Forney; E. Abbe; A. Shpilka; A. Wigderson"
  posedYear := 1994
  statement := Statement

end InfoTheory.Problems.ReedMullerCapacityGeneralDmc
