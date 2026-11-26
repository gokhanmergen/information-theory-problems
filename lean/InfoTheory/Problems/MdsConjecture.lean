import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MdsConjecture

/-- The MDS Conjecture (Segre 1955): for every finite field `F` of order `q = |F|` and every
    linear `[n, k, n - k + 1]_F` MDS code with `2 ≤ k ≤ q - 1`, we have `n ≤ q + 1`, except
    when `q` is even and `k ∈ {3, q - 1}`, in which case `n ≤ q + 2`. -/
def Statement : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n k : ℕ),
    let q : ℕ := Fintype.card F
    2 ≤ k → k ≤ q - 1 → IsLinearMDSCode F n k →
    if q % 2 = 0 ∧ (k = 3 ∨ k = q - 1) then n ≤ q + 2 else n ≤ q + 1

def problem : OpenProblem where
  id := "mds-conjecture"
  title := "The MDS Conjecture"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "Beniamino Segre"
  posedYear := 1955
  statement := Statement

end InfoTheory.Problems.MdsConjecture
