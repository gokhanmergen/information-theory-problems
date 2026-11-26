import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.LocallyCorrectableCodesConstantRate

/-- Open problem: Do there exist constant-rate binary linear Locally Correctable Codes
    with constant noise tolerance `δ > 0`, constant advantage `ε > 0`, and polylogarithmic
    query complexity `q = O((log n)^c)`? -/
def Statement : Prop :=
  ∃ (R δ ε C : ℝ) (c : ℕ), 0 < R ∧ 0 < δ ∧ 0 < ε ∧ 0 < C ∧
    ∀ N : ℕ, ∃ (n k q : ℕ), N ≤ n ∧
      R * (n : ℝ) ≤ (k : ℝ) ∧
      (q : ℝ) ≤ C * (Real.log (n : ℝ)) ^ c ∧
      IsBinaryLCC n k q δ ε

def problem : OpenProblem where
  id := "locally-correctable-codes-constant-rate"
  title := "Optimal Query Complexity of Constant-Rate Binary Locally Correctable Codes"
  category := .codingTheory
  status := .open
  posedBy := "Swastik Kopparty, Or Meir, Noga Ron-Zewi, and Shubhangi Saraf"
  posedYear := 2017
  statement := Statement

end InfoTheory.Problems.LocallyCorrectableCodesConstantRate
