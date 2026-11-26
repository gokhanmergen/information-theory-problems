import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.TraceReconstructionWorstCase

/-- Open problem: Does worst-case binary trace reconstruction at deletion probability
    `d = 1/2` have polynomial sample complexity `T_wc(n, 1/2) = O(n^c)`? -/
def Statement : Prop :=
  ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (traceReconWorstCaseSamples n (1 / 2 : ℝ) : ℝ) ≤ C * (n : ℝ) ^ c

def problem : OpenProblem where
  id := "trace-reconstruction-worst-case"
  title := "Sample Complexity of Worst-Case Binary Trace Reconstruction"
  category := .codingTheory
  status := .open
  posedBy := "Tugkan Batu, Sampath Kannan, Sanjeev Khanna, and Andrew McGregor"
  posedYear := 2004
  statement := Statement

end InfoTheory.Problems.TraceReconstructionWorstCase
