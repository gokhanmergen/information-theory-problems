import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.TraceReconstructionAverageCase

/-- Average-case trace reconstruction sample complexity `T_avg(n, d)`: minimum number `T > 0`
    of independent traces from `Del_d(X)` needed to reconstruct a uniformly random binary
    string `X ∈ {0,1}^n` with success probability at least `2/3`. -/
noncomputable def traceReconAvgCaseSamples (n : ℕ) (d : ℝ) : ℕ :=
  sInf { T : ℕ | 0 < T ∧
    ∃ dec : (Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool) → (Fin n → Bool),
      let successProb : ℝ :=
        ((1 : ℝ) / ((2 ^ n : ℕ) : ℝ)) *
          ∑ x : Fin n → Bool,
            ∑ tr : Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool,
              if dec tr = x then
                ∏ t : Fin T, deletionProb d (List.ofFn x) (List.ofFn (tr t).2)
              else 0
      2 / 3 ≤ successProb }

/-- Open problem: Does average-case binary trace reconstruction at deletion probability
    `d = 1/2` have polylogarithmic sample complexity `T_avg(n, 1/2) = O((log n)^c)`? -/
def Statement : Prop :=
  ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      (traceReconAvgCaseSamples n (1 / 2 : ℝ) : ℝ) ≤ C * (Real.log (n : ℝ)) ^ c

def problem : OpenProblem where
  id := "trace-reconstruction-average-case"
  title := "Sample Complexity of Average-Case Binary Trace Reconstruction"
  category := .codingTheory
  status := .open
  posedBy := "Tugkan Batu, Sampath Kannan, Sanjeev Khanna, and Andrew McGregor"
  posedYear := 2004
  statement := Statement

end InfoTheory.Problems.TraceReconstructionAverageCase
