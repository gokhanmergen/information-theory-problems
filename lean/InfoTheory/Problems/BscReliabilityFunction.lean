import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BscReliabilityFunction

/-- BSC Reliability Function Conjecture below the critical rate (Shannon–Gallager–Berlekamp
    1967; Gallager 1965): for every crossover probability `p ∈ (0, 1/2)` and every rate
    `0 < R < 1 - h(p)`, the reliability function `E(BSC(p), R)` equals
    `max(E_r(BSC(p), R), E_ex(BSC(p), R))`.
    (Known for `R ≥ R_crit(p)` and as `R → 0⁺`; open throughout `0 < R < R_crit(p)`.) -/
def Statement : Prop :=
  ∀ (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
    0 < p → p < 1 / 2 →
    ∀ (R : ℝ), 0 < R → R < 1 - binaryEntropy p →
      reliabilityFunction (bsc p h0 h1) R =
        max (randomCodingExponent (bsc p h0 h1) R)
            (expurgatedExponent (bsc p h0 h1) R)

def problem : OpenProblem where
  id := "bsc-reliability-function"
  title := "Exact Reliability Function of the Binary Symmetric Channel Below the Critical Rate"
  category := .channelCapacity
  status := .open
  posedBy := "Claude E. Shannon, Robert G. Gallager, and Elwyn R. Berlekamp"
  posedYear := 1967
  statement := Statement

end InfoTheory.Problems.BscReliabilityFunction
