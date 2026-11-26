import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ShannonCapacityC7

/-- The Shannon Capacity of the 7-Cycle (Shannon 1956; Lovász 1979):
    It is known that `367^{1/5} ≤ Θ(C₇) ≤ ϑ(C₇) = 7 cos(π/7) / (1 + cos(π/7)) ≈ 3.3177`.
    Does the Shannon capacity of `C₇` strictly fall below the Lovász theta bound `ϑ(C₇)`?
    (Resolving either `Θ(C₇) < ϑ(C₇)` or `Θ(C₇) = ϑ(C₇)` settles the core separation
    question for `C₇`.) -/
def Statement : Prop :=
  shannonCapacity (cycleGraph 7) < lovaszTheta (cycleGraph 7)

def problem : OpenProblem where
  id := "shannon-capacity-c7"
  title := "The Shannon Capacity of the 7-Cycle"
  category := .zeroError
  status := .open
  posedBy := "Claude Shannon"
  posedYear := 1956
  statement := Statement

end InfoTheory.Problems.ShannonCapacityC7
