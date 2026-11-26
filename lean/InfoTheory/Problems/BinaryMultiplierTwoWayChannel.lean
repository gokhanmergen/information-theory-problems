import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BinaryMultiplierTwoWayChannel

/-- Symmetric (equal-rate) operational capacity of Blackwell's Binary Multiplying Channel
    `Y₁ = Y₂ = X₁ · X₂`. -/
noncomputable def bmcSymmetricCapacity : ℝ :=
  sSup { R : ℝ | (R, R) ∈ twcCapacityRegion binaryMultiplyingChannel }

/-- Hekstra–Willems (1989) dependence-balance upper bound on the symmetric capacity of
    Blackwell's Binary Multiplying Channel (evaluates to ≈ 0.64628 bits). -/
noncomputable def bmcDependenceBalanceBound : ℝ :=
  sSup { r : ℝ | ∃ (kZ : ℕ) (P : ProbDist (Fin kZ × Bool × Bool)),
    let J : ProbDist (Fin kZ × Bool × Bool × Bool) :=
      P.map (fun t => (t.1, t.2.1, t.2.2, t.2.1 && t.2.2))
    let IX1X2_Z := condMutualInfo (J.map (fun t => (t.2.1, t.2.2.1, t.1)))
    let IX1X2_YZ := condMutualInfo (J.map (fun t => (t.2.1, t.2.2.1, (t.2.2.2, t.1))))
    let IX1Y_X2Z := condMutualInfo (J.map (fun t => (t.2.1, t.2.2.2, (t.2.2.1, t.1))))
    let IX2Y_X1Z := condMutualInfo (J.map (fun t => (t.2.2.1, t.2.2.2, (t.2.1, t.1))))
    IX1X2_Z ≤ IX1X2_YZ ∧ r = min IX1Y_X2Z IX2Y_X1Z }

/-- Symmetric Capacity of Blackwell's Binary Multiplying Channel (Blackwell / Shannon 1961;
    Hekstra–Willems 1989):
    Does the symmetric capacity of `binaryMultiplyingChannel` equal the Hekstra–Willems
    dependence-balance upper bound? -/
def Statement : Prop :=
  bmcSymmetricCapacity = bmcDependenceBalanceBound

def problem : OpenProblem where
  id := "binary-multiplier-two-way-channel"
  title := "Symmetric Capacity of Blackwell's Binary Multiplying Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "David Blackwell (via Claude E. Shannon)"
  posedYear := 1961
  statement := Statement

end InfoTheory.Problems.BinaryMultiplierTwoWayChannel
