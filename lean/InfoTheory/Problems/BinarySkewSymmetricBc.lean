import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BinarySkewSymmetricBc

/-- Operational sum-rate capacity of the Binary Skew-Symmetric Broadcast Channel. -/
noncomputable def bsscSumCapacity : ℝ :=
  sSup { s : ℝ | ∃ p ∈ bcCapacityRegion binarySkewSymmetricBC, s = p.1 + p.2 }

/-- Maximum sum-rate achievable by Marton's inner bound on the BSSC
    (evaluates to ≈ 0.3616428 bits via Nair–Wang–Geng 2010). -/
noncomputable def bsscMartonSumRate : ℝ :=
  sSup { s : ℝ | ∃ p ∈ martonInnerBound binarySkewSymmetricBC, s = p.1 + p.2 }

/-- Sum-Rate Capacity of the Binary Skew-Symmetric Broadcast Channel
    (Hajek–Pursley 1979; Nair–Wang–Geng 2010):
    Does Marton's inner bound achieve the exact sum-rate capacity of `binarySkewSymmetricBC`? -/
def Statement : Prop :=
  bsscSumCapacity = bsscMartonSumRate

def problem : OpenProblem where
  id := "binary-skew-symmetric-bc"
  title := "Sum-Rate Capacity of the Binary Skew-Symmetric Broadcast Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Bruce Hajek and Michael Pursley"
  posedYear := 1979
  statement := Statement

end InfoTheory.Problems.BinarySkewSymmetricBc
