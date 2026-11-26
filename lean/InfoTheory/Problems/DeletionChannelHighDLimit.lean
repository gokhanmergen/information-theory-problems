import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DeletionChannelHighDLimit

/-- The normalized high-deletion limit `L = inf_{d ∈ (0, 1)} C(d) / (1 - d)` of the binary
    deletion channel (proved equal to `lim_{d → 1⁻} C(d) / (1 - d)` by Dalai 2011). -/
noncomputable def highDeletionLimit : ℝ :=
  sInf { r : ℝ | ∃ d : ℝ, 0 < d ∧ d < 1 ∧ r = binaryDeletionCapacity d / (1 - d) }

/-- High-Deletion Limit Conjecture for the Binary Deletion Channel (Mitzenmacher–Drinea 2006;
    Dalai 2011; Rubinstein–Con 2023): currently `0.1221 < L < 0.3745`. We formalize the
    open benchmark conjecture that `lim_{d → 1⁻} C(d) / (1 - d) ≤ 1 / 4`. -/
def Statement : Prop :=
  highDeletionLimit ≤ 1 / 4

def problem : OpenProblem where
  id := "deletion-channel-high-d-limit"
  title := "High-Deletion Asymptotic Limit of the Binary Deletion Channel Capacity"
  category := .channelCapacity
  status := .open
  posedBy := "Michael Mitzenmacher and Eleni Drinea; Marco Dalai"
  posedYear := 2006
  statement := Statement

end InfoTheory.Problems.DeletionChannelHighDLimit
