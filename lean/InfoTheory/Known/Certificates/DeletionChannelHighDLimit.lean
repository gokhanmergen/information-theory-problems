import InfoTheory.Known.Certificates.DeletionChannel

/-!
# Certificate: `DeletionChannelHighDLimit`

Proofs live in the shared file `InfoTheory.Known.Certificates.DeletionChannel`; this module
restates the certified facts for `InfoTheory.Problems.DeletionChannelHighDLimit`:
the defining infimum is over a nonempty set bounded below, and `L ∈ [0, 1]`.
Not certified: the literature bounds `0.1221 < L < 0.3745`.

* **Regression**: `regression_formula_erasure` — the `sInf` formula defining
  `highDeletionLimit`, applied to the erasure-channel capacity `1 - d` (the solved
  comparison channel), returns the known value `1`; `regression_capacity_endpoints` —
  the capacity object inside the ratio has the known endpoint values `C(0) = 1`, `C(1) = 0`.
-/

namespace InfoTheory.Known.Certificates.DeletionChannelHighDLimit

open InfoTheory.Problems.DeletionChannelHighDLimit in
/-- `0 ≤ L ≤ 1` for the high-deletion limit `L = inf_{d ∈ (0,1)} C(d)/(1 − d)`. -/
theorem known_bounds : 0 ≤ highDeletionLimit ∧ highDeletionLimit ≤ 1 :=
  ⟨DeletionChannel.highDeletionLimit_nonneg, DeletionChannel.highDeletionLimit_le_one⟩

/-- **Regression**: the defining `sInf` formula returns `1` for the erasure channel. -/
theorem regression_formula_erasure :
    sInf { r : ℝ | ∃ d : ℝ, 0 < d ∧ d < 1 ∧ r = (1 - d) / (1 - d) } = 1 :=
  DeletionChannel.regression_highD_formula_erasure

/-- **Regression**: `C(0) = 1` and `C(1) = 0` for the capacity object in the ratio. -/
theorem regression_capacity_endpoints :
    InfoTheory.binaryDeletionCapacity 0 = 1 ∧ InfoTheory.binaryDeletionCapacity 1 = 0 :=
  ⟨DeletionChannel.capacity_zero, DeletionChannel.capacity_one⟩

end InfoTheory.Known.Certificates.DeletionChannelHighDLimit
