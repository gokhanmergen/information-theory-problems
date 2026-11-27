import InfoTheory.Known.Certificates.DeletionChannel

/-!
# Certificate: `DeletionChannelHighDLimit`

Proofs live in the shared file `InfoTheory.Known.Certificates.DeletionChannel`; this module
restates the certified facts for `InfoTheory.Problems.DeletionChannelHighDLimit`:
the defining infimum is over a nonempty set bounded below, and `L ∈ [0, 1]`.
Not certified: the literature bounds `0.1221 < L < 0.3745`.
-/

namespace InfoTheory.Known.Certificates.DeletionChannelHighDLimit

open InfoTheory.Problems.DeletionChannelHighDLimit in
/-- `0 ≤ L ≤ 1` for the high-deletion limit `L = inf_{d ∈ (0,1)} C(d)/(1 − d)`. -/
theorem known_bounds : 0 ≤ highDeletionLimit ∧ highDeletionLimit ≤ 1 :=
  ⟨DeletionChannel.highDeletionLimit_nonneg, DeletionChannel.highDeletionLimit_le_one⟩

end InfoTheory.Known.Certificates.DeletionChannelHighDLimit
