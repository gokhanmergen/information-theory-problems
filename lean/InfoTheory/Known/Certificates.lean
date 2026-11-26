import InfoTheory.Known.Certificates.ListDecodingZeroErrorCapacity
import InfoTheory.Known.Certificates.ShannonCapacityC7
import InfoTheory.Known.Certificates.ShannonCapacityComplementProduct
import InfoTheory.Known.Certificates.ShannonCapacityUnionProduct
import InfoTheory.Known.Certificates.SpernerCapacityDirectedGraphs
import InfoTheory.Known.Certificates.ZeroErrorMacAdder

/-!
# Problem-statement certificates

Each `InfoTheory.Known.Certificates.<M>` proves the known facts claimed in the docstring of
`InfoTheory.Problems.<M>` about the exact objects in its `Statement` (non-vacuity evidence).
Coverage is reported by `scripts/AuditKnown.lean`.
-/
