import InfoTheory.Known.Certificates.CorrelatedSourcesOverMac
import InfoTheory.Known.Certificates.CourtadeKumar
import InfoTheory.Known.Certificates.DegradedMessageSetsBcThreeReceivers
import InfoTheory.Known.Certificates.DeletionChannel
import InfoTheory.Known.Certificates.DeletionChannelHighDLimit
import InfoTheory.Known.Certificates.DeletionChannelSmallDAsymptotics
import InfoTheory.Known.Certificates.DiscreteEntropyPowerInequality
import InfoTheory.Known.Certificates.EditDistanceCodeCapacity
import InfoTheory.Known.Certificates.EntropicDoublingConstant
import InfoTheory.Known.Certificates.EntropyRegion
import InfoTheory.Known.Certificates.GilbertVarshamovBinary
import InfoTheory.Known.Certificates.KissingNumberHighDim
import InfoTheory.Known.Certificates.LinearRankEntropyRegionN6
import InfoTheory.Known.Certificates.ListDecodingCapacityBinaryLinear
import InfoTheory.Known.Certificates.ListDecodingZeroErrorCapacity
import InfoTheory.Known.Certificates.MdsConjecture
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
