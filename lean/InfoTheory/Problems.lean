import InfoTheory.Problems.AwgnFeedbackErrorExponent
import InfoTheory.Problems.BatchCodesOptimalRedundancy
import InfoTheory.Problems.BinaryDuplicationChannel
import InfoTheory.Problems.BinaryMultiplierTwoWayChannel
import InfoTheory.Problems.BinarySkewSymmetricBc
import InfoTheory.Problems.BinarySymmetricZInterferenceChannel
import InfoTheory.Problems.BroadcastChannel
import InfoTheory.Problems.BroadcastChannelThreeReceivers
import InfoTheory.Problems.BscReliabilityFunction
import InfoTheory.Problems.CascadeRateDistortionSideInfo
import InfoTheory.Problems.CeoProblemGeneral
import InfoTheory.Problems.ClassicalCapacityAdditivityThreshold
import InfoTheory.Problems.CodedCachingExactTradeoff
import InfoTheory.Problems.CognitiveInterferenceChannel
import InfoTheory.Problems.CommonInformationExactVsWyner
import InfoTheory.Problems.ConditionalEntropyPowerConjecture
import InfoTheory.Problems.ConditionalEntropySharpContinuity
import InfoTheory.Problems.CourtadeKumar
import InfoTheory.Problems.CourtadeKumarQary
import InfoTheory.Problems.CovertCommunicationSecondOrder
import InfoTheory.Problems.DeletionChannel
import InfoTheory.Problems.DeletionChannelHighDLimit
import InfoTheory.Problems.DeletionChannelSmallDAsymptotics
import InfoTheory.Problems.DiscreteEntropyPowerInequality
import InfoTheory.Problems.DistributedHypothesisTestingExponent
import InfoTheory.Problems.DmInterferenceChannelCapacity
import InfoTheory.Problems.DmcZeroRateErrorExponent
import InfoTheory.Problems.DnaStorageUnorderedChannel
import InfoTheory.Problems.EditDistanceCodeCapacity
import InfoTheory.Problems.EntropicDoublingConstant
import InfoTheory.Problems.EntropyRegion
import InfoTheory.Problems.EntropyRegionDecidability
import InfoTheory.Problems.ExplicitListDecodableBinary
import InfoTheory.Problems.FiniteStateChannelCapacity
import InfoTheory.Problems.GaussianInterferenceChannel
import InfoTheory.Problems.GaussianMultipleDescriptions3
import InfoTheory.Problems.GaussianOptimalityMutualInformation
import InfoTheory.Problems.GaussianRelayChannelCapacity
import InfoTheory.Problems.GilbertVarshamovBinary
import InfoTheory.Problems.GraphEntropySubadditivity
import InfoTheory.Problems.GrayWynerLossy
import InfoTheory.Problems.HypercontractivityRibbonDiscrete
import InfoTheory.Problems.IndexCodingLinearNonlinearGap
import InfoTheory.Problems.IndexCodingSingleLetter
import InfoTheory.Problems.InsertionDeletionChannel
import InfoTheory.Problems.InteractiveInfoComplexityCompression
import InfoTheory.Problems.IntrinsicVsSecretKeyGap
import InfoTheory.Problems.KissingNumberHighDim
import InfoTheory.Problems.LdpMinimaxKlSharp
import InfoTheory.Problems.LiMedardConjecture
import InfoTheory.Problems.LinearNetworkCodingGap
import InfoTheory.Problems.LinearRankEntropyRegionN6
import InfoTheory.Problems.ListDecodingCapacityBinaryLinear
import InfoTheory.Problems.ListDecodingZeroErrorCapacity
import InfoTheory.Problems.LocallyCorrectableCodesConstantRate
import InfoTheory.Problems.LocallyDecodableCodes3Query
import InfoTheory.Problems.LogSobolevHypercubeSharp
import InfoTheory.Problems.MacWithFeedback
import InfoTheory.Problems.MartonInnerBoundTightness
import InfoTheory.Problems.MdsConjecture
import InfoTheory.Problems.MinimaxKlLargeAlphabet
import InfoTheory.Problems.MmseDimensionSingleCrossing
import InfoTheory.Problems.MrsGerberGeneral
import InfoTheory.Problems.MultipleDescriptionsGeneral
import InfoTheory.Problems.MultiterminalSourceCoding
import InfoTheory.Problems.NetworkCodingCapacityDecidability
import InfoTheory.Problems.NoisyInteractiveCommunicationRate
import InfoTheory.Problems.NonAsymptoticLossyDispersion
import InfoTheory.Problems.NptBoundEntanglement
import InfoTheory.Problems.PirCodedCollusionCapacity
import InfoTheory.Problems.PoissonChannelDiscreteCapacity
import InfoTheory.Problems.PolarCodeScalingExponent
import InfoTheory.Problems.PrimitiveRelayChannelBsc
import InfoTheory.Problems.PrivateVsQuantumCapacityGap
import InfoTheory.Problems.QuantumBroadcastCapacity
import InfoTheory.Problems.QuantumCapacityDepolarizing
import InfoTheory.Problems.QuantumCapacitySingleLetter
import InfoTheory.Problems.QuantumCapacityTwoPauli
import InfoTheory.Problems.QuantumEntropyPowerSharp
import InfoTheory.Problems.QuantumLdpcRateDistance
import InfoTheory.Problems.QuantumReverseShannonNonCatalytic
import InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness
import InfoTheory.Problems.ReedMullerCapacityGeneralDmc
import InfoTheory.Problems.RegeneratingCodesExactRepair
import InfoTheory.Problems.RelayChannel
import InfoTheory.Problems.RenyiEntropyPowerSharp
import InfoTheory.Problems.SbmMultiCommunityThreshold
import InfoTheory.Problems.SdpiKlVsChisqEquality
import InfoTheory.Problems.SecretKeyCapacityPublicDiscussion
import InfoTheory.Problems.SecretSharingOptimalInfoRatio
import InfoTheory.Problems.ShannonCapacityC7
import InfoTheory.Problems.ShannonCapacityComplementProduct
import InfoTheory.Problems.ShannonCapacityComputability
import InfoTheory.Problems.ShannonCapacityUnionProduct
import InfoTheory.Problems.SicPovmZauner
import InfoTheory.Problems.SpernerCapacityDirectedGraphs
import InfoTheory.Problems.SuperactivationQubitChannels
import InfoTheory.Problems.TimingChannelGeneralQueue
import InfoTheory.Problems.TraceReconstructionAverageCase
import InfoTheory.Problems.TraceReconstructionWorstCase
import InfoTheory.Problems.TwoWayChannelCapacity
import InfoTheory.Problems.UndirectedNetworkCodingLiLi
import InfoTheory.Problems.UniversalLossyRedundancy
import InfoTheory.Problems.WiretapChannelCompoundSecrecy
import InfoTheory.Problems.WiretapWithFeedbackCapacity
import InfoTheory.Problems.ZeroErrorBroadcastChannel
import InfoTheory.Problems.ZeroErrorFeedbackVariableLength
import InfoTheory.Problems.ZeroErrorMacAdder
import InfoTheory.Problems.ZeroErrorSourceCodingSideInfo

/-!
# Master Registry of All 109 Information Theory Problems
-/

namespace InfoTheory

/-- Complete typed list of all cataloged problems and their frozen Lean 4 statements. -/
def allProblems : List OpenProblem := [
  InfoTheory.Problems.AwgnFeedbackErrorExponent.problem,
  InfoTheory.Problems.BatchCodesOptimalRedundancy.problem,
  InfoTheory.Problems.BinaryDuplicationChannel.problem,
  InfoTheory.Problems.BinaryMultiplierTwoWayChannel.problem,
  InfoTheory.Problems.BinarySkewSymmetricBc.problem,
  InfoTheory.Problems.BinarySymmetricZInterferenceChannel.problem,
  InfoTheory.Problems.BroadcastChannel.problem,
  InfoTheory.Problems.BroadcastChannelThreeReceivers.problem,
  InfoTheory.Problems.BscReliabilityFunction.problem,
  InfoTheory.Problems.CascadeRateDistortionSideInfo.problem,
  InfoTheory.Problems.CeoProblemGeneral.problem,
  InfoTheory.Problems.ClassicalCapacityAdditivityThreshold.problem,
  InfoTheory.Problems.CodedCachingExactTradeoff.problem,
  InfoTheory.Problems.CognitiveInterferenceChannel.problem,
  InfoTheory.Problems.CommonInformationExactVsWyner.problem,
  InfoTheory.Problems.ConditionalEntropyPowerConjecture.problem,
  InfoTheory.Problems.ConditionalEntropySharpContinuity.problem,
  InfoTheory.Problems.CourtadeKumar.problem,
  InfoTheory.Problems.CourtadeKumarQary.problem,
  InfoTheory.Problems.CovertCommunicationSecondOrder.problem,
  InfoTheory.Problems.DeletionChannel.problem,
  InfoTheory.Problems.DeletionChannelHighDLimit.problem,
  InfoTheory.Problems.DeletionChannelSmallDAsymptotics.problem,
  InfoTheory.Problems.DiscreteEntropyPowerInequality.problem,
  InfoTheory.Problems.DistributedHypothesisTestingExponent.problem,
  InfoTheory.Problems.DmInterferenceChannelCapacity.problem,
  InfoTheory.Problems.DmcZeroRateErrorExponent.problem,
  InfoTheory.Problems.DnaStorageUnorderedChannel.problem,
  InfoTheory.Problems.EditDistanceCodeCapacity.problem,
  InfoTheory.Problems.EntropicDoublingConstant.problem,
  InfoTheory.Problems.EntropyRegion.problem,
  InfoTheory.Problems.EntropyRegionDecidability.problem,
  InfoTheory.Problems.ExplicitListDecodableBinary.problem,
  InfoTheory.Problems.FiniteStateChannelCapacity.problem,
  InfoTheory.Problems.GaussianInterferenceChannel.problem,
  InfoTheory.Problems.GaussianMultipleDescriptions3.problem,
  InfoTheory.Problems.GaussianOptimalityMutualInformation.problem,
  InfoTheory.Problems.GaussianRelayChannelCapacity.problem,
  InfoTheory.Problems.GilbertVarshamovBinary.problem,
  InfoTheory.Problems.GraphEntropySubadditivity.problem,
  InfoTheory.Problems.GrayWynerLossy.problem,
  InfoTheory.Problems.HypercontractivityRibbonDiscrete.problem,
  InfoTheory.Problems.IndexCodingLinearNonlinearGap.problem,
  InfoTheory.Problems.IndexCodingSingleLetter.problem,
  InfoTheory.Problems.InsertionDeletionChannel.problem,
  InfoTheory.Problems.InteractiveInfoComplexityCompression.problem,
  InfoTheory.Problems.IntrinsicVsSecretKeyGap.problem,
  InfoTheory.Problems.KissingNumberHighDim.problem,
  InfoTheory.Problems.LdpMinimaxKlSharp.problem,
  InfoTheory.Problems.LiMedardConjecture.problem,
  InfoTheory.Problems.LinearNetworkCodingGap.problem,
  InfoTheory.Problems.LinearRankEntropyRegionN6.problem,
  InfoTheory.Problems.ListDecodingCapacityBinaryLinear.problem,
  InfoTheory.Problems.ListDecodingZeroErrorCapacity.problem,
  InfoTheory.Problems.LocallyCorrectableCodesConstantRate.problem,
  InfoTheory.Problems.LocallyDecodableCodes3Query.problem,
  InfoTheory.Problems.LogSobolevHypercubeSharp.problem,
  InfoTheory.Problems.MacWithFeedback.problem,
  InfoTheory.Problems.MartonInnerBoundTightness.problem,
  InfoTheory.Problems.MdsConjecture.problem,
  InfoTheory.Problems.MinimaxKlLargeAlphabet.problem,
  InfoTheory.Problems.MmseDimensionSingleCrossing.problem,
  InfoTheory.Problems.MrsGerberGeneral.problem,
  InfoTheory.Problems.MultipleDescriptionsGeneral.problem,
  InfoTheory.Problems.MultiterminalSourceCoding.problem,
  InfoTheory.Problems.NetworkCodingCapacityDecidability.problem,
  InfoTheory.Problems.NoisyInteractiveCommunicationRate.problem,
  InfoTheory.Problems.NonAsymptoticLossyDispersion.problem,
  InfoTheory.Problems.NptBoundEntanglement.problem,
  InfoTheory.Problems.PirCodedCollusionCapacity.problem,
  InfoTheory.Problems.PoissonChannelDiscreteCapacity.problem,
  InfoTheory.Problems.PolarCodeScalingExponent.problem,
  InfoTheory.Problems.PrimitiveRelayChannelBsc.problem,
  InfoTheory.Problems.PrivateVsQuantumCapacityGap.problem,
  InfoTheory.Problems.QuantumBroadcastCapacity.problem,
  InfoTheory.Problems.QuantumCapacityDepolarizing.problem,
  InfoTheory.Problems.QuantumCapacitySingleLetter.problem,
  InfoTheory.Problems.QuantumCapacityTwoPauli.problem,
  InfoTheory.Problems.QuantumEntropyPowerSharp.problem,
  InfoTheory.Problems.QuantumLdpcRateDistance.problem,
  InfoTheory.Problems.QuantumReverseShannonNonCatalytic.problem,
  InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness.problem,
  InfoTheory.Problems.ReedMullerCapacityGeneralDmc.problem,
  InfoTheory.Problems.RegeneratingCodesExactRepair.problem,
  InfoTheory.Problems.RelayChannel.problem,
  InfoTheory.Problems.RenyiEntropyPowerSharp.problem,
  InfoTheory.Problems.SbmMultiCommunityThreshold.problem,
  InfoTheory.Problems.SdpiKlVsChisqEquality.problem,
  InfoTheory.Problems.SecretKeyCapacityPublicDiscussion.problem,
  InfoTheory.Problems.SecretSharingOptimalInfoRatio.problem,
  InfoTheory.Problems.ShannonCapacityC7.problem,
  InfoTheory.Problems.ShannonCapacityComplementProduct.problem,
  InfoTheory.Problems.ShannonCapacityComputability.problem,
  InfoTheory.Problems.ShannonCapacityUnionProduct.problem,
  InfoTheory.Problems.SicPovmZauner.problem,
  InfoTheory.Problems.SpernerCapacityDirectedGraphs.problem,
  InfoTheory.Problems.SuperactivationQubitChannels.problem,
  InfoTheory.Problems.TimingChannelGeneralQueue.problem,
  InfoTheory.Problems.TraceReconstructionAverageCase.problem,
  InfoTheory.Problems.TraceReconstructionWorstCase.problem,
  InfoTheory.Problems.TwoWayChannelCapacity.problem,
  InfoTheory.Problems.UndirectedNetworkCodingLiLi.problem,
  InfoTheory.Problems.UniversalLossyRedundancy.problem,
  InfoTheory.Problems.WiretapChannelCompoundSecrecy.problem,
  InfoTheory.Problems.WiretapWithFeedbackCapacity.problem,
  InfoTheory.Problems.ZeroErrorBroadcastChannel.problem,
  InfoTheory.Problems.ZeroErrorFeedbackVariableLength.problem,
  InfoTheory.Problems.ZeroErrorMacAdder.problem,
  InfoTheory.Problems.ZeroErrorSourceCodingSideInfo.problem,
]

end InfoTheory
