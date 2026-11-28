import InfoTheory.Bridge.Mathlib
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.Gaussian
import InfoTheory.Bridge.Coding
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability
import InfoTheory.Bridge.RateDistortion
import InfoTheory.Bridge.MethodOfTypes
import InfoTheory.Bridge.ContinuousIT
import InfoTheory.Bridge.NetworkIT
import InfoTheory.Bridge.MrsGerber
import InfoTheory.Bridge.FeketeAndCopyLemma
import InfoTheory.Bridge.ErrorExponents
import InfoTheory.Bridge.FeedbackConverse
import InfoTheory.Bridge.RelayCoding
import InfoTheory.Bridge.BroadcastCoding
import InfoTheory.Bridge.WynerZiv
import InfoTheory.Bridge.ContinuityAndShearer
import InfoTheory.Bridge.WiretapCoding
import InfoTheory.Bridge.GaussianConverse
import InfoTheory.Bridge.MartonCoding
import InfoTheory.Bridge.GelfandPinsker
import InfoTheory.Bridge.EntropyPower
import InfoTheory.Bridge.Quantum
import InfoTheory.Bridge.RelayAchievability
import InfoTheory.Bridge.UniversalCoding

/-!
# `InfoTheory.Bridge` — Non-Destructive Bridge to Mathlib & Cover & Thomas Foundations

Single convenience import re-exporting:
- `InfoTheory.Bridge.Mathlib`: `ProbDist ↔ PMF/Measure`, `DMC ↔ Kernel`,
  `klDivergence ↔ InformationTheory.klDiv` (Gibbs, DPI), `Hamming`, `KraftMcMillan`,
  and Cover & Thomas Ch. 2 entropy/MI bounds.
- `InfoTheory.Bridge.CoverThomas`: chain rules, symmetry, strong subadditivity
  (`condMutualInfo_nonneg`), `Γ*_n ⊆ Γ_n` (`subsetEntropyVec_isPolymatroid`),
  sharp Fano's inequality, and the AEP / weak typicality bounds.
- `InfoTheory.Bridge.Gaussian`: `gaussianPdf1D ↔ gaussianPDFReal`, `gaussianDensity1D`,
  Gaussian differential entropy `½ ln(2π e v)`, entropy power `= v`, and Gaussian
  maximum differential entropy (`diffEntropy_le_gaussian`).
- `InfoTheory.Bridge.Coding`: Pinsker's inequality (`2 TV(P,Q)² ≤ ln 2 · D(P‖Q)`),
  Kraft existence theorem, source coding converse, and Shannon–Fano achievability.
- `InfoTheory.Bridge.ChannelCoding`: jointly weakly typical sequences & Joint AEP,
  Packing Lemma independent-pair bound, DMC multi-letter converse tensorization,
  and the Fano weak converse for block codes (`dmcAvgError_rate_converse`).
- `InfoTheory.Bridge.ChannelAchievability`: random-coding achievability via joint-typicality
  decoding and the full **Shannon Channel Coding Theorem** (`dmcOperationalCapacity W = W.capacity`).
- `InfoTheory.Bridge.RateDistortion`: convexity of `rateDistortion`, Rate–Distortion converse,
  Covering Lemma (El Gamal–Kim Lemma 3.3), and Shannon Rate–Distortion achievability.
- `InfoTheory.Bridge.MethodOfTypes`: log-sum inequality, convexity of KL / concavity of entropy,
  Csiszár's sum identity, Method of Types (Thms. 11.1.1–11.1.4), and Sanov's Theorem.
- `InfoTheory.Bridge.ContinuousIT`: translation/scaling of differential entropy, multivariate
  product Gaussians, AWGN capacity bound & Gaussian achievability, and multi-letter Jensen bound.
- `InfoTheory.Bridge.NetworkIT`: **Slepian–Wolf Theorem** (`slepian_wolf_theorem`) and
  **Two-User DMC MAC Capacity Region Theorem** (`mac_capacity_theorem`).
- `InfoTheory.Bridge.MrsGerber`: scalar & vector **Mrs. Gerber's Lemma** (`mrs_gerber_scalar`,
  `mrs_gerber_vector`) and Bergmans's Binary Symmetric Degraded Broadcast Channel bounds.
- `InfoTheory.Bridge.FeketeAndCopyLemma`: Fekete subadditivity/superadditivity lemmas,
  stationary entropy rate, the Copy Lemma, and the **Zhang–Yeung (1998) Non-Shannon
  Information Inequality** (`cl(Γ*_4) ⊂ Γ_4`).
- `InfoTheory.Bridge.ErrorExponents`: **Chernoff–Stein Lemma** (both halves, strong converse,
  and exact Cover & Thomas Thm. 11.8.3 limit) and **Gallager's (1965) Random-Coding Error Exponent**
  (`randomCodingExponent_le_reliabilityFunction`).
- `InfoTheory.Bridge.FeedbackConverse`: **Feedback Does Not Increase DMC Capacity**
  (Cover & Thomas Thm. 7.12.1: `dmc_feedback_capacity_theorem`) and the silent-user MAC-with-feedback
  converse (`isMACFeedbackAchievable_le_capacity_of_ignores_second`).
- `InfoTheory.Bridge.RelayCoding`: **Operational Relay Channel Cut-Set Bound**
  (Cover & Thomas Thm. 15.10.1 / El Gamal–Kim Thm. 16.1: `relayCapacity_le_cutsetBound`).
- `InfoTheory.Bridge.BroadcastCoding`: **Superposition Coding Inner Bound**, **Degraded Broadcast
  Channel Capacity Region Theorem** (`degradedBC_capacity_theorem`), and the full **Operational
  Bergmans Binary Symmetric Degraded BC Capacity Region** (`degradedBSC_operational_capacity_region`).
- `InfoTheory.Bridge.WynerZiv`: **Strong Typicality & the Markov Lemma** (El Gamal–Kim Lemma 12.1:
  `markov_lemma`) and the **Wyner–Ziv Lossy Source Coding Theorem** (`wyner_ziv_theorem`).
- `InfoTheory.Bridge.ContinuityAndShearer`: **Sharp Fannes–Audenaert / Zhang Entropy Continuity**
  (`shannonEntropy_continuity_audenaert`), **Alicki–Fannes–Winter Conditional Entropy & MI Continuity**
  (`condEntropy_continuity`, `mutualInfo_continuity_min`), **Shearer's Lemma** (`shearer_inequality_weighted`),
  **Han's Inequality** (`han_average_antitone_step`), and arbitrary-alphabet Zhang–Yeung.
- `InfoTheory.Bridge.WiretapCoding`: **Wyner (1975) / Csiszár–Körner (1978) Wiretap Channel Secrecy
  Capacity Theorem** (`wiretap_secrecy_capacity_theorem`, degraded simplification, weak-secrecy
  converse via Csiszár's sum identity, and random-binning achievability).
- `InfoTheory.Bridge.GaussianConverse`: **Strictly Causal Multi-User Gaussian Feedback & Relay
  Cut-Set Converse Toolkit** (`causal_awgn_feedback_rate_le`, `causal_simo_awgn_feedback_rate_le`,
  `gaussian_mac_feedback_sum_rate_converse`, `gaussian_bc_feedback_sum_rate_converse`,
  `gaussian_relay_cutset_converse_coupled`, and the exact EMZ 2006 lower bound
  `gaussian_relay_unit_energy_per_bit_ge`: `(3/4) · 2 ln 2 ≤ (P₁ + P₂) / R`).
- `InfoTheory.Bridge.MartonCoding`: **Mutual Covering Lemma** (El Gamal–Kim Lemma 8.1:
  `mutual_covering_lemma`) and **Marton's Inner Bound with Common Auxiliary `W`**
  (Marton 1979 / El Gamal–Kim Thm. 8.3: `martonInnerBound_subset_bcCapacityRegion`).
- `InfoTheory.Bridge.GelfandPinsker`: **Gelfand–Pinsker Theorem** for discrete memoryless
  channels with noncausal transmitter side information (El Gamal–Kim Thm. 7.3:
  `gelfand_pinsker_theorem`, deterministic-vs-stochastic equivalence, Csiszár-sum converse,
  and random-binning achievability).
- `InfoTheory.Bridge.EntropyPower`: **Cramér–Rao Inequality**, **Stam's Fisher Information
  Inequality** (`stam_inequality`), **De Bruijn's Identity** (`de_bruijn_identity`),
  **Shannon's 1D Entropy Power Inequality** (`entropyPower_add_ge`, Cover & Thomas Thm. 17.8.1),
  and **Bergmans's Scalar Gaussian Broadcast Channel Single-Letter Converse**
  (`gaussianBC_single_letter_converse`).
- `InfoTheory.Bridge.Quantum`: **Quantum Information Theory Foundations** directly against
  `Core/Quantum.lean` — von Neumann entropy bounds, concavity (`vonNeumannEntropy_concave`),
  tensor additivity (`vonNeumannEntropy_kronDensity`), purification symmetry, Peres–Horodecki
  PPT criterion (`isPPT_of_isSeparable`), Bell state entanglement & distillability, trace distance,
  identity/replacement/depolarizing/two-Pauli channels, and the `d = 2` tetrahedron SIC-POVM.
- `InfoTheory.Bridge.RelayAchievability`: **Cover–El Gamal (1979) Decode-and-Forward Achievability**
  (`relayDFRate_le_relayCapacity`) and the **Physically Degraded Relay Channel Capacity Theorem**
  (Cover & Thomas Thm. 15.10.2: `degradedRelay_capacity_theorem : relayCapacity W = relayCutsetBound W`).
- `InfoTheory.Bridge.UniversalCoding`: **Shtarkov NML Minimax Regret** (`shtarkov_minimax_regret`),
  **Krichevsky–Trofimov (1981) Universal Source Coding** (`kt_pointwise_regret_le`,
  `kt_kl_redundancy_le`, `universal_prefix_code_redundancy_le`), **Gallager–Haussler Capacity–Redundancy
  Compensation Identity**, and exact minimax redundancy asymptotics
  (`minimax_kl_redundancy_asymptotics : minimaxRedundancy α n / log₂ n → (|α| - 1) / 2`).
-/
