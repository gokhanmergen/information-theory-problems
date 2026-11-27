import InfoTheory.Bridge.Mathlib
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.Gaussian
import InfoTheory.Bridge.Coding
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.ChannelAchievability
import InfoTheory.Bridge.RateDistortion
import InfoTheory.Bridge.MethodOfTypes
import InfoTheory.Bridge.ContinuousIT

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
-/
