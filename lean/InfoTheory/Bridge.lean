import InfoTheory.Bridge.Mathlib
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.Gaussian
import InfoTheory.Bridge.Coding
import InfoTheory.Bridge.ChannelCoding

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
-/
