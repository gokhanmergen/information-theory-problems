import InfoTheory.Bridge.Mathlib
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.Gaussian

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
-/
