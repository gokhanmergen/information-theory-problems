import InfoTheory.Known.Entropy
import InfoTheory.Known.EntropyRegion
import InfoTheory.Known.Channels
import InfoTheory.Known.Coding
import InfoTheory.Known.ZeroError
import InfoTheory.Known.Operational
import InfoTheory.Known.GaussianChannel
import InfoTheory.Known.MarkovSource
import InfoTheory.Known.CostConstrainedCoding
import InfoTheory.Known.GaussianAchievability
import InfoTheory.Known.GaussianNetwork

/-!
# Known Results

Fully proved (standard axioms only) textbook theorems about the Core definitions.

They serve two purposes:
- They certify that Core definitions mean what they should: a definition that cannot reproduce
  a textbook value is wrong, and so is every open statement built on it.
- They give provers of the open `InfoTheory.Problems.*` statements a lemma base.

Headline results: Gibbs' inequality and `I(X;Y|Z) ≥ 0`; the Shannon inequalities
(`Γ*_n ⊆ cl Γ*_n ⊆ Γ_n`) and Ingleton for linear rank vectors; `C(BSC) = 1 − h(p)`,
`C(BEC) = 1 − ε`, `C_del(0) = 1`, `C_del(d) ≤ 1 − d`; the Singleton, Hamming and
Gilbert–Varshamov bounds (finite and asymptotic), and that Reed–Solomon codes are MDS;
Lovász's `Θ(G) ≤ ϑ(G)` and `Θ(C₅) = √5`.
-/
