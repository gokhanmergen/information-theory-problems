import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Core Entropy, Divergence, and Information Measures

Foundational definitions for discrete and continuous information measures:
- Finite probability distributions `ProbDist α`
- Base-2 logarithm `log2`, binary entropy `binaryEntropy`, binary convolution `binaryConv`
- Shannon entropy, joint entropy, conditional entropy, mutual information, conditional mutual information
- Kullback-Leibler divergence, Rényi entropy/divergence, total variation, χ²-divergence
- Entropic vectors `Γ*_n`, almost-entropic cone `cl(Γ*_n)`, polymatroid cone `Γ_n`, linear rank region
- Discrete distributions on `ℤ` and continuous densities on `ℝ^d` (differential entropy, entropy power, Fisher information)
-/

open scoped BigOperators
open MeasureTheory

namespace InfoTheory

/-- Base-2 logarithm on `ℝ`. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The elementary entropy summand `-p log₂ p`, defined as `0` for `p ≤ 0`. -/
noncomputable def negPLogP (p : ℝ) : ℝ :=
  if p ≤ 0 then 0 else -p * log2 p

/-- The binary entropy function `h(p) = -p log₂ p - (1 - p) log₂ (1 - p)`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  negPLogP p + negPLogP (1 - p)

/-- Binary convolution `p ★ q = p(1 - q) + (1 - p)q`. -/
def binaryConv (p q : ℝ) : ℝ :=
  p * (1 - q) + (1 - p) * q

/-- Inverse binary entropy `h⁻¹(y) ∈ [0, 1/2]` for `y ∈ [0, 1]`. -/
noncomputable def invBinaryEntropy (y : ℝ) : ℝ :=
  sSup { p : ℝ | 0 ≤ p ∧ p ≤ 1 / 2 ∧ binaryEntropy p ≤ y }

/-- A finite probability distribution over a finite type `α`. -/
structure ProbDist (α : Type*) [Fintype α] where
  pmf : α → ℝ
  nonneg : ∀ a, 0 ≤ pmf a
  sum_one : ∑ a : α, pmf a = 1

namespace ProbDist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Uniform distribution on a nonempty finite type. -/
noncomputable def uniform [Nonempty α] : ProbDist α where
  pmf := fun _ => (1 : ℝ) / (Fintype.card α : ℝ)
  nonneg := fun _ => by positivity
  sum_one := by
    have hcard : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hcard]

/-- Bernoulli distribution `Bern(p)` on `Bool` for `0 ≤ p ≤ 1`. -/
def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ProbDist Bool where
  pmf := fun b => if b then p else 1 - p
  nonneg := fun b => by cases b <;> simp <;> linarith
  sum_one := by simp

/-- First marginal of a joint distribution on `α × β`. -/
def fst (P : ProbDist (α × β)) : ProbDist α where
  pmf := fun a => ∑ b : β, P.pmf (a, b)
  nonneg := fun a => Finset.sum_nonneg (fun b _ => P.nonneg (a, b))
  sum_one := by
    rw [← Fintype.sum_prod_type']
    exact P.sum_one

/-- Second marginal of a joint distribution on `α × β`. -/
def snd (P : ProbDist (α × β)) : ProbDist β where
  pmf := fun b => ∑ a : α, P.pmf (a, b)
  nonneg := fun b => Finset.sum_nonneg (fun a _ => P.nonneg (a, b))
  sum_one := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    exact P.sum_one

/-- Independent product of two distributions. -/
def prod (P : ProbDist α) (Q : ProbDist β) : ProbDist (α × β) where
  pmf := fun ab => P.pmf ab.1 * Q.pmf ab.2
  nonneg := fun ab => mul_nonneg (P.nonneg ab.1) (Q.nonneg ab.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.sum_one, mul_one, P.sum_one]

/-- Pushforward distribution along a deterministic map `f : α → β`. -/
noncomputable def map (f : α → β) (P : ProbDist α) : ProbDist β := by
  classical
  exact
    { pmf := fun b => ∑ a : α, if f a = b then P.pmf a else 0
      nonneg := fun b => Finset.sum_nonneg (fun a _ => by split_ifs; exact P.nonneg a; exact le_rfl)
      sum_one := by
        rw [Finset.sum_comm]
        simp [P.sum_one] }

/-- Pair `(f(X), g(X))` distribution induced by `X ~ P`. -/
noncomputable def mapPair (f : α → β) (g : α → γ) (P : ProbDist α) : ProbDist (β × γ) :=
  P.map (fun a => (f a, g a))

end ProbDist

/-- Shannon entropy `H(X)` in bits. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (P : ProbDist α) : ℝ :=
  ∑ a : α, negPLogP (P.pmf a)

/-- Joint entropy `H(X, Y)` in bits. -/
noncomputable def jointEntropy {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist (α × β)) : ℝ :=
  shannonEntropy P

/-- Conditional entropy `H(X | Y) = H(X, Y) - H(Y)` in bits. -/
noncomputable def condEntropy {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist (α × β)) : ℝ :=
  shannonEntropy P - shannonEntropy P.snd

/-- Mutual information `I(X; Y) = H(X) + H(Y) - H(X, Y)` in bits. -/
noncomputable def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist (α × β)) : ℝ :=
  shannonEntropy P.fst + shannonEntropy P.snd - shannonEntropy P

/-- Conditional mutual information `I(X; Y | Z)` for `P : ProbDist (α × β × γ)`. -/
noncomputable def condMutualInfo {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProbDist (α × β × γ)) : ℝ :=
  let Pxz : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  let Pyz : ProbDist (β × γ) := P.map (fun t => (t.2.1, t.2.2))
  let Pz : ProbDist γ := P.map (fun t => t.2.2)
  shannonEntropy Pxz + shannonEntropy Pyz - shannonEntropy P - shannonEntropy Pz

/-- Kullback-Leibler divergence `D(P ‖ Q)` in bits (returns `0` on zero-mass support,
    assuming `P ≪ Q` when finite). -/
noncomputable def klDivergence {α : Type*} [Fintype α] (P Q : ProbDist α) : ℝ :=
  ∑ a : α, if P.pmf a ≤ 0 then 0 else P.pmf a * log2 (P.pmf a / Q.pmf a)

/-- Absolute continuity predicate `P ≪ Q` for finite distributions. -/
def AbsCont {α : Type*} [Fintype α] (P Q : ProbDist α) : Prop :=
  ∀ a : α, Q.pmf a = 0 → P.pmf a = 0

open Classical in
/-- Extended-real Kullback-Leibler divergence `D(P ‖ Q) ∈ EReal`: equals `⊤` when `¬ (P ≪ Q)`,
    preventing finite junk values on mismatched supports. -/
noncomputable def klDivergenceEReal {α : Type*} [Fintype α] (P Q : ProbDist α) : EReal :=
  if AbsCont P Q then (klDivergence P Q : EReal) else ⊤

/-- Total variation distance `TV(P, Q) = ½ ∑ |P(a) - Q(a)|`. -/
noncomputable def tvDistance {α : Type*} [Fintype α] (P Q : ProbDist α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : α, |P.pmf a - Q.pmf a|

/-- Pearson χ²-divergence `χ²(P ‖ Q) = ∑ (P(a) - Q(a))² / Q(a)`. -/
noncomputable def chiSqDivergence {α : Type*} [Fintype α] (P Q : ProbDist α) : ℝ :=
  ∑ a : α, if Q.pmf a ≤ 0 then 0 else (P.pmf a - Q.pmf a) ^ 2 / Q.pmf a

/-- Rényi entropy of order `α` (in bits, for `α > 0, α ≠ 1`). -/
noncomputable def renyiEntropy {Ω : Type*} [Fintype Ω] (order : ℝ) (P : ProbDist Ω) : ℝ :=
  if order = 1 then shannonEntropy P
  else (1 / (1 - order)) * log2 (∑ a : Ω, (P.pmf a) ^ order)

/-- Conditional Markov chain `X — Y — Z` for a triple `(X, Y, Z)`. -/
def IsMarkovChain {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProbDist (α × β × γ)) : Prop :=
  condMutualInfo (P.map (fun t => (t.1, t.2.2, t.2.1))) = 0

/-! ### Entropy Vectors, `Γ_n`, `Γ*_n`, and `cl(Γ*_n)` -/

/-- Subset entropy vector of a joint distribution on `Fin n → Fin k`. -/
noncomputable def subsetEntropyVec {n k : ℕ} (P : ProbDist (Fin n → Fin k)) :
    Finset (Fin n) → ℝ :=
  fun S => shannonEntropy (P.map (fun x (i : S) => x i.1))

/-- The set `Γ*_n` of all entropic vectors on `n` discrete random variables. -/
def IsEntropicVector (n : ℕ) (h : Finset (Fin n) → ℝ) : Prop :=
  ∃ (k : ℕ) (P : ProbDist (Fin n → Fin k)), ∀ S : Finset (Fin n), h S = subsetEntropyVec P S

/-- The closure `cl(Γ*_n)` (almost-entropic cone) in `ℝ^(2^n)`. -/
def InAlmostEntropicCone (n : ℕ) (h : Finset (Fin n) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h' : Finset (Fin n) → ℝ,
    IsEntropicVector n h' ∧ ∀ S : Finset (Fin n), |h S - h' S| < ε

/-- The Shannon polymatroid cone `Γ_n`: nonnegative, monotone, submodular set functions with `h(∅) = 0`. -/
def IsPolymatroid (n : ℕ) (h : Finset (Fin n) → ℝ) : Prop :=
  h ∅ = 0 ∧
  (∀ S T : Finset (Fin n), S ⊆ T → h S ≤ h T) ∧
  (∀ S T : Finset (Fin n), h (S ∪ T) + h (S ∩ T) ≤ h S + h T)

/-- Subspace-rank (linearly representable) entropy vector over some finite field `GF(p^r)`
    (prime `p`, `r ≥ 1`), matching the standard network coding / linear rank region `L_n`. -/
def IsLinearRankVector (n : ℕ) (h : Finset (Fin n) → ℝ) : Prop :=
  ∃ (p r d : ℕ) (hp : Fact p.Prime) (_ : 0 < r) (c : ℝ)
    (V : Fin n → Submodule (GaloisField p r) (Fin d → GaloisField p r)),
    0 < c ∧ ∀ S : Finset (Fin n),
      h S = c * (Module.finrank (GaloisField p r)
        (⨆ i ∈ S, V i : Submodule (GaloisField p r) (Fin d → GaloisField p r)) : ℝ)

/-! ### Discrete Integer Distributions and Continuous Densities -/

/-- A probability distribution on `ℤ`. -/
structure IntProbDist where
  pmf : ℤ → ℝ
  nonneg : ∀ k, 0 ≤ pmf k
  summable : Summable pmf
  tsum_one : ∑' k : ℤ, pmf k = 1

/-- Summability predicate ensuring `intEntropy P` does not fall back to the `tsum` junk value `0`. -/
def HasFiniteIntEntropy (P : IntProbDist) : Prop :=
  Summable (fun k : ℤ => if P.pmf k ≤ 0 then 0 else -P.pmf k * Real.log (P.pmf k))

/-- Discrete Shannon entropy on `ℤ` (in nats). -/
noncomputable def intEntropy (P : IntProbDist) : ℝ :=
  ∑' k : ℤ, if P.pmf k ≤ 0 then 0 else -P.pmf k * Real.log (P.pmf k)

/-- Independent sum convolution `P * Q` on `ℤ`. -/
noncomputable def intConv (P Q : IntProbDist) : ℤ → ℝ :=
  fun n => ∑' k : ℤ, P.pmf k * Q.pmf (n - k)

/-- A probability density function on `ℝ^d`. -/
structure Density (d : ℕ) where
  pdf : (Fin d → ℝ) → ℝ
  nonneg : ∀ x, 0 ≤ pdf x
  integrable : Integrable pdf volume
  integral_one : ∫ x, pdf x = 1

/-- Integrability predicate ensuring `diffEntropy f` is genuinely finite (not Bochner junk `0`). -/
def HasFiniteDiffEntropy {d : ℕ} (f : Density d) : Prop :=
  Integrable (fun x => if f.pdf x ≤ 0 then 0 else -f.pdf x * Real.log (f.pdf x)) volume

/-- Integrability predicate ensuring `renyiDiffEntropy α f` is genuinely finite. -/
def HasFiniteRenyiEntropy {d : ℕ} (α : ℝ) (f : Density d) : Prop :=
  Integrable (fun x => (f.pdf x) ^ α) volume

/-- Finite second-moment predicate `∫ ‖x‖² f(x) dx < ∞` on `ℝ^d`. -/
def HasFiniteSecondMoment {d : ℕ} (f : Density d) : Prop :=
  Integrable (fun x => (∑ i : Fin d, (x i) ^ 2) * f.pdf x) volume

/-- Differential entropy `h(f) = -∫ f(x) ln f(x) dx` in nats. -/
noncomputable def diffEntropy {d : ℕ} (f : Density d) : ℝ :=
  ∫ x, (if f.pdf x ≤ 0 then 0 else -f.pdf x * Real.log (f.pdf x))

/-- Entropy power `N(f) = (1 / (2πe)) exp(2 h(f) / d)`. -/
noncomputable def entropyPower {d : ℕ} (f : Density d) : ℝ :=
  (1 / (2 * Real.pi * Real.exp 1)) * Real.exp (2 * diffEntropy f / (d : ℝ))

/-- Rényi differential entropy of order `α` (for `α > 0, α ≠ 1`). -/
noncomputable def renyiDiffEntropy {d : ℕ} (α : ℝ) (f : Density d) : ℝ :=
  (1 / (1 - α)) * Real.log (∫ x, (f.pdf x) ^ α)

/-- Convolution of two densities on `ℝ^d` (corresponding to `X + Y` for independent `X, Y`). -/
noncomputable def densityConv {d : ℕ} (f g : Density d) : (Fin d → ℝ) → ℝ :=
  fun x => ∫ y, f.pdf y * g.pdf (x - y)

/-- Standard 1D Gaussian density with variance `v > 0`. -/
noncomputable def gaussianPdf1D (v : ℝ) (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x ^ 2) / (2 * v))

end InfoTheory
