import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import InfoTheory.Core.Entropy

/-!
# Operational Framework for Continuous-Alphabet (Gaussian) Channels

Definitions only.  Validation (non-vacuity, boundedness of the capacity set, the converse
`C_op ≤ ½ log₂(1 + P/N)`, and achievability of an explicit positive rate) is in
`InfoTheory.Known.GaussianChannel`.

References: Cover–Thomas, *Elements of Information Theory*, 2nd ed., Ch. 9 (§9.1 definitions
of an `(M, n)` code with power constraint, Def. of achievable rate and capacity);
El Gamal–Kim, *Network Information Theory*, Ch. 3 (§3.3, Gaussian channel).

## Design: why the classic junk values cannot occur here

Earlier continuous-alphabet statements broke in three ways; each is ruled out by construction:

1. **Non-measurable decoders.**  A `MeasurableBlockCode` carries a proof `measurable_decoder`.
   Hence every decoding region `decoder ⁻¹' {m}` is a measurable set and error probabilities are
   genuine probabilities (finitely additive over the decoding regions), not outer-measure or
   Bochner artefacts.  Encoders are maps out of the finite message set `Fin M`, hence
   automatically measurable.
2. **Power constraints via Bochner integrals.**  The power constraint is the deterministic,
   per-codeword inequality `∑ᵢ x(m)ᵢ² ≤ n P` (Cover–Thomas eq. (9.15) in its strong
   "every codeword" form; El Gamal–Kim §3.3).  No integral is involved, so "infinite power"
   cannot be counted as `0`.
3. **Error probabilities via Bochner integrals.**  Error probabilities are values of a
   *measure*, in `ℝ≥0∞`: `errorProb m = W (encoder m) {y | decoder y ≠ m}`.  There is no
   integrability side condition that could silently fail.
4. **`sSup` of an unbounded set.**  `awgnOperationalCapacity` is an `sSup` over a set that is
   proved nonempty and bounded above (by `½ log₂(1 + P/N)`) in
   `InfoTheory.Known.GaussianChannel`, for `0 ≤ P` and `0 < N`.
   (For `N ≤ 0` the noise degenerates to a point mass, every rate becomes achievable and the
   `sSup` *is* junk; all theorems therefore assume `0 < N`, as the problem statements must.)

## Generality

`MeasurableBlockCode α β n M` and `MeasurableBlockCode.errorProb` work for any input alphabet
`α`, any measurable output alphabet `β`, and any family of output laws
`W : (Fin n → α) → Measure (Fin n → β)` (e.g. a memoryless channel `memorylessLaw w`, or the law
of `(Y₁, Y₂)` for a Gaussian interference / broadcast channel).  Multi-user codes can be built
from several encoders and several `MeasurableBlockCode`-style measurable decoders.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace InfoTheory

/-! ### Generic measurable block codes -/

/-- An `(n, M)` block code with input alphabet `α` and measurable output alphabet `β`
    (Cover–Thomas Def. 7.5.1 / §9.1; El Gamal–Kim §3.1): a deterministic encoder
    `Fin M → (Fin n → α)` and a **measurable** decoder `(Fin n → β) → Fin M`.

    The encoder needs no measurability field: `Fin M` is finite (discrete σ-algebra), so every
    encoder is measurable. -/
structure MeasurableBlockCode (α β : Type*) [MeasurableSpace β] (n M : ℕ) where
  /-- Codeword `x(m) ∈ αⁿ` for message `m`. -/
  encoder : Fin M → Fin n → α
  /-- Decoding rule `ĝ : βⁿ → Fin M`. -/
  decoder : (Fin n → β) → Fin M
  /-- The decoder is measurable (rules out non-measurable "decoders" with junk error `0`). -/
  measurable_decoder : Measurable decoder

namespace MeasurableBlockCode

variable {α β : Type*} [MeasurableSpace β] {n M : ℕ}

/-- Conditional error probability `λ_m = W(x(m)) {y | ĝ(y) ≠ m}` of message `m`, where
    `W x` is the law of the channel output block given input block `x`.
    A value of a measure (in `ℝ≥0∞`), never a Bochner integral. -/
noncomputable def errorProb (C : MeasurableBlockCode α β n M)
    (W : (Fin n → α) → Measure (Fin n → β)) (m : Fin M) : ℝ≥0∞ :=
  W (C.encoder m) {y | C.decoder y ≠ m}

/-- Average error probability `P_e^{(n)} = (1/M) ∑_m λ_m` (Cover–Thomas eq. (7.31)). -/
noncomputable def avgErrorProb (C : MeasurableBlockCode α β n M)
    (W : (Fin n → α) → Measure (Fin n → β)) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, C.errorProb W m

/-- Maximal error probability `λ^{(n)} = max_m λ_m` (Cover–Thomas eq. (7.30)). -/
noncomputable def maxErrorProb (C : MeasurableBlockCode α β n M)
    (W : (Fin n → α) → Measure (Fin n → β)) : ℝ≥0∞ :=
  ⨆ m : Fin M, C.errorProb W m

/-- Deterministic per-codeword power (energy) constraint `∑ᵢ x(m)ᵢ² ≤ n P` for every message
    `m` (Cover–Thomas eq. (9.15); El Gamal–Kim §3.3).  No integral involved. -/
def SatisfiesPower (C : MeasurableBlockCode ℝ β n M) (P : ℝ) : Prop :=
  ∀ m : Fin M, ∑ i : Fin n, (C.encoder m i) ^ 2 ≤ (n : ℝ) * P

end MeasurableBlockCode

/-- Output-block law of a memoryless channel with per-letter output law `w : α → Measure β`:
    `W(x) = ⊗ᵢ w(xᵢ)` (realised with `Measure.pi`). -/
noncomputable def memorylessLaw {α β : Type*} [MeasurableSpace β] {n : ℕ}
    (w : α → Measure β) (x : Fin n → α) : Measure (Fin n → β) :=
  Measure.pi fun i => w (x i)

/-! ### The AWGN channel `Y = X + Z`, `Z ~ N(0, N)` i.i.d. -/

/-- Per-letter output law of the AWGN channel with noise variance `N`: `Y | X = a ~ N(a, N)`.
    (Mathlib's `gaussianReal` takes an `ℝ≥0` variance; `N` is truncated at `0`.) -/
noncomputable def awgnLetterLaw (N : ℝ) (a : ℝ) : Measure ℝ :=
  gaussianReal a N.toNNReal

/-- The i.i.d. noise law `Zⁿ ~ N(0, N)^{⊗n}` on `ℝⁿ`. -/
noncomputable def awgnNoise (n : ℕ) (N : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 N.toNNReal

/-- Output-block law of the memoryless AWGN channel given input block `x`:
    `Yⁿ = x + Zⁿ ~ ⊗ᵢ N(xᵢ, N)`. -/
noncomputable def awgnBlockLaw (n : ℕ) (N : ℝ) (x : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  memorylessLaw (awgnLetterLaw N) x

/-- An `(n, M)` code for the (real, scalar) AWGN channel. -/
abbrev AwgnCode (n M : ℕ) := MeasurableBlockCode ℝ ℝ n M

/-- Conditional error probability of message `m` over the AWGN channel, as the noise measure of
    the error event: `λ_m = P_Z {z | ĝ(x(m) + z) ≠ m}` (an `ℝ≥0∞`-valued measure, not an integral).
    Equals `C.errorProb (awgnBlockLaw n N) m` (proved in `Known.GaussianChannel`). -/
noncomputable def awgnErrorProb {n M : ℕ} (C : AwgnCode n M) (N : ℝ) (m : Fin M) : ℝ≥0∞ :=
  awgnNoise n N {z | C.decoder (C.encoder m + z) ≠ m}

/-- Average error probability `(1/M) ∑_m λ_m` of an AWGN code. -/
noncomputable def awgnAvgErrorProb {n M : ℕ} (C : AwgnCode n M) (N : ℝ) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, awgnErrorProb C N m

/-- Operational achievability of rate `R` (bits per channel use) over the AWGN channel with
    power constraint `P` and noise variance `N` (Cover–Thomas §9.1; El Gamal–Kim §3.3): for every
    `δ > 0` and all sufficiently large `n` there is an `(n, max 1 ⌊2^{nR}⌋)` code with measurable
    decoder, every codeword satisfying `∑ᵢ x(m)ᵢ² ≤ nP`, and average error probability `≤ δ`.
    (Same shape as `InfoTheory.Bridge.IsDmcAchievableRate`.) -/
def IsAwgnAchievable (P N R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : AwgnCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊),
      C.SatisfiesPower P ∧ awgnAvgErrorProb C N ≤ ENNReal.ofReal δ

/-- Operational capacity of the AWGN channel: `sSup` of achievable rates.  The defining set is
    nonempty and bounded above for `0 ≤ P`, `0 < N` (see `Known.GaussianChannel`), so this is
    not a junk value there. -/
noncomputable def awgnOperationalCapacity (P N : ℝ) : ℝ :=
  sSup { R : ℝ | IsAwgnAchievable P N R }

/-- Shannon's AWGN capacity formula `½ log₂(1 + P/N)` in bits (Cover–Thomas eq. (9.17)). -/
noncomputable def awgnCapacityFormula (P N : ℝ) : ℝ :=
  (1 / 2 : ℝ) * log2 (1 + P / N)

end InfoTheory
