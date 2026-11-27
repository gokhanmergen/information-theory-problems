import InfoTheory.Core
import InfoTheory.Core.GaussianOperational

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfoTheory.Problems.GaussianBcFeedbackSumCapacity

/-- A pair of received blocks `(y₁ⁿ, y₂ⁿ)` of the two-receiver broadcast channel. -/
abbrev BcBlock (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- An `(n, M₁, M₂)` code for the two-receiver broadcast channel with perfect causal output
    feedback from both receivers (El Gamal–Kim Ch. 17; Belhadj Amor–Steinberg–Wigger 2015):
    the channel input at time `i` is `enc i m₁ m₂ (y₁, y₂)`, which may depend only on the
    past outputs `(y₁,t, y₂,t)_{t < i}` (`causal`) and is jointly measurable in the outputs;
    receiver `k` decodes its own message with a measurable decoder of its own block. -/
structure BcFeedbackCode (n M₁ M₂ : ℕ) where
  /-- Encoder: time index, both messages, and the (causally used) output blocks. -/
  enc : Fin n → Fin M₁ → Fin M₂ → BcBlock n → ℝ
  /-- Causality: `enc i` depends only on the outputs at times `t < i`. -/
  causal : ∀ (i : Fin n) (m₁ : Fin M₁) (m₂ : Fin M₂) (y y' : BcBlock n),
    (∀ t : Fin n, t < i → y.1 t = y'.1 t ∧ y.2 t = y'.2 t) → enc i m₁ m₂ y = enc i m₁ m₂ y'
  /-- Each encoding map is measurable in the fed-back outputs. -/
  measurable_enc : ∀ i m₁ m₂, Measurable (enc i m₁ m₂)
  /-- Decoder of receiver 1. -/
  dec₁ : (Fin n → ℝ) → Fin M₁
  /-- Decoder of receiver 2. -/
  dec₂ : (Fin n → ℝ) → Fin M₂
  measurable_dec₁ : Measurable dec₁
  measurable_dec₂ : Measurable dec₂

namespace BcFeedbackCode

variable {n M₁ M₂ : ℕ} (C : BcFeedbackCode n M₁ M₂) (h₁ h₂ : ℝ)

/-- One pass of the channel equations `y_{k,i} = h_k x_i(m₁, m₂, y^{i-1}) + z_{k,i}`. -/
def step (m₁ : Fin M₁) (m₂ : Fin M₂) (z y : BcBlock n) : BcBlock n :=
  (fun i => h₁ * C.enc i m₁ m₂ y + z.1 i, fun i => h₂ * C.enc i m₁ m₂ y + z.2 i)

/-- The received blocks for messages `(m₁, m₂)` and noise `z = (z₁ⁿ, z₂ⁿ)`: `n` passes of
    `step` starting from `z`.  By causality, after `t` passes the first `t` output symbols are
    final, so this is the (unique) solution of the causal channel equations. -/
def output (m₁ : Fin M₁) (m₂ : Fin M₂) (z : BcBlock n) : BcBlock n :=
  (C.step h₁ h₂ m₁ m₂ z)^[n] z

/-- The transmitted block `xᵢ = enc i m₁ m₂ (y^{i-1})` along the realized outputs. -/
def input (m₁ : Fin M₁) (m₂ : Fin M₂) (z : BcBlock n) : Fin n → ℝ :=
  fun i => C.enc i m₁ m₂ (C.output h₁ h₂ m₁ m₂ z)

/-- Independent unit-variance noises `Z₁ⁿ, Z₂ⁿ ~ N(0, 1)^{⊗n}`. -/
noncomputable def noise (n : ℕ) : Measure (BcBlock n) :=
  (awgnNoise n 1).prod (awgnNoise n 1)

/-- Error probability for the message pair `(m₁, m₂)` (a value of a measure, in `ℝ≥0∞`). -/
noncomputable def errorProb (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ≥0∞ :=
  noise n {z | C.dec₁ (C.output h₁ h₂ m₁ m₂ z).1 ≠ m₁ ∨ C.dec₂ (C.output h₁ h₂ m₁ m₂ z).2 ≠ m₂}

/-- Average error probability over uniformly distributed message pairs. -/
noncomputable def avgErrorProb : ℝ≥0∞ :=
  ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, C.errorProb h₁ h₂ m₁ m₂

/-- Expected block energy `E[∑ᵢ Xᵢ²]` (over uniform messages and the noise), as a lower
    Lebesgue integral in `ℝ≥0∞` (infinite energy is `⊤`, never `0`). -/
noncomputable def expectedEnergy : ℝ≥0∞ :=
  ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
    ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (C.input h₁ h₂ m₁ m₂ z i) ^ 2) ∂noise n

/-- Expected block power constraint `∑ᵢ E[Xᵢ²] ≤ nP` (Ozarow–Leung 1984; Belhadj Amor–Steinberg–
    Wigger 2015). -/
def SatisfiesPower (P : ℝ) : Prop :=
  C.expectedEnergy h₁ h₂ ≤ ENNReal.ofReal ((n : ℝ) * P)

end BcFeedbackCode

/-- Operational achievability of `(R₁, R₂)` over the Gaussian broadcast channel
    `Y_k = h_k X + Z_k` (`k = 1, 2`, independent `Z_k ~ N(0, 1)`) with perfect output feedback and
    expected power `P`. -/
def IsBcFbAchievable (h₁ h₂ P R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : BcFeedbackCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊)
        (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊),
      C.SatisfiesPower h₁ h₂ P ∧ C.avgErrorProb h₁ h₂ ≤ ENNReal.ofReal δ

/-- Feedback sum-capacity, valued in `ℝ≥0∞` (an unbounded achievable set gives `⊤`, not `0`). -/
noncomputable def bcFbSumCapacity (h₁ h₂ P : ℝ) : ℝ≥0∞ :=
  sSup { r : ℝ≥0∞ | ∃ R₁ R₂ : ℝ, IsBcFbAchievable h₁ h₂ P R₁ R₂ ∧ r = ENNReal.ofReal (R₁ + R₂) }

/-- The linear-feedback capacity region of the two-user scalar Gaussian BC (Belhadj Amor–
    Steinberg–Wigger 2015, Cor. 2, via MAC–BC duality with Ozarow's region): rate pairs with,
    for some power split `P₁ + P₂ = P` and `ρ ∈ [0, 1]`,
    `R₁ ≤ ½ log₂(1 + h₁²P₁(1-ρ²))`, `R₂ ≤ ½ log₂(1 + h₂²P₂(1-ρ²))`,
    `R₁ + R₂ ≤ ½ log₂(1 + h₁²P₁ + h₂²P₂ + 2|h₁h₂|√(P₁P₂) ρ)`. -/
def InLinearFbRegion (h₁ h₂ P R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ P₁ P₂ ρ : ℝ, 0 ≤ P₁ ∧ 0 ≤ P₂ ∧ P₁ + P₂ = P ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
    R₁ ≤ (1 / 2 : ℝ) * log2 (1 + h₁ ^ 2 * P₁ * (1 - ρ ^ 2)) ∧
    R₂ ≤ (1 / 2 : ℝ) * log2 (1 + h₂ ^ 2 * P₂ * (1 - ρ ^ 2)) ∧
    R₁ + R₂ ≤ (1 / 2 : ℝ) * log2 (1 + h₁ ^ 2 * P₁ + h₂ ^ 2 * P₂ +
      2 * |h₁ * h₂| * Real.sqrt (P₁ * P₂) * ρ)

/-- Linear-feedback sum-capacity `max {R₁ + R₂ : (R₁, R₂) ∈ InLinearFbRegion}`.  The set is
    nonempty and bounded above for `P ≥ 0` (certified), so this `sSup` is not a junk value. -/
noncomputable def linearFbSumRate (h₁ h₂ P : ℝ) : ℝ :=
  sSup { s : ℝ | ∃ R₁ R₂ : ℝ, InLinearFbRegion h₁ h₂ P R₁ R₂ ∧ s = R₁ + R₂ }

/-- Sum-Capacity of the Symmetric Gaussian Broadcast Channel with Feedback (Ozarow–Leung 1984;
    Elia 2004; Belhadj Amor–Steinberg–Wigger 2015): for the two-receiver Gaussian BC with equal
    gains, independent noises and perfect feedback, is the feedback sum-capacity equal to the
    linear-feedback sum-capacity (achieved by the LQG / control-theoretic schemes)? -/
def Statement : Prop :=
  ∀ h P : ℝ, h ≠ 0 → 0 < P →
    bcFbSumCapacity h h P = ENNReal.ofReal (linearFbSumRate h h P)

def problem : OpenProblem where
  id := "gaussian-bc-feedback-sum-capacity"
  title := "Sum-Capacity of the Symmetric Gaussian Broadcast Channel with Feedback"
  category := .networkInfoTheory
  status := .open
  posedBy := "Lawrence H. Ozarow and S. K. Leung-Yan-Cheong; Belhadj Amor, Steinberg and Wigger"
  posedYear := 1984
  statement := Statement

end InfoTheory.Problems.GaussianBcFeedbackSumCapacity
