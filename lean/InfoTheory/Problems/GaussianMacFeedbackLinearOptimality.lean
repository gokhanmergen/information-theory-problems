import InfoTheory.Core
import InfoTheory.Core.GaussianOperational

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfoTheory.Problems.GaussianMacFeedbackLinearOptimality

/-- An `(n, (M_j)_j)` code for the `K`-user multiple-access channel with perfect causal output
    feedback to all senders (Ozarow 1984; Kramer 2002; Ardestanizadeh–Wigger–Kim–Javidi 2012,
    §II): sender `j` transmits `enc j i m_j y` at time `i`, which may depend only on its own
    message and on the past outputs `(y_t)_{t < i}` (`causal`) and is measurable in `y`;
    the receiver decodes each message with a measurable decoder. -/
structure MacFeedbackCode (K n : ℕ) (M : Fin K → ℕ) where
  /-- Encoder of sender `j` at time `i`. -/
  enc : (j : Fin K) → Fin n → Fin (M j) → (Fin n → ℝ) → ℝ
  /-- Causality: `enc j i` depends only on the outputs at times `t < i`. -/
  causal : ∀ (j : Fin K) (i : Fin n) (m : Fin (M j)) (y y' : Fin n → ℝ),
    (∀ t : Fin n, t < i → y t = y' t) → enc j i m y = enc j i m y'
  /-- Each encoding map is measurable in the fed-back outputs. -/
  measurable_enc : ∀ j i m, Measurable (enc j i m)
  /-- Decoder for the message of sender `j`. -/
  dec : (j : Fin K) → (Fin n → ℝ) → Fin (M j)
  measurable_dec : ∀ j, Measurable (dec j)

namespace MacFeedbackCode

variable {K n : ℕ} {M : Fin K → ℕ} (C : MacFeedbackCode K n M)

/-- One pass of the channel equation `yᵢ = ∑_j x_{j,i}(m_j, y^{i-1}) + zᵢ`. -/
def step (m : (j : Fin K) → Fin (M j)) (z y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (∑ j : Fin K, C.enc j i (m j) y) + z i

/-- The received block for messages `m` and noise `z`: `n` passes of `step` from `z`.  By
    causality, after `t` passes the first `t` output symbols are final, so this is the (unique)
    solution of the causal channel equations. -/
def output (m : (j : Fin K) → Fin (M j)) (z : Fin n → ℝ) : Fin n → ℝ :=
  (C.step m z)^[n] z

/-- Transmitted block of sender `j` along the realized output. -/
def input (j : Fin K) (m : (j : Fin K) → Fin (M j)) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => C.enc j i (m j) (C.output m z)

/-- Error probability for the message tuple `m` under noise `Zⁿ ~ N(0, N)^{⊗n}`: the noise
    measure of `{∃ j, m̂_j ≠ m_j}` (in `ℝ≥0∞`). -/
noncomputable def errorProb (N : ℝ) (m : (j : Fin K) → Fin (M j)) : ℝ≥0∞ :=
  awgnNoise n N {z | ∃ j, C.dec j (C.output m z) ≠ m j}

/-- Average error probability over uniformly distributed message tuples. -/
noncomputable def avgErrorProb (N : ℝ) : ℝ≥0∞ :=
  ((∏ j, M j : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : (j : Fin K) → Fin (M j), C.errorProb N m

/-- Expected block energy `E[∑ᵢ X_{j,i}²]` of sender `j` (uniform messages, Gaussian noise), as
    a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def expectedEnergy (N : ℝ) (j : Fin K) : ℝ≥0∞ :=
  ((∏ j, M j : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : (j : Fin K) → Fin (M j),
    ∫⁻ z, ENNReal.ofReal (∑ i : Fin n, (C.input j m z i) ^ 2) ∂awgnNoise n N

/-- Symmetric expected block power constraints `∑ᵢ E[X_{j,i}²] ≤ nP` for every sender
    (Ardestanizadeh–Wigger–Kim–Javidi 2012; Sula–Gastpar–Kramer 2020). -/
def SatisfiesPower (N P : ℝ) : Prop :=
  ∀ j, C.expectedEnergy N j ≤ ENNReal.ofReal ((n : ℝ) * P)

/-- Linear-feedback code (Ardestanizadeh–Wigger–Kim–Javidi 2012, Def. 1): each input is an
    arbitrary (nonlinear) function of the own message plus a fixed linear combination of past
    outputs, `x_{j,i} = w_j(m_j)ᵢ + ∑_{t < i} B_j(i, t) y_t`.  (Def. 1's `L_{ji}(θ_j(m_j), y^{i-1})`
    with `θ_j` arbitrary and `L_{ji}` linear is exactly this class: put `w_j = A_j ∘ θ_j`.) -/
def IsLinear : Prop :=
  ∃ (w : (j : Fin K) → Fin (M j) → Fin n → ℝ) (B : Fin K → Fin n → Fin n → ℝ),
    (∀ j i t, i ≤ t → B j i t = 0) ∧
    ∀ j i m y, C.enc j i m y = w j m i + ∑ t : Fin n, B j i t * y t

end MacFeedbackCode

/-- Operational achievability of the rate vector `R` over the `K`-user Gaussian MAC
    `Y = ∑_j X_j + Z`, `Z ~ N(0, N)`, with feedback and symmetric expected power `P`; with
    `linearOnly = true` only linear-feedback codes are allowed. -/
def IsMacFbAchievable (K : ℕ) (P N : ℝ) (linearOnly : Bool) (R : Fin K → ℝ) : Prop :=
  (∀ j, 0 ≤ R j) ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : MacFeedbackCode K n (fun j => max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R j)⌋₊),
      (linearOnly = true → C.IsLinear) ∧ C.SatisfiesPower N P ∧
        C.avgErrorProb N ≤ ENNReal.ofReal δ

/-- Achievable rate vectors with arbitrary (causal, measurable) feedback codes. -/
def macFbRegion (K : ℕ) (P N : ℝ) : Set (Fin K → ℝ) :=
  { R | IsMacFbAchievable K P N false R }

/-- Achievable rate vectors with linear-feedback codes. -/
def macLinearFbRegion (K : ℕ) (P N : ℝ) : Set (Fin K → ℝ) :=
  { R | IsMacFbAchievable K P N true R }

/-- Is Linear Feedback Optimal for the Symmetric `K`-User Gaussian MAC with Feedback, `K ≥ 3`?
    (Ozarow 1984 for `K = 2`; Kramer 2002; Ardestanizadeh–Wigger–Kim–Javidi 2012;
    Sula–Gastpar–Kramer 2020): is the closure of the feedback capacity region equal to the
    closure of the region achievable by linear-feedback codes, under equal powers `P`? -/
def Statement : Prop :=
  ∀ (K : ℕ) (P N : ℝ), 3 ≤ K → 0 < P → 0 < N →
    closure (macFbRegion K P N) = closure (macLinearFbRegion K P N)

def problem : OpenProblem where
  id := "gaussian-mac-feedback-linear-optimality"
  title := "Optimality of Linear Feedback for the Symmetric K-User Gaussian MAC with Feedback"
  category := .networkInfoTheory
  status := .open
  posedBy := "Gerhard Kramer; Ardestanizadeh, Wigger, Kim and Javidi; Sula, Gastpar and Kramer"
  posedYear := 2002
  statement := Statement

end InfoTheory.Problems.GaussianMacFeedbackLinearOptimality
