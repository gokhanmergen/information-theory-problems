import InfoTheory.Core

open scoped BigOperators Classical ENNReal
open MeasureTheory

namespace InfoTheory.Problems.AwgnFeedbackErrorExponent

/-- Shannon's (1959) sphere-packing exponent `E_sp(R, P)` (in nats) for the AWGN channel
    with SNR `P > 0` at rate `R ∈ (0, ½ ln(1 + P))`. -/
noncomputable def awgnSpherePacking (R P : ℝ) : ℝ :=
  let A : ℝ := Real.sqrt P
  let sinT : ℝ := Real.exp (-R)
  let cosT : ℝ := Real.sqrt (1 - Real.exp (-2 * R))
  let g : ℝ := (1 / 2 : ℝ) * (A * cosT + Real.sqrt (P * cosT ^ 2 + 4))
  P / 2 - (A * g * cosT) / 2 - Real.log (g * sinT)

/-- Prefix of the first `k ≤ n` channel outputs generated causally by feedback encoder `enc`
    on message `m` and noise realization `z`. -/
def awgnFeedbackPrefix (n M : ℕ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ)
    (m : Fin M) (z : Fin n → ℝ) : (k : ℕ) → k ≤ n → (Fin k → ℝ)
  | 0, _ => fun j => Fin.elim0 j
  | k + 1, hk =>
      let prev : Fin k → ℝ := awgnFeedbackPrefix n M enc m z k (Nat.le_of_succ_le hk)
      let yk : ℝ := enc ⟨k, hk⟩ m prev + z ⟨k, hk⟩
      fun j => if h : j.1 < k then prev ⟨j.1, h⟩ else yk

/-- Average error probability of a measurable blocklength-`n`, `M`-message causal feedback
    code `(enc, dec)` over the unit-variance AWGN channel `Y_i = X_i + Z_i`, evaluated directly
    in `ℝ≥0∞` via Lebesgue `lintegral` (preventing Bochner/toReal junk `0`). -/
noncomputable def awgnFeedbackAvgError (n M : ℕ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ)
    (dec : (Fin n → ℝ) → Fin M) : ℝ≥0∞ :=
  if M = 0 then ⊤ else
    let gaussDensity (z : Fin n → ℝ) : ℝ :=
      ∏ i : Fin n, gaussianPdf1D 1 (z i)
    (M : ℝ≥0∞)⁻¹ *
      ∑ m : Fin M,
        ∫⁻ z : Fin n → ℝ,
          if dec (awgnFeedbackPrefix n M enc m z n (Nat.le_refl n)) ≠ m
          then ENNReal.ofReal (gaussDensity z) else 0

/-- Strict almost-sure codeword energy constraint `∑_{i=1}^n X_i(m, Y^{i-1})^2 ≤ n P` for all
    messages `m` and all channel output histories `y`. -/
def SatisfiesPeakEnergy (n M : ℕ) (P : ℝ)
    (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ) : Prop :=
  ∀ (m : Fin M) (y : Fin n → ℝ),
    ∑ i : Fin n, (enc i m (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) ^ 2 ≤ (n : ℝ) * P

/-- Optimal minimum average error probability `P_e*(n, M, P)` over all measurable,
    peak-energy-constrained causal feedback codes on the AWGN channel, valued in `ℝ≥0∞`
    so an empty feasible set evaluates to `⊤` rather than junk `0`. -/
noncomputable def awgnFeedbackPeakMinError (n M : ℕ) (P : ℝ) : ℝ≥0∞ :=
  sInf { e : ℝ≥0∞ | ∃ (enc : ∀ i : Fin n, Fin M → (Fin i.1 → ℝ) → ℝ)
    (dec : (Fin n → ℝ) → Fin M),
    (∀ i m, Measurable (enc i m)) ∧ Measurable dec ∧
    SatisfiesPeakEnergy n M P enc ∧ e = awgnFeedbackAvgError n M enc dec }

/-- Reliability function `E_fb^peak(R, P)` (in nats) of the peak-energy-constrained AWGN
    channel with noiseless causal feedback, valued in `ℝ≥0∞` so an unbounded exponent set
    evaluates to `⊤` rather than junk `0`. -/
noncomputable def awgnFeedbackPeakReliability (R P : ℝ) : ℝ≥0∞ :=
  sSup { e : ℝ≥0∞ | ∃ E : ℝ, 0 ≤ E ∧ e = ENNReal.ofReal E ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      awgnFeedbackPeakMinError n (Nat.ceil (Real.exp ((n : ℝ) * R))) P ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (E - ε))) }

/-- Peak-Energy AWGN Feedback Reliability Conjecture (Shannon 1959; Pinsker 1968):
    does the reliability function of the peak-energy-constrained AWGN channel with noiseless
    feedback equal Shannon's sphere-packing bound `E_sp(R, P)` at every SNR `P > 0` and
    every rate `0 < R < ½ ln(1 + P)`? (Known for `R ≥ R_crit` and as `R → 0⁺`; open for
    `0 < R < R_crit`.) -/
def Statement : Prop :=
  ∀ (P R : ℝ), 0 < P → 0 < R → R < (1 / 2 : ℝ) * Real.log (1 + P) →
    awgnFeedbackPeakReliability R P = ENNReal.ofReal (awgnSpherePacking R P)

def problem : OpenProblem where
  id := "awgn-feedback-error-exponent"
  title := "Reliability Function of the Peak-Energy-Constrained AWGN Channel with Feedback"
  category := .channelCapacity
  status := .open
  posedBy := "Claude E. Shannon; Mark S. Pinsker"
  posedYear := 1968
  statement := Statement

end InfoTheory.Problems.AwgnFeedbackErrorExponent
