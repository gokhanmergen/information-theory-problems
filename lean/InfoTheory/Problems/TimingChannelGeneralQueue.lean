import InfoTheory.Core

open scoped BigOperators Classical
open MeasureTheory

namespace InfoTheory.Problems.TimingChannelGeneralQueue

/-- A continuous service-time probability density on `(0, ∞)` with finite positive mean
    and finite differential entropy. -/
structure ServiceDensity where
  pdf : ℝ → ℝ
  nonneg : ∀ x : ℝ, 0 ≤ pdf x
  pos_support : ∀ x : ℝ, x ≤ 0 → pdf x = 0
  integrable : Integrable pdf volume
  integral_one : ∫ x : ℝ, pdf x = 1
  finite_entropy : Integrable (fun x : ℝ => if pdf x ≤ 0 then 0 else -pdf x * Real.log (pdf x)) volume
  mean : ℝ
  mean_pos : 0 < mean
  mean_eq : ∫ x : ℝ, x * pdf x = mean

/-- Predicate stating that `S` is exponentially distributed (a.e.) with rate `μ = 1 / S.mean`. -/
def IsExponential (S : ServiceDensity) : Prop :=
  let μ : ℝ := 1 / S.mean
  ∀ᵐ x : ℝ ∂volume, 0 < x → S.pdf x = μ * Real.exp (-μ * x)

/-- Lindley recursion computing the `n` FIFO departure times `D_1, ..., D_n` from arrival
    epochs `a : Fin n → ℝ` and service times `s : Fin n → ℝ`. -/
def lindleyDepartures (n : ℕ) (a s : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    Nat.recOn (motive := fun _ => ℝ) i.1
      (max (a ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩) 0 +
        s ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩)
      (fun k prev =>
        if hk : k + 1 < n then max (a ⟨k + 1, hk⟩) prev + s ⟨k + 1, hk⟩ else prev)

/-- Operational no-feedback capacity `C(S, λ)` (in nats per unit time) of the FIFO `·/G/1`
    queue timing channel with measurable decoders and Lebesgue `lintegral` error. -/
noncomputable def queueNoFeedbackCapacity (S : ServiceDensity) (lam : ℝ) : ℝ :=
  sSup { R : ℝ | 0 ≤ R ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      let M : ℕ := Nat.max 1 (Nat.floor (Real.exp (((n : ℝ) / lam) * R)))
      ∃ (enc : Fin M → Fin n → ℝ) (dec : (Fin n → ℝ) → Fin M),
        Measurable dec ∧
        (∀ m : Fin M, ∀ i : Fin n, 0 ≤ enc m i) ∧
        (∀ m : Fin M, ∀ i j : Fin n, i ≤ j → enc m i ≤ enc m j) ∧
        (∀ m : Fin M, ∀ i : Fin n, enc m i ≤ (n : ℝ) / lam) ∧
        ((1 : ℝ) / (M : ℝ)) *
          ∑ m : Fin M, (∫⁻ s : Fin n → ℝ,
            if dec (lindleyDepartures n (enc m) s) ≠ m
            then ENNReal.ofReal (∏ i : Fin n, S.pdf (s i)) else 0).toReal ≤ ε }

/-- Single-letter full-feedback capacity `C_fb(S, λ) = λ · sup_{W ≥ 0, E[W] ≤ 1/λ - E[S]} I(W; W + S)`
    of the FIFO `·/G/1` queue timing channel (Anantharam–Verdú 1996), evaluated in nats/sec. -/
noncomputable def queueFeedbackCapacity (S : ServiceDensity) (lam : ℝ) : ℝ :=
  lam * sSup { r : ℝ | ∃ (W : ServiceDensity),
    W.mean ≤ 1 / lam - S.mean ∧
    let convPdf (y : ℝ) : ℝ := ∫ w : ℝ, W.pdf w * S.pdf (y - w)
    let hWS : ℝ := ∫ y : ℝ, if convPdf y ≤ 0 then 0 else -convPdf y * Real.log (convPdf y)
    let hS : ℝ := ∫ x : ℝ, if S.pdf x ≤ 0 then 0 else -S.pdf x * Real.log (S.pdf x)
    r = hWS - hS }

/-- Anantharam–Verdú Feedback Conjecture for the General `·/G/1` Queue Timing Channel (1996):
    for every non-exponential continuous service-time density `S` and every arrival rate
    `0 < λ < 1 / E[S]`, full causal departure-time feedback strictly increases the FIFO
    timing-channel capacity. (Proved for bounded-support service times by Sahasranand–Tchamkerten
    2024; open for general unbounded-support non-exponential service times.) -/
def Statement : Prop :=
  ∀ (S : ServiceDensity), ¬ IsExponential S →
    ∀ (lam : ℝ), 0 < lam → lam < 1 / S.mean →
      queueNoFeedbackCapacity S lam < queueFeedbackCapacity S lam

def problem : OpenProblem where
  id := "timing-channel-general-queue"
  title := "Feedback Capacity Gain of the General Single-Server Queue Timing Channel"
  category := .channelCapacity
  status := .partiallySolved
  posedBy := "Venkat Anantharam and Sergio Verdú"
  posedYear := 1996
  statement := Statement

end InfoTheory.Problems.TimingChannelGeneralQueue
