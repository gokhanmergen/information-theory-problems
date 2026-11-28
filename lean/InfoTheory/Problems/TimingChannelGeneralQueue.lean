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

/-- Predicate stating that `S` is an exponential (memoryless) service density `Exp(μ)`,
    `μ > 0`: the case where departure feedback yields no capacity gain
    (Anantharam–Verdú 1996). -/
def IsExponential (S : ServiceDensity) : Prop :=
  ∃ μ : ℝ, 0 < μ ∧
    (∀ᵐ x : ℝ ∂volume, 0 < x → S.pdf x = μ * Real.exp (-μ * x))

/-- Lindley recursion computing the `n` FIFO departure times `D_1, ..., D_n` from arrival
    epochs `a : Fin n → ℝ` and service times `s : Fin n → ℝ`. -/
def lindleyDepartures (n : ℕ) (a s : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    Nat.recOn (motive := fun _ => ℝ) i.1
      (max (a ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩) 0 +
        s ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩)
      (fun k prev =>
        if hk : k + 1 < n then max (a ⟨k + 1, hk⟩) prev + s ⟨k + 1, hk⟩ else prev)

/-- Departure time of the last (`n`-th) packet, `0` when `n = 0`. -/
def lastDeparture (n : ℕ) (a s : Fin n → ℝ) : ℝ :=
  if h : 0 < n then lindleyDepartures n a s ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩ else 0

/-- Operational no-feedback capacity `C(S, λ)` (in nats per unit time) of the FIFO `·/G/1`
    queue timing channel at output rate `λ` (Anantharam–Verdú 1996; Sahasranand–Tchamkerten
    2023, Def. of `(n, M, n/λ, ε)`-codes): `n` packets, `M ≈ e^{(n/λ) R}` equiprobable
    messages, nondecreasing nonnegative arrival epochs, the `n`-th departure occurring **on
    average** (over messages and service times) no later than `n/λ`, measurable decoders,
    and average error probability at most `ε`. The expected last departure is a Lebesgue
    `lintegral` (junk-free: no integrability side condition). -/
noncomputable def queueNoFeedbackCapacity (S : ServiceDensity) (lam : ℝ) : ℝ :=
  sSup { R : ℝ | 0 ≤ R ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      let M : ℕ := Nat.max 1 (Nat.floor (Real.exp (((n : ℝ) / lam) * R)))
      ∃ (enc : Fin M → Fin n → ℝ) (dec : (Fin n → ℝ) → Fin M),
        Measurable dec ∧
        (∀ m : Fin M, ∀ i : Fin n, 0 ≤ enc m i) ∧
        (∀ m : Fin M, ∀ i j : Fin n, i ≤ j → enc m i ≤ enc m j) ∧
        (∑ m : Fin M, ∫⁻ s : Fin n → ℝ,
            ENNReal.ofReal (lastDeparture n (enc m) s * ∏ i : Fin n, S.pdf (s i))) ≤
          ENNReal.ofReal ((M : ℝ) * ((n : ℝ) / lam)) ∧
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
    for every non-exponential continuous service-time density `S` and every output rate
    `0 < λ < 1 / E[S]`, full causal departure-time feedback strictly increases the FIFO
    timing-channel capacity. (Proved for bounded-support service times by Sahasranand–Tchamkerten,
    arXiv:2309.14145; open for general unbounded-support non-exponential service times.)

    **Statement-fix (2026-11-27).** (1) The previous no-feedback capacity constrained the
    *arrival* epochs to `[0, n/λ]` instead of the expected *last departure* `≤ n/λ`. That
    relaxation lets an encoder signal at any lower output rate `λ' < λ` on part of the window
    and dump the remaining packets at time `n/λ`, so it computes (at least)
    `sup_{λ' ≤ λ} C(λ')` rather than `C(λ)`. Since `queueFeedbackCapacity S λ → 0` as
    `λ ↑ 1/E[S]` while `sup_{λ' ≤ λ} C(λ') ≥ C(λ*) > 0` for a fixed `λ* < λ`, the old
    Statement was false as written for every service density (sketch). The code definition
    now follows Anantharam–Verdú / Sahasranand–Tchamkerten: `E[D_n] ≤ n/λ`. (2) The excluded
    class was "shifted exponential `c + Exp(μ)`"; the conjecture as posed excludes only the
    memoryless (exponential) service times, and the stated reason for excluding `c > 0`
    (that the constant delay cancels in the Lindley recursion) is incorrect, since `c` also
    occupies the server. The exclusion is now `IsExponential`. -/
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
