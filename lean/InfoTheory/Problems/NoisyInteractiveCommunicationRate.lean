import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.NoisyInteractiveCommunicationRate

/-- Deterministic transcript evaluator for a noiseless alternating interactive protocol
    (Alice sends on even rounds, Bob sends on odd rounds). -/
def runNoiseless {kX kY : ℕ}
    (alice : (t : ℕ) → Fin kX → (Fin t → Bool) → Bool)
    (bob : (t : ℕ) → Fin kY → (Fin t → Bool) → Bool)
    (x : Fin kX) (y : Fin kY) : (t : ℕ) → (Fin t → Bool)
  | 0 => fun i => Fin.elim0 i
  | t + 1 =>
    let prev := runNoiseless alice bob x y t
    let nextBit := if t % 2 = 0 then alice t x prev else bob t y prev
    fun i => if h : i.1 < t then prev ⟨i.1, h⟩ else nextBit

/-- Pair of local views `(viewA, viewB)` after `t` rounds of a **randomized adaptive**
    interactive protocol over `BSC(ε)` with shared randomness `r : Fin kR` and channel error
    pattern `e : Fin N → Bool`. At each round `t`, each party outputs `Option Bool`:
    `some b` means transmit bit `b`, `none` means listen (receiving `xor b_other errBit` if the
    other party transmits `some b_other`, or `errBit` on silence/collision). -/
def runAdaptiveNoisyViews {kX kY kR N : ℕ}
    (alice : (t : ℕ) → Fin kX → Fin kR → (Fin t → Option Bool) → Option Bool)
    (bob : (t : ℕ) → Fin kY → Fin kR → (Fin t → Option Bool) → Option Bool)
    (x : Fin kX) (y : Fin kY) (r : Fin kR) (e : Fin N → Bool) :
    (t : ℕ) → (Fin t → Option Bool) × (Fin t → Option Bool)
  | 0 => (fun i => Fin.elim0 i, fun i => Fin.elim0 i)
  | t + 1 =>
    let prev := runAdaptiveNoisyViews alice bob x y r e t
    let errBit : Bool := if h : t < N then e ⟨t, h⟩ else false
    let actA := alice t x r prev.1
    let actB := bob t y r prev.2
    let obsA : Option Bool :=
      match actA, actB with
      | some _, _ => none
      | none, some b => some (xor b errBit)
      | none, none => some errBit
    let obsB : Option Bool :=
      match actA, actB with
      | _, some _ => none
      | some a, none => some (xor a errBit)
      | none, none => some errBit
    (fun i => if h : i.1 < t then prev.1 ⟨i.1, h⟩ else obsA,
     fun i => if h : i.1 < t then prev.2 ⟨i.1, h⟩ else obsB)

/-- Adaptive randomized interactive coding capacity `C_int(ε)` over `BSC(ε)` (Haeupler 2014;
    Efremenko–Gelles–Haeupler 2016) for simulating arbitrary `T`-round noiseless alternating
    protocols with vanishing worst-case error (bypassing the Kol–Raz 2013 non-adaptive
    `1 - Ω(√h(ε))` barrier via adaptive speaking order and shared randomness). -/
noncomputable def interactiveCapacityBSC (ε : ℝ) : ℝ :=
  sSup { R : ℝ | 0 ≤ R ∧
    ∀ (δ : ℝ), 0 < δ → ∃ (T₀ : ℕ), ∀ (T : ℕ), T₀ ≤ T →
      ∀ (kX kY : ℕ)
        (alice0 : (t : ℕ) → Fin kX → (Fin t → Bool) → Bool)
        (bob0 : (t : ℕ) → Fin kY → (Fin t → Bool) → Bool),
        ∃ (N kR : ℕ)
          (alice1 : (t : ℕ) → Fin kX → Fin kR → (Fin t → Option Bool) → Option Bool)
          (bob1 : (t : ℕ) → Fin kY → Fin kR → (Fin t → Option Bool) → Option Bool)
          (outA : Fin kX → Fin kR → (Fin N → Option Bool) → (Fin T → Bool))
          (outB : Fin kY → Fin kR → (Fin N → Option Bool) → (Fin T → Bool)),
          0 < N ∧ 0 < kR ∧ (T : ℝ) ≥ R * (N : ℝ) ∧
          ∀ (x : Fin kX) (y : Fin kY),
            let τ := runNoiseless alice0 bob0 x y T
            ((1 : ℝ) / (kR : ℝ)) *
              (∑ r : Fin kR, ∑ e : Fin N → Bool,
                (∏ i : Fin N, if e i then ε else 1 - ε) *
                  if outA x r (runAdaptiveNoisyViews alice1 bob1 x y r e N).1 = τ ∧
                     outB y r (runAdaptiveNoisyViews alice1 bob1 x y r e N).2 = τ
                  then (0 : ℝ) else 1) ≤ δ }

/-- Shannon-scaling overhead conjecture for adaptive randomized interactive communication
    over `BSC(ε)`: does `1 - C_int(ε) = O(h(ε))` as `ε → 0⁺` (versus a strictly larger
    overhead such as `Θ(√(ε log log(1/ε)))` or `Θ(√ε)`)? -/
def Statement : Prop :=
  ∃ (C ε₀ : ℝ), 0 < C ∧ 0 < ε₀ ∧ ε₀ < (1 : ℝ) / 2 ∧
    ∀ (ε : ℝ), 0 < ε → ε < ε₀ →
      1 - interactiveCapacityBSC ε ≤ C * binaryEntropy ε

def problem : OpenProblem where
  id := "noisy-interactive-communication-rate"
  title := "Exact Interactive Coding Capacity over the Binary Symmetric Channel as ε → 0"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Leonard J. Schulman; Gillat Kol and Ran Raz; Bernhard Haeupler"
  posedYear := 1996
  statement := Statement

end InfoTheory.Problems.NoisyInteractiveCommunicationRate
