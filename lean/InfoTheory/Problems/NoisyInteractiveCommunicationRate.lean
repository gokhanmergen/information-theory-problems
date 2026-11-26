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

/-- Pair of local views `(viewA, viewB)` after `t` rounds of a noisy alternating
    interactive protocol over `BSC(ε)` under channel error pattern `e : Fin N → Bool`. -/
def runNoisyViews {kX kY N : ℕ}
    (alice : (t : ℕ) → Fin kX → (Fin t → Bool) → Bool)
    (bob : (t : ℕ) → Fin kY → (Fin t → Bool) → Bool)
    (x : Fin kX) (y : Fin kY) (e : Fin N → Bool) :
    (t : ℕ) → (Fin t → Bool) × (Fin t → Bool)
  | 0 => (fun i => Fin.elim0 i, fun i => Fin.elim0 i)
  | t + 1 =>
    let prev := runNoisyViews alice bob x y e t
    let errBit : Bool := if h : t < N then e ⟨t, h⟩ else false
    let aNext : Bool := if t % 2 = 0 then alice t x prev.1 else xor (bob t y prev.2) errBit
    let bNext : Bool := if t % 2 = 0 then xor (alice t x prev.1) errBit else bob t y prev.2
    (fun i => if h : i.1 < t then prev.1 ⟨i.1, h⟩ else aNext,
     fun i => if h : i.1 < t then prev.2 ⟨i.1, h⟩ else bNext)

/-- Interactive coding capacity `C_int(ε)` over `BSC(ε)` for simulating arbitrary
    `T`-round noiseless alternating interactive protocols with vanishing worst-case error. -/
noncomputable def interactiveCapacityBSC (ε : ℝ) : ℝ :=
  sSup { R : ℝ | 0 ≤ R ∧
    ∀ (δ : ℝ), 0 < δ → ∃ (T₀ : ℕ), ∀ (T : ℕ), T₀ ≤ T →
      ∀ (kX kY : ℕ)
        (alice0 : (t : ℕ) → Fin kX → (Fin t → Bool) → Bool)
        (bob0 : (t : ℕ) → Fin kY → (Fin t → Bool) → Bool),
        ∃ (N : ℕ)
          (alice1 : (t : ℕ) → Fin kX → (Fin t → Bool) → Bool)
          (bob1 : (t : ℕ) → Fin kY → (Fin t → Bool) → Bool)
          (outA : Fin kX → (Fin N → Bool) → (Fin T → Bool))
          (outB : Fin kY → (Fin N → Bool) → (Fin T → Bool)),
          0 < N ∧ (T : ℝ) ≥ R * (N : ℝ) ∧
          ∀ (x : Fin kX) (y : Fin kY),
            let τ := runNoiseless alice0 bob0 x y T
            (∑ e : Fin N → Bool,
              (∏ i : Fin N, if e i then ε else 1 - ε) *
                if outA x (runNoisyViews alice1 bob1 x y e N).1 = τ ∧
                   outB y (runNoisyViews alice1 bob1 x y e N).2 = τ
                then (0 : ℝ) else 1) ≤ δ }

/-- Shannon-scaling overhead conjecture for interactive communication over `BSC(ε)`:
    does `1 - C_int(ε) = O(h(ε))` as `ε → 0⁺` (versus a strictly larger overhead such as
    `Θ(√(ε log(1/ε)))` or `Θ(√ε)`)? -/
def Statement : Prop :=
  ∃ (C ε₀ : ℝ), 0 < C ∧ 0 < ε₀ ∧ ε₀ < (1 : ℝ) / 2 ∧
    ∀ (ε : ℝ), 0 < ε → ε < ε₀ →
      1 - interactiveCapacityBSC ε ≤ C * binaryEntropy ε

def problem : OpenProblem where
  id := "noisy-interactive-communication-rate"
  title := "Exact Interactive Coding Capacity over the Binary Symmetric Channel as ε → 0"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Leonard J. Schulman; Gillat Kol and Ran Raz"
  posedYear := 1996
  statement := Statement

end InfoTheory.Problems.NoisyInteractiveCommunicationRate
