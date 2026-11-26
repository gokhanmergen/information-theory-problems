import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ZeroErrorBroadcastChannel

/-- Instruction set of a Turing-complete Minsky register machine with `numRegs` registers
    and `numInsts` program lines. -/
inductive RegInstr (numRegs numInsts : ℕ) where
  | inc (r : Fin numRegs) (next : Fin numInsts)
  | decJz (r : Fin numRegs) (ifPos ifZero : Fin numInsts)
  | halt

/-- One execution step of a register machine program `prog`. -/
def regStep {numRegs numInsts : ℕ} (prog : Fin numInsts → RegInstr numRegs numInsts)
    (state : Fin numInsts × (Fin numRegs → ℕ)) : Fin numInsts × (Fin numRegs → ℕ) :=
  match prog state.1 with
  | .inc r next => (next, fun j => if j = r then state.2 j + 1 else state.2 j)
  | .decJz r ifPos ifZero =>
      if state.2 r = 0 then (ifZero, state.2)
      else (ifPos, fun j => if j = r then state.2 j - 1 else state.2 j)
  | .halt => state

/-- Running a register machine for `t` steps from initial state `s`. -/
def regRun {numRegs numInsts : ℕ} (prog : Fin numInsts → RegInstr numRegs numInsts) :
    ℕ → (Fin numInsts × (Fin numRegs → ℕ)) → (Fin numInsts × (Fin numRegs → ℕ))
  | 0, s => s
  | t + 1, s => regRun prog t (regStep prog s)

/-- Zero-error support relation `S(x, y₁, y₂)` of a two-receiver DMBC decoded from `code : ℕ`.
    To ensure every input `x` has at least one reachable output, `(0, 0)` is always reachable
    when no bit is set for `x`. -/
def supportOfCode (kX kY₁ kY₂ code : ℕ) (x : Fin kX) (y₁ : Fin kY₁) (y₂ : Fin kY₂) : Prop :=
  let bit (a : Fin kX) (b : Fin kY₁) (c : Fin kY₂) : Bool :=
    ((code / 2 ^ ((a.1 * kY₁ + b.1) * kY₂ + c.1)) % 2 == 1)
  bit x y₁ y₂ = true ∨
    ((∀ b : Fin kY₁, ∀ c : Fin kY₂, bit x b c = false) ∧ y₁.1 = 0 ∧ y₂.1 = 0)

/-- Zero-error adaptive feedback code of blocklength `n` and message sizes `(M₁, M₂)`
    for a two-receiver DMBC with support relation `S`. -/
def IsZeroErrorBCFeedbackCode {kX kY₁ kY₂ : ℕ}
    (S : Fin kX → Fin kY₁ → Fin kY₂ → Prop) (n M₁ M₂ : ℕ)
    (enc : ∀ i : Fin n, Fin M₁ → Fin M₂ → (Fin i.1 → Fin kY₁ × Fin kY₂) → Fin kX)
    (dec₁ : (Fin n → Fin kY₁) → Fin M₁)
    (dec₂ : (Fin n → Fin kY₂) → Fin M₂) : Prop :=
  ∀ (m₁ : Fin M₁) (m₂ : Fin M₂) (y : Fin n → Fin kY₁ × Fin kY₂),
    (∀ i : Fin n,
      S (enc i m₁ m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i).1 (y i).2) →
    dec₁ (fun i => (y i).1) = m₁ ∧ dec₂ (fun i => (y i).2) = m₂

/-- Zero-error feedback sum capacity `C_{0,f}^{sum}(S)` of a two-receiver DMBC support `S`. -/
noncomputable def zeroErrorBCFeedbackSumCap {kX kY₁ kY₂ : ℕ}
    (S : Fin kX → Fin kY₁ → Fin kY₂ → Prop) : ℝ :=
  sSup { r : ℝ | ∃ (n M₁ M₂ : ℕ)
    (enc : ∀ i : Fin n, Fin M₁ → Fin M₂ → (Fin i.1 → Fin kY₁ × Fin kY₂) → Fin kX)
    (dec₁ : (Fin n → Fin kY₁) → Fin M₁)
    (dec₂ : (Fin n → Fin kY₂) → Fin M₂),
    0 < n ∧ 0 < M₁ ∧ 0 < M₂ ∧
    IsZeroErrorBCFeedbackCode S n M₁ M₂ enc dec₁ dec₂ ∧
    r = (log2 (M₁ : ℝ) + log2 (M₂ : ℝ)) / (n : ℝ) }

/-- Initial register configuration loading `(kX, kY₁, kY₂, code, m)` into registers `0..4`. -/
def initRegs (numRegs kX kY₁ kY₂ code m : ℕ) : Fin numRegs → ℕ :=
  fun r =>
    if r.1 = 0 then kX
    else if r.1 = 1 then kY₁
    else if r.1 = 2 then kY₂
    else if r.1 = 3 then code
    else if r.1 = 4 then m
    else 0

/-- Zero-Error Broadcast Channel Feedback Sum Capacity (Körner–Orlitsky 1998;
    Shayevitz–Wigger 2013):
    While single-user zero-error feedback capacity has an exact computable single-letter
    formula (Shannon 1956), is the zero-error feedback sum capacity of a general two-receiver
    DMBC computable by a halting register machine to arbitrary precision `1 / m`? -/
def Statement : Prop :=
  ∃ (numRegs numInsts : ℕ) (hRegs : 5 ≤ numRegs) (start : Fin numInsts)
    (prog : Fin numInsts → RegInstr numRegs numInsts),
    ∀ (kX kY₁ kY₂ code m : ℕ), 0 < kX → 0 < kY₁ → 0 < kY₂ → 0 < m →
      ∃ t : ℕ,
        let final := regRun prog t (start, initRegs numRegs kX kY₁ kY₂ code m)
        let num := final.2 ⟨0, by omega⟩
        let den := final.2 ⟨1, by omega⟩
        prog final.1 = .halt ∧
        0 < den ∧
        |zeroErrorBCFeedbackSumCap (supportOfCode kX kY₁ kY₂ code) -
          (num : ℝ) / (den : ℝ)| ≤ 1 / (m : ℝ)

def problem : OpenProblem where
  id := "zero-error-broadcast-channel"
  title := "Computability and Characterization of the Zero-Error Broadcast Channel Feedback Capacity"
  category := .zeroError
  status := .open
  posedBy := "János Körner, Alon Orlitsky; Ofer Shayevitz, Michèle Wigger"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.ZeroErrorBroadcastChannel
