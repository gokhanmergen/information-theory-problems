import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.EntropyRegionDecidability

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

/-- Subset of `Fin 4` decoded from a 4-bit integer mask `k ∈ {0, ..., 15}`. -/
def subsetOfMask (k : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun i : Fin 4 => (k / 2 ^ i.1) % 2 = 1)

/-- Initial register configuration loading a rational vector `v : Finset (Fin 4) → ℕ × ℕ`
    (numerator and positive denominator for each of the 16 subsets) into registers `0..31`. -/
def initRegs (numRegs : ℕ) (v : Finset (Fin 4) → ℕ × ℕ) : Fin numRegs → ℕ :=
  fun r =>
    if r.1 < 32 then
      if r.1 % 2 = 0 then (v (subsetOfMask (r.1 / 2))).1
      else (v (subsetOfMask (r.1 / 2))).2
    else 0

/-- Decidability of the 4-variable almost-entropic cone `cl(Γ*_4)` (Chan–Yeung; Matúš):
    does there exist a halting register machine (equivalently, Turing machine) that decides
    for every nonnegative rational vector `h : 2^[4] → ℚ_≥0` whether `h ∈ cl(Γ*_4)`? -/
def Statement : Prop :=
  ∃ (numRegs numInsts : ℕ) (hRegs : 32 ≤ numRegs) (start : Fin numInsts)
    (prog : Fin numInsts → RegInstr numRegs numInsts),
    ∀ (v : Finset (Fin 4) → ℕ × ℕ), (∀ S : Finset (Fin 4), 0 < (v S).2) →
      ∃ (t : ℕ),
        let final := regRun prog t (start, initRegs numRegs v)
        prog final.1 = .halt ∧
        (InAlmostEntropicCone 4 (fun S => ((v S).1 : ℝ) / ((v S).2 : ℝ)) ↔
          final.2 ⟨0, by omega⟩ ≠ 0)

def problem : OpenProblem where
  id := "entropy-region-decidability"
  title := "Decidability of Membership in the Four-Variable Almost-Entropic Cone"
  category := .entropyInequalities
  status := .open
  posedBy := "Terence H. Chan and Raymond W. Yeung; František Matúš"
  posedYear := 2002
  statement := Statement

end InfoTheory.Problems.EntropyRegionDecidability
