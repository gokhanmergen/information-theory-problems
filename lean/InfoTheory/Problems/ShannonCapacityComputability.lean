import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ShannonCapacityComputability

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

/-- Simple graph on `Fin n` decoded from a bitmask `code : ℕ` encoding its adjacency matrix
    (symmetrized, with self-loops ignored). Every finite simple graph on `Fin n` arises this way. -/
def graphOfCode (n code : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧
    ((code / 2 ^ (i.1 * n + j.1)) % 2 = 1 ∨ (code / 2 ^ (j.1 * n + i.1)) % 2 = 1)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Initial register configuration loading `(n, code, m)` into registers `0, 1, 2`. -/
def initRegs (numRegs n code m : ℕ) : Fin numRegs → ℕ :=
  fun r =>
    if r.1 = 0 then n
    else if r.1 = 1 then code
    else if r.1 = 2 then m
    else 0

/-- Computability of the Shannon Capacity of Finite Graphs (Shannon 1956; Alon–Lubetzky 2006):
    does there exist a halting register machine (equivalently, Turing machine) that, given
    any finite simple graph `G` on `Fin n` (`0 < n`) and positive precision parameter `m`,
    outputs a rational `num / den` (`0 < den`) within `1 / m` of `shannonCapacity G`? -/
def Statement : Prop :=
  ∃ (numRegs numInsts : ℕ) (hRegs : 3 ≤ numRegs) (start : Fin numInsts)
    (prog : Fin numInsts → RegInstr numRegs numInsts),
    ∀ (n code m : ℕ), 0 < n → 0 < m →
      ∃ t : ℕ,
        let final := regRun prog t (start, initRegs numRegs n code m)
        let num := final.2 ⟨0, by omega⟩
        let den := final.2 ⟨1, by omega⟩
        prog final.1 = .halt ∧
        0 < den ∧
        |shannonCapacity (graphOfCode n code) - (num : ℝ) / (den : ℝ)| ≤ 1 / (m : ℝ)

def problem : OpenProblem where
  id := "shannon-capacity-computability"
  title := "Computability of the Shannon Capacity of Finite Graphs"
  category := .zeroError
  status := .open
  posedBy := "Claude Shannon; Noga Alon, Eyal Lubetzky"
  posedYear := 1956
  statement := Statement

end InfoTheory.Problems.ShannonCapacityComputability
