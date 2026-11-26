import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.IndexCodingSingleLetter

/-- Deterministic single-tape Turing machine over `{false, true}` with halt state `0`. -/
structure TuringMachine where
  numStates : ℕ
  hpos : 1 < numStates
  trans : Fin numStates → Bool → Fin numStates × Bool × Bool

/-- Configuration `(state, head, tape)` of a Turing machine. -/
structure TMConfig (M : TuringMachine) where
  state : Fin M.numStates
  head : ℤ
  tape : ℤ → Bool

/-- Single execution step of a Turing machine. -/
def tmStep (M : TuringMachine) (cfg : TMConfig M) : TMConfig M :=
  if cfg.state.1 = 0 then cfg
  else
    let res := M.trans cfg.state (cfg.tape cfg.head)
    let newTape : ℤ → Bool := fun p => if p = cfg.head then res.2.1 else cfg.tape p
    let newHead : ℤ := if res.2.2 then cfg.head + 1 else cfg.head - 1
    ⟨res.1, newHead, newTape⟩

/-- Run a Turing machine for `steps` steps. -/
def tmRun (M : TuringMachine) (steps : ℕ) (cfg : TMConfig M) : TMConfig M :=
  Nat.rec cfg (fun _ c => tmStep M c) steps

/-- Predicate: `M` halts on input bitstring `inp` with output bit `b` at tape cell `0`. -/
def tmOutputs (M : TuringMachine) (inp : List Bool) (b : Bool) : Prop :=
  let init : TMConfig M :=
    ⟨⟨1, M.hpos⟩, 0, fun p => if 0 ≤ p then inp.getD p.toNat false else false⟩
  ∃ steps : ℕ, (tmRun M steps init).state.1 = 0 ∧ (tmRun M steps init).tape 0 = b

/-- Prefix-free unary encoding of a natural number. -/
def encNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Canonical binary encoding of an `n`-vertex side-information graph and rational threshold
    query `(p, q, prec)`. -/
def encodeIndexQuery (n : ℕ) (adj : Fin n → Fin n → Bool) (p q prec : ℕ) : List Bool :=
  encNat n ++
  (List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => adj i j).flatten ++
  encNat p ++ encNat q ++ encNat prec

/-- Open problem: Is the optimal vector index coding broadcast rate `β(G)` algorithmically
    computable (approximable to within arbitrary rational precision `1 / prec` by a halting
    Turing machine)? -/
def Statement : Prop :=
  ∃ M : TuringMachine,
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (p q prec : ℕ),
      0 < n → 0 < q → 0 < prec →
      let inst : IndexCodingInstance n := ⟨fun i j => i ≠ j ∧ adj i j = true, fun _ h => h.1 rfl⟩
      let inp := encodeIndexQuery n adj p q prec
      (∃ b : Bool, tmOutputs M inp b) ∧
      (indexCodingBroadcastRate inst ≤ (p : ℝ) / (q : ℝ) - (1 : ℝ) / (prec : ℝ) →
        tmOutputs M inp true) ∧
      ((p : ℝ) / (q : ℝ) + (1 : ℝ) / (prec : ℝ) ≤ indexCodingBroadcastRate inst →
        tmOutputs M inp false)

def problem : OpenProblem where
  id := "index-coding-single-letter"
  title := "Single-Letter Characterization and Computability of the Index Coding Broadcast Rate"
  category := .networkCoding
  status := .open
  posedBy := "Yitzhak Birk and Tomer Kol; Ziv Bar-Yossef, Yitzhak Birk, T. S. Jayram, and Tomer Kol"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.IndexCodingSingleLetter
