import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.NetworkCodingCapacityDecidability

/-- A finite directed acyclic multi-source network with `V` vertices (edges `u → v` active iff
    `u.1 < v.1 ∧ adj u v = true`), `K` sources, and sink demand matrix `dem`. -/
structure MultiSourceDAG (V K : ℕ) where
  adj : Fin V → Fin V → Bool
  src : Fin K → Fin V
  dem : Fin V → Fin K → Bool

/-- Asymptotic (vanishing-error) symmetric rate achievability over a multi-source DAG network:
    for every `ε > 0`, for all sufficiently large blocklengths `t ≥ N`, there exists a valid
    local network code at rate `R` with block error at most `ε`. -/
def IsAsympAchievable {V K : ℕ} (net : MultiSourceDAG V K) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ (N : ℕ), 0 < N ∧ ∀ (t : ℕ), N ≤ t →
      let M : ℕ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((t : ℝ) * R)))
      ∃ (edgeVal : (Fin K → Fin M) → Fin V → Fin V → Fin (2 ^ t))
        (dec : ∀ (v : Fin V) (i : Fin K), (Fin V → Fin (2 ^ t)) → (Fin K → Fin M) → Fin M),
        (∀ msg u v, ¬ (u.1 < v.1 ∧ net.adj u v = true) → (edgeVal msg u v).1 = 0) ∧
        (∀ msg₁ msg₂ u,
          (∀ w : Fin V, edgeVal msg₁ w u = edgeVal msg₂ w u) →
          (∀ i : Fin K, net.src i = u → msg₁ i = msg₂ i) →
          ∀ v : Fin V, edgeVal msg₁ u v = edgeVal msg₂ u v) ∧
        (∀ v i inc msg₁ msg₂,
          (∀ j : Fin K, net.src j = v → msg₁ j = msg₂ j) →
          dec v i inc msg₁ = dec v i inc msg₂) ∧
        let errCount : ℕ :=
          (Finset.univ.filter (fun msg : Fin K → Fin M =>
            ∃ (v : Fin V) (i : Fin K), net.dem v i = true ∧
              dec v i (fun w : Fin V => edgeVal msg w v) msg ≠ msg i)).card
        (errCount : ℝ) / ((M ^ K : ℕ) : ℝ) ≤ ε

/-- Asymptotic symmetric network coding capacity `C_asymp(N)`. -/
noncomputable def dagAsympCapacity {V K : ℕ} (net : MultiSourceDAG V K) : ℝ :=
  sSup { R : ℝ | IsAsympAchievable net R }

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

/-- Single execution step of a Turing machine (no-op once in halt state `0`). -/
def tmStep (M : TuringMachine) (cfg : TMConfig M) : TMConfig M :=
  if cfg.state.1 = 0 then cfg
  else
    let res := M.trans cfg.state (cfg.tape cfg.head)
    let newTape : ℤ → Bool := fun p => if p = cfg.head then res.2.1 else cfg.tape p
    let newHead : ℤ := if res.2.2 then cfg.head + 1 else cfg.head - 1
    ⟨res.1, newHead, newTape⟩

/-- Run a Turing machine for `steps` steps from initial configuration `cfg`. -/
def tmRun (M : TuringMachine) (steps : ℕ) (cfg : TMConfig M) : TMConfig M :=
  Nat.rec cfg (fun _ c => tmStep M c) steps

/-- Predicate: `M` halts on binary input `inp` with output bit `b` at tape cell `0`. -/
def tmOutputs (M : TuringMachine) (inp : List Bool) (b : Bool) : Prop :=
  let init : TMConfig M :=
    ⟨⟨1, M.hpos⟩, 0, fun p => if 0 ≤ p then inp.getD p.toNat false else false⟩
  ∃ steps : ℕ, (tmRun M steps init).state.1 = 0 ∧ (tmRun M steps init).tape 0 = b

/-- Prefix-free unary encoding of a natural number as a bit list. -/
def encNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Canonical binary encoding of a multi-source DAG network and rational query `(p, q, prec)`. -/
def encodeQuery {V K : ℕ} (net : MultiSourceDAG V K) (p q prec : ℕ) : List Bool :=
  encNat V ++ encNat K ++
  (List.ofFn fun u : Fin V => List.ofFn fun v : Fin V => net.adj u v).flatten ++
  (List.ofFn fun i : Fin K => encNat (net.src i).1).flatten ++
  (List.ofFn fun v : Fin V => List.ofFn fun i : Fin K => net.dem v i).flatten ++
  encNat p ++ encNat q ++ encNat prec

/-- Open problem: Is the asymptotic multi-source network coding capacity `C_asymp(N)`
    algorithmically computable (approximable to within arbitrary rational tolerance `1 / prec`
    by a halting Turing machine)? -/
def Statement : Prop :=
  ∃ M : TuringMachine,
    ∀ (V K : ℕ) (net : MultiSourceDAG V K) (p q prec : ℕ),
      0 < q → 0 < prec →
      let inp := encodeQuery net p q prec
      (∃ b : Bool, tmOutputs M inp b) ∧
      ((p : ℝ) / (q : ℝ) + (1 : ℝ) / (prec : ℝ) ≤ dagAsympCapacity net →
        tmOutputs M inp true) ∧
      (dagAsympCapacity net ≤ (p : ℝ) / (q : ℝ) - (1 : ℝ) / (prec : ℝ) →
        tmOutputs M inp false)

def problem : OpenProblem where
  id := "network-coding-capacity-decidability"
  title := "Decidability of the Asymptotic Multi-Source Network Coding Capacity Region"
  category := .networkCoding
  status := .partiallySolved
  posedBy := "X. Yan, Raymond W. Yeung, and Zhen Zhang"
  posedYear := 2007
  statement := Statement

end InfoTheory.Problems.NetworkCodingCapacityDecidability
