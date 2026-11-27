import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CorrelatedSourcesOverMac

/-! ### Lossless transmission of a 2-DMS over a DM-MAC -/

/-- Error probability of a lossless joint source–channel code that maps `k` symbols of the
    i.i.d. source `(U, V) ~ P` onto `n` uses of the DM-MAC `W`: encoder 1 sees only `Uᵏ`,
    encoder 2 sees only `Vᵏ`, and the decoder must reproduce `(Uᵏ, Vᵏ)` exactly. -/
noncomputable def jsccError {U V X₁ X₂ Y : Type*}
    [Fintype U] [Fintype V] [Fintype X₁] [Fintype X₂] [Fintype Y]
    [DecidableEq U] [DecidableEq V]
    (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y) (k n : ℕ)
    (enc₁ : (Fin k → U) → Fin n → X₁) (enc₂ : (Fin k → V) → Fin n → X₂)
    (dec : (Fin n → Y) → (Fin k → U) × (Fin k → V)) : ℝ :=
  ∑ s : Fin k → U × V, (∏ i : Fin k, P.pmf (s i)) *
    ∑ y : Fin n → Y,
      if dec y ≠ (fun i => (s i).1, fun i => (s i).2) then
        (W.power n).trans
          (fun i => (enc₁ (fun j => (s j).1) i, enc₂ (fun j => (s j).2) i)) y
      else 0

/-- The source `P` is losslessly transmissible over `W` at `ρ ≥ 0` source symbols per channel
    use: for every `δ > 0` and all large `n` there are codes sending `⌊ρ n⌋` source symbols in
    `n` channel uses with error probability at most `δ`. (`ρ = 1` is the setting of
    Cover–El Gamal–Salehi 1980.) -/
def IsTransmissibleAtRatio {U V X₁ X₂ Y : Type*}
    [Fintype U] [Fintype V] [Fintype X₁] [Fintype X₂] [Fintype Y]
    [DecidableEq U] [DecidableEq V]
    (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧
  ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∃ (enc₁ : (Fin (Nat.floor (ρ * n)) → U) → Fin n → X₁)
      (enc₂ : (Fin (Nat.floor (ρ * n)) → V) → Fin n → X₂)
      (dec : (Fin n → Y) → (Fin (Nat.floor (ρ * n)) → U) × (Fin (Nat.floor (ρ * n)) → V)),
      jsccError P W (Nat.floor (ρ * n)) n enc₁ enc₂ dec ≤ δ

/-- The optimal source–channel rate `ρ*(P, W)`: supremum of the ratios (source symbols per
    channel use) at which `P` is losslessly transmissible over `W`. The source is transmissible
    with matched bandwidth (`ρ = 1`) if `ρ* > 1` and is not if `ρ* < 1`. -/
noncomputable def optimalTransmissionRatio {U V X₁ X₂ Y : Type*}
    [Fintype U] [Fintype V] [Fintype X₁] [Fintype X₂] [Fintype Y]
    [DecidableEq U] [DecidableEq V]
    (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y) : ℝ :=
  sSup { ρ : ℝ | IsTransmissibleAtRatio P W ρ }

/-! ### Rational instances -/

/-- Source pmf `P(u, v) = w(u, v) / ∑ w` from nonnegative integer weights (every rational pmf on
    `Fin a × Fin b` arises this way). -/
noncomputable def sourceOfWeights {a b : ℕ} (w : Fin a → Fin b → ℕ)
    (hw : 0 < ∑ u, ∑ t, w u t) : ProbDist (Fin a × Fin b) where
  pmf := fun z => (w z.1 z.2 : ℝ) / ∑ u, ∑ t, (w u t : ℝ)
  nonneg := fun z => div_nonneg (Nat.cast_nonneg _) (by positivity)
  sum_one := by
    have hpos : (0 : ℝ) < ∑ u, ∑ t, (w u t : ℝ) := by exact_mod_cast hw
    rw [← Finset.sum_div, Fintype.sum_prod_type]
    exact div_self hpos.ne'

/-- DM-MAC `W(y | x₁, x₂) = v(x₁, x₂, y) / ∑_{y'} v(x₁, x₂, y')` from nonnegative integer weights
    (every DM-MAC with rational transition probabilities arises this way). -/
noncomputable def macOfWeights {c d e : ℕ} (v : Fin c → Fin d → Fin e → ℕ)
    (hv : ∀ x₁ x₂, 0 < ∑ y, v x₁ x₂ y) : MACChannel (Fin c) (Fin d) (Fin e) where
  trans := fun x y => (v x.1 x.2 y : ℝ) / ∑ y', (v x.1 x.2 y' : ℝ)
  nonneg := fun x y => div_nonneg (Nat.cast_nonneg _) (by positivity)
  sum_one := fun x => by
    have hpos : (0 : ℝ) < ∑ y', (v x.1 x.2 y' : ℝ) := by exact_mod_cast hv x.1 x.2
    rw [← Finset.sum_div]
    exact div_self hpos.ne'

/-! ### Machine model (as in `InfoTheory.Problems.IndexCodingSingleLetter`) -/

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

/-- Canonical binary encoding of a rational source–MAC instance `(a, b, c, d, e, w, v)` and a
    rational threshold query `(p, q, prec)`. -/
def encodeQuery (a b c d e : ℕ) (w : Fin a → Fin b → ℕ) (v : Fin c → Fin d → Fin e → ℕ)
    (p q prec : ℕ) : List Bool :=
  encNat a ++ encNat b ++ encNat c ++ encNat d ++ encNat e ++
  (List.ofFn fun u : Fin a => (List.ofFn fun t : Fin b => encNat (w u t)).flatten).flatten ++
  (List.ofFn fun x₁ : Fin c => (List.ofFn fun x₂ : Fin d =>
    (List.ofFn fun y : Fin e => encNat (v x₁ x₂ y)).flatten).flatten).flatten ++
  encNat p ++ encNat q ++ encNat prec

/-- Lossless Transmission of Correlated Sources over a Multiple-Access Channel
    (Cover–El Gamal–Salehi 1980; Dueck 1981): no single-letter necessary and sufficient
    condition is known. Formal proxy: is the optimal source–channel rate `ρ*(P, W)`
    algorithmically computable from a rational description of the source `P` and the DM-MAC `W`,
    i.e. does a halting Turing machine answer every rational threshold query `ρ* ≶ p/q` with
    promise gap `1/prec`? Sources with all mass on one pair (where `ρ* = +∞`) are excluded. -/
def Statement : Prop :=
  ∃ M : TuringMachine,
    ∀ (a b c d e : ℕ) (w : Fin a → Fin b → ℕ) (v : Fin c → Fin d → Fin e → ℕ) (p q prec : ℕ)
      (hw : 0 < ∑ u, ∑ t, w u t) (hv : ∀ x₁ x₂, 0 < ∑ y, v x₁ x₂ y),
      0 < c → 0 < d → 0 < q → 0 < prec →
      (∀ u t, w u t < ∑ u', ∑ t', w u' t') →
      let ρ := optimalTransmissionRatio (sourceOfWeights w hw) (macOfWeights v hv)
      let inp := encodeQuery a b c d e w v p q prec
      (∃ bit : Bool, tmOutputs M inp bit) ∧
      (ρ ≤ (p : ℝ) / (q : ℝ) - (1 : ℝ) / (prec : ℝ) → tmOutputs M inp true) ∧
      ((p : ℝ) / (q : ℝ) + (1 : ℝ) / (prec : ℝ) ≤ ρ → tmOutputs M inp false)

def problem : OpenProblem where
  id := "correlated-sources-over-mac"
  title := "Lossless Transmission of Correlated Sources over a Multiple-Access Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas M. Cover, Abbas El Gamal, and Masoud Salehi"
  posedYear := 1980
  statement := Statement

end InfoTheory.Problems.CorrelatedSourcesOverMac
