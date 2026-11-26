import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ExplicitListDecodableBinary

/-- A uniform deterministic single-tape Turing machine over `{blank, false, true}`
    (`Option Bool`, where `none` is the blank delimiter) with halt state `0`. -/
structure UniformTM where
  numStates : ℕ
  hpos : 1 < numStates
  trans : Fin numStates → Option Bool → Fin numStates × Option Bool × Bool

/-- Execution configuration `(state, head, tape)` of a Turing machine. -/
structure TMState (M : UniformTM) where
  state : Fin M.numStates
  head : ℤ
  tape : ℤ → Option Bool

/-- Single transition step of `M` (fixed point at halt state `0`). -/
def tmStep (M : UniformTM) (cfg : TMState M) : TMState M :=
  if cfg.state.1 = 0 then cfg
  else
    let res := M.trans cfg.state (cfg.tape cfg.head)
    let newTape : ℤ → Option Bool := fun p => if p = cfg.head then res.2.1 else cfg.tape p
    let newHead : ℤ := if res.2.2 then cfg.head + 1 else cfg.head - 1
    ⟨res.1, newHead, newTape⟩

/-- Run `M` for `T` steps from an initial binary input tape `inp : Fin inLen → Bool`
    delimited by blank symbols (`none`) outside `[0, inLen)`. -/
def tmRunOnBits (M : UniformTM) {inLen : ℕ} (inp : Fin inLen → Bool) (T : ℕ) : TMState M :=
  let init : TMState M :=
    ⟨⟨1, M.hpos⟩, 0, fun p =>
      if _h0 : 0 ≤ p then
        if hlt : p.toNat < inLen then some (inp ⟨p.toNat, hlt⟩) else none
      else none⟩
  Nat.rec init (fun _ c => tmStep M c) T

/-- Read `outLen` bits from tape positions `0 .. outLen - 1` (treating blank as `false`). -/
def readTapeBits (M : UniformTM) (cfg : TMState M) (outLen : ℕ) : Fin outLen → Bool :=
  fun i => (cfg.tape (i.1 : ℤ)).getD false

/-- Extract the `ℓ`-th candidate `k`-bit message from a flattened `L * k`-bit output. -/
def extractListItem {L k : ℕ} (out : Fin (L * k) → Bool) (ℓ : Fin L) : Fin k → Bool :=
  fun j => out ⟨ℓ.1 * k + j.1, by
    calc ℓ.1 * k + j.1 < ℓ.1 * k + k := Nat.add_lt_add_left j.2 _
      _ = (ℓ.1 + 1) * k := by ring
      _ ≤ L * k := Nat.mul_le_mul_right k ℓ.2⟩

/-- Explicit Uniform Polynomial-Time List-Decodable Binary Codes Achieving Capacity
    (Guruswami–Sudan 2000; Kopparty–Ron-Zewi–Saraf–Wootters):
    for every `p ∈ (0, 1/2)` and `ε > 0`, do there exist a constant list size `L` and
    **uniform** polynomial-time Turing machines `(E, D)` (independent of blocklength `n`)
    encoding `k = ⌊(1 - h(p) - ε) n⌋` bits into `n` bits and list-decoding within
    Hamming radius `p n`? -/
def Statement : Prop :=
  ∀ (p ε : ℝ), 0 < p → p < 1 / 2 → 0 < ε → ε < 1 - binaryEntropy p →
    ∃ (L c d N₀ : ℕ) (E D : UniformTM), 0 < L ∧ 0 < c ∧
      ∀ n : ℕ, N₀ ≤ n →
        let k : ℕ := Nat.floor ((1 - binaryEntropy p - ε) * (n : ℝ))
        let T : ℕ := c * n ^ d
        let enc (m : Fin k → Bool) : Fin n → Bool := readTapeBits E (tmRunOnBits E m T) n
        let dec (y : Fin n → Bool) : Fin (L * k) → Bool := readTapeBits D (tmRunOnBits D y T) (L * k)
        (∀ m : Fin k → Bool, (tmRunOnBits E m T).state.1 = 0) ∧
        (∀ y : Fin n → Bool, (tmRunOnBits D y T).state.1 = 0) ∧
        Function.Injective enc ∧
        ∀ (m : Fin k → Bool) (y : Fin n → Bool),
          (hammingDistVec (enc m) y : ℝ) ≤ p * (n : ℝ) →
          ∃ ℓ : Fin L, extractListItem (dec y) ℓ = m

def problem : OpenProblem where
  id := "explicit-list-decodable-binary"
  title := "Explicit Polynomial-Time List-Decodable Binary Codes Achieving Capacity"
  category := .codingTheory
  status := .open
  posedBy := "Venkatesan Guruswami and Madhu Sudan"
  posedYear := 2000
  statement := Statement

end InfoTheory.Problems.ExplicitListDecodableBinary
