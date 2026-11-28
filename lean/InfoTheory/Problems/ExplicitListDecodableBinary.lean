import InfoTheory.Core

/-!
# Explicit polynomial-time list-decodable binary codes at list-decoding capacity

`Statement`: for every `p ∈ (0, 1/2)` and `ε ∈ (0, 1 - h(p))` there are a rational rate
`a / b ≥ 1 - h(p) - ε`, a constant list size `L`, and uniform polynomial-time Turing machines
`E, D` such that, for all large `m`, `E` maps `k = a m` bits injectively to `n = b m` bits and
`D` list-decodes every Hamming ball of radius `p n` into a list of `L` messages.

**Statement-fix (2026-11-27).** The previous statement fixed the message length to
`k = ⌊(1 - h(p) - ε) n⌋` for *every* real `p, ε` and every `n ≥ N₀`. Two artefacts of that
encoding changed the question:
1. The decoder `D` lays its list out in `k`-bit blocks, so it must compute `k` from `n`; for a
   non-computable real `1 - h(p) - ε` (all but countably many `ε`) no Turing machine computes
   `n ↦ ⌊(1 - h(p) - ε) n⌋`, so the formal statement could fail for reasons of computability
   rather than coding theory.
2. The encoder `E` sees only `k`, but several `n` share the same `k`; it had to emit one tape
   whose length-`n` prefixes work for all of them.
The literature asks for an explicit family of rate `≥ 1 - h(p) - ε` (Guruswami–Rudra 2008,
§1; Guruswami, "Algorithmic results in list decoding", 2006), and families defined on an
infinite arithmetic progression of lengths are the standard notion of an explicit family.
The fixed version lets the construction choose a rational rate `a / b ≥ 1 - h(p) - ε` and uses
lengths `n = b m`, `k = a m`, so `E` and `D` can compute `n` from `k` and `k` from `n`. It
remains a capacity statement: by the list-decoding converse (Elias 1991) a constant list size
forces `a / b ≤ 1 - h(p) + o(1)`, and random codes achieve every rate `< 1 - h(p)`
non-explicitly; what is open is an explicit, polynomial-time list-decodable family.
-/

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
    (Guruswami–Sudan 2000; Guruswami–Rudra 2008):
    for every `p ∈ (0, 1/2)` and `ε ∈ (0, 1 - h(p))`, are there a rational rate
    `a / b ≥ 1 - h(p) - ε`, a constant list size `L` and **uniform** polynomial-time Turing
    machines `(E, D)` such that for all large `m`, `E` encodes `k = a m` bits into `n = b m`
    bits injectively and `D` outputs `L` candidates (as `L` consecutive `k`-bit blocks)
    containing every message whose codeword is within Hamming distance `p n` of the input?
    (Statement-fix 2026-11-27: rational rate and lengths `n = b m`; see the module docstring.) -/
def Statement : Prop :=
  ∀ (p ε : ℝ), 0 < p → p < 1 / 2 → 0 < ε → ε < 1 - binaryEntropy p →
    ∃ (a b L c d N₀ : ℕ) (E D : UniformTM), 0 < b ∧ 0 < L ∧ 0 < c ∧
      1 - binaryEntropy p - ε ≤ (a : ℝ) / (b : ℝ) ∧
      ∀ m : ℕ, N₀ ≤ m →
        let n : ℕ := b * m
        let k : ℕ := a * m
        let T : ℕ := c * n ^ d
        let enc (msg : Fin k → Bool) : Fin n → Bool := readTapeBits E (tmRunOnBits E msg T) n
        let dec (y : Fin n → Bool) : Fin (L * k) → Bool :=
          readTapeBits D (tmRunOnBits D y T) (L * k)
        (∀ msg : Fin k → Bool, (tmRunOnBits E msg T).state.1 = 0) ∧
        (∀ y : Fin n → Bool, (tmRunOnBits D y T).state.1 = 0) ∧
        Function.Injective enc ∧
        ∀ (msg : Fin k → Bool) (y : Fin n → Bool),
          (hammingDistVec (enc msg) y : ℝ) ≤ p * (n : ℝ) →
          ∃ ℓ : Fin L, extractListItem (dec y) ℓ = msg

def problem : OpenProblem where
  id := "explicit-list-decodable-binary"
  title := "Explicit Polynomial-Time List-Decodable Binary Codes Achieving Capacity"
  category := .codingTheory
  status := .open
  posedBy := "Venkatesan Guruswami and Madhu Sudan"
  posedYear := 2000
  statement := Statement

end InfoTheory.Problems.ExplicitListDecodableBinary
