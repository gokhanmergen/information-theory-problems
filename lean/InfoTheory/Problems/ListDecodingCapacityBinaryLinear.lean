import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ListDecodingCapacityBinaryLinear

/-- Existence of a binary linear `[n, k]_2` code that is `(p, L)`-list-decodable. -/
def ExistsBinaryLinearListDecodable (n k : ℕ) (p : ℝ) (L : ℕ) : Prop :=
  ∃ (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (C : Finset (Fin n → Bool)),
    Module.finrank (ZMod 2) V = k ∧
    (∀ c : Fin n → Bool, c ∈ C ↔ (fun i : Fin n => if c i then (1 : ZMod 2) else 0) ∈ V) ∧
    IsListDecodable n p L C

/-- Open problem: Is the random-linear-code list-size threshold `h(p) / ε` asymptotically
    optimal among all binary linear codes at rate `1 - h(p) - ε`? That is, for every
    `p ∈ (0, 1/2)` and every `c < h(p)`, for all sufficiently small `ε > 0` and large `n`,
    no binary linear code of rate at least `1 - h(p) - ε` is `(p, ⌊c / ε⌋)`-list-decodable. -/
def Statement : Prop :=
  ∀ (p c : ℝ), 0 < p → p < 1 / 2 → 0 < c → c < binaryEntropy p →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N : ℕ, ∀ (n k : ℕ), N ≤ n →
          (1 - binaryEntropy p - ε) * (n : ℝ) ≤ (k : ℝ) →
          ¬ ExistsBinaryLinearListDecodable n k p (Nat.floor (c / ε))

def problem : OpenProblem where
  id := "list-decoding-capacity-binary-linear"
  title := "Optimal List Size of Binary Linear Codes Approaching List-Decoding Capacity"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "Peter Elias; Venkatesan Guruswami, Johan Håstad, and Swastik Kopparty"
  posedYear := 1957
  statement := Statement

end InfoTheory.Problems.ListDecodingCapacityBinaryLinear
