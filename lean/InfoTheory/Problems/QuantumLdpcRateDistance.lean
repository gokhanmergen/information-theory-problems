import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.QuantumLdpcRateDistance

/-- Hamming weight of a binary vector over `𝔽₂`. -/
def binWeight {n : ℕ} (v : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card

/-- Row space of an `m × n` binary matrix over `𝔽₂`. -/
def rowSpace {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2)
    { r : Fin n → ZMod 2 | ∃ i : Fin m, r = fun t : Fin n => H i t }

/-- A `w`-LDPC CSS quantum code of blocklength `n`, logical dimension at least `k`,
    and CSS minimum distance at least `d`. -/
def ExistsQLDPCCSSCode (n k d w : ℕ) : Prop :=
  ∃ (mX mZ : ℕ)
    (Hx : Matrix (Fin mX) (Fin n) (ZMod 2))
    (Hz : Matrix (Fin mZ) (Fin n) (ZMod 2)),
    -- CSS commutativity: Hx · Hzᵀ = 0
    (∀ (i : Fin mX) (j : Fin mZ), ∑ t : Fin n, Hx i t * Hz j t = 0) ∧
    -- LDPC row and column weight bounds ≤ w
    (∀ i : Fin mX, binWeight (fun t : Fin n => Hx i t) ≤ w) ∧
    (∀ t : Fin n, binWeight (fun i : Fin mX => Hx i t) ≤ w) ∧
    (∀ j : Fin mZ, binWeight (fun t : Fin n => Hz j t) ≤ w) ∧
    (∀ t : Fin n, binWeight (fun j : Fin mZ => Hz j t) ≤ w) ∧
    -- Logical qubit count k ≤ n - rank(Hx) - rank(Hz)
    k + Module.finrank (ZMod 2) (rowSpace Hx) + Module.finrank (ZMod 2) (rowSpace Hz) ≤ n ∧
    -- Z-distance ≥ d: every v ∈ ker(Hx) \ rowSpace(Hz) has weight ≥ d
    (∀ v : Fin n → ZMod 2,
      (∀ i : Fin mX, ∑ t : Fin n, Hx i t * v t = 0) →
      v ∉ rowSpace Hz → d ≤ binWeight v) ∧
    -- X-distance ≥ d: every v ∈ ker(Hz) \ rowSpace(Hx) has weight ≥ d
    (∀ v : Fin n → ZMod 2,
      (∀ j : Fin mZ, ∑ t : Fin n, Hz j t * v t = 0) →
      v ∉ rowSpace Hx → d ≤ binWeight v)

/-- Open problem: Can constant-check-weight quantum LDPC (CSS) codes achieve the CSS
    Gilbert–Varshamov rate–distance tradeoff `R = 1 - 2 h(δ)` for every `δ ∈ (0, h⁻¹(1/2))`? -/
def Statement : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ < 1 / 2 → 0 < 1 - 2 * binaryEntropy δ → 0 < ε →
    ∃ w : ℕ, ∀ N : ℕ, ∃ (n k d : ℕ), N ≤ n ∧ 0 < n ∧
      (1 - 2 * binaryEntropy δ - ε) * (n : ℝ) ≤ (k : ℝ) ∧
      δ * (n : ℝ) ≤ (d : ℝ) ∧
      ExistsQLDPCCSSCode n k d w

def problem : OpenProblem where
  id := "quantum-ldpc-rate-distance"
  title := "Optimal Rate–Distance Tradeoff for Constant-Weight Quantum LDPC Codes"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "Pavel Panteleev and Gleb Kalachev; Anthony Leverrier and Gilles Zémor"
  posedYear := 2022
  statement := Statement

end InfoTheory.Problems.QuantumLdpcRateDistance
