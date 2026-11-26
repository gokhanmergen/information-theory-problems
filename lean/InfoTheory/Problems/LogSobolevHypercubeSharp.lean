import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.LogSobolevHypercubeSharp

/-- Parity character `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}` on `{0,1}^n`. -/
def parityChar {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, if x i then (-1 : ℝ) else 1

/-- Walsh–Fourier coefficient `f̂(S) = 2^{-n} ∑_x f(x) χ_S(x)` for a `±1`-valued Boolean
    function encoded as `f : (Fin n → Bool) → Bool`. -/
noncomputable def fourierCoeff (n : ℕ) (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ℝ :=
  ((1 : ℝ) / ((2 : ℝ) ^ n)) *
    ∑ x : Fin n → Bool, (if f x then (1 : ℝ) else -1) * parityChar S x

/-- Fourier spectral entropy `H(f̂²) = ∑_S -f̂(S)² log₂(f̂(S)²)` in bits. -/
noncomputable def fourierEntropy (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S : Finset (Fin n), negPLogP ((fourierCoeff n f S) ^ 2)

/-- Total influence `I(f) = ∑_S |S| · f̂(S)²` of a Boolean function on `{0,1}^n`. -/
noncomputable def totalInfluence (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * (fourierCoeff n f S) ^ 2

/-- Fourier Entropy–Influence Conjecture (Friedgut–Kalai 1996; connected to Talagrand's
    sharp hypercube log-Sobolev and variance-influence inequalities): there exists a
    universal constant `C > 0` such that `H(f̂²) ≤ C · I(f)` for every `n` and every
    Boolean function `f : {0,1}^n → {-1, 1}`. -/
def Statement : Prop :=
  ∃ (C : ℝ), 0 < C ∧
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      fourierEntropy n f ≤ C * totalInfluence n f

def problem : OpenProblem where
  id := "log-sobolev-hypercube-sharp"
  title := "The Fourier Entropy–Influence Conjecture on the Boolean Hypercube"
  category := .entropyInequalities
  status := .open
  posedBy := "Michel Talagrand; Ehud Friedgut and Gil Kalai"
  posedYear := 1996
  statement := Statement

end InfoTheory.Problems.LogSobolevHypercubeSharp
