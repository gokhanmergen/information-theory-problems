import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.UniversalLossyRedundancy

/-- Hamming distortion on `Fin m`: `0` if `x = y`, `1` otherwise. -/
def hammingDist (m : ℕ) : Distortion (Fin m) (Fin m) where
  dist := fun x y => if x = y then 0 else 1
  nonneg := fun x y => by split_ifs <;> norm_num

/-- A variable-length prefix-free `d`-semifaithful block code of blocklength `n` and distortion
    threshold `D`: Kraft's inequality holds for the integer codeword lengths `len`, and every
    sequence `x : Fin n → Fin m` is reconstructed within average distortion `D`. -/
def IsDSemifaithfulCode (m : ℕ) (d : Distortion (Fin m) (Fin m)) (D : ℝ) (n M : ℕ)
    (enc : (Fin n → Fin m) → Fin M) (dec : Fin M → (Fin n → Fin m)) (len : Fin M → ℕ) : Prop :=
  0 < n ∧ 0 < M ∧
  (∑ c : Fin M, (2 : ℝ) ^ (-(len c : ℝ))) ≤ 1 ∧
  ∀ x : Fin n → Fin m,
    ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, d.dist (x i) (dec (enc x) i) ≤ D

/-- Expected per-symbol codeword length of a block code under an i.i.d. source `P`. -/
noncomputable def expectedRate {m : ℕ} (P : ProbDist (Fin m)) (n M : ℕ)
    (enc : (Fin n → Fin m) → Fin M) (len : Fin M → ℕ) : ℝ :=
  (∑ x : Fin n → Fin m, (∏ i : Fin n, P.pmf (x i)) * (len (enc x) : ℝ)) / (n : ℝ)

/-- Minimax universal redundancy `R_n^{univ}(m, d, D)` over all i.i.d. distributions on `Fin m`. -/
noncomputable def minimaxLossyRedundancy (m : ℕ) (d : Distortion (Fin m) (Fin m))
    (D : ℝ) (n : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ (M : ℕ) (enc : (Fin n → Fin m) → Fin M)
    (dec : Fin M → (Fin n → Fin m)) (len : Fin M → ℕ),
    IsDSemifaithfulCode m d D n M enc dec len ∧
    ∀ P : ProbDist (Fin m), expectedRate P n M enc len - rateDistortion P d D ≤ r }

/-- Minimax Redundancy Benchmark for Universal `d`-Semifaithful Lossy Source Coding
    (Yu–Speed 1993; Zhang–Yang–Wei 1997; Yang–Zhang 1999):
    for `d`-semifaithful lossy coding on an `m`-ary i.i.d. source under Hamming distortion
    `0 < D < 1 - 1/m`, the conjectured optimal minimax redundancy coefficient is `m / 2`
    (combining the `(m - 1) / 2` universal estimation penalty with the `1 / 2` known-source
    `d`-semifaithful covering penalty). Does `m / 2 · (log₂ n / n)` suffice asymptotically? -/
def Statement : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (D : ℝ), 0 < D → D < 1 - 1 / (m : ℝ) →
    ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ((n : ℝ) / log2 (n : ℝ)) * minimaxLossyRedundancy m (hammingDist m) D n ≤
        (m : ℝ) / 2 + ε

def problem : OpenProblem where
  id := "universal-lossy-redundancy"
  title := "Exact Minimax Redundancy Constant for Universal d-Semifaithful Lossy Source Coding"
  category := .sourceCoding
  status := .open
  posedBy := "Bin Yu, T. P. Speed; Zhen Zhang, En-Hui Yang, Victor K. Wei"
  posedYear := 1993
  statement := Statement

end InfoTheory.Problems.UniversalLossyRedundancy
