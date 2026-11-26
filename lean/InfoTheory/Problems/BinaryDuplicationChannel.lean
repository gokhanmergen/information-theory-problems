import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BinaryDuplicationChannel

/-- Elementary self-contained binomial coefficient `C(n, k)`. -/
def chooseNat : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseNat n k + chooseNat n (k + 1)

/-- Binomial coefficient cast to `ℝ`. -/
def binomR (n k : ℕ) : ℝ := (chooseNat n k : ℝ)

/-- Negative binomial transition probability `W_p(s | r) = C(s - 1, r - 1) (1 - p)^r p^(s - r)`
    for an input run of length `r + 1 ≥ 1` producing an output run of length `s + 1 ≥ 1`
    over the geometric binary duplication channel with duplication parameter `p ∈ (0, 1)`. -/
noncomputable def dupRunTrans (p : ℝ) (r s : ℕ) : ℝ :=
  if r ≤ s then binomR s r * (1 - p) ^ (r + 1) * p ^ (s - r) else 0

/-- A probability distribution on positive integers `ℤ_≥1` (indexed by `r : ℕ` representing
    run length `r + 1`) with finite mean. -/
structure PosIntDist where
  pmf : ℕ → ℝ
  nonneg : ∀ r : ℕ, 0 ≤ pmf r
  summable : Summable pmf
  tsum_one : ∑' r : ℕ, pmf r = 1
  mean_summable : Summable (fun r : ℕ => ((r + 1 : ℕ) : ℝ) * pmf r)

/-- Expected run length `E[R]` for a run-length distribution `P` on `ℤ_≥1`. -/
noncomputable def meanRunLen (P : PosIntDist) : ℝ :=
  ∑' r : ℕ, ((r + 1 : ℕ) : ℝ) * P.pmf r

/-- Mutual information per input bit `I(R; S) / E[R]` (in bits) of a run-length input
    distribution `P` over the geometric binary duplication channel with parameter `p`. -/
noncomputable def dupRate (p : ℝ) (P : PosIntDist) : ℝ :=
  let ps (s : ℕ) : ℝ := ∑' r : ℕ, P.pmf r * dupRunTrans p r s
  let hS : ℝ := ∑' s : ℕ, negPLogP (ps s)
  let hSgivenR : ℝ := ∑' r : ℕ, P.pmf r * ∑' s : ℕ, negPLogP (dupRunTrans p r s)
  (hS - hSgivenR) / meanRunLen P

/-- Capacity `C_dup(p) = sup_P I(R; S) / E[R]` of the geometric binary duplication channel
    (Mitzenmacher 2008). -/
noncomputable def geometricDuplicationCapacity (p : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ P : PosIntDist, r = dupRate p P }

/-- Convexity Conjecture for the Geometric Binary Duplication Channel Capacity
    (Mitzenmacher 2008; Kirshner–Farnoud): is the capacity `p ↦ C_dup(p)` convex on `(0, 1)`?
    (Note: the naive finite-support conjecture for the optimal run-length distribution can be
    refuted by perturbation; determining `C_dup(p)` and whether `C_dup` is convex remain open.) -/
def Statement : Prop :=
  ∀ (p₁ p₂ t : ℝ),
    0 < p₁ → p₁ < 1 → 0 < p₂ → p₂ < 1 → 0 ≤ t → t ≤ 1 →
    geometricDuplicationCapacity (t * p₁ + (1 - t) * p₂) ≤
      t * geometricDuplicationCapacity p₁ + (1 - t) * geometricDuplicationCapacity p₂

def problem : OpenProblem where
  id := "binary-duplication-channel"
  title := "Capacity and Optimal Input Support of the Geometric Binary Duplication Channel"
  category := .channelCapacity
  status := .open
  posedBy := "Michael Mitzenmacher; Noam Kirshner and Farzad Farnoud"
  posedYear := 2008
  statement := Statement

end InfoTheory.Problems.BinaryDuplicationChannel
