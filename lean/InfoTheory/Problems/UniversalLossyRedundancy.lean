import InfoTheory.Core

open scoped BigOperators

/-!
# Exact minimax redundancy constant for universal `d`-semifaithful lossy coding

**Statement-fix (2026-11-27).**  The previous frozen statement took the supremum over the
*whole* simplex `ProbDist (Fin m)` and asked for `(n / log₂ n) · R_n ≤ m/2 + ε`.  It was false:
the simplex contains zero-rate boundary sources such as `Bern(1/4)` at `D = 1/4`
(`R(P, D) = 0`, i.e. `D = D_max(P)`), where every `d`-semifaithful code has redundancy
`Ω(n^{-1/2})`; certified in `InfoTheory.Known.Certificates.UniversalLossyRedundancy`
(`fullSimplex_version_false`); see also Mahmood–Wagner, *Minimax rate-distortion*
(ISIT 2022; journal version), Cor. 5 and App. D, which show `Θ̃(n^{-1/2})` minimax
redundancy whenever the class reaches the zero-rate boundary.  All `O(log n / n)` results
(Yu–Speed 1993; Zhang–Yang–Wei 1997; Yang–Zhang) assume regularity conditions that hold on the
open set `{P : (m - 1) · minₓ P(x) > D}` (Hamming distortion: then
`R(P, D) = H(P) - h(D) - D log₂(m - 1)` and the optimal reproduction law has full support).
The source class is now the compact set `interiorClass m D δ` of sources with every letter
probability `≥ D/(m-1) + δ`; for `0 < δ < 1/m - D/(m-1)` it contains the uniform source in its
relative interior, and every compact subset of the regular region lies in some such class.

The question is now whether the pre-log limit **exists**. The old statement asked for the
constant `m/2`, which the `m = 2` interior lower bound `3/2` below contradicts, and the only
candidate constant `(m+1)/2` is backed by sketches that only an AI agent has reviewed (see the second
Statement-fix below). Known bounds:
* known source (`|S| = 1`): `½ · log n / n ≤ redundancy ≤ log n / n` (Zhang–Yang–Wei 1997;
  the lower bound "in most cases");
  `½` is exact for the uniform source (Sriramu–Wagner, arXiv:2601.11927, 2026);
* weakly universal (pointwise, "most" `P`): pre-log between `K/2` and `(K+2)/2`, `K = m` the
  reproduction alphabet size (Yang–Zhang, unpublished, as reported by Mahmood–Wagner);
* `m = 2`, minimax over an interval `[p₁, p₂] ⊂ (D, 1/2)`: lower bound `3/2`, so `m/2 = 1` is
  *not* the minimax constant; for general `m` a matching `(m+1)/2` upper/lower bound is claimed
  at sketch level (`attempts/universal-lossy-redundancy/2026-11-26-gemini-4-neon.md`,
  Claims 4–6; not in the refereed literature).
**Statement-fix 2 (2026-11-27, claude-known).** A same-day version froze the constant `(m+1)/2`.
No published source poses that value. It comes from the gemini-4-neon attempt, whose `m = 2`
lower bound was checked only by AI referees and whose general-`m` matching bounds are sketches.
Freezing it would make a disproof of an unrefereed guess count as a "resolution". The frozen
statement now asks whether the limit `lim (n / log₂ n) · R_n(m, D, δ)` **exists** (as a real)
for every interior class. That question is literature-robust: the refereed bounds give only
`Θ(log n / n)` with non-matching constants. `(m+1)/2 = (m-1)/2 + 1` (estimation penalty plus
the known-source covering penalty) is recorded in the `.md` as the conjectured value.
-/

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

/-- Minimax redundancy `inf_{codes} sup_{P ∈ S} ((1/n) 𝔼_P ℓ - R(P, D))` of `d`-semifaithful
    codes of blocklength `n` over a source class `S`.  (The defining set is nonempty — the
    fixed-length lossless code — and, for nonempty `S`, bounded below; see the certificate.) -/
noncomputable def minimaxLossyRedundancyOn (m : ℕ) (d : Distortion (Fin m) (Fin m))
    (D : ℝ) (S : Set (ProbDist (Fin m))) (n : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ (M : ℕ) (enc : (Fin n → Fin m) → Fin M)
    (dec : Fin M → (Fin n → Fin m)) (len : Fin M → ℕ),
    IsDSemifaithfulCode m d D n M enc dec len ∧
    ∀ P ∈ S, expectedRate P n M enc len - rateDistortion P d D ≤ r }

/-- Compact interior source class under Hamming distortion at level `D`: every letter has
    probability at least `D/(m-1) + δ`.  On it `(m - 1) · minₓ P(x) > D`, so the regularity
    conditions of Zhang–Yang–Wei / Yang–Zhang hold uniformly and `R(P, D) > 0`. -/
def interiorClass (m : ℕ) (D δ : ℝ) : Set (ProbDist (Fin m)) :=
  { P | ∀ x : Fin m, D / ((m : ℝ) - 1) + δ ≤ P.pmf x }

/-- Minimax universal redundancy `R_n(m, D, δ)` of `d`-semifaithful codes under Hamming
    distortion over the interior class `interiorClass m D δ`. -/
noncomputable def minimaxLossyRedundancy (m : ℕ) (D δ : ℝ) (n : ℕ) : ℝ :=
  minimaxLossyRedundancyOn m (hammingDist m) D (interiorClass m D δ) n

/-- Minimax Redundancy Constant for Universal `d`-Semifaithful Lossy Source Coding
    (Yu–Speed 1993; Zhang–Yang–Wei 1997; Yang–Zhang; statement-fixed 2026-11-27):
    for an `m`-ary memoryless source under Hamming distortion `0 < D < 1 - 1/m`, and every
    interior class `interiorClass m D δ` with `0 < δ < 1/m - D/(m-1)` (nonempty, compact, with
    nonempty relative interior), does the minimax redundancy have an exact pre-log constant,
    i.e. does `(n / log₂ n) · R_n(m, D, δ)` converge to a real limit `L(m, D, δ)`?
    (Conjectured: `L = (m + 1)/2`.) -/
def Statement : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (D : ℝ), 0 < D → D < 1 - 1 / (m : ℝ) →
    ∀ (δ : ℝ), 0 < δ → δ < 1 / (m : ℝ) - D / ((m : ℝ) - 1) →
    ∃ L : ℝ, ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |((n : ℝ) / log2 (n : ℝ)) * minimaxLossyRedundancy m D δ n - L| ≤ ε

def problem : OpenProblem where
  id := "universal-lossy-redundancy"
  title := "Exact Minimax Redundancy Constant for Universal d-Semifaithful Lossy Source Coding"
  category := .sourceCoding
  status := .open
  posedBy := "Bin Yu, T. P. Speed; Zhen Zhang, En-Hui Yang, Victor K. Wei"
  posedYear := 1993
  statement := Statement

end InfoTheory.Problems.UniversalLossyRedundancy
