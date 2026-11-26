import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CodedCachingExactTradeoff

/-- Zero-error achievability of rate `R` at normalized cache memory `M` in the centralized
    `(N, K)` coded caching problem allowing arbitrary (possibly coded) cache placement. -/
def IsCodedCachingAchievable (N K : ℕ) (M R : ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ R ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ (F Csize Bsize : ℕ), 0 < F ∧ 0 < Csize ∧ 0 < Bsize ∧
      log2 (Csize : ℝ) ≤ (M + ε) * (F : ℝ) ∧
      log2 (Bsize : ℝ) ≤ (R + ε) * (F : ℝ) ∧
      ∃ (place : Fin K → (Fin N → Fin F → Bool) → Fin Csize)
        (deliver : (Fin K → Fin N) → (Fin N → Fin F → Bool) → Fin Bsize)
        (dec : Fin K → (Fin K → Fin N) → Fin Csize → Fin Bsize → (Fin F → Bool)),
        ∀ (d : Fin K → Fin N) (W : Fin N → Fin F → Bool) (k : Fin K),
          dec k d (place k W) (deliver d W) = W (d k)

/-- Exact optimal worst-case broadcast rate `R*(N, K, M)` under general coded placement. -/
noncomputable def codedCachingOptimalRate (N K : ℕ) (M : ℝ) : ℝ :=
  sInf { R : ℝ | IsCodedCachingAchievable N K M R }

/-- Open problem: When `N ≥ K ≥ 2` and `M = t N / K` for an integer `t ∈ {1, ..., K}`,
    does the Maddah-Ali–Niesen rate `(K - t) / (t + 1)` equal the exact general
    (coded-placement) optimal caching rate `R*(N, K, M)`? -/
def Statement : Prop :=
  ∀ N K t : ℕ, 2 ≤ K → K ≤ N → 1 ≤ t → t ≤ K →
    codedCachingOptimalRate N K ((t : ℝ) * (N : ℝ) / (K : ℝ)) =
      ((K - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ)

def problem : OpenProblem where
  id := "coded-caching-exact-tradeoff"
  title := "Exact Rate–Memory Tradeoff of Centralized Coded Caching with Coded Placement"
  category := .networkCoding
  status := .partiallySolved
  posedBy := "Mohammad Ali Maddah-Ali and Urs Niesen"
  posedYear := 2014
  statement := Statement

end InfoTheory.Problems.CodedCachingExactTradeoff
