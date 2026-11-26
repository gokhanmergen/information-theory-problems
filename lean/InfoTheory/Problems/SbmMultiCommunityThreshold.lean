import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SbmMultiCommunityThreshold

/-- Unordered pairs `(u, v)` with `u < v` on `Fin n`. -/
abbrev GraphEdge (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

/-- Simple undirected graph on `Fin n` represented as an indicator on unordered pairs. -/
abbrev Graph (n : ℕ) := GraphEdge n → Bool

/-- Conditional probability `Pr[G | σ]` under the symmetric `q`-community SBM `(n, q, a/n, b/n)`. -/
noncomputable def sbmCondProb (n q : ℕ) (a b : ℝ)
    (σ : Fin n → Fin q) (G : Graph n) : ℝ :=
  ∏ e : GraphEdge n,
    let p : ℝ := if σ e.1.1 = σ e.1.2 then a / (n : ℝ) else b / (n : ℝ)
    if G e then p else 1 - p

/-- Marginal graph probability `Pr_{SBM}[G]` averaged over uniform community labels `σ`. -/
noncomputable def sbmProb (n q : ℕ) (a b : ℝ) (G : Graph n) : ℝ :=
  ((1 : ℝ) / ((q ^ n : ℕ) : ℝ)) * ∑ σ : Fin n → Fin q, sbmCondProb n q a b σ G

/-- Erdős–Rényi random graph probability `Pr_{G(n, d/n)}[G]`. -/
noncomputable def erProb (n : ℕ) (d : ℝ) (G : Graph n) : ℝ :=
  ∏ e : GraphEdge n, if G e then d / (n : ℝ) else 1 - d / (n : ℝ)

/-- Maximum permutation-aligned community overlap between true labels `σ` and estimate `τ`. -/
noncomputable def maxPermOverlap {n q : ℕ} (σ τ : Fin n → Fin q) : ℝ :=
  sSup { r : ℝ | ∃ (π : Fin q → Fin q), Function.Bijective π ∧
    r = ((1 : ℝ) / (n : ℝ)) * ∑ v : Fin n, if τ v = π (σ v) then (1 : ℝ) else 0 }

/-- Information-theoretic weak recovery is achievable in `SBM(n, q, a/n, b/n)`. -/
def sbmWeakRecoveryAchievable (q : ℕ) (a b : ℝ) : Prop :=
  ∃ (δ : ℝ), 0 < δ ∧ ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    ∃ (est : Graph n → Fin n → Fin q),
      ((1 : ℝ) / ((q ^ n : ℕ) : ℝ)) *
        ∑ σ : Fin n → Fin q, ∑ G : Graph n,
          sbmCondProb n q a b σ G * maxPermOverlap σ (est G) ≥
        (1 : ℝ) / (q : ℝ) + δ

/-- Strong distinguishability `TV(SBM(n, q, a/n, b/n), G(n, d/n)) → 1`. -/
def sbmDistinguishableFromER (q : ℕ) (a b : ℝ) : Prop :=
  let d : ℝ := (a + ((q - 1 : ℕ) : ℝ) * b) / (q : ℝ)
  ∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    (1 / 2 : ℝ) * ∑ G : Graph n, |sbmProb n q a b G - erProb n d G| ≥ 1 - ε

/-- Kesten–Stigum Weak Recovery Threshold Conjecture for the 4-Community SBM
    (Decelle–Krzakala–Moore–Zdeborová 2011; Mossel–Sly–Sohn 2025):
    While Mossel–Sly–Sohn (STOC 2025, arXiv:2406.15957) proved equivalence of weak recovery
    and distinguishability away from the critical point, and Banks et al. (2016) showed
    information-theoretic recovery strictly beats Kesten–Stigum for `q ≥ 5`, it remains
    open for `q = 4` (and `q = 3` at moderate degree) whether the information-theoretic
    weak recovery threshold coincides with the Kesten–Stigum threshold `(a - b)² = q (a + (q - 1) b)`. -/
def Statement : Prop :=
  ∀ (a b : ℝ), 0 < b → b < a →
    (a - b) ^ 2 < 4 * (a + 3 * b) →
    ¬ sbmWeakRecoveryAchievable 4 a b

def problem : OpenProblem where
  id := "sbm-multi-community-threshold"
  title := "Exact Information-Theoretic Weak Recovery Threshold for the q-Community Stochastic Block Model (q ≥ 5)"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Aurelien Decelle, Florent Krzakala, Cristopher Moore, and Lenka Zdeborová"
  posedYear := 2011
  statement := Statement

end InfoTheory.Problems.SbmMultiCommunityThreshold
