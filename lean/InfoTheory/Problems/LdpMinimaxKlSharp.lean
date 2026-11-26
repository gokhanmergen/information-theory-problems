import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.LdpMinimaxKlSharp

/-- Predicate that a channel `Q : Fin k → Fin m` is a symmetric `s`-Subset Selection
    `ε`-LDP mechanism: each output `y` corresponds to an `s`-element subset `S y ⊆ Fin k`,
    and `Q(y | x)` takes value `c · exp(ε)` if `x ∈ S y` and `c` otherwise. -/
def IsSubsetSelection (k m s : ℕ) (ε : ℝ) (Q : DMC (Fin k) (Fin m)) : Prop :=
  1 ≤ s ∧ s < k ∧
  ∃ (S : Fin m → Finset (Fin k)) (c : ℝ),
    0 < c ∧
    (∀ (y : Fin m), (S y).card = s) ∧
    (∀ (x : Fin k) (y : Fin m),
      Q.trans x y = if x ∈ S y then c * Real.exp ε else c)

/-- Minimax KL risk of `ε`-LDP discrete distribution estimation restricted to Subset
    Selection channels. -/
noncomputable def subsetSelectionMinimaxKLRisk (k n : ℕ) (ε : ℝ) : ℝ :=
  sInf { R : ℝ | ∃ (m s : ℕ) (Q : DMC (Fin k) (Fin m))
    (est : (Fin n → Fin m) → ProbDist (Fin k)),
    IsSubsetSelection k m s ε Q ∧
    ∀ (P : ProbDist (Fin k)),
      let Py := (Q.joint P).snd
      (∑ y : Fin n → Fin m, (∏ i : Fin n, Py.pmf (y i)) * klDivergence P (est y)) ≤ R }

/-- Exact asymptotic optimality (constant 1) of the Subset Selection mechanism family for
    minimax KL risk under `ε`-LDP across all alphabet sizes `k ≥ 2` and privacy parameters
    `ε > 0`. -/
def Statement : Prop :=
  ∀ (k : ℕ) (ε : ℝ), 2 ≤ k → 0 < ε →
    ∀ (δ : ℝ), 0 < δ →
      ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
        subsetSelectionMinimaxKLRisk k n ε ≤ (1 + δ) * ldpMinimaxKLRisk k n ε

def problem : OpenProblem where
  id := "ldp-minimax-kl-sharp"
  title := "Sharp Asymptotic Minimax KL Risk for Locally Differentially Private Distribution Estimation"
  category := .securityPrivacy
  status := .open
  posedBy := "John C. Duchi, Michael I. Jordan, and Martin J. Wainwright"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.LdpMinimaxKlSharp
