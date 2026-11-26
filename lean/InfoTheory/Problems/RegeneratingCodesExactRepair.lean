import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.RegeneratingCodesExactRepair

/-- Normalized storage–bandwidth pair `(αBar, βBar)` lies in the closure of the exact-repair
    `(n, k, d)` regenerating code achievable region `R_exact(n, k, d)`. -/
def IsExactRepairAchievable (n k d : ℕ) (αBar βBar : ℝ) : Prop :=
  0 < αBar ∧ 0 < βBar ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ (M A R : ℕ), 2 ≤ M ∧ 1 ≤ A ∧ 1 ≤ R ∧
      log2 (A : ℝ) / log2 (M : ℝ) ≤ αBar + ε ∧
      log2 (R : ℝ) / log2 (M : ℝ) ≤ βBar + ε ∧
      ∃ store : Fin n → Fin M → Fin A,
        -- k-node data reconstruction
        (∀ S : Finset (Fin n), S.card = k →
          ∀ m₁ m₂ : Fin M, (∀ i ∈ S, store i m₁ = store i m₂) → m₁ = m₂) ∧
        -- Exact repair of any failed node i from any d-subset H of helper nodes
        (∀ (i : Fin n) (H : Finset (Fin n)), i ∉ H → H.card = d →
          ∃ help : Fin n → Fin A → Fin R,
            ∀ m₁ m₂ : Fin M,
              (∀ j ∈ H, help j (store j m₁) = help j (store j m₂)) →
              store i m₁ = store i m₂)

/-- Shannon-type polymatroid outer bound `R_Shannon(n, k, d)` for exact-repair `(n, k, d)`
    regenerating codes (Tian 2014). -/
def InShannonRepairOuterBound (n k d : ℕ) (αBar βBar : ℝ) : Prop :=
  0 < αBar ∧ 0 < βBar ∧
  ∃ (Nvar : ℕ) (h : Finset (Fin Nvar) → ℝ)
    (nodeIdx : Fin n → Fin Nvar)
    (helpIdx : Fin n → Finset (Fin n) → Fin n → Fin Nvar),
    IsPolymatroid Nvar h ∧
    -- Total file entropy normalized to 1
    h (Finset.univ.image nodeIdx) = 1 ∧
    -- Per-node storage bound
    (∀ i : Fin n, h {nodeIdx i} ≤ αBar) ∧
    -- Per-helper repair bandwidth bound
    (∀ (i : Fin n) (H : Finset (Fin n)) (j : Fin n),
      i ∉ H → H.card = d → j ∈ H → h {helpIdx i H j} ≤ βBar) ∧
    -- Helper message is a deterministic function of helper node's storage
    (∀ (i : Fin n) (H : Finset (Fin n)) (j : Fin n),
      i ∉ H → H.card = d → j ∈ H →
      h ({nodeIdx j, helpIdx i H j} : Finset (Fin Nvar)) = h {nodeIdx j}) ∧
    -- Exact repair: failed node i is determined by the d helper messages from H
    (∀ (i : Fin n) (H : Finset (Fin n)),
      i ∉ H → H.card = d →
      h (insert (nodeIdx i) (H.image (helpIdx i H))) = h (H.image (helpIdx i H))) ∧
    -- k-node reconstruction: any k nodes contain the full normalized file entropy 1
    (∀ S : Finset (Fin n), S.card = k → 1 ≤ h (S.image nodeIdx))

/-- Open problem: Do Shannon-type information inequalities (the polymatroid outer bound)
    completely characterize the exact-repair storage–bandwidth tradeoff region
    `R_exact(n, k, d)` for all `2 ≤ k ≤ d < n`? -/
def Statement : Prop :=
  ∀ (n k d : ℕ) (αBar βBar : ℝ),
    2 ≤ k → k ≤ d → d < n → 0 < αBar → 0 < βBar →
    (InShannonRepairOuterBound n k d αBar βBar ↔ IsExactRepairAchievable n k d αBar βBar)

def problem : OpenProblem where
  id := "regenerating-codes-exact-repair"
  title := "Exact Storage–Bandwidth Tradeoff for Exact-Repair Regenerating Codes"
  category := .networkCoding
  status := .partiallySolved
  posedBy := "Alexandros G. Dimakis et al.; Chao Tian"
  posedYear := 2010
  statement := Statement

end InfoTheory.Problems.RegeneratingCodesExactRepair
