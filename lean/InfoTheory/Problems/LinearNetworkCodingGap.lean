import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.LinearNetworkCodingGap

/-- A directed acyclic multiple-unicast network on `Fin V` with unit-capacity edges
    (an edge `u → v` is active iff `u.1 < v.1` and `adj u v = true`) and `numSessions`
    source–destination pairs. -/
structure DAGNetwork (V : ℕ) where
  adj : Fin V → Fin V → Bool
  numSessions : ℕ
  src : Fin numSessions → Fin V
  dst : Fin numSessions → Fin V

/-- Symmetric (equal-rate) zero-error nonlinear network coding capacity `C_nl(N)`. -/
noncomputable def dagNonlinearCapacity {V : ℕ} (net : DAGNetwork V) : ℝ :=
  sSup { lam : ℝ | 0 ≤ lam ∧
    ∃ (t M : ℕ), 0 < t ∧ 0 < M ∧ (2 : ℝ) ^ ((t : ℝ) * lam) ≤ (M : ℝ) ∧
      ∃ edgeVal : (Fin net.numSessions → Fin M) → Fin V → Fin V → Fin (2 ^ t),
        -- Inactive or non-DAG pairs carry constant 0
        (∀ msg u v, ¬ (u.1 < v.1 ∧ net.adj u v = true) → (edgeVal msg u v).1 = 0) ∧
        -- Local causality: outgoing edges of u depend only on incoming edges and sources at u
        (∀ msg₁ msg₂ u,
          (∀ w : Fin V, edgeVal msg₁ w u = edgeVal msg₂ w u) →
          (∀ i : Fin net.numSessions, net.src i = u → msg₁ i = msg₂ i) →
          ∀ v : Fin V, edgeVal msg₁ u v = edgeVal msg₂ u v) ∧
        -- Zero-error decoding at every destination
        (∀ i : Fin net.numSessions, ∀ msg₁ msg₂,
          (∀ w : Fin V, edgeVal msg₁ w (net.dst i) = edgeVal msg₂ w (net.dst i)) →
          (∀ j : Fin net.numSessions, net.src j = net.dst i → msg₁ j = msg₂ j) →
          msg₁ i = msg₂ i) }

/-- Achievability of symmetric rate `lam` on `net` via a vector linear network code over `F`. -/
def HasLinearDAGRate (F : Type) [Field F] [Fintype F] {V : ℕ} (net : DAGNetwork V) (lam : ℝ) : Prop :=
  0 ≤ lam ∧
  ∃ (t k : ℕ), 0 < t ∧ lam ≤ (k : ℝ) / (t : ℝ) ∧
    ∃ edgeVal : (Fin net.numSessions → Fin k → F) →ₗ[F] (Fin V → Fin V → Fin t → F),
      (∀ msg u v, ¬ (u.1 < v.1 ∧ net.adj u v = true) → edgeVal msg u v = 0) ∧
      (∀ msg₁ msg₂ u,
        (∀ w : Fin V, edgeVal msg₁ w u = edgeVal msg₂ w u) →
        (∀ i : Fin net.numSessions, net.src i = u → msg₁ i = msg₂ i) →
        ∀ v : Fin V, edgeVal msg₁ u v = edgeVal msg₂ u v) ∧
      (∀ i : Fin net.numSessions, ∀ msg₁ msg₂,
        (∀ w : Fin V, edgeVal msg₁ w (net.dst i) = edgeVal msg₂ w (net.dst i)) →
        (∀ j : Fin net.numSessions, net.src j = net.dst i → msg₁ j = msg₂ j) →
        msg₁ i = msg₂ i)

/-- Symmetric (equal-rate) vector linear network coding capacity `C_lin(N)` maximized over
    all finite fields `F` and all vector dimensions `t ≥ 1`. -/
noncomputable def dagLinearCapacity {V : ℕ} (net : DAGNetwork V) : ℝ :=
  sSup { lam : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F),
    @HasLinearDAGRate F hF hFin V net lam }

/-- Open problem: Can the multiplicative capacity gap `C_nl(N) / C_lin(N)` between nonlinear
    and arbitrary-finite-field linear network coding approach linear growth `V^(1 - ε)` in the
    number of network vertices `V` for every `ε > 0`? -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ V₀ : ℕ, ∃ (V : ℕ) (net : DAGNetwork V),
    V₀ ≤ V ∧ 0 < V ∧ 0 < dagNonlinearCapacity net ∧
    (V : ℝ) ^ (1 - ε) * dagLinearCapacity net ≤ dagNonlinearCapacity net

def problem : OpenProblem where
  id := "linear-network-coding-gap"
  title := "Maximum Multiplicative Gap Between Nonlinear and Linear Network Coding Capacity"
  category := .networkCoding
  status := .partiallySolved
  posedBy := "Randall Dougherty, Chris Freiling, and Kenneth Zeger"
  posedYear := 2005
  statement := Statement

end InfoTheory.Problems.LinearNetworkCodingGap
