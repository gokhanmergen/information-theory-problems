import InfoTheory.Core

open scoped BigOperators Classical

namespace InfoTheory.Problems.SpernerCapacityDirectedGraphs

/-- A tournament on `Fin n` specified by choosing the orientation of each unordered pair
    `u < v` (`true` encodes `u → v`, `false` encodes `v → u`). -/
def tournamentOfBits (n : ℕ) (ori : { p : Fin n × Fin n // p.1 < p.2 } → Bool) :
    DiGraph (Fin n) where
  edge u v :=
    if h : u < v then ori ⟨(u, v), h⟩ = true
    else if h' : v < u then ori ⟨(v, u), h'⟩ = false
    else False
  irrefl u := by simp

/-- **Alon's Random Tournament Sperner Capacity Conjecture** (Alon 1998, *On the capacity
    of digraphs*, European J. Combin. 19(1), 1–5):
    Although there exist tournaments on `2n` vertices whose exponential Sperner capacity
    `2^{Σ(T)}` is at least `n` while their largest transitive subtournament has size
    `O(log n)` (disproving Körner–Simonyi), does a uniformly random tournament `T_n` on
    `n` vertices satisfy `2^{Σ(T_n)} ≤ c · log₂ n` with probability tending to `1` as
    `n → ∞`, for some absolute constant `c > 0`? -/
def Statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        let total : ℕ := Fintype.card ({ p : Fin n × Fin n // p.1 < p.2 } → Bool)
        let good : ℕ :=
          (Finset.univ.filter (fun ori : { p : Fin n × Fin n // p.1 < p.2 } → Bool =>
            (2 : ℝ) ^ (spernerCapacity (tournamentOfBits n ori)) ≤ c * log2 (n : ℝ))).card
        (good : ℝ) / (total : ℝ) ≥ 1 - ε

def problem : OpenProblem where
  id := "sperner-capacity-directed-graphs"
  title := "Sperner Capacity of Random Tournaments and Directed Graphs"
  category := .zeroError
  status := .open
  posedBy := "Noga Alon; Luisa Gargano, János Körner, Ugo Vaccaro"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.SpernerCapacityDirectedGraphs
