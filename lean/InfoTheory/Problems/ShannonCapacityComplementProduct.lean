import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ShannonCapacityComplementProduct

/-- Graph complement `Ḡ` of a simple graph `G`. -/
def graphCompl {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ¬ G.Adj u v
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, fun h' => h ((G.adj_comm _ _).mp h')⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Minimum Product of Shannon Capacities of a Graph and Its Complement
    (Lovász 1979; Haemers 1979; Alon 1998):
    While `Θ(G ⊠ Ḡ) ≥ n` and `ϑ(G) · ϑ(Ḡ) ≥ n` for all `n`-vertex graphs, Alon (1998)
    constructed `n`-vertex graphs with `Θ(G) · Θ(Ḡ) ≤ 2^{O(√(log n log log n))}`.
    Does there exist a constant `c > 0` such that for all sufficiently large `n`, there is
    an `n`-vertex graph `G` with `Θ(G) · Θ(Ḡ) ≤ (log₂ n)^c`? -/
def Statement : Prop :=
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 2 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
      ∃ G : SimpleGraph (Fin n),
        shannonCapacity G * shannonCapacity (graphCompl G) ≤ (log2 (n : ℝ)) ^ c

def problem : OpenProblem where
  id := "shannon-capacity-complement-product"
  title := "Minimum Product of Shannon Capacities of a Graph and Its Complement"
  category := .zeroError
  status := .open
  posedBy := "László Lovász; Willem Haemers; Noga Alon"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.ShannonCapacityComplementProduct
