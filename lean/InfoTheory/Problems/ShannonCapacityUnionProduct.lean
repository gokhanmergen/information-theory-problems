import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ShannonCapacityUnionProduct

/-- Boundedness of Shannon Capacity under Disjoint Union (Alon 1998):
    Alon (1998) disproved `Θ(G + H) = Θ(G) + Θ(H)` and showed `Θ(G + H)` can grow
    superpolynomially in `max(Θ(G), Θ(H))`. Is `Θ(G + H)` uniformly bounded whenever
    `Θ(G) ≤ C` and `Θ(H) ≤ C`? -/
def Statement : Prop :=
  ∀ (C : ℝ), ∃ (B : ℝ),
    ∀ (m n : ℕ) (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin n)),
      0 < m → 0 < n →
      shannonCapacity G ≤ C → shannonCapacity H ≤ C →
      shannonCapacity (disjointUnionGraph G H) ≤ B

def problem : OpenProblem where
  id := "shannon-capacity-union-product"
  title := "Boundedness of Shannon Capacity under Disjoint Union and Strong Product"
  category := .zeroError
  status := .open
  posedBy := "Claude Shannon; Noga Alon"
  posedYear := 1998
  statement := Statement

end InfoTheory.Problems.ShannonCapacityUnionProduct
