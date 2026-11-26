import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SpernerCapacityDirectedGraphs

/-- Sperner Capacity of Directed Odd Cycles (Gargano–Körner–Vaccaro 1992;
    Calderbank–Frankl–Graham–Li–Shepp 1993; Alon 1998):
    By Alon's out-degree bound `Σ(D) ≤ log₂(Δ⁺(D) + 1)`, every directed cycle `\vec{C}_m`
    (`m ≥ 3`) satisfies `Σ(\vec{C}_m) ≤ 1`. Equality `Σ(\vec{C}_3) = 1` holds for the cyclic
    triangle (Calderbank et al. 1993; Blokhuis 1993).
    For the directed 5-cycle `\vec{C}_5`, is `Σ(\vec{C}_5)` strictly less than `1`? -/
def Statement : Prop :=
  spernerCapacity (directedCycle 5) < 1

def problem : OpenProblem where
  id := "sperner-capacity-directed-graphs"
  title := "Sperner Capacity of Directed Odd Cycles"
  category := .zeroError
  status := .open
  posedBy := "Luisa Gargano, János Körner, Ugo Vaccaro"
  posedYear := 1992
  statement := Statement

end InfoTheory.Problems.SpernerCapacityDirectedGraphs
