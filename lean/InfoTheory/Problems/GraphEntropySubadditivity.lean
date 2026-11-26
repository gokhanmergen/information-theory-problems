import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.GraphEntropySubadditivity

/-- Edge union `F ∪ G` of two simple graphs on the same vertex set `V`. -/
def graphUnion {V : Type*} (F G : SimpleGraph V) : SimpleGraph V where
  Adj u v := F.Adj u v ∨ G.Adj u v
  symm := ⟨fun _ _ h =>
    h.elim (fun h1 => Or.inl ((F.adj_comm _ _).mp h1))
           (fun h2 => Or.inr ((G.adj_comm _ _).mp h2))⟩
  loopless := ⟨by intro u; simp [F.loopless, G.loopless]⟩

/-- Subadditivity of Witsenhausen's Zero-Error Rate under Graph Union
    (Körner–Marton 1988; Marton 1993; Simonyi 1995):
    While Körner's OR-product graph entropy satisfies `H(F ∪ G, P) ≤ H(F, P) + H(G, P)`
    universally, and the complementary case `F ∪ G = K_n` holds for `witsenhausenRate` via
    Lovász's theta bound, it is open whether Witsenhausen's AND-product rate satisfies
    `R₀(F ∪ G) ≤ R₀(F) + R₀(G)` for all finite graphs `F, G` on the same vertex set. -/
def Statement : Prop :=
  ∀ (n : ℕ) (F G : SimpleGraph (Fin n)), 0 < n →
    witsenhausenRate (graphUnion F G) ≤ witsenhausenRate F + witsenhausenRate G

def problem : OpenProblem where
  id := "graph-entropy-subadditivity"
  title := "Subadditivity of Witsenhausen's Rate and Complementary Graph Entropy under Graph Union"
  category := .zeroError
  status := .open
  posedBy := "János Körner, Katalin Marton; Gábor Simonyi"
  posedYear := 1988
  statement := Statement

end InfoTheory.Problems.GraphEntropySubadditivity
