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

/-- `P^t(U) = ∑_{x ∈ U} ∏_i P(x_i)`: probability of a set `U` of length-`t` sequences under
    the i.i.d. law `P^{⊗t}`. -/
noncomputable def iidProb {V : Type*} [Fintype V] (P : ProbDist V) (t : ℕ)
    (U : Finset (Fin t → V)) : ℝ :=
  ∑ x ∈ U, ∏ i : Fin t, P.pmf (x i)

/-- Block quantity `min_{U : P^t(U) > 1 - ε} (1/t) log₂ χ(G^{⊠t}[U])`: the colourings `c`
    need only be proper on the strong (normal) power `G^{⊠t}` induced on `U`. -/
noncomputable def coEntropyBlock {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P : ProbDist V) (ε : ℝ) (t : ℕ) : ℝ :=
  sInf { r : ℝ | ∃ (U : Finset (Fin t → V)) (m : ℕ) (c : (Fin t → V) → Fin m),
    1 - ε < iidProb P t U ∧ 0 < m ∧
    (∀ x ∈ U, ∀ y ∈ U, (strongPower G t).Adj x y → c x ≠ c y) ∧
    r = log2 (m : ℝ) / (t : ℝ) }

/-- `limsup_{t → ∞}` of `coEntropyBlock G P ε t`, written as `inf_N sup_{t ≥ N, t > 0}`. -/
noncomputable def coEntropyLimsup {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P : ProbDist V) (ε : ℝ) : ℝ :=
  sInf { s : ℝ | ∃ N : ℕ,
    s = sSup { r : ℝ | ∃ t : ℕ, N ≤ t ∧ 0 < t ∧ r = coEntropyBlock G P ε t } }

/-- Complementary graph entropy (Körner–Longo 1973 "co-entropy"; Simonyi 2001, Definition 32):
    `H̄(G, P) = lim_{ε → 0} limsup_{t → ∞} min_{U : P^t(U) > 1-ε} (1/t) log₂ χ(G^{⊠t}[U])`.
    The block quantity is non-increasing in `ε`, so the limit `ε → 0` is the supremum over
    `ε ∈ (0, 1)`. All sets involved are non-empty and bounded (`0 ≤ · ≤ log₂ |V|`). -/
noncomputable def complementaryGraphEntropy {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P : ProbDist V) : ℝ :=
  sSup { h : ℝ | ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ h = coEntropyLimsup G P ε }

/-- Statement-fix (2026-11-27). The previous statement asked whether Witsenhausen's
    distribution-free rate `R₀(G) = inf_k (1/k) log₂ χ(G^{⊠k})` is subadditive under edge union;
    no literature source poses that. The question actually posed in the literature is Körner's,
    for the complementary graph entropy `H̄(G, P)`:
    G. Simonyi, "Perfect graphs and graph entropy. An updated survey," in *Perfect Graphs*
    (J. L. Ramírez-Alfonsín and B. A. Reed, eds.), Wiley, 2001, §7.4: "It is an old and still
    open question of Körner whether H̄(G, P) is also sub-additive like graph entropy."
    Known: it holds when `F` and `G` are perfect, and when `F ∪ G` is perfect (Marton 1993).

    Statement: for all graphs `F, G` on a common finite vertex set and every distribution `P`,
    `H̄(F ∪ G, P) ≤ H̄(F, P) + H̄(G, P)`. -/
def Statement : Prop :=
  ∀ (n : ℕ) (F G : SimpleGraph (Fin n)) (P : ProbDist (Fin n)),
    complementaryGraphEntropy (graphUnion F G) P ≤
      complementaryGraphEntropy F P + complementaryGraphEntropy G P

def problem : OpenProblem where
  id := "graph-entropy-subadditivity"
  title := "Subadditivity of Complementary Graph Entropy under Graph Union"
  category := .zeroError
  status := .open
  posedBy := "János Körner (as recorded by Gábor Simonyi)"
  posedYear := 2001
  statement := Statement

end InfoTheory.Problems.GraphEntropySubadditivity
