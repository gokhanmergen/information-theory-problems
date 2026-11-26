import InfoTheory.Core.Entropy
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Zero-Error Information Theory and Graph Capacity

Definitions for zero-error channel capacity, strong graph products,
Lovász theta function, Körner graph entropy, Sperner capacity,
and zero-error multiuser channels.
-/

open scoped BigOperators

namespace InfoTheory

/-- Strong graph product `G ⊠ H`: distinct vertices `(u₁, v₁)` and `(u₂, v₂)` are adjacent
    iff in each coordinate they are either equal or adjacent. -/
def strongProd {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj p q := p ≠ q ∧ (p.1 = q.1 ∨ G.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.Adj p.2 q.2)
  symm := ⟨by
    intro p q ⟨hne, h1, h2⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · rcases h1 with heq | h; exact Or.inl heq.symm; exact Or.inr (G.adj_comm _ _ |>.mp h)
    · rcases h2 with heq | h; exact Or.inl heq.symm; exact Or.inr (H.adj_comm _ _ |>.mp h)⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- The `k`-fold strong power `G^{⊠ k}` on `Fin k → V`. -/
def strongPower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i : Fin k, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨by
    intro x y ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    rcases h i with heq | hadj
    · exact Or.inl heq.symm
    · exact Or.inr (G.adj_comm _ _ |>.mp hadj)⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- An independent set in `G`. -/
def IsIndepSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- Independence number `α(G)` of a finite graph `G`. -/
noncomputable def indepNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup { m : ℕ | ∃ S : Finset V, IsIndepSet G S ∧ S.card = m }

/-- Shannon (zero-error) capacity `Θ(G) = sup_{k ≥ 1} α(G^{⊠ k})^{1/k}`. -/
noncomputable def shannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ)) }

/-- The cycle graph `C_m` on `ZMod m` (for `m ≥ 3`). -/
def cycleGraph (m : ℕ) : SimpleGraph (ZMod m) where
  Adj x y := x ≠ y ∧ (x - y = 1 ∨ y - x = 1)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Disjoint union `G + H` of two graphs on `V ⊕ W`. -/
def disjointUnionGraph {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) where
  Adj p q := match p, q with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => False
  symm := ⟨by
    intro p q h
    cases p <;> cases q <;> simp_all [SimpleGraph.adj_comm]⟩
  loopless := ⟨by
    intro p; cases p <;> simp [G.loopless, H.loopless]⟩

/-- Orthonormal representation of `G` in `ℝ^d`: unit vectors `u_v` such that non-adjacent
    distinct vertices are orthogonal. -/
def IsOrthonormalRep {V : Type*} (G : SimpleGraph V) (d : ℕ) (u : V → Fin d → ℝ) : Prop :=
  (∀ v, ∑ i : Fin d, (u v i) ^ 2 = 1) ∧
  (∀ v w, v ≠ w → ¬ G.Adj v w → ∑ i : Fin d, u v i * u w i = 0)

/-- The Lovász theta function `ϑ(G)` via orthonormal representations. -/
noncomputable def lovaszTheta {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf { t : ℝ | ∃ (d : ℕ) (u : V → Fin d → ℝ) (c : Fin d → ℝ),
    IsOrthonormalRep G d u ∧
    (∑ i : Fin d, (c i) ^ 2 = 1) ∧
    (∀ v : V, (∑ i : Fin d, c i * u v i) ≠ 0 ∧
      1 / (∑ i : Fin d, c i * u v i) ^ 2 ≤ t) }

/-- Körner's graph entropy `H(G, P) = min_{X ∈ W ∈ I(G)} I(X; W)`. -/
noncomputable def kornerGraphEntropy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : ProbDist V) : ℝ :=
  sInf { r : ℝ | ∃ (Q : ProbDist (V × Finset V)),
    Q.fst = P ∧
    (∀ v S, Q.pmf (v, S) > 0 → v ∈ S ∧ IsIndepSet G S) ∧
    r = mutualInfo Q }

/-- Witsenhausen's zero-error source coding rate with side information (complementary graph entropy). -/
noncomputable def witsenhausenRate {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sInf { r : ℝ | ∃ (k : ℕ) (m : ℕ) (c : (Fin k → V) → Fin m),
    0 < k ∧ 0 < m ∧
    (∀ x y, (strongPower G k).Adj x y → c x ≠ c y) ∧
    r = log2 (m : ℝ) / (k : ℝ) }

/-- A directed graph on `V` (for Sperner capacity). -/
structure DiGraph (V : Type*) where
  edge : V → V → Prop
  irrefl : ∀ v, ¬ edge v v

/-- Directed odd cycle `\vec{C}_m` on `ZMod m`. -/
def directedCycle (m : ℕ) : DiGraph (ZMod m) where
  edge x y := x ≠ y ∧ y - x = 1
  irrefl := fun _ h => h.1 rfl

/-- `D`-qualitatively independent family of `k`-tuples (Gargano-Körner-Vaccaro Sperner capacity). -/
def IsSpernerCode {V : Type*} (D : DiGraph V) (k : ℕ) (C : Finset (Fin k → V)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ∃ i : Fin k, D.edge (x i) (y i)

/-- Sperner capacity `Σ(D) = sup_{k ≥ 1} (1/k) log₂ max |C|` over nonempty `D`-Sperner codes. -/
noncomputable def spernerCapacity {V : Type*} [Fintype V] (D : DiGraph V) : ℝ :=
  sSup { r : ℝ | ∃ (k : ℕ) (C : Finset (Fin k → V)),
    0 < k ∧ C.Nonempty ∧ IsSpernerCode D k C ∧ r = log2 (C.card : ℝ) / (k : ℝ) }

/-- Zero-error uniquely decodable code pair `(A, B)` for the binary adder MAC `X₁ + X₂`. -/
def IsAdderMACCode (n : ℕ) (A B : Finset (Fin n → Fin 2)) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B,
    (∀ i : Fin n, (a₁ i).1 + (b₁ i).1 = (a₂ i).1 + (b₂ i).1) → (a₁ = a₂ ∧ b₁ = b₂)

/-- Zero-error sum capacity of the binary adder MAC over nonempty uniquely decodable code pairs. -/
noncomputable def zeroErrorAdderMACSumCapacity : ℝ :=
  sSup { r : ℝ | ∃ (n : ℕ) (A B : Finset (Fin n → Fin 2)),
    0 < n ∧ A.Nonempty ∧ B.Nonempty ∧ IsAdderMACCode n A B ∧
    r = (log2 (A.card : ℝ) + log2 (B.card : ℝ)) / (n : ℝ) }

end InfoTheory
