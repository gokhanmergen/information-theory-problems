import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.PirCodedCollusionCapacity

/-- An `K × N` matrix `G` over a finite field `F` is an `[N, K]` MDS generator matrix iff
    every `K`-element subset of columns uniquely determines any `K`-symbol message vector. -/
def IsMDSGenerator (F : Type) [Field F] [Fintype F] (N K : ℕ)
    (G : Matrix (Fin K) (Fin N) F) : Prop :=
  ∀ S : Finset (Fin N), S.card = K →
    ∀ x₁ x₂ : Fin K → F,
      (∀ j ∈ S, ∑ r : Fin K, x₁ r * G r j = ∑ r : Fin K, x₂ r * G r j) →
      x₁ = x₂

/-- Achievability of download rate `R` for `T`-colluding PIR over `[N, K]` MDS-coded
    databases storing `M` files over a finite field `F`. -/
def HasMDSTPIRRate (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (N K T M : ℕ) (R : ℝ) : Prop :=
  ∃ (L numRand Q : ℕ) (D : Fin N → ℕ)
    (G : Matrix (Fin K) (Fin N) F)
    (query : Fin M → Fin numRand → Fin N → Fin Q)
    (ans : ∀ j : Fin N, (Fin M → Fin L → F) → Fin Q → Fin (D j))
    (dec : Fin M → Fin numRand → (∀ j : Fin N, Fin (D j)) → (Fin L → Fin K → F)),
    0 < L ∧ 0 < numRand ∧ 0 < Q ∧ (∀ j : Fin N, 0 < D j) ∧
    IsMDSGenerator F N K G ∧
    -- Correctness: user recovers W θ for every database W, demand θ, and randomness u
    (∀ (W : Fin M → Fin L → Fin K → F) (θ : Fin M) (u : Fin numRand),
      let stored (j : Fin N) (m : Fin M) (ℓ : Fin L) : F :=
        ∑ r : Fin K, W m ℓ r * G r j
      dec θ u (fun j : Fin N => ans j (stored j) (query θ u j)) = W θ) ∧
    -- Information-theoretic T-privacy: joint query distribution on any ≤ T servers is independent of θ
    (∀ (S : Finset (Fin N)), S.card ≤ T →
      ∀ (θ₁ θ₂ : Fin M) (qObs : Fin N → Fin Q),
        (Finset.univ.filter (fun u : Fin numRand => ∀ j ∈ S, query θ₁ u j = qObs j)).card =
        (Finset.univ.filter (fun u : Fin numRand => ∀ j ∈ S, query θ₂ u j = qObs j)).card) ∧
    -- Download rate condition
    0 < ∑ j : Fin N, log2 (D j : ℝ) ∧
    R ≤ ((L * K : ℕ) : ℝ) * log2 (Fintype.card F : ℝ) / (∑ j : Fin N, log2 (D j : ℝ))

/-- Exact `T`-colluding PIR capacity `C(N, K, T, M)` for `[N, K]` MDS-coded databases storing `M` files. -/
noncomputable def mdsTPirCapacity (N K T M : ℕ) : ℝ :=
  sSup { R : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F) (hDec : DecidableEq F),
    @HasMDSTPIRRate F hF hFin hDec N K T M R }

/-- Asymptotic MDS-TPIR capacity `C_∞(N, K, T) = inf_{M ≥ 1} C(N, K, T, M)`. -/
noncomputable def mdsTPirAsympCapacity (N K T : ℕ) : ℝ :=
  sInf { c : ℝ | ∃ M : ℕ, 1 ≤ M ∧ c = mdsTPirCapacity N K T M }

/-- Asymptotic MDS-TPIR Capacity Conjecture: for all `1 ≤ K, T` with `K + T - 1 < N`,
    `C_∞(N, K, T) = 1 - (K + T - 1) / N`. -/
def Statement : Prop :=
  ∀ N K T : ℕ, 1 ≤ K → 1 ≤ T → K + T - 1 < N →
    mdsTPirAsympCapacity N K T = 1 - ((K + T - 1 : ℕ) : ℝ) / (N : ℝ)

def problem : OpenProblem where
  id := "pir-coded-collusion-capacity"
  title := "Capacity of T-Colluding Private Information Retrieval from MDS-Coded Databases"
  category := .networkCoding
  status := .open
  posedBy := "Ragnar Freij-Hollanti, Oliver W. Gnilke, Camilla Hollanti, and David A. Karpuk; Hua Sun and Syed A. Jafar"
  posedYear := 2017
  statement := Statement

end InfoTheory.Problems.PirCodedCollusionCapacity
