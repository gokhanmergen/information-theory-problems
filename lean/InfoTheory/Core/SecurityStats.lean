import InfoTheory.Core.Entropy
import InfoTheory.Core.Channels

/-!
# Information-Theoretic Security, Privacy, SDPI, and Statistical Information Theory

Core definitions for:
- Secret key agreement with public discussion `S(X; Y ‖ Z)` and intrinsic information `I(X; Y ↓ Z)`
- Secret sharing access structures and optimal information ratio
- Strong Data Processing Inequality (SDPI) constants `η_KL(W)` and `η_χ²(W)`
- Hypercontractivity ribbon
- Distributed hypothesis testing error exponents
- Local Differential Privacy (LDP) minimax KL risk
- Interactive information complexity (internal vs external)
- Stochastic Block Model (SBM) recovery
-/

open scoped BigOperators

namespace InfoTheory

/-- Intrinsic conditional mutual information `I(X; Y ↓ Z) = inf_{Z̄ | Z} I(X; Y | Z̄)`
    (Maurer-Wolf 1999). -/
noncomputable def intrinsicInfo {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : ProbDist (X × Y × Z)) : ℝ :=
  sInf { r : ℝ | ∃ (kZb : ℕ) (W : DMC Z (Fin kZb)),
    let Q : ProbDist (X × Y × Fin kZb) :=
      { pmf := fun t => ∑ z : Z, P.pmf (t.1, t.2.1, z) * W.trans z t.2.2
        nonneg := fun t => Finset.sum_nonneg (fun z _ => mul_nonneg (P.nonneg _) (W.nonneg _ _))
        sum_one := by
          simp_rw [Fintype.sum_prod_type]
          calc ∑ x : X, ∑ y : Y, ∑ zb : Fin kZb, ∑ z : Z, P.pmf (x, y, z) * W.trans z zb
              = ∑ x : X, ∑ y : Y, ∑ z : Z, ∑ zb : Fin kZb, P.pmf (x, y, z) * W.trans z zb := by
                congr 1; ext x; congr 1; ext y; exact Finset.sum_comm
            _ = ∑ x : X, ∑ y : Y, ∑ z : Z, P.pmf (x, y, z) := by
                simp_rw [← Finset.mul_sum, W.sum_one, mul_one]
            _ = 1 := by
                simpa [Fintype.sum_prod_type] using P.sum_one }
    r = condMutualInfo Q }

/-- Recursive transcript evaluator for an `r`-round alternating public discussion protocol
    between Alice (holding `x`, private randomness `ra`) and Bob (holding `y`, private
    randomness `rb`), exchanging symbols in `Fin kM`. -/
def publicDiscussionTranscript {α β : Type*} {kRA kRB kM : ℕ}
    (aliceMsg : (t : ℕ) → α → Fin kRA → (Fin t → Fin kM) → Fin kM)
    (bobMsg : (t : ℕ) → β → Fin kRB → (Fin t → Fin kM) → Fin kM)
    (x : α) (y : β) (ra : Fin kRA) (rb : Fin kRB) : (t : ℕ) → (Fin t → Fin kM)
  | 0 => fun i => Fin.elim0 i
  | t + 1 =>
    let prev := publicDiscussionTranscript aliceMsg bobMsg x y ra rb t
    let nextSym := if t % 2 = 0 then aliceMsg t x ra prev else bobMsg t y rb prev
    fun i => if h : i.1 < t then prev ⟨i.1, h⟩ else nextSym

/-- `n`-fold i.i.d. product distribution of a tripartite source `P : ProbDist (X × Y × Z)`. -/
def sourcePower {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : ProbDist (X × Y × Z)) (n : ℕ) : ProbDist (Fin n → X × Y × Z) where
  pmf := fun s => ∏ i : Fin n, P.pmf (s i)
  nonneg := fun s => Finset.prod_nonneg (fun i _ => P.nonneg (s i))
  sum_one := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun _ _ => P.sum_one)

/-- Secret key capacity `S(X; Y ‖ Z)` with unlimited two-way public discussion (Maurer 1993;
    Ahlswede–Csiszár 1993).
    Alice and Bob observe `X^n`, `Y^n` with *independent* local randomness `(R_A, R_B)`,
    exchange an `r`-round causal public transcript `T`, and locally compute keys
    `K_A = keyA(X^n, R_A, T)` and `K_B = keyB(Y^n, R_B, T)`. Because `(R_A, R_B)` are
    independent of `(X^n, Y^n, Z^n)` and of each other, no free shared randomness exists,
    and every achievable rate is bounded above by `I(X; Y)`. -/
noncomputable def secretKeyCapacity {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : ProbDist (X × Y × Z)) : ℝ :=
  sSup { R : ℝ | 0 ≤ R ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∃ (r kK kM kRA kRB : ℕ)
        (Pa : ProbDist (Fin kRA)) (Pb : ProbDist (Fin kRB))
        (aliceMsg : (t : ℕ) → (Fin n → X) → Fin kRA → (Fin t → Fin kM) → Fin kM)
        (bobMsg : (t : ℕ) → (Fin n → Y) → Fin kRB → (Fin t → Fin kM) → Fin kM)
        (keyA : (Fin n → X) → Fin kRA → (Fin r → Fin kM) → Fin kK)
        (keyB : (Fin n → Y) → Fin kRB → (Fin r → Fin kM) → Fin kK),
        0 < kK ∧ 0 < kM ∧ 0 < kRA ∧ 0 < kRB ∧
        (log2 (kK : ℝ) / (n : ℝ)) ≥ R - ε ∧
        let fullDist : ProbDist ((Fin n → X × Y × Z) × Fin kRA × Fin kRB) :=
          (sourcePower P n).prod (Pa.prod Pb)
        let transOf (w : (Fin n → X × Y × Z) × Fin kRA × Fin kRB) : Fin r → Fin kM :=
          publicDiscussionTranscript aliceMsg bobMsg
            (fun i => (w.1 i).1) (fun i => (w.1 i).2.1) w.2.1 w.2.2 r
        let kAOf (w : (Fin n → X × Y × Z) × Fin kRA × Fin kRB) : Fin kK :=
          keyA (fun i => (w.1 i).1) w.2.1 (transOf w)
        let kBOf (w : (Fin n → X × Y × Z) × Fin kRA × Fin kRB) : Fin kK :=
          keyB (fun i => (w.1 i).2.1) w.2.2 (transOf w)
        -- Key agreement: `Pr[K_A ≠ K_B] ≤ ε`
        (∑ w, if kAOf w ≠ kBOf w then fullDist.pmf w else 0) ≤ ε ∧
        -- Secrecy & uniformity: `log₂ |K| - H(K_A | Z^n, T) ≤ n ε`
        log2 (kK : ℝ) - condEntropy (fullDist.map (fun w =>
          (kAOf w, (fun i => (w.1 i).2.2, transOf w)))) ≤ (n : ℝ) * ε }

/-- Strong Data Processing Inequality (SDPI) constant `η_KL(W)` for a DMC `W`. -/
noncomputable def sdpiKL {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) : ℝ :=
  sSup { r : ℝ | ∃ (P Q : ProbDist α),
    AbsCont P Q ∧ klDivergence P Q > 0 ∧
    r = klDivergence (W.joint P).snd (W.joint Q).snd / klDivergence P Q }

/-- χ²-contraction coefficient `η_χ²(W)` for a DMC `W`. -/
noncomputable def sdpiChiSq {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) : ℝ :=
  sSup { r : ℝ | ∃ (P Q : ProbDist α),
    (∀ a, 0 < Q.pmf a) ∧ chiSqDivergence P Q > 0 ∧
    r = chiSqDivergence (W.joint P).snd (W.joint Q).snd / chiSqDivergence P Q }

/-- Hypercontractivity ribbon `R(P_XY)` of a bipartite source `(X, Y)` via Nair's (2014) exact
    KL characterization: pairs `(p, q)` with `1 < p ≤ q` such that for every joint distribution
    `Q ≪ P`, `(1 / p) D(Q_X ‖ P_X) + (1 - 1 / q) D(Q_Y ‖ P_Y) ≤ D(Q ‖ P)`. -/
def inHypercontractivityRibbon {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) (p q : ℝ) : Prop :=
  1 < p ∧ p ≤ q ∧
  ∀ (Q : ProbDist (X × Y)),
    AbsCont Q P →
    (1 / p) * klDivergence Q.fst P.fst + (1 - 1 / q) * klDivergence Q.snd P.snd ≤
      klDivergence Q P

/-- A monotone secret sharing access structure on `n` participants. -/
structure AccessStructure (n : ℕ) where
  qualified : Finset (Fin n) → Prop
  monotone : ∀ A B, A ⊆ B → qualified A → qualified B
  nonempty_qualified : qualified Finset.univ
  empty_unqualified : ¬ qualified ∅

/-- Information ratio `max_i H(S_i) / H(S_0)` of a perfect secret sharing scheme for `Γ`. -/
noncomputable def optimalSecretSharingRatio {n : ℕ} (Γ : AccessStructure n) : ℝ :=
  sInf { r : ℝ | ∃ (k : ℕ) (P : ProbDist (Fin (n + 1) → Fin k)),
    let H (S : Finset (Fin (n + 1))) : ℝ := subsetEntropyVec P S
    0 < H {0} ∧
    (∀ A : Finset (Fin n),
      let A' : Finset (Fin (n + 1)) := A.map ⟨Fin.succ, Fin.succ_injective n⟩
      (Γ.qualified A → H (insert 0 A') - H A' = 0) ∧
      (¬ Γ.qualified A → H (insert 0 A') - H A' = H {0})) ∧
    ∀ i : Fin n, H {i.succ} / H {0} ≤ r }

/-- An `ε`-locally differentially private (LDP) channel `Q : α → β`. -/
def IsEpsLDP {α β : Type*} [Fintype α] [Fintype β] (ε : ℝ) (Q : DMC α β) : Prop :=
  ∀ x x' : α, ∀ y : β, Q.trans x y ≤ Real.exp ε * Q.trans x' y

/-- Minimax KL risk of `ε`-LDP distribution estimation on alphabet size `k` with `n` samples.
    Requires full-support output estimators (`∀ y a, 0 < (est y).pmf a`) so every worst-case
    KL divergence `D(P ‖ est y)` is genuinely finite (preventing negative `log2(p/0) = 0` junk). -/
noncomputable def ldpMinimaxKLRisk (k n : ℕ) (ε : ℝ) : ℝ :=
  sInf { R : ℝ | ∃ (m : ℕ) (Q : DMC (Fin k) (Fin m))
    (est : (Fin n → Fin m) → ProbDist (Fin k)),
    IsEpsLDP ε Q ∧
    (∀ (y : Fin n → Fin m) (a : Fin k), 0 < (est y).pmf a) ∧
    ∀ P : ProbDist (Fin k),
      let Py := (Q.joint P).snd
      (∑ y : Fin n → Fin m, (∏ i : Fin n, Py.pmf (y i)) * klDivergence P (est y)) ≤ R }

/-- Minimax KL risk of discrete distribution estimation (without privacy) for alphabet size `k`
    and `n` i.i.d. samples, over full-support estimators (`∀ x a, 0 < (est x).pmf a`). -/
noncomputable def minimaxKLRisk (k n : ℕ) : ℝ :=
  sInf { R : ℝ | ∃ (est : (Fin n → Fin k) → ProbDist (Fin k)),
    (∀ (x : Fin n → Fin k) (a : Fin k), 0 < (est x).pmf a) ∧
    ∀ P : ProbDist (Fin k),
      (∑ x : Fin n → Fin k, (∏ i : Fin n, P.pmf (x i)) * klDivergence P (est x)) ≤ R }

end InfoTheory
