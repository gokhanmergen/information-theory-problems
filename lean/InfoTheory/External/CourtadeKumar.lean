import InfoTheory.External.GeneralCKStatement
import InfoTheory.Problems.CourtadeKumar

/-!
# Courtade–Kumar: bridge from the external Lean proof's target to the frozen catalog statement

The Courtade–Kumar most-informative-Boolean-function conjecture was proved in September 2026
(Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, arXiv:2609.24931). That proof is
formalised in Lean 4 in the public repository
`github.com/dpwoodru/general-courtade-kumar-lean`. Its final theorem

  `GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar`

is checked there (`FinalCheck.lean`, `#guard_msgs`) to depend only on `propext`,
`Classical.choice` and `Quot.sound`. That development has about 45,500 modules on Lean
`v4.33.1`, while this repository is on `v4.36.0`, so it cannot be imported here.

This file closes the remaining gap: the target proposition upstream is **not** the catalog's
frozen `InfoTheory.Problems.CourtadeKumar.Statement`. It was written independently, with its own
definitions of entropy, the noise kernel and mutual information. We prove, against an unmodified
copy of the upstream statement file (`InfoTheory/External/GeneralCKStatement.lean`, byte-identical
to `GeneralCK/Statement.lean` at upstream commit
`68cd46b433a1003f06a5c3ee39df2af1a4a314e1`, SHA-256
`698272477382649febc3cd331c9c15f0e036285e1d8180f6107f76b115479342`):

* `mutualInfoBSC_eq`: the two formalisations of `I(f(X); Y)` are **equal** for every
  `n`, every Boolean `f` and every crossover probability `α ∈ [0, 1]`;
* `binaryEntropy_eq`: the two binary entropies agree on `[0, 1]`;
* `statement_of_generalCourtadeKumar : GeneralCK.GeneralCourtadeKumar → Statement`.

Together with the upstream kernel check, this gives a two-hop machine-checked chain from the
published proof to the catalog's frozen statement. The chain is not a single kernel check: the
upstream theorem is trusted through its own repository's build, not replayed here.
-/

open scoped BigOperators

namespace InfoTheory.External.CourtadeKumar

open InfoTheory

/-- The catalog's entropy summand is `negMulLog / log 2` on nonnegative reals. -/
theorem negPLogP_eq_negMulLog_div {p : ℝ} (hp : 0 ≤ p) :
    negPLogP p = Real.negMulLog p / Real.log 2 := by
  unfold negPLogP log2
  split_ifs with h
  · have : p = 0 := le_antisymm h hp
    subst this
    simp
  · simp only [Real.negMulLog]
    ring

/-- The catalog's Shannon entropy equals the upstream `GeneralCK.entropy` of the mass function. -/
theorem shannonEntropy_eq_entropy {α : Type*} [Fintype α] (P : ProbDist α) :
    shannonEntropy P = GeneralCK.entropy P.pmf := by
  unfold shannonEntropy GeneralCK.entropy
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun a _ => negPLogP_eq_negMulLog_div (P.nonneg a))

/-- The two binary entropies agree on `[0, 1]`. -/
theorem binaryEntropy_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    binaryEntropy p = GeneralCK.H p := by
  unfold binaryEntropy GeneralCK.H
  rw [negPLogP_eq_negMulLog_div h0, negPLogP_eq_negMulLog_div (by linarith),
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_div]

/-- The joint law of `(f(X), Y)` in the catalog is the upstream `jointMass`. -/
theorem joint_pmf_eq (n : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (f : (Fin n → Bool) → Bool) (b : Bool) (y : Fin n → Bool) :
    ((bscNoisyPair n α h0 h1).map (fun xy => (f xy.1, xy.2))).pmf (b, y) =
      GeneralCK.jointMass f α b y := by
  classical
  -- the uniform mass
  have hcard : (1 : ℝ) / (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ (-(n : ℤ)) := by
    simp [Fintype.card_bool, Fintype.card_fin, zpow_neg, zpow_natCast]
  set c : (Fin n → Bool) → (Fin n → Bool) → ℝ :=
    fun x y' => (1 : ℝ) / (Fintype.card (Fin n → Bool) : ℝ) * GeneralCK.noiseKernel α x y'
    with hc
  have hpmf : ∀ xy : (Fin n → Bool) × (Fin n → Bool),
      (bscNoisyPair n α h0 h1).pmf xy = c xy.1 xy.2 := by
    intro xy
    simp only [bscNoisyPair, DMC.joint, DMC.power, bsc, ProbDist.uniform, hc,
      GeneralCK.noiseKernel]
  have inner : ∀ x : Fin n → Bool,
      (∑ y' : Fin n → Bool,
        (if (f x, y') = (b, y) then c x y' else 0)) = if f x = b then c x y else 0 := by
    intro x
    rw [Finset.sum_eq_single y]
    · by_cases hfx : f x = b <;> simp [hfx]
    · intro y' _ hy'
      have h : (f x, y') ≠ (b, y) := fun h => hy' (Prod.mk.inj h).2
      simp [h]
    · intro h
      exact absurd (Finset.mem_univ y) h
  have lhs : ((bscNoisyPair n α h0 h1).map (fun xy => (f xy.1, xy.2))).pmf (b, y) =
      ∑ x : Fin n → Bool, (if f x = b then c x y else 0) := by
    simp only [ProbDist.map]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← inner x]
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    rw [hpmf (x, y')]
    by_cases h : (f x, y') = (b, y) <;> simp [h]
  rw [lhs, GeneralCK.jointMass, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hc, hcard]
  split_ifs <;> simp

/-- **The two formalisations of `I(f(X); Y)` coincide**, for every `n`, every Boolean `f`
and every crossover probability `α ∈ [0, 1]`. -/
theorem mutualInfoBSC_eq (n : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (f : (Fin n → Bool) → Bool) :
    mutualInfoBSC n α h0 h1 f = GeneralCK.mutualInformation f α := by
  have hP := joint_pmf_eq n α h0 h1 f
  set P := (bscNoisyPair n α h0 h1).map (fun xy => (f xy.1, xy.2)) with hPdef
  have hfst : P.fst.pmf = fun b => ∑ y, GeneralCK.jointMass f α b y := by
    funext b
    simp only [ProbDist.fst, hP]
  have hsnd : P.snd.pmf = fun y => ∑ b, GeneralCK.jointMass f α b y := by
    funext y
    simp only [ProbDist.snd, hP]
  have hjoint : P.pmf = fun byPair : Bool × (Fin n → Bool) =>
      GeneralCK.jointMass f α byPair.1 byPair.2 := by
    funext p
    exact hP p.1 p.2
  show mutualInfo P = _
  unfold mutualInfo GeneralCK.mutualInformation
  rw [shannonEntropy_eq_entropy, shannonEntropy_eq_entropy, shannonEntropy_eq_entropy,
    hfst, hsnd, hjoint]

/-- **Bridge.** The target proposition of the external Lean proof
(`dpwoodru/general-courtade-kumar-lean`) implies the catalog's frozen Courtade–Kumar
statement. -/
theorem statement_of_generalCourtadeKumar (h : GeneralCK.GeneralCourtadeKumar) :
    InfoTheory.Problems.CourtadeKumar.Statement := by
  intro n α h0 h1 f
  rw [mutualInfoBSC_eq, binaryEntropy_eq h0.le (by linarith)]
  exact h n f α h0.le (by linarith)

end InfoTheory.External.CourtadeKumar
