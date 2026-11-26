import InfoTheory.Bridge.CoverThomas
import InfoTheory.Known.Entropy

/-!
# Channel Coding Toolkit (Cover & Thomas Ch. 7; El Gamal–Kim Ch. 2–3)

Purely additive, kernel-verified foundational theorems for channel coding built on top of
`InfoTheory.Bridge.CoverThomas` and `InfoTheory.Core.Channels`:

1. **Jointly Weakly Typical Set & Joint AEP (Cover & Thomas §7.6, Theorem 7.6.1; El Gamal–Kim §2.5)**:
   - `jointTypicalSet`, `jointIidDist`
   - `jointIidDist_prob_not_typical_le` (explicit `O(1 / (n ε²))` union + Chebyshev tail bound)
   - `joint_aep_prob_tendsto_one` (`P^n(A_ε^(n)) ≥ 1 - δ` for all sufficiently large `n`)
   - `jointTypicalSet_card_le` and `jointTypicalSet_card_ge` (`|A_ε^(n)| ≈ 2^(n H(X, Y))`)
   - `jointTypicalSet_indep_prob_le` and `jointTypicalSet_indep_prob_ge`
     (Packing Lemma core: independent pair probability `≈ 2^(-n I(X; Y))`)

2. **Multi-letter DMC Converse Tensorization (Cover & Thomas §7.9, Lemma 7.9.2)**:
   - `shannonEntropy_pi_le_sum` (`H(X_1, …, X_n) ≤ ∑_i H(X_i)`)
   - `piProdDist` and `shannonEntropy_piProdDist` (`H(∏_i Q_i) = ∑_i H(Q_i)`)
   - `dmc_joint_shannonEntropy` (`H(X, Y) = H(X) + ∑_x P(x) H(W(· | x))`)
   - `dmcPower_mutualInfo_le_sum` (`I(X^n; Y^n) ≤ ∑_i I(X_i; Y_i)` for a memoryless channel `W^n`)
   - `dmc_mutualInfo_le_capacity` and `dmcPower_mutualInfo_le_mul_capacity` (`I(X^n; Y^n) ≤ n C(W)`)

3. **Weak Converse for Block Codes over DMCs (Cover & Thomas §7.9)**:
   - `dmc_blockCode_weak_converse` (general finite message type `M` with `2 ≤ |M|`:
     `log₂ |M| ≤ h(P_e) + P_e log₂(|M| - 1) + n C(W)`)
   - `dmcAvgError_weak_converse` (specialized directly to `dmcAvgError` on `Fin M`)
   - `dmcAvgError_rate_converse` (`(1 - P_e) · (log₂ M / n) ≤ C(W) + 1 / n`)

All theorems leave `Core/`, `Problems/`, `Bridge/Mathlib.lean`, `Bridge/CoverThomas.lean`,
`STATEMENT_LOCK.json`, and `Known/` untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Jointly Weakly Typical Set & Joint AEP (Cover & Thomas §7.6, Theorem 7.6.1) -/

section JointAEP

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Canonical bijection between pairs of `n`-tuples and `n`-tuples of pairs. -/
def zipEquiv (α β : Type*) (n : ℕ) : ((Fin n → α) × (Fin n → β)) ≃ (Fin n → α × β) where
  toFun := fun xy i => (xy.1 i, xy.2 i)
  invFun := fun z => (fun i => (z i).1, fun i => (z i).2)
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- The `n`-fold i.i.d. joint distribution `P^n` on `(Fin n → α) × (Fin n → β)`. -/
def jointIidDist (P : ProbDist (α × β)) (n : ℕ) : ProbDist ((Fin n → α) × (Fin n → β)) where
  pmf := fun xy => ∏ i : Fin n, P.pmf (xy.1 i, xy.2 i)
  nonneg := fun xy => Finset.prod_nonneg fun i _ => P.nonneg (xy.1 i, xy.2 i)
  sum_one := by
    have h := Fintype.sum_equiv (zipEquiv α β n)
      (fun xy => ∏ i : Fin n, P.pmf (xy.1 i, xy.2 i))
      (fun z => (iidDist P n).pmf z)
      (fun _ => rfl)
    rw [h, (iidDist P n).sum_one]

@[simp]
lemma jointIidDist_pmf (P : ProbDist (α × β)) (n : ℕ) (xy : (Fin n → α) × (Fin n → β)) :
    (jointIidDist P n).pmf xy = (iidDist P n).pmf (zipEquiv α β n xy) := rfl

lemma jointIidDist_fst (P : ProbDist (α × β)) (n : ℕ) :
    (jointIidDist P n).fst = iidDist P.fst n := by
  unfold ProbDist.fst jointIidDist iidDist
  congr
  funext x
  dsimp only
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : β) => P.pmf (x i, b))]

lemma jointIidDist_snd (P : ProbDist (α × β)) (n : ℕ) :
    (jointIidDist P n).snd = iidDist P.snd n := by
  unfold ProbDist.snd jointIidDist iidDist
  congr
  funext y
  dsimp only
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : α) => P.pmf (a, y i))]

/-- **Jointly Weakly Typical Set** `A_ε^(n)` (Cover & Thomas, Definition in §7.6; El Gamal–Kim §2.5):
    pairs `(x, y)` such that `x ∈ A_ε^(n)(X)`, `y ∈ A_ε^(n)(Y)`, and `(x, y) ∈ A_ε^(n)(X, Y)`. -/
noncomputable def jointTypicalSet (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ) :
    Finset ((Fin n → α) × (Fin n → β)) := by
  classical
  exact Finset.univ.filter fun xy =>
    xy.1 ∈ weakTypicalSet P.fst n ε ∧
    xy.2 ∈ weakTypicalSet P.snd n ε ∧
    (fun i => (xy.1 i, xy.2 i)) ∈ weakTypicalSet P n ε

lemma mem_jointTypicalSet {P : ProbDist (α × β)} {n : ℕ} {ε : ℝ}
    {xy : (Fin n → α) × (Fin n → β)} :
    xy ∈ jointTypicalSet P n ε ↔
      xy.1 ∈ weakTypicalSet P.fst n ε ∧
      xy.2 ∈ weakTypicalSet P.snd n ε ∧
      (fun i => (xy.1 i, xy.2 i)) ∈ weakTypicalSet P n ε := by
  classical
  simp [jointTypicalSet]

/-- **Explicit Chebyshev–Union Tail Bound for the Joint AEP**:
    for `n ≥ 1` and `ε > 0`,
    `1 - P^n(A_ε^(n)) ≤ (V(P_X) + V(P_Y) + V(P_{XY})) / (n ε²)`. -/
theorem jointIidDist_prob_not_typical_le (P : ProbDist (α × β)) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy ≤
      (varentropy P.fst + varentropy P.snd + varentropy P) / ((n : ℝ) * ε ^ 2) := by
  classical
  let p := (jointIidDist P n).pmf
  have hcomp_eq : 1 - ∑ xy ∈ jointTypicalSet P n ε, p xy =
      ∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ jointTypicalSet P n ε then p xy else 0 := by
    have hsplit : ∑ xy : (Fin n → α) × (Fin n → β), p xy =
        (∑ xy : (Fin n → α) × (Fin n → β), if xy ∈ jointTypicalSet P n ε then p xy else 0) +
        (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ jointTypicalSet P n ε then p xy else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun xy _ => by by_cases h : xy ∈ jointTypicalSet P n ε <;> simp [h]
    rw [(jointIidDist P n).sum_one] at hsplit
    have hmem : (∑ xy : (Fin n → α) × (Fin n → β), if xy ∈ jointTypicalSet P n ε then p xy else 0) =
        ∑ xy ∈ jointTypicalSet P n ε, p xy := by
      rw [← Finset.sum_filter]
      congr 1; ext xy; simp
    linarith
  have hunion : ∀ xy : (Fin n → α) × (Fin n → β),
      (if xy ∉ jointTypicalSet P n ε then p xy else 0) ≤
        (if xy.1 ∉ weakTypicalSet P.fst n ε then p xy else 0) +
        (if xy.2 ∉ weakTypicalSet P.snd n ε then p xy else 0) +
        (if zipEquiv α β n xy ∉ weakTypicalSet P n ε then p xy else 0) := by
    intro xy
    have hp0 : 0 ≤ p xy := (jointIidDist P n).nonneg xy
    by_cases h1 : xy.1 ∈ weakTypicalSet P.fst n ε
    · by_cases h2 : xy.2 ∈ weakTypicalSet P.snd n ε
      · by_cases h3 : zipEquiv α β n xy ∈ weakTypicalSet P n ε
        · have hmem : xy ∈ jointTypicalSet P n ε := mem_jointTypicalSet.mpr ⟨h1, h2, h3⟩
          simp [hmem, h1, h2, h3]
        · simp [h1, h2, h3]
          split_ifs <;> linarith
      · simp only [h1, h2, not_true_eq_false, not_false_eq_true, ↓reduceIte]
        split_ifs <;> linarith
    · simp only [h1, not_false_eq_true, ↓reduceIte]
      split_ifs <;> linarith
  have hsum_le : (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ jointTypicalSet P n ε then p xy else 0) ≤
      (∑ xy : (Fin n → α) × (Fin n → β), if xy.1 ∉ weakTypicalSet P.fst n ε then p xy else 0) +
      (∑ xy : (Fin n → α) × (Fin n → β), if xy.2 ∉ weakTypicalSet P.snd n ε then p xy else 0) +
      (∑ xy : (Fin n → α) × (Fin n → β), if zipEquiv α β n xy ∉ weakTypicalSet P n ε then p xy else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun xy _ => hunion xy
  have hfst_sum :
      (∑ xy : (Fin n → α) × (Fin n → β), if xy.1 ∉ weakTypicalSet P.fst n ε then p xy else 0) =
        1 - ∑ x ∈ weakTypicalSet P.fst n ε, (iidDist P.fst n).pmf x := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x : Fin n → α,
        (∑ y : Fin n → β, if x ∉ weakTypicalSet P.fst n ε then p (x, y) else 0) =
          if x ∉ weakTypicalSet P.fst n ε then (iidDist P.fst n).pmf x else 0 := fun x => by
      by_cases hx : x ∉ weakTypicalSet P.fst n ε
      · simp only [hx]
        change (jointIidDist P n).fst.pmf x = (iidDist P.fst n).pmf x
        rw [jointIidDist_fst]
      · simp [hx]
    simp_rw [hinner]
    have hsplit : ∑ x : Fin n → α, (iidDist P.fst n).pmf x =
        (∑ x : Fin n → α, if x ∈ weakTypicalSet P.fst n ε then (iidDist P.fst n).pmf x else 0) +
        (∑ x : Fin n → α, if x ∉ weakTypicalSet P.fst n ε then (iidDist P.fst n).pmf x else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by by_cases h : x ∈ weakTypicalSet P.fst n ε <;> simp [h]
    rw [(iidDist P.fst n).sum_one] at hsplit
    have hmem : (∑ x : Fin n → α, if x ∈ weakTypicalSet P.fst n ε then (iidDist P.fst n).pmf x else 0) =
        ∑ x ∈ weakTypicalSet P.fst n ε, (iidDist P.fst n).pmf x := by
      rw [← Finset.sum_filter]; congr 1; ext x; simp
    linarith
  have hsnd_sum :
      (∑ xy : (Fin n → α) × (Fin n → β), if xy.2 ∉ weakTypicalSet P.snd n ε then p xy else 0) =
        1 - ∑ y ∈ weakTypicalSet P.snd n ε, (iidDist P.snd n).pmf y := by
    rw [Fintype.sum_prod_type_right]
    have hinner : ∀ y : Fin n → β,
        (∑ x : Fin n → α, if y ∉ weakTypicalSet P.snd n ε then p (x, y) else 0) =
          if y ∉ weakTypicalSet P.snd n ε then (iidDist P.snd n).pmf y else 0 := fun y => by
      by_cases hy : y ∉ weakTypicalSet P.snd n ε
      · simp only [hy]
        change (jointIidDist P n).snd.pmf y = (iidDist P.snd n).pmf y
        rw [jointIidDist_snd]
      · simp [hy]
    simp_rw [hinner]
    have hsplit : ∑ y : Fin n → β, (iidDist P.snd n).pmf y =
        (∑ y : Fin n → β, if y ∈ weakTypicalSet P.snd n ε then (iidDist P.snd n).pmf y else 0) +
        (∑ y : Fin n → β, if y ∉ weakTypicalSet P.snd n ε then (iidDist P.snd n).pmf y else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => by by_cases h : y ∈ weakTypicalSet P.snd n ε <;> simp [h]
    rw [(iidDist P.snd n).sum_one] at hsplit
    have hmem : (∑ y : Fin n → β, if y ∈ weakTypicalSet P.snd n ε then (iidDist P.snd n).pmf y else 0) =
        ∑ y ∈ weakTypicalSet P.snd n ε, (iidDist P.snd n).pmf y := by
      rw [← Finset.sum_filter]; congr 1; ext y; simp
    linarith
  have hjoint_sum :
      (∑ xy : (Fin n → α) × (Fin n → β), if zipEquiv α β n xy ∉ weakTypicalSet P n ε then p xy else 0) =
        1 - ∑ z ∈ weakTypicalSet P n ε, (iidDist P n).pmf z := by
    have heq := Fintype.sum_equiv (zipEquiv α β n)
      (fun xy => if zipEquiv α β n xy ∉ weakTypicalSet P n ε then p xy else 0)
      (fun z => if z ∉ weakTypicalSet P n ε then (iidDist P n).pmf z else 0)
      (fun _ => rfl)
    rw [heq]
    have hsplit : ∑ z : Fin n → α × β, (iidDist P n).pmf z =
        (∑ z : Fin n → α × β, if z ∈ weakTypicalSet P n ε then (iidDist P n).pmf z else 0) +
        (∑ z : Fin n → α × β, if z ∉ weakTypicalSet P n ε then (iidDist P n).pmf z else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => by by_cases h : z ∈ weakTypicalSet P n ε <;> simp [h]
    rw [(iidDist P n).sum_one] at hsplit
    have hmem : (∑ z : Fin n → α × β, if z ∈ weakTypicalSet P n ε then (iidDist P n).pmf z else 0) =
        ∑ z ∈ weakTypicalSet P n ε, (iidDist P n).pmf z := by
      rw [← Finset.sum_filter]; congr 1; ext z; simp
    linarith
  have ht1 := iidDist_prob_not_typical_le P.fst hn hε
  have ht2 := iidDist_prob_not_typical_le P.snd hn hε
  have ht3 := iidDist_prob_not_typical_le P hn hε
  rw [hcomp_eq]
  rw [hfst_sum, hsnd_sum, hjoint_sum] at hsum_le
  have hadd : varentropy P.fst / ((n : ℝ) * ε ^ 2) +
      varentropy P.snd / ((n : ℝ) * ε ^ 2) +
      varentropy P / ((n : ℝ) * ε ^ 2) =
      (varentropy P.fst + varentropy P.snd + varentropy P) / ((n : ℝ) * ε ^ 2) := by ring
  linarith

/-- **Joint AEP Theorem (1): Typical Probability Approaches 1**
    (Cover & Thomas, Theorem 7.6.1(1); El Gamal–Kim §2.5):
    for all `ε > 0` and `δ > 0`, there exists `N` such that for all `n ≥ N`,
    `P^n(A_ε^(n)) ≥ 1 - δ`. -/
theorem joint_aep_prob_tendsto_one (P : ProbDist (α × β)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, 1 - δ ≤ ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy := by
  let V := varentropy P.fst + varentropy P.snd + varentropy P
  obtain ⟨N, hN⟩ := exists_nat_gt (V / (δ * ε ^ 2))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hn)
  have htail := jointIidDist_prob_not_typical_le P hn_pos hε
  have hn_gt : V / (δ * ε ^ 2) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast le_trans (le_max_left N 1) hn)
  have hbound : V / ((n : ℝ) * ε ^ 2) ≤ δ := by
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [div_le_iff₀ (by positivity)]
    have h1 := (div_lt_iff₀ (by positivity : 0 < δ * ε ^ 2)).mp hn_gt
    linarith
  change 1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy ≤ V / ((n : ℝ) * ε ^ 2) at htail
  linarith

/-- **Joint AEP Theorem (2a): Upper Cardinality Bound**
    (Cover & Thomas, Theorem 7.6.1(2)):
    `|A_ε^(n)| ≤ 2^(n (H(X, Y) + ε))`. -/
theorem jointTypicalSet_card_le (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ) :
    ((jointTypicalSet P n ε).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) := by
  classical
  have hcard_le : (jointTypicalSet P n ε).card ≤ (weakTypicalSet P n ε).card := by
    refine Finset.card_le_card_of_injOn (zipEquiv α β n) ?_ ?_
    · intro xy hxy
      exact (mem_jointTypicalSet.mp hxy).2.2
    · intro xy₁ _ xy₂ _ h
      exact (zipEquiv α β n).injective h
  exact le_trans (by exact_mod_cast hcard_le) (weakTypicalSet_card_le P n ε)

/-- **Joint AEP Theorem (2b): Lower Cardinality Bound**
    (Cover & Thomas, Theorem 7.6.1(2)):
    for all `ε > 0` and `δ > 0`, eventually
    `(1 - δ) * 2^(n (H(X, Y) - ε)) ≤ |A_ε^(n)|`. -/
theorem jointTypicalSet_card_ge (P : ProbDist (α × β)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (1 - δ) * (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε)) ≤
        ((jointTypicalSet P n ε).card : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := joint_aep_prob_tendsto_one P hε hδ
  refine ⟨N, fun n hn => ?_⟩
  have hprob := hN n hn
  have hup : ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy ≤
      ((jointTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := by
    calc ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy
      _ ≤ ∑ _xy ∈ jointTypicalSet P n ε, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) :=
          Finset.sum_le_sum fun xy hxy => by
            have hz := (mem_jointTypicalSet.mp hxy).2.2
            simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz
            exact hz.2
      _ = ((jointTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : 1 - δ ≤ ((jointTypicalSet P n ε).card : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := le_trans hprob hup
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) *
      (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpow_pos)
  rw [mul_assoc, hmul, mul_one] at h2
  exact h2

/-- **Joint AEP Theorem (3a): Independent Pair Probability Upper Bound (Packing Lemma Core)**
    (Cover & Thomas, Theorem 7.6.1(3); El Gamal–Kim §2.5):
    `(P_X^n × P_Y^n)(A_ε^(n)) ≤ 2^(-n (I(X; Y) - 3ε))`. -/
theorem jointTypicalSet_indep_prob_le (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ) :
    ∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P - 3 * ε))) := by
  classical
  have hterm : ∀ xy ∈ jointTypicalSet P n ε,
      ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) := by
    intro xy hxy
    have hx := (mem_jointTypicalSet.mp hxy).1
    have hy := (mem_jointTypicalSet.mp hxy).2.1
    simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact mul_le_mul hx.2 hy.2 ((iidDist P.snd n).nonneg xy.2)
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  have hsum : ∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy ≤
      ((jointTypicalSet P n ε).card : ℝ) *
        ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
         (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε)))) := by
    calc ∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy
      _ ≤ ∑ _xy ∈ jointTypicalSet P n ε,
            ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
             (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε)))) := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε))) :=
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  calc ∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy
    _ ≤ ((jointTypicalSet P n ε).card : ℝ) *
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε)))) := hsum
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) *
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst - ε))) *
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd - ε)))) :=
        mul_le_mul_of_nonneg_right (jointTypicalSet_card_le P n ε) hpow_nonneg
    _ = (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P - 3 * ε))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        unfold mutualInfo
        ring

/-- **Joint AEP Theorem (3b): Independent Pair Probability Lower Bound**
    (Cover & Thomas, Theorem 7.6.1(3)):
    for all `ε > 0` and `δ > 0`, eventually
    `(1 - δ) * 2^(-n (I(X; Y) + 3ε)) ≤ (P_X^n × P_Y^n)(A_ε^(n))`. -/
theorem jointTypicalSet_indep_prob_ge (P : ProbDist (α × β)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (1 - δ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P + 3 * ε))) ≤
        ∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy := by
  classical
  obtain ⟨N, hN⟩ := jointTypicalSet_card_ge P hε hδ
  refine ⟨N, fun n hn => ?_⟩
  have hcard := hN n hn
  have hterm : ∀ xy ∈ jointTypicalSet P n ε,
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε))) ≤
        ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy := by
    intro xy hxy
    have hx := (mem_jointTypicalSet.mp hxy).1
    have hy := (mem_jointTypicalSet.mp hxy).2.1
    simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact mul_le_mul hx.1 hy.1 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      ((iidDist P.fst n).nonneg xy.1)
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε))) :=
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  calc (1 - δ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P + 3 * ε)))
    _ = ((1 - δ) * (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε))) *
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε)))) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2
        unfold mutualInfo
        ring
    _ ≤ ((jointTypicalSet P n ε).card : ℝ) *
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε)))) :=
        mul_le_mul_of_nonneg_right hcard hpow_nonneg
    _ = ∑ _xy ∈ jointTypicalSet P n ε,
          ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
           (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy :=
        Finset.sum_le_sum hterm

end JointAEP

/-! ### 2. Multi-letter DMC Converse Tensorization (Cover & Thomas §7.9, Lemma 7.9.2) -/

section Tensorization

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Head-tail equivalence `(Fin (n + 1) → α) ≃ α × (Fin n → α)`. -/
def piSuccEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun := fun x => (x 0, fun i => x i.succ)
  invFun := fun p => Fin.cons p.1 p.2
  left_inv := fun x => by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv := fun ⟨a, xs⟩ => by
    ext <;> simp

/-- **Subadditivity of Joint Entropy over `n` Variables** (Cover & Thomas, Corollary to Thm. 2.6.5):
    `H(X_1, …, X_n) ≤ ∑_i H(X_i)`. -/
theorem shannonEntropy_pi_le_sum (n : ℕ) (P : ProbDist (Fin n → α)) :
    shannonEntropy P ≤ ∑ i : Fin n, shannonEntropy (P.map (fun x => x i)) := by
  induction n with
  | zero =>
    have hcard : Fintype.card (Fin 0 → α) = 1 := Fintype.card_unique
    have hle := shannonEntropy_le_log2_card P
    rw [hcard] at hle
    simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
    simpa using hle
  | succ n ih =>
    classical
    let e := piSuccEquiv α n
    have heq : shannonEntropy P = shannonEntropy (P.map e) := (shannonEntropy_map_equiv e P).symm
    have hsub := shannonEntropy_subadd (P.map e)
    have hfst : (P.map e).fst = P.map (fun x => x 0) := by
      unfold ProbDist.fst ProbDist.map
      congr; funext a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (fun i : Fin n => x i.succ)]
      · simp [e, piSuccEquiv]
      · intro xs _ hne
        simp [e, piSuccEquiv, hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hsnd : (P.map e).snd = P.map (fun x (i : Fin n) => x i.succ) := by
      unfold ProbDist.snd ProbDist.map
      congr; funext xs
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single (x 0)]
      · simp [e, piSuccEquiv]
      · intro a _ hne
        simp [e, piSuccEquiv, hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hih := ih (P.map (fun x (i : Fin n) => x i.succ))
    have hcomp : ∀ i : Fin n,
        (P.map (fun x (j : Fin n) => x j.succ)).map (fun xs => xs i) = P.map (fun x => x i.succ) := by
      intro i
      rw [map_comp_eq]; rfl
    simp_rw [hcomp] at hih
    rw [heq, Fin.sum_univ_succ]
    rw [hfst, hsnd] at hsub
    linarith

/-- Independent product distribution `∏_i Q_i` on `Fin n → β`. -/
def piProdDist {n : ℕ} (Q : Fin n → ProbDist β) : ProbDist (Fin n → β) where
  pmf := fun y => ∏ i : Fin n, (Q i).pmf (y i)
  nonneg := fun y => Finset.prod_nonneg fun i _ => (Q i).nonneg (y i)
  sum_one := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => (Q i).sum_one

/-- **Additivity of Entropy for Independent Product Distributions**:
    `H(∏_i Q_i) = ∑_i H(Q_i)`. -/
theorem shannonEntropy_piProdDist (n : ℕ) (Q : Fin n → ProbDist β) :
    shannonEntropy (piProdDist Q) = ∑ i : Fin n, shannonEntropy (Q i) := by
  induction n with
  | zero =>
    have hcard : Fintype.card (Fin 0 → β) = 1 := Fintype.card_unique
    have hle := shannonEntropy_le_log2_card (piProdDist Q)
    have hge := shannonEntropy_nonneg (piProdDist Q)
    rw [hcard] at hle
    simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
    simp [le_antisymm hle hge]
  | succ n ih =>
    classical
    let e := piSuccEquiv β n
    have hmap : (piProdDist Q).map e = (Q 0).prod (piProdDist (fun i => Q i.succ)) := by
      unfold ProbDist.map ProbDist.prod piProdDist
      congr; funext ⟨b, ys⟩
      rw [Finset.sum_eq_single (e.symm (b, ys))]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte]
        rw [Fin.prod_univ_succ]
        simp [e, piSuccEquiv]
      · intro y _ hne
        have : e y ≠ (b, ys) := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← shannonEntropy_map_equiv e (piProdDist Q), hmap, shannonEntropy_prod,
      ih (fun i => Q i.succ), Fin.sum_univ_succ]

/-- Elementary product identity for `-p log₂ p`:
    `negPLogP (p * q) = p * negPLogP q + q * negPLogP p` for `p, q ≥ 0`. -/
lemma negPLogP_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    negPLogP (p * q) = p * negPLogP q + q * negPLogP p := by
  by_cases hp0 : p ≤ 0
  · have : p = 0 := le_antisymm hp0 hp
    simp [this, negPLogP]
  · by_cases hq0 : q ≤ 0
    · have : q = 0 := le_antisymm hq0 hq
      simp [this, negPLogP]
    · have hppos : 0 < p := lt_of_not_ge hp0
      have hqpos : 0 < q := lt_of_not_ge hq0
      have hpqpos : 0 < p * q := mul_pos hppos hqpos
      simp only [negPLogP, ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hpqpos)),
        ite_eq_right_iff.mpr (fun h => absurd h hq0),
        ite_eq_right_iff.mpr (fun h => absurd h hp0)]
      rw [log2_mul_pos hppos hqpos]
      ring

/-- First marginal of `W.joint P` equals the input distribution `P`. -/
lemma dmc_joint_fst (W : DMC α β) (P : ProbDist α) : (W.joint P).fst = P := by
  unfold ProbDist.fst DMC.joint
  congr; funext x; dsimp only
  rw [← Finset.mul_sum, W.sum_one x, mul_one]

/-- **Chain Rule for a DMC**:
    `H(X, Y) = H(X) + ∑_x P(x) H(W(· | x))`. -/
theorem dmc_joint_shannonEntropy (W : DMC α β) (P : ProbDist α) :
    shannonEntropy (W.joint P) =
      shannonEntropy P + ∑ x : α, P.pmf x * shannonEntropy (dmcRow W x) := by
  unfold shannonEntropy DMC.joint dmcRow
  rw [Fintype.sum_prod_type]
  have hterm : ∀ x : α, ∑ y : β, negPLogP (P.pmf x * W.trans x y) =
      negPLogP (P.pmf x) + P.pmf x * ∑ y : β, negPLogP (W.trans x y) := by
    intro x
    simp_rw [negPLogP_mul (P.nonneg x) (W.nonneg x _), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, W.sum_one x, one_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]

/-- Change of variables for expectations under pushforward distributions:
    `∑_x P(x) f(g(x)) = ∑_a (P.map g)(a) f(a)`. -/
lemma sum_pmf_mul_comp (P : ProbDist α) (g : α → β) (f : β → ℝ) :
    ∑ x : α, P.pmf x * f (g x) = ∑ b : β, (P.map g).pmf b * f b := by
  classical
  unfold ProbDist.map; dsimp only
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (g x)]
  · simp
  · intro b _ hne; simp [hne.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Marginal output distribution at coordinate `i` of a memoryless product channel `W^n`
    equals the single-letter output distribution for marginal input `P_i`. -/
lemma dmcPower_output_coord_marginal (W : DMC α β) (n : ℕ) (P : ProbDist (Fin n → α)) (i : Fin n) :
    ((W.power n).joint P).snd.map (fun y => y i) = (W.joint (P.map (fun x => x i))).snd := by
  classical
  unfold ProbDist.map ProbDist.snd DMC.joint DMC.power
  congr; funext b; dsimp only
  have hpush : ∀ y : Fin n → β,
      (if y i = b then ∑ x : Fin n → α, P.pmf x * ∏ j : Fin n, W.trans (x j) (y j) else 0) =
        ∑ x : Fin n → α, if y i = b then P.pmf x * ∏ j : Fin n, W.trans (x j) (y j) else 0 :=
    fun y => by split_ifs <;> simp
  simp_rw [hpush]
  rw [Finset.sum_comm]
  have hcoord : ∀ x : Fin n → α,
      (∑ y : Fin n → β, if y i = b then P.pmf x * ∏ j : Fin n, W.trans (x j) (y j) else 0) =
        P.pmf x * W.trans (x i) b := by
    intro x
    let F : Fin n → β → ℝ := fun j yj =>
      if j = i then (if yj = b then W.trans (x j) yj else 0) else W.trans (x j) yj
    have hfun : ∀ y : Fin n → β,
        (if y i = b then P.pmf x * ∏ j : Fin n, W.trans (x j) (y j) else 0) =
          P.pmf x * ∏ j : Fin n, F j (y j) := by
      intro y
      conv_rhs => rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (y j)) (Finset.mem_univ i)]
      have hrest : ∏ j ∈ Finset.univ.erase i, F j (y j) =
          ∏ j ∈ Finset.univ.erase i, W.trans (x j) (y j) :=
        Finset.prod_congr rfl fun j hj => by simp [F, (Finset.mem_erase.mp hj).1]
      rw [hrest]
      by_cases hy : y i = b
      · simp only [hy, ↓reduceIte, F]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => W.trans (x j) (y j)) (Finset.mem_univ i), hy]
      · simp [F, hy]
    simp_rw [hfun, ← Finset.mul_sum, ← Fintype.prod_sum F]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ yj : β, F j yj) (Finset.mem_univ i)]
    have hi : ∑ yj : β, F i yj = W.trans (x i) b := by simp [F]
    have hrest : ∏ j ∈ Finset.univ.erase i, (∑ yj : β, F j yj) = 1 :=
      Finset.prod_eq_one fun j hj => by
        simp only [F, ite_eq_right_iff.mpr (fun h => absurd h (Finset.mem_erase.mp hj).1)]
        exact W.sum_one (x j)
    rw [hi, hrest, mul_one]
  simp_rw [hcoord]
  have h := sum_pmf_mul_comp P (fun x => x i) (fun a => W.trans a b)
  simpa [ProbDist.map] using h

/-- **Memoryless Channel Subadditivity of Mutual Information** (Cover & Thomas, Lemma 7.9.2):
    for any input distribution `P` on `Fin n → α` passed through the memoryless product channel
    `W^{⊗ n}`,
    `I(X^n; Y^n) ≤ ∑_{i=1}^n I(X_i; Y_i)`. -/
theorem dmcPower_mutualInfo_le_sum (W : DMC α β) (n : ℕ) (P : ProbDist (Fin n → α)) :
    mutualInfo ((W.power n).joint P) ≤
      ∑ i : Fin n, mutualInfo (W.joint (P.map (fun x => x i))) := by
  have hmi_n : mutualInfo ((W.power n).joint P) =
      shannonEntropy ((W.power n).joint P).snd -
        ∑ x : Fin n → α, P.pmf x * shannonEntropy (dmcRow (W.power n) x) := by
    unfold mutualInfo
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]
    ring
  have hrow : ∀ x : Fin n → α,
      shannonEntropy (dmcRow (W.power n) x) = ∑ i : Fin n, shannonEntropy (dmcRow W (x i)) := by
    intro x
    have heq : dmcRow (W.power n) x = piProdDist (fun i => dmcRow W (x i)) := rfl
    rw [heq, shannonEntropy_piProdDist]
  have hcond : ∑ x : Fin n → α, P.pmf x * shannonEntropy (dmcRow (W.power n) x) =
      ∑ i : Fin n, ∑ a : α, (P.map (fun x => x i)).pmf a * shannonEntropy (dmcRow W a) := by
    simp_rw [hrow, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact sum_pmf_mul_comp P (fun x => x i) (fun a => shannonEntropy (dmcRow W a))
  have hout : shannonEntropy ((W.power n).joint P).snd ≤
      ∑ i : Fin n, shannonEntropy (W.joint (P.map (fun x => x i))).snd := by
    calc shannonEntropy ((W.power n).joint P).snd
      _ ≤ ∑ i : Fin n, shannonEntropy (((W.power n).joint P).snd.map (fun y => y i)) :=
          shannonEntropy_pi_le_sum n ((W.power n).joint P).snd
      _ = ∑ i : Fin n, shannonEntropy (W.joint (P.map (fun x => x i))).snd := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dmcPower_output_coord_marginal]
  have hmi_i : ∀ i : Fin n,
      mutualInfo (W.joint (P.map (fun x => x i))) =
        shannonEntropy (W.joint (P.map (fun x => x i))).snd -
          ∑ a : α, (P.map (fun x => x i)).pmf a * shannonEntropy (dmcRow W a) := by
    intro i
    unfold mutualInfo
    rw [dmc_joint_fst, dmc_joint_shannonEntropy]
    ring
  rw [hmi_n, hcond]
  simp_rw [hmi_i, Finset.sum_sub_distrib]
  linarith

/-- The set of achievable single-letter mutual informations `{ I(X; Y) : P ∈ Δ(α) }` is bounded above. -/
lemma dmc_mutualInfo_bddAbove (W : DMC α β) :
    BddAbove { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P } := by
  by_cases hα : Nonempty α
  · refine ⟨log2 (Fintype.card α : ℝ), ?_⟩
    rintro r ⟨P, rfl⟩
    unfold DMC.mutualInfo mutualInfo
    have hce : 0 ≤ condEntropy (W.joint P) := condEntropy_nonneg (W.joint P)
    unfold condEntropy at hce
    have hent : shannonEntropy (W.joint P).fst ≤ log2 (Fintype.card α : ℝ) :=
      shannonEntropy_le_log2_card (W.joint P).fst
    linarith
  · refine ⟨0, ?_⟩
    rintro r ⟨P, rfl⟩
    exfalso
    have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (hα ⟨a⟩).elim
    linarith [P.sum_one]

/-- Single-letter mutual information is bounded above by Shannon capacity `W.capacity`. -/
theorem dmc_mutualInfo_le_capacity (W : DMC α β) (P : ProbDist α) :
    mutualInfo (W.joint P) ≤ W.capacity :=
  le_csSup (dmc_mutualInfo_bddAbove W) ⟨P, rfl⟩

/-- **Single-Letter Converse Tensorization Bound** (Cover & Thomas, §7.9):
    for any input distribution `P` on `Fin n → α`,
    `I(X^n; Y^n) ≤ n · C(W)`. -/
theorem dmcPower_mutualInfo_le_mul_capacity (W : DMC α β) (n : ℕ) (P : ProbDist (Fin n → α)) :
    mutualInfo ((W.power n).joint P) ≤ (n : ℝ) * W.capacity := by
  have h1 := dmcPower_mutualInfo_le_sum W n P
  have h2 : ∑ i : Fin n, mutualInfo (W.joint (P.map (fun x => x i))) ≤ ∑ _i : Fin n, W.capacity :=
    Finset.sum_le_sum fun _i _ => dmc_mutualInfo_le_capacity W _
  have h3 : ∑ _i : Fin n, W.capacity = (n : ℝ) * W.capacity := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end Tensorization

/-! ### 3. Weak Converse for Any Block Code over a DMC (Cover & Thomas §7.9) -/

section WeakConverse

variable {α β M : Type*} [Fintype α] [Fintype β] [Fintype M]

/-- Pre-compose a DMC `W : DMC α β` with a deterministic encoder `enc : M → α`. -/
def dmcPrecomp (W : DMC α β) (enc : M → α) : DMC M β where
  trans := fun m y => W.trans (enc m) y
  nonneg := fun m y => W.nonneg (enc m) y
  sum_one := fun m => W.sum_one (enc m)

/-- Deterministic pre-encoding preserves channel mutual information:
    for `M → X = enc(M) → Y` through `W`, `I(M; Y) = I(X; Y)`. -/
theorem dmcPrecomp_mutualInfo_eq (W : DMC α β) (P : ProbDist M) (enc : M → α) :
    mutualInfo ((dmcPrecomp W enc).joint P) = mutualInfo (W.joint (P.map enc)) := by
  have hsnd : ((dmcPrecomp W enc).joint P).snd = (W.joint (P.map enc)).snd := by
    unfold ProbDist.snd DMC.joint dmcPrecomp
    congr; funext y; dsimp only
    exact sum_pmf_mul_comp P enc (fun a => W.trans a y)
  have hcond : ∑ m : M, P.pmf m * shannonEntropy (dmcRow (dmcPrecomp W enc) m) =
      ∑ a : α, (P.map enc).pmf a * shannonEntropy (dmcRow W a) :=
    sum_pmf_mul_comp P enc (fun a => shannonEntropy (dmcRow W a))
  unfold mutualInfo
  rw [dmc_joint_fst, dmc_joint_fst, dmc_joint_shannonEntropy, dmc_joint_shannonEntropy, hsnd, hcond]
  ring

/-- **Fano + Tensorization Weak Converse Inequality for Any Block Code**
    (Cover & Thomas, §7.9):
    for any finite message set `M` with `2 ≤ |M|`, encoder `enc : M → Fin n → α`, and
    decoder `dec : (Fin n → β) → M` over a DMC `W`, with uniform message law and
    average error probability `P_e = estErrorProb P_MY dec`,
    `log₂ |M| ≤ h(P_e) + P_e log₂(|M| - 1) + n · C(W)`. -/
theorem dmc_blockCode_weak_converse (W : DMC α β) (n : ℕ) (hM : 2 ≤ Fintype.card M)
    (enc : M → Fin n → α) (dec : (Fin n → β) → M) :
    letI : Nonempty M := Fintype.card_pos_iff.mp (by omega)
    let P_MY := (dmcPrecomp (W.power n) enc).joint (ProbDist.uniform (α := M))
    let P_e := estErrorProb P_MY dec
    log2 (Fintype.card M : ℝ) ≤
      binaryEntropy P_e + P_e * log2 ((Fintype.card M : ℝ) - 1) + (n : ℝ) * W.capacity := by
  have : Nonempty M := Fintype.card_pos_iff.mp (by omega)
  dsimp only
  let P_MY := (dmcPrecomp (W.power n) enc).joint (ProbDist.uniform (α := M))
  have hfano := fano_inequality P_MY dec hM
  have hmi_eq : mutualInfo P_MY =
      mutualInfo ((W.power n).joint ((ProbDist.uniform (α := M)).map enc)) :=
    dmcPrecomp_mutualInfo_eq (W.power n) ProbDist.uniform enc
  have hcap : mutualInfo P_MY ≤ (n : ℝ) * W.capacity := by
    rw [hmi_eq]
    exact dmcPower_mutualInfo_le_mul_capacity W n ((ProbDist.uniform (α := M)).map enc)
  have hHM : shannonEntropy P_MY.fst = log2 (Fintype.card M : ℝ) := by
    change shannonEntropy ((dmcPrecomp (W.power n) enc).joint ProbDist.uniform).fst = _
    rw [dmc_joint_fst]
    exact (shannonEntropy_eq_log2_card_iff (ProbDist.uniform (α := M))).mpr rfl
  have hid : log2 (Fintype.card M : ℝ) = condEntropy P_MY + mutualInfo P_MY := by
    unfold condEntropy mutualInfo
    linarith [hHM]
  linarith

/-- **Weak Converse Directly in Terms of `dmcAvgError`** (from `InfoTheory.Core.Channels`):
    for any `(n, M)` block code with `2 ≤ M` over a DMC `W`,
    `log₂ M ≤ h(P_e) + P_e log₂(M - 1) + n · C(W)`. -/
theorem dmcAvgError_weak_converse [DecidableEq β] (W : DMC α β) (n M : ℕ) (hM : 2 ≤ M)
    (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) :
    log2 (M : ℝ) ≤
      binaryEntropy (dmcAvgError W n M enc dec) +
        dmcAvgError W n M enc dec * log2 ((M : ℝ) - 1) + (n : ℝ) * W.capacity := by
  have hcard : 2 ≤ Fintype.card (Fin M) := by simpa using hM
  have h := dmc_blockCode_weak_converse W n hcard enc dec
  have : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have herr : estErrorProb ((dmcPrecomp (W.power n) enc).joint (ProbDist.uniform (α := Fin M))) dec =
      dmcAvgError W n M enc dec := by
    classical
    unfold estErrorProb dmcAvgError dmcPrecomp DMC.joint ProbDist.uniform
    have hMne : M ≠ 0 := by omega
    simp only [hMne, ↓reduceIte, Fintype.card_fin]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  dsimp only at h
  rw [herr, Fintype.card_fin] at h
  exact h

/-- **Textbook Rate-Error Weak Converse** (Cover & Thomas, Eq. 7.115):
    for any `(n, M)` block code with `n ≥ 1` and `2 ≤ M` over a DMC `W`,
    `(1 - P_e) · (log₂ M / n) ≤ C(W) + 1 / n`. -/
theorem dmcAvgError_rate_converse [DecidableEq β] (W : DMC α β) (n M : ℕ) (hn : 0 < n) (hM : 2 ≤ M)
    (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) :
    (1 - dmcAvgError W n M enc dec) * (log2 (M : ℝ) / (n : ℝ)) ≤
      W.capacity + 1 / (n : ℝ) := by
  have : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  let P_MY := (dmcPrecomp (W.power n) enc).joint (ProbDist.uniform (α := Fin M))
  have herr : estErrorProb P_MY dec = dmcAvgError W n M enc dec := by
    classical
    unfold P_MY estErrorProb dmcAvgError dmcPrecomp DMC.joint ProbDist.uniform
    have hMne : M ≠ 0 := by omega
    simp only [hMne, ↓reduceIte, Fintype.card_fin]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  have hpe0 : 0 ≤ dmcAvgError W n M enc dec := herr ▸ estErrorProb_nonneg P_MY dec
  have hpe1 : dmcAvgError W n M enc dec ≤ 1 := herr ▸ estErrorProb_le_one P_MY dec
  have hconv := dmcAvgError_weak_converse W n M hM enc dec
  have hbin : binaryEntropy (dmcAvgError W n M enc dec) ≤ 1 :=
    InfoTheory.Known.binaryEntropy_le_one hpe0 hpe1
  have hlog : log2 ((M : ℝ) - 1) ≤ log2 (M : ℝ) := by
    unfold log2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    exact div_le_div_of_nonneg_right (Real.log_le_log hM1 (by linarith)) (le_of_lt hlog2)
  have hmul : dmcAvgError W n M enc dec * log2 ((M : ℝ) - 1) ≤
      dmcAvgError W n M enc dec * log2 (M : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hpe0
  have hmain : (1 - dmcAvgError W n M enc dec) * log2 (M : ℝ) ≤ (n : ℝ) * W.capacity + 1 := by
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  calc (1 - dmcAvgError W n M enc dec) * (log2 (M : ℝ) / (n : ℝ))
    _ = ((1 - dmcAvgError W n M enc dec) * log2 (M : ℝ)) / (n : ℝ) := by ring
    _ ≤ ((n : ℝ) * W.capacity + 1) / (n : ℝ) := div_le_div_of_nonneg_right hmain (le_of_lt hn_pos)
    _ = W.capacity + 1 / (n : ℝ) := by
        rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hn_pos)]

end WeakConverse

end InfoTheory.Bridge
