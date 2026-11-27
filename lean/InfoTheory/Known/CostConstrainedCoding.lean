import InfoTheory.Bridge.ChannelAchievability

/-!
# Cost-Constrained Channel Coding for DMCs (achievability)

For a DMC `W : DMC α β`, an input cost `b : α → ℝ` and a budget `B`, every rate
`0 ≤ R < I(P_X, W)` with `E_{P_X}[b(X)] < B` is achievable by `(n, max 1 ⌊2^{nR}⌋)` block codes
**every codeword** of which satisfies the deterministic cost constraint `∑ᵢ b(x(m)ᵢ) ≤ n B`
(El Gamal–Kim §3.3, "achievability with cost constraint"; Cover–Thomas §9.1 power constraint
proof, discrete version; Gallager §7.3).

Proof (random coding + expurgation):

1. `iidDist_cost_violation_le`: Chebyshev bound for the i.i.d. empirical cost,
   `P^n(∑ᵢ b(Xᵢ) > nB) ≤ Var_P(b) / (n (B - E_P b)²)`.
2. `exists_codebook_err_add_viol_le`: averaging over the i.i.d. random codebook of size `M'`
   (`InfoTheory.Bridge.codebookProb`) the sum "average error of the joint-typicality decoder +
   fraction of cost-violating codewords" is at most the random-coding bound plus the violation
   probability, so a deterministic codebook achieves it.
3. `exists_subcode_of_err_add_viol_le` (expurgation): from a codebook of size `2M` with
   `P_e + (fraction of violators) ≤ β ≤ min(δ, 1)/4`, keep `M` messages each of which has error
   probability `≤ δ` and satisfies the cost constraint.
4. `dmc_cost_constrained_achievable`: asymptotics.

Everything is finite-sum based and builds on `InfoTheory.Bridge.ChannelAchievability`.
-/

open scoped BigOperators
open Filter Topology
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Known.CostConstrainedCoding

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### 1. Chebyshev bound for the empirical cost -/

/-- Mean cost `E_P[b]`. -/
noncomputable def meanCost (P : ProbDist α) (b : α → ℝ) : ℝ := ∑ a, P.pmf a * b a

/-- Cost variance `Var_P[b]`. -/
noncomputable def varCost (P : ProbDist α) (b : α → ℝ) : ℝ :=
  ∑ a, P.pmf a * (b a - meanCost P b) ^ 2

/-- The cost of a block `x` violates the budget `n B`. -/
def CostViol (b : α → ℝ) (B : ℝ) {n : ℕ} (x : Fin n → α) : Prop :=
  (n : ℝ) * B < ∑ i, b (x i)

/-- Probability that an i.i.d. block violates the cost budget. -/
noncomputable def violProb (P : ProbDist α) (b : α → ℝ) (B : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ x : Fin n → α, if CostViol b B x then (iidDist P n).pmf x else 0

lemma violProb_nonneg (P : ProbDist α) (b : α → ℝ) (B : ℝ) (n : ℕ) :
    0 ≤ violProb P b B n := by
  classical
  unfold violProb
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [(iidDist P n).nonneg x]

/-- **Chebyshev bound** `P^n(∑ᵢ b(Xᵢ) > nB) ≤ Var(b) / (n (B - E b)²)` when `E b < B`. -/
theorem violProb_le (P : ProbDist α) (b : α → ℝ) {B : ℝ} (hB : meanCost P b < B)
    {n : ℕ} (hn : 0 < n) :
    violProb P b B n ≤ varCost P b / ((n : ℝ) * (B - meanCost P b) ^ 2) := by
  classical
  set μ := meanCost P b with hμ
  let Z : α → ℝ := fun a => b a - μ
  have hEZ : ∑ a : α, P.pmf a * Z a = 0 := by
    simp_rw [Z, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
    rw [hμ, meanCost, sub_self]
  have hVar : ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
      (n : ℝ) * varCost P b := by
    have hsq : ∀ x : Fin n → α,
        (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
          ∑ i : Fin n, ∑ j : Fin n, (iidDist P n).pmf x * (Z (x i) * Z (x j)) := by
      intro x
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    trans (∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → α, (iidDist P n).pmf x * (Z (x i) * Z (x j)))
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    · trans (∑ _i : Fin n, varCost P b)
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · have h := iidDist_sum_coord P (fun a => Z a * Z a) i
          simpa [← sq, varCost, Z, hμ] using h
        · intro j _ hji
          rw [iidDist_sum_two_coords P Z Z hji.symm, hEZ, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp
  have hg : 0 < B - μ := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hbad : ∀ x : Fin n → α,
      ((n : ℝ) * (B - μ)) ^ 2 * (if CostViol b B x then (iidDist P n).pmf x else 0) ≤
        (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 := by
    intro x
    split_ifs with hx
    · have hsum : ∑ i : Fin n, Z (x i) = ∑ i, b (x i) - (n : ℝ) * μ := by
        simp [Z, Finset.sum_sub_distrib]
      have hlt : (n : ℝ) * (B - μ) < ∑ i : Fin n, Z (x i) := by
        rw [hsum]; unfold CostViol at hx; linarith
      have h0 : 0 ≤ (n : ℝ) * (B - μ) := by positivity
      have hsq : ((n : ℝ) * (B - μ)) ^ 2 ≤ (∑ i : Fin n, Z (x i)) ^ 2 := by nlinarith
      have hp := (iidDist P n).nonneg x
      nlinarith
    · have hp := (iidDist P n).nonneg x
      simp only [mul_zero]
      positivity
  have hsum : ((n : ℝ) * (B - μ)) ^ 2 * violProb P b B n ≤ (n : ℝ) * varCost P b := by
    unfold violProb
    rw [Finset.mul_sum, ← hVar]
    exact Finset.sum_le_sum fun x _ => hbad x
  have hden : (0 : ℝ) < (n : ℝ) * (B - μ) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  have hrew : ((n : ℝ) * (B - μ)) ^ 2 = (n : ℝ) * ((n : ℝ) * (B - μ) ^ 2) := by ring
  rw [hrew, mul_assoc] at hsum
  have := le_of_mul_le_mul_left hsum hn_pos
  linarith

/-- The violation probability tends to `0`. -/
theorem violProb_eventually_le (P : ProbDist α) (b : α → ℝ) {B : ℝ} (hB : meanCost P b < B)
    {c : ℝ} (hc : 0 < c) : ∀ᶠ n : ℕ in atTop, violProb P b B n ≤ c := by
  have hg0 : 0 < B - meanCost P b := by linarith
  have hg : 0 < (B - meanCost P b) ^ 2 := by positivity
  have hV : 0 ≤ varCost P b :=
    Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt (varCost P b / (c * (B - meanCost P b) ^ 2))
  refine eventually_atTop.2 ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  refine le_trans (violProb_le P b hB hn1) ?_
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  rw [div_le_iff₀ (by positivity)]
  have h1 := (div_lt_iff₀ (by positivity : 0 < c * (B - meanCost P b) ^ 2)).mp
    (lt_of_lt_of_le hN hnr)
  nlinarith

/-! ### 2. A codebook with small error and few cost violators -/

/-- Per-message error probability `λ_m` of a block code over `W`. -/
noncomputable def msgError [DecidableEq β] (W : DMC α β) {n M : ℕ} (enc : Fin M → Fin n → α)
    (dec : (Fin n → β) → Fin M) (m : Fin M) : ℝ :=
  ∑ y : Fin n → β, if dec y ≠ m then (W.power n).trans (enc m) y else 0

lemma msgError_nonneg [DecidableEq β] (W : DMC α β) {n M : ℕ} (enc : Fin M → Fin n → α)
    (dec : (Fin n → β) → Fin M) (m : Fin M) : 0 ≤ msgError W enc dec m :=
  Finset.sum_nonneg fun y _ => by split_ifs <;> simp [(W.power n).nonneg]

lemma dmcAvgError_eq_msgError [DecidableEq β] (W : DMC α β) {n M : ℕ} (hM : 0 < M)
    (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) :
    dmcAvgError W n M enc dec = (1 / (M : ℝ)) * ∑ m, msgError W enc dec m := by
  unfold dmcAvgError msgError
  simp only [Nat.pos_iff_ne_zero.mp hM, ↓reduceIte]

/-- Number of cost-violating codewords. -/
noncomputable def numViol (b : α → ℝ) (B : ℝ) {n M : ℕ} (enc : Fin M → Fin n → α) : ℝ := by
  classical
  exact ∑ m : Fin M, if CostViol b B (enc m) then (1 : ℝ) else 0

lemma codebookProb_eq_iid (Px : ProbDist α) (n M : ℕ) (enc : Fin M → Fin n → α) :
    codebookProb Px n M enc = (iidDist (iidDist Px n) M).pmf enc := rfl

lemma sum_codebookProb_numViol (Px : ProbDist α) (b : α → ℝ) (B : ℝ) (n M : ℕ) :
    ∑ enc : Fin M → Fin n → α, codebookProb Px n M enc * numViol b B enc =
      (M : ℝ) * violProb Px b B n := by
  classical
  unfold numViol
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ m : Fin M, ∑ enc : Fin M → Fin n → α,
      codebookProb Px n M enc * (if CostViol b B (enc m) then (1 : ℝ) else 0) =
        violProb Px b B n := by
    intro m
    simp_rw [codebookProb_eq_iid]
    rw [iidDist_sum_coord (iidDist Px n) (fun x => if CostViol b B x then (1 : ℝ) else 0) m]
    unfold violProb
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun m _ => h m)]
  simp

lemma exists_le_of_weighted_sum_le_cc {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (B : ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1)
    (hle : ∑ i : ι, w i * f i ≤ B) :
    ∃ i : ι, f i ≤ B := by
  by_contra hall
  push Not at hall
  have hpos : ∃ i₀ : ι, 0 < w i₀ := by
    by_contra hno
    push Not at hno
    have hzero : ∑ i : ι, w i = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hno i) (hw0 i)
    linarith
  obtain ⟨i₀, hi₀⟩ := hpos
  have hlt : ∑ i : ι, w i * B < ∑ i : ι, w i * f i :=
    Finset.sum_lt_sum
      (fun i _ => mul_le_mul_of_nonneg_left (le_of_lt (hall i)) (hw0 i))
      ⟨i₀, Finset.mem_univ i₀, mul_lt_mul_of_pos_left (hall i₀) hi₀⟩
  have hB : ∑ i : ι, w i * B = B := by
    rw [← Finset.sum_mul, hw1, one_mul]
  linarith

/-- **Random coding with cost accounting**: some codebook of size `M' > 0` has
    `P_e(enc, joint-typicality decoder) + (#violators)/M' ≤`
    `(1 - P^n(A_ε)) + (M' - 1) 2^{-n(I - 3ε)} + P^n(cost violation)`. -/
theorem exists_codebook_err_add_viol_le [DecidableEq β] (W : DMC α β) (Px : ProbDist α)
    (b : α → ℝ) (B : ℝ) (n M' : ℕ) (hM' : 0 < M') (ε : ℝ) :
    ∃ (enc : Fin M' → Fin n → α) (dec : (Fin n → β) → Fin M'),
      dmcAvgError W n M' enc dec + numViol b B enc / (M' : ℝ) ≤
        (1 - ∑ xy ∈ jointTypicalSet (W.joint Px) n ε, (jointIidDist (W.joint Px) n).pmf xy) +
        ((M' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) +
        violProb Px b B n := by
  set P := W.joint Px with hP
  have hexp := dmc_random_coding_expected_error_le W Px n M' hM' ε
  have hindep := jointTypicalSet_indep_prob_le P n ε
  have hMpos : (0 : ℝ) < M' := Nat.cast_pos.mpr hM'
  have hviol := sum_codebookProb_numViol Px b B n M'
  set E := (1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy) +
    ((M' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) +
    violProb Px b B n with hE
  have hle : ∑ enc : Fin M' → Fin n → α, codebookProb Px n M' enc *
      (dmcAvgError W n M' enc (jointTypicalDec P n M' hM' ε enc) +
        numViol b B enc / (M' : ℝ)) ≤ E := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h2 : ∑ enc : Fin M' → Fin n → α, codebookProb Px n M' enc *
        (numViol b B enc / (M' : ℝ)) = violProb Px b B n := by
      simp_rw [mul_div_assoc', ← Finset.sum_div, hviol]
      field_simp
    rw [h2]
    have hmul : ((M' - 1 : ℕ) : ℝ) *
        (∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy) ≤
        ((M' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) :=
      mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg _)
    dsimp only at hexp
    rw [hE]
    linarith
  obtain ⟨enc, henc⟩ := exists_le_of_weighted_sum_le_cc (codebookProb Px n M')
    (fun enc => dmcAvgError W n M' enc (jointTypicalDec P n M' hM' ε enc) +
      numViol b B enc / (M' : ℝ)) E (codebookProb_nonneg Px n M')
    (codebookProb_sum_one Px n M') hle
  exact ⟨enc, jointTypicalDec P n M' hM' ε enc, henc⟩

/-! ### 3. Expurgation -/

/-- **Expurgation**: from a codebook of size `2M` whose average error plus violator fraction is
    at most `β ≤ min(δ, 1)/4`, one obtains an `(n, M)` code with every codeword satisfying the
    cost constraint and average error `≤ δ`. -/
theorem exists_subcode_of_err_add_viol_le [DecidableEq β] (W : DMC α β) (b : α → ℝ) (B : ℝ)
    {n M : ℕ} (hM : 0 < M) (enc : Fin (2 * M) → Fin n → α) (dec : (Fin n → β) → Fin (2 * M))
    {β' δ : ℝ} (hδ : 0 < δ)
    (hβ : dmcAvgError W n (2 * M) enc dec + numViol b B enc / ((2 * M : ℕ) : ℝ) ≤ β')
    (hβδ : 4 * β' ≤ δ) (hβ1 : 4 * β' ≤ 1) :
    ∃ (enc' : Fin M → Fin n → α) (dec' : (Fin n → β) → Fin M),
      (∀ m, ∑ i, b (enc' m i) ≤ (n : ℝ) * B) ∧ dmcAvgError W n M enc' dec' ≤ δ := by
  classical
  have h2M : 0 < 2 * M := by omega
  have h2Mr : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := Nat.cast_pos.mpr h2M
  set lam := msgError W enc dec with hlam
  have havg := dmcAvgError_eq_msgError W h2M enc dec
  have hviol0 : 0 ≤ numViol b B enc := by
    unfold numViol; exact Finset.sum_nonneg fun m _ => by split_ifs <;> norm_num
  have herr0 : 0 ≤ dmcAvgError W n (2 * M) enc dec := by
    rw [havg]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => msgError_nonneg _ _ _ _)
  -- bad sets
  let Bad1 : Finset (Fin (2 * M)) := Finset.univ.filter fun m => δ < lam m
  let Bad2 : Finset (Fin (2 * M)) := Finset.univ.filter fun m => CostViol b B (enc m)
  let Good : Finset (Fin (2 * M)) := Finset.univ.filter fun m => lam m ≤ δ ∧ ¬ CostViol b B (enc m)
  have hsumlam : ∑ m, lam m ≤ ((2 * M : ℕ) : ℝ) * β' := by
    have h1 : dmcAvgError W n (2 * M) enc dec ≤ β' := by
      have := div_nonneg hviol0 h2Mr.le
      linarith
    rw [havg] at h1
    rw [one_div, inv_mul_le_iff₀ h2Mr] at h1
    exact h1
  have hcard1 : δ * (Bad1.card : ℝ) ≤ ((2 * M : ℕ) : ℝ) * β' := by
    have : δ * (Bad1.card : ℝ) ≤ ∑ m ∈ Bad1, lam m := by
      rw [mul_comm, ← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ fun m hm => le_of_lt (Finset.mem_filter.mp hm).2
    refine le_trans this (le_trans ?_ hsumlam)
    exact Finset.sum_le_univ_sum_of_nonneg fun m => msgError_nonneg _ _ _ _
  have hcard2 : (Bad2.card : ℝ) ≤ ((2 * M : ℕ) : ℝ) * β' := by
    have h1 : numViol b B enc / ((2 * M : ℕ) : ℝ) ≤ β' := by linarith
    rw [div_le_iff₀ h2Mr] at h1
    have : (Bad2.card : ℝ) = numViol b B enc := by
      unfold numViol
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [this]; linarith
  have hc1 : (Bad1.card : ℝ) ≤ (M : ℝ) / 2 := by
    have : δ * (Bad1.card : ℝ) ≤ δ * ((M : ℝ) / 2) := by
      refine le_trans hcard1 ?_
      push_cast
      nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    exact le_of_mul_le_mul_left this hδ
  have hc2 : (Bad2.card : ℝ) ≤ (M : ℝ) / 2 := by
    refine le_trans hcard2 ?_
    push_cast
    nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hGood : M ≤ Good.card := by
    have hunion : Goodᶜ ⊆ Bad1 ∪ Bad2 := by
      intro m hm
      simp only [Good, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_and_or, not_le, not_not] at hm
      rcases hm with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hc : (Goodᶜ.card : ℝ) ≤ M := by
      have := Finset.card_le_card hunion
      have h3 := Finset.card_union_le Bad1 Bad2
      have : (Goodᶜ.card : ℝ) ≤ (Bad1.card : ℝ) + Bad2.card := by exact_mod_cast le_trans this h3
      linarith
    have htot : Good.card + Goodᶜ.card = 2 * M := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    have : (Good.card : ℝ) + Goodᶜ.card = 2 * M := by exact_mod_cast htot
    have : (M : ℝ) ≤ Good.card := by linarith
    exact_mod_cast this
  -- the selection map
  let ι : Fin M → Fin (2 * M) := fun m => Good.orderEmbOfFin rfl (Fin.castLE hGood m)
  have hιmem : ∀ m, ι m ∈ Good := fun m => Finset.orderEmbOfFin_mem Good rfl _
  have hιinj : Function.Injective ι := by
    intro a a' h
    have := (Good.orderEmbOfFin rfl).injective h
    exact Fin.castLE_injective hGood this
  let enc' : Fin M → Fin n → α := fun m => enc (ι m)
  let dec' : (Fin n → β) → Fin M := fun y =>
    if h : ∃ m, ι m = dec y then Classical.choose h else ⟨0, hM⟩
  have hdec' : ∀ y m, dec y = ι m → dec' y = m := by
    intro y m h
    have hex : ∃ m', ι m' = dec y := ⟨m, h.symm⟩
    simp only [dec', hex, ↓reduceDIte]
    exact hιinj ((Classical.choose_spec hex).trans h)
  refine ⟨enc', dec', fun m => ?_, ?_⟩
  · have := (Finset.mem_filter.mp (hιmem m)).2.2
    unfold CostViol at this
    exact not_lt.mp this
  · have hlam' : ∀ m, msgError W enc' dec' m ≤ δ := by
      intro m
      refine le_trans ?_ (Finset.mem_filter.mp (hιmem m)).2.1
      unfold msgError
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases h : dec' y ≠ m
      · have h2 : dec y ≠ ι m := fun he => h (hdec' y m he)
        simp [h, h2, enc']
      · simp only [h, ↓reduceIte]
        split_ifs <;> simp [(W.power n).nonneg]
    rw [dmcAvgError_eq_msgError W hM]
    have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    have : ∑ m, msgError W enc' dec' m ≤ ∑ _m : Fin M, δ := Finset.sum_le_sum fun m _ => hlam' m
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [one_div, inv_mul_le_iff₀ hMr]
    linarith

/-! ### 4. The cost-constrained achievability theorem -/

/-- `2^{-n c} → 0` for `c > 0`. -/
lemma eventually_two_rpow_neg_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (-((n : ℝ) * c)) ≤ t := by
  have hq0 : 0 < (2 : ℝ) ^ (-c) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2 : ℝ) ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  filter_upwards [(tendsto_order.1 hlim).2 t ht] with n hn
  have : (2 : ℝ) ^ (-((n : ℝ) * c)) = ((2 : ℝ) ^ (-c)) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [this]; exact hn.le

/-- **Cost-constrained DMC coding theorem (achievability)** (El Gamal–Kim §3.3; Gallager §7.3):
    if `E_{P_X}[b] < B` and `0 ≤ R < I(P_X, W)`, then for every `δ > 0` and all large `n` there is
    an `(n, max 1 ⌊2^{nR}⌋)` code all of whose codewords satisfy `∑ᵢ b(x(m)ᵢ) ≤ n B` and whose
    average error probability is at most `δ`. -/
theorem dmc_cost_constrained_achievable [DecidableEq β] (W : DMC α β) (Px : ProbDist α)
    (b : α → ℝ) {B R : ℝ} (hb : meanCost Px b < B) (hR0 : 0 ≤ R) (hR : R < W.mutualInfo Px)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (enc : Fin (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊) → Fin n → α)
        (dec : (Fin n → β) → Fin (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊)),
        (∀ m, ∑ i, b (enc m i) ≤ (n : ℝ) * B) ∧
          dmcAvgError W n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊) enc dec ≤ δ := by
  set ε : ℝ := (W.mutualInfo Px - R) / 4 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set t : ℝ := min δ 1 / 12 with ht_def
  have ht : 0 < t := by rw [ht_def]; have := lt_min hδ one_pos; positivity
  obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one (W.joint Px) hε ht
  have hev : ∀ᶠ n : ℕ in atTop,
      N₁ ≤ n ∧ (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ t / 2 ∧ violProb Px b B n ≤ t :=
    (eventually_ge_atTop N₁).and
      ((eventually_two_rpow_neg_le hε (by linarith)).and (violProb_eventually_le Px b hb ht))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hnN₁, hpow, hviol⟩ := hn₀ n hn
  set M := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ with hM_def
  have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have h2M : 0 < 2 * M := by omega
  obtain ⟨enc, dec, hbound⟩ := exists_codebook_err_add_viol_le W Px b B n (2 * M) h2M ε
  have hpowR : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hMle : (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    rw [hM_def]
    rcases le_total 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ with h | h
    · rw [max_eq_right h]; exact Nat.floor_le (by positivity)
    · rw [max_eq_left h]; push_cast; exact hpowR
  have hM1 : (((2 * M - 1 : ℕ)) : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R) := by
    have : ((2 * M - 1 : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    push_cast at this
    linarith
  have hterm2 : (((2 * M - 1 : ℕ)) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) ≤ t := by
    have hprod : (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) =
        (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [hε_def]; ring
    have hpos : 0 ≤ (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) := by positivity
    calc (((2 * M - 1 : ℕ)) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε)))
        ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM1 hpos
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * ε)) := by rw [mul_assoc, hprod]
      _ ≤ t := by linarith
  have hterm1 := hN₁ n hnN₁
  have hβ : dmcAvgError W n (2 * M) enc dec + numViol b B enc / ((2 * M : ℕ) : ℝ) ≤ 3 * t := by
    linarith
  have h3t : 4 * (3 * t) ≤ min δ 1 := by rw [ht_def]; linarith
  exact exists_subcode_of_err_add_viol_le W b B hM enc dec hδ hβ
    (le_trans h3t (min_le_left _ _)) (le_trans h3t (min_le_right _ _))

end InfoTheory.Known.CostConstrainedCoding
