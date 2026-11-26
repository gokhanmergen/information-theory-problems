import InfoTheory.Core
import InfoTheory.Known.Entropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open scoped BigOperators

namespace InfoTheory.Known

open InfoTheory.Bridge (pmf_le_one shannonEntropy_nonneg mutualInfo_nonneg)

open InfoTheory

/-! ## Elementary facts about `negPLogP` -/

private lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

private lemma negPLogP_of_nonneg {p : ℝ} (hp : 0 ≤ p) : negPLogP p = -p * log2 p := by
  unfold negPLogP
  split_ifs with h
  · have : p = 0 := le_antisymm h hp
    simp [this]
  · rfl

private lemma negPLogP_mul_log_two {p : ℝ} (hp : 0 ≤ p) :
    negPLogP p * Real.log 2 = -p * Real.log p := by
  rw [negPLogP_of_nonneg hp]; unfold log2
  field_simp [log_two_pos'.ne']

private lemma negPLogP_zero' : negPLogP 0 = 0 := by simp [negPLogP]

private lemma negPLogP_one' : negPLogP 1 = 0 := by simp [negPLogP, log2]

/-- `-(ab) log(ab) = a·(-b log b) + b·(-a log a)` for `a, b ≥ 0`. -/
private lemma negPLogP_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negPLogP (a * b) = a * negPLogP b + b * negPLogP a := by
  rw [negPLogP_of_nonneg (mul_nonneg ha hb), negPLogP_of_nonneg ha, negPLogP_of_nonneg hb]
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp
  unfold log2; rw [Real.log_mul ha'.ne' hb'.ne']; ring

/-- Grouping: `-S log S ≤ ∑ -aᵢ log aᵢ` where `S = ∑ aᵢ`, `aᵢ ≥ 0`. -/
private lemma negPLogP_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    negPLogP (∑ i ∈ s, a i) ≤ ∑ i ∈ s, negPLogP (a i) := by
  have hS : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i _ => ha i)
  rw [← mul_le_mul_iff_of_pos_right log_two_pos', Finset.sum_mul, negPLogP_mul_log_two hS,
    neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [negPLogP_mul_log_two (ha i)]
  rcases (ha i).eq_or_lt with h | h
  · rw [← h]; simp
  · have : Real.log (a i) ≤ Real.log (∑ i ∈ s, a i) :=
      Real.log_le_log h (Finset.single_le_sum (fun j _ => ha j) hi)
    nlinarith

/-! ## Entropy bounds (local copies; to be deduplicated with `Known/Entropy.lean`) -/

/-- `H(X) ≤ log₂ |α|` (Cover–Thomas Thm 2.6.4), via `log x ≤ x - 1`. -/
private lemma shannonEntropy_le_log_card' {α : Type*} [Fintype α] (P : ProbDist α) :
    shannonEntropy P ≤ log2 (Fintype.card α) := by
  have hN : (0 : ℝ) < Fintype.card α := by
    rcases isEmpty_or_nonempty α with h | h
    · have := P.sum_one; simp at this
    · exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card α : ℝ) with hNdef
  unfold shannonEntropy log2
  rw [le_div_iff₀ log_two_pos', Finset.sum_mul]
  have key : ∀ a, negPLogP (P.pmf a) * Real.log 2 ≤ P.pmf a * Real.log N + (1 / N - P.pmf a) := by
    intro a
    rw [negPLogP_mul_log_two (P.nonneg a)]
    rcases (P.nonneg a).eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (P.pmf a * N) by positivity)
      rw [one_div, Real.log_inv, Real.log_mul h.ne' hN.ne'] at h1
      have h2 : P.pmf a * (P.pmf a * N)⁻¹ = 1 / N := by field_simp
      nlinarith
  calc ∑ a, negPLogP (P.pmf a) * Real.log 2
      ≤ ∑ a, (P.pmf a * Real.log N + (1 / N - P.pmf a)) := Finset.sum_le_sum (fun a _ => key a)
    _ = Real.log N := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, Finset.sum_sub_distrib, P.sum_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp; ring

/-! ## Mutual information bounds for a joint distribution -/

/-! ## DMC: chain rule and the capacity API -/

section DMCAPI

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The input marginal of `W.joint P` is `P`. -/
theorem joint_fst_pmf (W : DMC α β) (P : ProbDist α) (x : α) :
    (W.joint P).fst.pmf x = P.pmf x := by
  simp [ProbDist.fst, DMC.joint, ← Finset.mul_sum, W.sum_one]

/-- The output marginal of `W.joint P` is `y ↦ ∑ₓ P(x) W(y|x)`. -/
theorem joint_snd_pmf (W : DMC α β) (P : ProbDist α) (y : β) :
    (W.joint P).snd.pmf y = ∑ x, P.pmf x * W.trans x y := rfl

/-- `H(X) ` of the joint input marginal equals `H(P)`. -/
theorem shannonEntropy_joint_fst (W : DMC α β) (P : ProbDist α) :
    shannonEntropy (W.joint P).fst = shannonEntropy P := by
  unfold shannonEntropy; simp only [joint_fst_pmf]

/-- Chain rule `H(X,Y) = H(X) + H(Y|X)` with `H(Y|X) = ∑ₓ P(x) H(W(·|x))`
(Cover–Thomas Thm 2.2.1). -/
theorem shannonEntropy_joint (W : DMC α β) (P : ProbDist α) :
    shannonEntropy (W.joint P) =
      shannonEntropy P + ∑ x, P.pmf x * ∑ y, negPLogP (W.trans x y) := by
  unfold shannonEntropy
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [DMC.joint]
  simp_rw [negPLogP_mul (P.nonneg x) (W.nonneg x _)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, W.sum_one]
  ring

/-- `I(X;Y) = H(Y) - H(Y|X)` for a DMC (Cover–Thomas §2.4, §7.1). -/
theorem mutualInfo_eq_entropy_output_sub (W : DMC α β) (P : ProbDist α) :
    W.mutualInfo P =
      shannonEntropy (W.joint P).snd - ∑ x, P.pmf x * ∑ y, negPLogP (W.trans x y) := by
  unfold DMC.mutualInfo mutualInfo
  rw [shannonEntropy_joint_fst, shannonEntropy_joint]
  ring

/-- `I(X;Y) ≥ 0` across any DMC (Cover–Thomas Thm 2.6.3). -/
theorem dmc_mutualInfo_nonneg (W : DMC α β) (P : ProbDist α) : 0 ≤ W.mutualInfo P :=
  mutualInfo_nonneg _

/-- `I(X;Y) ≤ H(X) ≤ log₂ |α|` (Cover–Thomas Thm 2.6.4, §7.1). -/
theorem dmc_mutualInfo_le_log_card_input (W : DMC α β) (P : ProbDist α) :
    W.mutualInfo P ≤ log2 (Fintype.card α) :=
  (mutualInfo_le_entropy_fst _).trans (shannonEntropy_le_log_card' _)

/-- `I(X;Y) ≤ H(Y) ≤ log₂ |β|` (Cover–Thomas Thm 2.6.4, §7.1). -/
theorem dmc_mutualInfo_le_log_card_output (W : DMC α β) (P : ProbDist α) :
    W.mutualInfo P ≤ log2 (Fintype.card β) :=
  (mutualInfo_le_entropy_snd _).trans (shannonEntropy_le_log_card' _)

/-- The set of achievable `I(X;Y)` values defining `DMC.capacity` is nonempty for a
nonempty input alphabet. -/
theorem capacity_set_nonempty [Nonempty α] (W : DMC α β) :
    { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P }.Nonempty :=
  ⟨_, ProbDist.uniform, rfl⟩

/-- The set defining `DMC.capacity` is bounded above (by `log₂ |α|`), so the `sSup` is a
genuine supremum (Cover–Thomas §7.1, property (2)). -/
theorem capacity_set_bddAbove (W : DMC α β) :
    BddAbove { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P } :=
  ⟨log2 (Fintype.card α), fun _ ⟨P, hP⟩ => hP ▸ dmc_mutualInfo_le_log_card_input W P⟩

/-- `I(X;Y) ≤ C(W)` for every input distribution. -/
theorem mutualInfo_le_capacity (W : DMC α β) (P : ProbDist α) : W.mutualInfo P ≤ W.capacity :=
  le_csSup (capacity_set_bddAbove W) ⟨P, rfl⟩

/-- `C(W) ≥ 0` (Cover–Thomas §7.1, property (1)). Holds even for empty input alphabet,
where the defining set is empty and `sSup ∅ = 0`. -/
theorem capacity_nonneg (W : DMC α β) : 0 ≤ W.capacity :=
  Real.sSup_nonneg (fun _ ⟨P, hP⟩ => hP ▸ dmc_mutualInfo_nonneg W P)

private lemma log2_natCast_nonneg (n : ℕ) : 0 ≤ log2 (n : ℝ) :=
  div_nonneg (Real.log_natCast_nonneg n) log_two_pos'.le

/-- `C(W) ≤ log₂ |α|` (Cover–Thomas §7.1, property (2)). -/
theorem capacity_le_log_card_input (W : DMC α β) : W.capacity ≤ log2 (Fintype.card α) :=
  Real.sSup_le (fun _ ⟨P, hP⟩ => hP ▸ dmc_mutualInfo_le_log_card_input W P)
    (log2_natCast_nonneg _)

/-- `C(W) ≤ log₂ |β|` (Cover–Thomas §7.1, property (3)). -/
theorem capacity_le_log_card_output (W : DMC α β) : W.capacity ≤ log2 (Fintype.card β) :=
  Real.sSup_le (fun _ ⟨P, hP⟩ => hP ▸ dmc_mutualInfo_le_log_card_output W P)
    (log2_natCast_nonneg _)

/-- Characterization of capacity as a least upper bound: if `I(P) ≤ c` for all `P` and
`I(P₀) = c` for some `P₀`, then `C(W) = c`. -/
theorem capacity_eq_of_le_of_eq (W : DMC α β) {c : ℝ} (hle : ∀ P, W.mutualInfo P ≤ c)
    (P₀ : ProbDist α) (h₀ : W.mutualInfo P₀ = c) : W.capacity = c :=
  le_antisymm (csSup_le ⟨_, P₀, rfl⟩ (fun _ ⟨P, hP⟩ => hP ▸ hle P))
    (h₀ ▸ mutualInfo_le_capacity W P₀)

end DMCAPI

/-! ## Binary entropy: bridge to Mathlib's `Real.binEntropy`

The `private` facts below duplicate public ones in `Known/Entropy.lean` (to be deduplicated). -/

private lemma log2_two : log2 2 = 1 := div_self log_two_pos'.ne'

/-- The project's `binaryEntropy` (bits) is Mathlib's `Real.binEntropy` (nats) divided by
`log 2`, on `[0, 1]`. -/
theorem binaryEntropy_eq_binEntropy_div {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    binaryEntropy p = Real.binEntropy p / Real.log 2 := by
  unfold binaryEntropy
  rw [negPLogP_of_nonneg h0, negPLogP_of_nonneg (by linarith),
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
  unfold log2; ring

/-- Entropy of a distribution on `Bool` is at most one bit. -/
private lemma shannonEntropy_bool_le_one (P : ProbDist Bool) : shannonEntropy P ≤ 1 := by
  have := shannonEntropy_le_log_card' P
  simpa [log2_two] using this

private lemma shannonEntropy_uniform_bool :
    shannonEntropy (ProbDist.uniform : ProbDist Bool) = 1 := by
  rw [shannonEntropy_uniform]; simp [log2_two]

/-! ## Binary erasure channel (Cover–Thomas §7.1.5) -/

section BEC

variable {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)

/-- For the BEC, `I(X;Y) = (1 - ε) H(X)` (Cover–Thomas eq. (7.15)–(7.17)). -/
theorem bec_mutualInfo (P : ProbDist Bool) :
    (bec ε h0 h1).mutualInfo P = (1 - ε) * shannonEntropy P := by
  rw [mutualInfo_eq_entropy_output_sub]
  have hcond : ∀ x, ∑ y, negPLogP ((bec ε h0 h1).trans x y) = negPLogP ε + negPLogP (1 - ε) := by
    intro x; rw [Fintype.sum_option]; cases x <;> simp [bec, negPLogP_zero']
  have hY : shannonEntropy ((bec ε h0 h1).joint P).snd =
      negPLogP ε + ∑ b, negPLogP (P.pmf b * (1 - ε)) := by
    unfold shannonEntropy
    rw [Fintype.sum_option]
    congr 1
    · show negPLogP (∑ x, P.pmf x * ε) = _
      rw [← Finset.sum_mul, P.sum_one, one_mul]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      simp [joint_snd_pmf, bec]
  simp_rw [hcond, hY, negPLogP_mul (P.nonneg _) (by linarith : (0:ℝ) ≤ 1 - ε)]
  rw [← Finset.sum_mul, P.sum_one, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one,
    ← Finset.mul_sum]
  unfold shannonEntropy; ring

/-- **Capacity of the binary erasure channel**: `C(BEC(ε)) = 1 - ε` bits
(Cover–Thomas §7.1.5). -/
theorem bec_capacity : (bec ε h0 h1).capacity = 1 - ε := by
  refine capacity_eq_of_le_of_eq _ (fun P => ?_) ProbDist.uniform ?_
  · rw [bec_mutualInfo]
    nlinarith [shannonEntropy_bool_le_one P]
  · rw [bec_mutualInfo, shannonEntropy_uniform_bool, mul_one]

end BEC

/-! ## Binary symmetric channel (Cover–Thomas §7.1.4) -/

section BSC

variable {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- For the BSC, `I(X;Y) = H(Y) - h(p)` (Cover–Thomas eq. (7.5)–(7.8)). -/
theorem bsc_mutualInfo (P : ProbDist Bool) :
    (bsc p h0 h1).mutualInfo P = shannonEntropy ((bsc p h0 h1).joint P).snd - binaryEntropy p := by
  rw [mutualInfo_eq_entropy_output_sub]
  have hcond : ∀ x, ∑ y, negPLogP ((bsc p h0 h1).trans x y) = binaryEntropy p := by
    intro x; cases x <;> simp [bsc, binaryEntropy, add_comm]
  simp_rw [hcond, ← Finset.sum_mul, P.sum_one, one_mul]

/-- Uniform input to the BSC gives uniform output. -/
theorem bsc_joint_uniform_snd_pmf (y : Bool) :
    ((bsc p h0 h1).joint ProbDist.uniform).snd.pmf y = 1 / 2 := by
  rw [joint_snd_pmf]
  cases y <;> simp [bsc, ProbDist.uniform] <;> ring

/-- **Capacity of the binary symmetric channel**: `C(BSC(p)) = 1 - h(p)` bits
(Cover–Thomas §7.1.4). -/
theorem bsc_capacity : (bsc p h0 h1).capacity = 1 - binaryEntropy p := by
  refine capacity_eq_of_le_of_eq _ (fun P => ?_) ProbDist.uniform ?_
  · rw [bsc_mutualInfo]
    linarith [shannonEntropy_bool_le_one ((bsc p h0 h1).joint P).snd]
  · rw [bsc_mutualInfo]
    have : shannonEntropy ((bsc p h0 h1).joint ProbDist.uniform).snd = 1 := by
      unfold shannonEntropy
      simp_rw [bsc_joint_uniform_snd_pmf]
      rw [Fintype.sum_bool]
      have := binaryEntropy_half
      unfold binaryEntropy at this
      norm_num at this ⊢
      linarith
    rw [this]

end BSC

/-! ## Binary deletion channel: sanity checks of the definitions -/

section Deletion

private lemma subseqCount_nil_right {α : Type*} [DecidableEq α] (x : List α) :
    subseqCount x [] = 1 := by
  cases x <;> rfl

/-- A longer word cannot be a subsequence of a shorter one. -/
theorem subseqCount_eq_zero_of_length_lt {α : Type*} [DecidableEq α] :
    ∀ (x y : List α), x.length < y.length → subseqCount x y = 0
  | [], [], h => by simp at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.length_cons] at h
    rw [subseqCount, subseqCount_eq_zero_of_length_lt xs (b :: ys) (by simp; omega),
      subseqCount_eq_zero_of_length_lt xs ys (by omega)]
    simp

/-- For words of equal length, `y` occurs as a subsequence of `x` iff `x = y`, exactly once. -/
theorem subseqCount_of_length_eq {α : Type*} [DecidableEq α] :
    ∀ (x y : List α), x.length = y.length → subseqCount x y = if x = y then 1 else 0
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [subseqCount, subseqCount_eq_zero_of_length_lt xs (b :: ys) (by simp; omega),
      subseqCount_of_length_eq xs ys h]
    by_cases hab : a = b <;> by_cases hxy : xs = ys <;> simp [hab, hxy]

/-- With `d = 0` the deletion channel is noiseless: `Pr[Del₀(x) = y] = [x = y]`. -/
theorem deletionProb_zero (x y : List Bool) :
    deletionProb 0 x y = if x = y then 1 else 0 := by
  unfold deletionProb
  by_cases hxy : x = y
  · subst hxy; simp [subseqCount_of_length_eq]
  · simp only [hxy, ↓reduceIte]
    split_ifs with hl
    · rcases hl.lt_or_eq with hl | hl
      · simp [zero_pow (Nat.sub_ne_zero_of_lt hl)]
      · simp [subseqCount_of_length_eq x y hl.symm, hxy]
    · rfl

/-- Point-mass distribution. -/
private def pointMass {α : Type*} [Fintype α] [DecidableEq α] (a : α) : ProbDist α where
  pmf := fun x => if x = a then 1 else 0
  nonneg := fun x => by split_ifs <;> norm_num
  sum_one := by simp

/-- A deterministic input carries zero information through the deletion channel,
for every `d` (no range assumption needed). -/
private lemma deletionChannelMI_pointMass (d : ℝ) (n : ℕ) (x₀ : Fin n → Bool) :
    deletionChannelMI d n (pointMass x₀) = 0 := by
  unfold deletionChannelMI
  simp [pointMass, ite_mul]

/-- `C_n(d) ≥ 0` for every `d` and `n` (a deterministic input achieves `0`). -/
theorem binaryDeletionMaxMI_nonneg (d : ℝ) (n : ℕ) : 0 ≤ binaryDeletionMaxMI d n := by
  unfold binaryDeletionMaxMI
  by_cases hb : BddAbove { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = deletionChannelMI d n P }
  · exact le_csSup hb ⟨pointMass (fun _ => false), (deletionChannelMI_pointMass d n _).symm⟩
  · rw [Real.sSup_of_not_bddAbove hb]

/-- The set whose infimum defines `binaryDeletionCapacity d` is bounded below by `0`,
for every `d`. -/
theorem binaryDeletionCapacity_set_bddBelow (d : ℝ) :
    BddBelow { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = binaryDeletionMaxMI d n / (n : ℝ) } :=
  ⟨0, fun _ ⟨n, _, hr⟩ => hr ▸ div_nonneg (binaryDeletionMaxMI_nonneg d n) (Nat.cast_nonneg n)⟩

/-- `C(d) ≥ 0` for every `d`. -/
theorem binaryDeletionCapacity_nonneg (d : ℝ) : 0 ≤ binaryDeletionCapacity d :=
  le_csInf ⟨_, 1, one_pos, rfl⟩
    (fun _ ⟨n, _, hr⟩ => hr ▸ div_nonneg (binaryDeletionMaxMI_nonneg d n) (Nat.cast_nonneg n))

/-- `C(d) ≤ C_n(d)/n` for every `n ≥ 1`. -/
theorem binaryDeletionCapacity_le_maxMI_div (d : ℝ) {n : ℕ} (hn : 0 < n) :
    binaryDeletionCapacity d ≤ binaryDeletionMaxMI d n / n :=
  csInf_le (binaryDeletionCapacity_set_bddBelow d) ⟨n, hn, rfl⟩

private lemma sum_out_one (f : (Σ k : Fin (1 + 1), Fin k.1 → Bool) → ℝ) :
    ∑ y, f y = f ⟨0, Fin.elim0⟩ + ∑ v : Fin 1 → Bool, f ⟨1, v⟩ := by
  rw [Fintype.sum_sigma, Fin.sum_univ_succ, Fin.sum_univ_one]
  congr 1
  exact Fintype.sum_unique (ι := Fin 0 → Bool) (fun v => f ⟨0, v⟩)

private lemma deletionProb_one_nil (d : ℝ) (x : Fin 1 → Bool) :
    deletionProb d (List.ofFn x) (List.ofFn (Fin.elim0 : Fin 0 → Bool)) = d := by
  simp [deletionProb, subseqCount_nil_right]

private lemma deletionProb_one_one (d : ℝ) (x v : Fin 1 → Bool) :
    deletionProb d (List.ofFn x) (List.ofFn v) = if x = v then 1 - d else 0 := by
  have hxv : x = v ↔ x 0 = v 0 := by
    constructor
    · rintro rfl; rfl
    · intro h; funext i; rw [Fin.fin_one_eq_zero i]; exact h
  simp only [List.ofFn_succ, List.ofFn_zero, deletionProb, List.length_cons, List.length_nil,
    le_refl, ↓reduceIte, subseqCount, hxv]
  split_ifs <;> simp

/-- With one input bit, the deletion channel is an erasure channel:
`I(X;Y) = (1 - d) H(X)`. (Stated for `d ≤ 1`; the identity is purely algebraic and does not
need `0 ≤ d`.) -/
theorem deletionChannelMI_one {d : ℝ} (h1 : d ≤ 1) (P : ProbDist (Fin 1 → Bool)) :
    deletionChannelMI d 1 P = (1 - d) * shannonEntropy P := by
  unfold deletionChannelMI
  simp only []
  rw [sum_out_one]
  simp_rw [sum_out_one, deletionProb_one_nil, deletionProb_one_one]
  have e1 : ∑ x, P.pmf x * d = d := by rw [← Finset.sum_mul, P.sum_one, one_mul]
  have e2 : ∀ v : Fin 1 → Bool, ∑ x, P.pmf x * (if x = v then 1 - d else 0) = P.pmf v * (1 - d) := by
    intro v; simp [mul_ite]
  have e3 : ∀ x : Fin 1 → Bool, ∑ v, negPLogP (if x = v then 1 - d else 0) = negPLogP (1 - d) := by
    intro x; simp [apply_ite negPLogP, negPLogP_zero']
  simp_rw [e1, e2, e3, negPLogP_mul (P.nonneg _) (by linarith : (0:ℝ) ≤ 1 - d)]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, ← Finset.mul_sum, ← Finset.sum_mul,
    P.sum_one]
  unfold shannonEntropy; ring

/-- **Single-letter deletion capacity**: `C₁(d) = max_P I(X;Y) = 1 - d`, as for the erasure
channel (Cover–Thomas §7.1.5). Holds for `d ≤ 1`, in particular on `[0, 1]`. -/
theorem binaryDeletionMaxMI_one {d : ℝ} (h1 : d ≤ 1) : binaryDeletionMaxMI d 1 = 1 - d := by
  have hcard : log2 (Fintype.card (Fin 1 → Bool)) = 1 := by simp [log2_two]
  unfold binaryDeletionMaxMI
  apply le_antisymm
  · refine csSup_le ⟨_, ProbDist.uniform, rfl⟩ (fun _ ⟨P, hP⟩ => ?_)
    rw [hP, deletionChannelMI_one h1]
    have := shannonEntropy_le_log_card' P
    rw [hcard] at this
    nlinarith
  · have hb : BddAbove { m : ℝ | ∃ P : ProbDist (Fin 1 → Bool), m = deletionChannelMI d 1 P } := by
      refine ⟨1 - d, fun _ ⟨P, hP⟩ => ?_⟩
      rw [hP, deletionChannelMI_one h1]
      have := shannonEntropy_le_log_card' P
      rw [hcard] at this
      nlinarith
    refine le_csSup_of_le hb ⟨ProbDist.uniform, rfl⟩ ?_
    rw [deletionChannelMI_one h1, shannonEntropy_uniform, hcard, mul_one]

/-- **Upper bound** `C(d) ≤ 1 - d` for the binary deletion channel (the erasure-channel
bound; Dobrushin 1967, Mitzenmacher 2009 survey §2), for `d ≤ 1`. -/
theorem binaryDeletionCapacity_le_one_sub {d : ℝ} (h1 : d ≤ 1) :
    binaryDeletionCapacity d ≤ 1 - d := by
  have := binaryDeletionCapacity_le_maxMI_div d (n := 1) one_pos
  rwa [binaryDeletionMaxMI_one h1, Nat.cast_one, div_one] at this

private lemma sum_out (n : ℕ) (f : (Σ k : Fin (n + 1), Fin k.1 → Bool) → ℝ) :
    ∑ y, f y = ∑ i : Fin n, ∑ v : Fin i → Bool, f ⟨i.castSucc, v⟩ +
      ∑ v : Fin n → Bool, f ⟨Fin.last n, v⟩ := by
  rw [Fintype.sum_sigma, Fin.sum_univ_castSucc]
  rfl

/-- With `d = 0` the deletion channel is noiseless and `I(X;Y) = H(X)`. -/
theorem deletionChannelMI_zero (n : ℕ) (P : ProbDist (Fin n → Bool)) :
    deletionChannelMI 0 n P = shannonEntropy P := by
  unfold deletionChannelMI
  simp only [deletionProb_zero, apply_ite negPLogP, negPLogP_one', negPLogP_zero', ite_self,
    Finset.sum_const_zero, mul_zero, sub_zero]
  rw [sum_out]
  have hne : ∀ (i : Fin n) (x : Fin n → Bool) (v : Fin i → Bool), List.ofFn x ≠ List.ofFn v := by
    intro i x v h
    have := congrArg List.length h
    simp only [List.length_ofFn] at this
    omega
  have hfirst : ∀ (i : Fin n) (v : Fin i → Bool),
      negPLogP (∑ x, P.pmf x * if List.ofFn x = List.ofFn v then 1 else 0) = 0 := by
    intro i v; simp [hne i, negPLogP_zero']
  simp only [hfirst, Finset.sum_const_zero, zero_add]
  change ∑ v : Fin n → Bool, negPLogP (∑ x, P.pmf x * if List.ofFn x = List.ofFn v then 1 else 0) = _
  simp only [List.ofFn_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  simp [shannonEntropy]

private lemma log2_card_fin_bool (n : ℕ) : log2 (Fintype.card (Fin n → Bool)) = n := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  unfold log2
  rw [Real.log_pow, mul_div_assoc, div_self log_two_pos'.ne', mul_one]

/-- **Noiseless case**: `C_n(0) = n` (uniform input on `{0,1}ⁿ` is optimal). -/
theorem binaryDeletionMaxMI_zero (n : ℕ) : binaryDeletionMaxMI 0 n = n := by
  unfold binaryDeletionMaxMI
  simp only [deletionChannelMI_zero]
  have hle : ∀ P : ProbDist (Fin n → Bool), shannonEntropy P ≤ n := fun P =>
    (shannonEntropy_le_log_card' P).trans_eq (log2_card_fin_bool n)
  apply le_antisymm
  · exact csSup_le ⟨_, ProbDist.uniform, rfl⟩ (fun _ ⟨P, hP⟩ => hP ▸ hle P)
  · refine le_csSup_of_le ⟨n, fun _ ⟨P, hP⟩ => hP ▸ hle P⟩ ⟨ProbDist.uniform, rfl⟩ ?_
    rw [shannonEntropy_uniform, log2_card_fin_bool]

/-- **Noiseless deletion channel**: `C(0) = 1` bit per channel use. -/
theorem binaryDeletionCapacity_zero : binaryDeletionCapacity 0 = 1 := by
  unfold binaryDeletionCapacity
  have hset : { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = binaryDeletionMaxMI 0 n / (n : ℝ) } = {1} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, binaryDeletionMaxMI_zero]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact div_self (by exact_mod_cast hn.ne')
    · rintro rfl
      exact ⟨1, one_pos, by simp⟩
  rw [hset, csInf_singleton]

/-- Crude count bound: `y` occurs at most `2^|x|` times as a subsequence of `x`. -/
private lemma subseqCount_le_two_pow {α : Type*} [DecidableEq α] :
    ∀ (x y : List α), subseqCount x y ≤ 2 ^ x.length
  | [], [] => le_rfl
  | [], _ :: _ => Nat.zero_le _
  | _ :: _, [] => Nat.one_le_two_pow
  | a :: xs, b :: ys => by
    rw [subseqCount, List.length_cons, pow_succ, mul_two]
    refine Nat.add_le_add (subseqCount_le_two_pow xs (b :: ys)) ?_
    split_ifs
    · exact subseqCount_le_two_pow xs ys
    · exact Nat.zero_le _

private lemma deletionProb_nonneg {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (x y : List Bool) :
    0 ≤ deletionProb d x y := by
  unfold deletionProb
  split_ifs
  · have : (0 : ℝ) ≤ 1 - d := by linarith
    positivity
  · exact le_rfl

private lemma deletionProb_le {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (x y : List Bool) :
    deletionProb d x y ≤ 2 ^ x.length := by
  unfold deletionProb
  split_ifs
  · have hc : (subseqCount x y : ℝ) ≤ 2 ^ x.length := by exact_mod_cast subseqCount_le_two_pow x y
    have ha : (1 - d) ^ y.length ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hb : d ^ (x.length - y.length) ≤ 1 := pow_le_one₀ h0 h1
    have ha0 : 0 ≤ (1 - d) ^ y.length := pow_nonneg (by linarith) _
    have hb0 : 0 ≤ d ^ (x.length - y.length) := pow_nonneg h0 _
    calc (subseqCount x y : ℝ) * (1 - d) ^ y.length * d ^ (x.length - y.length)
        ≤ 2 ^ x.length * 1 * 1 := by gcongr
      _ = 2 ^ x.length := by ring
  · positivity

private lemma negPLogP_le_inv_log_two (p : ℝ) : negPLogP p ≤ 1 / Real.log 2 := by
  rcases le_or_gt p 0 with hp | hp
  · rw [show negPLogP p = 0 by simp [negPLogP, hp]]; exact (one_div_pos.2 log_two_pos').le
  · rw [le_div_iff₀ log_two_pos', negPLogP_mul_log_two hp.le]
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hp)
    rw [Real.log_inv] at h
    have : p * p⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    nlinarith

private lemma negPLogP_ge_of_le {p M : ℝ} (hp : 0 ≤ p) (hM : 1 ≤ M) (hpM : p ≤ M) :
    -(M * log2 M) ≤ negPLogP p := by
  rw [← mul_le_mul_iff_of_pos_right log_two_pos', negPLogP_mul_log_two hp]
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have h2 : -(M * log2 M) * Real.log 2 = -(M * Real.log M) := by
    unfold log2; field_simp
  rw [h2]
  rcases hp.eq_or_lt with h | h
  · rw [← h]; simp; positivity
  · have := Real.log_le_log h hpM
    nlinarith

/-- For `d ∈ [0,1]`, the per-block mutual informations of the deletion channel are bounded
above (crude bound), so `binaryDeletionMaxMI d n` is a genuine supremum. -/
theorem binaryDeletionMaxMI_set_bddAbove {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (n : ℕ) :
    BddAbove { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = deletionChannelMI d n P } := by
  set K : ℝ := ((Fintype.card (Σ k : Fin (n + 1), Fin k.1 → Bool) : ℕ) : ℝ) with hK
  set M : ℝ := 2 ^ n
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  refine ⟨K * (1 / Real.log 2) + K * (M * log2 M), fun _ ⟨P, hP⟩ => ?_⟩
  rw [hP]
  unfold deletionChannelMI
  have hY : ∑ y : Σ k : Fin (n + 1), Fin k.1 → Bool,
      negPLogP (∑ x : Fin n → Bool, P.pmf x * deletionProb d (List.ofFn x) (List.ofFn y.2)) ≤
        K * (1 / Real.log 2) := by
    calc _ ≤ ∑ _y : Σ k : Fin (n + 1), Fin k.1 → Bool, 1 / Real.log 2 :=
          Finset.sum_le_sum (fun y _ => negPLogP_le_inv_log_two _)
      _ = K * (1 / Real.log 2) := by simp [K]
  have hYX : -(K * (M * log2 M)) ≤ ∑ x : Fin n → Bool, P.pmf x *
      ∑ y : Σ k : Fin (n + 1), Fin k.1 → Bool,
        negPLogP (deletionProb d (List.ofFn x) (List.ofFn y.2)) := by
    have hin : ∀ x : Fin n → Bool, -(K * (M * log2 M)) ≤
        ∑ y : Σ k : Fin (n + 1), Fin k.1 → Bool,
          negPLogP (deletionProb d (List.ofFn x) (List.ofFn y.2)) := by
      intro x
      calc -(K * (M * log2 M)) = ∑ _y : Σ k : Fin (n + 1), Fin k.1 → Bool, -(M * log2 M) := by
            simp [K]
        _ ≤ _ := Finset.sum_le_sum (fun y _ => negPLogP_ge_of_le
            (deletionProb_nonneg h0 h1 _ _) hM
            (by simpa [M] using deletionProb_le h0 h1 (List.ofFn x) (List.ofFn y.2)))
    calc -(K * (M * log2 M)) = ∑ x : Fin n → Bool, P.pmf x * -(K * (M * log2 M)) := by
          rw [← Finset.sum_mul, P.sum_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hin x) (P.nonneg x))
  linarith

/-- `I(Xⁿ;Y) ≤ C_n(d)` for every input distribution, when `d ∈ [0,1]`. -/
theorem deletionChannelMI_le_binaryDeletionMaxMI {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (n : ℕ)
    (P : ProbDist (Fin n → Bool)) : deletionChannelMI d n P ≤ binaryDeletionMaxMI d n :=
  le_csSup (binaryDeletionMaxMI_set_bddAbove h0 h1 n) ⟨P, rfl⟩

end Deletion

/-! ## Noiseless channel (Cover–Thomas §7.1.1) -/

section Noiseless

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The noiseless (identity) channel on a finite alphabet. -/
def noiselessChannel : DMC α α where
  trans := fun x y => if x = y then 1 else 0
  nonneg := fun x y => by split_ifs <;> norm_num
  sum_one := fun x => by simp

/-- Across the noiseless channel, `I(X;Y) = H(X)`. -/
theorem noiselessChannel_mutualInfo (P : ProbDist α) :
    (noiselessChannel α).mutualInfo P = shannonEntropy P := by
  rw [mutualInfo_eq_entropy_output_sub]
  have hcond : ∀ x, ∑ y, negPLogP ((noiselessChannel α).trans x y) = 0 := by
    intro x; simp [noiselessChannel, apply_ite negPLogP, negPLogP_one', negPLogP_zero']
  simp only [hcond, mul_zero, Finset.sum_const_zero, sub_zero]
  unfold shannonEntropy
  congr 1; funext y
  simp [joint_snd_pmf, noiselessChannel]

/-- **Capacity of the noiseless channel**: `C = log₂ |α|` bits (Cover–Thomas §7.1.1;
for `α = Fin k` this is `log₂ k`). -/
theorem noiselessChannel_capacity [Nonempty α] :
    (noiselessChannel α).capacity = log2 (Fintype.card α) := by
  refine capacity_eq_of_le_of_eq _ (fun P => ?_) ProbDist.uniform ?_
  · rw [noiselessChannel_mutualInfo]; exact shannonEntropy_le_log_card' P
  · rw [noiselessChannel_mutualInfo, shannonEntropy_uniform]

/-- `C(noiseless on Fin k) = log₂ k`. -/
theorem noiselessChannel_fin_capacity (k : ℕ) [NeZero k] :
    (noiselessChannel (Fin k)).capacity = log2 k := by
  rw [noiselessChannel_capacity, Fintype.card_fin]

end Noiseless

/-! ## Junk values outside the documented parameter range

These are *not* bugs affecting any current problem statement (all deletion-channel statements
in `Problems/` assume `0 < d < 1`), but they document that `binaryDeletionMaxMI` does not
enforce `d ∈ [0, 1]`, so any new statement must carry that hypothesis explicitly. -/

namespace DefinitionBugs

/-- Junk value: with `d = -1` the "deletion probability" `1 - d = 2` exceeds `1`, and the
single-letter maximal "mutual information" is `2` bits, more than the `log₂ 2 = 1` bit of
input entropy that a genuine `I(X;Y)` can carry (textbook: `C₁ ≤ log₂ |input|`). -/
theorem binaryDeletionMaxMI_neg_one_one : binaryDeletionMaxMI (-1) 1 = 2 := by
  rw [binaryDeletionMaxMI_one (by norm_num)]; norm_num

end DefinitionBugs

end InfoTheory.Known
