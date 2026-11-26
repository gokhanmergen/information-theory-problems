import InfoTheory.Core
import InfoTheory.Bridge.Mathlib
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Known facts about the core entropy definitions
-/

open scoped BigOperators
open Real

namespace InfoTheory.Known

-- Canonical versions live in `InfoTheory.Bridge` (proved via Mathlib's `klDiv`/`hammingDist`).
open InfoTheory.Bridge (pmf_le_one shannonEntropy_nonneg klDivergence_nonneg shannonEntropy_le_log2_card mutualInfo_nonneg)

open InfoTheory

private lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- `negPLogP` agrees with Mathlib's `Real.negMulLog` (in nats) divided by `log 2`
on `[0, ∞)`. -/
theorem negPLogP_eq_negMulLog {p : ℝ} (hp : 0 ≤ p) :
    negPLogP p = Real.negMulLog p / Real.log 2 := by
  unfold negPLogP log2 Real.negMulLog
  split_ifs with h
  · have : p = 0 := le_antisymm h hp
    simp [this]
  · ring

/-- Nonnegativity of the entropy summand: `-p log₂ p ≥ 0` for `p ∈ [0,1]`
(Cover–Thomas Lemma 2.1.1). -/
theorem negPLogP_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ negPLogP p := by
  rw [negPLogP_eq_negMulLog hp0]
  exact div_nonneg (Real.negMulLog_nonneg hp0 hp1) log_two_pos'.le

/-- Shannon entropy in bits is the natural-log entropy divided by `log 2`. -/
theorem shannonEntropy_eq_sum_negMulLog {α : Type*} [Fintype α] (P : ProbDist α) :
    shannonEntropy P = (∑ a, Real.negMulLog (P.pmf a)) / Real.log 2 := by
  unfold shannonEntropy
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun a _ => negPLogP_eq_negMulLog (P.nonneg a))

/-- Core termwise inequality behind Gibbs: if `q ≥ 0` and (`p > 0 → q > 0`), then
`p log (p/q) ≥ p - q` (with the convention that the term is `0` when `p ≤ 0`). -/
theorem gibbs_term {p q : ℝ} (hq : 0 ≤ q) (hac : 0 < p → 0 < q) :
    p - q ≤ (if p ≤ 0 then 0 else p * Real.log (p / q)) := by
  split_ifs with h
  · linarith
  · have hp' : 0 < p := lt_of_not_ge h
    have hq' := hac hp'
    have := Real.one_sub_inv_le_log_of_pos (div_pos hp' hq')
    rw [inv_div] at this
    have h2 : p * (1 - q / p) = p - q := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this hp'.le]

/-- Generalized Gibbs inequality (nats) for real weights: if `q` dominates the support
of `p` (`q ≥ 0`) and `∑ q ≤ ∑ p`, then `∑ p log (p/q) ≥ 0`. -/
theorem gibbs_sum {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hac : ∀ i ∈ s, 0 < p i → 0 < q i)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    0 ≤ ∑ i ∈ s, (if p i ≤ 0 then 0 else p i * Real.log (p i / q i)) := by
  have h1 : ∑ i ∈ s, (p i - q i) ≤
      ∑ i ∈ s, (if p i ≤ 0 then 0 else p i * Real.log (p i / q i)) :=
    Finset.sum_le_sum (fun i hi => gibbs_term (hq i hi) (hac i hi))
  rw [Finset.sum_sub_distrib] at h1
  linarith

/-- `D(P ‖ P) = 0` (Cover–Thomas Thm 2.6.3, equality case). -/
theorem klDivergence_self {α : Type*} [Fintype α] (P : ProbDist α) : klDivergence P P = 0 := by
  unfold klDivergence
  refine Finset.sum_eq_zero (fun a _ => ?_)
  split_ifs with h
  · rfl
  · rw [div_self (ne_of_gt (lt_of_not_ge h)), log2, Real.log_one, zero_div, mul_zero]

/-- Entropy of the uniform distribution: `H(U_α) = log₂ |α|` (Cover–Thomas Thm 2.6.4). -/
theorem shannonEntropy_uniform {α : Type*} [Fintype α] [Nonempty α] :
    shannonEntropy (ProbDist.uniform : ProbDist α) = log2 (Fintype.card α) := by
  have hn : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  rw [shannonEntropy_eq_sum_negMulLog]
  simp only [ProbDist.uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.negMulLog, log2, one_div, Real.log_inv]
  field_simp

/-! ### Joint, conditional and mutual information -/

section Joint

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A joint probability is at most the first marginal: `P(a,b) ≤ P_X(a)`. -/
theorem pmf_le_fst (P : ProbDist (α × β)) (a : α) (b : β) : P.pmf (a, b) ≤ P.fst.pmf a :=
  Finset.single_le_sum (f := fun b => P.pmf (a, b)) (fun b _ => P.nonneg (a, b))
    (Finset.mem_univ b)

/-- A joint probability is at most the second marginal: `P(a,b) ≤ P_Y(b)`. -/
theorem pmf_le_snd (P : ProbDist (α × β)) (a : α) (b : β) : P.pmf (a, b) ≤ P.snd.pmf b :=
  Finset.single_le_sum (f := fun a => P.pmf (a, b)) (fun a _ => P.nonneg (a, b))
    (Finset.mem_univ a)

private lemma neg_mul_log_le_negMulLog {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    -x * Real.log y ≤ Real.negMulLog x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · rw [Real.negMulLog]
    have := Real.log_le_log h hxy
    nlinarith

/-- Conditioning on more cannot make the joint entropy smaller than a marginal:
`H(Y) ≤ H(X,Y)` (Cover–Thomas Thm 2.2.1 + Thm 2.6.5 / chain rule with `H(X|Y) ≥ 0`). -/
theorem shannonEntropy_snd_le (P : ProbDist (α × β)) :
    shannonEntropy P.snd ≤ shannonEntropy P := by
  rw [shannonEntropy_eq_sum_negMulLog, shannonEntropy_eq_sum_negMulLog]
  refine div_le_div_of_nonneg_right ?_ log_two_pos'.le
  calc ∑ b, Real.negMulLog (P.snd.pmf b)
      = ∑ b, ∑ a, -P.pmf (a, b) * Real.log (P.snd.pmf b) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Real.negMulLog, ← Finset.sum_mul, Finset.sum_neg_distrib]
        rfl
    _ ≤ ∑ b, ∑ a, Real.negMulLog (P.pmf (a, b)) :=
        Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun a _ =>
          neg_mul_log_le_negMulLog (P.nonneg (a, b)) (pmf_le_snd P a b)))
    _ = ∑ ab, Real.negMulLog (P.pmf ab) :=
        (Fintype.sum_prod_type_right (fun ab => Real.negMulLog (P.pmf ab))).symm

/-- `H(X) ≤ H(X,Y)`. -/
theorem shannonEntropy_fst_le (P : ProbDist (α × β)) :
    shannonEntropy P.fst ≤ shannonEntropy P := by
  rw [shannonEntropy_eq_sum_negMulLog, shannonEntropy_eq_sum_negMulLog]
  refine div_le_div_of_nonneg_right ?_ log_two_pos'.le
  calc ∑ a, Real.negMulLog (P.fst.pmf a)
      = ∑ a, ∑ b, -P.pmf (a, b) * Real.log (P.fst.pmf a) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Real.negMulLog, ← Finset.sum_mul, Finset.sum_neg_distrib]
        rfl
    _ ≤ ∑ a, ∑ b, Real.negMulLog (P.pmf (a, b)) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
          neg_mul_log_le_negMulLog (P.nonneg (a, b)) (pmf_le_fst P a b)))
    _ = ∑ ab, Real.negMulLog (P.pmf ab) :=
        (Fintype.sum_prod_type (fun ab => Real.negMulLog (P.pmf ab))).symm

/-- Nonnegativity of conditional entropy, `H(X | Y) ≥ 0` for discrete variables
(Cover–Thomas Thm 2.2.1 / Lemma 2.1.1). -/
theorem condEntropy_nonneg (P : ProbDist (α × β)) : 0 ≤ condEntropy P := by
  unfold condEntropy
  linarith [shannonEntropy_snd_le P]

/-- `I(X;Y) ≤ H(X)` (Cover–Thomas Thm 2.4.1 / eq. (2.45)). -/
theorem mutualInfo_le_entropy_fst (P : ProbDist (α × β)) :
    mutualInfo P ≤ shannonEntropy P.fst := by
  unfold mutualInfo
  linarith [shannonEntropy_snd_le P]

/-- `I(X;Y) ≤ H(Y)`. -/
theorem mutualInfo_le_entropy_snd (P : ProbDist (α × β)) :
    mutualInfo P ≤ shannonEntropy P.snd := by
  unfold mutualInfo
  linarith [shannonEntropy_fst_le P]

/-- Mutual information is the (nat-valued) divergence between the joint and the product
of marginals, scaled to bits: `I(X;Y) = D(P_{XY} ‖ P_X ⊗ P_Y)` (Cover–Thomas eq. (2.29)). -/
theorem mutualInfo_mul_log_two (P : ProbDist (α × β)) :
    mutualInfo P * Real.log 2 = ∑ ab : α × β, (if P.pmf ab ≤ 0 then 0 else
      P.pmf ab * Real.log (P.pmf ab / (P.fst.pmf ab.1 * P.snd.pmf ab.2))) := by
  have hterm : ∀ ab : α × β, (if P.pmf ab ≤ 0 then 0 else
      P.pmf ab * Real.log (P.pmf ab / (P.fst.pmf ab.1 * P.snd.pmf ab.2))) =
      -Real.negMulLog (P.pmf ab) - P.pmf ab * Real.log (P.fst.pmf ab.1)
        - P.pmf ab * Real.log (P.snd.pmf ab.2) := by
    rintro ⟨a, b⟩
    split_ifs with h
    · have : P.pmf (a, b) = 0 := le_antisymm h (P.nonneg _)
      simp [this]
    · have hp : 0 < P.pmf (a, b) := lt_of_not_ge h
      have ha : 0 < P.fst.pmf a := lt_of_lt_of_le hp (pmf_le_fst P a b)
      have hb : 0 < P.snd.pmf b := lt_of_lt_of_le hp (pmf_le_snd P a b)
      rw [Real.log_div hp.ne' (mul_pos ha hb).ne', Real.log_mul ha.ne' hb.ne', Real.negMulLog]
      ring
  have hA : ∑ ab : α × β, P.pmf ab * Real.log (P.fst.pmf ab.1) =
      -∑ a, Real.negMulLog (P.fst.pmf a) := by
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    dsimp only
    rw [← Finset.sum_mul, Real.negMulLog]
    change P.fst.pmf a * _ = _
    ring
  have hB : ∑ ab : α × β, P.pmf ab * Real.log (P.snd.pmf ab.2) =
      -∑ b, Real.negMulLog (P.snd.pmf b) := by
    rw [Fintype.sum_prod_type_right, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    dsimp only
    rw [← Finset.sum_mul, Real.negMulLog]
    change P.snd.pmf b * _ = _
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hA, hB]
  unfold mutualInfo
  rw [shannonEntropy_eq_sum_negMulLog, shannonEntropy_eq_sum_negMulLog,
    shannonEntropy_eq_sum_negMulLog]
  field_simp
  ring

/-- Subadditivity of entropy: `H(X,Y) ≤ H(X) + H(Y)` (Cover–Thomas Thm 2.6.6). -/
theorem shannonEntropy_le_add (P : ProbDist (α × β)) :
    shannonEntropy P ≤ shannonEntropy P.fst + shannonEntropy P.snd := by
  have := mutualInfo_nonneg P
  unfold mutualInfo at this
  linarith

/-- Conditioning reduces entropy: `H(X | Y) ≤ H(X)` (Cover–Thomas Thm 2.6.5). -/
theorem condEntropy_le_entropy_fst (P : ProbDist (α × β)) :
    condEntropy P ≤ shannonEntropy P.fst := by
  unfold condEntropy
  linarith [shannonEntropy_le_add P]

/-- The first marginal of an independent product is the first factor (at the level of
entropy). -/
theorem shannonEntropy_prod_fst (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy (P.prod Q).fst = shannonEntropy P := by
  unfold shannonEntropy
  simp [ProbDist.fst, ProbDist.prod, ← Finset.mul_sum, Q.sum_one]

/-- The second marginal of an independent product is the second factor (at the level of
entropy). -/
theorem shannonEntropy_prod_snd (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy (P.prod Q).snd = shannonEntropy Q := by
  unfold shannonEntropy
  simp [ProbDist.snd, ProbDist.prod, ← Finset.sum_mul, P.sum_one]

/-- Additivity of entropy for independent variables: `H(X,Y) = H(X) + H(Y)` when
`X ⊥ Y` (Cover–Thomas Thm 2.6.6, equality case). -/
theorem shannonEntropy_prod (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy (P.prod Q) = shannonEntropy P + shannonEntropy Q := by
  rw [shannonEntropy_eq_sum_negMulLog, shannonEntropy_eq_sum_negMulLog,
    shannonEntropy_eq_sum_negMulLog, ← add_div]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [ProbDist.prod, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Q.sum_one, P.sum_one, one_mul]

/-- Independent variables have zero mutual information: `I(X;Y) = 0` for `P_X ⊗ P_Y`
(Cover–Thomas Thm 2.6.3, equality case). -/
theorem mutualInfo_prod (P : ProbDist α) (Q : ProbDist β) : mutualInfo (P.prod Q) = 0 := by
  unfold mutualInfo
  rw [shannonEntropy_prod_fst, shannonEntropy_prod_snd, shannonEntropy_prod]
  ring

end Joint

/-! ### Binary entropy -/

/-- The project's `binaryEntropy` (bits) is Mathlib's `Real.binEntropy` (nats) divided by
`log 2`, on `[0,1]` (Cover–Thomas eq. (2.5)). -/
theorem binaryEntropy_eq_binEntropy {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p = Real.binEntropy p / Real.log 2 := by
  rw [binaryEntropy, negPLogP_eq_negMulLog hp0, negPLogP_eq_negMulLog (sub_nonneg.2 hp1),
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_div]

/-- Symmetry of binary entropy, `h(p) = h(1 - p)` (holds for every real `p`). -/
theorem binaryEntropy_symm (p : ℝ) : binaryEntropy p = binaryEntropy (1 - p) := by
  rw [binaryEntropy, binaryEntropy, sub_sub_cancel, add_comm]

/-- Nonnegativity of binary entropy on `[0,1]`. -/
theorem binaryEntropy_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binaryEntropy p :=
  add_nonneg (negPLogP_nonneg hp0 hp1) (negPLogP_nonneg (by linarith) (by linarith))

/-- Binary entropy is at most one bit, `h(p) ≤ 1` on `[0,1]` (Cover–Thomas Example 2.1.1). -/
theorem binaryEntropy_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : binaryEntropy p ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy hp0 hp1, div_le_one log_two_pos']
  exact Real.binEntropy_le_log_two

/-- `h(1/2) = 1` bit (Cover–Thomas Example 2.1.1). -/
theorem binaryEntropy_half : binaryEntropy (1 / 2) = 1 := by
  rw [binaryEntropy_eq_binEntropy (by norm_num) (by norm_num), one_div, Real.binEntropy_two_inv,
    div_self log_two_pos'.ne']

/-- The entropy of a Bernoulli(`p`) distribution is the binary entropy `h(p)`
(Cover–Thomas Example 2.1.1). -/
theorem shannonEntropy_bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    shannonEntropy (ProbDist.bernoulli p hp0 hp1) = binaryEntropy p := by
  simp [shannonEntropy, ProbDist.bernoulli, binaryEntropy]

/-! ### Conditional mutual information -/

section Triple

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

private lemma sum_ite_single {ι : Type*} [Fintype ι] (c : ι) (p : ι → Prop)
    {_ : DecidablePred p} (f : ι → ℝ) (hp : ∀ i, p i ↔ i = c) :
    (∑ i, if p i then f i else 0) = f c := by
  rw [Finset.sum_eq_single c (fun i _ hi => ite_eq_right (fun h => hi ((hp i).1 h))) (by simp)]
  exact ite_eq_left ((hp c).2 rfl)

/-- The `(X,Z)`-marginal of a triple distribution: `P_{XZ}(a,c) = ∑_b P(a,b,c)`. -/
theorem map_xz_pmf (P : ProbDist (α × β × γ)) (a : α) (c : γ) :
    (P.map (fun t => (t.1, t.2.2))).pmf (a, c) = ∑ b, P.pmf (a, b, c) := by
  unfold ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    exact sum_ite_single c _ _ (by simp)
  · intro x _ hx
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun z _ => ite_eq_right ?_))
    simp [hx]
  · simp

/-- The `(Y,Z)`-marginal of a triple distribution: `P_{YZ}(b,c) = ∑_a P(a,b,c)`. -/
theorem map_yz_pmf (P : ProbDist (α × β × γ)) (b : β) (c : γ) :
    (P.map (fun t => (t.2.1, t.2.2))).pmf (b, c) = ∑ a, P.pmf (a, b, c) := by
  unfold ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single b]
  · exact sum_ite_single c _ _ (by simp)
  · intro x _ hx
    refine Finset.sum_eq_zero (fun z _ => ite_eq_right ?_)
    simp [hx]
  · simp

/-- The `Z`-marginal of a triple distribution: `P_Z(c) = ∑_a ∑_b P(a,b,c)`. -/
theorem map_z_pmf (P : ProbDist (α × β × γ)) (c : γ) :
    (P.map (fun t => t.2.2)).pmf c = ∑ a, ∑ b, P.pmf (a, b, c) := by
  unfold ProbDist.map
  dsimp only
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  exact sum_ite_single c _ _ (by simp)

/-- Nonnegativity of conditional mutual information, `I(X;Y|Z) ≥ 0`
(Cover–Thomas Cor. to Thm 2.6.3, eq. (2.92)); equivalently the submodularity
`H(X,Z) + H(Y,Z) ≥ H(X,Y,Z) + H(Z)`, the basic Shannon inequality. -/
theorem condMutualInfo_nonneg (P : ProbDist (α × β × γ)) : 0 ≤ condMutualInfo P := by
  set Pxz : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2)) with hPxz
  set Pyz : ProbDist (β × γ) := P.map (fun t => (t.2.1, t.2.2)) with hPyz
  set Pz : ProbDist γ := P.map (fun t => t.2.2) with hPz
  have hX : ∀ a c, Pxz.pmf (a, c) = ∑ b, P.pmf (a, b, c) := map_xz_pmf P
  have hY : ∀ b c, Pyz.pmf (b, c) = ∑ a, P.pmf (a, b, c) := map_yz_pmf P
  have hZ : ∀ c, Pz.pmf c = ∑ a, ∑ b, P.pmf (a, b, c) := map_z_pmf P
  have hcmi : condMutualInfo P = shannonEntropy Pxz + shannonEntropy Pyz
      - shannonEntropy P - shannonEntropy Pz := rfl
  have hZX : ∀ c, ∑ a, Pxz.pmf (a, c) = Pz.pmf c := fun c => by simp only [hX, hZ]
  have hZY : ∀ c, ∑ b, Pyz.pmf (b, c) = Pz.pmf c := fun c => by
    simp only [hY, hZ]; exact Finset.sum_comm
  have leX : ∀ a b c, P.pmf (a, b, c) ≤ Pxz.pmf (a, c) := fun a b c => by
    rw [hX]
    exact Finset.single_le_sum (f := fun b => P.pmf (a, b, c)) (fun b _ => P.nonneg _)
      (Finset.mem_univ b)
  have leY : ∀ a b c, P.pmf (a, b, c) ≤ Pyz.pmf (b, c) := fun a b c => by
    rw [hY]
    exact Finset.single_le_sum (f := fun a => P.pmf (a, b, c)) (fun a _ => P.nonneg _)
      (Finset.mem_univ a)
  have leZ : ∀ a b c, P.pmf (a, b, c) ≤ Pz.pmf c := fun a b c => by
    rw [← hZX]
    exact (leX a b c).trans (Finset.single_le_sum (f := fun a => Pxz.pmf (a, c))
      (fun a _ => Pxz.nonneg _) (Finset.mem_univ a))
  -- Gibbs with the reference measure `q(a,b,c) = P(a,c) P(b,c) / P(c)`.
  have hsum : ∑ t : α × β × γ, Pxz.pmf (t.1, t.2.2) * Pyz.pmf (t.2.1, t.2.2) / Pz.pmf t.2.2
      = 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type_right, ← Pz.sum_one]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    dsimp only
    calc ∑ b, ∑ a, Pxz.pmf (a, c) * Pyz.pmf (b, c) / Pz.pmf c
        = ∑ b, (∑ a, Pxz.pmf (a, c)) * Pyz.pmf (b, c) / Pz.pmf c := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_mul, Finset.sum_div]
      _ = Pz.pmf c * Pz.pmf c / Pz.pmf c := by
          rw [hZX, ← Finset.sum_div, ← Finset.mul_sum, hZY]
      _ = Pz.pmf c := mul_self_div_self _
  have key := gibbs_sum Finset.univ P.pmf
    (fun t => Pxz.pmf (t.1, t.2.2) * Pyz.pmf (t.2.1, t.2.2) / Pz.pmf t.2.2)
    (fun t _ => div_nonneg (mul_nonneg (Pxz.nonneg _) (Pyz.nonneg _)) (Pz.nonneg _))
    (fun ⟨a, b, c⟩ _ hp => div_pos (mul_pos (lt_of_lt_of_le hp (leX a b c))
      (lt_of_lt_of_le hp (leY a b c))) (lt_of_lt_of_le hp (leZ a b c)))
    (by rw [hsum, P.sum_one])
  have hterm : ∀ t : α × β × γ, (if P.pmf t ≤ 0 then 0 else P.pmf t *
      Real.log (P.pmf t / (Pxz.pmf (t.1, t.2.2) * Pyz.pmf (t.2.1, t.2.2) / Pz.pmf t.2.2))) =
      -Real.negMulLog (P.pmf t) - P.pmf t * Real.log (Pxz.pmf (t.1, t.2.2))
        - P.pmf t * Real.log (Pyz.pmf (t.2.1, t.2.2)) + P.pmf t * Real.log (Pz.pmf t.2.2) := by
    rintro ⟨a, b, c⟩
    split_ifs with h
    · have : P.pmf (a, b, c) = 0 := le_antisymm h (P.nonneg _)
      simp [this]
    · have hp : 0 < P.pmf (a, b, c) := lt_of_not_ge h
      have hx : 0 < Pxz.pmf (a, c) := lt_of_lt_of_le hp (leX a b c)
      have hy : 0 < Pyz.pmf (b, c) := lt_of_lt_of_le hp (leY a b c)
      have hz : 0 < Pz.pmf c := lt_of_lt_of_le hp (leZ a b c)
      dsimp only
      rw [Real.log_div hp.ne' (div_pos (mul_pos hx hy) hz).ne',
        Real.log_div (mul_pos hx hy).ne' hz.ne', Real.log_mul hx.ne' hy.ne', Real.negMulLog]
      ring
  have hA : ∑ t : α × β × γ, P.pmf t * Real.log (Pxz.pmf (t.1, t.2.2)) =
      -∑ ac, Real.negMulLog (Pxz.pmf ac) := by
    conv_rhs => rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Fintype.sum_prod_type_right, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    dsimp only
    rw [← Finset.sum_mul, ← hX, Real.negMulLog]
    ring
  have hB : ∑ t : α × β × γ, P.pmf t * Real.log (Pyz.pmf (t.2.1, t.2.2)) =
      -∑ bc, Real.negMulLog (Pyz.pmf bc) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun bc _ => ?_)
    obtain ⟨b, c⟩ := bc
    dsimp only
    rw [← Finset.sum_mul, ← hY, Real.negMulLog]
    ring
  have hC : ∑ t : α × β × γ, P.pmf t * Real.log (Pz.pmf t.2.2) =
      -∑ c, Real.negMulLog (Pz.pmf c) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type_right,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    dsimp only
    simp only [← Finset.sum_mul]
    rw [Finset.sum_comm, ← hZ, Real.negMulLog]
    ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    hA, hB, hC] at key
  rw [hcmi, shannonEntropy_eq_sum_negMulLog, shannonEntropy_eq_sum_negMulLog,
    shannonEntropy_eq_sum_negMulLog, shannonEntropy_eq_sum_negMulLog]
  rw [← add_div, ← sub_div, ← sub_div]
  exact div_nonneg (by linarith) log_two_pos'.le

end Triple

end InfoTheory.Known

/-! ### Definition bugs / regression witnesses

These record places where the project's junk-value conventions make a textbook statement
false without extra hypotheses. -/

namespace InfoTheory.Known.DefinitionBugs

open InfoTheory

/-- REGRESSION WITNESS (junk value): without `AbsCont P Q`, `klDivergence` can be negative.
With `P = Bern(1/2)` and `Q = Bern(1)` (point mass at `true`), the `false` term is
`(1/2) · log₂((1/2)/0) = (1/2) · log₂ 0 = 0` by the conventions `x/0 = 0`, `log 0 = 0`, so
`klDivergence P Q = (1/2) log₂ (1/2) = -1/2`, whereas the textbook value is `+∞`.
(`klDivergenceEReal` correctly returns `⊤` here.) -/
theorem klDivergence_bern_half_bern_one :
    klDivergence (ProbDist.bernoulli (1 / 2) (by norm_num) (by norm_num))
      (ProbDist.bernoulli 1 (by norm_num) (by norm_num)) = -1 / 2 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp [klDivergence, ProbDist.bernoulli, log2]
  field_simp
  norm_num

/-- Gibbs' inequality fails for `klDivergence` without the absolute-continuity hypothesis. -/
theorem klDivergence_neg_without_absCont :
    ∃ P Q : ProbDist Bool, ¬ AbsCont P Q ∧ klDivergence P Q < 0 :=
  ⟨ProbDist.bernoulli (1 / 2) (by norm_num) (by norm_num),
    ProbDist.bernoulli 1 (by norm_num) (by norm_num),
    fun h => by
      have := h false (by simp [ProbDist.bernoulli])
      simp [ProbDist.bernoulli] at this
      norm_num at this,
    by rw [klDivergence_bern_half_bern_one]; norm_num⟩

end InfoTheory.Known.DefinitionBugs
