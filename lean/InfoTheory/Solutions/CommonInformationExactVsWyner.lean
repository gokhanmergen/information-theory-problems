import InfoTheory.Problems.CommonInformationExactVsWyner
import InfoTheory.Bridge.Coding
import InfoTheory.Known.Entropy

/-!
# Disproof of Finite-Letter Attainment for Exact Common Information

We disprove `InfoTheory.Problems.CommonInformationExactVsWyner.Statement` using the
Symmetric Binary Erasure Source `SBES(3/4)` on `Fin 2 × Fin 3`, where `X ~ Unif({0, 1})`
and `Y = X` with probability `1/4` or `Y = 2` (erasure) with probability `3/4`:
- `P(0, 0) = P(1, 1) = 1/8`
- `P(0, 2) = P(1, 2) = 3/8`
- `P(0, 1) = P(1, 0) = 0`.

## Proof Outline

1. **Strict finite-`n` lower bound (`exactCommonInfoSingle (P^{⊗ n}) / n > h(3/4)` for every `n ≥ 1`)**:
   For any `n ≥ 1` and any finite `W` with `X^n ⊥ Y^n | W` and `(X^n, Y^n) ~ P^{⊗ n}`:
   - Entropy identity: `H(W) - n h(3/4) = (n - H(X^n, Y^n | W)) + H(W | X^n, Y^n)`.
   - For every `w` with `P(W = w) > 0`, conditional independence and the SBES support
     force `H(X^n, Y^n | W = w) ≤ n`.
   - For `w ∈ A := {w | P(0^n, 0^n, w) > 0}`, `X^n = 0^n` a.s. given `W = w` and `Y^n` is
     supported on `{0, 2}^n`, so `n - H(X^n, Y^n | W = w) = D(P_{Y^n | w} ‖ Unif({0, 2}^n))`.
   - Pinsker's inequality + Cauchy–Schwarz gives
     `((1/8)^n - P(W ∈ A, X^n = 0^n, Y^n = 2^n))^2 ≤ 2 ln 2 · (n - H(X^n, Y^n | W))`.
   - Either `n - H(X^n, Y^n | W)` is bounded away from `0`, or
     `P(W ∈ A | X^n = 0^n, Y^n = 2^n)` is bounded away from `{0, 1}`, forcing
     `H(W | X^n, Y^n)` to be bounded away from `0`.
   - Taking the infimum over all finite `W` yields a uniform strict gap `c(n) > 0`.

2. **Asymptotic upper bound (`exactCommonInfo P ≤ h(3/4)`)**:
   - Decompose `supp(P^{⊗ n})` into constant-erasure shells `S_k` (`k` non-erasures),
     with weights `p_bin(n, k) = C(n, k) (1/4)^k (3/4)^{n-k}`.
   - For `2k ≤ n`, cover `S_k` by `M_k` random product rectangles `A_w × B_w` (`w = (T, u)`
     with `|T| = 2k`). A one-sided Chernoff / MGF finite-sum bound guarantees a deterministic
     list of `M_k` rectangles covering every `(x, y) ∈ S_k` at most `(1 + δ) M_k p_k` times,
     leaving mass `δ / (1 + δ)` for singleton atoms.
   - For `2k > n`, use singleton atoms; their total probability is `≤ (7/8)^n`.
   - Using `C(n, k) (1/4)^k (3/4)^{n-k} ≤ 1` directly yields
     `E[log₂ C(n, K)] ≤ n h(3/4)`, giving `H(W) / n ≤ h(3/4) + ε` for sufficiently large `n`.

Combining (1) and (2) gives `exactCommonInfo P ≤ h(3/4) < exactCommonInfoSingle (P^{⊗ n}) / n`
for every `n ≥ 1`, refuting `Statement`.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge InfoTheory.Problems.CommonInformationExactVsWyner

namespace InfoTheory.Solutions.CommonInformationExactVsWyner

/-! ### Section 1: Elementary `log2`, `binaryEntropy`, and `ProbDist` Helpers -/

section Helpers

private lemma probDist_ext {α : Type*} [Fintype α] {P Q : ProbDist α}
    (h : ∀ a : α, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

private lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma log2_one : log2 1 = 0 := by
  unfold log2; simp

private lemma log2_two : log2 2 = 1 := by
  unfold log2
  exact div_self (ne_of_gt log_two_pos)

private lemma log2_pow (x : ℝ) (k : ℕ) : log2 (x ^ k) = (k : ℝ) * log2 x := by
  unfold log2
  rw [Real.log_pow, mul_div_assoc]

private lemma log2_two_pow (k : ℕ) : log2 ((2 : ℝ) ^ k) = (k : ℝ) := by
  rw [log2_pow, log2_two, mul_one]

private lemma log2_le_log2 {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt log_two_pos)

private lemma log2_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x := by
  rw [← log2_one]
  exact log2_le_log2 (by norm_num) hx

private lemma log2_neg_of_pos_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : log2 x < 0 := by
  unfold log2
  exact div_neg_of_neg_of_pos (Real.log_neg hx0 hx1) log_two_pos

private lemma negPLogP_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    negPLogP (p * q) = p * negPLogP q + q * negPLogP p := by
  rcases eq_or_lt_of_le hp with rfl | hp_pos
  · simp [negPLogP]
  · rcases eq_or_lt_of_le hq with rfl | hq_pos
    · simp [negPLogP]
    · have hpq : 0 < p * q := mul_pos hp_pos hq_pos
      unfold negPLogP
      rw [ite_eq_right (not_le.mpr hpq), ite_eq_right (not_le.mpr hq_pos),
          ite_eq_right (not_le.mpr hp_pos), log2_mul_pos hp_pos hq_pos]
      ring

private lemma binaryEntropy_ge_neg_log2 {ε₀ q : ℝ}
    (hε0 : 0 < ε₀) (hε1 : ε₀ < 1) (hq1 : ε₀ ≤ q) (hq2 : q ≤ 1 - ε₀) :
    -log2 (1 - ε₀) ≤ binaryEntropy q := by
  have hq_pos : 0 < q := lt_of_lt_of_le hε0 hq1
  have h1mq_pos : 0 < 1 - q := by linarith
  have h1mq_le : 1 - q ≤ 1 - ε₀ := by linarith
  unfold binaryEntropy negPLogP
  rw [ite_eq_right (not_le.mpr hq_pos), ite_eq_right (not_le.mpr h1mq_pos)]
  have h1 : log2 q ≤ log2 (1 - ε₀) := log2_le_log2 hq_pos hq2
  have h2 : log2 (1 - q) ≤ log2 (1 - ε₀) := log2_le_log2 h1mq_pos h1mq_le
  nlinarith

/-- Conditional distribution `R(· | b)` for `b` with `R.snd.pmf b > 0`. -/
private noncomputable def condDist {α β : Type*} [Fintype α] [Fintype β]
    (R : ProbDist (α × β)) (b : β) (hb : 0 < R.snd.pmf b) : ProbDist α where
  pmf := fun a => R.pmf (a, b) / R.snd.pmf b
  nonneg := fun a => div_nonneg (R.nonneg (a, b)) (le_of_lt hb)
  sum_one := by
    rw [← Finset.sum_div]
    change R.snd.pmf b / R.snd.pmf b = 1
    exact div_self (ne_of_gt hb)

/-- Decomposition of conditional entropy `H(X | Y) = ∑_y P(y) H(X | Y = y)`. -/
private lemma condEntropy_eq_sum_condDist {α β : Type*} [Fintype α] [Fintype β]
    (R : ProbDist (α × β)) :
    condEntropy R =
      ∑ b : β, if h : 0 < R.snd.pmf b then
        R.snd.pmf b * shannonEntropy (condDist R b h)
      else 0 := by
  unfold condEntropy shannonEntropy
  rw [Fintype.sum_prod_type_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : 0 < R.snd.pmf b
  · rw [dite_eq_left hb]
    have hterm : ∀ a : α,
        R.snd.pmf b * negPLogP ((condDist R b hb).pmf a) =
          negPLogP (R.pmf (a, b)) + R.pmf (a, b) * log2 (R.snd.pmf b) := by
      intro a
      change R.snd.pmf b * negPLogP (R.pmf (a, b) / R.snd.pmf b) = _
      by_cases hab : R.pmf (a, b) ≤ 0
      · have hab0 : R.pmf (a, b) = 0 := le_antisymm hab (R.nonneg (a, b))
        simp [hab0, negPLogP]
      · have hab_pos : 0 < R.pmf (a, b) := lt_of_not_ge hab
        have hdiv_pos : 0 < R.pmf (a, b) / R.snd.pmf b := div_pos hab_pos hb
        unfold negPLogP
        rw [ite_eq_right (not_le.mpr hdiv_pos), ite_eq_right (not_le.mpr hab_pos),
            log2_div_pos hab_pos hb]
        have hbne : R.snd.pmf b ≠ 0 := ne_of_gt hb
        field_simp [hbne]
        ring
    rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    change (∑ a : α, negPLogP (R.pmf (a, b))) - negPLogP (R.snd.pmf b) =
      (∑ a : α, negPLogP (R.pmf (a, b))) + R.snd.pmf b * log2 (R.snd.pmf b)
    unfold negPLogP
    rw [ite_eq_right (not_le.mpr hb)]
    ring
  · rw [dite_eq_right hb]
    have hb0 : R.snd.pmf b = 0 := le_antisymm (not_lt.mp hb) (R.snd.nonneg b)
    have hall : ∀ a : α, R.pmf (a, b) = 0 := fun a => by
      have hle : R.pmf (a, b) ≤ R.snd.pmf b :=
        Finset.single_le_sum (fun a' _ => R.nonneg (a', b)) (Finset.mem_univ a)
      linarith [R.nonneg (a, b)]
    simp [hb0, hall, negPLogP]

/-- Support bound for Shannon entropy: if `P` is supported on `s`, then `H(P) ≤ log₂ |s|`. -/
private lemma shannonEntropy_le_log2_support {α : Type*} [Fintype α]
    (P : ProbDist α) (s : Finset α) (hs : s.Nonempty)
    (hsupp : ∀ a : α, 0 < P.pmf a → a ∈ s) :
    shannonEntropy P ≤ log2 (s.card : ℝ) := by
  have : Nonempty {a : α // a ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let Ps : ProbDist {a : α // a ∈ s} :=
    { pmf := fun a => P.pmf a.1
      nonneg := fun a => P.nonneg a.1
      sum_one := by
        rw [Finset.sum_coe_sort s (fun a => P.pmf a), ← P.sum_one]
        refine Finset.sum_subset (Finset.subset_univ s) fun a _ ha => ?_
        by_contra hne
        have hpos : 0 < P.pmf a := lt_of_le_of_ne (P.nonneg a) (Ne.symm hne)
        exact ha (hsupp a hpos) }
  have hent : shannonEntropy P = shannonEntropy Ps := by
    unfold shannonEntropy
    change ∑ a : α, negPLogP (P.pmf a) = ∑ a : {a : α // a ∈ s}, negPLogP (P.pmf a.1)
    rw [Finset.sum_coe_sort s (fun a => negPLogP (P.pmf a))]
    symm
    refine Finset.sum_subset (Finset.subset_univ s) fun a _ ha => ?_
    have h0 : P.pmf a = 0 := by
      by_contra hne
      exact ha (hsupp a (lt_of_le_of_ne (P.nonneg a) (Ne.symm hne)))
    simp [h0, negPLogP]
  rw [hent]
  have hle := shannonEntropy_le_log2_card Ps
  rwa [Fintype.card_coe] at hle

/-- Point-mass distribution `δ_{a₀}`. -/
private noncomputable def pointMass {α : Type*} [Fintype α] (a₀ : α) : ProbDist α := by
  classical
  exact
    { pmf := fun a => if a = a₀ then 1 else 0
      nonneg := fun a => by split_ifs <;> norm_num
      sum_one := by simp }

/-- Uniform distribution on a nonempty `Finset`. -/
private noncomputable def finsetUniform {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) : ProbDist α := by
  classical
  exact
    { pmf := fun a => if a ∈ s then (1 : ℝ) / (s.card : ℝ) else 0
      nonneg := fun a => by split_ifs <;> positivity
      sum_one := by
        have hpos : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        field_simp [hpos] }

/-- Disjoint-union mixture `p · P ⊕ (1 - p) · Q` on `α ⊕ β`. -/
private def sumDist {α β : Type*} [Fintype α] [Fintype β]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : ProbDist α) (Q : ProbDist β) :
    ProbDist (α ⊕ β) where
  pmf := Sum.elim (fun a => p * P.pmf a) (fun b => (1 - p) * Q.pmf b)
  nonneg := fun x => by
    cases x with
    | inl a => exact mul_nonneg hp0 (P.nonneg a)
    | inr b => exact mul_nonneg (by linarith) (Q.nonneg b)
  sum_one := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum, P.sum_one, Q.sum_one]
    ring

/-- Grouping property of Shannon entropy for disjoint-union mixtures:
    `H(p P ⊕ (1 - p) Q) = h(p) + p H(P) + (1 - p) H(Q)`. -/
private lemma shannonEntropy_sumDist {α β : Type*} [Fintype α] [Fintype β]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy (sumDist p hp0 hp1 P Q) =
      binaryEntropy p + p * shannonEntropy P + (1 - p) * shannonEntropy Q := by
  unfold shannonEntropy sumDist binaryEntropy
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h1 : ∑ a : α, negPLogP (p * P.pmf a) = negPLogP p + p * ∑ a : α, negPLogP (P.pmf a) := by
    simp_rw [negPLogP_mul hp0 (P.nonneg _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, P.sum_one, one_mul, add_comm]
  have h2 : ∑ b : β, negPLogP ((1 - p) * Q.pmf b) =
      negPLogP (1 - p) + (1 - p) * ∑ b : β, negPLogP (Q.pmf b) := by
    simp_rw [negPLogP_mul (show 0 ≤ 1 - p by linarith) (Q.nonneg _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Q.sum_one, one_mul, add_comm]
  rw [h1, h2]
  ring

/-- Hierarchical (sigma) distribution `P(i) * Q_i(a)` on `Σ i : ι, α i`. -/
private def sigmaDist {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist ι) (Q : (i : ι) → ProbDist (α i)) : ProbDist (Σ i : ι, α i) where
  pmf := fun x => P.pmf x.1 * (Q x.1).pmf x.2
  nonneg := fun x => mul_nonneg (P.nonneg x.1) ((Q x.1).nonneg x.2)
  sum_one := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (Q _).sum_one, mul_one]
    exact P.sum_one

/-- Grouping / chain rule for sigma distributions:
    `H(I, X) = H(I) + ∑_i P(i) H(X | I = i)`. -/
private lemma shannonEntropy_sigmaDist {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ProbDist ι) (Q : (i : ι) → ProbDist (α i)) :
    shannonEntropy (sigmaDist P Q) =
      shannonEntropy P + ∑ i : ι, P.pmf i * shannonEntropy (Q i) := by
  unfold shannonEntropy sigmaDist
  dsimp only
  rw [Fintype.sum_sigma]
  have hinner : ∀ i : ι,
      ∑ a : α i, negPLogP (P.pmf i * (Q i).pmf a) =
        negPLogP (P.pmf i) + P.pmf i * ∑ a : α i, negPLogP ((Q i).pmf a) := by
    intro i
    simp_rw [negPLogP_mul (P.nonneg i) ((Q i).nonneg _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, (Q i).sum_one, one_mul, add_comm]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]

/-- Product-mixture distribution on `X × Y × Fin (Fintype.card W)` induced by
    `pW : ProbDist W` and local kernels `PX : W → ProbDist X`, `PY : W → ProbDist Y`. -/
private noncomputable def prodMixDist {X Y W : Type*} [Fintype X] [Fintype Y] [Fintype W]
    (pW : ProbDist W) (PX : W → ProbDist X) (PY : W → ProbDist Y) :
    ProbDist (X × Y × Fin (Fintype.card W)) :=
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  { pmf := fun t => pW.pmf (e.symm t.2.2) * (PX (e.symm t.2.2)).pmf t.1 * (PY (e.symm t.2.2)).pmf t.2.1
    nonneg := fun t =>
      mul_nonneg (mul_nonneg (pW.nonneg _) ((PX _).nonneg _)) ((PY _).nonneg _)
    sum_one := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      trans (∑ w : Fin (Fintype.card W), pW.pmf (e.symm w))
      · trans (∑ x : X, ∑ w : Fin (Fintype.card W), ∑ y : Y,
            pW.pmf (e.symm w) * (PX (e.symm w)).pmf x * (PY (e.symm w)).pmf y)
        · refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp_rw [← Finset.mul_sum, (PY _).sum_one, mul_one, ← Finset.mul_sum, (PX _).sum_one, mul_one]
      · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).trans pW.sum_one }

private lemma prodMixDist_marginal_xy {X Y W : Type*} [Fintype X] [Fintype Y] [Fintype W]
    (pW : ProbDist W) (PX : W → ProbDist X) (PY : W → ProbDist Y) (x : X) (y : Y) :
    ((prodMixDist pW PX PY).map (fun t => (t.1, t.2.1))).pmf (x, y) =
      ∑ w : W, pW.pmf w * (PX w).pmf x * (PY w).pmf y := by
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  unfold ProbDist.map prodMixDist
  dsimp only
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
    · simp only [↓reduceIte]
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    · intro y' _ hy'
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hy']
    · intro h; exact absurd (Finset.mem_univ y) h
  · intro x' _ hx'
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun i _ => ?_
    simp [hx']
  · intro h; exact absurd (Finset.mem_univ x) h

private lemma prodMixDist_marginal_w {X Y W : Type*} [Fintype X] [Fintype Y] [Fintype W]
    (pW : ProbDist W) (PX : W → ProbDist X) (PY : W → ProbDist Y) (i : Fin (Fintype.card W)) :
    ((prodMixDist pW PX PY).map (fun t => t.2.2)).pmf i = pW.pmf ((Fintype.equivFin W).symm i) := by
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  unfold ProbDist.map prodMixDist
  dsimp only
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  trans (∑ x : X, ∑ y : Y, pW.pmf (e.symm i) * (PX (e.symm i)).pmf x * (PY (e.symm i)).pmf y)
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro i' _ hi'; simp [hi']
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp_rw [← Finset.mul_sum, (PY _).sum_one, mul_one, ← Finset.mul_sum, (PX _).sum_one, mul_one]
    rfl

private lemma prodMixDist_shannonEntropy_w {X Y W : Type*} [Fintype X] [Fintype Y] [Fintype W]
    (pW : ProbDist W) (PX : W → ProbDist X) (PY : W → ProbDist Y) :
    shannonEntropy ((prodMixDist pW PX PY).map (fun t => t.2.2)) = shannonEntropy pW := by
  unfold shannonEntropy
  simp_rw [prodMixDist_marginal_w]
  exact Fintype.sum_equiv (Fintype.equivFin W).symm _ _ (fun _ => rfl)

private lemma prodMixDist_condMutualInfo {X Y W : Type*} [Fintype X] [Fintype Y] [Fintype W]
    (pW : ProbDist W) (PX : W → ProbDist X) (PY : W → ProbDist Y) :
    condMutualInfo (prodMixDist pW PX PY) = 0 := by
  classical
  rw [condMutualInfo_eq_zero_iff]
  let Q := prodMixDist pW PX PY
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  have hQ_pmf : ∀ x y i, Q.pmf (x, y, i) =
      pW.pmf (e.symm i) * (PX (e.symm i)).pmf x * (PY (e.symm i)).pmf y := fun _ _ _ => rfl
  have hxz : ∀ x i, (Q.map (fun t => (t.1, t.2.2))).pmf (x, i) =
      pW.pmf (e.symm i) * (PX (e.symm i)).pmf x := by
    intro x i
    rw [InfoTheory.Known.map_xz_pmf]
    simp_rw [hQ_pmf, ← Finset.mul_sum, (PY _).sum_one, mul_one]
  have hyz : ∀ y i, (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, i) =
      pW.pmf (e.symm i) * (PY (e.symm i)).pmf y := by
    intro y i
    rw [InfoTheory.Known.map_yz_pmf]
    simp_rw [hQ_pmf, ← Finset.sum_mul, ← Finset.mul_sum, (PX _).sum_one, mul_one]
  have hz : ∀ i, (Q.map (fun t => t.2.2)).pmf i = pW.pmf (e.symm i) :=
    prodMixDist_marginal_w pW PX PY
  refine probDist_ext fun ⟨x, y, i⟩ => ?_
  change Q.pmf (x, y, i) =
    if (Q.map (fun t => t.2.2)).pmf i = 0 then 0 else
      (Q.map (fun t => (t.1, t.2.2))).pmf (x, i) *
      (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, i) /
      (Q.map (fun t => t.2.2)).pmf i
  rw [hQ_pmf, hxz, hyz, hz]
  by_cases hw : pW.pmf (e.symm i) = 0
  · simp [hw]
  · rw [ite_eq_right hw]
    field_simp [hw]

/-- The feasible set for `exactCommonInfoSingle P` is always nonempty (take `W = X × Y`). -/
private lemma exactCommonInfoSingle_set_nonempty {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) :
    ({ r : ℝ | ∃ (kW : ℕ) (Q : ProbDist (X × Y × Fin kW)),
      Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo Q = 0 ∧
      r = shannonEntropy (Q.map (fun t => t.2.2)) }).Nonempty := by
  let PX : X × Y → ProbDist X := fun xy => pointMass xy.1
  let PY : X × Y → ProbDist Y := fun xy => pointMass xy.2
  have hmarg : (prodMixDist P PX PY).map (fun t => (t.1, t.2.1)) = P := by
    refine probDist_ext fun ⟨x, y⟩ => ?_
    rw [prodMixDist_marginal_xy]
    dsimp only [PX, PY, pointMass]
    rw [Finset.sum_eq_single (x, y)]
    · simp
    · intro ⟨x', y'⟩ _ hne
      by_cases hx : x = x'
      · have hy : y ≠ y' := fun hy => hne (Prod.ext hx.symm hy.symm)
        simp [hx, hy]
      · simp [hx]
    · intro h; exact absurd (Finset.mem_univ (x, y)) h
  exact ⟨shannonEntropy P, Fintype.card (X × Y), prodMixDist P PX PY, hmarg,
    prodMixDist_condMutualInfo P PX PY, (prodMixDist_shannonEntropy_w P PX PY).symm⟩

private lemma exactCommonInfoSingle_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) :
    0 ≤ exactCommonInfoSingle P := by
  unfold exactCommonInfoSingle
  refine le_csInf (exactCommonInfoSingle_set_nonempty P) ?_
  rintro r ⟨_, Q, _, _, rfl⟩
  exact shannonEntropy_nonneg _

end Helpers

/-! ### Section 2: The Symmetric Binary Erasure Source `SBES(3/4)` -/

section SBES

private noncomputable def sbesPmf : Fin 2 × Fin 3 → ℝ
  | (0, 0) => 1 / 8
  | (1, 1) => 1 / 8
  | (0, 2) => 3 / 8
  | (1, 2) => 3 / 8
  | _ => 0

private noncomputable def sbes : ProbDist (Fin 2 × Fin 3) where
  pmf := sbesPmf
  nonneg := fun xy => by
    rcases xy with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> norm_num [sbesPmf]
  sum_one := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [Fin.sum_univ_three, sbesPmf]
    norm_num

private lemma sbes_support_cond (x : Fin 2) (y : Fin 3) (h : 0 < sbes.pmf (x, y)) :
    y = 2 ∨ y.val = x.val := by
  fin_cases x <;> fin_cases y <;> simp [sbes, sbesPmf] at h ⊢

private lemma sbes_pmf_of_mem (x : Fin 2) (y : Fin 3) (h : y = 2 ∨ y.val = x.val) :
    sbes.pmf (x, y) = if y = 2 then 3 / 8 else 1 / 8 := by
  fin_cases x <;> fin_cases y <;> simp [sbes, sbesPmf] at h ⊢

private lemma shannonEntropy_sbes :
    shannonEntropy sbes = 1 + binaryEntropy (3 / 4) := by
  unfold shannonEntropy binaryEntropy negPLogP
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.sum_univ_three, sbes, sbesPmf]
  have h18 : ¬ ((1 / 8 : ℝ) ≤ 0) := by norm_num
  have h38 : ¬ ((3 / 8 : ℝ) ≤ 0) := by norm_num
  have h34 : ¬ ((3 / 4 : ℝ) ≤ 0) := by norm_num
  have h14 : ¬ ((1 - 3 / 4 : ℝ) ≤ 0) := by norm_num
  have h0 : (0 : ℝ) ≤ 0 := le_rfl
  simp only [h18, h38, h34, h14, h0, ↓reduceIte]
  have hlog18 : log2 (1 / 8 : ℝ) = log2 (1 - 3 / 4 : ℝ) - 1 := by
    have : (1 / 8 : ℝ) = (1 - 3 / 4 : ℝ) / 2 := by norm_num
    rw [this, log2_div_pos (by norm_num) (by norm_num), log2_two]
  have hlog38 : log2 (3 / 8 : ℝ) = log2 (3 / 4 : ℝ) - 1 := by
    have : (3 / 8 : ℝ) = (3 / 4 : ℝ) / 2 := by norm_num
    rw [this, log2_div_pos (by norm_num) (by norm_num), log2_two]
  rw [hlog18, hlog38]
  ring

/-- `H(P^{⊗ n}) = n * H(P)` for any bipartite source `P`. -/
private lemma shannonEntropy_bipartitePower {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) :
    ∀ n : ℕ, shannonEntropy (bipartitePower P n) = (n : ℝ) * shannonEntropy P
  | 0 => by
    have hcard : Fintype.card ((Fin 0 → X) × (Fin 0 → Y)) = 1 := by simp
    have hle := shannonEntropy_le_log2_card (bipartitePower P 0)
    have hge := shannonEntropy_nonneg (bipartitePower P 0)
    rw [hcard, Nat.cast_one, log2_one] at hle
    simp; linarith
  | n + 1 => by
    let e : (X × Y) × ((Fin n → X) × (Fin n → Y)) ≃
        ((Fin (n + 1) → X) × (Fin (n + 1) → Y)) :=
      { toFun := fun p => (Fin.cons p.1.1 p.2.1, Fin.cons p.1.2 p.2.2)
        invFun := fun q => ((q.1 0, q.2 0), (fun i => q.1 i.succ, fun i => q.2 i.succ))
        left_inv := fun ⟨⟨x, y⟩, ⟨xs, ys⟩⟩ => by
          ext <;> simp [Fin.cons]
        right_inv := fun ⟨xs, ys⟩ => by
          ext i
          · refine Fin.cases ?_ ?_ i <;> simp
          · refine Fin.cases ?_ ?_ i <;> simp }
    have hmap : (P.prod (bipartitePower P n)).map e = bipartitePower P (n + 1) := by
      classical
      refine probDist_ext fun ⟨xs, ys⟩ => ?_
      unfold ProbDist.map
      dsimp only
      rw [Finset.sum_eq_single (e.symm (xs, ys))]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte]
        change P.pmf (xs 0, ys 0) * ∏ i : Fin n, P.pmf (xs i.succ, ys i.succ) =
          ∏ i : Fin (n + 1), P.pmf (xs i, ys i)
        rw [Fin.prod_univ_succ]
      · intro a _ hne
        have : e a ≠ (xs, ys) := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hmap, shannonEntropy_map_equiv e, shannonEntropy_prod,
        shannonEntropy_bipartitePower P n]
    push_cast
    ring

end SBES

/-! ### Section 3: Part A — Strict Finite-`n` Lower Bound -/

section LowerBound

private lemma sbes_cond_entropy_le_n {n kW : ℕ}
    (Q : ProbDist ((Fin n → Fin 2) × (Fin n → Fin 3) × Fin kW))
    (hXY : Q.map (fun t => (t.1, t.2.1)) = bipartitePower sbes n)
    (hcmi : condMutualInfo Q = 0)
    (w : Fin kW)
    (Q_XY_W : ProbDist (((Fin n → Fin 2) × (Fin n → Fin 3)) × Fin kW))
    (hQXYW : ∀ x y w', Q_XY_W.pmf ((x, y), w') = Q.pmf (x, y, w'))
    (hw : 0 < Q_XY_W.snd.pmf w) :
    shannonEntropy (condDist Q_XY_W w hw) ≤ (n : ℝ) := by
  classical
  let Rw := condDist Q_XY_W w hw
  have hRw_pmf : ∀ x y, Rw.pmf (x, y) = Q.pmf (x, y, w) / Q_XY_W.snd.pmf w := fun x y => by
    change Q_XY_W.pmf ((x, y), w) / Q_XY_W.snd.pmf w = _
    rw [hQXYW]
  have hQ_snd : Q_XY_W.snd.pmf w = (Q.map (fun t => t.2.2)).pmf w := by
    rw [InfoTheory.Known.map_z_pmf]
    change ∑ xy : (Fin n → Fin 2) × (Fin n → Fin 3), Q_XY_W.pmf (xy, w) = _
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hQXYW x y w
  -- Conditional independence: `Rw = Rw.fst.prod Rw.snd`.
  have hprod : Rw = Rw.fst.prod Rw.snd := by
    have hci := (condMutualInfo_eq_zero_iff Q).mp hcmi
    have hQw_ne : (Q.map (fun t => t.2.2)).pmf w ≠ 0 := by
      rw [← hQ_snd]; exact ne_of_gt hw
    have hfst_pmf : ∀ x, Rw.fst.pmf x = (Q.map (fun t => (t.1, t.2.2))).pmf (x, w) / Q_XY_W.snd.pmf w := by
      intro x
      change ∑ y, Rw.pmf (x, y) = _
      simp_rw [hRw_pmf, ← Finset.sum_div, InfoTheory.Known.map_xz_pmf]
    have hsnd_pmf : ∀ y, Rw.snd.pmf y = (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, w) / Q_XY_W.snd.pmf w := by
      intro y
      change ∑ x, Rw.pmf (x, y) = _
      simp_rw [hRw_pmf, ← Finset.sum_div, InfoTheory.Known.map_yz_pmf]
    refine probDist_ext fun ⟨x, y⟩ => ?_
    change Rw.pmf (x, y) = Rw.fst.pmf x * Rw.snd.pmf y
    rw [hRw_pmf, hfst_pmf, hsnd_pmf]
    have hQeq : Q.pmf (x, y, w) = (condIndepDist Q).pmf (x, y, w) := by
      rw [← hci]
    rw [hQeq]
    change (if (Q.map (fun t => t.2.2)).pmf w = 0 then 0 else
        (Q.map (fun t => (t.1, t.2.2))).pmf (x, w) *
        (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, w) /
        (Q.map (fun t => t.2.2)).pmf w) / Q_XY_W.snd.pmf w = _
    rw [ite_eq_right hQw_ne, ← hQ_snd]
    have hw_ne : Q_XY_W.snd.pmf w ≠ 0 := ne_of_gt hw
    field_simp [hw_ne]
  -- Support compatibility with SBES.
  have hcompat : ∀ x y, 0 < Rw.pmf (x, y) → ∀ i : Fin n, y i = 2 ∨ (y i).val = (x i).val := by
    intro x y hpos i
    rw [hRw_pmf] at hpos
    have hQpos : 0 < Q.pmf (x, y, w) := by
      by_contra hle
      have h0 : Q.pmf (x, y, w) = 0 := le_antisymm (not_lt.mp hle) (Q.nonneg _)
      rw [h0, zero_div] at hpos
      exact lt_irrefl _ hpos
    have hPpos : 0 < (bipartitePower sbes n).pmf (x, y) := by
      rw [← hXY]
      unfold ProbDist.map
      dsimp only
      refine lt_of_lt_of_le hQpos ?_
      have hle := Finset.single_le_sum (f := fun t : (Fin n → Fin 2) × (Fin n → Fin 3) × Fin kW =>
          if (t.1, t.2.1) = (x, y) then Q.pmf t else 0)
        (fun t _ => by split_ifs; exact Q.nonneg t; exact le_rfl)
        (Finset.mem_univ (x, y, w))
      simpa using hle
    have hcoord : 0 < sbes.pmf (x i, y i) := by
      by_contra hle
      have h0 : sbes.pmf (x i, y i) = 0 := le_antisymm (not_lt.mp hle) (sbes.nonneg _)
      have hprod0 : (bipartitePower sbes n).pmf (x, y) = 0 := by
        change ∏ j : Fin n, sbes.pmf (x j, y j) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ i) h0
      linarith
    exact sbes_support_cond (x i) (y i) hcoord
  -- Pick `x₀` in the support of `Rw.fst`.
  have hx0_exists : ∃ x₀ : Fin n → Fin 2, 0 < Rw.fst.pmf x₀ := by
    by_contra hall
    push Not at hall
    have hsum0 : ∑ x : Fin n → Fin 2, Rw.fst.pmf x = 0 :=
      Finset.sum_eq_zero fun x _ => le_antisymm (hall x) (Rw.fst.nonneg x)
    linarith [Rw.fst.sum_one]
  obtain ⟨x₀, hx₀⟩ := hx0_exists
  -- Set `Sw` of coordinates where `Y_i ≠ 2` has positive probability given `W = w`.
  let Sw : Finset (Fin n) := Finset.univ.filter (fun i => ∃ y, 0 < Rw.snd.pmf y ∧ y i ≠ 2)
  -- For `i ∈ Sw`, every `x` in `supp(Rw.fst)` must agree with `x₀ i`!
  have hx_fixed : ∀ x, 0 < Rw.fst.pmf x → ∀ i ∈ Sw, x i = x₀ i := by
    intro x hx i hi
    simp only [Sw, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨y, hy, hy2⟩ := hi
    have hpos1 : 0 < Rw.pmf (x, y) := by
      rw [hprod]; exact mul_pos hx hy
    have hpos0 : 0 < Rw.pmf (x₀, y) := by
      rw [hprod]; exact mul_pos hx₀ hy
    have hc1 := (hcompat x y hpos1 i).resolve_left hy2
    have hc0 := (hcompat x₀ y hpos0 i).resolve_left hy2
    exact Fin.ext (by omega)
  -- Bound `H(X^n | w) ≤ n - |Sw|`.
  let SX : Finset (Fin n → Fin 2) := Finset.univ.filter (fun x => ∀ i ∈ Sw, x i = x₀ i)
  have hSX_nonempty : SX.Nonempty := ⟨x₀, by simp [SX]⟩
  have hSX_card : SX.card ≤ 2 ^ (n - Sw.card) := by
    let f : {x // x ∈ SX} → ({i : Fin n // i ∈ Finset.univ \ Sw} → Fin 2) :=
      fun x i => x.1 i.1
    have hfinj : Function.Injective f := by
      intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ heq
      simp only [SX, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      apply Subtype.ext
      dsimp only
      funext i
      by_cases hi : i ∈ Sw
      · rw [hx₁ i hi, hx₂ i hi]
      · exact congr_fun heq ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hle := Fintype.card_le_of_injective f hfinj
    simp only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ, Finset.card_sdiff, Finset.inter_univ] at hle
    exact hle
  have hHX : shannonEntropy Rw.fst ≤ ((n - Sw.card : ℕ) : ℝ) := by
    have h1 : shannonEntropy Rw.fst ≤ log2 (SX.card : ℝ) :=
      shannonEntropy_le_log2_support Rw.fst SX hSX_nonempty (fun x hx => by
        simp only [SX, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx_fixed x hx)
    have h2 : log2 (SX.card : ℝ) ≤ log2 ((2 : ℝ) ^ (n - Sw.card)) := by
      apply log2_le_log2 (Nat.cast_pos.mpr hSX_nonempty.card_pos)
      exact_mod_cast hSX_card
    rw [log2_two_pow] at h2
    linarith
  -- Bound `H(Y^n | w) ≤ |Sw|`.
  let SY : Finset (Fin n → Fin 3) :=
    Finset.univ.filter (fun y =>
      (∀ i, i ∉ Sw → y i = 2) ∧
      (∀ i, i ∈ Sw → y i = 2 ∨ (y i).val = (x₀ i).val))
  have hy0_exists : ∃ y₀ : Fin n → Fin 3, 0 < Rw.snd.pmf y₀ := by
    by_contra hall
    push Not at hall
    have hsum0 : ∑ y : Fin n → Fin 3, Rw.snd.pmf y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hall y) (Rw.snd.nonneg y)
    linarith [Rw.snd.sum_one]
  have hSY_supp : ∀ y, 0 < Rw.snd.pmf y → y ∈ SY := by
    intro y hy
    simp only [SY, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i hi => ?_, fun i _ => ?_⟩
    · by_contra hy2
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨y, hy, hy2⟩⟩)
    · have hpos : 0 < Rw.pmf (x₀, y) := by rw [hprod]; exact mul_pos hx₀ hy
      exact hcompat x₀ y hpos i
  obtain ⟨y₀, hy₀⟩ := hy0_exists
  have hSY_nonempty : SY.Nonempty := ⟨y₀, hSY_supp y₀ hy₀⟩
  have hSY_card : SY.card ≤ 2 ^ Sw.card := by
    let g : {y // y ∈ SY} → ({i : Fin n // i ∈ Sw} → Bool) :=
      fun y i => decide (y.1 i.1 = 2)
    have hginj : Function.Injective g := by
      intro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ heq
      simp only [SY, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
      apply Subtype.ext
      dsimp only
      funext i
      by_cases hi : i ∈ Sw
      · have hgi := congr_fun heq ⟨i, hi⟩
        dsimp only [g] at hgi
        by_cases h1 : y₁ i = 2
        · have h2 : y₂ i = 2 := by
            have : decide (y₂ i = 2) = true := by rw [← hgi]; simp [h1]
            exact of_decide_eq_true this
          rw [h1, h2]
        · have h2 : y₂ i ≠ 2 := by
            intro h2
            have : decide (y₁ i = 2) = true := by rw [hgi]; simp [h2]
            exact h1 (of_decide_eq_true this)
          have hv1 := (hy₁.2 i hi).resolve_left h1
          have hv2 := (hy₂.2 i hi).resolve_left h2
          exact Fin.ext (hv1.trans hv2.symm)
      · rw [hy₁.1 i hi, hy₂.1 i hi]
    have hle := Fintype.card_le_of_injective g hginj
    simp only [Fintype.card_coe, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ] at hle
    exact hle
  have hHY : shannonEntropy Rw.snd ≤ (Sw.card : ℝ) := by
    have h1 : shannonEntropy Rw.snd ≤ log2 (SY.card : ℝ) :=
      shannonEntropy_le_log2_support Rw.snd SY hSY_nonempty hSY_supp
    have h2 : log2 (SY.card : ℝ) ≤ log2 ((2 : ℝ) ^ Sw.card) := by
      apply log2_le_log2 (Nat.cast_pos.mpr hSY_nonempty.card_pos)
      exact_mod_cast hSY_card
    rw [log2_two_pow] at h2
    linarith
  -- Combine `H(X^n, Y^n | w) = H(X^n | w) + H(Y^n | w) ≤ (n - |Sw|) + |Sw| = n`.
  have hSw_le : Sw.card ≤ n := by
    calc Sw.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hsum_cast : ((n - Sw.card : ℕ) : ℝ) + (Sw.card : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hSw_le
  have hent_prod : shannonEntropy Rw = shannonEntropy Rw.fst + shannonEntropy Rw.snd := by
    conv_lhs => rw [hprod]
    exact shannonEntropy_prod Rw.fst Rw.snd
  linarith

/-- Strict finite-`n` lower bound for `SBES(3/4)`: for every `n ≥ 1`,
    `exactCommonInfoSingle (bipartitePower sbes n) / n > binaryEntropy (3 / 4)`. -/
private theorem sbes_finite_n_strict_lower_bound (n : ℕ) (hn : 0 < n) :
    binaryEntropy (3 / 4) < exactCommonInfoSingle (bipartitePower sbes n) / (n : ℝ) := by
  classical
  let p₀ : ℝ := (1 / 8 : ℝ) ^ n
  let p_e : ℝ := (3 / 8 : ℝ) ^ n
  have hp0_pos : 0 < p₀ := by positivity
  have hpe_pos : 0 < p_e := by positivity
  have hp0_lt_pe : p₀ < p_e :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)
  let m : ℝ := min (p₀ / 2) ((p_e - p₀) / 2)
  have hm_pos : 0 < m := lt_min (by linarith) (by linarith)
  have hm_le_p0 : m ≤ p₀ / 2 := min_le_left _ _
  have hm_le_diff : m ≤ (p_e - p₀) / 2 := min_le_right _ _
  let ε₀ : ℝ := m / p_e
  have hε0_pos : 0 < ε₀ := div_pos hm_pos hpe_pos
  have hε0_lt1 : ε₀ < 1 := by
    rw [div_lt_one hpe_pos]
    linarith
  let c₁ : ℝ := m ^ 2 / (2 * Real.log 2)
  let c₂ : ℝ := p_e * (-log2 (1 - ε₀))
  let c : ℝ := min c₁ c₂
  have hc1_pos : 0 < c₁ := div_pos (sq_pos_of_pos hm_pos) (mul_pos (by norm_num) log_two_pos)
  have hc2_pos : 0 < c₂ :=
    mul_pos hpe_pos (neg_pos.mpr (log2_neg_of_pos_of_lt_one (by linarith) (by linarith)))
  have hc_pos : 0 < c := lt_min hc1_pos hc2_pos
  have h_inf_ge : (n : ℝ) * binaryEntropy (3 / 4) + c ≤
      exactCommonInfoSingle (bipartitePower sbes n) := by
    unfold exactCommonInfoSingle
    refine le_csInf (exactCommonInfoSingle_set_nonempty _) ?_
    rintro r ⟨kW, Q, hXY, hcmi, rfl⟩
    let Q_XY_W : ProbDist (((Fin n → Fin 2) × (Fin n → Fin 3)) × Fin kW) :=
      Q.map (fun t => ((t.1, t.2.1), t.2.2))
    have hQXYW_pmf : ∀ x y w, Q_XY_W.pmf ((x, y), w) = Q.pmf (x, y, w) := by
      intro x y w
      unfold Q_XY_W ProbDist.map
      dsimp only
      rw [Finset.sum_eq_single (x, y, w)]
      · simp
      · intro ⟨x', y', w'⟩ _ hne
        have : ((x', y'), w') ≠ ((x, y), w) := by
          intro h; apply hne
          have h1 := (Prod.mk.inj h).1
          have h2 := (Prod.mk.inj h).2
          exact Prod.ext (Prod.mk.inj h1).1 (Prod.ext (Prod.mk.inj h1).2 h2)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hQXYW_fst : Q_XY_W.fst = bipartitePower sbes n := by
      rw [← hXY]
      refine probDist_ext fun ⟨x, y⟩ => ?_
      change ∑ w : Fin kW, Q_XY_W.pmf ((x, y), w) = _
      simp_rw [hQXYW_pmf]
      unfold ProbDist.map
      dsimp only
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single x]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single y]
        · simp
        · intro y' _ hy'
          exact Finset.sum_eq_zero fun w _ => by simp [hy']
        · intro h; exact absurd (Finset.mem_univ y) h
      · intro x' _ hx'
        rw [Fintype.sum_prod_type]
        exact Finset.sum_eq_zero fun y' _ => Finset.sum_eq_zero fun w _ => by simp [hx']
      · intro h; exact absurd (Finset.mem_univ x) h
    have hQXYW_snd : Q_XY_W.snd = Q.map (fun t => t.2.2) := by
      refine probDist_ext fun w => ?_
      change ∑ xy : (Fin n → Fin 2) × (Fin n → Fin 3), Q_XY_W.pmf (xy, w) = _
      rw [Fintype.sum_prod_type]
      simp_rw [hQXYW_pmf]
      rw [InfoTheory.Known.map_z_pmf]
    -- Entropy identity: `H(W) - n h(3/4) = (n - H(X^n, Y^n | W)) + H(W | X^n, Y^n)`.
    have hHXY : shannonEntropy Q_XY_W.fst = (n : ℝ) * (1 + binaryEntropy (3 / 4)) := by
      rw [hQXYW_fst, shannonEntropy_bipartitePower, shannonEntropy_sbes]
    have hident : shannonEntropy (Q.map (fun t => t.2.2)) - (n : ℝ) * binaryEntropy (3 / 4) =
        ((n : ℝ) - condEntropy Q_XY_W) + condEntropy (Q_XY_W.map Prod.swap) := by
      unfold condEntropy
      rw [snd_map_swap, shannonEntropy_swap, hQXYW_snd, hHXY]
      ring
    -- Non-negativity of `n - H(X^n, Y^n | w)` for every `w` with `Q_W(w) > 0`.
    have hle_n : ∀ w : Fin kW, ∀ hw : 0 < Q_XY_W.snd.pmf w,
        shannonEntropy (condDist Q_XY_W w hw) ≤ (n : ℝ) :=
      fun w hw => sbes_cond_entropy_le_n Q hXY hcmi w Q_XY_W hQXYW_pmf hw
    have hδ1_eq : (n : ℝ) - condEntropy Q_XY_W =
        ∑ w : Fin kW, if hw : 0 < Q_XY_W.snd.pmf w then
          Q_XY_W.snd.pmf w * ((n : ℝ) - shannonEntropy (condDist Q_XY_W w hw))
        else 0 := by
      rw [condEntropy_eq_sum_condDist]
      have hn_eq : (n : ℝ) = ∑ w : Fin kW,
          if _ : 0 < Q_XY_W.snd.pmf w then Q_XY_W.snd.pmf w * (n : ℝ) else 0 := by
        have hsum1 : (∑ w : Fin kW, if 0 < Q_XY_W.snd.pmf w then Q_XY_W.snd.pmf w else 0) = 1 := by
          rw [← Q_XY_W.snd.sum_one]
          refine Finset.sum_congr rfl fun w _ => ?_
          split_ifs with hw
          · rfl
          · exact (le_antisymm (not_lt.mp hw) (Q_XY_W.snd.nonneg w)).symm
        calc (n : ℝ) = 1 * (n : ℝ) := (one_mul _).symm
          _ = (∑ w : Fin kW, if 0 < Q_XY_W.snd.pmf w then Q_XY_W.snd.pmf w else 0) * (n : ℝ) := by
              rw [hsum1]
          _ = ∑ w : Fin kW, (if 0 < Q_XY_W.snd.pmf w then Q_XY_W.snd.pmf w else 0) * (n : ℝ) := by
              rw [Finset.sum_mul]
          _ = _ := by
              refine Finset.sum_congr rfl fun w _ => by
                by_cases hw : 0 < Q_XY_W.snd.pmf w
                · simp [hw]
                · simp [hw]
      conv_lhs => rw [hn_eq]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => by
        by_cases hw : 0 < Q_XY_W.snd.pmf w
        · rw [dite_eq_left hw, dite_eq_left hw, dite_eq_left hw]; ring
        · rw [dite_eq_right hw, dite_eq_right hw, dite_eq_right hw]; ring
    have hδ1_nonneg : 0 ≤ (n : ℝ) - condEntropy Q_XY_W := by
      rw [hδ1_eq]
      refine Finset.sum_nonneg fun w _ => ?_
      split_ifs with hw
      · exact mul_nonneg (le_of_lt hw) (by linarith [hle_n w hw])
      · exact le_rfl
    -- Specific points `x0 = 0^n`, `y0 = 0^n`, `ye = 2^n`.
    let x0 : Fin n → Fin 2 := fun _ => 0
    let y0 : Fin n → Fin 3 := fun _ => 0
    let ye : Fin n → Fin 3 := fun _ => 2
    have hP_00 : (bipartitePower sbes n).pmf (x0, y0) = p₀ := by
      change ∏ _i : Fin n, (1 / 8 : ℝ) = (1 / 8 : ℝ) ^ n
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hP_0e : (bipartitePower sbes n).pmf (x0, ye) = p_e := by
      change ∏ _i : Fin n, (3 / 8 : ℝ) = (3 / 8 : ℝ) ^ n
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- Event `A = {w | Q_W(w) > 0 ∧ Q(x0, y0, w) > 0}`.
    let A : Finset (Fin kW) :=
      Finset.univ.filter (fun w => 0 < Q_XY_W.snd.pmf w ∧ 0 < Q.pmf (x0, y0, w))
    -- For every `w ∈ A`, prove the per-`w` Pinsker bound.
    have hA_pinsker : ∀ w ∈ A,
        ∃ (hw : 0 < Q_XY_W.snd.pmf w),
          Q.pmf (x0, y0, w) = Q_XY_W.snd.pmf w * (condDist Q_XY_W w hw).snd.pmf y0 ∧
          Q.pmf (x0, ye, w) = Q_XY_W.snd.pmf w * (condDist Q_XY_W w hw).snd.pmf ye ∧
          ((condDist Q_XY_W w hw).snd.pmf y0 - (condDist Q_XY_W w hw).snd.pmf ye) ^ 2 ≤
            2 * Real.log 2 * ((n : ℝ) - shannonEntropy (condDist Q_XY_W w hw)) := by
      intro w hwA
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hwA
      obtain ⟨hw, hQ00⟩ := hwA
      let Rw := condDist Q_XY_W w hw
      have hRw_pmf : ∀ x y, Rw.pmf (x, y) = Q.pmf (x, y, w) / Q_XY_W.snd.pmf w := fun x y => by
        change Q_XY_W.pmf ((x, y), w) / Q_XY_W.snd.pmf w = _; rw [hQXYW_pmf]
      have hQ_snd : Q_XY_W.snd.pmf w = (Q.map (fun t => t.2.2)).pmf w := by
        rw [hQXYW_snd]
      -- Conditional independence: `Rw = Rw.fst.prod Rw.snd`.
      have hprod : Rw = Rw.fst.prod Rw.snd := by
        have hci := (condMutualInfo_eq_zero_iff Q).mp hcmi
        have hQw_ne : (Q.map (fun t => t.2.2)).pmf w ≠ 0 := by rw [← hQ_snd]; exact ne_of_gt hw
        have hfst_pmf : ∀ x, Rw.fst.pmf x =
            (Q.map (fun t => (t.1, t.2.2))).pmf (x, w) / Q_XY_W.snd.pmf w := by
          intro x; change ∑ y, Rw.pmf (x, y) = _
          simp_rw [hRw_pmf, ← Finset.sum_div, InfoTheory.Known.map_xz_pmf]
        have hsnd_pmf : ∀ y, Rw.snd.pmf y =
            (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, w) / Q_XY_W.snd.pmf w := by
          intro y; change ∑ x, Rw.pmf (x, y) = _
          simp_rw [hRw_pmf, ← Finset.sum_div, InfoTheory.Known.map_yz_pmf]
        refine probDist_ext fun ⟨x, y⟩ => ?_
        change Rw.pmf (x, y) = Rw.fst.pmf x * Rw.snd.pmf y
        rw [hRw_pmf, hfst_pmf, hsnd_pmf]
        have hQeq : Q.pmf (x, y, w) = (condIndepDist Q).pmf (x, y, w) := by rw [← hci]
        rw [hQeq]
        change (if (Q.map (fun t => t.2.2)).pmf w = 0 then 0 else
            (Q.map (fun t => (t.1, t.2.2))).pmf (x, w) *
            (Q.map (fun t => (t.2.1, t.2.2))).pmf (y, w) /
            (Q.map (fun t => t.2.2)).pmf w) / Q_XY_W.snd.pmf w = _
        rw [ite_eq_right hQw_ne, ← hQ_snd]
        have hw_ne : Q_XY_W.snd.pmf w ≠ 0 := ne_of_gt hw
        field_simp [hw_ne]
      -- Support compatibility with SBES.
      have hcompat : ∀ x y, 0 < Rw.pmf (x, y) → ∀ i : Fin n, y i = 2 ∨ (y i).val = (x i).val := by
        intro x y hpos i
        rw [hRw_pmf] at hpos
        have hQpos : 0 < Q.pmf (x, y, w) := by
          by_contra hle
          have h0 : Q.pmf (x, y, w) = 0 := le_antisymm (not_lt.mp hle) (Q.nonneg _)
          rw [h0, zero_div] at hpos; exact lt_irrefl _ hpos
        have hPpos : 0 < (bipartitePower sbes n).pmf (x, y) := by
          rw [← hXY]; unfold ProbDist.map; dsimp only
          refine lt_of_lt_of_le hQpos ?_
          have hle := Finset.single_le_sum (f := fun t : (Fin n → Fin 2) × (Fin n → Fin 3) × Fin kW =>
              if (t.1, t.2.1) = (x, y) then Q.pmf t else 0)
            (fun t _ => by split_ifs; exact Q.nonneg t; exact le_rfl)
            (Finset.mem_univ (x, y, w))
          simpa using hle
        have hcoord : 0 < sbes.pmf (x i, y i) := by
          by_contra hle
          have h0 : sbes.pmf (x i, y i) = 0 := le_antisymm (not_lt.mp hle) (sbes.nonneg _)
          have hprod0 : (bipartitePower sbes n).pmf (x, y) = 0 := by
            change ∏ j : Fin n, sbes.pmf (x j, y j) = 0
            exact Finset.prod_eq_zero (Finset.mem_univ i) h0
          linarith
        exact sbes_support_cond (x i) (y i) hcoord
      have hRw00 : 0 < Rw.pmf (x0, y0) := by rw [hRw_pmf]; exact div_pos hQ00 hw
      have hRwy0 : 0 < Rw.snd.pmf y0 := by
        refine lt_of_lt_of_le hRw00 ?_
        exact Finset.single_le_sum (fun x _ => Rw.nonneg (x, y0)) (Finset.mem_univ x0)
      -- `Rw.fst` is the point mass at `x0`.
      have hfst_zero : ∀ x, x ≠ x0 → Rw.fst.pmf x = 0 := by
        intro x hne
        by_contra h0
        have hxpos : 0 < Rw.fst.pmf x := lt_of_le_of_ne (Rw.fst.nonneg x) (Ne.symm h0)
        have hpos : 0 < Rw.pmf (x, y0) := by rw [hprod]; exact mul_pos hxpos hRwy0
        apply hne
        funext i
        have hc := hcompat x y0 hpos i
        have hy0ne : y0 i ≠ 2 := by simp [y0]
        have hval := hc.resolve_left hy0ne
        exact Fin.ext (by simpa [x0, y0] using hval.symm)
      have hfst_x0 : Rw.fst.pmf x0 = 1 := by
        rw [← Rw.fst.sum_one]
        symm
        rw [Finset.sum_eq_single x0]
        · intro x _ hne; exact hfst_zero x hne
        · intro h; exact absurd (Finset.mem_univ x0) h
      have hH_fst : shannonEntropy Rw.fst = 0 := by
        unfold shannonEntropy
        rw [Finset.sum_eq_single x0]
        · rw [hfst_x0]; simp [negPLogP, log2_one]
        · intro x _ hne; rw [hfst_zero x hne]; simp [negPLogP]
        · intro h; exact absurd (Finset.mem_univ x0) h
      have hH_eq : shannonEntropy Rw = shannonEntropy Rw.snd := by
        conv_lhs => rw [hprod]
        rw [shannonEntropy_prod, hH_fst, zero_add]
      -- `Rw.snd` is supported on `{0, 2}^n`.
      let embed : (Fin n → Bool) → (Fin n → Fin 3) := fun b i => if b i then 0 else 2
      have hembed_inj : Function.Injective embed := by
        intro b₁ b₂ heq
        funext i
        have hi := congr_fun heq i
        dsimp only [embed] at hi
        cases hb1 : b₁ i <;> cases hb2 : b₂ i <;> simp [hb1, hb2] at hi ⊢
      have hsnd_supp : ∀ y, 0 < Rw.snd.pmf y → ∃ b : Fin n → Bool, embed b = y := by
        intro y hy
        have hpos : 0 < Rw.pmf (x0, y) := by
          rw [hprod]
          change 0 < Rw.fst.pmf x0 * Rw.snd.pmf y
          rw [hfst_x0, one_mul]
          exact hy
        refine ⟨fun i => decide (y i = 0), ?_⟩
        funext i
        have hc := hcompat x0 y hpos i
        dsimp only [embed]
        rcases hc with h2 | h0
        · simp [h2]
        · have hyi0 : y i = 0 := Fin.ext (by simpa [x0] using h0)
          simp [hyi0]
      let RwBool : ProbDist (Fin n → Bool) :=
        { pmf := fun b => Rw.snd.pmf (embed b)
          nonneg := fun b => Rw.snd.nonneg (embed b)
          sum_one := by
            rw [← Rw.snd.sum_one]
            rw [← Finset.sum_image (f := fun y => Rw.snd.pmf y) (g := embed)
              (fun b₁ _ b₂ _ h => hembed_inj h)]
            refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
            by_contra hne
            have hypos : 0 < Rw.snd.pmf y := lt_of_le_of_ne (Rw.snd.nonneg y) (Ne.symm hne)
            obtain ⟨b, rfl⟩ := hsnd_supp y hypos
            exact hy (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩) }
      have hH_bool : shannonEntropy RwBool = shannonEntropy Rw.snd := by
        unfold shannonEntropy
        change ∑ b : Fin n → Bool, negPLogP (Rw.snd.pmf (embed b)) = _
        rw [← Finset.sum_image (f := fun y => negPLogP (Rw.snd.pmf y)) (g := embed)
          (fun b₁ _ b₂ _ h => hembed_inj h)]
        refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
        have hy0 : Rw.snd.pmf y = 0 := by
          by_contra hne
          obtain ⟨b, rfl⟩ := hsnd_supp y (lt_of_le_of_ne (Rw.snd.nonneg y) (Ne.symm hne))
          exact hy (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)
        simp [hy0, negPLogP]
      -- Pinsker's inequality against `ProbDist.uniform` on `Fin n → Bool`.
      have hkl : klDivergence RwBool ProbDist.uniform = (n : ℝ) - shannonEntropy Rw := by
        rw [klDivergence_uniform, hH_bool, ← hH_eq]
        have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
          simp
        rw [hcard, log2_two_pow]
      have hpinsker := pinsker_inequality RwBool ProbDist.uniform (absCont_uniform RwBool)
      rw [hkl] at hpinsker
      -- Relate `|Rw.snd(y0) - Rw.snd(ye)|` to `2 * TV(RwBool, Unif)`.
      let bt : Fin n → Bool := fun _ => true
      let bf : Fin n → Bool := fun _ => false
      have hbt_ne_bf : bt ≠ bf := by
        intro h
        have h0 := congr_fun h ⟨0, hn⟩
        simp [bt, bf] at h0
      have hpair_le : |RwBool.pmf bt - RwBool.pmf bf| ≤ 2 * tvDistance RwBool ProbDist.uniform := by
        unfold tvDistance
        have hUeq : (ProbDist.uniform : ProbDist (Fin n → Bool)).pmf bt =
            (ProbDist.uniform : ProbDist (Fin n → Bool)).pmf bf := rfl
        have htri : |RwBool.pmf bt - RwBool.pmf bf| ≤
            |RwBool.pmf bt - (ProbDist.uniform : ProbDist (Fin n → Bool)).pmf bt| +
            |RwBool.pmf bf - (ProbDist.uniform : ProbDist (Fin n → Bool)).pmf bf| := by
          calc |RwBool.pmf bt - RwBool.pmf bf|
            _ = |(RwBool.pmf bt - ProbDist.uniform.pmf bt) -
                  (RwBool.pmf bf - ProbDist.uniform.pmf bf)| := by rw [hUeq]; ring_nf
            _ ≤ |RwBool.pmf bt - ProbDist.uniform.pmf bt| +
                |RwBool.pmf bf - ProbDist.uniform.pmf bf| := abs_sub _ _
        have hsum_ge :
            |RwBool.pmf bt - (ProbDist.uniform : ProbDist (Fin n → Bool)).pmf bt| +
            |RwBool.pmf bf - (ProbDist.uniform : ProbDist (Fin n → Bool)).pmf bf| ≤
            ∑ b : Fin n → Bool, |RwBool.pmf b - ProbDist.uniform.pmf b| := by
          have hsub : ({bt, bf} : Finset (Fin n → Bool)) ⊆ Finset.univ := Finset.subset_univ _
          have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (f := fun b : Fin n → Bool => |RwBool.pmf b - ProbDist.uniform.pmf b|)
            (fun b _ _ => abs_nonneg _)
          rwa [Finset.sum_pair hbt_ne_bf] at hle
        linarith
      have hsq : (Rw.snd.pmf y0 - Rw.snd.pmf ye) ^ 2 ≤
          2 * Real.log 2 * ((n : ℝ) - shannonEntropy Rw) := by
        have hbt_eq : RwBool.pmf bt = Rw.snd.pmf y0 := rfl
        have hbf_eq : RwBool.pmf bf = Rw.snd.pmf ye := rfl
        rw [← hbt_eq, ← hbf_eq]
        have h1 : (RwBool.pmf bt - RwBool.pmf bf) ^ 2 ≤
            (2 * tvDistance RwBool ProbDist.uniform) ^ 2 := by
          rw [← sq_abs (RwBool.pmf bt - RwBool.pmf bf)]
          exact sq_le_sq' (by linarith [abs_nonneg (RwBool.pmf bt - RwBool.pmf bf)]) hpair_le
        linarith [show (2 * tvDistance RwBool ProbDist.uniform) ^ 2 =
            2 * (2 * (tvDistance RwBool ProbDist.uniform) ^ 2) by ring]
      have hQ00_eq : Q.pmf (x0, y0, w) = Q_XY_W.snd.pmf w * Rw.snd.pmf y0 := by
        have h := hRw_pmf x0 y0
        rw [hprod] at h
        change Rw.fst.pmf x0 * Rw.snd.pmf y0 = Q.pmf (x0, y0, w) / Q_XY_W.snd.pmf w at h
        rw [hfst_x0, one_mul, eq_div_iff (ne_of_gt hw)] at h
        linarith
      have hQ0e_eq : Q.pmf (x0, ye, w) = Q_XY_W.snd.pmf w * Rw.snd.pmf ye := by
        have h := hRw_pmf x0 ye
        rw [hprod] at h
        change Rw.fst.pmf x0 * Rw.snd.pmf ye = Q.pmf (x0, ye, w) / Q_XY_W.snd.pmf w at h
        rw [hfst_x0, one_mul, eq_div_iff (ne_of_gt hw)] at h
        linarith
      exact ⟨hw, hQ00_eq, hQ0e_eq, hsq⟩
    -- Sum over `w ∈ A` and apply Cauchy–Schwarz.
    let S_Ae : ℝ := ∑ w ∈ A, Q.pmf (x0, ye, w)
    have hsum_A00 : ∑ w ∈ A, Q.pmf (x0, y0, w) = p₀ := by
      have hmarg : ∑ w : Fin kW, Q.pmf (x0, y0, w) = p₀ := by
        rw [← hP_00, ← hQXYW_fst]
        change ∑ w : Fin kW, Q.pmf (x0, y0, w) = ∑ w : Fin kW, Q_XY_W.pmf ((x0, y0), w)
        exact Finset.sum_congr rfl fun w _ => (hQXYW_pmf x0 y0 w).symm
      rw [← hmarg]
      refine Finset.sum_subset (Finset.subset_univ A) fun w _ hwA => ?_
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt] at hwA
      rcases hwA with hw0 | hq0
      · have hle : Q.pmf (x0, y0, w) ≤ Q_XY_W.snd.pmf w := by
          rw [← hQXYW_pmf]
          exact Finset.single_le_sum (fun xy _ => Q_XY_W.nonneg (xy, w)) (Finset.mem_univ (x0, y0))
        linarith [Q.nonneg (x0, y0, w)]
      · exact le_antisymm hq0 (Q.nonneg _)
    have hCS : (p₀ - S_Ae) ^ 2 ≤ 2 * Real.log 2 * ((n : ℝ) - condEntropy Q_XY_W) := by
      let d : Fin kW → ℝ := fun w =>
        if hw : 0 < Q_XY_W.snd.pmf w then
          (condDist Q_XY_W w hw).snd.pmf y0 - (condDist Q_XY_W w hw).snd.pmf ye
        else 0
      have hdiff_eq : p₀ - S_Ae = ∑ w ∈ A, Real.sqrt (Q_XY_W.snd.pmf w) *
          (Real.sqrt (Q_XY_W.snd.pmf w) * d w) := by
        rw [← hsum_A00, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w hwA => ?_
        obtain ⟨hw, h00, h0e, _⟩ := hA_pinsker w hwA
        have hsq_rt : Real.sqrt (Q_XY_W.snd.pmf w) * Real.sqrt (Q_XY_W.snd.pmf w) =
            Q_XY_W.snd.pmf w := Real.mul_self_sqrt (le_of_lt hw)
        dsimp only [d]
        rw [dite_eq_left hw, h00, h0e, ← mul_assoc, hsq_rt]
        ring
      rw [hdiff_eq]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq A
        (fun w => Real.sqrt (Q_XY_W.snd.pmf w))
        (fun w => Real.sqrt (Q_XY_W.snd.pmf w) * d w)
      have hsum_w_le : ∑ w ∈ A, (Real.sqrt (Q_XY_W.snd.pmf w)) ^ 2 ≤ 1 := by
        calc ∑ w ∈ A, (Real.sqrt (Q_XY_W.snd.pmf w)) ^ 2
          _ = ∑ w ∈ A, Q_XY_W.snd.pmf w :=
              Finset.sum_congr rfl fun w _ => Real.sq_sqrt (Q_XY_W.snd.nonneg w)
          _ ≤ ∑ w : Fin kW, Q_XY_W.snd.pmf w :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
                (fun w _ _ => Q_XY_W.snd.nonneg w)
          _ = 1 := Q_XY_W.snd.sum_one
      have hsum_d_le : ∑ w ∈ A, (Real.sqrt (Q_XY_W.snd.pmf w) * d w) ^ 2 ≤
          2 * Real.log 2 * ((n : ℝ) - condEntropy Q_XY_W) := by
        rw [hδ1_eq, Finset.mul_sum]
        calc ∑ w ∈ A, (Real.sqrt (Q_XY_W.snd.pmf w) * d w) ^ 2
          _ ≤ ∑ w ∈ A, if hw : 0 < Q_XY_W.snd.pmf w then
                2 * Real.log 2 * (Q_XY_W.snd.pmf w * ((n : ℝ) - shannonEntropy (condDist Q_XY_W w hw)))
              else 0 := by
            refine Finset.sum_le_sum fun w hwA => ?_
            obtain ⟨hw, _, _, hpin⟩ := hA_pinsker w hwA
            rw [dite_eq_left hw, mul_pow, Real.sq_sqrt (le_of_lt hw)]
            dsimp only [d]
            rw [dite_eq_left hw]
            have hmul := mul_le_mul_of_nonneg_left hpin (le_of_lt hw)
            linarith
          _ ≤ ∑ w : Fin kW, if hw : 0 < Q_XY_W.snd.pmf w then
                2 * Real.log 2 * (Q_XY_W.snd.pmf w * ((n : ℝ) - shannonEntropy (condDist Q_XY_W w hw)))
              else 0 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun w _ _ => ?_
            split_ifs with hw
            · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt log_two_pos))
                (mul_nonneg (le_of_lt hw) (by linarith [hle_n w hw]))
            · exact le_rfl
          _ = ∑ w : Fin kW, 2 * Real.log 2 *
                (if hw : 0 < Q_XY_W.snd.pmf w then
                  Q_XY_W.snd.pmf w * ((n : ℝ) - shannonEntropy (condDist Q_XY_W w hw))
                else 0) := by
            refine Finset.sum_congr rfl fun w _ => by split_ifs <;> ring
      have hsum_d_nonneg : 0 ≤ ∑ w ∈ A, (Real.sqrt (Q_XY_W.snd.pmf w) * d w) ^ 2 :=
        Finset.sum_nonneg fun w _ => sq_nonneg _
      nlinarith
    -- Case split on `|p₀ - S_Ae| ≥ m` vs `< m`.
    by_cases hcase : m ≤ |p₀ - S_Ae|
    · have hmsq : m ^ 2 ≤ (p₀ - S_Ae) ^ 2 := by
        rw [← sq_abs (p₀ - S_Ae)]
        exact sq_le_sq' (by linarith) hcase
      have hδ1_ge : c₁ ≤ (n : ℝ) - condEntropy Q_XY_W := by
        dsimp only [c₁]
        rw [div_le_iff₀ (mul_pos (by norm_num) log_two_pos)]
        linarith
      have hce2 : 0 ≤ condEntropy (Q_XY_W.map Prod.swap) := condEntropy_nonneg _
      have hc_le : c ≤ c₁ := min_le_left _ _
      linarith
    · push Not at hcase
      rw [abs_lt] at hcase
      have hSAe_lo : m ≤ S_Ae := by linarith
      have hSAe_hi : S_Ae ≤ p_e - m := by linarith
      -- Lower bound `H(W | X^n, Y^n) ≥ p_e * H(W | X^n = 0^n, Y^n = 2^n) ≥ p_e * h(S_Ae / p_e)`.
      let Qswap := Q_XY_W.map Prod.swap
      have hQswap_snd_0e : Qswap.snd.pmf (x0, ye) = p_e := by
        rw [snd_map_swap, hQXYW_fst, hP_0e]
      have hQswap_pos : 0 < Qswap.snd.pmf (x0, ye) := by rw [hQswap_snd_0e]; exact hpe_pos
      let Re : ProbDist (Fin kW) := condDist Qswap (x0, ye) hQswap_pos
      have hRe_pmf : ∀ w : Fin kW, Re.pmf w = Q.pmf (x0, ye, w) / p_e := by
        intro w
        change Qswap.pmf (w, (x0, ye)) / Qswap.snd.pmf (x0, ye) = _
        rw [hQswap_snd_0e]
        congr 1
        unfold Qswap ProbDist.map
        dsimp only
        rw [Finset.sum_eq_single ((x0, ye), w)]
        · simp [hQXYW_pmf]
        · intro ⟨xy', w'⟩ _ hne
          have : (w', xy') ≠ (w, (x0, ye)) := fun h =>
            hne (Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      let indA : Fin kW → Bool := fun w => decide (w ∈ A)
      let q : ℝ := S_Ae / p_e
      have hmap_true : (Re.map indA).pmf true = q := by
        unfold ProbDist.map
        dsimp only [indA, q, S_Ae]
        simp_rw [hRe_pmf, decide_eq_true_eq]
        rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
      have hmap_false : (Re.map indA).pmf false = 1 - q := by
        have hsum := (Re.map indA).sum_one
        rw [Fintype.sum_bool, hmap_true] at hsum
        linarith
      have hH_ind : shannonEntropy (Re.map indA) = binaryEntropy q := by
        unfold shannonEntropy binaryEntropy
        rw [Fintype.sum_bool, hmap_true, hmap_false]
      have hH_Re : binaryEntropy q ≤ shannonEntropy Re := by
        rw [← hH_ind]
        exact shannonEntropy_map_le indA Re
      have hq_lo : ε₀ ≤ q := div_le_div_of_nonneg_right hSAe_lo (le_of_lt hpe_pos)
      have hq_hi : q ≤ 1 - ε₀ := by
        dsimp only [q, ε₀]
        rw [show 1 - m / p_e = (p_e - m) / p_e by field_simp [ne_of_gt hpe_pos]]
        exact div_le_div_of_nonneg_right hSAe_hi (le_of_lt hpe_pos)
      have hbin_ge : -log2 (1 - ε₀) ≤ binaryEntropy q :=
        binaryEntropy_ge_neg_log2 hε0_pos hε0_lt1 hq_lo hq_hi
      have hce2_ge : c₂ ≤ condEntropy Qswap := by
        rw [condEntropy_eq_sum_condDist]
        have hsingle := Finset.single_le_sum
          (f := fun xy : (Fin n → Fin 2) × (Fin n → Fin 3) =>
            if h : 0 < Qswap.snd.pmf xy then Qswap.snd.pmf xy * shannonEntropy (condDist Qswap xy h) else 0)
          (fun xy _ => by
            split_ifs with h
            · exact mul_nonneg (le_of_lt h) (shannonEntropy_nonneg _)
            · exact le_rfl)
          (Finset.mem_univ (x0, ye))
        rw [dite_eq_left hQswap_pos] at hsingle
        have hmul : c₂ ≤ Qswap.snd.pmf (x0, ye) * shannonEntropy Re := by
          dsimp only [c₂]
          rw [hQswap_snd_0e]
          exact mul_le_mul_of_nonneg_left (le_trans hbin_ge hH_Re) (le_of_lt hpe_pos)
        exact le_trans hmul hsingle
      have hc_le : c ≤ c₂ := min_le_right _ _
      linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [lt_div_iff₀ hn_pos]
  linarith

end LowerBound

/-! ### Section 4: Part B — Asymptotic Upper Bound via Random Rectangle Covering -/

section UpperBound

/-- Set of non-erased coordinates of `y : Fin n → Fin 3`. -/
private def nonErasures {n : ℕ} (y : Fin n → Fin 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => y i ≠ 2)

/-- Constant-erasure shell `S_k ⊆ supp(SBES(3/4)^{⊗ n})` with exactly `k` non-erasures. -/
private def shell (n k : ℕ) : Finset ((Fin n → Fin 2) × (Fin n → Fin 3)) :=
  Finset.univ.filter (fun xy =>
    (∀ i, xy.2 i = 2 ∨ (xy.2 i).val = (xy.1 i).val) ∧ (nonErasures xy.2).card = k)

private lemma card_shell (n k : ℕ) :
    (shell n k).card = Nat.choose n k * 2 ^ n := by
  classical
  let e : {xy // xy ∈ shell n k} ≃
      {E : Finset (Fin n) // E ∈ (Finset.univ : Finset (Fin n)).powersetCard k} ×
      (Fin n → Fin 2) :=
    { toFun := fun ⟨⟨x, y⟩, hxy⟩ =>
        let h := (Finset.mem_filter.mp hxy).2
        (⟨nonErasures y, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.2⟩⟩, x)
      invFun := fun ⟨⟨E, hE⟩, x⟩ =>
        let y : Fin n → Fin 3 := fun i => if i ∈ E then ⟨(x i).val, by omega⟩ else 2
        ⟨(x, y), by
          simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun i => ?_, ?_⟩
          · dsimp only [y]
            split_ifs
            · right; rfl
            · left; rfl
          · have hne : nonErasures y = E := by
              ext i
              simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and, y]
              split_ifs with hi
              · constructor
                · intro _; exact hi
                · intro _ h2
                  have hval := congr_arg Fin.val h2
                  dsimp only at hval
                  omega
              · simp [hi]
            rw [hne]
            exact (Finset.mem_powersetCard.mp hE).2⟩
      left_inv := fun ⟨⟨x, y⟩, hxy⟩ => by
        apply Subtype.ext
        dsimp only
        refine Prod.ext rfl ?_
        funext i
        have h := (Finset.mem_filter.mp hxy).2.1 i
        simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hi
        · exact Fin.ext (h.resolve_left hi).symm
        · exact (not_ne_iff.mp hi).symm
      right_inv := fun ⟨⟨E, hE⟩, x⟩ => by
        dsimp only
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          ext i
          simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with hi
          · constructor
            · intro _; exact hi
            · intro _ h2
              have hval := congr_arg Fin.val h2
              dsimp only at hval
              omega
          · simp [hi]
        · rfl }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Finset.card_powersetCard] at hc
  exact hc

private lemma shell_nonempty {n k : ℕ} (hk : k ≤ n) : (shell n k).Nonempty := by
  rw [← Finset.card_pos, card_shell]
  exact Nat.mul_pos (Nat.choose_pos hk) (Nat.pow_pos (by norm_num))

private lemma card_shell_le_four_pow (n k : ℕ) : (shell n k).card ≤ 4 ^ n := by
  rw [card_shell]
  have h1 : Nat.choose n k ≤ 2 ^ n := by
    calc Nat.choose n k
      _ ≤ ∑ j ∈ Finset.range (n + 1), Nat.choose n j := by
        by_cases hk : k ≤ n
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
        · rw [Nat.choose_eq_zero_of_lt (not_le.mp hk)]
          exact Nat.zero_le _
      _ = 2 ^ n := Nat.sum_range_choose n
  calc Nat.choose n k * 2 ^ n
    _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ h1
    _ = 4 ^ n := by rw [← mul_pow]; norm_num

private lemma bipartitePower_sbes_pmf_of_mem_shell {n k : ℕ}
    {xy : (Fin n → Fin 2) × (Fin n → Fin 3)} (hxy : xy ∈ shell n k) :
    (bipartitePower sbes n).pmf xy = (1 / 8 : ℝ) ^ k * (3 / 8 : ℝ) ^ (n - k) := by
  simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
  rcases hxy with ⟨hcompat, hcard⟩
  change ∏ i : Fin n, sbes.pmf (xy.1 i, xy.2 i) = _
  have hterm : ∀ i : Fin n, sbes.pmf (xy.1 i, xy.2 i) =
      if i ∈ nonErasures xy.2 then (1 / 8 : ℝ) else (3 / 8 : ℝ) := by
    intro i
    rw [sbes_pmf_of_mem _ _ (hcompat i)]
    simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> tauto
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter (fun i : Fin n => i ∈ nonErasures xy.2)).card = k := by
    rw [← hcard]; congr 1; ext i; simp
  have h2 : (Finset.univ.filter (fun i : Fin n => i ∉ nonErasures xy.2)).card = n - k := by
    have hfeq : Finset.univ.filter (fun i : Fin n => i ∉ nonErasures xy.2) =
        Finset.univ \ nonErasures xy.2 := by
      ext i; simp
    rw [hfeq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard]
  rw [h1, h2]

/-- Binomial distribution `Bin(n, 1/4)` on `Fin (n + 1)`. -/
private noncomputable def binDist (n : ℕ) : ProbDist (Fin (n + 1)) where
  pmf := fun k => (Nat.choose n k.val : ℝ) * (1 / 4 : ℝ) ^ k.val * (3 / 4 : ℝ) ^ (n - k.val)
  nonneg := fun k => by positivity
  sum_one := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (Nat.choose n k : ℝ) * (1 / 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ (n - k))]
    have h := add_pow (1 / 4 : ℝ) (3 / 4 : ℝ) n
    have h1 : (1 / 4 : ℝ) + 3 / 4 = 1 := by norm_num
    rw [h1, one_pow] at h
    trans (∑ k ∈ Finset.range (n + 1), (1 / 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ (n - k) * (Nat.choose n k : ℝ))
    · refine Finset.sum_congr rfl fun k _ => by ring
    · exact h.symm

/-- Exponential tail bound `P(Bin(n, 1/4) > n/2) ≤ (7/8)^n` via Markov on `4^K`. -/
private lemma binDist_tail_le (n : ℕ) :
    ∑ k : Fin (n + 1), (if 2 * k.val > n then (binDist n).pmf k else 0) ≤ (7 / 8 : ℝ) ^ n := by
  have hmgf : ∑ k : Fin (n + 1), (binDist n).pmf k * (4 : ℝ) ^ k.val = (7 / 4 : ℝ) ^ n := by
    dsimp only [binDist]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      ((Nat.choose n k : ℝ) * (1 / 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ (n - k)) * (4 : ℝ) ^ k)]
    have h := add_pow (1 : ℝ) (3 / 4 : ℝ) n
    have h74 : (1 : ℝ) + 3 / 4 = 7 / 4 := by norm_num
    rw [h74] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h4 : (1 / 4 : ℝ) ^ k * (4 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    calc (Nat.choose n k : ℝ) * (1 / 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ (n - k) * (4 : ℝ) ^ k
      _ = ((1 / 4 : ℝ) ^ k * (4 : ℝ) ^ k) * (3 / 4 : ℝ) ^ (n - k) * (Nat.choose n k : ℝ) := by ring
      _ = 1 ^ k * (3 / 4 : ℝ) ^ (n - k) * (Nat.choose n k : ℝ) := by rw [h4, one_pow]
  have hle : (2 : ℝ) ^ n * ∑ k : Fin (n + 1), (if 2 * k.val > n then (binDist n).pmf k else 0) ≤
      ∑ k : Fin (n + 1), (binDist n).pmf k * (4 : ℝ) ^ k.val := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · have hpow : (2 : ℝ) ^ n ≤ (4 : ℝ) ^ k.val := by
        have h4eq : (4 : ℝ) ^ k.val = (2 : ℝ) ^ (2 * k.val) := by
          rw [pow_mul]; norm_num
        rw [h4eq]
        exact pow_le_pow_right₀ (by norm_num) (le_of_lt hk)
      have := mul_le_mul_of_nonneg_left hpow ((binDist n).nonneg k)
      linarith
    · rw [mul_zero]
      exact mul_nonneg ((binDist n).nonneg k) (by positivity)
  rw [hmgf] at hle
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [show (7 / 8 : ℝ) ^ n = (7 / 4 : ℝ) ^ n / (2 : ℝ) ^ n by rw [← div_pow]; norm_num]
  rw [le_div_iff₀ h2pos]
  linarith

/-- Mean of `Bin(n, 1/4)` equals `n / 4`. -/
private lemma binDist_mean (n : ℕ) :
    ∑ k : Fin (n + 1), (k.val : ℝ) * (binDist n).pmf k = (n : ℝ) / 4 := by
  cases n with
  | zero => simp [binDist]
  | succ m =>
    dsimp only [binDist]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (k : ℝ) * ((Nat.choose (m + 1) k : ℝ) * (1 / 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ (m + 1 - k)))]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hterm : ∀ j ∈ Finset.range (m + 1),
        ((j + 1 : ℕ) : ℝ) * ((Nat.choose (m + 1) (j + 1) : ℝ) * (1 / 4 : ℝ) ^ (j + 1) *
          (3 / 4 : ℝ) ^ (m + 1 - (j + 1))) =
        ((m + 1 : ℕ) : ℝ) / 4 * ((Nat.choose m j : ℝ) * (1 / 4 : ℝ) ^ j * (3 / 4 : ℝ) ^ (m - j)) := by
      intro j _
      have hch : (j + 1) * Nat.choose (m + 1) (j + 1) = (m + 1) * Nat.choose m j := by
        have := Nat.add_one_mul_choose_eq m j
        linarith
      have hchR : ((j + 1 : ℕ) : ℝ) * (Nat.choose (m + 1) (j + 1) : ℝ) =
          ((m + 1 : ℕ) : ℝ) * (Nat.choose m j : ℝ) := by exact_mod_cast hch
      have hsub : m + 1 - (j + 1) = m - j := by omega
      rw [hsub, pow_succ]
      calc ((j + 1 : ℕ) : ℝ) * ((Nat.choose (m + 1) (j + 1) : ℝ) *
              ((1 / 4 : ℝ) ^ j * (1 / 4)) * (3 / 4 : ℝ) ^ (m - j))
        _ = (((j + 1 : ℕ) : ℝ) * (Nat.choose (m + 1) (j + 1) : ℝ)) *
              (1 / 4) * ((1 / 4 : ℝ) ^ j * (3 / 4 : ℝ) ^ (m - j)) := by ring
        _ = (((m + 1 : ℕ) : ℝ) * (Nat.choose m j : ℝ)) *
              (1 / 4) * ((1 / 4 : ℝ) ^ j * (3 / 4 : ℝ) ^ (m - j)) := by rw [hchR]
        _ = _ := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum1 : ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℝ) * (1 / 4 : ℝ) ^ j * (3 / 4 : ℝ) ^ (m - j) = 1 := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact (binDist m).sum_one
    rw [hsum1, mul_one]

/-- Two-line magic bound: `E[log₂ C(n, K)] ≤ n h(3/4)` from `C(n, k) (1/4)^k (3/4)^{n-k} ≤ 1`. -/
private lemma binDist_expect_log2_choose (n : ℕ) :
    ∑ k : Fin (n + 1), (binDist n).pmf k * log2 (Nat.choose n k.val : ℝ) ≤
      (n : ℝ) * binaryEntropy (3 / 4) := by
  have hpoint : ∀ k : Fin (n + 1),
      log2 (Nat.choose n k.val : ℝ) ≤
        -(k.val : ℝ) * log2 (1 / 4 : ℝ) - ((n - k.val : ℕ) : ℝ) * log2 (3 / 4 : ℝ) := by
    intro k
    have hk_le : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
    have hch_pos : (0 : ℝ) < (Nat.choose n k.val : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hk_le)
    have hpmf_pos : 0 < (binDist n).pmf k := by
      change 0 < (Nat.choose n k.val : ℝ) * (1 / 4 : ℝ) ^ k.val * (3 / 4 : ℝ) ^ (n - k.val)
      positivity
    have hpmf_le : (binDist n).pmf k ≤ 1 := pmf_le_one (binDist n) k
    have hlog_le : log2 ((binDist n).pmf k) ≤ 0 := by
      rw [← log2_one]; exact log2_le_log2 hpmf_pos hpmf_le
    change log2 ((Nat.choose n k.val : ℝ) * (1 / 4 : ℝ) ^ k.val * (3 / 4 : ℝ) ^ (n - k.val)) ≤ 0 at hlog_le
    rw [log2_mul_pos (mul_pos hch_pos (by positivity)) (by positivity),
        log2_mul_pos hch_pos (by positivity), log2_pow, log2_pow] at hlog_le
    linarith
  calc ∑ k : Fin (n + 1), (binDist n).pmf k * log2 (Nat.choose n k.val : ℝ)
    _ ≤ ∑ k : Fin (n + 1), (binDist n).pmf k *
          (-(k.val : ℝ) * log2 (1 / 4 : ℝ) - ((n - k.val : ℕ) : ℝ) * log2 (3 / 4 : ℝ)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hpoint k) ((binDist n).nonneg k)
    _ = -(∑ k : Fin (n + 1), (k.val : ℝ) * (binDist n).pmf k) * log2 (1 / 4 : ℝ) -
        ((n : ℝ) * (∑ k : Fin (n + 1), (binDist n).pmf k) -
          ∑ k : Fin (n + 1), (k.val : ℝ) * (binDist n).pmf k) * log2 (3 / 4 : ℝ) := by
        have hcast : ∀ k : Fin (n + 1), ((n - k.val : ℕ) : ℝ) = (n : ℝ) - (k.val : ℝ) :=
          fun k => Nat.cast_sub (Nat.lt_succ_iff.mp k.isLt)
        simp_rw [hcast]
        have h1 : ∀ k : Fin (n + 1),
            (binDist n).pmf k * (-(k.val : ℝ) * log2 (1 / 4 : ℝ) - ((n : ℝ) - (k.val : ℝ)) * log2 (3 / 4 : ℝ)) =
            -((k.val : ℝ) * (binDist n).pmf k) * log2 (1 / 4 : ℝ) -
            ((n : ℝ) * (binDist n).pmf k - (k.val : ℝ) * (binDist n).pmf k) * log2 (3 / 4 : ℝ) := by
          intro k; ring
        simp_rw [h1]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_neg_distrib,
          ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (n : ℝ) * binaryEntropy (3 / 4) := by
        rw [binDist_mean, (binDist n).sum_one]
        unfold binaryEntropy negPLogP
        have h34 : ¬ ((3 / 4 : ℝ) ≤ 0) := by norm_num
        have h14 : ¬ ((1 - 3 / 4 : ℝ) ≤ 0) := by norm_num
        rw [ite_eq_right h34, ite_eq_right h14, show (1 - 3 / 4 : ℝ) = 1 / 4 by norm_num]
        ring

/-- Index family `W_k` of product rectangles for `2k ≤ n`:
    pairs `(T, u)` with `|T| = 2k` and `u i = 0` outside `T`. -/
private def rectIndex (n k : ℕ) : Finset (Finset (Fin n) × (Fin n → Fin 2)) :=
  Finset.univ.filter (fun w => w.1.card = 2 * k ∧ ∀ i ∉ w.1, w.2 i = 0)

/-- `X`-side of rectangle `w = (T, u)`. -/
private def rectA {n : ℕ} (w : Finset (Fin n) × (Fin n → Fin 2)) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter (fun x => ∀ i ∈ w.1, x i = w.2 i)

/-- `Y`-side of rectangle `w = (T, u)` inside shell `S_k`. -/
private def rectB {n : ℕ} (k : ℕ) (w : Finset (Fin n) × (Fin n → Fin 2)) : Finset (Fin n → Fin 3) :=
  Finset.univ.filter (fun y =>
    (nonErasures y).card = k ∧ ∀ i, y i = 2 ∨ (i ∈ w.1 ∧ (y i).val = (w.2 i).val))

private noncomputable def rectProb (n k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) / ((Nat.choose n k : ℝ) * (2 : ℝ) ^ (2 * k))

private noncomputable def rectCount (n k : ℕ) (δ : ℝ) : ℕ :=
  Nat.ceil ((6 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * rectProb n k))

private lemma rect_subset_shell {n k : ℕ} {w : Finset (Fin n) × (Fin n → Fin 2)}
    {x : Fin n → Fin 2} {y : Fin n → Fin 3} (hx : x ∈ rectA w) (hy : y ∈ rectB k w) :
    (x, y) ∈ shell n k := by
  simp only [rectA, rectB, shell, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
  refine ⟨fun i => ?_, hy.1⟩
  rcases hy.2 i with h2 | ⟨hiT, hval⟩
  · left; exact h2
  · right; rw [hx i hiT]; exact hval

private lemma card_rectA {n k : ℕ} {w : Finset (Fin n) × (Fin n → Fin 2)} (hw : w ∈ rectIndex n k) :
    (rectA w).card = 2 ^ (n - 2 * k) := by
  classical
  have hTcard : w.1.card = 2 * k := (Finset.mem_filter.mp hw).2.1
  let e : {x // x ∈ rectA w} ≃ ({i : Fin n // i ∈ Finset.univ \ w.1} → Fin 2) :=
    { toFun := fun x i => x.1 i.1
      invFun := fun f =>
        ⟨fun i => if hi : i ∈ w.1 then w.2 i else f ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩,
         by
           simp only [rectA, Finset.mem_filter, Finset.mem_univ, true_and]
           intro i hi; simp [hi]⟩
      left_inv := fun ⟨x, hx⟩ => by
        apply Subtype.ext
        dsimp only
        funext i
        simp only [rectA, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        split_ifs with hi
        · exact (hx i hi).symm
        · rfl
      right_inv := fun f => by
        funext ⟨i, hi⟩
        have hni : i ∉ w.1 := (Finset.mem_sdiff.mp hi).2
        simp [hni] }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
    Finset.card_univ, Finset.card_sdiff, Finset.inter_univ, hTcard] at hc
  exact hc

private lemma card_rectB {n k : ℕ} {w : Finset (Fin n) × (Fin n → Fin 2)} (hw : w ∈ rectIndex n k) :
    (rectB k w).card = Nat.choose (2 * k) k := by
  classical
  have hTcard : w.1.card = 2 * k := (Finset.mem_filter.mp hw).2.1
  let e : {y // y ∈ rectB k w} ≃ {E : Finset (Fin n) // E ∈ w.1.powersetCard k} :=
    { toFun := fun ⟨y, hy⟩ =>
        ⟨nonErasures y, by
          simp only [rectB, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [Finset.mem_powersetCard]
          refine ⟨fun i hi => ?_, hy.1⟩
          have hyi : y i ≠ 2 := (Finset.mem_filter.mp hi).2
          exact ((hy.2 i).resolve_left hyi).1⟩
      invFun := fun ⟨E, hE⟩ =>
        ⟨fun i => if i ∈ E then ⟨(w.2 i).val, by omega⟩ else 2, by
          rw [Finset.mem_powersetCard] at hE
          simp only [rectB, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, fun i => ?_⟩
          · have hne : nonErasures (fun i => if i ∈ E then (⟨(w.2 i).val, by omega⟩ : Fin 3) else 2) = E := by
              ext i
              simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and]
              split_ifs with hi
              · constructor
                · intro _; exact hi
                · intro _ h2; have hv := congr_arg Fin.val h2; dsimp only at hv; omega
              · simp [hi]
            rw [hne]; exact hE.2
          · split_ifs with hi
            · right; exact ⟨hE.1 hi, rfl⟩
            · left; rfl⟩
      left_inv := fun ⟨y, hy⟩ => by
        apply Subtype.ext; dsimp only; funext i
        simp only [rectB, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hi
        · exact Fin.ext ((hy.2 i).resolve_left hi).2.symm
        · exact (not_ne_iff.mp hi).symm
      right_inv := fun ⟨E, hE⟩ => by
        apply Subtype.ext; dsimp only; ext i
        simp only [nonErasures, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hi
        · constructor
          · intro _; exact hi
          · intro _ h2; have hv := congr_arg Fin.val h2; dsimp only at hv; omega
        · simp [hi] }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_coe, Finset.card_powersetCard, hTcard] at hc
  exact hc

private lemma card_rectIndex (n k : ℕ) :
    (rectIndex n k).card = Nat.choose n (2 * k) * 2 ^ (2 * k) := by
  classical
  let e : {w // w ∈ rectIndex n k} ≃
      Σ T : {T : Finset (Fin n) // T ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * k)},
        ({i : Fin n // i ∈ T.1} → Fin 2) :=
    { toFun := fun ⟨⟨T, u⟩, hw⟩ =>
        let h := (Finset.mem_filter.mp hw).2
        ⟨⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h.1⟩⟩, fun i => u i.1⟩
      invFun := fun ⟨⟨T, hT⟩, f⟩ =>
        ⟨(T, fun i => if hi : i ∈ T then f ⟨i, hi⟩ else 0), by
          simp only [rectIndex, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(Finset.mem_powersetCard.mp hT).2, fun i hi => by simp [hi]⟩⟩
      left_inv := fun ⟨⟨T, u⟩, hw⟩ => by
        apply Subtype.ext; dsimp only; refine Prod.ext rfl ?_; funext i
        have h := (Finset.mem_filter.mp hw).2.2
        change (if hi : i ∈ T then u i else 0) = u i
        split_ifs with hi
        · rfl
        · exact (h i hi).symm
      right_inv := fun ⟨⟨T, hT⟩, f⟩ => by
        dsimp only
        refine Sigma.ext rfl ?_
        refine heq_of_eq ?_
        funext ⟨i, hi⟩; simp [hi] }
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_sigma] at hc
  rw [hc]
  have hinner : ∀ T : {T : Finset (Fin n) // T ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * k)},
      Fintype.card ({i : Fin n // i ∈ T.1} → Fin 2) = 2 ^ (2 * k) := by
    intro ⟨T, hT⟩
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe, (Finset.mem_powersetCard.mp hT).2]
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private lemma rectIndex_nonempty {n k : ℕ} (hk : 2 * k ≤ n) : (rectIndex n k).Nonempty := by
  rw [← Finset.card_pos, card_rectIndex]
  exact Nat.mul_pos (Nat.choose_pos hk) (Nat.pow_pos (by norm_num))

private lemma card_covering_rects {n k : ℕ} {xy : (Fin n → Fin 2) × (Fin n → Fin 3)}
    (hxy : xy ∈ shell n k) :
    ((rectIndex n k).filter (fun w => xy.1 ∈ rectA w ∧ xy.2 ∈ rectB k w)).card =
      Nat.choose (n - k) k := by
  classical
  simp only [shell, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
  rcases hxy with ⟨hcompat, hEcard⟩
  let E := nonErasures xy.2
  let Ecomp := (Finset.univ : Finset (Fin n)) \ E
  have hEcomp_card : Ecomp.card = n - k := by
    simp only [Ecomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      E, hEcard]
  let C := (rectIndex n k).filter (fun w => xy.1 ∈ rectA w ∧ xy.2 ∈ rectB k w)
  let e : {w // w ∈ C} ≃ {T' : Finset (Fin n) // T' ∈ Ecomp.powersetCard k} :=
    { toFun := fun ⟨⟨T, u⟩, hw⟩ =>
        ⟨T \ E, by
          simp only [C, rectIndex, rectA, rectB, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          rcases hw with ⟨⟨hTcard, _⟩, ⟨_, _, hyB⟩⟩
          have hET : E ⊆ T := fun i hi =>
            ((hyB i).resolve_left (Finset.mem_filter.mp hi).2).1
          rw [Finset.mem_powersetCard]
          refine ⟨fun i hi => ?_, ?_⟩
          · rw [Finset.mem_sdiff] at hi ⊢
            exact ⟨Finset.mem_univ i, hi.2⟩
          · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hET, hTcard, hEcard]; omega⟩
      invFun := fun ⟨T', hT'⟩ =>
        let T := E ∪ T'
        let u : Fin n → Fin 2 := fun i => if i ∈ T then xy.1 i else 0
        ⟨(T, u), by
          rw [Finset.mem_powersetCard] at hT'
          have hdisj : Disjoint E T' := by
            rw [Finset.disjoint_left]
            intro i hiE hiT'
            exact (Finset.mem_sdiff.mp (hT'.1 hiT')).2 hiE
          simp only [C, rectIndex, rectA, rectB, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨?_, fun i hi => by simp [u, hi]⟩, ⟨fun i hi => by simp [u, hi], hEcard, fun i => ?_⟩⟩
          · rw [Finset.card_union_of_disjoint hdisj, hEcard, hT'.2]; omega
          · rcases hcompat i with h2 | hval
            · left; exact h2
            · by_cases hy2 : xy.2 i = 2
              · left; exact hy2
              · right
                have hiE : i ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hy2⟩
                have hiT : i ∈ T := Finset.mem_union_left T' hiE
                exact ⟨hiT, by simp [u, hiT, hval]⟩⟩
      left_inv := fun ⟨⟨T, u⟩, hw⟩ => by
        simp only [C, rectIndex, rectA, rectB, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rcases hw with ⟨⟨_, hu0⟩, ⟨hxA, _, hyB⟩⟩
        have hET : E ⊆ T := fun i hi => ((hyB i).resolve_left (Finset.mem_filter.mp hi).2).1
        have hT_eq : E ∪ (T \ E) = T := Finset.union_sdiff_of_subset hET
        apply Subtype.ext; dsimp only
        apply Prod.ext hT_eq
        funext i
        change (if i ∈ E ∪ (T \ E) then xy.1 i else 0) = u i
        rw [hT_eq]
        split_ifs with hi
        · exact hxA i hi
        · exact (hu0 i hi).symm
      right_inv := fun ⟨T', hT'⟩ => by
        rw [Finset.mem_powersetCard] at hT'
        have hdisj : Disjoint E T' := by
          rw [Finset.disjoint_left]
          intro i hiE hiT'
          exact (Finset.mem_sdiff.mp (hT'.1 hiT')).2 hiE
        apply Subtype.ext; dsimp only
        exact Finset.union_sdiff_cancel_left hdisj }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_coe, Finset.card_powersetCard, hEcomp_card] at hc
  exact hc

private lemma central_choose_lower (k : ℕ) :
    2 ^ (2 * k) ≤ (2 * k + 1) * Nat.choose (2 * k) k := by
  have hsum := Nat.sum_range_choose (2 * k)
  rw [← hsum]
  calc ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j
    _ ≤ ∑ _j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) k := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := Nat.choose_le_middle j (2 * k)
        rwa [show 2 * k / 2 = k by omega] at h
    _ = (2 * k + 1) * Nat.choose (2 * k) k := by
        simp

private lemma choose_mul_symm {n k : ℕ} (hk : 2 * k ≤ n) :
    Nat.choose n (2 * k) * Nat.choose (2 * k) k = Nat.choose n k * Nat.choose (n - k) k := by
  have hpos : 0 < k.factorial * k.factorial * (n - 2 * k).factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos k)) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have h1 : Nat.choose n (2 * k) * (2 * k).factorial * (n - 2 * k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hk
  have h2 : Nat.choose (2 * k) k * k.factorial * (2 * k - k).factorial = (2 * k).factorial :=
    Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  rw [show 2 * k - k = k by omega] at h2
  have h3 : Nat.choose n k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
  have h4 : Nat.choose (n - k) k * k.factorial * (n - k - k).factorial = (n - k).factorial :=
    Nat.choose_mul_factorial_mul_factorial (show k ≤ n - k by omega)
  rw [show n - k - k = n - 2 * k by omega] at h4
  calc Nat.choose n (2 * k) * Nat.choose (2 * k) k * (k.factorial * k.factorial * (n - 2 * k).factorial)
    _ = Nat.choose n (2 * k) * (Nat.choose (2 * k) k * k.factorial * k.factorial) * (n - 2 * k).factorial := by ring
    _ = Nat.choose n (2 * k) * (2 * k).factorial * (n - 2 * k).factorial := by rw [h2]
    _ = n.factorial := h1
    _ = Nat.choose n k * k.factorial * (n - k).factorial := h3.symm
    _ = Nat.choose n k * k.factorial * (Nat.choose (n - k) k * k.factorial * (n - 2 * k).factorial) := by rw [← h4]
    _ = Nat.choose n k * Nat.choose (n - k) k * (k.factorial * k.factorial * (n - 2 * k).factorial) := by ring

/-- One-sided Chernoff / MGF finite-sum covering existence lemma:
    for `n ≥ 1`, `2k ≤ n`, `0 < δ ≤ 1/2`, there exists a deterministic list of `rectCount n k δ`
    rectangles in `W_k` covering every `(x, y) ∈ S_k` at most `(1 + δ) * rectCount * rectProb` times. -/
private lemma exists_good_rect_covering {n k : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    0 < rectCount n k δ ∧
    ∃ f : Fin (rectCount n k δ) → {w // w ∈ rectIndex n k},
      ∀ xy ∈ shell n k,
        ((Finset.univ.filter (fun j : Fin (rectCount n k δ) =>
          xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1)).card : ℝ) ≤
          (1 + δ) * (rectCount n k δ : ℝ) * rectProb n k := by
  classical
  set p_k : ℝ := rectProb n k
  set M : ℕ := rectCount n k δ
  have hk_le_n : k ≤ n := by omega
  have hpk_pos : 0 < p_k := by
    dsimp only [p_k, rectProb]
    have h1 : (0 : ℝ) < (Nat.choose (2 * k) k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have h2 : (0 : ℝ) < (Nat.choose n k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hk_le_n)
    positivity
  have hM_pos : 0 < M := by
    dsimp only [M, rectCount]
    refine Nat.ceil_pos.mpr (div_pos (by positivity) (mul_pos (sq_pos_of_pos hδ0) hpk_pos))
  refine ⟨hM_pos, ?_⟩
  -- Check `p_k = C(n - k, k) / |W_k|`.
  have hW_pos : (0 : ℝ) < ((rectIndex n k).card : ℝ) :=
    Nat.cast_pos.mpr (rectIndex_nonempty hk).card_pos
  have hpk_eq : p_k = (Nat.choose (n - k) k : ℝ) / ((rectIndex n k).card : ℝ) := by
    dsimp only [p_k, rectProb]
    rw [card_rectIndex]
    have hbinR : (Nat.choose n (2 * k) : ℝ) * (Nat.choose (2 * k) k : ℝ) =
        (Nat.choose n k : ℝ) * (Nat.choose (n - k) k : ℝ) := by exact_mod_cast choose_mul_symm hk
    have h1 : (Nat.choose n k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos hk_le_n))
    have h2 : (Nat.choose n (2 * k) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos hk))
    have h3 : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
    push_cast
    field_simp [h1, h2, h3]
    linarith
  -- Chernoff exponent parameter `t = δ / 2`: `exp t - 1 - t (1 + δ) ≤ -δ^2 / 6`.
  let t : ℝ := δ / 2
  have ht_pos : 0 < t := by dsimp only [t]; linarith
  have ht_bound : Real.exp t - 1 - t * (1 + δ) ≤ -(δ ^ 2 / 6) := by
    have h1mt_pos : 0 < 1 - t := by dsimp only [t]; linarith
    have hexp_inv : 1 - t ≤ (Real.exp t)⁻¹ := by
      rw [← Real.exp_neg]
      have := Real.add_one_le_exp (-t)
      linarith
    have hexp_le : Real.exp t ≤ (1 - t)⁻¹ := by
      have hpos : 0 < Real.exp t := Real.exp_pos t
      rw [le_inv_comm₀ hpos h1mt_pos]
      exact hexp_inv
    have hfrac : (1 - t)⁻¹ - 1 - t * (1 + δ) = t * (t / (1 - t) - δ) := by
      field_simp [ne_of_gt h1mt_pos]; ring
    have h34 : (3 : ℝ) / 4 ≤ 1 - t := by dsimp only [t]; linarith
    have hdiv_le : t / (1 - t) ≤ t / (3 / 4 : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt ht_pos) (by norm_num) h34
    have hsub_le : t / (1 - t) - δ ≤ -(δ / 3) := by
      dsimp only [t] at hdiv_le ⊢
      linarith
    have hmul_le : t * (t / (1 - t) - δ) ≤ t * (-(δ / 3)) :=
      mul_le_mul_of_nonneg_left hsub_le (le_of_lt ht_pos)
    have hprod_eq : t * (-(δ / 3)) = -(δ ^ 2 / 6) := by dsimp only [t]; ring
    linarith
  -- Finite probability space `Ω = Fin M → {w // w ∈ rectIndex n k}`.
  let W := {w // w ∈ rectIndex n k}
  let Ω := Fin M → W
  let bad : ((Fin n → Fin 2) × (Fin n → Fin 3)) → Ω → ℝ := fun xy f =>
    if (1 + δ) * (M : ℝ) * p_k <
        ((Finset.univ.filter (fun j : Fin M => xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1)).card : ℝ)
    then 1 else 0
  -- Per-`xy` MGF bound over `f : Ω`.
  have hmgf_xy : ∀ xy ∈ shell n k,
      ∑ f : Ω, bad xy f ≤ ((Fintype.card W : ℝ) ^ M) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6) := by
    intro xy hxy
    have hpoint : ∀ f : Ω,
        bad xy f ≤
          Real.exp (-t * (1 + δ) * (M : ℝ) * p_k) *
            ∏ j : Fin M, if xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1 then Real.exp t else 1 := by
      intro f
      let N := (Finset.univ.filter (fun j : Fin M => xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1)).card
      have hprod_eq :
          (∏ j : Fin M, if xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1 then Real.exp t else 1) =
            Real.exp (t * (N : ℝ)) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, ← Real.exp_nat_mul]
        congr 1; ring
      rw [hprod_eq, ← Real.exp_add]
      dsimp only [bad]
      split_ifs with hgt
      · have hexp_nonneg : 0 ≤ -t * (1 + δ) * (M : ℝ) * p_k + t * (N : ℝ) := by
          have : 0 < (N : ℝ) - (1 + δ) * (M : ℝ) * p_k := by linarith
          nlinarith
        exact Real.one_le_exp hexp_nonneg
      · exact le_of_lt (Real.exp_pos _)
    have hsum_prod :
        ∑ f : Ω, (∏ j : Fin M, if xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1 then Real.exp t else 1) =
          ((Fintype.card W : ℝ) * (1 + p_k * (Real.exp t - 1))) ^ M := by
      have hps := Fintype.prod_sum (fun (_ : Fin M) (w : W) =>
        if xy.1 ∈ rectA w.1 ∧ xy.2 ∈ rectB k w.1 then Real.exp t else (1 : ℝ))
      rw [← hps, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      have hcount :
          (∑ w : W, if xy.1 ∈ rectA w.1 ∧ xy.2 ∈ rectB k w.1 then Real.exp t else (1 : ℝ)) =
            ((Fintype.card W : ℝ) + ((Nat.choose (n - k) k : ℝ)) * (Real.exp t - 1)) := by
        have h1 : ∀ w : W,
            (if xy.1 ∈ rectA w.1 ∧ xy.2 ∈ rectB k w.1 then Real.exp t else (1 : ℝ)) =
              1 + if xy.1 ∈ rectA w.1 ∧ xy.2 ∈ rectB k w.1 then (Real.exp t - 1) else 0 := by
          intro w; split_ifs <;> ring
        simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        congr 2
        have hfc : (Finset.univ.filter (fun w : W => xy.1 ∈ rectA w.1 ∧ xy.2 ∈ rectB k w.1)).card =
            ((rectIndex n k).filter (fun w => xy.1 ∈ rectA w ∧ xy.2 ∈ rectB k w)).card := by
          refine Finset.card_bij (fun w _ => w.1) (fun w hw => ?_) (fun _ _ _ _ h => Subtype.ext h)
            (fun w hw => ⟨⟨w, (Finset.mem_filter.mp hw).1⟩, by simp [(Finset.mem_filter.mp hw).2], rfl⟩)
          exact Finset.mem_filter.mpr ⟨w.2, (Finset.mem_filter.mp hw).2⟩
        rw [hfc, card_covering_rects hxy]
      rw [hcount, hpk_eq, Fintype.card_coe]
      field_simp [ne_of_gt hW_pos]
    calc ∑ f : Ω, bad xy f
      _ ≤ ∑ f : Ω, Real.exp (-t * (1 + δ) * (M : ℝ) * p_k) *
            ∏ j : Fin M, if xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k (f j).1 then Real.exp t else 1 :=
          Finset.sum_le_sum fun f _ => hpoint f
      _ = Real.exp (-t * (1 + δ) * (M : ℝ) * p_k) *
            ((Fintype.card W : ℝ) * (1 + p_k * (Real.exp t - 1))) ^ M := by
          rw [← Finset.mul_sum, hsum_prod]
      _ = ((Fintype.card W : ℝ) ^ M) *
            (Real.exp (-t * (1 + δ) * (M : ℝ) * p_k) * (1 + p_k * (Real.exp t - 1)) ^ M) := by
          rw [mul_pow]; ring
      _ ≤ ((Fintype.card W : ℝ) ^ M) *
            (Real.exp (-t * (1 + δ) * (M : ℝ) * p_k) * Real.exp ((M : ℝ) * (p_k * (Real.exp t - 1)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))) (by positivity)
          have h1 : 0 ≤ 1 + p_k * (Real.exp t - 1) := by
            have := Real.one_le_exp (le_of_lt ht_pos)
            nlinarith
          have h2 : 1 + p_k * (Real.exp t - 1) ≤ Real.exp (p_k * (Real.exp t - 1)) := by
            linarith [Real.add_one_le_exp (p_k * (Real.exp t - 1))]
          calc (1 + p_k * (Real.exp t - 1)) ^ M
            _ ≤ (Real.exp (p_k * (Real.exp t - 1))) ^ M := pow_le_pow_left₀ h1 h2 M
            _ = Real.exp ((M : ℝ) * (p_k * (Real.exp t - 1))) := by rw [← Real.exp_nat_mul]
      _ = ((Fintype.card W : ℝ) ^ M) * Real.exp ((M : ℝ) * p_k * (Real.exp t - 1 - t * (1 + δ))) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ ((Fintype.card W : ℝ) ^ M) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have hMp : 0 ≤ (M : ℝ) * p_k := by positivity
          nlinarith
  -- Sum over all `xy ∈ shell n k` and show total bad sum `< |Ω|`.
  have htotal_lt : ∑ f : Ω, (∑ xy ∈ shell n k, bad xy f) < ∑ _f : Ω, (1 : ℝ) := by
    rw [Finset.sum_comm]
    have hcard_Ω : (∑ _f : Ω, (1 : ℝ)) = (Fintype.card W : ℝ) ^ M := by
      simp [Ω]
    rw [hcard_Ω]
    have hsum_le : ∑ xy ∈ shell n k, ∑ f : Ω, bad xy f ≤
        ((shell n k).card : ℝ) * (((Fintype.card W : ℝ) ^ M) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6)) := by
      calc ∑ xy ∈ shell n k, ∑ f : Ω, bad xy f
        _ ≤ ∑ _xy ∈ shell n k, ((Fintype.card W : ℝ) ^ M) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6) :=
            Finset.sum_le_sum fun xy hxy => hmgf_xy xy hxy
        _ = _ := by simp
    -- Show `|shell n k| * exp(-M p_k δ^2 / 6) < 1`.
    have hexp_lt1 : ((shell n k).card : ℝ) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6) < 1 := by
      have h4le : ((shell n k).card : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast card_shell_le_four_pow n k
      have h4exp : (4 : ℝ) ≤ Real.exp 2 := by
        have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he2 2
          _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      have hcard_exp : ((shell n k).card : ℝ) ≤ Real.exp (2 * (n : ℝ)) := by
        calc ((shell n k).card : ℝ) ≤ (4 : ℝ) ^ n := h4le
          _ ≤ (Real.exp 2) ^ n := pow_le_pow_left₀ (by norm_num) h4exp n
          _ = Real.exp (2 * (n : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      have hM_ge : (6 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) ≤ (M : ℝ) := Nat.le_ceil _
      have hexp_ge : 2 * (n : ℝ) + 1 ≤ (M : ℝ) * p_k * δ ^ 2 / 6 := by
        have hden : 0 < δ ^ 2 * p_k := mul_pos (sq_pos_of_pos hδ0) hpk_pos
        rw [div_le_iff₀ hden] at hM_ge
        linarith
      calc ((shell n k).card : ℝ) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6)
        _ ≤ Real.exp (2 * (n : ℝ)) * Real.exp (-(2 * (n : ℝ) + 1)) := by
            refine mul_le_mul hcard_exp (Real.exp_le_exp.mpr (by linarith))
              (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
        _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hWpow_pos : (0 : ℝ) < (Fintype.card W : ℝ) ^ M := by
      have : (0 : ℝ) < (Fintype.card W : ℝ) := by rw [Fintype.card_coe]; exact hW_pos
      positivity
    calc ∑ xy ∈ shell n k, ∑ f : Ω, bad xy f
      _ ≤ ((Fintype.card W : ℝ) ^ M) *
            (((shell n k).card : ℝ) * Real.exp (-(M : ℝ) * p_k * δ ^ 2 / 6)) := by linarith
      _ < ((Fintype.card W : ℝ) ^ M) * 1 := mul_lt_mul_of_pos_left hexp_lt1 hWpow_pos
      _ = (Fintype.card W : ℝ) ^ M := mul_one _
  obtain ⟨f, _, hf⟩ := Finset.exists_lt_of_sum_lt htotal_lt
  refine ⟨f, fun xy hxy => ?_⟩
  by_contra hgt
  push Not at hgt
  have h1 : (1 : ℝ) ≤ ∑ xy' ∈ shell n k, bad xy' f := by
    have hle := Finset.single_le_sum (f := fun xy' => bad xy' f)
      (fun xy' _ => by dsimp only [bad]; split_ifs <;> norm_num) hxy
    have hbad1 : bad xy f = 1 := ite_eq_left hgt
    linarith
  linarith

/-- Transport any product mixture on a finite type `W` to `Fin (Fintype.card W)`. -/
private lemma reindex_shell_decomp {X Y W : Type*} [Fintype X] [Fintype Y] [Fintype W]
    (pW : ProbDist W) (PX : W → ProbDist X) (PY : W → ProbDist Y) :
    let kW := Fintype.card W
    let e := Fintype.equivFin W
    let pW' : ProbDist (Fin kW) := pW.map e
    (∀ x y, ∑ i : Fin kW, pW'.pmf i * (PX (e.symm i)).pmf x * (PY (e.symm i)).pmf y =
      ∑ w : W, pW.pmf w * (PX w).pmf x * (PY w).pmf y) ∧
    shannonEntropy pW' = shannonEntropy pW := by
  classical
  intro kW e pW'
  have hpmf : ∀ i : Fin kW, pW'.pmf i = pW.pmf (e.symm i) := by
    intro i
    unfold pW' ProbDist.map
    dsimp only
    rw [Finset.sum_eq_single (e.symm i)]
    · simp
    · intro w _ hne
      have : e w ≠ i := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨fun x y => ?_, shannonEntropy_map_equiv e pW⟩
  simp_rw [hpmf]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- For each shell `k ≤ n`, construct a finite auxiliary distribution `(kW, pW, PX, PY)` on `Fin kW`
    that exactly reproduces `Unif(shell n k)` as a product mixture, with controlled entropy. -/
private lemma exists_shell_decomposition {n : ℕ} (hn : 0 < n) (k : Fin (n + 1))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ (kW : ℕ) (pW : ProbDist (Fin kW))
      (PX : Fin kW → ProbDist (Fin n → Fin 2)) (PY : Fin kW → ProbDist (Fin n → Fin 3)),
      (∀ x y, ∑ w : Fin kW, pW.pmf w * (PX w).pmf x * (PY w).pmf y =
        (finsetUniform (shell n k.val) (shell_nonempty (Nat.lt_succ_iff.mp k.isLt))).pmf (x, y)) ∧
      shannonEntropy pW ≤
        if 2 * k.val ≤ n then
          1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) +
            log2 (Nat.choose n k.val : ℝ) + 2 * δ * (n : ℝ)
        else 2 * (n : ℝ) := by
  classical
  have hk_le : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
  have hshell_ne : (shell n k.val).Nonempty := shell_nonempty hk_le
  have : Nonempty {xy // xy ∈ shell n k.val} := ⟨⟨hshell_ne.choose, hshell_ne.choose_spec⟩⟩
  by_cases h2k : 2 * k.val ≤ n
  · -- Small-`k` regime: random rectangle covering + singleton leftover.
    set p_k : ℝ := rectProb n k.val
    set M : ℕ := rectCount n k.val δ
    obtain ⟨hM_pos, f, hf⟩ := exists_good_rect_covering hn h2k hδ0 hδ1
    have hM_pos' : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have h1pd_pos : 0 < 1 + δ := by linarith
    have hS_pos : (0 : ℝ) < ((shell n k.val).card : ℝ) := Nat.cast_pos.mpr hshell_ne.card_pos
    -- Rectangle size `|A_w| * |B_w| = p_k * |S_k|`.
    have hrect_card : ∀ j : Fin M,
        ((rectA (f j).1).card : ℝ) * ((rectB k.val (f j).1).card : ℝ) =
          p_k * ((shell n k.val).card : ℝ) := by
      intro j
      rw [card_rectA (f j).2, card_rectB (f j).2, card_shell]
      dsimp only [p_k, rectProb]
      have h2pow : (2 : ℝ) ^ (n - 2 * k.val) * (2 : ℝ) ^ (2 * k.val) = (2 : ℝ) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel h2k]
      have hch_ne : (Nat.choose n k.val : ℝ) ≠ 0 :=
        ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos hk_le))
      have h2ne : (2 : ℝ) ^ (2 * k.val) ≠ 0 := by positivity
      push_cast
      field_simp [hch_ne, h2ne]
      calc (2 : ℝ) ^ (n - 2 * k.val) * (Nat.choose (2 * k.val) k.val : ℝ) * (2 : ℝ) ^ (2 * k.val)
        _ = ((2 : ℝ) ^ (n - 2 * k.val) * (2 : ℝ) ^ (2 * k.val)) *
              (Nat.choose (2 * k.val) k.val : ℝ) := by ring
        _ = (2 : ℝ) ^ n * (Nat.choose (2 * k.val) k.val : ℝ) := by rw [h2pow]
        _ = (Nat.choose (2 * k.val) k.val : ℝ) * (2 : ℝ) ^ n := by ring
    have hrectA_ne : ∀ j : Fin M, (rectA (f j).1).Nonempty := fun j => by
      rw [← Finset.card_pos, card_rectA (f j).2]; exact Nat.pow_pos (by norm_num)
    have hrectB_ne : ∀ j : Fin M, (rectB k.val (f j).1).Nonempty := fun j => by
      rw [← Finset.card_pos, card_rectB (f j).2]; exact Nat.choose_pos (by omega)
    -- Leftover probability mass on each `xy ∈ shell n k.val`.
    let covCount : (Fin n → Fin 2) × (Fin n → Fin 3) → ℕ := fun xy =>
      (Finset.univ.filter (fun j : Fin M => xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k.val (f j).1)).card
    let remMass : {xy // xy ∈ shell n k.val} → ℝ := fun xy =>
      (1 / ((shell n k.val).card : ℝ)) *
        (1 - (covCount xy.1 : ℝ) / ((1 + δ) * (M : ℝ) * p_k))
    have hpk_pos : 0 < p_k := by
      dsimp only [p_k, rectProb]
      have h1 : (0 : ℝ) < (Nat.choose (2 * k.val) k.val : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos (by omega))
      have h2 : (0 : ℝ) < (Nat.choose n k.val : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos hk_le)
      positivity
    have hrem_nonneg : ∀ xy : {xy // xy ∈ shell n k.val}, 0 ≤ remMass xy := by
      intro ⟨xy, hxy⟩
      dsimp only [remMass]
      refine mul_nonneg (by positivity) ?_
      have hle : (covCount xy : ℝ) ≤ (1 + δ) * (M : ℝ) * p_k := by
        simpa [covCount, M, p_k] using hf xy hxy
      have hden : 0 < (1 + δ) * (M : ℝ) * p_k := by positivity
      have hdiv : (covCount xy : ℝ) / ((1 + δ) * (M : ℝ) * p_k) ≤ 1 := by
        rw [div_le_one hden]; exact hle
      linarith
    have hsum_cov : ∑ xy : {xy // xy ∈ shell n k.val}, (covCount xy.1 : ℝ) =
        (M : ℝ) * p_k * ((shell n k.val).card : ℝ) := by
      have hnat : ∑ xy : {xy // xy ∈ shell n k.val}, covCount xy.1 =
          ∑ j : Fin M, (rectA (f j).1).card * (rectB k.val (f j).1).card := by
        have hlhs : ∑ xy : {xy // xy ∈ shell n k.val}, covCount xy.1 =
            ∑ xy : {xy // xy ∈ shell n k.val}, ∑ j : Fin M,
              if xy.1.1 ∈ rectA (f j).1 ∧ xy.1.2 ∈ rectB k.val (f j).1 then 1 else 0 := by
          refine Finset.sum_congr rfl fun xy _ => ?_
          dsimp only [covCount]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [hlhs, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : (∑ xy : {xy // xy ∈ shell n k.val},
            if xy.1.1 ∈ rectA (f j).1 ∧ xy.1.2 ∈ rectB k.val (f j).1 then 1 else 0) =
            ((rectA (f j).1) ×ˢ (rectB k.val (f j).1)).card := by
          rw [Finset.sum_coe_sort (shell n k.val)
            (fun xy => if xy.1 ∈ rectA (f j).1 ∧ xy.2 ∈ rectB k.val (f j).1 then 1 else 0)]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
          congr 1
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product]
          exact ⟨fun h => h.2, fun h => ⟨rect_subset_shell h.1 h.2, h⟩⟩
        rw [h1, Finset.card_product]
      have hR : ∑ xy : {xy // xy ∈ shell n k.val}, (covCount xy.1 : ℝ) =
          ∑ j : Fin M, ((rectA (f j).1).card : ℝ) * ((rectB k.val (f j).1).card : ℝ) := by
        exact_mod_cast hnat
      rw [hR]
      simp_rw [hrect_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hrem_sum : ∑ xy : {xy // xy ∈ shell n k.val}, remMass xy = δ / (1 + δ) := by
      dsimp only [remMass]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, mul_one, ← Finset.sum_div, hsum_cov]
      have hden1 : (1 + δ) * (M : ℝ) * p_k ≠ 0 := by positivity
      have hden2 : ((shell n k.val).card : ℝ) ≠ 0 := ne_of_gt hS_pos
      field_simp [hden1, hden2]
      ring
    -- Define `W_sum := Fin M ⊕ {xy // xy ∈ shell n k.val}` via `sumDist`.
    have : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
    let Rrem : ProbDist {xy // xy ∈ shell n k.val} :=
      { pmf := fun xy => remMass xy / (δ / (1 + δ))
        nonneg := fun xy => div_nonneg (hrem_nonneg xy) (by positivity)
        sum_one := by
          rw [← Finset.sum_div, hrem_sum]
          exact div_self (by positivity) }
    let pW0 : ProbDist (Fin M ⊕ {xy // xy ∈ shell n k.val}) :=
      sumDist (1 / (1 + δ)) (by positivity) (by rw [div_le_one h1pd_pos]; linarith)
        ProbDist.uniform Rrem
    let PX0 : Fin M ⊕ {xy // xy ∈ shell n k.val} → ProbDist (Fin n → Fin 2) :=
      Sum.elim (fun j => finsetUniform (rectA (f j).1) (hrectA_ne j)) (fun xy => pointMass xy.1.1)
    let PY0 : Fin M ⊕ {xy // xy ∈ shell n k.val} → ProbDist (Fin n → Fin 3) :=
      Sum.elim (fun j => finsetUniform (rectB k.val (f j).1) (hrectB_ne j)) (fun xy => pointMass xy.1.2)
    have hmarg0 : ∀ x y,
        ∑ w : Fin M ⊕ {xy // xy ∈ shell n k.val}, pW0.pmf w * (PX0 w).pmf x * (PY0 w).pmf y =
          (finsetUniform (shell n k.val) hshell_ne).pmf (x, y) := by
      intro x y
      rw [Fintype.sum_sum_type]
      dsimp only [pW0, sumDist, PX0, PY0]
      simp only [Sum.elim_inl, Sum.elim_inr]
      -- First sum: rectangles (`inl`).
      have hterm_rect : ∀ j : Fin M,
          1 / (1 + δ) * (ProbDist.uniform : ProbDist (Fin M)).pmf j *
            (finsetUniform (rectA (f j).1) (hrectA_ne j)).pmf x *
            (finsetUniform (rectB k.val (f j).1) (hrectB_ne j)).pmf y =
          if x ∈ rectA (f j).1 ∧ y ∈ rectB k.val (f j).1 then
            1 / ((1 + δ) * (M : ℝ) * p_k * ((shell n k.val).card : ℝ))
          else 0 := by
        intro j
        dsimp only [ProbDist.uniform, finsetUniform]
        rw [Fintype.card_fin]
        by_cases hxA : x ∈ rectA (f j).1
        · by_cases hyB : y ∈ rectB k.val (f j).1
          · rw [ite_eq_left hxA, ite_eq_left hyB, ite_eq_left ⟨hxA, hyB⟩]
            have hrc := hrect_card j
            have h1 : (1 + δ) ≠ 0 := ne_of_gt h1pd_pos
            have h2 : (M : ℝ) ≠ 0 := ne_of_gt hM_pos'
            have h3 : ((rectA (f j).1).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hrectA_ne j).card_pos.ne'
            have h4 : ((rectB k.val (f j).1).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hrectB_ne j).card_pos.ne'
            calc 1 / (1 + δ) * (1 / (M : ℝ)) * (1 / ((rectA (f j).1).card : ℝ)) *
                    (1 / ((rectB k.val (f j).1).card : ℝ))
              _ = 1 / ((1 + δ) * (M : ℝ) *
                    (((rectA (f j).1).card : ℝ) * ((rectB k.val (f j).1).card : ℝ))) := by
                  field_simp [h1, h2, h3, h4]
              _ = 1 / ((1 + δ) * (M : ℝ) * (p_k * ((shell n k.val).card : ℝ))) := by rw [hrc]
              _ = _ := by ring
          · simp [hxA, hyB]
        · simp [hxA]
      simp_rw [hterm_rect]
      -- Second sum: singletons (`inr`).
      have h1m : 1 - 1 / (1 + δ) = δ / (1 + δ) := by
        field_simp [ne_of_gt h1pd_pos]; ring
      have hterm_rem : ∀ xy : {xy // xy ∈ shell n k.val},
          (1 - 1 / (1 + δ)) * Rrem.pmf xy * (pointMass xy.1.1).pmf x * (pointMass xy.1.2).pmf y =
          if xy.1 = (x, y) then remMass xy else 0 := by
        intro xy
        dsimp only [Rrem, pointMass]
        rw [h1m]
        have hcancel : δ / (1 + δ) * (remMass xy / (δ / (1 + δ))) = remMass xy := by
          have : δ / (1 + δ) ≠ 0 := by positivity
          field_simp [this]
        rw [hcancel]
        by_cases hxy : xy.1 = (x, y)
        · have hx : x = xy.1.1 := by rw [hxy]
          have hy : y = xy.1.2 := by rw [hxy]
          rw [ite_eq_left hxy, ite_eq_left hx, ite_eq_left hy]; ring
        · rw [ite_eq_right hxy]
          by_cases hx : x = xy.1.1
          · have hy : y ≠ xy.1.2 := fun hy => hxy (Prod.ext hx.symm hy.symm)
            simp [hx, hy]
          · simp [hx]
      simp_rw [hterm_rem]
      dsimp only [finsetUniform]
      by_cases hmem : (x, y) ∈ shell n k.val
      · rw [ite_eq_left hmem]
        have hsum1 :
            (∑ j : Fin M, if x ∈ rectA (f j).1 ∧ y ∈ rectB k.val (f j).1 then
              1 / ((1 + δ) * (M : ℝ) * p_k * ((shell n k.val).card : ℝ)) else 0) =
            (covCount (x, y) : ℝ) / ((1 + δ) * (M : ℝ) * p_k * ((shell n k.val).card : ℝ)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          dsimp only [covCount]; ring
        have hsum2 :
            (∑ xy : {xy // xy ∈ shell n k.val}, if xy.1 = (x, y) then remMass xy else 0) =
            remMass ⟨(x, y), hmem⟩ := by
          rw [Finset.sum_eq_single ⟨(x, y), hmem⟩]
          · simp
          · intro xy _ hne
            have : xy.1 ≠ (x, y) := fun h => hne (Subtype.ext h)
            simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum1, hsum2]
        dsimp only [remMass]
        have h1 : (1 + δ) * (M : ℝ) * p_k ≠ 0 := by positivity
        have h2 : ((shell n k.val).card : ℝ) ≠ 0 := ne_of_gt hS_pos
        field_simp [h1, h2]
        ring
      · rw [ite_eq_right hmem]
        have hsum1 :
            (∑ j : Fin M, if x ∈ rectA (f j).1 ∧ y ∈ rectB k.val (f j).1 then
              1 / ((1 + δ) * (M : ℝ) * p_k * ((shell n k.val).card : ℝ)) else 0) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [ite_eq_right]
          rintro ⟨hxA, hyB⟩
          exact hmem (rect_subset_shell hxA hyB)
        have hsum2 :
            (∑ xy : {xy // xy ∈ shell n k.val}, if xy.1 = (x, y) then remMass xy else 0) = 0 := by
          refine Finset.sum_eq_zero fun xy _ => ?_
          have : xy.1 ≠ (x, y) := fun h => hmem (h ▸ xy.2)
          simp [this]
        rw [hsum1, hsum2, add_zero]
    have hent0 : shannonEntropy pW0 ≤
        1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) +
          log2 (Nat.choose n k.val : ℝ) + 2 * δ * (n : ℝ) := by
      dsimp only [pW0]
      rw [shannonEntropy_sumDist]
      have hH_bin : binaryEntropy (1 / (1 + δ)) ≤ 1 :=
        InfoTheory.Known.binaryEntropy_le_one (by positivity) (by rw [div_le_one h1pd_pos]; linarith)
      have hH_unif : shannonEntropy (ProbDist.uniform : ProbDist (Fin M)) ≤ log2 (M : ℝ) := by
        have := shannonEntropy_le_log2_card (ProbDist.uniform : ProbDist (Fin M))
        rwa [Fintype.card_fin] at this
      have hH_rem : shannonEntropy Rrem ≤ 2 * (n : ℝ) := by
        have h1 := shannonEntropy_le_log2_card Rrem
        rw [Fintype.card_coe] at h1
        have h2 : log2 ((shell n k.val).card : ℝ) ≤ log2 ((2 : ℝ) ^ (2 * n)) := by
          apply log2_le_log2 hS_pos
          have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]; norm_num
          rw [← h4]
          exact_mod_cast card_shell_le_four_pow n k.val
        rw [log2_two_pow] at h2
        push_cast at h2
        linarith
      -- Bound `log2 M ≤ log2 (12 * (2n + 1) * (n + 1) / δ^2) + log2 C(n, k)`.
      have hlogM : log2 (M : ℝ) ≤
          log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) + log2 (Nat.choose n k.val : ℝ) := by
        have hpk_le1 : p_k ≤ 1 := by
          dsimp only [p_k, rectProb]
          rw [div_le_one (by
            have : (0 : ℝ) < (Nat.choose n k.val : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hk_le)
            positivity)]
          have hch1 : (1 : ℝ) ≤ (Nat.choose n k.val : ℝ) := by
            exact_mod_cast Nat.choose_pos hk_le
          have hch2 : (Nat.choose (2 * k.val) k.val : ℝ) ≤ (2 : ℝ) ^ (2 * k.val) := by
            have hle : Nat.choose (2 * k.val) k.val ≤ 2 ^ (2 * k.val) := by
              rw [← Nat.sum_range_choose (2 * k.val)]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                (Finset.mem_range.mpr (by omega))
            exact_mod_cast hle
          nlinarith
        have harg_ge1 : (1 : ℝ) ≤ (6 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) := by
          rw [one_le_div (mul_pos (sq_pos_of_pos hδ0) hpk_pos)]
          have hδsq : δ ^ 2 ≤ 1 := by nlinarith
          have : δ ^ 2 * p_k ≤ 1 := by nlinarith
          linarith
        have hM_le1 : (M : ℝ) ≤ (12 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) := by
          have hceil : (M : ℝ) < (6 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) + 1 :=
            Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (6 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) by positivity)
          have hdouble : (12 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) =
              2 * ((6 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k)) := by ring
          linarith
        have hinv_pk : 1 / p_k ≤ ((n : ℝ) + 1) * (Nat.choose n k.val : ℝ) := by
          dsimp only [p_k, rectProb]
          rw [one_div_div]
          have hch_pos : (0 : ℝ) < (Nat.choose (2 * k.val) k.val : ℝ) :=
            Nat.cast_pos.mpr (Nat.choose_pos (by omega))
          rw [div_le_iff₀ hch_pos]
          have hcb : (2 : ℝ) ^ (2 * k.val) ≤
              ((2 * k.val + 1 : ℕ) : ℝ) * (Nat.choose (2 * k.val) k.val : ℝ) := by
            exact_mod_cast central_choose_lower k.val
          have h2kn : ((2 * k.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
            have : 2 * k.val + 1 ≤ n + 1 := by omega
            exact_mod_cast this
          have hch_nk_nonneg : (0 : ℝ) ≤ (Nat.choose n k.val : ℝ) := Nat.cast_nonneg _
          calc (Nat.choose n k.val : ℝ) * (2 : ℝ) ^ (2 * k.val)
            _ ≤ (Nat.choose n k.val : ℝ) *
                  (((2 * k.val + 1 : ℕ) : ℝ) * (Nat.choose (2 * k.val) k.val : ℝ)) :=
                mul_le_mul_of_nonneg_left hcb hch_nk_nonneg
            _ ≤ (Nat.choose n k.val : ℝ) * (((n : ℝ) + 1) * (Nat.choose (2 * k.val) k.val : ℝ)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right h2kn (le_of_lt hch_pos)) hch_nk_nonneg
            _ = ((n : ℝ) + 1) * (Nat.choose n k.val : ℝ) * (Nat.choose (2 * k.val) k.val : ℝ) := by
                ring
        have hM_le2 : (M : ℝ) ≤ (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) *
            (Nat.choose n k.val : ℝ) := by
          calc (M : ℝ)
            _ ≤ (12 * (2 * (n : ℝ) + 1)) / (δ ^ 2 * p_k) := hM_le1
            _ = (12 * (2 * (n : ℝ) + 1) / δ ^ 2) * (1 / p_k) := by ring
            _ ≤ (12 * (2 * (n : ℝ) + 1) / δ ^ 2) * (((n : ℝ) + 1) * (Nat.choose n k.val : ℝ)) :=
                mul_le_mul_of_nonneg_left hinv_pk (by positivity)
            _ = _ := by ring
        have hch_pos : (0 : ℝ) < (Nat.choose n k.val : ℝ) :=
          Nat.cast_pos.mpr (Nat.choose_pos hk_le)
        calc log2 (M : ℝ)
          _ ≤ log2 ((12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) * (Nat.choose n k.val : ℝ)) :=
              log2_le_log2 hM_pos' hM_le2
          _ = log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) + log2 (Nat.choose n k.val : ℝ) :=
              log2_mul_pos (by positivity) hch_pos
      have hfrac1 : 1 / (1 + δ) ≤ 1 := by rw [div_le_one h1pd_pos]; linarith
      have hfrac2 : 1 - 1 / (1 + δ) ≤ δ := by
        have h1m : 1 - 1 / (1 + δ) = δ / (1 + δ) := by field_simp [ne_of_gt h1pd_pos]; ring
        rw [h1m, div_le_iff₀ h1pd_pos]; nlinarith
      have h1_le : (1 / (1 + δ)) * shannonEntropy (ProbDist.uniform : ProbDist (Fin M)) ≤ log2 (M : ℝ) := by
        have hnn := shannonEntropy_nonneg (ProbDist.uniform : ProbDist (Fin M))
        calc _ ≤ 1 * shannonEntropy (ProbDist.uniform : ProbDist (Fin M)) :=
              mul_le_mul_of_nonneg_right hfrac1 hnn
          _ = shannonEntropy (ProbDist.uniform : ProbDist (Fin M)) := one_mul _
          _ ≤ log2 (M : ℝ) := hH_unif
      have h2_le : (1 - 1 / (1 + δ)) * shannonEntropy Rrem ≤ 2 * δ * (n : ℝ) := by
        have hnn := shannonEntropy_nonneg Rrem
        calc _ ≤ δ * shannonEntropy Rrem := mul_le_mul_of_nonneg_right hfrac2 hnn
          _ ≤ δ * (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left hH_rem (le_of_lt hδ0)
          _ = 2 * δ * (n : ℝ) := by ring
      linarith
    obtain ⟨hre_m, hre_e⟩ := reindex_shell_decomp pW0 PX0 PY0
    let e := Fintype.equivFin (Fin M ⊕ {xy // xy ∈ shell n k.val})
    refine ⟨Fintype.card (Fin M ⊕ {xy // xy ∈ shell n k.val}), pW0.map e,
      fun i => PX0 (e.symm i), fun i => PY0 (e.symm i), ?_, ?_⟩
    · intro x y; rw [hre_m x y, hmarg0 x y]
    · rw [ite_eq_left h2k, hre_e]; exact hent0
  · -- Large-`k` regime (`2k > n`): singleton atoms on `shell n k.val`.
    let Wk := {xy // xy ∈ shell n k.val}
    let pW0 : ProbDist Wk := ProbDist.uniform
    let PX0 : Wk → ProbDist (Fin n → Fin 2) := fun xy => pointMass xy.1.1
    let PY0 : Wk → ProbDist (Fin n → Fin 3) := fun xy => pointMass xy.1.2
    have hmarg0 : ∀ x y,
        ∑ w : Wk, pW0.pmf w * (PX0 w).pmf x * (PY0 w).pmf y =
          (finsetUniform (shell n k.val) hshell_ne).pmf (x, y) := by
      intro x y
      dsimp only [pW0, PX0, PY0, ProbDist.uniform, pointMass, finsetUniform]
      rw [Fintype.card_coe]
      by_cases hmem : (x, y) ∈ shell n k.val
      · rw [ite_eq_left hmem, Finset.sum_eq_single ⟨(x, y), hmem⟩]
        · simp
        · intro xy _ hne
          by_cases hx : x = xy.1.1
          · have hy : y ≠ xy.1.2 := fun hy => hne (Subtype.ext (Prod.ext hx.symm hy.symm))
            simp [hx, hy]
          · simp [hx]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [ite_eq_right hmem]
        refine Finset.sum_eq_zero fun xy _ => ?_
        by_cases hx : x = xy.1.1
        · have hy : y ≠ xy.1.2 := fun hy => hmem (by rw [hx, hy]; exact xy.2)
          simp [hx, hy]
        · simp [hx]
    have hent0 : shannonEntropy pW0 ≤ 2 * (n : ℝ) := by
      have h1 := shannonEntropy_le_log2_card pW0
      rw [Fintype.card_coe] at h1
      have h2 : log2 ((shell n k.val).card : ℝ) ≤ log2 ((2 : ℝ) ^ (2 * n)) := by
        apply log2_le_log2 (Nat.cast_pos.mpr hshell_ne.card_pos)
        have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]; norm_num
        rw [← h4]
        exact_mod_cast card_shell_le_four_pow n k.val
      rw [log2_two_pow] at h2
      push_cast at h2
      linarith
    obtain ⟨hre_m, hre_e⟩ := reindex_shell_decomp pW0 PX0 PY0
    let e := Fintype.equivFin Wk
    refine ⟨Fintype.card Wk, pW0.map e, fun i => PX0 (e.symm i), fun i => PY0 (e.symm i), ?_, ?_⟩
    · intro x y; rw [hre_m x y, hmarg0 x y]
    · rw [ite_eq_right h2k, hre_e]; exact hent0

/-- Finite-`n` achievability bound combining all shells for any `n ≥ 1` and `δ ∈ (0, 1/2]`. -/
private lemma sbes_exactCommonInfoSingle_le {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    exactCommonInfoSingle (bipartitePower sbes n) / (n : ℝ) ≤
      binaryEntropy (3 / 4) + 2 * δ +
        (log2 ((n : ℝ) + 1) + 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2)) / (n : ℝ) +
        2 * (7 / 8 : ℝ) ^ n := by
  classical
  -- Choose a shell decomposition on `Fin (kW k)` for each `k : Fin (n + 1)`.
  have hchoice := fun k : Fin (n + 1) => exists_shell_decomposition hn k hδ0 hδ1
  let kW : Fin (n + 1) → ℕ := fun k => (hchoice k).choose
  let pWk : (k : Fin (n + 1)) → ProbDist (Fin (kW k)) := fun k => (hchoice k).choose_spec.choose
  let PXk : (k : Fin (n + 1)) → Fin (kW k) → ProbDist (Fin n → Fin 2) :=
    fun k => (hchoice k).choose_spec.choose_spec.choose
  let PYk : (k : Fin (n + 1)) → Fin (kW k) → ProbDist (Fin n → Fin 3) :=
    fun k => (hchoice k).choose_spec.choose_spec.choose_spec.choose
  have hmarg : ∀ (k : Fin (n + 1)) x y,
      ∑ w : Fin (kW k), (pWk k).pmf w * (PXk k w).pmf x * (PYk k w).pmf y =
        (finsetUniform (shell n k.val) (shell_nonempty (Nat.lt_succ_iff.mp k.isLt))).pmf (x, y) :=
    fun k => (hchoice k).choose_spec.choose_spec.choose_spec.choose_spec.1
  have hent : ∀ k : Fin (n + 1),
      shannonEntropy (pWk k) ≤
        if 2 * k.val ≤ n then
          1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) +
            log2 (Nat.choose n k.val : ℝ) + 2 * δ * (n : ℝ)
        else 2 * (n : ℝ) :=
    fun k => (hchoice k).choose_spec.choose_spec.choose_spec.choose_spec.2
  -- Combine all shells via `sigmaDist (binDist n) pWk` and `prodMixDist`.
  let Wtot := Σ k : Fin (n + 1), Fin (kW k)
  let pW : ProbDist Wtot := sigmaDist (binDist n) pWk
  let PX : Wtot → ProbDist (Fin n → Fin 2) := fun kw => PXk kw.1 kw.2
  let PY : Wtot → ProbDist (Fin n → Fin 3) := fun kw => PYk kw.1 kw.2
  let Q := prodMixDist pW PX PY
  -- Verify marginal `(X^n, Y^n)` is `bipartitePower sbes n`.
  have hQ_marg : Q.map (fun t => (t.1, t.2.1)) = bipartitePower sbes n := by
    refine probDist_ext fun ⟨x, y⟩ => ?_
    rw [prodMixDist_marginal_xy]
    dsimp only [pW, sigmaDist, PX, PY]
    rw [Fintype.sum_sigma]
    have hinner : ∀ k : Fin (n + 1),
        ∑ w : Fin (kW k), (binDist n).pmf k * (pWk k).pmf w * (PXk k w).pmf x * (PYk k w).pmf y =
          (binDist n).pmf k *
            (finsetUniform (shell n k.val) (shell_nonempty (Nat.lt_succ_iff.mp k.isLt))).pmf (x, y) := by
      intro k
      rw [← hmarg k x y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => by ring
    simp_rw [hinner]
    by_cases hcompat : ∀ i : Fin n, y i = 2 ∨ (y i).val = (x i).val
    · let k₀ : Fin (n + 1) :=
        ⟨(nonErasures y).card,
          Nat.lt_succ_of_le (by
            calc (nonErasures y).card ≤ (Finset.univ : Finset (Fin n)).card :=
                  Finset.card_le_card (Finset.subset_univ _)
              _ = n := by simp)⟩
      have hmem0 : (x, y) ∈ shell n k₀.val := by
        simp [shell, k₀, hcompat]
      rw [Finset.sum_eq_single k₀]
      · dsimp only [finsetUniform]
        rw [ite_eq_left hmem0, bipartitePower_sbes_pmf_of_mem_shell hmem0, card_shell]
        dsimp only [binDist]
        have hch_ne : (Nat.choose n k₀.val : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.choose_pos (Nat.lt_succ_iff.mp k₀.isLt)))
        have h2ne : (2 : ℝ) ^ n ≠ 0 := by positivity
        push_cast
        have h18 : (1 / 8 : ℝ) ^ k₀.val * (3 / 8 : ℝ) ^ (n - k₀.val) =
            (1 / 4 : ℝ) ^ k₀.val * (3 / 4 : ℝ) ^ (n - k₀.val) / (2 : ℝ) ^ n := by
          have hk_le : k₀.val ≤ n := Nat.lt_succ_iff.mp k₀.isLt
          calc (1 / 8 : ℝ) ^ k₀.val * (3 / 8 : ℝ) ^ (n - k₀.val)
            _ = ((1 / 4 : ℝ) / 2) ^ k₀.val * ((3 / 4 : ℝ) / 2) ^ (n - k₀.val) := by norm_num
            _ = ((1 / 4 : ℝ) ^ k₀.val / (2 : ℝ) ^ k₀.val) *
                  ((3 / 4 : ℝ) ^ (n - k₀.val) / (2 : ℝ) ^ (n - k₀.val)) := by
                rw [div_pow (1 / 4 : ℝ) (2 : ℝ) k₀.val, div_pow (3 / 4 : ℝ) (2 : ℝ) (n - k₀.val)]
            _ = (1 / 4 : ℝ) ^ k₀.val * (3 / 4 : ℝ) ^ (n - k₀.val) /
                  ((2 : ℝ) ^ k₀.val * (2 : ℝ) ^ (n - k₀.val)) := by ring
            _ = _ := by rw [← pow_add, Nat.add_sub_cancel' hk_le]
        rw [h18]
        field_simp [hch_ne, h2ne]
      · intro k _ hne
        dsimp only [finsetUniform]
        have hnotmem : (x, y) ∉ shell n k.val := by
          intro h
          have hc := (Finset.mem_filter.mp h).2.2
          exact hne (Fin.ext hc.symm)
        simp [hnotmem]
      · intro h; exact absurd (Finset.mem_univ k₀) h
    · -- `(x, y)` is outside `supp(bipartitePower sbes n)`.
      push Not at hcompat
      obtain ⟨i, hy2, hval⟩ := hcompat
      have hzero_rhs : (bipartitePower sbes n).pmf (x, y) = 0 := by
        change ∏ j : Fin n, sbes.pmf (x j, y j) = 0
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        by_contra hne
        have hpos : 0 < sbes.pmf (x i, y i) := lt_of_le_of_ne (sbes.nonneg _) (Ne.symm hne)
        rcases sbes_support_cond (x i) (y i) hpos with h2 | hv
        · exact hy2 h2
        · exact hval hv
      rw [hzero_rhs]
      refine Finset.sum_eq_zero fun k _ => ?_
      dsimp only [finsetUniform]
      have hnotmem : (x, y) ∉ shell n k.val := by
        intro h
        rcases (Finset.mem_filter.mp h).2.1 i with h2 | hv
        · exact hy2 h2
        · exact hval hv
      simp [hnotmem]
  -- Bound `exactCommonInfoSingle ≤ shannonEntropy pW`.
  have hsingle_le : exactCommonInfoSingle (bipartitePower sbes n) ≤ shannonEntropy pW := by
    unfold exactCommonInfoSingle
    have hbdd : BddBelow { r : ℝ | ∃ (kW' : ℕ) (Q' : ProbDist ((Fin n → Fin 2) × (Fin n → Fin 3) × Fin kW')),
        Q'.map (fun t => (t.1, t.2.1)) = bipartitePower sbes n ∧
        condMutualInfo Q' = 0 ∧
        r = shannonEntropy (Q'.map (fun t => t.2.2)) } := by
      refine ⟨0, ?_⟩
      rintro r ⟨_, Q', _, _, rfl⟩
      exact shannonEntropy_nonneg _
    have hmem : shannonEntropy pW ∈ { r : ℝ | ∃ (kW' : ℕ) (Q' : ProbDist ((Fin n → Fin 2) × (Fin n → Fin 3) × Fin kW')),
        Q'.map (fun t => (t.1, t.2.1)) = bipartitePower sbes n ∧
        condMutualInfo Q' = 0 ∧
        r = shannonEntropy (Q'.map (fun t => t.2.2)) } :=
      ⟨Fintype.card Wtot, Q, hQ_marg, prodMixDist_condMutualInfo pW PX PY,
        (prodMixDist_shannonEntropy_w pW PX PY).symm⟩
    exact csInf_le hbdd hmem
  -- Bound `shannonEntropy pW`.
  set C_n : ℝ := 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) + 2 * δ * (n : ℝ)
  have hC_nonneg : 0 ≤ C_n := by
    dsimp only [C_n]
    have harg : (1 : ℝ) ≤ 12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2 := by
      rw [one_le_div (sq_pos_of_pos hδ0)]
      have : δ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hlog : 0 ≤ log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) :=
      log2_nonneg_of_one_le harg
    positivity
  have hH_bin : shannonEntropy (binDist n) ≤ log2 ((n : ℝ) + 1) := by
    have h := shannonEntropy_le_log2_card (binDist n)
    rwa [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h
  have hH_sum : ∑ k : Fin (n + 1), (binDist n).pmf k * shannonEntropy (pWk k) ≤
      C_n + (n : ℝ) * binaryEntropy (3 / 4) + 2 * (n : ℝ) * (7 / 8 : ℝ) ^ n := by
    have hterm_le : ∀ k : Fin (n + 1),
        (binDist n).pmf k * shannonEntropy (pWk k) ≤
          (binDist n).pmf k * C_n +
          (binDist n).pmf k * log2 (Nat.choose n k.val : ℝ) +
          2 * (n : ℝ) * (if 2 * k.val > n then (binDist n).pmf k else 0) := by
      intro k
      have hk_pmf := (binDist n).nonneg k
      have hlog_ch_nn : 0 ≤ log2 (Nat.choose n k.val : ℝ) :=
        log2_nonneg_of_one_le (by exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp k.isLt))
      have hek := hent k
      by_cases h2k : 2 * k.val ≤ n
      · rw [ite_eq_left h2k] at hek
        rw [ite_eq_right (not_lt.mpr h2k), mul_zero, add_zero]
        have : shannonEntropy (pWk k) ≤ C_n + log2 (Nat.choose n k.val : ℝ) := by
          dsimp only [C_n]; linarith
        nlinarith
      · rw [ite_eq_right h2k] at hek
        rw [ite_eq_left (lt_of_not_ge h2k)]
        nlinarith [mul_nonneg hk_pmf hC_nonneg, mul_nonneg hk_pmf hlog_ch_nn]
    calc ∑ k : Fin (n + 1), (binDist n).pmf k * shannonEntropy (pWk k)
      _ ≤ ∑ k : Fin (n + 1), ((binDist n).pmf k * C_n +
            (binDist n).pmf k * log2 (Nat.choose n k.val : ℝ) +
            2 * (n : ℝ) * (if 2 * k.val > n then (binDist n).pmf k else 0)) :=
          Finset.sum_le_sum fun k _ => hterm_le k
      _ = (∑ k : Fin (n + 1), (binDist n).pmf k) * C_n +
          (∑ k : Fin (n + 1), (binDist n).pmf k * log2 (Nat.choose n k.val : ℝ)) +
          2 * (n : ℝ) * (∑ k : Fin (n + 1), if 2 * k.val > n then (binDist n).pmf k else 0) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ 1 * C_n + (n : ℝ) * binaryEntropy (3 / 4) + 2 * (n : ℝ) * (7 / 8 : ℝ) ^ n := by
          rw [(binDist n).sum_one]
          linarith [binDist_expect_log2_choose n,
            mul_le_mul_of_nonneg_left (binDist_tail_le n) (show (0 : ℝ) ≤ 2 * (n : ℝ) by positivity)]
      _ = _ := by ring
  have hHpW : shannonEntropy pW ≤
      log2 ((n : ℝ) + 1) + C_n + (n : ℝ) * binaryEntropy (3 / 4) + 2 * (n : ℝ) * (7 / 8 : ℝ) ^ n := by
    dsimp only [pW]
    rw [shannonEntropy_sigmaDist]
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv := div_le_div_of_nonneg_right (le_trans hsingle_le hHpW) (le_of_lt hn_pos)
  have hrew : (log2 ((n : ℝ) + 1) + C_n + (n : ℝ) * binaryEntropy (3 / 4) + 2 * (n : ℝ) * (7 / 8 : ℝ) ^ n) / (n : ℝ) =
      binaryEntropy (3 / 4) + 2 * δ +
        (log2 ((n : ℝ) + 1) + 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2)) / (n : ℝ) +
        2 * (7 / 8 : ℝ) ^ n := by
    dsimp only [C_n]
    field_simp [ne_of_gt hn_pos]
    ring
  linarith

/-- Asymptotic upper bound `exactCommonInfo sbes ≤ binaryEntropy (3 / 4)`. -/
private theorem sbes_exactCommonInfo_le :
    exactCommonInfo sbes ≤ binaryEntropy (3 / 4) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let δ : ℝ := min (ε / 4) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have h2δ : 2 * δ ≤ ε / 2 := by linarith [min_le_left (ε / 4) (1 / 2)]
  -- Error term 2: `2 * (7/8)^n ≤ ε / 4` for `n ≥ N₁`.
  have htend_pow : Filter.Tendsto (fun n : ℕ => 2 * ((7 / 8 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (7 / 8 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop, 2 * ((7 / 8 : ℝ) ^ n) ≤ ε / 4 := by
    have hlt := htend_pow.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))
    exact hlt.mono fun n hn => le_of_lt hn
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev1
  -- Error term 1: `(log2 (n + 1) + 1 + log2 (12 * (2n + 1) * (n + 1) / δ^2)) / n ≤ ε / 4`.
  let K : ℝ := 1 + log2 (144 / δ ^ 2)
  let B : ℝ := 6 / Real.log 2
  have hterm1_bound : ∀ n : ℕ, 0 < n →
      log2 ((n : ℝ) + 1) + 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) ≤
        K + B * Real.sqrt (n : ℝ) := by
    intro n hn
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog_sqrt : Real.log (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hsq_pos]
    have hlog_n : log2 (n : ℝ) ≤ (2 / Real.log 2) * Real.sqrt (n : ℝ) := by
      unfold log2
      have heq : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
        rw [Real.log_sqrt (by linarith)]; ring
      rw [heq]
      have := mul_le_mul_of_nonneg_left hlog_sqrt (show (0 : ℝ) ≤ 2 / Real.log 2 by
        exact div_nonneg (by norm_num) (le_of_lt log_two_pos))
      linarith [show (2 * Real.log (Real.sqrt (n : ℝ))) / Real.log 2 =
        (2 / Real.log 2) * Real.log (Real.sqrt (n : ℝ)) by ring]
    have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have h2 : 2 * (n : ℝ) + 1 ≤ 3 * (n : ℝ) := by linarith
    have hprod_le : ((n : ℝ) + 1) * (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) ≤
        (144 / δ ^ 2) * ((n : ℝ) ^ 3) := by
      have ha : ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) ≤ (2 * (n : ℝ)) * (3 * (n : ℝ)) :=
        mul_le_mul h1 h2 (by linarith) (by linarith)
      have hmul1 : ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) ≤
          (2 * (n : ℝ)) * (3 * (n : ℝ)) * (2 * (n : ℝ)) :=
        mul_le_mul ha h1 (by linarith) (by positivity)
      have hmul2 : 12 * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) / δ ^ 2 ≤
          12 * ((2 * (n : ℝ)) * (3 * (n : ℝ)) * (2 * (n : ℝ))) / δ ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmul1 (by norm_num)) (by positivity)
      have hlhs : ((n : ℝ) + 1) * (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) =
          12 * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) / δ ^ 2 := by ring
      have hrhs : 12 * ((2 * (n : ℝ)) * (3 * (n : ℝ)) * (2 * (n : ℝ))) / δ ^ 2 =
          (144 / δ ^ 2) * ((n : ℝ) ^ 3) := by ring
      linarith
    have hlog_sum : log2 ((n : ℝ) + 1) + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) ≤
        log2 (144 / δ ^ 2) + 3 * log2 (n : ℝ) := by
      rw [← log2_mul_pos (by linarith) (by positivity)]
      calc log2 (((n : ℝ) + 1) * (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2))
        _ ≤ log2 ((144 / δ ^ 2) * ((n : ℝ) ^ 3)) := log2_le_log2 (by positivity) hprod_le
        _ = log2 (144 / δ ^ 2) + log2 ((n : ℝ) ^ 3) := log2_mul_pos (by positivity) (by positivity)
        _ = log2 (144 / δ ^ 2) + 3 * log2 (n : ℝ) := by rw [log2_pow]; norm_num
    dsimp only [K, B]
    linarith [show 3 * ((2 / Real.log 2) * Real.sqrt (n : ℝ)) =
      (6 / Real.log 2) * Real.sqrt (n : ℝ) by ring]
  -- Choose concrete `n`.
  let A : ℝ := max K 0 + B
  have hB_pos : 0 < B := div_pos (by norm_num) log_two_pos
  have hA_pos : 0 < A := by dsimp only [A]; linarith [le_max_right K 0]
  let N₂ : ℕ := Nat.ceil ((4 * A / ε) ^ 2) + 1
  let n : ℕ := max N₁ (max N₂ 1)
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N₂ 1) (le_max_right N₁ _))
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hstep1 := sbes_exactCommonInfoSingle_le hn hδ0 hδ1
  have hpow_le : 2 * ((7 / 8 : ℝ) ^ n) ≤ ε / 4 := hN₁ n (le_max_left _ _)
  have hsq_ge : 4 * A / ε ≤ Real.sqrt (n : ℝ) := by
    have hn_ge_N2 : (N₂ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_left N₂ 1) (le_max_right N₁ _)
    have hceil : (4 * A / ε) ^ 2 ≤ (n : ℝ) := by
      have h1 : (4 * A / ε) ^ 2 ≤ (Nat.ceil ((4 * A / ε) ^ 2) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil ((4 * A / ε) ^ 2) : ℝ) ≤ (N₂ : ℝ) := by
        dsimp only [N₂]; push_cast; linarith
      linarith
    have hnonneg : 0 ≤ 4 * A / ε := by positivity
    calc 4 * A / ε = Real.sqrt ((4 * A / ε) ^ 2) := (Real.sqrt_sq hnonneg).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hceil
  have hterm1_le :
      (log2 ((n : ℝ) + 1) + 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2)) / (n : ℝ) ≤
        ε / 4 := by
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hsq_ge1 : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn_ge1
    have hnum : log2 ((n : ℝ) + 1) + 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2) ≤
        A * Real.sqrt (n : ℝ) := by
      have hb := hterm1_bound n hn
      have hK_le : K ≤ max K 0 := le_max_left K 0
      have hmax_le : max K 0 ≤ max K 0 * Real.sqrt (n : ℝ) := by
        nlinarith [le_max_right K 0]
      dsimp only [A]
      linarith
    have hdiv1 : (A * Real.sqrt (n : ℝ)) / (n : ℝ) = A / Real.sqrt (n : ℝ) := by
      calc (A * Real.sqrt (n : ℝ)) / (n : ℝ)
        _ = (A * Real.sqrt (n : ℝ)) / (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
            rw [Real.mul_self_sqrt (by linarith)]
        _ = A / Real.sqrt (n : ℝ) := mul_div_mul_right A (Real.sqrt (n : ℝ)) (ne_of_gt hsq_pos)
    have hdiv2 : A / Real.sqrt (n : ℝ) ≤ ε / 4 := by
      rw [div_le_iff₀ hsq_pos]
      rw [div_le_iff₀ hε] at hsq_ge
      linarith
    calc (log2 ((n : ℝ) + 1) + 1 + log2 (12 * (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / δ ^ 2)) / (n : ℝ)
      _ ≤ (A * Real.sqrt (n : ℝ)) / (n : ℝ) := div_le_div_of_nonneg_right hnum (by linarith)
      _ = A / Real.sqrt (n : ℝ) := hdiv1
      _ ≤ ε / 4 := hdiv2
  -- Show `exactCommonInfo sbes ≤ exactCommonInfoSingle (bipartitePower sbes n) / n`.
  have hexact_le : exactCommonInfo sbes ≤ exactCommonInfoSingle (bipartitePower sbes n) / (n : ℝ) := by
    unfold exactCommonInfo
    refine csInf_le ?_ ⟨n, hn, rfl⟩
    refine ⟨0, ?_⟩
    rintro r ⟨m, hm, rfl⟩
    exact div_nonneg (exactCommonInfoSingle_nonneg _) (Nat.cast_nonneg m)
  linarith

end UpperBound

/-! ### Section 5: Disproof of `CommonInformationExactVsWyner.Statement` -/

theorem disproof : ¬ InfoTheory.Problems.CommonInformationExactVsWyner.Statement := by
  intro hStmt
  obtain ⟨n, hn, heq⟩ := hStmt 2 3 (by norm_num) (by norm_num) sbes
  have hlt : binaryEntropy (3 / 4) < exactCommonInfoSingle (bipartitePower sbes n) / (n : ℝ) :=
    sbes_finite_n_strict_lower_bound n hn
  have hle : exactCommonInfo sbes ≤ binaryEntropy (3 / 4) :=
    sbes_exactCommonInfo_le
  linarith

end InfoTheory.Solutions.CommonInformationExactVsWyner
