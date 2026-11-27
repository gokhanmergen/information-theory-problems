import InfoTheory.Bridge.ChannelAchievability

/-!
# Error Exponents: Chernoff–Stein Lemma & Gallager's Random-Coding Bound

Purely additive, kernel-verified formalization of two cornerstone error-exponent theorems
built directly on top of `InfoTheory.Bridge.ChannelAchievability` and `InfoTheory.Core.Channels`:

1. **Chernoff–Stein Lemma (Cover & Thomas, Theorem 11.8.3)**:
   - `htType1Error`, `htType2Error` (Type-I and Type-II hypothesis testing error probabilities)
   - `klDivergence_iidDist` (`D(P^n ‖ Q^n) = n · D(P ‖ Q)` for `P ≪ Q`)
   - `relEntTypicalSet` (relative-entropy typical set `A_δ^(n)(P ‖ Q)`, Def. 11.8.1)
   - `chernoff_stein_achievability` (for `P ≪ Q`, `ε ∈ (0, 1)`, `δ > 0`, eventually `α_n ≤ ε` and
     `β_n ≤ 2^(-n (D(P ‖ Q) - δ))`)
   - `chernoff_stein_converse` and `chernoff_stein_converse_rate`
     (`(1 - ε) (-log₂ β_n) ≤ n D(P ‖ Q) + 1`, via Data Processing Inequality for KL divergence)

2. **Gallager's (1965) Random-Coding Error Exponent (Gallager 1965, Thm. 1; Cover & Thomas Ch. 7)**:
   - `gallagerE0` (`E_0(ρ, P, W) = -log₂ ∑_y (∑_x P(x) W(y | x)^{1/(1+ρ)})^{1+ρ}`)
   - `gallagerRandomCodingExp` (`E_r(R, W) = sup_{0 ≤ ρ ≤ 1, P} (E_0(ρ, P, W) - ρ R)`,
     definitionally equal to `InfoTheory.randomCodingExponent W R`)
   - `mlDec` (maximum-likelihood decoder for `(n, M)` DMC block codes)
   - `gallager_random_coding_bound` and `dmcMinError_le_gallager`
     (`P_e*(W, n, M) ≤ (M - 1)^ρ · 2^(-n E_0(ρ, P, W))` for all `ρ ∈ [0, 1]`, `P : ProbDist α`)
   - `reliabilitySet_bddAbove_of_isPositive` (finiteness of `reliabilityFunction W R` for strictly
     positive DMCs `W.IsPositive` at `R > 0`)
   - `gallager_le_reliabilityFunction` and `randomCodingExponent_le_reliabilityFunction`
     (`E_r(R, W) ≤ reliabilityFunction W R` directly against `InfoTheory.Core.Channels`)

All theorems leave `Core/`, `Problems/`, `Bridge.lean`, `Known/`, and all other files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Chernoff–Stein Lemma (Cover & Thomas, Theorem 11.8.3) -/

section ChernoffStein

variable {α : Type*} [Fintype α]

/-- Type-I error probability `α_n = P^n(Aᶜ) = 1 - P^n(A)` of a binary hypothesis test
    with acceptance region `A ⊆ α^n` for `H₀ : P` vs `H₁ : Q`. -/
def htType1Error (P : ProbDist α) (n : ℕ) (A : Finset (Fin n → α)) : ℝ :=
  1 - ∑ x ∈ A, (iidDist P n).pmf x

/-- Type-II error probability `β_n = Q^n(A)` of a binary hypothesis test
    with acceptance region `A ⊆ α^n` for `H₀ : P` vs `H₁ : Q`. -/
def htType2Error (Q : ProbDist α) (n : ℕ) (A : Finset (Fin n → α)) : ℝ :=
  ∑ x ∈ A, (iidDist Q n).pmf x

/-- Single-letter log-likelihood ratio `log₂(P(a) / Q(a))` (returning `0` on zero-mass atoms of `P`). -/
private noncomputable def llrBit (P Q : ProbDist α) (a : α) : ℝ :=
  if P.pmf a ≤ 0 then 0 else log2 (P.pmf a / Q.pmf a)

private lemma expected_llrBit (P Q : ProbDist α) :
    ∑ a : α, P.pmf a * llrBit P Q a = klDivergence P Q := by
  unfold llrBit klDivergence
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hp : P.pmf a ≤ 0
  · have hp0 : P.pmf a = 0 := le_antisymm hp (P.nonneg a)
    simp [hp0]
  · simp [hp]

private lemma absCont_iidDist (P Q : ProbDist α) (n : ℕ) (hac : AbsCont P Q) :
    AbsCont (iidDist P n) (iidDist Q n) := by
  intro x hQ0
  unfold iidDist at hQ0 ⊢
  dsimp only at hQ0 ⊢
  rw [Finset.prod_eq_zero_iff] at hQ0 ⊢
  obtain ⟨i, hi, hQi⟩ := hQ0
  exact ⟨i, hi, hac (x i) hQi⟩

/-- **Additivity of KL Divergence on i.i.d. Product Distributions**:
    for `P ≪ Q`, `D(P^n ‖ Q^n) = n · D(P ‖ Q)`. -/
theorem klDivergence_iidDist (P Q : ProbDist α) (n : ℕ) (hac : AbsCont P Q) :
    klDivergence (iidDist P n) (iidDist Q n) = (n : ℝ) * klDivergence P Q := by
  have hterm : ∀ x : Fin n → α,
      (if (iidDist P n).pmf x ≤ 0 then (0 : ℝ)
       else (iidDist P n).pmf x * log2 ((iidDist P n).pmf x / (iidDist Q n).pmf x)) =
        (iidDist P n).pmf x * ∑ i : Fin n, llrBit P Q (x i) := by
    intro x
    by_cases hpx : (iidDist P n).pmf x ≤ 0
    · have hp0 : (iidDist P n).pmf x = 0 := le_antisymm hpx ((iidDist P n).nonneg x)
      simp [hp0]
    · have hpos : 0 < (iidDist P n).pmf x := lt_of_not_ge hpx
      have hcoord_P : ∀ i : Fin n, 0 < P.pmf (x i) := fun i => by
        by_contra hle
        have h0 : P.pmf (x i) = 0 := le_antisymm (not_lt.mp hle) (P.nonneg _)
        have hprod0 : (iidDist P n).pmf x = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) h0
        linarith
      have hcoord_Q : ∀ i : Fin n, 0 < Q.pmf (x i) := fun i =>
        lt_of_le_of_ne (Q.nonneg (x i)) fun h => by
          have := hac (x i) h.symm
          linarith [hcoord_P i]
      have hdiv : (iidDist P n).pmf x / (iidDist Q n).pmf x =
          ∏ i : Fin n, (P.pmf (x i) / Q.pmf (x i)) := by
        unfold iidDist; dsimp only
        rw [Finset.prod_div_distrib]
      have hlog : log2 ((iidDist P n).pmf x / (iidDist Q n).pmf x) =
          ∑ i : Fin n, llrBit P Q (x i) := by
        rw [hdiv]
        unfold log2
        rw [Real.log_prod fun i _ => ne_of_gt (div_pos (hcoord_P i) (hcoord_Q i)), Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hni : ¬ (P.pmf (x i) ≤ 0) := not_le.mpr (hcoord_P i)
        simp [llrBit, log2, hni]
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hpx), hlog]
  conv_lhs => unfold klDivergence
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  trans (∑ _i : Fin n, klDivergence P Q)
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [iidDist_sum_coord P (llrBit P Q) i, expected_llrBit]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Relative-Entropy Typical Set** `A_δ^(n)(P ‖ Q)` (Cover & Thomas, Definition 11.8.1):
    sequences `x : Fin n → α` with `P^n(x) > 0` satisfying
    `P^n(x) · 2^(-n(D(P ‖ Q) + δ)) ≤ Q^n(x) ≤ P^n(x) · 2^(-n(D(P ‖ Q) - δ))`. -/
noncomputable def relEntTypicalSet (P Q : ProbDist α) (n : ℕ) (δ : ℝ) : Finset (Fin n → α) := by
  classical
  exact Finset.univ.filter fun x =>
    0 < (iidDist P n).pmf x ∧
    (iidDist P n).pmf x * (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q + δ))) ≤ (iidDist Q n).pmf x ∧
    (iidDist Q n).pmf x ≤ (iidDist P n).pmf x * (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ)))

/-- **Chernoff–Stein Lemma — Achievability** (Cover & Thomas, Theorem 11.8.3):
    for any `P ≪ Q`, any `ε ∈ (0, 1)`, and any `δ > 0`, for all sufficiently large `n` there
    exists an acceptance region `A ⊆ α^n` with Type-I error `α_n ≤ ε` and Type-II error
    `β_n ≤ 2^(-n (D(P ‖ Q) - δ))`. -/
theorem chernoff_stein_achievability (P Q : ProbDist α) (hac : AbsCont P Q)
    {ε δ : ℝ} (hε0 : 0 < ε) (_hε1 : ε < 1) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ A : Finset (Fin n → α),
      htType1Error P n A ≤ ε ∧
      htType2Error Q n A ≤ (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) := by
  classical
  let Z : α → ℝ := fun a => llrBit P Q a - klDivergence P Q
  let V : ℝ := ∑ a : α, P.pmf a * (Z a) ^ 2
  have hEZ : ∑ a : α, P.pmf a * Z a = 0 := by
    simp_rw [Z, mul_sub, Finset.sum_sub_distrib, expected_llrBit, ← Finset.sum_mul, P.sum_one,
      one_mul, sub_self]
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (V / (ε * δ ^ 2))
  refine ⟨max N₀ 1, fun n hn => ⟨relEntTypicalSet P Q n δ, ?_, ?_⟩⟩
  · -- Type-I error bound via Chebyshev's inequality on `∑ Z(x_i)`
    have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N₀ 1) hn)
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hcomp_eq : htType1Error P n (relEntTypicalSet P Q n δ) =
        ∑ x ∈ (relEntTypicalSet P Q n δ)ᶜ, (iidDist P n).pmf x := by
      unfold htType1Error
      have h := Finset.sum_add_sum_compl (relEntTypicalSet P Q n δ) (iidDist P n).pmf
      rw [(iidDist P n).sum_one] at h
      linarith
    rw [hcomp_eq]
    have hVar : ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
        (n : ℝ) * V := by
      have hsq : ∀ x : Fin n → α,
          (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
            ∑ i : Fin n, ∑ j : Fin n, (iidDist P n).pmf x * (Z (x i) * Z (x j)) := by
        intro x
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
      simp_rw [hsq]
      rw [Finset.sum_comm]
      trans (∑ i : Fin n, ∑ j : Fin n,
          ∑ x : Fin n → α, (iidDist P n).pmf x * (Z (x i) * Z (x j)))
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      · trans (∑ _i : Fin n, V)
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · have h := iidDist_sum_coord P (fun a => Z a * Z a) i
            simpa [← sq, V] using h
          · intro j _ hji
            rw [iidDist_sum_two_coords P Z Z hji.symm, hEZ, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp
    have hbad : ∀ x ∈ (relEntTypicalSet P Q n δ)ᶜ,
        ((n : ℝ) * δ) ^ 2 * (iidDist P n).pmf x ≤
          (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 := by
      intro x hx
      by_cases hpx : (iidDist P n).pmf x ≤ 0
      · have h0 : (iidDist P n).pmf x = 0 := le_antisymm hpx ((iidDist P n).nonneg x)
        simp [h0]
      · have hpos : 0 < (iidDist P n).pmf x := lt_of_not_ge hpx
        have hcoord_P : ∀ i : Fin n, 0 < P.pmf (x i) := fun i => by
          by_contra hle
          have h0 : P.pmf (x i) = 0 := le_antisymm (not_lt.mp hle) (P.nonneg _)
          have hprod0 : (iidDist P n).pmf x = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) h0
          linarith
        have hcoord_Q : ∀ i : Fin n, 0 < Q.pmf (x i) := fun i =>
          lt_of_le_of_ne (Q.nonneg (x i)) fun h => by
            have := hac (x i) h.symm
            linarith [hcoord_P i]
        have hQpos : 0 < (iidDist Q n).pmf x := by
          unfold iidDist; dsimp only
          exact Finset.prod_pos fun i _ => hcoord_Q i
        have hsum_Z : ∑ i : Fin n, Z (x i) =
            log2 ((iidDist P n).pmf x / (iidDist Q n).pmf x) - (n : ℝ) * klDivergence P Q := by
          simp_rw [Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          congr 1
          have hdiv : (iidDist P n).pmf x / (iidDist Q n).pmf x =
              ∏ i : Fin n, (P.pmf (x i) / Q.pmf (x i)) := by
            unfold iidDist; dsimp only; rw [Finset.prod_div_distrib]
          rw [hdiv]
          unfold log2
          rw [Real.log_prod fun i _ => ne_of_gt (div_pos (hcoord_P i) (hcoord_Q i)), Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hni : ¬ (P.pmf (x i) ≤ 0) := not_le.mpr (hcoord_P i)
          simp [llrBit, log2, hni]
        have hnot : ¬ (0 < (iidDist P n).pmf x ∧
            (iidDist P n).pmf x * (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q + δ))) ≤
              (iidDist Q n).pmf x ∧
            (iidDist Q n).pmf x ≤
              (iidDist P n).pmf x * (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ)))) := by
          simp only [Finset.mem_compl, relEntTypicalSet, Finset.mem_filter, Finset.mem_univ,
            true_and] at hx
          exact hx
        have h2eq : ∀ t : ℝ, (2 : ℝ) ^ t = Real.exp (t * Real.log 2) := fun t => by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
        have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have habs : (n : ℝ) * δ < |∑ i : Fin n, Z (x i)| := by
          by_contra hle
          push Not at hle
          rw [hsum_Z, abs_le] at hle
          apply hnot
          refine ⟨hpos, ?_, ?_⟩
          · -- `P^n(x) * 2^(-n(D+δ)) ≤ Q^n(x)` from `log₂(P^n/Q^n) ≤ n(D+δ)`
            have h1 : Real.log ((iidDist P n).pmf x / (iidDist Q n).pmf x) / Real.log 2 ≤
                (n : ℝ) * (klDivergence P Q + δ) := by
              unfold log2 at hle; linarith [hle.2]
            have h2 : Real.log ((iidDist P n).pmf x / (iidDist Q n).pmf x) ≤
                (n : ℝ) * (klDivergence P Q + δ) * Real.log 2 :=
              (div_le_iff₀ hlog2pos).mp h1
            have hexp : (iidDist P n).pmf x / (iidDist Q n).pmf x ≤
                (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q + δ)) := by
              rw [h2eq, ← Real.exp_log (div_pos hpos hQpos)]
              exact Real.exp_le_exp.mpr h2
            have hinv : (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q + δ))) *
                (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q + δ)) = 1 := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
            have hmul1 : (iidDist P n).pmf x ≤
                (iidDist Q n).pmf x * (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q + δ)) := by
              have := (div_le_iff₀ hQpos).mp hexp
              linarith
            have hmul2 := mul_le_mul_of_nonneg_right hmul1
              (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
                (-((n : ℝ) * (klDivergence P Q + δ)))))
            have hrhs : (iidDist Q n).pmf x * (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q + δ)) *
                (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q + δ))) = (iidDist Q n).pmf x := by
              rw [mul_assoc, mul_comm ((2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q + δ))), hinv, mul_one]
            linarith
          · -- `Q^n(x) ≤ P^n(x) * 2^(-n(D-δ))` from `n(D-δ) ≤ log₂(P^n/Q^n)`
            have h1 : (n : ℝ) * (klDivergence P Q - δ) ≤
                Real.log ((iidDist P n).pmf x / (iidDist Q n).pmf x) / Real.log 2 := by
              unfold log2 at hle; linarith [hle.1]
            have h2 : (n : ℝ) * (klDivergence P Q - δ) * Real.log 2 ≤
                Real.log ((iidDist P n).pmf x / (iidDist Q n).pmf x) :=
              (le_div_iff₀ hlog2pos).mp h1
            have hexp : (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q - δ)) ≤
                (iidDist P n).pmf x / (iidDist Q n).pmf x := by
              rw [h2eq, ← Real.exp_log (div_pos hpos hQpos)]
              exact Real.exp_le_exp.mpr h2
            have hinv : (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) *
                (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q - δ)) = 1 := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
            have hmul1 : (iidDist Q n).pmf x * (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q - δ)) ≤
                (iidDist P n).pmf x := by
              have := (le_div_iff₀ hQpos).mp hexp
              linarith
            have hmul2 := mul_le_mul_of_nonneg_right hmul1
              (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
                (-((n : ℝ) * (klDivergence P Q - δ)))))
            have hlhs : (iidDist Q n).pmf x * (2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q - δ)) *
                (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) = (iidDist Q n).pmf x := by
              rw [mul_assoc, mul_comm ((2 : ℝ) ^ ((n : ℝ) * (klDivergence P Q - δ))), hinv, mul_one]
            linarith
        have hsq_le : ((n : ℝ) * δ) ^ 2 ≤ (∑ i : Fin n, Z (x i)) ^ 2 := by
          rw [← sq_abs (∑ i : Fin n, Z (x i))]
          have hne0 : 0 ≤ (n : ℝ) * δ := by positivity
          nlinarith
        nlinarith
    have hsum_bad : ((n : ℝ) * δ) ^ 2 *
        ∑ x ∈ (relEntTypicalSet P Q n δ)ᶜ, (iidDist P n).pmf x ≤ (n : ℝ) * V := by
      rw [Finset.mul_sum]
      calc ∑ x ∈ (relEntTypicalSet P Q n δ)ᶜ, ((n : ℝ) * δ) ^ 2 * (iidDist P n).pmf x
        _ ≤ ∑ x ∈ (relEntTypicalSet P Q n δ)ᶜ,
              (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 :=
            Finset.sum_le_sum hbad
        _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg fun x =>
              mul_nonneg ((iidDist P n).nonneg x) (sq_nonneg _)
        _ = (n : ℝ) * V := hVar
    have hden_pos : (0 : ℝ) < (n : ℝ) * δ ^ 2 := by positivity
    have htail : ∑ x ∈ (relEntTypicalSet P Q n δ)ᶜ, (iidDist P n).pmf x ≤
        V / ((n : ℝ) * δ ^ 2) := by
      rw [le_div_iff₀ hden_pos]
      have hrew : ((n : ℝ) * δ) ^ 2 = (n : ℝ) * ((n : ℝ) * δ ^ 2) := by ring
      rw [hrew, mul_assoc, mul_comm ((n : ℝ) * δ ^ 2)] at hsum_bad
      exact le_of_mul_le_mul_left hsum_bad hn_r
    have hn_gt : V / (ε * δ ^ 2) < (n : ℝ) :=
      lt_of_lt_of_le hN₀ (by exact_mod_cast le_trans (le_max_left N₀ 1) hn)
    have hV_le : V / ((n : ℝ) * δ ^ 2) ≤ ε := by
      rw [div_le_iff₀ hden_pos]
      have h1 := (div_lt_iff₀ (by positivity : 0 < ε * δ ^ 2)).mp hn_gt
      linarith
    exact le_trans htail hV_le
  · -- Type-II error bound: `Q^n(A) ≤ 2^(-n(D-δ)) * P^n(A) ≤ 2^(-n(D-δ))`
    unfold htType2Error
    have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    have hP_le1 : ∑ x ∈ relEntTypicalSet P Q n δ, (iidDist P n).pmf x ≤ 1 := by
      calc ∑ x ∈ relEntTypicalSet P Q n δ, (iidDist P n).pmf x
        _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x :=
            Finset.sum_le_univ_sum_of_nonneg fun x => (iidDist P n).nonneg x
        _ = 1 := (iidDist P n).sum_one
    calc ∑ x ∈ relEntTypicalSet P Q n δ, (iidDist Q n).pmf x
      _ ≤ ∑ x ∈ relEntTypicalSet P Q n δ,
            (iidDist P n).pmf x * (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) :=
          Finset.sum_le_sum fun x hx => by
            simp only [relEntTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            exact hx.2.2
      _ = (∑ x ∈ relEntTypicalSet P Q n δ, (iidDist P n).pmf x) *
            (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) :=
          mul_le_mul_of_nonneg_right hP_le1 hpow_nonneg
      _ = (2 : ℝ) ^ (-((n : ℝ) * (klDivergence P Q - δ))) := one_mul _

/-- **Chernoff–Stein Lemma — Converse** (Cover & Thomas, Theorem 11.8.3):
    for any `P ≪ Q`, any `n : ℕ`, and any acceptance region `A ⊆ α^n` with Type-I error
    `α_n ≤ ε < 1`,
    `(1 - ε) · (-log₂ β_n) ≤ n · D(P ‖ Q) + 1`. -/
theorem chernoff_stein_converse (P Q : ProbDist α) (hac : AbsCont P Q)
    (n : ℕ) (A : Finset (Fin n → α)) {ε : ℝ}
    (hα : htType1Error P n A ≤ ε) (hε1 : ε < 1) :
    (1 - ε) * (-log2 (htType2Error Q n A)) ≤ (n : ℝ) * klDivergence P Q + 1 := by
  classical
  let f : (Fin n → α) → Bool := fun x => decide (x ∈ A)
  have hac_n : AbsCont (iidDist P n) (iidDist Q n) := absCont_iidDist P Q n hac
  have hdpi := klDivergence_map_le f (iidDist P n) (iidDist Q n) hac_n
  rw [klDivergence_iidDist P Q n hac] at hdpi
  set p := ∑ x ∈ A, (iidDist P n).pmf x
  set q := htType2Error Q n A
  have hp_nonneg : 0 ≤ p := Finset.sum_nonneg fun x _ => (iidDist P n).nonneg x
  have hp_le1 : p ≤ 1 := by
    calc p ≤ ∑ x : Fin n → α, (iidDist P n).pmf x :=
          Finset.sum_le_univ_sum_of_nonneg fun x => (iidDist P n).nonneg x
      _ = 1 := (iidDist P n).sum_one
  have hq_nonneg : 0 ≤ q := Finset.sum_nonneg fun x _ => (iidDist Q n).nonneg x
  have hq_le1 : q ≤ 1 := by
    calc q ≤ ∑ x : Fin n → α, (iidDist Q n).pmf x :=
          Finset.sum_le_univ_sum_of_nonneg fun x => (iidDist Q n).nonneg x
      _ = 1 := (iidDist Q n).sum_one
  have hp_ge : 1 - ε ≤ p := by
    unfold htType1Error at hα
    linarith
  have hp_pos : 0 < p := by linarith
  have hq_pos : 0 < q := by
    by_contra hqle
    have hq0 : q = 0 := le_antisymm (not_lt.mp hqle) hq_nonneg
    have hQall : ∀ x ∈ A, (iidDist Q n).pmf x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => (iidDist Q n).nonneg x).mp hq0
    have hp0 : p = 0 := Finset.sum_eq_zero fun x hx => hac_n x (hQall x hx)
    linarith
  -- Compute marginals of the binary pushforward `(iidDist P n).map f` and `(iidDist Q n).map f`
  have hmap_true : ∀ R : ProbDist (Fin n → α),
      (R.map f).pmf true = ∑ x ∈ A, R.pmf x := fun R => by
    unfold ProbDist.map
    dsimp only [f]
    simp only [decide_eq_true_eq]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hmap_false : ∀ R : ProbDist (Fin n → α),
      (R.map f).pmf false = 1 - ∑ x ∈ A, R.pmf x := fun R => by
    have hsum := (R.map f).sum_one
    rw [Fintype.sum_bool, hmap_true R] at hsum
    linarith
  have hPtrue : ((iidDist P n).map f).pmf true = p := hmap_true (iidDist P n)
  have hPfalse : ((iidDist P n).map f).pmf false = 1 - p := hmap_false (iidDist P n)
  have hQtrue : ((iidDist Q n).map f).pmf true = q := hmap_true (iidDist Q n)
  have hQfalse : ((iidDist Q n).map f).pmf false = 1 - q := hmap_false (iidDist Q n)
  -- Lower bound `D((iidDist P n).map f ‖ (iidDist Q n).map f) ≥ -h(p) - p * log₂ q`
  have hkl_ge : -binaryEntropy p - p * log2 q ≤
      klDivergence ((iidDist P n).map f) ((iidDist Q n).map f) := by
    unfold klDivergence
    rw [Fintype.sum_bool, hPtrue, hPfalse, hQtrue, hQfalse]
    have htrue_eq : (if p ≤ 0 then (0 : ℝ) else p * log2 (p / q)) =
        -negPLogP p - p * log2 q := by
      have hnp : ¬ (p ≤ 0) := not_le.mpr hp_pos
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hnp), negPLogP]
      rw [log2_div_pos hp_pos hq_pos]
      ring
    have hfalse_ge : -negPLogP (1 - p) ≤
        (if 1 - p ≤ 0 then (0 : ℝ) else (1 - p) * log2 ((1 - p) / (1 - q))) := by
      by_cases h1mp : 1 - p ≤ 0
      · have h0 : 1 - p = 0 := by linarith
        simp [h0, negPLogP]
      · have h1mp_pos : 0 < 1 - p := lt_of_not_ge h1mp
        have h1mq_pos : 0 < 1 - q := by
          by_contra hle
          have h1mq0 : 1 - q = 0 := by linarith
          have hcompQ0 : ∑ x ∈ Aᶜ, (iidDist Q n).pmf x = 0 := by
            have h := Finset.sum_add_sum_compl A (iidDist Q n).pmf
            rw [(iidDist Q n).sum_one] at h
            change q + ∑ x ∈ Aᶜ, (iidDist Q n).pmf x = 1 at h
            linarith
          have hQall : ∀ x ∈ Aᶜ, (iidDist Q n).pmf x = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg fun x _ => (iidDist Q n).nonneg x).mp hcompQ0
          have hcompP0 : ∑ x ∈ Aᶜ, (iidDist P n).pmf x = 0 :=
            Finset.sum_eq_zero fun x hx => hac_n x (hQall x hx)
          have h := Finset.sum_add_sum_compl A (iidDist P n).pmf
          rw [(iidDist P n).sum_one, hcompP0] at h
          change p + 0 = 1 at h
          linarith
        have hlog_nonpos : log2 (1 - q) ≤ 0 := by
          unfold log2
          exact div_nonpos_of_nonpos_of_nonneg
            (Real.log_nonpos (le_of_lt h1mq_pos) (by linarith))
            (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        simp only [ite_eq_right_iff.mpr (fun h => absurd h h1mp), negPLogP]
        rw [log2_div_pos h1mp_pos h1mq_pos]
        have hmul_nonpos : (1 - p) * log2 (1 - q) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt h1mp_pos) hlog_nonpos
        linarith
    unfold binaryEntropy
    linarith
  have hbin : binaryEntropy p ≤ 1 := InfoTheory.Known.binaryEntropy_le_one hp_nonneg hp_le1
  have hneg_logq_nonneg : 0 ≤ -log2 q := by
    unfold log2
    have hlog_nonpos : Real.log q ≤ 0 := Real.log_nonpos (le_of_lt hq_pos) hq_le1
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : Real.log q / Real.log 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog_nonpos (le_of_lt hlog2_pos)
    linarith
  have hmono : (1 - ε) * (-log2 q) ≤ p * (-log2 q) :=
    mul_le_mul_of_nonneg_right hp_ge hneg_logq_nonneg
  linarith

/-- **Chernoff–Stein Lemma — Per-Sample Rate Converse** (Cover & Thomas, Theorem 11.8.3):
    for `n ≥ 1` and `α_n ≤ ε < 1`,
    `(1 - ε) · (-(1/n) log₂ β_n) ≤ D(P ‖ Q) + 1 / n`. -/
theorem chernoff_stein_converse_rate (P Q : ProbDist α) (hac : AbsCont P Q)
    {n : ℕ} (hn : 0 < n) (A : Finset (Fin n → α)) {ε : ℝ}
    (hα : htType1Error P n A ≤ ε) (hε1 : ε < 1) :
    (1 - ε) * (-log2 (htType2Error Q n A) / (n : ℝ)) ≤
      klDivergence P Q + 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hconv := chernoff_stein_converse P Q hac n A hα hε1
  have hdiv := div_le_div_of_nonneg_right hconv (le_of_lt hn_pos)
  calc (1 - ε) * (-log2 (htType2Error Q n A) / (n : ℝ))
    _ = ((1 - ε) * (-log2 (htType2Error Q n A))) / (n : ℝ) := by ring
    _ ≤ ((n : ℝ) * klDivergence P Q + 1) / (n : ℝ) := hdiv
    _ = klDivergence P Q + 1 / (n : ℝ) := by
        rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hn_pos)]

end ChernoffStein

/-! ### 2. Gallager's (1965) Random-Coding Error Exponent -/

section Gallager

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Gallager's auxiliary function `E_0(ρ, P, W)` (Gallager 1965, Eq. 19):
    `E_0(ρ, P, W) = -log₂ (∑_y (∑_x P(x) W(y | x)^{1/(1 + ρ)})^{1 + ρ})`. -/
noncomputable def gallagerE0 (ρ : ℝ) (P : ProbDist α) (W : DMC α β) : ℝ :=
  -log2 (∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ))

/-- Gallager's random-coding error exponent `E_r(R, W)` (Gallager 1965, Theorem 1):
    `E_r(R, W) = sup_{0 ≤ ρ ≤ 1, P} (E_0(ρ, P, W) - ρ R)`. -/
noncomputable def gallagerRandomCodingExp (W : DMC α β) (R : ℝ) : ℝ :=
  sSup { e : ℝ | ∃ (ρ : ℝ) (P : ProbDist α),
    0 ≤ ρ ∧ ρ ≤ 1 ∧ e = gallagerE0 ρ P W - ρ * R }

/-- `gallagerRandomCodingExp` coincides definitionally with `InfoTheory.randomCodingExponent`. -/
lemma gallagerRandomCodingExp_eq_randomCodingExponent (W : DMC α β) (R : ℝ) :
    gallagerRandomCodingExp W R = randomCodingExponent W R := rfl

/-- At `ρ = 0`, Gallager's function vanishes: `E_0(0, P, W) = 0`. -/
lemma gallagerE0_zero (P : ProbDist α) (W : DMC α β) :
    gallagerE0 0 P W = 0 := by
  unfold gallagerE0
  have hsum : ∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + (0 : ℝ)))) ^ (1 + (0 : ℝ)) =
      1 := by
    simp only [add_zero, div_one, Real.rpow_one]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, W.sum_one, mul_one]
    exact P.sum_one
  rw [hsum]
  simp [log2]

/-- Maximum-likelihood (ML) decoder for an `(n, M)` block code (`0 < M`) over a DMC `W`:
    for each received vector `y : Fin n → β`, outputs a message `m : Fin M` maximizing
    `W^n(y | enc m)`. -/
noncomputable def mlDec (W : DMC α β) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → α) (y : Fin n → β) : Fin M :=
  Classical.choose <|
    Finset.exists_max_image (Finset.univ : Finset (Fin M))
      (fun m => (W.power n).trans (enc m) y)
      ⟨⟨0, hM⟩, Finset.mem_univ _⟩

private lemma mlDec_max (W : DMC α β) (n M : ℕ) (hM : 0 < M)
    (enc : Fin M → Fin n → α) (y : Fin n → β) (m : Fin M) :
    (W.power n).trans (enc m) y ≤ (W.power n).trans (enc (mlDec W n M hM enc y)) y :=
  (Classical.choose_spec <|
    Finset.exists_max_image (Finset.univ : Finset (Fin M))
      (fun m' => (W.power n).trans (enc m') y)
      ⟨⟨0, hM⟩, Finset.mem_univ _⟩).2 m (Finset.mem_univ m)

/-- Elementary Young/Bernoulli inequality: `x ^ ρ ≤ ρ * x + (1 - ρ)` for `x ≥ 0`, `0 < ρ ≤ 1`. -/
private lemma rpow_le_linear_of_unit {x ρ : ℝ} (hx : 0 ≤ x) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    x ^ ρ ≤ ρ * x + (1 - ρ) := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [Real.zero_rpow (ne_of_gt hρ0)]
    linarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    set t := ρ * x + (1 - ρ)
    have htpos : 0 < t := by nlinarith
    have h1 : Real.log (x / t) ≤ x / t - 1 := Real.log_le_sub_one_of_pos (div_pos hxpos htpos)
    have h2 : Real.log (1 / t) ≤ 1 / t - 1 := Real.log_le_sub_one_of_pos (div_pos one_pos htpos)
    have hcomb : ρ * Real.log (x / t) + (1 - ρ) * Real.log (1 / t) ≤
        ρ * (x / t - 1) + (1 - ρ) * (1 / t - 1) := by
      have ha := mul_le_mul_of_nonneg_left h1 (le_of_lt hρ0)
      have hb := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - ρ)
      linarith
    have hrhs0 : ρ * (x / t - 1) + (1 - ρ) * (1 / t - 1) = 0 := by
      have htne : t ≠ 0 := ne_of_gt htpos
      field_simp [htne]
      dsimp only [t]
      ring
    have hlhs : ρ * Real.log (x / t) + (1 - ρ) * Real.log (1 / t) =
        ρ * Real.log x - Real.log t := by
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt htpos),
          Real.log_div one_ne_zero (ne_of_gt htpos), Real.log_one]
      ring
    have hlog_le : Real.log x * ρ ≤ Real.log t := by linarith
    calc x ^ ρ = Real.exp (Real.log x * ρ) := Real.rpow_def_of_pos hxpos ρ
      _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr hlog_le
      _ = t := Real.exp_log htpos

/-- Finite weighted Jensen's inequality for the concave function `t ↦ t^ρ` (`0 < ρ ≤ 1`). -/
private lemma weighted_sum_rpow_le {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1) (hv0 : ∀ i, 0 ≤ v i) :
    ∑ i : ι, w i * (v i) ^ ρ ≤ (∑ i : ι, w i * v i) ^ ρ := by
  set μ := ∑ i : ι, w i * v i
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hv0 i)
  by_cases hμz : μ = 0
  · have hall : ∀ i ∈ (Finset.univ : Finset ι), w i * v i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hw0 i) (hv0 i)).mp hμz
    have hlhs : ∑ i : ι, w i * (v i) ^ ρ = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases mul_eq_zero.mp (hall i (Finset.mem_univ i)) with hwi | hvi
      · simp [hwi]
      · rw [hvi, Real.zero_rpow (ne_of_gt hρ0), mul_zero]
    rw [hlhs, hμz, Real.zero_rpow (ne_of_gt hρ0)]
  · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμz)
    have hnorm : ∑ i : ι, w i * (v i / μ) ^ ρ ≤ 1 := by
      calc ∑ i : ι, w i * (v i / μ) ^ ρ
        _ ≤ ∑ i : ι, w i * (ρ * (v i / μ) + (1 - ρ)) :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left
                (rpow_le_linear_of_unit (div_nonneg (hv0 i) (le_of_lt hμpos)) hρ0 hρ1)
                (hw0 i)
        _ = ρ * ((∑ i : ι, w i * v i) / μ) + (1 - ρ) * (∑ i : ι, w i) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
            congr 1
            · rw [Finset.sum_div, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = 1 := by
            change ρ * (μ / μ) + (1 - ρ) * (∑ i : ι, w i) = 1
            rw [div_self (ne_of_gt hμpos), hw1]; ring
    have hμpow_pos : 0 < μ ^ ρ := Real.rpow_pos_of_pos hμpos ρ
    have hmul := mul_le_mul_of_nonneg_right hnorm (le_of_lt hμpow_pos)
    rw [one_mul, Finset.sum_mul] at hmul
    refine le_trans (le_of_eq ?_) hmul
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Real.mul_rpow (div_nonneg (hv0 i) (le_of_lt hμpos)) (le_of_lt hμpos),
      div_mul_cancel₀ _ (ne_of_gt hμpos)]

private lemma finset_prod_rpow_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, (f i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a (Finset.mem_insert_self a s))
        (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Equivalence splitting `Fin M → γ` into the `m`-th coordinate and the remaining `M - 1` coordinates. -/
private def splitPiAt {M : ℕ} {γ : Type*} (m : Fin M) :
    (Fin M → γ) ≃ γ × ({k : Fin M // k ≠ m} → γ) where
  toFun := fun f => (f m, fun k => f k.1)
  invFun := fun ⟨a, g⟩ k => if h : k = m then a else g ⟨k, h⟩
  left_inv := fun f => by funext k; dsimp only; split_ifs with h <;> simp [h]
  right_inv := fun ⟨a, g⟩ => by
    ext
    · simp
    · rename_i k; simp [k.2]

private lemma sum_pi_prod_mul_coord {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (Q : ProbDist γ) (i : ι) (h : γ → ℝ) :
    ∑ g : ι → γ, (∏ k : ι, Q.pmf (g k)) * h (g i) = ∑ x : γ, Q.pmf x * h x := by
  let F : ι → γ → ℝ := fun k x => if k = i then Q.pmf x * h x else Q.pmf x
  have hfun : ∀ g : ι → γ, (∏ k : ι, Q.pmf (g k)) * h (g i) = ∏ k : ι, F k (g k) := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ (fun k => Q.pmf (g k)) (Finset.mem_univ i),
        ← Finset.mul_prod_erase Finset.univ (fun k => F k (g k)) (Finset.mem_univ i)]
    have hrest : ∏ k ∈ Finset.univ.erase i, F k (g k) =
        ∏ k ∈ Finset.univ.erase i, Q.pmf (g k) :=
      Finset.prod_congr rfl fun k hk => by simp [F, (Finset.mem_erase.mp hk).1]
    rw [hrest]; simp only [F, ↓reduceIte]; ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ x : γ, F k x) (Finset.mem_univ i)]
  have hi : ∑ x : γ, F i x = ∑ x : γ, Q.pmf x * h x := by simp [F]
  have hrest : ∏ k ∈ Finset.univ.erase i, ∑ x : γ, F k x = 1 :=
    Finset.prod_eq_one fun k hk => by
      simp only [F, (Finset.mem_erase.mp hk).1, ↓reduceIte]; exact Q.sum_one
  rw [hi, hrest, mul_one]

private lemma sum_pi_prod_factor_at {M : ℕ} {γ : Type*} [Fintype γ]
    (Q : ProbDist γ) (m : Fin M) (f : γ → ℝ) (G : ({k : Fin M // k ≠ m} → γ) → ℝ) :
    ∑ enc : Fin M → γ, (∏ k : Fin M, Q.pmf (enc k)) * (f (enc m) * G (fun k => enc k.1)) =
      (∑ x : γ, Q.pmf x * f x) *
      (∑ g : ({k : Fin M // k ≠ m} → γ),
        (∏ k : {k : Fin M // k ≠ m}, Q.pmf (g k)) * G g) := by
  classical
  rw [← Fintype.sum_equiv (splitPiAt m).symm
    (fun xg => (∏ k : Fin M, Q.pmf ((splitPiAt m).symm xg k)) *
      (f ((splitPiAt m).symm xg m) * G (fun k => (splitPiAt m).symm xg k.1)))
    (fun enc => (∏ k : Fin M, Q.pmf (enc k)) * (f (enc m) * G (fun k => enc k.1)))
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hprod : (∏ k : Fin M, Q.pmf ((splitPiAt m).symm (x, g) k)) =
      Q.pmf x * ∏ k : {k : Fin M // k ≠ m}, Q.pmf (g k) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => Q.pmf ((splitPiAt m).symm (x, g) k)) (Finset.mem_univ m)]
    congr 1
    · simp [splitPiAt]
    · rw [Finset.prod_subtype (Finset.univ.erase m) (p := fun k : Fin M => k ≠ m)
        (fun k => by simp [Finset.mem_erase])]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [splitPiAt, k.2]
  have hfm : (splitPiAt m).symm (x, g) m = x := by simp [splitPiAt]
  have hrest : (fun k : {k : Fin M // k ≠ m} => (splitPiAt m).symm (x, g) k.1) = g := by
    funext k; simp [splitPiAt, k.2]
  rw [hprod, hfm, hrest]
  ring

private lemma gallager_inner_sum_pos (ρ : ℝ) (P : ProbDist α) (W : DMC α β) :
    0 < ∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ) := by
  have hx_exists : ∃ x₀ : α, 0 < P.pmf x₀ := by
    by_contra hno
    push Not at hno
    have h0 : ∑ x : α, P.pmf x = 0 :=
      Finset.sum_eq_zero fun x _ => le_antisymm (hno x) (P.nonneg x)
    linarith [P.sum_one]
  obtain ⟨x₀, hx₀⟩ := hx_exists
  have hy_exists : ∃ y₀ : β, 0 < W.trans x₀ y₀ := by
    by_contra hno
    push Not at hno
    have h0 : ∑ y : β, W.trans x₀ y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hno y) (W.nonneg x₀ y)
    linarith [W.sum_one x₀]
  obtain ⟨y₀, hy₀⟩ := hy_exists
  have hterm_nonneg : ∀ y : β,
      0 ≤ (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ) := fun y =>
    Real.rpow_nonneg
      (Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg x) (Real.rpow_nonneg (W.nonneg x y) _)) _
  have hinner_pos : 0 < ∑ x : α, P.pmf x * (W.trans x y₀) ^ (1 / (1 + ρ)) := by
    have h0pos : 0 < P.pmf x₀ * (W.trans x₀ y₀) ^ (1 / (1 + ρ)) :=
      mul_pos hx₀ (Real.rpow_pos_of_pos hy₀ _)
    exact lt_of_lt_of_le h0pos
      (Finset.single_le_sum
        (fun x _ => mul_nonneg (P.nonneg x) (Real.rpow_nonneg (W.nonneg x y₀) _))
        (Finset.mem_univ x₀))
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hinner_pos _)
    (Finset.single_le_sum (fun y _ => hterm_nonneg y) (Finset.mem_univ y₀))

private lemma two_rpow_neg_mul_gallagerE0 (ρ : ℝ) (P : ProbDist α) (W : DMC α β) (n : ℕ) :
    (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) =
      (∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ)) ^ n := by
  set S := ∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ)
  have hSpos : 0 < S := gallager_inner_sum_pos ρ P W
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold gallagerE0 log2
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsimp : Real.log 2 * -((n : ℝ) * -(Real.log S / Real.log 2)) = Real.log S * (n : ℝ) := by
    field_simp [hlog2ne]
  rw [hsimp, ← Real.rpow_def_of_pos hSpos, Real.rpow_natCast]

private lemma exists_le_of_prob_avg_le {ι : Type*} [Fintype ι]
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
  have hB : ∑ i : ι, w i * B = B := by rw [← Finset.sum_mul, hw1, one_mul]
  linarith

private lemma dmcAvgError_nonneg [DecidableEq β]
    (W : DMC α β) (n M : ℕ) (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) :
    0 ≤ dmcAvgError W n M enc dec := by
  unfold dmcAvgError
  split_ifs
  · exact le_rfl
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ =>
      Finset.sum_nonneg fun y _ => by split_ifs; exact (W.power n).nonneg _ _; exact le_rfl)

private lemma dmcAvgError_le_one [DecidableEq β]
    (W : DMC α β) (n M : ℕ) (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) :
    dmcAvgError W n M enc dec ≤ 1 := by
  unfold dmcAvgError
  split_ifs with hM0
  · norm_num
  · have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM0)
    have hsum : ∑ m : Fin M, ∑ y : Fin n → β,
        (if dec y ≠ m then (W.power n).trans (enc m) y else 0) ≤ (M : ℝ) := by
      calc ∑ m : Fin M, ∑ y : Fin n → β,
            (if dec y ≠ m then (W.power n).trans (enc m) y else 0)
        _ ≤ ∑ m : Fin M, ∑ y : Fin n → β, (W.power n).trans (enc m) y :=
            Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun y _ => by
              split_ifs; exact le_rfl; exact (W.power n).nonneg _ _
        _ = ∑ _m : Fin M, (1 : ℝ) := Finset.sum_congr rfl fun m _ => (W.power n).sum_one (enc m)
        _ = (M : ℝ) := by simp
    have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ))
    have hsimp : (1 : ℝ) / (M : ℝ) * (M : ℝ) = 1 := one_div_mul_cancel (ne_of_gt hMpos)
    linarith

/-- **Gallager's Random-Coding Error Bound** (Gallager 1965, Theorem 1, Eqs. 14–18):
    for any DMC `W`, input distribution `P`, blocklength `n`, message count `M > 0`, and
    `ρ ∈ [0, 1]`, there exists a deterministic `(n, M)` block code `(enc, dec)` satisfying
    `dmcAvgError W n M enc dec ≤ (M - 1)^ρ · 2^(-n E_0(ρ, P, W))`. -/
theorem gallager_random_coding_bound [DecidableEq β]
    (W : DMC α β) (P : ProbDist α) (n M : ℕ) (hM : 0 < M)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M),
      dmcAvgError W n M enc dec ≤
        ((M - 1 : ℕ) : ℝ) ^ ρ * (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) := by
  classical
  -- Extract a witness `a₀ : α` from `P.sum_one = 1`
  have ha₀ : Nonempty α := by
    by_contra hempty
    have h0 : ∑ x : α, P.pmf x = 0 := Finset.sum_eq_zero fun x _ => (hempty ⟨x⟩).elim
    linarith [P.sum_one]
  -- Handle `ρ = 0` directly: RHS = `1 * 2^0 = 1 ≥ dmcAvgError`
  by_cases hρz : ρ = 0
  · subst hρz
    refine ⟨fun _ _ => Classical.arbitrary α, fun _ => ⟨0, hM⟩, ?_⟩
    rw [Real.rpow_zero, gallagerE0_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one]
    exact dmcAvgError_le_one W n M _ _
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρz)
  set s : ℝ := 1 / (1 + ρ)
  have h1ρ_pos : 0 < 1 + ρ := by linarith
  have hs_pos : 0 < s := by dsimp only [s]; positivity
  have hs_id : s + s * ρ = 1 := by
    dsimp only [s]
    field_simp [ne_of_gt h1ρ_pos]
  -- Step 1: Pointwise Gallager upper bound for the ML decoder
  have hpoint : ∀ (enc : Fin M → Fin n → α) (y : Fin n → β) (m : Fin M),
      (if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤
        ((W.power n).trans (enc m) y) ^ s *
          (∑ m' ∈ Finset.univ.erase m, ((W.power n).trans (enc m') y) ^ s) ^ ρ := by
    intro enc y m
    have hrhs_nonneg : 0 ≤ ((W.power n).trans (enc m) y) ^ s *
        (∑ m' ∈ Finset.univ.erase m, ((W.power n).trans (enc m') y) ^ s) ^ ρ :=
      mul_nonneg (Real.rpow_nonneg ((W.power n).nonneg _ _) _)
        (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ((W.power n).nonneg _ _) _) _)
    split_ifs with herr
    · by_cases hpm : (W.power n).trans (enc m) y = 0
      · linarith [hrhs_nonneg]
      · have hpm_pos : 0 < (W.power n).trans (enc m) y :=
          lt_of_le_of_ne ((W.power n).nonneg _ _) (Ne.symm hpm)
        set mstar := mlDec W n M hM enc y
        have hmstar_mem : mstar ∈ Finset.univ.erase m :=
          Finset.mem_erase.mpr ⟨herr, Finset.mem_univ mstar⟩
        have hmax : (W.power n).trans (enc m) y ≤ (W.power n).trans (enc mstar) y :=
          mlDec_max W n M hM enc y m
        have hpow_le : ((W.power n).trans (enc m) y) ^ s ≤
            ∑ m' ∈ Finset.univ.erase m, ((W.power n).trans (enc m') y) ^ s :=
          le_trans (Real.rpow_le_rpow (le_of_lt hpm_pos) hmax (le_of_lt hs_pos))
            (Finset.single_le_sum
              (fun m' _ => Real.rpow_nonneg ((W.power n).nonneg (enc m') y) _) hmstar_mem)
        have hpow_ρ : (((W.power n).trans (enc m) y) ^ s) ^ ρ ≤
            (∑ m' ∈ Finset.univ.erase m, ((W.power n).trans (enc m') y) ^ s) ^ ρ :=
          Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hpm_pos) _) hpow_le hρ0
        have hmul := mul_le_mul_of_nonneg_left hpow_ρ (Real.rpow_nonneg (le_of_lt hpm_pos) s)
        have hlhs : ((W.power n).trans (enc m) y) ^ s * (((W.power n).trans (enc m) y) ^ s) ^ ρ =
            (W.power n).trans (enc m) y := by
          rw [← Real.rpow_mul (le_of_lt hpm_pos), ← Real.rpow_add hpm_pos, hs_id, Real.rpow_one]
        linarith
    · exact hrhs_nonneg
  -- Step 2: For fixed `m` and `y`, average the pointwise bound over `enc ~ codebookProb P n M`
  have havg_y : ∀ (m : Fin M) (y : Fin n → β),
      ∑ enc : Fin M → Fin n → α,
        codebookProb P n M enc *
          (if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤
        ((M - 1 : ℕ) : ℝ) ^ ρ *
          (∑ x : Fin n → α, (iidDist P n).pmf x * ((W.power n).trans x y) ^ s) ^ (1 + ρ) := by
    intro m y
    set A := ∑ x : Fin n → α, (iidDist P n).pmf x * ((W.power n).trans x y) ^ s
    have hA_nonneg : 0 ≤ A :=
      Finset.sum_nonneg fun x _ =>
        mul_nonneg ((iidDist P n).nonneg x) (Real.rpow_nonneg ((W.power n).nonneg x y) _)
    have h1 : ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤
        ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (((W.power n).trans (enc m) y) ^ s *
              (∑ k : {k : Fin M // k ≠ m}, ((W.power n).trans (enc k.1) y) ^ s) ^ ρ) := by
      refine Finset.sum_le_sum fun enc _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (codebookProb_nonneg P n M enc)
      have hsub : ∑ m' ∈ Finset.univ.erase m, ((W.power n).trans (enc m') y) ^ s =
          ∑ k : {k : Fin M // k ≠ m}, ((W.power n).trans (enc k.1) y) ^ s :=
        Finset.sum_subtype (Finset.univ.erase m) (p := fun k : Fin M => k ≠ m)
          (fun k => by simp [Finset.mem_erase])
          (fun m' => ((W.power n).trans (enc m') y) ^ s)
      rw [← hsub]
      exact hpoint enc y m
    have hfact : ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (((W.power n).trans (enc m) y) ^ s *
              (∑ k : {k : Fin M // k ≠ m}, ((W.power n).trans (enc k.1) y) ^ s) ^ ρ) =
        A * ∑ g : ({k : Fin M // k ≠ m} → Fin n → α),
          (∏ k : {k : Fin M // k ≠ m}, (iidDist P n).pmf (g k)) *
            (∑ k : {k : Fin M // k ≠ m}, ((W.power n).trans (g k) y) ^ s) ^ ρ := by
      unfold codebookProb
      exact sum_pi_prod_factor_at (iidDist P n) m
        (fun x => ((W.power n).trans x y) ^ s)
        (fun g => (∑ k : {k : Fin M // k ≠ m}, ((W.power n).trans (g k) y) ^ s) ^ ρ)
    -- Apply Jensen's inequality for `t ↦ t ^ ρ` to the second factor
    let w : ({k : Fin M // k ≠ m} → Fin n → α) → ℝ :=
      fun g => ∏ k : {k : Fin M // k ≠ m}, (iidDist P n).pmf (g k)
    let v : ({k : Fin M // k ≠ m} → Fin n → α) → ℝ :=
      fun g => ∑ k : {k : Fin M // k ≠ m}, ((W.power n).trans (g k) y) ^ s
    have hw0 : ∀ g, 0 ≤ w g := fun g => Finset.prod_nonneg fun k _ => (iidDist P n).nonneg (g k)
    have hw1 : ∑ g, w g = 1 := by
      dsimp only [w]
      rw [← Fintype.prod_sum]
      exact Finset.prod_eq_one fun _ _ => (iidDist P n).sum_one
    have hv0 : ∀ g, 0 ≤ v g := fun g =>
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg ((W.power n).nonneg (g k) y) _
    have hjensen : ∑ g, w g * (v g) ^ ρ ≤ (∑ g, w g * v g) ^ ρ :=
      weighted_sum_rpow_le w v hρpos hρ1 hw0 hw1 hv0
    have hEv : ∑ g, w g * v g = ((M - 1 : ℕ) : ℝ) * A := by
      dsimp only [w, v]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hcard : Fintype.card {k : Fin M // k ≠ m} = M - 1 := by
        rw [Fintype.card_subtype]
        have hfilt : (Finset.univ.filter fun k : Fin M => k ≠ m) = Finset.univ.erase m := by
          ext k; simp [Finset.mem_erase]
        rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
      trans (∑ _k : {k : Fin M // k ≠ m}, A)
      · refine Finset.sum_congr rfl fun k _ => ?_
        exact sum_pi_prod_mul_coord (iidDist P n) k (fun x => ((W.power n).trans x y) ^ s)
      · rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    rw [hEv] at hjensen
    have hmul_A := mul_le_mul_of_nonneg_left hjensen hA_nonneg
    have hcombine : A * (((M - 1 : ℕ) : ℝ) * A) ^ ρ =
        ((M - 1 : ℕ) : ℝ) ^ ρ * A ^ (1 + ρ) := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) hA_nonneg]
      have hApow : A * A ^ ρ = A ^ (1 + ρ) := by
        by_cases hAz : A = 0
        · rw [hAz, zero_mul, Real.zero_rpow (ne_of_gt h1ρ_pos)]
        · have hApos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hAz)
          rw [Real.rpow_add hApos, Real.rpow_one]
      calc A * (((M - 1 : ℕ) : ℝ) ^ ρ * A ^ ρ)
        _ = ((M - 1 : ℕ) : ℝ) ^ ρ * (A * A ^ ρ) := by ring
        _ = ((M - 1 : ℕ) : ℝ) ^ ρ * A ^ (1 + ρ) := by rw [hApow]
    calc ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0)
      _ ≤ A * ∑ g, w g * (v g) ^ ρ := by rw [← hfact]; exact h1
      _ ≤ A * (((M - 1 : ℕ) : ℝ) * A) ^ ρ := hmul_A
      _ = ((M - 1 : ℕ) : ℝ) ^ ρ * A ^ (1 + ρ) := hcombine
  -- Step 3: Tensorize the sum over `y : Fin n → β`
  have htensor :
      ∑ y : Fin n → β,
        (∑ x : Fin n → α, (iidDist P n).pmf x * ((W.power n).trans x y) ^ s) ^ (1 + ρ) =
      (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) := by
    rw [two_rpow_neg_mul_gallagerE0 ρ P W n]
    have hinner : ∀ y : Fin n → β,
        (∑ x : Fin n → α, (iidDist P n).pmf x * ((W.power n).trans x y) ^ s) ^ (1 + ρ) =
        ∏ i : Fin n, (∑ a : α, P.pmf a * (W.trans a (y i)) ^ s) ^ (1 + ρ) := by
      intro y
      have hx_prod : ∀ x : Fin n → α,
          (iidDist P n).pmf x * ((W.power n).trans x y) ^ s =
            ∏ i : Fin n, (P.pmf (x i) * (W.trans (x i) (y i)) ^ s) := by
        intro x
        unfold iidDist DMC.power; dsimp only
        rw [finset_prod_rpow_nonneg Finset.univ (fun i => W.trans (x i) (y i))
          (fun i _ => W.nonneg (x i) (y i)) s, ← Finset.prod_mul_distrib]
      simp_rw [hx_prod]
      rw [← Fintype.prod_sum (fun (i : Fin n) (a : α) => P.pmf a * (W.trans a (y i)) ^ s)]
      exact finset_prod_rpow_nonneg Finset.univ
        (fun i => ∑ a : α, P.pmf a * (W.trans a (y i)) ^ s)
        (fun i _ => Finset.sum_nonneg fun a _ =>
          mul_nonneg (P.nonneg a) (Real.rpow_nonneg (W.nonneg a (y i)) _))
        (1 + ρ)
    simp_rw [hinner]
    rw [← Fintype.prod_sum
      (fun (_ : Fin n) (b : β) => (∑ a : α, P.pmf a * (W.trans a b) ^ s) ^ (1 + ρ))]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Step 4: Sum over `y`, average over `m : Fin M`, and extract a deterministic codebook
  let B := ((M - 1 : ℕ) : ℝ) ^ ρ * (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W))
  have hm_bound : ∀ m : Fin M,
      ∑ enc : Fin M → Fin n → α,
        codebookProb P n M enc *
          (∑ y : Fin n → β,
            if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤ B := by
    intro m
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0)
      _ ≤ ∑ y : Fin n → β, ((M - 1 : ℕ) : ℝ) ^ ρ *
            (∑ x : Fin n → α, (iidDist P n).pmf x * ((W.power n).trans x y) ^ s) ^ (1 + ρ) :=
          Finset.sum_le_sum fun y _ => havg_y m y
      _ = ((M - 1 : ℕ) : ℝ) ^ ρ *
            ∑ y : Fin n → β,
              (∑ x : Fin n → α, (iidDist P n).pmf x * ((W.power n).trans x y) ^ s) ^ (1 + ρ) :=
          (Finset.mul_sum _ _ _).symm
      _ = B := by rw [htensor]
  have hMne : M ≠ 0 := Nat.ne_of_gt hM
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hexp_le : ∑ enc : Fin M → Fin n → α,
      codebookProb P n M enc * dmcAvgError W n M enc (mlDec W n M hM enc) ≤ B := by
    have havg : ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc * dmcAvgError W n M enc (mlDec W n M hM enc) =
        ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (∑ y : Fin n → β,
              if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) := by
      unfold dmcAvgError
      simp only [hMne, ↓reduceIte]
      have hrew : ∀ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ y : Fin n → β,
              if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) =
          ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
            codebookProb P n M enc *
              (∑ y : Fin n → β,
                if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0) := by
        intro enc
        rw [← mul_assoc, mul_comm (codebookProb P n M enc), mul_assoc, Finset.mul_sum]
      simp_rw [hrew]
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    rw [havg]
    calc ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ enc : Fin M → Fin n → α,
          codebookProb P n M enc *
            (∑ y : Fin n → β,
              if mlDec W n M hM enc y ≠ m then (W.power n).trans (enc m) y else 0)
      _ ≤ ((1 : ℝ) / (M : ℝ)) * ∑ _m : Fin M, B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hm_bound m) (by positivity)
      _ = ((1 : ℝ) / (M : ℝ)) * ((M : ℝ) * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = B := by field_simp [ne_of_gt hMpos]
  obtain ⟨enc, henc⟩ := exists_le_of_prob_avg_le
    (codebookProb P n M)
    (fun enc => dmcAvgError W n M enc (mlDec W n M hM enc))
    B (codebookProb_nonneg P n M) (codebookProb_sum_one P n M) hexp_le
  exact ⟨enc, mlDec W n M hM enc, henc⟩

/-- **Gallager Bound on Optimal Minimum Block-Code Error Probability**:
    `dmcMinError W n M ≤ (M - 1)^ρ · 2^(-n E_0(ρ, P, W))` for all `0 < M`, `ρ ∈ [0, 1]`,
    and `P : ProbDist α`. -/
theorem dmcMinError_le_gallager [DecidableEq β]
    (W : DMC α β) (P : ProbDist α) (n M : ℕ) (hM : 0 < M)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    dmcMinError W n M ≤
      ((M - 1 : ℕ) : ℝ) ^ ρ * (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) := by
  obtain ⟨enc, dec, hbound⟩ := gallager_random_coding_bound W P n M hM hρ0 hρ1
  have hbdd : BddBelow { e : ℝ | ∃ (enc' : Fin M → Fin n → α) (dec' : (Fin n → β) → Fin M),
      e = dmcAvgError W n M enc' dec' } :=
    ⟨0, by rintro _ ⟨enc', dec', rfl⟩; exact dmcAvgError_nonneg W n M enc' dec'⟩
  exact le_trans (csInf_le hbdd ⟨enc, dec, rfl⟩) hbound

/-- For any strictly positive DMC `W.IsPositive` on a nonempty input alphabet and any rate `R > 0`,
    the set of achievable error exponents defining `reliabilityFunction W R` is bounded above.
    (Note: `W.IsPositive` rules out zero-error/noiseless channels where `dmcMinError = 0` and the
    set of exponents would be `Set.univ`; `R > 0` rules out `M_n = 1` where `dmcMinError = 0`.) -/
theorem reliabilitySet_bddAbove_of_isPositive [Nonempty α] [DecidableEq β]
    (W : DMC α β) (hpos : W.IsPositive) {R : ℝ} (hR : 0 < R) :
    BddAbove { E : ℝ | ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      dmcMinError W n (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))) ≤
        (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) } := by
  have hβ : Nonempty β := by
    by_contra hempty
    have h0 : ∑ y : β, W.trans (Classical.arbitrary α) y = 0 :=
      Finset.sum_eq_zero fun y _ => (hempty ⟨y⟩).elim
    linarith [W.sum_one (Classical.arbitrary α)]
  have hne_ab : (Finset.univ : Finset (α × β)).Nonempty :=
    ⟨(Classical.arbitrary α, Classical.arbitrary β), Finset.mem_univ _⟩
  obtain ⟨xy₀, _, hxy₀_min⟩ := Finset.exists_min_image
    (Finset.univ : Finset (α × β)) (fun xy => W.trans xy.1 xy.2) hne_ab
  set w₀ := W.trans xy₀.1 xy₀.2
  have hw₀_pos : 0 < w₀ := hpos xy₀.1 xy₀.2
  have hw₀_le : ∀ x y, w₀ ≤ W.trans x y := fun x y => hxy₀_min (x, y) (Finset.mem_univ _)
  -- Lower bound `dmcMinError W n (Nat.ceil (2^(n*R))) ≥ (1/2) * w₀^n` for every `n ≥ 1`
  have hmin_ge : ∀ n : ℕ, 1 ≤ n →
      (1 / 2 : ℝ) * w₀ ^ n ≤ dmcMinError W n (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))) := by
    intro n hn1
    set M := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have h2pow_gt1 : (1 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R) := by
      rw [← Real.rpow_zero (2 : ℝ)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (mul_pos hn_r hR)
    have hM_ge2 : 2 ≤ M := by
      by_contra hlt
      push Not at hlt
      have hMle1 : (M : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ hlt
      linarith [Nat.le_ceil ((2 : ℝ) ^ ((n : ℝ) * R))]
    have hMpos : 0 < M := by omega
    have hMne : M ≠ 0 := by omega
    have hSne : { e : ℝ | ∃ (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M),
        e = dmcAvgError W n M enc dec }.Nonempty :=
      ⟨_, fun _ _ => Classical.arbitrary α, fun _ => ⟨0, hMpos⟩, rfl⟩
    refine le_csInf hSne ?_
    rintro _ ⟨enc, dec, rfl⟩
    unfold dmcAvgError
    simp only [hMne, ↓reduceIte]
    have hpow_ge : ∀ (m : Fin M) (y : Fin n → β), w₀ ^ n ≤ (W.power n).trans (enc m) y := by
      intro m y
      unfold DMC.power; dsimp only
      have hprod_le : ∀ (s : Finset (Fin n)),
          ∏ _i ∈ s, w₀ ≤ ∏ i ∈ s, W.trans (enc m i) (y i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.prod_insert hi]
          exact mul_le_mul (hw₀_le _ _) ih
            (Finset.prod_nonneg fun _ _ => le_of_lt hw₀_pos)
            (W.nonneg _ _)
      calc w₀ ^ n = ∏ _i : Fin n, w₀ := by simp
        _ ≤ ∏ i : Fin n, W.trans (enc m i) (y i) := hprod_le Finset.univ
    have hsum_ge : ((M - 1 : ℕ) : ℝ) * w₀ ^ n ≤
        ∑ m : Fin M, ∑ y : Fin n → β,
          if dec y ≠ m then (W.power n).trans (enc m) y else 0 := by
      rw [Finset.sum_comm]
      have hcard_y : (1 : ℝ) ≤ (Fintype.card (Fin n → β) : ℝ) := by
        have : Nonempty (Fin n → β) := ⟨fun _ => Classical.arbitrary β⟩
        exact_mod_cast Fintype.card_pos (α := Fin n → β)
      have hinner : ∀ y : Fin n → β,
          ((M - 1 : ℕ) : ℝ) * w₀ ^ n ≤
            ∑ m : Fin M, if dec y ≠ m then (W.power n).trans (enc m) y else 0 := by
        intro y
        calc ((M - 1 : ℕ) : ℝ) * w₀ ^ n
          _ = ∑ _m ∈ Finset.univ.erase (dec y), w₀ ^ n := by
              rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = ∑ m : Fin M, if dec y ≠ m then w₀ ^ n else 0 := by
              rw [← Finset.sum_filter]
              congr 1
              ext m
              simp [Finset.mem_erase, ne_comm]
          _ ≤ ∑ m : Fin M, if dec y ≠ m then (W.power n).trans (enc m) y else 0 :=
              Finset.sum_le_sum fun m _ => by split_ifs; exact hpow_ge m y; exact le_rfl
      calc ((M - 1 : ℕ) : ℝ) * w₀ ^ n
        _ = 1 * (((M - 1 : ℕ) : ℝ) * w₀ ^ n) := (one_mul _).symm
        _ ≤ (Fintype.card (Fin n → β) : ℝ) * (((M - 1 : ℕ) : ℝ) * w₀ ^ n) :=
            mul_le_mul_of_nonneg_right hcard_y (by positivity)
        _ = ∑ _y : Fin n → β, ((M - 1 : ℕ) : ℝ) * w₀ ^ n := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ y : Fin n → β, ∑ m : Fin M,
              if dec y ≠ m then (W.power n).trans (enc m) y else 0 :=
            Finset.sum_le_sum fun y _ => hinner y
    have hM_r : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
    have hhalf : (1 / 2 : ℝ) ≤ ((1 : ℝ) / (M : ℝ)) * ((M - 1 : ℕ) : ℝ) := by
      have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
      have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge2
      rw [hcast]
      rw [one_div_mul_eq_div, le_div_iff₀ hM_r]
      linarith
    calc (1 / 2 : ℝ) * w₀ ^ n
      _ ≤ (((1 : ℝ) / (M : ℝ)) * ((M - 1 : ℕ) : ℝ)) * w₀ ^ n :=
          mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = ((1 : ℝ) / (M : ℝ)) * (((M - 1 : ℕ) : ℝ) * w₀ ^ n) := by ring
      _ ≤ ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M, ∑ y : Fin n → β,
            if dec y ≠ m then (W.power n).trans (enc m) y else 0 :=
          mul_le_mul_of_nonneg_left hsum_ge (by positivity)
  -- Deduce the explicit upper bound `2 - log2 w₀` on every element `E` of the reliability set
  refine ⟨2 - log2 w₀, fun E hE => ?_⟩
  obtain ⟨N, hN⟩ := hE 1 zero_lt_one
  set n := max N 1
  have hn1 : 1 ≤ n := le_max_right N 1
  have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hle : (1 / 2 : ℝ) * w₀ ^ n ≤ (2 : ℝ) ^ (-(n : ℝ) * (E - 1)) :=
    le_trans (hmin_ge n hn1) (hN n (le_max_left N 1))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_mono : log2 ((1 / 2 : ℝ) * w₀ ^ n) ≤ log2 ((2 : ℝ) ^ (-(n : ℝ) * (E - 1))) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by positivity) hle) (le_of_lt hlog2_pos)
  have hlhs_log : log2 ((1 / 2 : ℝ) * w₀ ^ n) = -1 + (n : ℝ) * log2 w₀ := by
    rw [log2_mul_pos (by norm_num) (pow_pos hw₀_pos n)]
    have hhalf_log : log2 (1 / 2 : ℝ) = -1 := by
      unfold log2
      rw [one_div, Real.log_inv, neg_div, div_self (ne_of_gt hlog2_pos)]
    have hpow_log : log2 (w₀ ^ n) = (n : ℝ) * log2 w₀ := by
      unfold log2
      rw [Real.log_pow, mul_div_assoc]
    rw [hhalf_log, hpow_log]
  have hrhs_log : log2 ((2 : ℝ) ^ (-(n : ℝ) * (E - 1))) = -(n : ℝ) * (E - 1) := by
    unfold log2
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
      mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
  rw [hlhs_log, hrhs_log] at hlog_mono
  have h1 : (n : ℝ) * (E - 1) ≤ 1 - (n : ℝ) * log2 w₀ := by linarith
  have h2 : (n : ℝ) * (E - 1) ≤ (n : ℝ) * (1 - log2 w₀) := by nlinarith
  have h3 : E - 1 ≤ 1 - log2 w₀ := le_of_mul_le_mul_left h2 (by linarith)
  linarith

/-- **Gallager's Random-Coding Exponent Lower-Bounds the Reliability Function**
    (Gallager 1965, Theorem 1):
    for every strictly positive DMC `W` on a nonempty input alphabet and every rate `R > 0`,
    `gallagerRandomCodingExp W R ≤ reliabilityFunction W R`. -/
theorem gallager_le_reliabilityFunction [Nonempty α] [DecidableEq β]
    (W : DMC α β) (hpos : W.IsPositive) {R : ℝ} (hR : 0 < R) :
    gallagerRandomCodingExp W R ≤ reliabilityFunction W R := by
  have hG_ne : { e : ℝ | ∃ (ρ : ℝ) (P : ProbDist α),
      0 ≤ ρ ∧ ρ ≤ 1 ∧ e = gallagerE0 ρ P W - ρ * R }.Nonempty :=
    ⟨gallagerE0 0 ProbDist.uniform W - 0 * R, 0, ProbDist.uniform, le_rfl, zero_le_one, rfl⟩
  have hRel_bdd := reliabilitySet_bddAbove_of_isPositive W hpos hR
  refine csSup_le_csSup hRel_bdd hG_ne ?_
  rintro e ⟨ρ, P, hρ0, hρ1, rfl⟩ ε hε
  refine ⟨0, fun n _ => ?_⟩
  set M := Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R) := Real.rpow_pos_of_pos (by norm_num) _
  have hMpos : 0 < M := Nat.ceil_pos.mpr h2pos
  have hMsub : ((M - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    have hlt : M - 1 < M := Nat.sub_lt hMpos Nat.zero_lt_one
    exact le_of_lt (Nat.lt_ceil.mp hlt)
  have hgal := dmcMinError_le_gallager W P n M hMpos hρ0 hρ1
  have hpow_le : ((M - 1 : ℕ) : ℝ) ^ ρ ≤ ((2 : ℝ) ^ ((n : ℝ) * R)) ^ ρ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hMsub hρ0
  have hpow_mul : ((2 : ℝ) ^ ((n : ℝ) * R)) ^ ρ * (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) =
      (2 : ℝ) ^ (-(n : ℝ) * (gallagerE0 ρ P W - ρ * R)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hexp_mono : (2 : ℝ) ^ (-(n : ℝ) * (gallagerE0 ρ P W - ρ * R)) ≤
      (2 : ℝ) ^ (-(n : ℝ) * ((gallagerE0 ρ P W - ρ * R) - ε)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  calc dmcMinError W n M
    _ ≤ ((M - 1 : ℕ) : ℝ) ^ ρ * (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) := hgal
    _ ≤ ((2 : ℝ) ^ ((n : ℝ) * R)) ^ ρ * (2 : ℝ) ^ (-((n : ℝ) * gallagerE0 ρ P W)) :=
        mul_le_mul_of_nonneg_right hpow_le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    _ = (2 : ℝ) ^ (-(n : ℝ) * (gallagerE0 ρ P W - ρ * R)) := hpow_mul
    _ ≤ (2 : ℝ) ^ (-(n : ℝ) * ((gallagerE0 ρ P W - ρ * R) - ε)) := hexp_mono

/-- **Gallager Lower Bound Directly on `InfoTheory.randomCodingExponent`**:
    for every strictly positive DMC `W` on a nonempty input alphabet and every rate `R > 0`,
    `randomCodingExponent W R ≤ reliabilityFunction W R`. -/
theorem randomCodingExponent_le_reliabilityFunction [Nonempty α] [DecidableEq β]
    (W : DMC α β) (hpos : W.IsPositive) {R : ℝ} (hR : 0 < R) :
    randomCodingExponent W R ≤ reliabilityFunction W R :=
  gallager_le_reliabilityFunction W hpos hR

end Gallager

end InfoTheory.Bridge
