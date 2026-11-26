import InfoTheory.Bridge.CoverThomas
import Mathlib.InformationTheory.Coding.Kraft
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Cover & Thomas Ch. 5 & Ch. 11: Pinsker's Inequality & Source Coding Theorems

Purely additive, kernel-verified foundational theorems built on top of
`InfoTheory.Bridge.CoverThomas` and `Mathlib.InformationTheory.Coding`:

1. **Pinsker's Inequality (Cover & Thomas, Lemma 11.6.1)**:
   - `pinsker_inequality`: `2 * (tvDistance P Q) ^ 2 ≤ Real.log 2 * klDivergence P Q`
     whenever `P ≪ Q`, proved by first establishing the binary Pinsker inequality via the
     Mean Value Theorem and lifting to arbitrary finite alphabets via the Data Processing
     Inequality (`klDivergence_map_le`).
2. **Source Coding Converse (Cover & Thomas, Theorem 5.3.1)**:
   - `source_coding_converse_of_kraft`: lower bound `H(P) / log₂ D ≤ ∑ P(a) |c(a)|` from
     the Kraft sum inequality `∑ D^{-|c(a)|} ≤ 1` via Gibbs' inequality (`klDivergence_nonneg`).
   - `source_coding_converse`: for any injective uniquely decodable code (`IsUniquelyDecodable`),
     derived from Mathlib's Kraft–McMillan inequality.
   - `source_coding_converse_prefixFree`: for any injective prefix-free code (`IsPrefixFree`).
3. **Kraft's Existence Theorem & Shannon–Fano Achievability (Cover & Thomas, Theorems 5.2.1 & 5.4.1)**:
   - `exists_prefixFree_code_of_kraft`: converse of Kraft's inequality — given codeword lengths
     `l : ι → ℕ` with `∑ D^{-l(i)} ≤ 1`, constructs an explicit injective prefix-free code
     `c : ι → List β` with `(c i).length = l i` via sorted base-`D` cumulative intervals.
   - `shannon_fano_achievability`: for any strictly positive `P : ProbDist α` (`∀ a, 0 < P.pmf a`)
     and `2 ≤ |β|`, there exists an injective prefix-free code `c : α → List β` with
     `∑ P(a) |c(a)| < H(P) / log₂ |β| + 1`.
   - `shannon_fano_achievability_support`: strict `< H(P) / log₂ |β| + 1` bound for any
     `P : ProbDist α` by coding the positive support `{a : α // 0 < P.pmf a}`.
   - `shannon_fano_achievability_le`: non-strict `≤ H(P) / log₂ |β| + 1` bound on the full
     alphabet `α` for arbitrary `P : ProbDist α` (tight for point masses such as `(1, 0, 0)`).

This module is purely additive and leaves `Core/`, `Problems/`, `STATEMENT_LOCK.json`,
and existing `Bridge/` files untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Pinsker's Inequality (Cover & Thomas, Lemma 11.6.1) -/

section Pinsker

/-- Boundary binary Pinsker inequality (`p = 0`): `2 q² ≤ -ln(1 - q)` for `0 ≤ q < 1`. -/
private lemma pinsker_zero_left {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    2 * q ^ 2 ≤ -Real.log (1 - q) := by
  rcases eq_or_lt_of_le hq0 with rfl | hqpos
  · simp
  · let g : ℝ → ℝ := fun t => -Real.log (1 - t) - 2 * t ^ 2
    have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) q,
        HasDerivAt g (1 / (1 - t) - 4 * t) t := by
      intro t ht
      have h1mt : 1 - t ≠ 0 := by linarith [ht.2]
      have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
        simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
      have h2 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
        simpa [div_eq_mul_inv, mul_comm] using h1.log h1mt
      have h3 : HasDerivAt (fun s : ℝ => -Real.log (1 - s)) (1 / (1 - t)) t := by
        simpa [neg_div] using h2.fun_neg
      have h4 : HasDerivAt (fun s : ℝ => 2 * s ^ 2) (4 * t) t := by
        have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t ^ 1) t := hasDerivAt_pow 2 t
        have hm := hp.const_mul (2 : ℝ)
        convert hm using 1
        ring
      exact h3.fun_sub h4
    have hcont : ContinuousOn g (Set.Icc 0 q) := fun t ht =>
      (hderiv t ht).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g (fun t => 1 / (1 - t) - 4 * t) hqpos
      hcont (fun t ht => hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have h1mc : 0 < 1 - c := by linarith [hc.2]
    have hge : 0 ≤ 1 / (1 - c) - 4 * c := by
      have hsq : 0 ≤ (1 - 2 * c) ^ 2 := sq_nonneg _
      have heq : 1 / (1 - c) - 4 * c = (1 - 2 * c) ^ 2 / (1 - c) := by
        field_simp [ne_of_gt h1mc]
        ring
      rw [heq]
      exact div_nonneg hsq (le_of_lt h1mc)
    rw [hslope] at hge
    have hdiff : 0 ≤ g q - g 0 := by
      have hqsub : 0 < q - 0 := by linarith
      have hmul := mul_nonneg hge (le_of_lt hqsub)
      rwa [div_mul_cancel₀ _ (ne_of_gt hqsub)] at hmul
    have hg0 : g 0 = 0 := by simp [g]
    dsimp only [g] at hdiff hg0
    linarith

/-- Interior binary Pinsker inequality for `p, q ∈ (0, 1)`:
    `2 (p - q)² ≤ p ln(p / q) + (1 - p) ln((1 - p) / (1 - q))`. -/
private lemma pinsker_binary_inner {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  let f : ℝ → ℝ := fun t =>
    p * (Real.log p - Real.log t) + (1 - p) * (Real.log (1 - p) - Real.log (1 - t)) -
      2 * (p - t) ^ 2
  have hf_eq : ∀ t : ℝ, 0 < t → t < 1 →
      f t = p * Real.log (p / t) + (1 - p) * Real.log ((1 - p) / (1 - t)) - 2 * (p - t) ^ 2 := by
    intro t ht0 ht1
    dsimp only [f]
    rw [Real.log_div (ne_of_gt hp0) (ne_of_gt ht0),
      Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
  have hfp : f p = 0 := by simp [f]
  have hderiv : ∀ t : ℝ, 0 < t → t < 1 →
      HasDerivAt f ((t - p) * (1 / (t * (1 - t)) - 4)) t := by
    intro t ht0 ht1
    have htne : t ≠ 0 := ne_of_gt ht0
    have h1mtne : 1 - t ≠ 0 := by linarith
    have hlogt : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t := Real.hasDerivAt_log htne
    have hterm1 : HasDerivAt (fun s : ℝ => p * (Real.log p - Real.log s)) (p * (0 - t⁻¹)) t :=
      ((hasDerivAt_const t (Real.log p)).fun_sub hlogt).const_mul p
    have h1ms : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)
    have hlog1mt : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
      simpa [div_eq_mul_inv, mul_comm] using h1ms.log h1mtne
    have hterm2 : HasDerivAt (fun s : ℝ => (1 - p) * (Real.log (1 - p) - Real.log (1 - s)))
        ((1 - p) * (0 - (-1 / (1 - t)))) t :=
      ((hasDerivAt_const t (Real.log (1 - p))).fun_sub hlog1mt).const_mul (1 - p)
    have hpms : HasDerivAt (fun s : ℝ => p - s) (-1 : ℝ) t := by
      simpa using (hasDerivAt_const t p).fun_sub (hasDerivAt_id t)
    have hsq : HasDerivAt (fun s : ℝ => (p - s) ^ 2) (2 * (p - t) ^ 1 * (-1)) t :=
      hpms.pow 2
    have hterm3 : HasDerivAt (fun s : ℝ => 2 * (p - s) ^ 2) (2 * (2 * (p - t) ^ 1 * (-1))) t :=
      hsq.const_mul 2
    have hcomb := (hterm1.fun_add hterm2).fun_sub hterm3
    convert hcomb using 1
    field_simp [htne, h1mtne]
    ring
  have hfactor_nonneg : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ 1 / (t * (1 - t)) - 4 := by
    intro t ht0 ht1
    have hprod : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
    have hle : 4 * (t * (1 - t)) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * t)]
    have h4 : 4 ≤ 1 / (t * (1 - t)) := by
      rw [le_div_iff₀ hprod]
      linarith
    linarith
  have hfq_nonneg : 0 ≤ f q := by
    rcases lt_trichotomy p q with hpq | rfl | hqp
    · have hcont : ContinuousOn f (Set.Icc p q) := fun t ht =>
        (hderiv t (lt_of_lt_of_le hp0 ht.1) (lt_of_le_of_lt ht.2 hq1)).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f
        (fun t => (t - p) * (1 / (t * (1 - t)) - 4)) hpq hcont
        (fun t ht => hderiv t (lt_trans hp0 ht.1) (lt_trans ht.2 hq1))
      have hc0 : 0 < c := lt_trans hp0 hc.1
      have hc1 : c < 1 := lt_trans hc.2 hq1
      have hnonneg : 0 ≤ (c - p) * (1 / (c * (1 - c)) - 4) :=
        mul_nonneg (by linarith [hc.1]) (hfactor_nonneg c hc0 hc1)
      rw [hslope, hfp, sub_zero] at hnonneg
      have hqp_pos : 0 < q - p := by linarith
      have hmul := mul_nonneg hnonneg (le_of_lt hqp_pos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hqp_pos)] at hmul
    · rw [hfp]
    · have hcont : ContinuousOn f (Set.Icc q p) := fun t ht =>
        (hderiv t (lt_of_lt_of_le hq0 ht.1) (lt_of_le_of_lt ht.2 hp1)).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f
        (fun t => (t - p) * (1 / (t * (1 - t)) - 4)) hqp hcont
        (fun t ht => hderiv t (lt_trans hq0 ht.1) (lt_trans ht.2 hp1))
      have hc0 : 0 < c := lt_trans hq0 hc.1
      have hc1 : c < 1 := lt_trans hc.2 hp1
      have hnonpos : (c - p) * (1 / (c * (1 - c)) - 4) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith [hc.2]) (hfactor_nonneg c hc0 hc1)
      rw [hslope, hfp, zero_sub] at hnonpos
      have hpq_pos : 0 < p - q := by linarith
      have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hpq_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpq_pos)] at hmul
      linarith
  rw [hf_eq q hq0 hq1] at hfq_nonneg
  linarith

/-- Binary Pinsker inequality on `Bool`:
    `2 (P(true) - Q(true))² ≤ ln 2 · D(P ‖ Q)` whenever `P ≪ Q`. -/
theorem pinsker_bool (P Q : ProbDist Bool) (hac : AbsCont P Q) :
    2 * (P.pmf true - Q.pmf true) ^ 2 ≤ Real.log 2 * klDivergence P Q := by
  set p := P.pmf true
  set q := Q.pmf true
  have hp_false : P.pmf false = 1 - p := by
    have hsum := P.sum_one
    rw [Fintype.sum_bool] at hsum
    linarith
  have hq_false : Q.pmf false = 1 - q := by
    have hsum := Q.sum_one
    rw [Fintype.sum_bool] at hsum
    linarith
  have hp0 : 0 ≤ p := P.nonneg true
  have hp1 : p ≤ 1 := by linarith [P.nonneg false]
  have hq0 : 0 ≤ q := Q.nonneg true
  have hq1 : q ≤ 1 := by linarith [Q.nonneg false]
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hkl : Real.log 2 * klDivergence P Q =
      (if p ≤ 0 then 0 else p * Real.log (p / q)) +
      (if 1 - p ≤ 0 then 0 else (1 - p) * Real.log ((1 - p) / (1 - q))) := by
    unfold klDivergence log2
    rw [Fintype.sum_bool, hp_false, hq_false, mul_add]
    congr 1
    · split_ifs
      · ring
      · field_simp [hlog2ne]; rfl
    · split_ifs
      · ring
      · field_simp [hlog2ne]
  rw [hkl]
  rcases eq_or_lt_of_le hp0 with hp_zero | hp_pos
  · -- Case p = 0
    have hq_lt1 : q < 1 := by
      rcases eq_or_lt_of_le hq1 with hq_eq1 | hlt
      · exfalso
        have hQf0 : Q.pmf false = 0 := by linarith
        have hPf0 : P.pmf false = 0 := hac false hQf0
        linarith
      · exact hlt
    rw [← hp_zero]
    simp only [le_refl, ↓reduceIte, sub_zero, zero_add]
    have h1not : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    rw [ite_eq_right_iff.mpr (fun h => absurd h h1not), one_mul,
      Real.log_div one_ne_zero (ne_of_gt (by linarith)), Real.log_one, zero_sub]
    have := pinsker_zero_left hq0 hq_lt1
    linarith [show (0 - q) ^ 2 = q ^ 2 by ring]
  · rcases eq_or_lt_of_le hp1 with hp_one | hp_lt1
    · -- Case p = 1
      have hq_pos : 0 < q := by
        rcases eq_or_lt_of_le hq0 with hq_eq0 | hgt
        · exfalso
          have hPt0 : P.pmf true = 0 := hac true hq_eq0.symm
          linarith
        · exact hgt
      rw [hp_one]
      simp only [sub_self, le_refl, ↓reduceIte, add_zero]
      have h1not : ¬ ((1 : ℝ) ≤ 0) := by norm_num
      rw [ite_eq_right_iff.mpr (fun h => absurd h h1not), one_mul,
        Real.log_div one_ne_zero (ne_of_gt hq_pos), Real.log_one, zero_sub]
      have h := pinsker_zero_left (q := 1 - q) (by linarith) (by linarith)
      have h1m : 1 - (1 - q) = q := by ring
      rw [h1m] at h
      exact h
    · -- Interior case 0 < p < 1
      have hq_pos : 0 < q := by
        rcases eq_or_lt_of_le hq0 with hq_eq0 | hgt
        · exfalso
          have hPt0 : P.pmf true = 0 := hac true hq_eq0.symm
          linarith
        · exact hgt
      have hq_lt1 : q < 1 := by
        rcases eq_or_lt_of_le hq1 with hq_eq1 | hlt
        · exfalso
          have hQf0 : Q.pmf false = 0 := by linarith
          have hPf0 : P.pmf false = 0 := hac false hQf0
          linarith
        · exact hlt
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hp_pos)),
        ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr (by linarith)))]
      exact pinsker_binary_inner hp_pos hp_lt1 hq_pos hq_lt1

/-- Total variation distance equals `P(A) - Q(A)` for the Scheffé event
    `A = {a | Q(a) ≤ P(a)}`. -/
lemma tvDistance_eq_scheffe_diff {α : Type*} [Fintype α] (P Q : ProbDist α) :
    let f : α → Bool := fun a => decide (Q.pmf a ≤ P.pmf a)
    tvDistance P Q = (P.map f).pmf true - (Q.map f).pmf true := by
  classical
  intro f
  have hPmap : (P.map f).pmf true = ∑ a : α, if Q.pmf a ≤ P.pmf a then P.pmf a else 0 := by
    unfold ProbDist.map
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [f]
  have hQmap : (Q.map f).pmf true = ∑ a : α, if Q.pmf a ≤ P.pmf a then Q.pmf a else 0 := by
    unfold ProbDist.map
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [f]
  have hdiff_zero : ∑ a : α, (P.pmf a - Q.pmf a) = 0 := by
    rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one, sub_self]
  have hident : ∀ a : α, |P.pmf a - Q.pmf a| + (P.pmf a - Q.pmf a) =
      2 * (if Q.pmf a ≤ P.pmf a then P.pmf a - Q.pmf a else 0) := by
    intro a
    by_cases h : Q.pmf a ≤ P.pmf a
    · simp only [h, ↓reduceIte]
      rw [abs_of_nonneg (by linarith)]
      ring
    · simp only [h, ↓reduceIte]
      rw [abs_of_neg (by linarith)]
      ring
  have hsum : (∑ a : α, |P.pmf a - Q.pmf a|) + ∑ a : α, (P.pmf a - Q.pmf a) =
      2 * ((P.map f).pmf true - (Q.map f).pmf true) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hident]
    rw [← Finset.mul_sum, hPmap, hQmap, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [hdiff_zero, add_zero] at hsum
  unfold tvDistance
  linarith

/-- Absolute continuity is preserved under pushforward by any deterministic map. -/
lemma absCont_map {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (P Q : ProbDist α) (hac : AbsCont P Q) :
    AbsCont (P.map f) (Q.map f) := by
  classical
  intro b hQb
  unfold ProbDist.map at hQb ⊢
  dsimp only at hQb ⊢
  have hall : ∀ a ∈ (Finset.univ : Finset α),
      (if f a = b then Q.pmf a else 0) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by
      split_ifs; exact Q.nonneg a; exact le_rfl)).mp hQb
  refine Finset.sum_eq_zero fun a ha => ?_
  have hQa := hall a ha
  split_ifs with hfab
  · simp only [hfab, ↓reduceIte] at hQa
    exact hac a hQa
  · rfl

/-- **Pinsker's Inequality** (Cover & Thomas, Lemma 11.6.1):
    for any two finite distributions `P, Q : ProbDist α` with `P ≪ Q`,
    `2 · TV(P, Q)² ≤ ln 2 · D(P ‖ Q)` (equivalently `TV(P, Q) ≤ √(D_nat(P ‖ Q) / 2)`).

    Proved via Cover & Thomas's Data Processing Inequality reduction to the binary Scheffé
    indicator `f(a) = decide (Q(a) ≤ P(a))`. -/
theorem pinsker_inequality {α : Type*} [Fintype α] (P Q : ProbDist α) (hac : AbsCont P Q) :
    2 * (tvDistance P Q) ^ 2 ≤ Real.log 2 * klDivergence P Q := by
  let f : α → Bool := fun a => decide (Q.pmf a ≤ P.pmf a)
  have htv : tvDistance P Q = (P.map f).pmf true - (Q.map f).pmf true :=
    tvDistance_eq_scheffe_diff P Q
  have hbool : 2 * ((P.map f).pmf true - (Q.map f).pmf true) ^ 2 ≤
      Real.log 2 * klDivergence (P.map f) (Q.map f) :=
    pinsker_bool (P.map f) (Q.map f) (absCont_map f P Q hac)
  have hdpi : klDivergence (P.map f) (Q.map f) ≤ klDivergence P Q :=
    klDivergence_map_le f P Q hac
  have hlog2 : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  rw [htv]
  exact le_trans hbool (mul_le_mul_of_nonneg_left hdpi hlog2)

end Pinsker

/-! ### 2. Source Coding Converse (Cover & Thomas, Theorem 5.3.1) -/

section SourceCodingConverse

/-- Any distribution `P` is absolutely continuous w.r.t. a strictly positive distribution `Q`. -/
lemma absCont_of_pos {α : Type*} [Fintype α] (P Q : ProbDist α) (hQ : ∀ a, 0 < Q.pmf a) :
    AbsCont P Q := fun a h0 => absurd h0 (ne_of_gt (hQ a))

/-- **Source Coding Converse from Kraft Sum** (Cover & Thomas, Theorem 5.3.1 core):
    if a code `c : α → List β` over an alphabet of size `D ≥ 2` satisfies the Kraft sum
    inequality `∑ a, (1 / D)^{|c(a)|} ≤ 1`, then its expected length is at least
    `H(P) / log₂ D`. -/
theorem source_coding_converse_of_kraft {α β : Type*} [Fintype α] [Fintype β]
    (hβ : 2 ≤ Fintype.card β) (P : ProbDist α) (c : α → List β)
    (hkraft : ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (c a).length ≤ 1) :
    shannonEntropy P / log2 (Fintype.card β : ℝ) ≤
      ∑ a : α, P.pmf a * ((c a).length : ℝ) := by
  set D : ℝ := (Fintype.card β : ℝ)
  have hDge2 : (2 : ℝ) ≤ D := by dsimp only [D]; exact_mod_cast hβ
  have hDpos : 0 < D := by linarith
  have hDgt1 : 1 < D := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogDpos : 0 < Real.log D := Real.log_pos hDgt1
  have hlog2Dpos : 0 < log2 D := div_pos hlogDpos hlog2pos
  -- Nonemptiness of α follows from ∑ P(a) = 1
  have hneα : Nonempty α := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have h0 := P.sum_one
    simp at h0
  set Z : ℝ := ∑ a : α, (1 / D) ^ (c a).length
  have hZpos : 0 < Z := by
    obtain ⟨a₀⟩ := hneα
    have hterm : 0 < (1 / D) ^ (c a₀).length := by positivity
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum (f := fun a : α => (1 / D) ^ (c a).length)
        (fun a _ => by positivity) (Finset.mem_univ a₀))
  let Q : ProbDist α :=
    { pmf := fun a => (1 / D) ^ (c a).length / Z
      nonneg := fun a => by positivity
      sum_one := by
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt hZpos) }
  have hQpos : ∀ a : α, 0 < Q.pmf a := fun a => div_pos (by positivity) hZpos
  have hkl : 0 ≤ klDivergence P Q := klDivergence_nonneg P Q (absCont_of_pos P Q hQpos)
  have hlog2_pow : ∀ n : ℕ, log2 ((1 / D) ^ n) = -(n : ℝ) * log2 D := by
    intro n
    unfold log2
    rw [Real.log_pow, one_div, Real.log_inv]
    ring
  have hterm : ∀ a : α,
      (if P.pmf a ≤ 0 then (0 : ℝ) else P.pmf a * log2 (P.pmf a / Q.pmf a)) =
        -negPLogP (P.pmf a) + P.pmf a * ((c a).length : ℝ) * log2 D +
          P.pmf a * log2 Z := by
    intro a
    by_cases hp : P.pmf a ≤ 0
    · have hp0 : P.pmf a = 0 := le_antisymm hp (P.nonneg a)
      simp [hp0, negPLogP]
    · have hpos : 0 < P.pmf a := lt_of_not_ge hp
      simp only [hp, ↓reduceIte]
      have hdiv : log2 (P.pmf a / Q.pmf a) =
          log2 (P.pmf a) - (log2 ((1 / D) ^ (c a).length) - log2 Z) := by
        rw [log2_div_pos hpos (hQpos a)]
        change log2 (P.pmf a) - log2 ((1 / D) ^ (c a).length / Z) = _
        rw [log2_div_pos (by positivity) hZpos]
      rw [hdiv, hlog2_pow]
      unfold negPLogP
      simp only [hp, ↓reduceIte]
      ring
  have hkl_expand : klDivergence P Q =
      -shannonEntropy P + (∑ a : α, P.pmf a * ((c a).length : ℝ)) * log2 D + log2 Z := by
    unfold klDivergence shannonEntropy
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, P.sum_one, one_mul]
  have hlogZ_nonpos : log2 Z ≤ 0 := by
    unfold log2
    exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (le_of_lt hZpos) hkraft)
      (le_of_lt hlog2pos)
  rw [hkl_expand] at hkl
  rw [div_le_iff₀ hlog2Dpos]
  linarith

/-- **Source Coding Converse for Uniquely Decodable Codes** (Cover & Thomas, Theorem 5.3.1):
    for any finite alphabet `α`, code alphabet `β` with `2 ≤ |β|`, distribution `P : ProbDist α`,
    and injective uniquely decodable code `c : α → List β`,
    `H(P) / log₂ |β| ≤ ∑ a, P(a) · |c(a)|`. -/
theorem source_coding_converse {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) (P : ProbDist α)
    (c : α → List β) (hc : Function.Injective c)
    (hud : InformationTheory.IsUniquelyDecodable
      ((Finset.univ.image c : Finset (List β)) : Set (List β))) :
    shannonEntropy P / log2 (Fintype.card β : ℝ) ≤
      ∑ a : α, P.pmf a * ((c a).length : ℝ) := by
  have : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  have hkraft : ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (c a).length ≤ 1 := by
    have hsum : ∑ w ∈ Finset.univ.image c, (1 / (Fintype.card β : ℝ)) ^ w.length =
        ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (c a).length :=
      Finset.sum_image (fun a _ b _ h => hc h)
    rw [← hsum]
    exact kraft_mcmillan_inequality hud
  exact source_coding_converse_of_kraft hβ P c hkraft

/-- **Source Coding Converse for Prefix-Free Codes** (Cover & Thomas, Theorem 5.3.1):
    for any injective prefix-free code `c : α → List β` with `2 ≤ |β|`,
    `H(P) / log₂ |β| ≤ ∑ a, P(a) · |c(a)|`. -/
theorem source_coding_converse_prefixFree {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) (P : ProbDist α)
    (c : α → List β) (hc : Function.Injective c)
    (hpf : InformationTheory.IsPrefixFree
      ((Finset.univ.image c : Finset (List β)) : Set (List β))) :
    shannonEntropy P / log2 (Fintype.card β : ℝ) ≤
      ∑ a : α, P.pmf a * ((c a).length : ℝ) := by
  have : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  have hkraft : ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (c a).length ≤ 1 := by
    have hsum : ∑ w ∈ Finset.univ.image c, (1 / (Fintype.card β : ℝ)) ^ w.length =
        ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (c a).length :=
      Finset.sum_image (fun a _ b _ h => hc h)
    rw [← hsum]
    exact hpf.finsetSum_one_div_card_pow_length_le_one
  exact source_coding_converse_of_kraft hβ P c hkraft

end SourceCodingConverse

/-! ### 3. Kraft's Existence Theorem & Shannon–Fano Achievability (Cover & Thomas, Thms. 5.2.1 & 5.4.1) -/

section KraftAndShannonFano

/-- Most-significant-digit-first base-`D` representation of `x` padded to exact length `len`. -/
private def toDigits (D : ℕ) (hD : 0 < D) : ℕ → ℕ → List (Fin D)
  | 0, _ => []
  | m + 1, x => toDigits D hD m (x / D) ++ [⟨x % D, Nat.mod_lt x hD⟩]

private lemma toDigits_length (D : ℕ) (hD : 0 < D) (len x : ℕ) :
    (toDigits D hD len x).length = len := by
  induction len generalizing x with
  | zero => rfl
  | succ m ih => simp [toDigits, ih]

private lemma toDigits_take (D : ℕ) (hD : 0 < D) (m k x : ℕ) :
    (toDigits D hD (m + k) x).take m = toDigits D hD m (x / D ^ k) := by
  induction k generalizing x with
  | zero =>
    simp only [add_zero, pow_zero, Nat.div_one]
    exact List.take_of_length_le (le_of_eq (toDigits_length D hD m x))
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega, toDigits]
    have hlen : m ≤ (toDigits D hD (m + k) (x / D)).length := by
      rw [toDigits_length]; omega
    rw [List.take_append_of_le_length hlen, ih (x / D), Nat.div_div_eq_div_mul, ← pow_succ']

private lemma toDigits_injective (D : ℕ) (hD : 0 < D) (m : ℕ) {x y : ℕ}
    (hx : x < D ^ m) (hy : y < D ^ m)
    (heq : toDigits D hD m x = toDigits D hD m y) : x = y := by
  induction m generalizing x y with
  | zero =>
    simp only [pow_zero] at hx hy
    omega
  | succ m ih =>
    simp only [toDigits] at heq
    have hpair := List.append_inj heq (by simp [toDigits_length])
    have hdiv : x / D = y / D := by
      apply ih
      · exact (Nat.div_lt_iff_lt_mul hD).mpr (by rwa [← pow_succ])
      · exact (Nat.div_lt_iff_lt_mul hD).mpr (by rwa [← pow_succ])
      · exact hpair.1
    have hmod : x % D = y % D := by
      have hfin : (⟨x % D, Nat.mod_lt x hD⟩ : Fin D) = ⟨y % D, Nat.mod_lt y hD⟩ :=
        List.singleton_injective hpair.2
      exact congrArg Fin.val hfin
    rw [← Nat.div_add_mod x D, ← Nat.div_add_mod y D, hdiv, hmod]

/-- Kraft existence theorem for a sorted length tuple `f : Fin n → ℕ`. -/
private lemma exists_prefixFree_code_of_kraft_monotone {n : ℕ} {β : Type*} [Fintype β]
    [DecidableEq β] [Nonempty β] (f : Fin n → ℕ) (hf : Monotone f)
    (hkraft : ∑ i : Fin n, (1 / (Fintype.card β : ℝ)) ^ (f i) ≤ 1) :
    ∃ c : Fin n → List β,
      Function.Injective c ∧
      InformationTheory.IsPrefixFree ((Finset.univ.image c : Finset (List β)) : Set (List β)) ∧
      ∀ i, (c i).length = f i := by
  set D : ℕ := Fintype.card β
  have hDpos : 0 < D := Fintype.card_pos
  have hDRpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hDpos
  have hDRne : (D : ℝ) ≠ 0 := ne_of_gt hDRpos
  set L : ℕ := Finset.univ.sup f
  have hfleL : ∀ i : Fin n, f i ≤ L := fun i => Finset.le_sup (Finset.mem_univ i)
  -- Convert the real Kraft sum inequality to a natural-number inequality after multiplying by D^L
  have hkraft_nat : ∑ i : Fin n, D ^ (L - f i) ≤ D ^ L := by
    have hmul : (∑ i : Fin n, (1 / (D : ℝ)) ^ (f i)) * (D : ℝ) ^ L ≤ 1 * (D : ℝ) ^ L :=
      mul_le_mul_of_nonneg_right hkraft (by positivity)
    rw [Finset.sum_mul, one_mul] at hmul
    have hterm : ∀ i : Fin n, (1 / (D : ℝ)) ^ (f i) * (D : ℝ) ^ L = ((D ^ (L - f i) : ℕ) : ℝ) := by
      intro i
      rw [Nat.cast_pow, one_div, inv_pow]
      have hsplit : (D : ℝ) ^ L = (D : ℝ) ^ (f i) * (D : ℝ) ^ (L - f i) := by
        rw [← pow_add, Nat.add_sub_cancel' (hfleL i)]
      rw [hsplit, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hDRne), one_mul]
    simp_rw [hterm, ← Nat.cast_sum, ← Nat.cast_pow] at hmul
    exact Nat.cast_le.mp hmul
  -- Cumulative prefix sum S(k) = ∑_{j < k} D^{L - f j}
  let S : Fin n → ℕ := fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k), D ^ (L - f j)
  have hdiv : ∀ k : Fin n, D ^ (L - f k) ∣ S k := by
    intro k
    refine Finset.dvd_sum fun j hj => ?_
    have hjk : j < k := (Finset.mem_filter.mp hj).2
    have hfjle : f j ≤ f k := hf (le_of_lt hjk)
    exact pow_dvd_pow D (by have := hfleL k; omega)
  let q : Fin n → ℕ := fun k => S k / D ^ (L - f k)
  have hq_mul : ∀ k : Fin n, q k * D ^ (L - f k) = S k := fun k =>
    Nat.div_mul_cancel (hdiv k)
  have hS_step : ∀ {i j : Fin n}, i < j → S i + D ^ (L - f i) ≤ S j := by
    intro i j hij
    have hsub : insert i (Finset.univ.filter (fun m : Fin n => m < i)) ⊆
        Finset.univ.filter (fun m : Fin n => m < j) := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      rcases hm with rfl | hmi
      · exact hij
      · exact lt_trans hmi hij
    have hnotmem : i ∉ Finset.univ.filter (fun m : Fin n => m < i) := by simp
    have hle := Finset.sum_le_sum_of_subset (f := fun m : Fin n => D ^ (L - f m)) hsub
    rw [Finset.sum_insert hnotmem] at hle
    dsimp only [S]
    omega
  have hS_bound : ∀ k : Fin n, S k + D ^ (L - f k) ≤ D ^ L := by
    intro k
    have hsub : insert k (Finset.univ.filter (fun m : Fin n => m < k)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hnotmem : k ∉ Finset.univ.filter (fun m : Fin n => m < k) := by simp
    have hle := Finset.sum_le_sum_of_subset (f := fun m : Fin n => D ^ (L - f m)) hsub
    rw [Finset.sum_insert hnotmem] at hle
    dsimp only [S]
    omega
  have hq_lt : ∀ k : Fin n, q k < D ^ (f k) := by
    intro k
    have hb := hS_bound k
    rw [← hq_mul k] at hb
    have hmul_le : (q k + 1) * D ^ (L - f k) ≤ D ^ (f k) * D ^ (L - f k) := by
      rw [add_mul, one_mul, ← pow_add, Nat.add_sub_cancel' (hfleL k)]
      exact hb
    have hle : q k + 1 ≤ D ^ (f k) :=
      Nat.le_of_mul_le_mul_right hmul_le (pow_pos hDpos _)
    omega
  let equivβ : β ≃ Fin D := Fintype.equivFin β
  let raw : Fin n → List (Fin D) := fun k => toDigits D hDpos (f k) (q k)
  let c : Fin n → List β := fun k => (raw k).map equivβ.symm
  have hno_prefix_lt : ∀ {i j : Fin n}, i < j → ¬ (raw i <+: raw j) := by
    intro i j hij hpref
    have hfjge : f i ≤ f j := hf (le_of_lt hij)
    set d : ℕ := f j - f i
    have hfj_eq : f j = f i + d := by omega
    have htake : (raw j).take (f i) = raw i := by
      rcases hpref with ⟨t, ht⟩
      rw [← ht, List.take_left' (toDigits_length D hDpos (f i) (q i))]
    have htake2 : (raw j).take (f i) = toDigits D hDpos (f i) (q j / D ^ d) := by
      dsimp only [raw]
      rw [hfj_eq]
      exact toDigits_take D hDpos (f i) d (q j)
    have hdig_eq : toDigits D hDpos (f i) (q i) = toDigits D hDpos (f i) (q j / D ^ d) :=
      htake.symm.trans htake2
    have hqj_div_lt : q j / D ^ d < D ^ (f i) := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hDpos d), ← pow_add, ← hfj_eq]
      exact hq_lt j
    have hq_eq : q i = q j / D ^ d :=
      toDigits_injective D hDpos (f i) (hq_lt i) hqj_div_lt hdig_eq
    have hqj_lt : q j < (q i + 1) * D ^ d := by
      have hrem : q j = D ^ d * (q j / D ^ d) + q j % D ^ d := (Nat.div_add_mod _ _).symm
      have hmod : q j % D ^ d < D ^ d := Nat.mod_lt _ (pow_pos hDpos d)
      rw [← hq_eq] at hrem
      nlinarith
    have hpow_mul : D ^ d * D ^ (L - f j) = D ^ (L - f i) := by
      rw [← pow_add]
      congr 1
      have := hfleL j
      omega
    have hstrict : q j * D ^ (L - f j) < (q i + 1) * D ^ (L - f i) := by
      calc q j * D ^ (L - f j)
        _ < ((q i + 1) * D ^ d) * D ^ (L - f j) :=
            Nat.mul_lt_mul_of_pos_right hqj_lt (pow_pos hDpos _)
        _ = (q i + 1) * (D ^ d * D ^ (L - f j)) := by rw [mul_assoc]
        _ = (q i + 1) * D ^ (L - f i) := by rw [hpow_mul]
    rw [hq_mul j, add_mul, one_mul, hq_mul i] at hstrict
    have hstep := hS_step hij
    omega
  have hno_prefix_ne : ∀ {i j : Fin n}, i ≠ j → ¬ (raw i <+: raw j) := by
    intro i j hne hpref
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact hno_prefix_lt hij hpref
    · have hlen_le : (raw i).length ≤ (raw j).length := hpref.length_le
      rw [toDigits_length, toDigits_length] at hlen_le
      have hflen_ge : f j ≤ f i := hf (le_of_lt hji)
      have heq_len : (raw i).length = (raw j).length := by
        rw [toDigits_length, toDigits_length]; omega
      have heq : raw i = raw j := hpref.eq_of_length heq_len
      exact hno_prefix_lt hji (heq ▸ List.prefix_rfl)
  have hraw_pref_of_c : ∀ {i j : Fin n}, c i <+: c j → raw i <+: raw j := by
    intro i j ⟨t, ht⟩
    have hmap : (raw i).map equivβ.symm ++ t = (raw j).map equivβ.symm := ht
    have htake : ((raw j).map equivβ.symm).take (raw i).length = (raw i).map equivβ.symm := by
      rw [← hmap, List.take_left' (by simp)]
    rw [← List.map_take] at htake
    have hraw_take : (raw j).take (raw i).length = raw i :=
      List.map_injective_iff.mpr equivβ.symm.injective htake
    refine ⟨(raw j).drop (raw i).length, ?_⟩
    have htd := List.take_append_drop (raw i).length (raw j)
    rwa [hraw_take] at htd
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    exact hno_prefix_ne hne (hraw_pref_of_c (hij ▸ List.prefix_rfl))
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    by_cases hij : i = j
    · subst hij; rfl
    · exact absurd (hraw_pref_of_c hxy) (hno_prefix_ne hij)
  · intro i
    simp only [c, raw, List.length_map, toDigits_length]

/-- **Kraft's Existence Theorem** (Cover & Thomas, Theorem 5.2.1 converse):
    for any finite index type `ι`, nonempty finite code alphabet `β`, and length function
    `l : ι → ℕ` satisfying `∑ i, (1 / |β|)^{l(i)} ≤ 1`, there exists an injective
    prefix-free code `c : ι → List β` with `(c i).length = l i` for every `i`. -/
theorem exists_prefixFree_code_of_kraft {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] [Nonempty β] (l : ι → ℕ)
    (hkraft : ∑ i : ι, (1 / (Fintype.card β : ℝ)) ^ (l i) ≤ 1) :
    ∃ c : ι → List β,
      Function.Injective c ∧
      InformationTheory.IsPrefixFree ((Finset.univ.image c : Finset (List β)) : Set (List β)) ∧
      ∀ i, (c i).length = l i := by
  let e₀ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f₀ : Fin (Fintype.card ι) → ℕ := l ∘ e₀.symm
  let σ : Equiv.Perm (Fin (Fintype.card ι)) := Tuple.sort f₀
  let e : Fin (Fintype.card ι) ≃ ι := σ.trans e₀.symm
  have hmono : Monotone (l ∘ e) := Tuple.monotone_sort f₀
  have hkraft' : ∑ k : Fin (Fintype.card ι), (1 / (Fintype.card β : ℝ)) ^ ((l ∘ e) k) ≤ 1 := by
    have hsum : ∑ k : Fin (Fintype.card ι), (1 / (Fintype.card β : ℝ)) ^ (l (e k)) =
        ∑ i : ι, (1 / (Fintype.card β : ℝ)) ^ (l i) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    simpa [Function.comp] using hsum.le.trans hkraft
  obtain ⟨c₀, hc₀_inj, hc₀_pf, hc₀_len⟩ :=
    exists_prefixFree_code_of_kraft_monotone (l ∘ e) hmono hkraft'
  let c : ι → List β := fun i => c₀ (e.symm i)
  have himg : ((Finset.univ.image c : Finset (List β)) : Set (List β)) =
      ((Finset.univ.image c₀ : Finset (List β)) : Set (List β)) := by
    ext w
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e.symm i, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨e k, by simp [c]⟩
  refine ⟨c, hc₀_inj.comp e.symm.injective, ?_, fun i => ?_⟩
  · rw [himg]; exact hc₀_pf
  · simpa [c] using hc₀_len (e.symm i)

/-- **Shannon–Fano Code Achievability** (Cover & Thomas, Theorem 5.4.1):
    for any strictly positive distribution `P : ProbDist α` (`∀ a, 0 < P.pmf a`) and code
    alphabet `β` with `2 ≤ |β|`, there exists an injective prefix-free code `c : α → List β`
    with expected length strictly below `H(P) / log₂ |β| + 1`. -/
theorem shannon_fano_achievability {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) (P : ProbDist α) (hpos : ∀ a, 0 < P.pmf a) :
    ∃ c : α → List β,
      Function.Injective c ∧
      InformationTheory.IsPrefixFree ((Finset.univ.image c : Finset (List β)) : Set (List β)) ∧
      ∑ a : α, P.pmf a * ((c a).length : ℝ) <
        shannonEntropy P / log2 (Fintype.card β : ℝ) + 1 := by
  have : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  set D : ℝ := (Fintype.card β : ℝ)
  have hDge2 : (2 : ℝ) ≤ D := by dsimp only [D]; exact_mod_cast hβ
  have hDpos : 0 < D := by linarith
  have hDgt1 : 1 < D := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogDpos : 0 < Real.log D := Real.log_pos hDgt1
  have hlog2Dpos : 0 < log2 D := div_pos hlogDpos hlog2pos
  let l : α → ℕ := fun a => Nat.ceil (-Real.log (P.pmf a) / Real.log D)
  have hkraft_term : ∀ a : α, (1 / D) ^ (l a) ≤ P.pmf a := by
    intro a
    have hceil : -Real.log (P.pmf a) / Real.log D ≤ (l a : ℝ) := Nat.le_ceil _
    have hmul : -Real.log (P.pmf a) ≤ (l a : ℝ) * Real.log D :=
      (div_le_iff₀ hlogDpos).mp hceil
    have hlog_le : Real.log ((1 / D) ^ (l a)) ≤ Real.log (P.pmf a) := by
      rw [Real.log_pow, one_div, Real.log_inv]
      linarith
    exact (Real.log_le_log_iff (by positivity) (hpos a)).mp hlog_le
  have hkraft : ∑ a : α, (1 / D) ^ (l a) ≤ 1 := by
    calc ∑ a : α, (1 / D) ^ (l a)
      _ ≤ ∑ a : α, P.pmf a := Finset.sum_le_sum (fun a _ => hkraft_term a)
      _ = 1 := P.sum_one
  obtain ⟨c, hc_inj, hc_pf, hc_len⟩ := exists_prefixFree_code_of_kraft (β := β) l hkraft
  refine ⟨c, hc_inj, hc_pf, ?_⟩
  have hne : (Finset.univ : Finset α).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 := P.sum_one
    rw [hemp, Finset.sum_empty] at h0
    norm_num at h0
  have hlt_term : ∀ a ∈ (Finset.univ : Finset α),
      P.pmf a * ((c a).length : ℝ) < negPLogP (P.pmf a) / log2 D + P.pmf a := by
    intro a _
    rw [hc_len a]
    have harg_nonneg : 0 ≤ -Real.log (P.pmf a) / Real.log D := by
      have hlogp : Real.log (P.pmf a) ≤ 0 := Real.log_nonpos (le_of_lt (hpos a)) (pmf_le_one P a)
      exact div_nonneg (by linarith) (le_of_lt hlogDpos)
    have hlt : (l a : ℝ) < -Real.log (P.pmf a) / Real.log D + 1 :=
      Nat.ceil_lt_add_one harg_nonneg
    have hmul := mul_lt_mul_of_pos_left hlt (hpos a)
    have hrhs : P.pmf a * (-Real.log (P.pmf a) / Real.log D + 1) =
        negPLogP (P.pmf a) / log2 D + P.pmf a := by
      unfold negPLogP log2
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr (hpos a)))]
      have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
      have hlogDne : Real.log D ≠ 0 := ne_of_gt hlogDpos
      field_simp [hlog2ne, hlogDne]
    rwa [hrhs] at hmul
  have hsum_lt := Finset.sum_lt_sum_of_nonempty hne hlt_term
  rw [Finset.sum_add_distrib, ← Finset.sum_div, P.sum_one] at hsum_lt
  exact hsum_lt

open Classical in
/-- **Shannon–Fano Code Achievability on Positive Support** (Cover & Thomas, Theorem 5.4.1):
    for any distribution `P : ProbDist α` (possibly with zero-probability atoms) and `2 ≤ |β|`,
    there exists an injective prefix-free code on the support `{a : α // 0 < P.pmf a}` with
    expected length strictly below `H(P) / log₂ |β| + 1`. -/
theorem shannon_fano_achievability_support {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) (P : ProbDist α) :
    ∃ c : {a : α // 0 < P.pmf a} → List β,
      Function.Injective c ∧
      InformationTheory.IsPrefixFree ((Finset.univ.image c : Finset (List β)) : Set (List β)) ∧
      ∑ a : {a : α // 0 < P.pmf a}, P.pmf a.1 * ((c a).length : ℝ) <
        shannonEntropy P / log2 (Fintype.card β : ℝ) + 1 := by
  have hsum_supp : ∀ g : α → ℝ,
      ∑ a : {a : α // 0 < P.pmf a}, g a.1 =
        ∑ a ∈ Finset.univ.filter (fun a : α => 0 < P.pmf a), g a := by
    intro g
    refine Finset.sum_bij (fun a _ => a.1) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro a _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, a.2⟩
    · intro a _ b _ h; exact Subtype.ext h
    · intro b hb; exact ⟨⟨b, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, rfl⟩
  let Psupp : ProbDist {a : α // 0 < P.pmf a} :=
    { pmf := fun a => P.pmf a.1
      nonneg := fun a => P.nonneg a.1
      sum_one := by
        rw [hsum_supp P.pmf]
        have h2 : ∑ a ∈ Finset.univ.filter (fun a : α => 0 < P.pmf a), P.pmf a =
            ∑ a : α, P.pmf a := by
          refine Finset.sum_subset (Finset.filter_subset _ _) fun a _ hnot => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
          exact le_antisymm hnot (P.nonneg a)
        rw [h2, P.sum_one] }
  have hent : shannonEntropy Psupp = shannonEntropy P := by
    unfold shannonEntropy
    change ∑ a : {a : α // 0 < P.pmf a}, negPLogP (P.pmf a.1) = _
    rw [hsum_supp (fun a => negPLogP (P.pmf a))]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun a _ hnot => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
    have h0 : P.pmf a = 0 := le_antisymm hnot (P.nonneg a)
    simp [h0, negPLogP]
  obtain ⟨c, hcinj, hcpf, hclt⟩ := shannon_fano_achievability hβ Psupp (fun a => a.2)
  rw [hent] at hclt
  exact ⟨c, hcinj, hcpf, hclt⟩

/-- **Shannon–Fano Code Achievability on the Full Alphabet** (Cover & Thomas, Theorem 5.4.1):
    for ANY distribution `P : ProbDist α` (including distributions with zero-mass atoms, such as
    point masses) and code alphabet `β` with `2 ≤ |β|`, there exists an injective prefix-free code
    `c : α → List β` on the entire alphabet `α` with
    `∑ a, P(a) · |c(a)| ≤ H(P) / log₂ |β| + 1`. -/
theorem shannon_fano_achievability_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) (P : ProbDist α) :
    ∃ c : α → List β,
      Function.Injective c ∧
      InformationTheory.IsPrefixFree ((Finset.univ.image c : Finset (List β)) : Set (List β)) ∧
      ∑ a : α, P.pmf a * ((c a).length : ℝ) ≤
        shannonEntropy P / log2 (Fintype.card β : ℝ) + 1 := by
  classical
  have : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  set D : ℝ := (Fintype.card β : ℝ)
  have hDge2 : (2 : ℝ) ≤ D := by dsimp only [D]; exact_mod_cast hβ
  have hDpos : 0 < D := by linarith
  have hDgt1 : 1 < D := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogDpos : 0 < Real.log D := Real.log_pos hDgt1
  have hlog2Dpos : 0 < log2 D := div_pos hlogDpos hlog2pos
  set S : Finset α := Finset.univ.filter (fun a : α => 0 < P.pmf a)
  set Z : Finset α := Finset.univ.filter (fun a : α => ¬ (0 < P.pmf a))
  have hS_sum : ∑ a ∈ S, P.pmf a = 1 := by
    have hsub : ∑ a ∈ S, P.pmf a = ∑ a : α, P.pmf a := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun a _ hnot => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
      exact le_antisymm hnot (P.nonneg a)
    rw [hsub, P.sum_one]
  have hS_ent : ∑ a ∈ S, negPLogP (P.pmf a) = shannonEntropy P := by
    unfold shannonEntropy
    refine Finset.sum_subset (Finset.filter_subset _ _) fun a _ hnot => ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
    have h0 : P.pmf a = 0 := le_antisymm hnot (P.nonneg a)
    simp [h0, negPLogP]
  have hS_ne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hS_sum
    norm_num at hS_sum
  -- If all atoms are positive, use the strict theorem directly
  by_cases hZempty : Z = ∅
  · have hall : ∀ a : α, 0 < P.pmf a := by
      intro a
      by_contra hnot
      have hmem : a ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hnot⟩
      rw [hZempty] at hmem
      exact Finset.notMem_empty a hmem
    obtain ⟨c, hcinj, hcpf, hclt⟩ := shannon_fano_achievability hβ P hall
    exact ⟨c, hcinj, hcpf, le_of_lt hclt⟩
  -- Otherwise there are zero-mass atoms; build lengths `lS` on `S` with strictly positive Kraft slack
  let l₀ : α → ℕ := fun a => Nat.ceil (-Real.log (P.pmf a) / Real.log D)
  have hl₀_le : ∀ a ∈ S, (1 / D) ^ (l₀ a) ≤ P.pmf a := by
    intro a ha
    have hapos : 0 < P.pmf a := (Finset.mem_filter.mp ha).2
    have hceil : -Real.log (P.pmf a) / Real.log D ≤ (l₀ a : ℝ) := Nat.le_ceil _
    have hmul : -Real.log (P.pmf a) ≤ (l₀ a : ℝ) * Real.log D :=
      (div_le_iff₀ hlogDpos).mp hceil
    have hlog_le : Real.log ((1 / D) ^ (l₀ a)) ≤ Real.log (P.pmf a) := by
      rw [Real.log_pow, one_div, Real.log_inv]
      linarith
    exact (Real.log_le_log_iff (by positivity) hapos).mp hlog_le
  have hK₀_le : ∑ a ∈ S, (1 / D) ^ (l₀ a) ≤ 1 := by
    calc ∑ a ∈ S, (1 / D) ^ (l₀ a)
      _ ≤ ∑ a ∈ S, P.pmf a := Finset.sum_le_sum hl₀_le
      _ = 1 := hS_sum
  have hexists_lS : ∃ lS : α → ℕ,
      ∑ a ∈ S, (1 / D) ^ (lS a) < 1 ∧
      ∑ a ∈ S, P.pmf a * (lS a : ℝ) ≤ shannonEntropy P / log2 D + 1 := by
    rcases lt_or_eq_of_le hK₀_le with hK₀_lt | hK₀_eq
    · refine ⟨l₀, hK₀_lt, ?_⟩
      have hterm : ∀ a ∈ S, P.pmf a * (l₀ a : ℝ) ≤ negPLogP (P.pmf a) / log2 D + P.pmf a := by
        intro a ha
        have hapos : 0 < P.pmf a := (Finset.mem_filter.mp ha).2
        have harg_nonneg : 0 ≤ -Real.log (P.pmf a) / Real.log D := by
          have hlogp : Real.log (P.pmf a) ≤ 0 :=
            Real.log_nonpos (le_of_lt hapos) (pmf_le_one P a)
          exact div_nonneg (by linarith) (le_of_lt hlogDpos)
        have hle : (l₀ a : ℝ) ≤ -Real.log (P.pmf a) / Real.log D + 1 :=
          le_of_lt (Nat.ceil_lt_add_one harg_nonneg)
        have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hapos)
        have hrhs : P.pmf a * (-Real.log (P.pmf a) / Real.log D + 1) =
            negPLogP (P.pmf a) / log2 D + P.pmf a := by
          unfold negPLogP log2
          rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hapos))]
          have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
          have hlogDne : Real.log D ≠ 0 := ne_of_gt hlogDpos
          field_simp [hlog2ne, hlogDne]
        rwa [hrhs] at hmul
      calc ∑ a ∈ S, P.pmf a * (l₀ a : ℝ)
        _ ≤ ∑ a ∈ S, (negPLogP (P.pmf a) / log2 D + P.pmf a) := Finset.sum_le_sum hterm
        _ = (∑ a ∈ S, negPLogP (P.pmf a)) / log2 D + ∑ a ∈ S, P.pmf a := by
            rw [Finset.sum_add_distrib, ← Finset.sum_div]
        _ = shannonEntropy P / log2 D + 1 := by rw [hS_ent, hS_sum]
    · -- Dyadic saturation: `(1 / D)^{l₀ a} = P(a)` for every `a ∈ S`, so zero rounding overhead!
      have heq_all : ∀ a ∈ S, (1 / D) ^ (l₀ a) = P.pmf a := by
        have hsub0 : ∑ a ∈ S, (P.pmf a - (1 / D) ^ (l₀ a)) = 0 := by
          rw [Finset.sum_sub_distrib, hS_sum, hK₀_eq, sub_self]
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => sub_nonneg.mpr (hl₀_le a ha))).mp hsub0
        intro a ha
        linarith [hzero a ha]
      have hlen_exact : ∀ a ∈ S, P.pmf a * (l₀ a : ℝ) = negPLogP (P.pmf a) / log2 D := by
        intro a ha
        have hapos : 0 < P.pmf a := (Finset.mem_filter.mp ha).2
        have hlog_eq : Real.log ((1 / D) ^ (l₀ a)) = Real.log (P.pmf a) :=
          congrArg Real.log (heq_all a ha)
        rw [Real.log_pow, one_div, Real.log_inv] at hlog_eq
        have hlval : (l₀ a : ℝ) = -Real.log (P.pmf a) / Real.log D := by
          have hlogDne : Real.log D ≠ 0 := ne_of_gt hlogDpos
          field_simp [hlogDne]
          linarith
        rw [hlval]
        unfold negPLogP log2
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hapos))]
        have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
        have hlogDne : Real.log D ≠ 0 := ne_of_gt hlogDpos
        field_simp [hlog2ne, hlogDne]
      -- Bump a single atom `a₀ ∈ S` by 1 to create strictly positive Kraft slack
      obtain ⟨a₀, ha₀⟩ := hS_ne
      have ha₀_pos : 0 < P.pmf a₀ := (Finset.mem_filter.mp ha₀).2
      let lS : α → ℕ := fun a => if a = a₀ then l₀ a + 1 else l₀ a
      refine ⟨lS, ?_, ?_⟩
      · have hsplit : ∑ a ∈ S, (1 / D) ^ (lS a) =
            (∑ a ∈ S, (1 / D) ^ (l₀ a)) - (1 / D) ^ (l₀ a₀) + (1 / D) ^ (l₀ a₀ + 1) := by
          rw [← Finset.add_sum_erase S (fun a => (1 / D) ^ (lS a)) ha₀,
            ← Finset.add_sum_erase S (fun a => (1 / D) ^ (l₀ a)) ha₀]
          have hcong : ∑ a ∈ S.erase a₀, (1 / D) ^ (lS a) = ∑ a ∈ S.erase a₀, (1 / D) ^ (l₀ a) :=
            Finset.sum_congr rfl fun a ha => by
              simp [lS, (Finset.mem_erase.mp ha).1]
          rw [hcong]
          simp only [lS, ↓reduceIte]
          ring
        rw [hsplit, hK₀_eq, pow_succ, heq_all a₀ ha₀]
        have h1dlt1 : 1 / D < 1 := (div_lt_one hDpos).mpr hDgt1
        nlinarith
      · have hsplit : ∑ a ∈ S, P.pmf a * (lS a : ℝ) =
            (∑ a ∈ S, P.pmf a * (l₀ a : ℝ)) + P.pmf a₀ := by
          rw [← Finset.add_sum_erase S (fun a => P.pmf a * (lS a : ℝ)) ha₀,
            ← Finset.add_sum_erase S (fun a => P.pmf a * (l₀ a : ℝ)) ha₀]
          have hcong : ∑ a ∈ S.erase a₀, P.pmf a * (lS a : ℝ) =
              ∑ a ∈ S.erase a₀, P.pmf a * (l₀ a : ℝ) :=
            Finset.sum_congr rfl fun a ha => by
              simp [lS, (Finset.mem_erase.mp ha).1]
          rw [hcong]
          simp only [lS, ↓reduceIte, Nat.cast_add, Nat.cast_one]
          ring
        rw [hsplit, Finset.sum_congr rfl hlen_exact, ← Finset.sum_div, hS_ent]
        linarith [pmf_le_one P a₀]
  obtain ⟨lS, hKS_lt, hlenS_le⟩ := hexists_lS
  -- Allocate long codewords for the zero-mass atoms using the strictly positive slack `1 - ∑_{S} D^{-lS}`
  set slack : ℝ := 1 - ∑ a ∈ S, (1 / D) ^ (lS a)
  have hslack_pos : 0 < slack := by linarith
  have hZcard_pos : (0 : ℝ) < (Z.card : ℝ) := by
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hZempty))
  have htend : Filter.Tendsto (fun k : ℕ => (1 / D) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hDpos).mpr hDgt1)
  have hev := (tendsto_order.mp htend).2 (slack / (Z.card : ℝ)) (div_pos hslack_pos hZcard_pos)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hev
  have hZkraft : (Z.card : ℝ) * (1 / D) ^ L₀ ≤ slack := by
    have hlt := hL₀ L₀ le_rfl
    exact le_of_lt ((lt_div_iff₀' hZcard_pos).mp hlt)
  let lFull : α → ℕ := fun a => if a ∈ S then lS a else L₀
  have hpart : ∀ g : α → ℝ, ∑ a : α, g a = (∑ a ∈ S, g a) + ∑ a ∈ Z, g a := by
    intro g
    have hdisj : Disjoint S Z := by
      rw [Finset.disjoint_left]
      intro a haS haZ
      exact (Finset.mem_filter.mp haZ).2 (Finset.mem_filter.mp haS).2
    have hunion : S ∪ Z = Finset.univ := by
      ext a
      simp only [S, Z, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (em _)
    rw [← Finset.sum_union hdisj, hunion]
  have hkraft_full : ∑ a : α, (1 / D) ^ (lFull a) ≤ 1 := by
    rw [hpart]
    have h1 : ∑ a ∈ S, (1 / D) ^ (lFull a) = ∑ a ∈ S, (1 / D) ^ (lS a) :=
      Finset.sum_congr rfl fun a ha => by simp [lFull, ha]
    have h2 : ∑ a ∈ Z, (1 / D) ^ (lFull a) = (Z.card : ℝ) * (1 / D) ^ L₀ := by
      have hc : ∑ a ∈ Z, (1 / D) ^ (lFull a) = ∑ _a ∈ Z, (1 / D) ^ L₀ :=
        Finset.sum_congr rfl fun a ha => by
          have hnotS : a ∉ S := by
            simp only [S, Z, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            exact ha
          simp [lFull, hnotS]
      rw [hc, Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2]
    linarith
  obtain ⟨c, hcinj, hcpf, hclen⟩ := exists_prefixFree_code_of_kraft (β := β) lFull hkraft_full
  refine ⟨c, hcinj, hcpf, ?_⟩
  rw [hpart]
  have h1 : ∑ a ∈ S, P.pmf a * ((c a).length : ℝ) = ∑ a ∈ S, P.pmf a * (lS a : ℝ) :=
    Finset.sum_congr rfl fun a ha => by rw [hclen a]; simp [lFull, ha]
  have h2 : ∑ a ∈ Z, P.pmf a * ((c a).length : ℝ) = 0 :=
    Finset.sum_eq_zero fun a ha => by
      have hnotpos : ¬ (0 < P.pmf a) := (Finset.mem_filter.mp ha).2
      have h0 : P.pmf a = 0 := le_antisymm (not_lt.mp hnotpos) (P.nonneg a)
      simp [h0]
  rw [h1, h2, add_zero]
  exact hlenS_le

end KraftAndShannonFano

end InfoTheory.Bridge
