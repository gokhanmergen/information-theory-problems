import InfoTheory.Problems.UniversalLossyRedundancy
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.UniversalLossyRedundancy`

The statement (fixed 2026-11-27) asks whether the minimax redundancy
`R_n(m, D, δ) = minimaxLossyRedundancy m D δ n` of `d`-semifaithful codes on `m`-ary
memoryless sources under Hamming distortion, over the interior class
`interiorClass m D δ = {P : ∀ x, P(x) ≥ D/(m-1) + δ}`, satisfies
`(n / log₂ n) · R_n` converges to a real limit (conjectured `(m + 1)/2`).

## Certified (about exactly these objects)
* `uniform_mem_interiorClass`, `interiorClass_nonempty` : for `m ≥ 2` and
  `δ < 1/m - D/(m-1)` the class contains the uniform source, so the supremum is over a
  nonempty class (an empty class would make the minimax set all of `ℝ` and `sInf` junk).
* `interiorClass_regular` : every `P` in the class satisfies `D < (m-1) · P(x)` for all `x`,
  i.e. lies strictly inside the regular region where the `O(log n / n)` theory applies
  (in particular it stays away from the zero-rate boundary `D = D_max(P)`).
* `bern14_not_mem_interiorClass` : the old counterexample source `Bern(1/4)` at `D = 1/4` is
  not in any class `interiorClass 2 (1/4) δ`, `δ > 0`.
* `losslessCode_mem`, `minimaxLossyRedundancyOn_le`, `neg_rateDistortion_le_minimaxOn` :
  the defining set is nonempty (fixed-length lossless code with `⌈n log₂ m⌉`-bit codewords)
  and bounded below by `-R(P, D)` for any `P` in the class; so `R_n` is a genuine finite
  infimum with `-R(P, D) ≤ R_n ≤ ⌈n log₂ m⌉ / n`.
* `minimaxLossyRedundancyOn_mono`, `minimaxLossyRedundancy_le_fullSimplex` : `R_n` is monotone in
  the class; the interior-class redundancy is at most the full-simplex one.
* `fullSimplex_version_false` — **record of the catalog error fixed on 2026-11-27**: the old
  frozen proposition `FullSimplexStatement` (supremum over the whole simplex, constant `m/2`)
  is false. Evaluating any `d`-semifaithful code on the zero-rate boundary source
  `P₀ = Bern(1/4)` at `m = 2, D = 1/4` (`R(P₀, 1/4) = 0`) yields redundancy
  `≥ 1 / (54432 √n) ≫ (log₂ n) / n` (fourth-moment anticoncentration + uniform Chernoff cap +
  Kraft split).  `fullSimplexMinimax_nonneg` and `fullSimplexMinimax_le` show that old object
  was itself non-junk.

## Not certified
* Nonnegativity of `R_n` over the interior class (a converse `𝔼 ℓ ≥ n R(P, D)`), the
  `Θ(log n / n)` order on interior classes (Yu–Speed 1993; Zhang–Yang–Wei 1997; Yang–Zhang),
  and any bound on the constant (`3/2` lower bound for `m = 2` in the attempt file); these need
  type-covering lemmas that are not in `Bridge`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.UniversalLossyRedundancy

section InteriorClassCertificate

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.UniversalLossyRedundancy

theorem hammingDist_dist (m : ℕ) (x y : Fin m) :
    (hammingDist m).dist x y = if x = y then 0 else 1 := rfl

/-- `R(D) = 0` for a point-mass source and `D ≥ 0` (reproduce the atom). -/
theorem rateDistortion_dirac {m : ℕ} (a : Fin m) {D : ℝ} (hD : 0 ≤ D) :
    rateDistortion (diracDist a) (hammingDist m) D = 0 :=
  rateDistortion_eq_zero_of_const _ _ ⟨a, by
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun x _ => ?_)) hD
    by_cases h : x = a <;> simp [diracDist, hammingDist_dist, h]⟩

theorem expectedRate_nonneg {m : ℕ} (P : ProbDist (Fin m)) (n M : ℕ)
    (enc : (Fin n → Fin m) → Fin M) (len : Fin M → ℕ) : 0 ≤ expectedRate P n M enc len :=
  div_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg
    (Finset.prod_nonneg fun _ _ => P.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- The set whose infimum is `minimaxLossyRedundancyOn m d D S n`. -/
def minimaxSet (m : ℕ) (d : Distortion (Fin m) (Fin m)) (D : ℝ) (S : Set (ProbDist (Fin m)))
    (n : ℕ) : Set ℝ :=
  { r : ℝ | ∃ (M : ℕ) (enc : (Fin n → Fin m) → Fin M)
    (dec : Fin M → (Fin n → Fin m)) (len : Fin M → ℕ),
    IsDSemifaithfulCode m d D n M enc dec len ∧
    ∀ P ∈ S, expectedRate P n M enc len - rateDistortion P d D ≤ r }

theorem minimaxLossyRedundancyOn_eq (m : ℕ) (d : Distortion (Fin m) (Fin m)) (D : ℝ)
    (S : Set (ProbDist (Fin m))) (n : ℕ) :
    minimaxLossyRedundancyOn m d D S n = sInf (minimaxSet m d D S n) := rfl

/-- Every element of the minimax set is `≥ -R(P, D)` for each `P` in the class. -/
theorem minimaxSet_lower {m : ℕ} {d : Distortion (Fin m) (Fin m)} {D : ℝ}
    {S : Set (ProbDist (Fin m))} {n : ℕ} {P : ProbDist (Fin m)} (hP : P ∈ S) :
    ∀ r ∈ minimaxSet m d D S n, -rateDistortion P d D ≤ r := by
  rintro r ⟨M, enc, dec, len, -, hr⟩
  linarith [hr P hP, expectedRate_nonneg P n M enc len]

/-- The fixed-length lossless code (all `mⁿ` sequences, each with a `⌈n log₂ m⌉`-bit codeword)
    is `d`-semifaithful and has redundancy at most `⌈n log₂ m⌉ / n` against every source, for
    every class `S`. -/
theorem losslessCode_mem {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) {n : ℕ} (hn : 0 < n)
    (S : Set (ProbDist (Fin m))) :
    (Nat.ceil ((n : ℝ) * log2 (m : ℝ)) : ℝ) / (n : ℝ) ∈ minimaxSet m (hammingDist m) D S n := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set L := Nat.ceil ((n : ℝ) * log2 (m : ℝ)) with hL
  let e := Fintype.equivFin (Fin n → Fin m)
  have hlog : (2 : ℝ) ^ (log2 (m : ℝ)) = m := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    unfold log2
    rw [show Real.log 2 * (Real.log (m : ℝ) / Real.log 2) = Real.log (m : ℝ) by
      field_simp [(Real.log_pos one_lt_two).ne'], Real.exp_log (by exact_mod_cast hm)]
  have hpow : (m : ℝ) ^ n ≤ (2 : ℝ) ^ (L : ℝ) := by
    calc (m : ℝ) ^ n = ((2 : ℝ) ^ (log2 (m : ℝ))) ^ n := by rw [hlog]
      _ = (2 : ℝ) ^ ((n : ℝ) * log2 (m : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      _ ≤ (2 : ℝ) ^ (L : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  refine ⟨_, e, e.symm, fun _ => L, ⟨hn, Fintype.card_pos, ?_, fun x => ?_⟩, fun P _ => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcard : ((Fintype.card (Fin n → Fin m) : ℕ) : ℝ) = (m : ℝ) ^ n := by
      simp
    rw [hcard]
    calc (m : ℝ) ^ n * (2 : ℝ) ^ (-(L : ℝ)) ≤ (2 : ℝ) ^ (L : ℝ) * (2 : ℝ) ^ (-(L : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
  · simp [e, hammingDist_dist, hD]
  · have hrate : expectedRate P n _ e (fun _ => L) = (L : ℝ) / n := by
      show (∑ x : Fin n → Fin m, (iidDist P n).pmf x * (L : ℝ)) / n = (L : ℝ) / n
      rw [← Finset.sum_mul, (iidDist P n).sum_one, one_mul]
    rw [hrate]
    linarith [rateDistortion_nonneg P (hammingDist m) D]

/-- `R_n(S) ≤ ⌈n log₂ m⌉ / n` for every nonempty class `S`. -/
theorem minimaxLossyRedundancyOn_le {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) {n : ℕ}
    (hn : 0 < n) {S : Set (ProbDist (Fin m))} (hS : S.Nonempty) :
    minimaxLossyRedundancyOn m (hammingDist m) D S n ≤
      (Nat.ceil ((n : ℝ) * log2 (m : ℝ)) : ℝ) / (n : ℝ) := by
  obtain ⟨P, hP⟩ := hS
  exact csInf_le ⟨_, minimaxSet_lower hP⟩ (losslessCode_mem hm hD hn S)

/-- `-R(P, D) ≤ R_n(S)` for every `P ∈ S` (the infimum is over a nonempty set). -/
theorem neg_rateDistortion_le_minimaxOn {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) {n : ℕ}
    (hn : 0 < n) {S : Set (ProbDist (Fin m))} {P : ProbDist (Fin m)} (hP : P ∈ S) :
    -rateDistortion P (hammingDist m) D ≤ minimaxLossyRedundancyOn m (hammingDist m) D S n :=
  le_csInf ⟨_, losslessCode_mem hm hD hn S⟩ (minimaxSet_lower hP)

/-- Monotonicity in the source class. -/
theorem minimaxLossyRedundancyOn_mono {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) {n : ℕ}
    (hn : 0 < n) {S T : Set (ProbDist (Fin m))} (hS : S.Nonempty) (hST : S ⊆ T) :
    minimaxLossyRedundancyOn m (hammingDist m) D S n ≤
      minimaxLossyRedundancyOn m (hammingDist m) D T n := by
  obtain ⟨P, hP⟩ := hS
  refine csInf_le_csInf ⟨_, minimaxSet_lower hP⟩ ⟨_, losslessCode_mem hm hD hn T⟩ ?_
  rintro r ⟨M, enc, dec, len, hc, hr⟩
  exact ⟨M, enc, dec, len, hc, fun Q hQ => hr Q (hST hQ)⟩

/-- For `m ≥ 2` and `δ ≤ 1/m - D/(m-1)` the uniform source lies in the interior class. -/
theorem uniform_mem_interiorClass {m : ℕ} [Nonempty (Fin m)] {D δ : ℝ}
    (hδ : δ ≤ 1 / (m : ℝ) - D / ((m : ℝ) - 1)) :
    (ProbDist.uniform : ProbDist (Fin m)) ∈ interiorClass m D δ := by
  intro x
  simp only [ProbDist.uniform, Fintype.card_fin]
  linarith

theorem interiorClass_nonempty {m : ℕ} (hm : 2 ≤ m) {D δ : ℝ}
    (hδ : δ ≤ 1 / (m : ℝ) - D / ((m : ℝ) - 1)) : (interiorClass m D δ).Nonempty :=
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  ⟨_, uniform_mem_interiorClass hδ⟩

/-- Every source in the class is strictly regular: `D < (m - 1) · P(x)` for all letters. -/
theorem interiorClass_regular {m : ℕ} (hm : 2 ≤ m) {D δ : ℝ} (hδ : 0 < δ)
    {P : ProbDist (Fin m)} (hP : P ∈ interiorClass m D δ) (x : Fin m) :
    D < ((m : ℝ) - 1) * P.pmf x := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h := mul_le_mul_of_nonneg_left (hP x) hm1.le
  rw [mul_add, mul_div_cancel₀ _ hm1.ne'] at h
  nlinarith

/-- The interior-class redundancy is a genuine finite infimum:
    `-R(uniform, D) ≤ R_n(m, D, δ) ≤ ⌈n log₂ m⌉ / n`. -/
theorem minimaxLossyRedundancy_bounds {m : ℕ} [Nonempty (Fin m)] (hm : 2 ≤ m) {D δ : ℝ}
    (hD : 0 ≤ D) (hδ : δ ≤ 1 / (m : ℝ) - D / ((m : ℝ) - 1)) {n : ℕ} (hn : 0 < n) :
    -rateDistortion (ProbDist.uniform : ProbDist (Fin m)) (hammingDist m) D ≤
        minimaxLossyRedundancy m D δ n ∧
      minimaxLossyRedundancy m D δ n ≤ (Nat.ceil ((n : ℝ) * log2 (m : ℝ)) : ℝ) / (n : ℝ) :=
  ⟨neg_rateDistortion_le_minimaxOn (by omega) hD hn (uniform_mem_interiorClass hδ),
    minimaxLossyRedundancyOn_le (by omega) hD hn (interiorClass_nonempty hm hδ)⟩

/-- The interior-class redundancy is at most the full-simplex redundancy. -/
theorem minimaxLossyRedundancy_le_fullSimplex {m : ℕ} (hm : 2 ≤ m) {D δ : ℝ} (hD : 0 ≤ D)
    (hδ : δ ≤ 1 / (m : ℝ) - D / ((m : ℝ) - 1)) {n : ℕ} (hn : 0 < n) :
    minimaxLossyRedundancy m D δ n ≤
      minimaxLossyRedundancyOn m (hammingDist m) D Set.univ n :=
  minimaxLossyRedundancyOn_mono (by omega) hD hn (interiorClass_nonempty hm hδ)
    (Set.subset_univ _)

end InteriorClassCertificate

/-! ## The old (pre-2026-11-27) full-simplex proposition -/

section FullSimplex

open InfoTheory InfoTheory.Problems.UniversalLossyRedundancy

/-- The old frozen object: minimax redundancy over the *entire* simplex. -/
noncomputable def fullSimplexMinimax (m : ℕ) (D : ℝ) (n : ℕ) : ℝ :=
  minimaxLossyRedundancyOn m (hammingDist m) D Set.univ n

/-- The old frozen `Statement` (before the 2026-11-27 statement fix), spelled out:
    supremum over the whole simplex and conjectured constant `m/2`. -/
def FullSimplexStatement : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (D : ℝ), 0 < D → D < 1 - 1 / (m : ℝ) →
    ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ((n : ℝ) / log2 (n : ℝ)) * fullSimplexMinimax m D n ≤ (m : ℝ) / 2 + ε

/-- The old object was non-junk: `0 ≤ fullSimplexMinimax` (test on a point mass). -/
theorem fullSimplexMinimax_nonneg {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) (n : ℕ) :
    0 ≤ fullSimplexMinimax m D n := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨M, enc, dec, len, -, hP⟩
  have := hP (InfoTheory.Known.Operational.diracDist ⟨0, hm⟩) (Set.mem_univ _)
  rw [rateDistortion_dirac _ hD, sub_zero] at this
  exact le_trans (expectedRate_nonneg _ _ _ _ _) this

theorem fullSimplexMinimax_le {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : 0 ≤ D) {n : ℕ} (hn : 0 < n) :
    fullSimplexMinimax m D n ≤ (Nat.ceil ((n : ℝ) * log2 (m : ℝ)) : ℝ) / (n : ℝ) :=
  minimaxLossyRedundancyOn_le hm hD hn
    ⟨InfoTheory.Known.Operational.diracDist (⟨0, hm⟩ : Fin m), Set.mem_univ _⟩

end FullSimplex

section BoundaryKink

open InfoTheory InfoTheory.Problems.UniversalLossyRedundancy

/-! ### Step 1: Nonnegativity of mutual information and rate-distortion -/

private lemma log_two_pos : (0 : ℝ) < Real.log 2 :=
  Real.log_pos (by norm_num)

private lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

private lemma mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (Q : ProbDist (α × β)) : 0 ≤ mutualInfo Q := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  -- Rewrite `- (Real.log 2) * mutualInfo Q` as `∑ ab, if Q.pmf ab ≤ 0 then 0 else Q.pmf ab * log (p_a q_b / Q ab)`
  have h_eq :
      ∑ ab : α × β,
        (if Q.pmf ab ≤ 0 then (0 : ℝ)
         else Q.pmf ab * Real.log (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 / Q.pmf ab))
      = -(Real.log 2) * mutualInfo Q := by
    have hfst : ∀ a : α, Q.fst.pmf a = ∑ b : β, Q.pmf (a, b) := fun _ => rfl
    have hsnd : ∀ b : β, Q.snd.pmf b = ∑ a : α, Q.pmf (a, b) := fun _ => rfl
    have hfst_ge : ∀ ab : α × β, Q.pmf ab ≤ Q.fst.pmf ab.1 := fun ab =>
      Finset.single_le_sum (fun b _ => Q.nonneg (ab.1, b)) (Finset.mem_univ ab.2)
    have hsnd_ge : ∀ ab : α × β, Q.pmf ab ≤ Q.snd.pmf ab.2 := fun ab =>
      Finset.single_le_sum (fun a _ => Q.nonneg (a, ab.2)) (Finset.mem_univ ab.1)
    have h1 :
        ∑ ab : α × β,
          (if Q.pmf ab ≤ 0 then (0 : ℝ)
           else Q.pmf ab * Real.log (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 / Q.pmf ab))
        = (∑ ab : α × β, if Q.pmf ab ≤ 0 then (0 : ℝ) else Q.pmf ab * Real.log (Q.fst.pmf ab.1)) +
          (∑ ab : α × β, if Q.pmf ab ≤ 0 then (0 : ℝ) else Q.pmf ab * Real.log (Q.snd.pmf ab.2)) -
          (∑ ab : α × β, if Q.pmf ab ≤ 0 then (0 : ℝ) else Q.pmf ab * Real.log (Q.pmf ab)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun ab _ => ?_)
      split_ifs with hq
      · ring
      · push Not at hq
        have ha : 0 < Q.fst.pmf ab.1 := lt_of_lt_of_le hq (hfst_ge ab)
        have hb : 0 < Q.snd.pmf ab.2 := lt_of_lt_of_le hq (hsnd_ge ab)
        rw [Real.log_div (mul_pos ha hb).ne' hq.ne', Real.log_mul ha.ne' hb.ne']
        ring
    have hA :
        (∑ ab : α × β, if Q.pmf ab ≤ 0 then (0 : ℝ) else Q.pmf ab * Real.log (Q.fst.pmf ab.1))
        = -(Real.log 2) * shannonEntropy Q.fst := by
      rw [Fintype.sum_prod_type, shannonEntropy, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [negPLogP, log2]
      by_cases ha : Q.fst.pmf a ≤ 0
      · have hzero : ∀ b : β, Q.pmf (a, b) ≤ 0 := fun b => le_trans (hfst_ge (a, b)) ha
        simp [ha, hzero]
      · simp only [ha, ↓reduceIte]
        have hterm : ∀ b : β,
            (if Q.pmf (a, b) ≤ 0 then (0 : ℝ) else Q.pmf (a, b) * Real.log (Q.fst.pmf a))
            = Q.pmf (a, b) * Real.log (Q.fst.pmf a) := by
          intro b
          split_ifs with hq
          · have hq0 : Q.pmf (a, b) = 0 := le_antisymm hq (Q.nonneg _)
            simp [hq0]
          · rfl
        simp_rw [hterm, ← Finset.sum_mul]
        change Q.fst.pmf a * Real.log (Q.fst.pmf a) = _
        field_simp [hlog2.ne']
    have hB :
        (∑ ab : α × β, if Q.pmf ab ≤ 0 then (0 : ℝ) else Q.pmf ab * Real.log (Q.snd.pmf ab.2))
        = -(Real.log 2) * shannonEntropy Q.snd := by
      rw [Fintype.sum_prod_type_right, shannonEntropy, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [negPLogP, log2]
      by_cases hb : Q.snd.pmf b ≤ 0
      · have hzero : ∀ a : α, Q.pmf (a, b) ≤ 0 := fun a => le_trans (hsnd_ge (a, b)) hb
        simp [hb, hzero]
      · simp only [hb, ↓reduceIte]
        have hterm : ∀ a : α,
            (if Q.pmf (a, b) ≤ 0 then (0 : ℝ) else Q.pmf (a, b) * Real.log (Q.snd.pmf b))
            = Q.pmf (a, b) * Real.log (Q.snd.pmf b) := by
          intro a
          split_ifs with hq
          · have hq0 : Q.pmf (a, b) = 0 := le_antisymm hq (Q.nonneg _)
            simp [hq0]
          · rfl
        simp_rw [hterm, ← Finset.sum_mul]
        change Q.snd.pmf b * Real.log (Q.snd.pmf b) = _
        field_simp [hlog2.ne']
    have hC :
        (∑ ab : α × β, if Q.pmf ab ≤ 0 then (0 : ℝ) else Q.pmf ab * Real.log (Q.pmf ab))
        = -(Real.log 2) * shannonEntropy Q := by
      rw [shannonEntropy, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ab _ => ?_)
      simp only [negPLogP, log2]
      split_ifs with hq
      · simp
      · field_simp [hlog2.ne']
    rw [h1, hA, hB, hC, mutualInfo]
    ring
  have hle :
      ∑ ab : α × β,
        (if Q.pmf ab ≤ 0 then (0 : ℝ)
         else Q.pmf ab * Real.log (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 / Q.pmf ab))
      ≤ 0 := by
    have hpt : ∀ ab : α × β,
        (if Q.pmf ab ≤ 0 then (0 : ℝ)
         else Q.pmf ab * Real.log (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 / Q.pmf ab))
        ≤ Q.fst.pmf ab.1 * Q.snd.pmf ab.2 - Q.pmf ab := by
      intro ab
      split_ifs with hq
      · have hq0 : Q.pmf ab = 0 := le_antisymm hq (Q.nonneg ab)
        rw [hq0, sub_zero]
        exact mul_nonneg (Q.fst.nonneg ab.1) (Q.snd.nonneg ab.2)
      · push Not at hq
        have ha : 0 < Q.fst.pmf ab.1 :=
          lt_of_lt_of_le hq (Finset.single_le_sum (fun b _ => Q.nonneg (ab.1, b)) (Finset.mem_univ ab.2))
        have hb : 0 < Q.snd.pmf ab.2 :=
          lt_of_lt_of_le hq (Finset.single_le_sum (fun a _ => Q.nonneg (a, ab.2)) (Finset.mem_univ ab.1))
        have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hb) hq)
        have hmul := mul_le_mul_of_nonneg_left hlog hq.le
        have hsimp : Q.pmf ab * (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 / Q.pmf ab - 1) =
            Q.fst.pmf ab.1 * Q.snd.pmf ab.2 - Q.pmf ab := by
          field_simp [hq.ne']
        linarith
    calc
      ∑ ab : α × β,
          (if Q.pmf ab ≤ 0 then (0 : ℝ)
           else Q.pmf ab * Real.log (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 / Q.pmf ab))
        ≤ ∑ ab : α × β, (Q.fst.pmf ab.1 * Q.snd.pmf ab.2 - Q.pmf ab) :=
          Finset.sum_le_sum (fun ab _ => hpt ab)
      _ = (∑ ab : α × β, Q.fst.pmf ab.1 * Q.snd.pmf ab.2) - ∑ ab : α × β, Q.pmf ab :=
          Finset.sum_sub_distrib _ _
      _ = (∑ a : α, Q.fst.pmf a) * (∑ b : β, Q.snd.pmf b) - 1 := by
          rw [Fintype.sum_prod_type, Q.sum_one]
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = 0 := by rw [Q.fst.sum_one, Q.snd.sum_one]; ring
  rw [h_eq] at hle
  nlinarith

private lemma rateDistortion_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbDist α) (d : Distortion α β) (D : ℝ) :
    0 ≤ rateDistortion P d D := by
  unfold rateDistortion
  refine Real.sInf_nonneg (fun r hr => ?_)
  rcases hr with ⟨Q, _, _, rfl⟩
  exact mutualInfo_nonneg Q

/-! ### Step 2: The critical boundary source `P₀ = Bern(1/4)` has `R(P₀, 1/4) = 0` -/

private noncomputable def P₀ : ProbDist (Fin 2) where
  pmf := fun x => if x = 0 then (3 : ℝ) / 4 else (1 : ℝ) / 4
  nonneg := fun x => by fin_cases x <;> norm_num
  sum_one := by rw [Fin.sum_univ_two]; norm_num

private def δ₀ : ProbDist (Fin 2) where
  pmf := fun y => if y = 0 then (1 : ℝ) else 0
  nonneg := fun y => by fin_cases y <;> norm_num
  sum_one := by rw [Fin.sum_univ_two]; norm_num

private lemma probDist_ext {α : Type*} [Fintype α] {P Q : ProbDist α}
    (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P
  cases Q
  congr 1
  funext a
  exact h a

private lemma rateDistortion_P₀_eq_zero :
    rateDistortion P₀ (Problems.UniversalLossyRedundancy.hammingDist 2) (1 / 4) = 0 := by
  apply le_antisymm _ (rateDistortion_nonneg P₀ (Problems.UniversalLossyRedundancy.hammingDist 2) (1 / 4))
  unfold rateDistortion
  have hbdd : BddBelow { r : ℝ | ∃ Q : ProbDist (Fin 2 × Fin 2),
      Q.fst = P₀ ∧
      (∑ xy : Fin 2 × Fin 2, Q.pmf xy * (Problems.UniversalLossyRedundancy.hammingDist 2).dist xy.1 xy.2) ≤ 1 / 4 ∧
      r = mutualInfo Q } := by
    refine ⟨0, fun r hr => ?_⟩
    rcases hr with ⟨Q, _, _, rfl⟩
    exact mutualInfo_nonneg Q
  apply csInf_le hbdd
  refine ⟨P₀.prod δ₀, ?_, ?_, ?_⟩
  · -- `(P₀.prod δ₀).fst = P₀`
    refine probDist_ext (fun a => ?_)
    simp [ProbDist.fst, ProbDist.prod, δ₀]
  · -- expected Hamming distortion is `1 / 4 ≤ 1 / 4`
    rw [Fintype.sum_prod_type]
    simp [ProbDist.prod, P₀, δ₀, Problems.UniversalLossyRedundancy.hammingDist, Fin.sum_univ_two]
  · -- `mutualInfo (P₀.prod δ₀) = 0`
    have hfst : shannonEntropy (P₀.prod δ₀).fst = shannonEntropy P₀ := by
      congr 1
      refine probDist_ext (fun a => ?_)
      simp [ProbDist.fst, ProbDist.prod, δ₀]
    have hsnd : shannonEntropy (P₀.prod δ₀).snd = 0 := by
      have h1 : (P₀.prod δ₀).snd.pmf 0 = 1 := by
        simp [ProbDist.snd, ProbDist.prod, P₀, δ₀, Fin.sum_univ_two]; norm_num
      have h2 : (P₀.prod δ₀).snd.pmf 1 = 0 := by
        simp [ProbDist.snd, ProbDist.prod, P₀, δ₀, Fin.sum_univ_two]
      rw [shannonEntropy, Fin.sum_univ_two, h1, h2]
      simp [negPLogP, log2]
    have hjoint : shannonEntropy (P₀.prod δ₀) = shannonEntropy P₀ := by
      simp only [shannonEntropy, Fintype.sum_prod_type, ProbDist.prod, δ₀, Fin.sum_univ_two, negPLogP]
      simp
    rw [mutualInfo, hfst, hsnd, hjoint]
    ring

/-! ### Step 3: Exact moments and fourth-moment anticoncentration for `P₀^{⊗ n}` -/

private noncomputable def w₀ (n : ℕ) (x : Fin n → Fin 2) : ℝ :=
  ∏ i : Fin n, P₀.pmf (x i)

private lemma w₀_nonneg (n : ℕ) (x : Fin n → Fin 2) : 0 ≤ w₀ n x :=
  Finset.prod_nonneg (fun i _ => P₀.nonneg (x i))

private lemma w₀_sum_one (n : ℕ) : ∑ x : Fin n → Fin 2, w₀ n x = 1 := by
  unfold w₀
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one (fun _ _ => P₀.sum_one)

private noncomputable def y₀ (b : Fin 2) : ℝ :=
  if b = 1 then (3 : ℝ) / 4 else -(1 : ℝ) / 4

private noncomputable def Z₀ (n : ℕ) (x : Fin n → Fin 2) : ℝ :=
  ∑ i : Fin n, y₀ (x i)

private lemma sum_succ_factor (n : ℕ) (f : Fin 2 → ℝ) (g : (Fin n → Fin 2) → ℝ) :
    (∑ x : Fin (n + 1) → Fin 2, w₀ (n + 1) x * (f (x 0) * g (fun i => x i.succ))) =
      (∑ b : Fin 2, P₀.pmf b * f b) * (∑ x' : Fin n → Fin 2, w₀ n x' * g x') := by
  let e : (Fin 2 × (Fin n → Fin 2)) ≃ (Fin (n + 1) → Fin 2) :=
    Fin.consEquiv (fun _ => Fin 2)
  rw [← Fintype.sum_equiv e
    (fun p => w₀ (n + 1) (e p) * (f (e p 0) * g (fun i => e p i.succ)))
    (fun x => w₀ (n + 1) x * (f (x 0) * g (fun i => x i.succ)))
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  have hterm : ∀ b : Fin 2, ∀ x' : Fin n → Fin 2,
      w₀ (n + 1) (e (b, x')) * (f (e (b, x') 0) * g (fun i => e (b, x') i.succ)) =
        (P₀.pmf b * f b) * (w₀ n x' * g x') := by
    intro b x'
    have hw : w₀ (n + 1) (e (b, x')) = P₀.pmf b * w₀ n x' := by
      simp [w₀, e, Fin.prod_univ_succ]
    have h0 : e (b, x') 0 = b := rfl
    have hs : (fun i : Fin n => e (b, x') i.succ) = x' := by
      funext i; rfl
    rw [hw, h0, hs]
    ring
  simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul]

private lemma y₀_m1 : ∑ b : Fin 2, P₀.pmf b * y₀ b = 0 := by
  rw [Fin.sum_univ_two]; simp [P₀, y₀]; norm_num

private lemma y₀_m2 : ∑ b : Fin 2, P₀.pmf b * (y₀ b) ^ 2 = 3 / 16 := by
  rw [Fin.sum_univ_two]; simp [P₀, y₀]; norm_num

private lemma y₀_m4 : ∑ b : Fin 2, P₀.pmf b * (y₀ b) ^ 4 = 21 / 256 := by
  rw [Fin.sum_univ_two]; simp [P₀, y₀]; norm_num

private lemma Z₀_mean (n : ℕ) : ∑ x : Fin n → Fin 2, w₀ n x * Z₀ n x = 0 := by
  induction n with
  | zero => simp [Z₀]
  | succ n ih =>
    have hsplit : ∀ x : Fin (n + 1) → Fin 2,
        w₀ (n + 1) x * Z₀ (n + 1) x =
          w₀ (n + 1) x * (y₀ (x 0) * 1) + w₀ (n + 1) x * (1 * Z₀ n (fun i => x i.succ)) := by
      intro x
      simp only [Z₀, Fin.sum_univ_succ]
      ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [sum_succ_factor n y₀ (fun _ => 1), sum_succ_factor n (fun _ => 1) (Z₀ n)]
    rw [y₀_m1, ih]
    ring

private lemma Z₀_second_moment (n : ℕ) :
    ∑ x : Fin n → Fin 2, w₀ n x * (Z₀ n x) ^ 2 = (3 : ℝ) / 16 * (n : ℝ) := by
  induction n with
  | zero => simp [Z₀]
  | succ n ih =>
    have hsplit : ∀ x : Fin (n + 1) → Fin 2,
        w₀ (n + 1) x * (Z₀ (n + 1) x) ^ 2 =
          w₀ (n + 1) x * ((y₀ (x 0)) ^ 2 * 1) +
          2 * (w₀ (n + 1) x * (y₀ (x 0) * Z₀ n (fun i => x i.succ))) +
          w₀ (n + 1) x * (1 * (Z₀ n (fun i => x i.succ)) ^ 2) := by
      intro x
      simp only [Z₀, Fin.sum_univ_succ]
      ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_succ_factor n (fun b => (y₀ b) ^ 2) (fun _ => 1),
        sum_succ_factor n y₀ (Z₀ n),
        sum_succ_factor n (fun _ => 1) (fun x' => (Z₀ n x') ^ 2)]
    have hone : ∑ b : Fin 2, P₀.pmf b * (1 : ℝ) = 1 := by simp [P₀.sum_one]
    have hone_n : ∑ x' : Fin n → Fin 2, w₀ n x' * (1 : ℝ) = 1 := by simp [w₀_sum_one n]
    rw [y₀_m2, y₀_m1, hone, hone_n, ih]
    push_cast
    ring

private lemma Z₀_fourth_moment (n : ℕ) :
    ∑ x : Fin n → Fin 2, w₀ n x * (Z₀ n x) ^ 4 =
      (27 : ℝ) / 256 * (n : ℝ) ^ 2 - (6 : ℝ) / 256 * (n : ℝ) := by
  induction n with
  | zero => simp [Z₀]
  | succ n ih =>
    have hsplit : ∀ x : Fin (n + 1) → Fin 2,
        w₀ (n + 1) x * (Z₀ (n + 1) x) ^ 4 =
          w₀ (n + 1) x * ((y₀ (x 0)) ^ 4 * 1) +
          4 * (w₀ (n + 1) x * ((y₀ (x 0)) ^ 3 * Z₀ n (fun i => x i.succ))) +
          6 * (w₀ (n + 1) x * ((y₀ (x 0)) ^ 2 * (Z₀ n (fun i => x i.succ)) ^ 2)) +
          4 * (w₀ (n + 1) x * (y₀ (x 0) * (Z₀ n (fun i => x i.succ)) ^ 3)) +
          w₀ (n + 1) x * (1 * (Z₀ n (fun i => x i.succ)) ^ 4) := by
      intro x
      simp only [Z₀, Fin.sum_univ_succ]
      ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_succ_factor n (fun b => (y₀ b) ^ 4) (fun _ => 1),
        sum_succ_factor n (fun b => (y₀ b) ^ 3) (Z₀ n),
        sum_succ_factor n (fun b => (y₀ b) ^ 2) (fun x' => (Z₀ n x') ^ 2),
        sum_succ_factor n y₀ (fun x' => (Z₀ n x') ^ 3),
        sum_succ_factor n (fun _ => 1) (fun x' => (Z₀ n x') ^ 4)]
    have hone : ∑ b : Fin 2, P₀.pmf b * (1 : ℝ) = 1 := by simp [P₀.sum_one]
    have hone_n : ∑ x' : Fin n → Fin 2, w₀ n x' * (1 : ℝ) = 1 := by simp [w₀_sum_one n]
    rw [y₀_m4, y₀_m2, y₀_m1, hone, hone_n, Z₀_mean n, Z₀_second_moment n, ih]
    push_cast
    ring

private lemma poly_anticonc_pointwise {s x : ℝ} (hs : 0 < s) :
    x / 2 + x ^ 2 / (6 * s) - x ^ 4 / (54 * s ^ 3) ≤
      s / 18 + x ^ 2 / (36 * s) + (if s / 18 ≤ x then 9 * s else 0) := by
  set u : ℝ := x / s
  have hx : x = u * s := (div_mul_cancel₀ x hs.ne').symm
  -- Step A: `u / 2 + u^2 / 6 - u^4 / 54 ≤ max u 0`
  have hA : u / 2 + u ^ 2 / 6 - u ^ 4 / 54 ≤ max u 0 := by
    by_cases hu : 0 ≤ u
    · rw [max_eq_left hu]
      have hfactor : 0 ≤ u * ((u - 2) ^ 2 * (u + 4) + 3 * u + 11) := by positivity
      have heq : u * ((u - 2) ^ 2 * (u + 4) + 3 * u + 11) =
          54 * (u - (u / 2 + u ^ 2 / 6 - u ^ 4 / 54)) := by ring
      linarith
    · push Not at hu
      rw [max_eq_right hu.le]
      set t : ℝ := -u
      have ht : 0 ≤ t := by linarith
      have hfactor : 0 ≤ t * ((t - 2) ^ 2 * (t + 4) + 3 * t + 11) := by positivity
      have heq : t * ((t - 2) ^ 2 * (t + 4) + 3 * t + 11) =
          54 * (-(u / 2 + u ^ 2 / 6 - u ^ 4 / 54)) := by
        dsimp [t]; ring
      linarith
  -- Step B: `max u 0 ≤ 1/18 + u^2 / 36 + (if 1/18 ≤ u then 9 else 0)`
  have hB : max u 0 ≤ 1 / 18 + u ^ 2 / 36 + (if (1 : ℝ) / 18 ≤ u then 9 else 0) := by
    split_ifs with h18
    · have hsq : 0 ≤ (u - 18) ^ 2 := sq_nonneg (u - 18)
      rw [max_eq_left (by linarith)]
      nlinarith
    · push Not at h18
      have hsq : 0 ≤ u ^ 2 / 36 := by positivity
      have hmax : max u 0 ≤ 1 / 18 := max_le h18.le (by norm_num)
      linarith
  have hAB := le_trans hA hB
  have hcond : ((1 : ℝ) / 18 ≤ u) ↔ (s / 18 ≤ x) := by
    rw [hx]
    constructor <;> intro h <;> nlinarith
  have hmul := mul_le_mul_of_nonneg_right hAB hs.le
  rw [if_congr hcond rfl rfl] at hmul
  have hLHS : (u / 2 + u ^ 2 / 6 - u ^ 4 / 54) * s =
      x / 2 + x ^ 2 / (6 * s) - x ^ 4 / (54 * s ^ 3) := by
    rw [hx]; field_simp [hs.ne']
  have hRHS : (1 / 18 + u ^ 2 / 36 + (if s / 18 ≤ x then (9 : ℝ) else 0)) * s =
      s / 18 + x ^ 2 / (36 * s) + (if s / 18 ≤ x then 9 * s else 0) := by
    rw [hx]
    split_ifs
    · field_simp [hs.ne']
    · field_simp [hs.ne']; ring
  linarith

private noncomputable def s₀ (n : ℕ) : ℝ :=
  Real.sqrt ((3 : ℝ) / 16 * (n : ℝ))

private noncomputable def t₀ (n : ℕ) : ℝ :=
  s₀ n / 18

private lemma s₀_pos {n : ℕ} (hn : 0 < n) : 0 < s₀ n := by
  unfold s₀
  exact Real.sqrt_pos.mpr (by positivity)

private lemma s₀_sq (n : ℕ) : (s₀ n) ^ 2 = (3 : ℝ) / 16 * (n : ℝ) :=
  Real.sq_sqrt (by positivity)

private noncomputable def E_set (n : ℕ) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter (fun x => t₀ n ≤ Z₀ n x)

private lemma prob_E_set_ge {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / 324 ≤ ∑ x ∈ E_set n, w₀ n x := by
  have hs : 0 < s₀ n := s₀_pos hn
  have hsq : (s₀ n) ^ 2 = (3 : ℝ) / 16 * (n : ℝ) := s₀_sq n
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (poly_anticonc_pointwise hs (x := Z₀ n x)) (w₀_nonneg n x))
  -- Evaluate LHS sum
  have hLHS :
      (∑ x : Fin n → Fin 2, w₀ n x * (Z₀ n x / 2 + (Z₀ n x) ^ 2 / (6 * s₀ n) -
        (Z₀ n x) ^ 4 / (54 * (s₀ n) ^ 3)))
      ≥ s₀ n / 9 := by
    have hrewrite : ∀ x : Fin n → Fin 2,
        w₀ n x * (Z₀ n x / 2 + (Z₀ n x) ^ 2 / (6 * s₀ n) - (Z₀ n x) ^ 4 / (54 * (s₀ n) ^ 3)) =
          (1 / 2) * (w₀ n x * Z₀ n x) +
          (1 / (6 * s₀ n)) * (w₀ n x * (Z₀ n x) ^ 2) -
          (1 / (54 * (s₀ n) ^ 3)) * (w₀ n x * (Z₀ n x) ^ 4) := by
      intro x; ring
    simp_rw [hrewrite, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Z₀_mean n, Z₀_second_moment n, Z₀_fourth_moment n]
    have h4 : (27 : ℝ) / 256 * (n : ℝ) ^ 2 - 6 / 256 * (n : ℝ) ≤ 3 * (s₀ n) ^ 4 := by
      have h4' : (s₀ n) ^ 4 = ((s₀ n) ^ 2) ^ 2 := by ring
      rw [h4', hsq]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hden : 0 < 54 * (s₀ n) ^ 3 := by positivity
    have hdiv : (1 / (54 * (s₀ n) ^ 3)) * ((27 : ℝ) / 256 * (n : ℝ) ^ 2 - 6 / 256 * (n : ℝ)) ≤
        (1 / (54 * (s₀ n) ^ 3)) * (3 * (s₀ n) ^ 4) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have hcalc : (1 / 2) * (0 : ℝ) + (1 / (6 * s₀ n)) * ((s₀ n) ^ 2) -
        (1 / (54 * (s₀ n) ^ 3)) * (3 * (s₀ n) ^ 4) = s₀ n / 9 := by
      field_simp [hs.ne']; ring
    rw [← hsq]
    linarith
  -- Evaluate RHS sum
  have hRHS :
      (∑ x : Fin n → Fin 2, w₀ n x * (s₀ n / 18 + (Z₀ n x) ^ 2 / (36 * s₀ n) +
        (if s₀ n / 18 ≤ Z₀ n x then 9 * s₀ n else 0)))
      = s₀ n / 12 + 9 * s₀ n * (∑ x ∈ E_set n, w₀ n x) := by
    have hrewrite : ∀ x : Fin n → Fin 2,
        w₀ n x * (s₀ n / 18 + (Z₀ n x) ^ 2 / (36 * s₀ n) +
          (if s₀ n / 18 ≤ Z₀ n x then 9 * s₀ n else 0)) =
          (s₀ n / 18) * w₀ n x +
          (1 / (36 * s₀ n)) * (w₀ n x * (Z₀ n x) ^ 2) +
          (9 * s₀ n) * (if t₀ n ≤ Z₀ n x then w₀ n x else 0) := by
      intro x; unfold t₀; split_ifs <;> ring
    simp_rw [hrewrite, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [w₀_sum_one n, Z₀_second_moment n, ← hsq]
    have hfilt : (∑ x : Fin n → Fin 2, if t₀ n ≤ Z₀ n x then w₀ n x else 0) =
        ∑ x ∈ E_set n, w₀ n x := by
      rw [E_set, Finset.sum_filter]
    rw [hfilt]
    field_simp [hs.ne']; ring
  nlinarith

/-! ### Step 4: Uniform exponential Chernoff bound on `B(c, n/4) ∩ E_set n` -/

private lemma ball_inter_E_le (n : ℕ) (hn : 0 < n) (c : Fin n → Fin 2)
    (S : Finset (Fin n → Fin 2))
    (hSE : ∀ x ∈ S, t₀ n ≤ Z₀ n x)
    (hSB : ∀ x ∈ S, ((1 : ℝ) / (n : ℝ)) * ∑ i : Fin n, (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i) ≤ 1 / 4) :
    ∑ x ∈ S, w₀ n x ≤ (2 : ℝ) ^ (-t₀ n) := by
  let S₁ : Finset (Fin n) := Finset.univ.filter (fun i => c i = 1)
  let w : ℕ := S₁.card
  let A : (Fin n → Fin 2) → ℕ := fun x => (S₁.filter (fun i => x i = 1)).card
  -- Pointwise: on `S`, `(w : ℝ) + t₀ n ≤ 2 * (A x : ℝ)`, hence `2^(w + t₀ n) ≤ 4^(A x)`
  have hpoint : ∀ x ∈ S, (2 : ℝ) ^ (w : ℝ) * (2 : ℝ) ^ (t₀ n) ≤ (4 : ℝ) ^ (A x) := by
    intro x hx
    have hZ : t₀ n ≤ Z₀ n x := hSE x hx
    have hD : ∑ i : Fin n, (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i) ≤ (n : ℝ) / 4 := by
      have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have h1 := mul_le_mul_of_nonneg_left (hSB x hx) hn'.le
      have h2 : (n : ℝ) * ((1 : ℝ) / (n : ℝ) * ∑ i : Fin n, (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i)) =
          ∑ i : Fin n, (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i) := by
        field_simp [hn'.ne']
      linarith
    -- Algebraic identity per coordinate `i`:
    -- `y₀ (x i) + (1/4) - d(x i, c i) = 2 * 1_{c i = 1 ∧ x i = 1} - 1_{c i = 1}`
    have hcoord : ∀ i : Fin n,
        y₀ (x i) + 1 / 4 - (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i) =
          (if c i = 1 ∧ x i = 1 then (2 : ℝ) else 0) - (if c i = 1 then (1 : ℝ) else 0) := by
      intro i
      generalize hxi : x i = a
      generalize hci : c i = b
      fin_cases a <;> fin_cases b <;> simp [y₀, Problems.UniversalLossyRedundancy.hammingDist] <;> norm_num
    have hsum_id :
        Z₀ n x + (n : ℝ) / 4 - ∑ i : Fin n, (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i) =
          2 * (A x : ℝ) - (w : ℝ) := by
      have h1 : Z₀ n x + (n : ℝ) / 4 - ∑ i : Fin n, (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i) =
          ∑ i : Fin n, (y₀ (x i) + 1 / 4 - (Problems.UniversalLossyRedundancy.hammingDist 2).dist (x i) (c i)) := by
        simp only [Z₀, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [h1]
      simp_rw [hcoord, Finset.sum_sub_distrib]
      have hA_eq : (∑ i : Fin n, if c i = 1 ∧ x i = 1 then (2 : ℝ) else 0) = 2 * (A x : ℝ) := by
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun i : Fin n => c i = 1 ∧ x i = 1) =
            S₁.filter (fun i => x i = 1) := by
          ext i; simp [S₁]
        rw [hf, Finset.sum_const, nsmul_eq_mul]
        ring
      have hw_eq : (∑ i : Fin n, if c i = 1 then (1 : ℝ) else 0) = (w : ℝ) := by
        rw [← Finset.sum_filter]
        simp [S₁, w]
      rw [hA_eq, hw_eq]
    have hineq : (w : ℝ) + t₀ n ≤ 2 * (A x : ℝ) := by linarith
    have hpow1 : (2 : ℝ) ^ ((w : ℝ) + t₀ n) ≤ (2 : ℝ) ^ (2 * (A x : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hineq
    rw [Real.rpow_add (by norm_num)] at hpow1
    have hpow2 : (2 : ℝ) ^ (2 * (A x : ℝ)) = (4 : ℝ) ^ (A x) := by
      rw [show (2 : ℝ) * (A x : ℝ) = ((2 * A x : ℕ) : ℝ) by push_cast; ring]
      rw [Real.rpow_natCast, pow_mul]
      norm_num
    linarith
  -- Expectation of `4^(A x)` under `P₀^{⊗ n}` is `(7/4)^w ≤ 2^w`
  have hMGF : ∑ x : Fin n → Fin 2, w₀ n x * (4 : ℝ) ^ (A x) ≤ (2 : ℝ) ^ (w : ℝ) := by
    have hprod : ∀ x : Fin n → Fin 2,
        w₀ n x * (4 : ℝ) ^ (A x) =
          ∏ i : Fin n, (P₀.pmf (x i) * (if c i = 1 ∧ x i = 1 then (4 : ℝ) else 1)) := by
      intro x
      have h4 : (4 : ℝ) ^ (A x) = ∏ i : Fin n, (if c i = 1 ∧ x i = 1 then (4 : ℝ) else 1) := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        congr 1
        dsimp [A]
        congr 1
        ext i; simp [S₁]
      unfold w₀
      rw [h4, ← Finset.prod_mul_distrib]
    simp_rw [hprod]
    have hps := Fintype.prod_sum (fun (i : Fin n) (b : Fin 2) =>
      P₀.pmf b * (if c i = 1 ∧ b = 1 then (4 : ℝ) else 1))
    rw [← hps]
    have hcoord_le : ∀ i : Fin n,
        (∑ b : Fin 2, P₀.pmf b * (if c i = 1 ∧ b = 1 then (4 : ℝ) else 1)) ≤
          if c i = 1 then (2 : ℝ) else 1 := by
      intro i
      generalize hci : c i = b
      fin_cases b <;> rw [Fin.sum_univ_two] <;> simp [P₀] <;> norm_num
    have hcoord_nonneg : ∀ i : Fin n,
        0 ≤ ∑ b : Fin 2, P₀.pmf b * (if c i = 1 ∧ b = 1 then (4 : ℝ) else 1) := fun i =>
      Finset.sum_nonneg (fun b _ => mul_nonneg (P₀.nonneg b) (by split_ifs <;> norm_num))
    have hprod_le :
        ∀ s : Finset (Fin n),
          ∏ i ∈ s, (∑ b : Fin 2, P₀.pmf b * (if c i = 1 ∧ b = 1 then (4 : ℝ) else 1)) ≤
            ∏ i ∈ s, (if c i = 1 then (2 : ℝ) else 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        exact mul_le_mul (hcoord_le a) ih
          (Finset.prod_nonneg (fun i _ => hcoord_nonneg i))
          (by split_ifs <;> norm_num)
    calc
      ∏ i : Fin n, (∑ b : Fin 2, P₀.pmf b * (if c i = 1 ∧ b = 1 then (4 : ℝ) else 1))
        ≤ ∏ i : Fin n, (if c i = 1 then (2 : ℝ) else 1) := hprod_le Finset.univ
      _ = (2 : ℝ) ^ w := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      _ = (2 : ℝ) ^ (w : ℝ) := (Real.rpow_natCast 2 w).symm
  -- Combine via Markov's inequality
  have hmarkov : (2 : ℝ) ^ (w : ℝ) * (2 : ℝ) ^ (t₀ n) * (∑ x ∈ S, w₀ n x) ≤ (2 : ℝ) ^ (w : ℝ) := by
    calc
      (2 : ℝ) ^ (w : ℝ) * (2 : ℝ) ^ (t₀ n) * (∑ x ∈ S, w₀ n x)
        = ∑ x ∈ S, w₀ n x * ((2 : ℝ) ^ (w : ℝ) * (2 : ℝ) ^ (t₀ n)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ ∑ x ∈ S, w₀ n x * (4 : ℝ) ^ (A x) :=
            Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hpoint x hx) (w₀_nonneg n x))
      _ ≤ ∑ x : Fin n → Fin 2, w₀ n x * (4 : ℝ) ^ (A x) :=
            Finset.sum_le_univ_sum_of_nonneg (fun x => mul_nonneg (w₀_nonneg n x) (by positivity))
      _ ≤ (2 : ℝ) ^ (w : ℝ) := hMGF
  have h2w : (0 : ℝ) < (2 : ℝ) ^ (w : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h2t : (0 : ℝ) < (2 : ℝ) ^ (t₀ n) := Real.rpow_pos_of_pos (by norm_num) _
  have hcancel : (2 : ℝ) ^ (t₀ n) * (∑ x ∈ S, w₀ n x) ≤ 1 := by
    refine le_of_mul_le_mul_left ?_ h2w
    linarith [show (2 : ℝ) ^ (w : ℝ) * ((2 : ℝ) ^ (t₀ n) * ∑ x ∈ S, w₀ n x) =
      (2 : ℝ) ^ (w : ℝ) * (2 : ℝ) ^ (t₀ n) * ∑ x ∈ S, w₀ n x by ring]
  rw [Real.rpow_neg (by norm_num), ← one_div, le_div_iff₀' h2t]
  exact hcancel

/-! ### Step 5: Kraft + short/long codeword split gives `expectedRate ≥ t₀ n / (1296 * n)` -/

private lemma expectedRate_P₀_ge {n M : ℕ}
    (enc : (Fin n → Fin 2) → Fin M) (dec : Fin M → (Fin n → Fin 2)) (len : Fin M → ℕ)
    (hcode : IsDSemifaithfulCode 2 (Problems.UniversalLossyRedundancy.hammingDist 2) (1 / 4) n M enc dec len)
    (ht20 : 20 ≤ t₀ n) :
    t₀ n / (1296 * (n : ℝ)) ≤ expectedRate P₀ n M enc len := by
  rcases hcode with ⟨hn, _, hkraft, hdist⟩
  let short : Finset (Fin M) := Finset.univ.filter (fun c => (len c : ℝ) ≤ t₀ n / 2)
  -- Kraft bound on the number of short codewords
  have hshort_card : (short.card : ℝ) ≤ (2 : ℝ) ^ (t₀ n / 2) := by
    have h1 : (short.card : ℝ) * (2 : ℝ) ^ (-(t₀ n / 2)) ≤
        ∑ c ∈ short, (2 : ℝ) ^ (-(len c : ℝ)) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum (fun c hc => ?_)
      have hlc : (len c : ℝ) ≤ t₀ n / 2 := (Finset.mem_filter.mp hc).2
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : ∑ c ∈ short, (2 : ℝ) ^ (-(len c : ℝ)) ≤ 1 :=
      le_trans
        (Finset.sum_le_univ_sum_of_nonneg (fun c => Real.rpow_nonneg (by norm_num) _))
        hkraft
    have hle1 : (short.card : ℝ) * (2 : ℝ) ^ (-(t₀ n / 2)) ≤ 1 := le_trans h1 h2
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (t₀ n / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_right hle1 hpos.le
    have hcancel : (2 : ℝ) ^ (-(t₀ n / 2)) * (2 : ℝ) ^ (t₀ n / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      simp
    linarith [show (short.card : ℝ) * (2 : ℝ) ^ (-(t₀ n / 2)) * (2 : ℝ) ^ (t₀ n / 2) =
      (short.card : ℝ) by rw [mul_assoc, hcancel, mul_one]]
  -- Partition `E_set n` into `E_short` and `E_long`
  let E_short : Finset (Fin n → Fin 2) := (E_set n).filter (fun x => enc x ∈ short)
  let E_long : Finset (Fin n → Fin 2) := (E_set n).filter (fun x => enc x ∉ short)
  have hE_split : ∑ x ∈ E_short, w₀ n x + ∑ x ∈ E_long, w₀ n x = ∑ x ∈ E_set n, w₀ n x :=
    Finset.sum_filter_add_sum_filter_not (E_set n) (fun x => enc x ∈ short) (w₀ n)
  -- Upper bound `P₀^{⊗ n}(E_short)` by summing over `c ∈ short`
  have hE_short_le : ∑ x ∈ E_short, w₀ n x ≤ (2 : ℝ) ^ (-(t₀ n / 2)) := by
    have hfib : ∑ x ∈ E_short, w₀ n x =
        ∑ c ∈ short, ∑ x ∈ (E_set n).filter (fun x => enc x = c), w₀ n x := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := enc) (t := short)
        (fun x hx => (Finset.mem_filter.mp hx).2)]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      congr 1
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hxE, _⟩, rfl⟩; exact ⟨hxE, rfl⟩
      · rintro ⟨hxE, rfl⟩; exact ⟨⟨hxE, hc⟩, rfl⟩
    rw [hfib]
    have hper_c : ∀ c ∈ short,
        ∑ x ∈ (E_set n).filter (fun x => enc x = c), w₀ n x ≤ (2 : ℝ) ^ (-t₀ n) := by
      intro c _
      refine ball_inter_E_le n hn (dec c) ((E_set n).filter (fun x => enc x = c)) ?_ ?_
      · intro x hx
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      · intro x hx
        have henc : enc x = c := (Finset.mem_filter.mp hx).2
        rw [← henc]
        exact hdist x
    calc
      ∑ c ∈ short, ∑ x ∈ (E_set n).filter (fun x => enc x = c), w₀ n x
        ≤ ∑ _c ∈ short, (2 : ℝ) ^ (-t₀ n) := Finset.sum_le_sum hper_c
      _ = (short.card : ℝ) * (2 : ℝ) ^ (-t₀ n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ (t₀ n / 2) * (2 : ℝ) ^ (-t₀ n) :=
          mul_le_mul_of_nonneg_right hshort_card (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (-(t₀ n / 2)) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1; ring
  -- Since `t₀ n ≥ 20`, `2 ^ (-(t₀ n / 2)) ≤ 2 ^ (-10) = 1 / 1024 ≤ 1 / 648`
  have htail : (2 : ℝ) ^ (-(t₀ n / 2)) ≤ 1 / 648 := by
    have h1 : (2 : ℝ) ^ (-(t₀ n / 2)) ≤ (2 : ℝ) ^ (-(10 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-(10 : ℝ)) = 1 / 1024 := by
      rw [Real.rpow_neg (by norm_num), show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    linarith
  have hE_long_ge : (1 : ℝ) / 648 ≤ ∑ x ∈ E_long, w₀ n x := by
    have hE := prob_E_set_ge hn
    linarith
  -- Lower bound expected codeword length by restricting to `E_long`
  have hEL : t₀ n / 1296 ≤ ∑ x : Fin n → Fin 2, w₀ n x * (len (enc x) : ℝ) := by
    calc
      t₀ n / 1296 = (t₀ n / 2) * (1 / 648) := by ring
      _ ≤ (t₀ n / 2) * (∑ x ∈ E_long, w₀ n x) :=
          mul_le_mul_of_nonneg_left hE_long_ge (by linarith)
      _ = ∑ x ∈ E_long, w₀ n x * (t₀ n / 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ ∑ x ∈ E_long, w₀ n x * (len (enc x) : ℝ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          have hnot : enc x ∉ short := (Finset.mem_filter.mp hx).2
          have hgt : t₀ n / 2 < (len (enc x) : ℝ) := by
            simp only [short, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
            exact hnot
          exact mul_le_mul_of_nonneg_left hgt.le (w₀_nonneg n x)
      _ ≤ ∑ x : Fin n → Fin 2, w₀ n x * (len (enc x) : ℝ) :=
          Finset.sum_le_univ_sum_of_nonneg (fun x =>
            mul_nonneg (w₀_nonneg n x) (Nat.cast_nonneg _))
  unfold expectedRate
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv := div_le_div_of_nonneg_right hEL hn'.le
  have heq : t₀ n / 1296 / (n : ℝ) = t₀ n / (1296 * (n : ℝ)) := by ring
  simpa [w₀, heq] using hdiv

/-! ### Step 6: Nonemptiness of the feasible redundancy set and lower bound on `minimaxLossyRedundancy` -/

private lemma minimaxLossyRedundancy_ge {n : ℕ} (hn : 0 < n) (ht20 : 20 ≤ t₀ n) :
    t₀ n / (1296 * (n : ℝ)) ≤ fullSimplexMinimax 2 (1 / 4) n := by
  unfold fullSimplexMinimax minimaxLossyRedundancyOn
  refine le_csInf ?_ ?_
  · -- Nonempty: trivial lossless code `M = 2^n`, `len c = n`, `r = 1`
    refine ⟨1, 2 ^ n, ?_⟩
    have hcard : Fintype.card (Fin n → Fin 2) = 2 ^ n := by simp
    let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard
    refine ⟨e, e.symm, fun _ => n, ?_, ?_⟩
    · refine ⟨hn, by positivity, ?_, ?_⟩
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        have hpos : ((2 : ℝ) ^ n) ≠ 0 := by positivity
        push_cast
        field_simp [hpos]
        exact le_rfl
      · intro x
        simp [Problems.UniversalLossyRedundancy.hammingDist]
    · intro P _
      have hR0 : 0 ≤ rateDistortion P (Problems.UniversalLossyRedundancy.hammingDist 2) (1 / 4) :=
        rateDistortion_nonneg P (Problems.UniversalLossyRedundancy.hammingDist 2) (1 / 4)
      have hrate : expectedRate P n (2 ^ n) e (fun _ => n) = 1 := by
        unfold expectedRate
        rw [← Finset.sum_mul, ← Fintype.prod_sum]
        have hp : ∏ _i : Fin n, ∑ x : Fin 2, P.pmf x = 1 :=
          Finset.prod_eq_one (fun _ _ => P.sum_one)
        rw [hp, one_mul]
        exact div_self (Nat.cast_ne_zero.mpr hn.ne')
      linarith
  · -- Lower bound for every `r` in the set
    rintro r ⟨M, enc, dec, len, hcode, hr⟩
    have hP₀ := hr P₀ (Set.mem_univ _)
    rw [rateDistortion_P₀_eq_zero, sub_zero] at hP₀
    exact le_trans (expectedRate_P₀_ge enc dec len hcode ht20) hP₀

/-! ### Step 7: Elementary upper bound on `log2 n` and final disproof -/

private lemma log2_le_eight_rpow_quarter {n : ℕ} (hn : 1 ≤ n) :
    log2 (n : ℝ) ≤ 8 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_quarter : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos ((1 : ℝ) / 4))
    linarith
  rw [Real.log_rpow hn_pos] at hlog_quarter
  have hlog_n : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by linarith
  unfold log2
  have hlog2_pos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hlog2_half : (1 : ℝ) / 2 ≤ Real.log 2 := log_two_ge_half
  rw [div_le_iff₀ hlog2_pos]
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hn_pos.le _
  nlinarith

/-- **Record of the catalog error fixed on 2026-11-27**: the old frozen statement (supremum over
    the whole simplex, constant `m/2`) is false. -/
theorem fullSimplex_version_false : ¬ FullSimplexStatement := by
  intro hstmt
  rcases hstmt 2 (by norm_num) (1 / 4) (by norm_num) (by norm_num) 1 (by norm_num) with
    ⟨N, hN2, hbound⟩
  let n : ℕ := max N (10 ^ 24)
  have hn_ge_N : N ≤ n := le_max_left N _
  have hn_ge_big : (10 ^ 24 : ℕ) ≤ n := le_max_right N _
  have hn_pos : 0 < n := by omega
  have hn_real : (10 : ℝ) ^ (24 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_big
  have hn_rpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  -- Lower bound `n ^ (1/4) ≥ 10 ^ 6`
  have hq_ge : (10 : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 := Real.rpow_le_rpow (by positivity) hn_real (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    have h2 : ((10 : ℝ) ^ (24 : ℕ)) ^ ((1 : ℝ) / 4) = (10 : ℝ) ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    linarith
  -- Lower bound `t₀ n ≥ √n / 42`
  have ht_ge : Real.sqrt (n : ℝ) / 42 ≤ t₀ n := by
    unfold t₀ s₀
    have h1 : (Real.sqrt (n : ℝ) / 42) ^ 2 ≤ (Real.sqrt ((3 : ℝ) / 16 * (n : ℝ)) / 18) ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt hn_rpos.le, Real.sq_sqrt (by positivity)]
      linarith
    have ha : 0 ≤ Real.sqrt (n : ℝ) / 42 := by positivity
    have hb : 0 ≤ Real.sqrt ((3 : ℝ) / 16 * (n : ℝ)) / 18 := by positivity
    nlinarith
  -- Show `20 ≤ t₀ n`
  have hsqrt_ge : (10 : ℝ) ^ (12 : ℕ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) hn_rpos.le]
    norm_num at hn_real ⊢
    linarith
  have ht20 : 20 ≤ t₀ n := by linarith
  -- Apply `minimaxLossyRedundancy_ge` and `hbound n hn_ge_N`
  have hminimax := minimaxLossyRedundancy_ge hn_pos ht20
  have hupper := hbound n hn_ge_N
  have hlog2_pos : 0 < log2 (n : ℝ) := by
    unfold log2
    have hn2 : (1 : ℝ) < (n : ℝ) := by linarith
    exact div_pos (Real.log_pos hn2) log_two_pos
  have hlog2_le := log2_le_eight_rpow_quarter (by omega : 1 ≤ n)
  -- Show `(n / log2 n) * (t₀ n / (1296 * n)) = t₀ n / (1296 * log2 n)`
  have hsimp : ((n : ℝ) / log2 (n : ℝ)) * (t₀ n / (1296 * (n : ℝ))) =
      t₀ n / (1296 * log2 (n : ℝ)) := by
    field_simp [hn_rpos.ne', hlog2_pos.ne']
  have hchain : t₀ n / (1296 * log2 (n : ℝ)) ≤ (2 : ℝ) / 2 + 1 := by
    calc
      t₀ n / (1296 * log2 (n : ℝ))
        = ((n : ℝ) / log2 (n : ℝ)) * (t₀ n / (1296 * (n : ℝ))) := hsimp.symm
      _ ≤ ((n : ℝ) / log2 (n : ℝ)) * fullSimplexMinimax 2 (1 / 4) n :=
          mul_le_mul_of_nonneg_left hminimax (div_nonneg hn_rpos.le hlog2_pos.le)
      _ ≤ (2 : ℝ) / 2 + 1 := hupper
  -- Since `√n = (n^(1/4))^2`, we get `t₀ n ≥ (n^(1/4))^2 / 42`
  have hsqrt_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_rpos.le]
    norm_num
  have ht_ge2 : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 / 42 ≤ t₀ n := by
    rw [← hsqrt_eq]; exact ht_ge
  have hden_pos : 0 < 1296 * log2 (n : ℝ) := by positivity
  have hmul : t₀ n ≤ 2 * (1296 * log2 (n : ℝ)) := by
    have h := (div_le_iff₀ hden_pos).mp hchain
    linarith
  have hq_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn_rpos _
  -- `((n^(1/4))^2) / 42 ≤ 2 * 1296 * (8 * n^(1/4)) = 20736 * n^(1/4)`
  -- Hence `n^(1/4) ≤ 870912 < 10^6`, contradiction!
  nlinarith


/-- The old counterexample source `Bern(1/4)` (any source with `P(1) = 1/4`, at `D = 1/4`)
    is excluded from every interior class of the fixed statement. -/
theorem bern14_not_mem_interiorClass {δ : ℝ} (hδ : 0 < δ) {P : ProbDist (Fin 2)}
    (hP : P.pmf 1 = 1 / 4) : P ∉ interiorClass 2 (1 / 4) δ := by
  intro h
  have := h 1
  rw [hP] at this
  norm_num at this
  linarith

end BoundaryKink

end InfoTheory.Known.Certificates.UniversalLossyRedundancy
