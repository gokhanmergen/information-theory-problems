import InfoTheory.Problems.CovertCommunicationSecondOrder
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.CovertCommunicationSecondOrder`

The frozen statement (statement-fix 2026-11-27) is the Tahmasbi–Bloch (2019) conjecture that
the missed-detection converse `log₂ M*_β ≤ a √n - b n^{1/4} + O(log n)` is achievable up to
`o(n^{1/4})`.

Certified here, about the exact objects of `Statement` (no junk values):
* `betaAlpha_nonneg`, `betaAlpha_le_one`, `betaAlpha_self` — the warden's optimal
  missed-detection probability is a genuine number in `[0, 1]`, and `β_α(P, P) ≥ 1 - α`
  (an output distribution equal to the innocent one is undetectable);
* `prodPmf_sum_one`, `channelPow_le_one` — the `n`-letter innocent law `Q₀^{⊗n}` and the
  `n`-letter main-channel law are probability distributions;
* `covertSet_bddAbove` — every feasible message count satisfies `m (1 - ε) ≤ kYⁿ`
  (disjoint decoding regions), so the `sSup` is over a bounded set for `ε < 1`;
* `one_le_covertMaxMessagesBeta`, `covertMaxMessagesBeta_le`, `log2_covertMax_nonneg` — the
  one-message all-innocent code is feasible, hence `1 ≤ M*_β ≤ kYⁿ / (1 - ε)` and
  `log₂ M*_β ≥ 0` (the lower bound in `Statement` is not compared against a junk `0`);
* `chiSqFn_pos` — under `Q₁ ≪ Q₀`, `Q₁ ≠ Q₀`, `χ²(Q₁‖Q₀) > 0`, so the coefficients `a, b`
  of `Statement` do not divide by zero.

Not certified: the Tahmasbi–Bloch converse (29) and achievability (30), the square-root law,
any property of `gaussQinv` (e.g. `Λ + Υ > 0`), and the variational-distance analogue
(Zhang–Zhou–Li, arXiv:2609.24675). These facts do not settle `Statement`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CovertCommunicationSecondOrder

open InfoTheory InfoTheory.Problems.CovertCommunicationSecondOrder

/-! ### The warden's missed-detection probability -/

theorem betaAlpha_nonneg {Ω : Type*} [Fintype Ω] (α : ℝ) (P Q : Ω → ℝ) (hQ : ∀ ω, 0 ≤ Q ω) :
    0 ≤ betaAlpha α P Q := by
  apply Real.sInf_nonneg
  rintro b ⟨T, _, rfl⟩
  exact Finset.sum_nonneg (fun ω _ => by split_ifs; exact hQ ω; exact le_rfl)

theorem betaAlpha_le_one {Ω : Type*} [Fintype Ω] (α : ℝ) (hα : 0 ≤ α) (P Q : Ω → ℝ)
    (hQ : ∀ ω, 0 ≤ Q ω) (hQ1 : ∑ ω, Q ω = 1) : betaAlpha α P Q ≤ 1 := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro b ⟨T, _, rfl⟩
    exact Finset.sum_nonneg (fun ω _ => by split_ifs; exact hQ ω; exact le_rfl)
  · exact ⟨fun _ => true, by simp [hα], by simp [hQ1]⟩

theorem betaAlpha_self {Ω : Type*} [Fintype Ω] (α : ℝ) (hα : 0 ≤ α) (P : Ω → ℝ)
    (hP : ∑ ω, P ω = 1) : 1 - α ≤ betaAlpha α P P := by
  apply le_csInf
  · exact ⟨_, fun _ => true, by simp [hα], rfl⟩
  · rintro b ⟨T, hT, rfl⟩
    have h : (∑ ω, if T ω then 0 else P ω) + (∑ ω, if T ω then P ω else 0) = 1 := by
      rw [← Finset.sum_add_distrib, ← hP]
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      split_ifs <;> ring
    linarith

/-! ### `n`-letter laws -/

theorem prodPmf_sum_one {Z : Type*} [Fintype Z] (n : ℕ) (q : Z → ℝ) (hq : ∑ z, q z = 1) :
    ∑ z : Fin n → Z, ∏ i : Fin n, q (z i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => q a)]
  simp [hq]

theorem marginalY_sum {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    (x : Bool) : ∑ y : Y, ∑ z : Z, W.trans x (y, z) = 1 := by
  rw [← W.sum_one x, Fintype.sum_prod_type]

theorem marginalZ_sum {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    (x : Bool) : ∑ z : Z, ∑ y : Y, W.trans x (y, z) = 1 := by
  rw [Finset.sum_comm]; exact marginalY_sum W x

theorem marginalY_le_one {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    (x : Bool) (y : Y) : ∑ z : Z, W.trans x (y, z) ≤ 1 := by
  rw [← marginalY_sum W x]
  exact Finset.single_le_sum (f := fun y => ∑ z : Z, W.trans x (y, z))
    (fun y _ => Finset.sum_nonneg (fun z _ => W.nonneg _ _)) (Finset.mem_univ y)

theorem channelPow_nonneg {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    {n : ℕ} (x : Fin n → Bool) (y : Fin n → Y) :
    0 ≤ ∏ i : Fin n, ∑ z : Z, W.trans (x i) (y i, z) :=
  Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun z _ => W.nonneg _ _))

theorem channelPow_le_one {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    {n : ℕ} (x : Fin n → Bool) (y : Fin n → Y) :
    ∏ i : Fin n, ∑ z : Z, W.trans (x i) (y i, z) ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg (fun z _ => W.nonneg _ _))
    (fun i _ => marginalY_le_one W (x i) (y i))

theorem channelPow_sum {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    {n : ℕ} (x : Fin n → Bool) :
    ∑ y : Fin n → Y, ∏ i : Fin n, ∑ z : Z, W.trans (x i) (y i, z) = 1 := by
  rw [← Fintype.prod_sum (fun i b => ∑ z : Z, W.trans (x i) (b, z))]
  exact Finset.prod_eq_one (fun i _ => marginalY_sum W (x i))

/-! ### The maximal message count -/

/-- Disjoint decoding regions: a code with maximal error `≤ ε` has `m (1 - ε) ≤ kYⁿ`. -/
theorem count_bound {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    {n m K : ℕ} (ε : ℝ) (enc : Fin K → Fin m → Fin n → Bool) (dec : Fin K → (Fin n → Y) → Fin m)
    (hK : 0 < K)
    (herr : ∀ (s : Fin K) (w : Fin m),
      (∑ y : Fin n → Y, if dec s y ≠ w then
        ∏ i : Fin n, ∑ z : Z, W.trans (enc s w i) (y i, z) else 0) ≤ ε) :
    (m : ℝ) * (1 - ε) ≤ (Fintype.card (Fin n → Y) : ℝ) := by
  set s0 : Fin K := ⟨0, hK⟩
  have hcorr : ∀ w : Fin m, 1 - ε ≤ ∑ y : Fin n → Y,
      if dec s0 y = w then ∏ i : Fin n, ∑ z : Z, W.trans (enc s0 w i) (y i, z) else 0 := by
    intro w
    have hsplit := channelPow_sum W (enc s0 w)
    have h2 : (∑ y : Fin n → Y, ∏ i : Fin n, ∑ z : Z, W.trans (enc s0 w i) (y i, z)) =
        (∑ y : Fin n → Y, if dec s0 y ≠ w then
          ∏ i : Fin n, ∑ z : Z, W.trans (enc s0 w i) (y i, z) else 0) +
        (∑ y : Fin n → Y, if dec s0 y = w then
          ∏ i : Fin n, ∑ z : Z, W.trans (enc s0 w i) (y i, z) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : dec s0 y = w <;> simp [h]
    have := herr s0 w
    linarith
  calc (m : ℝ) * (1 - ε) = ∑ w : Fin m, (1 - ε) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ w : Fin m, ∑ y : Fin n → Y,
        (if dec s0 y = w then ∏ i : Fin n, ∑ z : Z, W.trans (enc s0 w i) (y i, z) else 0) :=
        Finset.sum_le_sum (fun w _ => hcorr w)
    _ ≤ ∑ w : Fin m, ∑ y : Fin n → Y, (if dec s0 y = w then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun y _ => ?_))
        split_ifs
        · exact channelPow_le_one W _ _
        · exact le_rfl
    _ = (Fintype.card (Fin n → Y) : ℝ) := by
        rw [Finset.sum_comm]
        simp [Finset.sum_ite_eq]

theorem covertSet_bddAbove {Y Z : Type*} [Fintype Y] [Fintype Z] (W : WiretapChannel Bool Y Z)
    (n : ℕ) (ε δ α : ℝ) (hε1 : ε < 1) :
    BddAbove { r : ℝ | ∃ (m K : ℕ) (enc : Fin K → Fin m → Fin n → Bool)
      (dec : Fin K → (Fin n → Y) → Fin m),
      0 < m ∧ 0 < K ∧ r = (m : ℝ) ∧
      (∀ (s : Fin K) (w : Fin m),
        (∑ y : Fin n → Y, if dec s y ≠ w then
          ∏ i : Fin n, ∑ z : Z, W.trans (enc s w i) (y i, z) else 0) ≤ ε) ∧
      let qZ (z : Fin n → Z) : ℝ := ((1 : ℝ) / ((m * K : ℕ) : ℝ)) *
        ∑ s : Fin K, ∑ w : Fin m, ∏ i : Fin n, ∑ y : Y, W.trans (enc s w i) (y, z i)
      let q0Pow (z : Fin n → Z) : ℝ := ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i)
      1 - α - δ ≤ betaAlpha α q0Pow qZ } := by
  refine ⟨(Fintype.card (Fin n → Y) : ℝ) / (1 - ε), ?_⟩
  rintro r ⟨m, K, enc, dec, hm, hK, rfl, herr, -⟩
  rw [le_div_iff₀ (by linarith)]
  exact count_bound W ε enc dec hK herr

theorem one_le_covertMaxMessagesBeta {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : WiretapChannel Bool Y Z) (n : ℕ) (ε δ α : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ) : 1 ≤ covertMaxMessagesBeta W n ε δ α := by
  unfold covertMaxMessagesBeta
  apply le_csSup (covertSet_bddAbove W n ε δ α hε1)
  refine ⟨1, 1, fun _ _ _ => false, fun _ _ => 0, one_pos, one_pos, by simp, ?_, ?_⟩
  · intro s w
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    simp [hε0]
  · show 1 - α - δ ≤ betaAlpha α _ _
    have hq : ∑ z : Fin n → Z, ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i) = 1 :=
      prodPmf_sum_one n (fun z => ∑ y : Y, W.trans false (y, z)) (marginalZ_sum W false)
    have h := betaAlpha_self α hα
      (fun z : Fin n → Z => ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i)) hq
    have heq : (fun z : Fin n → Z => ((1 : ℝ) / ((1 * 1 : ℕ) : ℝ)) *
        ∑ s : Fin 1, ∑ w : Fin 1, ∏ i : Fin n, ∑ y : Y,
          W.trans ((fun (_ : Fin 1) (_ : Fin 1) (_ : Fin n) => false) s w i) (y, z i)) =
        (fun z : Fin n → Z => ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i)) := by
      funext z; simp
    rw [heq]
    linarith

theorem covertMaxMessagesBeta_le {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : WiretapChannel Bool Y Z) (n : ℕ) (ε δ α : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ) :
    covertMaxMessagesBeta W n ε δ α ≤ (Fintype.card (Fin n → Y) : ℝ) / (1 - ε) := by
  have h1 := one_le_covertMaxMessagesBeta W n ε δ α hε0 hε1 hα hδ
  unfold covertMaxMessagesBeta at h1 ⊢
  apply csSup_le
  · by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty] at h1
    linarith
  · rintro r ⟨m, K, enc, dec, hm, hK, rfl, herr, -⟩
    rw [le_div_iff₀ (by linarith)]
    exact count_bound W ε enc dec hK herr

theorem log2_covertMax_nonneg {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : WiretapChannel Bool Y Z) (n : ℕ) (ε δ α : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ) : 0 ≤ log2 (covertMaxMessagesBeta W n ε δ α) :=
  div_nonneg (Real.log_nonneg (one_le_covertMaxMessagesBeta W n ε δ α hε0 hε1 hα hδ))
    (Real.log_pos one_lt_two).le

/-! ### `χ²(Q₁ ‖ Q₀) > 0` under the hypotheses of `Statement` -/

theorem chiSqFn_pos {Z : Type*} [Fintype Z] (Q1 Q0 : Z → ℝ) (h0 : ∀ z, 0 ≤ Q0 z)
    (hac : ∀ z, Q0 z = 0 → Q1 z = 0) (hne : ∃ z, Q1 z ≠ Q0 z) : 0 < chiSqFn Q1 Q0 := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hpos : 0 < Q0 z₀ := by
    rcases (h0 z₀).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hac z₀ h.symm, ← h]) hz₀
  have hterm : ∀ z, 0 ≤ (if Q0 z ≤ 0 then 0 else (Q1 z - Q0 z) ^ 2 / Q0 z) := by
    intro z; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (sq_nonneg _) (lt_of_not_ge h).le
  unfold chiSqFn
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun z _ => hterm z) (Finset.mem_univ z₀))
  rw [if_neg (not_le.2 hpos)]
  exact div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hz₀)))) hpos

end InfoTheory.Known.Certificates.CovertCommunicationSecondOrder
