import InfoTheory.Bridge.CoverThomas

/-!
# Method of Types, Sanov's Theorem, Log-Sum Inequality & Csiszár's Sum Identity

Purely additive, kernel-verified foundational theorems built directly on top of
`InfoTheory.Bridge.CoverThomas` and `InfoTheory.Bridge.Mathlib`:

1. **Log-Sum Inequality & Convexity (Cover & Thomas, Theorems 2.7.1–2.7.3)**:
   - `log_sum_inequality`
   - `probMix`, `klDivergence_convex`, `shannonEntropy_concave`
2. **Csiszár's Sum Identity (El Gamal–Kim, §2.3)**:
   - `prefixVec`, `suffixVec`, `csiszar_sum_identity`
3. **Method of Types & Sanov's Theorem (Cover & Thomas, §§11.1–11.4)**:
   - `typeCount`, `empiricalType`, `typeClass`, `typesSet`
   - `card_typesSet_le` (Theorem 11.1.1 — polynomial number of types `|𝒫_n(α)| ≤ (n + 1)^{|α|}`)
   - `iidDist_pmf_eq_type` (Theorem 11.1.2 — `Q^n(x) = 2^{-n(H(P_x) + D(P_x ‖ Q))}`)
   - `typeClass_card_le`, `typeClass_card_ge` (Theorem 11.1.3 — `|T(P)| ≍ 2^{n H(P)}`)
   - `typeClass_prob_le`, `typeClass_prob_ge` (Theorem 11.1.4 — `Q^n(T(P)) ≍ 2^{-n D(P ‖ Q)}`)
   - `sanov_upper_bound` (Theorem 11.4.1 — Sanov's Theorem)

All theorems leave `Core/`, `Problems/`, `STATEMENT_LOCK.json`, `Known/`, and all other
`Bridge/` files untouched.
-/

open scoped BigOperators Nat
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Log-Sum Inequality & Convexity (Cover & Thomas, Theorems 2.7.1–2.7.3) -/

section LogSumConvexity

/-- **Log-Sum Inequality** (Cover & Thomas, Theorem 2.7.1):
    for any finite index set `s` and nonnegative sequences `a, b : ι → ℝ` with
    `b i = 0 → a i = 0` on `s`,
    `(∑ a_i) log₂ ((∑ a_i) / (∑ b_i)) ≤ ∑ a_i log₂ (a_i / b_i)`. -/
theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hac : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log2 ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, if a i ≤ 0 then 0 else a i * log2 (a i / b i) := by
  set A := ∑ i ∈ s, a i
  set B := ∑ i ∈ s, b i
  have hA0 : 0 ≤ A := Finset.sum_nonneg ha
  have hB0 : 0 ≤ B := Finset.sum_nonneg hb
  by_cases hAzero : A = 0
  · have ha_all : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).mp hAzero
    have hrhs : (∑ i ∈ s, if a i ≤ 0 then (0 : ℝ) else a i * log2 (a i / b i)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      simp [ha_all i hi]
    rw [hAzero, zero_mul, hrhs]
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAzero)
    have hBpos : 0 < B := by
      by_contra hBle
      have hBzero : B = 0 := le_antisymm (not_lt.mp hBle) hB0
      have hb_all : ∀ i ∈ s, b i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hb).mp hBzero
      have hAzero' : A = 0 := Finset.sum_eq_zero fun i hi => hac i hi (hb_all i hi)
      exact hAzero hAzero'
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hterm : ∀ i ∈ s,
        a i - (A / B) * b i ≤
          (if a i ≤ 0 then (0 : ℝ) else a i * Real.log (a i / b i)) - a i * Real.log (A / B) := by
      intro i hi
      by_cases hai : a i ≤ 0
      · have ha0 : a i = 0 := le_antisymm hai (ha i hi)
        simp only [ha0, le_refl, ↓reduceIte, zero_mul, zero_sub]
        have : 0 ≤ (A / B) * b i := mul_nonneg (div_nonneg hA0 hB0) (hb i hi)
        linarith
      · have hapos : 0 < a i := lt_of_not_ge hai
        have hbpos : 0 < b i := lt_of_le_of_ne (hb i hi) fun h => by
          have := hac i hi h.symm
          linarith
        simp only [ite_eq_right_iff.mpr (fun h => absurd h hai)]
        have hxpos : 0 < (A * b i) / (B * a i) := by positivity
        have hlog := Real.log_le_sub_one_of_pos hxpos
        have hlog_eq : Real.log ((A * b i) / (B * a i)) =
            Real.log (A / B) - Real.log (a i / b i) := by
          have hrew : (A * b i) / (B * a i) = (A / B) / (a i / b i) := by
            field_simp [ne_of_gt hBpos, ne_of_gt hapos, ne_of_gt hbpos]
          rw [hrew, Real.log_div (ne_of_gt (div_pos hApos hBpos)) (ne_of_gt (div_pos hapos hbpos))]
        rw [hlog_eq] at hlog
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hapos)
        have hrhs_eq : a i * ((A * b i) / (B * a i) - 1) = (A / B) * b i - a i := by
          field_simp [ne_of_gt hBpos, ne_of_gt hapos]
        rw [hrhs_eq] at hmul
        linarith
    have hsum := Finset.sum_le_sum hterm
    have hlhs_sum : ∑ i ∈ s, (a i - (A / B) * b i) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      change A - (A / B) * B = 0
      field_simp [ne_of_gt hBpos]
      ring
    have hrhs_sum : ∑ i ∈ s, ((if a i ≤ 0 then (0 : ℝ) else a i * Real.log (a i / b i)) -
        a i * Real.log (A / B)) =
        (∑ i ∈ s, if a i ≤ 0 then (0 : ℝ) else a i * Real.log (a i / b i)) - A * Real.log (A / B) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hlhs_sum, hrhs_sum] at hsum
    have hnat_log : A * Real.log (A / B) ≤
        ∑ i ∈ s, if a i ≤ 0 then (0 : ℝ) else a i * Real.log (a i / b i) := by linarith
    have hdiv := div_le_div_of_nonneg_right hnat_log (le_of_lt hlog2pos)
    unfold log2
    calc A * (Real.log (A / B) / Real.log 2)
      _ = (A * Real.log (A / B)) / Real.log 2 := by ring
      _ ≤ (∑ i ∈ s, if a i ≤ 0 then (0 : ℝ) else a i * Real.log (a i / b i)) / Real.log 2 := hdiv
      _ = ∑ i ∈ s, (if a i ≤ 0 then (0 : ℝ) else a i * Real.log (a i / b i)) / Real.log 2 :=
          Finset.sum_div _ _ _
      _ = ∑ i ∈ s, if a i ≤ 0 then (0 : ℝ) else a i * (Real.log (a i / b i) / Real.log 2) :=
          Finset.sum_congr rfl fun i _ => by split_ifs <;> simp [mul_div_assoc]

/-- Convex mixture of two finite distributions:
    `(probMix t ht0 ht1 P₁ P₂).pmf a = t * P₁.pmf a + (1 - t) * P₂.pmf a`. -/
def probMix {α : Type*} [Fintype α] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ P₂ : ProbDist α) : ProbDist α where
  pmf := fun a => t * P₁.pmf a + (1 - t) * P₂.pmf a
  nonneg := fun a => add_nonneg (mul_nonneg ht0 (P₁.nonneg a)) (mul_nonneg (by linarith) (P₂.nonneg a))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, P₁.sum_one, P₂.sum_one]
    ring

/-- **Joint Convexity of Relative Entropy** (Cover & Thomas, Theorem 2.7.2):
    for `t ∈ [0, 1]`, `P₁ ≪ Q₁`, and `P₂ ≪ Q₂`,
    `D(t P₁ + (1 - t) P₂ ‖ t Q₁ + (1 - t) Q₂) ≤ t D(P₁ ‖ Q₁) + (1 - t) D(P₂ ‖ Q₂)`. -/
theorem klDivergence_convex {α : Type*} [Fintype α]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P₁ Q₁ P₂ Q₂ : ProbDist α) (hac₁ : AbsCont P₁ Q₁) (hac₂ : AbsCont P₂ Q₂) :
    klDivergence (probMix t ht0 ht1 P₁ P₂) (probMix t ht0 ht1 Q₁ Q₂) ≤
      t * klDivergence P₁ Q₁ + (1 - t) * klDivergence P₂ Q₂ := by
  have h1mt : 0 ≤ 1 - t := by linarith
  have hpoint : ∀ a : α,
      (if (probMix t ht0 ht1 P₁ P₂).pmf a ≤ 0 then (0 : ℝ)
       else (probMix t ht0 ht1 P₁ P₂).pmf a *
         log2 ((probMix t ht0 ht1 P₁ P₂).pmf a / (probMix t ht0 ht1 Q₁ Q₂).pmf a)) ≤
      t * (if P₁.pmf a ≤ 0 then (0 : ℝ) else P₁.pmf a * log2 (P₁.pmf a / Q₁.pmf a)) +
      (1 - t) * (if P₂.pmf a ≤ 0 then (0 : ℝ) else P₂.pmf a * log2 (P₂.pmf a / Q₂.pmf a)) := by
    intro a
    let u : Bool → ℝ := fun b => if b then t * P₁.pmf a else (1 - t) * P₂.pmf a
    let v : Bool → ℝ := fun b => if b then t * Q₁.pmf a else (1 - t) * Q₂.pmf a
    have hu : ∀ b ∈ (Finset.univ : Finset Bool), 0 ≤ u b := fun b _ => by
      cases b <;> simp [u]
      · exact mul_nonneg h1mt (P₂.nonneg a)
      · exact mul_nonneg ht0 (P₁.nonneg a)
    have hv : ∀ b ∈ (Finset.univ : Finset Bool), 0 ≤ v b := fun b _ => by
      cases b <;> simp [v]
      · exact mul_nonneg h1mt (Q₂.nonneg a)
      · exact mul_nonneg ht0 (Q₁.nonneg a)
    have huv : ∀ b ∈ (Finset.univ : Finset Bool), v b = 0 → u b = 0 := fun b _ hvb => by
      cases b
      · simp only [v, u, Bool.false_eq_true, ↓reduceIte, mul_eq_zero] at hvb ⊢
        rcases hvb with h | h
        · exact Or.inl h
        · exact Or.inr (hac₂ a h)
      · simp only [v, u, ↓reduceIte, mul_eq_zero] at hvb ⊢
        rcases hvb with h | h
        · exact Or.inl h
        · exact Or.inr (hac₁ a h)
    have hls := log_sum_inequality (Finset.univ : Finset Bool) u v hu hv huv
    simp only [Fintype.sum_bool, u, v, ↓reduceIte, Bool.false_eq_true] at hls
    have hterm1 : (if t * P₁.pmf a ≤ 0 then (0 : ℝ)
        else t * P₁.pmf a * log2 (t * P₁.pmf a / (t * Q₁.pmf a))) =
        t * (if P₁.pmf a ≤ 0 then (0 : ℝ) else P₁.pmf a * log2 (P₁.pmf a / Q₁.pmf a)) := by
      by_cases ht : t = 0
      · simp [ht]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        by_cases hp : P₁.pmf a ≤ 0
        · have hp0 : P₁.pmf a = 0 := le_antisymm hp (P₁.nonneg a)
          simp [hp0]
        · have htp : ¬ (t * P₁.pmf a ≤ 0) := not_le.mpr (mul_pos htpos (lt_of_not_ge hp))
          simp only [ite_eq_right_iff.mpr (fun h => absurd h htp),
            ite_eq_right_iff.mpr (fun h => absurd h hp)]
          rw [mul_div_mul_left _ _ ht, mul_assoc]
    have hterm2 : (if (1 - t) * P₂.pmf a ≤ 0 then (0 : ℝ)
        else (1 - t) * P₂.pmf a * log2 ((1 - t) * P₂.pmf a / ((1 - t) * Q₂.pmf a))) =
        (1 - t) * (if P₂.pmf a ≤ 0 then (0 : ℝ) else P₂.pmf a * log2 (P₂.pmf a / Q₂.pmf a)) := by
      by_cases ht : 1 - t = 0
      · simp [ht]
      · have htpos : 0 < 1 - t := lt_of_le_of_ne h1mt (Ne.symm ht)
        by_cases hp : P₂.pmf a ≤ 0
        · have hp0 : P₂.pmf a = 0 := le_antisymm hp (P₂.nonneg a)
          simp [hp0]
        · have htp : ¬ ((1 - t) * P₂.pmf a ≤ 0) := not_le.mpr (mul_pos htpos (lt_of_not_ge hp))
          simp only [ite_eq_right_iff.mpr (fun h => absurd h htp),
            ite_eq_right_iff.mpr (fun h => absurd h hp)]
          rw [mul_div_mul_left _ _ ht, mul_assoc]
    rw [hterm1, hterm2] at hls
    have hlhs : (if (probMix t ht0 ht1 P₁ P₂).pmf a ≤ 0 then (0 : ℝ)
        else (probMix t ht0 ht1 P₁ P₂).pmf a *
          log2 ((probMix t ht0 ht1 P₁ P₂).pmf a / (probMix t ht0 ht1 Q₁ Q₂).pmf a)) =
        (t * P₁.pmf a + (1 - t) * P₂.pmf a) *
          log2 ((t * P₁.pmf a + (1 - t) * P₂.pmf a) / (t * Q₁.pmf a + (1 - t) * Q₂.pmf a)) := by
      change (if t * P₁.pmf a + (1 - t) * P₂.pmf a ≤ 0 then (0 : ℝ) else _) = _
      by_cases h : t * P₁.pmf a + (1 - t) * P₂.pmf a ≤ 0
      · have h0 : t * P₁.pmf a + (1 - t) * P₂.pmf a = 0 :=
          le_antisymm h ((probMix t ht0 ht1 P₁ P₂).nonneg a)
        simp [h0]
      · simp [h, probMix]
    rw [hlhs]
    exact hls
  unfold klDivergence
  calc ∑ a : α, (if (probMix t ht0 ht1 P₁ P₂).pmf a ≤ 0 then (0 : ℝ)
        else (probMix t ht0 ht1 P₁ P₂).pmf a *
          log2 ((probMix t ht0 ht1 P₁ P₂).pmf a / (probMix t ht0 ht1 Q₁ Q₂).pmf a))
    _ ≤ ∑ a : α, (t * (if P₁.pmf a ≤ 0 then (0 : ℝ) else P₁.pmf a * log2 (P₁.pmf a / Q₁.pmf a)) +
          (1 - t) * (if P₂.pmf a ≤ 0 then (0 : ℝ) else P₂.pmf a * log2 (P₂.pmf a / Q₂.pmf a))) :=
        Finset.sum_le_sum fun a _ => hpoint a
    _ = t * (∑ a : α, if P₁.pmf a ≤ 0 then (0 : ℝ) else P₁.pmf a * log2 (P₁.pmf a / Q₁.pmf a)) +
        (1 - t) * (∑ a : α, if P₂.pmf a ≤ 0 then (0 : ℝ) else P₂.pmf a * log2 (P₂.pmf a / Q₂.pmf a)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Concavity of Shannon Entropy** (Cover & Thomas, Theorem 2.7.3):
    for `t ∈ [0, 1]` and any `P₁, P₂ : ProbDist α`,
    `t H(P₁) + (1 - t) H(P₂) ≤ H(t P₁ + (1 - t) P₂)`. -/
theorem shannonEntropy_concave {α : Type*} [Fintype α]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (P₁ P₂ : ProbDist α) :
    t * shannonEntropy P₁ + (1 - t) * shannonEntropy P₂ ≤
      shannonEntropy (probMix t ht0 ht1 P₁ P₂) := by
  by_cases hne : Nonempty α
  · have hunif : probMix t ht0 ht1 (ProbDist.uniform (α := α)) ProbDist.uniform =
        ProbDist.uniform := by
      unfold probMix ProbDist.uniform
      congr
      funext _
      ring
    have hconv := klDivergence_convex t ht0 ht1 P₁ ProbDist.uniform P₂ ProbDist.uniform
      (absCont_uniform P₁) (absCont_uniform P₂)
    rw [hunif, klDivergence_uniform, klDivergence_uniform, klDivergence_uniform] at hconv
    linarith
  · have : IsEmpty α := not_nonempty_iff.mp hne
    simp [shannonEntropy]

end LogSumConvexity

/-! ### 2. Csiszár's Sum Identity (El Gamal–Kim, §2.3) -/

section CsiszarSumIdentity

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Prefix `x^{i-1} = (x_0, …, x_{i-1})` of a length-`n` vector at index `i : Fin n`. -/
def prefixVec {n : ℕ} (i : Fin n) (x : Fin n → α) : Fin i.1 → α :=
  fun j => x ⟨j.1, lt_trans j.2 i.2⟩

/-- Suffix `y_{i+1}^n = (y_{i+1}, …, y_{n-1})` of a length-`n` vector at index `i : Fin n`. -/
def suffixVec {n : ℕ} (i : Fin n) (y : Fin n → β) : Fin (n - 1 - i.1) → β :=
  fun j => y ⟨i.1 + 1 + j.1, by omega⟩

private lemma sum_fin_telescope (n : ℕ) (h : ℕ → ℝ) :
    ∑ i : Fin n, (h (i.1 + 1) - h i.1) = h n - h 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

private lemma shannonEntropy_eq_zero_of_unique {γ : Type*} [Fintype γ] [Unique γ]
    (P : ProbDist γ) : shannonEntropy P = 0 := by
  have hle := shannonEntropy_le_log2_card P
  have hge := shannonEntropy_nonneg P
  rw [Fintype.card_unique] at hle
  simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
  exact le_antisymm hle hge

/-- **Csiszár's Sum Identity** (El Gamal–Kim, §2.3):
    for any joint distribution `P` on `(Fin n → α) × (Fin n → β)`,
    `∑_{i=0}^{n-1} I(X_i; Y_{i+1}^n | X^{i-1}) = ∑_{i=0}^{n-1} I(X^{i-1}; Y_i | Y_{i+1}^n)`. -/
theorem csiszar_sum_identity {n : ℕ} (P : ProbDist ((Fin n → α) × (Fin n → β))) :
    ∑ i : Fin n, condMutualInfo (P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1))) =
      ∑ i : Fin n, condMutualInfo (P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2))) := by
  -- Define the three telescoping entropy sequences for `k ≤ n`:
  -- `hX k = H(X_{<k})`, `hY k = H(Y_{≥k})`, `hXY k = H(X_{<k}, Y_{≥k})`.
  let pref : ∀ (k : ℕ), k ≤ n → (Fin n → α) → (Fin k → α) :=
    fun _ hk x j => x ⟨j.1, lt_of_lt_of_le j.2 hk⟩
  let suff : ∀ (k : ℕ), k ≤ n → (Fin n → β) → (Fin (n - k) → β) :=
    fun k _ y j => y ⟨k + j.1, by omega⟩
  let hX : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun xy => pref k hk xy.1)) else 0
  let hY : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun xy => suff k hk xy.2)) else 0
  let hXY : ℕ → ℝ := fun k =>
    if hk : k ≤ n then shannonEntropy (P.map (fun xy => (pref k hk xy.1, suff k hk xy.2))) else 0
  have hterm : ∀ i : Fin n,
      condMutualInfo (P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1))) -
      condMutualInfo (P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2))) =
      (hX (i.1 + 1) - hX i.1) + (hY (i.1 + 1) - hY i.1) - (hXY (i.1 + 1) - hXY i.1) := by
    intro i
    have hi_le : i.1 ≤ n := le_of_lt i.2
    have hi1_le : i.1 + 1 ≤ n := i.2
    -- Bijection `α × (Fin i.1 → α) ≃ (Fin (i.1 + 1) → α)`
    let ePref : (α × (Fin i.1 → α)) ≃ (Fin (i.1 + 1) → α) :=
      { toFun := fun af j => if h : j.1 < i.1 then af.2 ⟨j.1, h⟩ else af.1
        invFun := fun g => (g ⟨i.1, Nat.lt_succ_self _⟩, fun j => g ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
        left_inv := fun ⟨a, f⟩ => by
          ext
          · simp
          · rename_i j; simp [j.2]
        right_inv := fun g => by
          funext j; dsimp only
          split_ifs with h
          · rfl
          · congr 1; apply Fin.ext; dsimp only; omega }
    -- Bijection `β × (Fin (n - 1 - i.1) → β) ≃ (Fin (n - i.1) → β)`
    let eSuff : (β × (Fin (n - 1 - i.1) → β)) ≃ (Fin (n - i.1) → β) :=
      { toFun := fun bg j => if h : j.1 = 0 then bg.1 else bg.2 ⟨j.1 - 1, by omega⟩
        invFun := fun g => (g ⟨0, by omega⟩, fun j => g ⟨j.1 + 1, by omega⟩)
        left_inv := fun ⟨b, g⟩ => by
          ext
          · simp
          · rename_i j; simp
        right_inv := fun g => by
          funext j; dsimp only
          split_ifs with h
          · congr 1; exact Fin.ext h.symm
          · congr 1; apply Fin.ext; dsimp only; omega }
    -- Cast `Fin (n - 1 - i.1) ≃ Fin (n - (i.1 + 1))`
    let eLen : (Fin (n - 1 - i.1) → β) ≃ (Fin (n - (i.1 + 1)) → β) :=
      { toFun := fun g j => g ⟨j.1, by omega⟩
        invFun := fun g j => g ⟨j.1, by omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    -- Bijection for `(X_i, Y_{>i}, X_{<i}) ≃ (X_{<i+1}, Y_{≥i+1})`
    let eL : (α × (Fin (n - 1 - i.1) → β) × (Fin i.1 → α)) ≃
        ((Fin (i.1 + 1) → α) × (Fin (n - (i.1 + 1)) → β)) :=
      { toFun := fun t => (ePref (t.1, t.2.2), eLen t.2.1)
        invFun := fun pq => ((ePref.symm pq.1).1, eLen.symm pq.2, (ePref.symm pq.1).2)
        left_inv := fun ⟨a, y, x⟩ => by simp
        right_inv := fun ⟨p, q⟩ => by simp }
    -- Bijection for `(X_{<i}, Y_i, Y_{>i}) ≃ (X_{<i}, Y_{≥i})`
    let eR : ((Fin i.1 → α) × β × (Fin (n - 1 - i.1) → β)) ≃
        ((Fin i.1 → α) × (Fin (n - i.1) → β)) :=
      { toFun := fun t => (t.1, eSuff (t.2.1, t.2.2))
        invFun := fun pq => (pq.1, (eSuff.symm pq.2).1, (eSuff.symm pq.2).2)
        left_inv := fun ⟨x, b, y⟩ => by simp
        right_inv := fun ⟨p, q⟩ => by simp }
    -- Identify every entropy term in `condMutualInfo` for LHS and RHS
    have hL_xz : shannonEntropy ((P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1))).map
        (fun t => (t.1, t.2.2))) = hX (i.1 + 1) := by
      simp only [hX, hi1_le, ↓reduceDIte]
      rw [← shannonEntropy_map_equiv ePref, map_comp_eq, map_comp_eq]
      congr 2; funext xy; funext j
      dsimp [ePref, prefixVec, pref]
      split_ifs with h
      · rfl
      · exact congrArg xy.1 (Fin.ext (by dsimp only; omega))
    have hL_z : shannonEntropy ((P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1))).map
        (fun t => t.2.2)) = hX i.1 := by
      simp only [hX, hi_le, ↓reduceDIte]
      rw [map_comp_eq]; rfl
    have hL_xyz : shannonEntropy (P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1))) =
        hXY (i.1 + 1) := by
      simp only [hXY, hi1_le, ↓reduceDIte]
      rw [← shannonEntropy_map_equiv eL, map_comp_eq]
      congr 2; funext xy
      apply Prod.ext
      · funext j; dsimp [eL, ePref, prefixVec, pref]
        split_ifs with h
        · rfl
        · exact congrArg xy.1 (Fin.ext (by dsimp only; omega))
      · funext j; rfl
    have hR_yz : shannonEntropy ((P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2))).map
        (fun t => (t.2.1, t.2.2))) = hY i.1 := by
      simp only [hY, hi_le, ↓reduceDIte]
      rw [← shannonEntropy_map_equiv eSuff, map_comp_eq, map_comp_eq]
      congr 2; funext xy; funext j
      dsimp [eSuff, suffixVec, suff]
      split_ifs with h
      · exact congrArg xy.2 (Fin.ext (by dsimp only; omega))
      · exact congrArg xy.2 (Fin.ext (by dsimp only; omega))
    have hR_z : shannonEntropy ((P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2))).map
        (fun t => t.2.2)) = hY (i.1 + 1) := by
      simp only [hY, hi1_le, ↓reduceDIte]
      rw [← shannonEntropy_map_equiv eLen, map_comp_eq, map_comp_eq]
      rfl
    have hR_xyz : shannonEntropy (P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2))) =
        hXY i.1 := by
      simp only [hXY, hi_le, ↓reduceDIte]
      rw [← shannonEntropy_map_equiv eR, map_comp_eq]
      congr 2; funext xy
      apply Prod.ext
      · rfl
      · funext j; dsimp [eR, eSuff, suffixVec, suff]
        split_ifs with h
        · exact congrArg xy.2 (Fin.ext (by dsimp only; omega))
        · exact congrArg xy.2 (Fin.ext (by dsimp only; omega))
    have hCross : shannonEntropy ((P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1))).map
        (fun t => (t.2.1, t.2.2))) =
        shannonEntropy ((P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2))).map
          (fun t => (t.1, t.2.2))) := by
      rw [← shannonEntropy_swap, map_comp_eq, map_comp_eq, map_comp_eq]
      rfl
    unfold condMutualInfo
    dsimp only
    rw [hL_xz, hL_z, hL_xyz, hR_yz, hR_z, hR_xyz, hCross]
    ring
  -- Boundary values of `hX`, `hY`, `hXY` at `0` and `n`
  have hX0 : hX 0 = 0 := by
    simp only [hX, Nat.zero_le, ↓reduceDIte]
    exact shannonEntropy_eq_zero_of_unique _
  have hYn : hY n = 0 := by
    simp only [hY, le_refl, ↓reduceDIte]
    have : Unique (Fin (n - n) → β) :=
      ⟨⟨fun j => absurd j.2 (by omega)⟩, fun f => funext fun j => absurd j.2 (by omega)⟩
    exact shannonEntropy_eq_zero_of_unique _
  have hXY0 : hXY 0 = hY 0 := by
    simp only [hXY, hY, Nat.zero_le, ↓reduceDIte]
    let e0 : ((Fin 0 → α) × (Fin (n - 0) → β)) ≃ (Fin (n - 0) → β) :=
      { toFun := Prod.snd
        invFun := fun y => (fun j => Fin.elim0 j, y)
        left_inv := fun ⟨x, y⟩ => by ext j; exact Fin.elim0 j; rfl
        right_inv := fun _ => rfl }
    rw [← shannonEntropy_map_equiv e0, map_comp_eq]
    rfl
  have hXYn : hXY n = hX n := by
    simp only [hXY, hX, le_refl, ↓reduceDIte]
    let en : ((Fin n → α) × (Fin (n - n) → β)) ≃ (Fin n → α) :=
      { toFun := Prod.fst
        invFun := fun x => (x, fun j => absurd j.2 (by omega))
        left_inv := fun ⟨x, y⟩ => by ext j; rfl; exact absurd j.2 (by omega)
        right_inv := fun _ => rfl }
    rw [← shannonEntropy_map_equiv en, map_comp_eq]
    rfl
  have hdiff : (∑ i : Fin n, condMutualInfo (P.map (fun xy => (xy.1 i, suffixVec i xy.2, prefixVec i xy.1)))) -
      (∑ i : Fin n, condMutualInfo (P.map (fun xy => (prefixVec i xy.1, xy.2 i, suffixVec i xy.2)))) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      sum_fin_telescope n hX, sum_fin_telescope n hY, sum_fin_telescope n hXY,
      hX0, hYn, hXY0, hXYn]
    ring
  linarith

end CsiszarSumIdentity

/-! ### 3. Method of Types & Sanov's Theorem (Cover & Thomas, §§11.1–11.4) -/

section MethodOfTypes

variable {α : Type*} [Fintype α]

/-- Empirical count `N(a | x) = |{i : Fin n | x i = a}|` of symbol `a` in sequence `x`. -/
noncomputable def typeCount {n : ℕ} (x : Fin n → α) (a : α) : ℕ :=
  by classical exact (Finset.univ.filter (fun i : Fin n => x i = a)).card

omit [Fintype α] in
private lemma typeCount_eq_card [DecidableEq α] {n : ℕ} (x : Fin n → α) (a : α) :
    typeCount x a = (Finset.univ.filter (fun i : Fin n => x i = a)).card := by
  unfold typeCount; congr

private lemma sum_typeCount {n : ℕ} (x : Fin n → α) :
    ∑ a : α, typeCount x a = n := by
  classical
  simp_rw [typeCount_eq_card]
  rw [← Finset.card_biUnion]
  · have huniv : Finset.univ.biUnion (fun a : α => Finset.univ.filter (fun i : Fin n => x i = a)) =
        (Finset.univ : Finset (Fin n)) := by
      ext i; simp
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hab (ha.symm.trans hb)

omit [Fintype α] in
private lemma typeCount_le {n : ℕ} (x : Fin n → α) (a : α) : typeCount x a ≤ n := by
  classical
  rw [typeCount_eq_card]
  calc (Finset.univ.filter (fun i : Fin n => x i = a)).card
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Empirical type (empirical distribution) `P_x` of a sequence `x : Fin n → α` for `n > 0`. -/
noncomputable def empiricalType {n : ℕ} (hn : 0 < n) (x : Fin n → α) : ProbDist α where
  pmf := fun a => (typeCount x a : ℝ) / (n : ℝ)
  nonneg := fun a => by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_typeCount,
      div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

/-- Type class `T(P) = {x : Fin n → α | P_x = P}` of sequences with empirical type `P`. -/
noncomputable def typeClass {n : ℕ} (hn : 0 < n) (P : ProbDist α) : Finset (Fin n → α) :=
  by classical exact Finset.univ.filter (fun x => empiricalType hn x = P)

/-- Set of all empirical types `𝒫_n(α)` of length-`n` sequences over `α`. -/
noncomputable def typesSet (α : Type*) [Fintype α] {n : ℕ} (hn : 0 < n) : Finset (ProbDist α) :=
  by classical exact Finset.univ.image (empiricalType hn)

private lemma empiricalType_eq_iff {n : ℕ} (hn : 0 < n) (x y : Fin n → α) :
    empiricalType hn x = empiricalType hn y ↔ ∀ a : α, typeCount x a = typeCount y a := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  constructor
  · intro h a
    have hpmf := congrArg (fun P : ProbDist α => P.pmf a) h
    change (typeCount x a : ℝ) / (n : ℝ) = (typeCount y a : ℝ) / (n : ℝ) at hpmf
    have hcast : (typeCount x a : ℝ) = (typeCount y a : ℝ) := by
      exact (div_left_inj₀ hn_ne).mp hpmf
    exact_mod_cast hcast
  · intro h
    cases hx : empiricalType hn x with | mk pmfX _ _ =>
    cases hy : empiricalType hn y with | mk pmfY _ _ =>
    congr
    funext a
    have h1 : pmfX a = (typeCount x a : ℝ) / (n : ℝ) := congrArg (fun P => P.pmf a) hx.symm
    have h2 : pmfY a = (typeCount y a : ℝ) / (n : ℝ) := congrArg (fun P => P.pmf a) hy.symm
    rw [h1, h2, h a]

/-- **Polynomial Number of Types** (Cover & Thomas, Theorem 11.1.1):
    `|𝒫_n(α)| ≤ (n + 1)^{|α|}`. -/
theorem card_typesSet_le (α : Type*) [Fintype α] {n : ℕ} (hn : 0 < n) :
    (typesSet α hn).card ≤ (n + 1) ^ (Fintype.card α) := by
  classical
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  let g : ProbDist α → (α → Fin (n + 1)) := fun P a =>
    ⟨min n ⌊(n : ℝ) * P.pmf a⌋₊, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
  have hg_emp : ∀ (x : Fin n → α) (a : α), (g (empiricalType hn x) a).1 = typeCount x a := by
    intro x a
    change min n ⌊(n : ℝ) * ((typeCount x a : ℝ) / (n : ℝ))⌋₊ = typeCount x a
    rw [mul_div_cancel₀ _ hn_ne, Nat.floor_natCast]
    exact Nat.min_eq_right (typeCount_le x a)
  have hinj : Set.InjOn g (typesSet α hn : Set (ProbDist α)) := by
    intro P₁ hP₁ P₂ hP₂ hEq
    simp only [Finset.mem_coe, typesSet, Finset.mem_image, Finset.mem_univ, true_and] at hP₁ hP₂
    obtain ⟨x₁, rfl⟩ := hP₁
    obtain ⟨x₂, rfl⟩ := hP₂
    rw [empiricalType_eq_iff]
    intro a
    have hval := congrArg (fun f : α → Fin (n + 1) => (f a).1) hEq
    rw [hg_emp x₁ a, hg_emp x₂ a] at hval
    exact hval
  calc (typesSet α hn).card
    _ ≤ (Finset.univ : Finset (α → Fin (n + 1))).card :=
        Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _) hinj
    _ = (n + 1) ^ (Fintype.card α) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

private lemma prod_comp_eq_prod_pow_typeCount {n : ℕ} (x : Fin n → α) (f : α → ℝ) :
    ∏ i : Fin n, f (x i) = ∏ a : α, (f a) ^ (typeCount x a) := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset α))
    (g := x) (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [typeCount_eq_card]
  trans (∏ _i ∈ Finset.univ.filter (fun i : Fin n => x i = a), f a)
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hi]
  · rw [Finset.prod_const]

/-- **Probability of a Sequence via its Type** (Cover & Thomas, Theorem 11.1.2):
    if `P_x ≪ Q`, then `Q^n(x) = 2^{-n (H(P_x) + D(P_x ‖ Q))}`. -/
theorem iidDist_pmf_eq_type {n : ℕ} (hn : 0 < n) (x : Fin n → α) (Q : ProbDist α)
    (hac : AbsCont (empiricalType hn x) Q) :
    (iidDist Q n).pmf x =
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy (empiricalType hn x) +
        klDivergence (empiricalType hn x) Q))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  -- Rewrite exponent as `∑ a, if typeCount x a = 0 then 0 else typeCount x a * log2 (Q.pmf a)`
  have hexp : -((n : ℝ) * (shannonEntropy (empiricalType hn x) +
      klDivergence (empiricalType hn x) Q)) =
      ∑ a : α, if typeCount x a = 0 then (0 : ℝ) else (typeCount x a : ℝ) * log2 (Q.pmf a) := by
    unfold shannonEntropy klDivergence negPLogP
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hc : typeCount x a = 0
    · have hp0 : (empiricalType hn x).pmf a = 0 := by
        change (typeCount x a : ℝ) / (n : ℝ) = 0; simp [hc]
      simp [hc, hp0]
    · have hcpos : (0 : ℝ) < (typeCount x a : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
      have hppos : 0 < (empiricalType hn x).pmf a := div_pos hcpos hn_pos
      have hqpos : 0 < Q.pmf a := lt_of_le_of_ne (Q.nonneg a) fun h => by
        have := hac a h.symm
        linarith
      have hnotle : ¬ ((empiricalType hn x).pmf a ≤ 0) := not_le.mpr hppos
      simp only [hc, ↓reduceIte, ite_eq_right_iff.mpr (fun h => absurd h hnotle)]
      rw [log2_div_pos hppos hqpos]
      have hmul : (n : ℝ) * (empiricalType hn x).pmf a = (typeCount x a : ℝ) := by
        change (n : ℝ) * ((typeCount x a : ℝ) / (n : ℝ)) = (typeCount x a : ℝ)
        exact mul_div_cancel₀ _ hn_ne
      calc -((n : ℝ) * (-(empiricalType hn x).pmf a * log2 ((empiricalType hn x).pmf a) +
              (empiricalType hn x).pmf a * (log2 ((empiricalType hn x).pmf a) - log2 (Q.pmf a))))
        _ = ((n : ℝ) * (empiricalType hn x).pmf a) * log2 (Q.pmf a) := by ring
        _ = (typeCount x a : ℝ) * log2 (Q.pmf a) := by rw [hmul]
  rw [hexp, Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  change ∏ i : Fin n, Q.pmf (x i) = _
  rw [prod_comp_eq_prod_pow_typeCount]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases hc : typeCount x a = 0
  · simp [hc]
  · have hcpos : (0 : ℝ) < (typeCount x a : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
    have hppos : 0 < (empiricalType hn x).pmf a := div_pos hcpos hn_pos
    have hqpos : 0 < Q.pmf a := lt_of_le_of_ne (Q.nonneg a) fun h => by
      have := hac a h.symm
      linarith
    simp only [hc, ↓reduceIte]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), log2]
    have hsimp : Real.log 2 * ((typeCount x a : ℝ) * (Real.log (Q.pmf a) / Real.log 2)) =
        Real.log (Q.pmf a) * (typeCount x a : ℝ) := by
      field_simp [hlog2_ne]
    rw [hsimp, ← Real.rpow_def_of_pos hqpos, Real.rpow_natCast]

private lemma typeClass_prob_eq {n : ℕ} (hn : 0 < n) (P Q : ProbDist α) (hac : AbsCont P Q) :
    ∑ x ∈ typeClass hn P, (iidDist Q n).pmf x =
      ((typeClass hn P).card : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) := by
  classical
  have hconst : ∀ x ∈ typeClass hn P,
      (iidDist Q n).pmf x =
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) := by
    intro x hx
    simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hac' : AbsCont (empiricalType hn x) Q := hx ▸ hac
    rw [iidDist_pmf_eq_type hn x Q hac', hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

private lemma klDivergence_self (P : ProbDist α) : klDivergence P P = 0 :=
  (klDivergence_eq_zero_iff P P (fun _ h => h)).mpr rfl

/-- **Type Class Cardinality Upper Bound** (Cover & Thomas, Theorem 11.1.3):
    `|T(P)| ≤ 2^{n H(P)}`. -/
theorem typeClass_card_le {n : ℕ} (hn : 0 < n) (P : ProbDist α) :
    ((typeClass hn P).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * shannonEntropy P) := by
  have hsum_le : ∑ x ∈ typeClass hn P, (iidDist P n).pmf x ≤ 1 := by
    calc ∑ x ∈ typeClass hn P, (iidDist P n).pmf x
      _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x :=
          Finset.sum_le_univ_sum_of_nonneg fun x => (iidDist P n).nonneg x
      _ = 1 := (iidDist P n).sum_one
  rw [typeClass_prob_eq hn P P (fun _ h => h), klDivergence_self, add_zero] at hsum_le
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * shannonEntropy P) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : (2 : ℝ) ^ (-((n : ℝ) * shannonEntropy P)) *
      (2 : ℝ) ^ ((n : ℝ) * shannonEntropy P) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have h2 := mul_le_mul_of_nonneg_right hsum_le (le_of_lt hpow_pos)
  rw [mul_assoc, hmul, mul_one, one_mul] at h2
  exact h2

/-- Multinomial counting identity for functions `dom → α` with prescribed fiber counts `k`
    supported in `s : Finset α`: `|F| * ∏_{a ∈ s} (k a)! = |dom|!`. -/
private lemma card_multinomial_aux [DecidableEq α] {n : ℕ}
    (s : Finset α) (k : α → ℕ) :
    ∀ (dom : Finset (Fin n)), ∑ a ∈ s, k a = dom.card →
      (Finset.univ.filter (fun x : dom → α =>
        (∀ i, x i ∈ s) ∧ ∀ a ∈ s, (Finset.univ.filter (fun i => x i = a)).card = k a)).card *
        ∏ a ∈ s, (k a)! = (dom.card)! := by
  induction s using Finset.induction_on with
  | empty =>
    intro dom hdom
    simp only [Finset.sum_empty] at hdom
    have hdom_empty : dom = ∅ := Finset.card_eq_zero.mp hdom.symm
    subst hdom_empty
    have : Unique ((∅ : Finset (Fin n)) → α) :=
      ⟨⟨fun i => absurd i.2 (Finset.notMem_empty _)⟩,
       fun f => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
    have hfilt : (Finset.univ.filter (fun x : (∅ : Finset (Fin n)) → α =>
        (∀ i, x i ∈ (∅ : Finset α)) ∧ ∀ a ∈ (∅ : Finset α),
          (Finset.univ.filter (fun i => x i = a)).card = k a)) = Finset.univ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨fun i => absurd i.2 (Finset.notMem_empty _), fun a ha => absurd ha (Finset.notMem_empty _)⟩
    rw [hfilt, Finset.card_univ, Fintype.card_unique, Finset.prod_empty, Finset.card_empty]
    simp
  | @insert a s ha ih =>
    intro dom hdom
    rw [Finset.sum_insert ha] at hdom
    have hka_le : k a ≤ dom.card := by omega
    let F : Finset (dom → α) := Finset.univ.filter (fun x : dom → α =>
      (∀ i, x i ∈ insert a s) ∧ ∀ b ∈ insert a s, (Finset.univ.filter (fun i => x i = b)).card = k b)
    -- Map each `x ∈ F` to the subset `A(x) ⊆ dom` of size `k a` where `x` takes value `a`
    let fiberA : (dom → α) → Finset (Fin n) := fun x =>
      (Finset.univ.filter (fun i : dom => x i = a)).map ⟨Subtype.val, Subtype.val_injective⟩
    have hmaps : ∀ x ∈ F, fiberA x ∈ dom.powersetCard (k a) := by
      intro x hx
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [fiberA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk] at hi
        obtain ⟨⟨j, hj⟩, _, rfl⟩ := hi
        exact hj
      · rw [Finset.card_map]
        exact hx.2 a (Finset.mem_insert_self a s)
    -- For each `A ∈ dom.powersetCard (k a)`, the fiber `{x ∈ F | fiberA x = A}` is in bijection
    -- with the multinomial set on `dom \ A` over `s`.
    have hfiber_card : ∀ A ∈ dom.powersetCard (k a),
        (F.filter (fun x => fiberA x = A)).card =
          (Finset.univ.filter (fun y : (dom \ A : Finset (Fin n)) → α =>
            (∀ i, y i ∈ s) ∧ ∀ b ∈ s, (Finset.univ.filter (fun i => y i = b)).card = k b)).card := by
      intro A hA
      rw [Finset.mem_powersetCard] at hA
      obtain ⟨hA_sub, hA_card⟩ := hA
      refine Finset.card_bij
        (fun x _ i => x ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩)
        ?_ ?_ ?_
      · -- Maps into target set
        intro x hx
        simp only [Finset.mem_filter, F, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨⟨hx_mem, hx_cnt⟩, hfib⟩ := hx
        refine ⟨?_, ?_⟩
        · intro i
          have hi_dom : i.1 ∈ dom := (Finset.mem_sdiff.mp i.2).1
          have hi_notA : i.1 ∉ A := (Finset.mem_sdiff.mp i.2).2
          have hne_a : x ⟨i.1, hi_dom⟩ ≠ a := by
            intro heq
            apply hi_notA
            have hmem : i.1 ∈ fiberA x := by
              simp only [fiberA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                Function.Embedding.coeFn_mk]
              exact ⟨⟨i.1, hi_dom⟩, heq, rfl⟩
            rwa [hfib] at hmem
          exact (Finset.mem_insert.mp (hx_mem ⟨i.1, hi_dom⟩)).resolve_left hne_a
        · intro b hb
          have hba : b ≠ a := fun h => ha (h ▸ hb)
          rw [← hx_cnt b (Finset.mem_insert_of_mem hb)]
          refine Finset.card_bij
            (fun i _ => ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩)
            ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi
          · intro i₁ _ i₂ _ h
            exact Subtype.ext (congrArg (fun z : dom => z.1) h)
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            have hj_notA : j.1 ∉ A := by
              intro hjA
              rw [← hfib] at hjA
              simp only [fiberA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                Function.Embedding.coeFn_mk] at hjA
              obtain ⟨⟨j', hj'⟩, hj'a, hjj'⟩ := hjA
              have : j = ⟨j', hj'⟩ := Subtype.ext hjj'.symm
              rw [this] at hj
              exact hba (hj.symm.trans hj'a)
            refine ⟨⟨j.1, Finset.mem_sdiff.mpr ⟨j.2, hj_notA⟩⟩, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hj
      · -- Injective
        intro x₁ hx₁ x₂ hx₂ hEq
        simp only [Finset.mem_filter, F, Finset.mem_univ, true_and] at hx₁ hx₂
        funext i
        by_cases hiA : i.1 ∈ A
        · have h1 : x₁ i = a := by
            rw [← hx₁.2] at hiA
            simp only [fiberA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
              Function.Embedding.coeFn_mk] at hiA
            obtain ⟨j, hja, hji⟩ := hiA
            have : i = j := Subtype.ext hji.symm
            rw [this]; exact hja
          have h2 : x₂ i = a := by
            rw [← hx₂.2] at hiA
            simp only [fiberA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
              Function.Embedding.coeFn_mk] at hiA
            obtain ⟨j, hja, hji⟩ := hiA
            have : i = j := Subtype.ext hji.symm
            rw [this]; exact hja
          rw [h1, h2]
        · exact congrFun hEq ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hiA⟩⟩
      · -- Surjective
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        obtain ⟨hy_mem, hy_cnt⟩ := hy
        let x : dom → α := fun i =>
          if hi : i.1 ∈ A then a else y ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hi⟩⟩
        have hx_fib : fiberA x = A := by
          ext j
          simp only [fiberA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨⟨j', hj'⟩, hxa, rfl⟩
            dsimp only [x] at hxa
            by_cases hjA : j' ∈ A
            · exact hjA
            · simp only [hjA, ↓reduceDIte] at hxa
              exact absurd (hxa ▸ hy_mem ⟨j', Finset.mem_sdiff.mpr ⟨hj', hjA⟩⟩) ha
          · intro hjA
            refine ⟨⟨j, hA_sub hjA⟩, ?_, rfl⟩
            simp [x, hjA]
        refine ⟨x, ?_, ?_⟩
        · simp only [Finset.mem_filter, F, Finset.mem_univ, true_and]
          refine ⟨⟨?_, ?_⟩, hx_fib⟩
          · intro i
            dsimp only [x]
            split_ifs with hiA
            · exact Finset.mem_insert_self a s
            · exact Finset.mem_insert_of_mem (hy_mem _)
          · intro b hb
            rcases Finset.mem_insert.mp hb with rfl | hbs
            · have hcard := congrArg Finset.card hx_fib
              rw [Finset.card_map] at hcard
              exact hcard.trans hA_card
            · have hba : b ≠ a := fun h => ha (h ▸ hbs)
              rw [← hy_cnt b hbs]
              refine Finset.card_bij
                (fun i hi => ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                  intro hiA
                  simp only [x, hiA, ↓reduceDIte] at hi
                  exact hba hi.symm⟩⟩)
                ?_ ?_ ?_
              · intro i hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                have hiA : i.1 ∉ A := by
                  intro hiA; simp only [x, hiA, ↓reduceDIte] at hi; exact hba hi.symm
                simpa [x, hiA] using hi
              · intro i₁ _ i₂ _ h
                exact Subtype.ext (congrArg (fun z : (dom \ A : Finset (Fin n)) => z.1) h)
              · intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                have hj_notA : j.1 ∉ A := (Finset.mem_sdiff.mp j.2).2
                refine ⟨⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩, ?_, Subtype.ext rfl⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, hj_notA, ↓reduceDIte]
                exact hj
        · funext i
          have hi_notA : i.1 ∉ A := (Finset.mem_sdiff.mp i.2).2
          simp [x, hi_notA]
    have hFcard : F.card = ∑ A ∈ dom.powersetCard (k a), (F.filter (fun x => fiberA x = A)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    change F.card * ∏ b ∈ insert a s, (k b)! = (dom.card)!
    rw [Finset.prod_insert ha, hFcard, Finset.sum_mul]
    have hterm : ∀ A ∈ dom.powersetCard (k a),
        (F.filter (fun x => fiberA x = A)).card * ((k a)! * ∏ b ∈ s, (k b)!) =
          (k a)! * (dom.card - k a)! := by
      intro A hA
      rw [hfiber_card A hA]
      have hA_sub : A ⊆ dom := (Finset.mem_powersetCard.mp hA).1
      have hA_card : A.card = k a := (Finset.mem_powersetCard.mp hA).2
      have hsdiff_card : (dom \ A).card = dom.card - k a := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hA_sub, hA_card]
      have hih := ih (dom \ A) (by omega)
      rw [hsdiff_card] at hih
      calc (Finset.univ.filter (fun y : (dom \ A : Finset (Fin n)) → α =>
              (∀ i, y i ∈ s) ∧ ∀ b ∈ s, (Finset.univ.filter (fun i => y i = b)).card = k b)).card *
              ((k a)! * ∏ b ∈ s, (k b)!)
        _ = (k a)! * ((Finset.univ.filter (fun y : (dom \ A : Finset (Fin n)) → α =>
              (∀ i, y i ∈ s) ∧ ∀ b ∈ s, (Finset.univ.filter (fun i => y i = b)).card = k b)).card *
              ∏ b ∈ s, (k b)!) := by ring
        _ = (k a)! * (dom.card - k a)! := by rw [hih]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul,
      ← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hka_le

private lemma typeClass_card_mul_prod_factorial {n : ℕ} (hn : 0 < n) (x₀ : Fin n → α) :
    (typeClass hn (empiricalType hn x₀)).card * ∏ a : α, (typeCount x₀ a)! = n ! := by
  classical
  let dom : Finset (Fin n) := Finset.univ
  have hsum : ∑ a ∈ (Finset.univ : Finset α), typeCount x₀ a = dom.card := by
    rw [sum_typeCount]; simp [dom]
  have haux := card_multinomial_aux (Finset.univ : Finset α) (typeCount x₀) dom hsum
  have hdom_card : dom.card = n := by simp [dom]
  rw [hdom_card] at haux
  have hcard_eq : (typeClass hn (empiricalType hn x₀)).card =
      (Finset.univ.filter (fun x : dom → α =>
        (∀ i, x i ∈ (Finset.univ : Finset α)) ∧
        ∀ a ∈ (Finset.univ : Finset α),
          (Finset.univ.filter (fun i => x i = a)).card = typeCount x₀ a)).card := by
    refine Finset.card_bij
      (fun x _ i => x i.1)
      ?_ ?_ ?_
    · intro x hx
      simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [empiricalType_eq_iff] at hx
      refine ⟨fun _ => trivial, fun a _ => ?_⟩
      rw [← hx a, typeCount_eq_card]
      refine Finset.card_bij (fun i _ => i.1)
        (fun i hi => by simpa using hi)
        (fun i₁ _ i₂ _ h => Subtype.ext h)
        (fun j hj => ⟨⟨j, Finset.mem_univ j⟩, by simpa using hj, rfl⟩)
    · intro x₁ _ x₂ _ hEq
      funext j
      exact congrFun hEq ⟨j, Finset.mem_univ j⟩
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨fun j => y ⟨j, Finset.mem_univ j⟩, ?_, ?_⟩
      · simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [empiricalType_eq_iff]
        intro a
        rw [typeCount_eq_card, ← hy.2 a trivial]
        refine Finset.card_bij (fun j _ => ⟨j, Finset.mem_univ j⟩)
          (fun j hj => by simpa using hj)
          (fun j₁ _ j₂ _ h => congrArg Subtype.val h)
          (fun i hi => ⟨i.1, by simpa using hi, Subtype.ext rfl⟩)
      · funext i; rfl
  rw [hcard_eq]
  exact haux

/-- Elementary natural-number inequality `p! * p^q ≤ q! * p^p`, used to prove that
    `P^n(T(Q)) ≤ P^n(T(P))` for every empirical type `Q` (Cover & Thomas, Lemma 11.1.3). -/
private lemma factorial_mul_pow_le (p q : ℕ) : p ! * p ^ q ≤ q ! * p ^ p := by
  rcases le_total p q with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hstep : ∀ d : ℕ, p ! * p ^ d ≤ (p + d)! := by
      intro d
      induction d with
      | zero => simp
      | succ k ih =>
        calc p ! * p ^ (k + 1)
          _ = (p ! * p ^ k) * p := by ring
          _ ≤ (p + k)! * (p + k + 1) := Nat.mul_le_mul ih (by omega)
          _ = (p + (k + 1))! := by
              rw [show p + (k + 1) = (p + k) + 1 by omega, Nat.factorial_succ, mul_comm]
    calc p ! * p ^ (p + d)
      _ = (p ! * p ^ d) * p ^ p := by rw [pow_add]; ring
      _ ≤ (p + d)! * p ^ p := Nat.mul_le_mul_right _ (hstep d)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hstep : ∀ (r d : ℕ), q + d ≤ r → (q + d)! ≤ q ! * r ^ d := by
      intro r d
      induction d with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        calc (q + (k + 1))!
          _ = (q + k + 1) * (q + k)! := by
              rw [show q + (k + 1) = (q + k) + 1 by omega, Nat.factorial_succ]
          _ ≤ r * (q ! * r ^ k) := Nat.mul_le_mul (by omega) (ih (by omega))
          _ = q ! * r ^ (k + 1) := by rw [pow_succ]; ring
    calc (q + d)! * (q + d) ^ q
      _ ≤ (q ! * (q + d) ^ d) * (q + d) ^ q := Nat.mul_le_mul_right _ (hstep (q + d) d le_rfl)
      _ = q ! * (q + d) ^ (q + d) := by rw [pow_add]; ring

/-- **Maximum-Likelihood Property of Type Classes** (Cover & Thomas, Lemma 11.1.3):
    for any two empirical types `P, Q ∈ 𝒫_n(α)`, `P^n(T(Q)) ≤ P^n(T(P))`. -/
private lemma typeClass_prob_le_self {n : ℕ} (hn : 0 < n) (xP xQ : Fin n → α) :
    ∑ x ∈ typeClass hn (empiricalType hn xQ), (iidDist (empiricalType hn xP) n).pmf x ≤
      ∑ x ∈ typeClass hn (empiricalType hn xP), (iidDist (empiricalType hn xP) n).pmf x := by
  classical
  let P := empiricalType hn xP
  let Q := empiricalType hn xQ
  -- Step 1: Natural-number multinomial inequality
  have hprod_nat : ∏ a : α, ((typeCount xP a)! * (typeCount xP a) ^ (typeCount xQ a)) ≤
      ∏ a : α, ((typeCount xQ a)! * (typeCount xP a) ^ (typeCount xP a)) :=
    Finset.prod_le_prod fun a _ =>
      factorial_mul_pow_le (typeCount xP a) (typeCount xQ a)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod_nat
  have hmult_nat :
      (typeClass hn Q).card * ∏ a : α, (typeCount xP a) ^ (typeCount xQ a) ≤
        (typeClass hn P).card * ∏ a : α, (typeCount xP a) ^ (typeCount xP a) := by
    have hmul := Nat.mul_le_mul_left ((typeClass hn Q).card * (typeClass hn P).card) hprod_nat
    have hQfac := typeClass_card_mul_prod_factorial hn xQ
    have hPfac := typeClass_card_mul_prod_factorial hn xP
    have hlhs : (typeClass hn Q).card * (typeClass hn P).card *
        ((∏ a : α, (typeCount xP a)!) * ∏ a : α, (typeCount xP a) ^ (typeCount xQ a)) =
        n ! * ((typeClass hn Q).card * ∏ a : α, (typeCount xP a) ^ (typeCount xQ a)) := by
      calc (typeClass hn Q).card * (typeClass hn P).card *
            ((∏ a : α, (typeCount xP a)!) * ∏ a : α, (typeCount xP a) ^ (typeCount xQ a))
        _ = ((typeClass hn P).card * ∏ a : α, (typeCount xP a)!) *
              ((typeClass hn Q).card * ∏ a : α, (typeCount xP a) ^ (typeCount xQ a)) := by ring
        _ = n ! * ((typeClass hn Q).card * ∏ a : α, (typeCount xP a) ^ (typeCount xQ a)) := by
            rw [hPfac]
    have hrhs : (typeClass hn Q).card * (typeClass hn P).card *
        ((∏ a : α, (typeCount xQ a)!) * ∏ a : α, (typeCount xP a) ^ (typeCount xP a)) =
        n ! * ((typeClass hn P).card * ∏ a : α, (typeCount xP a) ^ (typeCount xP a)) := by
      calc (typeClass hn Q).card * (typeClass hn P).card *
            ((∏ a : α, (typeCount xQ a)!) * ∏ a : α, (typeCount xP a) ^ (typeCount xP a))
        _ = ((typeClass hn Q).card * ∏ a : α, (typeCount xQ a)!) *
              ((typeClass hn P).card * ∏ a : α, (typeCount xP a) ^ (typeCount xP a)) := by ring
        _ = n ! * ((typeClass hn P).card * ∏ a : α, (typeCount xP a) ^ (typeCount xP a)) := by
            rw [hQfac]
    rw [hlhs, hrhs] at hmul
    exact Nat.le_of_mul_le_mul_left hmul (Nat.factorial_pos n)
  -- Step 2: Evaluate both sums as `|T(R)| * (∏ (p a)^(r a)) / n^n`
  have hsum_eval : ∀ xR : Fin n → α,
      ∑ x ∈ typeClass hn (empiricalType hn xR), (iidDist P n).pmf x =
        (((typeClass hn (empiricalType hn xR)).card *
          ∏ a : α, (typeCount xP a) ^ (typeCount xR a) : ℕ) : ℝ) / (n : ℝ) ^ n := by
    intro xR
    have hconst : ∀ x ∈ typeClass hn (empiricalType hn xR),
        (iidDist P n).pmf x =
          ((∏ a : α, (typeCount xP a) ^ (typeCount xR a) : ℕ) : ℝ) / (n : ℝ) ^ n := by
      intro x hx
      simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hcnt : ∀ a : α, typeCount x a = typeCount xR a := (empiricalType_eq_iff hn x xR).mp hx
      change ∏ i : Fin n, P.pmf (x i) = _
      rw [prod_comp_eq_prod_pow_typeCount]
      simp_rw [hcnt]
      change ∏ a : α, ((typeCount xP a : ℝ) / (n : ℝ)) ^ (typeCount xR a) = _
      simp_rw [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_typeCount]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul, mul_div_assoc]
  rw [hsum_eval xQ, hsum_eval xP]
  have hnn_pos : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmult_nat) (le_of_lt hnn_pos)

/-- **Type Class Cardinality Lower Bound** (Cover & Thomas, Theorem 11.1.3):
    for any empirical type `P ∈ 𝒫_n(α)`,
    `((n + 1)^{|α|})⁻¹ * 2^{n H(P)} ≤ |T(P)|`. -/
theorem typeClass_card_ge {n : ℕ} (hn : 0 < n) {P : ProbDist α} (hP : P ∈ typesSet α hn) :
    ((n + 1 : ℝ) ^ (Fintype.card α))⁻¹ * (2 : ℝ) ^ ((n : ℝ) * shannonEntropy P) ≤
      ((typeClass hn P).card : ℝ) := by
  classical
  simp only [typesSet, Finset.mem_image, Finset.mem_univ, true_and] at hP
  obtain ⟨xP, rfl⟩ := hP
  -- Partition `Fin n → α` by empirical type
  have hpart : (∑ Q ∈ typesSet α hn, ∑ x ∈ typeClass hn Q,
      (iidDist (empiricalType hn xP) n).pmf x) = 1 := by
    have huniv : (typesSet α hn).biUnion (typeClass hn) = Finset.univ := by
      ext x
      simp only [Finset.mem_biUnion, typesSet, typeClass, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      exact ⟨empiricalType hn x, ⟨x, rfl⟩, rfl⟩
    have hdisj : Set.PairwiseDisjoint (typesSet α hn : Set (ProbDist α)) (typeClass hn) := by
      intro Q₁ _ Q₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      exact hne (hx₁.symm.trans hx₂)
    rw [← Finset.sum_biUnion hdisj, huniv]
    exact (iidDist (empiricalType hn xP) n).sum_one
  -- Bound each type class probability by `P^n(T(P))`
  have hle_max : ∀ Q ∈ typesSet α hn,
      ∑ x ∈ typeClass hn Q, (iidDist (empiricalType hn xP) n).pmf x ≤
        ∑ x ∈ typeClass hn (empiricalType hn xP), (iidDist (empiricalType hn xP) n).pmf x := by
    intro Q hQ
    simp only [typesSet, Finset.mem_image, Finset.mem_univ, true_and] at hQ
    obtain ⟨xQ, rfl⟩ := hQ
    exact typeClass_prob_le_self hn xP xQ
  have hprob_nonneg : 0 ≤ ∑ x ∈ typeClass hn (empiricalType hn xP),
      (iidDist (empiricalType hn xP) n).pmf x :=
    Finset.sum_nonneg fun x _ => (iidDist (empiricalType hn xP) n).nonneg x
  have hcard_types : ((typesSet α hn).card : ℝ) ≤ (n + 1 : ℝ) ^ (Fintype.card α) := by
    exact_mod_cast card_typesSet_le α hn
  have h1_le : 1 ≤ ((n + 1 : ℝ) ^ (Fintype.card α)) *
      ∑ x ∈ typeClass hn (empiricalType hn xP), (iidDist (empiricalType hn xP) n).pmf x := by
    calc (1 : ℝ)
      _ = ∑ Q ∈ typesSet α hn, ∑ x ∈ typeClass hn Q,
            (iidDist (empiricalType hn xP) n).pmf x := hpart.symm
      _ ≤ ∑ _Q ∈ typesSet α hn, ∑ x ∈ typeClass hn (empiricalType hn xP),
            (iidDist (empiricalType hn xP) n).pmf x := Finset.sum_le_sum hle_max
      _ = ((typesSet α hn).card : ℝ) * ∑ x ∈ typeClass hn (empiricalType hn xP),
            (iidDist (empiricalType hn xP) n).pmf x := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℝ) ^ (Fintype.card α)) * ∑ x ∈ typeClass hn (empiricalType hn xP),
            (iidDist (empiricalType hn xP) n).pmf x :=
          mul_le_mul_of_nonneg_right hcard_types hprob_nonneg
  have hden_pos : (0 : ℝ) < (n + 1 : ℝ) ^ (Fintype.card α) := by positivity
  have hprob_ge : ((n + 1 : ℝ) ^ (Fintype.card α))⁻¹ ≤
      ∑ x ∈ typeClass hn (empiricalType hn xP), (iidDist (empiricalType hn xP) n).pmf x := by
    rw [inv_le_iff_one_le_mul₀' hden_pos]
    exact h1_le
  rw [typeClass_prob_eq hn _ _ (fun _ h => h), klDivergence_self, add_zero] at hprob_ge
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * shannonEntropy (empiricalType hn xP)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : (2 : ℝ) ^ (-((n : ℝ) * shannonEntropy (empiricalType hn xP))) *
      (2 : ℝ) ^ ((n : ℝ) * shannonEntropy (empiricalType hn xP)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have h2 := mul_le_mul_of_nonneg_right hprob_ge (le_of_lt hpow_pos)
  rw [mul_assoc, hmul, mul_one] at h2
  exact h2

/-- **Probability of a Type Class — Upper Bound** (Cover & Thomas, Theorem 11.1.4):
    if `P ≪ Q`, then `Q^n(T(P)) ≤ 2^{-n D(P ‖ Q)}`. -/
theorem typeClass_prob_le {n : ℕ} (hn : 0 < n) (P Q : ProbDist α) (hac : AbsCont P Q) :
    ∑ x ∈ typeClass hn P, (iidDist Q n).pmf x ≤
      (2 : ℝ) ^ (-((n : ℝ) * klDivergence P Q)) := by
  rw [typeClass_prob_eq hn P Q hac]
  have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  calc ((typeClass hn P).card : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q)))
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * shannonEntropy P) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) :=
        mul_le_mul_of_nonneg_right (typeClass_card_le hn P) hpow_nonneg
    _ = (2 : ℝ) ^ (-((n : ℝ) * klDivergence P Q)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; ring

/-- **Probability of a Type Class — Lower Bound** (Cover & Thomas, Theorem 11.1.4):
    for any empirical type `P ∈ 𝒫_n(α)` with `P ≪ Q`,
    `((n + 1)^{|α|})⁻¹ * 2^{-n D(P ‖ Q)} ≤ Q^n(T(P))`. -/
theorem typeClass_prob_ge {n : ℕ} (hn : 0 < n) {P : ProbDist α} (hP : P ∈ typesSet α hn)
    (Q : ProbDist α) (hac : AbsCont P Q) :
    ((n + 1 : ℝ) ^ (Fintype.card α))⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * klDivergence P Q)) ≤
      ∑ x ∈ typeClass hn P, (iidDist Q n).pmf x := by
  rw [typeClass_prob_eq hn P Q hac]
  have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  calc ((n + 1 : ℝ) ^ (Fintype.card α))⁻¹ * (2 : ℝ) ^ (-((n : ℝ) * klDivergence P Q))
    _ = ((n + 1 : ℝ) ^ (Fintype.card α))⁻¹ * (2 : ℝ) ^ ((n : ℝ) * shannonEntropy P) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2; ring
    _ ≤ ((typeClass hn P).card : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + klDivergence P Q))) :=
        mul_le_mul_of_nonneg_right (typeClass_card_ge hn hP) hpow_nonneg

/-- **Sanov's Theorem (Upper Bound)** (Cover & Thomas, Theorem 11.4.1):
    for any set of distributions `E` with `P ≪ Q` and `d ≤ D(P ‖ Q)` for all `P ∈ E`,
    `Q^n({x | P_x ∈ E}) ≤ (n + 1)^{|α|} * 2^{-n d}`. -/
theorem sanov_upper_bound {n : ℕ} (hn : 0 < n) (E : Set (ProbDist α))
    [DecidablePred (· ∈ E)] (Q : ProbDist α) {d : ℝ}
    (hac : ∀ P ∈ E, AbsCont P Q) (hd : ∀ P ∈ E, d ≤ klDivergence P Q) :
    ∑ x ∈ Finset.univ.filter (fun x => empiricalType hn x ∈ E), (iidDist Q n).pmf x ≤
      ((n + 1 : ℝ) ^ (Fintype.card α)) * (2 : ℝ) ^ (-((n : ℝ) * d)) := by
  classical
  let Etypes : Finset (ProbDist α) := (typesSet α hn).filter (fun P => P ∈ E)
  have hbiUnion : Etypes.biUnion (typeClass hn) =
      Finset.univ.filter (fun x => empiricalType hn x ∈ E) := by
    ext x
    simp only [Finset.mem_biUnion, Etypes, typesSet, typeClass, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨P, ⟨⟨_, _⟩, hPE⟩, rfl⟩; exact hPE
    · intro hxE
      exact ⟨empiricalType hn x, ⟨⟨x, rfl⟩, hxE⟩, rfl⟩
  have hdisj : Set.PairwiseDisjoint (Etypes : Set (ProbDist α)) (typeClass hn) := by
    intro P₁ _ P₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    exact hne (hx₁.symm.trans hx₂)
  rw [← hbiUnion, Finset.sum_biUnion hdisj]
  have hterm : ∀ P ∈ Etypes,
      ∑ x ∈ typeClass hn P, (iidDist Q n).pmf x ≤ (2 : ℝ) ^ (-((n : ℝ) * d)) := by
    intro P hP
    have hPE : P ∈ E := (Finset.mem_filter.mp hP).2
    refine le_trans (typeClass_prob_le hn P Q (hac P hPE)) ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hd P hPE]
  have hcard_le : (Etypes.card : ℝ) ≤ (n + 1 : ℝ) ^ (Fintype.card α) := by
    have h1 : Etypes.card ≤ (typesSet α hn).card := Finset.card_filter_le _ _
    have h2 : Etypes.card ≤ (n + 1) ^ (Fintype.card α) := le_trans h1 (card_typesSet_le α hn)
    exact_mod_cast h2
  have hpow_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * d)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  calc ∑ P ∈ Etypes, ∑ x ∈ typeClass hn P, (iidDist Q n).pmf x
    _ ≤ ∑ _P ∈ Etypes, (2 : ℝ) ^ (-((n : ℝ) * d)) := Finset.sum_le_sum hterm
    _ = (Etypes.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * d)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1 : ℝ) ^ (Fintype.card α)) * (2 : ℝ) ^ (-((n : ℝ) * d)) :=
        mul_le_mul_of_nonneg_right hcard_le hpow_nonneg

end MethodOfTypes

end InfoTheory.Bridge
