import InfoTheory.Bridge.CoverThomas
import Mathlib.Analysis.Subadditive

/-!
# Fekete's Lemma, Stationary Entropy Rate, the Copy Lemma, and the Zhang–Yeung Inequality

Purely additive, kernel-verified foundational theorems for Cover & Thomas Ch. 4 and
Yeung Ch. 15 (*Non-Shannon-Type Information Inequalities*), built directly on top of
`InfoTheory.Bridge.CoverThomas` and `Mathlib.Analysis.Subadditive`:

1. **Fekete's Subadditivity & Superadditivity Lemmas** (Cover & Thomas Ch. 4):
   - `fekete_subadditive_tendsto`, `fekete_subadditive_inf_le`: for `a : ℕ → ℝ` subadditive on
     positive integers and linearly bounded below (`c * n ≤ a n`), `a n / n → inf_{k > 0} a k / k`.
   - `fekete_superadditive_tendsto`, `fekete_superadditive_le_sup`: dual version for superadditive
     sequences bounded above (`a n ≤ C * n`), `a n / n → sup_{k > 0} a k / k`.
   - `IsStationaryShift`, `stationary_entropy_subadd`, `stationary_entropyRate_exists`:
     existence of the entropy rate `lim_{n → ∞} H(X_1, ..., X_n) / n` for any discrete
     stationary process (Cover & Thomas, Theorem 4.2.1).
2. **The Copy Lemma** (Zhang–Yeung 1998; Dougherty–Freiling–Zeger 2006):
   - `copyDist`: conditional copy `(A, B, B')` of `B` over `A`, with `copyDist_marginal_12`,
     `copyDist_marginal_13`, `copyDist_condIndep` (`I(B; B' | A) = 0`), and `copyDist_entropy`.
   - `copyOverFirst`: conditional copy `(A, B, C, C')` of `C` over `A` given `(A, B, C)`, with
     `copyOverFirst_marginal_123`, `copyOverFirst_marginal_14`, `copyOverFirst_condIndep`
     (`I(C'; (B, C) | A) = 0`), and `copyOverFirst_entropy`.
3. **Zhang–Yeung (1998) Non-Shannon Information Inequality & `cl(Γ*_4) ⊊ Γ_4`**:
   - `zhang_yeung_subsetEntropyVec`, `zhang_yeung_entropic`, `zhang_yeung_almostEntropic`:
     every 4-variable entropic (and almost-entropic) vector satisfies
     `2 I(C; D) ≤ I(A; B) + I(A; C, D) + 3 I(C; D | A) + I(C; D | B)`.
   - `exists_polymatroid_not_almostEntropic`, `exists_polymatroid_not_entropic`,
     `almostEntropic4_ssubset_polymatroid4`: strict inclusion `cl(Γ*_4) ⊊ Γ_4` and `Γ*_4 ⊊ Γ_4`.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Fekete's Subadditivity & Superadditivity Lemmas and Stationary Entropy Rate -/

section Fekete

/-- Helper: extend a sequence that is subadditive on `ℕ+` to a `Subadditive` function on `ℕ`
    by setting the `0`-th entry to `0`. -/
private def zeroPad (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then 0 else a n

private lemma zeroPad_subadditive {a : ℕ → ℝ}
    (hsub : ∀ m n : ℕ, 0 < m → 0 < n → a (m + n) ≤ a m + a n) :
    Subadditive (zeroPad a) := by
  intro m n
  unfold zeroPad
  by_cases hm : m = 0
  · subst hm; simp
  · by_cases hn : n = 0
    · subst hn; simp
    · have hmn : m + n ≠ 0 := by omega
      simp only [hm, hn, hmn, ↓reduceIte]
      exact hsub m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

private lemma zeroPad_bddBelow {a : ℕ → ℝ} {c : ℝ}
    (hlow : ∀ n : ℕ, 0 < n → c * (n : ℝ) ≤ a n) :
    BddBelow (Set.range fun n : ℕ => zeroPad a n / (n : ℝ)) := by
  refine ⟨min c 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  unfold zeroPad
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, ↓reduceIte]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hle : c ≤ a n / (n : ℝ) := (le_div_iff₀ hnpos).mpr (hlow n (Nat.pos_of_ne_zero hn))
    exact le_trans (min_le_left c 0) hle

/-- **Fekete's Subadditive Lemma** (Cover & Thomas, Ch. 4):
    if `a : ℕ → ℝ` is subadditive on positive integers (`a (m + n) ≤ a m + a n` for `m, n > 0`)
    and linearly bounded below (`c * n ≤ a n` for `n > 0`), then `a n / n` converges to
    `inf { a k / k | k > 0 }`. -/
theorem fekete_subadditive_tendsto {a : ℕ → ℝ}
    (hsub : ∀ m n : ℕ, 0 < m → 0 < n → a (m + n) ≤ a m + a n)
    (hlow : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c * (n : ℝ) ≤ a n) :
    Filter.Tendsto (fun n : ℕ => a n / (n : ℝ)) Filter.atTop
      (nhds (sInf { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = a k / (k : ℝ) })) := by
  obtain ⟨c, hc⟩ := hlow
  let u := zeroPad a
  have hu : Subadditive u := zeroPad_subadditive hsub
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := zeroPad_bddBelow hc
  have htend : Filter.Tendsto (fun n : ℕ => u n / (n : ℝ)) Filter.atTop (nhds hu.lim) :=
    hu.tendsto_lim hbdd
  set S : Set ℝ := { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = a k / (k : ℝ) }
  have hS_ne : S.Nonempty := ⟨a 1 / (1 : ℕ), 1, Nat.one_pos, rfl⟩
  have hS_bdd : BddBelow S := by
    refine ⟨c, ?_⟩
    rintro r ⟨k, hk, rfl⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact (le_div_iff₀ hkpos).mpr (hc k hk)
  have hlim_eq : hu.lim = sInf S := by
    apply le_antisymm
    · refine le_csInf hS_ne ?_
      rintro r ⟨k, hk, rfl⟩
      have hkne : k ≠ 0 := Nat.ne_of_gt hk
      have hle := hu.lim_le_div hbdd hkne
      simpa [u, zeroPad, hkne] using hle
    · refine ge_of_tendsto htend ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hne : n ≠ 0 := by omega
      have hmem : u n / (n : ℝ) ∈ S := ⟨n, Nat.pos_of_ne_zero hne, by simp [u, zeroPad, hne]⟩
      exact csInf_le hS_bdd hmem
  rw [← hlim_eq]
  refine htend.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : n ≠ 0 := by omega
  simp [u, zeroPad, hne]

/-- Every normalized term `a n / n` (`n > 0`) of a subadditive sequence bounded below dominates
    the Fekete limit `inf { a k / k | k > 0 }`. -/
theorem fekete_subadditive_inf_le {a : ℕ → ℝ}
    (hlow : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c * (n : ℝ) ≤ a n)
    {n : ℕ} (hn : 0 < n) :
    sInf { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = a k / (k : ℝ) } ≤ a n / (n : ℝ) := by
  obtain ⟨c, hc⟩ := hlow
  refine csInf_le ⟨c, ?_⟩ ⟨n, hn, rfl⟩
  rintro r ⟨k, hk, rfl⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact (le_div_iff₀ hkpos).mpr (hc k hk)

/-- **Fekete's Superadditive Lemma** (dual form, used for channel / zero-error capacities):
    if `a : ℕ → ℝ` is superadditive on positive integers (`a m + a n ≤ a (m + n)` for `m, n > 0`)
    and linearly bounded above (`a n ≤ C * n` for `n > 0`), then `a n / n` converges to
    `sup { a k / k | k > 0 }`. -/
theorem fekete_superadditive_tendsto {a : ℕ → ℝ}
    (hsup : ∀ m n : ℕ, 0 < m → 0 < n → a m + a n ≤ a (m + n))
    (hup : ∃ C : ℝ, ∀ n : ℕ, 0 < n → a n ≤ C * (n : ℝ)) :
    Filter.Tendsto (fun n : ℕ => a n / (n : ℝ)) Filter.atTop
      (nhds (sSup { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = a k / (k : ℝ) })) := by
  obtain ⟨C, hC⟩ := hup
  let b : ℕ → ℝ := fun n => -a n
  have hb_sub : ∀ m n : ℕ, 0 < m → 0 < n → b (m + n) ≤ b m + b n := by
    intro m n hm hn
    dsimp only [b]
    linarith [hsup m n hm hn]
  have hb_low : ∃ c : ℝ, ∀ n : ℕ, 0 < n → c * (n : ℝ) ≤ b n := by
    refine ⟨-C, fun n hn => ?_⟩
    dsimp only [b]
    linarith [hC n hn]
  have htend_b := fekete_subadditive_tendsto hb_sub hb_low
  set S : Set ℝ := { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = a k / (k : ℝ) }
  set T : Set ℝ := { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = b k / (k : ℝ) }
  have hT_eq : T = Neg.neg '' S := by
    ext r
    simp only [T, S, b, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨a k / (k : ℝ), ⟨k, hk, rfl⟩, by ring⟩
    · rintro ⟨s, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by ring⟩
  have hS_ne : S.Nonempty := ⟨a 1 / (1 : ℕ), 1, Nat.one_pos, rfl⟩
  have hS_bdd : BddAbove S := by
    refine ⟨C, ?_⟩
    rintro r ⟨k, hk, rfl⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact (div_le_iff₀ hkpos).mpr (hC k hk)
  have hT_ne : T.Nonempty := hT_eq ▸ hS_ne.image _
  have hT_bdd : BddBelow T := by
    rw [hT_eq]
    obtain ⟨M, hM⟩ := hS_bdd
    exact ⟨-M, by rintro _ ⟨s, hs, rfl⟩; linarith [hM hs]⟩
  have hsup_eq : -sInf T = sSup S := by
    apply le_antisymm
    · rw [neg_le]
      refine le_csInf hT_ne ?_
      rw [hT_eq]
      rintro _ ⟨s, hs, rfl⟩
      exact neg_le_neg (le_csSup hS_bdd hs)
    · refine csSup_le hS_ne ?_
      intro s hs
      have hmem : -s ∈ T := hT_eq ▸ ⟨s, hs, rfl⟩
      linarith [csInf_le hT_bdd hmem]
  have htend_neg := htend_b.neg
  rw [hsup_eq] at htend_neg
  refine htend_neg.congr (fun n => ?_)
  simp [b, neg_div]

/-- Every normalized term `a n / n` (`n > 0`) of a superadditive sequence bounded above is at most
    the Fekete limit `sup { a k / k | k > 0 }`. -/
theorem fekete_superadditive_le_sup {a : ℕ → ℝ}
    (hup : ∃ C : ℝ, ∀ n : ℕ, 0 < n → a n ≤ C * (n : ℝ))
    {n : ℕ} (hn : 0 < n) :
    a n / (n : ℝ) ≤ sSup { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = a k / (k : ℝ) } := by
  obtain ⟨C, hC⟩ := hup
  refine le_csSup ⟨C, ?_⟩ ⟨n, hn, rfl⟩
  rintro r ⟨k, hk, rfl⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact (div_le_iff₀ hkpos).mpr (hC k hk)

/-! #### Application to Cover & Thomas Ch. 4: Stationary Process Entropy Rate -/

/-- A discrete-time stochastic process specified by its `n`-block marginals
    `P n : ProbDist (Fin n → α)` is **stationary** (marginal-consistent and shift-invariant) if
    for all `m, n : ℕ`, projecting `P (m + n)` onto the first `m` coordinates gives `P m` and
    projecting `P (m + n)` onto the last `n` coordinates gives `P n`. -/
def IsStationaryShift {α : Type*} [Fintype α] (P : (n : ℕ) → ProbDist (Fin n → α)) : Prop :=
  (∀ m n : ℕ,
    (P (m + n)).map
      (fun x (i : Fin m) => x ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right m n)⟩) = P m) ∧
  (∀ m n : ℕ,
    (P (m + n)).map
      (fun x (j : Fin n) => x ⟨m + j.1, Nat.add_lt_add_left j.2 m⟩) = P n)

private lemma fst_eq_map_fst {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist (α × β)) :
    Q.fst = Q.map Prod.fst := by
  classical
  cases Q with
  | mk pmf nonneg sum_one =>
    unfold ProbDist.fst ProbDist.map
    congr
    funext a
    rw [Fintype.sum_prod_type]
    trans (∑ a' : α, if a' = a then ∑ b : β, pmf (a, b) else 0)
    · simp
    · refine Finset.sum_congr rfl fun a' _ => ?_
      by_cases h : a' = a
      · subst h; simp
      · simp [h]

private lemma snd_eq_map_snd {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist (α × β)) :
    Q.snd = Q.map Prod.snd := by
  classical
  cases Q with
  | mk pmf nonneg sum_one =>
    unfold ProbDist.snd ProbDist.map
    congr
    funext b
    rw [Fintype.sum_prod_type_right]
    trans (∑ b' : β, if b' = b then ∑ a : α, pmf (a, b) else 0)
    · simp
    · refine Finset.sum_congr rfl fun b' _ => ?_
      by_cases h : b' = b
      · subst h; simp
      · simp [h]

/-- Block entropies of a stationary process are subadditive: `H(X_1^{m+n}) ≤ H(X_1^m) + H(X_1^n)`. -/
theorem stationary_entropy_subadd {α : Type*} [Fintype α]
    (P : (n : ℕ) → ProbDist (Fin n → α)) (hstat : IsStationaryShift P) (m n : ℕ) :
    shannonEntropy (P (m + n)) ≤ shannonEntropy (P m) + shannonEntropy (P n) := by
  let splitEquiv : (Fin (m + n) → α) ≃ ((Fin m → α) × (Fin n → α)) :=
    { toFun := fun x =>
        (fun i => x ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right m n)⟩,
         fun j => x ⟨m + j.1, Nat.add_lt_add_left j.2 m⟩)
      invFun := fun pq k =>
        if h : k.1 < m then pq.1 ⟨k.1, h⟩
        else pq.2 ⟨k.1 - m, by omega⟩
      left_inv := fun x => by
        funext k
        dsimp only
        split_ifs with h
        · rfl
        · congr 1; ext; dsimp; omega
      right_inv := fun ⟨p, q⟩ => by
        ext i
        · simp [i.2]
        · have hnot : ¬ (m + i.1 < m) := by omega
          simp only [hnot, ↓reduceDIte]
          congr 1; ext; dsimp; omega }
  let Q : ProbDist ((Fin m → α) × (Fin n → α)) := (P (m + n)).map splitEquiv
  have hQ_ent : shannonEntropy Q = shannonEntropy (P (m + n)) :=
    shannonEntropy_map_equiv splitEquiv (P (m + n))
  have hQ_fst : Q.fst = P m := by
    rw [fst_eq_map_fst, map_comp_eq]
    exact hstat.1 m n
  have hQ_snd : Q.snd = P n := by
    rw [snd_eq_map_snd, map_comp_eq]
    exact hstat.2 m n
  have hsub := shannonEntropy_subadd Q
  rw [hQ_ent, hQ_fst, hQ_snd] at hsub
  exact hsub

/-- **Existence of the Entropy Rate for Stationary Processes** (Cover & Thomas, Theorem 4.2.1):
    for any stationary process `P`, `H(X_1, ..., X_n) / n` converges as `n → ∞` to
    `inf_{k > 0} H(X_1, ..., X_k) / k`. -/
theorem stationary_entropyRate_exists {α : Type*} [Fintype α]
    (P : (n : ℕ) → ProbDist (Fin n → α)) (hstat : IsStationaryShift P) :
    Filter.Tendsto (fun n : ℕ => shannonEntropy (P n) / (n : ℝ)) Filter.atTop
      (nhds (sInf { r : ℝ | ∃ k : ℕ, 0 < k ∧ r = shannonEntropy (P k) / (k : ℝ) })) := by
  refine fekete_subadditive_tendsto
    (fun m n _ _ => stationary_entropy_subadd P hstat m n)
    ⟨0, fun n _ => ?_⟩
  simpa using shannonEntropy_nonneg (P n)

end Fekete

/-! ### 2. The Copy Lemma (Zhang–Yeung 1998; Dougherty–Freiling–Zeger 2006) -/

section CopyLemma

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

private lemma probDist_ext {ι : Type*} [Fintype ι] {P Q : ProbDist ι}
    (h : ∀ x, P.pmf x = Q.pmf x) : P = Q := by
  cases P; cases Q; congr; funext x; exact h x

private lemma map_pmf_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : ProbDist ι) (f : ι → κ) (y : κ) :
    (P.map f).pmf y = ∑ x : ι, if f x = y then P.pmf x else 0 := by
  unfold ProbDist.map
  dsimp only
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : f x = y <;> simp [h]

private lemma map_equiv_pmf {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ProbDist ι) (e : ι ≃ κ) (y : κ) :
    (P.map e).pmf y = P.pmf (e.symm y) := by
  classical
  rw [map_pmf_apply, Finset.sum_eq_single (e.symm y)]
  · simp
  · intro x _ hne
    have : e x ≠ y := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma swap_pmf_apply {δ ε : Type*} [Fintype δ] [Fintype ε]
    (R : ProbDist (δ × ε)) (y : ε) (x : δ) :
    (R.map Prod.swap).pmf (y, x) = R.pmf (x, y) :=
  map_equiv_pmf R (Equiv.prodComm δ ε) (y, x)

private lemma pmf_eq_zero_of_fst_eq_zero (P : ProbDist (α × β)) {a : α}
    (ha : P.fst.pmf a = 0) (b : β) : P.pmf (a, b) = 0 := by
  have hle : P.pmf (a, b) ≤ P.fst.pmf a :=
    Finset.single_le_sum (fun b' _ => P.nonneg (a, b')) (Finset.mem_univ b)
  exact le_antisymm (by linarith) (P.nonneg (a, b))

/-- **Conditional Copy Distribution** `(A, B, B')` of `B` over `A`:
    `Q(a, b, b') = P(a, b) P(a, b') / P_A(a)` (and `0` when `P_A(a) = 0`). -/
noncomputable def copyDist (P : ProbDist (α × β)) : ProbDist (α × β × β) where
  pmf := fun t =>
    if P.fst.pmf t.1 = 0 then 0
    else P.pmf (t.1, t.2.1) * P.pmf (t.1, t.2.2) / P.fst.pmf t.1
  nonneg := fun t => by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (P.nonneg _) (P.nonneg _)) (P.fst.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    trans (∑ a : α, P.fst.pmf a)
    · refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : P.fst.pmf a = 0
      · simp [ha]
      · simp only [ha, ↓reduceIte]
        have hsum_b : ∑ b : β, P.pmf (a, b) = P.fst.pmf a := rfl
        simp_rw [← Finset.sum_div, ← Finset.mul_sum, hsum_b, ← Finset.sum_mul, hsum_b]
        field_simp [ha]
    · exact P.fst.sum_one

/-- First copy marginal: `(A, B) ~ P`. -/
theorem copyDist_marginal_12 (P : ProbDist (α × β)) :
    (copyDist P).map (fun t => (t.1, t.2.1)) = P := by
  classical
  refine probDist_ext fun ⟨a, b⟩ => ?_
  rw [map_pmf_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp only [↓reduceIte, copyDist]
      by_cases ha : P.fst.pmf a = 0
      · simp only [ha, ↓reduceIte, Finset.sum_const_zero]
        exact (pmf_eq_zero_of_fst_eq_zero P ha b).symm
      · simp only [ha, ↓reduceIte]
        have hsum_b : ∑ b' : β, P.pmf (a, b') = P.fst.pmf a := rfl
        simp_rw [← Finset.sum_div, ← Finset.mul_sum, hsum_b]
        field_simp [ha]
    · intro b' _ hne
      exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Second copy marginal: `(A, B') ~ P`. -/
theorem copyDist_marginal_13 (P : ProbDist (α × β)) :
    (copyDist P).map (fun t => (t.1, t.2.2)) = P := by
  classical
  refine probDist_ext fun ⟨a, b'⟩ => ?_
  rw [map_pmf_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_comm]
    rw [Finset.sum_eq_single b']
    · simp only [↓reduceIte, copyDist]
      by_cases ha : P.fst.pmf a = 0
      · simp only [ha, ↓reduceIte, Finset.sum_const_zero]
        exact (pmf_eq_zero_of_fst_eq_zero P ha b').symm
      · simp only [ha, ↓reduceIte]
        have hsum_b : ∑ b : β, P.pmf (a, b) = P.fst.pmf a := rfl
        simp_rw [← Finset.sum_div, ← Finset.sum_mul, hsum_b]
        field_simp [ha]
    · intro b'' _ hne
      exact Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Conditional independence of the copy: `I(B; B' | A) = 0`. -/
theorem copyDist_condIndep (P : ProbDist (α × β)) :
    condMutualInfo ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))) = 0 := by
  let e : (α × β × β) ≃ (β × β × α) :=
    { toFun := fun t => (t.2.1, t.2.2, t.1)
      invFun := fun s => (s.2.2, s.1, s.2.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  let Q : ProbDist (β × β × α) := (copyDist P).map e
  change condMutualInfo Q = 0
  rw [condMutualInfo_eq_zero_iff]
  have hQ_pmf : ∀ b1 b2 a, Q.pmf (b1, b2, a) = (copyDist P).pmf (a, b1, b2) := fun b1 b2 a =>
    map_equiv_pmf (copyDist P) e (b1, b2, a)
  have hQ13 : Q.map (fun s => (s.1, s.2.2)) = P.map Prod.swap := by
    calc Q.map (fun s => (s.1, s.2.2))
      _ = (copyDist P).map (fun t => (t.2.1, t.1)) := by
          change ((copyDist P).map e).map _ = _; rw [map_comp_eq]; rfl
      _ = ((copyDist P).map (fun t => (t.1, t.2.1))).map Prod.swap := by rw [map_comp_eq]; rfl
      _ = P.map Prod.swap := by rw [copyDist_marginal_12]
  have hQ23 : Q.map (fun s => (s.2.1, s.2.2)) = P.map Prod.swap := by
    calc Q.map (fun s => (s.2.1, s.2.2))
      _ = (copyDist P).map (fun t => (t.2.2, t.1)) := by
          change ((copyDist P).map e).map _ = _; rw [map_comp_eq]; rfl
      _ = ((copyDist P).map (fun t => (t.1, t.2.2))).map Prod.swap := by rw [map_comp_eq]; rfl
      _ = P.map Prod.swap := by rw [copyDist_marginal_13]
  have hQ3 : Q.map (fun s => s.2.2) = P.fst := by
    calc Q.map (fun s => s.2.2)
      _ = (copyDist P).map (fun t => t.1) := by
          change ((copyDist P).map e).map _ = _; rw [map_comp_eq]; rfl
      _ = ((copyDist P).map (fun t => (t.1, t.2.1))).map Prod.fst := by rw [map_comp_eq]; rfl
      _ = P.fst := by rw [copyDist_marginal_12, fst_eq_map_fst]
  refine probDist_ext fun ⟨b1, b2, a⟩ => ?_
  rw [hQ_pmf]
  change (copyDist P).pmf (a, b1, b2) =
    if (Q.map (fun s => s.2.2)).pmf a = 0 then 0
    else (Q.map (fun s => (s.1, s.2.2))).pmf (b1, a) *
      (Q.map (fun s => (s.2.1, s.2.2))).pmf (b2, a) / (Q.map (fun s => s.2.2)).pmf a
  rw [hQ13, hQ23, hQ3, swap_pmf_apply, swap_pmf_apply]
  rfl

/-- Entropy identity of the conditional copy: `H(A, B, B') = 2 H(A, B) - H(A)`. -/
theorem copyDist_entropy (P : ProbDist (α × β)) :
    shannonEntropy (copyDist P) = 2 * shannonEntropy P - shannonEntropy P.fst := by
  let e : (α × β × β) ≃ (β × β × α) :=
    { toFun := fun t => (t.2.1, t.2.2, t.1)
      invFun := fun s => (s.2.2, s.1, s.2.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hcmi := copyDist_condIndep P
  unfold condMutualInfo at hcmi
  dsimp only at hcmi
  have h1 : ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => (t.1, t.2.2)) =
      P.map Prod.swap := by
    calc ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => (t.1, t.2.2))
      _ = ((copyDist P).map (fun t => (t.1, t.2.1))).map Prod.swap := by
          rw [map_comp_eq, map_comp_eq]; rfl
      _ = P.map Prod.swap := by rw [copyDist_marginal_12]
  have h2 : ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => (t.2.1, t.2.2)) =
      P.map Prod.swap := by
    calc ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => (t.2.1, t.2.2))
      _ = ((copyDist P).map (fun t => (t.1, t.2.2))).map Prod.swap := by
          rw [map_comp_eq, map_comp_eq]; rfl
      _ = P.map Prod.swap := by rw [copyDist_marginal_13]
  have h3 : ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => t.2.2) = P.fst := by
    calc ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))).map (fun t => t.2.2)
      _ = ((copyDist P).map (fun t => (t.1, t.2.1))).map Prod.fst := by
          rw [map_comp_eq, map_comp_eq]; rfl
      _ = P.fst := by rw [copyDist_marginal_12, fst_eq_map_fst]
  have h4 : shannonEntropy ((copyDist P).map (fun t => (t.2.1, t.2.2, t.1))) =
      shannonEntropy (copyDist P) := shannonEntropy_map_equiv e (copyDist P)
  rw [h1, h2, h3, h4, shannonEntropy_swap] at hcmi
  linarith

private lemma triple_pac_pmf (P : ProbDist (α × β × γ)) (a : α) (c : γ) :
    (P.map (fun t => (t.1, t.2.2))).pmf (a, c) = ∑ b : β, P.pmf (a, b, c) := by
  classical
  rw [map_pmf_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne
    exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma triple_fst_pmf (P : ProbDist (α × β × γ)) (a : α) :
    P.fst.pmf a = ∑ b : β, ∑ c : γ, P.pmf (a, b, c) := by
  change ∑ bc : β × γ, P.pmf (a, bc) = ∑ b : β, ∑ c : γ, P.pmf (a, b, c)
  rw [Fintype.sum_prod_type]

private lemma triple_sum_pac (P : ProbDist (α × β × γ)) (a : α) :
    ∑ c : γ, (P.map (fun t => (t.1, t.2.2))).pmf (a, c) = P.fst.pmf a := by
  simp_rw [triple_pac_pmf, triple_fst_pmf]
  exact Finset.sum_comm

private lemma triple_pmf_eq_zero_of_fst (P : ProbDist (α × β × γ)) {a : α}
    (ha : P.fst.pmf a = 0) (b : β) (c : γ) : P.pmf (a, b, c) = 0 :=
  pmf_eq_zero_of_fst_eq_zero P ha (b, c)

private lemma triple_pac_eq_zero_of_fst (P : ProbDist (α × β × γ)) {a : α}
    (ha : P.fst.pmf a = 0) (c : γ) : (P.map (fun t => (t.1, t.2.2))).pmf (a, c) = 0 := by
  rw [triple_pac_pmf]
  exact Finset.sum_eq_zero fun b _ => triple_pmf_eq_zero_of_fst P ha b c

/-- **General Copy Lemma Construction (`copyOverFirst`)**: given `(A, B, C) ~ P`, construct
    `(A, B, C, C')` on `α × β × γ × γ` such that `(A, B, C) ~ P`, `(A, C') ~ P_{A, C}`, and
    `C' — A — (B, C)` (`I(C'; (B, C) | A) = 0`). -/
noncomputable def copyOverFirst (P : ProbDist (α × β × γ)) : ProbDist (α × β × γ × γ) :=
  let Pac : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  { pmf := fun t =>
      if P.fst.pmf t.1 = 0 then 0
      else P.pmf (t.1, t.2.1, t.2.2.1) * Pac.pmf (t.1, t.2.2.2) / P.fst.pmf t.1
    nonneg := fun t => by
      split_ifs
      · exact le_rfl
      · exact div_nonneg (mul_nonneg (P.nonneg _) (Pac.nonneg _)) (P.fst.nonneg _)
    sum_one := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      trans (∑ a : α, P.fst.pmf a)
      · refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : P.fst.pmf a = 0
        · simp [ha]
        · simp only [ha, ↓reduceIte]
          have hsum_c' : ∑ c' : γ, Pac.pmf (a, c') = P.fst.pmf a := triple_sum_pac P a
          have hsum_bc : ∑ b : β, ∑ c : γ, P.pmf (a, b, c) = P.fst.pmf a :=
            (triple_fst_pmf P a).symm
          simp_rw [← Finset.sum_div, ← Finset.mul_sum, hsum_c', ← Finset.sum_mul]
          rw [hsum_bc]
          field_simp [ha]
      · exact P.fst.sum_one }

/-- Original marginal of `copyOverFirst`: `(A, B, C) ~ P`. -/
theorem copyOverFirst_marginal_123 (P : ProbDist (α × β × γ)) :
    (copyOverFirst P).map (fun t => (t.1, t.2.1, t.2.2.1)) = P := by
  classical
  refine probDist_ext fun ⟨a, b, c⟩ => ?_
  rw [map_pmf_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · simp only [↓reduceIte, copyOverFirst]
        by_cases ha : P.fst.pmf a = 0
        · simp only [ha, ↓reduceIte, Finset.sum_const_zero]
          exact (triple_pmf_eq_zero_of_fst P ha b c).symm
        · simp only [ha, ↓reduceIte]
          have hsum_c' : ∑ c' : γ, (P.map (fun t => (t.1, t.2.2))).pmf (a, c') = P.fst.pmf a :=
            triple_sum_pac P a
          simp_rw [← Finset.sum_div, ← Finset.mul_sum, hsum_c']
          field_simp [ha]
      · intro c' _ hne
        exact Finset.sum_eq_zero fun _ _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b' _ hne
      exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ hne
    exact Finset.sum_eq_zero fun _ _ =>
      Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Copied marginal of `copyOverFirst`: `(A, C') ~ P_{A, C}`. -/
theorem copyOverFirst_marginal_14 (P : ProbDist (α × β × γ)) :
    (copyOverFirst P).map (fun t => (t.1, t.2.2.2)) = P.map (fun t => (t.1, t.2.2)) := by
  classical
  let Pac : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  refine probDist_ext fun ⟨a, c'⟩ => ?_
  rw [map_pmf_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · trans (∑ b : β, ∑ c : γ, (copyOverFirst P).pmf (a, b, c, c'))
    · refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single c']
      · simp
      · intro c'' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [copyOverFirst]
      by_cases ha : P.fst.pmf a = 0
      · simp only [ha, ↓reduceIte, Finset.sum_const_zero]
        exact (triple_pac_eq_zero_of_fst P ha c').symm
      · simp only [ha, ↓reduceIte]
        have hsum_bc : ∑ b : β, ∑ c : γ, P.pmf (a, b, c) = P.fst.pmf a :=
          (triple_fst_pmf P a).symm
        have hfact : ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Pac.pmf (a, c') / P.fst.pmf a =
            (∑ b : β, ∑ c : γ, P.pmf (a, b, c)) * Pac.pmf (a, c') / P.fst.pmf a := by
          simp_rw [← Finset.sum_div, ← Finset.sum_mul]
        change ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * Pac.pmf (a, c') / P.fst.pmf a = Pac.pmf (a, c')
        rw [hfact, hsum_bc]
        field_simp [ha]
  · intro a' _ hne
    exact Finset.sum_eq_zero fun _ _ =>
      Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Conditional independence of `copyOverFirst`: `I(C'; (B, C) | A) = 0`. -/
theorem copyOverFirst_condIndep (P : ProbDist (α × β × γ)) :
    condMutualInfo ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))) = 0 := by
  let e : (α × β × γ × γ) ≃ (γ × (β × γ) × α) :=
    { toFun := fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1)
      invFun := fun s => (s.2.2, s.2.1.1, s.2.1.2, s.1)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl }
  let Q : ProbDist (γ × (β × γ) × α) := (copyOverFirst P).map e
  change condMutualInfo Q = 0
  rw [condMutualInfo_eq_zero_iff]
  have hQ_pmf : ∀ c' b c a, Q.pmf (c', (b, c), a) = (copyOverFirst P).pmf (a, b, c, c') :=
    fun c' b c a => map_equiv_pmf (copyOverFirst P) e (c', (b, c), a)
  let Pac : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  have hQ13 : Q.map (fun s => (s.1, s.2.2)) = Pac.map Prod.swap := by
    calc Q.map (fun s => (s.1, s.2.2))
      _ = (copyOverFirst P).map (fun t => (t.2.2.2, t.1)) := by
          change ((copyOverFirst P).map e).map _ = _; rw [map_comp_eq]; rfl
      _ = ((copyOverFirst P).map (fun t => (t.1, t.2.2.2))).map Prod.swap := by
          rw [map_comp_eq]; rfl
      _ = Pac.map Prod.swap := by rw [copyOverFirst_marginal_14]
  have hQ23 : Q.map (fun s => (s.2.1, s.2.2)) = P.map Prod.swap := by
    calc Q.map (fun s => (s.2.1, s.2.2))
      _ = (copyOverFirst P).map (fun t => ((t.2.1, t.2.2.1), t.1)) := by
          change ((copyOverFirst P).map e).map _ = _; rw [map_comp_eq]; rfl
      _ = ((copyOverFirst P).map (fun t => (t.1, t.2.1, t.2.2.1))).map Prod.swap := by
          rw [map_comp_eq]; rfl
      _ = P.map Prod.swap := by rw [copyOverFirst_marginal_123]
  have hQ3 : Q.map (fun s => s.2.2) = P.fst := by
    calc Q.map (fun s => s.2.2)
      _ = (copyOverFirst P).map (fun t => t.1) := by
          change ((copyOverFirst P).map e).map _ = _; rw [map_comp_eq]; rfl
      _ = ((copyOverFirst P).map (fun t => (t.1, t.2.1, t.2.2.1))).map Prod.fst := by
          rw [map_comp_eq]; rfl
      _ = P.fst := by rw [copyOverFirst_marginal_123, fst_eq_map_fst]
  refine probDist_ext fun ⟨c', ⟨b, c⟩, a⟩ => ?_
  rw [hQ_pmf]
  change (copyOverFirst P).pmf (a, b, c, c') =
    if (Q.map (fun s => s.2.2)).pmf a = 0 then 0
    else (Q.map (fun s => (s.1, s.2.2))).pmf (c', a) *
      (Q.map (fun s => (s.2.1, s.2.2))).pmf ((b, c), a) / (Q.map (fun s => s.2.2)).pmf a
  rw [hQ13, hQ23, hQ3, swap_pmf_apply, swap_pmf_apply]
  simp only [copyOverFirst]
  split_ifs
  · rfl
  · ring

/-- Entropy identity of `copyOverFirst`: `H(A, B, C, C') = H(A, B, C) + H(A, C) - H(A)`. -/
theorem copyOverFirst_entropy (P : ProbDist (α × β × γ)) :
    shannonEntropy (copyOverFirst P) =
      shannonEntropy P + shannonEntropy (P.map (fun t => (t.1, t.2.2))) - shannonEntropy P.fst := by
  let e : (α × β × γ × γ) ≃ (γ × (β × γ) × α) :=
    { toFun := fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1)
      invFun := fun s => (s.2.2, s.2.1.1, s.2.1.2, s.1)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl }
  have hcmi := copyOverFirst_condIndep P
  unfold condMutualInfo at hcmi
  dsimp only at hcmi
  have h1 : ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))).map
      (fun s => (s.1, s.2.2)) = (P.map (fun t => (t.1, t.2.2))).map Prod.swap := by
    calc ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))).map
          (fun s => (s.1, s.2.2))
      _ = ((copyOverFirst P).map (fun t => (t.1, t.2.2.2))).map Prod.swap := by
          rw [map_comp_eq, map_comp_eq]; rfl
      _ = (P.map (fun t => (t.1, t.2.2))).map Prod.swap := by rw [copyOverFirst_marginal_14]
  have h2 : ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))).map
      (fun s => (s.2.1, s.2.2)) = P.map Prod.swap := by
    calc ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))).map
          (fun s => (s.2.1, s.2.2))
      _ = ((copyOverFirst P).map (fun t => (t.1, t.2.1, t.2.2.1))).map Prod.swap := by
          rw [map_comp_eq, map_comp_eq]; rfl
      _ = P.map Prod.swap := by rw [copyOverFirst_marginal_123]
  have h3 : ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))).map
      (fun s => s.2.2) = P.fst := by
    calc ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))).map
          (fun s => s.2.2)
      _ = ((copyOverFirst P).map (fun t => (t.1, t.2.1, t.2.2.1))).map Prod.fst := by
          rw [map_comp_eq, map_comp_eq]; rfl
      _ = P.fst := by rw [copyOverFirst_marginal_123, fst_eq_map_fst]
  have h4 : shannonEntropy ((copyOverFirst P).map (fun t => (t.2.2.2, (t.2.1, t.2.2.1), t.1))) =
      shannonEntropy (copyOverFirst P) := shannonEntropy_map_equiv e (copyOverFirst P)
  rw [h1, h2, h3, h4, shannonEntropy_swap, shannonEntropy_swap] at hcmi
  linarith

end CopyLemma

/-! ### 3. Zhang–Yeung (1998) Non-Shannon Information Inequality & `cl(Γ*_4) ⊊ Γ_4` -/

section ZhangYeung

/-- Bijection packaging `((C, D), B, A, R)` as a 5-tuple `![A, B, C, D, R] : Fin 5 → α`. -/
private def equivCopy5 (α : Type*) : ((α × α) × α × α × α) ≃ (Fin 5 → α) where
  toFun := fun t => ![t.2.2.1, t.2.1, t.1.1, t.1.2, t.2.2.2]
  invFun := fun y => ((y 2, y 3), y 1, y 0, y 4)
  left_inv := fun ⟨⟨_, _⟩, _, _, _⟩ => rfl
  right_inv := fun y => by
    funext i
    fin_cases i <;> rfl

/-- Bijection packaging `((C, D), B, A)` as a 4-tuple `![A, B, C, D] : Fin 4 → α`. -/
private def equivTuple4 (α : Type*) : ((α × α) × α × α) ≃ (Fin 4 → α) where
  toFun := fun t => ![t.2.2, t.2.1, t.1.1, t.1.2]
  invFun := fun x => ((x 2, x 3), x 1, x 0)
  left_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl
  right_inv := fun x => by
    funext i
    fin_cases i <;> rfl

/-- Entropy of a single-element subset `{i}` equals `H(X_i)`. -/
private lemma subsetEntropyVec_singleton {n k : ℕ} (P : ProbDist (Fin n → Fin k)) (i : Fin n) :
    subsetEntropyVec P {i} = shannonEntropy (P.map (fun x => x i)) := by
  let e : (∀ _ : ({i} : Finset (Fin n)), Fin k) ≃ Fin k :=
    { toFun := fun f => f ⟨i, Finset.mem_singleton_self i⟩
      invFun := fun a _ => a
      left_inv := fun f => by
        funext j
        have hj : j.1 = i := Finset.mem_singleton.mp j.2
        have hsub : j = ⟨i, Finset.mem_singleton_self i⟩ := Subtype.ext hj
        rw [hsub]
      right_inv := fun _ => rfl }
  unfold subsetEntropyVec
  rw [← shannonEntropy_map_equiv e, map_comp_eq]
  rfl

/-- Entropy of a 2-element subset `{i, j}` (`i ≠ j`) equals `H(X_i, X_j)`. -/
private lemma subsetEntropyVec_pair {n k : ℕ} (P : ProbDist (Fin n → Fin k)) {i j : Fin n}
    (hij : i ≠ j) :
    subsetEntropyVec P {i, j} = shannonEntropy (P.map (fun x => (x i, x j))) := by
  let e : (∀ _ : ({i, j} : Finset (Fin n)), Fin k) ≃ (Fin k × Fin k) :=
    { toFun := fun f => (f ⟨i, by simp⟩, f ⟨j, by simp⟩)
      invFun := fun ab t => if t.1 = i then ab.1 else ab.2
      left_inv := fun f => by
        funext t
        rcases Finset.mem_insert.mp t.2 with hi | hj
        · simp only [hi, ↓reduceIte]
          congr 1; exact Subtype.ext hi.symm
        · have hj' : t.1 = j := Finset.mem_singleton.mp hj
          have hne : t.1 ≠ i := by rw [hj']; exact hij.symm
          simp only [hne, ↓reduceIte]
          congr 1; exact Subtype.ext hj'.symm
      right_inv := fun ⟨a, b⟩ => by
        ext
        · simp
        · simp [hij.symm] }
  unfold subsetEntropyVec
  rw [← shannonEntropy_map_equiv e, map_comp_eq]
  rfl

/-- Entropy of a 3-element subset `{i, j, l}` (pairwise distinct) equals `H((X_i, X_j), X_l)`. -/
private lemma subsetEntropyVec_triple {n k : ℕ} (P : ProbDist (Fin n → Fin k)) {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    subsetEntropyVec P {i, j, l} = shannonEntropy (P.map (fun x => ((x i, x j), x l))) := by
  let e : (∀ _ : ({i, j, l} : Finset (Fin n)), Fin k) ≃ ((Fin k × Fin k) × Fin k) :=
    { toFun := fun f => ((f ⟨i, by simp⟩, f ⟨j, by simp⟩), f ⟨l, by simp⟩)
      invFun := fun abc t =>
        if t.1 = i then abc.1.1 else if t.1 = j then abc.1.2 else abc.2
      left_inv := fun f => by
        funext t
        rcases Finset.mem_insert.mp t.2 with hi | hjl_mem
        · simp only [hi, ↓reduceIte]
          congr 1; exact Subtype.ext hi.symm
        · rcases Finset.mem_insert.mp hjl_mem with hj | hl_mem
          · simp only [hj, hij.symm, ↓reduceIte]
            congr 1; exact Subtype.ext hj.symm
          · have hl : t.1 = l := Finset.mem_singleton.mp hl_mem
            have hne1 : t.1 ≠ i := by rw [hl]; exact hil.symm
            have hne2 : t.1 ≠ j := by rw [hl]; exact hjl.symm
            simp only [hne1, hne2, ↓reduceIte]
            congr 1; exact Subtype.ext hl.symm
      right_inv := fun ⟨⟨a, b⟩, c⟩ => by
        simp [hij.symm, hil.symm, hjl.symm] }
  unfold subsetEntropyVec
  rw [← shannonEntropy_map_equiv e, map_comp_eq]
  rfl

/-- Entropy of the full subset `Finset.univ` equals `H(P)`. -/
private lemma subsetEntropyVec_univ {n k : ℕ} (P : ProbDist (Fin n → Fin k)) :
    subsetEntropyVec P Finset.univ = shannonEntropy P := by
  let e : (∀ _ : (Finset.univ : Finset (Fin n)), Fin k) ≃ (Fin n → Fin k) :=
    { toFun := fun f i => f ⟨i, Finset.mem_univ i⟩
      invFun := fun x i => x i.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold subsetEntropyVec
  rw [← shannonEntropy_map_equiv e, map_comp_eq]
  have hid : (e ∘ fun x (i : (Finset.univ : Finset (Fin n))) => x i.1) = id := rfl
  rw [hid]
  classical
  cases P with
  | mk pmf nonneg sum_one =>
    unfold ProbDist.map
    congr; funext x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- Restriction of a 5-variable distribution whose `(0, 1, 2, 3)` marginal is `P` preserves
    all subset entropies on `Fin 4`. -/
private lemma subsetEntropyVec_embed4 {k : ℕ} (P : ProbDist (Fin 4 → Fin k))
    (Q : ProbDist (Fin 5 → Fin k))
    (hmarg : Q.map (fun y (i : Fin 4) => y i.castSucc) = P)
    (S : Finset (Fin 4)) :
    subsetEntropyVec Q (S.map Fin.castSuccEmb) = subsetEntropyVec P S := by
  let e : (∀ _ : (S.map Fin.castSuccEmb : Finset (Fin 5)), Fin k) ≃ (∀ _ : S, Fin k) :=
    { toFun := fun f i => f ⟨i.1.castSucc, Finset.mem_map.mpr ⟨i.1, i.2, rfl⟩⟩
      invFun := fun g j =>
        let hj := Finset.mem_map.mp j.2
        g ⟨hj.choose, hj.choose_spec.1⟩
      left_inv := fun f => by
        funext j
        dsimp only
        have hspec := (Finset.mem_map.mp j.2).choose_spec.2
        congr 1
        exact Subtype.ext hspec
      right_inv := fun g => by
        funext i
        dsimp only
        have hmem : i.1.castSucc ∈ S.map Fin.castSuccEmb := Finset.mem_map.mpr ⟨i.1, i.2, rfl⟩
        have hspec : (Finset.mem_map.mp hmem).choose.castSucc = i.1.castSucc :=
          (Finset.mem_map.mp hmem).choose_spec.2
        have heq : (Finset.mem_map.mp hmem).choose = i.1 := Fin.castSucc_inj.mp hspec
        congr 1
        exact Subtype.ext heq }
  unfold subsetEntropyVec
  rw [← shannonEntropy_map_equiv e, map_comp_eq, ← hmarg, map_comp_eq]
  rfl

/-- **Zhang–Yeung (1998) Non-Shannon Information Inequality for Any 4-Variable Distribution**
    (Zhang & Yeung, *IEEE Trans. Inform. Theory* 44(4), 1998, Theorem 1; Yeung, *Information Theory
    and Network Coding*, Theorem 15.7):

    For any joint distribution `P` on 4 discrete random variables `(A, B, C, D) = (X_0, X_1, X_2, X_3)`,
    writing `h := subsetEntropyVec P`:
    ```
    2 I(C; D) ≤ I(A; B) + I(A; C, D) + 3 I(C; D | A) + I(C; D | B)
    ```
    Proved by applying the Copy Lemma (`copyOverFirst`) to copy `A = X_0` over `(C, D) = (X_2, X_3)`
    into a 5th variable `R = X_4`, and summing 10 submodularity inequalities on `(A, B, C, D, R)`. -/
theorem zhang_yeung_subsetEntropyVec {k : ℕ} (P : ProbDist (Fin 4 → Fin k)) :
    let h := subsetEntropyVec P
    let I (A B : Finset (Fin 4)) : ℝ := h A + h B - h (A ∪ B)
    let cI (A B C : Finset (Fin 4)) : ℝ := h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C
    2 * I {2} {3} ≤ I {0} {1} + I {0} ({2, 3} : Finset (Fin 4)) +
      3 * cI {2} {3} {0} + cI {2} {3} {1} := by
  let P_reorg : ProbDist ((Fin k × Fin k) × Fin k × Fin k) := P.map (equivTuple4 (Fin k)).symm
  let Q_copy : ProbDist ((Fin k × Fin k) × Fin k × Fin k × Fin k) := copyOverFirst P_reorg
  let Q : ProbDist (Fin 5 → Fin k) := Q_copy.map (equivCopy5 (Fin k))
  let h := subsetEntropyVec P
  let H := subsetEntropyVec Q
  -- 1. Marginal on {0, 1, 2, 3} equals P
  have hQ_marg4 : Q.map (fun y (i : Fin 4) => y i.castSucc) = P := by
    have hcomp1 : Q.map (fun y (i : Fin 4) => y i.castSucc) =
        (Q_copy.map (fun t => (t.1, t.2.1, t.2.2.1))).map (equivTuple4 (Fin k)) := by
      simp only [Q]
      rw [map_comp_eq, map_comp_eq]
      congr 1; funext ⟨⟨c, d⟩, b, a, r⟩; funext i; fin_cases i <;> rfl
    rw [hcomp1, copyOverFirst_marginal_123]
    simp only [P_reorg]
    rw [map_comp_eq]
    have hid : ((equivTuple4 (Fin k)) ∘ (equivTuple4 (Fin k)).symm) = id :=
      funext (equivTuple4 (Fin k)).apply_symm_apply
    rw [hid]
    classical
    cases P with
    | mk pmf nonneg sum_one =>
      unfold ProbDist.map
      congr; funext x
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
  have h4 : ∀ S : Finset (Fin 4), H (S.map Fin.castSuccEmb) = h S :=
    fun S => subsetEntropyVec_embed4 P Q hQ_marg4 S
  -- 2. Marginal of ((C, D), R) in Q equals ((C, D), A) in P
  have hQ_copy : Q.map (fun y => ((y 2, y 3), y 4)) = P.map (fun x => ((x 2, x 3), x 0)) := by
    have h1 : Q.map (fun y => ((y 2, y 3), y 4)) = Q_copy.map (fun t => (t.1, t.2.2.2)) := by
      simp only [Q]; rw [map_comp_eq]; rfl
    rw [h1, copyOverFirst_marginal_14]
    simp only [P_reorg]; rw [map_comp_eq]; rfl
  -- Extract the four copy equalities: H(R)=h(A), H(C,R)=h(A,C), H(D,R)=h(A,D), H(C,D,R)=h(A,C,D)
  have hR_eq : H {4} = h {0} := by
    change subsetEntropyVec Q {4} = subsetEntropyVec P {0}
    rw [subsetEntropyVec_singleton, subsetEntropyVec_singleton]
    have hm : Q.map (fun y => y 4) = P.map (fun x => x 0) := by
      calc Q.map (fun y => y 4)
        _ = (Q.map (fun y => ((y 2, y 3), y 4))).map Prod.snd :=
            (map_comp_eq Q (fun y => ((y 2, y 3), y 4)) Prod.snd).symm
        _ = (P.map (fun x => ((x 2, x 3), x 0))).map Prod.snd := by rw [hQ_copy]
        _ = P.map (fun x => x 0) := map_comp_eq P (fun x => ((x 2, x 3), x 0)) Prod.snd
    rw [hm]
  have hCR_eq : H {2, 4} = h {0, 2} := by
    change subsetEntropyVec Q {2, 4} = subsetEntropyVec P {0, 2}
    rw [subsetEntropyVec_pair Q (by decide), subsetEntropyVec_pair P (by decide)]
    have hm : Q.map (fun y => (y 2, y 4)) = P.map (fun x => (x 2, x 0)) := by
      calc Q.map (fun y => (y 2, y 4))
        _ = (Q.map (fun y => ((y 2, y 3), y 4))).map
            (fun t : (Fin k × Fin k) × Fin k => (t.1.1, t.2)) :=
            (map_comp_eq Q (fun y => ((y 2, y 3), y 4))
              (fun t : (Fin k × Fin k) × Fin k => (t.1.1, t.2))).symm
        _ = (P.map (fun x => ((x 2, x 3), x 0))).map
            (fun t : (Fin k × Fin k) × Fin k => (t.1.1, t.2)) := by rw [hQ_copy]
        _ = P.map (fun x => (x 2, x 0)) :=
            map_comp_eq P (fun x => ((x 2, x 3), x 0))
              (fun t : (Fin k × Fin k) × Fin k => (t.1.1, t.2))
    rw [hm]
    have hswap : P.map (fun x => (x 2, x 0)) = (P.map (fun x => (x 0, x 2))).map Prod.swap := by
      rw [map_comp_eq]; rfl
    rw [hswap, shannonEntropy_swap]
  have hDR_eq : H {3, 4} = h {0, 3} := by
    change subsetEntropyVec Q {3, 4} = subsetEntropyVec P {0, 3}
    rw [subsetEntropyVec_pair Q (by decide), subsetEntropyVec_pair P (by decide)]
    have hm : Q.map (fun y => (y 3, y 4)) = P.map (fun x => (x 3, x 0)) := by
      calc Q.map (fun y => (y 3, y 4))
        _ = (Q.map (fun y => ((y 2, y 3), y 4))).map
            (fun t : (Fin k × Fin k) × Fin k => (t.1.2, t.2)) :=
            (map_comp_eq Q (fun y => ((y 2, y 3), y 4))
              (fun t : (Fin k × Fin k) × Fin k => (t.1.2, t.2))).symm
        _ = (P.map (fun x => ((x 2, x 3), x 0))).map
            (fun t : (Fin k × Fin k) × Fin k => (t.1.2, t.2)) := by rw [hQ_copy]
        _ = P.map (fun x => (x 3, x 0)) :=
            map_comp_eq P (fun x => ((x 2, x 3), x 0))
              (fun t : (Fin k × Fin k) × Fin k => (t.1.2, t.2))
    rw [hm]
    have hswap : P.map (fun x => (x 3, x 0)) = (P.map (fun x => (x 0, x 3))).map Prod.swap := by
      rw [map_comp_eq]; rfl
    rw [hswap, shannonEntropy_swap]
  -- 3. Conditional independence identity: H(A,B,C,D,R) = h(A,B,C,D) + h(A,C,D) - h(C,D)
  have hFull_eq : H {0, 1, 2, 3, 4} = h {0, 1, 2, 3} + h {0, 2, 3} - h {2, 3} := by
    have hent := copyOverFirst_entropy P_reorg
    have hLHS : shannonEntropy Q_copy = H {0, 1, 2, 3, 4} := by
      have huniv : ({0, 1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
      rw [huniv]
      change shannonEntropy Q_copy = subsetEntropyVec Q Finset.univ
      rw [subsetEntropyVec_univ]
      exact (shannonEntropy_map_equiv (equivCopy5 (Fin k)) Q_copy).symm
    have hP_ent : shannonEntropy P_reorg = h {0, 1, 2, 3} := by
      have huniv : ({0, 1, 2, 3} : Finset (Fin 4)) = Finset.univ := by decide
      rw [huniv]
      change shannonEntropy P_reorg = subsetEntropyVec P Finset.univ
      rw [subsetEntropyVec_univ]
      exact shannonEntropy_map_equiv (equivTuple4 (Fin k)).symm P
    have hACD : shannonEntropy (P_reorg.map (fun t => (t.1, t.2.2))) = h {0, 2, 3} := by
      have hperm : ({0, 2, 3} : Finset (Fin 4)) = {2, 3, 0} := by decide
      rw [hperm]
      change shannonEntropy (P_reorg.map (fun t => (t.1, t.2.2))) = subsetEntropyVec P {2, 3, 0}
      rw [subsetEntropyVec_triple P (by decide) (by decide) (by decide)]
      simp only [P_reorg]; rw [map_comp_eq]; rfl
    have hCD : shannonEntropy P_reorg.fst = h {2, 3} := by
      change shannonEntropy P_reorg.fst = subsetEntropyVec P {2, 3}
      rw [subsetEntropyVec_pair P (by decide), fst_eq_map_fst]
      simp only [P_reorg]; rw [map_comp_eq]; rfl
    rw [← hLHS, ← hP_ent, ← hACD, ← hCD]
    exact hent
  -- 4. Apply 10 submodularity inequalities on H = subsetEntropyVec Q
  have hsub : ∀ S T : Finset (Fin 5), H (S ∪ T) + H (S ∩ T) ≤ H S + H T :=
    (subsetEntropyVec_isPolymatroid Q).2.2
  have s1 := hsub {0, 4} {1, 4}
  have s2 := hsub {0, 2} {2, 4}
  have s3 := hsub {0, 3} {3, 4}
  have s4 := hsub {0, 2, 4} {0, 3, 4}
  have s5 := hsub {1, 2} {2, 4}
  have s6 := hsub {1, 3} {3, 4}
  have s7 := hsub {1, 2, 4} {1, 3, 4}
  have s8 := hsub {0, 1, 2, 3} {1, 2, 3, 4}
  have s9 := hsub {0, 1, 2, 3} {0, 2, 3, 4}
  have s10 := hsub {0, 1, 2, 3} {0, 1, 4}
  -- Normalize Finset unions & intersections in s1..s10
  have u1 : ({0, 4} : Finset (Fin 5)) ∪ {1, 4} = {0, 1, 4} := by decide
  have i1 : ({0, 4} : Finset (Fin 5)) ∩ {1, 4} = {4} := by decide
  have u2 : ({0, 2} : Finset (Fin 5)) ∪ {2, 4} = {0, 2, 4} := by decide
  have i2 : ({0, 2} : Finset (Fin 5)) ∩ {2, 4} = {2} := by decide
  have u3 : ({0, 3} : Finset (Fin 5)) ∪ {3, 4} = {0, 3, 4} := by decide
  have i3 : ({0, 3} : Finset (Fin 5)) ∩ {3, 4} = {3} := by decide
  have u4 : ({0, 2, 4} : Finset (Fin 5)) ∪ {0, 3, 4} = {0, 2, 3, 4} := by decide
  have i4 : ({0, 2, 4} : Finset (Fin 5)) ∩ {0, 3, 4} = {0, 4} := by decide
  have u5 : ({1, 2} : Finset (Fin 5)) ∪ {2, 4} = {1, 2, 4} := by decide
  have i5 : ({1, 2} : Finset (Fin 5)) ∩ {2, 4} = {2} := by decide
  have u6 : ({1, 3} : Finset (Fin 5)) ∪ {3, 4} = {1, 3, 4} := by decide
  have i6 : ({1, 3} : Finset (Fin 5)) ∩ {3, 4} = {3} := by decide
  have u7 : ({1, 2, 4} : Finset (Fin 5)) ∪ {1, 3, 4} = {1, 2, 3, 4} := by decide
  have i7 : ({1, 2, 4} : Finset (Fin 5)) ∩ {1, 3, 4} = {1, 4} := by decide
  have u8 : ({0, 1, 2, 3} : Finset (Fin 5)) ∪ {1, 2, 3, 4} = {0, 1, 2, 3, 4} := by decide
  have i8 : ({0, 1, 2, 3} : Finset (Fin 5)) ∩ {1, 2, 3, 4} = {1, 2, 3} := by decide
  have u9 : ({0, 1, 2, 3} : Finset (Fin 5)) ∪ {0, 2, 3, 4} = {0, 1, 2, 3, 4} := by decide
  have i9 : ({0, 1, 2, 3} : Finset (Fin 5)) ∩ {0, 2, 3, 4} = {0, 2, 3} := by decide
  have u10 : ({0, 1, 2, 3} : Finset (Fin 5)) ∪ {0, 1, 4} = {0, 1, 2, 3, 4} := by decide
  have i10 : ({0, 1, 2, 3} : Finset (Fin 5)) ∩ {0, 1, 4} = {0, 1} := by decide
  rw [u1, i1] at s1; rw [u2, i2] at s2; rw [u3, i3] at s3; rw [u4, i4] at s4
  rw [u5, i5] at s5; rw [u6, i6] at s6; rw [u7, i7] at s7; rw [u8, i8] at s8
  rw [u9, i9] at s9; rw [u10, i10] at s10
  -- Identify all embedded Fin 4 subsets via h4
  have eC : H {2} = h {2} := by simpa using h4 {2}
  have eD : H {3} = h {3} := by simpa using h4 {3}
  have eAB : H {0, 1} = h {0, 1} := by simpa using h4 {0, 1}
  have eAC : H {0, 2} = h {0, 2} := by simpa using h4 {0, 2}
  have eAD : H {0, 3} = h {0, 3} := by simpa using h4 {0, 3}
  have eBC : H {1, 2} = h {1, 2} := by simpa using h4 {1, 2}
  have eBD : H {1, 3} = h {1, 3} := by simpa using h4 {1, 3}
  have eACD : H {0, 2, 3} = h {0, 2, 3} := by simpa using h4 {0, 2, 3}
  have eBCD : H {1, 2, 3} = h {1, 2, 3} := by simpa using h4 {1, 2, 3}
  have eABCD : H {0, 1, 2, 3} = h {0, 1, 2, 3} := by simpa using h4 {0, 1, 2, 3}
  -- Normalize the Fin 4 set expressions in the goal
  have g1 : ({2} : Finset (Fin 4)) ∪ {3} = {2, 3} := by decide
  have g2 : ({0} : Finset (Fin 4)) ∪ {1} = {0, 1} := by decide
  have g3 : ({0} : Finset (Fin 4)) ∪ ({2, 3} : Finset (Fin 4)) = {0, 2, 3} := by decide
  have g4 : ({2} : Finset (Fin 4)) ∪ {0} = {0, 2} := by decide
  have g5 : ({3} : Finset (Fin 4)) ∪ {0} = {0, 3} := by decide
  have g6 : ({2, 3} : Finset (Fin 4)) ∪ {0} = {0, 2, 3} := by decide
  have g7 : ({2} : Finset (Fin 4)) ∪ {1} = {1, 2} := by decide
  have g8 : ({3} : Finset (Fin 4)) ∪ {1} = {1, 3} := by decide
  have g9 : ({2, 3} : Finset (Fin 4)) ∪ {1} = {1, 2, 3} := by decide
  dsimp only
  rw [g1, g2, g3, g4, g5, g6, g7, g8, g9]
  linarith [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    hR_eq, hCR_eq, hDR_eq, hFull_eq,
    eC, eD, eAB, eAC, eAD, eBC, eBD, eACD, eBCD, eABCD]

/-- **Zhang–Yeung (1998) Inequality on `Γ*_4`**: every entropic vector on 4 variables satisfies
    the Zhang–Yeung non-Shannon information inequality. -/
theorem zhang_yeung_entropic {h : Finset (Fin 4) → ℝ} (hent : IsEntropicVector 4 h) :
    let I (A B : Finset (Fin 4)) : ℝ := h A + h B - h (A ∪ B)
    let cI (A B C : Finset (Fin 4)) : ℝ := h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C
    2 * I {2} {3} ≤ I {0} {1} + I {0} ({2, 3} : Finset (Fin 4)) +
      3 * cI {2} {3} {0} + cI {2} {3} {1} := by
  obtain ⟨k, P, hP⟩ := hent
  have key := zhang_yeung_subsetEntropyVec P
  dsimp only at key ⊢
  simp_rw [hP]
  exact key

/-- **Zhang–Yeung (1998) Inequality on `cl(Γ*_4)`**: by continuity of linear inequalities, every
    almost-entropic vector on 4 variables satisfies the Zhang–Yeung inequality. -/
theorem zhang_yeung_almostEntropic {h : Finset (Fin 4) → ℝ} (hae : InAlmostEntropicCone 4 h) :
    let I (A B : Finset (Fin 4)) : ℝ := h A + h B - h (A ∪ B)
    let cI (A B C : Finset (Fin 4)) : ℝ := h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C
    2 * I {2} {3} ≤ I {0} {1} + I {0} ({2, 3} : Finset (Fin 4)) +
      3 * cI {2} {3} {0} + cI {2} {3} {1} := by
  dsimp only
  by_contra hlt
  rw [not_le] at hlt
  set lhs := 2 * (h {2} + h {3} - h ({2} ∪ {3}))
  set rhs := (h {0} + h {1} - h ({0} ∪ {1})) +
    (h {0} + h ({2, 3} : Finset (Fin 4)) - h ({0} ∪ {2, 3})) +
    3 * (h ({2} ∪ {0}) + h ({3} ∪ {0}) - h ({2} ∪ {3} ∪ {0}) - h {0}) +
    (h ({2} ∪ {1}) + h ({3} ∪ {1}) - h ({2} ∪ {3} ∪ {1}) - h {1})
  have hδ : 0 < lhs - rhs := by linarith
  obtain ⟨h', hh', hclose⟩ := hae ((lhs - rhs) / 30) (by linarith)
  have hzy := zhang_yeung_entropic hh'
  dsimp only at hzy
  have c0 := abs_lt.mp (hclose {0})
  have c1 := abs_lt.mp (hclose {1})
  have c2 := abs_lt.mp (hclose {2})
  have c3 := abs_lt.mp (hclose {3})
  have c23u := abs_lt.mp (hclose ({2} ∪ {3}))
  have c01 := abs_lt.mp (hclose ({0} ∪ {1}))
  have c23 := abs_lt.mp (hclose ({2, 3} : Finset (Fin 4)))
  have c023 := abs_lt.mp (hclose ({0} ∪ ({2, 3} : Finset (Fin 4))))
  have c20 := abs_lt.mp (hclose ({2} ∪ {0}))
  have c30 := abs_lt.mp (hclose ({3} ∪ {0}))
  have c230 := abs_lt.mp (hclose ({2} ∪ {3} ∪ {0}))
  have c21 := abs_lt.mp (hclose ({2} ∪ {1}))
  have c31 := abs_lt.mp (hclose ({3} ∪ {1}))
  have c231 := abs_lt.mp (hclose ({2} ∪ {3} ∪ {1}))
  linarith [hzy,
    c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2,
    c23u.1, c23u.2, c01.1, c01.2, c23.1, c23.2, c023.1, c023.2,
    c20.1, c20.2, c30.1, c30.2, c230.1, c230.2,
    c21.1, c21.2, c31.1, c31.2, c231.1, c231.2]

/-- Explicit 4-variable integer polymatroid witnessing `cl(Γ*_4) ⊊ Γ_4`:
    `h(∅) = 0`, `h(i) = 2`, `h({0, 1}) = 4`, `h(ij) = 3` for all other pairs, and `h = 4` on
    all sets of size `≥ 3`. -/
private def zhangYeungWitness (S : Finset (Fin 4)) : ℕ :=
  if S.card = 0 then 0 else if S.card = 1 then 2 else if S.card = 2 ∧ S ≠ {0, 1} then 3 else 4

private lemma zhangYeungWitness_isPolymatroid :
    IsPolymatroid 4 (fun S => (zhangYeungWitness S : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [zhangYeungWitness]
  · have key : ∀ S T : Finset (Fin 4), S ⊆ T → zhangYeungWitness S ≤ zhangYeungWitness T := by
      decide
    intro S T hST
    beta_reduce
    exact_mod_cast key S T hST
  · have key : ∀ S T : Finset (Fin 4),
        zhangYeungWitness (S ∪ T) + zhangYeungWitness (S ∩ T) ≤
          zhangYeungWitness S + zhangYeungWitness T := by
      decide
    intro S T
    beta_reduce
    exact_mod_cast key S T

/-- **Existence of a Non-Almost-Entropic Polymatroid** (Zhang–Yeung 1998, Theorem 1):
    there exists a 4-variable polymatroid `h ∈ Γ_4` that does not lie in `cl(Γ*_4)`,
    witnessed by `zhangYeungWitness` violating the Zhang–Yeung inequality (`2 > 1`). -/
theorem exists_polymatroid_not_almostEntropic :
    ∃ h : Finset (Fin 4) → ℝ, IsPolymatroid 4 h ∧ ¬ InAlmostEntropicCone 4 h := by
  refine ⟨fun S => (zhangYeungWitness S : ℝ), zhangYeungWitness_isPolymatroid, fun hae => ?_⟩
  have hzy := zhang_yeung_almostEntropic hae
  dsimp only at hzy
  have v0 : zhangYeungWitness {0} = 2 := by decide
  have v1 : zhangYeungWitness {1} = 2 := by decide
  have v2 : zhangYeungWitness {2} = 2 := by decide
  have v3 : zhangYeungWitness {3} = 2 := by decide
  have v23u : zhangYeungWitness ({2} ∪ {3}) = 3 := by decide
  have v01 : zhangYeungWitness ({0} ∪ {1}) = 4 := by decide
  have v23 : zhangYeungWitness ({2, 3} : Finset (Fin 4)) = 3 := by decide
  have v023 : zhangYeungWitness ({0} ∪ ({2, 3} : Finset (Fin 4))) = 4 := by decide
  have v20 : zhangYeungWitness ({2} ∪ {0}) = 3 := by decide
  have v30 : zhangYeungWitness ({3} ∪ {0}) = 3 := by decide
  have v230 : zhangYeungWitness ({2} ∪ {3} ∪ {0}) = 4 := by decide
  have v21 : zhangYeungWitness ({2} ∪ {1}) = 3 := by decide
  have v31 : zhangYeungWitness ({3} ∪ {1}) = 3 := by decide
  have v231 : zhangYeungWitness ({2} ∪ {3} ∪ {1}) = 4 := by decide
  simp only [v0, v1, v2, v3, v23u, v01, v23, v023, v20, v30, v230, v21, v31, v231] at hzy
  norm_num at hzy

/-- **Existence of a Non-Entropic Polymatroid**: `Γ*_4 ⊊ Γ_4`. -/
theorem exists_polymatroid_not_entropic :
    ∃ h : Finset (Fin 4) → ℝ, IsPolymatroid 4 h ∧ ¬ IsEntropicVector 4 h := by
  obtain ⟨h, hp, hnae⟩ := exists_polymatroid_not_almostEntropic
  refine ⟨h, hp, fun hent => hnae fun ε hε => ⟨h, hent, fun S => by simpa using hε⟩⟩

/-- **Strict Inclusion `cl(Γ*_4) ⊊ Γ_4`** (Zhang–Yeung 1998): the almost-entropic cone of four
    random variables is a strict subset of the Shannon polymatroid cone. -/
theorem almostEntropic4_ssubset_polymatroid4 :
    { h : Finset (Fin 4) → ℝ | InAlmostEntropicCone 4 h } ⊂ { h | IsPolymatroid 4 h } := by
  refine ⟨fun h hae => ?_, ?_⟩
  · -- cl(Γ*_4) ⊆ Γ_4 via `subsetEntropyVec_isPolymatroid`
    refine ⟨?_, ?_, ?_⟩
    · by_contra hne
      obtain ⟨h', ⟨k, P, hP⟩, hclose⟩ := hae |h ∅| (abs_pos.mpr hne)
      have h0 : h' ∅ = 0 := by rw [hP]; exact (subsetEntropyVec_isPolymatroid P).1
      have hc := hclose ∅
      rw [h0, sub_zero] at hc
      exact lt_irrefl _ hc
    · intro S T hST
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨h', ⟨k, P, hP⟩, hclose⟩ := hae ((h S - h T) / 2) (by linarith)
      have hm : h' S ≤ h' T := by
        rw [hP, hP]; exact (subsetEntropyVec_isPolymatroid P).2.1 S T hST
      have h1 := abs_lt.mp (hclose S)
      have h2 := abs_lt.mp (hclose T)
      linarith [h1.1, h1.2, h2.1, h2.2]
    · intro S T
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨h', ⟨k, P, hP⟩, hclose⟩ :=
        hae ((h (S ∪ T) + h (S ∩ T) - h S - h T) / 4) (by linarith)
      have hm : h' (S ∪ T) + h' (S ∩ T) ≤ h' S + h' T := by
        rw [hP, hP, hP, hP]; exact (subsetEntropyVec_isPolymatroid P).2.2 S T
      have h1 := abs_lt.mp (hclose (S ∪ T))
      have h2 := abs_lt.mp (hclose (S ∩ T))
      have h3 := abs_lt.mp (hclose S)
      have h4 := abs_lt.mp (hclose T)
      linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  · intro hsub
    obtain ⟨h, hp, hnae⟩ := exists_polymatroid_not_almostEntropic
    exact hnae (hsub hp)

end ZhangYeung

end InfoTheory.Bridge
