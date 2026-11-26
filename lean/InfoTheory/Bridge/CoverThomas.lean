import InfoTheory.Bridge.Mathlib

/-!
# Cover & Thomas (Ch. 2–3) and El Gamal–Kim (Ch. 2) Core Toolkit

Purely additive, kernel-verified foundational theorems built directly on top of
`InfoTheory.Bridge.Mathlib` (which bridges `InfoTheory.Core` to `Mathlib.InformationTheory`):

1. **Chain Rules, Symmetry, Conditioning & Strong Subadditivity (Cover & Thomas §§2.2–2.6,
   El Gamal–Kim §2.1)**:
   - `shannonEntropy_map_equiv`, `shannonEntropy_swap`, `mutualInfo_swap`
   - `shannonEntropy_prod`, `shannonEntropy_subadd`, `shannonEntropy_chain_rule`
   - `condEntropy_nonneg`, `condEntropy_le_log2_card`, `shannonEntropy_map_le`
   - `condMutualInfo_eq_klDivergence`, `condMutualInfo_nonneg` (strong subadditivity!)
   - `subsetEntropyVec_isPolymatroid` (`Γ*_n ⊆ Γ_n`)
2. **Fano's Inequality (Cover & Thomas Theorem 2.10.1, El Gamal–Kim §2.1)**:
   - `fano_inequality` (sharp form `H(X | Y) ≤ h(P_e) + P_e log₂(|α| - 1)` for `2 ≤ |α|`,
     proved via a single application of Mathlib's Gibbs inequality `klDivergence_nonneg`!)
   - `fano_inequality_card` (`H(X | Y) ≤ h(P_e) + P_e log₂|α|` for all `[Nonempty α]`)
3. **Asymptotic Equipartition Property (AEP) & Weak Typicality (Cover & Thomas Ch. 3,
   Theorems 3.1.1 & 3.1.2)**:
   - `iidDist`, `weakTypicalSet`
   - `iidDist_prob_not_typical_le` (explicit `O(1 / (n ε²))` Chebyshev tail bound)
   - `aep_typical_prob_tendsto_one`
   - `weakTypicalSet_card_le` and `weakTypicalSet_card_ge`

All theorems leave `Core/`, `Problems/`, `STATEMENT_LOCK.json`, and `Known/` untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Chain Rules, Symmetry, Conditioning & Strong Subadditivity -/

section EntropyCalculus

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma log2_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2; rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy), add_div]

lemma log2_div_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log2 (x / y) = log2 x - log2 y := by
  unfold log2; rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy), sub_div]

lemma negPLogP_nonneg {p : ℝ} (hp1 : p ≤ 1) : 0 ≤ negPLogP p := by
  unfold negPLogP log2
  by_cases hp : p ≤ 0
  · simp [hp]
  · simp only [ite_eq_right_iff.mpr (fun h => absurd h hp)]
    have hpos : 0 < p := lt_of_not_ge hp
    have hlogp : Real.log p ≤ 0 := Real.log_nonpos (le_of_lt hpos) hp1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : Real.log p / Real.log 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlogp (le_of_lt hlog2)
    nlinarith

lemma negPLogP_zero : negPLogP 0 = 0 := by simp [negPLogP]

/-- Bijections preserve Shannon entropy: `H(e(X)) = H(X)`. -/
theorem shannonEntropy_map_equiv (e : α ≃ β) (P : ProbDist α) :
    shannonEntropy (P.map e) = shannonEntropy P := by
  classical
  have hpmf : ∀ b : β, (P.map e).pmf b = P.pmf (e.symm b) := by
    intro b
    unfold ProbDist.map
    dsimp only
    rw [Finset.sum_eq_single (e.symm b)]
    · simp
    · intro a _ hne
      have : e a ≠ b := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold shannonEntropy
  simp_rw [hpmf]
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- Swapping coordinates preserves joint entropy: `H(Y, X) = H(X, Y)`. -/
theorem shannonEntropy_swap (P : ProbDist (α × β)) :
    shannonEntropy (P.map Prod.swap) = shannonEntropy P :=
  shannonEntropy_map_equiv (Equiv.prodComm α β) P

lemma fst_map_swap (P : ProbDist (α × β)) : (P.map Prod.swap).fst = P.snd := by
  classical
  unfold ProbDist.fst ProbDist.snd ProbDist.map
  congr
  funext b
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne; simp [Prod.swap, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma snd_map_swap (P : ProbDist (α × β)) : (P.map Prod.swap).snd = P.fst := by
  classical
  unfold ProbDist.fst ProbDist.snd ProbDist.map
  congr
  funext a
  rw [Finset.sum_comm, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; simp [Prod.swap, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Symmetry of Mutual Information** (Cover & Thomas, §2.4): `I(Y; X) = I(X; Y)`. -/
theorem mutualInfo_swap (P : ProbDist (α × β)) :
    mutualInfo (P.map Prod.swap) = mutualInfo P := by
  unfold mutualInfo
  rw [fst_map_swap, snd_map_swap, shannonEntropy_swap]
  ring

/-- **Chain Rule for Entropy** (Cover & Thomas, Theorem 2.2.1): `H(X, Y) = H(Y) + H(X | Y)`. -/
theorem shannonEntropy_chain_rule (P : ProbDist (α × β)) :
    shannonEntropy P = shannonEntropy P.snd + condEntropy P := by
  unfold condEntropy; ring

/-- **Subadditivity of Entropy** (Cover & Thomas, Corollary to Thm. 2.6.5):
    `H(X, Y) ≤ H(X) + H(Y)`. -/
theorem shannonEntropy_subadd (P : ProbDist (α × β)) :
    shannonEntropy P ≤ shannonEntropy P.fst + shannonEntropy P.snd := by
  have h := mutualInfo_nonneg P
  unfold mutualInfo at h
  linarith

/-- **Additivity for Independent Variables**: `H(P × Q) = H(P) + H(Q)`. -/
theorem shannonEntropy_prod (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy (P.prod Q) = shannonEntropy P + shannonEntropy Q := by
  have hfst : (P.prod Q).fst = P := by
    unfold ProbDist.fst ProbDist.prod
    congr; funext a; simp [← Finset.mul_sum, Q.sum_one]
  have hsnd : (P.prod Q).snd = Q := by
    unfold ProbDist.snd ProbDist.prod
    congr; funext b; simp [← Finset.sum_mul, P.sum_one]
  have hmi : mutualInfo (P.prod Q) = 0 := by
    rw [mutualInfo_eq_zero_iff_indep, hfst, hsnd]
  unfold mutualInfo at hmi
  rw [hfst, hsnd] at hmi
  linarith

/-- **Non-negativity of Conditional Entropy** (Cover & Thomas, §2.2): `H(X | Y) ≥ 0`. -/
theorem condEntropy_nonneg (P : ProbDist (α × β)) : 0 ≤ condEntropy P := by
  unfold condEntropy shannonEntropy
  rw [Fintype.sum_prod_type_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun b _ => ?_
  have hterm : ∀ a : α, P.pmf (a, b) ≤ P.snd.pmf b := fun a =>
    Finset.single_le_sum (fun a' _ => P.nonneg (a', b)) (Finset.mem_univ a)
  by_cases hb : P.snd.pmf b ≤ 0
  · have hb0 : P.snd.pmf b = 0 := le_antisymm hb (P.snd.nonneg b)
    have hall : ∀ a : α, P.pmf (a, b) = 0 := fun a => le_antisymm (by linarith [hterm a]) (P.nonneg (a, b))
    simp [hb0, hall, negPLogP]
  · have hbpos : 0 < P.snd.pmf b := lt_of_not_ge hb
    have hle : ∀ a : α, -P.pmf (a, b) * log2 (P.snd.pmf b) ≤ negPLogP (P.pmf (a, b)) := by
      intro a
      by_cases ha : P.pmf (a, b) ≤ 0
      · have ha0 : P.pmf (a, b) = 0 := le_antisymm ha (P.nonneg (a, b))
        simp [ha0, negPLogP]
      · have hapos : 0 < P.pmf (a, b) := lt_of_not_ge ha
        simp only [negPLogP, ite_eq_right_iff.mpr (fun h => absurd h ha)]
        have hlog : log2 (P.pmf (a, b)) ≤ log2 (P.snd.pmf b) := by
          unfold log2
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          exact div_le_div_of_nonneg_right (Real.log_le_log hapos (hterm a)) (le_of_lt hlog2)
        nlinarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hle a)
    have hlhs : ∑ a : α, (-P.pmf (a, b) * log2 (P.snd.pmf b)) = negPLogP (P.snd.pmf b) := by
      simp_rw [neg_mul, Finset.sum_neg_distrib, ← Finset.sum_mul]
      change -(P.snd.pmf b * log2 (P.snd.pmf b)) = negPLogP (P.snd.pmf b)
      simp only [negPLogP, ite_eq_right_iff.mpr (fun h => absurd h hb)]
      ring
    linarith

/-- Upper bound on conditional entropy: `H(X | Y) ≤ log₂ |α|`. -/
theorem condEntropy_le_log2_card [Nonempty α] (P : ProbDist (α × β)) :
    condEntropy P ≤ log2 (Fintype.card α : ℝ) :=
  le_trans (condEntropy_le_shannonEntropy P) (shannonEntropy_le_log2_card P.fst)

/-- **Deterministic Functions Reduce Entropy**: `H(f(X)) ≤ H(X)`. -/
theorem shannonEntropy_map_le (f : α → β) (P : ProbDist α) :
    shannonEntropy (P.map f) ≤ shannonEntropy P := by
  classical
  let Q : ProbDist (α × β) := P.map (fun a => (a, f a))
  have hQ_snd : Q.snd = P.map f := by
    unfold Q ProbDist.snd ProbDist.map
    congr; funext b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ_ent : shannonEntropy Q = shannonEntropy P := by
    unfold Q shannonEntropy ProbDist.map
    dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (f a)]
    · congr 1
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hne
      rw [Finset.sum_eq_zero fun a' _ => by
        split_ifs with h
        · exact absurd ((Prod.mk.inj h).1 ▸ (Prod.mk.inj h).2) hne.symm
        · rfl, negPLogP_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hce := condEntropy_nonneg Q
  unfold condEntropy at hce
  rw [hQ_snd, hQ_ent] at hce
  linarith

/-- Conditional independent product distribution `Q(a, b, c) = P(a, c) P(b, c) / P(c)` used
    to express conditional mutual information as a KL divergence. -/
noncomputable def condIndepDist (P : ProbDist (α × β × γ)) : ProbDist (α × β × γ) := by
  classical
  let Pxz : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  let Pyz : ProbDist (β × γ) := P.map (fun t => (t.2.1, t.2.2))
  let Pz : ProbDist γ := P.map (fun t => t.2.2)
  have hPxz_pmf : ∀ a c, Pxz.pmf (a, c) = ∑ b : β, P.pmf (a, b, c) := by
    intro a c
    unfold Pxz ProbDist.map
    dsimp only
    rw [Fintype.sum_prod_type]
    trans (∑ a' : α, if a' = a then ∑ b : β, P.pmf (a, b, c) else 0)
    · refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Fintype.sum_prod_type]
      by_cases ha : a' = a
      · subst ha
        simp only [↓reduceIte]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp [ha]
    · simp
  have hPyz_pmf : ∀ b c, Pyz.pmf (b, c) = ∑ a : α, P.pmf (a, b, c) := by
    intro b c
    unfold Pyz ProbDist.map
    dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPz_pmf : ∀ c, Pz.pmf c = ∑ a : α, ∑ b : β, P.pmf (a, b, c) := by
    intro c
    unfold Pz ProbDist.map
    dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact
    { pmf := fun t => if Pz.pmf t.2.2 = 0 then 0 else Pxz.pmf (t.1, t.2.2) * Pyz.pmf (t.2.1, t.2.2) / Pz.pmf t.2.2
      nonneg := fun t => by
        split_ifs
        · exact le_rfl
        · exact div_nonneg (mul_nonneg (Pxz.nonneg _) (Pyz.nonneg _)) (Pz.nonneg _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        trans (∑ c : γ, Pz.pmf c)
        · trans (∑ a : α, ∑ c : γ, ∑ b : β,
              if Pz.pmf c = 0 then 0 else Pxz.pmf (a, c) * Pyz.pmf (b, c) / Pz.pmf c)
          · exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun c _ => by
              by_cases hc : Pz.pmf c = 0
              · simp [hc]
              · simp only [ite_eq_right_iff.mpr (fun h => absurd h hc)]
                have hsum_a : ∑ a : α, Pxz.pmf (a, c) = Pz.pmf c := by
                  simp_rw [hPxz_pmf, hPz_pmf]
                have hsum_b : ∑ b : β, Pyz.pmf (b, c) = Pz.pmf c := by
                  simp_rw [hPyz_pmf, hPz_pmf]
                  exact Finset.sum_comm
                simp_rw [← Finset.sum_div, ← Finset.mul_sum, hsum_b, ← Finset.sum_mul, hsum_a]
                field_simp [hc]
        · exact Pz.sum_one }

/-- **Conditional Mutual Information as KL Divergence** (Cover & Thomas, Eq. 2.92):
    `I(X; Y | Z) = D(P_{XYZ} ‖ P_{XZ} P_{YZ} / P_Z)`. -/
theorem condMutualInfo_eq_klDivergence (P : ProbDist (α × β × γ)) :
    condMutualInfo P = klDivergence P (condIndepDist P) := by
  classical
  let Pxz : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  let Pyz : ProbDist (β × γ) := P.map (fun t => (t.2.1, t.2.2))
  let Pz : ProbDist γ := P.map (fun t => t.2.2)
  have hPxz_pmf : ∀ a c, Pxz.pmf (a, c) = ∑ b : β, P.pmf (a, b, c) := by
    intro a c
    unfold Pxz ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type]
    trans (∑ a' : α, if a' = a then ∑ b : β, P.pmf (a, b, c) else 0)
    · refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Fintype.sum_prod_type]
      by_cases ha : a' = a
      · subst ha; simp only [↓reduceIte]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp [ha]
    · simp
  have hPyz_pmf : ∀ b c, Pyz.pmf (b, c) = ∑ a : α, P.pmf (a, b, c) := by
    intro b c
    unfold Pyz ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro c' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPz_pmf : ∀ c, Pz.pmf c = ∑ a : α, ∑ b : β, P.pmf (a, b, c) := by
    intro c
    unfold Pz ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQ_pmf : ∀ a b c, (condIndepDist P).pmf (a, b, c) =
      if Pz.pmf c = 0 then 0 else Pxz.pmf (a, c) * Pyz.pmf (b, c) / Pz.pmf c := fun _ _ _ => rfl
  have hterm : ∀ t : α × β × γ,
      (if P.pmf t ≤ 0 then (0 : ℝ) else P.pmf t * log2 (P.pmf t / (condIndepDist P).pmf t)) =
        -negPLogP (P.pmf t) - P.pmf t * log2 (Pxz.pmf (t.1, t.2.2)) -
          P.pmf t * log2 (Pyz.pmf (t.2.1, t.2.2)) + P.pmf t * log2 (Pz.pmf t.2.2) := by
    intro ⟨a, b, c⟩
    by_cases hp : P.pmf (a, b, c) ≤ 0
    · have hp0 : P.pmf (a, b, c) = 0 := le_antisymm hp (P.nonneg (a, b, c))
      simp [hp0, negPLogP]
    · have hpos : 0 < P.pmf (a, b, c) := lt_of_not_ge hp
      have hxz : 0 < Pxz.pmf (a, c) := by
        rw [hPxz_pmf]
        exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun b' _ => P.nonneg (a, b', c)) (Finset.mem_univ b))
      have hyz : 0 < Pyz.pmf (b, c) := by
        rw [hPyz_pmf]
        exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun a' _ => P.nonneg (a', b, c)) (Finset.mem_univ a))
      have hz : 0 < Pz.pmf c := by
        rw [hPz_pmf]
        have h1 : P.pmf (a, b, c) ≤ ∑ b' : β, P.pmf (a, b', c) :=
          Finset.single_le_sum (fun b' _ => P.nonneg (a, b', c)) (Finset.mem_univ b)
        have h2 : ∑ b' : β, P.pmf (a, b', c) ≤ ∑ a' : α, ∑ b' : β, P.pmf (a', b', c) :=
          Finset.single_le_sum (fun a' _ => Finset.sum_nonneg fun b' _ => P.nonneg (a', b', c)) (Finset.mem_univ a)
        linarith
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hp), negPLogP, hQ_pmf,
        ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hz))]
      rw [log2_div_pos hpos (div_pos (mul_pos hxz hyz) hz),
        log2_div_pos (mul_pos hxz hyz) hz, log2_mul_pos hxz hyz]
      ring
  have hsum_xz : ∑ t : α × β × γ, P.pmf t * log2 (Pxz.pmf (t.1, t.2.2)) = -shannonEntropy Pxz := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    unfold shannonEntropy
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, ← hPxz_pmf]
    by_cases h : Pxz.pmf (a, c) ≤ 0
    · have h0 : Pxz.pmf (a, c) = 0 := le_antisymm h (Pxz.nonneg _)
      simp [h0, negPLogP]
    · simp [negPLogP, h]
  have hsum_yz : ∑ t : α × β × γ, P.pmf t * log2 (Pyz.pmf (t.2.1, t.2.2)) = -shannonEntropy Pyz := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    unfold shannonEntropy
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, ← hPyz_pmf]
    by_cases h : Pyz.pmf (b, c) ≤ 0
    · have h0 : Pyz.pmf (b, c) = 0 := le_antisymm h (Pyz.nonneg _)
      simp [h0, negPLogP]
    · simp [negPLogP, h]
  have hsum_z : ∑ t : α × β × γ, P.pmf t * log2 (Pz.pmf t.2.2) = -shannonEntropy Pz := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    trans (∑ c : γ, (∑ a : α, ∑ b : β, P.pmf (a, b, c)) * log2 (Pz.pmf c))
    · trans (∑ a : α, ∑ c : γ, ∑ b : β, P.pmf (a, b, c) * log2 (Pz.pmf c))
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp_rw [← Finset.sum_mul]
    · unfold shannonEntropy
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← hPz_pmf]
      by_cases h : Pz.pmf c ≤ 0
      · have h0 : Pz.pmf c = 0 := le_antisymm h (Pz.nonneg _)
        simp [h0, negPLogP]
      · simp [negPLogP, h]
  unfold klDivergence condMutualInfo
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  change shannonEntropy Pxz + shannonEntropy Pyz - shannonEntropy P - shannonEntropy Pz =
    -shannonEntropy P - (∑ t : α × β × γ, P.pmf t * log2 (Pxz.pmf (t.1, t.2.2))) -
      (∑ t : α × β × γ, P.pmf t * log2 (Pyz.pmf (t.2.1, t.2.2))) +
      (∑ t : α × β × γ, P.pmf t * log2 (Pz.pmf t.2.2))
  rw [hsum_xz, hsum_yz, hsum_z]
  ring

lemma absCont_condIndepDist (P : ProbDist (α × β × γ)) : AbsCont P (condIndepDist P) := by
  classical
  intro ⟨a, b, c⟩ hQ0
  by_contra hPne
  have hpos : 0 < P.pmf (a, b, c) := lt_of_le_of_ne (P.nonneg _) (Ne.symm hPne)
  let Pxz : ProbDist (α × γ) := P.map (fun t => (t.1, t.2.2))
  let Pyz : ProbDist (β × γ) := P.map (fun t => (t.2.1, t.2.2))
  let Pz : ProbDist γ := P.map (fun t => t.2.2)
  have hxz : 0 < Pxz.pmf (a, c) := by
    unfold Pxz ProbDist.map; dsimp only
    refine lt_of_lt_of_le hpos (le_trans ?_
      (Finset.single_le_sum (fun t _ => by split_ifs; exact P.nonneg t; exact le_rfl)
        (Finset.mem_univ (a, b, c))))
    simp
  have hyz : 0 < Pyz.pmf (b, c) := by
    unfold Pyz ProbDist.map; dsimp only
    refine lt_of_lt_of_le hpos (le_trans ?_
      (Finset.single_le_sum (fun t _ => by split_ifs; exact P.nonneg t; exact le_rfl)
        (Finset.mem_univ (a, b, c))))
    simp
  have hz : 0 < Pz.pmf c := by
    unfold Pz ProbDist.map; dsimp only
    refine lt_of_lt_of_le hpos (le_trans ?_
      (Finset.single_le_sum (fun t _ => by split_ifs; exact P.nonneg t; exact le_rfl)
        (Finset.mem_univ (a, b, c))))
    simp
  have hQpos : 0 < (condIndepDist P).pmf (a, b, c) := by
    change 0 < if Pz.pmf c = 0 then 0 else Pxz.pmf (a, c) * Pyz.pmf (b, c) / Pz.pmf c
    rw [ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hz))]
    exact div_pos (mul_pos hxz hyz) hz
  linarith

/-- **Strong Subadditivity / Non-negativity of Conditional Mutual Information**
    (Cover & Thomas, Eq. 2.92; El Gamal–Kim §2.1): `I(X; Y | Z) ≥ 0`. -/
theorem condMutualInfo_nonneg (P : ProbDist (α × β × γ)) : 0 ≤ condMutualInfo P := by
  rw [condMutualInfo_eq_klDivergence]
  exact klDivergence_nonneg P (condIndepDist P) (absCont_condIndepDist P)

/-- Conditional mutual information vanishes iff `X` and `Y` are conditionally independent given `Z`. -/
theorem condMutualInfo_eq_zero_iff (P : ProbDist (α × β × γ)) :
    condMutualInfo P = 0 ↔ P = condIndepDist P := by
  rw [condMutualInfo_eq_klDivergence]
  exact klDivergence_eq_zero_iff P (condIndepDist P) (absCont_condIndepDist P)

lemma map_comp_eq {δ : Type*} [Fintype δ] (P : ProbDist α) (f : α → β) (g : β → δ) :
    (P.map f).map g = P.map (g ∘ f) := by
  classical
  unfold ProbDist.map
  congr
  funext d
  simp only [Function.comp_apply]
  trans (∑ b : β, ∑ a : α, if g b = d ∧ f a = b then P.pmf a else 0)
  · refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hgb : g b = d
    · simp [hgb]
    · simp [hgb]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (f a)]
    · simp
    · intro b _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **Every Entropic Vector is a Polymatroid** (`Γ*_n ⊆ Γ_n`, Cover & Thomas / Yeung Ch. 13):
    for any joint distribution `P` on `Fin n → Fin k`, its subset entropy vector satisfies
    `h(∅) = 0`, monotonicity, and submodularity (`IsPolymatroid`). -/
theorem subsetEntropyVec_isPolymatroid {n k : ℕ} (P : ProbDist (Fin n → Fin k)) :
    IsPolymatroid n (subsetEntropyVec P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- h(∅) = 0
    have _ : Unique (∀ _ : (∅ : Finset (Fin n)), Fin k) :=
      ⟨⟨fun i => absurd i.2 (Finset.notMem_empty _)⟩, fun f => funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
    have hcard : Fintype.card (∀ _ : (∅ : Finset (Fin n)), Fin k) = 1 := Fintype.card_unique
    have hle := shannonEntropy_le_log2_card (P.map (fun x (i : (∅ : Finset (Fin n))) => x i.1))
    have hge := shannonEntropy_nonneg (P.map (fun x (i : (∅ : Finset (Fin n))) => x i.1))
    rw [hcard] at hle
    simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
    exact le_antisymm hle hge
  · -- Monotonicity: S ⊆ T → h(S) ≤ h(T)
    intro S T hST
    unfold subsetEntropyVec
    let proj : (∀ _ : T, Fin k) → (∀ _ : S, Fin k) := fun y i => y ⟨i.1, hST i.2⟩
    have hcomp : P.map (fun x (i : S) => x i.1) = (P.map (fun x (i : T) => x i.1)).map proj := by
      rw [map_comp_eq]; rfl
    rw [hcomp]
    exact shannonEntropy_map_le proj _
  · -- Submodularity: h(S ∪ T) + h(S ∩ T) ≤ h(S) + h(T)
    intro S T
    unfold subsetEntropyVec
    let X : (Fin n → Fin k) → (∀ _ : (S \ T : Finset (Fin n)), Fin k) := fun x i => x i.1
    let Y : (Fin n → Fin k) → (∀ _ : (T \ S : Finset (Fin n)), Fin k) := fun x i => x i.1
    let Z : (Fin n → Fin k) → (∀ _ : (S ∩ T : Finset (Fin n)), Fin k) := fun x i => x i.1
    let Q : ProbDist ((∀ _ : (S \ T : Finset (Fin n)), Fin k) ×
        (∀ _ : (T \ S : Finset (Fin n)), Fin k) ×
        (∀ _ : (S ∩ T : Finset (Fin n)), Fin k)) :=
      P.map (fun x => (X x, Y x, Z x))
    have hcmi := condMutualInfo_nonneg Q
    unfold condMutualInfo at hcmi
    -- Build bijections identifying the four marginals with S, T, S ∪ T, S ∩ T
    let eS : ((∀ _ : (S \ T : Finset (Fin n)), Fin k) × (∀ _ : (S ∩ T : Finset (Fin n)), Fin k)) ≃
        (∀ _ : S, Fin k) :=
      { toFun := fun pq i =>
          if h : i.1 ∈ T then pq.2 ⟨i.1, Finset.mem_inter.mpr ⟨i.2, h⟩⟩
          else pq.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩
        invFun := fun f =>
          (fun i => f ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, (Finset.mem_inter.mp i.2).1⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext i
          · simp [(Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_inter.mp i.2).2]
        right_inv := fun f => by
          funext i; dsimp only; split_ifs <;> rfl }
    let eT : ((∀ _ : (T \ S : Finset (Fin n)), Fin k) × (∀ _ : (S ∩ T : Finset (Fin n)), Fin k)) ≃
        (∀ _ : T, Fin k) :=
      { toFun := fun pq i =>
          if h : i.1 ∈ S then pq.2 ⟨i.1, Finset.mem_inter.mpr ⟨h, i.2⟩⟩
          else pq.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩
        invFun := fun f =>
          (fun i => f ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, (Finset.mem_inter.mp i.2).2⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext i
          · simp [(Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_inter.mp i.2).1]
        right_inv := fun f => by
          funext i; dsimp only; split_ifs <;> rfl }
    let eU : ((∀ _ : (S \ T : Finset (Fin n)), Fin k) ×
        (∀ _ : (T \ S : Finset (Fin n)), Fin k) ×
        (∀ _ : (S ∩ T : Finset (Fin n)), Fin k)) ≃ (∀ _ : (S ∪ T : Finset (Fin n)), Fin k) :=
      { toFun := fun pqr i =>
          if hS : i.1 ∈ S then
            if hT : i.1 ∈ T then pqr.2.2 ⟨i.1, Finset.mem_inter.mpr ⟨hS, hT⟩⟩
            else pqr.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨hS, hT⟩⟩
          else pqr.2.1 ⟨i.1, Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp i.2).resolve_left hS, hS⟩⟩
        invFun := fun f =>
          (fun i => f ⟨i.1, Finset.mem_union_left T (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, Finset.mem_union_right S (Finset.mem_sdiff.mp i.2).1⟩,
           fun i => f ⟨i.1, Finset.mem_union_left T (Finset.mem_inter.mp i.2).1⟩)
        left_inv := fun ⟨p, q, r⟩ => by
          ext i
          · simp [(Finset.mem_sdiff.mp i.2).1, (Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_sdiff.mp i.2).2]
          · simp [(Finset.mem_inter.mp i.2).1, (Finset.mem_inter.mp i.2).2]
        right_inv := fun f => by
          funext i; dsimp only; split_ifs <;> rfl }
    have hS_eq : shannonEntropy (Q.map (fun t => (t.1, t.2.2))) =
        shannonEntropy (P.map (fun x (i : S) => x i.1)) := by
      rw [← shannonEntropy_map_equiv eS, map_comp_eq, map_comp_eq]
      congr 2; funext x; funext i; dsimp [eS, X, Z]; split_ifs <;> rfl
    have hT_eq : shannonEntropy (Q.map (fun t => (t.2.1, t.2.2))) =
        shannonEntropy (P.map (fun x (i : T) => x i.1)) := by
      rw [← shannonEntropy_map_equiv eT, map_comp_eq, map_comp_eq]
      congr 2; funext x; funext i; dsimp [eT, Y, Z]; split_ifs <;> rfl
    have hU_eq : shannonEntropy Q =
        shannonEntropy (P.map (fun x (i : (S ∪ T : Finset (Fin n))) => x i.1)) := by
      rw [← shannonEntropy_map_equiv eU, map_comp_eq]
      congr 2; funext x; funext i; dsimp [eU, X, Y, Z]; split_ifs <;> rfl
    have hI_eq : shannonEntropy (Q.map (fun t => t.2.2)) =
        shannonEntropy (P.map (fun x (i : (S ∩ T : Finset (Fin n))) => x i.1)) := by
      rw [map_comp_eq]; rfl
    dsimp only at hcmi
    rw [hS_eq, hT_eq, hU_eq, hI_eq] at hcmi
    linarith

end EntropyCalculus

/-! ### 2. Fano's Inequality (Cover & Thomas, Theorem 2.10.1; El Gamal–Kim §2.1) -/

section Fano

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Error probability `P_e = P(g(Y) ≠ X)` of an estimator `g : β → α` under joint law `P`. -/
noncomputable def estErrorProb (P : ProbDist (α × β)) (g : β → α) : ℝ :=
  by classical exact ∑ ab : α × β, if g ab.2 ≠ ab.1 then P.pmf ab else 0

lemma estErrorProb_nonneg (P : ProbDist (α × β)) (g : β → α) :
    0 ≤ estErrorProb P g := by
  classical
  unfold estErrorProb
  exact Finset.sum_nonneg fun ab _ => by split_ifs; exact P.nonneg ab; exact le_rfl

lemma estErrorProb_le_one (P : ProbDist (α × β)) (g : β → α) :
    estErrorProb P g ≤ 1 := by
  classical
  unfold estErrorProb
  calc ∑ ab : α × β, (if g ab.2 ≠ ab.1 then P.pmf ab else 0)
    _ ≤ ∑ ab : α × β, P.pmf ab := Finset.sum_le_sum fun ab _ => by split_ifs; exact le_rfl; exact P.nonneg ab
    _ = 1 := P.sum_one

lemma one_sub_estErrorProb (P : ProbDist (α × β)) (g : β → α) :
    1 - estErrorProb P g = ∑ b : β, P.pmf (g b, b) := by
  classical
  unfold estErrorProb
  have hsplit : ∑ ab : α × β, P.pmf ab =
      (∑ ab : α × β, if g ab.2 = ab.1 then P.pmf ab else 0) +
      (∑ ab : α × β, if g ab.2 ≠ ab.1 then P.pmf ab else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ab _ => by by_cases h : g ab.2 = ab.1 <;> simp [h]
  have hdiag : (∑ ab : α × β, if g ab.2 = ab.1 then P.pmf ab else 0) =
      ∑ b : β, P.pmf (g b, b) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single (g b)]
    · simp
    · intro a _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [P.sum_one] at hsplit
  linarith

/-- **Fano's Inequality (Sharp Form)** (Cover & Thomas, Theorem 2.10.1; El Gamal–Kim §2.1):
    for any joint distribution `P` on `α × β` with `2 ≤ |α|` and any estimator `g : β → α`,
    `H(X | Y) ≤ h(P_e) + P_e log₂(|α| - 1)`.

    Proved via a single application of Mathlib's Gibbs inequality (`klDivergence_nonneg`)
    against the isotropic-error reference law `Q(a, b) = (1 - P_e) P_Y(b)` for `a = g(b)`
    and `Q(a, b) = (P_e / (|α| - 1)) P_Y(b)` for `a ≠ g(b)`. -/
theorem fano_inequality (P : ProbDist (α × β)) (g : β → α) (hcard : 2 ≤ Fintype.card α) :
    condEntropy P ≤
      binaryEntropy (estErrorProb P g) +
        estErrorProb P g * log2 ((Fintype.card α : ℝ) - 1) := by
  classical
  set pe := estErrorProb P g
  have hpe0 : 0 ≤ pe := estErrorProb_nonneg P g
  have hpe1 : pe ≤ 1 := estErrorProb_le_one P g
  have hMpos : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard
    linarith
  have hMne : (Fintype.card α : ℝ) - 1 ≠ 0 := ne_of_gt hMpos
  let Q : ProbDist (α × β) :=
    { pmf := fun ab =>
        if g ab.2 = ab.1 then (1 - pe) * P.snd.pmf ab.2
        else (pe / ((Fintype.card α : ℝ) - 1)) * P.snd.pmf ab.2
      nonneg := fun ab => by
        split_ifs
        · exact mul_nonneg (by linarith) (P.snd.nonneg ab.2)
        · exact mul_nonneg (div_nonneg hpe0 (le_of_lt hMpos)) (P.snd.nonneg ab.2)
      sum_one := by
        rw [Fintype.sum_prod_type_right]
        trans (∑ b : β, P.snd.pmf b)
        · refine Finset.sum_congr rfl fun b _ => ?_
          have hsum_a : ∑ a : α, (if g b = a then (1 - pe) * P.snd.pmf b
              else pe / ((Fintype.card α : ℝ) - 1) * P.snd.pmf b) =
              (1 - pe) * P.snd.pmf b +
                ∑ a ∈ Finset.univ.erase (g b), (pe / ((Fintype.card α : ℝ) - 1) * P.snd.pmf b) := by
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (g b))]
            simp only [↓reduceIte]
            congr 1
            refine Finset.sum_congr rfl fun a ha => ?_
            simp [(Finset.mem_erase.mp ha).1.symm]
          rw [hsum_a, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (g b)),
            Finset.card_univ, nsmul_eq_mul]
          have hcast : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          rw [hcast]
          field_simp [hMne]
          ring
        · exact P.snd.sum_one }
  have hac : AbsCont P Q := by
    intro ⟨a, b⟩ hQ0
    by_contra hPne
    have hPpos : 0 < P.pmf (a, b) := lt_of_le_of_ne (P.nonneg _) (Ne.symm hPne)
    have hPy : 0 < P.snd.pmf b := lt_of_lt_of_le hPpos
      (Finset.single_le_sum (fun a' _ => P.nonneg (a', b)) (Finset.mem_univ a))
    by_cases hga : g b = a
    · have h1mpe : 0 < 1 - pe := by
        rw [one_sub_estErrorProb]
        have hle : P.pmf (g b, b) ≤ ∑ b' : β, P.pmf (g b', b') :=
          Finset.single_le_sum (fun b' _ => P.nonneg (g b', b')) (Finset.mem_univ b)
        rw [hga] at hle
        linarith
      have hQpos : 0 < Q.pmf (a, b) := by
        simp only [Q, hga, ↓reduceIte]
        exact mul_pos h1mpe hPy
      linarith
    · have hpepos : 0 < pe := by
        have hle : (if g b ≠ a then P.pmf (a, b) else 0) ≤ estErrorProb P g := by
          unfold estErrorProb
          exact Finset.single_le_sum (f := fun ab : α × β => if g ab.2 ≠ ab.1 then P.pmf ab else 0)
            (fun ab _ => by split_ifs; exact P.nonneg ab; exact le_rfl)
            (Finset.mem_univ (a, b))
        simp only [hga, ne_eq, not_false_eq_true, ↓reduceIte] at hle
        linarith
      have hQpos : 0 < Q.pmf (a, b) := by
        simp only [Q, ite_eq_right_iff.mpr (fun h => absurd h hga)]
        exact mul_pos (div_pos hpepos hMpos) hPy
      linarith
  have hkl_nonneg : 0 ≤ klDivergence P Q := klDivergence_nonneg P Q hac
  -- Expand `klDivergence P Q = -condEntropy P + binaryEntropy pe + pe * log2(|α| - 1)`
  have hterm : ∀ ab : α × β,
      (if P.pmf ab ≤ 0 then (0 : ℝ) else P.pmf ab * log2 (P.pmf ab / Q.pmf ab)) =
        -negPLogP (P.pmf ab) - P.pmf ab * log2 (P.snd.pmf ab.2) +
          (if g ab.2 = ab.1 then -P.pmf ab * log2 (1 - pe)
           else -P.pmf ab * log2 pe + P.pmf ab * log2 ((Fintype.card α : ℝ) - 1)) := by
    intro ⟨a, b⟩
    by_cases hp : P.pmf (a, b) ≤ 0
    · have hp0 : P.pmf (a, b) = 0 := le_antisymm hp (P.nonneg (a, b))
      simp [hp0, negPLogP]
    · have hpos : 0 < P.pmf (a, b) := lt_of_not_ge hp
      have hPy : 0 < P.snd.pmf b := lt_of_lt_of_le hpos
        (Finset.single_le_sum (fun a' _ => P.nonneg (a', b)) (Finset.mem_univ a))
      simp only [ite_eq_right_iff.mpr (fun h => absurd h hp), negPLogP]
      by_cases hga : g b = a
      · have h1mpe : 0 < 1 - pe := by
          rw [one_sub_estErrorProb]
          have hle : P.pmf (g b, b) ≤ ∑ b' : β, P.pmf (g b', b') :=
            Finset.single_le_sum (fun b' _ => P.nonneg (g b', b')) (Finset.mem_univ b)
          rw [hga] at hle; linarith
        simp only [Q, hga, ↓reduceIte]
        rw [log2_div_pos hpos (mul_pos h1mpe hPy), log2_mul_pos h1mpe hPy]
        ring
      · have hpepos : 0 < pe := by
          have hle : (if g b ≠ a then P.pmf (a, b) else 0) ≤ estErrorProb P g := by
            unfold estErrorProb
            exact Finset.single_le_sum (f := fun ab : α × β => if g ab.2 ≠ ab.1 then P.pmf ab else 0)
              (fun ab _ => by split_ifs; exact P.nonneg ab; exact le_rfl)
              (Finset.mem_univ (a, b))
          simp only [hga, ne_eq, not_false_eq_true, ↓reduceIte] at hle
          linarith
        simp only [Q, ite_eq_right_iff.mpr (fun h => absurd h hga)]
        rw [log2_div_pos hpos (mul_pos (div_pos hpepos hMpos) hPy),
          log2_mul_pos (div_pos hpepos hMpos) hPy, log2_div_pos hpepos hMpos]
        ring
  have hsum_y : ∑ ab : α × β, P.pmf ab * log2 (P.snd.pmf ab.2) = -shannonEntropy P.snd := by
    rw [Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    unfold shannonEntropy
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    change P.snd.pmf b * log2 (P.snd.pmf b) = -negPLogP (P.snd.pmf b)
    by_cases hb : P.snd.pmf b ≤ 0
    · have h0 : P.snd.pmf b = 0 := le_antisymm hb (P.snd.nonneg b)
      simp [h0, negPLogP]
    · simp [negPLogP, hb]
  have hsum_err : ∑ ab : α × β,
      (if g ab.2 = ab.1 then -P.pmf ab * log2 (1 - pe)
       else -P.pmf ab * log2 pe + P.pmf ab * log2 ((Fintype.card α : ℝ) - 1)) =
      binaryEntropy pe + pe * log2 ((Fintype.card α : ℝ) - 1) := by
    have hsplit : ∀ ab : α × β,
        (if g ab.2 = ab.1 then -P.pmf ab * log2 (1 - pe)
         else -P.pmf ab * log2 pe + P.pmf ab * log2 ((Fintype.card α : ℝ) - 1)) =
        (if g ab.2 = ab.1 then P.pmf ab else 0) * (-log2 (1 - pe)) +
        (if g ab.2 ≠ ab.1 then P.pmf ab else 0) * (-log2 pe + log2 ((Fintype.card α : ℝ) - 1)) := by
      intro ab
      by_cases h : g ab.2 = ab.1
      · simp [h]
      · simp [h]; ring
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
    have hdiag : (∑ ab : α × β, if g ab.2 = ab.1 then P.pmf ab else 0) = 1 - pe := by
      rw [one_sub_estErrorProb, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_eq_single (g b)]
      · simp
      · intro a _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have herr : (∑ ab : α × β, if g ab.2 ≠ ab.1 then P.pmf ab else 0) = pe := rfl
    rw [hdiag, herr]
    unfold binaryEntropy
    have h1 : (1 - pe) * (-log2 (1 - pe)) = negPLogP (1 - pe) := by
      unfold negPLogP
      by_cases h : 1 - pe ≤ 0
      · have h0 : 1 - pe = 0 := by linarith
        simp [h0]
      · simp only [ite_eq_right_iff.mpr (fun h' => absurd h' h)]; ring
    have h2 : pe * (-log2 pe) = negPLogP pe := by
      unfold negPLogP
      by_cases h : pe ≤ 0
      · have h0 : pe = 0 := le_antisymm h hpe0
        simp [h0]
      · simp only [ite_eq_right_iff.mpr (fun h' => absurd h' h)]; ring
    linarith [mul_add pe (-log2 pe) (log2 ((Fintype.card α : ℝ) - 1))]
  unfold klDivergence at hkl_nonneg
  simp_rw [hterm] at hkl_nonneg
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hkl_nonneg
  change 0 ≤ -shannonEntropy P - (∑ ab : α × β, P.pmf ab * log2 (P.snd.pmf ab.2)) +
      (∑ ab : α × β, if g ab.2 = ab.1 then -P.pmf ab * log2 (1 - pe)
        else -P.pmf ab * log2 pe + P.pmf ab * log2 ((Fintype.card α : ℝ) - 1)) at hkl_nonneg
  rw [hsum_y, hsum_err] at hkl_nonneg
  unfold condEntropy
  linarith

/-- **Fano's Inequality (General Nonempty Form)**: for any `[Nonempty α]`,
    `H(X | Y) ≤ h(P_e) + P_e log₂|α|`. -/
theorem fano_inequality_card [Nonempty α] (P : ProbDist (α × β)) (g : β → α) :
    condEntropy P ≤
      binaryEntropy (estErrorProb P g) +
        estErrorProb P g * log2 (Fintype.card α : ℝ) := by
  by_cases hcard : 2 ≤ Fintype.card α
  · have h := fano_inequality P g hcard
    have hpe0 : 0 ≤ estErrorProb P g := estErrorProb_nonneg P g
    have hlog : log2 ((Fintype.card α : ℝ) - 1) ≤ log2 (Fintype.card α : ℝ) := by
      unfold log2
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hM : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hcard
        linarith
      exact div_le_div_of_nonneg_right (Real.log_le_log hM (by linarith)) (le_of_lt hlog2)
    have hmul : estErrorProb P g * log2 ((Fintype.card α : ℝ) - 1) ≤
        estErrorProb P g * log2 (Fintype.card α : ℝ) :=
      mul_le_mul_of_nonneg_left hlog hpe0
    linarith
  · have h1 : Fintype.card α = 1 := by
      have := Fintype.card_pos (α := α); omega
    have hce : condEntropy P ≤ 0 := by
      have h := condEntropy_le_log2_card P
      rw [h1] at h
      simp only [Nat.cast_one, log2, Real.log_one, zero_div] at h
      exact h
    have hbin : 0 ≤ binaryEntropy (estErrorProb P g) := by
      unfold binaryEntropy
      have hpe0 := estErrorProb_nonneg P g
      have hpe1 := estErrorProb_le_one P g
      exact add_nonneg (negPLogP_nonneg hpe1) (negPLogP_nonneg (by linarith))
    rw [h1]
    simp only [Nat.cast_one, log2, Real.log_one, zero_div, mul_zero, add_zero]
    linarith

end Fano

/-! ### 3. Asymptotic Equipartition Property (AEP) & Weak Typicality (Cover & Thomas Ch. 3) -/

section AEP

variable {α : Type*} [Fintype α]

/-- The `n`-fold i.i.d. product distribution `P^n` on `Fin n → α`. -/
def iidDist (P : ProbDist α) (n : ℕ) : ProbDist (Fin n → α) where
  pmf := fun x => ∏ i : Fin n, P.pmf (x i)
  nonneg := fun x => Finset.prod_nonneg fun i _ => P.nonneg (x i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp [P.sum_one]

/-- Self-information (surprisal) `ι_P(a) = -log₂ P(a)` (with `0` on zero-mass atoms). -/
noncomputable def selfInfo (P : ProbDist α) (a : α) : ℝ :=
  if P.pmf a ≤ 0 then 0 else -log2 (P.pmf a)

/-- Expectation of `selfInfo P` under `P` equals `shannonEntropy P`. -/
lemma expected_selfInfo (P : ProbDist α) :
    ∑ a : α, P.pmf a * selfInfo P a = shannonEntropy P := by
  unfold selfInfo shannonEntropy negPLogP
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hp : P.pmf a ≤ 0
  · simp [hp]
  · simp only [ite_eq_right_iff.mpr (fun h => absurd h hp)]; ring

/-- Variance of self-information `V(P) = E[(ι_P(X) - H(P))²]` (varentropy / source dispersion). -/
noncomputable def varentropy (P : ProbDist α) : ℝ :=
  ∑ a : α, P.pmf a * (selfInfo P a - shannonEntropy P) ^ 2

lemma varentropy_nonneg (P : ProbDist α) : 0 ≤ varentropy P :=
  Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _)

/-- **Weakly Typical Set** `A_ε^(n)` (Cover & Thomas, Definition 3.1):
    sequences `x : Fin n → α` satisfying
    `2^(-n(H(P) + ε)) ≤ P^n(x) ≤ 2^(-n(H(P) - ε))`. -/
noncomputable def weakTypicalSet (P : ProbDist α) (n : ℕ) (ε : ℝ) : Finset (Fin n → α) :=
  by
    classical
    exact Finset.univ.filter fun x =>
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤ (iidDist P n).pmf x ∧
      (iidDist P n).pmf x ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε)))

/-- Helper: expectation of a single-coordinate function under `iidDist P n`. -/
lemma iidDist_sum_coord (P : ProbDist α) {n : ℕ} (f : α → ℝ) (i : Fin n) :
    ∑ x : Fin n → α, (iidDist P n).pmf x * f (x i) = ∑ a : α, P.pmf a * f a := by
  classical
  let F : Fin n → α → ℝ := fun j a => if j = i then P.pmf a * f a else P.pmf a
  have hfun : ∀ x : Fin n → α, (iidDist P n).pmf x * f (x i) = ∏ j : Fin n, F j (x j) := by
    intro x
    unfold iidDist; dsimp only
    conv_rhs => rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (x j)) (Finset.mem_univ i)]
    conv_lhs => rw [← Finset.mul_prod_erase Finset.univ (fun j => P.pmf (x j)) (Finset.mem_univ i)]
    have hi : F i (x i) = P.pmf (x i) * f (x i) := by simp [F]
    have heq : ∏ j ∈ Finset.univ.erase i, F j (x j) =
        ∏ j ∈ Finset.univ.erase i, P.pmf (x j) :=
      Finset.prod_congr rfl fun j hj => by simp [F, (Finset.mem_erase.mp hj).1]
    rw [hi, heq]; ring
  simp_rw [hfun]
  rw [← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ a : α, F j a) (Finset.mem_univ i)]
  have hi : ∑ a : α, F i a = ∑ a : α, P.pmf a * f a := by simp [F]
  have hrest : ∏ j ∈ Finset.univ.erase i, (∑ a : α, F j a) = 1 :=
    Finset.prod_eq_one fun j hj => by
      simp only [F, ite_eq_right_iff.mpr (fun h => absurd h (Finset.mem_erase.mp hj).1)]
      exact P.sum_one
  rw [hi, hrest, mul_one]

/-- Helper: expectation of a product of two distinct coordinates under `iidDist P n`. -/
lemma iidDist_sum_two_coords (P : ProbDist α) {n : ℕ} (f g : α → ℝ) {i j : Fin n} (hij : i ≠ j) :
    ∑ x : Fin n → α, (iidDist P n).pmf x * (f (x i) * g (x j)) =
      (∑ a : α, P.pmf a * f a) * (∑ a : α, P.pmf a * g a) := by
  classical
  let F : Fin n → α → ℝ := fun k a =>
    if k = i then P.pmf a * f a else if k = j then P.pmf a * g a else P.pmf a
  have hfun : ∀ x : Fin n → α, (iidDist P n).pmf x * (f (x i) * g (x j)) =
      ∏ k : Fin n, F k (x k) := by
    intro x
    unfold iidDist; dsimp only
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    conv_rhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun k => F k (x k)) (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => F k (x k)) hj_mem]
    conv_lhs =>
      rw [← Finset.mul_prod_erase Finset.univ (fun k => P.pmf (x k)) (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => P.pmf (x k)) hj_mem]
    have hi : F i (x i) = P.pmf (x i) * f (x i) := by simp [F]
    have hj : F j (x j) = P.pmf (x j) * g (x j) := by simp [F, hij.symm]
    have heq : ∏ k ∈ (Finset.univ.erase i).erase j, F k (x k) =
        ∏ k ∈ (Finset.univ.erase i).erase j, P.pmf (x k) :=
      Finset.prod_congr rfl fun k hk => by
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        simp [F, hki, hkj]
    rw [hi, hj, heq]; ring
  simp_rw [hfun]
  rw [← Fintype.prod_sum F]
  have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ a : α, F k a) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun k => ∑ a : α, F k a) hj_mem]
  have hi : ∑ a : α, F i a = ∑ a : α, P.pmf a * f a := by simp [F]
  have hj : ∑ a : α, F j a = ∑ a : α, P.pmf a * g a := by simp [F, hij.symm]
  have hrest : ∏ k ∈ (Finset.univ.erase i).erase j, (∑ a : α, F k a) = 1 :=
    Finset.prod_eq_one fun k hk => by
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp only [F, hki, hkj, ↓reduceIte]
      exact P.sum_one
  rw [hi, hj, hrest, mul_one]

/-- **Explicit Chebyshev Tail Bound for the AEP** (Cover & Thomas, Theorem 3.1.1):
    for any `n ≥ 1` and `ε > 0`,
    `1 - P^n(A_ε^(n)) ≤ V(P) / (n ε²)`. -/
theorem iidDist_prob_not_typical_le (P : ProbDist α) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    1 - ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x ≤
      varentropy P / ((n : ℝ) * ε ^ 2) := by
  classical
  have hcomp_eq : 1 - ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x =
      ∑ x ∈ (weakTypicalSet P n ε)ᶜ, (iidDist P n).pmf x := by
    have h := Finset.sum_add_sum_compl (weakTypicalSet P n ε) (iidDist P n).pmf
    rw [(iidDist P n).sum_one] at h
    linarith
  rw [hcomp_eq]
  let Z : α → ℝ := fun a => selfInfo P a - shannonEntropy P
  have hEZ : ∑ a : α, P.pmf a * Z a = 0 := by
    simp_rw [Z, mul_sub, Finset.sum_sub_distrib, expected_selfInfo, ← Finset.sum_mul, P.sum_one, one_mul, sub_self]
  have hVar : ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 =
      (n : ℝ) * varentropy P := by
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
    · trans (∑ i : Fin n, varentropy P)
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · have h := iidDist_sum_coord P (fun a => Z a * Z a) i
          simpa [← sq, varentropy, Z] using h
        · intro j _ hji
          rw [iidDist_sum_two_coords P Z Z hji.symm, hEZ, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp
  -- Show that on `(weakTypicalSet P n ε)ᶜ`, whenever `P^n(x) > 0`, `|∑ Z(x_i)| > n * ε`
  have hbad : ∀ x ∈ (weakTypicalSet P n ε)ᶜ,
      ((n : ℝ) * ε) ^ 2 * (iidDist P n).pmf x ≤
        (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 := by
    intro x hx
    by_cases hpx : (iidDist P n).pmf x ≤ 0
    · have h0 : (iidDist P n).pmf x = 0 := le_antisymm hpx ((iidDist P n).nonneg x)
      simp [h0]
    · have hpos : 0 < (iidDist P n).pmf x := lt_of_not_ge hpx
      have hcoord_pos : ∀ i : Fin n, 0 < P.pmf (x i) := fun i => by
        by_contra hle
        have h0 : P.pmf (x i) = 0 := le_antisymm (not_lt.mp hle) (P.nonneg _)
        have hprod0 : (iidDist P n).pmf x = 0 := by
          unfold iidDist; dsimp only
          exact Finset.prod_eq_zero (Finset.mem_univ i) h0
        linarith
      have hlog_prod : log2 ((iidDist P n).pmf x) = ∑ i : Fin n, log2 (P.pmf (x i)) := by
        unfold iidDist log2; dsimp only
        rw [Real.log_prod (fun i _ => ne_of_gt (hcoord_pos i)), Finset.sum_div]
      have hsum_Z : ∑ i : Fin n, Z (x i) = -log2 ((iidDist P n).pmf x) - (n : ℝ) * shannonEntropy P := by
        simp_rw [Z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        rw [hlog_prod, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold selfInfo
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr (hcoord_pos i)))]
      have hnot : ¬ ((2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤ (iidDist P n).pmf x ∧
          (iidDist P n).pmf x ≤ (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε)))) := by
        simp only [Finset.mem_compl, weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hx
      have h2eq : ∀ t : ℝ, (2 : ℝ) ^ t = Real.exp (t * Real.log 2) := fun t => by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have habs : (n : ℝ) * ε < |∑ i : Fin n, Z (x i)| := by
        by_contra hle
        push Not at hle
        rw [hsum_Z, abs_le] at hle
        apply hnot
        constructor
        · rw [h2eq, ← Real.exp_log hpos]
          apply Real.exp_le_exp.mpr
          have h1 : -log2 ((iidDist P n).pmf x) - (n : ℝ) * shannonEntropy P ≤ (n : ℝ) * ε := hle.2
          unfold log2 at h1
          have h2 : -((n : ℝ) * (shannonEntropy P + ε)) ≤ Real.log ((iidDist P n).pmf x) / Real.log 2 := by linarith
          exact (le_div_iff₀ hlog2pos).mp h2
        · rw [h2eq, ← Real.exp_log hpos]
          apply Real.exp_le_exp.mpr
          have h1 : -((n : ℝ) * ε) ≤ -log2 ((iidDist P n).pmf x) - (n : ℝ) * shannonEntropy P := hle.1
          unfold log2 at h1
          have h2 : Real.log ((iidDist P n).pmf x) / Real.log 2 ≤ -((n : ℝ) * (shannonEntropy P - ε)) := by linarith
          exact (div_le_iff₀ hlog2pos).mp h2
      have hsq_le : ((n : ℝ) * ε) ^ 2 ≤ (∑ i : Fin n, Z (x i)) ^ 2 := by
        rw [← sq_abs (∑ i : Fin n, Z (x i))]
        have hne0 : 0 ≤ (n : ℝ) * ε := by positivity
        nlinarith
      nlinarith
  have hsum_bad : ((n : ℝ) * ε) ^ 2 * ∑ x ∈ (weakTypicalSet P n ε)ᶜ, (iidDist P n).pmf x ≤
      (n : ℝ) * varentropy P := by
    rw [Finset.mul_sum]
    calc ∑ x ∈ (weakTypicalSet P n ε)ᶜ, ((n : ℝ) * ε) ^ 2 * (iidDist P n).pmf x
      _ ≤ ∑ x ∈ (weakTypicalSet P n ε)ᶜ, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 :=
          Finset.sum_le_sum hbad
      _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x * (∑ i : Fin n, Z (x i)) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg fun x => mul_nonneg ((iidDist P n).nonneg x) (sq_nonneg _)
      _ = (n : ℝ) * varentropy P := hVar
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ε ^ 2 := by positivity
  rw [le_div_iff₀ hden_pos]
  have hrew : ((n : ℝ) * ε) ^ 2 = (n : ℝ) * ((n : ℝ) * ε ^ 2) := by ring
  rw [hrew, mul_assoc, mul_comm ((n : ℝ) * ε ^ 2)] at hsum_bad
  exact le_of_mul_le_mul_left hsum_bad hn_pos

/-- **AEP Theorem — Typical Set Probability Approaches 1** (Cover & Thomas, Theorem 3.1.2(1)):
    for every `ε > 0` and `δ > 0`, there exists `N` such that for all `n ≥ N`,
    `P^n(A_ε^(n)) ≥ 1 - δ`. -/
theorem aep_typical_prob_tendsto_one (P : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, 1 - δ ≤ ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (varentropy P / (δ * ε ^ 2))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hn)
  have htail := iidDist_prob_not_typical_le P hn_pos hε
  have hn_gt : varentropy P / (δ * ε ^ 2) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast le_trans (le_max_left N 1) hn)
  have hbound : varentropy P / ((n : ℝ) * ε ^ 2) ≤ δ := by
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [div_le_iff₀ (by positivity)]
    have h1 := (div_lt_iff₀ (by positivity : 0 < δ * ε ^ 2)).mp hn_gt
    linarith
  linarith

/-- **Typical Set Upper Cardinality Bound** (Cover & Thomas, Theorem 3.1.2(2)):
    `|A_ε^(n)| ≤ 2^(n(H(P) + ε))`. -/
theorem weakTypicalSet_card_le (P : ProbDist α) (n : ℕ) (ε : ℝ) :
    ((weakTypicalSet P n ε).card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) := by
  classical
  have hsum_le : ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x ≤ 1 := by
    calc ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x
      _ ≤ ∑ x : Fin n → α, (iidDist P n).pmf x :=
          Finset.sum_le_univ_sum_of_nonneg fun x => (iidDist P n).nonneg x
      _ = 1 := (iidDist P n).sum_one
  have hlow : ((weakTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤
      ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x := by
    calc ((weakTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε)))
      _ = ∑ _x ∈ weakTypicalSet P n ε, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x :=
          Finset.sum_le_sum fun x hx => by
            simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            exact hx.1
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) *
      (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P + ε)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have h1 : ((weakTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P + ε))) ≤ 1 :=
    le_trans hlow hsum_le
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpow_pos)
  rw [mul_assoc, hmul, mul_one, one_mul] at h2
  exact h2

/-- **Typical Set Lower Cardinality Bound** (Cover & Thomas, Theorem 3.1.2(3)):
    for every `ε > 0` and `δ > 0`, eventually
    `(1 - δ) * 2^(n(H(P) - ε)) ≤ |A_ε^(n)|`. -/
theorem weakTypicalSet_card_ge (P : ProbDist α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (1 - δ) * (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε)) ≤
        ((weakTypicalSet P n ε).card : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := aep_typical_prob_tendsto_one P hε hδ
  refine ⟨N, fun n hn => ?_⟩
  have hprob := hN n hn
  have hup : ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x ≤
      ((weakTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := by
    calc ∑ x ∈ weakTypicalSet P n ε, (iidDist P n).pmf x
      _ ≤ ∑ _x ∈ weakTypicalSet P n ε, (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) :=
          Finset.sum_le_sum fun x hx => by
            simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            exact hx.2
      _ = ((weakTypicalSet P n ε).card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : 1 - δ ≤ ((weakTypicalSet P n ε).card : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := le_trans hprob hup
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul : (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) *
      (2 : ℝ) ^ ((n : ℝ) * (shannonEntropy P - ε)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpow_pos)
  rw [mul_assoc, hmul, mul_one] at h2
  exact h2

end AEP

end InfoTheory.Bridge
