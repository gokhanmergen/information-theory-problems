import InfoTheory.Problems.CorrelatedSourcesOverMac
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.CorrelatedSourcesOverMac`

The frozen statement asks whether the optimal source–channel rate
`ρ*(P, W) = optimalTransmissionRatio P W` (an `sSup` of the ratios `ρ` at which the 2-DMS `P`
is losslessly transmissible over the DM-MAC `W`) is computable from rational data, for all
sources not concentrated on a single pair.

## Certified (about exactly these objects)
* `isTransmissibleAtRatio_zero` — `ρ = 0` is always transmissible (for nonempty input
  alphabets), so the `sSup` is over a nonempty set.
* `success_le` — an elementary converse: any code sending `k` source symbols over `n` channel
  uses has success probability at most `pₘₐₓᵏ |Y|ⁿ`, where `pₘₐₓ` bounds the source pmf.
* `le_of_isTransmissibleAtRatio`, `transmissibleSet_bddAbove` — hence, if `pₘₐₓ < 1`, every
  transmissible ratio satisfies `ρ ≤ (log₂|Y| + 1 + L) / L` with `L = log₂ (1/pₘₐₓ) > 0`; the
  `sSup` is over a set bounded above, i.e. `ρ*` is a genuine supremum, not a junk value.
* `optimalTransmissionRatio_nonneg`, `optimalTransmissionRatio_le`.
* `instance_bounds` — for exactly the rational instances quantified over in `Statement`
  (`sourceOfWeights w hw`, `macOfWeights v hv` with the non-degeneracy hypothesis), with total
  weight `S`: `0 ≤ ρ* ≤ (log₂ e + 1 + L) / L` where `L = -log₂ (1 - 1/S) > 0`.

## Not certified
* The Cover–El Gamal–Salehi sufficient condition, the Slepian–Wolf/MAC separation bounds and
  Dueck's counterexample: these need joint-typicality and MAC coding theorems that `Bridge`
  does not provide.
* Monotonicity of transmissibility in `ρ` (so that `ρ* > 1` ⇒ transmissible at `ρ = 1`); this
  is a standard padding/averaging argument and is only asserted in the problem file.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CorrelatedSourcesOverMac

open InfoTheory InfoTheory.Problems.CorrelatedSourcesOverMac

/-- Transition probabilities of a DMC are at most `1`. -/
theorem trans_le_one {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) (x : α) (y : β) :
    W.trans x y ≤ 1 := by
  rw [← W.sum_one x]
  exact Finset.single_le_sum (fun y _ => W.nonneg x y) (Finset.mem_univ y)

variable {U V X₁ X₂ Y : Type*} [Fintype U] [Fintype V] [Fintype X₁] [Fintype X₂] [Fintype Y]
  [DecidableEq U] [DecidableEq V]

/-- `ρ = 0` is transmissible: zero source symbols are sent with zero error. -/
theorem isTransmissibleAtRatio_zero [Nonempty X₁] [Nonempty X₂]
    (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y) : IsTransmissibleAtRatio P W 0 := by
  refine ⟨le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  have h0 : Nat.floor ((0 : ℝ) * n) = 0 := by simp
  rw [h0]
  refine ⟨fun _ _ => Classical.arbitrary X₁, fun _ _ => Classical.arbitrary X₂,
    fun _ => (fun i => i.elim0, fun i => i.elim0), ?_⟩
  have : jsccError P W 0 n (fun _ _ => Classical.arbitrary X₁)
      (fun _ _ => Classical.arbitrary X₂) (fun _ => (fun i => i.elim0, fun i => i.elim0)) = 0 := by
    unfold jsccError
    refine Finset.sum_eq_zero fun s _ => ?_
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
    have : ((fun i : Fin 0 => i.elim0, fun i : Fin 0 => i.elim0) : (Fin 0 → U) × (Fin 0 → V)) =
        (fun i => (s i).1, fun i => (s i).2) :=
      Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    simp [this]
  rw [this]; exact hδ.le

/-- **Elementary converse.** If every source letter has probability at most `pm`, the success
    probability `1 - P_e` of any code sending `k` source symbols over `n` channel uses is at
    most `pmᵏ |Y|ⁿ`. -/
theorem success_le (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y) {pm : ℝ}
    (hpm : ∀ z, P.pmf z ≤ pm) (k n : ℕ)
    (enc₁ : (Fin k → U) → Fin n → X₁) (enc₂ : (Fin k → V) → Fin n → X₂)
    (dec : (Fin n → Y) → (Fin k → U) × (Fin k → V)) :
    1 - jsccError P W k n enc₁ enc₂ dec ≤ pm ^ k * (Fintype.card Y : ℝ) ^ n := by
  classical
  set T : (Fin k → U × V) → (Fin n → Y) → ℝ := fun s y =>
    (W.power n).trans (fun i => (enc₁ (fun j => (s j).1) i, enc₂ (fun j => (s j).2) i)) y
    with hT
  set Pk : (Fin k → U × V) → ℝ := fun s => ∏ i : Fin k, P.pmf (s i) with hPk
  set sp : (Fin k → U × V) → (Fin k → U) × (Fin k → V) :=
    fun s => (fun i => (s i).1, fun i => (s i).2) with hsp
  have hPk1 : ∑ s, Pk s = 1 := by
    show ∑ s : Fin k → U × V, ∏ i : Fin k, P.pmf (s i) = 1
    rw [← Fintype.prod_sum (fun _ a => P.pmf a)]
    simp [P.sum_one]
  have hPk0 : ∀ s, 0 ≤ Pk s := fun s => Finset.prod_nonneg fun i _ => P.nonneg _
  have hpm0 : 0 ≤ pm := by
    obtain ⟨z⟩ : Nonempty (U × V) := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := P.sum_one
      simp at this
    exact (P.nonneg z).trans (hpm z)
  have hPkle : ∀ s, Pk s ≤ pm ^ k := by
    intro s
    show ∏ i : Fin k, P.pmf (s i) ≤ pm ^ k
    calc ∏ i : Fin k, P.pmf (s i) ≤ ∏ _i : Fin k, pm :=
          Finset.prod_le_prod₀ (fun i _ => P.nonneg _) (fun i _ => hpm _)
      _ = pm ^ k := by simp
  -- the error as `1 - success`
  have herr : jsccError P W k n enc₁ enc₂ dec =
      1 - ∑ s, Pk s * ∑ y, (if dec y = sp s then T s y else 0) := by
    have herr0 : jsccError P W k n enc₁ enc₂ dec =
        ∑ s, Pk s * ∑ y, (if dec y ≠ sp s then T s y else 0) := rfl
    rw [herr0]
    have : ∀ s, (∑ y, if dec y ≠ sp s then T s y else 0) =
        1 - ∑ y, (if dec y = sp s then T s y else 0) := by
      intro s
      rw [← (W.power n).sum_one (fun i => (enc₁ (fun j => (s j).1) i, enc₂ (fun j => (s j).2) i)),
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases h : dec y = sp s <;> simp [h, hT]
    simp_rw [this, mul_sub, mul_one, Finset.sum_sub_distrib, hPk1]
  -- at most one source block is decoded correctly from each output
  have hinner : ∀ y, ∑ s, (if dec y = sp s then T s y else 0) ≤ 1 := by
    intro y
    set s₀ : Fin k → U × V := fun i => ((dec y).1 i, (dec y).2 i)
    calc ∑ s, (if dec y = sp s then T s y else 0)
        ≤ ∑ s, (if s₀ = s then T s y else 0) := by
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases h : dec y = sp s
          · have : s₀ = s := by
              funext i
              simp only [s₀, h, hsp]
            rw [ite_eq_left h, ite_eq_left this]
          · rw [ite_eq_right h]
            split_ifs
            · exact (W.power n).nonneg _ _
            · exact le_rfl
      _ = T s₀ y := by rw [Finset.sum_ite_eq]; simp
      _ ≤ 1 := trans_le_one _ _ _
  have hsucc : ∑ s, Pk s * ∑ y, (if dec y = sp s then T s y else 0) ≤
      pm ^ k * (Fintype.card Y : ℝ) ^ n := by
    calc ∑ s, Pk s * ∑ y, (if dec y = sp s then T s y else 0)
        ≤ ∑ s, pm ^ k * ∑ y, (if dec y = sp s then T s y else 0) := by
          refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hPkle s) ?_
          exact Finset.sum_nonneg fun y _ => by
            split_ifs
            · exact (W.power n).nonneg _ _
            · exact le_rfl
      _ = pm ^ k * ∑ y, ∑ s, (if dec y = sp s then T s y else 0) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ pm ^ k * ∑ _y : Fin n → Y, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hinner y) (pow_nonneg hpm0 _)
      _ = pm ^ k * (Fintype.card Y : ℝ) ^ n := by simp
  rw [herr]
  linarith

private lemma log2_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log2 a ≤ log2 b := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log ha hab) (Real.log_pos one_lt_two).le

/-- **Bound on transmissible ratios.** If `P ≤ pm < 1` pointwise, every transmissible `ρ`
    satisfies `ρ ≤ (log₂ |Y| + 1 + L) / L`, where `L = -log₂ pm > 0`. -/
theorem le_of_isTransmissibleAtRatio [Nonempty Y] (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y)
    {pm : ℝ} (hpm : ∀ z, P.pmf z ≤ pm) (hpm0 : 0 < pm) (hpm1 : pm < 1) {ρ : ℝ}
    (h : IsTransmissibleAtRatio P W ρ) :
    ρ ≤ (log2 (Fintype.card Y) + 1 + (-log2 pm)) / (-log2 pm) := by
  obtain ⟨hρ0, hach⟩ := h
  obtain ⟨N, hN⟩ := hach (1 / 2) (by norm_num)
  set n := N + 1 with hn
  have hc := hN n (by omega)
  generalize hk : Nat.floor (ρ * n) = k at hc
  obtain ⟨enc₁, enc₂, dec, herr⟩ := hc
  have hs := success_le P W hpm k n enc₁ enc₂ dec
  have hhalf : (1 / 2 : ℝ) ≤ pm ^ k * (Fintype.card Y : ℝ) ^ n := by linarith
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  set L := -log2 pm with hL
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hLpos : 0 < L := by
    have : Real.log pm / Real.log 2 < 0 := div_neg_of_neg_of_pos (Real.log_neg hpm0 hpm1) hlog2pos
    rw [hL]; unfold log2; linarith
  have hcY0 : 0 ≤ log2 (Fintype.card Y) := by
    unfold log2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) hlog2pos.le
  -- take logarithms: `-1 ≤ -k L + n log₂ |Y|`
  have hlog := log2_mono (by norm_num) hhalf
  have e1 : log2 (1 / 2 : ℝ) = -1 := by
    unfold log2; rw [one_div, Real.log_inv]; field_simp
  have e2 : log2 (pm ^ k * (Fintype.card Y : ℝ) ^ n) =
      (k : ℝ) * log2 pm + (n : ℝ) * log2 (Fintype.card Y) := by
    unfold log2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [e1, e2] at hlog
  have hkL : (k : ℝ) * L ≤ (n : ℝ) * log2 (Fintype.card Y) + 1 := by rw [hL]; linarith
  have hρk : ρ * n < (k : ℝ) + 1 := hk ▸ Nat.lt_floor_add_one _
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  rw [le_div_iff₀ hLpos]
  have h1 : ρ * n * L ≤ ((k : ℝ) + 1) * L := mul_le_mul_of_nonneg_right hρk.le hLpos.le
  have h2 : ρ * L * n ≤ (log2 (Fintype.card Y) + 1 + L) * n := by nlinarith
  exact le_of_mul_le_mul_right h2 (by linarith)

theorem transmissibleSet_bddAbove [Nonempty Y] (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y)
    {pm : ℝ} (hpm : ∀ z, P.pmf z ≤ pm) (hpm0 : 0 < pm) (hpm1 : pm < 1) :
    BddAbove { ρ : ℝ | IsTransmissibleAtRatio P W ρ } :=
  ⟨_, fun _ h => le_of_isTransmissibleAtRatio P W hpm hpm0 hpm1 h⟩

theorem optimalTransmissionRatio_nonneg [Nonempty X₁] [Nonempty X₂] [Nonempty Y]
    (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y)
    {pm : ℝ} (hpm : ∀ z, P.pmf z ≤ pm) (hpm0 : 0 < pm) (hpm1 : pm < 1) :
    0 ≤ optimalTransmissionRatio P W :=
  le_csSup (transmissibleSet_bddAbove P W hpm hpm0 hpm1) (isTransmissibleAtRatio_zero P W)

theorem optimalTransmissionRatio_le [Nonempty X₁] [Nonempty X₂] [Nonempty Y]
    (P : ProbDist (U × V)) (W : MACChannel X₁ X₂ Y)
    {pm : ℝ} (hpm : ∀ z, P.pmf z ≤ pm) (hpm0 : 0 < pm) (hpm1 : pm < 1) :
    optimalTransmissionRatio P W ≤ (log2 (Fintype.card Y) + 1 + (-log2 pm)) / (-log2 pm) :=
  csSup_le ⟨0, isTransmissibleAtRatio_zero P W⟩
    fun _ h => le_of_isTransmissibleAtRatio P W hpm hpm0 hpm1 h

/-- **Bounds for the rational instances of `Statement`.** With total source weight
    `S = ∑ w`, the non-degeneracy hypothesis gives `P ≤ 1 - 1/S < 1`, whence
    `0 ≤ ρ* ≤ (log₂ e + 1 + L) / L` with `L = -log₂ (1 - 1/S)`. -/
theorem instance_bounds {a b c d e : ℕ} (w : Fin a → Fin b → ℕ) (v : Fin c → Fin d → Fin e → ℕ)
    (hw : 0 < ∑ u, ∑ t, w u t) (hv : ∀ x₁ x₂, 0 < ∑ y, v x₁ x₂ y) (hc : 0 < c) (hd : 0 < d)
    (hnd : ∀ u t, w u t < ∑ u', ∑ t', w u' t') :
    let S : ℝ := ∑ u, ∑ t, (w u t : ℝ)
    let L : ℝ := -log2 (1 - 1 / S)
    0 ≤ optimalTransmissionRatio (sourceOfWeights w hw) (macOfWeights v hv) ∧
      optimalTransmissionRatio (sourceOfWeights w hw) (macOfWeights v hv) ≤
        (log2 (e : ℝ) + 1 + L) / L := by
  intro S L
  have : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have he : 0 < e := by
    have := hv ⟨0, hc⟩ ⟨0, hd⟩
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at this
    · exact h
  have : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
  have hSnat : 2 ≤ ∑ u, ∑ t, w u t := by
    by_contra hlt
    push Not at hlt
    have h1 : ∑ u, ∑ t, w u t = 1 := by omega
    have hall : ∀ u t, w u t = 0 := fun u t => by have := hnd u t; omega
    simp [hall] at hw
  have hS2 : (2 : ℝ) ≤ S := by
    show (2 : ℝ) ≤ ∑ u, ∑ t, (w u t : ℝ)
    exact_mod_cast hSnat
  have hSpos : 0 < S := by linarith
  set pm : ℝ := 1 - 1 / S with hpmdef
  have hpm0 : 0 < pm := by
    have : 1 / S ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hS2
    linarith [hpmdef]
  have hpm1 : pm < 1 := by
    have : 0 < 1 / S := by positivity
    linarith [hpmdef]
  have hpm : ∀ z, (sourceOfWeights w hw).pmf z ≤ pm := by
    intro z
    show (w z.1 z.2 : ℝ) / S ≤ 1 - 1 / S
    have hlt : w z.1 z.2 + 1 ≤ ∑ u, ∑ t, w u t := hnd z.1 z.2
    have hlt' : (w z.1 z.2 : ℝ) + 1 ≤ S := by
      show (w z.1 z.2 : ℝ) + 1 ≤ ∑ u, ∑ t, (w u t : ℝ)
      exact_mod_cast hlt
    rw [div_le_iff₀ hSpos, sub_mul, one_div_mul_cancel hSpos.ne', one_mul]
    linarith
  have hcard : (Fintype.card (Fin e) : ℝ) = (e : ℝ) := by simp
  refine ⟨optimalTransmissionRatio_nonneg _ _ hpm hpm0 hpm1, ?_⟩
  have := optimalTransmissionRatio_le (sourceOfWeights w hw) (macOfWeights v hv) hpm hpm0 hpm1
  rw [hcard] at this
  exact this

end InfoTheory.Known.Certificates.CorrelatedSourcesOverMac
