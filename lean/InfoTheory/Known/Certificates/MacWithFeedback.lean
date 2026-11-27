import InfoTheory.Problems.MacWithFeedback
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.MacWithFeedback`

The frozen statement asks whether, for every finite two-user DM-MAC `W` with noiseless
feedback, some `k ≥ 1` satisfies `macFeedbackCapacityRegion W = coverLeungKLetterRegion k W`.

## Certified (about exactly these objects)
* `isMACFeedbackAchievable_of_isMACAchievable`, `macOperationalRegion_subset_macFeedbackCapacityRegion`
  — a code without feedback is a feedback code whose encoders ignore the feedback.
* `macSingleLetterRegion_subset_macFeedbackCapacityRegion` — hence, by the **MAC capacity
  theorem** (`Bridge.mac_capacity_theorem`, Cover–Thomas Thm. 15.3.1), the no-feedback capacity
  region (closed convex hull of the product-input pentagons) is contained in the feedback
  region. (Feedback can only help; Gaarder–Wolf 1975 show the inclusion can be strict.)
* `macFeedback_err_ge`, `sum_le_log2_card_of_isMACFeedbackAchievable`,
  `macFeedbackCapacityRegion_subset` — a counting converse valid for every feedback code:
  error `≥ 1 - |Y|ⁿ / (M₁ M₂)`, hence `R₁ + R₂ ≤ log₂ |Y|` on the whole feedback region (it uses
  the normalisation of causal chains, `Known.Operational.sum_causal_prod_eq_one`). So the
  operational side is a bounded set.
* `coverLeungKLetterRegion_subset` — for `k ≥ 1`, the `k`-letter Cover–Leung region also
  satisfies `R₁ + R₂ ≤ log₂ |Y|`, and `zero_mem_coverLeungKLetterRegion` — it contains `(0, 0)`
  (constant strategies). So both sides of the statement are nonempty bounded sets.
* Generic counting tools reused by other certificates: `sum_success_le_card`,
  `err_ge_one_sub_card`, `rate_le_log2_of_counting`.

## Not certified
* The sharper outer bound `R₁ + R₂ ≤ C(W) = max I(X₁, X₂; Y)` (the Cover–Thomas feedback
  converse, Thm. 7.12.1 style, not in the library), the dependence-balance bound, and the
  achievability of Cover–Leung (block-Markov superposition coding).
* No statement-level conclusion: the problem is open (Kramer 1998 gives a multi-letter
  directed-information characterisation; Bross–Lapidoth 2005 improved on Cover–Leung).

Sources: Gaarder–Wolf, IEEE Trans. IT 1975; Cover–Leung, IEEE Trans. IT 1981;
El Gamal–Kim, *Network Information Theory*, §17.1; Cover–Thomas Thm. 15.3.1.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MacWithFeedback

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.MacWithFeedback

/-! ### Generic counting converse -/

section Counting

/-- **Counting bound on correct decoding**: if each message `m` induces a probability law
    `T m` on `Ω` and the decoder only sees `π ω ∈ Z`, the total probability of correct decoding
    summed over messages is at most `|Z|`. -/
theorem sum_success_le_card {M Ω Z : Type*} [Fintype M] [Fintype Ω] [Fintype Z] [DecidableEq M]
    (T : M → Ω → ℝ) (hT0 : ∀ m ω, 0 ≤ T m ω) (hT1 : ∀ m, ∑ ω, T m ω = 1)
    (π : Ω → Z) (dec : Z → M) :
    ∑ m, ∑ ω, (if dec (π ω) = m then T m ω else 0) ≤ (Fintype.card Z : ℝ) := by
  classical
  rw [Finset.sum_comm]
  have h1 : ∀ ω, ∑ m, (if dec (π ω) = m then T m ω else 0) = T (dec (π ω)) ω := by
    intro ω; rw [Finset.sum_ite_eq]; simp
  simp_rw [h1]
  have h2 : ∀ ω, T (dec (π ω)) ω = ∑ z, if π ω = z then T (dec z) ω else 0 := by
    intro ω; rw [Finset.sum_ite_eq]; simp
  simp_rw [h2]
  rw [Finset.sum_comm]
  calc ∑ z, ∑ ω, (if π ω = z then T (dec z) ω else 0) ≤ ∑ z : Z, ∑ ω, T (dec z) ω := by
        refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun ω _ => ?_
        split_ifs
        · exact le_rfl
        · exact hT0 _ _
    _ = Fintype.card Z := by simp [hT1]

/-- **Counting converse for the average error**: `P_e ≥ 1 - |Z| / |M|`. -/
theorem err_ge_one_sub_card {M Ω Z : Type*} [Fintype M] [Fintype Ω] [Fintype Z] [DecidableEq M]
    (hM : 0 < Fintype.card M)
    (T : M → Ω → ℝ) (hT0 : ∀ m ω, 0 ≤ T m ω) (hT1 : ∀ m, ∑ ω, T m ω = 1)
    (π : Ω → Z) (dec : Z → M) :
    1 - (Fintype.card Z : ℝ) / Fintype.card M ≤
      ((1 : ℝ) / (Fintype.card M : ℝ)) * ∑ m, ∑ ω, (if dec (π ω) ≠ m then T m ω else 0) := by
  have hS := sum_success_le_card T hT0 hT1 π dec
  have hsplit : ∀ m, ∑ ω, (if dec (π ω) ≠ m then T m ω else 0) =
      1 - ∑ ω, (if dec (π ω) = m then T m ω else 0) := by
    intro m
    rw [← hT1 m, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : dec (π ω) = m <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hMr : (0 : ℝ) < Fintype.card M := by exact_mod_cast hM
  rw [mul_sub, one_div, inv_mul_cancel₀ hMr.ne', ← div_eq_inv_mul]
  have : (∑ m, ∑ ω, (if dec (π ω) = m then T m ω else 0)) / Fintype.card M ≤
      (Fintype.card Z : ℝ) / Fintype.card M :=
    div_le_div_of_nonneg_right hS hMr.le
  linarith

lemma natMax_one_floor_ge (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
  set x : ℝ := (2 : ℝ) ^ ((n : ℝ) * R) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : x / 2 ≤ (Nat.floor x : ℝ) := by
    have h1 : x - 1 < (Nat.floor x : ℝ) := Nat.sub_one_lt_floor x
    by_cases hx2 : x < 2
    · have : (1 : ℝ) ≤ (Nat.floor x : ℝ) := by
        exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx1
      linarith
    · push Not at hx2
      linarith
  have : (Nat.floor x : ℝ) ≤ ((Nat.max 1 (Nat.floor x) : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 1 (Nat.floor x)
  linarith

lemma natMax_one_pos (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- **Rate bound from a counting converse**: if, for every `ε > 0` and all large `n`, there are
    message counts `M ≥ c 2^{nR}` with `1 - Kⁿ / M ≤ ε`, then `R ≤ log₂ K`. -/
theorem rate_le_log2_of_counting {R c : ℝ} {K : ℕ} (hK : 0 < K) (hc : 0 < c)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ M : ℝ, c * (2 : ℝ) ^ ((n : ℝ) * R) ≤ M ∧
      1 - ((K : ℝ) ^ n) / M ≤ ε) : R ≤ log2 K := by
  by_contra hlt
  push Not at hlt
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK2 : (K : ℝ) < (2 : ℝ) ^ R := by
    have e : (2 : ℝ) ^ (log2 (K : ℝ)) = K := by
      unfold log2
      rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne',
        Real.exp_log hKr]
    rw [← e]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  have h2R : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
  set a : ℝ := (K : ℝ) / (2 : ℝ) ^ R with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one h2R]; exact hK2
  have hev : ∀ᶠ n : ℕ in Filter.atTop, a ^ n < c / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).eventually (gt_mem_nhds (half_pos hc))
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  obtain ⟨n, hnN, hn⟩ := ((Filter.eventually_ge_atTop N).and hev).exists
  obtain ⟨M, hM, hcM⟩ := hN n hnN
  have hpow : (2 : ℝ) ^ ((n : ℝ) * R) = ((2 : ℝ) ^ R) ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hpos : (0 : ℝ) < c * (2 : ℝ) ^ ((n : ℝ) * R) := by positivity
  have hp : (0 : ℝ) < ((2 : ℝ) ^ R) ^ n := by positivity
  have hbound : (K : ℝ) ^ n / M ≤ a ^ n / c := by
    calc (K : ℝ) ^ n / M ≤ (K : ℝ) ^ n / (c * (2 : ℝ) ^ ((n : ℝ) * R)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hM
      _ = a ^ n / c := by rw [hpow, ha, div_pow]; field_simp
  have : a ^ n / c < 1 / 2 := by rw [div_lt_iff₀ hc]; linarith
  linarith

end Counting

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-! ### The no-feedback region is inside the feedback region -/

/-- A code without feedback is a feedback code whose encoders ignore the feedback. -/
theorem isMACFeedbackAchievable_of_isMACAchievable (W : MACChannel X₁ X₂ Y) {R₁ R₂ : ℝ}
    (h : IsMACAchievable W R₁ R₂) : IsMACFeedbackAchievable W R₁ R₂ := by
  classical
  obtain ⟨h1, h2, h⟩ := h
  refine ⟨h1, h2, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec, herr⟩ := hN n hn
  refine ⟨fun i m _ => enc₁ m i, fun i m _ => enc₂ m i, dec, le_of_eq_of_le ?_ herr⟩
  have hM : ¬ (max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) = 0 ∨
      max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) = 0) := by
    rintro (h | h) <;> exact absurd h (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)).ne'
  unfold macAvgError
  rw [ite_eq_right hM]
  congr 1

theorem macOperationalRegion_subset_macFeedbackCapacityRegion (W : MACChannel X₁ X₂ Y) :
    macOperationalRegion W ⊆ macFeedbackCapacityRegion W :=
  closure_mono fun _ hp => isMACFeedbackAchievable_of_isMACAchievable W hp

/-- **Feedback does not shrink the MAC capacity region**: the single-letter (no-feedback)
    capacity region of the MAC capacity theorem lies inside `macFeedbackCapacityRegion W`. -/
theorem macSingleLetterRegion_subset_macFeedbackCapacityRegion (W : MACChannel X₁ X₂ Y) :
    macSingleLetterRegion W ⊆ macFeedbackCapacityRegion W := by
  rw [← mac_capacity_theorem]
  exact macOperationalRegion_subset_macFeedbackCapacityRegion W

/-! ### Counting outer bound on the feedback region -/

/-- **Counting converse for feedback MAC codes**: average error `≥ 1 - |Y|ⁿ / (M₁ M₂)`. -/
theorem macFeedback_err_ge (W : MACChannel X₁ X₂ Y) {n M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i.1 → Y) → X₁)
    (enc₂ : ∀ i : Fin n, Fin M₂ → (Fin i.1 → Y) → X₂)
    (dec : (Fin n → Y) → Fin M₁ × Fin M₂) :
    1 - ((Fintype.card Y : ℝ) ^ n) / ((M₁ * M₂ : ℕ) : ℝ) ≤
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
        (if dec y ≠ (m₁, m₂) then ∏ i : Fin n,
          W.trans (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
            enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i) else 0) := by
  classical
  let T : Fin M₁ × Fin M₂ → (Fin n → Y) → ℝ := fun m y => ∏ i : Fin n,
    W.trans (enc₁ i m.1 (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
      enc₂ i m.2 (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)
  have hT0 : ∀ m y, 0 ≤ T m y := fun m y => Finset.prod_nonneg fun i _ => W.nonneg _ _
  have hT1 : ∀ m, ∑ y, T m y = 1 := fun m =>
    sum_causal_prod_eq_one n (fun i h b => W.trans (enc₁ i m.1 h, enc₂ i m.2 h) b)
      (fun i h => W.sum_one _)
  have hcard : 0 < Fintype.card (Fin M₁ × Fin M₂) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; exact Nat.mul_pos hM₁ hM₂
  have h := err_ge_one_sub_card hcard T hT0 hT1 id dec
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at h
  push_cast at h ⊢
  refine le_of_le_of_eq h ?_
  congr 1
  rw [Fintype.sum_prod_type]
  rfl

/-- **Counting sum-rate bound with feedback**: every feedback-achievable pair has
    `R₁ + R₂ ≤ log₂ |Y|`. -/
theorem sum_le_log2_card_of_isMACFeedbackAchievable [Nonempty Y] (W : MACChannel X₁ X₂ Y)
    {R₁ R₂ : ℝ} (h : IsMACFeedbackAchievable W R₁ R₂) : R₁ + R₂ ≤ log2 (Fintype.card Y) := by
  obtain ⟨hR₁, hR₂, h⟩ := h
  refine rate_le_log2_of_counting Fintype.card_pos (by norm_num : (0 : ℝ) < 1 / 4)
    fun ε hε => ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec, herr⟩ := hN n hn
  refine ⟨((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) *
    Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) : ℕ) : ℝ), ?_,
    le_trans (macFeedback_err_ge W (natMax_one_pos _) (natMax_one_pos _) enc₁ enc₂ dec) herr⟩
  have a1 := natMax_one_floor_ge n hR₁
  have a2 := natMax_one_floor_ge n hR₂
  have e : (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂)) =
      (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ ((n : ℝ) * R₂) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  rw [Nat.cast_mul, e]
  have p1 : 0 ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) / 2 := by positivity
  have p2 : 0 ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) / 2 := by positivity
  calc 1 / 4 * ((2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ ((n : ℝ) * R₂))
      = ((2 : ℝ) ^ ((n : ℝ) * R₁) / 2) * ((2 : ℝ) ^ ((n : ℝ) * R₂) / 2) := by ring
    _ ≤ _ := mul_le_mul a1 a2 p2 (by positivity)

/-- **Counting outer bound on the feedback region**:
    `C_FB(W) ⊆ {R₁, R₂ ≥ 0, R₁ + R₂ ≤ log₂ |Y|}`. -/
theorem macFeedbackCapacityRegion_subset [Nonempty Y] (W : MACChannel X₁ X₂ Y) :
    macFeedbackCapacityRegion W ⊆
      { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 + r.2 ≤ log2 (Fintype.card Y) } := by
  refine closure_minimal (fun r hr => ⟨hr.1, hr.2.1,
    sum_le_log2_card_of_isMACFeedbackAchievable W hr⟩) ?_
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

/-! ### The `k`-letter Cover–Leung region -/

lemma log2_card_pow (α : Type*) [Fintype α] (k : ℕ) :
    log2 (Fintype.card (Fin k → α) : ℝ) = k * log2 (Fintype.card α) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  unfold log2
  push_cast
  rw [Real.log_pow]
  ring

/-- `(1/k) I(S; Yᵏ) ≤ log₂ |Y|` (instance passed implicitly so that it unifies with the one
    baked into the region's definition). -/
theorem scaled_mi_le [Nonempty Y] {α : Type*} {_inst : Fintype α} {k : ℕ} (hk : 0 < k)
    (Q : ProbDist (α × (Fin k → Y))) : (1 / (k : ℝ)) * mutualInfo Q ≤ log2 (Fintype.card Y) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hb := (mutualInfo_le_entropy_snd Q).trans (shannonEntropy_le_log2_card _)
  rw [log2_card_pow] at hb
  calc (1 / (k : ℝ)) * mutualInfo Q ≤ (1 / (k : ℝ)) * ((k : ℝ) * log2 (Fintype.card Y)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = log2 (Fintype.card Y) := by field_simp

/-- For `k ≥ 1` the `k`-letter Cover–Leung region satisfies `R₁ + R₂ ≤ log₂ |Y|`. -/
theorem coverLeungKLetterRegion_subset [Nonempty Y] {k : ℕ} (hk : 0 < k)
    (W : MACChannel X₁ X₂ Y) :
    coverLeungKLetterRegion k W ⊆
      { r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 + r.2 ≤ log2 (Fintype.card Y) } := by
  refine closure_minimal (fun r hr => ?_) ?_
  · obtain ⟨h1, h2, kU, Pu, Ps₁, Ps₂, J, -, -, -, h12⟩ := hr
    exact ⟨h1, h2, h12.trans (scaled_mi_le hk _)⟩
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

open Classical in
/-- The `k`-letter Cover–Leung region contains `(0, 0)` (both users play constant strategies). -/
theorem zero_mem_coverLeungKLetterRegion [Nonempty X₁] [Nonempty X₂] (k : ℕ)
    (W : MACChannel X₁ X₂ Y) : ((0 : ℝ), (0 : ℝ)) ∈ coverLeungKLetterRegion k W := by
  let x₁ : X₁ := Classical.arbitrary X₁
  let x₂ : X₂ := Classical.arbitrary X₂
  let s₁ : MACFeedbackStrat k X₁ Y := fun _ _ => x₁
  let s₂ : MACFeedbackStrat k X₂ Y := fun _ _ => x₂
  let Q : ProbDist (Fin k → Y) :=
    { pmf := fun y => (W.power k).trans (fun _ => (x₁, x₂)) y
      nonneg := fun y => (W.power k).nonneg _ y
      sum_one := (W.power k).sum_one _ }
  let J : ProbDist (Fin 1 × MACFeedbackStrat k X₁ Y × MACFeedbackStrat k X₂ Y × (Fin k → Y)) :=
    Q.map (fun y => ((0 : Fin 1), s₁, s₂, y))
  refine subset_closure ⟨le_rfl, le_rfl, 1, ProbDist.uniform, fun _ => diracDist s₁,
    fun _ => diracDist s₂, J, ?_, ?_, ?_, ?_⟩
  · intro u t₁ t₂ y
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    simp only [J, ProbDist.map, ProbDist.uniform, diracDist, Fintype.card_fin, Nat.cast_one,
      div_one, one_mul]
    rw [Finset.sum_eq_single y]
    · by_cases h1 : t₁ = s₁
      · by_cases h2 : t₂ = s₂
        · subst h1; subst h2
          simp [Q, DMC.power, s₁, s₂]
        · simp [h2, Ne.symm h2]
      · simp [h1, Ne.symm h1]
    · intro y' _ hy
      simp [hy]
    · simp
  · exact mul_nonneg (by positivity) (condMutualInfo_nonneg _)
  · exact mul_nonneg (by positivity) (condMutualInfo_nonneg _)
  · simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ)) (mutualInfo_nonneg _)

end InfoTheory.Known.Certificates.MacWithFeedback
