import InfoTheory.Problems.HypercontractivityRibbonDiscrete
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.HypercontractivityRibbonDiscrete`

The frozen statement asks whether, for the uniform-input `m`-ary symmetric channel
`P = (qarySC m α).joint uniform` (`m ≥ 3`), passing the hypercontractive norm inequality on
**two-valued** nonnegative test functions (`passesTwoValuedHCTest P p q`) implies membership of
`(p, q)` in the ribbon, stated through Nair's KL characterization
(`inFullHypercontractivityRibbon P p q`).

Certified here, about the exact objects of `Statement` (no junk values):
* `kl_fst_le`, `kl_snd_le` — marginal data processing for the Core `klDivergence`;
* `ribbon_diag` — every diagonal pair `(p, p)`, `p > 1`, is in the ribbon of every source
  (so the ribbon predicate is satisfiable);
* **regression, `α = 0` (noiseless, `ρ = 1`)**: the Bonami–Beckner hyperbola
  `(p - 1)/(q - 1) ≥ ρ² = 1` is exactly the diagonal:
  - `identity_ribbon_iff` — `inFullHypercontractivityRibbon P p q ↔ 1 < p ∧ p = q`;
  - `identity_twoValued_fails` — for `p < q` the two-valued test already fails
    (`f = g = 1_{0}`), so `passesTwoValuedHCTest` is not vacuously true;
  - `statement_instance_identity` — the implication of `Statement` holds at `α = 0`;
* **regression, `α = (m - 1)/m` (independent, `ρ = 0`)**: `independent_ribbon` — the ribbon is
  the whole region `1 < p ≤ q`, as the hyperbola with `ρ = 0` predicts.

Not certified: the doubly-symmetric binary ribbon `(p - 1)/(q - 1) ≥ (1 - 2α)²` for
`0 < α < 1/2` (Bonami–Beckner; needs the two-point inequality), Nair's equivalence between the
functional and KL forms, the necessity `(p - 1)/(q - 1) ≥ ρ_m²`, and anything about
`0 < α < 1`, `α ≠ (m-1)/m` for `m ≥ 3` (the open question). These facts do not settle
`Statement`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.HypercontractivityRibbonDiscrete

open InfoTheory InfoTheory.Problems.HypercontractivityRibbonDiscrete

/-! ### Generic KL helpers -/

theorem kl_congr {α : Type*} [Fintype α] {P P' Q Q' : ProbDist α}
    (hP : ∀ a, P.pmf a = P'.pmf a) (hQ : ∀ a, Q.pmf a = Q'.pmf a) :
    klDivergence P Q = klDivergence P' Q' := by
  unfold klDivergence; simp only [hP, hQ]

theorem fst_pmf_eq_map {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist (α × β)) (a : α) :
    Q.fst.pmf a = (Q.map Prod.fst).pmf a := by
  classical
  simp only [ProbDist.fst, ProbDist.map, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem snd_pmf_eq_map {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist (α × β)) (b : β) :
    Q.snd.pmf b = (Q.map Prod.snd).pmf b := by
  classical
  simp only [ProbDist.snd, ProbDist.map, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [hc]
  · simp

theorem kl_fst_le {α β : Type*} [Fintype α] [Fintype β] (Q P : ProbDist (α × β))
    (h : AbsCont Q P) : klDivergence Q.fst P.fst ≤ klDivergence Q P := by
  rw [kl_congr (fst_pmf_eq_map Q) (fst_pmf_eq_map P)]
  exact InfoTheory.Bridge.klDivergence_map_le Prod.fst Q P h

theorem kl_snd_le {α β : Type*} [Fintype α] [Fintype β] (Q P : ProbDist (α × β))
    (h : AbsCont Q P) : klDivergence Q.snd P.snd ≤ klDivergence Q P := by
  rw [kl_congr (snd_pmf_eq_map Q) (snd_pmf_eq_map P)]
  exact InfoTheory.Bridge.klDivergence_map_le Prod.snd Q P h

/-- KL divergence of a point mass: `D(δ_{a₀} ‖ Q) = log₂ (1 / Q(a₀))`. -/
theorem kl_of_indicator {α : Type*} [Fintype α] [DecidableEq α] (P Q : ProbDist α) (a₀ : α)
    (hP : ∀ a, P.pmf a = if a = a₀ then 1 else 0) :
    klDivergence P Q = log2 (1 / Q.pmf a₀) := by
  unfold klDivergence
  rw [Finset.sum_eq_single a₀]
  · simp [hP]
  · intro b _ hb; simp [hP, hb]
  · simp

/-- Point mass at `a`. -/
noncomputable def pointMass {α : Type*} [Fintype α] [DecidableEq α] (a : α) : ProbDist α where
  pmf := fun b => if b = a then 1 else 0
  nonneg := fun b => by split_ifs <;> norm_num
  sum_one := by simp

theorem log2_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < log2 x :=
  div_pos (Real.log_pos hx) (Real.log_pos one_lt_two)

/-! ### Every source contains the diagonal -/

theorem ribbon_diag {X Y : Type*} [Fintype X] [Fintype Y] (P : ProbDist (X × Y)) {p : ℝ}
    (hp : 1 < p) : inFullHypercontractivityRibbon P p p := by
  refine ⟨hp, le_rfl, fun Q hQ => ?_⟩
  have h1 := kl_fst_le Q P hQ
  have h2 := kl_snd_le Q P hQ
  have hp0 : 0 ≤ 1 / p := by positivity
  have hp1 : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have e1 := mul_le_mul_of_nonneg_left h1 hp0
  have e2 := mul_le_mul_of_nonneg_left h2 hp1
  nlinarith

/-! ### The `m`-ary symmetric source at `α = 0` (`X = Y`) -/

/-- The uniform-input noiseless `m`-ary source (the `Statement` object at `α = 0`). -/
noncomputable def identitySource (m : ℕ) (hm : 2 ≤ m) : ProbDist (Fin m × Fin m) :=
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  (qarySC m hm 0 le_rfl zero_le_one).joint ProbDist.uniform

theorem identitySource_pmf (m : ℕ) (hm : 2 ≤ m) (x y : Fin m) :
    (identitySource m hm).pmf (x, y) = if x = y then 1 / (m : ℝ) else 0 := by
  simp only [identitySource, DMC.joint, qarySC, ProbDist.uniform, Fintype.card_fin]
  by_cases h : x = y
  · subst h; simp
  · simp [h, Ne.symm h]

theorem identitySource_fst (m : ℕ) (hm : 2 ≤ m) (x : Fin m) :
    (identitySource m hm).fst.pmf x = 1 / (m : ℝ) := by
  simp only [ProbDist.fst, identitySource_pmf]
  rw [Finset.sum_ite_eq]; simp

theorem identitySource_snd (m : ℕ) (hm : 2 ≤ m) (y : Fin m) :
    (identitySource m hm).snd.pmf y = 1 / (m : ℝ) := by
  simp only [ProbDist.snd, identitySource_pmf]
  rw [Finset.sum_ite_eq']; simp

theorem identity_ribbon_iff (m : ℕ) (hm : 2 ≤ m) (p q : ℝ) :
    inFullHypercontractivityRibbon (identitySource m hm) p q ↔ 1 < p ∧ p = q := by
  constructor
  · rintro ⟨hp, hpq, h⟩
    refine ⟨hp, ?_⟩
    by_contra hne
    have hlt : p < q := lt_of_le_of_ne hpq hne
    set a : Fin m := ⟨0, by omega⟩
    let Q : ProbDist (Fin m × Fin m) := pointMass (a, a)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hQ : AbsCont Q (identitySource m hm) := by
      intro xy hxy
      show (if xy = (a, a) then (1 : ℝ) else 0) = 0
      split_ifs with hx
      · subst hx; rw [identitySource_pmf] at hxy; simp at hxy; omega
      · rfl
    have hQ1 : ∀ x, Q.fst.pmf x = if x = a then 1 else 0 := by
      intro x
      simp only [ProbDist.fst, Q, pointMass, Prod.mk.injEq]
      by_cases hx : x = a
      · simp [hx]
      · simp [hx]
    have hQ2 : ∀ y, Q.snd.pmf y = if y = a then 1 else 0 := by
      intro y
      simp only [ProbDist.snd, Q, pointMass, Prod.mk.injEq]
      by_cases hy : y = a
      · simp [hy]
      · simp [hy]
    have k1 : klDivergence Q.fst (identitySource m hm).fst = log2 m := by
      rw [kl_of_indicator _ _ a hQ1, identitySource_fst]; simp
    have k2 : klDivergence Q.snd (identitySource m hm).snd = log2 m := by
      rw [kl_of_indicator _ _ a hQ2, identitySource_snd]; simp
    have k3 : klDivergence Q (identitySource m hm) = log2 m := by
      rw [kl_of_indicator _ _ (a, a) (fun _ => rfl), identitySource_pmf]; simp
    have hL : 0 < log2 (m : ℝ) :=
      log2_pos_of_one_lt (by exact_mod_cast (show 1 < m by omega))
    have key := h Q hQ
    rw [k1, k2, k3] at key
    have hp0 : 0 < p := by linarith
    have hq0 : 0 < q := by linarith
    have : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp0 hlt
    nlinarith
  · rintro ⟨hp, rfl⟩
    exact ribbon_diag _ hp

/-- At `α = 0` and `p < q`, the indicator test functions `f = g = 1_{0}` violate the norm
    inequality: the two-valued test is not vacuous. -/
theorem identity_twoValued_fails (m : ℕ) (hm : 2 ≤ m) (p q : ℝ) (hp : 1 < p) (hpq : p < q) :
    ¬ passesTwoValuedHCTest (identitySource m hm) p q := by
  intro h
  set a : Fin m := ⟨0, by omega⟩
  let f : Fin m → ℝ := fun x => if x = a then 1 else 0
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [f]; split_ifs <;> norm_num
  have hf2 : IsTwoValued f := ⟨1, 0, fun x => by simp only [f]; split_ifs <;> simp⟩
  have key := h f f hf0 hf0 hf2 hf2
  have hp0 : 0 < p := by linarith
  have hq1 : 1 < q := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hq' : 0 < q / (q - 1) := div_pos (by linarith) (by linarith)
  have hpow : ∀ (r : ℝ), 0 < r → ∀ x, f x ^ r = f x := by
    intro r hr x
    simp only [f]; split_ifs
    · exact Real.one_rpow r
    · exact Real.zero_rpow hr.ne'
  -- left side: `P(a, a) = 1/m`
  have hlhs : ∑ xy : Fin m × Fin m, (identitySource m hm).pmf xy * f xy.1 * f xy.2
      = 1 / (m : ℝ) := by
    rw [Finset.sum_eq_single (a, a)]
    · rw [identitySource_pmf]; simp [f]
    · rintro ⟨x, y⟩ _ hxy
      rw [identitySource_pmf]
      by_cases hx : x = a
      · by_cases hy : y = a
        · exact absurd (by rw [hx, hy]) hxy
        · simp [f, hy]
      · simp [f, hx]
    · simp
  have hn1 : ∑ x : Fin m, (identitySource m hm).fst.pmf x * f x ^ p = 1 / (m : ℝ) := by
    simp only [hpow p hp0, identitySource_fst, f]
    simp
  have hn2 : ∑ y : Fin m, (identitySource m hm).snd.pmf y * f y ^ (q / (q - 1))
      = 1 / (m : ℝ) := by
    simp only [hpow _ hq', identitySource_snd, f]
    simp
  rw [hlhs, hn1, hn2, ← Real.rpow_add (by positivity)] at key
  have hexp : 1 < 1 / p + 1 / (q / (q - 1)) := by
    have e : 1 / (q / (q - 1)) = 1 - 1 / q := by
      field_simp
    rw [e]
    have : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp0 hpq
    linarith
  have hb0 : (0 : ℝ) < 1 / m := by positivity
  have hb1 : (1 : ℝ) / m < 1 := by rw [div_lt_one hm0]; exact hm1
  have := Real.rpow_lt_rpow_of_exponent_gt hb0 hb1 hexp
  rw [Real.rpow_one] at this
  linarith

/-- The implication of `Statement` holds at `α = 0` (both sides are equivalent to `p = q`). -/
theorem statement_instance_identity (m : ℕ) (hm : 2 ≤ m) (p q : ℝ) (hp : 1 < p) (hpq : p ≤ q) :
    passesTwoValuedHCTest (identitySource m hm) p q →
      inFullHypercontractivityRibbon (identitySource m hm) p q := by
  intro h
  rcases lt_or_eq_of_le hpq with hlt | heq
  · exact absurd h (identity_twoValued_fails m hm p q hp hlt)
  · exact (identity_ribbon_iff m hm p q).2 ⟨hp, heq⟩

/-! ### The `m`-ary symmetric source at `α = (m - 1)/m` (independent `X`, `Y`) -/

theorem indep_alpha_nonneg (m : ℕ) (hm : 2 ≤ m) : 0 ≤ ((m : ℝ) - 1) / m := by
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply div_nonneg <;> linarith

theorem indep_alpha_le_one (m : ℕ) (hm : 2 ≤ m) : ((m : ℝ) - 1) / m ≤ 1 := by
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_le_one (by linarith)]; linarith

/-- The uniform-input `m`-ary symmetric source at `α = (m - 1)/m`: `X`, `Y` independent. -/
noncomputable def independentSource (m : ℕ) (hm : 2 ≤ m) : ProbDist (Fin m × Fin m) :=
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  (qarySC m hm (((m : ℝ) - 1) / m) (indep_alpha_nonneg m hm) (indep_alpha_le_one m hm)).joint
    ProbDist.uniform

theorem independentSource_pmf (m : ℕ) (hm : 2 ≤ m) (xy : Fin m × Fin m) :
    (independentSource m hm).pmf xy = 1 / ((m : ℝ) * m) := by
  have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  simp only [independentSource, DMC.joint, qarySC, ProbDist.uniform, Fintype.card_fin]
  split_ifs
  · field_simp; ring
  · field_simp

theorem independent_ribbon (m : ℕ) (hm : 2 ≤ m) (p q : ℝ) (hp : 1 < p) (hpq : p ≤ q) :
    inFullHypercontractivityRibbon (independentSource m hm) p q := by
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  refine ⟨hp, hpq, fun Q _ => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hfst : ∀ x, (independentSource m hm).fst.pmf x =
      (ProbDist.uniform : ProbDist (Fin m)).pmf x := by
    intro x
    simp only [ProbDist.fst, independentSource_pmf, ProbDist.uniform, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hsnd : ∀ y, (independentSource m hm).snd.pmf y =
      (ProbDist.uniform : ProbDist (Fin m)).pmf y := by
    intro y
    simp only [ProbDist.snd, independentSource_pmf, ProbDist.uniform, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hjoint : ∀ xy, (independentSource m hm).pmf xy =
      (ProbDist.uniform : ProbDist (Fin m × Fin m)).pmf xy := by
    intro xy
    rw [independentSource_pmf]
    simp [ProbDist.uniform, Fintype.card_prod, Fintype.card_fin]
  rw [kl_congr (fun _ => rfl) hfst, kl_congr (fun _ => rfl) hsnd,
    kl_congr (fun _ => rfl) hjoint]
  have a1 := InfoTheory.Bridge.klDivergence_nonneg Q.fst ProbDist.uniform
    (InfoTheory.Bridge.absCont_uniform _)
  have a2 := InfoTheory.Bridge.klDivergence_nonneg Q.snd ProbDist.uniform
    (InfoTheory.Bridge.absCont_uniform _)
  have hI := InfoTheory.Bridge.mutualInfo_nonneg Q
  unfold mutualInfo at hI
  rw [InfoTheory.Bridge.klDivergence_uniform] at a1 a2 ⊢
  rw [InfoTheory.Bridge.klDivergence_uniform]
  rw [InfoTheory.Bridge.klDivergence_uniform]
  have hcard : log2 (Fintype.card (Fin m × Fin m) : ℝ) = 2 * log2 (Fintype.card (Fin m) : ℝ) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    unfold log2
    rw [Real.log_mul hm0.ne' hm0.ne']; ring
  rw [hcard]
  have hp1 : 1 / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hp0 : 0 ≤ 1 / p := by positivity
  have hq1 : 0 ≤ 1 - 1 / q := by rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hq2 : 1 - 1 / q ≤ 1 := by
    have : 0 ≤ 1 / q := by
      have : 0 < q := by linarith
      positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hp1 a1, mul_le_mul_of_nonneg_right hq2 a2]

end InfoTheory.Known.Certificates.HypercontractivityRibbonDiscrete
