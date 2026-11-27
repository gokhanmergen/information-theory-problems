import InfoTheory.Problems.MultipleDescriptionsGeneral
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.MultipleDescriptionsGeneral`

The frozen statement asks whether, for every finite-alphabet source and distortions,
operational two-description achievability `IsMDAchievable` coincides with the time-sharing
closure of the Zhang–Berger inner bound `InZhangBergerClosure`.

## Certified (about exactly these objects)
* Generic machinery: `rd_map_le_of_codes`, `rd_le_of_timeSharing` (Jensen over the convex
  `R(·)`), and the chain rule `mutualInfo_add_condMutualInfo`
  (`I(X;U) + I(X;V|U) = I(X;VU)`, Cover–Thomas Thm. 2.5.2).
* `isMDAchievable_rd₁_le`, `isMDAchievable_rd₂_le`, `isMDAchievable_rd₀_le` — the
  El Gamal–Cover (1982) outer bounds `R(D₁) ≤ R₁`, `R(D₂) ≤ R₂`, `R(D₀) ≤ R₁ + R₂` for every
  operationally achievable tuple.
* `zhangBerger_rd₁_le`, `zhangBerger_rd₂_le`, `zhangBerger_rd₀_le`,
  `inZhangBergerClosure_rd_le` — the Zhang–Berger region and its closure lie inside the same
  outer bounds (inner ⊆ outer).
* `elGamalCover_subset_zhangBerger` — the El Gamal–Cover inner bound `elGamalCoverMDRegion`
  (from `Core`) is contained in the Zhang–Berger region (take `U₀` constant; Zhang–Berger 1987).
* `trivial_mem_both` — both sides are nonempty: when constant reconstructions meet the
  distortions, every nonnegative rate pair is in the El Gamal–Cover region, in the
  Zhang–Berger closure, and operationally achievable.

## Not certified
* Achievability of the El Gamal–Cover / Zhang–Berger regions (multiple-description coding
  theorem; needs the multivariate covering lemma, not in `Bridge`).
* Ozarow's Gaussian solution and the no-excess-rate results (Ahlswede 1985): out of scope.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MultipleDescriptionsGeneral

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.MultipleDescriptionsGeneral

section Helpers

variable {S α β γ δ : Type*} [Fintype S] [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Pull a distortion measure back along a projection `π : S → α`. -/
def distComap (d : Distortion α β) (π : S → α) : Distortion S β :=
  ⟨fun s y => d.dist (π s) y, fun _ _ => d.nonneg _ _⟩

/-- Data processing on both coordinates: `I(f(X); g(Y)) ≤ I(X; Y)` (Cover–Thomas Thm. 2.8.1). -/
theorem mutualInfo_map_prodMap_le (P : ProbDist (α × β)) (f : α → γ) (g : β → δ) :
    mutualInfo (P.map (Prod.map f g)) ≤ mutualInfo P := by
  set P' := P.map (Prod.map id g) with hP'
  have h1 : mutualInfo P' ≤ mutualInfo P := mutualInfo_map_right_le P g
  have heq : P.map (Prod.map f g) = ((P'.map Prod.swap).map (Prod.map id f)).map Prod.swap := by
    rw [hP', map_comp_eq, map_comp_eq, map_comp_eq]; rfl
  rw [heq, mutualInfo_swap]
  calc mutualInfo ((P'.map Prod.swap).map (Prod.map id f)) ≤ mutualInfo (P'.map Prod.swap) :=
        mutualInfo_map_right_le _ f
    _ = mutualInfo P' := mutualInfo_swap P'
    _ ≤ mutualInfo P := h1

/-- `P(s) ≤ (π_* P)(π s)`. -/
theorem pmf_le_map_pmf (P : ProbDist S) (π : S → α) (s : S) : P.pmf s ≤ (P.map π).pmf (π s) := by
  classical
  simp only [ProbDist.map]
  calc P.pmf s = if π s = π s then P.pmf s else 0 := by simp
    _ ≤ ∑ a : S, if π a = π s then P.pmf a else 0 :=
      Finset.single_le_sum (f := fun a => if π a = π s then P.pmf a else 0)
        (fun a _ => by split_ifs <;> simp [P.nonneg]) (Finset.mem_univ s)

/-- `Q(a, y) ≤ Q_X(a)`. -/
theorem pmf_le_fst_pmf (Q : ProbDist (α × β)) (a : α) (y : β) : Q.pmf (a, y) ≤ Q.fst.pmf a :=
  Finset.single_le_sum (f := fun y => Q.pmf (a, y)) (fun _ _ => Q.nonneg _) (Finset.mem_univ y)

/-- **Rate–distortion of a projection** (Cover–Thomas §10.2): the rate–distortion function of
    `π(S)` under `d` is at most that of `S` under the pulled-back distortion `d ∘ π`. -/
theorem rateDistortion_map_le (P : ProbDist S) (π : S → α) (d : Distortion α β) (D : ℝ) :
    rateDistortion (P.map π) d D ≤ rateDistortion P (distComap d π) D := by
  classical
  by_cases hA : ∃ Q : ProbDist (α × β), Q.fst = P.map π ∧
      (∑ xy : α × β, Q.pmf xy * d.dist xy.1 xy.2) ≤ D
  · obtain ⟨Q, hQf, hQd⟩ := hA
    set Pπ := P.map π with hPπ
    have hQle : ∀ a y, Q.pmf (a, y) ≤ Pπ.pmf a := fun a y => by
      have := pmf_le_fst_pmf Q a y; rwa [hQf] at this
    -- the coupling `Q'(s, y) = P(s) Q(π s, y) / Pπ(π s)`
    have hrow : ∀ s, ∑ y : β, P.pmf s * (Q.pmf (π s, y) / Pπ.pmf (π s)) = P.pmf s := by
      intro s
      rw [← Finset.mul_sum, ← Finset.sum_div]
      have hfst : ∑ y : β, Q.pmf (π s, y) = Pπ.pmf (π s) := by
        have := congrArg (fun R => ProbDist.pmf R (π s)) hQf; simpa [ProbDist.fst] using this
      rw [hfst]
      by_cases h0 : Pπ.pmf (π s) = 0
      · have : P.pmf s = 0 := le_antisymm (h0 ▸ pmf_le_map_pmf P π s) (P.nonneg s)
        simp [this]
      · rw [div_self h0, mul_one]
    let Q' : ProbDist (S × β) :=
      { pmf := fun sy => P.pmf sy.1 * (Q.pmf (π sy.1, sy.2) / Pπ.pmf (π sy.1))
        nonneg := fun sy => mul_nonneg (P.nonneg _) (div_nonneg (Q.nonneg _) (Pπ.nonneg _))
        sum_one := by rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact P.sum_one }
    have hQ'f : Q'.fst = P := by
      refine probDist_eq_of_pmf fun s => ?_
      simp only [ProbDist.fst, Q']; exact hrow s
    have hQ'd : (∑ sy : S × β, Q'.pmf sy * (distComap d π).dist sy.1 sy.2) ≤ D := by
      have h1 : (∑ sy : S × β, Q'.pmf sy * (distComap d π).dist sy.1 sy.2) =
          ∑ s : S, P.pmf s * (fun a => ∑ y : β, Q.pmf (a, y) / Pπ.pmf a * d.dist a y) (π s) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Q', distComap, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring
      rw [h1, sum_pmf_mul_comp P π (fun a => ∑ y : β, Q.pmf (a, y) / Pπ.pmf a * d.dist a y)]
      have h2 : ∀ a : α, Pπ.pmf a * (∑ y : β, Q.pmf (a, y) / Pπ.pmf a * d.dist a y) =
          ∑ y : β, Q.pmf (a, y) * d.dist a y := by
        intro a
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h0 : Pπ.pmf a = 0
        · have : Q.pmf (a, y) = 0 := le_antisymm (h0 ▸ hQle a y) (Q.nonneg _)
          simp [this]
        · field_simp
      rw [← hPπ]
      simp_rw [h2]
      rw [← Fintype.sum_prod_type (f := fun xy : α × β => Q.pmf xy * d.dist xy.1 xy.2)]
      exact hQd
    unfold rateDistortion
    refine le_csInf ⟨mutualInfo Q', Q', hQ'f, hQ'd, rfl⟩ ?_
    rintro b ⟨Q'', hQ''f, hQ''d, rfl⟩
    set Q3 := Q''.map (Prod.map π id) with hQ3
    have hQ3f : Q3.fst = P.map π := by
      rw [← map_fst_eq_fst, hQ3, map_comp_eq, ← hQ''f, ← map_fst_eq_fst, map_comp_eq]; rfl
    have hQ3d : (∑ xy : α × β, Q3.pmf xy * d.dist xy.1 xy.2) ≤ D := by
      rw [hQ3, ← sum_pmf_mul_comp Q'' (Prod.map π id) (fun xy => d.dist xy.1 xy.2)]
      exact hQ''d
    calc sInf { r : ℝ | ∃ Q : ProbDist (α × β), Q.fst = P.map π ∧
          (∑ xy : α × β, Q.pmf xy * d.dist xy.1 xy.2) ≤ D ∧ r = mutualInfo Q }
        ≤ mutualInfo Q3 := csInf_le ⟨0, by rintro r ⟨Q, -, -, rfl⟩; exact mutualInfo_nonneg Q⟩
          ⟨Q3, hQ3f, hQ3d, rfl⟩
      _ ≤ mutualInfo Q'' := mutualInfo_map_prodMap_le Q'' π id
  · have hempty : { r : ℝ | ∃ Q : ProbDist (α × β), Q.fst = P.map π ∧
        (∑ xy : α × β, Q.pmf xy * d.dist xy.1 xy.2) ≤ D ∧ r = mutualInfo Q } = ∅ := by
      ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨Q, h1, h2, -⟩; exact hA ⟨Q, h1, h2⟩
    unfold rateDistortion
    rw [hempty, Real.sInf_empty]
    exact rateDistortion_nonneg P (distComap d π) D

/-- `1 ≤ max 1 ⌊x⌋` and `max 1 ⌊x⌋ ≤ x` for `x ≥ 1`. -/
theorem one_le_natMaxFloor (x : ℝ) : 1 ≤ Nat.max 1 (Nat.floor x) := le_max_left _ _

theorem natMaxFloor_le {x : ℝ} (hx : 1 ≤ x) : ((Nat.max 1 (Nat.floor x) : ℕ) : ℝ) ≤ x := by
  have h1 : 1 ≤ Nat.floor x := Nat.le_floor (by exact_mod_cast hx)
  have : Nat.max 1 (Nat.floor x) = Nat.floor x := max_eq_right h1
  rw [this]; exact Nat.floor_le (by linarith)

/-- Rate-`(R + ε)` codebook sizes are at most `2^{n(R+ε)}`. -/
theorem natMaxFloor_rpow_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * r))) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * r) :=
  natMaxFloor_le (Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hr))

omit [Fintype β] in
/-- Any family of codes with at most `2^{nR}` codewords yields operational achievability. -/
theorem isRDAchievable_of_codes (P : ProbDist α) (d : Distortion α β) {D R : ℝ} (hR : 0 ≤ R)
    (h : ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ K : ℕ, 1 ≤ K ∧ (K : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) ∧
      ∃ (enc : (Fin n → α) → Fin K) (dec : Fin K → Fin n → β),
        ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (dec (enc x)) ≤ D + δ) :
    IsRateDistortionAchievable P d D R := by
  refine ⟨hR, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨max N 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun n hn => ?_⟩
  obtain ⟨K, hK1, hKle, enc, dec, hcode⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hKM : K ≤ Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) :=
    le_trans (Nat.le_floor hKle) (le_max_right _ _)
  refine ⟨fun x => Fin.castLE hKM (enc x), fun m => dec ⟨min m.1 (K - 1), by omega⟩, ?_⟩
  have hdec : ∀ x, dec ⟨min (Fin.castLE hKM (enc x)).1 (K - 1), by omega⟩ = dec (enc x) := by
    intro x; congr 1; ext; simp only [Fin.val_castLE]; have := (enc x).2; omega
  simp_rw [hdec]; exact hcode

/-- **Code-to-converse bridge.** If, for every `η, δ > 0`, the source `S ~ P` has block codes
    with at most `2^{n(R+η)}` codewords whose reconstruction of `π(S)` has expected distortion
    `≤ D + δ`, then `R(π_* P, d, D) ≤ R` (Cover–Thomas Thm. 10.2.1 converse, via
    `rateDistortion_operational_converse`). -/
theorem rd_map_le_of_codes (P : ProbDist S) (π : S → α) (d : Distortion α β) {D R : ℝ}
    (hR : 0 ≤ R)
    (h : ∀ η > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ K : ℕ, 1 ≤ K ∧
      (K : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (R + η)) ∧
      ∃ (enc : (Fin n → S) → Fin K) (dec : Fin K → Fin n → β),
        ∑ x : Fin n → S, (∏ i : Fin n, P.pmf (x i)) *
          ((1 / (n : ℝ)) * ∑ i : Fin n, d.dist (π (x i)) (dec (enc x) i)) ≤ D + δ) :
    rateDistortion (P.map π) d D ≤ R := by
  refine le_trans (rateDistortion_map_le P π d D) ?_
  refine le_of_forall_pos_le_add fun η hη => ?_
  exact rateDistortion_operational_converse P (distComap d π)
    (isRDAchievable_of_codes P _ (by linarith) (h η hη))

/-- Product of two rate-`(Rᵢ + ε)` codebook sizes is at most `2^{n(R₁+R₂+η)}` when `2ε ≤ η`. -/
theorem card_mul_le {n : ℕ} {R₁ R₂ ε η : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hε : 0 < ε)
    (hεη : 2 * ε ≤ η) :
    ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε)))) *
      Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε)))) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂ + η)) := by
  rw [Nat.cast_mul]
  calc _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + ε)) * (2 : ℝ) ^ ((n : ℝ) * (R₂ + ε)) :=
        mul_le_mul (natMaxFloor_rpow_le (by linarith)) (natMaxFloor_rpow_le (by linarith))
          (Nat.cast_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂ + 2 * ε)) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + R₂ + η)) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))

/-- Feasibility of a distortion level: some test channel achieves expected distortion `≤ D`. -/
def RDFeasible (P : ProbDist α) (d : Distortion α β) (D : ℝ) : Prop :=
  ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D

theorem RDFeasible.mono {P : ProbDist α} {d : Distortion α β} {D D' : ℝ}
    (h : RDFeasible P d D) (hD : D ≤ D') : RDFeasible P d D' := by
  obtain ⟨Q, h1, h2⟩ := h; exact ⟨Q, h1, le_trans h2 hD⟩

/-- At an infeasible distortion level the defining set is empty, so `R(D) = sInf ∅ = 0`. -/
theorem rateDistortion_eq_zero_of_not_feasible {P : ProbDist α} {d : Distortion α β} {D : ℝ}
    (h : ¬ RDFeasible P d D) : rateDistortion P d D = 0 := by
  unfold rateDistortion
  have hempty : { r : ℝ | ∃ Q : ProbDist (α × β), Q.fst = P ∧
      (∑ xy : α × β, Q.pmf xy * d.dist xy.1 xy.2) ≤ D ∧ r = mutualInfo Q } = ∅ := by
    ext r; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨Q, h1, h2, -⟩; exact h ⟨Q, h1, h2⟩
  rw [hempty, Real.sInf_empty]

/-- Limit argument: if `R(D + ε) ≤ R + ε` for all `ε > 0` and `R ≥ 0`, then `R(D) ≤ R`
    (right-continuity of `R(·)` at feasible `D`, `rateDistortion_rightContinuous`). -/
theorem rd_le_of_forall_pos {P : ProbDist α} {d : Distortion α β} {D R : ℝ} (hR : 0 ≤ R)
    (h : ∀ ε > 0, rateDistortion P d (D + ε) ≤ R + ε) : rateDistortion P d D ≤ R := by
  by_cases hf : RDFeasible P d D
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨δ, hδ, hrc⟩ := rateDistortion_rightContinuous P d hf (ε / 2) (by linarith)
    have h1 : rateDistortion P d (D + δ) ≤ rateDistortion P d (D + min δ (ε / 2)) :=
      rateDistortion_antitone (hf.mono (by linarith [lt_min hδ (half_pos hε)]))
        (by linarith [min_le_left δ (ε / 2)])
    have h2 := h (min δ (ε / 2)) (lt_min hδ (half_pos hε))
    linarith [min_le_right δ (ε / 2)]
  · rw [rateDistortion_eq_zero_of_not_feasible hf]; exact hR

/-- Convexity of `R(·)` on the (convex, upward-closed) set of feasible distortion levels. -/
theorem rateDistortion_convexOn (P : ProbDist α) (d : Distortion α β) :
    ConvexOn ℝ { D | RDFeasible P d D } (rateDistortion P d) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rcases le_total x y with hxy | hxy
    · refine RDFeasible.mono hx ?_
      simp only [smul_eq_mul]; rw [show a = 1 - b by linarith]
      nlinarith [mul_nonneg hb (sub_nonneg.2 hxy)]
    · refine RDFeasible.mono hy ?_
      simp only [smul_eq_mul]; rw [show b = 1 - a by linarith]
      nlinarith [mul_nonneg ha (sub_nonneg.2 hxy)]
  · intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    simpa [smul_eq_mul] using rateDistortion_convex hx hy ha (by linarith)

/-- **Time-sharing (Jensen) bound**: for a probability vector `w` and feasible levels `δᵢ`,
    `R(∑ wᵢ δᵢ) ≤ ∑ wᵢ R(δᵢ)` (Cover–Thomas Lemma 10.4.1 iterated). -/
theorem rd_sum_le (P : ProbDist α) (d : Distortion α β) {m : ℕ} (w δ : Fin m → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : Fin m, w i = 1) (hf : ∀ i, RDFeasible P d (δ i)) :
    rateDistortion P d (∑ i : Fin m, w i * δ i) ≤ ∑ i : Fin m, w i * rateDistortion P d (δ i) := by
  have := (rateDistortion_convexOn P d).map_sum_le (t := Finset.univ) (w := w) (p := δ)
    (fun i _ => hw0 i) hw1 (fun i _ => hf i)
  simpa [smul_eq_mul] using this

/-- A convex combination of feasible levels is feasible. -/
theorem rdFeasible_sum (P : ProbDist α) (d : Distortion α β) {m : ℕ} (w δ : Fin m → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : Fin m, w i = 1) (hf : ∀ i, RDFeasible P d (δ i)) :
    RDFeasible P d (∑ i : Fin m, w i * δ i) := by
  have := (rateDistortion_convexOn P d).1.sum_mem (t := Finset.univ) (w := w) (z := δ)
    (fun i _ => hw0 i) hw1 (fun i _ => hf i)
  simpa [smul_eq_mul] using this

/-- Closure bookkeeping: if each time-sharing component satisfies `R(δᵢ) ≤ rᵢ` at a feasible
    `δᵢ`, and `∑ wᵢ δᵢ ≤ D + ε`, `∑ wᵢ rᵢ ≤ R + ε` for all `ε > 0`, then `R(D) ≤ R`. -/
theorem rd_le_of_timeSharing {P : ProbDist α} {d : Distortion α β} {D R : ℝ}
    (h : ∀ ε > 0, ∃ (m : ℕ) (w r δ : Fin m → ℝ), (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
      (∀ i, RDFeasible P d (δ i)) ∧ (∀ i, rateDistortion P d (δ i) ≤ r i) ∧
      (∑ i : Fin m, w i * δ i) ≤ D + ε ∧ (∑ i : Fin m, w i * r i) ≤ R + ε) :
    rateDistortion P d D ≤ R := by
  have hR : 0 ≤ R := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m, w, r, δ, hw0, hw1, hf, hle, -, hr⟩ := h ε hε
    have : 0 ≤ ∑ i : Fin m, w i * r i := Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw0 i) (le_trans (rateDistortion_nonneg P d _) (hle i))
    linarith
  refine rd_le_of_forall_pos hR fun ε hε => ?_
  obtain ⟨m, w, r, δ, hw0, hw1, hf, hle, hδ, hr⟩ := h ε hε
  calc rateDistortion P d (D + ε) ≤ rateDistortion P d (∑ i : Fin m, w i * δ i) :=
        rateDistortion_antitone (rdFeasible_sum P d w δ hw0 hw1 hf) hδ
    _ ≤ ∑ i : Fin m, w i * rateDistortion P d (δ i) := rd_sum_le P d w δ hw0 hw1 hf
    _ ≤ ∑ i : Fin m, w i * r i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hw0 i)
    _ ≤ R + ε := hr

/-- `I(X; Y | Z) = 0` when `X` is constant. -/
theorem condMutualInfo_map_const_fst {ι : Type*} [Fintype ι] (R : ProbDist ι) (c : α)
    (f : ι → β) (g : ι → γ) : condMutualInfo (R.map (fun i => (c, f i, g i))) = 0 := by
  have e0 : R.map (fun i => (c, f i, g i)) =
      (R.map (fun i => (f i, g i))).map (fun yz => (c, yz.1, yz.2)) := by rw [map_comp_eq]; rfl
  have e1 : (R.map (fun i => (c, f i, g i))).map (fun t => (t.1, t.2.2)) =
      (R.map g).map (fun z => (c, z)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (R.map (fun i => (c, f i, g i))).map (fun t => (t.2.1, t.2.2)) =
      R.map (fun i => (f i, g i)) := by rw [map_comp_eq]; rfl
  have e3 : (R.map (fun i => (c, f i, g i))).map (fun t => t.2.2) = R.map g := by
    rw [map_comp_eq]; rfl
  have i0 : Function.Injective (fun yz : β × γ => (c, yz.1, yz.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2
  have i1 : Function.Injective (fun z : γ => (c, z)) := fun a b h => (Prod.mk.inj h).2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ i0, shannonEntropy_map_of_injective _ i1]
  ring

/-- `I(X; Y | Z) = 0` when `Y` is constant. -/
theorem condMutualInfo_map_const_snd {ι : Type*} [Fintype ι] (R : ProbDist ι) (c : β)
    (f : ι → α) (g : ι → γ) : condMutualInfo (R.map (fun i => (f i, c, g i))) = 0 := by
  have e0 : R.map (fun i => (f i, c, g i)) =
      (R.map (fun i => (f i, g i))).map (fun xz => (xz.1, c, xz.2)) := by rw [map_comp_eq]; rfl
  have e1 : (R.map (fun i => (f i, c, g i))).map (fun t => (t.1, t.2.2)) =
      R.map (fun i => (f i, g i)) := by rw [map_comp_eq]; rfl
  have e2 : (R.map (fun i => (f i, c, g i))).map (fun t => (t.2.1, t.2.2)) =
      (R.map g).map (fun z => (c, z)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (R.map (fun i => (f i, c, g i))).map (fun t => t.2.2) = R.map g := by
    rw [map_comp_eq]; rfl
  have i0 : Function.Injective (fun xz : α × γ => (xz.1, c, xz.2)) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.2
  have i1 : Function.Injective (fun z : γ => (c, z)) := fun a b h => (Prod.mk.inj h).2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ i0, shannonEntropy_map_of_injective _ i1]
  ring

/-- `I(X; Y) = 0` when `Y` is constant. -/
theorem mutualInfo_map_const_snd {ι : Type*} [Fintype ι] (R : ProbDist ι) (f : ι → α) (c : β) :
    mutualInfo (R.map (fun i => (f i, c))) = 0 := by
  have e0 : R.map (fun i => (f i, c)) = (R.map f).map (fun x => (x, c)) := by
    rw [map_comp_eq]; rfl
  have e1 : (R.map (fun i => (f i, c))).fst = R.map f := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have e2 : (R.map (fun i => (f i, c))).snd = R.map (fun _ => c) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have i0 : Function.Injective (fun x : α => (x, c)) := fun a b h => (Prod.mk.inj h).1
  unfold mutualInfo
  rw [e1, e2, shannonEntropy_map_const, e0, shannonEntropy_map_of_injective _ i0]
  ring

/-- Expected block distortion of a constant reconstruction equals (at most) the single-letter
    expected distortion. -/
theorem iid_avg_coord_le (P : ProbDist α) (n : ℕ) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ x : Fin n → α, (∏ i : Fin n, P.pmf (x i)) * ((1 / (n : ℝ)) * ∑ i : Fin n, f (x i)) ≤
      ∑ a : α, P.pmf a * f a := by
  have hS : 0 ≤ ∑ a : α, P.pmf a * f a := Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (hf a)
  have h1 : ∑ x : Fin n → α, (∏ i : Fin n, P.pmf (x i)) * ((1 / (n : ℝ)) * ∑ i : Fin n, f (x i)) =
      (1 / (n : ℝ)) * ∑ i : Fin n, ∑ x : Fin n → α, (iidDist P n).pmf x * f (x i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [iidDist]; ring
  rw [h1]
  simp_rw [iidDist_sum_coord P f]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [hS]
  · rw [← mul_assoc, one_div_mul_cancel (by positivity), one_mul]

/-- **Chain rule for mutual information** (Cover–Thomas Thm. 2.5.2):
    `I(X; U) + I(X; V | U) = I(X; (V, U))`. -/
theorem mutualInfo_add_condMutualInfo {ι : Type*} [Fintype ι] (R : ProbDist ι) (fx : ι → α)
    (fu : ι → β) (fv : ι → γ) :
    mutualInfo (R.map (fun i => (fx i, fu i))) +
      condMutualInfo (R.map (fun i => (fx i, fv i, fu i))) =
      mutualInfo (R.map (fun i => (fx i, (fv i, fu i)))) := by
  have a1 : (R.map (fun i => (fx i, fu i))).fst = R.map fx := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have a2 : (R.map (fun i => (fx i, fu i))).snd = R.map fu := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have b1 : (R.map (fun i => (fx i, fv i, fu i))).map (fun t => (t.1, t.2.2)) =
      R.map (fun i => (fx i, fu i)) := by rw [map_comp_eq]; rfl
  have b2 : (R.map (fun i => (fx i, fv i, fu i))).map (fun t => (t.2.1, t.2.2)) =
      R.map (fun i => (fv i, fu i)) := by rw [map_comp_eq]; rfl
  have b3 : (R.map (fun i => (fx i, fv i, fu i))).map (fun t => t.2.2) = R.map fu := by
    rw [map_comp_eq]; rfl
  have c1 : (R.map (fun i => (fx i, (fv i, fu i)))).fst = R.map fx := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have c2 : (R.map (fun i => (fx i, (fv i, fu i)))).snd = R.map (fun i => (fv i, fu i)) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have c3 : R.map (fun i => (fx i, (fv i, fu i))) =
      (R.map (fun i => (fx i, fv i, fu i))).map (fun t => (t.1, (t.2.1, t.2.2))) := by
    rw [map_comp_eq]; rfl
  have hinj : Function.Injective (fun t : α × γ × β => (t.1, (t.2.1, t.2.2))) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  unfold mutualInfo condMutualInfo; dsimp only
  rw [a1, a2, b1, b2, b3, c1, c2, c3, shannonEntropy_map_of_injective _ hinj]
  ring

theorem map_id_eq (P : ProbDist α) : P.map id = P := by
  classical
  refine probDist_eq_of_pmf fun a => ?_
  simp [ProbDist.map]

/-- A single rate-`(R + ε)` codebook has at most `2^{n(R+η)}` words when `ε ≤ η`. -/
theorem card_le {n : ℕ} {R ε η : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hεη : ε ≤ η) :
    ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R + ε)))) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (R + η)) :=
  le_trans (natMaxFloor_rpow_le (by linarith)) (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)))

end Helpers

section MD

variable {X Xh₀ Xh₁ Xh₂ : Type*} [Fintype X] [Fintype Xh₀] [Fintype Xh₁] [Fintype Xh₂]

/-! ### Operational outer bounds (El Gamal–Cover 1982, §II) -/

/-- Each description alone is a rate-`R₁` code: `R(D₁) ≤ R₁`. -/
theorem isMDAchievable_rd₁_le (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : IsMDAchievable P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂) : rateDistortion P d₁ D₁ ≤ R₁ := by
  obtain ⟨hR₁, hR₂, hach⟩ := h
  rw [← map_id_eq P]
  refine rd_map_le_of_codes P id d₁ hR₁ fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min η δ) (lt_min hη hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₀, dec₁, dec₂, -, hD₁, -⟩ := hN n hn
  refine ⟨_, one_le_natMaxFloor _, card_le hR₁ (lt_min hη hδ) (min_le_left _ _), enc₁, dec₁, ?_⟩
  exact le_trans hD₁ (by linarith [min_le_right η δ])

/-- `R(D₂) ≤ R₂`. -/
theorem isMDAchievable_rd₂_le (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : IsMDAchievable P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂) : rateDistortion P d₂ D₂ ≤ R₂ := by
  obtain ⟨hR₁, hR₂, hach⟩ := h
  rw [← map_id_eq P]
  refine rd_map_le_of_codes P id d₂ hR₂ fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min η δ) (lt_min hη hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₀, dec₁, dec₂, -, -, hD₂⟩ := hN n hn
  refine ⟨_, one_le_natMaxFloor _, card_le hR₂ (lt_min hη hδ) (min_le_left _ _), enc₂, dec₂, ?_⟩
  exact le_trans hD₂ (by linarith [min_le_right η δ])

/-- The pair of descriptions is a rate-`(R₁ + R₂)` code: `R(D₀) ≤ R₁ + R₂`. -/
theorem isMDAchievable_rd₀_le (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : IsMDAchievable P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂) : rateDistortion P d₀ D₀ ≤ R₁ + R₂ := by
  obtain ⟨hR₁, hR₂, hach⟩ := h
  rw [← map_id_eq P]
  refine rd_map_le_of_codes P id d₀ (by linarith) fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min (η / 2) δ) (lt_min (by linarith) hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₀, dec₁, dec₂, hD₀, -, -⟩ := hN n hn
  refine ⟨_, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity)),
    card_mul_le hR₁ hR₂ (lt_min (by linarith) hδ) (by linarith [min_le_left (η / 2) δ]),
    fun x => finProdFinEquiv (enc₁ x, enc₂ x), fun k => dec₀ (finProdFinEquiv.symm k), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact le_trans hD₀ (by linarith [min_le_right (η / 2) δ])

/-! ### The Zhang–Berger region lies inside the same outer bound -/

/-- `R(D₁) ≤ r₁` on the Zhang–Berger region: `r₁ ≥ I(X; U₀X̂₁) ≥ I(X; X̂₁)`. -/
theorem zhangBerger_rd₁_le (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {D₀ D₁ D₂ : ℝ} {r : ℝ × ℝ}
    (hr : r ∈ zhangBergerMDRegion P d₀ d₁ d₂ D₀ D₁ D₂) :
    RDFeasible P d₁ D₁ ∧ rateDistortion P d₁ D₁ ≤ r.1 := by
  obtain ⟨-, -, kU₀, Q, hQ, -, hd₁, -, h₁, -, -⟩ := hr
  set Q'' := Q.map (fun t => (t.1, t.2.2.2.1)) with hQ''
  have hf : Q''.fst = P := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQ, ← map_fst_eq_fst]; rfl
  have hdist : expectedDist Q'' d₁ ≤ D₁ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.1, t.2.2.2.1))
      (fun xy : X × Xh₁ => d₁.dist xy.1 xy.2)]; exact hd₁
  have hmi : mutualInfo Q'' ≤ mutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.2.1)))) := by
    have : Q'' = (Q.map (fun t => (t.1, (t.2.1, t.2.2.2.1)))).map (Prod.map id Prod.snd) := by
      rw [hQ'', map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  exact ⟨⟨Q'', hf, hdist⟩, by linarith [rateDistortion_le_mutualInfo hf hdist]⟩

/-- `R(D₂) ≤ r₂` on the Zhang–Berger region. -/
theorem zhangBerger_rd₂_le (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {D₀ D₁ D₂ : ℝ} {r : ℝ × ℝ}
    (hr : r ∈ zhangBergerMDRegion P d₀ d₁ d₂ D₀ D₁ D₂) :
    RDFeasible P d₂ D₂ ∧ rateDistortion P d₂ D₂ ≤ r.2 := by
  obtain ⟨-, -, kU₀, Q, hQ, -, -, hd₂, -, h₂, -⟩ := hr
  set Q'' := Q.map (fun t => (t.1, t.2.2.2.2)) with hQ''
  have hf : Q''.fst = P := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQ, ← map_fst_eq_fst]; rfl
  have hdist : expectedDist Q'' d₂ ≤ D₂ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.1, t.2.2.2.2))
      (fun xy : X × Xh₂ => d₂.dist xy.1 xy.2)]; exact hd₂
  have hmi : mutualInfo Q'' ≤ mutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.2.2)))) := by
    have : Q'' = (Q.map (fun t => (t.1, (t.2.1, t.2.2.2.2)))).map (Prod.map id Prod.snd) := by
      rw [hQ'', map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  exact ⟨⟨Q'', hf, hdist⟩, by linarith [rateDistortion_le_mutualInfo hf hdist]⟩

/-- `R(D₀) ≤ r₁ + r₂` on the Zhang–Berger region:
    `r₁ + r₂ ≥ I(X;U₀) + I(X; X̂₀X̂₁X̂₂ | U₀) = I(X; X̂₀X̂₁X̂₂U₀) ≥ I(X; X̂₀)` (chain rule + DPI). -/
theorem zhangBerger_rd₀_le (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {D₀ D₁ D₂ : ℝ} {r : ℝ × ℝ}
    (hr : r ∈ zhangBergerMDRegion P d₀ d₁ d₂ D₀ D₁ D₂) :
    RDFeasible P d₀ D₀ ∧ rateDistortion P d₀ D₀ ≤ r.1 + r.2 := by
  obtain ⟨-, -, kU₀, Q, hQ, hd₀, -, -, -, -, hsum⟩ := hr
  set Q'' := Q.map (fun t => (t.1, t.2.2.1)) with hQ''
  have hf : Q''.fst = P := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQ, ← map_fst_eq_fst]; rfl
  have hdist : expectedDist Q'' d₀ ≤ D₀ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.1, t.2.2.1))
      (fun xy : X × Xh₀ => d₀.dist xy.1 xy.2)]; exact hd₀
  have hmi : mutualInfo Q'' ≤
      mutualInfo (Q.map (fun t => (t.1, ((t.2.2.1, t.2.2.2.1, t.2.2.2.2), t.2.1)))) := by
    have : Q'' = (Q.map (fun t => (t.1, ((t.2.2.1, t.2.2.2.1, t.2.2.2.2), t.2.1)))).map
        (Prod.map id (fun vu => vu.1.1)) := by rw [hQ'', map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  have hchain := mutualInfo_add_condMutualInfo Q (fun t => t.1) (fun t => t.2.1)
    (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2))
  have h0 := mutualInfo_nonneg (Q.map (fun t => (t.1, t.2.1)))
  have h3 := condMutualInfo_nonneg (Q.map (fun t => (t.2.2.2.1, t.2.2.2.2, t.2.1)))
  exact ⟨⟨Q'', hf, hdist⟩, by linarith [rateDistortion_le_mutualInfo hf hdist]⟩

/-- **The time-sharing closure of the Zhang–Berger region obeys the El Gamal–Cover outer
    bounds** `R(D₁) ≤ R₁`, `R(D₂) ≤ R₂`, `R(D₀) ≤ R₁ + R₂`, exactly as the operational region
    does (`isMDAchievable_rd₀_le` etc.). -/
theorem inZhangBergerClosure_rd_le (P : ProbDist X) (d₀ : Distortion X Xh₀)
    (d₁ : Distortion X Xh₁) (d₂ : Distortion X Xh₂) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h : InZhangBergerClosure P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂) :
    rateDistortion P d₁ D₁ ≤ R₁ ∧ rateDistortion P d₂ D₂ ≤ R₂ ∧
      rateDistortion P d₀ D₀ ≤ R₁ + R₂ := by
  refine ⟨rd_le_of_timeSharing fun ε hε => ?_, rd_le_of_timeSharing fun ε hε => ?_,
    rd_le_of_timeSharing fun ε hε => ?_⟩
  · obtain ⟨m, w, r₁, r₂, δ₀, δ₁, δ₂, hw0, hw1, hin, hr₁, -, -, hδ₁, -⟩ := h ε hε
    exact ⟨m, w, r₁, δ₁, hw0, hw1, fun i => (zhangBerger_rd₁_le P d₀ d₁ d₂ (hin i)).1,
      fun i => (zhangBerger_rd₁_le P d₀ d₁ d₂ (hin i)).2, hδ₁, hr₁⟩
  · obtain ⟨m, w, r₁, r₂, δ₀, δ₁, δ₂, hw0, hw1, hin, -, hr₂, -, -, hδ₂⟩ := h ε hε
    exact ⟨m, w, r₂, δ₂, hw0, hw1, fun i => (zhangBerger_rd₂_le P d₀ d₁ d₂ (hin i)).1,
      fun i => (zhangBerger_rd₂_le P d₀ d₁ d₂ (hin i)).2, hδ₂, hr₂⟩
  · obtain ⟨m, w, r₁, r₂, δ₀, δ₁, δ₂, hw0, hw1, hin, hr₁, hr₂, hδ₀, -, -⟩ := h (ε / 2) (half_pos hε)
    refine ⟨m, w, fun i => r₁ i + r₂ i, δ₀, hw0, hw1,
      fun i => (zhangBerger_rd₀_le P d₀ d₁ d₂ (hin i)).1,
      fun i => (zhangBerger_rd₀_le P d₀ d₁ d₂ (hin i)).2, by linarith, ?_⟩
    simp only [mul_add, Finset.sum_add_distrib]; linarith

/-! ### El Gamal–Cover ⊆ Zhang–Berger, and nonemptiness -/

/-- **El Gamal–Cover inner bound ⊆ Zhang–Berger inner bound** (take `U₀` constant;
    Zhang–Berger 1987). -/
theorem elGamalCover_subset_zhangBerger (P : ProbDist X) (d₀ : Distortion X Xh₀)
    (d₁ : Distortion X Xh₁) (d₂ : Distortion X Xh₂) (D₀ D₁ D₂ : ℝ) :
    elGamalCoverMDRegion P d₀ d₁ d₂ D₀ D₁ D₂ ⊆ zhangBergerMDRegion P d₀ d₁ d₂ D₀ D₁ D₂ := by
  rintro r ⟨hr₁, hr₂, Q, hQ, hd₀, hd₁, hd₂, h₁, h₂, hsum⟩
  let f : X × Xh₀ × Xh₁ × Xh₂ → X × Fin 1 × Xh₀ × Xh₁ × Xh₂ :=
    fun t => (t.1, 0, t.2.1, t.2.2.1, t.2.2.2)
  refine ⟨hr₁, hr₂, 1, Q.map f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_fst_eq_fst, map_comp_eq, ← hQ, ← map_fst_eq_fst]; rfl
  · rw [← sum_pmf_mul_comp Q f (fun t => d₀.dist t.1 t.2.2.1)]; exact hd₀
  · rw [← sum_pmf_mul_comp Q f (fun t => d₁.dist t.1 t.2.2.2.1)]; exact hd₁
  · rw [← sum_pmf_mul_comp Q f (fun t => d₂.dist t.1 t.2.2.2.2)]; exact hd₂
  · have : (Q.map f).map (fun t => (t.1, (t.2.1, t.2.2.2.1))) =
        (Q.map (fun t => (t.1, t.2.2.1))).map (Prod.map id (fun y => ((0 : Fin 1), y))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    show r.1 ≥ _
    rw [this]; exact le_trans (mutualInfo_map_right_le _ _) h₁
  · have : (Q.map f).map (fun t => (t.1, (t.2.1, t.2.2.2.2))) =
        (Q.map (fun t => (t.1, t.2.2.2))).map (Prod.map id (fun y => ((0 : Fin 1), y))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    show r.2 ≥ _
    rw [this]; exact le_trans (mutualInfo_map_right_le _ _) h₂
  · have e1 : (Q.map f).map (fun t => (t.1, t.2.1)) = Q.map (fun t => (t.1, (0 : Fin 1))) := by
      rw [map_comp_eq]; rfl
    have e2 : (Q.map f).map (fun t => (t.1, (t.2.2.1, t.2.2.2.1, t.2.2.2.2), t.2.1)) =
        (Q.map (fun t => (t.1, (t.2.1, t.2.2.1, t.2.2.2)))).map
          (fun ab => (ab.1, ab.2, (0 : Fin 1))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    have e3 : (Q.map f).map (fun t => (t.2.2.2.1, t.2.2.2.2, t.2.1)) =
        (Q.map (fun t => (t.2.2.1, t.2.2.2))).map (fun ab => (ab.1, ab.2, (0 : Fin 1))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    show r.1 + r.2 ≥ _
    rw [e1, e2, e3, condMutualInfo_map_const, condMutualInfo_map_const,
      mutualInfo_map_const_snd Q (fun t => t.1) (0 : Fin 1)]
    linarith

/-- **Both sides of `Statement` are nonempty** in the trivial regime: if constant
    reconstructions `cᵢ` meet the distortions, every nonnegative rate pair lies in the
    El Gamal–Cover region (hence in the Zhang–Berger closure) and is operationally achievable. -/
theorem trivial_mem_both (P : ProbDist X) (d₀ : Distortion X Xh₀) (d₁ : Distortion X Xh₁)
    (d₂ : Distortion X Xh₂) {R₁ R₂ D₀ D₁ D₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (c₀ : Xh₀) (c₁ : Xh₁) (c₂ : Xh₂) (h₀ : ∑ x : X, P.pmf x * d₀.dist x c₀ ≤ D₀)
    (h₁ : ∑ x : X, P.pmf x * d₁.dist x c₁ ≤ D₁) (h₂ : ∑ x : X, P.pmf x * d₂.dist x c₂ ≤ D₂) :
    (R₁, R₂) ∈ elGamalCoverMDRegion P d₀ d₁ d₂ D₀ D₁ D₂ ∧
    InZhangBergerClosure P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ ∧
    IsMDAchievable P d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  have hEGC : (R₁, R₂) ∈ elGamalCoverMDRegion P d₀ d₁ d₂ D₀ D₁ D₂ := by
    let g : X → X × Xh₀ × Xh₁ × Xh₂ := fun x => (x, c₀, c₁, c₂)
    refine ⟨hR₁, hR₂, P.map g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
    · rw [← sum_pmf_mul_comp P g (fun t => d₀.dist t.1 t.2.1)]; exact h₀
    · rw [← sum_pmf_mul_comp P g (fun t => d₁.dist t.1 t.2.2.1)]; exact h₁
    · rw [← sum_pmf_mul_comp P g (fun t => d₂.dist t.1 t.2.2.2)]; exact h₂
    · show R₁ ≥ _
      rw [map_comp_eq]; exact le_of_eq_of_le (mutualInfo_map_const_snd P id c₁) hR₁
    · show R₂ ≥ _
      rw [map_comp_eq]; exact le_of_eq_of_le (mutualInfo_map_const_snd P id c₂) hR₂
    · show R₁ + R₂ ≥ _
      rw [map_comp_eq, map_comp_eq]
      have e1 : mutualInfo (P.map ((fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2)) ∘ g)) = 0 :=
        mutualInfo_map_const_snd P id (c₀, c₁, c₂)
      have e2 : mutualInfo (P.map ((fun t => (t.2.2.1, t.2.2.2)) ∘ g)) = 0 :=
        mutualInfo_map_const_snd P (fun _ => c₁) c₂
      linarith
  refine ⟨hEGC, fun ε hε => ⟨1, fun _ => 1, fun _ => R₁, fun _ => R₂, fun _ => D₀, fun _ => D₁,
    fun _ => D₂, fun _ => zero_le_one, by simp,
    fun _ => elGamalCover_subset_zhangBerger P d₀ d₁ d₂ D₀ D₁ D₂ hEGC, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  refine ⟨hR₁, hR₂, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  refine ⟨fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩, fun _ _ => c₀,
    fun _ _ => c₁, fun _ _ => c₂, ?_, ?_, ?_⟩
  · exact le_trans (iid_avg_coord_le P n (fun x => d₀.dist x c₀) (fun _ => d₀.nonneg _ _))
      (by linarith)
  · exact le_trans (iid_avg_coord_le P n (fun x => d₁.dist x c₁) (fun _ => d₁.nonneg _ _))
      (by linarith)
  · exact le_trans (iid_avg_coord_le P n (fun x => d₂.dist x c₂) (fun _ => d₂.nonneg _ _))
      (by linarith)

end MD

end InfoTheory.Known.Certificates.MultipleDescriptionsGeneral
