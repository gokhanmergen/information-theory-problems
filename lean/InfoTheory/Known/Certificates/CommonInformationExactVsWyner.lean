import InfoTheory.Problems.CommonInformationExactVsWyner
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.CommonInformationExactVsWyner`

The frozen statement asks whether every finite-alphabet bipartite source attains its
asymptotic exact common information at a finite blocklength:
`∃ n ≥ 1, exactCommonInfo P = exactCommonInfoSingle (P^{⊗n}) / n`.

## Certified (about exactly these objects)
* `wyner_sandwich` — `I(X; Y) ≤ C_W(X; Y) ≤ G₁(X; Y) ≤ min(H(X), H(Y))`
  (Wyner 1975, Thm. 1; Kumar–Li–El Gamal 2014): components `mutualInfo_le_wynerCommonInfo`,
  `wynerCommonInfo_le_exactCommonInfoSingle`, `wynerCommonInfo_le_entropy_fst/_snd`,
  `exactCommonInfoSingle_le_entropy_fst/_snd`. In particular the defining sets of `C_W` and
  `G₁` are nonempty (witnesses `W = X` and `W = Y` via `Fintype.equivFin`) and bounded below,
  so neither is a junk `sInf ∅ = 0`.
* `wynerCommonInfo_nonneg`, `exactCommonInfoSingle_nonneg`, `exactCommonInfo_nonneg`.
* `exactCommonInfo_le_single_power` — `G(X; Y) ≤ G₁(Xⁿ; Yⁿ)/n` for every `n ≥ 1`, with the
  `n`-letter law literally `bipartitePower P n`: the right-hand side of `Statement` always
  dominates the left, so `Statement` asks exactly whether the infimum is attained.
  `exactCommonInfo_le_entropy` — hence `G ≤ H(X)`.

* **Regression (solved special cases; Wyner 1975, Kumar–Li–El Gamal 2014):**
  - independent components `P = P_X ⊗ P_Y`: `exactCommonInfoSingle_prod`,
    `wynerCommonInfo_prod`, `exactCommonInfo_prod` — `G₁ = C_W = G = 0` (constant `W`), and
    `statement_instance_prod` — `Statement`'s equation holds at `n = 1` for such sources
    (via `bipartitePower_prod : (P_X ⊗ P_Y)^{⊗n} = P_Xⁿ ⊗ P_Yⁿ`);
  - identical components `X = Y` (law `P.map (x ↦ (x, x))`): `wynerCommonInfo_diag`,
    `exactCommonInfoSingle_diag`, `exactCommonInfo_diag` — `C_W = G₁ = G = H(X)` (via
    `I(X; X) = H(X)`, `bipartitePower_diag`, and `H(Pⁿ) = n H(P)`), and
    `statement_instance_diag` — `Statement`'s equation holds at `n = 1`.
  So all three frozen common-information functionals reproduce the textbook values.

## Not certified
* `C_W(X; Y) ≤ G(X; Y)` for the asymptotic `G` (needs tensorization
  `C_W(Xⁿ; Yⁿ) = n C_W(X; Y)`); the strict separations of Yu–Tan (2020) and
  Kumar–Li–El Gamal (2014, SBES): require explicit optimizations over auxiliaries.

## Status
`Solutions/CommonInformationExactVsWyner.lean` proves `¬ Statement` (verified, standard
axioms): on `SBES(3/4)`, `G₁(Xⁿ; Yⁿ)/n > h(3/4) ≥ G(X; Y)` for every `n`, so the infimum is
not attained at any finite `n`. This settles the formal sub-question; the headline question
(a computable single-letter formula for `G`) remains open.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CommonInformationExactVsWyner

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.CommonInformationExactVsWyner

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

/-- Relabeling the conditioning variable injectively leaves `I(X; Y | Z)` unchanged. -/
theorem condMutualInfo_map_cond_injective (R : ProbDist (α × β × γ)) {h : γ → δ}
    (hh : Function.Injective h) :
    condMutualInfo (R.map (fun t => (t.1, t.2.1, h t.2.2))) = condMutualInfo R := by
  have e1 : (R.map (fun t => (t.1, t.2.1, h t.2.2))).map (fun t => (t.1, t.2.2)) =
      (R.map (fun t => (t.1, t.2.2))).map (Prod.map id h) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (R.map (fun t => (t.1, t.2.1, h t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      (R.map (fun t => (t.2.1, t.2.2))).map (Prod.map id h) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (R.map (fun t => (t.1, t.2.1, h t.2.2))).map (fun t => t.2.2) =
      (R.map (fun t => t.2.2)).map h := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have i1 : Function.Injective (Prod.map (id : α → α) h) :=
    Function.Injective.prodMap (fun _ _ e => e) hh
  have i2 : Function.Injective (Prod.map (id : β → β) h) :=
    Function.Injective.prodMap (fun _ _ e => e) hh
  have i0 : Function.Injective (fun t : α × β × γ => (t.1, t.2.1, h t.2.2)) := fun a b hab => by
    simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 (Prod.ext hab.2.1 (hh hab.2.2))
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ i1, shannonEntropy_map_of_injective _ i2,
    shannonEntropy_map_of_injective _ hh, shannonEntropy_map_of_injective _ i0]

end Helpers

section CommonInfo

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The canonical witness `W = e(X)` (with `e : X ≃ Fin |X|`), for which `X - W - Y` holds. -/
noncomputable def copyX (P : ProbDist (X × Y)) : ProbDist (X × Y × Fin (Fintype.card X)) :=
  P.map (fun xy => (xy.1, xy.2, Fintype.equivFin X xy.1))

theorem copyX_marg (P : ProbDist (X × Y)) : (copyX P).map (fun t => (t.1, t.2.1)) = P := by
  rw [copyX, map_comp_eq]; exact map_id_eq P

/-- `X - e(X) - Y` is a Markov chain: `I(X; Y | e(X)) = 0`. -/
theorem copyX_markov (P : ProbDist (X × Y)) : condMutualInfo (copyX P) = 0 := by
  have e := Fintype.equivFin X
  have i0 : Function.Injective (fun xy : X × Y => (xy.1, xy.2, Fintype.equivFin X xy.1)) :=
    fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1
  have i1 : Function.Injective (fun x : X => (x, Fintype.equivFin X x)) :=
    fun a b h => (Prod.mk.inj h).1
  have i2 : Function.Injective (fun xy : X × Y => (xy.2, Fintype.equivFin X xy.1)) :=
    fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext ((Fintype.equivFin X).injective h.2) h.1
  have e1 : (copyX P).map (fun t => (t.1, t.2.2)) = (P.map Prod.fst).map
      (fun x => (x, Fintype.equivFin X x)) := by rw [copyX, map_comp_eq, map_comp_eq]; rfl
  have e2 : (copyX P).map (fun t => (t.2.1, t.2.2)) =
      P.map (fun xy => (xy.2, Fintype.equivFin X xy.1)) := by rw [copyX, map_comp_eq]; rfl
  have e3 : (copyX P).map (fun t => t.2.2) = (P.map Prod.fst).map (Fintype.equivFin X) := by
    rw [copyX, map_comp_eq, map_comp_eq]; rfl
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ i1, shannonEntropy_map_of_injective _ i2,
    shannonEntropy_map_of_injective _ (Fintype.equivFin X).injective, copyX,
    shannonEntropy_map_of_injective _ i0]
  ring

/-- For the witness `W = e(X)`: `I(X, Y; W) = H(X)`. -/
theorem copyX_mutualInfo (P : ProbDist (X × Y)) :
    mutualInfo ((copyX P).map (fun t => ((t.1, t.2.1), t.2.2))) = shannonEntropy P.fst := by
  have i0 : Function.Injective (fun xy : X × Y => (xy, Fintype.equivFin X xy.1)) :=
    fun a b h => (Prod.mk.inj h).1
  have e0 : (copyX P).map (fun t => ((t.1, t.2.1), t.2.2)) =
      P.map (fun xy => (xy, Fintype.equivFin X xy.1)) := by rw [copyX, map_comp_eq]; rfl
  have e1 : (P.map (fun xy => (xy, Fintype.equivFin X xy.1))).fst = P := by
    rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
  have e2 : (P.map (fun xy => (xy, Fintype.equivFin X xy.1))).snd =
      (P.map Prod.fst).map (Fintype.equivFin X) := by
    rw [← map_snd_eq_snd, map_comp_eq, map_comp_eq]; rfl
  unfold mutualInfo
  rw [e0, e1, e2, shannonEntropy_map_of_injective _ (Fintype.equivFin X).injective,
    shannonEntropy_map_of_injective _ i0, map_fst_eq_fst]
  ring

/-- For the witness `W = e(X)`: `H(W) = H(X)`. -/
theorem copyX_entropy (P : ProbDist (X × Y)) :
    shannonEntropy ((copyX P).map (fun t => t.2.2)) = shannonEntropy P.fst := by
  have e3 : (copyX P).map (fun t => t.2.2) = (P.map Prod.fst).map (Fintype.equivFin X) := by
    rw [copyX, map_comp_eq, map_comp_eq]; rfl
  rw [e3, shannonEntropy_map_of_injective _ (Fintype.equivFin X).injective, map_fst_eq_fst]

/-- The Wyner set is bounded below by `0`. -/
theorem wyner_bddBelow (P : ProbDist (X × Y)) :
    BddBelow { r : ℝ | ∃ (kW : ℕ) (Q : ProbDist (X × Y × Fin kW)),
      Q.map (fun t => (t.1, t.2.1)) = P ∧ condMutualInfo Q = 0 ∧
      r = mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2))) } :=
  ⟨0, by rintro r ⟨kW, Q, -, -, rfl⟩; exact mutualInfo_nonneg _⟩

/-- The exact-common-information set is bounded below by `0`. -/
theorem exact_bddBelow (P : ProbDist (X × Y)) :
    BddBelow { r : ℝ | ∃ (kW : ℕ) (Q : ProbDist (X × Y × Fin kW)),
      Q.map (fun t => (t.1, t.2.1)) = P ∧ condMutualInfo Q = 0 ∧
      r = shannonEntropy (Q.map (fun t => t.2.2)) } :=
  ⟨0, by rintro r ⟨kW, Q, -, -, rfl⟩; exact shannonEntropy_nonneg _⟩

/-- **`C_W(X; Y) ≤ H(X)`** (Wyner 1975): the defining set is nonempty, so `C_W` is a genuine
    infimum. -/
theorem wynerCommonInfo_le_entropy_fst (P : ProbDist (X × Y)) :
    wynerCommonInfo P ≤ shannonEntropy P.fst := by
  rw [← copyX_mutualInfo P]
  exact csInf_le (wyner_bddBelow P) ⟨_, copyX P, copyX_marg P, copyX_markov P, rfl⟩

/-- **`G₁(X; Y) ≤ H(X)`**: the one-shot exact common information is a genuine infimum. -/
theorem exactCommonInfoSingle_le_entropy_fst (P : ProbDist (X × Y)) :
    exactCommonInfoSingle P ≤ shannonEntropy P.fst := by
  rw [← copyX_entropy P]
  exact csInf_le (exact_bddBelow P) ⟨_, copyX P, copyX_marg P, copyX_markov P, rfl⟩

theorem wynerCommonInfo_nonneg (P : ProbDist (X × Y)) : 0 ≤ wynerCommonInfo P :=
  le_csInf ⟨_, _, copyX P, copyX_marg P, copyX_markov P, rfl⟩
    (by rintro r ⟨kW, Q, -, -, rfl⟩; exact mutualInfo_nonneg _)

theorem exactCommonInfoSingle_nonneg (P : ProbDist (X × Y)) : 0 ≤ exactCommonInfoSingle P :=
  le_csInf ⟨_, _, copyX P, copyX_marg P, copyX_markov P, rfl⟩
    (by rintro r ⟨kW, Q, -, -, rfl⟩; exact shannonEntropy_nonneg _)

/-- **`I(X; Y) ≤ C_W(X; Y)`** (Wyner 1975, Thm. 1 lower bound): for every `X - W - Y`,
    `I(X; Y) ≤ I(X; YW) = I(X; W) + I(X; Y | W) = I(X; W) ≤ I(XY; W)`. -/
theorem mutualInfo_le_wynerCommonInfo (P : ProbDist (X × Y)) :
    mutualInfo P ≤ wynerCommonInfo P := by
  refine le_csInf ⟨_, _, copyX P, copyX_marg P, copyX_markov P, rfl⟩ ?_
  rintro r ⟨kW, Q, hQ, hM, rfl⟩
  have h1 : mutualInfo (Q.map (fun t => (t.1, t.2.1))) ≤
      mutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2)))) := by
    have : Q.map (fun t => (t.1, t.2.1)) =
        (Q.map (fun t => (t.1, (t.2.1, t.2.2)))).map (Prod.map id Prod.fst) := by
      rw [map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  have hchain := mutualInfo_add_condMutualInfo Q (fun t => t.1) (fun t => t.2.2)
    (fun t => t.2.1)
  have hQid : Q.map (fun t => (t.1, t.2.1, t.2.2)) = Q := map_id_eq Q
  rw [hQid, hM, add_zero] at hchain
  have h2 : mutualInfo (Q.map (fun t => (t.1, t.2.2))) ≤
      mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2))) := by
    have : Q.map (fun t => (t.1, t.2.2)) =
        (Q.map (fun t => ((t.1, t.2.1), t.2.2))).map (Prod.map Prod.fst id) := by
      rw [map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  rw [hQ, hQid] at h1
  linarith

/-- **`C_W(X; Y) ≤ G₁(X; Y)`**: `I(XY; W) ≤ H(W)` for every admissible `W`. -/
theorem wynerCommonInfo_le_exactCommonInfoSingle (P : ProbDist (X × Y)) :
    wynerCommonInfo P ≤ exactCommonInfoSingle P := by
  refine le_csInf ⟨_, _, copyX P, copyX_marg P, copyX_markov P, rfl⟩ ?_
  rintro r ⟨kW, Q, hQ, hM, rfl⟩
  refine csInf_le_of_le (wyner_bddBelow P) ⟨kW, Q, hQ, hM, rfl⟩ ?_
  have := mutualInfo_le_entropy_snd (Q.map (fun t => ((t.1, t.2.1), t.2.2)))
  have e : (Q.map (fun t => ((t.1, t.2.1), t.2.2))).snd = Q.map (fun t => t.2.2) := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  rwa [e] at this

/-- The symmetric witness `W = e(Y)`. -/
noncomputable def copyY (P : ProbDist (X × Y)) : ProbDist (X × Y × Fin (Fintype.card Y)) :=
  P.map (fun xy => (xy.1, xy.2, Fintype.equivFin Y xy.2))

theorem copyY_marg (P : ProbDist (X × Y)) : (copyY P).map (fun t => (t.1, t.2.1)) = P := by
  rw [copyY, map_comp_eq]; exact map_id_eq P

theorem copyY_markov (P : ProbDist (X × Y)) : condMutualInfo (copyY P) = 0 := by
  have i0 : Function.Injective (fun xy : X × Y => (xy.1, xy.2, Fintype.equivFin Y xy.2)) :=
    fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1
  have i1 : Function.Injective (fun xy : X × Y => (xy.1, Fintype.equivFin Y xy.2)) :=
    fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 ((Fintype.equivFin Y).injective h.2)
  have i2 : Function.Injective (fun y : Y => (y, Fintype.equivFin Y y)) :=
    fun a b h => (Prod.mk.inj h).1
  have e1 : (copyY P).map (fun t => (t.1, t.2.2)) =
      P.map (fun xy => (xy.1, Fintype.equivFin Y xy.2)) := by rw [copyY, map_comp_eq]; rfl
  have e2 : (copyY P).map (fun t => (t.2.1, t.2.2)) = (P.map Prod.snd).map
      (fun y => (y, Fintype.equivFin Y y)) := by rw [copyY, map_comp_eq, map_comp_eq]; rfl
  have e3 : (copyY P).map (fun t => t.2.2) = (P.map Prod.snd).map (Fintype.equivFin Y) := by
    rw [copyY, map_comp_eq, map_comp_eq]; rfl
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ i1, shannonEntropy_map_of_injective _ i2,
    shannonEntropy_map_of_injective _ (Fintype.equivFin Y).injective, copyY,
    shannonEntropy_map_of_injective _ i0]
  ring

theorem copyY_mutualInfo (P : ProbDist (X × Y)) :
    mutualInfo ((copyY P).map (fun t => ((t.1, t.2.1), t.2.2))) = shannonEntropy P.snd := by
  have i0 : Function.Injective (fun xy : X × Y => (xy, Fintype.equivFin Y xy.2)) :=
    fun a b h => (Prod.mk.inj h).1
  have e0 : (copyY P).map (fun t => ((t.1, t.2.1), t.2.2)) =
      P.map (fun xy => (xy, Fintype.equivFin Y xy.2)) := by rw [copyY, map_comp_eq]; rfl
  have e1 : (P.map (fun xy => (xy, Fintype.equivFin Y xy.2))).fst = P := by
    rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
  have e2 : (P.map (fun xy => (xy, Fintype.equivFin Y xy.2))).snd =
      (P.map Prod.snd).map (Fintype.equivFin Y) := by
    rw [← map_snd_eq_snd, map_comp_eq, map_comp_eq]; rfl
  unfold mutualInfo
  rw [e0, e1, e2, shannonEntropy_map_of_injective _ (Fintype.equivFin Y).injective,
    shannonEntropy_map_of_injective _ i0, map_snd_eq_snd]
  ring

theorem copyY_entropy (P : ProbDist (X × Y)) :
    shannonEntropy ((copyY P).map (fun t => t.2.2)) = shannonEntropy P.snd := by
  have e3 : (copyY P).map (fun t => t.2.2) = (P.map Prod.snd).map (Fintype.equivFin Y) := by
    rw [copyY, map_comp_eq, map_comp_eq]; rfl
  rw [e3, shannonEntropy_map_of_injective _ (Fintype.equivFin Y).injective, map_snd_eq_snd]

/-- **`C_W(X; Y) ≤ H(Y)`**. -/
theorem wynerCommonInfo_le_entropy_snd (P : ProbDist (X × Y)) :
    wynerCommonInfo P ≤ shannonEntropy P.snd := by
  rw [← copyY_mutualInfo P]
  exact csInf_le (wyner_bddBelow P) ⟨_, copyY P, copyY_marg P, copyY_markov P, rfl⟩

/-- **`G₁(X; Y) ≤ H(Y)`**. -/
theorem exactCommonInfoSingle_le_entropy_snd (P : ProbDist (X × Y)) :
    exactCommonInfoSingle P ≤ shannonEntropy P.snd := by
  rw [← copyY_entropy P]
  exact csInf_le (exact_bddBelow P) ⟨_, copyY P, copyY_marg P, copyY_markov P, rfl⟩

/-- **Wyner's sandwich** `I(X; Y) ≤ C_W(X; Y) ≤ G₁(X; Y) ≤ min(H(X), H(Y))`
    (Wyner 1975; Kumar–Li–El Gamal 2014, Prop. 1). -/
theorem wyner_sandwich (P : ProbDist (X × Y)) :
    mutualInfo P ≤ wynerCommonInfo P ∧ wynerCommonInfo P ≤ exactCommonInfoSingle P ∧
      exactCommonInfoSingle P ≤ min (shannonEntropy P.fst) (shannonEntropy P.snd) :=
  ⟨mutualInfo_le_wynerCommonInfo P, wynerCommonInfo_le_exactCommonInfoSingle P,
    le_min (exactCommonInfoSingle_le_entropy_fst P) (exactCommonInfoSingle_le_entropy_snd P)⟩

/-- The asymptotic exact common information is bounded below by `0` (so it is a genuine
    infimum) and **`G(X; Y) ≤ G₁(Xⁿ; Yⁿ)/n` for every `n ≥ 1`**: the right-hand side of
    `Statement` always dominates the left-hand side, so `Statement` asks exactly whether the
    infimum defining `exactCommonInfo` is attained. -/
theorem exactCommonInfo_le_single_power (P : ProbDist (X × Y)) {n : ℕ} (hn : 0 < n) :
    exactCommonInfo P ≤ exactCommonInfoSingle (bipartitePower P n) / (n : ℝ) := by
  refine csInf_le ⟨0, ?_⟩ ⟨n, hn, ?_⟩
  · rintro r ⟨m, hm, hr⟩
    rw [hr]; exact div_nonneg (exactCommonInfoSingle_nonneg _) (Nat.cast_nonneg _)
  · dsimp only
    congr 2

theorem exactCommonInfo_nonneg (P : ProbDist (X × Y)) : 0 ≤ exactCommonInfo P := by
  refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
  rintro r ⟨m, hm, hr⟩
  rw [hr]; exact div_nonneg (exactCommonInfoSingle_nonneg _) (Nat.cast_nonneg _)

/-- Consequently, for `n = 1`: `G(X; Y) ≤ G₁(X¹; Y¹) ≤ H(X)`. -/
theorem exactCommonInfo_le_entropy (P : ProbDist (X × Y)) :
    exactCommonInfo P ≤ shannonEntropy (bipartitePower P 1).fst := by
  have := exactCommonInfo_le_single_power P one_pos
  rw [Nat.cast_one, div_one] at this
  exact le_trans this (exactCommonInfoSingle_le_entropy_fst _)

/-! ### Regression: independent and identical components -/

/-- `I(X; Y | W) = I(X; Y)` when `W` is constant. -/
theorem condMutualInfo_map_const_cond {ι α β γ : Type*} [Fintype ι] [Fintype α] [Fintype β]
    [Fintype γ] (R : ProbDist ι) (f : ι → α) (g : ι → β) (c : γ) :
    condMutualInfo (R.map (fun i => (f i, g i, c))) = mutualInfo (R.map (fun i => (f i, g i))) := by
  have e0 : R.map (fun i => (f i, g i, c)) =
      (R.map (fun i => (f i, g i))).map (fun p => (p.1, p.2, c)) := by rw [map_comp_eq]; rfl
  have e1 : (R.map (fun i => (f i, g i, c))).map (fun t => (t.1, t.2.2)) =
      (R.map f).map (fun x => (x, c)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (R.map (fun i => (f i, g i, c))).map (fun t => (t.2.1, t.2.2)) =
      (R.map g).map (fun y => (y, c)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (R.map (fun i => (f i, g i, c))).map (fun t => t.2.2) = R.map (fun _ => c) := by
    rw [map_comp_eq]; rfl
  have a1 : (R.map (fun i => (f i, g i))).fst = R.map f := by
    rw [← map_fst_eq_fst, map_comp_eq]; rfl
  have a2 : (R.map (fun i => (f i, g i))).snd = R.map g := by
    rw [← map_snd_eq_snd, map_comp_eq]; rfl
  have i0 : Function.Injective (fun p : α × β => (p.1, p.2, c)) := fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1
  have i1 : Function.Injective (fun x : α => (x, c)) := fun a b h => (Prod.mk.inj h).1
  have i2 : Function.Injective (fun y : β => (y, c)) := fun a b h => (Prod.mk.inj h).1
  unfold condMutualInfo mutualInfo; dsimp only
  rw [e1, e2, e3, e0, a1, a2, shannonEntropy_map_of_injective _ i0,
    shannonEntropy_map_of_injective _ i1, shannonEntropy_map_of_injective _ i2,
    shannonEntropy_map_const]
  ring

/-- **Independent components: `G₁(X; Y) = 0`** (constant `W` already makes `X ⊥ Y`). -/
theorem exactCommonInfoSingle_prod (A : ProbDist X) (B : ProbDist Y) :
    exactCommonInfoSingle (A.prod B) = 0 := by
  refine le_antisymm ?_ (exactCommonInfoSingle_nonneg _)
  have hmarg : ((A.prod B).map (fun xy => (xy.1, xy.2, (0 : Fin 1)))).map
      (fun t => (t.1, t.2.1)) = A.prod B := by
    rw [map_comp_eq]; exact map_id_eq _
  have hM : condMutualInfo ((A.prod B).map (fun xy => (xy.1, xy.2, (0 : Fin 1)))) = 0 := by
    rw [condMutualInfo_map_const_cond (A.prod B) Prod.fst Prod.snd (0 : Fin 1)]
    exact (congrArg mutualInfo (map_id_eq (A.prod B))).trans (mutualInfo_prod A B)
  have hH : shannonEntropy (((A.prod B).map (fun xy => (xy.1, xy.2, (0 : Fin 1)))).map
      (fun t => t.2.2)) = 0 := by
    rw [map_comp_eq]; exact shannonEntropy_map_const _ _
  exact csInf_le (exact_bddBelow _) ⟨1, _, hmarg, hM, hH.symm⟩

/-- **Independent components: `C_W(X; Y) = 0`** (Wyner 1975). -/
theorem wynerCommonInfo_prod (A : ProbDist X) (B : ProbDist Y) :
    wynerCommonInfo (A.prod B) = 0 :=
  le_antisymm ((wynerCommonInfo_le_exactCommonInfoSingle _).trans_eq (exactCommonInfoSingle_prod A B))
    (wynerCommonInfo_nonneg _)

/-- The `n`-letter power of an independent source is independent: `(P_X ⊗ P_Y)^{⊗n} = P_Xⁿ ⊗ P_Yⁿ`. -/
theorem bipartitePower_prod (A : ProbDist X) (B : ProbDist Y) (n : ℕ) :
    bipartitePower (A.prod B) n = (iidDist A n).prod (iidDist B n) :=
  probDist_eq_of_pmf fun xy => by
    simp only [bipartitePower, ProbDist.prod, iidDist, Finset.prod_mul_distrib]

/-- **Independent components: `G(X; Y) = 0`**. -/
theorem exactCommonInfo_prod (A : ProbDist X) (B : ProbDist Y) :
    exactCommonInfo (A.prod B) = 0 := by
  refine le_antisymm ?_ (exactCommonInfo_nonneg _)
  have h := exactCommonInfo_le_single_power (A.prod B) one_pos
  rwa [bipartitePower_prod, exactCommonInfoSingle_prod, zero_div] at h

/-- **`Statement` is consistent on independent sources**: its equation holds at `n = 1`. -/
theorem statement_instance_prod (A : ProbDist X) (B : ProbDist Y) :
    ∃ n : ℕ, 0 < n ∧ exactCommonInfo (A.prod B) =
      exactCommonInfoSingle (bipartitePower (A.prod B) n) / (n : ℝ) :=
  ⟨1, one_pos, by rw [exactCommonInfo_prod, bipartitePower_prod, exactCommonInfoSingle_prod,
    zero_div]⟩

/-- `I(X; X) = H(X)`. -/
theorem mutualInfo_diag (P : ProbDist X) :
    mutualInfo (P.map (fun x => (x, x))) = shannonEntropy P := by
  have a1 : (P.map (fun x => (x, x))).fst = P := by
    rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
  have a2 : (P.map (fun x => (x, x))).snd = P := by
    rw [← map_snd_eq_snd, map_comp_eq]; exact map_id_eq P
  have i : Function.Injective (fun x : X => (x, x)) := fun a b h => (Prod.mk.inj h).1
  unfold mutualInfo
  rw [a1, a2, shannonEntropy_map_of_injective _ i]; ring

/-- **Identical components: `C_W(X; X) = H(X)`** (Wyner 1975). -/
theorem wynerCommonInfo_diag (P : ProbDist X) :
    wynerCommonInfo (P.map (fun x => (x, x))) = shannonEntropy P := by
  have h := wyner_sandwich (P.map (fun x => (x, x)))
  have a1 : (P.map (fun x => (x, x))).fst = P := by
    rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
  rw [mutualInfo_diag, a1] at h
  exact le_antisymm (h.2.1.trans (h.2.2.trans (min_le_left _ _))) h.1

/-- **Identical components: `G₁(X; X) = H(X)`** (Kumar–Li–El Gamal 2014). -/
theorem exactCommonInfoSingle_diag (P : ProbDist X) :
    exactCommonInfoSingle (P.map (fun x => (x, x))) = shannonEntropy P := by
  have h := wyner_sandwich (P.map (fun x => (x, x)))
  have a1 : (P.map (fun x => (x, x))).fst = P := by
    rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
  rw [mutualInfo_diag, a1] at h
  exact le_antisymm (h.2.2.trans (min_le_left _ _)) (h.1.trans h.2.1)

theorem map_pmf_of_injective {α β : Type*} [Fintype α] [Fintype β] (P : ProbDist α) {f : α → β} (hf : Function.Injective f) (a : α) :
    (P.map f).pmf (f a) = P.pmf a := by
  classical
  simp only [ProbDist.map]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; simp [hf.ne hne]
  · simp

theorem map_diag_pmf_of_ne {α : Type*} [Fintype α] (P : ProbDist α) {a b : α} (h : a ≠ b) :
    (P.map (fun x => (x, x))).pmf (a, b) = 0 := by
  classical
  simp only [ProbDist.map]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with hx
  · simp only [Prod.mk.injEq] at hx
    exact absurd (hx.1.symm.trans hx.2) h
  · rfl

/-- The `n`-letter power of `X = Y` is `Xⁿ = Yⁿ`. -/
theorem bipartitePower_diag (P : ProbDist X) (n : ℕ) :
    bipartitePower (P.map (fun x => (x, x))) n = (iidDist P n).map (fun x => (x, x)) := by
  have hi : Function.Injective (fun x : Fin n → X => (x, x)) := fun a b h => (Prod.mk.inj h).1
  have hi1 : Function.Injective (fun x : X => (x, x)) := fun a b h => (Prod.mk.inj h).1
  refine probDist_eq_of_pmf fun ab => ?_
  obtain ⟨a, b⟩ := ab
  by_cases hab : a = b
  · subst hab
    have h1 : ((iidDist P n).map (fun x => (x, x))).pmf (a, a) = (iidDist P n).pmf a :=
      map_pmf_of_injective (iidDist P n) hi a
    have h2 : ∀ i, (P.map (fun x => (x, x))).pmf (a i, a i) = P.pmf (a i) :=
      fun i => map_pmf_of_injective P hi1 (a i)
    rw [h1]
    simp only [bipartitePower, iidDist, h2]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := not_forall.mp fun h => hab (funext h)
    have h0 : (bipartitePower (P.map (fun x => (x, x))) n).pmf (a, b) = 0 := by
      simp only [bipartitePower]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (map_diag_pmf_of_ne P hi)
    rw [h0, map_diag_pmf_of_ne _ hab]

/-- `H(Pⁿ) = n H(P)`. -/
theorem shannonEntropy_iidDist (P : ProbDist X) (n : ℕ) :
    shannonEntropy (iidDist P n) = n * shannonEntropy P := by
  have e : iidDist P n = piProdDist (fun _ : Fin n => P) := rfl
  rw [e, shannonEntropy_piProdDist]
  simp

/-- `G₁(Xⁿ; Xⁿ) / n = H(X)` for every `n ≥ 1`. -/
theorem exactCommonInfoSingle_power_diag (P : ProbDist X) {n : ℕ} (hn : 0 < n) :
    exactCommonInfoSingle (bipartitePower (P.map (fun x => (x, x))) n) / (n : ℝ) =
      shannonEntropy P := by
  rw [bipartitePower_diag, exactCommonInfoSingle_diag, shannonEntropy_iidDist]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- **Identical components: `G(X; X) = H(X)`** (Kumar–Li–El Gamal 2014). -/
theorem exactCommonInfo_diag (P : ProbDist X) :
    exactCommonInfo (P.map (fun x => (x, x))) = shannonEntropy P := by
  refine le_antisymm ?_ ?_
  · have h := exactCommonInfo_le_single_power (P.map (fun x => (x, x))) one_pos
    rwa [exactCommonInfoSingle_power_diag P one_pos] at h
  · refine le_csInf ⟨_, 1, one_pos, rfl⟩ ?_
    rintro r ⟨m, hm, hr⟩
    have hr' : r = exactCommonInfoSingle (bipartitePower (P.map (fun x => (x, x))) m) / (m : ℝ) :=
      hr
    rw [hr', exactCommonInfoSingle_power_diag P hm]

/-- **`Statement` is consistent on `X = Y`**: its equation holds at `n = 1`. -/
theorem statement_instance_diag (P : ProbDist X) :
    ∃ n : ℕ, 0 < n ∧ exactCommonInfo (P.map (fun x => (x, x))) =
      exactCommonInfoSingle (bipartitePower (P.map (fun x => (x, x))) n) / (n : ℝ) :=
  ⟨1, one_pos, by rw [exactCommonInfo_diag, exactCommonInfoSingle_power_diag P one_pos]⟩

end CommonInfo

end InfoTheory.Known.Certificates.CommonInformationExactVsWyner
