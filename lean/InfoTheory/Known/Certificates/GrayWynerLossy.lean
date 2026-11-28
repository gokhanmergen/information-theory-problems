import InfoTheory.Problems.GrayWynerLossy
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.GrayWynerLossy`

The frozen statement asks whether, for all finite-alphabet sources with decoder side
information `(Z₁, Z₂)`, operational achievability `IsLossyGWSIAchievable` coincides with the
time-sharing closure of the single-letter split-binning Heegard–Berger / Gray–Wyner inner bound
(`R₀ + R₁ ≥ a₁ + b₁`, `R₀ + R₂ ≥ a₂ + b₂`, `R₀ + R₁ + R₂ ≥ max(a₁, a₂) + b₁ + b₂`, with
`aⱼ = I(X; U₀ | Zⱼ)`, `bⱼ = I(X; Uⱼ | U₀, Zⱼ)`), as corrected by the 2026-11-27 statement-fix.

## Certified (about exactly these objects)
* Generic machinery: `rd_map_le_of_codes`, `rd_le_of_timeSharing`, the chain rule
  `mutualInfo_add_condMutualInfo`, injective relabelings `condMutualInfo_map_cond_injective`,
  `condMutualInfo_map_mid_injective`, and `condMutualInfo_map_fn_cond` (`I(f(Z); Y | Z) = 0`).
* `isLossyGWSIAchievable_rd₁_le`, `isLossyGWSIAchievable_rd₂_le` — when decoder `i` has no side
  information (`Zᵢ` a singleton, e.g. `Fin 1`, which `Statement` includes), every achievable
  tuple satisfies the Gray–Wyner (1974) cut-set bound `R_{Xᵢ}(Dᵢ) ≤ R₀ + Rᵢ`.
* `lossyGWSIInner_rd₁_le`, `lossyGWSIInner_rd₂_le`, `inLossyGWSIClosure_rd₁_le`,
  `inLossyGWSIClosure_rd₂_le` — the inner bound and its closure satisfy the same bounds
  (`r₀ + rᵢ ≥ I(X; U₀) + I(X; Uᵢ | U₀) = I(X; UᵢU₀) ≥ R_{Xᵢ}(Dᵢ)`): inner ⊆ outer in the
  side-information-free case solved by Gray–Wyner.
* `trivial_mem_both` — both sides are nonempty: if constant reconstructions meet the
  distortions, every nonnegative rate triple is in the inner bound, its closure, and is
  operationally achievable.
* `lossless_mem_lossyGWSIInner` — Slepian–Wolf split-binning regression: with `U₀ = (X₁, X₂)`,
  every nonnegative triple with `R₀ + Rⱼ ≥ H(X₁, X₂ | Zⱼ)` is a single-letter point at
  `(D₁, D₂) = (0, 0)` (distortions vanishing on the diagonal).
* `bec_point_mem` — **statement-fix regression**: for `X₁ = X₂ ~ Bern(1/2)`, `Z₁ = BEC(e)(X)`,
  `Z₂` constant, Hamming distortions (`becP`, `hamming2`), the tuple `(e, 0, 1 - e, 0, 0)` —
  which refuted the pre-fix statement for `0 < e < 1` — lies in the corrected inner bound and
  its closure, via `becP_condEntropy_Z₁` (`H(X | Z₁) = e`) and `becP_condEntropy_Z₂`
  (`H(X | Z₂) = 1`).

## Not certified
* Operational achievability of the corrected inner bound (split binning + superposition
  covering + Wyner–Ziv decoding); in particular achievability of the BEC tuple (Slepian–Wolf).
* The exact Gray–Wyner region (`R₀ ≥ I(X;U₀)`, `Rᵢ ≥ R_{Xᵢ|U₀}(Dᵢ)`) and the lossless
  Gray–Wyner region, to which the corrected region reduces when `Z₁, Z₂` are trivial:
  conditional rate–distortion is not defined in `Core`, and achievability needs superposition
  covering (lossy), not in `Bridge`.
* Anything with genuinely non-trivial lossy side information (Heegard–Berger, Timo–Grant–
  Chan–Kramer 2008, Benammar–Zaidi 2018): needs Wyner–Ziv coding.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.GrayWynerLossy

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.GrayWynerLossy

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

/-- Relabeling the middle variable injectively leaves `I(X; Y | Z)` unchanged. -/
theorem condMutualInfo_map_mid_injective (R : ProbDist (α × β × γ)) {h : β → δ}
    (hh : Function.Injective h) :
    condMutualInfo (R.map (fun t => (t.1, h t.2.1, t.2.2))) = condMutualInfo R := by
  have e1 : (R.map (fun t => (t.1, h t.2.1, t.2.2))).map (fun t => (t.1, t.2.2)) =
      R.map (fun t => (t.1, t.2.2)) := by
    rw [map_comp_eq]; rfl
  have e2 : (R.map (fun t => (t.1, h t.2.1, t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      (R.map (fun t => (t.2.1, t.2.2))).map (Prod.map h id) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e3 : (R.map (fun t => (t.1, h t.2.1, t.2.2))).map (fun t => t.2.2) =
      R.map (fun t => t.2.2) := by
    rw [map_comp_eq]; rfl
  have i2 : Function.Injective (Prod.map h (id : γ → γ)) :=
    Function.Injective.prodMap hh (fun _ _ e => e)
  have i0 : Function.Injective (fun t : α × β × γ => (t.1, h t.2.1, t.2.2)) := fun a b hab => by
    simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 (Prod.ext (hh hab.2.1) hab.2.2)
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ i2, shannonEntropy_map_of_injective _ i0]

/-- `I(f(Z); Y | Z) = 0`: a function of the conditioning variable carries no information. -/
theorem condMutualInfo_map_fn_cond (R : ProbDist (β × γ)) (f : γ → α) :
    condMutualInfo (R.map (fun t => (f t.2, t.1, t.2))) = 0 := by
  have e1 : (R.map (fun t => (f t.2, t.1, t.2))).map (fun t => (t.1, t.2.2)) =
      (R.map (fun t => t.2)).map (fun z => (f z, z)) := by
    rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (R.map (fun t => (f t.2, t.1, t.2))).map (fun t => (t.2.1, t.2.2)) = R := by
    rw [map_comp_eq]; exact map_id_eq R
  have e3 : (R.map (fun t => (f t.2, t.1, t.2))).map (fun t => t.2.2) = R.map (fun t => t.2) := by
    rw [map_comp_eq]; rfl
  have i1 : Function.Injective (fun z : γ => (f z, z)) := fun a b h => (Prod.mk.inj h).2
  have i0 : Function.Injective (fun t : β × γ => (f t.2, t.1, t.2)) := fun a b hab => by
    simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.2.1 hab.2.2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ i1, shannonEntropy_map_of_injective _ i0]
  ring

end Helpers

section GW

variable {X₁ X₂ Z₁ Z₂ Xh₁ Xh₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Z₁] [Fintype Z₂]
  [Fintype Xh₁] [Fintype Xh₂]

/-! ### Operational cut-set bounds without side information at a decoder -/

/-- **Cut-set bound at decoder 1 (no side information there, `Z₁` a singleton)**: every
    achievable tuple has `R_{X₁}(D₁) ≤ R₀ + R₁` (Gray–Wyner 1974, Thm. 4). -/
theorem isLossyGWSIAchievable_rd₁_le [Unique Z₁] (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂) {R₀ R₁ R₂ D₁ D₂ : ℝ}
    (h : IsLossyGWSIAchievable P d₁ d₂ R₀ R₁ R₂ D₁ D₂) :
    rateDistortion P.fst d₁ D₁ ≤ R₀ + R₁ := by
  obtain ⟨hR₀, hR₁, hR₂, hach⟩ := h
  rw [← map_fst_eq_fst]
  refine rd_map_le_of_codes P Prod.fst d₁ (by linarith) fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min (η / 2) δ) (lt_min (by linarith) hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₀, enc₁, enc₂, dec₁, dec₂, hD₁, -⟩ := hN n hn
  refine ⟨_, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity)),
    card_mul_le hR₀ hR₁ (lt_min (by linarith) hδ) (by linarith [min_le_left (η / 2) δ]),
    fun w => finProdFinEquiv (enc₀ (fun j => ((w j).1, (w j).2.1)),
      enc₁ (fun j => ((w j).1, (w j).2.1))),
    fun k => dec₁ ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2, fun _ => default), ?_⟩
  simp only [Equiv.symm_apply_apply]
  have hz : ∀ w : Fin n → X₁ × X₂ × Z₁ × Z₂, (fun j => (w j).2.2.1) = fun _ => (default : Z₁) :=
    fun w => funext fun _ => Subsingleton.elim _ _
  simp only [hz] at hD₁
  exact le_trans hD₁ (by linarith [min_le_right (η / 2) δ])

/-- **Cut-set bound at decoder 2** (`Z₂` a singleton): `R_{X₂}(D₂) ≤ R₀ + R₂`. -/
theorem isLossyGWSIAchievable_rd₂_le [Unique Z₂] (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂) {R₀ R₁ R₂ D₁ D₂ : ℝ}
    (h : IsLossyGWSIAchievable P d₁ d₂ R₀ R₁ R₂ D₁ D₂) :
    rateDistortion (P.map (fun w => w.2.1)) d₂ D₂ ≤ R₀ + R₂ := by
  obtain ⟨hR₀, hR₁, hR₂, hach⟩ := h
  refine rd_map_le_of_codes P (fun w => w.2.1) d₂ (by linarith) fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min (η / 2) δ) (lt_min (by linarith) hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₀, enc₁, enc₂, dec₁, dec₂, -, hD₂⟩ := hN n hn
  refine ⟨_, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity)),
    card_mul_le hR₀ hR₂ (lt_min (by linarith) hδ) (by linarith [min_le_left (η / 2) δ]),
    fun w => finProdFinEquiv (enc₀ (fun j => ((w j).1, (w j).2.1)),
      enc₂ (fun j => ((w j).1, (w j).2.1))),
    fun k => dec₂ ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2, fun _ => default), ?_⟩
  simp only [Equiv.symm_apply_apply]
  have hz : ∀ w : Fin n → X₁ × X₂ × Z₁ × Z₂, (fun j => (w j).2.2.2) = fun _ => (default : Z₂) :=
    fun w => funext fun _ => Subsingleton.elim _ _
  simp only [hz] at hD₂
  exact le_trans hD₂ (by linarith [min_le_right (η / 2) δ])

/-! ### The inner bound obeys the same cut-set bounds -/

/-- On the single-letter inner bound with a singleton `Z₁`:
    `r₀ + r₁ ≥ I(X; U₀) + I(X; U₁ | U₀) = I(X; U₁U₀) ≥ I(X₁; X̂₁) ≥ R_{X₁}(D₁)`. -/
theorem lossyGWSIInner_rd₁_le [Unique Z₁] (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂) {D₁ D₂ : ℝ} {r : ℝ × ℝ × ℝ}
    (hr : r ∈ lossyGWSIInner P d₁ d₂ D₁ D₂) :
    RDFeasible P.fst d₁ D₁ ∧ rateDistortion P.fst d₁ D₁ ≤ r.1 + r.2.1 := by
  obtain ⟨-, -, -, k₀, k₁, k₂, Q, g₁, g₂, hQP, -, hd₁, -, hAB, -, -, -⟩ := hr
  set XX : X₁ × X₂ × Z₁ × Z₂ × Fin k₀ × Fin k₁ × Fin k₂ → X₁ × X₂ := fun t => (t.1, t.2.1)
    with hXX
  have eA : Q.map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.1)) =
      (Q.map (fun t => (XX t, t.2.2.2.2.1))).map (fun ab => (ab.1, ab.2, (default : Z₁))) := by
    rw [map_comp_eq]; congr 1; funext t
    exact Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))
  have eB : Q.map (fun t => ((t.1, t.2.1), t.2.2.2.2.2.1, (t.2.2.2.2.1, t.2.2.1))) =
      (Q.map (fun t => (XX t, t.2.2.2.2.2.1, t.2.2.2.2.1))).map
        (fun s => (s.1, s.2.1, (fun u => (u, (default : Z₁))) s.2.2)) := by
    rw [map_comp_eq]; congr 1; funext t
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _)))
  have hinj : Function.Injective (fun u : Fin k₀ => (u, (default : Z₁))) :=
    fun a b h => (Prod.mk.inj h).1
  rw [eA, condMutualInfo_map_const, eB, condMutualInfo_map_cond_injective _ hinj] at hAB
  have hchain := mutualInfo_add_condMutualInfo Q XX (fun t => t.2.2.2.2.1)
    (fun t => t.2.2.2.2.2.1)
  set Q'' := Q.map (fun t => (t.1, g₁ (t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.1))) with hQ''
  have hf : Q''.fst = P.fst := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQP, ← map_fst_eq_fst, map_comp_eq]; rfl
  have hdist : expectedDist Q'' d₁ ≤ D₁ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.1, g₁ (t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.1)))
      (fun xy : X₁ × Xh₁ => d₁.dist xy.1 xy.2)]; exact hd₁
  have hmi : mutualInfo Q'' ≤ mutualInfo (Q.map (fun t => (XX t, (t.2.2.2.2.2.1, t.2.2.2.2.1)))) := by
    have : Q'' = (Q.map (fun t => (XX t, (t.2.2.2.2.2.1, t.2.2.2.2.1)))).map
        (Prod.map Prod.fst (fun vu => g₁ (vu.2, vu.1, (default : Z₁)))) := by
      rw [hQ'', map_comp_eq]; congr 1; funext t
      exact Prod.ext rfl (congrArg g₁ (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))))
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  refine ⟨⟨Q'', hf, hdist⟩, ?_⟩
  have := rateDistortion_le_mutualInfo hf hdist
  simp only [hXX] at hchain hmi hAB
  linarith

/-- Same at decoder 2 with a singleton `Z₂`: `R_{X₂}(D₂) ≤ r₀ + r₂`. -/
theorem lossyGWSIInner_rd₂_le [Unique Z₂] (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂) {D₁ D₂ : ℝ} {r : ℝ × ℝ × ℝ}
    (hr : r ∈ lossyGWSIInner P d₁ d₂ D₁ D₂) :
    RDFeasible (P.map (fun w => w.2.1)) d₂ D₂ ∧
      rateDistortion (P.map (fun w => w.2.1)) d₂ D₂ ≤ r.1 + r.2.2 := by
  obtain ⟨-, -, -, k₀, k₁, k₂, Q, g₁, g₂, hQP, -, -, hd₂, -, hAB, -, -⟩ := hr
  set XX : X₁ × X₂ × Z₁ × Z₂ × Fin k₀ × Fin k₁ × Fin k₂ → X₁ × X₂ := fun t => (t.1, t.2.1)
    with hXX
  have eA : Q.map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.2.1)) =
      (Q.map (fun t => (XX t, t.2.2.2.2.1))).map (fun ab => (ab.1, ab.2, (default : Z₂))) := by
    rw [map_comp_eq]; congr 1; funext t
    exact Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))
  have eB : Q.map (fun t => ((t.1, t.2.1), t.2.2.2.2.2.2, (t.2.2.2.2.1, t.2.2.2.1))) =
      (Q.map (fun t => (XX t, t.2.2.2.2.2.2, t.2.2.2.2.1))).map
        (fun s => (s.1, s.2.1, (fun u => (u, (default : Z₂))) s.2.2)) := by
    rw [map_comp_eq]; congr 1; funext t
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _)))
  have hinj : Function.Injective (fun u : Fin k₀ => (u, (default : Z₂))) :=
    fun a b h => (Prod.mk.inj h).1
  rw [eA, condMutualInfo_map_const, eB, condMutualInfo_map_cond_injective _ hinj] at hAB
  have hchain := mutualInfo_add_condMutualInfo Q XX (fun t => t.2.2.2.2.1)
    (fun t => t.2.2.2.2.2.2)
  set Q'' := Q.map (fun t => (t.2.1, g₂ (t.2.2.2.2.1, t.2.2.2.2.2.2, t.2.2.2.1))) with hQ''
  have hf : Q''.fst = P.map (fun w => w.2.1) := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQP, map_comp_eq]; rfl
  have hdist : expectedDist Q'' d₂ ≤ D₂ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.2.1, g₂ (t.2.2.2.2.1, t.2.2.2.2.2.2, t.2.2.2.1)))
      (fun xy : X₂ × Xh₂ => d₂.dist xy.1 xy.2)]; exact hd₂
  have hmi : mutualInfo Q'' ≤ mutualInfo (Q.map (fun t => (XX t, (t.2.2.2.2.2.2, t.2.2.2.2.1)))) := by
    have : Q'' = (Q.map (fun t => (XX t, (t.2.2.2.2.2.2, t.2.2.2.2.1)))).map
        (Prod.map Prod.snd (fun vu => g₂ (vu.2, vu.1, (default : Z₂)))) := by
      rw [hQ'', map_comp_eq]; congr 1; funext t
      exact Prod.ext rfl (congrArg g₂ (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))))
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  refine ⟨⟨Q'', hf, hdist⟩, ?_⟩
  have := rateDistortion_le_mutualInfo hf hdist
  simp only [hXX] at hchain hmi hAB
  linarith

/-- **The time-sharing closure obeys the cut-set bounds** (singleton side information):
    `R_{X₁}(D₁) ≤ R₀ + R₁`. -/
theorem inLossyGWSIClosure_rd₁_le [Unique Z₁] (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂) {R₀ R₁ R₂ D₁ D₂ : ℝ}
    (h : InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ D₁ D₂) :
    rateDistortion P.fst d₁ D₁ ≤ R₀ + R₁ := by
  refine rd_le_of_timeSharing fun ε hε => ?_
  obtain ⟨m, w, r₀, r₁, r₂, δ₁, δ₂, hw0, hw1, hin, hr₀, hr₁, -, hδ₁, -⟩ := h (ε / 2) (half_pos hε)
  refine ⟨m, w, fun i => r₀ i + r₁ i, δ₁, hw0, hw1,
    fun i => (lossyGWSIInner_rd₁_le P d₁ d₂ (hin i)).1,
    fun i => (lossyGWSIInner_rd₁_le P d₁ d₂ (hin i)).2, by linarith, ?_⟩
  simp only [mul_add, Finset.sum_add_distrib]; linarith

/-- `R_{X₂}(D₂) ≤ R₀ + R₂` on the closure (singleton `Z₂`). -/
theorem inLossyGWSIClosure_rd₂_le [Unique Z₂] (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂) {R₀ R₁ R₂ D₁ D₂ : ℝ}
    (h : InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ D₁ D₂) :
    rateDistortion (P.map (fun w => w.2.1)) d₂ D₂ ≤ R₀ + R₂ := by
  refine rd_le_of_timeSharing fun ε hε => ?_
  obtain ⟨m, w, r₀, r₁, r₂, δ₁, δ₂, hw0, hw1, hin, hr₀, -, hr₂, -, hδ₂⟩ := h (ε / 2) (half_pos hε)
  refine ⟨m, w, fun i => r₀ i + r₂ i, δ₂, hw0, hw1,
    fun i => (lossyGWSIInner_rd₂_le P d₁ d₂ (hin i)).1,
    fun i => (lossyGWSIInner_rd₂_le P d₁ d₂ (hin i)).2, by linarith, ?_⟩
  simp only [mul_add, Finset.sum_add_distrib]; linarith

/-! ### Nonemptiness of both sides of `Statement` -/

/-- **Trivial regime**: if constant reconstructions `c₁, c₂` meet the distortions, every
    nonnegative rate triple is in the inner bound (constant auxiliaries), in its closure, and
    operationally achievable. -/
theorem trivial_mem_both (P : ProbDist (X₁ × X₂ × Z₁ × Z₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {R₀ R₁ R₂ D₁ D₂ : ℝ} (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (c₁ : Xh₁) (c₂ : Xh₂) (h₁ : ∑ w : X₁ × X₂ × Z₁ × Z₂, P.pmf w * d₁.dist w.1 c₁ ≤ D₁)
    (h₂ : ∑ w : X₁ × X₂ × Z₁ × Z₂, P.pmf w * d₂.dist w.2.1 c₂ ≤ D₂) :
    (R₀, R₁, R₂) ∈ lossyGWSIInner P d₁ d₂ D₁ D₂ ∧
    InLossyGWSIClosure P d₁ d₂ R₀ R₁ R₂ D₁ D₂ ∧
    IsLossyGWSIAchievable P d₁ d₂ R₀ R₁ R₂ D₁ D₂ := by
  have hin : (R₀, R₁, R₂) ∈ lossyGWSIInner P d₁ d₂ D₁ D₂ := by
    let g : X₁ × X₂ × Z₁ × Z₂ → X₁ × X₂ × Z₁ × Z₂ × Fin 1 × Fin 1 × Fin 1 :=
      fun w => (w.1, w.2.1, w.2.2.1, w.2.2.2, 0, 0, 0)
    have za₁ : condMutualInfo ((P.map g).map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.1))) = 0 := by
      rw [map_comp_eq]; exact condMutualInfo_map_const_snd P _ _ _
    have za₂ : condMutualInfo ((P.map g).map
        (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.2.1))) = 0 := by
      rw [map_comp_eq]; exact condMutualInfo_map_const_snd P _ _ _
    have zb₁ : condMutualInfo ((P.map g).map
        (fun t => ((t.1, t.2.1), t.2.2.2.2.2.1, (t.2.2.2.2.1, t.2.2.1)))) = 0 := by
      rw [map_comp_eq]; exact condMutualInfo_map_const_snd P _ _ _
    have zb₂ : condMutualInfo ((P.map g).map
        (fun t => ((t.1, t.2.1), t.2.2.2.2.2.2, (t.2.2.2.2.1, t.2.2.2.1)))) = 0 := by
      rw [map_comp_eq]; exact condMutualInfo_map_const_snd P _ _ _
    refine ⟨hR₀, hR₁, hR₂, 1, 1, 1, P.map g, fun _ => c₁, fun _ => c₂, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [map_comp_eq]; exact map_id_eq P
    · rw [map_comp_eq]
      exact condMutualInfo_map_const_fst P ((0 : Fin 1), (0 : Fin 1), (0 : Fin 1)) _ _
    · rw [← sum_pmf_mul_comp P g (fun t => d₁.dist t.1 c₁)]; exact h₁
    · rw [← sum_pmf_mul_comp P g (fun t => d₂.dist t.2.1 c₂)]; exact h₂
    · show R₀ + R₁ ≥ _; rw [za₁, zb₁]; linarith
    · show R₀ + R₂ ≥ _; rw [za₂, zb₂]; linarith
    · show R₀ + R₁ + R₂ ≥ _; rw [za₁, zb₁, zb₂]; linarith
    · show R₀ + R₁ + R₂ ≥ _; rw [za₂, zb₁, zb₂]; linarith
  refine ⟨hin, fun ε hε => ⟨1, fun _ => 1, fun _ => R₀, fun _ => R₁, fun _ => R₂, fun _ => D₁,
    fun _ => D₂, fun _ => zero_le_one, by simp, fun _ => hin, ?_, ?_, ?_, ?_, ?_⟩,
    hR₀, hR₁, hR₂, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  refine ⟨fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩,
    fun _ _ => c₁, fun _ _ => c₂, ?_, ?_⟩
  · exact le_trans (iid_avg_coord_le P n (fun w => d₁.dist w.1 c₁) (fun _ => d₁.nonneg _ _))
      (by linarith)
  · exact le_trans (iid_avg_coord_le P n (fun w => d₂.dist w.2.1 c₂) (fun _ => d₂.nonneg _ _))
      (by linarith)

/-! ### Lossless split-binning points (Slepian–Wolf regression) -/

/-- **Lossless split-binning points are single-letter points of the corrected inner bound.**
    With `U₀ = X = (X₁, X₂)` (relabeled into `Fin |X₁ × X₂|`), `U₁, U₂` constant and
    `X̂ⱼ = Xⱼ`, every nonnegative triple with `R₀ + Rⱼ ≥ H(X | Zⱼ)` (written as
    `I(X; X | Zⱼ)`) lies in `lossyGWSIInner P d₁ d₂ 0 0` for distortions vanishing on the
    diagonal. Instantiated at `X₁ = X₂ ~ Bern(1/2)`, `Z₁ = BEC(e)(X)`, `Z₂` constant
    (`H(X | Z₁) = e`, `H(X | Z₂) = 1`), this puts the old counterexample point `(e, 0, 1 - e)` at
    `(D₁, D₂) = (0, 0)` in the corrected region (the entropy values are not computed here). -/
theorem lossless_mem_lossyGWSIInner (P : ProbDist (X₁ × X₂ × Z₁ × Z₂))
    (d₁ : Distortion X₁ X₁) (d₂ : Distortion X₂ X₂) (hd₁ : ∀ x, d₁.dist x x = 0)
    (hd₂ : ∀ x, d₂.dist x x = 0) {R₀ R₁ R₂ : ℝ} (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h₁ : R₀ + R₁ ≥ condMutualInfo (P.map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.1))))
    (h₂ : R₀ + R₂ ≥ condMutualInfo (P.map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.2)))) :
    (R₀, R₁, R₂) ∈ lossyGWSIInner P d₁ d₂ 0 0 := by
  classical
  obtain ⟨e⟩ : Nonempty (X₁ × X₂ ≃ Fin (Fintype.card (X₁ × X₂))) := ⟨Fintype.equivFin _⟩
  let g : X₁ × X₂ × Z₁ × Z₂ →
      X₁ × X₂ × Z₁ × Z₂ × Fin (Fintype.card (X₁ × X₂)) × Fin 1 × Fin 1 :=
    fun w => (w.1, w.2.1, w.2.2.1, w.2.2.2, e (w.1, w.2.1), 0, 0)
  have za₁ : condMutualInfo ((P.map g).map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.1))) =
      condMutualInfo (P.map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.1))) := by
    have : (P.map g).map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.1)) =
        (P.map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.1))).map
          (fun t => (t.1, e t.2.1, t.2.2)) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [this, condMutualInfo_map_mid_injective _ e.injective]
  have za₂ : condMutualInfo ((P.map g).map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.2.1))) =
      condMutualInfo (P.map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.2))) := by
    have : (P.map g).map (fun t => ((t.1, t.2.1), t.2.2.2.2.1, t.2.2.2.1)) =
        (P.map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.2))).map
          (fun t => (t.1, e t.2.1, t.2.2)) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [this, condMutualInfo_map_mid_injective _ e.injective]
  have zb₁ : condMutualInfo ((P.map g).map
      (fun t => ((t.1, t.2.1), t.2.2.2.2.2.1, (t.2.2.2.2.1, t.2.2.1)))) = 0 := by
    rw [map_comp_eq]; exact condMutualInfo_map_const_snd P _ _ _
  have zb₂ : condMutualInfo ((P.map g).map
      (fun t => ((t.1, t.2.1), t.2.2.2.2.2.2, (t.2.2.2.2.1, t.2.2.2.1)))) = 0 := by
    rw [map_comp_eq]; exact condMutualInfo_map_const_snd P _ _ _
  refine ⟨hR₀, hR₁, hR₂, Fintype.card (X₁ × X₂), 1, 1, P.map g, fun u => (e.symm u.1).1,
    fun u => (e.symm u.1).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_comp_eq]; exact map_id_eq P
  · have : (P.map g).map (fun t =>
        ((t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2), (t.2.2.1, t.2.2.2.1), (t.1, t.2.1))) =
        (P.map (fun w => ((w.2.2.1, w.2.2.2), (w.1, w.2.1)))).map
          (fun t => ((fun x => (e x, (0 : Fin 1), (0 : Fin 1))) t.2, t.1, t.2)) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [this]
    exact condMutualInfo_map_fn_cond (P.map (fun w => ((w.2.2.1, w.2.2.2), (w.1, w.2.1))))
      (fun x => (e x, (0 : Fin 1), (0 : Fin 1)))
  · have h := sum_pmf_mul_comp P g (fun t => d₁.dist t.1 (e.symm t.2.2.2.2.1).1)
    refine le_of_eq (h.symm.trans ?_)
    refine Finset.sum_eq_zero fun w _ => ?_
    simp only [g, Equiv.symm_apply_apply, hd₁, mul_zero]
  · have h := sum_pmf_mul_comp P g (fun t => d₂.dist t.2.1 (e.symm t.2.2.2.2.1).2)
    refine le_of_eq (h.symm.trans ?_)
    refine Finset.sum_eq_zero fun w _ => ?_
    simp only [g, Equiv.symm_apply_apply, hd₂, mul_zero]
  · show R₀ + R₁ ≥ _; rw [za₁, zb₁]; linarith
  · show R₀ + R₂ ≥ _; rw [za₂, zb₂]; linarith
  · show R₀ + R₁ + R₂ ≥ _; rw [za₁, zb₁, zb₂]; linarith
  · show R₀ + R₁ + R₂ ≥ _; rw [za₂, zb₁, zb₂]; linarith

end GW


/-! ### The 2026-11-27 counterexample point is in the corrected region -/

section BEC

/-- Hamming distortion on `Fin 2`. -/
def hamming2 : Distortion (Fin 2) (Fin 2) :=
  ⟨fun x y => if x = y then 0 else 1, fun x y => by split_ifs <;> norm_num⟩

/-- Binary erasure channel output: `Z₁ = X` if not erased, `Z₁ = 2` if erased. -/
def becErase (s : Fin 2 × Bool) : Fin 3 := if s.2 then 2 else Fin.castSucc s.1

/-- `(X, erasure flag) ~ Unif(Fin 2) ⊗ Bern(e)`. -/
noncomputable def becSrc (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) : ProbDist (Fin 2 × Bool) :=
  (ProbDist.uniform : ProbDist (Fin 2)).prod (ProbDist.bernoulli e h0 h1)

/-- The counterexample source of the 2026-11-27 statement-fix: `X₁ = X₂ = X ~ Bern(1/2)`,
    `Z₁ = BEC(e)(X)` on `Fin 3`, `Z₂` constant on `Fin 1`. -/
noncomputable def becP (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) : ProbDist (Fin 2 × Fin 2 × Fin 3 × Fin 1) :=
  (becSrc e h0 h1).map (fun s => (s.1, s.1, becErase s, 0))

theorem negPLogP_half_mul {p : ℝ} (hp : 0 ≤ p) : negPLogP (p / 2) = p / 2 + negPLogP p / 2 := by
  have hh : negPLogP (1 / 2 : ℝ) = 1 / 2 := by
    have h2 : Real.log 2 ≠ 0 := by positivity
    simp only [negPLogP, log2, show ¬ ((1 / 2 : ℝ) ≤ 0) by norm_num, ↓reduceIte]
    rw [one_div, Real.log_inv]
    field_simp
  rw [show p / 2 = p * (1 / 2) by ring, InfoTheory.Bridge.negPLogP_mul hp (by norm_num), hh]
  ring

theorem becSrc_entropy (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    shannonEntropy (becSrc e h0 h1) = 1 + negPLogP e + negPLogP (1 - e) := by
  unfold becSrc
  rw [shannonEntropy_prod, InfoTheory.Known.shannonEntropy_uniform]
  have h2 : Real.log 2 ≠ 0 := by positivity
  simp only [Fintype.card_fin, Nat.cast_ofNat, log2, div_self h2]
  simp [shannonEntropy, ProbDist.bernoulli]
  ring

theorem becErase_entropy (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    shannonEntropy ((becSrc e h0 h1).map becErase) = (1 - e) + negPLogP (1 - e) + negPLogP e := by
  classical
  have hp : ∀ k : Fin 3, ((becSrc e h0 h1).map becErase).pmf k =
      if k = 2 then e else (1 - e) / 2 := by
    intro k
    fin_cases k <;>
      simp [becSrc, becErase, ProbDist.map, ProbDist.prod, ProbDist.uniform, ProbDist.bernoulli,
        Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring
  unfold shannonEntropy
  simp only [Fin.sum_univ_three, hp]
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ↓reduceIte]
  rw [negPLogP_half_mul (by linarith)]
  ring

/-- `H(X | Z₁) = e` for the BEC instance (as `I(X; X | Z₁)` on `X = (X₁, X₂)`). -/
theorem becP_condEntropy_Z₁ (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    condMutualInfo ((becP e h0 h1).map
      (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.1))) = e := by
  set S := becSrc e h0 h1 with hS
  have hmap : (becP e h0 h1).map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.1)) =
      S.map (fun s => ((s.1, s.1), (s.1, s.1), becErase s)) := by
    unfold becP; rw [map_comp_eq]; rfl
  have ixz : Function.Injective (fun s : Fin 2 × Bool => ((s.1, s.1), becErase s)) := by decide
  have i3 : Function.Injective
      (fun s : Fin 2 × Bool => ((s.1, s.1), (s.1, s.1), becErase s)) := by decide
  have e1 : (S.map (fun s => ((s.1, s.1), (s.1, s.1), becErase s))).map
      (fun t => (t.1, t.2.2)) = S.map (fun s => ((s.1, s.1), becErase s)) := by
    rw [map_comp_eq]; rfl
  have e2 : (S.map (fun s => ((s.1, s.1), (s.1, s.1), becErase s))).map
      (fun t => (t.2.1, t.2.2)) = S.map (fun s => ((s.1, s.1), becErase s)) := by
    rw [map_comp_eq]; rfl
  have e3 : (S.map (fun s => ((s.1, s.1), (s.1, s.1), becErase s))).map
      (fun t => t.2.2) = S.map becErase := by
    rw [map_comp_eq]; rfl
  rw [hmap]; unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ ixz, shannonEntropy_map_of_injective _ i3,
    hS, becErase_entropy, becSrc_entropy]
  ring

/-- `H(X | Z₂) = H(X) = 1` for the BEC instance (`Z₂` constant). -/
theorem becP_condEntropy_Z₂ (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    condMutualInfo ((becP e h0 h1).map
      (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.2))) = 1 := by
  set S := becSrc e h0 h1 with hS
  have hmap : (becP e h0 h1).map (fun w => ((w.1, w.2.1), (w.1, w.2.1), w.2.2.2)) =
      (S.map Prod.fst).map (fun x => ((x, x), (x, x), (0 : Fin 1))) := by
    unfold becP; rw [map_comp_eq, map_comp_eq]; rfl
  have ixz : Function.Injective (fun x : Fin 2 => ((x, x), (0 : Fin 1))) := by decide
  have i3 : Function.Injective (fun x : Fin 2 => ((x, x), (x, x), (0 : Fin 1))) := by decide
  have e1 : ((S.map Prod.fst).map (fun x => ((x, x), (x, x), (0 : Fin 1)))).map
      (fun t => (t.1, t.2.2)) = (S.map Prod.fst).map (fun x => ((x, x), (0 : Fin 1))) := by
    rw [map_comp_eq]; rfl
  have e2 : ((S.map Prod.fst).map (fun x => ((x, x), (x, x), (0 : Fin 1)))).map
      (fun t => (t.2.1, t.2.2)) = (S.map Prod.fst).map (fun x => ((x, x), (0 : Fin 1))) := by
    rw [map_comp_eq]; rfl
  have e3 : ((S.map Prod.fst).map (fun x => ((x, x), (x, x), (0 : Fin 1)))).map
      (fun t => t.2.2) = (S.map Prod.fst).map (fun _ => (0 : Fin 1)) := by
    rw [map_comp_eq]; rfl
  have hU : shannonEntropy (S.map Prod.fst) = 1 := by
    rw [map_fst_eq_fst, hS, becSrc, InfoTheory.Known.shannonEntropy_prod_fst,
      InfoTheory.Known.shannonEntropy_uniform]
    have h2 : Real.log 2 ≠ 0 := by positivity
    simp only [Fintype.card_fin, Nat.cast_ofNat, log2, div_self h2]
  rw [hmap]; unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, shannonEntropy_map_of_injective _ ixz, shannonEntropy_map_of_injective _ i3,
    shannonEntropy_map_const, hU]
  ring

/-- **Regression for the 2026-11-27 statement-fix.** For every `e ∈ [0, 1]` the old
    counterexample tuple `(R₀, R₁, R₂, D₁, D₂) = (e, 0, 1 - e, 0, 0)` is a single-letter point
    of the corrected inner bound (`U₀ = X`), hence lies in its closure. (Under the previous
    `lossyGWSIInner` it was outside the closure for `0 < e < 1`.) -/
theorem bec_point_mem (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    (e, 0, 1 - e) ∈ lossyGWSIInner (becP e h0 h1) hamming2 hamming2 0 0 ∧
    InLossyGWSIClosure (becP e h0 h1) hamming2 hamming2 e 0 (1 - e) 0 0 := by
  have hin : (e, 0, 1 - e) ∈ lossyGWSIInner (becP e h0 h1) hamming2 hamming2 0 0 :=
    lossless_mem_lossyGWSIInner (becP e h0 h1) hamming2 hamming2 (fun x => by simp [hamming2])
      (fun x => by simp [hamming2]) h0 le_rfl (by linarith)
      (by rw [becP_condEntropy_Z₁]; linarith) (by rw [becP_condEntropy_Z₂]; linarith)
  refine ⟨hin, fun ε hε => ⟨1, fun _ => 1, fun _ => e, fun _ => 0, fun _ => 1 - e, fun _ => 0,
    fun _ => 0, fun _ => zero_le_one, by simp, fun _ => hin, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp <;> linarith

end BEC

end InfoTheory.Known.Certificates.GrayWynerLossy
