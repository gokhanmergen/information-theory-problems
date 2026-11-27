import InfoTheory.Problems.CeoProblemGeneral
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.CeoProblemGeneral`

The frozen statement asks whether, for the two-agent binary symmetric CEO problem
(`X ~ Bern(1/2)` observed through independent `BSC(p₁)`, `BSC(p₂)`, `0 < pᵢ < 1/2`, Hamming
distortion), operational achievability `IsCEOAchievable` coincides with the closure of the
Berger–Tung inner bound `InCEOBergerTungClosure`, for all `R₁, R₂` and `0 ≤ D ≤ 1/2`.

## Certified (about exactly these objects)
* Generic converse machinery (copied from the `MultiterminalSourceCoding` certificate):
  `rateDistortion_map_le`, `rd_map_le_of_codes` (block codes ⇒ `R(D) ≤ R`, via the Bridge's
  `rateDistortion_operational_converse`).
* `isCEOAchievable_rd_le` — cut-set converse `R_X(D) ≤ R₁ + R₂` for every operationally
  achievable tuple of any discrete memoryless CEO problem (the agents' joint message is a
  rate-`(R₁+R₂)` code for the i.i.d. source `(X, Y₁, Y₂)` with distortion on `X`;
  Berger–Zhang–Viswanathan 1996, El Gamal–Kim §12.4).
* `one_sub_binaryEntropy_le_rateDistortion` — `R(D) ≥ 1 - h(D)` for `Bern(1/2)` under Hamming
  distortion, `0 ≤ D ≤ 1/2` (Cover–Thomas Thm. 10.3.1 converse half, via Fano).
* `achievable_sumRate_ge`, `zero_rates_not_achievable` — the left-hand side of `Statement`
  satisfies `R₁ + R₂ ≥ 1 - h(D)` and is not trivially true.
* `isCEOAchievable_of_const`, `inCEOBergerTungClosure_of_const`, `half_mem_both` — both
  sides are nonempty: at `D = 1/2` every nonnegative rate pair is achievable and lies in the
  Berger–Tung closure (constant time-sharing variable and auxiliaries).

## Not certified
* Achievability of the Berger–Tung inner bound for the CEO problem (needs the Markov lemma
  and distributed binning; not in `Bridge`).
* The sum-rate bound for the closure side (`R₁ + R₂ ≥ I(Y₁Y₂; U₁U₂ | Q) ≥ R_X(D)`): requires a
  conditional data-processing inequality given the time-sharing variable `Q`, which is not
  available in `Bridge`; not attempted.
* The positive minimum distortion `D_min > 0` (infinite-rate MAP error) and the
  Oohama / Prabhakaran–Tse–Ramchandran sum-rate results (Gaussian CEO; out of scope).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CeoProblemGeneral

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.CeoProblemGeneral

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

/-- Pushforward along an injective map keeps the mass of each atom. -/
theorem map_pmf_of_injective (P : ProbDist α) {f : α → β} (hf : Function.Injective f) (a : α) :
    (P.map f).pmf (f a) = P.pmf a := by
  classical
  simp only [ProbDist.map]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne; simp [hf.ne hne]
  · simp

end Helpers

/-! ### The discrete memoryless CEO problem: generic facts -/

section CEO

variable {X Y₁ Y₂ Xh : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Xh]

/-- Joint single-letter law of `(X, Y₁, Y₂)`: `P(x) W₁(y₁|x) W₂(y₂|x)`. -/
def ceoJoint (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂) : ProbDist (X × Y₁ × Y₂) where
  pmf t := Px.pmf t.1 * W₁.trans t.1 t.2.1 * W₂.trans t.1 t.2.2
  nonneg t := mul_nonneg (mul_nonneg (Px.nonneg _) (W₁.nonneg _ _)) (W₂.nonneg _ _)
  sum_one := by
    have h : ∀ x, ∑ y₁ : Y₁, ∑ y₂ : Y₂, Px.pmf x * W₁.trans x y₁ * W₂.trans x y₂ = Px.pmf x := by
      intro x
      simp_rw [← Finset.mul_sum, W₂.sum_one, mul_one, ← Finset.mul_sum, W₁.sum_one, mul_one]
    simp_rw [Fintype.sum_prod_type, h]; exact Px.sum_one

theorem ceoJoint_map_fst (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂) :
    (ceoJoint Px W₁ W₂).map Prod.fst = Px := by
  rw [map_fst_eq_fst]
  refine probDist_eq_of_pmf fun x => ?_
  simp only [ProbDist.fst, ceoJoint, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, W₂.sum_one, mul_one, ← Finset.mul_sum, W₁.sum_one, mul_one]

/-- **Cut-set converse for the CEO problem**: every operationally achievable `(R₁, R₂, D)`
    satisfies `R_X(D) ≤ R₁ + R₂` — the agents' joint message is a rate-`(R₁+R₂)` code for the
    source `(X, Y₁, Y₂)` with distortion measured on `X` (Berger–Zhang–Viswanathan 1996;
    El Gamal–Kim §12.4). -/
theorem isCEOAchievable_rd_le (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂)
    (d : Distortion X Xh) {R₁ R₂ D : ℝ} (h : IsCEOAchievable Px W₁ W₂ d R₁ R₂ D) :
    rateDistortion Px d D ≤ R₁ + R₂ := by
  obtain ⟨hR₁, hR₂, hach⟩ := h
  rw [← ceoJoint_map_fst Px W₁ W₂]
  refine rd_map_le_of_codes (ceoJoint Px W₁ W₂) Prod.fst d (by linarith) fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min (η / 2) δ) (lt_min (by linarith) hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec, hD⟩ := hN n hn
  refine ⟨_, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity)),
    card_mul_le hR₁ hR₂ (lt_min (by linarith) hδ) (by linarith [min_le_left (η / 2) δ]),
    fun z => finProdFinEquiv (enc₁ (fun j => (z j).2.1), enc₂ (fun j => (z j).2.2)),
    fun k => dec (finProdFinEquiv.symm k), ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact le_trans hD (by linarith [min_le_right (η / 2) δ])

/-- **Trivial corner, operational side**: if a constant reconstruction `c` has expected
    distortion `≤ D`, every nonnegative rate pair is achievable at `D`. -/
theorem isCEOAchievable_of_const (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂)
    (d : Distortion X Xh) {R₁ R₂ D : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (c : Xh)
    (hc : ∑ x : X, Px.pmf x * d.dist x c ≤ D) : IsCEOAchievable Px W₁ W₂ d R₁ R₂ D := by
  refine ⟨hR₁, hR₂, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  refine ⟨fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩, fun _ _ => c, ?_⟩
  have h := iid_avg_coord_le (ceoJoint Px W₁ W₂) n (fun t => d.dist t.1 c) (fun t => d.nonneg _ _)
  have h2 : ∑ t : X × Y₁ × Y₂, (ceoJoint Px W₁ W₂).pmf t * d.dist t.1 c ≤ D := by
    rw [sum_pmf_mul_comp (ceoJoint Px W₁ W₂) Prod.fst (fun x => d.dist x c), ceoJoint_map_fst]
    exact hc
  exact le_trans h (by linarith)

/-- **Trivial corner, single-letter side**: under the same hypothesis every nonnegative rate
    pair lies in the closure of the Berger–Tung inner bound (constant time-sharing variable and
    constant auxiliaries `U₁ = U₂ = 0`). -/
theorem inCEOBergerTungClosure_of_const (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂)
    (d : Distortion X Xh) {R₁ R₂ D : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (c : Xh)
    (hc : ∑ x : X, Px.pmf x * d.dist x c ≤ D) : InCEOBergerTungClosure Px W₁ W₂ d R₁ R₂ D := by
  intro ε hε
  set J0 := ceoJoint Px W₁ W₂ with hJ0
  let f : X × Y₁ × Y₂ → Fin 1 × X × Y₁ × Y₂ × Fin 1 × Fin 1 := fun s => (0, s.1, s.2.1, s.2.2, 0, 0)
  have hf : Function.Injective f := fun a b h => by
    simp only [f, Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2.1)
  refine ⟨by linarith, by linarith, 1, 1, 1, diracDist 0, fun _ => diracDist 0,
    fun _ => diracDist 0, fun _ => c, J0.map f, ?_, ?_, ?_, ?_, ?_⟩
  · intro q x y₁ y₂ u₁ u₂
    obtain rfl : q = 0 := Subsingleton.elim _ _
    obtain rfl : u₁ = 0 := Subsingleton.elim _ _
    obtain rfl : u₂ = 0 := Subsingleton.elim _ _
    have := map_pmf_of_injective J0 hf (x, y₁, y₂)
    simp only [f] at this
    rw [this]; simp [hJ0, ceoJoint, diracDist]
  · rw [← sum_pmf_mul_comp J0 f (fun t => d.dist t.2.1 c)]
    have h2 : ∑ t : X × Y₁ × Y₂, J0.pmf t * d.dist t.1 c ≤ D := by
      rw [sum_pmf_mul_comp J0 Prod.fst (fun x => d.dist x c), hJ0, ceoJoint_map_fst]; exact hc
    simp only [f]; linarith
  · rw [map_comp_eq]
    have := condMutualInfo_map_const_snd J0 (0 : Fin 1) (fun s => s.2.1)
      (fun _ => ((0 : Fin 1), (0 : Fin 1)))
    exact le_of_eq_of_le this (by linarith)
  · rw [map_comp_eq]
    have := condMutualInfo_map_const_snd J0 (0 : Fin 1) (fun s => s.2.2)
      (fun _ => ((0 : Fin 1), (0 : Fin 1)))
    exact le_of_eq_of_le this (by linarith)
  · rw [map_comp_eq]
    have := condMutualInfo_map_const_snd J0 ((0 : Fin 1), (0 : Fin 1))
      (fun s => (s.2.1, s.2.2)) (fun _ => (0 : Fin 1))
    exact le_of_eq_of_le this (by linarith)

end CEO

/-! ### The binary symmetric CEO problem of `Statement` -/

section Binary

/-- **Binary rate–distortion lower bound** (Cover–Thomas Thm. 10.3.1, converse half, via
    Fano's inequality): for a `Bern(1/2)` source under Hamming distortion and `0 ≤ D ≤ 1/2`,
    `R(D) ≥ 1 - h(D)`. -/
theorem one_sub_binaryEntropy_le_rateDistortion {P : ProbDist Bool} (hP : ∀ b, P.pmf b = 1 / 2)
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1 / 2) :
    1 - binaryEntropy D ≤ rateDistortion P ceoBinHamming D := by
  classical
  have hPb : P = ProbDist.bernoulli (1 / 2) (by norm_num) (by norm_num) :=
    probDist_eq_of_pmf fun b => by cases b <;> (simp [ProbDist.bernoulli, hP]; try norm_num)
  have hH : shannonEntropy P = 1 := by
    rw [hPb, shannonEntropy_bernoulli, binaryEntropy_half]
  unfold rateDistortion
  refine le_csInf ⟨mutualInfo (P.map fun x => (x, x)), P.map fun x => (x, x), ?_, ?_, rfl⟩ ?_
  · rw [← map_fst_eq_fst, map_comp_eq]
    exact probDist_eq_of_pmf fun b => by cases b <;> simp [ProbDist.map]
  · rw [← sum_pmf_mul_comp P (fun x => (x, x)) (fun xy => ceoBinHamming.dist xy.1 xy.2)]
    simpa [ceoBinHamming] using hD0
  rintro r ⟨Q, hQf, hQd, rfl⟩
  have hpe : estErrorProb Q id = ∑ xy : Bool × Bool, Q.pmf xy * ceoBinHamming.dist xy.1 xy.2 := by
    unfold estErrorProb
    refine Finset.sum_congr rfl fun xy _ => ?_
    by_cases h : xy.2 = xy.1
    · simp [h, ceoBinHamming]
    · simp [h, ceoBinHamming, Ne.symm h]
  have hfano := fano_inequality Q id (by simp)
  have hcard : log2 ((Fintype.card Bool : ℝ) - 1) = 0 := by norm_num [log2]
  rw [hcard, mul_zero, add_zero] at hfano
  set pe := estErrorProb Q id
  have hpe0 : 0 ≤ pe := estErrorProb_nonneg Q id
  have hpeD : pe ≤ D := hpe ▸ hQd
  have hmono : binaryEntropy pe ≤ binaryEntropy D := by
    rw [binaryEntropy_eq_binEntropy hpe0 (by linarith), binaryEntropy_eq_binEntropy hD0 (by linarith)]
    refine div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le
    exact Real.binEntropy_strictMonoOn.monotoneOn ⟨hpe0, by linarith⟩ ⟨hD0, by linarith⟩ hpeD
  have hmi : mutualInfo Q = shannonEntropy Q.fst - condEntropy Q := by
    unfold mutualInfo condEntropy; ring
  rw [hmi, hQf, hH]; linarith

/-- `h(D) < 1` strictly below `D = 1/2`, so `1 - h(D) > 0`. -/
theorem binaryEntropy_lt_one {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D < 1 / 2) : binaryEntropy D < 1 := by
  rw [← binaryEntropy_half, binaryEntropy_eq_binEntropy hD0 (by linarith),
    binaryEntropy_eq_binEntropy (by norm_num) (by norm_num)]
  refine div_lt_div_of_pos_right ?_ (Real.log_pos (by norm_num))
  exact Real.binEntropy_strictMonoOn ⟨hD0, by linarith⟩ ⟨by norm_num, by norm_num⟩
    (by linarith)


theorem uniform_bool_pmf (b : Bool) : (ProbDist.uniform : ProbDist Bool).pmf b = 1 / 2 := by
  simp [ProbDist.uniform]

/-- **Left-hand side of `Statement` is outer-bounded**: for the binary symmetric CEO problem,
    every achievable `(R₁, R₂, D)` with `0 ≤ D ≤ 1/2` has `R₁ + R₂ ≥ 1 - h(D)`. -/
theorem achievable_sumRate_ge {p₁ p₂ : ℝ} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1) (h20 : 0 ≤ p₂)
    (h21 : p₂ ≤ 1) {R₁ R₂ D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1 / 2)
    (h : IsCEOAchievable ProbDist.uniform (bsc p₁ h10 h11) (bsc p₂ h20 h21) ceoBinHamming
      R₁ R₂ D) :
    1 - binaryEntropy D ≤ R₁ + R₂ :=
  le_trans (one_sub_binaryEntropy_le_rateDistortion uniform_bool_pmf hD0 hD1)
    (isCEOAchievable_rd_le _ _ _ _ h)

/-- The left-hand side is not trivially true: zero rates are not achievable below `D = 1/2`. -/
theorem zero_rates_not_achievable {p₁ p₂ : ℝ} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1) (h20 : 0 ≤ p₂)
    (h21 : p₂ ≤ 1) {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D < 1 / 2) :
    ¬ IsCEOAchievable ProbDist.uniform (bsc p₁ h10 h11) (bsc p₂ h20 h21) ceoBinHamming 0 0 D :=
  fun h => by
    have := achievable_sumRate_ge h10 h11 h20 h21 hD0 hD1.le h
    have := binaryEntropy_lt_one hD0 hD1
    linarith

theorem uniform_const_dist (c : Bool) :
    ∑ x : Bool, (ProbDist.uniform : ProbDist Bool).pmf x * ceoBinHamming.dist x c = 1 / 2 := by
  cases c <;> simp [ceoBinHamming, uniform_bool_pmf]

/-- **Both sides of `Statement` are nonempty**: at `D = 1/2` every nonnegative rate pair is
    achievable and lies in the Berger–Tung closure. -/
theorem half_mem_both {p₁ p₂ : ℝ} (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1) (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    IsCEOAchievable ProbDist.uniform (bsc p₁ h10 h11) (bsc p₂ h20 h21) ceoBinHamming
      R₁ R₂ (1 / 2) ∧
    InCEOBergerTungClosure ProbDist.uniform (bsc p₁ h10 h11) (bsc p₂ h20 h21) ceoBinHamming
      R₁ R₂ (1 / 2) :=
  ⟨isCEOAchievable_of_const _ _ _ _ hR₁ hR₂ false (uniform_const_dist false).le,
    inCEOBergerTungClosure_of_const _ _ _ _ hR₁ hR₂ false (uniform_const_dist false).le⟩

end Binary

end InfoTheory.Known.Certificates.CeoProblemGeneral
