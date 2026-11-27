import InfoTheory.Problems.MultiterminalSourceCoding
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.MultiterminalSourceCoding`

The frozen statement asks whether, for the doubly symmetric binary source `DSBS(p)`
(`0 < p < 1/2`) under separate binary Hamming distortions, operational achievability
`IsBergerTungAchievable` coincides with membership in the time-sharing closure of the
Berger–Tung inner bound `InBergerTungClosure`, for all `R₁, R₂` and `0 ≤ Dᵢ ≤ 1/2`.

## Certified (about exactly these objects)
* Generic converse machinery (any finite alphabets):
  `rateDistortion_map_le` (rate–distortion of a projection), `rd_map_le_of_codes`
  (any family of rate-`R` block codes for a source with a projected distortion gives
  `R(D) ≤ R`, via the Bridge's `rateDistortion_operational_converse`), and the
  time-sharing/Jensen bound `rd_le_of_timeSharing` (from `rateDistortion_convex`,
  `rateDistortion_rightContinuous`).
* `isBergerTungAchievable_rd_fst_le`, `isBergerTungAchievable_rd_snd_le` — the cut-set
  (sum-rate) outer bound `R_{Xᵢ}(Dᵢ) ≤ R₁ + R₂` for every operationally achievable tuple
  (Berger 1977; El Gamal–Kim, *Network Information Theory*, Ch. 12).
* `bergerTungInnerBound_rd_fst_le`/`_snd_le`, `inBergerTungClosure_rd_fst_le`/`_snd_le` —
  the Berger–Tung inner bound and its time-sharing closure lie inside the same outer bound
  (data processing + convexity of `R(·)`), i.e. *inner ⊆ outer* for the bounds of `Statement`.
* `one_sub_binaryEntropy_le_rateDistortion` — `R(D) ≥ 1 - h(D)` for a `Bern(1/2)` source
  under Hamming distortion, `0 ≤ D ≤ 1/2` (Cover–Thomas Thm. 10.3.1, converse half, via the
  Bridge's Fano inequality).
* `achievable_sumRate_ge`, `closure_sumRate_ge` — both sides of the `↔` in `Statement`
  satisfy `R₁ + R₂ ≥ 1 - h(Dᵢ)`; `zero_rates_not_achievable` — so neither side is trivially
  true (zero rates fail on both sides for `D₁ < 1/2`).
* `achievable_half_half`, `mem_bergerTungInnerBound_half_half`, `inClosure_half_half` —
  both sides are nonempty: at `D₁ = D₂ = 1/2` every nonnegative rate pair is on both sides
  (constant reconstructions / constant auxiliaries).
* `isBergerTungAchievable_of_slepianWolf`, `achievable_lossless_of_slepianWolf` — the
  Slepian–Wolf lossless corner is consistent with the formalization: every interior
  Slepian–Wolf pair (Bridge `slepian_wolf_achievability`) is achievable at `D₁ = D₂ = 0`;
  `lossless_sumRate_ge` — and any achievable lossless pair has `R₁ + R₂ ≥ 1`.
* `slepianWolf_subset_bergerTungInnerBound`, `slepianWolf_subset_closure`,
  `lossless_corner_both` — single-letter side of the corner: the Slepian–Wolf region
  (Bridge `slepianWolfSingleLetter`) lies in the Berger–Tung inner bound at `D₁ = D₂ = 0`
  (take `Uᵢ = Xᵢ`); so interior Slepian–Wolf pairs of `DSBS(p)` are on *both* sides of
  `Statement` at `D = 0`.

## Not certified
* Achievability of the Berger–Tung inner bound (`InBergerTungClosure → IsBergerTungAchievable`;
  Berger 1977, Tung 1978): needs the Markov lemma / mutual covering lemma for distributed
  quantize-and-bin, which `Bridge` does not provide.
* The individual-rate bounds `Rᵢ ≥ R_{Xᵢ|Xⱼ}(Dᵢ)` (conditional rate–distortion is not defined
  in `Core`) and the exact value `R(D) = 1 - h(D)` (only the lower bound is proved).
  Note that the naive bound `Rᵢ ≥ R_{Xᵢ}(Dᵢ)` is false here (the decoder sees both messages),
  so only sum-rate bounds are certified.
* The Wagner–Kelly–Altuğ (2011) counterexample for general sources (out of scope).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MultiterminalSourceCoding

open InfoTheory InfoTheory.Bridge InfoTheory.Known.Operational
open InfoTheory.Problems.MultiterminalSourceCoding

/-! ### Generic helpers: projections, data processing, and code-to-converse bridge -/

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

theorem map_id_eq (P : ProbDist α) : P.map id = P := by
  classical
  refine probDist_eq_of_pmf fun a => ?_
  simp [ProbDist.map]

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

end Helpers

/-! ### Generic operational sum-rate converse for Berger–Tung codes -/

section Operational

variable {X₁ X₂ Xh₁ Xh₂ : Type*} [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]

/-- **Cut-set (sum-rate) converse, first source.** Any operationally achievable
    `(R₁, R₂, D₁, D₂)` for two-terminal distributed lossy coding satisfies
    `R_{X₁}(D₁) ≤ R₁ + R₂`: merging the two encoders gives a single code for `X₁` of size
    `M₁ M₂` (Berger 1977, §3; El Gamal–Kim Thm. 12.1 outer bound, sum-rate coordinate). -/
theorem isBergerTungAchievable_rd_fst_le (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {R₁ R₂ D₁ D₂ : ℝ}
    (h : IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂) :
    rateDistortion P.fst d₁ D₁ ≤ R₁ + R₂ := by
  obtain ⟨hR₁, hR₂, hach⟩ := h
  rw [← map_fst_eq_fst]
  refine rd_map_le_of_codes P Prod.fst d₁ (by linarith) fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min (η / 2) δ) (lt_min (by linarith) hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, -, hD₁, -⟩ := hN n hn
  refine ⟨_, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity)),
    card_mul_le hR₁ hR₂ (lt_min (by linarith) hδ) (by linarith [min_le_left (η / 2) δ]),
    fun x => finProdFinEquiv (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)),
    fun k => dec₁ (finProdFinEquiv.symm k), ?_⟩
  simp only [Equiv.symm_apply_apply]
  linarith [min_le_right (η / 2) δ]

/-- **Cut-set (sum-rate) converse, second source**: `R_{X₂}(D₂) ≤ R₁ + R₂`. -/
theorem isBergerTungAchievable_rd_snd_le (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {R₁ R₂ D₁ D₂ : ℝ}
    (h : IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂) :
    rateDistortion P.snd d₂ D₂ ≤ R₁ + R₂ := by
  obtain ⟨hR₁, hR₂, hach⟩ := h
  rw [← map_snd_eq_snd]
  refine rd_map_le_of_codes P Prod.snd d₂ (by linarith) fun η hη δ hδ => ?_
  obtain ⟨N, hN⟩ := hach (min (η / 2) δ) (lt_min (by linarith) hδ)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, -, dec₂, -, hD₂⟩ := hN n hn
  refine ⟨_, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity)),
    card_mul_le hR₁ hR₂ (lt_min (by linarith) hδ) (by linarith [min_le_left (η / 2) δ]),
    fun x => finProdFinEquiv (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)),
    fun k => dec₂ (finProdFinEquiv.symm k), ?_⟩
  simp only [Equiv.symm_apply_apply]
  linarith [min_le_right (η / 2) δ]

/-- **Berger–Tung inner-bound points obey the same sum-rate bound**:
    `R₁ + R₂ ≥ I(X₁X₂; U₁U₂) ≥ I(X₁; g₁(U₁, U₂)) ≥ R_{X₁}(D₁)` (data processing). -/
theorem bergerTungInnerBound_rd_fst_le (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {D₁ D₂ : ℝ} {r : ℝ × ℝ}
    (hr : r ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂) :
    RDFeasible P.fst d₁ D₁ ∧ rateDistortion P.fst d₁ D₁ ≤ r.1 + r.2 := by
  obtain ⟨-, -, kU₁, kU₂, Q, g₁, g₂, hQP, -, -, hd₁, -, -, -, hsum⟩ := hr
  set Q'' := Q.map (fun t => (t.1, g₁ (t.2.2.1, t.2.2.2))) with hQ''
  have hf : Q''.fst = P.fst := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQP, ← map_fst_eq_fst, map_comp_eq]; rfl
  have hdist : expectedDist Q'' d₁ ≤ D₁ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.1, g₁ (t.2.2.1, t.2.2.2)))
      (fun xy : X₁ × Xh₁ => d₁.dist xy.1 xy.2)]; exact hd₁
  have hmi : mutualInfo Q'' ≤ mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) := by
    have : Q'' = (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).map
        (Prod.map Prod.fst g₁) := by rw [hQ'', map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  exact ⟨⟨Q'', hf, hdist⟩, by linarith [rateDistortion_le_mutualInfo hf hdist]⟩

/-- Same for the second source: `R_{X₂}(D₂) ≤ r₁ + r₂` on the Berger–Tung inner bound. -/
theorem bergerTungInnerBound_rd_snd_le (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {D₁ D₂ : ℝ} {r : ℝ × ℝ}
    (hr : r ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂) :
    RDFeasible P.snd d₂ D₂ ∧ rateDistortion P.snd d₂ D₂ ≤ r.1 + r.2 := by
  obtain ⟨-, -, kU₁, kU₂, Q, g₁, g₂, hQP, -, -, -, hd₂, -, -, hsum⟩ := hr
  set Q'' := Q.map (fun t => (t.2.1, g₂ (t.2.2.1, t.2.2.2))) with hQ''
  have hf : Q''.fst = P.snd := by
    rw [← map_fst_eq_fst, hQ'', map_comp_eq, ← hQP, ← map_snd_eq_snd, map_comp_eq]; rfl
  have hdist : expectedDist Q'' d₂ ≤ D₂ := by
    unfold expectedDist
    rw [hQ'', ← sum_pmf_mul_comp Q (fun t => (t.2.1, g₂ (t.2.2.1, t.2.2.2)))
      (fun xy : X₂ × Xh₂ => d₂.dist xy.1 xy.2)]; exact hd₂
  have hmi : mutualInfo Q'' ≤ mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) := by
    have : Q'' = (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).map
        (Prod.map Prod.snd g₂) := by rw [hQ'', map_comp_eq]; rfl
    rw [this]; exact mutualInfo_map_prodMap_le _ _ _
  exact ⟨⟨Q'', hf, hdist⟩, by linarith [rateDistortion_le_mutualInfo hf hdist]⟩

/-- **The time-sharing closure of the Berger–Tung inner bound obeys the sum-rate bound**
    `R_{X₁}(D₁) ≤ R₁ + R₂` (Jensen over the convex `R(·)`, then right-continuity). -/
theorem inBergerTungClosure_rd_fst_le (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {R₁ R₂ D₁ D₂ : ℝ}
    (h : InBergerTungClosure P d₁ d₂ R₁ R₂ D₁ D₂) :
    rateDistortion P.fst d₁ D₁ ≤ R₁ + R₂ := by
  refine rd_le_of_timeSharing fun ε hε => ?_
  obtain ⟨m, w, r₁, r₂, δ₁, δ₂, hw0, hw1, hin, hr₁, hr₂, hδ₁, -⟩ := h (ε / 2) (half_pos hε)
  refine ⟨m, w, fun i => r₁ i + r₂ i, δ₁, hw0, hw1, fun i => (bergerTungInnerBound_rd_fst_le P
    d₁ d₂ (hin i)).1, fun i => (bergerTungInnerBound_rd_fst_le P d₁ d₂ (hin i)).2,
    by linarith, ?_⟩
  simp only [mul_add, Finset.sum_add_distrib]; linarith

/-- Second-source version: `R_{X₂}(D₂) ≤ R₁ + R₂` on the closure. -/
theorem inBergerTungClosure_rd_snd_le (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁)
    (d₂ : Distortion X₂ Xh₂) {R₁ R₂ D₁ D₂ : ℝ}
    (h : InBergerTungClosure P d₁ d₂ R₁ R₂ D₁ D₂) :
    rateDistortion P.snd d₂ D₂ ≤ R₁ + R₂ := by
  refine rd_le_of_timeSharing fun ε hε => ?_
  obtain ⟨m, w, r₁, r₂, δ₁, δ₂, hw0, hw1, hin, hr₁, hr₂, -, hδ₂⟩ := h (ε / 2) (half_pos hε)
  refine ⟨m, w, fun i => r₁ i + r₂ i, δ₂, hw0, hw1, fun i => (bergerTungInnerBound_rd_snd_le P
    d₁ d₂ (hin i)).1, fun i => (bergerTungInnerBound_rd_snd_le P d₁ d₂ (hin i)).2,
    by linarith, ?_⟩
  simp only [mul_add, Finset.sum_add_distrib]; linarith

omit [Fintype Xh₁] [Fintype Xh₂] in
/-- Per-letter distortion is dominated by the block (Slepian–Wolf) error probability whenever
    `d(x, x) = 0` and `d ≤ 1`; stated for a generic coordinate `proj` of the source pair. -/
theorem avgDist_le_slepianWolfError {Y : Type*} (P : ProbDist (X₁ × X₂)) (d : Distortion Y Y)
    (hd : ∀ x, d.dist x x = 0) (hd' : ∀ x y, d.dist x y ≤ 1)
    {n : ℕ} (proj : X₁ × X₂ → Y) (projSeq : (Fin n → X₁) × (Fin n → X₂) → Fin n → Y)
    (hproj : ∀ (xy : (Fin n → X₁) × (Fin n → X₂)) i, projSeq xy i = proj (xy.1 i, xy.2 i))
    {M₁ M₂ : ℕ} (f₁ : (Fin n → X₁) → Fin M₁) (f₂ : (Fin n → X₂) → Fin M₂)
    (dec : Fin M₁ → Fin M₂ → (Fin n → X₁) × (Fin n → X₂)) :
    ∑ z : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (z i)) * ((1 / (n : ℝ)) * ∑ i : Fin n,
      d.dist (proj (z i)) (projSeq (dec (f₁ fun j => (z j).1) (f₂ fun j => (z j).2)) i)) ≤
      slepianWolfError P n M₁ M₂ f₁ f₂ dec := by
  classical
  unfold slepianWolfError
  rw [← Fintype.sum_equiv (zipEquiv X₁ X₂ n).symm _ _ (fun _ => rfl)]
  refine Finset.sum_le_sum fun z _ => ?_
  have hz : (zipEquiv X₁ X₂ n).symm z = (fun j => (z j).1, fun j => (z j).2) := rfl
  have hP : (jointIidDist P n).pmf ((zipEquiv X₁ X₂ n).symm z) = ∏ i : Fin n, P.pmf (z i) := rfl
  rw [hP, hz]
  have hprod : 0 ≤ ∏ i : Fin n, P.pmf (z i) := Finset.prod_nonneg fun i _ => P.nonneg _
  split_ifs with hc
  · refine mul_le_of_le_one_right hprod ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [one_div, inv_mul_le_iff₀ (by positivity), mul_one]
      calc _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hd' _ _
        _ = n := by simp
  · rw [not_not] at hc
    have : ∀ i, d.dist (proj (z i)) (projSeq (dec (f₁ fun j => (z j).1) (f₂ fun j => (z j).2)) i)
        = 0 := by
      intro i; rw [hc, hproj]; exact hd _
    simp [this]

omit [Fintype Xh₁] [Fintype Xh₂] in
/-- **Slepian–Wolf ⇒ lossless corner of the Berger–Tung region.** Any Slepian–Wolf achievable
    pair `(R₁, R₂)` (Cover–Thomas §15.4) is operationally achievable for distributed lossy
    coding at `D₁ = D₂ = 0`, for any distortions vanishing on the diagonal and bounded by `1`
    (e.g. Hamming). -/
theorem isBergerTungAchievable_of_slepianWolf (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ X₁)
    (d₂ : Distortion X₂ X₂) (hd₁ : ∀ x, d₁.dist x x = 0) (hd₁' : ∀ x y, d₁.dist x y ≤ 1)
    (hd₂ : ∀ x, d₂.dist x x = 0) (hd₂' : ∀ x y, d₂.dist x y ≤ 1) {R₁ R₂ : ℝ}
    (h : IsSlepianWolfAchievable P R₁ R₂) : IsBergerTungAchievable P d₁ d₂ R₁ R₂ 0 0 := by
  obtain ⟨hR₁, hR₂, hsw⟩ := h
  refine ⟨hR₁, hR₂, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hsw ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨f₁, f₂, dec, herr⟩ := hN n hn
  have hle : ∀ R : ℝ, 0 ≤ R → max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) ≤
      Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R + ε)))) := fun R hR =>
    max_le_max le_rfl (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))))
  have key : ∀ (A₁ A₂ : ℕ) (hA₁ : 1 ≤ A₁) (hA₂ : 1 ≤ A₂) (f₁ : (Fin n → X₁) → Fin A₁)
      (f₂ : (Fin n → X₂) → Fin A₂) (dec : Fin A₁ → Fin A₂ → (Fin n → X₁) × (Fin n → X₂)),
      slepianWolfError P n A₁ A₂ f₁ f₂ dec ≤ ε →
      ∀ (B₁ B₂ : ℕ) (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂),
      ∃ (enc₁ : (Fin n → X₁) → Fin B₁) (enc₂ : (Fin n → X₂) → Fin B₂)
        (dec₁ : Fin B₁ × Fin B₂ → Fin n → X₁) (dec₂ : Fin B₁ × Fin B₂ → Fin n → X₂),
        (∑ x : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (x i)) *
          ((1 / (n : ℝ)) * ∑ i : Fin n, d₁.dist (x i).1
            (dec₁ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))) ≤ 0 + ε ∧
        (∑ x : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (x i)) *
          ((1 / (n : ℝ)) * ∑ i : Fin n, d₂.dist (x i).2
            (dec₂ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))) ≤ 0 + ε := by
    intro A₁ A₂ hA₁ hA₂ f₁ f₂ dec herr B₁ B₂ h₁ h₂
    let cl₁ : ℕ → Fin A₁ := fun m => ⟨min m (A₁ - 1), by omega⟩
    let cl₂ : ℕ → Fin A₂ := fun m => ⟨min m (A₂ - 1), by omega⟩
    have hcl₁ : ∀ a : Fin A₁, cl₁ a.1 = a := fun a => Fin.ext (by simp only [cl₁]; omega)
    have hcl₂ : ∀ a : Fin A₂, cl₂ a.1 = a := fun a => Fin.ext (by simp only [cl₂]; omega)
    refine ⟨fun x => Fin.castLE h₁ (f₁ x), fun x => Fin.castLE h₂ (f₂ x),
      fun m => (dec (cl₁ m.1.1) (cl₂ m.2.1)).1, fun m => (dec (cl₁ m.1.1) (cl₂ m.2.1)).2, ?_, ?_⟩
    · simp only [Fin.val_castLE, hcl₁, hcl₂]
      have := avgDist_le_slepianWolfError P d₁ hd₁ hd₁' Prod.fst Prod.fst (fun _ _ => rfl)
        f₁ f₂ dec
      linarith
    · simp only [Fin.val_castLE, hcl₁, hcl₂]
      have := avgDist_le_slepianWolfError P d₂ hd₂ hd₂' Prod.snd Prod.snd (fun _ _ => rfl)
        f₁ f₂ dec
      linarith
  exact key _ _ (le_max_left _ _) (le_max_left _ _) f₁ f₂ dec herr _ _ (hle R₁ hR₁) (hle R₂ hR₂)

/-- `I(h(Z); Y | Z) = 0`: a function of the conditioning variable carries no extra information. -/
theorem condMutualInfo_map_fun_cond {ι A B C : Type*} [Fintype ι] [Fintype A] [Fintype B]
    [Fintype C] (P : ProbDist ι) (h : C → A) (fy : ι → B) (fz : ι → C) :
    condMutualInfo (P.map (fun xy => (h (fz xy), fy xy, fz xy))) = 0 := by
  have e1 : (P.map (fun xy => (h (fz xy), fy xy, fz xy))).map (fun t => (t.1, t.2.2)) =
      (P.map fz).map (fun z => (h z, z)) := by rw [map_comp_eq, map_comp_eq]; rfl
  have e2 : (P.map (fun xy => (h (fz xy), fy xy, fz xy))).map (fun t => (t.2.1, t.2.2)) =
      P.map (fun xy => (fy xy, fz xy)) := by rw [map_comp_eq]; rfl
  have e3 : (P.map (fun xy => (h (fz xy), fy xy, fz xy))).map (fun t => t.2.2) = P.map fz := by
    rw [map_comp_eq]; rfl
  have e0 : P.map (fun xy => (h (fz xy), fy xy, fz xy)) =
      (P.map (fun xy => (fy xy, fz xy))).map (fun yz => (h yz.2, yz.1, yz.2)) := by
    rw [map_comp_eq]; rfl
  have i1 : Function.Injective (fun z : C => (h z, z)) := fun a b hab => (Prod.mk.inj hab).2
  have i0 : Function.Injective (fun yz : B × C => (h yz.2, yz.1, yz.2)) := fun a b hab => by
    simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.2.1 hab.2.2
  unfold condMutualInfo; dsimp only
  rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ i1, shannonEntropy_map_of_injective _ i0]
  ring

omit [Fintype Xh₁] [Fintype Xh₂] in
/-- **Slepian–Wolf region ⊆ Berger–Tung inner bound at `D₁ = D₂ = 0`** (single-letter side of
    the lossless corner): take `Uᵢ = Xᵢ` (relabelled into `Fin |Xᵢ|`) and `gᵢ` the inverse
    relabelling; the Berger–Tung rate constraints become `H(X₁|X₂)`, `H(X₂|X₁)`, `H(X₁X₂)`. -/
theorem slepianWolf_subset_bergerTungInnerBound (P : ProbDist (X₁ × X₂))
    (d₁ : Distortion X₁ X₁) (d₂ : Distortion X₂ X₂) (hd₁ : ∀ x, d₁.dist x x = 0)
    (hd₂ : ∀ x, d₂.dist x x = 0) :
    slepianWolfSingleLetter P ⊆ bergerTungInnerBound P d₁ d₂ 0 0 := by
  rintro r ⟨hr₁, hr₂, hc₁, hc₂, hH⟩
  set e₁ := Fintype.equivFin X₁
  set e₂ := Fintype.equivFin X₂
  let f : X₁ × X₂ → X₁ × X₂ × Fin (Fintype.card X₁) × Fin (Fintype.card X₂) :=
    fun xy => (xy.1, xy.2, e₁ xy.1, e₂ xy.2)
  have inj3 : Function.Injective (fun xy : X₁ × X₂ => (xy.1, e₁ xy.1, e₂ xy.2)) :=
    fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (e₂.injective h.2.2)
  have inj3' : Function.Injective (fun xy : X₁ × X₂ => (xy.2, e₂ xy.2, e₁ xy.1)) :=
    fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext (e₁.injective h.2.2) h.1
  have injA : Function.Injective (fun xy : X₁ × X₂ => (xy.1, e₂ xy.2)) :=
    fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (e₂.injective h.2)
  have injB : Function.Injective (fun xy : X₁ × X₂ => (e₁ xy.1, e₂ xy.2)) :=
    fun a b h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (e₁.injective h.1) (e₂.injective h.2)
  have injA' : Function.Injective (fun xy : X₁ × X₂ => (xy.2, e₁ xy.1)) :=
    fun a b h => by simp only [Prod.mk.injEq] at h; exact Prod.ext (e₁.injective h.2) h.1
  have injB' : Function.Injective (fun xy : X₁ × X₂ => (e₂ xy.2, e₁ xy.1)) :=
    fun a b h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (e₁.injective h.2) (e₂.injective h.1)
  have injC : Function.Injective (fun xy : X₁ × X₂ => (xy, (e₁ xy.1, e₂ xy.2))) :=
    fun a b h => (Prod.mk.inj h).1
  have hsnd : shannonEntropy ((P.map Prod.snd).map e₂) = shannonEntropy P.snd := by
    rw [shannonEntropy_map_of_injective _ e₂.injective, map_snd_eq_snd]
  have hfst : shannonEntropy ((P.map Prod.fst).map e₁) = shannonEntropy P.fst := by
    rw [shannonEntropy_map_of_injective _ e₁.injective, map_fst_eq_fst]
  refine ⟨hr₁, hr₂, _, _, P.map f, fun u => e₁.symm u.1, fun u => e₂.symm u.2, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [map_comp_eq]; exact map_id_eq P
  · rw [map_comp_eq]
    exact condMutualInfo_map_fun_cond P e₁ (fun xy => (xy.2, e₂ xy.2)) (fun xy => xy.1)
  · rw [map_comp_eq]
    exact condMutualInfo_map_fun_cond P e₂ (fun xy => (xy.1, e₁ xy.1)) (fun xy => xy.2)
  · rw [← sum_pmf_mul_comp P f (fun t => d₁.dist t.1 (e₁.symm t.2.2.1))]
    simp [f, hd₁]
  · rw [← sum_pmf_mul_comp P f (fun t => d₂.dist t.2.1 (e₂.symm t.2.2.2))]
    simp [f, hd₂]
  · show r.1 ≥ _
    rw [map_comp_eq]
    have e1 : (P.map ((fun t => (t.1, t.2.2.1, t.2.2.2)) ∘ f)).map (fun t => (t.1, t.2.2)) =
        P.map (fun xy => (xy.1, e₂ xy.2)) := by rw [map_comp_eq]; rfl
    have e2 : (P.map ((fun t => (t.1, t.2.2.1, t.2.2.2)) ∘ f)).map (fun t => (t.2.1, t.2.2)) =
        P.map (fun xy => (e₁ xy.1, e₂ xy.2)) := by rw [map_comp_eq]; rfl
    have e3 : (P.map ((fun t => (t.1, t.2.2.1, t.2.2.2)) ∘ f)).map (fun t => t.2.2) =
        (P.map Prod.snd).map e₂ := by rw [map_comp_eq, map_comp_eq]; rfl
    have e0 : P.map ((fun t => (t.1, t.2.2.1, t.2.2.2)) ∘ f) =
        P.map (fun xy => (xy.1, e₁ xy.1, e₂ xy.2)) := rfl
    unfold condMutualInfo; dsimp only
    rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ injA, shannonEntropy_map_of_injective _ injB, shannonEntropy_map_of_injective _ inj3, hsnd]
    unfold condEntropy at hc₁; linarith
  · show r.2 ≥ _
    rw [map_comp_eq]
    have e1 : (P.map ((fun t => (t.2.1, t.2.2.2, t.2.2.1)) ∘ f)).map (fun t => (t.1, t.2.2)) =
        P.map (fun xy => (xy.2, e₁ xy.1)) := by rw [map_comp_eq]; rfl
    have e2 : (P.map ((fun t => (t.2.1, t.2.2.2, t.2.2.1)) ∘ f)).map (fun t => (t.2.1, t.2.2)) =
        P.map (fun xy => (e₂ xy.2, e₁ xy.1)) := by rw [map_comp_eq]; rfl
    have e3 : (P.map ((fun t => (t.2.1, t.2.2.2, t.2.2.1)) ∘ f)).map (fun t => t.2.2) =
        (P.map Prod.fst).map e₁ := by rw [map_comp_eq, map_comp_eq]; rfl
    have e0 : P.map ((fun t => (t.2.1, t.2.2.2, t.2.2.1)) ∘ f) =
        P.map (fun xy => (xy.2, e₂ xy.2, e₁ xy.1)) := rfl
    unfold condMutualInfo; dsimp only
    rw [e1, e2, e3, e0, shannonEntropy_map_of_injective _ injA', shannonEntropy_map_of_injective _ injB', shannonEntropy_map_of_injective _ inj3', hfst]
    unfold condEntropy at hc₂
    rw [shannonEntropy_swap, snd_map_swap] at hc₂
    linarith
  · show r.1 + r.2 ≥ _
    rw [map_comp_eq]
    have e0 : P.map ((fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘ f) =
        P.map (fun xy => (xy, (e₁ xy.1, e₂ xy.2))) := rfl
    have e1 : (P.map (fun xy => (xy, (e₁ xy.1, e₂ xy.2)))).fst = P := by
      rw [← map_fst_eq_fst, map_comp_eq]; exact map_id_eq P
    have e2 : (P.map (fun xy => (xy, (e₁ xy.1, e₂ xy.2)))).snd =
        P.map (fun xy => (e₁ xy.1, e₂ xy.2)) := by rw [← map_snd_eq_snd, map_comp_eq]; rfl
    unfold mutualInfo
    rw [e0, e1, e2, shannonEntropy_map_of_injective _ injB, shannonEntropy_map_of_injective _ injC]
    linarith

omit [Fintype Xh₁] [Fintype Xh₂] in
/-- Hence the Slepian–Wolf region lies in the Berger–Tung closure at `D₁ = D₂ = 0`. -/
theorem slepianWolf_subset_closure (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ X₁)
    (d₂ : Distortion X₂ X₂) (hd₁ : ∀ x, d₁.dist x x = 0) (hd₂ : ∀ x, d₂.dist x x = 0)
    {r : ℝ × ℝ} (hr : r ∈ slepianWolfSingleLetter P) :
    InBergerTungClosure P d₁ d₂ r.1 r.2 0 0 := by
  intro ε hε
  refine ⟨1, fun _ => 1, fun _ => r.1, fun _ => r.2, fun _ => 0, fun _ => 0,
    fun _ => zero_le_one, by simp,
    fun _ => slepianWolf_subset_bergerTungInnerBound P d₁ d₂ hd₁ hd₂ hr, ?_, ?_, ?_, ?_⟩ <;>
    simp <;> linarith

end Operational

/-! ### The doubly symmetric binary source -/

section DSBS

variable {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

theorem dsbs_fst_pmf (b : Bool) : (dsbsDist p hp0 hp1).fst.pmf b = 1 / 2 := by
  cases b <;> simp [ProbDist.fst, dsbsDist] <;> ring

theorem dsbs_snd_pmf (b : Bool) : (dsbsDist p hp0 hp1).snd.pmf b = 1 / 2 := by
  cases b <;> simp [ProbDist.snd, dsbsDist] <;> ring

/-- Expected Hamming distortion of a constant reconstruction of a `Bern(1/2)` bit is `1/2`. -/
theorem half_const_dist {P : ProbDist Bool} (hP : ∀ b, P.pmf b = 1 / 2) (c : Bool) :
    ∑ a : Bool, P.pmf a * binHamming.dist a c = 1 / 2 := by
  cases c <;> simp [binHamming, hP]

/-- **Binary rate–distortion lower bound** (Cover–Thomas Thm. 10.3.1, converse half, via
    Fano's inequality): for a `Bern(1/2)` source under Hamming distortion and `0 ≤ D ≤ 1/2`,
    `R(D) ≥ 1 - h(D)`. -/
theorem one_sub_binaryEntropy_le_rateDistortion {P : ProbDist Bool} (hP : ∀ b, P.pmf b = 1 / 2)
    {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1 / 2) :
    1 - binaryEntropy D ≤ rateDistortion P binHamming D := by
  classical
  have hPb : P = ProbDist.bernoulli (1 / 2) (by norm_num) (by norm_num) :=
    probDist_eq_of_pmf fun b => by cases b <;> (simp [ProbDist.bernoulli, hP]; try norm_num)
  have hH : shannonEntropy P = 1 := by
    rw [hPb, shannonEntropy_bernoulli, binaryEntropy_half]
  unfold rateDistortion
  refine le_csInf ⟨mutualInfo (P.map fun x => (x, x)), P.map fun x => (x, x), ?_, ?_, rfl⟩ ?_
  · rw [← map_fst_eq_fst, map_comp_eq]
    exact probDist_eq_of_pmf fun b => by cases b <;> simp [ProbDist.map]
  · rw [← sum_pmf_mul_comp P (fun x => (x, x)) (fun xy => binHamming.dist xy.1 xy.2)]
    simpa [binHamming] using hD0
  rintro r ⟨Q, hQf, hQd, rfl⟩
  have hpe : estErrorProb Q id = ∑ xy : Bool × Bool, Q.pmf xy * binHamming.dist xy.1 xy.2 := by
    unfold estErrorProb
    refine Finset.sum_congr rfl fun xy _ => ?_
    by_cases h : xy.2 = xy.1
    · simp [h, binHamming]
    · simp [h, binHamming, Ne.symm h]
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

end DSBS

/-! ### Certified facts about the exact objects of `Statement` -/

section StatementFacts

/-- **Left-hand side of `Statement` is a genuine outer-bounded region**: every operationally
    achievable `(R₁, R₂, D₁, D₂)` for `DSBS(p)` with `0 ≤ Dᵢ ≤ 1/2` has
    `R₁ + R₂ ≥ 1 - h(Dᵢ)` for both `i` (cut-set bound + binary rate–distortion converse). -/
theorem achievable_sumRate_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ D₁ D₂ : ℝ}
    (hD₁0 : 0 ≤ D₁) (hD₁1 : D₁ ≤ 1 / 2) (hD₂0 : 0 ≤ D₂) (hD₂1 : D₂ ≤ 1 / 2)
    (h : IsBergerTungAchievable (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ D₁ D₂) :
    1 - binaryEntropy D₁ ≤ R₁ + R₂ ∧ 1 - binaryEntropy D₂ ≤ R₁ + R₂ :=
  ⟨le_trans (one_sub_binaryEntropy_le_rateDistortion (dsbs_fst_pmf hp0 hp1) hD₁0 hD₁1)
      (isBergerTungAchievable_rd_fst_le _ _ _ h),
    le_trans (one_sub_binaryEntropy_le_rateDistortion (dsbs_snd_pmf hp0 hp1) hD₂0 hD₂1)
      (isBergerTungAchievable_rd_snd_le _ _ _ h)⟩

/-- **Right-hand side of `Statement` obeys the same bound**: every point of the time-sharing
    closure of the Berger–Tung inner bound for `DSBS(p)` has `R₁ + R₂ ≥ 1 - h(Dᵢ)`. -/
theorem closure_sumRate_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ D₁ D₂ : ℝ}
    (hD₁0 : 0 ≤ D₁) (hD₁1 : D₁ ≤ 1 / 2) (hD₂0 : 0 ≤ D₂) (hD₂1 : D₂ ≤ 1 / 2)
    (h : InBergerTungClosure (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ D₁ D₂) :
    1 - binaryEntropy D₁ ≤ R₁ + R₂ ∧ 1 - binaryEntropy D₂ ≤ R₁ + R₂ :=
  ⟨le_trans (one_sub_binaryEntropy_le_rateDistortion (dsbs_fst_pmf hp0 hp1) hD₁0 hD₁1)
      (inBergerTungClosure_rd_fst_le _ _ _ h),
    le_trans (one_sub_binaryEntropy_le_rateDistortion (dsbs_snd_pmf hp0 hp1) hD₂0 hD₂1)
      (inBergerTungClosure_rd_snd_le _ _ _ h)⟩

/-- Neither side of the `↔` in `Statement` is trivially true: below `D₁ = 1/2`, zero rates are
    neither achievable nor in the closure. -/
theorem zero_rates_not_achievable {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {D₁ D₂ : ℝ}
    (hD₁0 : 0 ≤ D₁) (hD₁1 : D₁ < 1 / 2) (hD₂0 : 0 ≤ D₂) (hD₂1 : D₂ ≤ 1 / 2) :
    ¬ IsBergerTungAchievable (dsbsDist p hp0 hp1) binHamming binHamming 0 0 D₁ D₂ ∧
    ¬ InBergerTungClosure (dsbsDist p hp0 hp1) binHamming binHamming 0 0 D₁ D₂ := by
  have := binaryEntropy_lt_one hD₁0 hD₁1
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (achievable_sumRate_ge hp0 hp1 hD₁0 hD₁1.le hD₂0 hD₂1 h).1; linarith
  · have := (closure_sumRate_ge hp0 hp1 hD₁0 hD₁1.le hD₂0 hD₂1 h).1; linarith

/-- **Trivial corner, operational side**: at `D₁ = D₂ = 1/2` every nonnegative rate pair is
    achievable (constant reconstructions; no bits needed). -/
theorem achievable_half_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    IsBergerTungAchievable (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ (1 / 2) (1 / 2) := by
  refine ⟨hR₁, hR₂, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  refine ⟨fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩,
    fun _ _ => false, fun _ _ => false, ?_, ?_⟩
  · have h := iid_avg_coord_le (dsbsDist p hp0 hp1) n (fun a => binHamming.dist a.1 false)
      (fun a => binHamming.nonneg _ _)
    have h2 : ∑ a : Bool × Bool, (dsbsDist p hp0 hp1).pmf a * binHamming.dist a.1 false = 1 / 2 := by
      rw [sum_pmf_mul_comp (dsbsDist p hp0 hp1) Prod.fst (fun a => binHamming.dist a false),
        map_fst_eq_fst]
      exact half_const_dist (dsbs_fst_pmf hp0 hp1) false
    simp only at h ⊢; linarith
  · have h := iid_avg_coord_le (dsbsDist p hp0 hp1) n (fun a => binHamming.dist a.2 false)
      (fun a => binHamming.nonneg _ _)
    have h2 : ∑ a : Bool × Bool, (dsbsDist p hp0 hp1).pmf a * binHamming.dist a.2 false = 1 / 2 := by
      rw [sum_pmf_mul_comp (dsbsDist p hp0 hp1) Prod.snd (fun a => binHamming.dist a false),
        map_snd_eq_snd]
      exact half_const_dist (dsbs_snd_pmf hp0 hp1) false
    simp only at h ⊢; linarith

/-- **Trivial corner, single-letter side**: at `D₁ = D₂ = 1/2` every nonnegative rate pair
    lies in the Berger–Tung inner bound (constant auxiliaries `U₁ = U₂ = 0`). -/
theorem mem_bergerTungInnerBound_half_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    (R₁, R₂) ∈ bergerTungInnerBound (dsbsDist p hp0 hp1) binHamming binHamming (1 / 2) (1 / 2) := by
  set P := dsbsDist p hp0 hp1
  let Q : ProbDist (Bool × Bool × Fin 1 × Fin 1) := P.map (fun xy => (xy.1, xy.2, 0, 0))
  have hQP : Q.map (fun t => (t.1, t.2.1)) = P := by
    rw [map_comp_eq]
    refine probDist_eq_of_pmf fun b => ?_
    simp [ProbDist.map]
  have hd : ∀ (f : Bool × Bool → Bool), (∀ b, (P.map f).pmf b = 1 / 2) →
      (∑ t, Q.pmf t * binHamming.dist (f (t.1, t.2.1)) false) = 1 / 2 := by
    intro f hf
    rw [← sum_pmf_mul_comp P (fun xy => (xy.1, xy.2, (0 : Fin 1), (0 : Fin 1)))
      (fun t => binHamming.dist (f (t.1, t.2.1)) false)]
    rw [sum_pmf_mul_comp P f (fun a => binHamming.dist a false)]
    exact half_const_dist hf false
  refine ⟨hR₁, hR₂, 1, 1, Q, fun _ => false, fun _ => false, hQP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_comp_eq]; exact condMutualInfo_map_const_fst P (0 : Fin 1) _ _
  · rw [map_comp_eq]; exact condMutualInfo_map_const_fst P (0 : Fin 1) _ _
  · exact (hd Prod.fst (by rw [map_fst_eq_fst]; exact dsbs_fst_pmf hp0 hp1)).le
  · exact (hd Prod.snd (by rw [map_snd_eq_snd]; exact dsbs_snd_pmf hp0 hp1)).le
  · show R₁ ≥ _
    rw [map_comp_eq]
    have := condMutualInfo_map_const_snd P (0 : Fin 1) (fun xy : Bool × Bool => xy.1)
      (fun _ => (0 : Fin 1))
    exact le_of_eq_of_le this hR₁
  · show R₂ ≥ _
    rw [map_comp_eq]
    have := condMutualInfo_map_const_snd P (0 : Fin 1) (fun xy : Bool × Bool => xy.2)
      (fun _ => (0 : Fin 1))
    exact le_of_eq_of_le this hR₂
  · show R₁ + R₂ ≥ _
    rw [map_comp_eq]
    have := mutualInfo_map_const_snd P (fun xy : Bool × Bool => (xy.1, xy.2)) ((0 : Fin 1), (0 : Fin 1))
    exact le_of_eq_of_le this (by linarith)

/-- ... hence also in the time-sharing closure (the right-hand side of `Statement`). -/
theorem inClosure_half_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    InBergerTungClosure (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ (1 / 2) (1 / 2) := by
  intro ε hε
  refine ⟨1, fun _ => 1, fun _ => R₁, fun _ => R₂, fun _ => 1 / 2, fun _ => 1 / 2,
    fun _ => zero_le_one, by simp, fun _ => mem_bergerTungInnerBound_half_half hp0 hp1 hR₁ hR₂,
    ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

theorem binHamming_diag (x : Bool) : binHamming.dist x x = 0 := by simp [binHamming]

theorem binHamming_le_one (x y : Bool) : binHamming.dist x y ≤ 1 := by
  simp only [binHamming]; split_ifs <;> norm_num

/-- **Slepian–Wolf lossless corner is consistent with the formalization**: every rate pair in
    the interior of the Slepian–Wolf region of `DSBS(p)` (Slepian–Wolf 1973; Cover–Thomas
    Thm. 15.4.1, `slepian_wolf_achievability`) is operationally achievable at
    `D₁ = D₂ = 0` for the `IsBergerTungAchievable` of `Statement`. -/
theorem achievable_lossless_of_slepianWolf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ : ℝ}
    (h1 : condEntropy (dsbsDist p hp0 hp1) < R₁)
    (h2 : condEntropy ((dsbsDist p hp0 hp1).map Prod.swap) < R₂)
    (h12 : shannonEntropy (dsbsDist p hp0 hp1) < R₁ + R₂) :
    IsBergerTungAchievable (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ 0 0 :=
  isBergerTungAchievable_of_slepianWolf _ _ _ binHamming_diag binHamming_le_one binHamming_diag
    binHamming_le_one (slepian_wolf_achievability _ h1 h2 h12)

/-- At the lossless corner the cut-set bound reads `R₁ + R₂ ≥ R_{X₁}(0) ≥ 1 = H(X₁)`. -/
theorem lossless_sumRate_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ : ℝ}
    (h : IsBergerTungAchievable (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ 0 0) :
    1 ≤ R₁ + R₂ := by
  have := (achievable_sumRate_ge hp0 hp1 le_rfl (by norm_num) le_rfl (by norm_num) h).1
  have h0 : binaryEntropy 0 = 0 := by simp [binaryEntropy, negPLogP, log2]
  linarith

/-- **The Slepian–Wolf lossless corner lies on both sides of `Statement`**: every interior
    Slepian–Wolf pair of `DSBS(p)` is operationally achievable at `D₁ = D₂ = 0` and lies in the
    Berger–Tung closure at `D₁ = D₂ = 0`. -/
theorem lossless_corner_both {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R₁ R₂ : ℝ}
    (h1 : condEntropy (dsbsDist p hp0 hp1) < R₁)
    (h2 : condEntropy ((dsbsDist p hp0 hp1).map Prod.swap) < R₂)
    (h12 : shannonEntropy (dsbsDist p hp0 hp1) < R₁ + R₂) :
    IsBergerTungAchievable (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ 0 0 ∧
    InBergerTungClosure (dsbsDist p hp0 hp1) binHamming binHamming R₁ R₂ 0 0 :=
  ⟨achievable_lossless_of_slepianWolf hp0 hp1 h1 h2 h12,
    slepianWolf_subset_closure _ _ _ binHamming_diag binHamming_diag (r := (R₁, R₂))
      ⟨le_of_lt (lt_of_le_of_lt (condEntropy_nonneg _) h1),
        le_of_lt (lt_of_le_of_lt (condEntropy_nonneg _) h2), h1.le, h2.le, h12.le⟩⟩

end StatementFacts

end InfoTheory.Known.Certificates.MultiterminalSourceCoding
