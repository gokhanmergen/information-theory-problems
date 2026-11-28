import InfoTheory.Problems.SdpiKlVsChisqEquality
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.SdpiKlVsChisqEquality`

The frozen statement asks whether two-sided equality of the input-dependent KL and `χ²` SDPI
constants (`sdpiKLAt QX W = sdpiChiSqAt QX W` and the same for the reverse channel) forces the
hypercontractivity ribbon (Nair's KL form, `inNairRibbon`) to be the Bonami–Beckner region
`(p - 1)/(q - 1) ≥ sdpiChiSqAt QX W`.

Certified here, about the exact objects of `Statement` (no junk values):
* `absCont_out` — `P ≪ Q` implies `PW ≪ QW`, so no `log 0` junk in the KL numerator;
* `sdpiKLAt_nonneg`, `sdpiKLAt_le_one` — `0 ≤ s_KL(Q, W) ≤ 1` (KL data processing), so the
  `sSup` is over a bounded set;
* `chiSq_channel_le`, `sdpiChiSqAt_nonneg`, `sdpiChiSqAt_le_one` — `χ²` data processing
  (Cauchy–Schwarz) and `0 ≤ s_{χ²}(Q, W) ≤ 1` for full-support `Q`;
* **regressions** (known exact values):
  - `sdpiChiSqAt_bsc_uniform` — `BSC(p)` with uniform input: `s_{χ²} = (1 - 2p)²`
    (`ρ_m = |1 - 2p|`);
  - `sdpiKLAt_identity`, `sdpiChiSqAt_identity` — noiseless channel on `Fin k`, `k ≥ 2`,
    uniform input: both constants equal `1`;
  - `sdpiKLAt_const`, `sdpiChiSqAt_const` — a channel with identical rows: both equal `0`;
  - `nair_diag` — every `(p, p)`, `p ≥ 1`, is in every ribbon;
  - `identity_nairRibbon_iff` — for the noiseless uniform source, the ribbon is exactly the
    Bonami–Beckner region with `ρ² = 1`, i.e. `p = q`;
  - `identity_hypotheses`, `statement_instance_identity` — the noiseless source satisfies
    every hypothesis of `Statement` (two-sided equality `1 = 1`) and its conclusion.

Not certified: `s_KL(Unif, BSC(p)) = (1 - 2p)²` for `0 < p < 1/2` (Ahlswede–Gács; needs the
binary KL contraction inequality), the general inequality `s_{χ²} ≤ s_KL`, the channel-level
equality `η_KL = η_{χ²}`, and the DSBS ribbon for `0 < p < 1/2`. These facts do not settle
`Statement`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.SdpiKlVsChisqEquality

open InfoTheory InfoTheory.Problems.SdpiKlVsChisqEquality

/-! ### Helpers -/

theorem kl_congr {α : Type*} [Fintype α] {P P' Q Q' : ProbDist α}
    (hP : ∀ a, P.pmf a = P'.pmf a) (hQ : ∀ a, Q.pmf a = Q'.pmf a) :
    klDivergence P Q = klDivergence P' Q' := by
  unfold klDivergence; simp only [hP, hQ]

theorem chiSq_congr {α : Type*} [Fintype α] {P P' Q Q' : ProbDist α}
    (hP : ∀ a, P.pmf a = P'.pmf a) (hQ : ∀ a, Q.pmf a = Q'.pmf a) :
    chiSqDivergence P Q = chiSqDivergence P' Q' := by
  unfold chiSqDivergence; simp only [hP, hQ]

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

theorem out_pmf {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) (P : ProbDist α) (y : β) :
    (W.joint P).snd.pmf y = ∑ x : α, P.pmf x * W.trans x y := rfl

/-! ### No junk: absolute continuity and boundedness -/

theorem absCont_out {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) (P Q : ProbDist α)
    (h : AbsCont P Q) : AbsCont (W.joint P).snd (W.joint Q).snd := by
  intro y hy
  rw [out_pmf] at hy ⊢
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => mul_nonneg (Q.nonneg x) (W.nonneg x y))).1 hy
  refine Finset.sum_eq_zero (fun x hx => ?_)
  rcases mul_eq_zero.1 (hz x hx) with h0 | h0
  · rw [h x h0, zero_mul]
  · rw [h0, mul_zero]

theorem sdpiKLAt_nonneg {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist α) (W : DMC α β) :
    0 ≤ sdpiKLAt Q W := by
  apply Real.sSup_nonneg
  rintro r ⟨P, hPQ, hpos, rfl⟩
  exact div_nonneg (InfoTheory.Bridge.klDivergence_nonneg _ _ (absCont_out W P Q hPQ))
    hpos.le

theorem sdpiKLAt_le_one {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist α) (W : DMC α β) :
    sdpiKLAt Q W ≤ 1 := by
  apply Real.sSup_le _ zero_le_one
  rintro r ⟨P, hPQ, hpos, rfl⟩
  rw [div_le_one hpos]
  exact InfoTheory.Bridge.klDivergence_channel_le W P Q hPQ

/-- `χ²` data processing for a full-support reference input (Cauchy–Schwarz). -/
theorem chiSq_channel_le {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β)
    (P Q : ProbDist α) (hQ : ∀ x, 0 < Q.pmf x) :
    chiSqDivergence (W.joint P).snd (W.joint Q).snd ≤ chiSqDivergence P Q := by
  unfold chiSqDivergence
  have hrhs : (∑ x : α, if Q.pmf x ≤ 0 then 0 else (P.pmf x - Q.pmf x) ^ 2 / Q.pmf x) =
      ∑ y : β, ∑ x : α, (P.pmf x - Q.pmf x) ^ 2 / Q.pmf x * W.trans x y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [if_neg (not_le.2 (hQ x)), ← Finset.mul_sum, W.sum_one, mul_one]
  rw [hrhs]
  refine Finset.sum_le_sum (fun y _ => ?_)
  have hR : 0 ≤ ∑ x : α, (P.pmf x - Q.pmf x) ^ 2 / Q.pmf x * W.trans x y :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (div_nonneg (sq_nonneg _) (hQ x).le) (W.nonneg x y))
  split_ifs with hy
  · exact hR
  · have hpos : 0 < (W.joint Q).snd.pmf y := lt_of_not_ge hy
    rw [div_le_iff₀ hpos]
    have hdiff : (W.joint P).snd.pmf y - (W.joint Q).snd.pmf y =
        ∑ x : α, (P.pmf x - Q.pmf x) * W.trans x y := by
      rw [out_pmf, out_pmf, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => by ring)
    rw [hdiff, out_pmf]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun x _ => mul_nonneg (div_nonneg (sq_nonneg _) (hQ x).le) (W.nonneg x y))
      (fun x _ => mul_nonneg (Q.nonneg x) (W.nonneg x y)) (fun x _ => ?_)
    have hq := (hQ x).ne'
    apply le_of_eq
    field_simp

theorem sdpiChiSqAt_nonneg {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist α)
    (W : DMC α β) : 0 ≤ sdpiChiSqAt Q W := by
  apply Real.sSup_nonneg
  rintro r ⟨P, _, hpos, rfl⟩
  refine div_nonneg (Finset.sum_nonneg (fun y _ => ?_)) hpos.le
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) (lt_of_not_ge h).le

theorem sdpiChiSqAt_le_one {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist α)
    (W : DMC α β) (hQ : ∀ x, 0 < Q.pmf x) : sdpiChiSqAt Q W ≤ 1 := by
  apply Real.sSup_le _ zero_le_one
  rintro r ⟨P, _, hpos, rfl⟩
  rw [div_le_one hpos]
  exact chiSq_channel_le W P Q hQ

/-! ### Regression: `BSC(p)` with uniform input, `s_{χ²} = (1 - 2p)²` -/

theorem sdpiChiSqAt_bsc_uniform (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    sdpiChiSqAt (ProbDist.uniform : ProbDist Bool) (bsc p h0 h1) = (1 - 2 * p) ^ 2 := by
  have hratio : ∀ P : ProbDist Bool,
      chiSqDivergence ((bsc p h0 h1).joint P).snd ((bsc p h0 h1).joint ProbDist.uniform).snd =
        (1 - 2 * p) ^ 2 * chiSqDivergence P ProbDist.uniform := by
    intro P
    have hs := P.sum_one
    simp only [Fintype.sum_bool] at hs
    have hf : P.pmf false = 1 - P.pmf true := by linarith
    have hu : ∀ x, (ProbDist.uniform : ProbDist Bool).pmf x = 1 / 2 := by
      intro x; simp [ProbDist.uniform]
    have hU : ∀ y, ((bsc p h0 h1).joint ProbDist.uniform).snd.pmf y = 1 / 2 := by
      intro y; rw [out_pmf, Fintype.sum_bool, hu, hu]
      cases y <;> simp only [bsc] <;> norm_num <;> ring
    have hT : ((bsc p h0 h1).joint P).snd.pmf true =
        P.pmf true * (1 - p) + P.pmf false * p := by
      rw [out_pmf, Fintype.sum_bool]; simp only [bsc]; norm_num
    have hF : ((bsc p h0 h1).joint P).snd.pmf false =
        P.pmf false * (1 - p) + P.pmf true * p := by
      rw [out_pmf, Fintype.sum_bool]; simp only [bsc]; norm_num; ring
    simp only [chiSqDivergence, Fintype.sum_bool, hU, hT, hF, hu,
      if_neg (show ¬ ((1 : ℝ) / 2 ≤ 0) by norm_num)]
    rw [hf]
    ring
  have hset : { r : ℝ | ∃ (P : ProbDist Bool),
      AbsCont P ProbDist.uniform ∧ chiSqDivergence P ProbDist.uniform > 0 ∧
      r = chiSqDivergence ((bsc p h0 h1).joint P).snd
        ((bsc p h0 h1).joint ProbDist.uniform).snd / chiSqDivergence P ProbDist.uniform } =
      {(1 - 2 * p) ^ 2} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, _, hpos, rfl⟩
      rw [hratio, mul_div_assoc, div_self hpos.ne', mul_one]
    · rintro rfl
      refine ⟨pointMass true, InfoTheory.Bridge.absCont_uniform _, ?_, ?_⟩
      · simp [chiSqDivergence, pointMass, ProbDist.uniform]; norm_num
      · have hpos : chiSqDivergence (pointMass true) ProbDist.uniform ≠ 0 := by
          simp [chiSqDivergence, pointMass, ProbDist.uniform]; norm_num
        rw [hratio, mul_div_assoc, div_self hpos, mul_one]
  unfold sdpiChiSqAt
  rw [hset, csSup_singleton]

/-! ### Regression: the noiseless channel (`ρ_m = 1`) -/

/-- The noiseless channel on `α`. -/
def idDMC (α : Type*) [Fintype α] [DecidableEq α] : DMC α α where
  trans := fun x y => if x = y then 1 else 0
  nonneg := fun x y => by split_ifs <;> norm_num
  sum_one := fun x => by simp

theorem idDMC_out {α : Type*} [Fintype α] [DecidableEq α] (P : ProbDist α) (y : α) :
    ((idDMC α).joint P).snd.pmf y = P.pmf y := by
  rw [out_pmf]; simp [idDMC]

theorem uniform_pos (k : ℕ) [Nonempty (Fin k)] (x : Fin k) :
    0 < (ProbDist.uniform : ProbDist (Fin k)).pmf x := by
  simp only [ProbDist.uniform]
  have : 0 < Fintype.card (Fin k) := Fintype.card_pos
  positivity

theorem kl_pointMass_uniform_pos (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] :
    0 < klDivergence (pointMass (⟨0, by omega⟩ : Fin k)) ProbDist.uniform := by
  rw [kl_of_indicator _ _ ⟨0, by omega⟩ (fun _ => rfl)]
  simp only [ProbDist.uniform, Fintype.card_fin, one_div, inv_inv]
  exact log2_pos_of_one_lt (by exact_mod_cast (show 1 < k by omega))

theorem chiSq_pointMass_uniform_pos (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] :
    0 < chiSqDivergence (pointMass (⟨0, by omega⟩ : Fin k)) ProbDist.uniform := by
  unfold chiSqDivergence
  have hterm : ∀ x : Fin k, 0 ≤ (if (ProbDist.uniform : ProbDist (Fin k)).pmf x ≤ 0 then 0
      else ((pointMass (⟨0, by omega⟩ : Fin k)).pmf x -
        (ProbDist.uniform : ProbDist (Fin k)).pmf x) ^ 2 /
        (ProbDist.uniform : ProbDist (Fin k)).pmf x) := by
    intro x; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (sq_nonneg _) (lt_of_not_ge h).le
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun x _ => hterm x)
    (Finset.mem_univ (⟨0, by omega⟩ : Fin k)))
  rw [if_neg (not_le.2 (uniform_pos k _))]
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  apply div_pos _ (uniform_pos k _)
  have h1 : (pointMass (⟨0, by omega⟩ : Fin k)).pmf ⟨0, by omega⟩ = 1 := by simp [pointMass]
  rw [h1]
  simp only [ProbDist.uniform, Fintype.card_fin]
  have : (1 : ℝ) / k < 1 := by rw [div_lt_one (by linarith)]; exact hk1
  exact pow_pos (by linarith) 2

theorem sdpiKLAt_identity (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] :
    sdpiKLAt (ProbDist.uniform : ProbDist (Fin k)) (idDMC (Fin k)) = 1 := by
  apply le_antisymm (sdpiKLAt_le_one _ _)
  apply le_csSup ⟨1, ?_⟩
  · refine ⟨pointMass ⟨0, by omega⟩, InfoTheory.Bridge.absCont_uniform _,
      kl_pointMass_uniform_pos k hk, ?_⟩
    rw [kl_congr (idDMC_out _) (idDMC_out _), div_self (kl_pointMass_uniform_pos k hk).ne']
  · rintro r ⟨P, hPQ, hpos, rfl⟩
    rw [div_le_one hpos]
    exact InfoTheory.Bridge.klDivergence_channel_le _ P _ hPQ

theorem sdpiChiSqAt_identity (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] :
    sdpiChiSqAt (ProbDist.uniform : ProbDist (Fin k)) (idDMC (Fin k)) = 1 := by
  apply le_antisymm (sdpiChiSqAt_le_one _ _ (uniform_pos k))
  apply le_csSup ⟨1, ?_⟩
  · refine ⟨pointMass ⟨0, by omega⟩, InfoTheory.Bridge.absCont_uniform _,
      chiSq_pointMass_uniform_pos k hk, ?_⟩
    rw [chiSq_congr (idDMC_out _) (idDMC_out _),
      div_self (chiSq_pointMass_uniform_pos k hk).ne']
  · rintro r ⟨P, _, hpos, rfl⟩
    rw [div_le_one hpos]
    exact chiSq_channel_le _ P _ (uniform_pos k)

/-! ### Regression: a channel with identical rows (`ρ_m = 0`) -/

/-- The channel whose every row is `R` (output independent of input). -/
def constDMC {α β : Type*} [Fintype α] [Fintype β] (R : ProbDist β) : DMC α β where
  trans := fun _ y => R.pmf y
  nonneg := fun _ y => R.nonneg y
  sum_one := fun _ => R.sum_one

theorem constDMC_out {α β : Type*} [Fintype α] [Fintype β] (R : ProbDist β) (P : ProbDist α)
    (y : β) : ((constDMC R : DMC α β).joint P).snd.pmf y = R.pmf y := by
  rw [out_pmf]; simp only [constDMC]; rw [← Finset.sum_mul, P.sum_one, one_mul]

theorem sdpiKLAt_const {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist α)
    (R : ProbDist β) : sdpiKLAt Q (constDMC R : DMC α β) = 0 := by
  apply le_antisymm _ (sdpiKLAt_nonneg _ _)
  apply Real.sSup_nonpos
  rintro r ⟨P, _, _, rfl⟩
  rw [kl_congr (constDMC_out R P) (constDMC_out R Q)]
  unfold klDivergence
  rw [Finset.sum_eq_zero (fun y _ => ?_), zero_div]
  split_ifs with h
  · rfl
  · rw [div_self (ne_of_gt (lt_of_not_ge h)), log2, Real.log_one, zero_div, mul_zero]

theorem sdpiChiSqAt_const {α β : Type*} [Fintype α] [Fintype β] (Q : ProbDist α)
    (R : ProbDist β) : sdpiChiSqAt Q (constDMC R : DMC α β) = 0 := by
  apply le_antisymm _ (sdpiChiSqAt_nonneg _ _)
  apply Real.sSup_nonpos
  rintro r ⟨P, _, _, rfl⟩
  rw [chiSq_congr (constDMC_out R P) (constDMC_out R Q)]
  unfold chiSqDivergence
  simp

/-! ### The Nair ribbon -/

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

theorem nair_diag {X Y : Type*} [Fintype X] [Fintype Y] (P : ProbDist (X × Y)) {p : ℝ}
    (hp : 1 ≤ p) : inNairRibbon P p p := by
  refine ⟨hp, le_rfl, fun Q hQ => ?_⟩
  have h1 : klDivergence Q.fst P.fst ≤ klDivergence Q P := by
    rw [kl_congr (fst_pmf_eq_map Q) (fst_pmf_eq_map P)]
    exact InfoTheory.Bridge.klDivergence_map_le Prod.fst Q P hQ
  have h2 : klDivergence Q.snd P.snd ≤ klDivergence Q P := by
    rw [kl_congr (snd_pmf_eq_map Q) (snd_pmf_eq_map P)]
    exact InfoTheory.Bridge.klDivergence_map_le Prod.snd Q P hQ
  have hp0 : 0 ≤ 1 / p := by positivity
  have hp1 : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hp
  have e1 := mul_le_mul_of_nonneg_left h1 hp0
  have e2 := mul_le_mul_of_nonneg_left h2 hp1
  nlinarith

theorem identity_joint_pmf (k : ℕ) [Nonempty (Fin k)] (x y : Fin k) :
    ((idDMC (Fin k)).joint ProbDist.uniform).pmf (x, y) = if x = y then 1 / (k : ℝ) else 0 := by
  simp only [DMC.joint, idDMC, ProbDist.uniform, Fintype.card_fin]
  split_ifs <;> simp

theorem identity_nairRibbon_iff (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] (p q : ℝ) :
    inNairRibbon ((idDMC (Fin k)).joint ProbDist.uniform) p q ↔ 1 ≤ p ∧ p = q := by
  constructor
  · rintro ⟨hp, hpq, h⟩
    refine ⟨hp, ?_⟩
    by_contra hne
    have hlt : p < q := lt_of_le_of_ne hpq hne
    set a : Fin k := ⟨0, by omega⟩
    let Q : ProbDist (Fin k × Fin k) := pointMass (a, a)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hQ : AbsCont Q ((idDMC (Fin k)).joint ProbDist.uniform) := by
      intro xy hxy
      show (if xy = (a, a) then (1 : ℝ) else 0) = 0
      split_ifs with hx
      · subst hx; rw [identity_joint_pmf] at hxy; simp at hxy; omega
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
    have hfst : ((idDMC (Fin k)).joint ProbDist.uniform).fst.pmf a = 1 / (k : ℝ) := by
      simp only [ProbDist.fst, identity_joint_pmf]; rw [Finset.sum_ite_eq]; simp
    have hsnd : ((idDMC (Fin k)).joint ProbDist.uniform).snd.pmf a = 1 / (k : ℝ) := by
      simp only [ProbDist.snd, identity_joint_pmf]; rw [Finset.sum_ite_eq']; simp
    have k1 : klDivergence Q.fst ((idDMC (Fin k)).joint ProbDist.uniform).fst = log2 k := by
      rw [kl_of_indicator _ _ a hQ1, hfst]; simp
    have k2 : klDivergence Q.snd ((idDMC (Fin k)).joint ProbDist.uniform).snd = log2 k := by
      rw [kl_of_indicator _ _ a hQ2, hsnd]; simp
    have k3 : klDivergence Q ((idDMC (Fin k)).joint ProbDist.uniform) = log2 k := by
      rw [kl_of_indicator _ _ (a, a) (fun _ => rfl), identity_joint_pmf]; simp
    have hL : 0 < log2 (k : ℝ) :=
      log2_pos_of_one_lt (by exact_mod_cast (show 1 < k by omega))
    have key := h Q hQ
    rw [k1, k2, k3] at key
    have hp0 : 0 < p := by linarith
    have : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp0 hlt
    nlinarith
  · rintro ⟨hp, rfl⟩
    exact nair_diag _ hp

/-- The noiseless uniform source satisfies every hypothesis of `Statement` with `W = Wrev = id`,
    including two-sided KL/`χ²` equality (`1 = 1`). -/
theorem identity_hypotheses (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] :
    (∀ x : Fin k, 0 < (ProbDist.uniform : ProbDist (Fin k)).pmf x) ∧
    (∀ x y : Fin k, (ProbDist.uniform : ProbDist (Fin k)).pmf x * (idDMC (Fin k)).trans x y =
      (ProbDist.uniform : ProbDist (Fin k)).pmf y * (idDMC (Fin k)).trans y x) ∧
    sdpiKLAt (ProbDist.uniform : ProbDist (Fin k)) (idDMC (Fin k)) =
      sdpiChiSqAt (ProbDist.uniform : ProbDist (Fin k)) (idDMC (Fin k)) := by
  refine ⟨uniform_pos k, fun x y => ?_, by rw [sdpiKLAt_identity k hk, sdpiChiSqAt_identity k hk]⟩
  simp only [idDMC, ProbDist.uniform]
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- The conclusion of `Statement` holds for the noiseless uniform source. -/
theorem statement_instance_identity (k : ℕ) (hk : 2 ≤ k) [Nonempty (Fin k)] (p q : ℝ)
    (hp : 1 < p) (hpq : p ≤ q)
    (h : sdpiChiSqAt (ProbDist.uniform : ProbDist (Fin k)) (idDMC (Fin k)) ≤ (p - 1) / (q - 1)) :
    inNairRibbon ((idDMC (Fin k)).joint ProbDist.uniform) p q := by
  rw [sdpiChiSqAt_identity k hk] at h
  refine (identity_nairRibbon_iff k hk p q).2 ⟨hp.le, ?_⟩
  by_contra hne
  have hlt : p < q := lt_of_le_of_ne hpq hne
  rw [le_div_iff₀ (by linarith)] at h
  linarith

end InfoTheory.Known.Certificates.SdpiKlVsChisqEquality
