import InfoTheory.Problems.SdpiKlVsChisqEquality
import InfoTheory.Bridge.Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds

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

* **the 3-letter reversible source** `exQ = (1/4, 1/4, 1/2)`, `exW` (eigenvalues `1, 3/10, 1/5`)
  of the 2026-11-27 counterexample attempt: `ex_reversible`, `sdpiChiSqAt_ex` (`s_{χ²} = 9/100`),
  `sdpiKLAt_ex_ge` (`s_KL ≥ 9/100`, via `P_z → Q`), `ex_not_ribbon` (the ribbon fails at
  `(p, q) = (127/100, 4)`, where `(p - 1)/(q - 1) = 9/100`), and the conditional
  `not_statement_of_sdpiKLAt_ex_le : sdpiKLAt exQ exW ≤ 9/100 → ¬ Statement`. The hypothesis of
  that reduction (a global inequality `D(PW ‖ Q) ≤ (9/100) D(P ‖ Q)` over the whole simplex,
  see `sdpiKLAt_ex_le_of`) is **not** proved here, so the problem is not settled.

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

/-! ### A reversible 3-letter source with `s_KL ≥ s_{χ²} = 9/100` and a ribbon violation

Objects of `attempts/sdpi-kl-vs-chisq-equality/2026-11-27-antigravity-counterexample.md`. -/

noncomputable def exQ : ProbDist (Fin 3) where
  pmf := ![1/4, 1/4, 1/2]
  nonneg := by intro a; fin_cases a <;> norm_num
  sum_one := by simp [Fin.sum_univ_three]; norm_num

noncomputable def exW : DMC (Fin 3) (Fin 3) where
  trans := ![![9/20, 3/20, 2/5], ![3/20, 9/20, 2/5], ![1/5, 1/5, 3/5]]
  nonneg := by intro x y; fin_cases x <;> fin_cases y <;> norm_num
  sum_one := by intro x; fin_cases x <;> simp [Fin.sum_univ_three] <;> norm_num

theorem exQ_pos : ∀ x, 0 < exQ.pmf x := by
  intro x; fin_cases x <;> simp [exQ]

theorem ex_reversible : ∀ x y : Fin 3, exQ.pmf x * exW.trans x y = exQ.pmf y * exW.trans y x := by
  intro x y; fin_cases x <;> fin_cases y <;> simp [exQ, exW] <;> norm_num

theorem ex_out (P : ProbDist (Fin 3)) :
    (exW.joint P).snd.pmf 0 = P.pmf 0 * (9/20) + P.pmf 1 * (3/20) + P.pmf 2 * (1/5) ∧
    (exW.joint P).snd.pmf 1 = P.pmf 0 * (3/20) + P.pmf 1 * (9/20) + P.pmf 2 * (1/5) ∧
    (exW.joint P).snd.pmf 2 = P.pmf 0 * (2/5) + P.pmf 1 * (2/5) + P.pmf 2 * (3/5) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [out_pmf, Fin.sum_univ_three] <;> simp [exW]

theorem ex_outQ : ∀ y, (exW.joint exQ).snd.pmf y = exQ.pmf y := by
  obtain ⟨h0, h1, h2⟩ := ex_out exQ
  intro y; fin_cases y
  · rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, h0]; simp [exQ]; norm_num
  · rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, h1]; simp [exQ]; norm_num
  · rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, h2]; simp [exQ]; norm_num

theorem chiSq_exQ (P : ProbDist (Fin 3)) : chiSqDivergence P exQ =
    (P.pmf 0 - 1/4)^2 / (1/4) + (P.pmf 1 - 1/4)^2 / (1/4) + (P.pmf 2 - 1/2)^2 / (1/2) := by
  simp [chiSqDivergence, Fin.sum_univ_three, exQ]; norm_num

theorem chiSq_ex_out (P : ProbDist (Fin 3)) :
    chiSqDivergence (exW.joint P).snd (exW.joint exQ).snd ≤
      9/100 * chiSqDivergence P exQ := by
  rw [chiSq_congr (fun _ => rfl) ex_outQ, chiSq_exQ, chiSq_exQ]
  obtain ⟨h0, h1, h2⟩ := ex_out P
  rw [h0, h1, h2]
  have hs := P.sum_one
  rw [Fin.sum_univ_three] at hs
  have hc : P.pmf 2 = 1 - P.pmf 0 - P.pmf 1 := by linarith
  rw [hc]
  nlinarith [sq_nonneg (P.pmf 0 + P.pmf 1 - 1/2)]

noncomputable def exP : ProbDist (Fin 3) where
  pmf := ![1/2, 0, 1/2]
  nonneg := by intro a; fin_cases a <;> norm_num
  sum_one := by simp [Fin.sum_univ_three]; norm_num

theorem sdpiChiSqAt_ex : sdpiChiSqAt exQ exW = 9/100 := by
  have hpos : 0 < chiSqDivergence exP exQ := by
    rw [chiSq_exQ]; simp [exP]; norm_num
  apply le_antisymm
  · apply Real.sSup_le _ (by norm_num)
    rintro r ⟨P, _, hP, rfl⟩
    rw [div_le_iff₀ hP]; exact chiSq_ex_out P
  · apply le_csSup ⟨1, ?_⟩
    · refine ⟨exP, fun a h => absurd h (exQ_pos a).ne', hpos, ?_⟩
      rw [eq_div_iff hpos.ne', chiSq_congr (fun _ => rfl) ex_outQ, chiSq_exQ, chiSq_exQ]
      obtain ⟨h0, h1, h2⟩ := ex_out exP
      rw [h0, h1, h2]; simp [exP]; norm_num
    · rintro r ⟨P, _, hP, rfl⟩
      rw [div_le_one hP]; exact chiSq_channel_le _ P _ exQ_pos


noncomputable def exRm : Fin 3 → Fin 3 → ℝ :=
  ![![2/200, 4/200, 3/200], ![6/200, 111/200, 27/200], ![4/200, 24/200, 19/200]]

noncomputable def exR : ProbDist (Fin 3 × Fin 3) where
  pmf := fun ij => exRm ij.1 ij.2
  nonneg := by intro ij; rcases ij with ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [exRm] <;> norm_num
  sum_one := by simp [Fintype.sum_prod_type, Fin.sum_univ_three, exRm]; norm_num

theorem exKL_fst : klDivergence exR.fst (exW.joint exQ).fst =
    9/200 * log2 (9/50) + 144/200 * log2 (72/25) + 47/200 * log2 (47/100) := by
  simp [klDivergence, ProbDist.fst, Fin.sum_univ_three, exR, exRm, DMC.joint, exQ, exW]
  norm_num

theorem exKL_snd : klDivergence exR.snd (exW.joint exQ).snd =
    3/50 * log2 (6/25) + 139/200 * log2 (139/50) + 49/200 * log2 (49/100) := by
  simp [klDivergence, ProbDist.snd, Fin.sum_univ_three, exR, exRm, DMC.joint, exQ, exW]
  norm_num

theorem exKL_joint : klDivergence exR (exW.joint exQ) =
    1 / 100 * log2 (4 / 45) + 1 / 50 * log2 (8 / 15) + 3 / 200 * log2 (3 / 20) +
        (3 / 100 * log2 (4 / 5) + 111 / 200 * log2 (74 / 15) + 27 / 200 * log2 (27 / 20)) +
      (1 / 50 * log2 (1 / 5) + 3 / 25 * log2 (6 / 5) + 19 / 200 * log2 (19 / 60)) := by
  simp [klDivergence, Fintype.sum_prod_type, Fin.sum_univ_three, exR, exRm, DMC.joint, exQ, exW]
  norm_num

theorem log_series_mem (y : ℝ) (n : ℕ) (hy : |1 - y| < 1) :
    -(∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1)) - |1 - y| ^ (n + 1) / (1 - |1 - y|) ≤
      Real.log y ∧
    Real.log y ≤
      -(∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1)) + |1 - y| ^ (n + 1) / (1 - |1 - y|) := by
  have h := Real.abs_log_sub_add_sum_range_le hy n
  rw [sub_sub_cancel] at h
  constructor <;> linarith [(abs_le.1 h).1, (abs_le.1 h).2]

theorem exLog2_bd0 : (-2.4739315 : ℝ) ≤ log2 (9/50 : ℝ) ∧ log2 (9/50 : ℝ) ≤ -2.4739308 := by
    have hx : Real.log (9/50 : ℝ) = -2 * Real.log 2 + Real.log (18/25 : ℝ) := by
      rw [show (9/50 : ℝ) = (18/25 : ℝ) / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.328504069 : ℝ) ≤ Real.log (18/25 : ℝ) ∧ Real.log (18/25 : ℝ) ≤ -0.328504064 := by
      obtain ⟨h1, h2⟩ := log_series_mem (18/25 : ℝ) 18 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd1 : (1.5260685 : ℝ) ≤ log2 (72/25 : ℝ) ∧ log2 (72/25 : ℝ) ≤ 1.5260692 := by
    have hx : Real.log (72/25 : ℝ) = 2 * Real.log 2 + Real.log (18/25 : ℝ) := by
      rw [show (72/25 : ℝ) = 2 ^ 2 * (18/25 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.328504069 : ℝ) ≤ Real.log (18/25 : ℝ) ∧ Real.log (18/25 : ℝ) ≤ -0.328504064 := by
      obtain ⟨h1, h2⟩ := log_series_mem (18/25 : ℝ) 18 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd2 : (-1.0892677 : ℝ) ≤ log2 (47/100 : ℝ) ∧ log2 (47/100 : ℝ) ≤ -1.089267 := by
    have hx : Real.log (47/100 : ℝ) = -1 * Real.log 2 + Real.log (47/50 : ℝ) := by
      rw [show (47/100 : ℝ) = (47/50 : ℝ) / 2 ^ 1 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.061875406 : ℝ) ≤ Real.log (47/50 : ℝ) ∧ Real.log (47/50 : ℝ) ≤ -0.061875401 := by
      obtain ⟨h1, h2⟩ := log_series_mem (47/50 : ℝ) 8 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd3 : (-2.058894 : ℝ) ≤ log2 (6/25 : ℝ) ∧ log2 (6/25 : ℝ) ≤ -2.0588933 := by
    have hx : Real.log (6/25 : ℝ) = -2 * Real.log 2 + Real.log (24/25 : ℝ) := by
      rw [show (6/25 : ℝ) = (24/25 : ℝ) / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.040821997 : ℝ) ≤ Real.log (24/25 : ℝ) ∧ Real.log (24/25 : ℝ) ≤ -0.040821992 := by
      obtain ⟨h1, h2⟩ := log_series_mem (24/25 : ℝ) 7 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd4 : (1.4750845 : ℝ) ≤ log2 (139/50 : ℝ) ∧ log2 (139/50 : ℝ) ≤ 1.4750852 := by
    have hx : Real.log (139/50 : ℝ) = 1 * Real.log 2 + Real.log (139/100 : ℝ) := by
      rw [show (139/50 : ℝ) = 2 ^ 1 * (139/100 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.329303745 : ℝ) ≤ Real.log (139/100 : ℝ) ∧ Real.log (139/100 : ℝ) ≤ 0.32930375 := by
      obtain ⟨h1, h2⟩ := log_series_mem (139/100 : ℝ) 24 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd5 : (-1.0291467 : ℝ) ≤ log2 (49/100 : ℝ) ∧ log2 (49/100 : ℝ) ≤ -1.029146 := by
    have hx : Real.log (49/100 : ℝ) = -1 * Real.log 2 + Real.log (49/50 : ℝ) := by
      rw [show (49/100 : ℝ) = (49/50 : ℝ) / 2 ^ 1 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.02020271 : ℝ) ≤ Real.log (49/50 : ℝ) ∧ Real.log (49/50 : ℝ) ≤ -0.020202705 := by
      obtain ⟨h1, h2⟩ := log_series_mem (49/50 : ℝ) 5 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd6 : (-3.4918534 : ℝ) ≤ log2 (4/45 : ℝ) ∧ log2 (4/45 : ℝ) ≤ -3.4918527 := by
    have hx : Real.log (4/45 : ℝ) = -3 * Real.log 2 + Real.log (32/45 : ℝ) := by
      rw [show (4/45 : ℝ) = (32/45 : ℝ) / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.340926589 : ℝ) ≤ Real.log (32/45 : ℝ) ∧ Real.log (32/45 : ℝ) ≤ -0.340926584 := by
      obtain ⟨h1, h2⟩ := log_series_mem (32/45 : ℝ) 18 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd7 : (-0.9068909 : ℝ) ≤ log2 (8/15 : ℝ) ∧ log2 (8/15 : ℝ) ≤ -0.9068902 := by
    have hx : Real.log (8/15 : ℝ) = -1 * Real.log 2 + Real.log (16/15 : ℝ) := by
      rw [show (8/15 : ℝ) = (16/15 : ℝ) / 2 ^ 1 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.064538519 : ℝ) ≤ Real.log (16/15 : ℝ) ∧ Real.log (16/15 : ℝ) ≤ 0.064538524 := by
      obtain ⟨h1, h2⟩ := log_series_mem (16/15 : ℝ) 8 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd8 : (-2.7369659 : ℝ) ≤ log2 (3/20 : ℝ) ∧ log2 (3/20 : ℝ) ≤ -2.7369652 := by
    have hx : Real.log (3/20 : ℝ) = -3 * Real.log 2 + Real.log (6/5 : ℝ) := by
      rw [show (3/20 : ℝ) = (6/5 : ℝ) / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.182321554 : ℝ) ≤ Real.log (6/5 : ℝ) ∧ Real.log (6/5 : ℝ) ≤ 0.182321559 := by
      obtain ⟨h1, h2⟩ := log_series_mem (6/5 : ℝ) 14 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd9 : (-0.3219284 : ℝ) ≤ log2 (4/5 : ℝ) ∧ log2 (4/5 : ℝ) ≤ -0.3219277 := by
    have hx : Real.log (4/5 : ℝ) = 0 * Real.log 2 + Real.log (4/5 : ℝ) := by
      rw [show (4/5 : ℝ) = 2 ^ 0 * (4/5 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.223143554 : ℝ) ≤ Real.log (4/5 : ℝ) ∧ Real.log (4/5 : ℝ) ≤ -0.223143549 := by
      obtain ⟨h1, h2⟩ := log_series_mem (4/5 : ℝ) 14 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd10 : (2.3025624 : ℝ) ≤ log2 (74/15 : ℝ) ∧ log2 (74/15 : ℝ) ≤ 2.3025631 := by
    have hx : Real.log (74/15 : ℝ) = 2 * Real.log 2 + Real.log (37/30 : ℝ) := by
      rw [show (74/15 : ℝ) = 2 ^ 2 * (37/30 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.209720528 : ℝ) ≤ Real.log (37/30 : ℝ) ∧ Real.log (37/30 : ℝ) ≤ 0.209720533 := by
      obtain ⟨h1, h2⟩ := log_series_mem (37/30 : ℝ) 16 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd11 : (0.4329591 : ℝ) ≤ log2 (27/20 : ℝ) ∧ log2 (27/20 : ℝ) ≤ 0.4329598 := by
    have hx : Real.log (27/20 : ℝ) = 0 * Real.log 2 + Real.log (27/20 : ℝ) := by
      rw [show (27/20 : ℝ) = 2 ^ 0 * (27/20 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.30010459 : ℝ) ≤ Real.log (27/20 : ℝ) ∧ Real.log (27/20 : ℝ) ≤ 0.300104595 := by
      obtain ⟨h1, h2⟩ := log_series_mem (27/20 : ℝ) 22 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd12 : (-2.3219284 : ℝ) ≤ log2 (1/5 : ℝ) ∧ log2 (1/5 : ℝ) ≤ -2.3219277 := by
    have hx : Real.log (1/5 : ℝ) = -2 * Real.log 2 + Real.log (4/5 : ℝ) := by
      rw [show (1/5 : ℝ) = (4/5 : ℝ) / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (-0.223143554 : ℝ) ≤ Real.log (4/5 : ℝ) ∧ Real.log (4/5 : ℝ) ≤ -0.223143549 := by
      obtain ⟨h1, h2⟩ := log_series_mem (4/5 : ℝ) 14 (by norm_num [abs_of_pos])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_pos]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_pos]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd13 : (0.2630341 : ℝ) ≤ log2 (6/5 : ℝ) ∧ log2 (6/5 : ℝ) ≤ 0.2630348 := by
    have hx : Real.log (6/5 : ℝ) = 0 * Real.log 2 + Real.log (6/5 : ℝ) := by
      rw [show (6/5 : ℝ) = 2 ^ 0 * (6/5 : ℝ) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.182321554 : ℝ) ≤ Real.log (6/5 : ℝ) ∧ Real.log (6/5 : ℝ) ≤ 0.182321559 := by
      obtain ⟨h1, h2⟩ := log_series_mem (6/5 : ℝ) 14 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem exLog2_bd14 : (-1.6589634 : ℝ) ≤ log2 (19/60 : ℝ) ∧ log2 (19/60 : ℝ) ≤ -1.6589627 := by
    have hx : Real.log (19/60 : ℝ) = -2 * Real.log 2 + Real.log (19/15 : ℝ) := by
      rw [show (19/60 : ℝ) = (19/15 : ℝ) / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    have hy : (0.236388776 : ℝ) ≤ Real.log (19/15 : ℝ) ∧ Real.log (19/15 : ℝ) ≤ 0.236388781 := by
      obtain ⟨h1, h2⟩ := log_series_mem (19/15 : ℝ) 17 (by norm_num [abs_of_neg])
      constructor
      · refine le_trans ?_ h1; norm_num [Finset.sum_range_succ, abs_of_neg]
      · refine le_trans h2 ?_; norm_num [Finset.sum_range_succ, abs_of_neg]
    have l1 := Real.log_two_gt_d9
    have l2 := Real.log_two_lt_d9
    have hl2 : (0 : ℝ) < Real.log 2 := by linarith
    unfold log2
    constructor
    · rw [le_div_iff₀ hl2]; linarith [hy.1, hy.2]
    · rw [div_le_iff₀ hl2]; linarith [hy.1, hy.2]

theorem ex_joint_pos : ∀ ij, 0 < (exW.joint exQ).pmf ij := by
  rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [DMC.joint, exQ, exW]

theorem ex_not_ribbon : ¬ inNairRibbon (exW.joint exQ) (127/100) 4 := by
  rintro ⟨-, -, h⟩
  have key := h exR (fun ij hij => absurd hij (ex_joint_pos ij).ne')
  rw [exKL_fst, exKL_snd, exKL_joint] at key
  linarith [exLog2_bd0.1, exLog2_bd1.1, exLog2_bd2.1, exLog2_bd3.1, exLog2_bd4.1, exLog2_bd5.1,
    exLog2_bd6.2, exLog2_bd7.2, exLog2_bd8.2, exLog2_bd9.2, exLog2_bd10.2, exLog2_bd11.2, exLog2_bd12.2,
    exLog2_bd13.2, exLog2_bd14.2]

noncomputable def gSym (w : ℝ) : ℝ := (1 + w) * Real.log (1 + w) + (1 - w) * Real.log (1 - w)

theorem log_one_sub_near_sq (x : ℝ) (hx : |x| < 1) :
    |Real.log (1 - x) + x + x ^ 2 / 2| ≤ |x| ^ 3 / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  convert h using 2; ring

theorem gSym_near (w : ℝ) (h0 : 0 < w) (h1 : w < 1) :
    |gSym w - w ^ 2| ≤ 2 * (w ^ 3 / (1 - w)) := by
  have e1 := log_one_sub_near_sq (-w) (by rw [abs_neg, abs_of_pos h0]; exact h1)
  have e2 := log_one_sub_near_sq w (by rw [abs_of_pos h0]; exact h1)
  rw [abs_neg, abs_of_pos h0, sub_neg_eq_add] at e1
  rw [abs_of_pos h0] at e2
  set E := w ^ 3 / (1 - w)
  have hE : 0 ≤ E := div_nonneg (by positivity) (by linarith)
  have hg : gSym w - w ^ 2 = (1 + w) * (Real.log (1 + w) - w + w ^ 2 / 2) +
      (1 - w) * (Real.log (1 - w) + w + w ^ 2 / 2) := by unfold gSym; ring
  rw [hg]
  have a1 := abs_le.1 e1
  have a2 := abs_le.1 e2
  have hA : (1 + w) * (Real.log (1 + w) - w + w ^ 2 / 2) ≤ (1 + w) * E :=
    mul_le_mul_of_nonneg_left (by have := a1.2; ring_nf at this ⊢; linarith) (by linarith)
  have hA' : -((1 + w) * E) ≤ (1 + w) * (Real.log (1 + w) - w + w ^ 2 / 2) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (by have := a1.1; ring_nf at this ⊢; linarith) (by linarith)
  have hB : (1 - w) * (Real.log (1 - w) + w + w ^ 2 / 2) ≤ (1 - w) * E :=
    mul_le_mul_of_nonneg_left a2.2 (by linarith)
  have hB' : -((1 - w) * E) ≤ (1 - w) * (Real.log (1 - w) + w + w ^ 2 / 2) := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left a2.1 (by linarith)
  rw [abs_le]; constructor <;> nlinarith


/-- The tilted inputs `P_z = ((1+z)/4, (1-z)/4, 1/2)`, `|z| ≤ 1`. -/
noncomputable def Pz (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) : ProbDist (Fin 3) where
  pmf := ![(1 + z) / 4, (1 - z) / 4, 1 / 2]
  nonneg := by intro a; fin_cases a <;> simp <;> linarith
  sum_one := by simp [Fin.sum_univ_three]; ring

theorem kl_Pz (z : ℝ) (h0 : 0 < z) (h1 : z < 1) :
    klDivergence (Pz z h0.le h1.le) exQ = gSym z / (4 * Real.log 2) := by
  have ha : ¬ ((1 + z) / 4 ≤ 0) := by intro h; linarith
  have hb : ¬ ((1 - z) / 4 ≤ 0) := by intro h; linarith
  have p0 : (Pz z h0.le h1.le).pmf 0 = (1 + z) / 4 := rfl
  have p1 : (Pz z h0.le h1.le).pmf 1 = (1 - z) / 4 := rfl
  have p2 : (Pz z h0.le h1.le).pmf 2 = 1 / 2 := rfl
  have q0 : exQ.pmf 0 = 1 / 4 := rfl
  have q1 : exQ.pmf 1 = 1 / 4 := rfl
  have q2 : exQ.pmf 2 = 1 / 2 := rfl
  unfold klDivergence
  rw [Fin.sum_univ_three, p0, p1, p2, q0, q1, q2, if_neg ha, if_neg hb,
    if_neg (by norm_num : ¬ ((1 / 2 : ℝ) ≤ 0)), show (1 + z) / 4 / (1 / 4) = 1 + z by ring,
    show (1 - z) / 4 / (1 / 4) = 1 - z by ring, show (1 / 2 : ℝ) / (1 / 2) = 1 by norm_num]
  unfold log2 gSym
  rw [Real.log_one]
  ring

theorem out_Pz (z : ℝ) (h0 : 0 < z) (h1 : z < 1) :
    ∀ y, (exW.joint (Pz z h0.le h1.le)).snd.pmf y =
      (Pz (3 / 10 * z) (by positivity) (by linarith)).pmf y := by
  obtain ⟨e0, e1, e2⟩ := ex_out (Pz z h0.le h1.le)
  intro y; fin_cases y
  · rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, e0]; simp [Pz]; ring
  · rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, e1]; simp [Pz]; ring
  · rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, e2]; simp [Pz]; ring

theorem ratio_Pz (z : ℝ) (h0 : 0 < z) (h1 : z ≤ 1 / 10) :
    9 / 100 - 3 / 10 * z ≤
      klDivergence (exW.joint (Pz z h0.le (by linarith))).snd (exW.joint exQ).snd /
        klDivergence (Pz z h0.le (by linarith)) exQ := by
  have hz1 : z < 1 := by linarith
  rw [kl_congr (out_Pz z h0 hz1) ex_outQ, kl_Pz z h0 hz1,
    kl_Pz (3 / 10 * z) (by positivity) (by linarith)]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have gA := abs_le.1 (gSym_near z h0 hz1)
  have gB := abs_le.1 (gSym_near (3 / 10 * z) (by positivity) (by linarith))
  have hE1 : z ^ 3 / (1 - z) ≤ 10 / 9 * z ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos h0 3]
  have hE2 : (3 / 10 * z) ^ 3 / (1 - 3 / 10 * z) ≤ 10 / 9 * (3 / 10 * z) ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos h0 3]
  have gpos : 0 < gSym z := by nlinarith [pow_pos h0 3]
  rw [div_div_div_cancel_right₀ (by positivity), le_div_iff₀ gpos]
  nlinarith [pow_pos h0 3, pow_pos h0 4, mul_pos h0 h0]

theorem sdpiKLAt_ex_ge : 9 / 100 ≤ sdpiKLAt exQ exW := by
  have hbdd : BddAbove { r : ℝ | ∃ (P : ProbDist (Fin 3)),
      AbsCont P exQ ∧ klDivergence P exQ > 0 ∧
      r = klDivergence (exW.joint P).snd (exW.joint exQ).snd / klDivergence P exQ } := by
    refine ⟨1, ?_⟩
    rintro r ⟨P, hPQ, hpos, rfl⟩
    rw [div_le_one hpos]
    exact InfoTheory.Bridge.klDivergence_channel_le _ P _ hPQ
  by_contra hlt
  rw [not_le] at hlt
  set c := sdpiKLAt exQ exW
  set z := min (1 / 10) (9 / 100 - c) with hz
  have hz0 : 0 < z := lt_min (by norm_num) (by linarith)
  have hz1 : z ≤ 1 / 10 := min_le_left _ _
  have hz2 : z ≤ 9 / 100 - c := min_le_right _ _
  have hz1' : z ≤ 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hklpos : 0 < klDivergence (Pz z hz0.le hz1') exQ := by
    rw [kl_Pz z hz0 (by linarith)]
    have := abs_le.1 (gSym_near z hz0 (by linarith))
    have hE : z ^ 3 / (1 - z) ≤ 10 / 9 * z ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hz0 3]
    apply div_pos _ (by positivity)
    nlinarith [pow_pos hz0 3]
  have hmem := le_csSup hbdd ⟨Pz z hz0.le hz1', fun a h => absurd h (exQ_pos a).ne', hklpos, rfl⟩
  have hr := ratio_Pz z hz0 hz1
  change _ ≤ c at hmem
  linarith


/-- The KL constant is bounded by `9/100` as soon as the single global inequality
    `D(PW ‖ Q) ≤ (9/100) D(P ‖ Q)` holds for every input `P` (claim 2 of the 2026-11-27
    counterexample attempt, which is only sketched there). -/
theorem sdpiKLAt_ex_le_of (h : ∀ P : ProbDist (Fin 3),
    klDivergence (exW.joint P).snd (exW.joint exQ).snd ≤ 9 / 100 * klDivergence P exQ) :
    sdpiKLAt exQ exW ≤ 9 / 100 := by
  apply Real.sSup_le _ (by norm_num)
  rintro r ⟨P, _, hP, rfl⟩
  rw [div_le_iff₀ hP]; exact h P

/-- **Reduction.** The frozen `Statement` is refuted by the reversible 3-letter source
    `(exQ, exW)` at `(p, q) = (127/100, 4)` *provided* `s_KL(exQ, exW) ≤ 9/100`. Everything else
    (`s_{χ²} = 9/100`, `s_KL ≥ 9/100`, reversibility, the ribbon violation) is proved above.
    This does not settle the problem: the hypothesis is open in this file. -/
theorem not_statement_of_sdpiKLAt_ex_le (h : sdpiKLAt exQ exW ≤ 9 / 100) : ¬ Statement := by
  intro hS
  have heq : sdpiKLAt exQ exW = sdpiChiSqAt exQ exW := by
    rw [sdpiChiSqAt_ex]; exact le_antisymm h sdpiKLAt_ex_ge
  exact ex_not_ribbon (hS 3 3 exQ exQ exW exW (by norm_num) (by norm_num) exQ_pos exQ_pos
    ex_reversible heq heq (127 / 100) 4 (by norm_num) (by norm_num)
    (by rw [sdpiChiSqAt_ex]; norm_num))

end InfoTheory.Known.Certificates.SdpiKlVsChisqEquality
