import InfoTheory.Problems.WiretapChannelCompoundSecrecy
import InfoTheory.Known
import InfoTheory.Bridge
import InfoTheory.Known.Certificates.DmInterferenceChannelCapacity

/-!
# Certificate for `InfoTheory.Problems.WiretapChannelCompoundSecrecy`

The frozen statement asks whether, for every finite family `W : Fin kS → WiretapChannel X Y Z`
(`kS ≥ 1`), the regularised compound secrecy capacity `compoundSecrecyCapacity W` equals the
single-letter Liang–Kramer–Poor–Shamai bound `lkpsSingleLetterBound W`.

## Certified (about exactly these objects)
* `compoundWiretapRateN_le` — the `n`-letter secrecy expression satisfies
  `sup_V [min_s I(V; Y_sⁿ) - max_s I(V; Z_sⁿ)] ≤ n log₂ |Y|` (`max_s I(V; Z_sⁿ) ≥ 0` and
  `I(V; Y_sⁿ) ≤ H(Y_sⁿ)`).
* `compoundSecrecyCapacity_le_log2_card` — hence the regularised capacity is `≤ log₂ |Y|`.
* `lkpsSingleLetterBound_le_log2_card` — the single-letter bound is `≤ log₂ |Y|`
  (`I(V; Y_s | U) ≤ log₂ |Y|`).
So both sides of the statement are suprema of sets that are bounded above (they are not the
junk value of an unbounded `sSup`), and both are `≤ log₂ |Y|`.
* **Regression (one state, lower half; passes).**  `wiretapSecrecyCapacity_le_lkps_one` : for a
  single channel (`kS = 1`), `Core.wiretapSecrecyCapacity W ≤ lkpsSingleLetterBound (fun _ => W)`
  — every Csiszár–Körner term `I(V; Y) - I(V; Z)` is an LKPS term with `U` constant
  (`ck_term_le_lkps_one`; the singleton `sInf`/`sSup` over `Fin 1` collapse and
  `I(V; Y | const) = I(V; Y)`).  The reverse inequality (removing `U` by averaging), which would
  give the known one-state equality with Csiszár–Körner, is not certified.

## Not certified
* Lower bounds (`≥ 0`, attained by constant `U, V`): they need explicit construction of the
  joint laws with their normalisation proofs; not done here.
* `lkpsSingleLetterBound W ≤ compoundSecrecyCapacity W` (achievability, Liang–Kramer–Poor–Shamai
  2009) and the degraded-case equality: these need wiretap coding, not in the library.
* No statement-level conclusion: the problem is open.

Sources: Liang–Kramer–Poor–Shamai, IEEE Trans. IT 2009; Bjelaković–Boche–Sommerfeld, 2013.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.WiretapChannelCompoundSecrecy

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.WiretapChannelCompoundSecrecy
open InfoTheory.Known.Certificates.DmInterferenceChannelCapacity (condMutualInfo_le_log2_card
  log2_card_pow)

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

lemma log2_card_nonneg (α : Type*) [Fintype α] : 0 ≤ log2 (Fintype.card α : ℝ) := by
  unfold log2
  exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos one_lt_two).le

/-- The `n`-letter secrecy expression is at most `n log₂ |Y|`. -/
theorem compoundWiretapRateN_le [Nonempty Y] {kS : ℕ} (hkS : 0 < kS)
    (W : Fin kS → WiretapChannel X Y Z) (n : ℕ) :
    compoundWiretapRateN W n ≤ n * log2 (Fintype.card Y) := by
  unfold compoundWiretapRateN
  refine Real.sSup_le (fun r hr => ?_) (mul_nonneg (Nat.cast_nonneg _) (log2_card_nonneg Y))
  obtain ⟨kV, Pvx, joint, -, rfl⟩ := hr
  have hmax : 0 ≤ sSup { b : ℝ | ∃ s : Fin kS,
      b = mutualInfo ((joint s).map (fun t => (t.1, fun i => (t.2.2 i).2))) } :=
    Real.sSup_nonneg fun b ⟨s, hb⟩ => hb ▸ mutualInfo_nonneg _
  have hmin : sInf { a : ℝ | ∃ s : Fin kS,
      a = mutualInfo ((joint s).map (fun t => (t.1, fun i => (t.2.2 i).1))) } ≤
      n * log2 (Fintype.card Y) := by
    refine csInf_le_of_le ⟨0, fun a ⟨s, ha⟩ => ha ▸ mutualInfo_nonneg _⟩ ⟨⟨0, hkS⟩, rfl⟩ ?_
    have := (mutualInfo_le_entropy_snd _).trans (shannonEntropy_le_log2_card
      ((((joint ⟨0, hkS⟩).map (fun t => (t.1, fun i => (t.2.2 i).1)))).snd))
    rwa [log2_card_pow] at this
  linarith

/-- **Upper bound on the regularised compound secrecy capacity**: `≤ log₂ |Y|`. -/
theorem compoundSecrecyCapacity_le_log2_card [Nonempty Y] {kS : ℕ} (hkS : 0 < kS)
    (W : Fin kS → WiretapChannel X Y Z) :
    compoundSecrecyCapacity W ≤ log2 (Fintype.card Y) := by
  unfold compoundSecrecyCapacity
  refine Real.sSup_le (fun r hr => ?_) (log2_card_nonneg Y)
  obtain ⟨n, hn, rfl⟩ := hr
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnr]
  linarith [compoundWiretapRateN_le hkS W n]

/-- **Upper bound on the LKPS single-letter bound**: `≤ log₂ |Y|`. -/
theorem lkpsSingleLetterBound_le_log2_card [Nonempty Y] {kS : ℕ} (hkS : 0 < kS)
    (W : Fin kS → WiretapChannel X Y Z) :
    lkpsSingleLetterBound W ≤ log2 (Fintype.card Y) := by
  unfold lkpsSingleLetterBound
  refine Real.sSup_le (fun r hr => ?_) (log2_card_nonneg Y)
  obtain ⟨kU, kV, Puvx, joint, -, rfl⟩ := hr
  have hmax : 0 ≤ sSup { b : ℝ | ∃ s : Fin kS,
      b = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.2, t.1))) } :=
    Real.sSup_nonneg fun b ⟨s, hb⟩ => hb ▸ condMutualInfo_nonneg _
  have hmin : sInf { a : ℝ | ∃ s : Fin kS,
      a = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.1, t.1))) } ≤
      log2 (Fintype.card Y) :=
    csInf_le_of_le ⟨0, fun a ⟨s, ha⟩ => ha ▸ condMutualInfo_nonneg _⟩ ⟨⟨0, hkS⟩, rfl⟩
      (condMutualInfo_le_log2_card _)
  linarith

/-! ### Regression: one state reduces to Csiszár–Körner (lower half) -/

lemma map_pmf_of_injective {α β : Type*} [Fintype α] [Fintype β] {f : α → β}
    (hf : Function.Injective f) (P : ProbDist α) (a : α) : (P.map f).pmf (f a) = P.pmf a := by
  classical
  unfold ProbDist.map
  dsimp only
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hf.ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The LKPS set is bounded above by `log₂ |Y|` (as in `lkpsSingleLetterBound_le_log2_card`). -/
theorem lkps_bddAbove [Nonempty Y] {kS : ℕ} (hkS : 0 < kS) (W : Fin kS → WiretapChannel X Y Z) :
    BddAbove { r : ℝ | ∃ (kU kV : ℕ) (Puvx : ProbDist (Fin kU × Fin kV × X))
      (joint : Fin kS → ProbDist (Fin kU × Fin kV × X × (Y × Z))),
      (∀ (s : Fin kS) (t : Fin kU × Fin kV × X × (Y × Z)),
        (joint s).pmf t = Puvx.pmf (t.1, t.2.1, t.2.2.1) * (W s).trans t.2.2.1 t.2.2.2) ∧
      let minY := sInf { a : ℝ | ∃ (s : Fin kS),
        a = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.1, t.1))) }
      let maxZ := sSup { b : ℝ | ∃ (s : Fin kS),
        b = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.2, t.1))) }
      r = minY - maxZ } := by
  refine ⟨log2 (Fintype.card Y), fun r hr => ?_⟩
  obtain ⟨kU, kV, Puvx, joint, -, rfl⟩ := hr
  have hmax : 0 ≤ sSup { b : ℝ | ∃ s : Fin kS,
      b = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.2, t.1))) } :=
    Real.sSup_nonneg fun b ⟨s, hb⟩ => hb ▸ condMutualInfo_nonneg _
  have hmin : sInf { a : ℝ | ∃ s : Fin kS,
      a = condMutualInfo ((joint s).map (fun t => (t.2.1, t.2.2.2.1, t.1))) } ≤
      log2 (Fintype.card Y) :=
    csInf_le_of_le ⟨0, fun a ⟨s, ha⟩ => ha ▸ condMutualInfo_nonneg _⟩ ⟨⟨0, hkS⟩, rfl⟩
      (condMutualInfo_le_log2_card _)
  linarith

/-- Every Csiszár–Körner term `I(V; Y) - I(V; Z)` (for a joint law `P_{VX} W`) is a term of the
    LKPS set of the one-state family, with `U` constant. -/
theorem ck_term_le_lkps_one [Nonempty Y] (W : WiretapChannel X Y Z) {kV : ℕ}
    (Pvx : ProbDist (Fin kV × X)) (joint : ProbDist (Fin kV × X × Y × Z))
    (hj : ∀ t, joint.pmf t = Pvx.pmf (t.1, t.2.1) * W.trans t.2.1 (t.2.2.1, t.2.2.2)) :
    mutualInfo (joint.map (fun t => (t.1, t.2.2.1))) -
        mutualInfo (joint.map (fun t => (t.1, t.2.2.2))) ≤
      lkpsSingleLetterBound (fun _ : Fin 1 => W) := by
  set φ : Fin kV × X × Y × Z → Fin 1 × Fin kV × X × (Y × Z) :=
    fun s => (0, s.1, s.2.1, (s.2.2.1, s.2.2.2)) with hφ
  have hφi : Function.Injective φ := by
    intro a b h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨-, h1, h2, h3, h4⟩ := h
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  set ψ : Fin kV × X → Fin 1 × Fin kV × X := fun s => (0, s.1, s.2) with hψ
  have hψi : Function.Injective ψ := by
    intro a b h
    simp only [hψ, Prod.mk.injEq] at h
    exact Prod.ext h.2.1 h.2.2
  set J := joint.map φ
  set Puvx := Pvx.map ψ
  have hJ : ∀ t : Fin 1 × Fin kV × X × (Y × Z),
      J.pmf t = Puvx.pmf (t.1, t.2.1, t.2.2.1) * W.trans t.2.2.1 t.2.2.2 := by
    rintro ⟨u, v, x, y, z⟩
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    have e1 : ((0 : Fin 1), v, x, (y, z)) = φ (v, x, y, z) := rfl
    have e2 : ((0 : Fin 1), v, x) = ψ (v, x) := rfl
    simp only
    rw [e1, map_pmf_of_injective hφi, e2, map_pmf_of_injective hψi, hj]
  have hY : condMutualInfo (J.map (fun t => (t.2.1, t.2.2.2.1, t.1))) =
      mutualInfo (joint.map (fun t => (t.1, t.2.2.1))) := by
    have : J.map (fun t => (t.2.1, t.2.2.2.1, t.1)) =
        (joint.map (fun t => (t.1, t.2.2.1))).map (fun ab => (ab.1, ab.2, (0 : Fin 1))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [this, condMutualInfo_map_const]
  have hZ : condMutualInfo (J.map (fun t => (t.2.1, t.2.2.2.2, t.1))) =
      mutualInfo (joint.map (fun t => (t.1, t.2.2.2))) := by
    have : J.map (fun t => (t.2.1, t.2.2.2.2, t.1)) =
        (joint.map (fun t => (t.1, t.2.2.2))).map (fun ab => (ab.1, ab.2, (0 : Fin 1))) := by
      rw [map_comp_eq, map_comp_eq]; rfl
    rw [this, condMutualInfo_map_const]
  have hsetY : { a : ℝ | ∃ (s : Fin 1),
      a = condMutualInfo (((fun _ : Fin 1 => J) s).map (fun t => (t.2.1, t.2.2.2.1, t.1))) } =
      {mutualInfo (joint.map (fun t => (t.1, t.2.2.1)))} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hY]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  have hsetZ : { b : ℝ | ∃ (s : Fin 1),
      b = condMutualInfo (((fun _ : Fin 1 => J) s).map (fun t => (t.2.1, t.2.2.2.2, t.1))) } =
      {mutualInfo (joint.map (fun t => (t.1, t.2.2.2)))} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hZ]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  unfold lkpsSingleLetterBound
  refine le_csSup (lkps_bddAbove Nat.one_pos _) ⟨1, kV, Puvx, fun _ => J, fun _ t => hJ t, ?_⟩
  dsimp only
  rw [hsetY, hsetZ, csInf_singleton, csSup_singleton]

/-- **Regression (one state ⇒ Csiszár–Körner, lower half).**  For a single wiretap channel
    (`kS = 1`), the frozen LKPS single-letter bound is at least the Csiszár–Körner secrecy
    capacity `max_{V - X - YZ} [I(V; Y) - I(V; Z)]` (`Core.wiretapSecrecyCapacity`): take `U`
    constant.  (Equality — the known one-state answer — also needs `U` to be removable by
    averaging, not certified here.) -/
theorem wiretapSecrecyCapacity_le_lkps_one [Nonempty X] [Nonempty Y]
    (W : WiretapChannel X Y Z) :
    wiretapSecrecyCapacity W ≤ lkpsSingleLetterBound (fun _ : Fin 1 => W) := by
  unfold wiretapSecrecyCapacity
  refine csSup_le ⟨_, 1, (ProbDist.uniform (α := Fin 1)).prod ProbDist.uniform, rfl⟩ ?_
  rintro r ⟨kV, Pvx, rfl⟩
  exact ck_term_le_lkps_one W Pvx _ (fun _ => rfl)

end InfoTheory.Known.Certificates.WiretapChannelCompoundSecrecy
