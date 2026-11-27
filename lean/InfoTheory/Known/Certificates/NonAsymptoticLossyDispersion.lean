import InfoTheory.Problems.NonAsymptoticLossyDispersion
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.NonAsymptoticLossyDispersion`

The frozen statement asks for a second-order (dispersion) expansion of the
finite-blocklength Wyner–Ziv rate `wynerZivFiniteRate` around `wynerZivRate` at interior
distortion levels.

## Certified (about exactly these objects)
* `wynerZivRate_nonneg`, `wynerZivRate_le_of_admissible`, `interior_wellDefined` — `R_WZ(D)` is
  nonnegative, bounded by `I(X; U | Y)` for every admissible test channel, and under
  `IsInteriorDistortion` its defining set is nonempty (so it is a genuine infimum, `> 0`).
* `wynerZivFiniteRate_nonneg` — `R_WZ(n, D, ε) ≥ 0`.
* `wynerZivFiniteRate_eq_zero_of_one_le` — sanity check of the finite-blocklength definition:
  for `ε ≥ 1` a single codeword suffices and the rate is `0`.

## Not certified
* Any first- or second-order asymptotics (Wyner–Ziv coding theorem, Kostina–Verdú 2012,
  Watanabe–Kuzuoka–Tan 2015): need Wyner–Ziv achievability and a Berry–Esseen theorem, not
  in `Bridge`. Note: for a constant side-information alphabet (`kY = 1`) the problem reduces
  to point-to-point lossy coding, whose dispersion is known (Kostina–Verdú 2012); not
  formalized here.
* Properties of `stdNormalQuantile` (not needed for well-definedness).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.NonAsymptoticLossyDispersion

open InfoTheory InfoTheory.Bridge InfoTheory.Problems.NonAsymptoticLossyDispersion

variable {X Y Xhat : Type*} [Fintype X] [Fintype Y] [Fintype Xhat]

/-- `R_WZ(D) ≥ 0` (conditional mutual information is nonnegative). -/
theorem wynerZivRate_nonneg (P : ProbDist (X × Y)) (d : Distortion X Xhat) (D : ℝ) :
    0 ≤ wynerZivRate P d D := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨kU, Q, g, -, -, -, -, rfl⟩
  exact condMutualInfo_nonneg _

/-- The Wyner–Ziv set is bounded below, and nonempty at every interior distortion level, so
    under the hypothesis `IsInteriorDistortion` of `Statement`, `R_WZ(D)` is a genuine infimum
    attained-or-approached by actual test channels (in particular it is `≤ I(X; U | Y)` for
    every admissible `(U, g)`). -/
theorem wynerZivRate_le_of_admissible (P : ProbDist (X × Y)) (d : Distortion X Xhat) {D : ℝ}
    {kU : ℕ} (Q : ProbDist (X × Y × Fin kU)) (g : Fin kU × Y → Xhat) (hk : 0 < kU)
    (hQ : Q.map (fun t => (t.1, t.2.1)) = P)
    (hM : condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0)
    (hd : (∑ t : X × Y × Fin kU, Q.pmf t * d.dist t.1 (g (t.2.2, t.2.1))) ≤ D) :
    wynerZivRate P d D ≤ condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) :=
  csInf_le ⟨0, by rintro r ⟨kU, Q, g, -, -, -, -, rfl⟩; exact condMutualInfo_nonneg _⟩
    ⟨kU, Q, g, hk, hQ, hM, hd, rfl⟩

/-- Under `IsInteriorDistortion`, the infimum defining `R_WZ(D)` is over a nonempty set
    bounded below, and `0 < R_WZ(D) ≤ I(X; U | Y)` for the interior witness. -/
theorem interior_wellDefined (P : ProbDist (X × Y)) (d : Distortion X Xhat) {D : ℝ}
    (h : IsInteriorDistortion P d D) :
    0 < wynerZivRate P d D ∧ ∃ (kU : ℕ) (Q : ProbDist (X × Y × Fin kU)),
      wynerZivRate P d D ≤ condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) := by
  obtain ⟨hpos, kU, Q, g, hk, hQ, hM, hd⟩ := h
  exact ⟨hpos, kU, Q, wynerZivRate_le_of_admissible P d Q g hk hQ hM hd.le⟩

/-- `R_WZ(n, D, ε) ≥ 0`: every element `log₂ M / n` (with `M ≥ 1`) is nonnegative. -/
theorem wynerZivFiniteRate_nonneg (P : ProbDist (X × Y)) (d : Distortion X Xhat) (n : ℕ)
    (D ε : ℝ) : 0 ≤ wynerZivFiniteRate P d n D ε := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨M, enc, dec, hM, -, rfl⟩
  refine div_nonneg ?_ (Nat.cast_nonneg n)
  unfold log2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hM)) (Real.log_pos one_lt_two).le

/-- For `ε ≥ 1` the excess-distortion constraint is vacuous and a single codeword suffices:
    `R_WZ(n, D, ε) = 0` (sanity check of the finite-blocklength definition; `Statement` only
    uses `ε < 1`). -/
theorem wynerZivFiniteRate_eq_zero_of_one_le [Nonempty Xhat] (P : ProbDist (X × Y))
    (d : Distortion X Xhat) (n : ℕ) (D : ℝ) {ε : ℝ} (hε : 1 ≤ ε) :
    wynerZivFiniteRate P d n D ε = 0 := by
  classical
  refine le_antisymm ?_ (wynerZivFiniteRate_nonneg P d n D ε)
  refine csInf_le ⟨0, ?_⟩ ⟨1, fun _ => 0, fun _ _ _ => Classical.arbitrary Xhat, one_pos, ?_, ?_⟩
  · rintro r ⟨M, enc, dec, hM, -, rfl⟩
    refine div_nonneg ?_ (Nat.cast_nonneg n)
    unfold log2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hM)) (Real.log_pos one_lt_two).le
  · dsimp only
    refine le_trans ?_ hε
    calc _ ≤ ∑ xy : Fin n → X × Y, ∏ i : Fin n, P.pmf (xy i) :=
          Finset.sum_le_sum fun xy _ => by
            split_ifs
            · exact le_rfl
            · exact Finset.prod_nonneg fun i _ => P.nonneg _
      _ = 1 := (iidDist P n).sum_one
  · simp [log2]

end InfoTheory.Known.Certificates.NonAsymptoticLossyDispersion
