import InfoTheory.Problems.NptBoundEntanglement

/-!
# Certificate for `InfoTheory.Problems.NptBoundEntanglement`

The frozen statement asks for `dA, dB ≥ 1` and a state `ρ` on `ℂ^{dA} ⊗ ℂ^{dB}` with
`¬ IsPPT ρ` (partial transpose `partialTransposeB` not PSD) and `¬ IsDistillable ρ`
(no `n ≥ 1` and Schmidt-rank-≤2 vector `ψ` across `A₁…Aₙ | B₁…Bₙ` with
`⟨ψ|(ρ^{T_B})^{⊗n}|ψ⟩ < 0`, using `kronPowerMat` and the de-interleaving maps
`extractAliceCopyIdx` / `extractBobCopyIdx`).
The certificate checks that both predicates are non-junk, i.e. take both truth values on
textbook states, so the Statement is neither trivially true nor trivially false.

## Certified
* **Bell state** `bell = |Φ⁺⟩⟨Φ⁺|` (2×2): `bell_not_PPT` (NPT, witnessed by the singlet
  vector `|01⟩ − |10⟩`, `⟨ψ|ρ^{T_B}|ψ⟩ = −1`) and `bell_distillable` (1-copy distillable with
  the Schmidt-rank-2 vector `|0⟩|1⟩ − |1⟩|0⟩`, exercising the `n = 1` de-interleaving and
  `kronPowerMat`). So "NPT" and "distillable" are both satisfiable.
* **Maximally mixed state** `mixed = I/4`: `mixed_PPT` and `mixed_not_distillable`
  (`¬ IsDistillable`, for *all* `n`, via `kronPowerMat_smul_one : (c·I)^{⊗n} = cⁿ·I`).
  So `IsDistillable` is not junk-true (it is a genuine all-`n` condition that fails on
  undistillable states), consistent with "PPT ⇒ undistillable" (Horodecki 1998).
* `isPPT_dB_one`: every state with `dB = 1` is PPT, so the Statement cannot be met by a
  degenerate one-dimensional Bob.

## Not certified
* "PPT ⇒ undistillable" in general (needs PSD-ness of `kronPowerMat` powers);
  "NPT ⇒ distillable" in `2 × N` (Horodecki); the Werner-state reduction.

## Adversarial check (2026-11-27)
The Horodecki criterion is encoded correctly (`(ρ^{⊗n})^{T_B} = (ρ^{T_B})^{⊗n}`, Schmidt rank
≤ 2 across the true `A|B` cut after de-interleaving; unnormalized `ψ` is harmless since the
condition is scale-invariant). Claimed resolutions (Simon 2006, quant-ph/0608250; Vianna–
Doherty-type claims) were not accepted (Chattopadhyay–Sarkar, quant-ph/0609050); a 2024
survey (arXiv:2402.18037) still calls it open, and no accepted resolution was found
through 2026. Statement FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.NptBoundEntanglement

open InfoTheory Matrix

/-- Indicator of the Bell support `{|00⟩, |11⟩}` (indices `0` and `3`). -/
def bellVec (i : Fin (2 * 2)) : ℂ := if i.1 = 0 ∨ i.1 = 3 then 1 else 0

/-- Row vector `⟨00| + ⟨11|`. -/
def bellRow : Matrix (Fin 1) (Fin (2 * 2)) ℂ := Matrix.of fun _ j => bellVec j

/-- The Bell state `|Φ⁺⟩⟨Φ⁺|`, `Φ⁺ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellMat : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ :=
  Matrix.of fun i j => if (i.1 = 0 ∨ i.1 = 3) ∧ (j.1 = 0 ∨ j.1 = 3) then 1 / 2 else 0

theorem bellMat_eq : bellMat = (1 / 2 : ℂ) • (bellRowᴴ * bellRow) := by
  ext i j
  simp only [bellMat, bellRow, bellVec, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_one, smul_eq_mul]
  split_ifs <;> simp_all

noncomputable def bell : DensityMatrix (2 * 2) where
  mat := bellMat
  posSemidef := by
    rw [bellMat_eq]
    exact (posSemidef_conjTranspose_mul_self _).smul (by rw [Complex.le_def]; norm_num)
  trace_one := by
    show ∑ i : Fin 4, bellMat i i = 1
    simp [bellMat, Fin.sum_univ_four]
    norm_num

theorem bell_not_PPT : ¬ @IsPPT 2 2 bell := by
  intro h
  have := h.re_dotProduct_nonneg (fun i : Fin (2 * 2) =>
    if i.1 = 1 then 1 else if i.1 = 2 then -1 else 0)
  revert this
  show ¬ 0 ≤ RCLike.re (∑ i : Fin 4, _)
  simp [Fin.sum_univ_four, Matrix.mulVec, dotProduct, partialTransposeB, bell, bellMat]

theorem bell_distillable : @IsDistillable 2 2 bell := by
  refine ⟨1, one_pos, fun a => if a = 0 then 1 else 0, fun a => if a = 1 then 1 else 0,
    fun b => if b = 1 then 1 else 0, fun b => if b = 0 then -1 else 0, ?_⟩
  show (∑ i : Fin 4, ∑ j : Fin 4, (_ : ℂ)).re < 0
  simp [Fin.sum_univ_four, extractAliceCopyIdx, extractBobCopyIdx, kronPowerMat, kronMat,
    partialTransposeB, bell, bellMat]

/-! ### Maximally mixed state: PPT and undistillable -/

/-- `kronMat` of scalar identities is a scalar identity. -/
theorem kronMat_smul_one {m n : ℕ} (a b : ℂ) :
    kronMat (a • (1 : Matrix (Fin m) (Fin m) ℂ)) (b • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (a * b) • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) := by
  ext i j
  simp only [kronMat, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.mk.injEq]
  by_cases hij : i = j
  · subst hij; simp
  · have : ¬ (i.1 / n = j.1 / n ∧ i.1 % n = j.1 % n) := by
      rintro ⟨h1, h2⟩
      apply hij
      ext
      rw [← Nat.div_add_mod i.1 n, ← Nat.div_add_mod j.1 n, h1, h2]
    by_cases h1 : i.1 / n = j.1 / n
    · have h2 : ¬ i.1 % n = j.1 % n := fun h2 => this ⟨h1, h2⟩
      simp [h2, hij]
    · simp [h1, hij]

/-- `(c·I)^{⊗ n} = cⁿ·I` for `kronPowerMat`. -/
theorem kronPowerMat_smul_one {m : ℕ} (c : ℂ) :
    ∀ n : ℕ, kronPowerMat n (fun _ => c • (1 : Matrix (Fin m) (Fin m) ℂ)) =
      (c ^ n) • (1 : Matrix (Fin (m ^ n)) (Fin (m ^ n)) ℂ)
  | 0 => by
    ext i j
    have hi : i = j := Subsingleton.elim (α := Fin 1) i j
    subst hi
    show (1 : ℂ) = ((c ^ 0) • (1 : Matrix (Fin (m ^ 0)) (Fin (m ^ 0)) ℂ)) i i
    rw [Matrix.smul_apply, Matrix.one_apply_eq, show c ^ 0 = 1 from pow_zero c, smul_eq_mul,
      mul_one]
  | n + 1 => by
    rw [kronPowerMat, kronPowerMat_smul_one c n, kronMat_smul_one,
      show c ^ (n + 1) = c ^ n * c from pow_succ c n]
    rfl

/-- The maximally mixed two-qubit state `I/4`. -/
noncomputable def mixed : DensityMatrix (2 * 2) where
  mat := ((1 / 4 : ℝ) : ℂ) • 1
  posSemidef := PosSemidef.one.smul (by rw [Complex.le_def]; norm_num)
  trace_one := by
    show ∑ i : Fin 4, (((1 / 4 : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i i = 1
    simp

theorem partialTranspose_mixed :
    @partialTransposeB 2 2 mixed.mat = ((1 / 4 : ℝ) : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [partialTransposeB, mixed, Matrix.one_apply]

theorem mixed_PPT : @IsPPT 2 2 mixed := by
  unfold IsPPT
  rw [partialTranspose_mixed]
  exact PosSemidef.one.smul (by rw [Complex.le_def]; norm_num)

/-- The maximally mixed state is not `n`-copy distillable for any `n`. -/
theorem mixed_not_distillable : ¬ @IsDistillable 2 2 mixed := by
  rintro ⟨n, -, u₁, u₂, v₁, v₂, h⟩
  dsimp only at h
  rw [partialTranspose_mixed, kronPowerMat_smul_one] at h
  set ψ : Fin ((2 * 2) ^ n) → ℂ := fun idx =>
    u₁ (extractAliceCopyIdx 2 2 n idx.1) * v₁ (extractBobCopyIdx 2 2 n idx.1) +
      u₂ (extractAliceCopyIdx 2 2 n idx.1) * v₂ (extractBobCopyIdx 2 2 n idx.1)
  have hsum : (∑ i, ∑ j, star (ψ i) *
      ((((1 / 4 : ℝ) : ℂ) ^ n) • (1 : Matrix (Fin ((2 * 2) ^ n)) (Fin ((2 * 2) ^ n)) ℂ)) i j *
        ψ j) = (((1 / 4 : ℝ) ^ n * ∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.conj_mul', Complex.star_def]
    ring
  rw [hsum, Complex.ofReal_re] at h
  have : 0 ≤ (1 / 4 : ℝ) ^ n * ∑ i, ‖ψ i‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity)
  linarith

/-! ### No NPT states when Bob is trivial -/

theorem partialTransposeB_dB_one {dA : ℕ} (M : Matrix (Fin (dA * 1)) (Fin (dA * 1)) ℂ) :
    @partialTransposeB dA 1 M = M := by
  ext i j
  simp only [partialTransposeB, Matrix.of_apply, Nat.div_one, Nat.mod_one, mul_one, add_zero]

/-- Every state on `ℂ^{dA} ⊗ ℂ¹` is PPT, so a witness of the Statement needs `dB ≥ 2`. -/
theorem isPPT_dB_one {dA : ℕ} (ρ : DensityMatrix (dA * 1)) : @IsPPT dA 1 ρ := by
  unfold IsPPT
  rw [partialTransposeB_dB_one]
  exact ρ.posSemidef

end InfoTheory.Known.Certificates.NptBoundEntanglement
