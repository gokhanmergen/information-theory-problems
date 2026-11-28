import InfoTheory.Problems.MmseDimensionSingleCrossing

/-!
# Certificate for `InfoTheory.Problems.MmseDimensionSingleCrossing`

The frozen statement is the matrix-SNR single-crossing implication
`E_X(H₀) ⪯ (J + H₀ᵀH₀)⁻¹ ⟹ E_X(H₁) ⪯ (J + H₁ᵀH₁)⁻¹` for finite-support inputs and
`H₁ᵀH₁ ⪰ H₀ᵀH₀`.

**Catalog note (2026-11-27).** This implication is a known theorem, not an open problem: along
`S(t) = S₀ + tΔ` one has `-(d/dt) E(S(t)) = E[Cov(X|Y) Δ Cov(X|Y)] ⪰ E Δ E` (Payaró–Palomar
2009 Jacobian of the MMSE matrix, plus matrix Jensen for the convex map `C ↦ CΔC`), hence
`(d/dt) E⁻¹ ⪰ Δ`, so `E(S(t))⁻¹ - (J + S(t))` is Loewner-nondecreasing (smooth `X` first if
`E` is singular). See `problems/mmse-dimension-single-crossing.md`. Nothing here proves it.

Certified here, about the *exact* objects in `Statement` (no junk values):
* `stdGaussPdf_pos` — the Gaussian kernel is strictly positive, so `postMean` never divides by
  zero for a genuine input distribution;
* `postMean_dirac`, `mmseMatrix_dirac` — **regression (deterministic input):** for a one-point
  input the posterior mean is the point itself and the MMSE matrix `E_X(H)` is exactly `0` for
  every channel `H` (so the `IsPSDMat` conclusions of `Statement` are about the real MMSE
  integral, which vanishes where it must).

Not certified: the Gaussian-input identity `E_{X_G}(S) = (J + S)⁻¹` (the formal statement uses
finite-support inputs only), the scalar Guo–Wu–Shamai–Verdú single-crossing, or the theorem
above.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MmseDimensionSingleCrossing

open InfoTheory InfoTheory.Problems.MmseDimensionSingleCrossing

theorem stdGaussPdf_pos (d : ℕ) (z : Fin d → ℝ) : 0 < stdGaussPdf d z := by
  unfold stdGaussPdf
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem pmf_fin_one (P : ProbDist (Fin 1)) : P.pmf 0 = 1 := by
  simpa using P.sum_one

/-- For a deterministic (one-point) input the posterior mean is that point. -/
theorem postMean_dirac {d : ℕ} (P : ProbDist (Fin 1)) (xs : Fin 1 → (Fin d → ℝ))
    (H : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (a : Fin d) :
    postMean P xs H y a = xs 0 a := by
  unfold postMean
  simp only [Fin.sum_univ_one, pmf_fin_one, one_mul]
  have := stdGaussPdf_pos d (fun j => y j - matVecMul H (xs 0) j)
  field_simp

/-- **Regression**: the MMSE matrix of a deterministic input vanishes for every channel. -/
theorem mmseMatrix_dirac {d : ℕ} (P : ProbDist (Fin 1)) (xs : Fin 1 → (Fin d → ℝ))
    (H : Matrix (Fin d) (Fin d) ℝ) : mmseMatrix P xs H = 0 := by
  ext a b
  simp [mmseMatrix, postMean_dirac]

end InfoTheory.Known.Certificates.MmseDimensionSingleCrossing
