import InfoTheory.Core

open scoped BigOperators
open MeasureTheory

namespace InfoTheory.Problems.MmseDimensionSingleCrossing

/-- Real symmetric positive-semidefinite predicate on `d × d` matrices. -/
def IsPSDMat {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ (i j : Fin d), M i j = M j i) ∧
  (∀ (v : Fin d → ℝ), 0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * M i j * v j)

/-- Real symmetric positive-definite predicate on `d × d` matrices. -/
def IsPDMat {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ (i j : Fin d), M i j = M j i) ∧
  (∀ (v : Fin d → ℝ), (∃ (i : Fin d), v i ≠ 0) →
    0 < ∑ i : Fin d, ∑ j : Fin d, v i * M i j * v j)

/-- Matrix-vector product `H v` on `Fin d → ℝ`. -/
def matVecMul {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ j : Fin d, H i j * v j

/-- Gram matrix `Hᵀ H` of a real `d × d` channel matrix `H`. -/
def gramMat {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ r : Fin d, H r i * H r j

/-- Standard `d`-dimensional Gaussian density `φ_d(z) = (2π)^{-d/2} exp(-½ ‖z‖²)`. -/
noncomputable def stdGaussPdf (d : ℕ) (z : Fin d → ℝ) : ℝ :=
  ((2 * Real.pi) ^ (-(d : ℝ) / 2)) *
    Real.exp (-(1 / 2 : ℝ) * ∑ i : Fin d, (z i) ^ 2)

/-- Posterior mean `E[X | H X + Z = y]` for a discrete vector input `(P, xs)` in `ℝ^d`. -/
noncomputable def postMean {d k : ℕ} (P : ProbDist (Fin k)) (xs : Fin k → (Fin d → ℝ))
    (H : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (a : Fin d) : ℝ :=
  (∑ i : Fin k, P.pmf i * stdGaussPdf d (fun j => y j - matVecMul H (xs i) j) * xs i a) /
  (∑ i : Fin k, P.pmf i * stdGaussPdf d (fun j => y j - matVecMul H (xs i) j))

/-- Exact `d × d` MMSE covariance matrix `E_X(H)` for observing `Y = H X + Z` with
    `Z ~ N(0, I_d)` and finite-support input `(P, xs)`. -/
noncomputable def mmseMatrix {d k : ℕ} (P : ProbDist (Fin k)) (xs : Fin k → (Fin d → ℝ))
    (H : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b =>
    ∫ (y : Fin d → ℝ),
      ∑ i : Fin k,
        P.pmf i * stdGaussPdf d (fun j => y j - matVecMul H (xs i) j) *
        (xs i a - postMean P xs H y a) *
        (xs i b - postMean P xs H y b)

/-- Matrix-SNR Single-Crossing Conjecture (Bustin–Payaró–Palomar–Shamai 2013):
    for any dimension `d ≥ 2`, any finite-support vector input `X`, any positive-definite
    Gaussian precision matrix `J`, and any pair of channel matrices `H₀, H₁` with
    `H₁ᵀ H₁ ⪰ H₀ᵀ H₀`, does `E_X(H₀) ⪯ (J + H₀ᵀ H₀)⁻¹` imply `E_X(H₁) ⪯ (J + H₁ᵀ H₁)⁻¹`? -/
def Statement : Prop :=
  ∀ (d k : ℕ) (P : ProbDist (Fin k)) (xs : Fin k → (Fin d → ℝ))
    (J H₀ H₁ M₀ M₁ : Matrix (Fin d) (Fin d) ℝ),
    2 ≤ d → 0 < k →
    IsPDMat J →
    IsPSDMat (gramMat H₁ - gramMat H₀) →
    M₀ * (J + gramMat H₀) = 1 →
    M₁ * (J + gramMat H₁) = 1 →
    IsPSDMat (M₀ - mmseMatrix P xs H₀) →
    IsPSDMat (M₁ - mmseMatrix P xs H₁)

def problem : OpenProblem where
  id := "mmse-dimension-single-crossing"
  title := "Matrix-SNR Single-Crossing Inequality and MMSE Dimension for Non-Gaussian Vectors"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Dongning Guo, Shlomo Shamai (Shitz), and Sergio Verdú; Yihong Wu and Sergio Verdú"
  posedYear := 2005
  statement := Statement

end InfoTheory.Problems.MmseDimensionSingleCrossing
