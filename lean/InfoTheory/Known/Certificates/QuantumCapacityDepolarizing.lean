import InfoTheory.Problems.QuantumCapacityDepolarizing
import InfoTheory.Known.Certificates.QuantumCapacitySingleLetter

/-!
# Certificate for `InfoTheory.Problems.QuantumCapacityDepolarizing`

The frozen statement asks for `p ∈ (0, 1/4)` such that every Kraus realisation `N` of the
qubit depolarizing channel `D_p(ρ) = (1-p)ρ + (p/3)(XρX + YρY + ZρZ)` has `Q(N) = 0`.

## Certified (non-junk)
* `depolCh p` (Kraus operators `√(1-p) I, √(p/3) X, √(p/3) Y, √(p/3) Z`) is a CPTP map with
  `depolCh_isDepolarizing : IsDepolarizingChannel p (depolCh p _ _)` for every `p ∈ [0, 1]`:
  the universally quantified `∀ N, IsDepolarizingChannel p N → …` is not vacuous.
* `quantumCapacity_le_one`: `Q(N) ≤ 1` for every qubit channel (the `sSup` is bounded; see
  the toolkit in `Certificates/QuantumCapacitySingleLetter`).
* **Regression `p = 0`:** `idCh_isDepolarizing_zero` (the identity channel is `D_0`) and
  `quantumCapacity_idCh 2 = 1`, hence `not_zeroCapacity_at_zero`: the property
  `∀ N, IsDepolarizingChannel p N → Q(N) = 0` fails at `p = 0` (the inner predicate is not
  trivially true).
* Pauli facts `pauliX_mul_self`, `pauliY_mul_self`, `pauliZ_mul_self` and the
  self-adjointness lemmas (reused by `QuantumCapacityTwoPauli`).

## Not certified
* `Q(D_p) = 0` for `p ≥ 1/4` (anti-degradability via symmetric cloning), the hashing bound
  `Q(D_p) ≥ 1 - H(1-p, p/3, p/3, p/3)`, and independence of `Q` from the Kraus realisation.

## Adversarial check (2026-11-27)
The parameterisation `D_p = (1 - 4p/3)ρ + (2p/3)I` makes `p = 1/4` the shrinking factor
`2/3` of the optimal symmetric `1 → 2` cloner, so `p = 1/4` is exactly the
anti-degradability threshold, and `p = 1/2` the entanglement-breaking one: consistent with
the docstring. Recent work only raises the *positivity* threshold from below (e.g.
Agarwal–Kalra–Lee–Leung–Schaeffer–Sinha–Smith, "Enhanced quantum capacity thresholds from
symmetry", arXiv:2605.09138, 2026; certified lower-bound preprints, 2026); no upper bound
vanishing strictly below `1/4` is known. The statement is OPEN and FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.QuantumCapacityDepolarizing

open InfoTheory Matrix InfoTheory.Problems.QuantumCapacityDepolarizing
open InfoTheory.Known.Certificates.QuantumCapacitySingleLetter

/-! ### Pauli facts -/

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, conjTranspose_apply]

theorem pauliY_conjTranspose : pauliYᴴ = pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, conjTranspose_apply]

theorem pauliZ_conjTranspose : pauliZᴴ = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, conjTranspose_apply]

/-- A real square-root weight `√c` as a complex scalar. -/
noncomputable def sqw (c : ℝ) : ℂ := ((Real.sqrt c : ℝ) : ℂ)

theorem star_sqw_mul (c : ℝ) (hc : 0 ≤ c) : star (sqw c) * sqw c = (c : ℂ) := by
  unfold sqw
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

theorem sqw_mul_star (c : ℝ) (hc : 0 ≤ c) : sqw c * star (sqw c) = (c : ℂ) := by
  rw [mul_comm, star_sqw_mul c hc]

/-- `(√c σ)ᴴ (√c σ) = c · σ²` for a self-adjoint `σ`. -/
theorem weighted_conj_mul (c : ℝ) (hc : 0 ≤ c) (σ : Matrix (Fin 2) (Fin 2) ℂ) (hσ : σᴴ = σ) :
    (sqw c • σ)ᴴ * (sqw c • σ) = (c : ℂ) • (σ * σ) := by
  rw [conjTranspose_smul, hσ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_sqw_mul c hc]

/-- `(√c σ) ρ (√c σ)ᴴ = c · σ ρ σ` for a self-adjoint `σ`. -/
theorem weighted_sandwich (c : ℝ) (hc : 0 ≤ c) (σ ρ : Matrix (Fin 2) (Fin 2) ℂ) (hσ : σᴴ = σ) :
    (sqw c • σ) * ρ * (sqw c • σ)ᴴ = (c : ℂ) • (σ * ρ * σ) := by
  rw [conjTranspose_smul, hσ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqw_mul_star c hc]

/-! ### The depolarizing channel exists -/

/-- Kraus operators of `D_p`. -/
noncomputable def depolKraus (p : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![sqw (1 - p) • (1 : Matrix (Fin 2) (Fin 2) ℂ), sqw (p / 3) • pauliX, sqw (p / 3) • pauliY,
    sqw (p / 3) • pauliZ]

/-- The qubit depolarizing channel `D_p` for `p ∈ [0, 1]`. -/
noncomputable def depolCh (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : QuantumChannel 2 2 where
  numKraus := 4
  kraus := depolKraus p
  tracePreserving := by
    have h1 : 0 ≤ 1 - p := by linarith
    have h3 : 0 ≤ p / 3 := by positivity
    simp only [Fin.sum_univ_four, depolKraus, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [weighted_conj_mul _ h1 _ conjTranspose_one, weighted_conj_mul _ h3 _ pauliX_conjTranspose,
      weighted_conj_mul _ h3 _ pauliY_conjTranspose, weighted_conj_mul _ h3 _ pauliZ_conjTranspose,
      pauliX_mul_self, pauliY_mul_self, pauliZ_mul_self, Matrix.one_mul, ← add_smul, ← add_smul,
      ← add_smul]
    convert one_smul ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ) using 2
    push_cast
    ring

theorem depolCh_isDepolarizing (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDepolarizingChannel p (depolCh p hp0 hp1) := by
  intro ρ
  have h1 : 0 ≤ 1 - p := by linarith
  have h3 : 0 ≤ p / 3 := by positivity
  show ∑ a : Fin 4, depolKraus p a * ρ * (depolKraus p a)ᴴ = _
  simp only [Fin.sum_univ_four, depolKraus, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [weighted_sandwich _ h1 _ _ conjTranspose_one, weighted_sandwich _ h3 _ _ pauliX_conjTranspose,
    weighted_sandwich _ h3 _ _ pauliY_conjTranspose, weighted_sandwich _ h3 _ _ pauliZ_conjTranspose,
    Matrix.one_mul, Matrix.mul_one]
  unfold depolarizingApply
  rw [smul_add, smul_add]
  abel

/-! ### Capacity facts -/

theorem log2_two : log2 ((2 : ℕ) : ℝ) = 1 := by
  unfold log2
  push_cast
  exact div_self (Real.log_pos one_lt_two).ne'

/-- Every qubit channel has `Q ≤ 1`. -/
theorem quantumCapacity_le_one (N : QuantumChannel 2 2) : quantumCapacity N ≤ 1 := by
  have := quantumCapacity_le_log2 N
  rwa [log2_two] at this

/-- **Regression:** the identity channel realises `D_0`. -/
theorem idCh_isDepolarizing_zero : IsDepolarizingChannel 0 (idCh 2) := by
  intro ρ
  show (∑ _a : Fin 1, (1 : Matrix (Fin 2) (Fin 2) ℂ) * ρ * 1ᴴ) = _
  simp [depolarizingApply]

/-- **Regression:** at `p = 0` the zero-capacity property fails (`Q(D_0) = 1`). -/
theorem not_zeroCapacity_at_zero :
    ¬ ∀ N : QuantumChannel 2 2, IsDepolarizingChannel 0 N → quantumCapacity N = 0 := by
  intro h
  have := h (idCh 2) idCh_isDepolarizing_zero
  rw [quantumCapacity_idQubit] at this
  exact one_ne_zero this

end InfoTheory.Known.Certificates.QuantumCapacityDepolarizing
