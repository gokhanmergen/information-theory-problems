import InfoTheory.Problems.QuantumCapacityTwoPauli
import InfoTheory.Known.Certificates.QuantumCapacityDepolarizing

/-!
# Certificate for `InfoTheory.Problems.QuantumCapacityTwoPauli`

The frozen statement asks for `p ∈ (0, 1/3)` such that every Kraus realisation `N` of the
two-Pauli channel `N_p(ρ) = (1-p)ρ + (p/2)(XρX + ZρZ)` has `Q(N) = 0`.

## Certified (non-junk)
* `twoPauliCh p` (Kraus operators `√(1-p) I, √(p/2) X, √(p/2) Z`) is CPTP and
  `twoPauliCh_isTwoPauli : IsTwoPauliChannel p (twoPauliCh p _ _)` for all `p ∈ [0, 1]`:
  the `∀ N, IsTwoPauliChannel p N → …` quantifier is not vacuous.
* `quantumCapacity_le_one` (from the depolarizing certificate): `Q(N) ≤ 1` for every qubit
  channel, so `quantumCapacity` is a genuine bounded supremum.
* **Regression `p = 0`:** `idCh_isTwoPauli_zero` and `Q(id₂) = 1`, hence
  `not_zeroCapacity_at_zero`.

## Not certified
* Anti-degradability (`Q = 0`) for `p ≥ 1/3`, the hashing bound `1 - h(p) - p`, and the
  entanglement-breaking threshold `p ≥ 1/2`.

## Adversarial check (2026-11-27)
The no-cloning threshold `1/3` for this channel (Pauli weights `(1-p, p/2, 0, p/2)`) is the
standard anti-degradability point (Cerf 2000; Smith–Smolin 2008). Recent symmetric-code
searches (arXiv:2605.09138, 2026) improve the *positivity* threshold for Pauli channels from
below; no proof that `Q(N_p) = 0` for some `p < 1/3` is known. OPEN and FINE; Lean not
modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.QuantumCapacityTwoPauli

open InfoTheory Matrix InfoTheory.Problems.QuantumCapacityTwoPauli
open InfoTheory.Known.Certificates.QuantumCapacitySingleLetter
open InfoTheory.Known.Certificates.QuantumCapacityDepolarizing

/-- Kraus operators of the two-Pauli channel. -/
noncomputable def twoPauliKraus (p : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![sqw (1 - p) • (1 : Matrix (Fin 2) (Fin 2) ℂ), sqw (p / 2) • pauliX, sqw (p / 2) • pauliZ]

/-- The qubit two-Pauli channel for `p ∈ [0, 1]`. -/
noncomputable def twoPauliCh (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : QuantumChannel 2 2 where
  numKraus := 3
  kraus := twoPauliKraus p
  tracePreserving := by
    have h1 : 0 ≤ 1 - p := by linarith
    have h2 : 0 ≤ p / 2 := by positivity
    simp only [Fin.sum_univ_three, twoPauliKraus, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [weighted_conj_mul _ h1 _ conjTranspose_one, weighted_conj_mul _ h2 _ pauliX_conjTranspose,
      weighted_conj_mul _ h2 _ pauliZ_conjTranspose, pauliX_mul_self, pauliZ_mul_self,
      Matrix.one_mul, ← add_smul, ← add_smul]
    convert one_smul ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ) using 2
    push_cast
    ring

theorem twoPauliCh_isTwoPauli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsTwoPauliChannel p (twoPauliCh p hp0 hp1) := by
  intro ρ
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ p / 2 := by positivity
  show ∑ a : Fin 3, twoPauliKraus p a * ρ * (twoPauliKraus p a)ᴴ = _
  simp only [Fin.sum_univ_three, twoPauliKraus, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [weighted_sandwich _ h1 _ _ conjTranspose_one, weighted_sandwich _ h2 _ _ pauliX_conjTranspose,
    weighted_sandwich _ h2 _ _ pauliZ_conjTranspose, Matrix.one_mul, Matrix.mul_one, smul_add]
  abel

/-- **Regression:** the identity channel realises the two-Pauli channel at `p = 0`. -/
theorem idCh_isTwoPauli_zero : IsTwoPauliChannel 0 (idCh 2) := by
  intro ρ
  show (∑ _a : Fin 1, (1 : Matrix (Fin 2) (Fin 2) ℂ) * ρ * 1ᴴ) = _
  simp

/-- **Regression:** at `p = 0` the zero-capacity property fails (`Q(N_0) = Q(id₂) = 1`). -/
theorem not_zeroCapacity_at_zero :
    ¬ ∀ N : QuantumChannel 2 2, IsTwoPauliChannel 0 N → quantumCapacity N = 0 := by
  intro h
  have := h (idCh 2) idCh_isTwoPauli_zero
  rw [quantumCapacity_idQubit] at this
  exact one_ne_zero this

/-- Every realisation of the two-Pauli channel has `Q ≤ 1`. -/
theorem quantumCapacity_twoPauli_le_one (p : ℝ) (N : QuantumChannel 2 2)
    (_ : IsTwoPauliChannel p N) : quantumCapacity N ≤ 1 :=
  quantumCapacity_le_one N

end InfoTheory.Known.Certificates.QuantumCapacityTwoPauli
