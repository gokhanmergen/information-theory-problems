import InfoTheory.Problems.SuperactivationQubitChannels
import InfoTheory.Known.Certificates.QuantumCapacitySingleLetter

/-!
# Certificate for `InfoTheory.Problems.SuperactivationQubitChannels`

The frozen statement asks for qubit channels `N₁, N₂` with `Q(N₁) = Q(N₂) = 0` and a
4-dimensional channel `N₁₂` realising `N₁ ⊗ N₂` (Kraus operators `K_a ⊗ L_b` via `kronMat`)
with `Q(N₁₂) > 0`.

## Certified (non-junk)
* `tensorCh N₁ N₂` (Kraus operators `kronMat (K_a) (L_b)`, indexed through
  `finProdFinEquiv`) is a CPTP map and `tensorCh_apply` shows it realises
  `tensorChannelApply N₁ N₂`: the existential over `N₁₂` is always satisfiable, for every
  pair of channels (any dimensions).
* `Q(N) ≤ 1` for qubit channels and `quantumCapacity_tensor_le_two : Q(N₁₂) ≤ 2` — all
  capacities involved are genuine bounded suprema (toolkit in
  `Certificates/QuantumCapacitySingleLetter`).
* **Regression (zero-capacity hypotheses are satisfiable):** the qubit reset channel has
  `Q(reset₂) = 0` (`quantumCapacity_resetQubit`).
* **Regression (no trivial superactivation):** `quantumCapacity_tensor_reset_le :
  Q(reset₂ ⊗ reset₂) ≤ 0`, so `reset_pair_not_superactivating`: the pair
  `(reset₂, reset₂, tensorCh reset₂ reset₂)` satisfies the first three conjuncts but not
  `0 < Q(N₁₂)` — the target inequality is not automatic.
* `tensorCh_idCh_apply`: `id₂ ⊗ id₂` acts as the identity on `M₄` (sanity check of the
  `kronMat`-based tensor product).

## Not certified
* `Q(N₁ ⊗ N₂) = 0` for pairs of anti-degradable or entanglement-breaking qubit channels in
  general, and the Smith–Yard superactivation in dimension `≥ 4`.

## Adversarial check (2026-11-27)
Smith–Yard (Science 321, 2008) and all later superactivation examples use a PPT
(Horodecki) channel, impossible on qubits (2⊗2 PPT ⇒ separable). The 2026 finite-blocklength
study of superactivation (Parentin–Bergh–Datta–Wilde, arXiv:2604.27042) works with the
original 50%-erasure + PPT pair, not qubit channels. No qubit superactivation (or
impossibility proof) found. OPEN and FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.SuperactivationQubitChannels

open InfoTheory Matrix InfoTheory.Problems.SuperactivationQubitChannels
open InfoTheory.Known.Certificates.QuantumCapacitySingleLetter

/-- The tensor product channel, Kraus operators `K_a ⊗ L_b`. -/
def tensorCh {d₁ d₂ e₁ e₂ : ℕ} (N₁ : QuantumChannel d₁ d₂) (N₂ : QuantumChannel e₁ e₂) :
    QuantumChannel (d₁ * e₁) (d₂ * e₂) where
  numKraus := N₁.numKraus * N₂.numKraus
  kraus := fun x => kronMat (N₁.kraus (finProdFinEquiv.symm x).1)
    (N₂.kraus (finProdFinEquiv.symm x).2)
  tracePreserving := by
    refine (Equiv.sum_comp finProdFinEquiv _).symm.trans ?_
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [kronMat_conjTranspose, kronMat_mul]
    simp_rw [← kronMat_sum_right]
    rw [← kronMat_sum_left, N₁.tracePreserving, N₂.tracePreserving, kronMat_one]

theorem tensorCh_apply {d₁ d₂ e₁ e₂ : ℕ} (N₁ : QuantumChannel d₁ d₂) (N₂ : QuantumChannel e₁ e₂)
    (ρ : Matrix (Fin (d₁ * e₁)) (Fin (d₁ * e₁)) ℂ) :
    (tensorCh N₁ N₂).applyMat ρ = tensorChannelApply N₁ N₂ ρ := by
  unfold QuantumChannel.applyMat
  refine (Equiv.sum_comp finProdFinEquiv _).symm.trans ?_
  simp only [tensorCh, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  rfl

/-- The existential witness `N₁₂` of the statement always exists. -/
theorem exists_tensor_realisation (N₁ N₂ : QuantumChannel 2 2) :
    ∃ N₁₂ : QuantumChannel (2 * 2) (2 * 2),
      ∀ ρ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ, N₁₂.applyMat ρ = tensorChannelApply N₁ N₂ ρ :=
  ⟨tensorCh N₁ N₂, tensorCh_apply N₁ N₂⟩

theorem log2_four : log2 ((2 * 2 : ℕ) : ℝ) = 2 := by
  unfold log2
  rw [show (((2 * 2 : ℕ)) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  field_simp [(Real.log_pos one_lt_two).ne']
  norm_num

/-- `Q(N₁₂) ≤ 2` for every 4-dimensional channel. -/
theorem quantumCapacity_tensor_le_two (N₁₂ : QuantumChannel (2 * 2) (2 * 2)) :
    quantumCapacity N₁₂ ≤ 2 := by
  have := quantumCapacity_le_log2 N₁₂
  rwa [log2_four] at this

/-- **Regression:** `reset₂ ⊗ reset₂` has `Q ≤ 0` (it is again a constant-output channel). -/
theorem quantumCapacity_tensor_reset_le :
    quantumCapacity (tensorCh (resetCh 2 two_pos) (resetCh 2 two_pos)) ≤ 0 := by
  refine quantumCapacity_constOut_le (r := 1 * 1) (by norm_num) _
    (kronMat (ket0 2 two_pos) (ket0 2 two_pos)) ?_
    (fun x => kronMat (braE (d := 2) (finProdFinEquiv.symm x).1)
      (braE (d := 2) (finProdFinEquiv.symm x).2)) ?_
  · rw [kronMat_conjTranspose, kronMat_mul, ket0_conj_mul, kronMat_one]
  · intro x
    exact (kronMat_mul _ _ _ _).symm

/-- **Regression:** the reset pair satisfies the zero-capacity hypotheses but does not
superactivate. -/
theorem reset_pair_not_superactivating :
    quantumCapacity (resetCh 2 two_pos) = 0 ∧
    (∀ ρ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ,
      (tensorCh (resetCh 2 two_pos) (resetCh 2 two_pos)).applyMat ρ =
        tensorChannelApply (resetCh 2 two_pos) (resetCh 2 two_pos) ρ) ∧
    ¬ 0 < quantumCapacity (tensorCh (resetCh 2 two_pos) (resetCh 2 two_pos)) :=
  ⟨quantumCapacity_resetQubit, tensorCh_apply _ _, not_lt.2 quantumCapacity_tensor_reset_le⟩

/-- `id₂ ⊗ id₂` acts as the identity on `M₄`. -/
theorem tensorCh_idCh_apply (ρ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ) :
    (tensorCh (idCh 2) (idCh 2)).applyMat ρ = ρ := by
  rw [tensorCh_apply]
  show (∑ _a : Fin 1, ∑ _b : Fin 1, kronMat (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 * ρ *
    (kronMat (1 : Matrix (Fin 2) (Fin 2) ℂ) 1)ᴴ) = ρ
  simp [kronMat_one]

end InfoTheory.Known.Certificates.SuperactivationQubitChannels
