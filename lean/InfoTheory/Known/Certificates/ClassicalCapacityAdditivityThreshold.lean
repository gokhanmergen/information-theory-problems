import InfoTheory.Problems.ClassicalCapacityAdditivityThreshold

/-!
# Certificate for `InfoTheory.Problems.ClassicalCapacityAdditivityThreshold`

The frozen statement asks whether there are quantum channels `N₁ : M_{d₁} → M_2`,
`N₂ : M_{e₁} → M_2` (qubit outputs) with
`minOutputEntropyTensor N₁ N₂ < minOutputEntropy N₁ + minOutputEntropy N₂`.
The certificate checks that `minOutputEntropy` / `minOutputEntropyTensor` are not junk:
they are bounded below by `0` and take the textbook values on simple channels, including
qubit-output pairs for which additivity is known.

## Certified
* `matEntropy_nonneg_of_state`: the von Neumann entropy (`matEntropy`) of any positive
  semidefinite trace-one matrix is `≥ 0`; `applyMat_posSemidef`, `applyMat_trace`: channel
  outputs are states; hence `minOutputEntropy_nonneg : 0 ≤ S_min(N)` for every channel, and
  the `sInf` in `minOutputEntropy` is over a nonempty set bounded below (no `sInf ∅ = 0` or
  unbounded-below junk).
* `matEntropy_eq_zero_of_idem`: pure states (Hermitian idempotents) have entropy `0`;
  `matEntropy_smul_one`: `S(c·I_d) = d · (−c log₂ c)` (so `S(I_d/d) = log₂ d`).
* **Regression, identity qubit channel:** `minOutputEntropy_idQubit : S_min(id₂) = 0`,
  `minOutputEntropyTensor_idQubit : S_min(id₂ ⊗ id₂) = 0`, so additivity holds (`0 = 0 + 0`).
* **Regression, qubit replacement channel** `replQubit : M_1 → M_2`, `ρ ↦ I/2` (Kraus
  operators `(1/2)(1, ±1)ᵀ`): `minOutputEntropy_replQubit : S_min = 1` bit, and
  `minOutputEntropyTensor_replQubit : S_min(R ⊗ R) = 2 = 1 + 1`
  (`replQubit_additive`): additivity holds, as it must for entanglement-breaking channels
  (Shor 2002). In particular `S_min` is not identically `0`, and the tensor-product object
  `minOutputEntropyTensor` (Kraus operators `K_a ⊗ L_b` via `kronMat`) produces the right
  4×4 output `I/4`.

## Not certified
* The general easy direction `S_min(N₁ ⊗ N₂) ≤ S_min(N₁) + S_min(N₂)` (product inputs) and
  King's additivity theorem for unital qubit channels (King 2002); these need additivity of
  `matEntropy` under `kronMat`, not available in `Known`/`Bridge` yet.

## Adversarial check (2026-11-27)
The Statement is the `d = 2` case of "smallest output dimension admitting a violation".
Via complementary channels (King–Matsumoto–Nathanson–Ruskai, Markov Proc. Rel. Fields 13,
2007: `S_min(N) = S_min(N^c)` and additivity for a pair iff for the conjugate pair) it is
equivalent to the same question for channels with two Kraus operators. Known violations
(Hastings 2009; Belinschi–Collins–Nechita 2016) need output dimension in the hundreds;
additivity is known when one factor is a unital qubit channel (King 2002) or
entanglement-breaking (Shor 2002); for general non-unital qubit-output pairs it is open.
No resolution found in the 2020–2026 literature. Statement FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold

open InfoTheory InfoTheory.Problems.ClassicalCapacityAdditivityThreshold Matrix

/-! ### Entropy of states -/

private lemma negPLogP_nonneg_of_le_one {p : ℝ} (hp1 : p ≤ 1) : 0 ≤ negPLogP p := by
  unfold negPLogP
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    have : log2 p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos h.le hp1)
      (Real.log_nonneg one_le_two)
    nlinarith

/-- The von Neumann entropy of a state is nonnegative. -/
theorem matEntropy_nonneg_of_state {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.PosSemidef) (htr : M.trace = 1) : 0 ≤ matEntropy M := by
  unfold matEntropy
  rw [dif_pos hM.1]
  have hsum : ∑ i, hM.1.eigenvalues i = 1 := by
    have := hM.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 : ((∑ i, hM.1.eigenvalues i : ℝ) : ℂ) = 1 := by
      rw [this]; push_cast; rfl
    exact_mod_cast h2
  refine Finset.sum_nonneg fun i _ => negPLogP_nonneg_of_le_one ?_
  rw [← hsum]
  exact Finset.single_le_sum (f := fun i => hM.1.eigenvalues i)
    (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

private lemma eigvec_ne_zero {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (j : Fin d) : (⇑(hA.eigenvectorBasis j) : Fin d → ℂ) ≠ 0 :=
  (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero j)

private lemma eig_of_mulVec {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (j : Fin d) (μ : ℂ)
    (h : A *ᵥ ⇑(hA.eigenvectorBasis j) = μ • ⇑(hA.eigenvectorBasis j)) :
    ((hA.eigenvalues j : ℝ) : ℂ) = μ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (eigvec_ne_zero hA j)
  have h1 := congrFun (hA.mulVec_eigenvectorBasis j) i
  have h2 := congrFun h i
  rw [h1] at h2
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2 hi
  rw [RCLike.real_smul_eq_coe_mul] at h2
  exact mul_right_cancel₀ hi h2

/-- Pure states (Hermitian idempotents) have entropy `0`. -/
theorem matEntropy_eq_zero_of_idem {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.IsHermitian) (hidem : M * M = M) : matEntropy M = 0 := by
  unfold matEntropy
  rw [dif_pos hM]
  refine Finset.sum_eq_zero fun j _ => ?_
  set v := (⇑(hM.eigenvectorBasis j) : Fin d → ℂ)
  set l : ℂ := ((hM.eigenvalues j : ℝ) : ℂ)
  have hv : M *ᵥ v = l • v := by
    have := hM.mulVec_eigenvectorBasis j
    rw [this]
    ext i
    simp [l, v, RCLike.real_smul_eq_coe_mul]
  have hll : l * l = l := by
    have e : M *ᵥ (M *ᵥ v) = (l * l) • v := by
      rw [hv, Matrix.mulVec_smul, hv, smul_smul]
    rw [Matrix.mulVec_mulVec, hidem, hv] at e
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (eigvec_ne_zero hM j)
    have := congrFun e i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact (mul_right_cancel₀ hi this).symm
  have hr : hM.eigenvalues j * hM.eigenvalues j = hM.eigenvalues j := by
    have : ((hM.eigenvalues j * hM.eigenvalues j : ℝ) : ℂ) = ((hM.eigenvalues j : ℝ) : ℂ) := by
      push_cast; exact hll
    exact_mod_cast this
  have : hM.eigenvalues j = 0 ∨ hM.eigenvalues j = 1 := by
    have : hM.eigenvalues j * (hM.eigenvalues j - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases this with h | h <;> rw [h] <;> simp [negPLogP, log2]

/-- `S(c · I_d) = d · (−c log₂ c)`. -/
theorem matEntropy_smul_one {d : ℕ} (c : ℝ) :
    matEntropy (((c : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) = d * negPLogP c := by
  have hH : (((c : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [Complex.conj_ofReal, map_ofNat]
  unfold matEntropy
  rw [dif_pos hH]
  have : ∀ j, hH.eigenvalues j = c := by
    intro j
    have := eig_of_mulVec hH j (c : ℂ) (by rw [Matrix.smul_mulVec, Matrix.one_mulVec])
    exact_mod_cast this
  simp [this]

/-! ### Channel outputs are states -/

theorem applyMat_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    {ρ : Matrix (Fin d₁) (Fin d₁) ℂ} (hρ : ρ.PosSemidef) : (N.applyMat ρ).PosSemidef :=
  posSemidef_sum _ fun a _ => hρ.mul_mul_conjTranspose_same (N.kraus a)

theorem applyMat_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) : (N.applyMat ρ).trace = ρ.trace := by
  unfold QuantumChannel.applyMat
  rw [Matrix.trace_sum]
  have : ∀ a, (N.kraus a * ρ * (N.kraus a)ᴴ).trace = ((N.kraus a)ᴴ * N.kraus a * ρ).trace := by
    intro a
    rw [Matrix.trace_mul_cycle]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul, N.tracePreserving, Matrix.one_mul]

/-- `S_min(N) ≥ 0` for every channel. -/
theorem minOutputEntropy_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    0 ≤ minOutputEntropy N := by
  unfold minOutputEntropy
  apply Real.sInf_nonneg
  rintro r ⟨ρ, rfl⟩
  exact matEntropy_nonneg_of_state (applyMat_posSemidef N ρ.posSemidef)
    (by rw [applyMat_trace, ρ.trace_one])

/-! ### Pure states -/

/-- The row vector `⟨0|` in dimension `d`. -/
def bra0 (d : ℕ) (hd : 0 < d) : Matrix (Fin 1) (Fin d) ℂ :=
  Matrix.of fun _ j => if j = ⟨0, hd⟩ then 1 else 0

theorem bra0_mul_conj (d : ℕ) (hd : 0 < d) : bra0 d hd * (bra0 d hd)ᴴ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [bra0, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The pure state `|0⟩⟨0|` in dimension `d`. -/
def pure0 (d : ℕ) (hd : 0 < d) : DensityMatrix d where
  mat := (bra0 d hd)ᴴ * bra0 d hd
  posSemidef := posSemidef_conjTranspose_mul_self _
  trace_one := by
    rw [Matrix.trace_mul_comm, bra0_mul_conj]
    simp

theorem matEntropy_pure0 (d : ℕ) (hd : 0 < d) : matEntropy (pure0 d hd).mat = 0 := by
  apply matEntropy_eq_zero_of_idem (pure0 d hd).posSemidef.1
  show (bra0 d hd)ᴴ * bra0 d hd * ((bra0 d hd)ᴴ * bra0 d hd) = (bra0 d hd)ᴴ * bra0 d hd
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bra0 d hd), bra0_mul_conj, Matrix.one_mul]

/-! ### Identity qubit channel -/

/-- The identity channel on a qubit (one Kraus operator `I`). -/
def idQubit : QuantumChannel 2 2 where
  numKraus := 1
  kraus := fun _ => 1
  tracePreserving := by simp

theorem idQubit_apply (ρ : Matrix (Fin 2) (Fin 2) ℂ) : idQubit.applyMat ρ = ρ := by
  show (∑ _a : Fin 1, (1 : Matrix (Fin 2) (Fin 2) ℂ) * ρ * 1ᴴ) = ρ
  simp

/-- **Regression:** `S_min(id₂) = 0`. -/
theorem minOutputEntropy_idQubit : minOutputEntropy idQubit = 0 := by
  apply le_antisymm _ (minOutputEntropy_nonneg _)
  unfold minOutputEntropy
  refine csInf_le ⟨0, ?_⟩ ⟨pure0 2 (by norm_num), ?_⟩
  · rintro r ⟨ρ, rfl⟩
    exact matEntropy_nonneg_of_state (applyMat_posSemidef _ ρ.posSemidef)
      (by rw [applyMat_trace, ρ.trace_one])
  · rw [idQubit_apply, matEntropy_pure0]

theorem kronMat_one_one :
    kronMat (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kronMat, Matrix.one_apply]

theorem tensor_idQubit_apply (ρ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ) :
    tensorChannelApply idQubit idQubit ρ = ρ := by
  show (∑ _a : Fin 1, ∑ _b : Fin 1, kronMat (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 * ρ *
    (kronMat (1 : Matrix (Fin 2) (Fin 2) ℂ) 1)ᴴ) = ρ
  simp [kronMat_one_one]

/-- **Regression:** `S_min(id₂ ⊗ id₂) = 0 = S_min(id₂) + S_min(id₂)` (additivity). -/
theorem minOutputEntropyTensor_idQubit : minOutputEntropyTensor idQubit idQubit = 0 := by
  unfold minOutputEntropyTensor
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨pure0 (2 * 2) (by norm_num), ?_⟩
    · rintro r ⟨ρ, rfl⟩
      rw [tensor_idQubit_apply]
      exact matEntropy_nonneg_of_state ρ.posSemidef ρ.trace_one
    · rw [tensor_idQubit_apply, matEntropy_pure0]
  · apply Real.sInf_nonneg
    rintro r ⟨ρ, rfl⟩
    rw [tensor_idQubit_apply]
    exact matEntropy_nonneg_of_state ρ.posSemidef ρ.trace_one

theorem idQubit_additive :
    minOutputEntropyTensor idQubit idQubit = minOutputEntropy idQubit + minOutputEntropy idQubit := by
  rw [minOutputEntropyTensor_idQubit, minOutputEntropy_idQubit, add_zero]

/-! ### Qubit replacement channel `ρ ↦ I/2` -/

/-- Kraus operators `(1/2)(1, 1)ᵀ` and `(1/2)(1, -1)ᵀ`. -/
noncomputable def replKraus (a : Fin 2) : Matrix (Fin 2) (Fin 1) ℂ :=
  Matrix.of fun i _ =>
    if a = 0 then ((1 / 2 : ℝ) : ℂ) else if i = 0 then ((1 / 2 : ℝ) : ℂ) else ((-1 / 2 : ℝ) : ℂ)

/-- The qubit replacement channel `M_1 → M_2`, `ρ ↦ (Tr ρ) I/2` (entanglement-breaking). -/
noncomputable def replQubit : QuantumChannel 1 2 where
  numKraus := 2
  kraus := replKraus
  tracePreserving := by
    ext i j
    fin_cases i; fin_cases j
    simp [replKraus, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.conj_ofReal, map_ofNat]
    norm_num

private lemma densityMatrix_one (ρ : DensityMatrix 1) : ρ.mat = 1 := by
  ext i j
  fin_cases i; fin_cases j
  have := ρ.trace_one
  simpa [Matrix.trace] using this

theorem replQubit_apply (ρ : DensityMatrix 1) :
    replQubit.applyMat ρ.mat = (((1 / 2 : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [densityMatrix_one]
  show (∑ a : Fin 2, replKraus a * 1 * (replKraus a)ᴴ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [replKraus, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.conj_ofReal, map_ofNat] <;> norm_num

private lemma negPLogP_half : negPLogP (1 / 2) = 1 / 2 := by
  unfold negPLogP log2
  rw [if_neg (by norm_num), one_div, Real.log_inv]
  have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

private lemma negPLogP_quarter : negPLogP (1 / 4) = 1 / 2 := by
  unfold negPLogP log2
  rw [if_neg (by norm_num), one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_pow]
  have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp
  ring

private lemma sInf_const_set {ι : Type*} [Nonempty ι] (f : ι → ℝ) (c : ℝ) (h : ∀ i, f i = c) :
    sInf { r : ℝ | ∃ i, r = f i } = c := by
  have : { r : ℝ | ∃ i, r = f i } = {c} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, h]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Classical.arbitrary ι, h⟩⟩
  rw [this, csInf_singleton]

/-- The unique state in dimension 1. -/
def state1 : DensityMatrix 1 where
  mat := 1
  posSemidef := PosSemidef.one
  trace_one := by simp

instance : Nonempty (DensityMatrix 1) := ⟨state1⟩

instance : Nonempty (DensityMatrix (1 * 1)) := ⟨state1⟩

/-- **Regression:** `S_min(replQubit) = 1` bit (output is always `I/2`). -/
theorem minOutputEntropy_replQubit : minOutputEntropy replQubit = 1 := by
  unfold minOutputEntropy
  refine sInf_const_set _ 1 fun ρ => ?_
  rw [replQubit_apply, matEntropy_smul_one, negPLogP_half]
  norm_num

theorem tensor_replQubit_apply (ρ : DensityMatrix (1 * 1)) :
    tensorChannelApply replQubit replQubit ρ.mat =
      (((1 / 4 : ℝ) : ℂ)) • (1 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ) := by
  rw [show ρ.mat = 1 from densityMatrix_one ρ]
  show (∑ a : Fin 2, ∑ b : Fin 2, kronMat (replKraus a) (replKraus b) * 1 *
    (kronMat (replKraus a) (replKraus b))ᴴ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [replKraus, kronMat, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Complex.conj_ofReal, map_ofNat] <;> norm_num

/-- **Regression:** `S_min(R ⊗ R) = 2` bits. -/
theorem minOutputEntropyTensor_replQubit : minOutputEntropyTensor replQubit replQubit = 2 := by
  unfold minOutputEntropyTensor
  refine sInf_const_set _ 2 fun ρ => ?_
  rw [tensor_replQubit_apply, matEntropy_smul_one, negPLogP_quarter]
  norm_num

/-- **Regression:** additivity `S_min(R ⊗ R) = S_min(R) + S_min(R)` for the
(entanglement-breaking, Shor 2002) qubit replacement channel. -/
theorem replQubit_additive :
    minOutputEntropyTensor replQubit replQubit =
      minOutputEntropy replQubit + minOutputEntropy replQubit := by
  rw [minOutputEntropyTensor_replQubit, minOutputEntropy_replQubit]
  norm_num

end InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold
