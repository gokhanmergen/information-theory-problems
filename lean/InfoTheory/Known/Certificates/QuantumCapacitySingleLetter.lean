import InfoTheory.Problems.QuantumCapacitySingleLetter
import InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.QuantumCapacitySingleLetter`

The frozen statement asks for a uniform blocklength `k(d₁, d₂)` with
`Q(N) = coherentInfoRegN N k` for all channels `N : M_{d₁} → M_{d₂}`.
This file also hosts the shared quantum-capacity toolkit used by the certificates of
`QuantumCapacityDepolarizing`, `QuantumCapacityTwoPauli`, `SuperactivationQubitChannels`
and `PrivateVsQuantumCapacityGap`.

## Certified (non-junk)
* `kronMat_eq_reindex`: the Core `kronMat` is Mathlib's Kronecker product reindexed by
  `finProdFinEquiv`; hence mixed product, adjoint and identity rules (`kronMat_mul`,
  `kronMat_conjTranspose`, `kronMat_one`) and the same for `kronPowerMat`.
* `kraus_power_complete`: `∑_s (K_s)ᴴ K_s = 1` for the `n`-fold Kraus family, so
  `channelPowerApply N n ρ` is a state (`channelPowerApply_posSemidef`,
  `channelPowerApply_trace`).
* `channelPowerCompApply_eq`: the Core complementary channel (little-endian Kraus index
  unpacking) is the Gram matrix `Tr(K_i ρ K_jᴴ)` indexed via Mathlib's
  `finFunctionFinEquiv`; it is a state (`channelPowerCompApply_posSemidef`,
  `channelPowerCompApply_trace`).
* `matEntropy_le_log2_of_state`: `S(ρ) ≤ log₂ d`.
* Consequently every `sSup` in `coherentInfoRegN` / `quantumCapacity` is over a nonempty set
  bounded above (no `sSup` junk): `coherentInfoN_le`, `coherentInfoRegN_le`,
  `le_coherentInfoRegN`, `quantumCapacity_le_log2 : Q(N) ≤ log₂ d₂`,
  `coherentInfoRegN_le_quantumCapacity : Q^{(n)}(N)/n ≤ Q(N)`.
* **Regression, identity channel** `idCh d`: `coherentInfoRegN_idCh : Q^{(n)}(id_d)/n = log₂ d`
  for every `n ≥ 1` and `quantumCapacity_idCh : Q(id_d) = log₂ d`; in particular
  `quantumCapacity_idQubit : Q(id₂) = 1` and `idCh_singleLetter` (the statement's equation
  holds for the identity channel with every `k ≥ 1`).
* **Regression, reset channel** `resetCh d : ρ ↦ Tr(ρ)|0⟩⟨0|` (entanglement-breaking):
  `coherentInfoRegN_resetCh_nonpos`, `quantumCapacity_resetCh_le : Q ≤ 0`, and for the qubit
  `quantumCapacity_resetQubit : Q(reset₂) = 0`. So `quantumCapacity` is not constant and
  takes the textbook values `1` and `0` on the two extreme qubit channels.

## Not certified
* `Q(N) ≥ 0` for every channel (needs `S(N(ψ)) = S(N^c(ψ))` for pure `ψ`, i.e. equality of
  the nonzero spectra of `AAᴴ`, `AᴴA`), Devetak–Shor additivity for degradable channels, and
  the Cubitt et al. (2015) unbounded-regularization family (dimension grows with `n`).

## Adversarial check (2026-11-27)
Cubitt–Elkouss–Matthews–Ozols–Pérez-García–Strelchuk (arXiv:1408.5115, Nature Commun. 6,
6739 (2015)) build, for each `n`, a channel with `Q^{(n)} = 0 < Q`; their switched
erasure / approximate-pbit channel carries an `N`-copy shield, so its dimension grows with
`n`, and the paper explicitly leaves a constant dimension bound open. Hence the
fixed-`(d₁, d₂)` statement is neither proved nor refuted by it; no 2016–2026 resolution
found. Junk: all `sSup`s are bounded (above), so the definitions are faithful. FINE.
-/

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace InfoTheory.Known.Certificates.QuantumCapacitySingleLetter

open InfoTheory Matrix
open InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold
  (matEntropy_nonneg_of_state matEntropy_eq_zero_of_idem matEntropy_smul_one applyMat_posSemidef
    applyMat_trace pure0 matEntropy_pure0)

/-! ### Kronecker products -/

theorem kronMat_eq_reindex {m₁ n₁ m₂ n₂ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℂ) (B : Matrix (Fin m₂) (Fin n₂) ℂ) :
    kronMat A B = (A ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  rfl

theorem kronMat_mul {a b c a' b' c' : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin a') (Fin b') ℂ)
    (C : Matrix (Fin b) (Fin c) ℂ) (D : Matrix (Fin b') (Fin c') ℂ) :
    kronMat A B * kronMat C D = kronMat (A * C) (B * D) := by
  rw [kronMat_eq_reindex, kronMat_eq_reindex, kronMat_eq_reindex, submatrix_mul_equiv,
    ← mul_kronecker_mul]

theorem kronMat_conjTranspose {a b a' b' : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin a') (Fin b') ℂ) :
    (kronMat A B)ᴴ = kronMat Aᴴ Bᴴ := by
  rw [kronMat_eq_reindex, kronMat_eq_reindex, conjTranspose_submatrix, conjTranspose_kronecker]

theorem kronMat_one {a b : ℕ} :
    kronMat (1 : Matrix (Fin a) (Fin a) ℂ) (1 : Matrix (Fin b) (Fin b) ℂ) = 1 := by
  rw [kronMat_eq_reindex, one_kronecker_one, submatrix_one_equiv]

theorem kronMat_sum_left {ι : Type*} (s : Finset ι) {a b a' b' : ℕ}
    (A : ι → Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin a') (Fin b') ℂ) :
    kronMat (∑ i ∈ s, A i) B = ∑ i ∈ s, kronMat (A i) B := by
  ext i j
  simp [kronMat, Matrix.sum_apply, Finset.sum_mul]

theorem kronMat_sum_right {ι : Type*} (s : Finset ι) {a b a' b' : ℕ}
    (A : Matrix (Fin a) (Fin b) ℂ) (B : ι → Matrix (Fin a') (Fin b') ℂ) :
    kronMat A (∑ i ∈ s, B i) = ∑ i ∈ s, kronMat A (B i) := by
  ext i j
  simp [kronMat, Matrix.sum_apply, Finset.mul_sum]

theorem kronPowerMat_succ {d₁ d₂ n : ℕ} (f : Fin (n + 1) → Matrix (Fin d₂) (Fin d₁) ℂ) :
    kronPowerMat (n + 1) f = kronMat (kronPowerMat n (fun i => f i.castSucc)) (f (Fin.last n)) :=
  rfl

theorem kronPowerMat_mul {a b c : ℕ} : ∀ (n : ℕ) (A : Fin n → Matrix (Fin a) (Fin b) ℂ)
    (B : Fin n → Matrix (Fin b) (Fin c) ℂ),
    kronPowerMat n A * kronPowerMat n B = kronPowerMat n (fun i => A i * B i)
  | 0, A, B => by
    ext i j
    simp only [kronPowerMat, Matrix.mul_apply, of_apply, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, pow_zero, one_smul]
  | n + 1, A, B => by
    rw [kronPowerMat_succ, kronPowerMat_succ, kronPowerMat_succ]
    exact (kronMat_mul _ _ _ _).trans (by rw [kronPowerMat_mul n])

theorem kronPowerMat_conjTranspose {a b : ℕ} : ∀ (n : ℕ) (A : Fin n → Matrix (Fin a) (Fin b) ℂ),
    (kronPowerMat n A)ᴴ = kronPowerMat n (fun i => (A i)ᴴ)
  | 0, A => by
    ext i j
    show star (1 : ℂ) = (1 : ℂ)
    exact star_one ℂ
  | n + 1, A => by
    rw [kronPowerMat_succ, kronPowerMat_succ]
    exact (kronMat_conjTranspose _ _).trans (by rw [kronPowerMat_conjTranspose n])

theorem kronPowerMat_one {a : ℕ} : ∀ (n : ℕ),
    kronPowerMat n (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) = 1
  | 0 => by
    have : Subsingleton (Fin (a ^ 0)) := by rw [pow_zero]; infer_instance
    ext i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    rw [Matrix.one_apply_eq]
    rfl
  | n + 1 => by
    rw [kronPowerMat_succ, kronPowerMat_one n]
    exact kronMat_one

/-- Distributing a sum over all index strings through a Kronecker power. -/
theorem sum_kronPowerMat {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (G : ι → Matrix (Fin a) (Fin b) ℂ) : ∀ (n : ℕ),
    ∑ s : Fin n → ι, kronPowerMat n (fun i => G (s i)) =
      kronPowerMat n (fun _ => ∑ x, G x)
  | 0 => by
    show (∑ _s : Fin 0 → ι, (Matrix.of fun _ _ => 1 : Matrix (Fin (a ^ 0)) (Fin (b ^ 0)) ℂ)) =
      Matrix.of fun _ _ => 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Nat.pow_zero (Fintype.card ι), one_smul]
  | n + 1 => by
    rw [← (Fin.snocEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv_apply, kronPowerMat_succ, Fin.snoc_castSucc, Fin.snoc_last]
    have key : (∑ x, ∑ y : Fin n → ι, kronMat (kronPowerMat n fun i => G (y i)) (G x) :
        Matrix (Fin (a ^ n * a)) (Fin (b ^ n * b)) ℂ) =
        kronMat (kronPowerMat n fun _ => ∑ x, G x) (∑ x, G x) := by
      rw [Finset.sum_comm]
      simp_rw [← kronMat_sum_right]
      rw [← kronMat_sum_left, sum_kronPowerMat G n]
    exact key

/-! ### Tensor-power channels output states -/

theorem kraus_power_complete {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ) :
    ∑ s : Fin n → Fin N.numKraus,
      (kronPowerMat n (fun i => N.kraus (s i)))ᴴ * kronPowerMat n (fun i => N.kraus (s i)) = 1 := by
  simp_rw [kronPowerMat_conjTranspose, kronPowerMat_mul]
  rw [sum_kronPowerMat (fun a => (N.kraus a)ᴴ * N.kraus a) n, N.tracePreserving, kronPowerMat_one]

theorem channelPowerApply_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    {ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ} (hρ : ρ.PosSemidef) :
    (channelPowerApply N n ρ).PosSemidef :=
  posSemidef_sum _ fun _ _ => hρ.mul_mul_conjTranspose_same _

theorem channelPowerApply_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    (channelPowerApply N n ρ).trace = ρ.trace := by
  unfold channelPowerApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle _ ρ, ← Matrix.trace_sum, ← Finset.sum_mul, kraus_power_complete,
    Matrix.one_mul]

/-- Gram matrix `Tr(K_i ρ K_jᴴ)` of a family of operators (complementary-channel output). -/
def gramMat {ι : Type*} {a b : ℕ} (K : ι → Matrix (Fin b) (Fin a) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (K i * ρ * (K j)ᴴ).trace

theorem gramMat_posSemidef {ι : Type*} [Fintype ι] {a b : ℕ} (K : ι → Matrix (Fin b) (Fin a) ℂ)
    {ρ : Matrix (Fin a) (Fin a) ℂ} (hρ : ρ.PosSemidef) : (gramMat K ρ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [gramMat, conjTranspose_apply, of_apply]
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hρ.1.eq, Matrix.mul_assoc]
  · have key : star x ⬝ᵥ (gramMat K ρ *ᵥ x) =
        ((∑ i, star (x i) • K i) * ρ * (∑ j, star (x j) • K j)ᴴ).trace := by
      simp only [dotProduct, mulVec, gramMat, of_apply, Pi.star_apply, conjTranspose_sum,
        conjTranspose_smul, star_star, Matrix.sum_mul, Matrix.mul_sum, Finset.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [key]
    exact (hρ.mul_mul_conjTranspose_same _).trace_nonneg

theorem gramMat_trace {ι : Type*} [Fintype ι] {a b : ℕ} (K : ι → Matrix (Fin b) (Fin a) ℂ)
    (ρ : Matrix (Fin a) (Fin a) ℂ) :
    (gramMat K ρ).trace = (∑ i, K i * ρ * (K i)ᴴ).trace := by
  simp [gramMat, Matrix.trace, Matrix.sum_apply]
  rw [Finset.sum_comm]

/-- The Core complementary channel is the Gram matrix of the `n`-fold Kraus family indexed
by Mathlib's `finFunctionFinEquiv` (little-endian digits). -/
theorem channelPowerCompApply_eq {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    channelPowerCompApply N n ρ =
      gramMat (fun idx : Fin (N.numKraus ^ n) =>
        kronPowerMat n (fun i => N.kraus (finFunctionFinEquiv.symm idx i))) ρ := by
  ext idx₁ idx₂
  simp only [channelPowerCompApply, gramMat, of_apply]
  congr 4 <;> (funext i; congr 1; ext; simp [finFunctionFinEquiv_symm_apply_val])

theorem channelPowerCompApply_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    {ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ} (hρ : ρ.PosSemidef) :
    (channelPowerCompApply N n ρ).PosSemidef := by
  rw [channelPowerCompApply_eq]
  exact gramMat_posSemidef _ hρ

theorem channelPowerCompApply_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    (channelPowerCompApply N n ρ).trace = ρ.trace := by
  rw [channelPowerCompApply_eq, gramMat_trace, ← channelPowerApply_trace N n ρ]
  unfold channelPowerApply
  exact congrArg Matrix.trace
    (finFunctionFinEquiv.symm.sum_comp (fun s : Fin n → Fin N.numKraus =>
      kronPowerMat n (fun i => N.kraus (s i)) * ρ * (kronPowerMat n (fun i => N.kraus (s i)))ᴴ))

/-! ### Entropy bounds -/

theorem matEntropy_le_log2_of_state {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.PosSemidef) (htr : M.trace = 1) : matEntropy M ≤ log2 d := by
  unfold matEntropy
  rw [dif_pos hM.1]
  have hsum : ∑ i, hM.1.eigenvalues i = 1 := by
    have := hM.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 : ((∑ i, hM.1.eigenvalues i : ℝ) : ℂ) = 1 := by
      rw [this]; push_cast; rfl
    exact_mod_cast h2
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [log2]
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let P : ProbDist (Fin d) := ⟨fun i => hM.1.eigenvalues i, hM.eigenvalues_nonneg, hsum⟩
  have := InfoTheory.Bridge.shannonEntropy_le_log2_card P
  simpa [shannonEntropy, P] using this

theorem log2_natCast_nonneg (d : ℕ) : 0 ≤ log2 (d : ℝ) :=
  div_nonneg (Real.log_natCast_nonneg d) (Real.log_nonneg one_le_two)

theorem log2_pow (d n : ℕ) : log2 ((d ^ n : ℕ) : ℝ) = n * log2 d := by
  unfold log2
  rw [Nat.cast_pow, Real.log_pow]
  ring

/-! ### Coherent information and quantum capacity are well defined -/

theorem coherentInfoN_le {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : DensityMatrix (d₁ ^ n)) : coherentInfoN N n ρ ≤ n * log2 d₂ := by
  unfold coherentInfoN
  have hB := matEntropy_le_log2_of_state (channelPowerApply_posSemidef N n ρ.posSemidef)
    (by rw [channelPowerApply_trace, ρ.trace_one])
  have hE := matEntropy_nonneg_of_state (channelPowerCompApply_posSemidef N n ρ.posSemidef)
    (by rw [channelPowerCompApply_trace, ρ.trace_one])
  rw [log2_pow] at hB
  linarith

theorem coherentInfoRegN_bddAbove {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) {n : ℕ} (hn : 0 < n) :
    BddAbove { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) } := by
  refine ⟨log2 d₂, ?_⟩
  rintro r ⟨ρ, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  linarith [coherentInfoN_le N n ρ]

theorem coherentInfoRegN_le {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) {n : ℕ} (hn : 0 < n) :
    coherentInfoRegN N n ≤ log2 d₂ := by
  unfold coherentInfoRegN
  refine Real.sSup_le ?_ (log2_natCast_nonneg d₂)
  rintro r ⟨ρ, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  linarith [coherentInfoN_le N n ρ]

theorem le_coherentInfoRegN {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) {n : ℕ} (hn : 0 < n)
    (ρ : DensityMatrix (d₁ ^ n)) : coherentInfoN N n ρ / n ≤ coherentInfoRegN N n :=
  le_csSup (coherentInfoRegN_bddAbove N hn) ⟨ρ, rfl⟩

theorem quantumCapacity_bddAbove {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    BddAbove { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN N n } := by
  refine ⟨log2 d₂, ?_⟩
  rintro r ⟨n, hn, rfl⟩
  exact coherentInfoRegN_le N hn

/-- `Q(N) ≤ log₂ d₂`: the capacity `sSup` is over a bounded set. -/
theorem quantumCapacity_le_log2 {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    quantumCapacity N ≤ log2 d₂ := by
  unfold quantumCapacity
  refine Real.sSup_le ?_ (log2_natCast_nonneg d₂)
  rintro r ⟨n, hn, rfl⟩
  exact coherentInfoRegN_le N hn

theorem coherentInfoRegN_le_quantumCapacity {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) {n : ℕ}
    (hn : 0 < n) : coherentInfoRegN N n ≤ quantumCapacity N :=
  le_csSup (quantumCapacity_bddAbove N) ⟨n, hn, rfl⟩

/-- Upper bound on `Q` from a uniform bound on all `n`-letter coherent informations. -/
theorem quantumCapacity_le_of_forall {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, 0 < n → ∀ ρ : DensityMatrix (d₁ ^ n), coherentInfoN N n ρ ≤ n * c) :
    quantumCapacity N ≤ c := by
  unfold quantumCapacity
  refine Real.sSup_le ?_ hc
  rintro r ⟨n, hn, rfl⟩
  unfold coherentInfoRegN
  refine Real.sSup_le ?_ hc
  rintro r ⟨ρ, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  linarith [h n hn ρ]

/-! ### Maximally mixed state -/

/-- The maximally mixed state `I/m` on `ℂ^m`. -/
noncomputable def maxMixed (m : ℕ) (hm : 0 < m) : DensityMatrix m where
  mat := (((1 / m : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)
  posSemidef := by
    refine PosSemidef.smul PosSemidef.one ?_
    have : (0 : ℝ) ≤ 1 / m := by positivity
    exact_mod_cast this
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp

theorem matEntropy_maxMixed (m : ℕ) (hm : 0 < m) : matEntropy (maxMixed m hm).mat = log2 m := by
  show matEntropy ((((1 / m : ℝ)) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) = _
  rw [matEntropy_smul_one]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold negPLogP log2
  rw [if_neg (not_le.mpr (by positivity)), one_div, Real.log_inv]
  field_simp

/-! ### Regression: identity channel, `Q(id_d) = log₂ d` -/

/-- The identity channel on `ℂ^d` (one Kraus operator `I`). -/
def idCh (d : ℕ) : QuantumChannel d d where
  numKraus := 1
  kraus := fun _ => 1
  tracePreserving := by simp

theorem channelPowerApply_idCh (d n : ℕ) (ρ : Matrix (Fin (d ^ n)) (Fin (d ^ n)) ℂ) :
    channelPowerApply (idCh d) n ρ = ρ := by
  show (∑ _s : Fin n → Fin 1, kronPowerMat n (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) * ρ *
    (kronPowerMat n (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)))ᴴ) = ρ
  simp [kronPowerMat_one]

theorem channelPowerCompApply_idCh (d n : ℕ) (ρ : DensityMatrix (d ^ n)) :
    channelPowerCompApply (idCh d) n ρ.mat = Matrix.of fun _ _ => 1 := by
  rw [channelPowerCompApply_eq]
  ext i j
  show (kronPowerMat n (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) * ρ.mat *
    (kronPowerMat n (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)))ᴴ).trace = 1
  simp [kronPowerMat_one, ρ.trace_one]

theorem matEntropy_ones_one (n : ℕ) :
    matEntropy (Matrix.of fun (_ : Fin (1 ^ n)) (_ : Fin (1 ^ n)) => (1 : ℂ)) = 0 := by
  apply matEntropy_eq_zero_of_idem
  · ext i j; simp
  · ext i j; simp [Matrix.mul_apply]

theorem coherentInfoN_idCh (d n : ℕ) (ρ : DensityMatrix (d ^ n)) :
    coherentInfoN (idCh d) n ρ = matEntropy ρ.mat := by
  unfold coherentInfoN
  rw [channelPowerApply_idCh, channelPowerCompApply_idCh]
  have := matEntropy_ones_one n
  rw [sub_eq_self]
  exact this

/-- **Regression:** `Q^{(n)}(id_d)/n = log₂ d` for every `n ≥ 1`. -/
theorem coherentInfoRegN_idCh (d : ℕ) (hd : 0 < d) {n : ℕ} (hn : 0 < n) :
    coherentInfoRegN (idCh d) n = log2 d := by
  refine le_antisymm (coherentInfoRegN_le _ hn) ?_
  have hpow : 0 < d ^ n := pow_pos hd n
  have := le_coherentInfoRegN (idCh d) hn (maxMixed (d ^ n) hpow)
  rw [coherentInfoN_idCh, matEntropy_maxMixed, log2_pow] at this
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rwa [mul_div_cancel_left₀ _ hn'] at this

/-- **Regression:** `Q(id_d) = log₂ d`. -/
theorem quantumCapacity_idCh (d : ℕ) (hd : 0 < d) : quantumCapacity (idCh d) = log2 d := by
  refine le_antisymm (quantumCapacity_le_log2 _) ?_
  rw [← coherentInfoRegN_idCh d hd one_pos]
  exact coherentInfoRegN_le_quantumCapacity _ one_pos

/-- **Regression:** the noiseless qubit has quantum capacity exactly one qubit per use. -/
theorem quantumCapacity_idQubit : quantumCapacity (idCh 2) = 1 := by
  rw [quantumCapacity_idCh 2 two_pos]
  unfold log2
  push_cast
  exact div_self (Real.log_pos one_lt_two).ne'

/-- The statement's equation `Q(N) = Q^{(k)}(N)/k` holds for the identity channel with every
`k ≥ 1` (consistency check of the frozen objects). -/
theorem idCh_singleLetter (d : ℕ) (hd : 0 < d) {k : ℕ} (hk : 0 < k) :
    quantumCapacity (idCh d) = coherentInfoRegN (idCh d) k := by
  rw [quantumCapacity_idCh d hd, coherentInfoRegN_idCh d hd hk]

/-! ### Regression: reset channel `ρ ↦ Tr(ρ)|0⟩⟨0|`, `Q = 0` -/

/-- Column vector `|0⟩`. -/
def ket0 (d : ℕ) (hd : 0 < d) : Matrix (Fin d) (Fin 1) ℂ :=
  Matrix.of fun i _ => if i = ⟨0, hd⟩ then 1 else 0

/-- Row vector `⟨a|`. -/
def braE {d : ℕ} (a : Fin d) : Matrix (Fin 1) (Fin d) ℂ :=
  Matrix.of fun _ j => if j = a then 1 else 0

theorem ket0_conj_mul (d : ℕ) (hd : 0 < d) : (ket0 d hd)ᴴ * ket0 d hd = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [ket0, Matrix.mul_apply, conjTranspose_apply]

theorem sum_braE (d : ℕ) : ∑ a : Fin d, (braE a)ᴴ * braE a = 1 := by
  ext i j
  simp [braE, Matrix.mul_apply, conjTranspose_apply, Matrix.sum_apply, Matrix.one_apply]

/-- The reset (replacement-by-`|0⟩`) channel on `ℂ^d`, Kraus operators `|0⟩⟨a|`. -/
def resetCh (d : ℕ) (hd : 0 < d) : QuantumChannel d d where
  numKraus := d
  kraus := fun a => ket0 d hd * braE a
  tracePreserving := by
    simp_rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ket0 d hd)ᴴ,
      ket0_conj_mul, Matrix.one_mul]
    exact sum_braE d

/-- The trace-out channel `M_d → M_1`, Kraus operators `⟨a|`. -/
def traceCh (d : ℕ) : QuantumChannel d 1 where
  numKraus := d
  kraus := braE
  tracePreserving := sum_braE d

theorem eq_one_of_trace_one {n : ℕ} {C : Matrix (Fin (1 ^ n)) (Fin (1 ^ n)) ℂ}
    (h : C.trace = 1) : C = 1 := by
  have hs : Subsingleton (Fin (1 ^ n)) := by rw [one_pow]; infer_instance
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst hij
  have : C.trace = C i i := by
    unfold Matrix.trace
    rw [Fintype.sum_subsingleton _ i]
    rfl
  rw [Matrix.one_apply_eq, ← this, h]

/-- A channel all of whose Kraus operators have the form `u ⟨b_a|` for a fixed unit column
`u` ("constant pure output"); `r = 1` is kept as a hypothesis so that `Fin (1 * 1)`-typed
columns (tensor products) are accepted. -/
theorem channelPowerApply_constOut {d₁ d₂ r : ℕ} (hr : r = 1) (N : QuantumChannel d₁ d₂)
    (u : Matrix (Fin d₂) (Fin r) ℂ) (hu : uᴴ * u = 1)
    (B : Fin N.numKraus → Matrix (Fin r) (Fin d₁) ℂ) (hK : ∀ a, N.kraus a = u * B a)
    (n : ℕ) (ρ : DensityMatrix (d₁ ^ n)) :
    channelPowerApply N n ρ.mat = kronPowerMat n (fun _ => u) * (kronPowerMat n (fun _ => u))ᴴ := by
  subst hr
  have hTP : ∑ a, (B a)ᴴ * B a = 1 := by
    have h := N.tracePreserving
    simp_rw [hK, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hu,
      Matrix.one_mul] at h
    exact h
  let T : QuantumChannel d₁ 1 := ⟨N.numKraus, B, hTP⟩
  set U := kronPowerMat n (fun _ => u)
  have h1 : channelPowerApply N n ρ.mat = ∑ s : Fin n → Fin N.numKraus,
      U * (kronPowerMat n (fun i => B (s i)) * ρ.mat *
        (kronPowerMat n (fun i => B (s i)))ᴴ) * Uᴴ := by
    refine Finset.sum_congr rfl fun s _ => ?_
    show kronPowerMat n (fun i => N.kraus (s i)) * ρ.mat *
      (kronPowerMat n (fun i => N.kraus (s i)))ᴴ = _
    rw [show kronPowerMat n (fun i => N.kraus (s i)) =
      U * kronPowerMat n (fun i => B (s i)) by
        simp_rw [hK]; exact (kronPowerMat_mul n _ _).symm, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hC : (∑ s : Fin n → Fin N.numKraus, kronPowerMat n (fun i => B (s i)) * ρ.mat *
      (kronPowerMat n (fun i => B (s i)))ᴴ) = 1 := by
    refine eq_one_of_trace_one ?_
    rw [show (∑ s : Fin n → Fin N.numKraus, kronPowerMat n (fun i => B (s i)) * ρ.mat *
      (kronPowerMat n (fun i => B (s i)))ᴴ) = channelPowerApply T n ρ.mat from rfl,
      channelPowerApply_trace, ρ.trace_one]
  rw [h1, ← Matrix.sum_mul, ← Matrix.mul_sum, hC, Matrix.mul_one]

theorem coherentInfoN_constOut_nonpos {d₁ d₂ r : ℕ} (hr : r = 1) (N : QuantumChannel d₁ d₂)
    (u : Matrix (Fin d₂) (Fin r) ℂ) (hu : uᴴ * u = 1)
    (B : Fin N.numKraus → Matrix (Fin r) (Fin d₁) ℂ) (hK : ∀ a, N.kraus a = u * B a)
    (n : ℕ) (ρ : DensityMatrix (d₁ ^ n)) : coherentInfoN N n ρ ≤ 0 := by
  have hB : matEntropy (channelPowerApply N n ρ.mat) = 0 := by
    rw [channelPowerApply_constOut hr N u hu B hK]
    set U := kronPowerMat n (fun _ => u)
    have hU : Uᴴ * U = 1 := by
      rw [kronPowerMat_conjTranspose, kronPowerMat_mul]
      simp_rw [hu]
      exact kronPowerMat_one n
    apply matEntropy_eq_zero_of_idem (isHermitian_mul_conjTranspose_self U)
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  unfold coherentInfoN
  rw [hB]
  have := matEntropy_nonneg_of_state (channelPowerCompApply_posSemidef N n
    ρ.posSemidef) (by rw [channelPowerCompApply_trace, ρ.trace_one])
  linarith

/-- Constant-pure-output channels have `Q ≤ 0`. -/
theorem quantumCapacity_constOut_le {d₁ d₂ r : ℕ} (hr : r = 1) (N : QuantumChannel d₁ d₂)
    (u : Matrix (Fin d₂) (Fin r) ℂ) (hu : uᴴ * u = 1)
    (B : Fin N.numKraus → Matrix (Fin r) (Fin d₁) ℂ) (hK : ∀ a, N.kraus a = u * B a) :
    quantumCapacity N ≤ 0 :=
  quantumCapacity_le_of_forall _ le_rfl fun n _ ρ => by
    simpa using coherentInfoN_constOut_nonpos hr N u hu B hK n ρ

theorem coherentInfoN_resetCh_nonpos (d : ℕ) (hd : 0 < d) (n : ℕ) (ρ : DensityMatrix (d ^ n)) :
    coherentInfoN (resetCh d hd) n ρ ≤ 0 :=
  coherentInfoN_constOut_nonpos rfl (resetCh d hd) (ket0 d hd) (ket0_conj_mul d hd) braE
    (fun _ => rfl) n ρ

theorem coherentInfoRegN_resetCh_nonpos (d : ℕ) (hd : 0 < d) (n : ℕ) :
    coherentInfoRegN (resetCh d hd) n ≤ 0 := by
  unfold coherentInfoRegN
  refine Real.sSup_nonpos ?_
  rintro r ⟨ρ, rfl⟩
  exact div_nonpos_of_nonpos_of_nonneg (coherentInfoN_resetCh_nonpos d hd n ρ) (Nat.cast_nonneg n)

/-- **Regression:** the reset channel has `Q ≤ 0`. -/
theorem quantumCapacity_resetCh_le (d : ℕ) (hd : 0 < d) : quantumCapacity (resetCh d hd) ≤ 0 :=
  quantumCapacity_constOut_le rfl (resetCh d hd) (ket0 d hd) (ket0_conj_mul d hd) braE
    (fun _ => rfl)

theorem finFunctionFinEquiv_symm_two (i : Fin (2 ^ 1)) (l : Fin 1) :
    (finFunctionFinEquiv.symm i l : Fin 2) = if (i : ℕ) = 0 then 0 else 1 := by
  have hl : (l : ℕ) = 0 := by omega
  have hi : (i : ℕ) < 2 := i.2
  ext
  rw [finFunctionFinEquiv_symm_apply_val, hl, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hi]
  split_ifs with h <;> simp <;> omega

/-- The environment output of the qubit reset channel on `|0⟩⟨0|` is `|0⟩⟨0|`. -/
theorem channelPowerCompApply_resetQubit_pure0 :
    channelPowerCompApply (resetCh 2 two_pos) 1 (pure0 (2 ^ 1) (by norm_num)).mat =
      (pure0 (2 ^ 1) (by norm_num)).mat := by
  rw [channelPowerCompApply_eq]
  show gramMat (fun idx : Fin (2 ^ 1) => kronPowerMat 1
    (fun i => ket0 2 two_pos * braE (d := 2) (finFunctionFinEquiv.symm idx i))) _ = _
  simp only [finFunctionFinEquiv_symm_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramMat, kronPowerMat, kronMat, ket0, braE, pure0,
      InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold.bra0, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_two, conjTranspose_apply]

theorem coherentInfoN_resetQubit_pure0 :
    coherentInfoN (resetCh 2 two_pos) 1 (pure0 (2 ^ 1) (by norm_num)) = 0 := by
  have hB := coherentInfoN_resetCh_nonpos 2 two_pos 1 (pure0 (2 ^ 1) (by norm_num))
  refine le_antisymm hB ?_
  have hE : matEntropy (channelPowerCompApply (resetCh 2 two_pos) 1
      (pure0 (2 ^ 1) (by norm_num)).mat) = 0 := by
    rw [channelPowerCompApply_resetQubit_pure0]
    exact matEntropy_pure0 _ _
  unfold coherentInfoN
  rw [hE, sub_zero]
  exact matEntropy_nonneg_of_state (channelPowerApply_posSemidef _ 1 (pure0 _ _).posSemidef)
    (by rw [channelPowerApply_trace, (pure0 _ _).trace_one])

/-- **Regression:** the qubit reset channel (entanglement-breaking) has `Q = 0`. -/
theorem quantumCapacity_resetQubit : quantumCapacity (resetCh 2 two_pos) = 0 := by
  refine le_antisymm (quantumCapacity_resetCh_le 2 two_pos) ?_
  have h1 := le_coherentInfoRegN (resetCh 2 two_pos) one_pos (pure0 (2 ^ 1) (by norm_num))
  rw [coherentInfoN_resetQubit_pure0, zero_div] at h1
  exact h1.trans (coherentInfoRegN_le_quantumCapacity _ one_pos)

end InfoTheory.Known.Certificates.QuantumCapacitySingleLetter
