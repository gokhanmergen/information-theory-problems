import InfoTheory.Bridge.CoverThomas
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Quantum Information Theory Foundations (`InfoTheory.Bridge.Quantum`)

Machine-checked foundational library built directly against `InfoTheory.Core.Quantum`
(zero `sorry`, standard Lean axioms only):

1. **Von Neumann Entropy & `matEntropy` Basics**:
   - Eigenvalue multiset invariance under characteristic-polynomial equality
     (`hermitian_eigenvalues_multiset_eq_of_charpoly_eq`, `matEntropy_eq_of_charpoly_eq`)
   - Unitary conjugation invariance (`matEntropy_unitary_conj`), permutation/reindexing invariance
     (`matEntropy_submatrix_equiv`), transpose invariance (`matEntropy_transpose`),
     and SVD / purification symmetry `S(M Mᴴ) = S(Mᴴ M)`
     (`matEntropy_mul_conjTranspose_eq_conjTranspose_mul`)
   - Diagonal entropy `matEntropy (diagonal P) = shannonEntropy P` (`matEntropy_diag`)
   - Non-negativity (`vonNeumannEntropy_nonneg`), dimension bound (`vonNeumannEntropy_le_log2`),
     and **concavity of von Neumann entropy** (`vonNeumannEntropy_concave`) via Peierls' inequality
   - Pure states (`pureState`, `vonNeumannEntropy_pure`) and maximally mixed states
     (`maxMixedState`, `vonNeumannEntropy_maxMixed`)

2. **Kronecker Product, Partial Trace, Partial Transpose, Peres–Horodecki PPT Criterion, & Bell State**:
   - `kronMat` algebra (`kronMat_conjTranspose`, `kronMat_mul`, `kronMat_one`, `kronMat_posSemidef`,
     `kronMat_trace`, `kronDensity`) and additivity of entropy on product states (`matEntropy_kronMat`)
   - Partial trace (`partialTraceA/B_isHermitian`, `partialTraceA/B_posSemidef`,
     `partialTraceA/B_trace`, `partialTraceA/B_kronMat`)
   - Partial transpose (`partialTransposeB_isHermitian`, `partialTransposeB_trace`,
     `partialTransposeB_kronMat`, `partialTransposeB_add`, `partialTransposeB_smul`)
   - **Peres–Horodecki PPT Criterion** (`isPPT_of_isSeparable`)
   - **Bell State `|Φ⁺⟩`** (`bellStatePhiPlus`): zero entropy, maximally mixed reduced state,
     `¬ IsPPT`, `¬ IsSeparable`, and `1`-copy `IsDistillable`

3. **Trace Distance Basics**:
   - `traceDistance_nonneg`, `traceDistance_self`, `traceDistance_symm`,
     `traceDistance_le_one`, `traceDistance_eq_zero_iff`

4. **Quantum Channels, Capacities, Explicit Channels, & `d = 2` SIC-POVM**:
   - `applyMat` and `complementaryMat` preserve Hermiticity, PSD, and trace
     (`applyDensity`, `complementaryDensity`), plus `n`-fold power preservation
   - Purification symmetry for channels on pure states
     (`applyMat_pureState_entropy_eq_complementary`)
   - Bounds on `minOutputEntropy`, `coherentInfoN`, `quantumCapacity`, and `privateCapacity`
   - **Identity channel** (`idQuantumChannel`, `minOutputEntropy = 0`, `quantumCapacity = log2 d`)
   - **Replacement / constant channel** (`constQuantumChannel`, `quantumCapacity = 0`)
   - **Qubit depolarizing channel** (`depolarizingChannel`, `IsDepolarizingChannel`)
   - **Qubit two-Pauli channel** (`twoPauliChannel`, `IsTwoPauliChannel`)
   - **Tetrahedron `d = 2` SIC-POVM** (`exists_sicPovm_two`)
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Bridge

/-! ### Private Arithmetic, Matrix, and Spectral Helpers -/

section PrivateHelpers

private lemma sum_fin_pow_zero {m : ℕ} (f : Fin (m ^ 0) → ℂ) :
    ∑ j : Fin (m ^ 0), f j = f ⟨0, by simp⟩ :=
  Fin.sum_univ_one f

private lemma negPLogP_one : negPLogP 1 = 0 := by
  simp [negPLogP, log2]

private lemma mul_right_add_div {a b d : ℕ} (hb : b < d) : (a * d + b) / d = a := by
  have hd : 0 < d := Nat.pos_of_ne_zero (by omega)
  rw [mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt hb, add_zero]

private lemma mul_right_add_mod {a b d : ℕ} (hb : b < d) : (a * d + b) % d = b := by
  rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private lemma div_lt_pow_of_lt_pow_succ {x d n : ℕ} (h : x < d ^ (n + 1)) : x / d < d ^ n :=
  Nat.div_lt_of_lt_mul (by rw [mul_comm, ← pow_succ]; exact h)

private lemma posSemidef_sum {ι : Type*} {d : ℕ} (s : Finset ι)
    (f : ι → Matrix (Fin d) (Fin d) ℂ) (hf : ∀ i ∈ s, (f i).PosSemidef) :
    (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma isHermitian_sum {ι : Type*} {d : ℕ} (s : Finset ι)
    (f : ι → Matrix (Fin d) (Fin d) ℂ) (hf : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma posSemidef_smul_real {d : ℕ} {r : ℝ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.PosSemidef) (hr : 0 ≤ r) : ((r : ℂ) • M).PosSemidef := by
  have hrc : (0 : ℂ) ≤ (r : ℂ) := Complex.zero_le_real.mpr hr
  exact hM.smul hrc

private lemma ofReal_sq_norm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma ofReal_sq_norm' (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  rw [mul_comm, ofReal_sq_norm]

private lemma finMulIdx {m n : ℕ} (a : Fin m) (b : Fin n) : a.1 * n + b.1 < m * n := by
  calc a.1 * n + b.1 < a.1 * n + n := Nat.add_lt_add_left b.2 _
    _ = (a.1 + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right n a.2

private def finPairEquiv (m n : ℕ) : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := ⟨p.1.1 * n + p.2.1, finMulIdx p.1 p.2⟩
  invFun i :=
    have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ i.2)
    (⟨i.1 / n, Nat.div_lt_of_lt_mul (by have := i.2; nlinarith)⟩,
     ⟨i.1 % n, Nat.mod_lt _ hn⟩)
  left_inv p := by
    ext
    · exact mul_right_add_div p.2.2
    · exact mul_right_add_mod p.2.2
  right_inv i := by
    ext
    dsimp only
    rw [mul_comm, Nat.div_add_mod]

private lemma sum_fin_mul {β : Type*} [AddCommMonoid β] {m n : ℕ} (f : Fin (m * n) → β) :
    ∑ i : Fin (m * n), f i = ∑ a : Fin m, ∑ b : Fin n, f ⟨a.1 * n + b.1, finMulIdx a b⟩ := by
  rw [← (finPairEquiv m n).sum_comp, Fintype.sum_prod_type]
  rfl

private lemma densityMatrix_ext {d : ℕ} {ρ σ : DensityMatrix d} (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ; cases σ; simp only [DensityMatrix.mk.injEq]; exact h

private lemma densityMatrix_dim_pos {d : ℕ} (ρ : DensityMatrix d) : 0 < d := by
  by_contra h
  have hd : d = 0 := Nat.eq_zero_of_not_pos h
  subst hd
  have htr : ρ.mat.trace = 0 := by simp [Matrix.trace]
  rw [ρ.trace_one] at htr
  exact one_ne_zero htr

private lemma unitary_mul_conjTranspose {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    U * Uᴴ = 1 :=
  mul_eq_one_comm.mp hU

private lemma spectral_decomp {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    let U : Matrix (Fin d) (Fin d) ℂ := hA.eigenvectorUnitary
    A = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
  intro U
  have h := hA.spectral_theorem
  simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using h

private lemma spectral_unitary_mul_left {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2)

private lemma spectral_unitary_mul_right {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2)

private lemma posSemidef_exists_mul_conjTranspose {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) : ∃ S : Matrix (Fin d) (Fin d) ℂ, A = S * Sᴴ := by
  let U : Matrix (Fin d) (Fin d) ℂ := hA.isHermitian.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => ((Real.sqrt (hA.isHermitian.eigenvalues i) : ℝ) : ℂ))
  refine ⟨U * D, ?_⟩
  have hD_herm : Dᴴ = D := by
    ext i j
    by_cases h : i = j
    · subst h; simp [D]
    · simp [D, h, Ne.symm h]
  have hDD : D * D = Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
  calc A = U * Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * Uᴴ :=
        spectral_decomp hA.isHermitian
    _ = U * (D * D) * Uᴴ := by rw [hDD]
    _ = (U * D) * (Dᴴ * Uᴴ) := by rw [hD_herm]; simp only [Matrix.mul_assoc]
    _ = (U * D) * (U * D)ᴴ := by rw [Matrix.conjTranspose_mul]

private def permMatrix {α β : Type*} [DecidableEq β] (e : α ≃ β) : Matrix α β ℂ :=
  Matrix.of fun i j => if e i = j then 1 else 0

private lemma permMatrix_conjTranspose_mul {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    (permMatrix e)ᴴ * permMatrix e = 1 := by
  ext i j
  simp only [Matrix.mul_apply, permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm i)]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro a _ ha
    have hne : e a ≠ i := fun heq => ha (e.injective (by simp [heq]))
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma submatrix_eq_perm_conj {α β : Type*} [Fintype β]
    [DecidableEq β] (e : α ≃ β) (M : Matrix β β ℂ) :
    M.submatrix e e = permMatrix e * M * (permMatrix e)ᴴ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, permMatrix, Matrix.conjTranspose_apply,
    Matrix.of_apply]
  rw [Finset.sum_eq_single (e j)]
  · rw [Finset.sum_eq_single (e i)]
    · simp
    · intro k _ hk; simp [hk.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l _ hl; simp [hl.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma multiset_map_roots_prod_X_sub_C {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∏ i : ι, (Polynomial.X - Polynomial.C (f i : ℂ))).roots =
      Finset.univ.val.map (fun i => (f i : ℂ)) := by
  have hne : ∏ i : ι, (Polynomial.X - Polynomial.C (f i : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_prod _ _ hne]
  simp only [Polynomial.roots_X_sub_C]
  exact Multiset.bind_singleton _ _

end PrivateHelpers

/-! ### Section 1: Von Neumann Entropy & `matEntropy` Basics -/

section VonNeumannEntropy

/-- `negPLogP` is concave on `[0, ∞)`, inherited from Mathlib's `Real.concaveOn_negMulLog`. -/
theorem concaveOn_negPLogP : ConcaveOn ℝ (Set.Ici 0) negPLogP := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : (0 : ℝ) ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (le_of_lt hlog2)
  have hscaled : ConcaveOn ℝ (Set.Ici 0) (fun x => (Real.log 2)⁻¹ * Real.negMulLog x) :=
    Real.concaveOn_negMulLog.smul hinv
  refine hscaled.congr fun x hx => ?_
  have hx0 : 0 ≤ x := hx
  by_cases hle : x ≤ 0
  · have hxzero : x = 0 := le_antisymm hle hx0
    simp [hxzero, negPLogP, Real.negMulLog]
  · simp only [negPLogP, hle, ↓reduceIte, log2, Real.negMulLog]
    ring

/-- Two Hermitian matrices with the same characteristic polynomial have the same multiset of
    real eigenvalues. -/
theorem hermitian_eigenvalues_multiset_eq_of_charpoly_eq {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcp : A.charpoly = B.charpoly) :
    Finset.univ.val.map hA.eigenvalues = Finset.univ.val.map hB.eigenvalues := by
  have h1 : A.charpoly = ∏ i : Fin d, (Polynomial.X - Polynomial.C (hA.eigenvalues i : ℂ)) :=
    hA.charpoly_eq
  have h2 : B.charpoly = ∏ i : Fin d, (Polynomial.X - Polynomial.C (hB.eigenvalues i : ℂ)) :=
    hB.charpoly_eq
  have hprod :
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (hA.eigenvalues i : ℂ)) =
        ∏ i : Fin d, (Polynomial.X - Polynomial.C (hB.eigenvalues i : ℂ)) :=
    h1.symm.trans (hcp.trans h2)
  have hroots := congrArg Polynomial.roots hprod
  rw [multiset_map_roots_prod_X_sub_C, multiset_map_roots_prod_X_sub_C] at hroots
  have hre := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at hre
  exact hre

/-- Any symmetric spectral sum `∑ i, f (λ_i)` depends only on the characteristic polynomial of a
    Hermitian matrix. -/
theorem hermitian_sum_eigenvalues_eq_of_charpoly_eq {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcp : A.charpoly = B.charpoly) (f : ℝ → ℝ) :
    ∑ i : Fin d, f (hA.eigenvalues i) = ∑ i : Fin d, f (hB.eigenvalues i) := by
  change (Finset.univ.val.map (fun i => f (hA.eigenvalues i))).sum =
    (Finset.univ.val.map (fun i => f (hB.eigenvalues i))).sum
  rw [show (fun i => f (hA.eigenvalues i)) = f ∘ hA.eigenvalues from rfl,
      show (fun i => f (hB.eigenvalues i)) = f ∘ hB.eigenvalues from rfl,
      ← Multiset.map_map, ← Multiset.map_map,
      hermitian_eigenvalues_multiset_eq_of_charpoly_eq hA hB hcp]

/-- Two Hermitian matrices with equal characteristic polynomials have equal `matEntropy`. -/
theorem matEntropy_eq_of_charpoly_eq {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hcp : A.charpoly = B.charpoly) :
    matEntropy A = matEntropy B := by
  simp only [matEntropy, hA, hB, ↓reduceDIte]
  exact hermitian_sum_eigenvalues_eq_of_charpoly_eq hA hB hcp negPLogP

/-- For any density matrix `ρ`, `matEntropy ρ.mat = vonNeumannEntropy ρ`. -/
@[simp]
theorem matEntropy_eq_vonNeumannEntropy {d : ℕ} (ρ : DensityMatrix d) :
    matEntropy ρ.mat = vonNeumannEntropy ρ := by
  simp [matEntropy, vonNeumannEntropy, ρ.posSemidef.isHermitian]

/-- The eigenvalues of a density matrix `ρ : DensityMatrix d` form a `ProbDist (Fin d)`. -/
noncomputable def eigenvalues_probDist {d : ℕ} (ρ : DensityMatrix d) : ProbDist (Fin d) where
  pmf := ρ.posSemidef.isHermitian.eigenvalues
  nonneg := ρ.posSemidef.eigenvalues_nonneg
  sum_one := by
    have htr := ρ.posSemidef.isHermitian.trace_eq_sum_eigenvalues
    rw [ρ.trace_one] at htr
    have hre := congrArg Complex.re htr
    simpa [Complex.re_sum] using hre.symm

/-- Non-negativity of von Neumann entropy: `0 ≤ S(ρ)`. -/
theorem vonNeumannEntropy_nonneg {d : ℕ} (ρ : DensityMatrix d) :
    0 ≤ vonNeumannEntropy ρ :=
  shannonEntropy_nonneg (eigenvalues_probDist ρ)

/-- Maximum entropy bound for a `d`-dimensional density matrix: `S(ρ) ≤ log₂ d`. -/
theorem vonNeumannEntropy_le_log2 {d : ℕ} (ρ : DensityMatrix d) (hd : 0 < d) :
    vonNeumannEntropy ρ ≤ log2 d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  change shannonEntropy (eigenvalues_probDist ρ) ≤ log2 d
  simpa using shannonEntropy_le_log2_card (eigenvalues_probDist ρ)

/-- Non-negativity of `matEntropy` for any positive semidefinite matrix of trace `1`. -/
theorem matEntropy_nonneg_of_posSemidef_trace_one {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hpos : M.PosSemidef) (htr : M.trace = 1) : 0 ≤ matEntropy M := by
  let ρ : DensityMatrix d := ⟨M, hpos, htr⟩
  rw [show M = ρ.mat from rfl, matEntropy_eq_vonNeumannEntropy]
  exact vonNeumannEntropy_nonneg ρ

/-- Upper bound `matEntropy M ≤ log₂ d` for any positive semidefinite matrix of trace `1`. -/
theorem matEntropy_le_log2_of_posSemidef_trace_one {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hpos : M.PosSemidef) (htr : M.trace = 1) (hd : 0 < d) : matEntropy M ≤ log2 d := by
  let ρ : DensityMatrix d := ⟨M, hpos, htr⟩
  rw [show M = ρ.mat from rfl, matEntropy_eq_vonNeumannEntropy]
  exact vonNeumannEntropy_le_log2 ρ hd

/-- Unitary conjugation invariance of `matEntropy`: `S(U M Uᴴ) = S(M)` whenever `Uᴴ U = I`. -/
theorem matEntropy_unitary_conj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    matEntropy (U * M * Uᴴ) = matEntropy M := by
  have hiff : (U * M * Uᴴ).IsHermitian ↔ M.IsHermitian := by
    constructor
    · intro h
      have h1 : Uᴴ * (U * M * Uᴴ)ᴴ * U = Uᴴ * (U * M * Uᴴ) * U := by rw [h.eq]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h1
      have hL : Uᴴ * (U * (Mᴴ * Uᴴ)) * U = Mᴴ := by
        calc Uᴴ * (U * (Mᴴ * Uᴴ)) * U = (Uᴴ * U) * Mᴴ * (Uᴴ * U) := by simp [Matrix.mul_assoc]
          _ = Mᴴ := by rw [hU, Matrix.one_mul, Matrix.mul_one]
      have hR : Uᴴ * (U * M * Uᴴ) * U = M := by
        calc Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) := by simp [Matrix.mul_assoc]
          _ = M := by rw [hU, Matrix.one_mul, Matrix.mul_one]
      rw [hL, hR] at h1
      exact h1
    · intro h
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, h.eq, Matrix.mul_assoc]
  by_cases hM : M.IsHermitian
  · have hUMU : (U * M * Uᴴ).IsHermitian := hiff.mpr hM
    refine matEntropy_eq_of_charpoly_eq hUMU hM ?_
    calc (U * M * Uᴴ).charpoly = (Uᴴ * (U * M)).charpoly := Matrix.charpoly_mul_comm _ _
      _ = ((Uᴴ * U) * M).charpoly := by rw [Matrix.mul_assoc]
      _ = M.charpoly := by rw [hU, Matrix.one_mul]
  · have hUMU : ¬ (U * M * Uᴴ).IsHermitian := fun h => hM (hiff.mp h)
    simp [matEntropy, hM, hUMU]

/-- Reindexing a square matrix by a permutation `e : Fin d ≃ Fin d` preserves `matEntropy`. -/
theorem matEntropy_submatrix_equiv {d : ℕ} (e : Fin d ≃ Fin d)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    matEntropy (M.submatrix e e) = matEntropy M := by
  rw [submatrix_eq_perm_conj e M]
  exact matEntropy_unitary_conj (permMatrix e) (permMatrix_conjTranspose_mul e) M

/-- Matrix transposition preserves `matEntropy`: `S(Mᵀ) = S(M)`. -/
theorem matEntropy_transpose {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    matEntropy M.transpose = matEntropy M := by
  have hiff : M.transpose.IsHermitian ↔ M.IsHermitian := by
    constructor
    · intro h
      ext i j
      have hij := congrFun (congrFun h.eq j) i
      simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using hij
    · intro h
      ext i j
      have hij := congrFun (congrFun h.eq j) i
      simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using hij
  by_cases hM : M.IsHermitian
  · exact matEntropy_eq_of_charpoly_eq (hiff.mpr hM) hM (Matrix.charpoly_transpose M)
  · have hMt : ¬ M.transpose.IsHermitian := fun h => hM (hiff.mp h)
    simp [matEntropy, hM, hMt]

/-- `matEntropy` of a real-valued diagonal matrix equals `∑ i, negPLogP (v i)`. -/
theorem matEntropy_diag_real {d : ℕ} (v : Fin d → ℝ) :
    matEntropy (Matrix.diagonal (fun i => (v i : ℂ))) = ∑ i : Fin d, negPLogP (v i) := by
  let D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => (v i : ℂ))
  have hD : D.IsHermitian := by
    ext i j
    by_cases h : i = j
    · subst h; simp [D]
    · simp [D, h, Ne.symm h]
  change matEntropy D = ∑ i : Fin d, negPLogP (v i)
  simp only [matEntropy, hD, ↓reduceDIte]
  have h1 : D.charpoly = ∏ i : Fin d, (Polynomial.X - Polynomial.C (hD.eigenvalues i : ℂ)) :=
    hD.charpoly_eq
  have h2 : D.charpoly = ∏ i : Fin d, (Polynomial.X - Polynomial.C (v i : ℂ)) :=
    Matrix.charpoly_diagonal (fun i => (v i : ℂ))
  have hprod :
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (hD.eigenvalues i : ℂ)) =
        ∏ i : Fin d, (Polynomial.X - Polynomial.C (v i : ℂ)) :=
    h1.symm.trans h2
  have hroots := congrArg Polynomial.roots hprod
  rw [multiset_map_roots_prod_X_sub_C, multiset_map_roots_prod_X_sub_C] at hroots
  have hre : Finset.univ.val.map hD.eigenvalues = Finset.univ.val.map v := by
    have := congrArg (Multiset.map Complex.re) hroots
    simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at this
    exact this
  change (Finset.univ.val.map (negPLogP ∘ hD.eigenvalues)).sum =
    (Finset.univ.val.map (negPLogP ∘ v)).sum
  rw [← Multiset.map_map, ← Multiset.map_map, hre]

/-- For a diagonal density matrix with entries `P.pmf i`, `matEntropy` equals `shannonEntropy P`. -/
theorem matEntropy_diag {d : ℕ} (P : ProbDist (Fin d)) :
    matEntropy (Matrix.diagonal (fun i => (P.pmf i : ℂ))) = shannonEntropy P :=
  matEntropy_diag_real P.pmf

/-- Rank-1 pure state `|ψ⟩⟨ψ|` associated to a unit vector `ψ : Fin d → ℂ`. -/
def pureState {d : ℕ} (ψ : Fin d → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) : DensityMatrix d where
  mat := Matrix.of fun i j => ψ i * star (ψ j)
  posSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, mul_comm]
    · intro x
      have hquad : star x ⬝ᵥ (Matrix.of fun i j => ψ i * star (ψ j)).mulVec x =
          star (∑ j, star (ψ j) * x j) * (∑ j, star (ψ j) * x j) := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_sum, star_mul', star_star]
        calc ∑ i, star (x i) * ∑ j, ψ i * star (ψ j) * x j
            = ∑ i, (ψ i * star (x i)) * ∑ j, star (ψ j) * x j := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
          _ = (∑ i, ψ i * star (x i)) * ∑ j, star (ψ j) * x j := by rw [← Finset.sum_mul]
      rw [hquad]
      exact star_mul_self_nonneg _
  trace_one := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
    have : ∑ i : Fin d, ψ i * star (ψ i) = ∑ i : Fin d, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun i _ => (ofReal_sq_norm (ψ i)).symm
    rw [this, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]

/-- Every pure state `|ψ⟩⟨ψ|` is an orthogonal projection: `ρ² = ρ`. -/
theorem pureState_mul_self {d : ℕ} (ψ : Fin d → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    (pureState ψ hψ).mat * (pureState ψ hψ).mat = (pureState ψ hψ).mat := by
  ext i j
  simp only [pureState, Matrix.mul_apply, Matrix.of_apply]
  have hsum : ∑ k : Fin d, star (ψ k) * ψ k = 1 := by
    have : ∑ k : Fin d, star (ψ k) * ψ k = ∑ k : Fin d, ((‖ψ k‖ ^ 2 : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun k _ => (ofReal_sq_norm' (ψ k)).symm
    rw [this, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  calc ∑ k, ψ i * star (ψ k) * (ψ k * star (ψ j))
      = (ψ i * star (ψ j)) * ∑ k, star (ψ k) * ψ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ψ i * star (ψ j) := by rw [hsum, mul_one]

/-- Every pure state has zero von Neumann entropy: `S(|ψ⟩⟨ψ|) = 0`. -/
theorem vonNeumannEntropy_pure {d : ℕ} (ψ : Fin d → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    vonNeumannEntropy (pureState ψ hψ) = 0 := by
  unfold vonNeumannEntropy
  refine Finset.sum_eq_zero fun i _ => ?_
  set ρ := pureState ψ hψ
  set h := ρ.posSemidef.isHermitian
  set v := (h.eigenvectorBasis i).ofLp
  have hv : ρ.mat.mulVec v = (h.eigenvalues i : ℂ) • v := by
    simpa [RCLike.real_smul_eq_coe_smul] using h.mulVec_eigenvectorBasis i
  have hv2 : (ρ.mat * ρ.mat).mulVec v = ((h.eigenvalues i : ℂ) * (h.eigenvalues i : ℂ)) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul]
  rw [pureState_mul_self, hv] at hv2
  have hv_ne : v ≠ 0 := by
    have hnorm : ‖h.eigenvectorBasis i‖ = 1 := h.eigenvectorBasis.orthonormal.1 i
    intro h0
    have h0' : h.eigenvectorBasis i = 0 := WithLp.ofLp_injective _ h0
    rw [h0', norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hsub : ((h.eigenvalues i : ℂ) - (h.eigenvalues i : ℂ) * (h.eigenvalues i : ℂ)) • v = 0 := by
    rw [sub_smul, hv2, sub_self]
  have hcoeff : (h.eigenvalues i : ℂ) - (h.eigenvalues i : ℂ) * (h.eigenvalues i : ℂ) = 0 :=
    (smul_eq_zero.mp hsub).resolve_right hv_ne
  have hreal : h.eigenvalues i - h.eigenvalues i * h.eigenvalues i = 0 := by
    exact_mod_cast hcoeff
  have hor : h.eigenvalues i = 0 ∨ h.eigenvalues i = 1 := by
    have hfac : h.eigenvalues i * (1 - h.eigenvalues i) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rcases hor with h0 | h1
  · rw [h0, negPLogP_zero]
  · rw [h1, negPLogP_one]

/-- Maximally mixed state `I_d / d` in dimension `d > 0`. -/
noncomputable def maxMixedState (d : ℕ) (hd : 0 < d) : DensityMatrix d where
  mat := ((1 / (d : ℝ) : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
  posSemidef := posSemidef_smul_real Matrix.PosSemidef.one (by positivity)
  trace_one := by
    have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
    simp [Matrix.trace_smul, hd_ne]

/-- The maximally mixed state in dimension `d > 0` has entropy `log₂ d`. -/
theorem vonNeumannEntropy_maxMixed (d : ℕ) (hd : 0 < d) :
    vonNeumannEntropy (maxMixedState d hd) = log2 d := by
  rw [← matEntropy_eq_vonNeumannEntropy]
  have hdiag : (maxMixedState d hd).mat =
      Matrix.diagonal (fun _ : Fin d => ((1 / (d : ℝ) : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [maxMixedState, h]
  rw [hdiag, matEntropy_diag_real]
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hpos : ¬ ((1 : ℝ) / (d : ℝ) ≤ 0) := not_le.mpr (div_pos one_pos hd_pos)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    negPLogP, hpos, ↓reduceIte, log2]
  rw [Real.log_div one_ne_zero hd_ne, Real.log_one, zero_sub]
  field_simp [hd_ne]

/-- SVD / purification spectral symmetry: for any rectangular matrix `M : Matrix (Fin m) (Fin k) ℂ`,
    `matEntropy (M * Mᴴ) = matEntropy (Mᴴ * M)`. -/
theorem matEntropy_mul_conjTranspose_eq_conjTranspose_mul {m k : ℕ}
    (M : Matrix (Fin m) (Fin k) ℂ) :
    matEntropy (M * Mᴴ) = matEntropy (Mᴴ * M) := by
  suffices hle : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ), a ≤ b →
      matEntropy (A * Aᴴ) = matEntropy (Aᴴ * A) by
    rcases le_total m k with hmk | hkm
    · exact hle M hmk
    · have h := hle Mᴴ hkm
      simpa [Matrix.conjTranspose_conjTranspose] using h.symm
  intro a b A hab
  let r := b - a
  have hadd : a + r = b := Nat.add_sub_of_le hab
  let e : Fin a ⊕ Fin r ≃ Fin b := finSumFinEquiv.trans (finCongr hadd)
  let N : Matrix (Fin a ⊕ Fin r) (Fin a ⊕ Fin r) ℂ :=
    Matrix.of fun x y => match x with | Sum.inl i => A i (e y) | Sum.inr _ => 0
  have hNN : N * Nᴴ = Matrix.fromBlocks (A * Aᴴ) 0 0 0 := by
    ext x y
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
          Matrix.fromBlocks_apply₁₁, N]
        rw [e.sum_comp (fun k => A i k * star (A j k))]
      | inr j =>
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, N]
    | inr i =>
      cases y with
      | inl j => simp [Matrix.mul_apply, Matrix.conjTranspose_apply, N]
      | inr j => simp [Matrix.mul_apply, Matrix.conjTranspose_apply, N]
  have hNN' : Nᴴ * N = (Aᴴ * A).submatrix e e := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
      Fintype.sum_sum_type, N, Matrix.of_apply, star_zero, zero_mul, Finset.sum_const_zero,
      add_zero]
  have hcp_eq : (Matrix.fromBlocks (A * Aᴴ) (0 : Matrix (Fin a) (Fin r) ℂ)
      (0 : Matrix (Fin r) (Fin a) ℂ) (0 : Matrix (Fin r) (Fin r) ℂ)).charpoly =
      (Aᴴ * A).charpoly := by
    calc (Matrix.fromBlocks (A * Aᴴ) 0 0 0).charpoly
        = (N * Nᴴ).charpoly := by rw [hNN]
      _ = (Nᴴ * N).charpoly := Matrix.charpoly_mul_comm N Nᴴ
      _ = ((Aᴴ * A).submatrix e e).charpoly := by rw [hNN']
      _ = (Aᴴ * A).charpoly := Matrix.charpoly_reindex e.symm (Aᴴ * A)
  rw [Matrix.charpoly_fromBlocks_zero₁₂] at hcp_eq
  have h0cp : (0 : Matrix (Fin r) (Fin r) ℂ).charpoly =
      ∏ _ : Fin r, (Polynomial.X - Polynomial.C (((0 : ℝ) : ℂ))) := by
    have h0d : (0 : Matrix (Fin r) (Fin r) ℂ) = Matrix.diagonal (fun _ => (((0 : ℝ) : ℂ))) := by
      ext i j; simp
    rw [h0d, Matrix.charpoly_diagonal]
  have hA1 : (A * Aᴴ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hA2 : (Aᴴ * A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hc1 : (A * Aᴴ).charpoly =
      ∏ i : Fin a, (Polynomial.X - Polynomial.C (hA1.eigenvalues i : ℂ)) := hA1.charpoly_eq
  have hc2 : (Aᴴ * A).charpoly =
      ∏ i : Fin b, (Polynomial.X - Polynomial.C (hA2.eigenvalues i : ℂ)) := hA2.charpoly_eq
  rw [hc1, hc2, h0cp] at hcp_eq
  have hne1 : ∏ i : Fin a, (Polynomial.X - Polynomial.C (hA1.eigenvalues i : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro i _; exact Polynomial.X_sub_C_ne_zero _
  have hne0 : ∏ _ : Fin r, (Polynomial.X - Polynomial.C (((0 : ℝ) : ℂ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro i _; exact Polynomial.X_sub_C_ne_zero _
  have hroots := congrArg Polynomial.roots hcp_eq
  rw [Polynomial.roots_mul (mul_ne_zero hne1 hne0),
    multiset_map_roots_prod_X_sub_C hA1.eigenvalues,
    multiset_map_roots_prod_X_sub_C (fun _ : Fin r => (0 : ℝ)),
    multiset_map_roots_prod_X_sub_C hA2.eigenvalues] at hroots
  have hre : Finset.univ.val.map hA1.eigenvalues + Finset.univ.val.map (fun _ : Fin r => (0 : ℝ)) =
      Finset.univ.val.map hA2.eigenvalues := by
    have := congrArg (Multiset.map Complex.re) hroots
    simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, Complex.ofReal_re] at this
    exact this
  simp only [matEntropy, hA1, hA2, ↓reduceDIte]
  have hsum := congrArg (fun s : Multiset ℝ => (s.map negPLogP).sum) hre
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def] at hsum
  have hzero : (Finset.univ.val.map (fun _ : Fin r => negPLogP 0)).sum = 0 := by
    change ∑ _ : Fin r, negPLogP 0 = 0
    simp [negPLogP_zero]
  rw [hzero, add_zero] at hsum
  exact hsum

/-- Peierls' inequality: for any positive semidefinite matrix `M` and unitary `U` (`Uᴴ U = I`),
    `matEntropy M ≤ ∑ i, negPLogP ((Uᴴ * M * U) i i).re`. -/
private lemma peierls_inequality {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) :
    matEntropy M ≤ ∑ i : Fin d, negPLogP ((Uᴴ * M * U) i i).re := by
  let V : Matrix (Fin d) (Fin d) ℂ := hM.isHermitian.eigenvectorUnitary
  let W : Matrix (Fin d) (Fin d) ℂ := Uᴴ * V
  have hUU : U * Uᴴ = 1 := unitary_mul_conjTranspose hU
  have hVV : V * Vᴴ = 1 := spectral_unitary_mul_right hM.isHermitian
  have hVV' : Vᴴ * V = 1 := spectral_unitary_mul_left hM.isHermitian
  have hWW : W * Wᴴ = 1 := by
    calc W * Wᴴ = (Uᴴ * V) * (Vᴴ * U) := by simp [W, Matrix.conjTranspose_mul]
      _ = Uᴴ * (V * Vᴴ) * U := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hVV, Matrix.mul_one, hU]
  have hWW' : Wᴴ * W = 1 := by
    calc Wᴴ * W = (Vᴴ * U) * (Uᴴ * V) := by simp [W, Matrix.conjTranspose_mul]
      _ = Vᴴ * (U * Uᴴ) * V := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hVV']
  have hdiag : ∀ i : Fin d,
      ((Uᴴ * M * U) i i).re = ∑ j : Fin d, ‖W i j‖ ^ 2 * hM.isHermitian.eigenvalues j := by
    intro i
    have hspec : Uᴴ * M * U =
        W * Matrix.diagonal (fun j => (hM.isHermitian.eigenvalues j : ℂ)) * Wᴴ := by
      have h1 := spectral_decomp hM.isHermitian
      calc Uᴴ * M * U
          = Uᴴ * (V * Matrix.diagonal (fun j => (hM.isHermitian.eigenvalues j : ℂ)) * Vᴴ) * U := by
            rw [← h1]
        _ = (Uᴴ * V) * Matrix.diagonal (fun j => (hM.isHermitian.eigenvalues j : ℂ)) * (Vᴴ * U) := by
            simp [Matrix.mul_assoc]
        _ = W * Matrix.diagonal (fun j => (hM.isHermitian.eigenvalues j : ℂ)) * Wᴴ := by
            simp [W, Matrix.conjTranspose_mul]
    rw [hspec]
    have hentry : (W * Matrix.diagonal (fun j => (hM.isHermitian.eigenvalues j : ℂ)) * Wᴴ) i i =
        ∑ j : Fin d, ((‖W i j‖ ^ 2 * hM.isHermitian.eigenvalues j : ℝ) : ℂ) := by
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.ofReal_mul, ofReal_sq_norm (W i j)]
      ring
    rw [hentry, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Complex.ofReal_re _
  have hrow : ∀ i : Fin d, ∑ j : Fin d, ‖W i j‖ ^ 2 = 1 := by
    intro i
    have h1 := congrFun (congrFun hWW i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have h2 : ∑ j : Fin d, ((‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      convert h1 using 1
      exact Finset.sum_congr rfl fun j _ => ofReal_sq_norm (W i j)
    have hre := congrArg Complex.re h2
    rw [Complex.re_sum, Complex.one_re] at hre
    simpa only [Complex.ofReal_re] using hre
  have hcol : ∀ j : Fin d, ∑ i : Fin d, ‖W i j‖ ^ 2 = 1 := by
    intro j
    have h1 := congrFun (congrFun hWW' j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have h2 : ∑ i : Fin d, ((‖W i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      convert h1 using 1
      exact Finset.sum_congr rfl fun i _ => ofReal_sq_norm' (W i j)
    have hre := congrArg Complex.re h2
    rw [Complex.re_sum, Complex.one_re] at hre
    simpa only [Complex.ofReal_re] using hre
  simp only [matEntropy, hM.isHermitian, ↓reduceDIte]
  calc ∑ j : Fin d, negPLogP (hM.isHermitian.eigenvalues j)
      = ∑ j : Fin d, (∑ i : Fin d, ‖W i j‖ ^ 2) * negPLogP (hM.isHermitian.eigenvalues j) := by
        refine Finset.sum_congr rfl fun j _ => by rw [hcol j, one_mul]
    _ = ∑ i : Fin d, ∑ j : Fin d, ‖W i j‖ ^ 2 * negPLogP (hM.isHermitian.eigenvalues j) := by
        simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin d, negPLogP (∑ j : Fin d, ‖W i j‖ ^ 2 * hM.isHermitian.eigenvalues j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [smul_eq_mul] using concaveOn_negPLogP.le_map_sum
          (fun j _ => sq_nonneg ‖W i j‖) (hrow i) (fun j _ => hM.eigenvalues_nonneg j)
    _ = ∑ i : Fin d, negPLogP ((Uᴴ * M * U) i i).re := by
        refine Finset.sum_congr rfl fun i _ => by rw [hdiag i]

/-- **Concavity of von Neumann entropy**: for any ensemble `(P, σ)` of positive semidefinite
    matrices, `∑ x, P(x) S(σ_x) ≤ S(∑ x, P(x) σ_x)`. -/
theorem vonNeumannEntropy_concave {m d : ℕ} (P : ProbDist (Fin m))
    (σ : Fin m → Matrix (Fin d) (Fin d) ℂ) (hσ : ∀ x, (σ x).PosSemidef) :
    ∑ x : Fin m, P.pmf x * matEntropy (σ x) ≤
      matEntropy (∑ x : Fin m, (P.pmf x : ℂ) • σ x) := by
  let M : Matrix (Fin d) (Fin d) ℂ := ∑ x : Fin m, (P.pmf x : ℂ) • σ x
  have hM_pos : M.PosSemidef :=
    posSemidef_sum Finset.univ _ (fun x _ => posSemidef_smul_real (hσ x) (P.nonneg x))
  have hM : M.IsHermitian := hM_pos.isHermitian
  let U : Matrix (Fin d) (Fin d) ℂ := hM.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := spectral_unitary_mul_left hM
  have hU_diag : ∀ i : Fin d, ((Uᴴ * M * U) i i).re = hM.eigenvalues i := by
    intro i
    have hspec := spectral_decomp hM
    have hconj : Uᴴ * M * U = Matrix.diagonal (fun j => (hM.eigenvalues j : ℂ)) := by
      calc Uᴴ * M * U
          = Uᴴ * (U * Matrix.diagonal (fun j => (hM.eigenvalues j : ℂ)) * Uᴴ) * U := by
            rw [← hspec]
        _ = (Uᴴ * U) * Matrix.diagonal (fun j => (hM.eigenvalues j : ℂ)) * (Uᴴ * U) := by
            simp [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun j => (hM.eigenvalues j : ℂ)) := by
            rw [hU, Matrix.one_mul, Matrix.mul_one]
    rw [hconj]
    simp
  have hlin : ∀ i : Fin d,
      ((Uᴴ * M * U) i i).re = ∑ x : Fin m, P.pmf x * ((Uᴴ * σ x * U) i i).re := by
    intro i
    have hmul : Uᴴ * M * U = ∑ x : Fin m, (P.pmf x : ℂ) • (Uᴴ * σ x * U) := by
      simp only [M, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hmul]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hnonneg : ∀ (x : Fin m) (i : Fin d), 0 ≤ ((Uᴴ * σ x * U) i i).re := by
    intro x i
    have hpos_conj : (Uᴴ * σ x * U).PosSemidef := (hσ x).conjTranspose_mul_mul_same U
    have hre := hpos_conj.re_dotProduct_nonneg (Pi.single i 1)
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hre
  calc ∑ x : Fin m, P.pmf x * matEntropy (σ x)
      ≤ ∑ x : Fin m, P.pmf x * ∑ i : Fin d, negPLogP ((Uᴴ * σ x * U) i i).re := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact mul_le_mul_of_nonneg_left (peierls_inequality (hσ x) U hU) (P.nonneg x)
    _ = ∑ i : Fin d, ∑ x : Fin m, P.pmf x * negPLogP ((Uᴴ * σ x * U) i i).re := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin d, negPLogP (∑ x : Fin m, P.pmf x * ((Uᴴ * σ x * U) i i).re) := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [smul_eq_mul] using concaveOn_negPLogP.le_map_sum
          (fun x _ => P.nonneg x) P.sum_one (fun x _ => hnonneg x i)
    _ = matEntropy M := by
        simp only [matEntropy, hM, ↓reduceDIte]
        refine Finset.sum_congr rfl fun i _ => by rw [← hlin i, hU_diag i]

end VonNeumannEntropy

/-! ### Section 2: Kronecker Product, Partial Trace, Partial Transpose, PPT Criterion, & Bell State -/

section BipartiteQuantum

/-- Conjugate transpose distributes over Kronecker product: `(A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ`. -/
theorem kronMat_conjTranspose {m₁ n₁ m₂ n₂ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℂ) (B : Matrix (Fin m₂) (Fin n₂) ℂ) :
    (kronMat A B)ᴴ = kronMat Aᴴ Bᴴ := by
  ext i j
  simp [kronMat, Matrix.conjTranspose_apply]

/-- Kronecker product of Hermitian matrices is Hermitian. -/
theorem kronMat_isHermitian {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (kronMat A B).IsHermitian := by
  rw [Matrix.IsHermitian, kronMat_conjTranspose, hA.eq, hB.eq]

/-- Mixed-product property of Kronecker product: `(A₁ ⊗ B₁)(A₂ ⊗ B₂) = (A₁ A₂) ⊗ (B₁ B₂)`. -/
theorem kronMat_mul {m₁ n₁ p₁ m₂ n₂ p₂ : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n₁) ℂ) (B₁ : Matrix (Fin m₂) (Fin n₂) ℂ)
    (A₂ : Matrix (Fin n₁) (Fin p₁) ℂ) (B₂ : Matrix (Fin n₂) (Fin p₂) ℂ) :
    kronMat A₁ B₁ * kronMat A₂ B₂ = kronMat (A₁ * A₂) (B₁ * B₂) := by
  ext i j
  simp only [Matrix.mul_apply, kronMat, Matrix.of_apply]
  rw [sum_fin_mul]
  have hstep : ∀ (a : Fin n₁) (b : Fin n₂),
      (⟨(a.1 * n₂ + b.1) / n₂,
          Nat.div_lt_of_lt_mul (by have := finMulIdx a b; nlinarith)⟩ : Fin n₁) = a ∧
      (⟨(a.1 * n₂ + b.1) % n₂,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ b.2))⟩ :
          Fin n₂) = b := by
    intro a b
    constructor <;> ext
    · exact mul_right_add_div b.2
    · exact mul_right_add_mod b.2
  calc ∑ a : Fin n₁, ∑ b : Fin n₂,
        A₁ _ ⟨(a.1 * n₂ + b.1) / n₂, _⟩ * B₁ _ ⟨(a.1 * n₂ + b.1) % n₂, _⟩ *
          (A₂ ⟨(a.1 * n₂ + b.1) / n₂, _⟩ _ * B₂ ⟨(a.1 * n₂ + b.1) % n₂, _⟩ _)
      = ∑ a : Fin n₁, ∑ b : Fin n₂,
        (A₁ _ a * A₂ a _) * (B₁ _ b * B₂ b _) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        obtain ⟨ha, hb⟩ := hstep a b
        rw [ha, hb]; ring
    _ = (∑ a : Fin n₁, A₁ _ a * A₂ a _) * (∑ b : Fin n₂, B₁ _ b * B₂ b _) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- Kronecker product of identity matrices is the identity matrix: `I_m ⊗ I_n = I_{m·n}`. -/
theorem kronMat_one (m n : ℕ) :
    kronMat (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  simp only [kronMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hne : ¬ (i.1 / n = j.1 / n ∧ i.1 % n = j.1 % n) := by
      rintro ⟨hd, hm⟩
      apply hij; ext
      rw [← Nat.div_add_mod i.1 n, ← Nat.div_add_mod j.1 n, hd, hm]
    simp only [Fin.mk.injEq, mul_ite, mul_one, mul_zero]
    split_ifs with h1 h2
    · exact absurd ⟨h2, h1⟩ hne
    · rfl
    · rfl

/-- Kronecker product of positive semidefinite matrices is positive semidefinite. -/
theorem kronMat_posSemidef {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (kronMat A B).PosSemidef := by
  obtain ⟨SA, hSA⟩ := posSemidef_exists_mul_conjTranspose hA
  obtain ⟨SB, hSB⟩ := posSemidef_exists_mul_conjTranspose hB
  rw [hSA, hSB, ← kronMat_mul, ← kronMat_conjTranspose]
  have h1 : kronMat SA SB * (kronMat SA SB)ᴴ = kronMat SA SB * 1 * (kronMat SA SB)ᴴ := by
    rw [Matrix.mul_one]
  rw [h1]
  exact Matrix.PosSemidef.one.mul_mul_conjTranspose_same (kronMat SA SB)

/-- Trace is multiplicative under Kronecker product: `Tr(A ⊗ B) = Tr(A) · Tr(B)`. -/
theorem kronMat_trace {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (kronMat A B).trace = A.trace * B.trace := by
  simp only [Matrix.trace, Matrix.diag, kronMat, Matrix.of_apply]
  rw [sum_fin_mul]
  calc ∑ a : Fin m, ∑ b : Fin n,
        A ⟨(a.1 * n + b.1) / n, _⟩ ⟨(a.1 * n + b.1) / n, _⟩ *
          B ⟨(a.1 * n + b.1) % n, _⟩ ⟨(a.1 * n + b.1) % n, _⟩
      = ∑ a : Fin m, ∑ b : Fin n, A a a * B b b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ b.2)
        have ha : (⟨(a.1 * n + b.1) / n,
            Nat.div_lt_of_lt_mul (by have := finMulIdx a b; nlinarith)⟩ : Fin m) = a :=
          Fin.ext (mul_right_add_div b.2)
        have hb : (⟨(a.1 * n + b.1) % n, Nat.mod_lt _ hn⟩ : Fin n) = b :=
          Fin.ext (mul_right_add_mod b.2)
        rw [ha, hb]
    _ = (∑ a : Fin m, A a a) * (∑ b : Fin n, B b b) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

/-- Tensor product of two density matrices `ρ ⊗ σ`. -/
def kronDensity {dA dB : ℕ} (ρ : DensityMatrix dA) (σ : DensityMatrix dB) :
    DensityMatrix (dA * dB) where
  mat := kronMat ρ.mat σ.mat
  posSemidef := kronMat_posSemidef ρ.posSemidef σ.posSemidef
  trace_one := by rw [kronMat_trace, ρ.trace_one, σ.trace_one, mul_one]

/-- Additivity of von Neumann entropy on tensor products of density matrices:
    `S(A ⊗ B) = S(A) + S(B)`. -/
theorem matEntropy_kronMat {dA dB : ℕ} {A : Matrix (Fin dA) (Fin dA) ℂ}
    {B : Matrix (Fin dB) (Fin dB) ℂ}
    (hA : A.PosSemidef) (hAtr : A.trace = 1) (hB : B.PosSemidef) (hBtr : B.trace = 1) :
    matEntropy (kronMat A B) = matEntropy A + matEntropy B := by
  let UA : Matrix (Fin dA) (Fin dA) ℂ := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix (Fin dB) (Fin dB) ℂ := hB.isHermitian.eigenvectorUnitary
  let DA : Matrix (Fin dA) (Fin dA) ℂ :=
    Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))
  let DB : Matrix (Fin dB) (Fin dB) ℂ :=
    Matrix.diagonal (fun j => (hB.isHermitian.eigenvalues j : ℂ))
  have hU_unit : (kronMat UA UB)ᴴ * kronMat UA UB = 1 := by
    rw [kronMat_conjTranspose, kronMat_mul, spectral_unitary_mul_left hA.isHermitian,
      spectral_unitary_mul_left hB.isHermitian, kronMat_one]
  have hdecomp : kronMat A B = kronMat UA UB * kronMat DA DB * (kronMat UA UB)ᴴ := by
    rw [kronMat_conjTranspose, kronMat_mul, kronMat_mul, ← spectral_decomp hA.isHermitian,
      ← spectral_decomp hB.isHermitian]
  have hdiag : kronMat DA DB =
      Matrix.diagonal (fun k : Fin (dA * dB) =>
        (((hA.isHermitian.eigenvalues ⟨k.1 / dB,
            Nat.div_lt_of_lt_mul (by have := k.2; nlinarith)⟩ *
          hB.isHermitian.eigenvalues ⟨k.1 % dB,
            Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ k.2))⟩) :
            ℝ) : ℂ)) := by
    ext i j
    simp only [kronMat, DA, DB, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [Complex.ofReal_mul]
    · have hne : ¬ (i.1 / dB = j.1 / dB ∧ i.1 % dB = j.1 % dB) := by
        rintro ⟨hd, hm⟩
        apply hij; ext
        rw [← Nat.div_add_mod i.1 dB, ← Nat.div_add_mod j.1 dB, hd, hm]
      simp only [hij, ↓reduceIte, Fin.mk.injEq, mul_ite, mul_zero, ite_mul, zero_mul]
      split_ifs with h1 h2
      · exact absurd ⟨h2, h1⟩ hne
      · rfl
      · rfl
  rw [hdecomp, matEntropy_unitary_conj _ hU_unit, hdiag, matEntropy_diag_real, sum_fin_mul]
  let ρA : DensityMatrix dA := ⟨A, hA, hAtr⟩
  let ρB : DensityMatrix dB := ⟨B, hB, hBtr⟩
  have hsumA : ∑ a : Fin dA, hA.isHermitian.eigenvalues a = 1 := (eigenvalues_probDist ρA).sum_one
  have hsumB : ∑ b : Fin dB, hB.isHermitian.eigenvalues b = 1 := (eigenvalues_probDist ρB).sum_one
  have hterm : ∀ (a : Fin dA) (b : Fin dB),
      negPLogP (hA.isHermitian.eigenvalues a * hB.isHermitian.eigenvalues b) =
        hB.isHermitian.eigenvalues b * negPLogP (hA.isHermitian.eigenvalues a) +
        hA.isHermitian.eigenvalues a * negPLogP (hB.isHermitian.eigenvalues b) := by
    intro a b
    have ha0 : 0 ≤ hA.isHermitian.eigenvalues a := hA.eigenvalues_nonneg a
    have hb0 : 0 ≤ hB.isHermitian.eigenvalues b := hB.eigenvalues_nonneg b
    by_cases ha : hA.isHermitian.eigenvalues a = 0
    · simp [ha, negPLogP_zero]
    · by_cases hb : hB.isHermitian.eigenvalues b = 0
      · simp [hb, negPLogP_zero]
      · have hap : 0 < hA.isHermitian.eigenvalues a := lt_of_le_of_ne ha0 (Ne.symm ha)
        have hbp : 0 < hB.isHermitian.eigenvalues b := lt_of_le_of_ne hb0 (Ne.symm hb)
        have habp : 0 < hA.isHermitian.eigenvalues a * hB.isHermitian.eigenvalues b :=
          mul_pos hap hbp
        simp only [negPLogP, not_le.mpr hap, not_le.mpr hbp, not_le.mpr habp, ↓reduceIte]
        rw [log2_mul_pos hap hbp]
        ring
  calc ∑ a : Fin dA, ∑ b : Fin dB,
        negPLogP (hA.isHermitian.eigenvalues ⟨(a.1 * dB + b.1) / dB, _⟩ *
          hB.isHermitian.eigenvalues ⟨(a.1 * dB + b.1) % dB, _⟩)
      = ∑ a : Fin dA, ∑ b : Fin dB,
        negPLogP (hA.isHermitian.eigenvalues a * hB.isHermitian.eigenvalues b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have hdB : 0 < dB := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ b.2)
        have ha : (⟨(a.1 * dB + b.1) / dB,
            Nat.div_lt_of_lt_mul (by have := finMulIdx a b; nlinarith)⟩ : Fin dA) = a :=
          Fin.ext (mul_right_add_div b.2)
        have hb : (⟨(a.1 * dB + b.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b :=
          Fin.ext (mul_right_add_mod b.2)
        rw [ha, hb]
    _ = ∑ a : Fin dA, ∑ b : Fin dB,
        (hB.isHermitian.eigenvalues b * negPLogP (hA.isHermitian.eigenvalues a) +
          hA.isHermitian.eigenvalues a * negPLogP (hB.isHermitian.eigenvalues b)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
    _ = (∑ b : Fin dB, hB.isHermitian.eigenvalues b) *
          (∑ a : Fin dA, negPLogP (hA.isHermitian.eigenvalues a)) +
        (∑ a : Fin dA, hA.isHermitian.eigenvalues a) *
          (∑ b : Fin dB, negPLogP (hB.isHermitian.eigenvalues b)) := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by rw [Finset.sum_mul]
        · rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = matEntropy A + matEntropy B := by
        rw [hsumA, hsumB, one_mul, one_mul]
        simp [matEntropy, hA.isHermitian, hB.isHermitian]

/-- Additivity of von Neumann entropy on product states `ρ ⊗ σ`. -/
theorem vonNeumannEntropy_kronDensity {dA dB : ℕ} (ρ : DensityMatrix dA) (σ : DensityMatrix dB) :
    vonNeumannEntropy (kronDensity ρ σ) = vonNeumannEntropy ρ + vonNeumannEntropy σ := by
  rw [← matEntropy_eq_vonNeumannEntropy, ← matEntropy_eq_vonNeumannEntropy,
    ← matEntropy_eq_vonNeumannEntropy]
  exact matEntropy_kronMat ρ.posSemidef ρ.trace_one σ.posSemidef σ.trace_one

/-- Partial trace over subsystem A preserves Hermiticity. -/
theorem partialTraceA_isHermitian {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.IsHermitian) : (partialTraceA M).IsHermitian := by
  ext b₁ b₂
  simp only [partialTraceA, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact congrFun (congrFun hM.eq ⟨a.1 * dB + b₁.1, finMulIdx a b₁⟩) ⟨a.1 * dB + b₂.1, finMulIdx a b₂⟩

/-- Partial trace over subsystem B preserves Hermiticity. -/
theorem partialTraceB_isHermitian {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.IsHermitian) : (partialTraceB M).IsHermitian := by
  ext a₁ a₂
  simp only [partialTraceB, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact congrFun (congrFun hM.eq ⟨a₁.1 * dB + b.1, finMulIdx a₁ b⟩) ⟨a₂.1 * dB + b.1, finMulIdx a₂ b⟩

/-- Partial trace over subsystem A preserves positive semidefiniteness. -/
theorem partialTraceA_posSemidef {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.PosSemidef) : (partialTraceA M).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨partialTraceA_isHermitian hM.isHermitian, fun x => ?_⟩
  let lift : Fin dA → (Fin (dA * dB) → ℂ) := fun a idx =>
    if idx.1 / dB = a.1 then
      x ⟨idx.1 % dB, Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ idx.2))⟩
    else 0
  have hsum : star x ⬝ᵥ (partialTraceA M).mulVec x =
      ∑ a : Fin dA, star (lift a) ⬝ᵥ M.mulVec (lift a) := by
    have hterm : ∀ a : Fin dA,
        star (lift a) ⬝ᵥ M.mulVec (lift a) =
          ∑ b₁ : Fin dB, ∑ b₂ : Fin dB,
            star (x b₁) * M ⟨a.1 * dB + b₁.1, finMulIdx a b₁⟩ ⟨a.1 * dB + b₂.1, finMulIdx a b₂⟩ * x b₂ := by
      intro a
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      rw [sum_fin_mul]
      rw [Finset.sum_eq_single a]
      · refine Finset.sum_congr rfl fun b₁ _ => ?_
        have hdB : 0 < dB := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ b₁.2)
        have hdiv1 : (a.1 * dB + b₁.1) / dB = a.1 := mul_right_add_div b₁.2
        have hmod1 : (⟨(a.1 * dB + b₁.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b₁ :=
          Fin.ext (mul_right_add_mod b₁.2)
        have hlift1 : lift a ⟨a.1 * dB + b₁.1, finMulIdx a b₁⟩ = x b₁ := by
          simp only [lift, hdiv1, ↓reduceIte, hmod1]
        rw [hlift1, sum_fin_mul, Finset.sum_eq_single a]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b₂ _ => ?_
          have hdiv2 : (a.1 * dB + b₂.1) / dB = a.1 := mul_right_add_div b₂.2
          have hmod2 : (⟨(a.1 * dB + b₂.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b₂ :=
            Fin.ext (mul_right_add_mod b₂.2)
          have hlift2 : lift a ⟨a.1 * dB + b₂.1, finMulIdx a b₂⟩ = x b₂ := by
            simp only [lift, hdiv2, ↓reduceIte, hmod2]
          rw [hlift2]; ring
        · intro a' _ ha'
          refine Finset.sum_eq_zero fun b₂ _ => ?_
          have hdiv2 : (a'.1 * dB + b₂.1) / dB = a'.1 := mul_right_add_div b₂.2
          have hne : a'.1 ≠ a.1 := fun h => ha' (Fin.ext h)
          simp [lift, hdiv2, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a' _ ha'
        refine Finset.sum_eq_zero fun b₁ _ => ?_
        have hdiv1 : (a'.1 * dB + b₁.1) / dB = a'.1 := mul_right_add_div b₁.2
        have hne : a'.1 ≠ a.1 := fun h => ha' (Fin.ext h)
        simp [lift, hdiv1, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm]
    symm
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, partialTraceA, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hsum]
  exact Finset.sum_nonneg fun a _ => hM.dotProduct_mulVec_nonneg (lift a)

/-- Partial trace over subsystem B preserves positive semidefiniteness. -/
theorem partialTraceB_posSemidef {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.PosSemidef) : (partialTraceB M).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨partialTraceB_isHermitian hM.isHermitian, fun x => ?_⟩
  let lift : Fin dB → (Fin (dA * dB) → ℂ) := fun b idx =>
    if idx.1 % dB = b.1 then
      x ⟨idx.1 / dB, Nat.div_lt_of_lt_mul (by have := idx.2; nlinarith)⟩
    else 0
  have hsum : star x ⬝ᵥ (partialTraceB M).mulVec x =
      ∑ b : Fin dB, star (lift b) ⬝ᵥ M.mulVec (lift b) := by
    have hterm : ∀ b : Fin dB,
        star (lift b) ⬝ᵥ M.mulVec (lift b) =
          ∑ a₁ : Fin dA, ∑ a₂ : Fin dA,
            star (x a₁) * M ⟨a₁.1 * dB + b.1, finMulIdx a₁ b⟩ ⟨a₂.1 * dB + b.1, finMulIdx a₂ b⟩ * x a₂ := by
      intro b
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      rw [sum_fin_mul]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_eq_single b]
      · have hmod1 : (a₁.1 * dB + b.1) % dB = b.1 := mul_right_add_mod b.2
        have hdiv1 : (⟨(a₁.1 * dB + b.1) / dB,
            Nat.div_lt_of_lt_mul (by have := finMulIdx a₁ b; nlinarith)⟩ : Fin dA) = a₁ :=
          Fin.ext (mul_right_add_div b.2)
        have hlift1 : lift b ⟨a₁.1 * dB + b.1, finMulIdx a₁ b⟩ = x a₁ := by
          simp [lift, hmod1, hdiv1]
        rw [hlift1, sum_fin_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a₂ _ => ?_
        rw [Finset.sum_eq_single b]
        · have hmod2 : (a₂.1 * dB + b.1) % dB = b.1 := mul_right_add_mod b.2
          have hdiv2 : (⟨(a₂.1 * dB + b.1) / dB,
              Nat.div_lt_of_lt_mul (by have := finMulIdx a₂ b; nlinarith)⟩ : Fin dA) = a₂ :=
            Fin.ext (mul_right_add_div b.2)
          have hlift2 : lift b ⟨a₂.1 * dB + b.1, finMulIdx a₂ b⟩ = x a₂ := by
            simp [lift, hmod2, hdiv2]
          rw [hlift2]; ring
        · intro b' _ hb'
          have hmod2 : (a₂.1 * dB + b'.1) % dB = b'.1 := mul_right_add_mod b'.2
          have hne : b'.1 ≠ b.1 := fun h => hb' (Fin.ext h)
          simp [lift, hmod2, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b' _ hb'
        have hmod1 : (a₁.1 * dB + b'.1) % dB = b'.1 := mul_right_add_mod b'.2
        have hne : b'.1 ≠ b.1 := fun h => hb' (Fin.ext h)
        simp [lift, hmod1, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm]
    symm
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, partialTraceB, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  exact Finset.sum_nonneg fun b _ => hM.dotProduct_mulVec_nonneg (lift b)

/-- Partial trace over subsystem A preserves trace: `Tr(Tr_A(M)) = Tr(M)`. -/
theorem partialTraceA_trace {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    (partialTraceA M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTraceA, Matrix.of_apply]
  rw [Finset.sum_comm, sum_fin_mul]

/-- Partial trace over subsystem B preserves trace: `Tr(Tr_B(M)) = Tr(M)`. -/
theorem partialTraceB_trace {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    (partialTraceB M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTraceB, Matrix.of_apply]
  rw [sum_fin_mul]

/-- Partial trace over A of a Kronecker product: `Tr_A(A ⊗ B) = Tr(A) • B`. -/
theorem partialTraceA_kronMat {dA dB : ℕ}
    (A : Matrix (Fin dA) (Fin dA) ℂ) (B : Matrix (Fin dB) (Fin dB) ℂ) :
    partialTraceA (kronMat A B) = A.trace • B := by
  ext b₁ b₂
  have hdB : 0 < dB := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ b₁.2)
  simp only [partialTraceA, kronMat, Matrix.of_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha1 : (⟨(a.1 * dB + b₁.1) / dB,
      Nat.div_lt_of_lt_mul (by have := finMulIdx a b₁; nlinarith)⟩ : Fin dA) = a :=
    Fin.ext (mul_right_add_div b₁.2)
  have ha2 : (⟨(a.1 * dB + b₂.1) / dB,
      Nat.div_lt_of_lt_mul (by have := finMulIdx a b₂; nlinarith)⟩ : Fin dA) = a :=
    Fin.ext (mul_right_add_div b₂.2)
  have hb1 : (⟨(a.1 * dB + b₁.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b₁ :=
    Fin.ext (mul_right_add_mod b₁.2)
  have hb2 : (⟨(a.1 * dB + b₂.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b₂ :=
    Fin.ext (mul_right_add_mod b₂.2)
  rw [ha1, ha2, hb1, hb2]

/-- Partial trace over B of a Kronecker product: `Tr_B(A ⊗ B) = Tr(B) • A`. -/
theorem partialTraceB_kronMat {dA dB : ℕ}
    (A : Matrix (Fin dA) (Fin dA) ℂ) (B : Matrix (Fin dB) (Fin dB) ℂ) :
    partialTraceB (kronMat A B) = B.trace • A := by
  ext a₁ a₂
  simp only [partialTraceB, kronMat, Matrix.of_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hdB : 0 < dB := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ b.2)
  have ha1 : (⟨(a₁.1 * dB + b.1) / dB,
      Nat.div_lt_of_lt_mul (by have := finMulIdx a₁ b; nlinarith)⟩ : Fin dA) = a₁ :=
    Fin.ext (mul_right_add_div b.2)
  have ha2 : (⟨(a₂.1 * dB + b.1) / dB,
      Nat.div_lt_of_lt_mul (by have := finMulIdx a₂ b; nlinarith)⟩ : Fin dA) = a₂ :=
    Fin.ext (mul_right_add_div b.2)
  have hb1 : (⟨(a₁.1 * dB + b.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b :=
    Fin.ext (mul_right_add_mod b.2)
  have hb2 : (⟨(a₂.1 * dB + b.1) % dB, Nat.mod_lt _ hdB⟩ : Fin dB) = b :=
    Fin.ext (mul_right_add_mod b.2)
  rw [ha1, ha2, hb1, hb2, mul_comm]

/-- Partial transpose on subsystem B preserves Hermiticity. -/
theorem partialTransposeB_isHermitian {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.IsHermitian) : (partialTransposeB M).IsHermitian := by
  ext i j
  simp only [partialTransposeB, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact congrFun (congrFun hM.eq _) _

/-- Partial transpose on subsystem B preserves trace: `Tr(M^{T_B}) = Tr(M)`. -/
theorem partialTransposeB_trace {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    (partialTransposeB M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTransposeB, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.1 / dB * dB + i.1 % dB = i.1 := by rw [mul_comm, Nat.div_add_mod]
  congr 1 <;> exact Fin.ext hi

/-- Partial transpose on a Kronecker product: `(A ⊗ B)^{T_B} = A ⊗ Bᵀ`. -/
theorem partialTransposeB_kronMat {dA dB : ℕ}
    (A : Matrix (Fin dA) (Fin dA) ℂ) (B : Matrix (Fin dB) (Fin dB) ℂ) :
    partialTransposeB (kronMat A B) = kronMat A B.transpose := by
  ext i j
  have hB : 0 < dB := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ i.2)
  have hiB : i.1 % dB < dB := Nat.mod_lt _ hB
  have hjB : j.1 % dB < dB := Nat.mod_lt _ hB
  simp only [partialTransposeB, kronMat, Matrix.of_apply, Matrix.transpose_apply]
  have h1 : (i.1 / dB * dB + j.1 % dB) / dB = i.1 / dB := mul_right_add_div hjB
  have h2 : (j.1 / dB * dB + i.1 % dB) / dB = j.1 / dB := mul_right_add_div hiB
  have h3 : (i.1 / dB * dB + j.1 % dB) % dB = j.1 % dB := mul_right_add_mod hjB
  have h4 : (j.1 / dB * dB + i.1 % dB) % dB = i.1 % dB := mul_right_add_mod hiB
  congr 1
  · congr 1 <;> ext <;> assumption
  · congr 1 <;> ext <;> assumption

/-- Additivity of partial transpose: `(M + N)^{T_B} = M^{T_B} + N^{T_B}`. -/
theorem partialTransposeB_add {dA dB : ℕ}
    (M N : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    partialTransposeB (M + N) = partialTransposeB M + partialTransposeB N := by
  ext i j; simp [partialTransposeB]

/-- Scalar linearity of partial transpose: `(c • M)^{T_B} = c • M^{T_B}`. -/
theorem partialTransposeB_smul {dA dB : ℕ}
    (c : ℂ) (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    partialTransposeB (c • M) = c • partialTransposeB M := by
  ext i j; simp [partialTransposeB]

private lemma partialTransposeB_sum {ι : Type*} {dA dB : ℕ} (s : Finset ι)
    (f : ι → Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    partialTransposeB (∑ k ∈ s, f k) = ∑ k ∈ s, partialTransposeB (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; simp [partialTransposeB]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, partialTransposeB_add, ih]

/-- **Peres–Horodecki PPT Criterion** (Peres 1996, Horodecki 1996): every separable bipartite
    state has a positive semidefinite partial transpose (`IsSeparable ρ → IsPPT ρ`). -/
theorem isPPT_of_isSeparable {dA dB : ℕ} {ρ : DensityMatrix (dA * dB)} (h : IsSeparable ρ) :
    IsPPT ρ := by
  rcases h with ⟨m, P, σA, σB, hρ⟩
  unfold IsPPT
  rw [hρ, partialTransposeB_sum]
  refine posSemidef_sum Finset.univ _ fun k _ => ?_
  rw [partialTransposeB_smul, partialTransposeB_kronMat]
  exact posSemidef_smul_real
    (kronMat_posSemidef (σA k).posSemidef (σB k).posSemidef.transpose) (P.nonneg k)

/-- The two-qubit Bell state vector `|Φ⁺⟩ = (|00⟩ + |11⟩) / √2`. -/
noncomputable def bellVecPhiPlus : Fin (2 * 2) → ℂ :=
  ![((1 / Real.sqrt 2 : ℝ) : ℂ), 0, 0, ((1 / Real.sqrt 2 : ℝ) : ℂ)]

private lemma bellVecPhiPlus_norm_sq : ∑ i : Fin (2 * 2), ‖bellVecPhiPlus i‖ ^ 2 = 1 := by
  change ∑ i : Fin 4, ‖bellVecPhiPlus i‖ ^ 2 = 1
  rw [Fin.sum_univ_four]
  simp only [bellVecPhiPlus, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    norm_zero, zero_pow (by norm_num : 2 ≠ 0), Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [one_div, inv_pow, Real.sq_sqrt h2]
  norm_num

/-- The maximally entangled two-qubit Bell state `|Φ⁺⟩⟨Φ⁺|`. -/
noncomputable def bellStatePhiPlus : DensityMatrix (2 * 2) :=
  pureState bellVecPhiPlus bellVecPhiPlus_norm_sq

/-- The Bell state `|Φ⁺⟩⟨Φ⁺|` is pure, hence has zero von Neumann entropy. -/
theorem vonNeumannEntropy_bellStatePhiPlus : vonNeumannEntropy bellStatePhiPlus = 0 :=
  vonNeumannEntropy_pure bellVecPhiPlus bellVecPhiPlus_norm_sq

private lemma inv_sqrt2_mul_self :
    (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private lemma half_from_inv_sqrt2 :
    ((1 / Real.sqrt 2 : ℝ) : ℂ) * star ((1 / Real.sqrt 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  rw [one_div, ← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]

/-- The reduced state of `|Φ⁺⟩⟨Φ⁺|` on Bob's qubit is the maximally mixed qubit state `I₂ / 2`. -/
theorem partialTraceA_bellStatePhiPlus :
    partialTraceA bellStatePhiPlus.mat = (maxMixedState 2 (by norm_num)).mat := by
  ext b₁ b₂
  fin_cases b₁ <;> fin_cases b₂ <;>
    simp [partialTraceA, bellStatePhiPlus, pureState, bellVecPhiPlus, maxMixedState,
      Fin.sum_univ_two, inv_sqrt2_mul_self]

/-- The reduced state of `|Φ⁺⟩⟨Φ⁺|` has entanglement entropy `1` bit. -/
theorem matEntropy_partialTraceA_bellStatePhiPlus :
    matEntropy (partialTraceA bellStatePhiPlus.mat) = 1 := by
  rw [partialTraceA_bellStatePhiPlus, matEntropy_eq_vonNeumannEntropy,
    vonNeumannEntropy_maxMixed 2 (by norm_num)]
  simp [log2, Real.log_pos (by norm_num : (1 : ℝ) < 2) |>.ne']

/-- The Bell state `|Φ⁺⟩⟨Φ⁺|` fails the PPT criterion: `⟨Ψ⁻ | (|Φ⁺⟩⟨Φ⁺|)^{T_B} | Ψ⁻⟩ = -1 < 0`. -/
theorem bellStatePhiPlus_not_isPPT : ¬ IsPPT bellStatePhiPlus := by
  intro h
  let w : Fin (2 * 2) → ℂ := ![0, 1, -1, 0]
  have hnonneg : 0 ≤ (star w ⬝ᵥ (partialTransposeB bellStatePhiPlus.mat).mulVec w).re := by
    simpa [RCLike.re_to_complex] using h.re_dotProduct_nonneg w
  have hval : (star w ⬝ᵥ (partialTransposeB bellStatePhiPlus.mat).mulVec w).re = -1 := by
    have hcomplex : star w ⬝ᵥ (partialTransposeB bellStatePhiPlus.mat).mulVec w = -1 := by
      change ∑ i : Fin 4, star (w i) * ∑ j : Fin 4, partialTransposeB bellStatePhiPlus.mat i j * w j = -1
      simp only [Fin.sum_univ_four, w, partialTransposeB, bellStatePhiPlus, pureState, bellVecPhiPlus,
        Matrix.of_apply]
      simp [inv_sqrt2_mul_self]
      ring
    rw [hcomplex]; simp
  linarith

/-- The Bell state `|Φ⁺⟩⟨Φ⁺|` is entangled (`¬ IsSeparable bellStatePhiPlus`). -/
theorem bellStatePhiPlus_not_isSeparable : ¬ IsSeparable bellStatePhiPlus :=
  fun h => bellStatePhiPlus_not_isPPT (isPPT_of_isSeparable h)

/-- The Bell state `|Φ⁺⟩⟨Φ⁺|` is `1`-copy distillable, hence `IsDistillable`. -/
theorem bellStatePhiPlus_isDistillable : IsDistillable bellStatePhiPlus := by
  refine ⟨1, Nat.one_pos, ?_⟩
  refine ⟨fun a => if a = 0 then 1 else 0,
          fun a => if a = 1 then 1 else 0,
          fun b => if b = 1 then 1 else 0,
          fun b => if b = 0 then -1 else 0, ?_⟩
  dsimp only
  have hsum :
      (∑ i : Fin ((2 * 2) ^ 1), ∑ j : Fin ((2 * 2) ^ 1),
        star ((if extractAliceCopyIdx 2 2 1 i.1 = 0 then (1 : ℂ) else 0) *
              (if extractBobCopyIdx 2 2 1 i.1 = 1 then (1 : ℂ) else 0) +
              (if extractAliceCopyIdx 2 2 1 i.1 = 1 then (1 : ℂ) else 0) *
              (if extractBobCopyIdx 2 2 1 i.1 = 0 then (-1 : ℂ) else 0)) *
          kronPowerMat 1 (fun _ => partialTransposeB bellStatePhiPlus.mat) i j *
          ((if extractAliceCopyIdx 2 2 1 j.1 = 0 then (1 : ℂ) else 0) *
           (if extractBobCopyIdx 2 2 1 j.1 = 1 then (1 : ℂ) else 0) +
           (if extractAliceCopyIdx 2 2 1 j.1 = 1 then (1 : ℂ) else 0) *
           (if extractBobCopyIdx 2 2 1 j.1 = 0 then (-1 : ℂ) else 0))) = -1 := by
    change ∑ i : Fin 4, ∑ j : Fin 4, _ = -1
    simp only [Fin.sum_univ_four, extractAliceCopyIdx, extractBobCopyIdx, Fin.sum_univ_one,
      kronPowerMat, kronMat, partialTransposeB, bellStatePhiPlus, pureState, bellVecPhiPlus,
      Matrix.of_apply]
    simp [inv_sqrt2_mul_self]
    ring
  rw [hsum]
  norm_num

end BipartiteQuantum

/-! ### Section 3: Trace Distance Basics -/

section TraceDistance

/-- Non-negativity of trace distance: `0 ≤ D(ρ, σ)`. -/
theorem traceDistance_nonneg {d : ℕ} (ρ σ : DensityMatrix d) :
    0 ≤ traceDistance ρ σ := by
  unfold traceDistance
  have h : (ρ.mat - σ.mat).IsHermitian :=
    ρ.posSemidef.isHermitian.sub σ.posSemidef.isHermitian
  simp only [h, ↓reduceDIte]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => abs_nonneg _)

/-- Zero self-distance: `D(ρ, ρ) = 0`. -/
theorem traceDistance_self {d : ℕ} (ρ : DensityMatrix d) :
    traceDistance ρ ρ = 0 := by
  unfold traceDistance
  have h : (ρ.mat - ρ.mat).IsHermitian := by rw [sub_self]; exact Matrix.isHermitian_zero
  simp only [h, ↓reduceDIte]
  have heig : h.eigenvalues = 0 := h.eigenvalues_eq_zero_iff.mpr (sub_self ρ.mat)
  simp only [heig, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero]

/-- Symmetry of trace distance: `D(ρ, σ) = D(σ, ρ)`. -/
theorem traceDistance_symm {d : ℕ} (ρ σ : DensityMatrix d) :
    traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance
  have h1 : (ρ.mat - σ.mat).IsHermitian :=
    ρ.posSemidef.isHermitian.sub σ.posSemidef.isHermitian
  have h2 : (σ.mat - ρ.mat).IsHermitian :=
    σ.posSemidef.isHermitian.sub ρ.posSemidef.isHermitian
  simp only [h1, h2, ↓reduceDIte]
  apply congrArg ((1 / 2 : ℝ) * ·)
  let U : Matrix (Fin d) (Fin d) ℂ := h1.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := spectral_unitary_mul_left h1
  have hneg : σ.mat - ρ.mat =
      U * Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have hspec := spectral_decomp h1
    have hdiag_neg : -Matrix.diagonal (fun i => (h1.eigenvalues i : ℂ)) =
        Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [h]
    calc σ.mat - ρ.mat = -(ρ.mat - σ.mat) := by abel
      _ = -(U * Matrix.diagonal (fun i => (h1.eigenvalues i : ℂ)) * Uᴴ) := by rw [← hspec]
      _ = U * (-Matrix.diagonal (fun i => (h1.eigenvalues i : ℂ))) * Uᴴ := by
          rw [Matrix.mul_neg, Matrix.neg_mul]
      _ = U * Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by rw [hdiag_neg]
  have hcp : (σ.mat - ρ.mat).charpoly =
      ∏ i : Fin d, (Polynomial.X - Polynomial.C ((-h1.eigenvalues i : ℝ) : ℂ)) := by
    calc (σ.mat - ρ.mat).charpoly
        = (U * Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ)) * Uᴴ).charpoly := by
            rw [hneg]
      _ = (Uᴴ * (U * Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ)))).charpoly :=
            Matrix.charpoly_mul_comm _ _
      _ = ((Uᴴ * U) * Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ))).charpoly := by
            rw [Matrix.mul_assoc]
      _ = (Matrix.diagonal (fun i => ((-h1.eigenvalues i : ℝ) : ℂ))).charpoly := by
            rw [hU, Matrix.one_mul]
      _ = ∏ i : Fin d, (Polynomial.X - Polynomial.C ((-h1.eigenvalues i : ℝ) : ℂ)) :=
            Matrix.charpoly_diagonal _
  have hc2 : (σ.mat - ρ.mat).charpoly =
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (h2.eigenvalues i : ℂ)) := h2.charpoly_eq
  have hprod :
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (h2.eigenvalues i : ℂ)) =
        ∏ i : Fin d, (Polynomial.X - Polynomial.C ((-h1.eigenvalues i : ℝ) : ℂ)) :=
    hc2.symm.trans hcp
  have hroots := congrArg Polynomial.roots hprod
  rw [multiset_map_roots_prod_X_sub_C h2.eigenvalues,
    multiset_map_roots_prod_X_sub_C (fun i => -h1.eigenvalues i)] at hroots
  have hre : Finset.univ.val.map h2.eigenvalues = Finset.univ.val.map (fun i => -h1.eigenvalues i) := by
    have := congrArg (Multiset.map Complex.re) hroots
    simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at this
    exact this
  have hsum := congrArg (fun s : Multiset ℝ => (s.map abs).sum) hre
  simp only [Multiset.map_map, Function.comp_def, abs_neg] at hsum
  exact hsum.symm

/-- Trace distance between any two density matrices is at most `1`: `D(ρ, σ) ≤ 1`. -/
theorem traceDistance_le_one {d : ℕ} (ρ σ : DensityMatrix d) :
    traceDistance ρ σ ≤ 1 := by
  unfold traceDistance
  have h : (ρ.mat - σ.mat).IsHermitian :=
    ρ.posSemidef.isHermitian.sub σ.posSemidef.isHermitian
  simp only [h, ↓reduceDIte]
  let U : Matrix (Fin d) (Fin d) ℂ := h.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := spectral_unitary_mul_left h
  have htrace_conj : ∀ (τ : DensityMatrix d),
      ∑ i : Fin d, ((Uᴴ * τ.mat * U) i i).re = 1 := by
    intro τ
    have htr : (Uᴴ * τ.mat * U).trace = 1 := by
      calc (Uᴴ * τ.mat * U).trace = (U * Uᴴ * τ.mat).trace := by
            rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
        _ = τ.mat.trace := by rw [unitary_mul_conjTranspose hU, Matrix.one_mul]
        _ = 1 := τ.trace_one
    have hre := congrArg Complex.re htr
    simpa [Matrix.trace, Matrix.diag, Complex.re_sum] using hre
  have hdiag_nonneg : ∀ (τ : DensityMatrix d) (i : Fin d), 0 ≤ ((Uᴴ * τ.mat * U) i i).re := by
    intro τ i
    have hpos : (Uᴴ * τ.mat * U).PosSemidef := τ.posSemidef.conjTranspose_mul_mul_same U
    have hre := hpos.re_dotProduct_nonneg (Pi.single i 1)
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hre
  have heig_diff : ∀ i : Fin d,
      h.eigenvalues i = ((Uᴴ * ρ.mat * U) i i).re - ((Uᴴ * σ.mat * U) i i).re := by
    intro i
    have hconj : Uᴴ * (ρ.mat - σ.mat) * U =
        Matrix.diagonal (fun j => (h.eigenvalues j : ℂ)) := by
      have hspec := spectral_decomp h
      calc Uᴴ * (ρ.mat - σ.mat) * U
          = Uᴴ * (U * Matrix.diagonal (fun j => (h.eigenvalues j : ℂ)) * Uᴴ) * U := by
            rw [← hspec]
        _ = (Uᴴ * U) * Matrix.diagonal (fun j => (h.eigenvalues j : ℂ)) * (Uᴴ * U) := by
            simp [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun j => (h.eigenvalues j : ℂ)) := by
            rw [hU, Matrix.one_mul, Matrix.mul_one]
    have hsub : Uᴴ * (ρ.mat - σ.mat) * U = Uᴴ * ρ.mat * U - Uᴴ * σ.mat * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    have hij := congrArg Complex.re (congrFun (congrFun (hsub.symm.trans hconj) i) i)
    simpa [Matrix.sub_apply] using hij.symm
  have hsum_le : ∑ i : Fin d, |h.eigenvalues i| ≤ 2 := by
    calc ∑ i : Fin d, |h.eigenvalues i|
        ≤ ∑ i : Fin d, (((Uᴴ * ρ.mat * U) i i).re + ((Uᴴ * σ.mat * U) i i).re) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [heig_diff i]
          have ha := hdiag_nonneg ρ i
          have hb := hdiag_nonneg σ i
          rw [abs_le]
          constructor <;> linarith
      _ = (∑ i : Fin d, ((Uᴴ * ρ.mat * U) i i).re) +
          (∑ i : Fin d, ((Uᴴ * σ.mat * U) i i).re) := Finset.sum_add_distrib
      _ = 1 + 1 := by rw [htrace_conj ρ, htrace_conj σ]
      _ = 2 := by norm_num
  linarith

/-- Definiteness of trace distance: `D(ρ, σ) = 0 ↔ ρ = σ`. -/
theorem traceDistance_eq_zero_iff {d : ℕ} (ρ σ : DensityMatrix d) :
    traceDistance ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h0
    unfold traceDistance at h0
    have h : (ρ.mat - σ.mat).IsHermitian :=
      ρ.posSemidef.isHermitian.sub σ.posSemidef.isHermitian
    simp only [h, ↓reduceDIte] at h0
    have hsum : ∑ i : Fin d, |h.eigenvalues i| = 0 := by linarith
    have hall : ∀ i : Fin d, |h.eigenvalues i| = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)).mp hsum i (Finset.mem_univ i)
    have heig : h.eigenvalues = 0 := funext fun i => abs_eq_zero.mp (hall i)
    have hdiff : ρ.mat - σ.mat = 0 := h.eigenvalues_eq_zero_iff.mp heig
    exact densityMatrix_ext (sub_eq_zero.mp hdiff)
  · intro h; subst h; exact traceDistance_self ρ

end TraceDistance

/-! ### Section 4: Quantum Channels, Capacities, Explicit Channels, & `d = 2` SIC-POVM -/

section QuantumChannels

/-- Channel output preserves Hermiticity. -/
theorem applyMat_isHermitian {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    {ρ : Matrix (Fin d₁) (Fin d₁) ℂ} (hρ : ρ.IsHermitian) :
    (N.applyMat ρ).IsHermitian := by
  unfold QuantumChannel.applyMat
  refine isHermitian_sum Finset.univ _ fun a _ => ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

/-- Channel output preserves positive semidefiniteness (complete positivity). -/
theorem applyMat_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    {ρ : Matrix (Fin d₁) (Fin d₁) ℂ} (hρ : ρ.PosSemidef) :
    (N.applyMat ρ).PosSemidef := by
  unfold QuantumChannel.applyMat
  exact posSemidef_sum Finset.univ _ fun a _ => hρ.mul_mul_conjTranspose_same (N.kraus a)

/-- Channel output preserves trace: `Tr(N(ρ)) = Tr(ρ)`. -/
theorem applyMat_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) :
    (N.applyMat ρ).trace = ρ.trace := by
  unfold QuantumChannel.applyMat
  rw [Matrix.trace_sum]
  calc ∑ a : Fin N.numKraus, (N.kraus a * ρ * (N.kraus a)ᴴ).trace
      = ∑ a : Fin N.numKraus, ((N.kraus a)ᴴ * N.kraus a * ρ).trace := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
    _ = ((∑ a : Fin N.numKraus, (N.kraus a)ᴴ * N.kraus a) * ρ).trace := by
        rw [← Matrix.trace_sum, Matrix.sum_mul]
    _ = ρ.trace := by rw [N.tracePreserving, Matrix.one_mul]

/-- Apply a CPTP quantum channel to a density matrix, producing a density matrix. -/
def applyDensity {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (ρ : DensityMatrix d₁) :
    DensityMatrix d₂ where
  mat := N.applyMat ρ.mat
  posSemidef := applyMat_posSemidef N ρ.posSemidef
  trace_one := by rw [applyMat_trace, ρ.trace_one]

/-- Complementary channel preserves Hermiticity. -/
theorem complementaryMat_isHermitian {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    {ρ : Matrix (Fin d₁) (Fin d₁) ℂ} (hρ : ρ.IsHermitian) :
    (N.complementaryMat ρ).IsHermitian := by
  ext a b
  simp only [QuantumChannel.complementaryMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

/-- Complementary channel preserves positive semidefiniteness. -/
theorem complementaryMat_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    {ρ : Matrix (Fin d₁) (Fin d₁) ℂ} (hρ : ρ.PosSemidef) :
    (N.complementaryMat ρ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨complementaryMat_isHermitian N hρ.isHermitian, fun x => ?_⟩
  let B : Matrix (Fin d₂) (Fin d₁) ℂ := ∑ a : Fin N.numKraus, star (x a) • N.kraus a
  have hB_conj : Bᴴ = ∑ b : Fin N.numKraus, x b • (N.kraus b)ᴴ := by
    simp [B, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  have hquad : star x ⬝ᵥ (N.complementaryMat ρ).mulVec x = (B * ρ * Bᴴ).trace := by
    have hRHS : (B * ρ * Bᴴ).trace =
        ∑ a : Fin N.numKraus, ∑ b : Fin N.numKraus,
          star (x a) * x b * (N.kraus a * ρ * (N.kraus b)ᴴ).trace := by
      simp only [B, hB_conj, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hRHS]
    simp only [dotProduct, Matrix.mulVec, QuantumChannel.complementaryMat, Matrix.of_apply,
      Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hquad]
  exact (hρ.mul_mul_conjTranspose_same B).trace_nonneg

/-- Complementary channel preserves trace: `Tr(N^c(ρ)) = Tr(ρ)`. -/
theorem complementaryMat_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) :
    (N.complementaryMat ρ).trace = ρ.trace := by
  calc (N.complementaryMat ρ).trace
      = ∑ a : Fin N.numKraus, (N.kraus a * ρ * (N.kraus a)ᴴ).trace := rfl
    _ = (N.applyMat ρ).trace := by rw [QuantumChannel.applyMat, Matrix.trace_sum]
    _ = ρ.trace := applyMat_trace N ρ

/-- Apply the complementary channel `N^c` to a density matrix, producing a density matrix. -/
def complementaryDensity {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (ρ : DensityMatrix d₁) :
    DensityMatrix N.numKraus where
  mat := N.complementaryMat ρ.mat
  posSemidef := complementaryMat_posSemidef N ρ.posSemidef
  trace_one := by rw [complementaryMat_trace, ρ.trace_one]

/-- On any pure input state `|ψ⟩⟨ψ|`, a channel and its complementary channel have identical
    output entropies: `S(N(|ψ⟩⟨ψ|)) = S(N^c(|ψ⟩⟨ψ|))`. -/
theorem applyMat_pureState_entropy_eq_complementary {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ψ : Fin d₁ → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    matEntropy (N.applyMat (pureState ψ hψ).mat) =
      matEntropy (N.complementaryMat (pureState ψ hψ).mat) := by
  let M : Matrix (Fin d₂) (Fin N.numKraus) ℂ :=
    Matrix.of fun r a => (N.kraus a).mulVec ψ r
  have h1 : N.applyMat (pureState ψ hψ).mat = M * Mᴴ := by
    ext r s
    simp only [QuantumChannel.applyMat, pureState, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, M]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h2 : N.complementaryMat (pureState ψ hψ).mat = (Mᴴ * M).transpose := by
    ext a b
    simp only [QuantumChannel.complementaryMat, pureState, Matrix.transpose_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.mulVec, dotProduct, M]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, matEntropy_transpose]
  exact matEntropy_mul_conjTranspose_eq_conjTranspose_mul M

/-! #### `n`-fold Tensor Power Channels and Capacity Bounds -/

private lemma channel_pos_output_dim {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (hd₁ : 0 < d₁) :
    0 < d₂ := by
  by_contra h
  have hd₂ : d₂ = 0 := Nat.eq_zero_of_not_pos h
  subst hd₂
  have h1 : (∑ a : Fin N.numKraus, (N.kraus a)ᴴ * N.kraus a) ⟨0, hd₁⟩ ⟨0, hd₁⟩ = 0 := by
    simp [Matrix.sum_apply]
  rw [N.tracePreserving] at h1
  simp at h1

private lemma kronPowerMat_conjTranspose {d₁ d₂ : ℕ} :
    ∀ (n : ℕ) (f : Fin n → Matrix (Fin d₂) (Fin d₁) ℂ),
      (kronPowerMat n f)ᴴ = kronPowerMat n (fun i => (f i)ᴴ)
  | 0, _ => by
    ext i j
    simp [kronPowerMat]
    rfl
  | n + 1, f => by
    change (kronMat (kronPowerMat n fun i => f i.castSucc) (f (Fin.last n)))ᴴ =
      kronMat (kronPowerMat n fun i => (f i.castSucc)ᴴ) (f (Fin.last n))ᴴ
    rw [kronMat_conjTranspose, kronPowerMat_conjTranspose n]

private lemma kronPowerMat_mul {d₁ d₂ d₃ : ℕ} :
    ∀ (n : ℕ) (f : Fin n → Matrix (Fin d₂) (Fin d₁) ℂ) (g : Fin n → Matrix (Fin d₃) (Fin d₂) ℂ),
      kronPowerMat n g * kronPowerMat n f = kronPowerMat n (fun i => g i * f i)
  | 0, _, _ => by
    ext i j
    simp only [kronPowerMat, Matrix.mul_apply, sum_fin_pow_zero]
    change (1 : ℂ) * 1 = 1
    simp
  | n + 1, f, g => by
    change kronMat (kronPowerMat n fun i => g i.castSucc) (g (Fin.last n)) *
        kronMat (kronPowerMat n fun i => f i.castSucc) (f (Fin.last n)) =
      kronMat (kronPowerMat n fun i => g i.castSucc * f i.castSucc) (g (Fin.last n) * f (Fin.last n))
    rw [kronMat_mul, kronPowerMat_mul n]

private lemma kronPowerMat_one {d : ℕ} :
    ∀ n : ℕ, kronPowerMat n (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = 1
  | 0 => by ext i j; fin_cases i; fin_cases j; rfl
  | n + 1 => by
    change kronMat (kronPowerMat n (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)))
      (1 : Matrix (Fin d) (Fin d) ℂ) = 1
    rw [kronPowerMat_one n, kronMat_one]

private lemma sum_kronMat {m₁ m₂ : ℕ} {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (A : ι₁ → Matrix (Fin m₁) (Fin m₁) ℂ) (B : ι₂ → Matrix (Fin m₂) (Fin m₂) ℂ) :
    ∑ x : ι₁, ∑ y : ι₂, kronMat (A x) (B y) = kronMat (∑ x : ι₁, A x) (∑ y : ι₂, B y) := by
  ext i j
  simp only [Matrix.sum_apply, kronMat, Matrix.of_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]

private lemma kronPowerMat_tracePreserving {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    ∀ n : ℕ, ∑ s : Fin n → Fin N.numKraus,
      (kronPowerMat n (fun i => N.kraus (s i)))ᴴ * kronPowerMat n (fun i => N.kraus (s i)) = 1
  | 0 => by
    ext i j; fin_cases i; fin_cases j
    rw [Fintype.sum_unique]
    simp only [kronPowerMat, Matrix.mul_apply, Matrix.conjTranspose_apply, sum_fin_pow_zero]
    change star (1 : ℂ) * 1 = 1
    simp
  | n + 1 => by
    let e : (Fin n → Fin N.numKraus) × Fin N.numKraus ≃ (Fin (n + 1) → Fin N.numKraus) :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun s => (fun i => s i.castSucc, s (Fin.last n))
        left_inv := fun ⟨f, a⟩ => by ext i <;> simp [Fin.snoc]
        right_inv := fun s => by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc]
          · intro j; simp [Fin.snoc] }
    rw [← e.sum_comp, Fintype.sum_prod_type]
    have hstep : ∀ (f : Fin n → Fin N.numKraus) (a : Fin N.numKraus),
        (kronPowerMat (n + 1) (fun i => N.kraus (e (f, a) i)))ᴴ *
          kronPowerMat (n + 1) (fun i => N.kraus (e (f, a) i)) =
        kronMat ((kronPowerMat n (fun i => N.kraus (f i)))ᴴ *
          kronPowerMat n (fun i => N.kraus (f i))) ((N.kraus a)ᴴ * N.kraus a) := by
      intro f a
      have h1 : (fun i : Fin n => N.kraus (e (f, a) i.castSucc)) = fun i => N.kraus (f i) := by
        funext i; simp [e]
      have h2 : N.kraus (e (f, a) (Fin.last n)) = N.kraus a := by simp [e]
      change (kronMat (kronPowerMat n fun i => N.kraus (e (f, a) i.castSucc))
          (N.kraus (e (f, a) (Fin.last n))))ᴴ *
        kronMat (kronPowerMat n fun i => N.kraus (e (f, a) i.castSucc))
          (N.kraus (e (f, a) (Fin.last n))) = _
      rw [h1, h2, kronMat_conjTranspose, kronMat_mul]
    simp_rw [hstep]
    change ∑ f : Fin n → Fin N.numKraus, ∑ a : Fin N.numKraus,
        kronMat ((kronPowerMat n (fun i => N.kraus (f i)))ᴴ *
          kronPowerMat n (fun i => N.kraus (f i))) ((N.kraus a)ᴴ * N.kraus a) =
      (1 : Matrix (Fin (d₁ ^ n * d₁)) (Fin (d₁ ^ n * d₁)) ℂ)
    rw [sum_kronMat, kronPowerMat_tracePreserving N n, N.tracePreserving, kronMat_one]

private def mkIdxLE (k n : ℕ) (idx : Fin (k ^ n)) (i : Fin n) : Fin k :=
  ⟨(idx.1 / k ^ i.1) % k, by
    by_cases h : k = 0
    · have h0 : k ^ n = 0 := by
        cases n with
        | zero => exact Fin.elim0 i
        | succ m => rw [h]; exact zero_pow (Nat.succ_ne_zero m)
      exact absurd (lt_of_lt_of_eq idx.2 h0) (Nat.not_lt_zero _)
    · exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩

private lemma encodeLE_lt (k : ℕ) : ∀ (n : ℕ) (s : Fin n → Fin k),
    ∑ i : Fin n, (s i).1 * k ^ i.1 < k ^ n
  | 0, _ => by simp
  | n + 1, s => by
    rw [Fin.sum_univ_castSucc]
    have hih := encodeLE_lt k n (fun i => s i.castSucc)
    have hlast : (s (Fin.last n)).1 < k := (s (Fin.last n)).2
    have h1 : (s (Fin.last n)).1 + 1 ≤ k := hlast
    calc (∑ i : Fin n, (s i.castSucc).1 * k ^ i.1) + (s (Fin.last n)).1 * k ^ n
        < k ^ n + (s (Fin.last n)).1 * k ^ n := Nat.add_lt_add_right hih _
      _ = ((s (Fin.last n)).1 + 1) * k ^ n := by ring
      _ ≤ k * k ^ n := Nat.mul_le_mul_right _ h1
      _ = k ^ (n + 1) := by rw [pow_succ']

private lemma mkIdxLE_encodeLE (k : ℕ) : ∀ (n : ℕ) (s : Fin n → Fin k) (j : Fin n),
    ((∑ i : Fin n, (s i).1 * k ^ i.1) / k ^ j.1) % k = (s j).1
  | 0, _, j => Fin.elim0 j
  | n + 1, s, j => by
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ (s j).2)
    rw [Fin.sum_univ_castSucc]
    refine Fin.lastCases ?_ ?_ j
    · simp only [Fin.val_last, Fin.val_castSucc]
      have hih := encodeLE_lt k n (fun i => s i.castSucc)
      rw [add_comm, mul_right_add_div hih, Nat.mod_eq_of_lt (s (Fin.last n)).2]
    · intro j'
      simp only [Fin.val_castSucc, Fin.val_last]
      have hpow : k ^ n = k ^ j'.1 * k ^ (n - j'.1) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt j'.2)]
      have hkp : 0 < k ^ j'.1 := pow_pos hk j'.1
      have hrem : k ^ (n - j'.1) = k * k ^ (n - j'.1 - 1) := by
        have hpos : 1 ≤ n - j'.1 := Nat.sub_pos_of_lt j'.2
        conv_lhs => rw [← Nat.sub_add_cancel hpos]
        rw [pow_succ']
      rw [hpow, show (s (Fin.last n)).1 * (k ^ j'.1 * k ^ (n - j'.1)) =
          k ^ j'.1 * ((s (Fin.last n)).1 * k ^ (n - j'.1)) by ring,
        add_comm, Nat.mul_add_div hkp, hrem,
        show (s (Fin.last n)).1 * (k * k ^ (n - j'.1 - 1)) =
          k * ((s (Fin.last n)).1 * k ^ (n - j'.1 - 1)) by ring,
        Nat.mul_add_mod]
      exact mkIdxLE_encodeLE k n (fun i => s i.castSucc) j'

private lemma encodeLE_mkIdxLE (k : ℕ) : ∀ (n : ℕ) (x : ℕ), x < k ^ n →
    ∑ i : Fin n, ((x / k ^ i.1) % k) * k ^ i.1 = x
  | 0, x, hx => by simp at hx; simp [hx]
  | n + 1, x, hx => by
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by
      subst h; rw [zero_pow (Nat.succ_ne_zero n)] at hx; exact Nat.not_lt_zero _ hx)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hrem : x % k ^ n < k ^ n := Nat.mod_lt x (pow_pos hk n)
    have hmod_eq : ∀ i : Fin n, (x / k ^ i.1) % k = ((x % k ^ n) / k ^ i.1) % k := by
      intro i
      have hpow : k ^ n = k ^ i.1 * k ^ (n - i.1) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt i.2)]
      have hrem2 : k ^ (n - i.1) = k * k ^ (n - i.1 - 1) := by
        have hpos : 1 ≤ n - i.1 := Nat.sub_pos_of_lt i.2
        conv_lhs => rw [← Nat.sub_add_cancel hpos]
        rw [pow_succ']
      have hdecomp : x = k ^ i.1 * (k ^ (n - i.1) * (x / k ^ n)) + x % k ^ n := by
        calc x = k ^ n * (x / k ^ n) + x % k ^ n := (Nat.div_add_mod x (k ^ n)).symm
          _ = k ^ i.1 * (k ^ (n - i.1) * (x / k ^ n)) + x % k ^ n := by rw [hpow]; ring
      conv_lhs => rw [hdecomp]
      rw [Nat.mul_add_div (pow_pos hk i.1), hrem2,
        show k * k ^ (n - i.1 - 1) * (x / k ^ n) =
          k * (k ^ (n - i.1 - 1) * (x / k ^ n)) by ring,
        Nat.mul_add_mod]
    have hsum_eq : ∑ i : Fin n, ((x / k ^ i.1) % k) * k ^ i.1 = x % k ^ n := by
      calc ∑ i : Fin n, ((x / k ^ i.1) % k) * k ^ i.1
          = ∑ i : Fin n, (((x % k ^ n) / k ^ i.1) % k) * k ^ i.1 :=
            Finset.sum_congr rfl fun i _ => by rw [hmod_eq i]
        _ = x % k ^ n := encodeLE_mkIdxLE k n (x % k ^ n) hrem
    rw [hsum_eq]
    have hq_lt : x / k ^ n < k := Nat.div_lt_of_lt_mul (by rwa [← pow_succ])
    rw [Nat.mod_eq_of_lt hq_lt, mul_comm (x / k ^ n), add_comm, Nat.div_add_mod]

private def finPowEquivLE (k n : ℕ) : Fin (k ^ n) ≃ (Fin n → Fin k) where
  toFun := mkIdxLE k n
  invFun s := ⟨∑ i : Fin n, (s i).1 * k ^ i.1, encodeLE_lt k n s⟩
  left_inv idx := by
    ext
    exact encodeLE_mkIdxLE k n idx.1 idx.2
  right_inv s := by
    funext j; ext
    exact mkIdxLE_encodeLE k n s j

/-- `n`-fold tensor power channel output preserves positive semidefiniteness. -/
theorem channelPowerApply_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    {ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ} (hρ : ρ.PosSemidef) :
    (channelPowerApply N n ρ).PosSemidef := by
  unfold channelPowerApply
  exact posSemidef_sum Finset.univ _ fun s _ =>
    hρ.mul_mul_conjTranspose_same (kronPowerMat n (fun i => N.kraus (s i)))

/-- `n`-fold tensor power channel output preserves trace. -/
theorem channelPowerApply_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    (channelPowerApply N n ρ).trace = ρ.trace := by
  unfold channelPowerApply
  rw [Matrix.trace_sum]
  calc ∑ s : Fin n → Fin N.numKraus,
        (kronPowerMat n (fun i => N.kraus (s i)) * ρ *
          (kronPowerMat n (fun i => N.kraus (s i)))ᴴ).trace
      = ∑ s : Fin n → Fin N.numKraus,
        ((kronPowerMat n (fun i => N.kraus (s i)))ᴴ *
          kronPowerMat n (fun i => N.kraus (s i)) * ρ).trace := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
    _ = ((∑ s : Fin n → Fin N.numKraus,
          (kronPowerMat n (fun i => N.kraus (s i)))ᴴ *
            kronPowerMat n (fun i => N.kraus (s i))) * ρ).trace := by
        rw [← Matrix.trace_sum, Matrix.sum_mul]
    _ = ρ.trace := by rw [kronPowerMat_tracePreserving N n, Matrix.one_mul]

/-- `n`-fold complementary channel output preserves positive semidefiniteness. -/
theorem channelPowerCompApply_posSemidef {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    {ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ} (hρ : ρ.PosSemidef) :
    (channelPowerCompApply N n ρ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a b
    simp only [channelPowerCompApply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hρ.isHermitian.eq, Matrix.mul_assoc]
  · let K : Fin (N.numKraus ^ n) → Matrix (Fin (d₂ ^ n)) (Fin (d₁ ^ n)) ℂ := fun idx =>
      kronPowerMat n (fun i => N.kraus (mkIdxLE N.numKraus n idx i))
    let B : Matrix (Fin (d₂ ^ n)) (Fin (d₁ ^ n)) ℂ :=
      ∑ idx : Fin (N.numKraus ^ n), star (x idx) • K idx
    have hB_conj : Bᴴ = ∑ idx : Fin (N.numKraus ^ n), x idx • (K idx)ᴴ := by
      simp [B, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
    have hquad : star x ⬝ᵥ (channelPowerCompApply N n ρ).mulVec x = (B * ρ * Bᴴ).trace := by
      have hRHS : (B * ρ * Bᴴ).trace =
          ∑ a : Fin (N.numKraus ^ n), ∑ b : Fin (N.numKraus ^ n),
            star (x a) * x b * (K a * ρ * (K b)ᴴ).trace := by
        simp only [B, hB_conj, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [hRHS]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      change star (x a) * ((K a * ρ * (K b)ᴴ).trace * x b) =
        star (x a) * x b * (K a * ρ * (K b)ᴴ).trace
      ring
    rw [hquad]
    exact (hρ.mul_mul_conjTranspose_same B).trace_nonneg

/-- `n`-fold complementary channel output preserves trace. -/
theorem channelPowerCompApply_trace {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    (channelPowerCompApply N n ρ).trace = ρ.trace := by
  let g : (Fin n → Fin N.numKraus) → ℂ := fun s =>
    (kronPowerMat n (fun i => N.kraus (s i)) * ρ *
      (kronPowerMat n (fun i => N.kraus (s i)))ᴴ).trace
  calc (channelPowerCompApply N n ρ).trace
      = ∑ idx : Fin (N.numKraus ^ n), g (finPowEquivLE N.numKraus n idx) := rfl
    _ = ∑ s : Fin n → Fin N.numKraus, g s := (finPowEquivLE N.numKraus n).sum_comp g
    _ = (channelPowerApply N n ρ).trace := by rw [channelPowerApply, Matrix.trace_sum]
    _ = ρ.trace := channelPowerApply_trace N n ρ

/-- `n`-fold purification symmetry: on any pure input `|ψ⟩⟨ψ|`, `S(N^{⊗ n}(|ψ⟩⟨ψ|)) = S((N^{⊗ n})^c(|ψ⟩⟨ψ|))`. -/
private lemma channelPowerApply_pureState_entropy_eq_comp {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (n : ℕ) (ψ : Fin (d₁ ^ n) → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    matEntropy (channelPowerApply N n (pureState ψ hψ).mat) =
      matEntropy (channelPowerCompApply N n (pureState ψ hψ).mat) := by
  let K : Fin (N.numKraus ^ n) → Matrix (Fin (d₂ ^ n)) (Fin (d₁ ^ n)) ℂ := fun idx =>
    kronPowerMat n (fun i => N.kraus (finPowEquivLE N.numKraus n idx i))
  let M : Matrix (Fin (d₂ ^ n)) (Fin (N.numKraus ^ n)) ℂ :=
    Matrix.of fun r idx => (K idx).mulVec ψ r
  have h1 : channelPowerApply N n (pureState ψ hψ).mat = M * Mᴴ := by
    ext r s
    simp only [channelPowerApply, pureState, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, M]
    rw [← (finPowEquivLE N.numKraus n).sum_comp]
    refine Finset.sum_congr rfl fun idx _ => ?_
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum, K]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h2 : channelPowerCompApply N n (pureState ψ hψ).mat = (Mᴴ * M).transpose := by
    ext a b
    have hLHS : channelPowerCompApply N n (pureState ψ hψ).mat a b =
        (K a * (pureState ψ hψ).mat * (K b)ᴴ).trace := rfl
    rw [hLHS]
    simp only [pureState, Matrix.transpose_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, M]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, matEntropy_transpose]
  exact matEntropy_mul_conjTranspose_eq_conjTranspose_mul M

/-- Minimum output entropy is nonnegative: `0 ≤ S_min(N)`. -/
theorem minOutputEntropy_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    0 ≤ minOutputEntropy N := by
  unfold minOutputEntropy
  by_cases hd₁ : 0 < d₁
  · refine le_csInf ⟨matEntropy (N.applyMat (maxMixedState d₁ hd₁).mat), maxMixedState d₁ hd₁, rfl⟩ ?_
    rintro r ⟨ρ, rfl⟩
    exact matEntropy_nonneg_of_posSemidef_trace_one
      (applyMat_posSemidef N ρ.posSemidef) (by rw [applyMat_trace, ρ.trace_one])
  · have hEmpty : { r : ℝ | ∃ ρ : DensityMatrix d₁, r = matEntropy (N.applyMat ρ.mat) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨ρ, _⟩
      exact hd₁ (densityMatrix_dim_pos ρ)
    rw [hEmpty, Real.sInf_empty]

/-- Minimum output entropy is bounded above by `log₂ d₂`: `S_min(N) ≤ log₂ d₂`. -/
theorem minOutputEntropy_le_log2 {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (hd₂ : 0 < d₂) :
    minOutputEntropy N ≤ log2 d₂ := by
  unfold minOutputEntropy
  by_cases hd₁ : 0 < d₁
  · have hbdd : BddBelow { r : ℝ | ∃ ρ : DensityMatrix d₁, r = matEntropy (N.applyMat ρ.mat) } := by
      refine ⟨0, ?_⟩
      rintro r ⟨ρ, rfl⟩
      exact matEntropy_nonneg_of_posSemidef_trace_one
        (applyMat_posSemidef N ρ.posSemidef) (by rw [applyMat_trace, ρ.trace_one])
    calc sInf { r : ℝ | ∃ ρ : DensityMatrix d₁, r = matEntropy (N.applyMat ρ.mat) }
        ≤ matEntropy (N.applyMat (maxMixedState d₁ hd₁).mat) :=
          csInf_le hbdd ⟨maxMixedState d₁ hd₁, rfl⟩
      _ ≤ log2 d₂ :=
          matEntropy_le_log2_of_posSemidef_trace_one
            (applyMat_posSemidef N (maxMixedState d₁ hd₁).posSemidef)
            (by rw [applyMat_trace, (maxMixedState d₁ hd₁).trace_one]) hd₂
  · have hEmpty : { r : ℝ | ∃ ρ : DensityMatrix d₁, r = matEntropy (N.applyMat ρ.mat) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨ρ, _⟩
      exact hd₁ (densityMatrix_dim_pos ρ)
    rw [hEmpty, Real.sInf_empty]
    unfold log2
    exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hd₂)) (le_of_lt (Real.log_pos (by norm_num)))

/-- Coherent information upper bound: `I_c(ρ, N^{⊗ n}) ≤ n · log₂ d₂`. -/
theorem coherentInfoN_le {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : DensityMatrix (d₁ ^ n)) :
    coherentInfoN N n ρ ≤ (n : ℝ) * log2 d₂ := by
  unfold coherentInfoN
  have hcomp_nonneg : 0 ≤ matEntropy (channelPowerCompApply N n ρ.mat) :=
    matEntropy_nonneg_of_posSemidef_trace_one
      (channelPowerCompApply_posSemidef N n ρ.posSemidef)
      (by rw [channelPowerCompApply_trace, ρ.trace_one])
  cases n with
  | zero =>
    have h1 : matEntropy (channelPowerApply N 0 ρ.mat) ≤ log2 (d₂ ^ 0 : ℕ) :=
      matEntropy_le_log2_of_posSemidef_trace_one
        (channelPowerApply_posSemidef N 0 ρ.posSemidef)
        (by rw [channelPowerApply_trace, ρ.trace_one]) (by simp)
    have hlog0 : log2 ((d₂ ^ 0 : ℕ) : ℝ) = 0 := by simp [log2]
    rw [hlog0] at h1
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ m =>
    have hd1_pos : 0 < d₁ := by
      have hpow : 0 < d₁ ^ (m + 1) := densityMatrix_dim_pos ρ
      exact Nat.pos_of_ne_zero fun h => by
        rw [h, zero_pow (Nat.succ_ne_zero m)] at hpow; exact Nat.not_lt_zero _ hpow
    have hd2_pos : 0 < d₂ := channel_pos_output_dim N hd1_pos
    have h1 : matEntropy (channelPowerApply N (m + 1) ρ.mat) ≤ log2 (d₂ ^ (m + 1) : ℕ) :=
      matEntropy_le_log2_of_posSemidef_trace_one
        (channelPowerApply_posSemidef N (m + 1) ρ.posSemidef)
        (by rw [channelPowerApply_trace, ρ.trace_one]) (pow_pos hd2_pos (m + 1))
    have hlog : log2 (d₂ ^ (m + 1) : ℕ) = ((m + 1 : ℕ) : ℝ) * log2 d₂ := by
      unfold log2
      rw [Nat.cast_pow, Real.log_pow, mul_div_assoc]
    rw [hlog] at h1
    linarith

private lemma coherentInfoRegN_bddAbove {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (hn : 0 < n) :
    BddAbove { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) } := by
  refine ⟨log2 d₂, ?_⟩
  rintro r ⟨ρ, rfl⟩
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hle := coherentInfoN_le N n ρ
  rw [div_le_iff₀ hn_pos]
  linarith

private lemma coherentInfoRegN_le_log2 {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (hn : 0 < n) (hd₂ : 0 < d₂) :
    coherentInfoRegN N n ≤ log2 d₂ := by
  unfold coherentInfoRegN
  by_cases hd₁ : 0 < d₁
  · have hne : { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) }.Nonempty :=
      ⟨_, maxMixedState (d₁ ^ n) (pow_pos hd₁ n), rfl⟩
    refine csSup_le hne ?_
    rintro r ⟨ρ, rfl⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [div_le_iff₀ hn_pos]
    linarith [coherentInfoN_le N n ρ]
  · have hEmpty : { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨ρ, _⟩
      have hpow := densityMatrix_dim_pos ρ
      have h0 : d₁ = 0 := Nat.eq_zero_of_not_pos hd₁
      rw [h0, zero_pow (Nat.ne_of_gt hn)] at hpow
      exact Nat.not_lt_zero _ hpow
    rw [hEmpty, Real.sSup_empty]
    unfold log2
    exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hd₂)) (le_of_lt (Real.log_pos (by norm_num)))

private lemma coherentInfoRegN_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (hn : 0 < n) :
    0 ≤ coherentInfoRegN N n := by
  unfold coherentInfoRegN
  by_cases hd₁ : 0 < d₁
  · have hpow : 0 < d₁ ^ n := pow_pos hd₁ n
    let e0 : Fin (d₁ ^ n) → ℂ := Pi.single ⟨0, hpow⟩ 1
    have he0 : ∑ i : Fin (d₁ ^ n), ‖e0 i‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single ⟨0, hpow⟩]
      · simp [e0]
      · intro b _ hb; simp [e0, hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    let ρ0 : DensityMatrix (d₁ ^ n) := pureState e0 he0
    have hzero : coherentInfoN N n ρ0 = 0 := by
      unfold coherentInfoN
      rw [channelPowerApply_pureState_entropy_eq_comp N n e0 he0, sub_self]
    have hmem : (0 : ℝ) ∈ { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) } :=
      ⟨ρ0, by rw [hzero, zero_div]⟩
    exact le_csSup (coherentInfoRegN_bddAbove N n hn) hmem
  · have hEmpty : { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨ρ, _⟩
      have hpow := densityMatrix_dim_pos ρ
      have h0 : d₁ = 0 := Nat.eq_zero_of_not_pos hd₁
      rw [h0, zero_pow (Nat.ne_of_gt hn)] at hpow
      exact Nat.not_lt_zero _ hpow
    rw [hEmpty, Real.sSup_empty]

/-- Quantum capacity is nonnegative: `0 ≤ Q(N)`. -/
theorem quantumCapacity_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    0 ≤ quantumCapacity N := by
  unfold quantumCapacity
  by_cases hd₂ : 0 < d₂
  · have hbdd : BddAbove { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN N n } := by
      refine ⟨log2 d₂, ?_⟩
      rintro r ⟨n, hn, rfl⟩
      exact coherentInfoRegN_le_log2 N n hn hd₂
    calc (0 : ℝ) ≤ coherentInfoRegN N 1 := coherentInfoRegN_nonneg N 1 Nat.one_pos
      _ ≤ sSup { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN N n } :=
          le_csSup hbdd ⟨1, Nat.one_pos, rfl⟩
  · have hd₁ : ¬ 0 < d₁ := fun h => hd₂ (channel_pos_output_dim N h)
    have hval : ∀ n : ℕ, 0 < n → coherentInfoRegN N n = 0 := by
      intro n hn
      unfold coherentInfoRegN
      have hEmpty : { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) } = ∅ := by
        ext r; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨ρ, _⟩
        have hpow := densityMatrix_dim_pos ρ
        have h0 : d₁ = 0 := Nat.eq_zero_of_not_pos hd₁
        rw [h0, zero_pow (Nat.ne_of_gt hn)] at hpow
        exact Nat.not_lt_zero _ hpow
      rw [hEmpty, Real.sSup_empty]
    have hbdd : BddAbove { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN N n } := by
      refine ⟨0, ?_⟩
      rintro r ⟨n, hn, rfl⟩
      rw [hval n hn]
    have hmem : (0 : ℝ) ∈ { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN N n } :=
      ⟨1, Nat.one_pos, (hval 1 Nat.one_pos).symm⟩
    exact le_csSup hbdd hmem

/-- Quantum capacity upper bound: `Q(N) ≤ log₂ d₂`. -/
theorem quantumCapacity_le_log2 {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (hd₂ : 0 < d₂) :
    quantumCapacity N ≤ log2 d₂ := by
  unfold quantumCapacity
  refine csSup_le ⟨coherentInfoRegN N 1, 1, Nat.one_pos, rfl⟩ ?_
  rintro r ⟨n, hn, rfl⟩
  exact coherentInfoRegN_le_log2 N n hn hd₂

private lemma privateCapacity_term_le {d₁ d₂ n m : ℕ} (N : QuantumChannel d₁ d₂)
    (hn : 0 < n) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)) :
    let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
    let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
    let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
    let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
    (chiB - chiE) / (n : ℝ) ≤ log2 d₂ := by
  intro avgB avgE chiB chiE
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst hm0
    have := P.sum_one
    simp at this
  have hd1_pos : 0 < d₁ := by
    have hpow := densityMatrix_dim_pos (σ ⟨0, hm⟩)
    exact Nat.pos_of_ne_zero fun h => by
      rw [h, zero_pow (Nat.ne_of_gt hn)] at hpow; exact Nat.not_lt_zero _ hpow
  have hd2_pos : 0 < d₂ := channel_pos_output_dim N hd1_pos
  have hchiE_nonneg : 0 ≤ chiE := by
    have hconc := vonNeumannEntropy_concave P
      (fun x => channelPowerCompApply N n (σ x).mat)
      (fun x => channelPowerCompApply_posSemidef N n (σ x).posSemidef)
    linarith
  have havgB_pos : avgB.PosSemidef :=
    posSemidef_sum Finset.univ _ fun x _ =>
      posSemidef_smul_real (channelPowerApply_posSemidef N n (σ x).posSemidef) (P.nonneg x)
  have havgB_tr : avgB.trace = 1 := by
    simp only [avgB, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    calc ∑ x : Fin m, (P.pmf x : ℂ) * (channelPowerApply N n (σ x).mat).trace
        = ∑ x : Fin m, (P.pmf x : ℂ) := by
          refine Finset.sum_congr rfl fun x _ => by
            rw [channelPowerApply_trace, (σ x).trace_one, mul_one]
      _ = 1 := by rw [← Complex.ofReal_sum, P.sum_one, Complex.ofReal_one]
  have havgB_le : matEntropy avgB ≤ (n : ℝ) * log2 d₂ := by
    have h1 := matEntropy_le_log2_of_posSemidef_trace_one havgB_pos havgB_tr (pow_pos hd2_pos n)
    have hlog : log2 (d₂ ^ n : ℕ) = (n : ℝ) * log2 d₂ := by
      unfold log2; rw [Nat.cast_pow, Real.log_pow, mul_div_assoc]
    rwa [hlog] at h1
  have hsumB_nonneg : 0 ≤ ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat) :=
    Finset.sum_nonneg fun x _ =>
      mul_nonneg (P.nonneg x) (matEntropy_nonneg_of_posSemidef_trace_one
        (channelPowerApply_posSemidef N n (σ x).posSemidef)
        (by rw [channelPowerApply_trace, (σ x).trace_one]))
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hn_pos]
  linarith

/-- Private capacity is nonnegative: `0 ≤ P(N)`. -/
theorem privateCapacity_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    0 ≤ privateCapacity N := by
  unfold privateCapacity
  by_cases hd₁ : 0 < d₁
  · have hbdd : BddAbove { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
        0 < n ∧
        let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
        let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
        let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
        let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
        r = (chiB - chiE) / (n : ℝ) } := by
      refine ⟨log2 d₂, ?_⟩
      rintro r ⟨n, m, P, σ, hn, rfl⟩
      exact privateCapacity_term_le N hn P σ
    have hmem : (0 : ℝ) ∈ { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
        0 < n ∧
        let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
        let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
        let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
        let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
        r = (chiB - chiE) / (n : ℝ) } := by
      refine ⟨1, 1, ProbDist.uniform, fun _ => maxMixedState (d₁ ^ 1) (by simpa using hd₁), Nat.one_pos, ?_⟩
      simp [ProbDist.uniform]
    exact le_csSup hbdd hmem
  · have hEmpty : { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
        0 < n ∧
        let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
        let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
        let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
        let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
        r = (chiB - chiE) / (n : ℝ) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, m, P, σ, hn, _⟩
      have hm : 0 < m := by
        by_contra h
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
        subst hm0; have := P.sum_one; simp at this
      have hpow := densityMatrix_dim_pos (σ ⟨0, hm⟩)
      have h0 : d₁ = 0 := Nat.eq_zero_of_not_pos hd₁
      rw [h0, zero_pow (Nat.ne_of_gt hn)] at hpow
      exact Nat.not_lt_zero _ hpow
    rw [hEmpty, Real.sSup_empty]

/-- Private capacity upper bound: `P(N) ≤ log₂ d₂`. -/
theorem privateCapacity_le_log2 {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (hd₂ : 0 < d₂) :
    privateCapacity N ≤ log2 d₂ := by
  unfold privateCapacity
  by_cases hd₁ : 0 < d₁
  · have hne : { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
        0 < n ∧
        let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
        let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
        let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
        let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
        r = (chiB - chiE) / (n : ℝ) }.Nonempty := by
      refine ⟨0, 1, 1, ProbDist.uniform, fun _ => maxMixedState (d₁ ^ 1) (by simpa using hd₁),
        Nat.one_pos, ?_⟩
      simp [ProbDist.uniform]
    refine csSup_le hne ?_
    rintro r ⟨n, m, P, σ, hn, rfl⟩
    exact privateCapacity_term_le N hn P σ
  · have hEmpty : { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
        0 < n ∧
        let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
        let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
        let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
        let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
        r = (chiB - chiE) / (n : ℝ) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, m, P, σ, hn, _⟩
      have hm : 0 < m := by
        by_contra h
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
        subst hm0; have := P.sum_one; simp at this
      have hpow := densityMatrix_dim_pos (σ ⟨0, hm⟩)
      have h0 : d₁ = 0 := Nat.eq_zero_of_not_pos hd₁
      rw [h0, zero_pow (Nat.ne_of_gt hn)] at hpow
      exact Nat.not_lt_zero _ hpow
    rw [hEmpty, Real.sSup_empty]
    unfold log2
    exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hd₂)) (le_of_lt (Real.log_pos (by norm_num)))

/-! #### Explicit Channels: Identity, Replacement, Depolarizing, and Two-Pauli -/

/-- The `d`-dimensional noiseless identity quantum channel `id_d(ρ) = ρ`. -/
def idQuantumChannel (d : ℕ) : QuantumChannel d d where
  numKraus := 1
  kraus := fun _ => 1
  tracePreserving := by simp

/-- Action of the identity channel: `(idQuantumChannel d).applyMat ρ = ρ`. -/
@[simp]
theorem idQuantumChannel_applyMat (d : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (idQuantumChannel d).applyMat ρ = ρ := by
  change ∑ _ : Fin 1, (1 : Matrix (Fin d) (Fin d) ℂ) * ρ * (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ = ρ
  simp

/-- Minimum output entropy of the identity channel is `0` for `d > 0`. -/
theorem idQuantumChannel_minOutputEntropy (d : ℕ) (hd : 0 < d) :
    minOutputEntropy (idQuantumChannel d) = 0 := by
  apply le_antisymm _ (minOutputEntropy_nonneg (idQuantumChannel d))
  unfold minOutputEntropy
  let e0 : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
  have he0 : ∑ i : Fin d, ‖e0 i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single ⟨0, hd⟩]
    · simp [e0]
    · intro b _ hb; simp [e0, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hbdd : BddBelow { r : ℝ | ∃ ρ : DensityMatrix d, r = matEntropy ((idQuantumChannel d).applyMat ρ.mat) } := by
    refine ⟨0, ?_⟩
    rintro r ⟨ρ, rfl⟩
    rw [idQuantumChannel_applyMat, matEntropy_eq_vonNeumannEntropy]
    exact vonNeumannEntropy_nonneg ρ
  calc sInf { r : ℝ | ∃ ρ : DensityMatrix d, r = matEntropy ((idQuantumChannel d).applyMat ρ.mat) }
      ≤ matEntropy ((idQuantumChannel d).applyMat (pureState e0 he0).mat) :=
        csInf_le hbdd ⟨pureState e0 he0, rfl⟩
    _ = 0 := by rw [idQuantumChannel_applyMat, matEntropy_eq_vonNeumannEntropy, vonNeumannEntropy_pure]

/-- Quantum capacity of the `d`-dimensional identity channel is `log₂ d` for `d > 0`. -/
theorem idQuantumChannel_quantumCapacity (d : ℕ) (hd : 0 < d) :
    quantumCapacity (idQuantumChannel d) = log2 d := by
  apply le_antisymm (quantumCapacity_le_log2 (idQuantumChannel d) hd)
  unfold quantumCapacity
  have hbdd : BddAbove { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN (idQuantumChannel d) n } := by
    refine ⟨log2 d, ?_⟩
    rintro r ⟨n, hn, rfl⟩
    exact coherentInfoRegN_le_log2 (idQuantumChannel d) n hn hd
  refine le_trans ?_ (le_csSup hbdd ⟨1, Nat.one_pos, rfl⟩)
  unfold coherentInfoRegN
  let ρ := maxMixedState (d ^ 1) (by simpa using hd)
  refine le_trans ?_ (le_csSup (coherentInfoRegN_bddAbove (idQuantumChannel d) 1 Nat.one_pos) ⟨ρ, rfl⟩)
  have happly : channelPowerApply (idQuantumChannel d) 1 ρ.mat = ρ.mat := by
    change (∑ _ : Fin 1 → Fin 1,
      let K := kronPowerMat 1 (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ))
      K * ρ.mat * Kᴴ) = ρ.mat
    rw [Fintype.sum_unique]
    dsimp only
    rw [kronPowerMat_one (d := d) 1, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have hcomp : matEntropy (channelPowerCompApply (idQuantumChannel d) 1 ρ.mat) = 0 := by
    have hge := matEntropy_nonneg_of_posSemidef_trace_one
      (channelPowerCompApply_posSemidef (idQuantumChannel d) 1 ρ.posSemidef)
      (by rw [channelPowerCompApply_trace, ρ.trace_one])
    have hle := matEntropy_le_log2_of_posSemidef_trace_one
      (channelPowerCompApply_posSemidef (idQuantumChannel d) 1 ρ.posSemidef)
      (by rw [channelPowerCompApply_trace, ρ.trace_one]) (by simp [idQuantumChannel])
    have hlog1 : log2 (((idQuantumChannel d).numKraus ^ 1 : ℕ) : ℝ) = 0 := by
      simp [idQuantumChannel, log2]
    rw [hlog1] at hle
    linarith
  simp only [coherentInfoN, happly, hcomp, sub_zero, Nat.cast_one, div_one,
    matEntropy_eq_vonNeumannEntropy, ρ, vonNeumannEntropy_maxMixed]
  simp

private noncomputable def constChannelKraus {d₁ d₂ : ℕ}
    (V : Matrix (Fin d₂) (Fin d₂) ℂ) (lam : Fin d₂ → ℝ) (a : Fin (d₁ * d₂)) :
    Matrix (Fin d₂) (Fin d₁) ℂ :=
  let hB : 0 < d₂ := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ a.2)
  let i : Fin d₁ := ⟨a.1 / d₂, Nat.div_lt_of_lt_mul (by have := a.2; nlinarith)⟩
  let j : Fin d₂ := ⟨a.1 % d₂, Nat.mod_lt _ hB⟩
  Matrix.of fun r c => if c = i then ((Real.sqrt (lam j) : ℝ) : ℂ) * V r j else 0

private lemma constChannelKraus_apply {d₁ d₂ : ℕ}
    (V : Matrix (Fin d₂) (Fin d₂) ℂ) (lam : Fin d₂ → ℝ) (k : Fin (d₁ * d₂))
    (r : Fin d₂) (c : Fin d₁) :
    constChannelKraus V lam k r c =
      if c = ((finPairEquiv d₁ d₂).symm k).1 then
        ((Real.sqrt (lam ((finPairEquiv d₁ d₂).symm k).2) : ℝ) : ℂ) *
          V r ((finPairEquiv d₁ d₂).symm k).2
      else 0 := rfl

private lemma constChannel_tracePreserving_aux {d₁ d₂ : ℕ}
    (V : Matrix (Fin d₂) (Fin d₂) ℂ) (hVV' : Vᴴ * V = 1)
    (lam : Fin d₂ → ℝ) (hlam0 : ∀ j, 0 ≤ lam j) (hlam1 : ∑ j : Fin d₂, (lam j : ℂ) = 1) :
    ∑ a : Fin (d₁ * d₂), (constChannelKraus V lam a)ᴴ * constChannelKraus V lam a = 1 := by
  ext c₁ c₂
  simp only [constChannelKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [sum_fin_mul]
  have hinner : ∀ (i : Fin d₁) (j : Fin d₂),
      ∑ r : Fin d₂,
        star (if c₁ = ⟨(i.1 * d₂ + j.1) / d₂,
            Nat.div_lt_of_lt_mul (by have := finMulIdx i j; nlinarith)⟩ then
            ((Real.sqrt (lam ⟨(i.1 * d₂ + j.1) % d₂,
              Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩) :
              ℝ) : ℂ) * V r ⟨(i.1 * d₂ + j.1) % d₂,
              Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩
          else 0) *
        (if c₂ = ⟨(i.1 * d₂ + j.1) / d₂,
            Nat.div_lt_of_lt_mul (by have := finMulIdx i j; nlinarith)⟩ then
            ((Real.sqrt (lam ⟨(i.1 * d₂ + j.1) % d₂,
              Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩) :
              ℝ) : ℂ) * V r ⟨(i.1 * d₂ + j.1) % d₂,
              Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩
          else 0) =
      if c₁ = i ∧ c₂ = i then (lam j : ℂ) else 0 := by
    intro i j
    have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2)
    have hi : (⟨(i.1 * d₂ + j.1) / d₂,
        Nat.div_lt_of_lt_mul (by have := finMulIdx i j; nlinarith)⟩ : Fin d₁) = i :=
      Fin.ext (mul_right_add_div j.2)
    have hj : (⟨(i.1 * d₂ + j.1) % d₂, Nat.mod_lt _ hd₂⟩ : Fin d₂) = j :=
      Fin.ext (mul_right_add_mod j.2)
    simp_rw [hi, hj]
    by_cases h1 : c₁ = i
    · by_cases h2 : c₂ = i
      · simp only [h1, h2, ↓reduceIte, and_self, star_mul']
        have hnorm : ∑ r : Fin d₂, star (V r j) * V r j = 1 := by
          have := congrFun (congrFun hVV' j) j
          simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
        calc _ = (((Real.sqrt (lam j) : ℝ) : ℂ) * ((Real.sqrt (lam j) : ℝ) : ℂ)) *
                ∑ r : Fin d₂, star (V r j) * V r j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ => ?_
              simp only [Complex.star_def, Complex.conj_ofReal]; ring
          _ = (lam j : ℂ) := by
              rw [hnorm, mul_one, ← Complex.ofReal_mul, Real.mul_self_sqrt (hlam0 j)]
      · simp [h1, h2]
    · simp [h1]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hinner i j).trans ?_
  by_cases h12 : c₁ = c₂
  · subst h12
    rw [Finset.sum_eq_single c₁]
    · simp [hlam1]
    · intro i _ hi; simp [Ne.symm hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [h12, ↓reduceIte]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hnot : ¬ (c₁ = i ∧ c₂ = i) := fun ⟨ha, hb⟩ => h12 (ha.trans hb.symm)
    simp [hnot]

/-- Replacement (constant) channel `Φ_σ(ρ) = Tr(ρ) · σ` built from the eigendecomposition of `σ`. -/
noncomputable def constQuantumChannel (d₁ : ℕ) {d₂ : ℕ} (σ : DensityMatrix d₂) :
    QuantumChannel d₁ d₂ where
  numKraus := d₁ * d₂
  kraus := constChannelKraus
    (σ.posSemidef.isHermitian.eigenvectorUnitary : Matrix (Fin d₂) (Fin d₂) ℂ)
    σ.posSemidef.isHermitian.eigenvalues
  tracePreserving :=
    constChannel_tracePreserving_aux
      (σ.posSemidef.isHermitian.eigenvectorUnitary : Matrix (Fin d₂) (Fin d₂) ℂ)
      (spectral_unitary_mul_left σ.posSemidef.isHermitian)
      σ.posSemidef.isHermitian.eigenvalues
      σ.posSemidef.eigenvalues_nonneg
      (by have htr := σ.posSemidef.isHermitian.trace_eq_sum_eigenvalues; rw [σ.trace_one] at htr; exact htr.symm)

private lemma constChannel_applyMat_aux {d₁ d₂ : ℕ}
    (V : Matrix (Fin d₂) (Fin d₂) ℂ) (lam : Fin d₂ → ℝ) (hlam0 : ∀ j, 0 ≤ lam j)
    (σmat : Matrix (Fin d₂) (Fin d₂) ℂ)
    (hspec : σmat = V * Matrix.diagonal (fun j => (lam j : ℂ)) * Vᴴ)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) :
    (∑ a : Fin (d₁ * d₂),
      constChannelKraus V lam a * ρ * (constChannelKraus V lam a)ᴴ) = ρ.trace • σmat := by
  ext r s
  simp only [constChannelKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag]
  rw [sum_fin_mul]
  have hterm : ∀ (i : Fin d₁) (j : Fin d₂),
      ∑ c₂ : Fin d₁, (∑ c₁ : Fin d₁,
        (if c₁ = ⟨(i.1 * d₂ + j.1) / d₂,
            Nat.div_lt_of_lt_mul (by have := finMulIdx i j; nlinarith)⟩ then
            ((Real.sqrt (lam ⟨(i.1 * d₂ + j.1) % d₂, Nat.mod_lt _
              (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩) : ℝ) : ℂ) *
              V r ⟨(i.1 * d₂ + j.1) % d₂, Nat.mod_lt _
                (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩
          else 0) * ρ c₁ c₂) *
        star (if c₂ = ⟨(i.1 * d₂ + j.1) / d₂,
            Nat.div_lt_of_lt_mul (by have := finMulIdx i j; nlinarith)⟩ then
            ((Real.sqrt (lam ⟨(i.1 * d₂ + j.1) % d₂, Nat.mod_lt _
              (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩) : ℝ) : ℂ) *
              V s ⟨(i.1 * d₂ + j.1) % d₂, Nat.mod_lt _
                (Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2))⟩
          else 0) =
      ρ i i * ((lam j : ℂ) * V r j * star (V s j)) := by
    intro i j
    have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2)
    have hi : (⟨(i.1 * d₂ + j.1) / d₂,
        Nat.div_lt_of_lt_mul (by have := finMulIdx i j; nlinarith)⟩ : Fin d₁) = i :=
      Fin.ext (mul_right_add_div j.2)
    have hj : (⟨(i.1 * d₂ + j.1) % d₂, Nat.mod_lt _ hd₂⟩ : Fin d₂) = j :=
      Fin.ext (mul_right_add_mod j.2)
    simp_rw [hi, hj]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte, star_mul']
        have hsq : ((Real.sqrt (lam j) : ℝ) : ℂ) * ((Real.sqrt (lam j) : ℝ) : ℂ) = (lam j : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam0 j)]
        have hst : star ((Real.sqrt (lam j) : ℝ) : ℂ) = ((Real.sqrt (lam j) : ℝ) : ℂ) := by
          simp
        rw [hst]
        calc _ = ρ i i * ((((Real.sqrt (lam j) : ℝ) : ℂ) * ((Real.sqrt (lam j) : ℝ) : ℂ)) *
                V r j * star (V s j)) := by ring
          _ = ρ i i * ((lam j : ℂ) * V r j * star (V s j)) := by rw [hsq]
      · intro c₁ _ hc₁; simp [hc₁]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c₂ _ hc₂; simp [hc₂]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j).trans ?_
  have hfact : ∀ i : Fin d₁,
      ∑ j : Fin d₂, ρ i i * ((lam j : ℂ) * V r j * star (V s j)) =
      ρ i i * ∑ j : Fin d₂, (lam j : ℂ) * V r j * star (V s j) :=
    fun i => (Finset.mul_sum _ _ _).symm
  simp_rw [hfact, ← Finset.sum_mul]
  congr 1
  have hσ_rs : σmat r s = ∑ j : Fin d₂, (lam j : ℂ) * V r j * star (V s j) := by
    have := congrFun (congrFun hspec r) s
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => by ring
  exact hσ_rs.symm

/-- Action of the replacement channel: `(constQuantumChannel d₁ σ).applyMat ρ = Tr(ρ) • σ.mat`. -/
theorem constQuantumChannel_applyMat (d₁ : ℕ) {d₂ : ℕ} (σ : DensityMatrix d₂)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) :
    (constQuantumChannel d₁ σ).applyMat ρ = ρ.trace • σ.mat := by
  unfold QuantumChannel.applyMat constQuantumChannel
  dsimp only
  exact constChannel_applyMat_aux
    (σ.posSemidef.isHermitian.eigenvectorUnitary : Matrix (Fin d₂) (Fin d₂) ℂ)
    σ.posSemidef.isHermitian.eigenvalues
    σ.posSemidef.eigenvalues_nonneg
    σ.mat
    (spectral_decomp σ.posSemidef.isHermitian)
    ρ

/-! #### Big-Endian Indexing Helpers for `constQuantumChannel_quantumCapacity` -/

private def encodeBE (d : ℕ) : ∀ (n : ℕ), (Fin n → Fin d) → Fin (d ^ n)
  | 0, _ => ⟨0, by simp⟩
  | n + 1, f =>
    ⟨(encodeBE d n (fun i => f i.castSucc)).1 * d + (f (Fin.last n)).1,
      finMulIdx (encodeBE d n (fun i => f i.castSucc)) (f (Fin.last n))⟩

private def decodeBE (d : ℕ) : ∀ (n : ℕ), Fin (d ^ n) → (Fin n → Fin d)
  | 0, _ => Fin.elim0
  | n + 1, idx =>
    have hd : 0 < d := Nat.pos_of_ne_zero fun h => by
      subst h; rw [zero_pow (Nat.succ_ne_zero n)] at idx; exact Nat.not_lt_zero _ idx.2
    Fin.snoc (decodeBE d n ⟨idx.1 / d, div_lt_pow_of_lt_pow_succ idx.2⟩)
      ⟨idx.1 % d, Nat.mod_lt _ hd⟩

private def finPowEquivBE (d n : ℕ) : (Fin n → Fin d) ≃ Fin (d ^ n) where
  toFun := encodeBE d n
  invFun := decodeBE d n
  left_inv f := by
    induction n with
    | zero => funext i; exact Fin.elim0 i
    | succ n ih =>
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [decodeBE, encodeBE, Fin.snoc_last, mul_right_add_mod (f (Fin.last n)).2]
      · intro j
        simp only [decodeBE, encodeBE, Fin.snoc_castSucc]
        have hfin : (⟨((encodeBE d n fun i => f i.castSucc).1 * d + (f (Fin.last n)).1) / d,
            div_lt_pow_of_lt_pow_succ (finMulIdx (encodeBE d n fun i => f i.castSucc) (f (Fin.last n)))⟩ :
            Fin (d ^ n)) = encodeBE d n (fun i => f i.castSucc) :=
          Fin.ext (mul_right_add_div (f (Fin.last n)).2)
        rw [hfin]
        exact congrFun (ih (fun i => f i.castSucc)) j
  right_inv idx := by
    induction n with
    | zero => ext; have := idx.2; simp at this; simp [encodeBE, this]
    | succ n ih =>
      ext
      simp only [encodeBE, decodeBE, Fin.snoc_castSucc, Fin.snoc_last]
      have hrec := congrArg Fin.val (ih ⟨idx.1 / d, div_lt_pow_of_lt_pow_succ idx.2⟩)
      rw [hrec, mul_comm, Nat.div_add_mod]

private lemma constChannel_kronPowerMat_entry {d₁ d₂ : ℕ} (σ : DensityMatrix d₂) :
    ∀ (n : ℕ) (s : Fin n → Fin (d₁ * d₂)) (r : Fin (d₂ ^ n)) (c : Fin (d₁ ^ n)),
      let V : Matrix (Fin d₂) (Fin d₂) ℂ := σ.posSemidef.isHermitian.eigenvectorUnitary
      let a : Fin n → Fin d₁ := fun k => (finPairEquiv d₁ d₂).symm (s k) |>.1
      let b : Fin n → Fin d₂ := fun k => (finPairEquiv d₁ d₂).symm (s k) |>.2
      kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (s k)) r c =
        if c = encodeBE d₁ n a then
          (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ)) *
            kronPowerMat n (fun _ => V) r (encodeBE d₂ n b)
        else 0
  | 0, s, r, c => by
    fin_cases r; fin_cases c
    simp only [kronPowerMat, encodeBE, ↓reduceIte, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rfl
  | n + 1, s, r, c => by
    intro V a b
    have hd1 : 0 < d₁ := Nat.pos_of_ne_zero fun h => by
      subst h; rw [zero_pow (Nat.succ_ne_zero n)] at c; exact Nat.not_lt_zero _ c.2
    have hd2 : 0 < d₂ := Nat.pos_of_ne_zero fun h => by
      subst h; rw [zero_pow (Nat.succ_ne_zero n)] at r; exact Nat.not_lt_zero _ r.2
    change kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (s k.castSucc))
        ⟨r.1 / d₂, div_lt_pow_of_lt_pow_succ r.2⟩ ⟨c.1 / d₁, div_lt_pow_of_lt_pow_succ c.2⟩ *
      (constQuantumChannel d₁ σ).kraus (s (Fin.last n))
        ⟨r.1 % d₂, Nat.mod_lt _ hd2⟩ ⟨c.1 % d₁, Nat.mod_lt _ hd1⟩ = _
    have hih := constChannel_kronPowerMat_entry σ n (fun k => s k.castSucc)
      ⟨r.1 / d₂, div_lt_pow_of_lt_pow_succ r.2⟩
      ⟨c.1 / d₁, div_lt_pow_of_lt_pow_succ c.2⟩
    dsimp only at hih
    rw [hih]
    have hlast_kraus :
        (constQuantumChannel d₁ σ).kraus (s (Fin.last n))
          ⟨r.1 % d₂, Nat.mod_lt _ hd2⟩ ⟨c.1 % d₁, Nat.mod_lt _ hd1⟩ =
        if (⟨c.1 % d₁, Nat.mod_lt _ hd1⟩ : Fin d₁) = a (Fin.last n) then
          ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b (Fin.last n))) : ℝ) : ℂ) *
            V ⟨r.1 % d₂, Nat.mod_lt _ hd2⟩ (b (Fin.last n))
        else 0 := by
      unfold constQuantumChannel
      dsimp only
      exact constChannelKraus_apply V σ.posSemidef.isHermitian.eigenvalues (s (Fin.last n)) _ _
    rw [hlast_kraus]
    have hcond :
        ((⟨c.1 / d₁, div_lt_pow_of_lt_pow_succ c.2⟩ :
            Fin (d₁ ^ n)) = encodeBE d₁ n (fun k => a k.castSucc) ∧
          (⟨c.1 % d₁, Nat.mod_lt _ hd1⟩ : Fin d₁) = a (Fin.last n)) ↔
        c = encodeBE d₁ (n + 1) a := by
      constructor
      · rintro ⟨h1, h2⟩
        ext
        have h1' := congrArg Fin.val h1
        have h2' := congrArg Fin.val h2
        dsimp only [encodeBE] at h1' h2' ⊢
        rw [← h1', ← h2', mul_comm, Nat.div_add_mod]
      · intro h
        subst h
        constructor <;> ext
        · exact mul_right_add_div (a (Fin.last n)).2
        · exact mul_right_add_mod (a (Fin.last n)).2
    have hdiv_fin : (⟨(encodeBE d₂ (n + 1) b).1 / d₂,
        div_lt_pow_of_lt_pow_succ (encodeBE d₂ (n + 1) b).2⟩ :
        Fin (d₂ ^ n)) = encodeBE d₂ n (fun k => b k.castSucc) :=
      Fin.ext (mul_right_add_div (b (Fin.last n)).2)
    have hmod_fin : (⟨(encodeBE d₂ (n + 1) b).1 % d₂, Nat.mod_lt _ hd2⟩ : Fin d₂) = b (Fin.last n) :=
      Fin.ext (mul_right_add_mod (b (Fin.last n)).2)
    by_cases hc : c = encodeBE d₁ (n + 1) a
    · obtain ⟨h1, h2⟩ := hcond.mpr hc
      have h1' : (⟨c.1 / d₁, div_lt_pow_of_lt_pow_succ c.2⟩ : Fin (d₁ ^ n)) =
          encodeBE d₁ n (fun k => ((finPairEquiv d₁ d₂).symm (s k.castSucc)).1) := h1
      rw [ite_eq_left_iff.mpr (fun h => absurd hc h),
        ite_eq_left_iff.mpr (fun h => absurd h1' h),
        ite_eq_left_iff.mpr (fun h => absurd h2 h),
        Fin.prod_univ_castSucc]
      change _ = (∏ i : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b i.castSucc)) : ℝ) : ℂ)) *
          ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b (Fin.last n))) : ℝ) : ℂ) *
          (kronPowerMat n (fun _ => V) ⟨r.1 / d₂, div_lt_pow_of_lt_pow_succ r.2⟩
            ⟨(encodeBE d₂ (n + 1) b).1 / d₂, div_lt_pow_of_lt_pow_succ (encodeBE d₂ (n + 1) b).2⟩ *
           V ⟨r.1 % d₂, Nat.mod_lt _ hd2⟩ ⟨(encodeBE d₂ (n + 1) b).1 % d₂, Nat.mod_lt _ hd2⟩)
      rw [hdiv_fin, hmod_fin]
      change (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k.castSucc)) : ℝ) : ℂ)) *
          kronPowerMat n (fun _ => V) ⟨r.1 / d₂, div_lt_pow_of_lt_pow_succ r.2⟩
            (encodeBE d₂ n (fun k => b k.castSucc)) *
          (((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b (Fin.last n))) : ℝ) : ℂ) *
            V ⟨r.1 % d₂, Nat.mod_lt _ hd2⟩ (b (Fin.last n))) = _
      ring
    · simp only [hc, ↓reduceIte]
      by_cases h1 : (⟨c.1 / d₁, div_lt_pow_of_lt_pow_succ c.2⟩ :
          Fin (d₁ ^ n)) = encodeBE d₁ n (fun k => a k.castSucc)
      · have h2 : ¬ ((⟨c.1 % d₁, Nat.mod_lt _ hd1⟩ : Fin d₁) = a (Fin.last n)) :=
          fun h2 => hc (hcond.mp ⟨h1, h2⟩)
        simp only [h2, ↓reduceIte, mul_zero]
      · have h1' : ¬ ((⟨c.1 / d₁, div_lt_pow_of_lt_pow_succ c.2⟩ : Fin (d₁ ^ n)) =
            encodeBE d₁ n (fun k => ((finPairEquiv d₁ d₂).symm (s k.castSucc)).1)) := h1
        simp only [h1', ↓reduceIte, zero_mul]

private lemma constChannel_kronPowerMat_diag {d₂ : ℕ} (σ : DensityMatrix d₂) :
    ∀ (n : ℕ) (b₁ b₂ : Fin n → Fin d₂),
      kronPowerMat n (fun _ => Matrix.diagonal (fun j => (σ.posSemidef.isHermitian.eigenvalues j : ℂ)))
        (encodeBE d₂ n b₁) (encodeBE d₂ n b₂) =
      if b₁ = b₂ then ∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b₁ k) : ℂ) else 0
  | 0, b₁, b₂ => by
    have h : b₁ = b₂ := funext fun i => Fin.elim0 i
    simp only [h, ↓reduceIte, Finset.univ_eq_empty, Finset.prod_empty, kronPowerMat]
    rfl
  | n + 1, b₁, b₂ => by
    have hd₂ : 0 < d₂ := densityMatrix_dim_pos σ
    change kronPowerMat n (fun _ => Matrix.diagonal (fun j => (σ.posSemidef.isHermitian.eigenvalues j : ℂ)))
        ⟨(encodeBE d₂ (n + 1) b₁).1 / d₂, div_lt_pow_of_lt_pow_succ (encodeBE d₂ (n + 1) b₁).2⟩
        ⟨(encodeBE d₂ (n + 1) b₂).1 / d₂, div_lt_pow_of_lt_pow_succ (encodeBE d₂ (n + 1) b₂).2⟩ *
      Matrix.diagonal (fun j => (σ.posSemidef.isHermitian.eigenvalues j : ℂ))
        ⟨(encodeBE d₂ (n + 1) b₁).1 % d₂, Nat.mod_lt _ hd₂⟩
        ⟨(encodeBE d₂ (n + 1) b₂).1 % d₂, Nat.mod_lt _ hd₂⟩ = _
    have hdiv1 : (⟨(encodeBE d₂ (n + 1) b₁).1 / d₂,
        div_lt_pow_of_lt_pow_succ (encodeBE d₂ (n + 1) b₁).2⟩ :
        Fin (d₂ ^ n)) = encodeBE d₂ n (fun k => b₁ k.castSucc) :=
      Fin.ext (mul_right_add_div (b₁ (Fin.last n)).2)
    have hdiv2 : (⟨(encodeBE d₂ (n + 1) b₂).1 / d₂,
        div_lt_pow_of_lt_pow_succ (encodeBE d₂ (n + 1) b₂).2⟩ :
        Fin (d₂ ^ n)) = encodeBE d₂ n (fun k => b₂ k.castSucc) :=
      Fin.ext (mul_right_add_div (b₂ (Fin.last n)).2)
    have hmod1 : (⟨(encodeBE d₂ (n + 1) b₁).1 % d₂, Nat.mod_lt _ hd₂⟩ : Fin d₂) = b₁ (Fin.last n) :=
      Fin.ext (mul_right_add_mod (b₁ (Fin.last n)).2)
    have hmod2 : (⟨(encodeBE d₂ (n + 1) b₂).1 % d₂, Nat.mod_lt _ hd₂⟩ : Fin d₂) = b₂ (Fin.last n) :=
      Fin.ext (mul_right_add_mod (b₂ (Fin.last n)).2)
    rw [hdiv1, hdiv2, hmod1, hmod2, constChannel_kronPowerMat_diag σ n, Matrix.diagonal_apply]
    by_cases h : b₁ = b₂
    · subst h; simp [Fin.prod_univ_castSucc]
    · simp only [h, ↓reduceIte]
      by_cases h1 : (fun k : Fin n => b₁ k.castSucc) = (fun k : Fin n => b₂ k.castSucc)
      · have h2 : b₁ (Fin.last n) ≠ b₂ (Fin.last n) := by
          intro hlast
          apply h; funext i
          exact Fin.lastCases hlast (fun j => congrFun h1 j) i
        simp [h1, h2]
      · simp [h1]

private lemma constChannel_channelPowerApply {d₁ d₂ : ℕ} (σ : DensityMatrix d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    channelPowerApply (constQuantumChannel d₁ σ) n ρ =
      ρ.trace • kronPowerMat n (fun _ => σ.mat) := by
  let V : Matrix (Fin d₂) (Fin d₂) ℂ := σ.posSemidef.isHermitian.eigenvectorUnitary
  let D : Matrix (Fin d₂) (Fin d₂) ℂ :=
    Matrix.diagonal (fun j => (σ.posSemidef.isHermitian.eigenvalues j : ℂ))
  have hσ_power : kronPowerMat n (fun _ => σ.mat) =
      kronPowerMat n (fun _ => V) * kronPowerMat n (fun _ => D) *
        (kronPowerMat n (fun _ => V))ᴴ := by
    rw [kronPowerMat_conjTranspose, kronPowerMat_mul, kronPowerMat_mul]
    congr 1; funext _
    exact spectral_decomp σ.posSemidef.isHermitian
  ext r s
  unfold channelPowerApply
  simp only [Matrix.sum_apply]
  change (∑ s' : Fin n → Fin (d₁ * d₂),
    (kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (s' k)) * ρ *
      (kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (s' k)))ᴴ) r s) =
    (ρ.trace • kronPowerMat n (fun _ => σ.mat)) r s
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul]
  let e : (Fin n → Fin d₁) × (Fin n → Fin d₂) ≃ (Fin n → Fin (d₁ * d₂)) :=
    { toFun := fun p k => finPairEquiv d₁ d₂ (p.1 k, p.2 k)
      invFun := fun s => (fun k => ((finPairEquiv d₁ d₂).symm (s k)).1,
                          fun k => ((finPairEquiv d₁ d₂).symm (s k)).2)
      left_inv := fun ⟨a, b⟩ => by ext k <;> simp
      right_inv := fun s => by funext k; simp }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  have hterm : ∀ (a : Fin n → Fin d₁) (b : Fin n → Fin d₂),
      ∑ c₂ : Fin (d₁ ^ n), (∑ c₁ : Fin (d₁ ^ n),
        kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (e (a, b) k)) r c₁ * ρ c₁ c₂) *
        star (kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (e (a, b) k)) s c₂) =
      ρ (encodeBE d₁ n a) (encodeBE d₁ n a) *
        ((∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b k) : ℂ)) *
          kronPowerMat n (fun _ => V) r (encodeBE d₂ n b) *
          star (kronPowerMat n (fun _ => V) s (encodeBE d₂ n b))) := by
    intro a b
    have hK := fun r' c' => constChannel_kronPowerMat_entry σ n (e (a, b)) r' c'
    have hproj1 : (fun k => ((finPairEquiv d₁ d₂).symm (e (a, b) k)).1) = a := by
      funext k; simp [e]
    have hproj2 : (fun k => ((finPairEquiv d₁ d₂).symm (e (a, b) k)).2) = b := by
      funext k; simp [e]
    have hproj2' : ∀ k, ((finPairEquiv d₁ d₂).symm (e (a, b) k)).2 = b k := fun k => by simp [e]
    have hK' : ∀ r' c',
        kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (e (a, b) k)) r' c' =
        if c' = encodeBE d₁ n a then
          (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ)) *
            kronPowerMat n (fun _ => V) r' (encodeBE d₂ n b)
        else 0 := by
      intro r' c'
      have h1 := constChannel_kronPowerMat_entry σ n (e (a, b)) r' c'
      dsimp only at h1
      simp_rw [hproj1, hproj2, hproj2'] at h1
      exact h1
    simp_rw [hK']
    rw [Finset.sum_eq_single (encodeBE d₁ n a)]
    · rw [Finset.sum_eq_single (encodeBE d₁ n a)]
      · simp only [↓reduceIte, star_mul']
        have hprod_star :
            star (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ)) =
              ∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ) := by
          rw [star_prod]
          refine Finset.prod_congr rfl fun k _ => by simp
        rw [hprod_star]
        have hprod_sq :
            (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ)) *
              (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ)) =
            ∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b k) : ℂ) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (σ.posSemidef.eigenvalues_nonneg (b k))]
        calc _ = ρ (encodeBE d₁ n a) (encodeBE d₁ n a) *
                (((∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ)) *
                  (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b k)) : ℝ) : ℂ))) *
                  kronPowerMat n (fun _ => V) r (encodeBE d₂ n b) *
                  star (kronPowerMat n (fun _ => V) s (encodeBE d₂ n b))) := by ring
          _ = _ := by rw [hprod_sq]
      · intro c₁ _ hc₁; simp [hc₁]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c₂ _ hc₂; simp [hc₂]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hterm]
  have hfact : ∀ a : Fin n → Fin d₁,
      ∑ b : Fin n → Fin d₂,
        ρ (encodeBE d₁ n a) (encodeBE d₁ n a) *
          ((∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b k) : ℂ)) *
            kronPowerMat n (fun _ => V) r (encodeBE d₂ n b) *
            star (kronPowerMat n (fun _ => V) s (encodeBE d₂ n b))) =
      ρ (encodeBE d₁ n a) (encodeBE d₁ n a) *
        ∑ b : Fin n → Fin d₂,
          (∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b k) : ℂ)) *
            kronPowerMat n (fun _ => V) r (encodeBE d₂ n b) *
            star (kronPowerMat n (fun _ => V) s (encodeBE d₂ n b)) :=
    fun a => (Finset.mul_sum _ _ _).symm
  simp_rw [hfact, ← Finset.sum_mul]
  have htr : ∑ a : Fin n → Fin d₁, ρ (encodeBE d₁ n a) (encodeBE d₁ n a) = ρ.trace :=
    (finPowEquivBE d₁ n).sum_comp (fun idx => ρ idx idx)
  rw [htr]
  congr 1
  rw [hσ_power]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← (finPowEquivBE d₂ n).sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (finPowEquivBE d₂ n).sum_comp]
  rw [Finset.sum_eq_single b]
  · have hd := constChannel_kronPowerMat_diag σ n b b
    simp only [↓reduceIte] at hd
    change (∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b k) : ℂ)) *
        kronPowerMat n (fun _ => V) r (encodeBE d₂ n b) *
        star (kronPowerMat n (fun _ => V) s (encodeBE d₂ n b)) =
      kronPowerMat n (fun _ => V) r (encodeBE d₂ n b) *
        kronPowerMat n (fun _ => D) (encodeBE d₂ n b) (encodeBE d₂ n b) *
        star (kronPowerMat n (fun _ => V) s (encodeBE d₂ n b))
    rw [hd]; ring
  · intro b' _ hb'
    have hd := constChannel_kronPowerMat_diag σ n b' b
    simp only [hb', ↓reduceIte] at hd
    change kronPowerMat n (fun _ => V) r (encodeBE d₂ n b') *
        kronPowerMat n (fun _ => D) (encodeBE d₂ n b') (encodeBE d₂ n b) = 0
    rw [hd, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma kronPowerMat_const_posSemidef {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.PosSemidef) : ∀ n : ℕ, (kronPowerMat n (fun _ => M)).PosSemidef
  | 0 => by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨by ext i j; simp [kronPowerMat]; rfl, fun x => ?_⟩
    simp only [dotProduct, Matrix.mulVec, kronPowerMat, sum_fin_pow_zero]
    change 0 ≤ star (x ⟨0, by simp⟩) * ((1 : ℂ) * x ⟨0, by simp⟩)
    rw [one_mul]
    exact star_mul_self_nonneg _
  | n + 1 => kronMat_posSemidef (kronPowerMat_const_posSemidef hM n) hM

private lemma kronPowerMat_const_trace {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    ∀ n : ℕ, (kronPowerMat n (fun _ => M)).trace = M.trace ^ n
  | 0 => by
    simp only [Matrix.trace, Matrix.diag, kronPowerMat, sum_fin_pow_zero, pow_zero]
    rfl
  | n + 1 => by
    change (kronMat (kronPowerMat n (fun _ => M)) M).trace = M.trace ^ (n + 1)
    rw [kronMat_trace, kronPowerMat_const_trace M n, pow_succ]

/-- Quantum capacity of any replacement / constant channel is `0`. -/
theorem constQuantumChannel_quantumCapacity (d₁ : ℕ) {d₂ : ℕ} (σ : DensityMatrix d₂) :
    quantumCapacity (constQuantumChannel d₁ σ) = 0 := by
  apply le_antisymm _ (quantumCapacity_nonneg (constQuantumChannel d₁ σ))
  unfold quantumCapacity
  refine csSup_le ⟨coherentInfoRegN (constQuantumChannel d₁ σ) 1, 1, Nat.one_pos, rfl⟩ ?_
  rintro r ⟨n, hn, rfl⟩
  unfold coherentInfoRegN
  by_cases hd₁ : 0 < d₁
  · refine csSup_le ⟨_, maxMixedState (d₁ ^ n) (pow_pos hd₁ n), rfl⟩ ?_
    rintro q ⟨ρ, rfl⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    refine div_nonpos_of_nonpos_of_nonneg ?_ (le_of_lt hn_pos)
    unfold coherentInfoN
    let V : Matrix (Fin d₂) (Fin d₂) ℂ := σ.posSemidef.isHermitian.eigenvectorUnitary
    let D : Matrix (Fin d₂) (Fin d₂) ℂ :=
      Matrix.diagonal (fun j => (σ.posSemidef.isHermitian.eigenvalues j : ℂ))
    let Vn : Matrix (Fin (d₂ ^ n)) (Fin (d₂ ^ n)) ℂ := kronPowerMat n (fun _ => V)
    let Dn : Matrix (Fin (d₂ ^ n)) (Fin (d₂ ^ n)) ℂ := kronPowerMat n (fun _ => D)
    have hVn_unit : Vnᴴ * Vn = 1 := by
      dsimp only [Vn]
      rw [kronPowerMat_conjTranspose, kronPowerMat_mul]
      have hVV : Vᴴ * V = 1 := spectral_unitary_mul_left σ.posSemidef.isHermitian
      simp only [hVV, kronPowerMat_one]
    have hσn_eq : kronPowerMat n (fun _ => σ.mat) = Vn * Dn * Vnᴴ := by
      simp only [Vn, Dn, kronPowerMat_conjTranspose, kronPowerMat_mul]
      congr 1; funext _; exact spectral_decomp σ.posSemidef.isHermitian
    have hApply_ent : matEntropy (channelPowerApply (constQuantumChannel d₁ σ) n ρ.mat) =
        matEntropy Dn := by
      rw [constChannel_channelPowerApply σ n ρ.mat, ρ.trace_one, one_smul, hσn_eq,
        matEntropy_unitary_conj Vn hVn_unit Dn]
    let eMid : (Fin n → Fin (d₁ * d₂)) ≃ Fin (d₁ ^ n) × Fin (d₂ ^ n) :=
      { toFun := fun s =>
          (encodeBE d₁ n (fun k => ((finPairEquiv d₁ d₂).symm (s k)).1),
           encodeBE d₂ n (fun k => ((finPairEquiv d₁ d₂).symm (s k)).2))
        invFun := fun p k =>
          finPairEquiv d₁ d₂ (decodeBE d₁ n p.1 k, decodeBE d₂ n p.2 k)
        left_inv := fun s => by
          funext k
          have h1 := congrFun ((finPowEquivBE d₁ n).left_inv
            (fun k => ((finPairEquiv d₁ d₂).symm (s k)).1)) k
          have h2 := congrFun ((finPowEquivBE d₂ n).left_inv
            (fun k => ((finPairEquiv d₁ d₂).symm (s k)).2)) k
          dsimp only [finPowEquivBE] at h1 h2
          change finPairEquiv d₁ d₂
            (decodeBE d₁ n (encodeBE d₁ n fun k => ((finPairEquiv d₁ d₂).symm (s k)).1) k,
             decodeBE d₂ n (encodeBE d₂ n fun k => ((finPairEquiv d₁ d₂).symm (s k)).2) k) = s k
          rw [h1, h2]
          exact (finPairEquiv d₁ d₂).apply_symm_apply (s k)
        right_inv := fun ⟨x, y⟩ => by
          ext1
          · change encodeBE d₁ n (fun k => ((finPairEquiv d₁ d₂).symm
              (finPairEquiv d₁ d₂ (decodeBE d₁ n x k, decodeBE d₂ n y k))).1) = x
            simp only [Equiv.symm_apply_apply]
            exact (finPowEquivBE d₁ n).right_inv x
          · change encodeBE d₂ n (fun k => ((finPairEquiv d₁ d₂).symm
              (finPairEquiv d₁ d₂ (decodeBE d₁ n x k, decodeBE d₂ n y k))).2) = y
            simp only [Equiv.symm_apply_apply]
            exact (finPowEquivBE d₂ n).right_inv y }
    let ePerm : Fin ((d₁ * d₂) ^ n) ≃ Fin (d₁ ^ n * d₂ ^ n) :=
      (finPowEquivLE (d₁ * d₂) n).trans (eMid.trans (finPairEquiv (d₁ ^ n) (d₂ ^ n)))
    have hComp_sub : channelPowerCompApply (constQuantumChannel d₁ σ) n ρ.mat =
        (kronMat ρ.mat Dn).submatrix ePerm ePerm := by
      ext idx₁ idx₂
      let s₁ : Fin n → Fin (d₁ * d₂) := finPowEquivLE (d₁ * d₂) n idx₁
      let s₂ : Fin n → Fin (d₁ * d₂) := finPowEquivLE (d₁ * d₂) n idx₂
      let a₁ : Fin n → Fin d₁ := fun k => ((finPairEquiv d₁ d₂).symm (s₁ k)).1
      let b₁ : Fin n → Fin d₂ := fun k => ((finPairEquiv d₁ d₂).symm (s₁ k)).2
      let a₂ : Fin n → Fin d₁ := fun k => ((finPairEquiv d₁ d₂).symm (s₂ k)).1
      let b₂ : Fin n → Fin d₂ := fun k => ((finPairEquiv d₁ d₂).symm (s₂ k)).2
      have hLHS : channelPowerCompApply (constQuantumChannel d₁ σ) n ρ.mat idx₁ idx₂ =
          (kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (s₁ k)) * ρ.mat *
            (kronPowerMat n (fun k => (constQuantumChannel d₁ σ).kraus (s₂ k)))ᴴ).trace := rfl
      rw [hLHS, Matrix.trace]
      simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
      have hK1 := constChannel_kronPowerMat_entry σ n s₁
      have hK2 := constChannel_kronPowerMat_entry σ n s₂
      simp_rw [hK1, hK2]
      have hcollapse : ∀ r : Fin (d₂ ^ n),
          ∑ c₂ : Fin (d₁ ^ n),
            (∑ c₁ : Fin (d₁ ^ n),
              (if c₁ = encodeBE d₁ n a₁ then
                (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b₁ k)) : ℝ) : ℂ)) *
                  Vn r (encodeBE d₂ n b₁)
              else 0) * ρ.mat c₁ c₂) *
            star (if c₂ = encodeBE d₁ n a₂ then
              (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b₂ k)) : ℝ) : ℂ)) *
                Vn r (encodeBE d₂ n b₂)
            else 0) =
          ρ.mat (encodeBE d₁ n a₁) (encodeBE d₁ n a₂) *
            ((∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b₁ k)) : ℝ) : ℂ)) *
             (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b₂ k)) : ℝ) : ℂ))) *
            (star (Vn r (encodeBE d₂ n b₂)) * Vn r (encodeBE d₂ n b₁)) := by
        intro r
        rw [Finset.sum_eq_single (encodeBE d₁ n a₂)]
        · rw [Finset.sum_eq_single (encodeBE d₁ n a₁)]
          · simp only [↓reduceIte, star_mul']
            have hstar_prod :
                star (∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b₂ k)) : ℝ) : ℂ)) =
                  ∏ k : Fin n, ((Real.sqrt (σ.posSemidef.isHermitian.eigenvalues (b₂ k)) : ℝ) : ℂ) := by
              rw [star_prod]
              refine Finset.prod_congr rfl fun k _ => by simp
            rw [hstar_prod]; ring
          · intro c₁ _ hc₁; simp [hc₁]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro c₂ _ hc₂; simp [hc₂]
        · intro h; exact absurd (Finset.mem_univ _) h
      refine (Finset.sum_congr rfl fun r _ => hcollapse r).trans ?_
      rw [← Finset.mul_sum]
      have hortho : ∑ r : Fin (d₂ ^ n), star (Vn r (encodeBE d₂ n b₂)) * Vn r (encodeBE d₂ n b₁) =
          if b₁ = b₂ then 1 else 0 := by
        have h1 := congrFun (congrFun hVn_unit (encodeBE d₂ n b₂)) (encodeBE d₂ n b₁)
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h1
        rw [h1]
        by_cases h : b₁ = b₂
        · simp [h]
        · have hne : encodeBE d₂ n b₂ ≠ encodeBE d₂ n b₁ :=
            fun heq => h ((finPowEquivBE d₂ n).injective heq).symm
          simp [h, hne]
      rw [hortho]
      have hRHS : (kronMat ρ.mat Dn).submatrix ePerm ePerm idx₁ idx₂ =
          ρ.mat (encodeBE d₁ n a₁) (encodeBE d₁ n a₂) *
            Dn (encodeBE d₂ n b₁) (encodeBE d₂ n b₂) := by
        have hd2n : 0 < d₂ ^ n := pow_pos (densityMatrix_dim_pos σ) n
        simp only [kronMat, ePerm, eMid, Equiv.coe_fn_mk, finPairEquiv]
        have ha1 : (⟨((encodeBE d₁ n a₁).1 * d₂ ^ n + (encodeBE d₂ n b₁).1) / d₂ ^ n,
            Nat.div_lt_of_lt_mul (by have := finMulIdx (encodeBE d₁ n a₁) (encodeBE d₂ n b₁); nlinarith)⟩ :
            Fin (d₁ ^ n)) = encodeBE d₁ n a₁ :=
          Fin.ext (mul_right_add_div (encodeBE d₂ n b₁).2)
        have ha2 : (⟨((encodeBE d₁ n a₂).1 * d₂ ^ n + (encodeBE d₂ n b₂).1) / d₂ ^ n,
            Nat.div_lt_of_lt_mul (by have := finMulIdx (encodeBE d₁ n a₂) (encodeBE d₂ n b₂); nlinarith)⟩ :
            Fin (d₁ ^ n)) = encodeBE d₁ n a₂ :=
          Fin.ext (mul_right_add_div (encodeBE d₂ n b₂).2)
        have hb1 : (⟨((encodeBE d₁ n a₁).1 * d₂ ^ n + (encodeBE d₂ n b₁).1) % d₂ ^ n,
            Nat.mod_lt _ hd2n⟩ : Fin (d₂ ^ n)) = encodeBE d₂ n b₁ :=
          Fin.ext (mul_right_add_mod (encodeBE d₂ n b₁).2)
        have hb2 : (⟨((encodeBE d₁ n a₂).1 * d₂ ^ n + (encodeBE d₂ n b₂).1) % d₂ ^ n,
            Nat.mod_lt _ hd2n⟩ : Fin (d₂ ^ n)) = encodeBE d₂ n b₂ :=
          Fin.ext (mul_right_add_mod (encodeBE d₂ n b₂).2)
        change ρ.mat ⟨((encodeBE d₁ n a₁).1 * d₂ ^ n + (encodeBE d₂ n b₁).1) / d₂ ^ n, _⟩
            ⟨((encodeBE d₁ n a₂).1 * d₂ ^ n + (encodeBE d₂ n b₂).1) / d₂ ^ n, _⟩ *
          Dn ⟨((encodeBE d₁ n a₁).1 * d₂ ^ n + (encodeBE d₂ n b₁).1) % d₂ ^ n, _⟩
            ⟨((encodeBE d₁ n a₂).1 * d₂ ^ n + (encodeBE d₂ n b₂).1) % d₂ ^ n, _⟩ = _
        rw [ha1, ha2, hb1, hb2]
      rw [hRHS, show Dn (encodeBE d₂ n b₁) (encodeBE d₂ n b₂) =
        if b₁ = b₂ then ∏ k : Fin n, (σ.posSemidef.isHermitian.eigenvalues (b₁ k) : ℂ) else 0 from
          constChannel_kronPowerMat_diag σ n b₁ b₂]
      by_cases h : b₁ = b₂
      · simp only [h, ↓reduceIte, mul_one]
        congr 1
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (σ.posSemidef.eigenvalues_nonneg (b₂ k))]
      · simp [h]
    have hDn_pos : Dn.PosSemidef := by
      have h1 : Dn = Vnᴴ * kronPowerMat n (fun _ => σ.mat) * Vn := by
        rw [hσn_eq]; simp only [Matrix.mul_assoc]
        rw [hVn_unit, Matrix.mul_one, ← Matrix.mul_assoc, hVn_unit, Matrix.one_mul]
      rw [h1]
      exact (kronPowerMat_const_posSemidef σ.posSemidef n).conjTranspose_mul_mul_same Vn
    have hDn_tr : Dn.trace = 1 := by
      have h1 : Dn = Vnᴴ * kronPowerMat n (fun _ => σ.mat) * Vn := by
        rw [hσn_eq]; simp only [Matrix.mul_assoc]
        rw [hVn_unit, Matrix.mul_one, ← Matrix.mul_assoc, hVn_unit, Matrix.one_mul]
      rw [h1, Matrix.trace_mul_cycle, unitary_mul_conjTranspose hVn_unit, Matrix.one_mul,
        kronPowerMat_const_trace σ.mat n, σ.trace_one, one_pow]
    have hComp_ent : matEntropy (channelPowerCompApply (constQuantumChannel d₁ σ) n ρ.mat) =
        matEntropy (kronMat ρ.mat Dn) := by
      rw [hComp_sub]
      change matEntropy ((kronMat ρ.mat Dn).submatrix ePerm ePerm) = matEntropy (kronMat ρ.mat Dn)
      have hK_herm : (kronMat ρ.mat Dn).IsHermitian :=
        kronMat_isHermitian ρ.posSemidef.isHermitian hDn_pos.isHermitian
      have hSub_herm : ((kronMat ρ.mat Dn).submatrix ePerm ePerm).IsHermitian := by
        ext i j
        simp only [Matrix.conjTranspose_apply, Matrix.submatrix_apply]
        exact congrFun (congrFun hK_herm.eq (ePerm i)) (ePerm j)
      have hcp : ((kronMat ρ.mat Dn).submatrix ePerm ePerm).charpoly =
          (kronMat ρ.mat Dn).charpoly :=
        Matrix.charpoly_reindex ePerm.symm (kronMat ρ.mat Dn)
      have hLHS_ent : matEntropy ((kronMat ρ.mat Dn).submatrix ePerm ePerm) =
          ∑ i : Fin ((d₁ * d₂) ^ n), negPLogP (hSub_herm.eigenvalues i) := by
        simp only [matEntropy, hSub_herm, ↓reduceDIte]
      have hRHS_ent : matEntropy (kronMat ρ.mat Dn) =
          ∑ j : Fin (d₁ ^ n * d₂ ^ n), negPLogP (hK_herm.eigenvalues j) := by
        simp only [matEntropy, hK_herm, ↓reduceDIte]
      rw [hLHS_ent, hRHS_ent]
      have hc1 : ((kronMat ρ.mat Dn).submatrix ePerm ePerm).charpoly =
          ∏ i : Fin ((d₁ * d₂) ^ n), (Polynomial.X - Polynomial.C (hSub_herm.eigenvalues i : ℂ)) :=
        hSub_herm.charpoly_eq
      have hc2 : (kronMat ρ.mat Dn).charpoly =
          ∏ j : Fin (d₁ ^ n * d₂ ^ n), (Polynomial.X - Polynomial.C (hK_herm.eigenvalues j : ℂ)) :=
        hK_herm.charpoly_eq
      have hprod :
          ∏ i : Fin ((d₁ * d₂) ^ n), (Polynomial.X - Polynomial.C (hSub_herm.eigenvalues i : ℂ)) =
            ∏ j : Fin (d₁ ^ n * d₂ ^ n), (Polynomial.X - Polynomial.C (hK_herm.eigenvalues j : ℂ)) :=
        hc1.symm.trans (hcp.trans hc2)
      have hroots := congrArg Polynomial.roots hprod
      rw [multiset_map_roots_prod_X_sub_C, multiset_map_roots_prod_X_sub_C] at hroots
      have hre : Finset.univ.val.map hSub_herm.eigenvalues = Finset.univ.val.map hK_herm.eigenvalues := by
        have := congrArg (Multiset.map Complex.re) hroots
        simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at this
        exact this
      have hsum := congrArg (fun s : Multiset ℝ => (s.map negPLogP).sum) hre
      simp only [Multiset.map_map, Function.comp_def] at hsum
      exact hsum
    rw [hApply_ent, hComp_ent, matEntropy_kronMat ρ.posSemidef ρ.trace_one hDn_pos hDn_tr,
      matEntropy_eq_vonNeumannEntropy]
    linarith [vonNeumannEntropy_nonneg ρ]
  · have hEmpty : { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n),
        r = coherentInfoN (constQuantumChannel d₁ σ) n ρ / (n : ℝ) } = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]; rintro ⟨ρ, _⟩
      have hpow := densityMatrix_dim_pos ρ
      have h0 : d₁ = 0 := Nat.eq_zero_of_not_pos hd₁
      rw [h0, zero_pow (Nat.ne_of_gt hn)] at hpow
      exact Nat.not_lt_zero _ hpow
    rw [hEmpty, Real.sSup_empty]

/-! #### Explicit Qubit Depolarizing & Two-Pauli Channels -/

private lemma pauliI_conjTranspose : pauliIᴴ = pauliI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliI]

private lemma pauliX_conjTranspose : pauliXᴴ = pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX]

private lemma pauliY_conjTranspose : pauliYᴴ = pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY]

private lemma pauliZ_conjTranspose : pauliZᴴ = pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ]

private lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit Kraus realization of the qubit depolarizing channel `D_p` for `p ∈ [0, 1]`. -/
noncomputable def depolarizingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumChannel 2 2 where
  numKraus := 4
  kraus := ![
    ((Real.sqrt (1 - p) : ℝ) : ℂ) • pauliI,
    ((Real.sqrt (p / 3) : ℝ) : ℂ) • pauliX,
    ((Real.sqrt (p / 3) : ℝ) : ℂ) • pauliY,
    ((Real.sqrt (p / 3) : ℝ) : ℂ) • pauliZ]
  tracePreserving := by
    rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      pauliI, Matrix.conjTranspose_one, pauliX_conjTranspose, pauliY_conjTranspose,
      pauliZ_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, pauliX_mul_self, pauliY_mul_self, pauliZ_mul_self,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1),
      Real.mul_self_sqrt (div_nonneg hp0 (by norm_num : (0 : ℝ) ≤ 3)),
      ← add_smul]
    have hcoeff : ((1 - p : ℝ) : ℂ) + ((p / 3 : ℝ) : ℂ) + ((p / 3 : ℝ) : ℂ) + ((p / 3 : ℝ) : ℂ) = 1 := by
      push_cast; ring
    rw [hcoeff, one_smul]

/-- `depolarizingChannel p` realizes `depolarizingApply p`. -/
theorem depolarizingChannel_isDepolarizing (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDepolarizingChannel p (depolarizingChannel p hp0 hp1) := by
  intro ρ
  unfold QuantumChannel.applyMat depolarizingChannel depolarizingApply
  change ∑ a : Fin 4, _ = _
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    pauliI, Matrix.conjTranspose_one, pauliX_conjTranspose, pauliY_conjTranspose,
    pauliZ_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1),
    Real.mul_self_sqrt (div_nonneg hp0 (by norm_num : (0 : ℝ) ≤ 3))]
  simp only [smul_add, add_assoc]

/-- Explicit Kraus realization of the qubit two-Pauli channel `ρ ↦ (1-p)ρ + (p/2)(XρX + ZρZ)`. -/
noncomputable def twoPauliChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumChannel 2 2 where
  numKraus := 3
  kraus := ![
    ((Real.sqrt (1 - p) : ℝ) : ℂ) • pauliI,
    ((Real.sqrt (p / 2) : ℝ) : ℂ) • pauliX,
    ((Real.sqrt (p / 2) : ℝ) : ℂ) • pauliZ]
  tracePreserving := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      pauliI, Matrix.conjTranspose_one, pauliX_conjTranspose, pauliZ_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, pauliX_mul_self, pauliZ_mul_self,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1),
      Real.mul_self_sqrt (div_nonneg hp0 (by norm_num : (0 : ℝ) ≤ 2)),
      ← add_smul]
    have hcoeff : ((1 - p : ℝ) : ℂ) + ((p / 2 : ℝ) : ℂ) + ((p / 2 : ℝ) : ℂ) = 1 := by
      push_cast; ring
    rw [hcoeff, one_smul]

/-- `twoPauliChannel p` realizes the qubit two-Pauli channel predicate `IsTwoPauliChannel p`. -/
theorem twoPauliChannel_isTwoPauli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsTwoPauliChannel p (twoPauliChannel p hp0 hp1) := by
  intro ρ
  unfold QuantumChannel.applyMat twoPauliChannel
  change ∑ a : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    pauliI, Matrix.conjTranspose_one, pauliX_conjTranspose, pauliZ_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.mpr hp1),
    Real.mul_self_sqrt (div_nonneg hp0 (by norm_num : (0 : ℝ) ≤ 2))]
  simp only [smul_add, add_assoc]

/-! #### Explicit `d = 2` Tetrahedron SIC-POVM -/

/-- The four fiducial qubit states forming a regular tetrahedron on the Bloch sphere:
    `|ψ₀⟩ = |0⟩`, `|ψ₁⟩ = (1/√3, √(2/3))`, `|ψ₂⟩ = (1/√3, -1/√6 + i/√2)`,
    `|ψ₃⟩ = (1/√3, -1/√6 - i/√2)`. -/
noncomputable def sicPovmTwoVec : Fin (2 * 2) → Fin 2 → ℂ :=
  ![ ![1, 0],
     ![((1 / Real.sqrt 3 : ℝ) : ℂ), ((Real.sqrt (2 / 3) : ℝ) : ℂ)],
     ![((1 / Real.sqrt 3 : ℝ) : ℂ), ⟨-(1 / Real.sqrt 6), 1 / Real.sqrt 2⟩],
     ![((1 / Real.sqrt 3 : ℝ) : ℂ), ⟨-(1 / Real.sqrt 6), -(1 / Real.sqrt 2)⟩] ]

private lemma sq_norm_of_re_im (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private lemma sq_inv_sqrt (a : ℝ) (ha : 0 ≤ a) : (1 / Real.sqrt a) ^ 2 = 1 / a := by
  rw [one_div, inv_pow, Real.sq_sqrt ha, one_div]

private lemma sqrt_two_thirds_mul_inv_sqrt6 :
    Real.sqrt (2 / 3) * (1 / Real.sqrt 6) = 1 / 3 := by
  have h1 : Real.sqrt (2 / 3) / Real.sqrt 6 = Real.sqrt ((2 / 3) / 6) :=
    (Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2 / 3) 6).symm
  rw [mul_one_div, h1]
  have h2 : (2 / 3 : ℝ) / 6 = (1 / 3) ^ 2 := by norm_num
  rw [h2, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)]

private lemma sqrt_two_thirds_mul_inv_sqrt2 :
    Real.sqrt (2 / 3) * (1 / Real.sqrt 2) = 1 / Real.sqrt 3 := by
  have h1 : Real.sqrt (2 / 3) / Real.sqrt 2 = Real.sqrt ((2 / 3) / 2) :=
    (Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2 / 3) 2).symm
  rw [mul_one_div, h1]
  have h2 : (2 / 3 : ℝ) / 2 = 1 / 3 := by norm_num
  rw [h2, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

private lemma inv_sqrt6_mul_inv_sqrt2 :
    (1 / Real.sqrt 6) * (1 / Real.sqrt 2) = 1 / (2 * Real.sqrt 3) := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [h6]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2_ne : Real.sqrt 2 ≠ 0 := by positivity
  have h3_ne : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [h2_ne, h3_ne]
  linarith [h2]

/-- **Existence of a qubit (`d = 2`) SIC-POVM**: the 4 regular-tetrahedron states satisfy
    `IsSICPOVM 2`. -/
theorem exists_sicPovm_two : ∃ ψ : Fin (2 * 2) → Fin 2 → ℂ, IsSICPOVM 2 ψ := by
  refine ⟨sicPovmTwoVec, ?_, ?_⟩
  · intro j
    fin_cases j
    · simp [sicPovmTwoVec, Fin.sum_univ_two]
    · rw [Fin.sum_univ_two]
      change ‖((1 / Real.sqrt 3 : ℝ) : ℂ)‖ ^ 2 + ‖((Real.sqrt (2 / 3) : ℝ) : ℂ)‖ ^ 2 = 1
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [sq_inv_sqrt 3 (by norm_num), Real.sq_sqrt (by norm_num)]
      norm_num
    · rw [Fin.sum_univ_two]
      change ‖((1 / Real.sqrt 3 : ℝ) : ℂ)‖ ^ 2 +
        ‖(⟨-(1 / Real.sqrt 6), 1 / Real.sqrt 2⟩ : ℂ)‖ ^ 2 = 1
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq_norm_of_re_im, neg_sq]
      rw [sq_inv_sqrt 3 (by norm_num), sq_inv_sqrt 6 (by norm_num), sq_inv_sqrt 2 (by norm_num)]
      norm_num
    · rw [Fin.sum_univ_two]
      change ‖((1 / Real.sqrt 3 : ℝ) : ℂ)‖ ^ 2 +
        ‖(⟨-(1 / Real.sqrt 6), -(1 / Real.sqrt 2)⟩ : ℂ)‖ ^ 2 = 1
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq_norm_of_re_im, neg_sq]
      rw [sq_inv_sqrt 3 (by norm_num), sq_inv_sqrt 6 (by norm_num), sq_inv_sqrt 2 (by norm_num)]
      norm_num
  · have hsymm : ∀ j k : Fin (2 * 2),
        ‖∑ r : Fin 2, star (sicPovmTwoVec k r) * sicPovmTwoVec j r‖ ^ 2 =
          ‖∑ r : Fin 2, star (sicPovmTwoVec j r) * sicPovmTwoVec k r‖ ^ 2 := by
      intro j k
      have hconj : (∑ r : Fin 2, star (sicPovmTwoVec k r) * sicPovmTwoVec j r) =
          star (∑ r : Fin 2, star (sicPovmTwoVec j r) * sicPovmTwoVec k r) := by
        rw [star_sum]
        refine Finset.sum_congr rfl fun r _ => by simp [mul_comm]
      rw [hconj, norm_star]
    have h01 : ‖∑ r : Fin 2, star (sicPovmTwoVec 0 r) * sicPovmTwoVec 1 r‖ ^ 2 = 1 / 3 := by
      simp only [sicPovmTwoVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        star_one, star_zero, one_mul, zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact sq_inv_sqrt 3 (by norm_num)
    have h02 : ‖∑ r : Fin 2, star (sicPovmTwoVec 0 r) * sicPovmTwoVec 2 r‖ ^ 2 = 1 / 3 := by
      simp only [sicPovmTwoVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, star_one, star_zero, one_mul, zero_mul, add_zero, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
      exact sq_inv_sqrt 3 (by norm_num)
    have h03 : ‖∑ r : Fin 2, star (sicPovmTwoVec 0 r) * sicPovmTwoVec 3 r‖ ^ 2 = 1 / 3 := by
      simp only [sicPovmTwoVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, star_one, star_zero, one_mul, zero_mul, add_zero, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
      exact sq_inv_sqrt 3 (by norm_num)
    have h12 : ‖∑ r : Fin 2, star (sicPovmTwoVec 1 r) * sicPovmTwoVec 2 r‖ ^ 2 = 1 / 3 := by
      have hval : ∑ r : Fin 2, star (sicPovmTwoVec 1 r) * sicPovmTwoVec 2 r =
          ⟨0, 1 / Real.sqrt 3⟩ := by
        simp only [sicPovmTwoVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Complex.star_def, Complex.conj_ofReal]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero, mul_neg]
          rw [show (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = (1 / Real.sqrt 3) ^ 2 by ring,
            sq_inv_sqrt 3 (by norm_num), sqrt_two_thirds_mul_inv_sqrt6]
          norm_num
        · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, zero_mul, add_zero, zero_add]
          exact sqrt_two_thirds_mul_inv_sqrt2
      rw [hval, sq_norm_of_re_im, zero_pow (by norm_num), zero_add, sq_inv_sqrt 3 (by norm_num)]
    have h13 : ‖∑ r : Fin 2, star (sicPovmTwoVec 1 r) * sicPovmTwoVec 3 r‖ ^ 2 = 1 / 3 := by
      have hval : ∑ r : Fin 2, star (sicPovmTwoVec 1 r) * sicPovmTwoVec 3 r =
          ⟨0, -(1 / Real.sqrt 3)⟩ := by
        simp only [sicPovmTwoVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Complex.star_def, Complex.conj_ofReal]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero, mul_neg]
          rw [show (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = (1 / Real.sqrt 3) ^ 2 by ring,
            sq_inv_sqrt 3 (by norm_num), sqrt_two_thirds_mul_inv_sqrt6]
          norm_num
        · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, zero_mul, add_zero, zero_add, mul_neg]
          rw [sqrt_two_thirds_mul_inv_sqrt2]; ring
      rw [hval, sq_norm_of_re_im, zero_pow (by norm_num), zero_add, neg_sq, sq_inv_sqrt 3 (by norm_num)]
    have h23 : ‖∑ r : Fin 2, star (sicPovmTwoVec 2 r) * sicPovmTwoVec 3 r‖ ^ 2 = 1 / 3 := by
      have hval : ∑ r : Fin 2, star (sicPovmTwoVec 2 r) * sicPovmTwoVec 3 r =
          ⟨0, 1 / Real.sqrt 3⟩ := by
        simp only [sicPovmTwoVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Complex.star_def, Complex.conj_ofReal]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, mul_neg, neg_mul, neg_neg]
          rw [show (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = (1 / Real.sqrt 3) ^ 2 by ring,
            show (1 / Real.sqrt 6) * (1 / Real.sqrt 6) = (1 / Real.sqrt 6) ^ 2 by ring,
            show (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / Real.sqrt 2) ^ 2 by ring,
            sq_inv_sqrt 3 (by norm_num), sq_inv_sqrt 6 (by norm_num), sq_inv_sqrt 2 (by norm_num)]
          norm_num
        · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.conj_re, Complex.conj_im, mul_zero, zero_mul, add_zero, zero_add,
            mul_neg, neg_mul, neg_neg]
          rw [show (1 / Real.sqrt 6) * (1 / Real.sqrt 2) + (1 / Real.sqrt 2) * (1 / Real.sqrt 6) =
            2 * ((1 / Real.sqrt 6) * (1 / Real.sqrt 2)) by ring, inv_sqrt6_mul_inv_sqrt2]
          ring
      rw [hval, sq_norm_of_re_im, zero_pow (by norm_num), zero_add, sq_inv_sqrt 3 (by norm_num)]
    intro j k hjk
    have htarget : (1 : ℝ) / ((2 : ℕ) + 1 : ℝ) = 1 / 3 := by norm_num
    rw [htarget]
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · exact h01
    · exact h02
    · exact h03
    · rw [hsymm]; exact h01
    · exact absurd rfl hjk
    · exact h12
    · exact h13
    · rw [hsymm]; exact h02
    · rw [hsymm]; exact h12
    · exact absurd rfl hjk
    · exact h23
    · rw [hsymm]; exact h03
    · rw [hsymm]; exact h13
    · rw [hsymm]; exact h23
    · exact absurd rfl hjk

end QuantumChannels

end InfoTheory.Bridge
