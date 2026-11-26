import InfoTheory.Core.Entropy
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Core Quantum Information Theory Definitions

Finite-dimensional density matrices, Kraus-represented CPTP quantum channels,
von Neumann entropy, Holevo information, coherent information, quantum/classical/private
capacities, entanglement (separability, PPT, bound entanglement), SIC-POVMs, and
squashed entanglement. Zero `sorry` anywhere.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory

/-- A `d × d` density matrix: Hermitian, positive semidefinite, and trace 1. -/
structure DensityMatrix (d : ℕ) where
  mat : Matrix (Fin d) (Fin d) ℂ
  posSemidef : mat.PosSemidef
  trace_one : mat.trace = 1

/-- Von Neumann entropy `S(ρ) = -Tr(ρ log₂ ρ)` defined via eigenvalues of `ρ`. -/
noncomputable def vonNeumannEntropy {d : ℕ} (ρ : DensityMatrix d) : ℝ :=
  ∑ i : Fin d, negPLogP (ρ.posSemidef.isHermitian.eigenvalues i)

/-- Von Neumann entropy of an arbitrary matrix (0 if not Hermitian, else `-∑ λ_i log₂ λ_i`). -/
noncomputable def matEntropy {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : ℝ := by
  classical
  exact if h : M.IsHermitian then ∑ i : Fin d, negPLogP (h.eigenvalues i) else 0

/-- A completely positive trace-preserving (CPTP) quantum channel `Φ : M_{d₁}(ℂ) → M_{d₂}(ℂ)`
    given by a finite Kraus representation `{K_a}` with `∑_a K_a† K_a = I`. -/
structure QuantumChannel (d₁ d₂ : ℕ) where
  numKraus : ℕ
  kraus : Fin numKraus → Matrix (Fin d₂) (Fin d₁) ℂ
  tracePreserving : ∑ a : Fin numKraus, (kraus a)ᴴ * (kraus a) = 1

/-- Action of a CPTP channel on a matrix `ρ`. -/
def QuantumChannel.applyMat {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) : Matrix (Fin d₂) (Fin d₂) ℂ :=
  ∑ a : Fin N.numKraus, N.kraus a * ρ * (N.kraus a)ᴴ

/-- Complementary channel `N^c(ρ)` associated to the Stinespring dilation of `N`. -/
def QuantumChannel.complementaryMat {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ρ : Matrix (Fin d₁) (Fin d₁) ℂ) : Matrix (Fin N.numKraus) (Fin N.numKraus) ℂ :=
  Matrix.of fun a b => (N.kraus a * ρ * (N.kraus b)ᴴ).trace

/-- Kronecker tensor product of two complex matrices. -/
def kronMat {m₁ n₁ m₂ n₂ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℂ) (B : Matrix (Fin m₂) (Fin n₂) ℂ) :
    Matrix (Fin (m₁ * m₂)) (Fin (n₁ * n₂)) ℂ :=
  Matrix.of fun i j =>
    let hm : 0 < m₂ := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ i.2)
    let hn : 0 < n₂ := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ j.2)
    A ⟨i.1 / m₂, Nat.div_lt_of_lt_mul (by have := i.2; nlinarith)⟩
      ⟨j.1 / n₂, Nat.div_lt_of_lt_mul (by have := j.2; nlinarith)⟩ *
    B ⟨i.1 % m₂, Nat.mod_lt _ hm⟩ ⟨j.1 % n₂, Nat.mod_lt _ hn⟩

/-- Action of tensor product channel `(N₁ ⊗ N₂)(ρ)` directly via Kraus operators `K_a ⊗ L_b`. -/
def tensorChannelApply {d₁ d₂ e₁ e₂ : ℕ}
    (N₁ : QuantumChannel d₁ d₂) (N₂ : QuantumChannel e₁ e₂)
    (ρ : Matrix (Fin (d₁ * e₁)) (Fin (d₁ * e₁)) ℂ) :
    Matrix (Fin (d₂ * e₂)) (Fin (d₂ * e₂)) ℂ :=
  ∑ a : Fin N₁.numKraus, ∑ b : Fin N₂.numKraus,
    kronMat (N₁.kraus a) (N₂.kraus b) * ρ * (kronMat (N₁.kraus a) (N₂.kraus b))ᴴ

/-- `n`-fold tensor power of a Kraus operator family indexed by `Fin n`. -/
def kronPowerMat {d₁ d₂ : ℕ} :
    (n : ℕ) → (Fin n → Matrix (Fin d₂) (Fin d₁) ℂ) →
    Matrix (Fin (d₂ ^ n)) (Fin (d₁ ^ n)) ℂ
  | 0, _ => Matrix.of fun _ _ => 1
  | n + 1, f =>
    kronMat (kronPowerMat n (fun i => f i.castSucc)) (f (Fin.last n))

/-- Exact `n`-fold tensor power channel action `N^{⊗ n}(ρ)`. -/
def channelPowerApply {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    Matrix (Fin (d₂ ^ n)) (Fin (d₂ ^ n)) ℂ :=
  ∑ s : Fin n → Fin N.numKraus,
    let K := kronPowerMat n (fun i => N.kraus (s i))
    K * ρ * Kᴴ

/-- Exact `n`-fold complementary channel action `(N^{⊗ n})^c(ρ)`. -/
def channelPowerCompApply {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (d₁ ^ n)) (Fin (d₁ ^ n)) ℂ) :
    Matrix (Fin (N.numKraus ^ n)) (Fin (N.numKraus ^ n)) ℂ :=
  Matrix.of fun idx₁ idx₂ =>
    let mkIdx (idx : Fin (N.numKraus ^ n)) (i : Fin n) : Fin N.numKraus :=
      ⟨(idx.1 / N.numKraus ^ i.1) % N.numKraus, by
        by_cases h : N.numKraus = 0
        · have h0 : N.numKraus ^ n = 0 := by
            cases n with
            | zero => exact Fin.elim0 i
            | succ m => rw [h]; exact zero_pow (Nat.succ_ne_zero m)
          exact absurd (lt_of_lt_of_eq idx.2 h0) (Nat.not_lt_zero _)
        · exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩
    let K₁ := kronPowerMat n (fun i => N.kraus (mkIdx idx₁ i))
    let K₂ := kronPowerMat n (fun i => N.kraus (mkIdx idx₂ i))
    (K₁ * ρ * K₂ᴴ).trace

/-- Minimum output entropy `S_min(N) = inf_ρ S(N(ρ))`. -/
noncomputable def minOutputEntropy {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : ℝ :=
  sInf { r : ℝ | ∃ ρ : DensityMatrix d₁, r = matEntropy (N.applyMat ρ.mat) }

/-- Minimum output entropy of tensor product `N₁ ⊗ N₂`. -/
noncomputable def minOutputEntropyTensor {d₁ d₂ e₁ e₂ : ℕ}
    (N₁ : QuantumChannel d₁ d₂) (N₂ : QuantumChannel e₁ e₂) : ℝ :=
  sInf { r : ℝ | ∃ ρ : DensityMatrix (d₁ * e₁), r = matEntropy (tensorChannelApply N₁ N₂ ρ.mat) }

/-- Coherent information `I_c(ρ, N) = S(N(ρ)) - S(N^c(ρ))` for `n` uses of `N`. -/
noncomputable def coherentInfoN {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : DensityMatrix (d₁ ^ n)) : ℝ :=
  matEntropy (channelPowerApply N n ρ.mat) - matEntropy (channelPowerCompApply N n ρ.mat)

/-- `n`-letter maximized coherent information `(1/n) max_ρ I_c(ρ, N^{⊗ n})`. -/
noncomputable def coherentInfoRegN {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ) : ℝ :=
  sSup { r : ℝ | ∃ ρ : DensityMatrix (d₁ ^ n), r = coherentInfoN N n ρ / (n : ℝ) }

/-- Quantum capacity `Q(N) = sup_{n ≥ 1} (1/n) Q^{(1)}(N^{⊗ n})` (Lloyd-Shor-Devetak formula). -/
noncomputable def quantumCapacity {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : ℝ :=
  sSup { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = coherentInfoRegN N n }

/-- Holevo information `χ(N^{⊗ n})` for `n` uses of `N`. -/
noncomputable def holevoInfoN {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ) : ℝ :=
  sSup { r : ℝ | ∃ (m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
    let avgMat := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
    r = matEntropy avgMat - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat) }

/-- Classical capacity `C(N) = sup_{n ≥ 1} (1/n) χ(N^{⊗ n})` (HSW theorem). -/
noncomputable def classicalCapacity {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : ℝ :=
  sSup { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = holevoInfoN N n / (n : ℝ) }

/-- Private capacity `P(N)` via the regularized Devetak-Cai-Winter-Yeung formula. -/
noncomputable def privateCapacity {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : ℝ :=
  sSup { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
    0 < n ∧
    let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
    let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
    let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
    let chiE := matEntropy avgE - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
    r = (chiB - chiE) / (n : ℝ) }

/-- Qubit Pauli matrices `I, X, Y, Z`. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := 1
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Action of the qubit depolarizing channel `D_p(ρ) = (1-p) ρ + (p/3)(XρX + YρY + ZρZ)`. -/
noncomputable def depolarizingApply (p : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 - p : ℝ) : ℂ) • ρ +
  ((p / 3 : ℝ) : ℂ) • (pauliX * ρ * pauliX + pauliY * ρ * pauliY + pauliZ * ρ * pauliZ)

/-- Predicate stating that a quantum channel `N` realizes the qubit depolarizing channel `D_p`. -/
def IsDepolarizingChannel (p : ℝ) (N : QuantumChannel 2 2) : Prop :=
  ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, N.applyMat ρ = depolarizingApply p ρ

/-- Predicate stating that `N` realizes the qubit two-Pauli channel `ρ ↦ (1-p)ρ + (p/2)(XρX + ZρZ)`. -/
def IsTwoPauliChannel (p : ℝ) (N : QuantumChannel 2 2) : Prop :=
  ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
    N.applyMat ρ = ((1 - p : ℝ) : ℂ) • ρ + ((p / 2 : ℝ) : ℂ) • (pauliX * ρ * pauliX + pauliZ * ρ * pauliZ)

/-- Partial transpose on the second subsystem of a bipartite `d_A × d_B` state. -/
def partialTransposeB {dA dB : ℕ} (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ :=
  Matrix.of fun i j =>
    let hB : 0 < dB := Nat.pos_of_ne_zero (fun h => by subst h; exact Nat.not_lt_zero _ i.2)
    let iA := i.1 / dB
    let iB := i.1 % dB
    let jA := j.1 / dB
    let jB := j.1 % dB
    ρ ⟨iA * dB + jB, by
        have hiA : iA < dA := Nat.div_lt_of_lt_mul (by have := i.2; nlinarith)
        have hjB : jB < dB := Nat.mod_lt _ hB
        calc iA * dB + jB < iA * dB + dB := Nat.add_lt_add_left hjB _
          _ = (iA + 1) * dB := by ring
          _ ≤ dA * dB := Nat.mul_le_mul_right dB hiA⟩
      ⟨jA * dB + iB, by
        have hjA : jA < dA := Nat.div_lt_of_lt_mul (by have := j.2; nlinarith)
        have hiB : iB < dB := Nat.mod_lt _ hB
        calc jA * dB + iB < jA * dB + dB := Nat.add_lt_add_left hiB _
          _ = (jA + 1) * dB := by ring
          _ ≤ dA * dB := Nat.mul_le_mul_right dB hjA⟩

/-- A bipartite state is Positive Partial Transpose (PPT). -/
def IsPPT {dA dB : ℕ} (ρ : DensityMatrix (dA * dB)) : Prop :=
  (partialTransposeB ρ.mat).PosSemidef

/-- A bipartite state is separable (convex combination of product density matrices). -/
def IsSeparable {dA dB : ℕ} (ρ : DensityMatrix (dA * dB)) : Prop :=
  ∃ (m : ℕ) (P : ProbDist (Fin m)) (σA : Fin m → DensityMatrix dA) (σB : Fin m → DensityMatrix dB),
    ρ.mat = ∑ k : Fin m, (P.pmf k : ℂ) • kronMat (σA k).mat (σB k).mat

/-- Extract Alice's `n`-copy index in `Fin (dA ^ n)` from an interleaved `n`-copy bipartite
    basis index `idx : Fin ((dA * dB) ^ n)` matching `kronPowerMat n` ordering
    `(A₁ B₁)(A₂ B₂)…(Aₙ Bₙ)`. -/
def extractAliceCopyIdx (dA dB n : ℕ) (idx : ℕ) : ℕ :=
  ∑ i : Fin n,
    let copyVal := (idx / (dA * dB) ^ (n - 1 - i.1)) % (dA * dB)
    (copyVal / dB) * dA ^ (n - 1 - i.1)

/-- Extract Bob's `n`-copy index in `Fin (dB ^ n)` from an interleaved `n`-copy bipartite
    basis index `idx : Fin ((dA * dB) ^ n)` matching `kronPowerMat n` ordering. -/
def extractBobCopyIdx (dA dB n : ℕ) (idx : ℕ) : ℕ :=
  ∑ i : Fin n,
    let copyVal := (idx / (dA * dB) ^ (n - 1 - i.1)) % (dA * dB)
    (copyVal % dB) * dB ^ (n - 1 - i.1)

/-- `n`-copy 2-distillability of a bipartite state `ρ` (Horodecki criterion):
    there exists a Schmidt-rank-≤2 vector `ψ = u₁ ⊗ v₁ + u₂ ⊗ v₂` across the TRUE
    bipartition `(A₁ ⋯ Aₙ) | (B₁ ⋯ Bₙ)` such that `⟨ψ | (ρ^{⊗ n})^{T_B} | ψ⟩ < 0`.
    Note: `kronPowerMat n` orders basis elements as `(A₁ B₁)…(Aₙ Bₙ)`, so we de-interleave
    Alice's and Bob's indices via `extractAliceCopyIdx` / `extractBobCopyIdx`. -/
def IsNCopyDistillable {dA dB : ℕ} (n : ℕ) (ρ : DensityMatrix (dA * dB)) : Prop :=
  ∃ (u₁ u₂ : ℕ → ℂ) (v₁ v₂ : ℕ → ℂ),
    let ψ : Fin ((dA * dB) ^ n) → ℂ := fun idx =>
      let a := extractAliceCopyIdx dA dB n idx.1
      let b := extractBobCopyIdx dA dB n idx.1
      u₁ a * v₁ b + u₂ a * v₂ b
    let ρn : Matrix (Fin ((dA * dB) ^ n)) (Fin ((dA * dB) ^ n)) ℂ :=
      kronPowerMat n (fun _ => partialTransposeB ρ.mat)
    (∑ i, ∑ j, star (ψ i) * ρn i j * ψ j).re < 0

/-- A bipartite state is distillable if it is `n`-copy distillable for some `n ≥ 1`. -/
def IsDistillable {dA dB : ℕ} (ρ : DensityMatrix (dA * dB)) : Prop :=
  ∃ n : ℕ, 0 < n ∧ IsNCopyDistillable n ρ

/-- Symmetric Informationally Complete POVM (SIC-POVM) in dimension `d`:
    `d²` unit vectors `|ψ_k⟩ ∈ ℂ^d` with `|⟨ψ_j | ψ_k⟩|² = 1/(d+1)` for all `j ≠ k`. -/
def IsSICPOVM (d : ℕ) (ψ : Fin (d * d) → Fin d → ℂ) : Prop :=
  (∀ j : Fin (d * d), ∑ r : Fin d, ‖ψ j r‖ ^ 2 = 1) ∧
  (∀ j k : Fin (d * d), j ≠ k →
    ‖∑ r : Fin d, star (ψ j r) * ψ k r‖ ^ 2 = (1 : ℝ) / ((d : ℝ) + 1))

/-- Partial trace over the second subsystem of a bipartite `dA × dB` matrix. -/
def partialTraceB {dA dB : ℕ} (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    Matrix (Fin dA) (Fin dA) ℂ :=
  Matrix.of fun a₁ a₂ =>
    ∑ b : Fin dB,
      ρ ⟨a₁.1 * dB + b.1, by
          calc a₁.1 * dB + b.1 < a₁.1 * dB + dB := Nat.add_lt_add_left b.2 _
            _ = (a₁.1 + 1) * dB := by ring
            _ ≤ dA * dB := Nat.mul_le_mul_right dB a₁.2⟩
        ⟨a₂.1 * dB + b.1, by
          calc a₂.1 * dB + b.1 < a₂.1 * dB + dB := Nat.add_lt_add_left b.2 _
            _ = (a₂.1 + 1) * dB := by ring
            _ ≤ dA * dB := Nat.mul_le_mul_right dB a₂.2⟩

/-- Partial trace over the first subsystem of a bipartite `dA × dB` matrix. -/
def partialTraceA {dA dB : ℕ} (ρ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    Matrix (Fin dB) (Fin dB) ℂ :=
  Matrix.of fun b₁ b₂ =>
    ∑ a : Fin dA,
      ρ ⟨a.1 * dB + b₁.1, by
          calc a.1 * dB + b₁.1 < a.1 * dB + dB := Nat.add_lt_add_left b₁.2 _
            _ = (a.1 + 1) * dB := by ring
            _ ≤ dA * dB := Nat.mul_le_mul_right dB a.2⟩
        ⟨a.1 * dB + b₂.1, by
          calc a.1 * dB + b₂.1 < a.1 * dB + dB := Nat.add_lt_add_left b₂.2 _
            _ = (a.1 + 1) * dB := by ring
            _ ≤ dA * dB := Nat.mul_le_mul_right dB a.2⟩

/-- Squashed entanglement `E_sq(ρ_AB) = ½ inf_{ρ_ABE} I(A; B | E)`. -/
noncomputable def squashedEntanglement {dA dB : ℕ} (ρ : DensityMatrix (dA * dB)) : ℝ :=
  (1 / 2 : ℝ) * sInf { r : ℝ | ∃ (dE : ℕ) (σ : DensityMatrix (dA * dB * dE)),
    partialTraceB σ.mat = ρ.mat ∧
    let σAE := partialTraceA (Matrix.of fun (i : Fin (dB * (dA * dE))) (j : Fin (dB * (dA * dE))) =>
      let b₁ := i.1 / (dA * dE); let ae₁ := i.1 % (dA * dE); let a₁ := ae₁ / dE; let e₁ := ae₁ % dE
      let b₂ := j.1 / (dA * dE); let ae₂ := j.1 % (dA * dE); let a₂ := ae₂ / dE; let e₂ := ae₂ % dE
      let idx₁ := (a₁ * dB + b₁) * dE + e₁
      let idx₂ := (a₂ * dB + b₂) * dE + e₂
      if h₁ : idx₁ < dA * dB * dE then
        if h₂ : idx₂ < dA * dB * dE then σ.mat ⟨idx₁, h₁⟩ ⟨idx₂, h₂⟩ else 0
      else 0)
    let σBE := partialTraceA (Matrix.of fun (i : Fin (dA * (dB * dE))) (j : Fin (dA * (dB * dE))) =>
      let h₁ : i.1 < dA * dB * dE := by simpa [mul_assoc] using i.2
      let h₂ : j.1 < dA * dB * dE := by simpa [mul_assoc] using j.2
      σ.mat ⟨i.1, h₁⟩ ⟨j.1, h₂⟩)
    let σE := partialTraceA σ.mat
    r = matEntropy σAE + matEntropy σBE - vonNeumannEntropy σ - matEntropy σE }

/-- Trace distance `½ ‖ρ - σ‖₁` via eigenvalues of the Hermitian difference `ρ - σ`. -/
noncomputable def traceDistance {d : ℕ} (ρ σ : DensityMatrix d) : ℝ := by
  classical
  exact (1 / 2 : ℝ) *
    if h : (ρ.mat - σ.mat).IsHermitian then ∑ i : Fin d, |h.eigenvalues i| else 0

end InfoTheory
