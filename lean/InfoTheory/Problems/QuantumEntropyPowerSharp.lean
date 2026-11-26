import InfoTheory.Core

open scoped BigOperators Matrix

namespace InfoTheory.Problems.QuantumEntropyPowerSharp

/-- Elementary factorial on `ℕ`. -/
def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Elementary binomial coefficient on `ℕ`. -/
def binom : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Exact single-mode bosonic beam-splitter Fock matrix element `⟨k, l | U_λ | m, n⟩`
    for transmissivity `lam ∈ (0, 1)`. -/
noncomputable def beamSplitterEntry (lam : ℝ) (k l m n : ℕ) : ℝ :=
  if k + l = m + n then
    Real.sqrt (((fact k * fact l : ℕ) : ℝ) / ((fact m * fact n : ℕ) : ℝ)) *
      ∑ r : Fin (m + 1),
        if r.1 ≤ k ∧ k - r.1 ≤ n then
          ((binom m r.1 * binom n (k - r.1) : ℕ) : ℝ) *
          ((-1 : ℝ) ^ (k - r.1)) *
          (Real.sqrt lam) ^ (r.1 + (n - (k - r.1))) *
          (Real.sqrt (1 - lam)) ^ ((m - r.1) + (k - r.1))
        else 0
  else 0

/-- Exact beam-splitter isometry `U_λ : ℂ^{M × M} → ℂ^{(2M) × (2M)}` on Fock states
    with photon number `< M` in each input mode. -/
noncomputable def beamSplitterIso (M : ℕ) (lam : ℝ) :
    Matrix (Fin (2 * M * (2 * M))) (Fin (M * M)) ℂ :=
  Matrix.of fun q p =>
    ((beamSplitterEntry lam (q.1 / (2 * M)) (q.1 % (2 * M)) (p.1 / M) (p.1 % M) : ℝ) : ℂ)

/-- Bosonic thermal entropy function `g(x) = (x + 1) log₂(x + 1) - x log₂ x` for `x ≥ 0`. -/
noncomputable def bosonicG (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else (x + 1) * log2 (x + 1) - x * log2 x

/-- Entropy photon number `N(S) = g⁻¹(S)` for von Neumann entropy `S ≥ 0`. -/
noncomputable def entropyPhotonNumber (S : ℝ) : ℝ :=
  sSup { x : ℝ | 0 ≤ x ∧ bosonicG x ≤ S }

/-- Guha–Erkmen–Shapiro Entropy Photon-Number Inequality (EPnI, 2008; De Palma–Mari–Giovannetti 2014):
    strictly stronger than the proved bosonic quantum EPI (König–Smith 2014; De Palma–Trevisan 2018),
    for any two independent single-mode bosonic states `ρ_A, ρ_B` (with Fock cutoff `M ≥ 1`)
    mixed through a beam splitter of transmissivity `λ ∈ (0, 1)` yielding output `σ_C = Tr_D(U_λ (ρ_A ⊗ ρ_B) U_λ†)`,
    `N(S(σ_C)) ≥ λ · N(S(ρ_A)) + (1 - λ) · N(S(ρ_B))`. -/
def Statement : Prop :=
  ∀ (M : ℕ) (lam : ℝ) (ρA ρB : DensityMatrix M),
    0 < M → 0 < lam → lam < 1 →
    let U := beamSplitterIso M lam
    let σCD := U * kronMat ρA.mat ρB.mat * Uᴴ
    let σC := @partialTraceB (2 * M) (2 * M) σCD
    lam * entropyPhotonNumber (vonNeumannEntropy ρA) +
      (1 - lam) * entropyPhotonNumber (vonNeumannEntropy ρB) ≤
      entropyPhotonNumber (matEntropy σC)

def problem : OpenProblem where
  id := "quantum-entropy-power-sharp"
  title := "The Bosonic Entropy Photon-Number Inequality (EPnI)"
  category := .quantumInfo
  status := .open
  posedBy := "Saikat Guha, Jeffrey H. Shapiro, and Baris I. Erkmen"
  posedYear := 2008
  statement := Statement

end InfoTheory.Problems.QuantumEntropyPowerSharp
