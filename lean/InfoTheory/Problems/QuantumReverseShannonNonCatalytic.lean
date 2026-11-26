import InfoTheory.Core

open scoped BigOperators Matrix

namespace InfoTheory.Problems.QuantumReverseShannonNonCatalytic

/-- Action of `id_{dR} ⊗ N` on a bipartite matrix on `Fin (dR * d₁)`. -/
def idTensorChannelApply (dR : ℕ) {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂)
    (ρ : Matrix (Fin (dR * d₁)) (Fin (dR * d₁)) ℂ) :
    Matrix (Fin (dR * d₂)) (Fin (dR * d₂)) ℂ :=
  ∑ a : Fin N.numKraus,
    let K := kronMat (1 : Matrix (Fin dR) (Fin dR) ℂ) (N.kraus a)
    K * ρ * Kᴴ

/-- Action of `id_{dR} ⊗ N^{⊗ n}` on a bipartite matrix on `Fin (dR * d₁^n)`. -/
def idTensorPowerApply (dR : ℕ) {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n : ℕ)
    (ρ : Matrix (Fin (dR * d₁ ^ n)) (Fin (dR * d₁ ^ n)) ℂ) :
    Matrix (Fin (dR * d₂ ^ n)) (Fin (dR * d₂ ^ n)) ℂ :=
  ∑ s : Fin n → Fin N.numKraus,
    let K := kronMat (1 : Matrix (Fin dR) (Fin dR) ℂ) (kronPowerMat n (fun i => N.kraus (s i)))
    K * ρ * Kᴴ

/-- Entanglement of formation `E_F(σ_{AB})` of a bipartite state `σ` on `dA × dB`:
    minimum average entanglement entropy `∑ p_i S(Tr_B |ψ_i⟩⟨ψ_i|)` over pure-state
    decompositions of `σ`. -/
noncomputable def entanglementOfFormation {dA dB : ℕ}
    (σ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) : ℝ :=
  sInf { r : ℝ | ∃ (m : ℕ) (P : ProbDist (Fin m)) (ψ : Fin m → Fin (dA * dB) → ℂ),
    (∀ k, ∑ i, ‖ψ k i‖ ^ 2 = 1) ∧
    (σ = ∑ k : Fin m, (P.pmf k : ℂ) • Matrix.of (fun i j => ψ k i * star (ψ k j))) ∧
    r = ∑ k : Fin m, P.pmf k *
      matEntropy (@partialTraceB dA dB (Matrix.of (fun i j => ψ k i * star (ψ k j)))) }

/-- Single-letter channel entanglement of formation `E_F(N) = sup_{ρ_{RA}} E_F((id ⊗ N)(ρ))`
    (Berta–Brandão–Christandl–Wehner 2013). -/
noncomputable def channelEF {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : ℝ :=
  sSup { r : ℝ | ∃ (ρ : DensityMatrix (d₁ * d₁)),
    r = entanglementOfFormation (idTensorChannelApply d₁ N ρ.mat) }

/-- Regularized entanglement cost `E_C(N) = inf_{n ≥ 1} (1/n) E_F(N^{⊗ n})` of simulating
    a quantum channel `N` with free classical communication (Berta–Brandão–Christandl–Wehner 2013). -/
noncomputable def channelEntanglementCost {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : ℝ :=
  sInf { r : ℝ | ∃ (n : ℕ), 0 < n ∧
    r = (sSup { e : ℝ | ∃ (ρ : DensityMatrix (d₁ ^ n * d₁ ^ n)),
      e = entanglementOfFormation (idTensorPowerApply (d₁ ^ n) N n ρ.mat) }) / (n : ℝ) }

/-- Single-Letterization of Qubit Quantum Channel Entanglement Cost
    (Berta–Brandão–Christandl–Wehner 2013):
    While Bennett et al. (2014) showed that non-catalytic ebit-only simulation fails for
    general correlated sources at rate `C_E(N)` and Hastings' additivity violation implies
    regularization is needed in high dimension, it remains open whether the entanglement cost
    `E_C(N)` of every *qubit* quantum channel (`d₁ = d₂ = 2`) single-letterizes to `E_F(N)`. -/
def Statement : Prop :=
  ∀ (N : QuantumChannel 2 2),
    channelEntanglementCost N = channelEF N

def problem : OpenProblem where
  id := "quantum-reverse-shannon-non-catalytic"
  title := "Single-Letterization of Quantum Channel Entanglement Cost and Channel Simulation"
  category := .quantumInfo
  status := .open
  posedBy := "Mario Berta, Fernando G. S. L. Brandão, Matthias Christandl, and Stephanie Wehner"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.QuantumReverseShannonNonCatalytic
