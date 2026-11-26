import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.PoissonChannelDiscreteCapacity

/-- Elementary factorial helper `n!` (self-contained). -/
def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Poisson transition PMF `W_{λ₀}(y | x) = e^{-(x + λ₀)} (x + λ₀)^y / y!` for `y : ℕ`. -/
noncomputable def poissonTrans (lam₀ x : ℝ) (y : ℕ) : ℝ :=
  Real.exp (-(x + lam₀)) * (x + lam₀) ^ y / (fact y : ℝ)

/-- Mutual information `I(X; Y)` (in bits) across the discrete-time Poisson channel with
    dark current `λ₀` for a `k`-point discrete input distribution with support points
    `pts : Fin k → ℝ` and probabilities `w : ProbDist (Fin k)`. -/
noncomputable def dtpcDiscreteMI (lam₀ : ℝ) (k : ℕ) (pts : Fin k → ℝ) (w : ProbDist (Fin k)) : ℝ :=
  let py (y : ℕ) : ℝ := ∑ i : Fin k, w.pmf i * poissonTrans lam₀ (pts i) y
  let hY : ℝ := ∑' y : ℕ, negPLogP (py y)
  let hYgivenX : ℝ := ∑ i : Fin k, w.pmf i *
    ∑' y : ℕ, negPLogP (poissonTrans lam₀ (pts i) y)
  hY - hYgivenX

/-- Capacity `C_DTPC(λ₀, A, μ)` of the peak- and average-power-constrained discrete-time
    Poisson channel over all finitely supported distributions on `[0, A]` with mean `≤ μ`
    (equals the full capacity over all Borel distributions on `[0, A]` by Shamai 1990). -/
noncomputable def dtpcCapacity (lam₀ A mu : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ (k : ℕ) (pts : Fin k → ℝ) (w : ProbDist (Fin k)),
    (∀ i : Fin k, 0 ≤ pts i ∧ pts i ≤ A) ∧
    (∑ i : Fin k, w.pmf i * pts i) ≤ mu ∧
    r = dtpcDiscreteMI lam₀ k pts w }

/-- Sharp `O(√A)` Support-Size Conjecture for the Discrete-Time Poisson Channel
    (Shamai 1990; Lapidoth–Moser 2009; Dytso–Fauß–Poor 2019; Cheraghchi–Ribeiro 2019):
    for every dark current `λ₀ ≥ 0`, there exists `K > 0` such that for all peak amplitudes
    `A ≥ 1` and all average-power budgets `μ ∈ (0, A]`, the capacity `C_DTPC(λ₀, A, μ)` is
    achieved by a discrete input distribution on `[0, A]` with at most `⌈K √A⌉` mass points. -/
def Statement : Prop :=
  ∀ (lam₀ : ℝ), 0 ≤ lam₀ →
    ∃ (K : ℝ), 0 < K ∧
      ∀ (A mu : ℝ), 1 ≤ A → 0 < mu → mu ≤ A →
        ∃ (k : ℕ) (pts : Fin k → ℝ) (w : ProbDist (Fin k)),
          (k : ℝ) ≤ K * Real.sqrt A + 1 ∧
          (∀ i : Fin k, 0 ≤ pts i ∧ pts i ≤ A) ∧
          (∑ i : Fin k, w.pmf i * pts i) ≤ mu ∧
          dtpcDiscreteMI lam₀ k pts w = dtpcCapacity lam₀ A mu

def problem : OpenProblem where
  id := "poisson-channel-discrete-capacity"
  title := "Optimal Support Size and Capacity of the Discrete-Time Poisson Channel"
  category := .channelCapacity
  status := .open
  posedBy := "Shlomo Shamai (Shitz); Amos Lapidoth and Stefan M. Moser; Mahdi Cheraghchi and João Ribeiro"
  posedYear := 1990
  statement := Statement

end InfoTheory.Problems.PoissonChannelDiscreteCapacity
