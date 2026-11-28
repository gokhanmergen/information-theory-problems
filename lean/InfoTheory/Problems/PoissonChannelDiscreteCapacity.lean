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

/-- Sublinear Support-Size Problem for the Amplitude-Constrained Discrete-Time Poisson Channel
    (Shamai 1990; Dytso–Barletta–Shamai 2021; Barletta–Dytso–Shamai 2024).

    **Statement-fix (2026-11-27).** The previous frozen statement asserted a sharp `O(√A)`
    support-size bound, uniformly over an extra average-power budget `μ ∈ (0, A]`. That
    conjecture does not appear in the literature and is contradicted by the published
    numerics: Barletta–Dytso–Shamai (arXiv:2401.05045, 2024) fit `N(A) ≈ A^{0.71}` at
    `λ₀ = 0` and state that "neither the upper nor lower bounds are tight". What is proved is
    `Ω(√A) ≤ N(A)` (Dytso–Barletta–Shamai, IEEE Trans. IT 2021, via `C ≈ ½ log A`) and
    `N(A) = O(A)` (Barletta–Dytso–Shamai 2024 for `λ₀ = 0`; linear-in-`A` bound for fixed
    `λ₀ > 0`); the open question they pose is the exact order of `N(A)`. The statement now
    asks the first genuinely open step: is the optimal support size polynomially sublinear,
    `N(A) = O(A^{1-δ})` for some `δ > 0`, under the **amplitude constraint only** (encoded
    as `dtpcCapacity lam₀ A A`, where the mean constraint `E[X] ≤ A` is automatic)?

    For every dark current `λ₀ ≥ 0` there exist `δ > 0` and `K > 0` such that for every peak
    amplitude `A ≥ 1`, the amplitude-constrained capacity `C_DTPC(λ₀, A, A)` is achieved by a
    discrete input distribution on `[0, A]` with at most `K · A^{1-δ}` mass points. (The
    capacity-achieving input is unique — Shamai 1990 — so this bounds its support size.) -/
def Statement : Prop :=
  ∀ (lam₀ : ℝ), 0 ≤ lam₀ →
    ∃ (δ K : ℝ), 0 < δ ∧ 0 < K ∧
      ∀ (A : ℝ), 1 ≤ A →
        ∃ (k : ℕ) (pts : Fin k → ℝ) (w : ProbDist (Fin k)),
          (k : ℝ) ≤ K * A ^ (1 - δ) ∧
          (∀ i : Fin k, 0 ≤ pts i ∧ pts i ≤ A) ∧
          dtpcDiscreteMI lam₀ k pts w = dtpcCapacity lam₀ A A

def problem : OpenProblem where
  id := "poisson-channel-discrete-capacity"
  title := "Optimal Support Size and Capacity of the Discrete-Time Poisson Channel"
  category := .channelCapacity
  status := .open
  posedBy := "Shlomo Shamai (Shitz); Amos Lapidoth and Stefan M. Moser; Mahdi Cheraghchi and João Ribeiro"
  posedYear := 1990
  statement := Statement

end InfoTheory.Problems.PoissonChannelDiscreteCapacity
