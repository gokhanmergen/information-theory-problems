import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.PolarCodeScalingExponent

/-- Base-`ℓ` lexicographic bijection `Fin (ℓ^m) → (Fin m → Fin ℓ)` for `ℓ > 0`. -/
def polarIdx (ℓ m : ℕ) (hℓ : 0 < ℓ) (t : Fin (ℓ ^ m)) : Fin m → Fin ℓ :=
  fun s => ⟨(t.1 / ℓ ^ (m - 1 - s.1)) % ℓ, Nat.mod_lt _ hℓ⟩

/-- Encoding `x = u · G^{⊗ m}` of a message vector `u : (Fin m → Fin ℓ) → ZMod 2` under
    the `m`-fold Kronecker power of an `ℓ × ℓ` binary kernel `G`. -/
def polarEncode (ℓ m : ℕ) (G : Fin ℓ → Fin ℓ → ZMod 2)
    (u : (Fin m → Fin ℓ) → ZMod 2) : (Fin m → Fin ℓ) → ZMod 2 :=
  fun j => ∑ i : Fin m → Fin ℓ, u i * ∏ s : Fin m, G (i s) (j s)

/-- Invertibility of an `ℓ × ℓ` binary matrix `G` over `𝔽₂`. -/
def IsInvertibleKernel (ℓ : ℕ) (G : Fin ℓ → Fin ℓ → ZMod 2) : Prop :=
  ∃ Ginv : Fin ℓ → Fin ℓ → ZMod 2,
    ∀ i j : Fin ℓ, (∑ k : Fin ℓ, G i k * Ginv k j) = if i = j then 1 else 0

/-- Exact successive cancellation (SC) block error probability of a binary polar code
    with kernel `G`, depth `m`, information set `A`, and causal SC decision functions `dec`,
    communicating over `BSC(p)` (via the exact genie-aided coupling identity). -/
noncomputable def polarSCBlockError (ℓ m : ℕ) (hℓ : 0 < ℓ)
    (G : Fin ℓ → Fin ℓ → ZMod 2)
    (A : Finset (Fin m → Fin ℓ))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (dec : ∀ t : Fin (ℓ ^ m), ((Fin m → Fin ℓ) → Bool) → (Fin t.1 → ZMod 2) → ZMod 2) : ℝ :=
  let validU : Finset ((Fin m → Fin ℓ) → ZMod 2) :=
    Finset.univ.filter (fun u => ∀ i : Fin m → Fin ℓ, i ∉ A → u i = 0)
  ((1 : ℝ) / ((2 ^ A.card : ℕ) : ℝ)) *
    ∑ u ∈ validU,
      ∑ y : (Fin m → Fin ℓ) → Bool,
        if ∃ t : Fin (ℓ ^ m),
            polarIdx ℓ m hℓ t ∈ A ∧
            dec t y (fun s : Fin t.1 => u (polarIdx ℓ m hℓ ⟨s.1, Nat.lt_trans s.2 t.2⟩)) ≠
              u (polarIdx ℓ m hℓ t)
        then
          ∏ j : Fin m → Fin ℓ,
            (bsc p hp0 hp1).trans (decide (polarEncode ℓ m G u j = 1)) (y j)
        else 0

/-- Open problem: On `BSC(p)` for any `p ∈ (0, 1/2)`, can binary polar codes with a single
    fixed finite invertible binary kernel `G ∈ GL_ℓ(𝔽₂)` achieve SC scaling exponent
    arbitrarily close to the optimal value `μ = 2`? -/
def Statement : Prop :=
  ∀ (p ε η : ℝ), (hp0 : 0 < p) → (hp1 : p < 1 / 2) → 0 < ε → 0 < η → η < 1 →
    ∃ (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (G : Fin ℓ → Fin ℓ → ZMod 2) (c : ℝ) (m₀ : ℕ),
      IsInvertibleKernel ℓ G ∧ 0 < c ∧
      ∀ m : ℕ, m₀ ≤ m →
        ∃ (A : Finset (Fin m → Fin ℓ))
          (dec : ∀ t : Fin (ℓ ^ m), ((Fin m → Fin ℓ) → Bool) → (Fin t.1 → ZMod 2) → ZMod 2),
          (1 - binaryEntropy p) - c * ((ℓ ^ m : ℕ) : ℝ) ^ (-(1 : ℝ) / (2 + ε)) ≤
            (A.card : ℝ) / ((ℓ ^ m : ℕ) : ℝ) ∧
          polarSCBlockError ℓ m (by omega : 0 < ℓ) G A p (le_of_lt hp0) (by linarith) dec ≤ η

def problem : OpenProblem where
  id := "polar-code-scaling-exponent"
  title := "Optimal Scaling Exponent of Binary Polar Codes with Finite Kernels on the BSC"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "Erdal Arıkan; S. Hamed Hassani, Kasra Alishahi, and Rüdiger L. Urbanke"
  posedYear := 2014
  statement := Statement

end InfoTheory.Problems.PolarCodeScalingExponent
