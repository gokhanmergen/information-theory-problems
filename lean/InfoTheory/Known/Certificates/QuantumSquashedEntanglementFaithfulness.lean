import InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness
import InfoTheory.Known.Certificates.ConditionalEntropySharpContinuity

/-!
# Certificate for `InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness`

The frozen statement asks for a universal `c > 0` with
`E_sq(ρ) ≥ (c / min(d_A, d_B)) · dist₁(ρ, SEP)²` for all bipartite states (the conjectured
optimal exponent `α = 1`; `α = 2` is known, `α < 1` is ruled out by the antisymmetric state).
It does **not** ask for qualitative faithfulness (`E_sq = 0 ⇒ separable`), which is the
Brandão–Christandl–Yard (2011) theorem.

## Certified
* `kron_isSeparable`: product states `σ_A ⊗ σ_B` (`kronMat`) satisfy `IsSeparable`, so the
  separable witness set is nonempty; `traceDistance_self`, `traceDistance_nonneg`
  (re-exported from the `ConditionalEntropySharpContinuity` certificate).
* `matEntropy_cast`: entropy is invariant under `Fin.cast` relabellings.
* `cmi_dim_one`: for `d_A = d_B = 1` and any extension `σ_{ABE}` (any `d_E`), the three
  marginals `σ_{AE}`, `σ_{BE}`, `σ_E` built by the index juggling inside
  `squashedEntanglement` are exactly relabellings of `σ_{ABE}`, so `I(A;B|E) = 0`.
* **Regression:** `squashedEntanglement_dim_one : E_sq(ρ) = 0` on `ℂ¹ ⊗ ℂ¹` (no `sInf`
  junk; the infimum is over a set of zeros).

## Not certified
* `E_sq ≥ 0` in general (needs strong subadditivity, not in `Known`/`Bridge`), the BCY
  lower bound, and the antisymmetric-state upper bound `E_sq(α_d) = O(1/d)`.

## Adversarial check (2026-11-27)
Index conventions checked by hand: `σ_{AE}` reindexes `(b, a, e) ↦ (a·d_B + b)·d_E + e` and
traces out `B`; `σ_{BE}` reads `σ` on `A × (B × E)` and traces out `A`; `σ_E` traces out
`AB`; `d_E = 0` is impossible (no trace-one `0 × 0` matrix). The `σ` in the Statement is an
existential separable witness, equivalent to `dist₁(ρ, SEP)` up to the attained infimum
(SEP is compact). BCY settled faithfulness, not the exponent; Li–Winter (2014, 2018) improve
constants and give `α = 2` in trace norm. No result closing `α ∈ [1, 2]` found through 2026.
Statement FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.QuantumSquashedEntanglementFaithfulness

open InfoTheory Matrix

/-! ### Separable states and trace distance -/

/-- Product states are separable. -/
theorem kron_isSeparable {dA dB : ℕ} (σA : DensityMatrix dA) (σB : DensityMatrix dB)
    (ρ : DensityMatrix (dA * dB)) (h : ρ.mat = kronMat σA.mat σB.mat) :
    @IsSeparable dA dB ρ := by
  refine ⟨1, ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩, fun _ => σA, fun _ => σB, ?_⟩
  simp [h]

theorem traceDistance_self {d : ℕ} (ρ : DensityMatrix d) : traceDistance ρ ρ = 0 :=
  ConditionalEntropySharpContinuity.traceDistance_self ρ

theorem traceDistance_nonneg {d : ℕ} (ρ σ : DensityMatrix d) : 0 ≤ traceDistance ρ σ :=
  ConditionalEntropySharpContinuity.traceDistance_nonneg ρ σ

/-! ### Squashed entanglement of a trivial `1 × 1` system -/

/-- Entropy is invariant under a `Fin.cast` relabelling. -/
theorem matEntropy_cast {n m : ℕ} (h : n = m) (M : Matrix (Fin m) (Fin m) ℂ) :
    matEntropy (M.submatrix (Fin.cast h) (Fin.cast h)) = matEntropy M := by
  subst h; rfl

private lemma one_mul_dE (dE : ℕ) : 1 * dE = 1 * 1 * dE := by simp

private lemma dE_eq (dE : ℕ) : dE = 1 * 1 * dE := by simp

/-- For `dA = dB = 1` every extension has `I(A;B|E) = 0`: all of `σ_{AE}`, `σ_{BE}`, `σ_E`
    are relabellings of `σ_{ABE}`. -/
theorem cmi_dim_one (dE : ℕ) (σ : DensityMatrix (1 * 1 * dE)) :
    let σAE := partialTraceA (Matrix.of fun (i : Fin (1 * (1 * dE))) (j : Fin (1 * (1 * dE))) =>
      let b₁ := i.1 / (1 * dE); let ae₁ := i.1 % (1 * dE); let a₁ := ae₁ / dE; let e₁ := ae₁ % dE
      let b₂ := j.1 / (1 * dE); let ae₂ := j.1 % (1 * dE); let a₂ := ae₂ / dE; let e₂ := ae₂ % dE
      let idx₁ := (a₁ * 1 + b₁) * dE + e₁
      let idx₂ := (a₂ * 1 + b₂) * dE + e₂
      if h₁ : idx₁ < 1 * 1 * dE then
        if h₂ : idx₂ < 1 * 1 * dE then σ.mat ⟨idx₁, h₁⟩ ⟨idx₂, h₂⟩ else 0
      else 0)
    let σBE := partialTraceA (Matrix.of fun (i : Fin (1 * (1 * dE))) (j : Fin (1 * (1 * dE))) =>
      let h₁ : i.1 < 1 * 1 * dE := by simpa [mul_assoc] using i.2
      let h₂ : j.1 < 1 * 1 * dE := by simpa [mul_assoc] using j.2
      σ.mat ⟨i.1, h₁⟩ ⟨j.1, h₂⟩)
    let σE := @partialTraceA (1 * 1) dE σ.mat
    matEntropy σAE + matEntropy σBE - vonNeumannEntropy σ - matEntropy σE = 0 := by
  intro σAE σBE σE
  have hAE : σAE = σ.mat.submatrix (Fin.cast (one_mul_dE dE)) (Fin.cast (one_mul_dE dE)) := by
    ext i j
    have hi : i.1 < dE := by simpa using i.2
    have hj : j.1 < dE := by simpa using j.2
    simp [σAE, partialTraceA, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hj,
      Nat.mod_eq_of_lt hj, hi, hj]
  have hBE : σBE = σ.mat.submatrix (Fin.cast (one_mul_dE dE)) (Fin.cast (one_mul_dE dE)) := by
    ext i j
    simp [σBE, partialTraceA]
  have hE : σE = σ.mat.submatrix (Fin.cast (dE_eq dE)) (Fin.cast (dE_eq dE)) := by
    ext i j
    simp [σE, partialTraceA]
    rfl
  rw [hAE, hBE, hE, matEntropy_cast, matEntropy_cast,
    ConditionalEntropySharpContinuity.vonNeumannEntropy_eq_matEntropy]
  ring

/-- **Regression:** `E_sq = 0` on the trivial `1 × 1` system (every extension has
    `I(A;B|E) = 0`, so the infimum is `0`; no `sInf`-junk). -/
theorem squashedEntanglement_dim_one (ρ : DensityMatrix (1 * 1)) :
    @squashedEntanglement 1 1 ρ = 0 := by
  unfold squashedEntanglement
  rw [mul_eq_zero]; right
  apply le_antisymm
  · apply Real.sInf_nonpos
    rintro r ⟨dE, σ, -, hr⟩
    dsimp only at hr
    rw [hr]; exact (cmi_dim_one dE σ).le
  · apply Real.sInf_nonneg
    rintro r ⟨dE, σ, -, hr⟩
    dsimp only at hr
    rw [hr]; exact (cmi_dim_one dE σ).ge

end InfoTheory.Known.Certificates.QuantumSquashedEntanglementFaithfulness
