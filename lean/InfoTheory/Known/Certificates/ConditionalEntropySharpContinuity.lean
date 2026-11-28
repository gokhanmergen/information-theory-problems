import InfoTheory.Problems.ConditionalEntropySharpContinuity
import InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold

/-!
# Certificate for `InfoTheory.Problems.ConditionalEntropySharpContinuity`

The frozen statement is the sharp continuity bound for quantum conditional entropy:
for `d_A ≥ 2`, `d_B ≥ 1` and states `ρ, σ` on `ℂ^{d_A} ⊗ ℂ^{d_B}` with
`ε = traceDistance ρ σ ≤ 1 - 1/d_A²`,
`|S(A|B)_ρ - S(A|B)_σ| ≤ ε log₂(d_A² - 1) + h(ε)`, where
`S(A|B)_ρ = vonNeumannEntropy ρ - matEntropy (partialTraceA ρ.mat)`.
The catalog marks it `formal_status: claimed-resolved` (Berta–Costa Rico–Kossmann–Lami–Zeiss,
arXiv:2607.24687). This file does **not** prove it. It checks that the objects in
`Statement` are not junk.

Certified here:
* `traceDistance_nonneg`, `traceDistance_self`: `ε ≥ 0`, and `ε(ρ, ρ) = 0` (the `dif` on
  Hermitian-ness is always taken: `ρ - σ` is Hermitian);
* `vonNeumannEntropy_eq_matEntropy`: the two entropy functionals in `Statement` agree on
  states; `vonNeumannEntropy_nonneg`;
* `binaryEntropy_zero`, `bound_zero`: the right-hand side vanishes at `ε = 0`;
  `statement_instance_self`: the inequality holds for `ρ = σ` (a sanity instance, not a
  proof of `Statement`);
* `bound_nonneg`: the right-hand side is `≥ 0` for `ε ∈ [0, 1]`;
* `threshold_pos`, `threshold_lt_one`: the admissible range `0 < 1 - 1/d_A² < 1` is a
  nontrivial interval for `d_A ≥ 2`;
* `bound_at_threshold`: at the threshold `ε = 1 - 1/d_A²` the bound equals `2 log₂ d_A`, the
  trivial maximal spread of `S(A|B) ∈ [-log₂ d_A, log₂ d_A]`, as the textbook bound does
  (Alhejji–Smith 2020; Berta et al. 2026). This checks that `binaryEntropy`, `log2` and the
  `ℕ`-subtraction cast `((d_A·d_A - 1 : ℕ) : ℝ)` have their intended values;
* `matEntropy_partialTraceA_dB_one`, `condEntropy_dB_one`: for `d_B = 1` the reduced state
  `partialTraceA ρ` is the `1 × 1` identity, so `S(A|B)_ρ = S(ρ)` (`partialTraceA` sums the
  diagonal blocks correctly); `condEntropy_pure_dB_one`: pure states then have
  `S(A|B) = 0`.

Not certified: `traceDistance ≤ 1` and the general range `-log₂ d_A ≤ S(A|B) ≤ log₂ d_A`
(these need operator-norm and subadditivity facts not yet in `Known`/`Bridge`); the
attaining pair (maximally entangled state versus its isotropic depolarisation).
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.ConditionalEntropySharpContinuity

open InfoTheory InfoTheory.Problems.ConditionalEntropySharpContinuity Matrix
open InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold

/-! ### Trace distance -/

/-- `traceDistance ρ σ ≥ 0`. -/
theorem traceDistance_nonneg {d : ℕ} (ρ σ : DensityMatrix d) : 0 ≤ traceDistance ρ σ := by
  unfold traceDistance
  refine mul_nonneg (by norm_num) ?_
  split_ifs with h
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · exact le_rfl

/-- The difference of two states is Hermitian, so the `dif` in `traceDistance` is never junk. -/
theorem sub_isHermitian {d : ℕ} (ρ σ : DensityMatrix d) : (ρ.mat - σ.mat).IsHermitian :=
  ρ.posSemidef.isHermitian.sub σ.posSemidef.isHermitian

/-- `traceDistance ρ ρ = 0`. -/
theorem traceDistance_self {d : ℕ} (ρ : DensityMatrix d) : traceDistance ρ ρ = 0 := by
  unfold traceDistance
  split_ifs with h
  · have h0 : h.eigenvalues = 0 := h.eigenvalues_eq_zero_iff.2 (sub_self _)
    rw [h0]; simp
  · exact absurd (sub_isHermitian ρ ρ) h

/-! ### Entropies -/

/-- The two entropy functionals of `Statement` agree on states. -/
theorem vonNeumannEntropy_eq_matEntropy {d : ℕ} (ρ : DensityMatrix d) :
    vonNeumannEntropy ρ = matEntropy ρ.mat := by
  unfold matEntropy vonNeumannEntropy
  split_ifs with h
  · rfl
  · exact absurd ρ.posSemidef.isHermitian h

/-- `S(ρ) ≥ 0`. -/
theorem vonNeumannEntropy_nonneg {d : ℕ} (ρ : DensityMatrix d) : 0 ≤ vonNeumannEntropy ρ := by
  rw [vonNeumannEntropy_eq_matEntropy]
  exact matEntropy_nonneg_of_state ρ.posSemidef ρ.trace_one

/-! ### The bound function -/

private lemma negPLogP_nonneg' {p : ℝ} (hp1 : p ≤ 1) : 0 ≤ negPLogP p := by
  unfold negPLogP
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have : log2 p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos h.le hp1)
      (Real.log_nonneg one_le_two)
    nlinarith

/-- `h(0) = 0`. -/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, negPLogP, log2]

/-- The right-hand side of `Statement` vanishes at `ε = 0`. -/
theorem bound_zero (dA : ℕ) :
    (0 : ℝ) * log2 ((dA * dA - 1 : ℕ) : ℝ) + binaryEntropy 0 = 0 := by
  rw [binaryEntropy_zero]; ring

/-- The right-hand side of `Statement` is nonnegative for `ε ∈ [0, 1]`. -/
theorem bound_nonneg (dA : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    0 ≤ ε * log2 ((dA * dA - 1 : ℕ) : ℝ) + binaryEntropy ε := by
  have hlog : 0 ≤ log2 ((dA * dA - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (dA * dA - 1) with h | h
    · rw [h]; simp [log2]
    · have : (1 : ℝ) ≤ ((dA * dA - 1 : ℕ) : ℝ) := by exact_mod_cast h
      exact div_nonneg (Real.log_nonneg this) (Real.log_nonneg one_le_two)
  have hb : 0 ≤ binaryEntropy ε :=
    add_nonneg (negPLogP_nonneg' h1) (negPLogP_nonneg' (by linarith))
  have := mul_nonneg h0 hlog
  linarith

/-- The admissible range of `Statement` is a nontrivial interval: `0 < 1 - 1/d_A²`. -/
theorem threshold_pos {dA : ℕ} (hdA : 2 ≤ dA) : 0 < 1 - (1 : ℝ) / ((dA * dA : ℕ) : ℝ) := by
  have h4 : (4 : ℝ) ≤ ((dA * dA : ℕ) : ℝ) := by
    have : 4 ≤ dA * dA := by nlinarith
    exact_mod_cast this
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

/-- `1 - 1/d_A² < 1`. -/
theorem threshold_lt_one {dA : ℕ} (hdA : 2 ≤ dA) : 1 - (1 : ℝ) / ((dA * dA : ℕ) : ℝ) < 1 := by
  have : (0 : ℝ) < ((dA * dA : ℕ) : ℝ) := by
    have : 0 < dA * dA := by nlinarith
    exact_mod_cast this
  have := one_div_pos.2 this
  linarith

/-- At the threshold `ε = 1 - 1/d_A²` the bound equals `2 log₂ d_A`, the maximal possible
spread of the conditional entropy. -/
theorem bound_at_threshold {dA : ℕ} (hdA : 2 ≤ dA) :
    (1 - (1 : ℝ) / ((dA * dA : ℕ) : ℝ)) * log2 ((dA * dA - 1 : ℕ) : ℝ) +
      binaryEntropy (1 - (1 : ℝ) / ((dA * dA : ℕ) : ℝ)) = 2 * log2 (dA : ℝ) := by
  set D : ℝ := ((dA * dA : ℕ) : ℝ) with hD
  have h4 : (4 : ℝ) ≤ D := by
    have : 4 ≤ dA * dA := by nlinarith
    rw [hD]; exact_mod_cast this
  have hDpos : 0 < D := by linarith
  have hcast : ((dA * dA - 1 : ℕ) : ℝ) = D - 1 := by
    rw [hD, Nat.cast_sub (by nlinarith : 1 ≤ dA * dA)]; push_cast; ring
  rw [hcast]
  have hε : 1 - 1 / D = (D - 1) / D := by field_simp
  have h1ε : 1 - (1 - 1 / D) = 1 / D := by ring
  have hεpos : 0 < (D - 1) / D := div_pos (by linarith) hDpos
  have hlogD : log2 D = 2 * log2 (dA : ℝ) := by
    unfold log2
    rw [hD]; push_cast
    rw [Real.log_mul (by positivity) (by positivity)]; ring
  unfold binaryEntropy negPLogP
  have hDinv : (0 : ℝ) < 1 / D := by positivity
  rw [h1ε, hε]
  split_ifs with ha hb hb
  · linarith
  · linarith
  · linarith
  have hl1 : log2 ((D - 1) / D) = log2 (D - 1) - log2 D := by
    unfold log2; rw [Real.log_div (by linarith) hDpos.ne']; ring
  have hl2 : log2 (1 / D) = -log2 D := by
    unfold log2; rw [one_div, Real.log_inv]; ring
  rw [hl1, hl2, ← hlogD]
  field_simp
  ring

/-! ### Regression: `d_B = 1` -/

/-- For `d_B = 1`, `partialTraceA ρ` is the `1 × 1` identity. -/
theorem partialTraceA_dB_one {dA : ℕ} (ρ : DensityMatrix (dA * 1)) :
    @partialTraceA dA 1 ρ.mat = 1 := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp only [partialTraceA, Matrix.of_apply, Matrix.one_apply_eq]
  rw [← ρ.trace_one, Matrix.trace]
  refine Fintype.sum_equiv (finCongr (Nat.mul_one dA)).symm _ _ fun a => ?_
  have e : ((finCongr (Nat.mul_one dA)).symm a : Fin (dA * 1)) =
      ⟨a.1 * 1 + (0 : Fin 1).1, by simp⟩ := Fin.ext (by simp)
  rw [Matrix.diag_apply, e]

/-- For `d_B = 1`, the reduced state on `B` has entropy `0`. -/
theorem matEntropy_partialTraceA_dB_one {dA : ℕ} (ρ : DensityMatrix (dA * 1)) :
    matEntropy (@partialTraceA dA 1 ρ.mat) = 0 := by
  rw [partialTraceA_dB_one]
  exact matEntropy_eq_zero_of_idem Matrix.isHermitian_one (mul_one 1)

/-- For `d_B = 1`, `S(A|B)_ρ = S(ρ)`: `Statement` then specialises to an unconditional
continuity bound with the larger constant `log₂(d_A² - 1)`. -/
theorem condEntropy_dB_one {dA : ℕ} (ρ : DensityMatrix (dA * 1)) :
    vonNeumannEntropy ρ - matEntropy (@partialTraceA dA 1 ρ.mat) = vonNeumannEntropy ρ := by
  rw [matEntropy_partialTraceA_dB_one, sub_zero]

/-- For `d_B = 1` and a pure state `ρ` (`ρ² = ρ`), `S(A|B)_ρ = 0`. -/
theorem condEntropy_pure_dB_one {dA : ℕ} (ρ : DensityMatrix (dA * 1))
    (hpure : ρ.mat * ρ.mat = ρ.mat) :
    vonNeumannEntropy ρ - matEntropy (@partialTraceA dA 1 ρ.mat) = 0 := by
  rw [condEntropy_dB_one, vonNeumannEntropy_eq_matEntropy]
  exact matEntropy_eq_zero_of_idem ρ.posSemidef.isHermitian hpure

/-! ### Sanity instance -/

/-- The inequality of `Statement` holds for `ρ = σ` (both sides are `0`). This is only a
sanity check of the objects, not a proof of `Statement`. -/
theorem statement_instance_self (dA dB : ℕ) (ρ : DensityMatrix (dA * dB)) :
    |(vonNeumannEntropy ρ - matEntropy (@partialTraceA dA dB ρ.mat)) -
     (vonNeumannEntropy ρ - matEntropy (@partialTraceA dA dB ρ.mat))| ≤
      traceDistance ρ ρ * log2 ((dA * dA - 1 : ℕ) : ℝ) + binaryEntropy (traceDistance ρ ρ) := by
  rw [traceDistance_self, bound_zero, sub_self, abs_zero]

end InfoTheory.Known.Certificates.ConditionalEntropySharpContinuity
