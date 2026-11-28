import InfoTheory.Problems.QuantumEntropyPowerSharp
import InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold

/-!
# Certificate for `InfoTheory.Problems.QuantumEntropyPowerSharp`

The frozen statement is the Entropy Photon-Number Inequality (Guha–Erkmen–Shapiro 2008) for
single-mode states supported below a Fock cutoff `M`: with the exact Fock-basis beam-splitter
isometry `beamSplitterIso M λ` (output cutoff `2M`, photon number conserved),
`λ N(S(ρ_A)) + (1-λ) N(S(ρ_B)) ≤ N(S(σ_C))`, `N = g⁻¹`, `g(x) = (x+1)log₂(x+1) − x log₂ x`.

## Certified
* **Entropy photon number is not junk:** `bosonicG_zero`, `bosonicG_pos` (`g(x) > 0` for
  `x > 0`), `log2_succ_le_bosonicG` (`g(x) ≥ log₂(1+x)`, so the `sSup` defining `N(S)` is over a
  nonempty set bounded by `2^S`), `entropyPhotonNumber_zero : N(0) = 0`,
  `entropyPhotonNumber_nonneg : S ≥ 0 → N(S) ≥ 0`.
* **Beam-splitter matrix elements (textbook values):** `bs_one_zero`
  (`U|1,0⟩ = √λ|1,0⟩ + √(1−λ)|0,1⟩`), `bs_zero_one` (`U|0,1⟩ = −√(1−λ)|1,0⟩ + √λ|0,1⟩`),
  `bs_hom : ⟨1,1|U|1,1⟩ = 2λ − 1` and the Hong–Ou–Mandel dip `bs_hom_dip` (`= 0` at `λ = 1/2`).
  So `beamSplitterEntry` (signs, binomials, `√(k! l!/(m! n!))`) is the standard unitary.
* **Regression, vacuum (cutoff `M = 1`):** `outputC_cutoff_one` (the output mode `C` is the
  vacuum `|0⟩⟨0|`) and `epni_cutoff_one` (both sides of the inequality equal `0`). This is
  only the trivial `M = 1` instance.

## Not certified
* Isometry of `beamSplitterIso M λ` for general `M`; the proved quantum EPI (König–Smith;
  De Palma–Mari–Giovannetti); the one-Gaussian-input case of the EPnI.

## Adversarial check (2026-11-27)
The Fock cutoff only restricts to finitely supported inputs (a special case of the EPnI;
the general case follows by energy-constrained approximation and continuity of entropy), and
the output space `2M × 2M` holds every output Fock state exactly, so no truncation error
enters. `N` uses the same base-2 units as `S`. The EPnI is proved only for Gaussian inputs,
when one input is the vacuum / Gaussian, and for some special classes (Das–Sharma–
Muthukrishnan; De Palma–Trevisan–Giovannetti 2016–17); no general proof or counterexample
found through 2026. Statement FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.QuantumEntropyPowerSharp

open InfoTheory InfoTheory.Problems.QuantumEntropyPowerSharp Matrix

/-! ### The thermal entropy function and the entropy photon number -/

theorem bosonicG_zero : bosonicG 0 = 0 := by simp [bosonicG]

/-- `g(x) ≥ log₂(x + 1)` for `x > 0`. -/
theorem log2_succ_le_bosonicG {x : ℝ} (hx : 0 < x) : log2 (x + 1) ≤ bosonicG x := by
  unfold bosonicG log2
  rw [if_neg (not_le.2 hx)]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmono : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx (by linarith)
  rw [mul_div_assoc', mul_div_assoc', ← sub_div, div_le_div_iff_of_pos_right hl2]
  nlinarith

theorem bosonicG_pos {x : ℝ} (hx : 0 < x) : 0 < bosonicG x := by
  refine lt_of_lt_of_le ?_ (log2_succ_le_bosonicG hx)
  unfold log2
  exact div_pos (Real.log_pos (by linarith)) (Real.log_pos one_lt_two)

private lemma epn_bdd (S : ℝ) : BddAbove { x : ℝ | 0 ≤ x ∧ bosonicG x ≤ S } := by
  refine ⟨(2 : ℝ) ^ S, ?_⟩
  rintro x ⟨hx0, hx⟩
  rcases hx0.eq_or_lt with h | h
  · subst h; exact (Real.rpow_pos_of_pos two_pos S).le
  · have h1 := (log2_succ_le_bosonicG h).trans hx
    unfold log2 at h1
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [div_le_iff₀ hl2] at h1
    have : x + 1 ≤ (2 : ℝ) ^ S := by
      rw [← Real.exp_log (by linarith : 0 < x + 1), Real.rpow_def_of_pos two_pos]
      exact Real.exp_le_exp.2 (by linarith)
    linarith

/-- `N(0) = 0`: only the vacuum has zero thermal entropy. -/
theorem entropyPhotonNumber_zero : entropyPhotonNumber 0 = 0 := by
  unfold entropyPhotonNumber
  have : { x : ℝ | 0 ≤ x ∧ bosonicG x ≤ 0 } = {0} := by
    ext x
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, hg⟩
      by_contra hne
      exact absurd hg (not_le.2 (bosonicG_pos (lt_of_le_of_ne h0 (Ne.symm hne))))
    · rintro rfl; exact ⟨le_rfl, by rw [bosonicG_zero]⟩
  rw [this, csSup_singleton]

/-- `N(S) ≥ 0` for `S ≥ 0` (the `sSup` is over a nonempty bounded set). -/
theorem entropyPhotonNumber_nonneg {S : ℝ} (hS : 0 ≤ S) : 0 ≤ entropyPhotonNumber S :=
  le_csSup (epn_bdd S) ⟨le_rfl, by rw [bosonicG_zero]; exact hS⟩

/-! ### Beam-splitter matrix elements -/

/-- Single photon in mode `a`: `U|1,0⟩ = √λ |1,0⟩ + √(1-λ) |0,1⟩`. -/
theorem bs_one_zero (lam : ℝ) :
    beamSplitterEntry lam 1 0 1 0 = Real.sqrt lam ∧
      beamSplitterEntry lam 0 1 1 0 = Real.sqrt (1 - lam) := by
  constructor <;> simp [beamSplitterEntry, fact, binom]

/-- Single photon in mode `b`: `U|0,1⟩ = -√(1-λ) |1,0⟩ + √λ |0,1⟩`. -/
theorem bs_zero_one (lam : ℝ) :
    beamSplitterEntry lam 1 0 0 1 = -Real.sqrt (1 - lam) ∧
      beamSplitterEntry lam 0 1 0 1 = Real.sqrt lam := by
  constructor <;> simp [beamSplitterEntry, fact, binom]

/-- Hong–Ou–Mandel amplitude `⟨1,1|U|1,1⟩ = 2λ − 1`. -/
theorem bs_hom (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    beamSplitterEntry lam 1 1 1 1 = 2 * lam - 1 := by
  simp [beamSplitterEntry, fact, binom, Fin.sum_univ_two]
  rw [Real.sq_sqrt h0, Real.sq_sqrt (by linarith)]
  ring

/-- The Hong–Ou–Mandel dip: a balanced beam splitter never outputs `|1,1⟩` from `|1,1⟩`. -/
theorem bs_hom_dip : beamSplitterEntry (1 / 2) 1 1 1 1 = 0 := by
  rw [bs_hom _ (by norm_num) (by norm_num)]; norm_num

/-! ### Fock cutoff `M = 1`: vacuum inputs -/

private lemma densityMatrix_one (ρ : DensityMatrix 1) : ρ.mat = 1 := by
  ext i j
  fin_cases i; fin_cases j
  have := ρ.trace_one
  simpa [Matrix.trace] using this

theorem vonNeumannEntropy_eq_matEntropy {d : ℕ} (ρ : DensityMatrix d) :
    vonNeumannEntropy ρ = matEntropy ρ.mat := by
  unfold vonNeumannEntropy matEntropy
  rw [dif_pos ρ.posSemidef.1]

theorem vonNeumannEntropy_dim_one (ρ : DensityMatrix 1) : vonNeumannEntropy ρ = 0 := by
  rw [vonNeumannEntropy_eq_matEntropy, densityMatrix_one]
  exact ClassicalCapacityAdditivityThreshold.matEntropy_eq_zero_of_idem
    (Matrix.isHermitian_one) (Matrix.one_mul 1)

/-- With cutoff `M = 1` the beam splitter maps the two-mode vacuum to the vacuum and the
    output mode `C` is the vacuum `|0⟩⟨0|` (as a 2×2 matrix). -/
theorem outputC_cutoff_one (lam : ℝ) (ρA ρB : DensityMatrix 1) :
    @partialTraceB (2 * 1) (2 * 1)
      (beamSplitterIso 1 lam * kronMat ρA.mat ρB.mat * (beamSplitterIso 1 lam)ᴴ) =
      Matrix.of fun i j : Fin (2 * 1) => if i.1 = 0 ∧ j.1 = 0 then (1 : ℂ) else 0 := by
  rw [densityMatrix_one ρA, densityMatrix_one ρB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceB, beamSplitterIso, beamSplitterEntry, Matrix.mul_apply, kronMat,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, fact, binom]

/-- **Regression (vacuum inputs):** the Statement's inequality holds at Fock cutoff
    `M = 1` — both sides are `0`, since `N(0) = 0` and the output is the vacuum. This is
    only the trivial `M = 1` instance, not the Statement. -/
theorem epni_cutoff_one (lam : ℝ) (ρA ρB : DensityMatrix 1) :
    let U := beamSplitterIso 1 lam
    let σCD := U * kronMat ρA.mat ρB.mat * Uᴴ
    let σC := @partialTraceB (2 * 1) (2 * 1) σCD
    lam * entropyPhotonNumber (vonNeumannEntropy ρA) +
      (1 - lam) * entropyPhotonNumber (vonNeumannEntropy ρB) =
      entropyPhotonNumber (matEntropy σC) := by
  intro U σCD σC
  have hσ : matEntropy σC = 0 := by
    show matEntropy (@partialTraceB (2 * 1) (2 * 1)
      (beamSplitterIso 1 lam * kronMat ρA.mat ρB.mat * (beamSplitterIso 1 lam)ᴴ)) = 0
    rw [outputC_cutoff_one]
    apply ClassicalCapacityAdditivityThreshold.matEntropy_eq_zero_of_idem
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hσ, vonNeumannEntropy_dim_one, vonNeumannEntropy_dim_one, entropyPhotonNumber_zero]
  ring

end InfoTheory.Known.Certificates.QuantumEntropyPowerSharp
