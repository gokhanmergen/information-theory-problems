import InfoTheory.Problems.ConditionalEntropyPowerConjecture
import InfoTheory.Bridge.EntropyPower

/-!
# Certificate for `InfoTheory.Problems.ConditionalEntropyPowerConjecture`

`Statement` (Courtade's strong EPI with unconstrained `W`): for all `d ≥ 1` and independent
`X, Y, W` on `ℝ^d` with finite entropies and second moments,
`N(X+W) N(Y+W) ≥ N(X+Y+W) N(W) + N(X) N(Y)`, where the sum densities are given through
`densityConv`. Facts below are about the exact `Core` objects (`Density`, `entropyPower`,
`densityConv`), using `Bridge.Gaussian` and Shannon's 1-D EPI from `Bridge.EntropyPower`.

## Certified
* `SliceAt`, `statement_iff_forall_slice` — `Statement ↔ ∀ d ≥ 1, SliceAt d` (definitional).
* `entropyPower_pos'` — all entropy powers are `> 0` (no junk `0`).
* `gaussian_hypotheses` — **non-vacuity**: the Gaussian triple `N(0,a), N(0,b), N(0,c)` with
  sum densities `N(0,a+c), N(0,b+c), N(0,a+c+b)` satisfies every hypothesis of `SliceAt 1`.
* `gaussian_equality`, `slice_one_gaussian` — **regression (Gaussian equality case, `d = 1`)**:
  for Gaussian `X, Y, W` and any `fXW, fYW, fXYW` satisfying the convolution hypotheses,
  `N(X+W) N(Y+W) = N(X+Y+W) N(W) + N(X) N(Y)` (`(a+c)(b+c) = (a+b+c)c + ab`).
* `epi_consequences` — **regression (trivial conditioning, `d = 1`)**: under the slice
  hypotheses, `N(X+W) ≥ N(X) + N(W)`, `N(Y+W) ≥ N(Y) + N(W)`, `N(X+Y+W) ≥ N(X+W) + N(Y)`
  (`Bridge.entropyPower_add_ge`). The first is the `I(X;V) = I(X+W;V) = 0` instance of the
  conjecture's equivalent form `N(X+W) e^{-2I(X;V)} ≥ N(X) e^{-2I(X+W;V)} + N(W)`.
* `slice_one_of_tight` — in `d = 1` the conjectured inequality holds whenever
  `N(X+Y+W) ≤ N(X) + N(Y) + N(W)` (three-term EPI tight).

None of these proves or disproves `Statement`: the open case is non-Gaussian `W`
(Courtade 2018 proves Gaussian `W`, which is not formalized here).
-/

open scoped BigOperators Real
open MeasureTheory InfoTheory InfoTheory.Bridge

namespace InfoTheory.Known.Certificates.ConditionalEntropyPowerConjecture

open InfoTheory.Problems.ConditionalEntropyPowerConjecture

/-- Two densities with the same pdf are equal. -/
lemma density_ext {d : ℕ} {f g : Density d} (h : ∀ x, f.pdf x = g.pdf x) : f = g := by
  cases f; cases g
  simp only [Density.mk.injEq]
  exact funext h

/-- The `d`-dimensional slice of `Statement` (its body at a fixed `d`). -/
def SliceAt (d : ℕ) : Prop :=
  ∀ (fX fY fW fXW fYW fXYW : Density d),
    HasFiniteDiffEntropy fX → HasFiniteDiffEntropy fY → HasFiniteDiffEntropy fW →
    HasFiniteDiffEntropy fXW → HasFiniteDiffEntropy fYW → HasFiniteDiffEntropy fXYW →
    HasFiniteSecondMoment fX → HasFiniteSecondMoment fY → HasFiniteSecondMoment fW →
    (∀ x : Fin d → ℝ, fXW.pdf x = densityConv fX fW x) →
    (∀ x : Fin d → ℝ, fYW.pdf x = densityConv fY fW x) →
    (∀ x : Fin d → ℝ, fXYW.pdf x = densityConv fXW fY x) →
    entropyPower fXW * entropyPower fYW ≥
      entropyPower fXYW * entropyPower fW + entropyPower fX * entropyPower fY

/-- `Statement` is exactly "every slice `d ≥ 1` holds" (definitional; checks `SliceAt`). -/
theorem statement_iff_forall_slice : Statement ↔ ∀ d : ℕ, 1 ≤ d → SliceAt d := Iff.rfl

/-- Entropy powers are strictly positive (never the junk value `0`). -/
theorem entropyPower_pos' {d : ℕ} (f : Density d) : 0 < entropyPower f := by
  unfold entropyPower
  positivity

lemma hasFiniteSecondMoment_gaussianDensity1D' {v : ℝ} (hv : 0 < v) :
    HasFiniteSecondMoment (gaussianDensity1D v hv) := by
  unfold HasFiniteSecondMoment
  simp only [Fin.sum_univ_one]
  exact (integrable_fin1_iff (fun t => t ^ 2 * gaussianPdf1D v t)).mpr
    (integrable_sq_mul_gaussianPdf1D hv)

/-- In `d = 1`, the `densityConv` hypotheses of the statement identify the sum densities with
    `Bridge.convDensity`. -/
lemma eq_convDensity {f g h : Density 1} (hh : ∀ x, h.pdf x = densityConv f g x) :
    h = convDensity f g :=
  density_ext hh

/-! ### Regression: Gaussian triples (equality) -/

/-- **Gaussian equality case (`d = 1`).** If `X ~ N(0, a)`, `Y ~ N(0, b)`, `W ~ N(0, c)`, then
    for *any* densities `fXW, fYW, fXYW` satisfying the statement's convolution hypotheses,
    `N(X+W) N(Y+W) = N(X+Y+W) N(W) + N(X) N(Y)`, i.e. `(a+c)(b+c) = (a+b+c)c + ab`. -/
theorem gaussian_equality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (fXW fYW fXYW : Density 1)
    (h₁ : ∀ x, fXW.pdf x = densityConv (gaussianDensity1D a ha) (gaussianDensity1D c hc) x)
    (h₂ : ∀ x, fYW.pdf x = densityConv (gaussianDensity1D b hb) (gaussianDensity1D c hc) x)
    (h₃ : ∀ x, fXYW.pdf x = densityConv fXW (gaussianDensity1D b hb) x) :
    entropyPower fXW * entropyPower fYW =
      entropyPower fXYW * entropyPower (gaussianDensity1D c hc) +
        entropyPower (gaussianDensity1D a ha) * entropyPower (gaussianDensity1D b hb) := by
  have e₁ : fXW = awgnOutputDensity (gaussianDensity1D a ha) c hc := density_ext h₁
  have e₂ : fYW = awgnOutputDensity (gaussianDensity1D b hb) c hc := density_ext h₂
  subst e₁ e₂
  have e₃ : fXYW = awgnOutputDensity (awgnOutputDensity (gaussianDensity1D a ha) c hc) b hb :=
    density_ext h₃
  subst e₃
  simp only [awgnOutputDensity_gaussian, entropyPower_gaussianDensity1D]
  ring

/-- The Gaussian triple satisfies every hypothesis of the `d = 1` slice (so the slice is not
    vacuous), with the sum densities given by Gaussians of the summed variances. -/
theorem gaussian_hypotheses {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    let fX := gaussianDensity1D a ha
    let fY := gaussianDensity1D b hb
    let fW := gaussianDensity1D c hc
    let fXW := gaussianDensity1D (a + c) (add_pos ha hc)
    let fYW := gaussianDensity1D (b + c) (add_pos hb hc)
    let fXYW := gaussianDensity1D (a + c + b) (add_pos (add_pos ha hc) hb)
    HasFiniteDiffEntropy fX ∧ HasFiniteDiffEntropy fY ∧ HasFiniteDiffEntropy fW ∧
      HasFiniteDiffEntropy fXW ∧ HasFiniteDiffEntropy fYW ∧ HasFiniteDiffEntropy fXYW ∧
      HasFiniteSecondMoment fX ∧ HasFiniteSecondMoment fY ∧ HasFiniteSecondMoment fW ∧
      (∀ x : Fin 1 → ℝ, fXW.pdf x = densityConv fX fW x) ∧
      (∀ x : Fin 1 → ℝ, fYW.pdf x = densityConv fY fW x) ∧
      (∀ x : Fin 1 → ℝ, fXYW.pdf x = densityConv fXW fY x) := by
  intro fX fY fW fXW fYW fXYW
  refine ⟨hasFiniteDiffEntropy_gaussianDensity1D _, hasFiniteDiffEntropy_gaussianDensity1D _,
    hasFiniteDiffEntropy_gaussianDensity1D _, hasFiniteDiffEntropy_gaussianDensity1D _,
    hasFiniteDiffEntropy_gaussianDensity1D _, hasFiniteDiffEntropy_gaussianDensity1D _,
    hasFiniteSecondMoment_gaussianDensity1D' _, hasFiniteSecondMoment_gaussianDensity1D' _,
    hasFiniteSecondMoment_gaussianDensity1D' _, ?_, ?_, ?_⟩
  · intro x
    exact (congrFun (congrArg Density.pdf (awgnOutputDensity_gaussian ha hc)) x).symm
  · intro x
    exact (congrFun (congrArg Density.pdf (awgnOutputDensity_gaussian hb hc)) x).symm
  · intro x
    exact (congrFun (congrArg Density.pdf (awgnOutputDensity_gaussian (add_pos ha hc) hb)) x).symm

/-! ### Regression: the EPI ("trivial conditioning") consequences in `d = 1` -/

/-- **Unconditional EPI on the statement's objects (`d = 1`).** Under the hypotheses of the
    `d = 1` slice, Shannon's EPI (`Bridge.entropyPower_add_ge`) gives
    `N(X+W) ≥ N(X) + N(W)`, `N(Y+W) ≥ N(Y) + N(W)` and `N(X+Y+W) ≥ N(X+W) + N(Y)`.
    The first is the `I(X; V) = I(X+W; V) = 0` (trivial-conditioning) instance of the
    conjecture's equivalent form `N(X+W) e^{-2I(X;V)} ≥ N(X) e^{-2I(X+W;V)} + N(W)`. -/
theorem epi_consequences (fX fY fW fXW fYW fXYW : Density 1)
    (hX : HasFiniteDiffEntropy fX) (hY : HasFiniteDiffEntropy fY) (hW : HasFiniteDiffEntropy fW)
    (hXW : HasFiniteDiffEntropy fXW) (hYW : HasFiniteDiffEntropy fYW)
    (hXYW : HasFiniteDiffEntropy fXYW)
    (mX : HasFiniteSecondMoment fX) (mY : HasFiniteSecondMoment fY)
    (mW : HasFiniteSecondMoment fW)
    (cXW : ∀ x : Fin 1 → ℝ, fXW.pdf x = densityConv fX fW x)
    (cYW : ∀ x : Fin 1 → ℝ, fYW.pdf x = densityConv fY fW x)
    (cXYW : ∀ x : Fin 1 → ℝ, fXYW.pdf x = densityConv fXW fY x) :
    entropyPower fX + entropyPower fW ≤ entropyPower fXW ∧
      entropyPower fY + entropyPower fW ≤ entropyPower fYW ∧
      entropyPower fXW + entropyPower fY ≤ entropyPower fXYW := by
  have e₁ := eq_convDensity cXW
  have e₂ := eq_convDensity cYW
  have e₃ := eq_convDensity cXYW
  subst e₁ e₂ e₃
  refine ⟨entropyPower_add_ge fX fW hX hW hXW mX mW,
    entropyPower_add_ge fY fW hY hW hYW mY mW, ?_⟩
  exact entropyPower_add_ge (convDensity fX fW) fY hXW hY hXYW
    (hasFiniteSecondMoment_convDensity fX fW mX mW) mY

/-- **Conditional regression (`d = 1`).** Under the slice hypotheses, the conjectured
    inequality holds whenever `N(X+Y+W) ≤ N(X) + N(Y) + N(W)` (by EPI this forces equality in
    the three-term EPI, as for Gaussians). Proof: `N(X+W) N(Y+W) ≥ (N(X)+N(W))(N(Y)+N(W))`
    by `epi_consequences`. This does not decide the statement. -/
theorem slice_one_of_tight (fX fY fW fXW fYW fXYW : Density 1)
    (hX : HasFiniteDiffEntropy fX) (hY : HasFiniteDiffEntropy fY) (hW : HasFiniteDiffEntropy fW)
    (hXW : HasFiniteDiffEntropy fXW) (hYW : HasFiniteDiffEntropy fYW)
    (hXYW : HasFiniteDiffEntropy fXYW)
    (mX : HasFiniteSecondMoment fX) (mY : HasFiniteSecondMoment fY)
    (mW : HasFiniteSecondMoment fW)
    (cXW : ∀ x : Fin 1 → ℝ, fXW.pdf x = densityConv fX fW x)
    (cYW : ∀ x : Fin 1 → ℝ, fYW.pdf x = densityConv fY fW x)
    (cXYW : ∀ x : Fin 1 → ℝ, fXYW.pdf x = densityConv fXW fY x)
    (htight : entropyPower fXYW ≤ entropyPower fX + entropyPower fY + entropyPower fW) :
    entropyPower fXW * entropyPower fYW ≥
      entropyPower fXYW * entropyPower fW + entropyPower fX * entropyPower fY := by
  obtain ⟨h₁, h₂, _⟩ :=
    epi_consequences fX fY fW fXW fYW fXYW hX hY hW hXW hYW hXYW mX mY mW cXW cYW cXYW
  have pX := entropyPower_pos' fX
  have pY := entropyPower_pos' fY
  have pW := entropyPower_pos' fW
  have hprod : (entropyPower fX + entropyPower fW) * (entropyPower fY + entropyPower fW) ≤
      entropyPower fXW * entropyPower fYW :=
    mul_le_mul h₁ h₂ (by positivity) (by linarith)
  have hW' : entropyPower fXYW * entropyPower fW ≤
      (entropyPower fX + entropyPower fY + entropyPower fW) * entropyPower fW :=
    mul_le_mul_of_nonneg_right htight pW.le
  nlinarith

/-- The `d = 1` slice restricted to Gaussian `X, Y, W` holds (with equality). -/
theorem slice_one_gaussian {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (fXW fYW fXYW : Density 1)
    (h₁ : ∀ x, fXW.pdf x = densityConv (gaussianDensity1D a ha) (gaussianDensity1D c hc) x)
    (h₂ : ∀ x, fYW.pdf x = densityConv (gaussianDensity1D b hb) (gaussianDensity1D c hc) x)
    (h₃ : ∀ x, fXYW.pdf x = densityConv fXW (gaussianDensity1D b hb) x) :
    entropyPower fXW * entropyPower fYW ≥
      entropyPower fXYW * entropyPower (gaussianDensity1D c hc) +
        entropyPower (gaussianDensity1D a ha) * entropyPower (gaussianDensity1D b hb) :=
  (gaussian_equality ha hb hc fXW fYW fXYW h₁ h₂ h₃).ge

end InfoTheory.Known.Certificates.ConditionalEntropyPowerConjecture
