import InfoTheory.Core

/-!
# Symmetric three-description quadratic Gaussian multiple descriptions

`Statement`: for `0 < D₃ ≤ D₂ ≤ D₁ ≤ 1`, the optimal symmetric per-description rate
`gaussMD3SymRate D₁ D₂ D₃` of the three-description problem for `X ~ N(0, 1)` equals
`tmdSymRateLowerBound D₁ D₂ D₃`, the Tian–Mohajer–Diggavi (2009) three-level remote-source
sum-rate lower bound (divided by 3), optimised over its two auxiliary noise levels. In words:
is the best known converse tight once all three distortion levels are active?

**Statement-fix (2026-11-27).** The previous right-hand side was a specific Tian–Chen
achievable rate (`tianChenMD3SymRate`) that fixed the layer-2 refinement noise independent of
the layer-1 noises and omitted time-sharing. It was false as written in two ways: a correlated
refinement beats it at `(1/2, 1/10, 1/20)`, and it is strictly non-convex at
`(3/5, 7/80, 19/400)` while `gaussMD3SymRate` is convex
(`attempts/gaussian-multiple-descriptions-3/2026-11-26-gemini-4-neon.md`). Any fixed
achievable scheme risks the same fate, so the new right-hand side is the *converse* side. A
new achievable scheme cannot refute it. Only a strictly better converse can, or a matching
scheme can prove it. It is convex in `(D₁, D₂, D₃)`: term `k` is convex in `D_k` when
`a ≥ b`, and a supremum of convex functions is convex. So the non-convexity mechanism does
not apply either. Tian, Mohajer and Diggavi (IEEE Trans. IT 55(8), 2009, §3.1.2) derive the
bound with free auxiliary noises `d₁ ≥ d₂ > 0` and write: "One could optimize within this set
of lower bounds to find the tightest one, however without a matching inner bound, solving this
rather involved optimization problem offers little insight", and (§1) "Though the lower bound
given here may not be tight, it is the first provably good bound with more than two levels of
distortion constraints enforced". Here `a = d₁/(1+d₁)` and `b = d₂/(1+d₂)` are the
MMSEs of `X` given the two remote sources. The closed range `0 ≤ b ≤ a ≤ 1` has the same
supremum by continuity. Song–Shao–Chen (IEEE Trans. IT 60(12), 2014, Thm. 7 and Cor. 10)
show that, for the Gaussian source, Gaussian remote sources are optimal in their general
single-letter bound. With `L = 3` it then reduces to this same expression
(our reduction: `θ₀ = 1` and `θ₃ = 0` are optimal, and the inner minimum is at `δ = d`).

Known facts:
* `½ log₂ (1/D₁) ≤ RHS ≤ ½ log₂(1/D₁) + ¼ log₂(D₁/D₂) + ⅙ log₂(D₂/D₃)`. The upper end is the
  successive-refinement plus MDS rate of Tian–Mohajer–Diggavi (2009, eq. (22)), which is
  achievable. The RHS is finite and never junk (certificate).
* Regression checks (certificate): `RHS(D, D, D) = ½ log₂(1/D)` (Shannon's Gaussian `R(D)`,
  which is exact when only individual descriptions matter), and `RHS(1, D, D) = ¼ log₂(1/D)`
  (the exact pairwise-only rate, attained by a `(3,2)` MDS split). With `b = 0` the RHS
  dominates Ozarow's two-description bound applied to any pair. With `b = a` it dominates the
  one-auxiliary Wang–Viswanath bound, which is the exact answer when `D₂` is inactive
  (Wang–Viswanath 2007; Chen 2009; Song–Shao–Chen 2014, Cor. 12).
* Open: when `D₁, D₂, D₃` are all active. Numerically, the best known inner bounds (Tian–Chen
  2010 layering with correlated refinement) lie about 0.12–0.18 bit per description above the
  RHS at sample points, for example `≈ 0.979` versus `≈ 0.862` at `(1/2, 1/10, 1/20)`.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfoTheory.Problems.GaussianMultipleDescriptions3

/-- Operational achievability of symmetric per-description rate `R` for the 3-channel
    quadratic Gaussian multiple descriptions problem (`X ~ N(0, 1)`) with measurable
    encoders and MSE evaluated via Lebesgue `lintegral` (preventing non-measurable `0` junk). -/
def IsGaussMD3SymAchievable (D₁ D₂ D₃ R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R + ε))))
    ∃ (enc₁ enc₂ enc₃ : (Fin n → ℝ) → Fin M)
      (dec₁ dec₂ dec₃ : Fin M → Fin n → ℝ)
      (dec₁₂ dec₁₃ dec₂₃ : Fin M × Fin M → Fin n → ℝ)
      (dec₁₂₃ : Fin M × Fin M × Fin M → Fin n → ℝ),
      Measurable enc₁ ∧ Measurable enc₂ ∧ Measurable enc₃ ∧
      let mse (recon : (Fin n → ℝ) → Fin n → ℝ) : ENNReal :=
        ∫⁻ x : Fin n → ℝ,
          ENNReal.ofReal ((∏ i : Fin n, gaussianPdf1D 1 (x i)) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, (x i - recon x i) ^ 2))
      mse (fun x => dec₁ (enc₁ x)) ≤ ENNReal.ofReal (D₁ + ε) ∧
      mse (fun x => dec₂ (enc₂ x)) ≤ ENNReal.ofReal (D₁ + ε) ∧
      mse (fun x => dec₃ (enc₃ x)) ≤ ENNReal.ofReal (D₁ + ε) ∧
      mse (fun x => dec₁₂ (enc₁ x, enc₂ x)) ≤ ENNReal.ofReal (D₂ + ε) ∧
      mse (fun x => dec₁₃ (enc₁ x, enc₃ x)) ≤ ENNReal.ofReal (D₂ + ε) ∧
      mse (fun x => dec₂₃ (enc₂ x, enc₃ x)) ≤ ENNReal.ofReal (D₂ + ε) ∧
      mse (fun x => dec₁₂₃ (enc₁ x, enc₂ x, enc₃ x)) ≤ ENNReal.ofReal (D₃ + ε)

/-- Optimal symmetric per-description rate `R*_sym(D₁, D₂, D₃)` for 3-channel quadratic
    Gaussian multiple descriptions, valued in `ℝ≥0∞` so an empty achievable set evaluates
    to `⊤` rather than junk `0`. -/
noncomputable def gaussMD3SymRate (D₁ D₂ D₃ : ℝ) : ℝ≥0∞ :=
  sInf { r : ℝ≥0∞ | ∃ R : ℝ, IsGaussMD3SymAchievable D₁ D₂ D₃ R ∧ r = ENNReal.ofReal R }

/-- One member of the Tian–Mohajer–Diggavi (2009, §3.1.2, eqs. (25)–(27)) family of
    lower bounds on the symmetric per-description rate (sum-rate bound divided by 3). The
    remote sources `Y₁ = X + N₁ + N₂` and `Y₂ = X + N₂` have MMSEs `a ≥ b` about `X`, with
    `a = d₁/(1+d₁)` and `b = d₂/(1+d₂)`. The three terms come from the one-description,
    two-description and three-description levels. -/
noncomputable def tmdBoundTerm (D₁ D₂ D₃ a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * log2 (1 / (a + D₁ * (1 - a))) +
  (1 / 4 : ℝ) * log2 ((a + D₂ * (1 - a)) / (b + D₂ * (1 - b))) +
  (1 / 6 : ℝ) * log2 ((b + D₃ * (1 - b)) / D₃)

/-- The optimised Tian–Mohajer–Diggavi lower bound on the symmetric per-description rate,
    which is also the Gaussian evaluation of the Song–Shao–Chen (2014) bound. The supremum is
    taken in `ℝ≥0∞` over the nonempty compact parameter set `0 ≤ b ≤ a ≤ 1`. On the domain of
    `Statement` it is finite and at least `½ log₂(1/D₁)` (certificate). -/
noncomputable def tmdSymRateLowerBound (D₁ D₂ D₃ : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : 0 ≤ b ∧ b ≤ a ∧ a ≤ 1),
    ENNReal.ofReal (tmdBoundTerm D₁ D₂ D₃ a b)

/-- Symmetric three-description quadratic Gaussian multiple descriptions
    (Venkataramani–Kramer–Goyal 2003; Tian–Mohajer–Diggavi 2009): is the optimised
    Tian–Mohajer–Diggavi three-level converse tight for all `0 < D₃ ≤ D₂ ≤ D₁ ≤ 1`? -/
def Statement : Prop :=
  ∀ (D₁ D₂ D₃ : ℝ), 0 < D₃ → D₃ ≤ D₂ → D₂ ≤ D₁ → D₁ ≤ 1 →
    gaussMD3SymRate D₁ D₂ D₃ = tmdSymRateLowerBound D₁ D₂ D₃

def problem : OpenProblem where
  id := "gaussian-multiple-descriptions-3"
  title := "Symmetric Rate-Distortion Function for Three-Channel Quadratic Gaussian Multiple Descriptions"
  category := .sourceCoding
  status := .open
  posedBy := "Raman Venkataramani, Gerhard Kramer, and Vivek K. Goyal"
  posedYear := 2003
  statement := Statement

end InfoTheory.Problems.GaussianMultipleDescriptions3
