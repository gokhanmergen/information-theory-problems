import InfoTheory.Problems.RenyiEntropyPowerSharp
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.RenyiEntropyPowerSharp`

The frozen statement asks for `N_α(X + Y) ≥ c_*(α) (N_α(X) + N_α(Y))` for all `α > 1`, all
`d ≥ 1` and all independent `X, Y` with finite `L^α` norms, where `c_* = sharpRenyiConst`.

**Catalog status (2026-11-27 audit): this is a published theorem.** `sharpRenyiConst α` is,
identically, the two-summand Ram–Sason constant `c_α^{(2)} = α^{1/(α-1)} (1 - 1/(2α'))^{2α'-1}`,
`α' = α/(α-1)` (E. Ram and I. Sason, "On Rényi entropy power inequalities", IEEE Trans. Inf.
Theory 62(12):6800–6815, 2016, Theorem 1 with `n = 2`), proved there for all independent random
vectors in every dimension. See `problems/renyi-entropy-power-sharp.md`.

## Certified (about exactly these objects)
* `sharpRenyiConst_eq_ramSason` — the identity `c_*(α) = α^{1/(α-1)} ((α+1)/(2α))^{(α+1)/(α-1)}`
  `= α^{1/(α-1)} (1 - 1/(2α'))^{2α'-1}` for every `α > 1`, i.e. the catalog constant is exactly
  Ram–Sason's `c_α^{(2)}` (this is what identifies `Statement` with their Theorem 1).
* `sharpRenyiConst_two` — **regression** `c_*(2) = 27/32`.
* `sharpRenyiConst_pos` — `c_*(α) > 0` for `α > 1`; `renyiEntropyPower_pos` — `N_α(f) > 0`.

## Not certified
* Ram–Sason's Theorem 1 itself (sharp Young inequality of Beckner/Brascamp–Lieb is not in
  Mathlib), hence `Statement` is **not** proved here.
* Sharpness: the uniform distribution on the Euclidean ball in `ℝ^d`, `d → ∞`, has
  `N_α(X+Y)/(N_α(X)+N_α(Y)) → c_*(α)` (a Laplace-method computation recorded in the problem
  file), so `c_*(α)` is the optimal dimension-free constant.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.RenyiEntropyPowerSharp

open InfoTheory InfoTheory.Problems.RenyiEntropyPowerSharp

theorem renyiEntropyPower_pos {d : ℕ} (α : ℝ) (f : Density d) : 0 < renyiEntropyPower α f :=
  Real.exp_pos _

theorem sharpRenyiConst_pos {α : ℝ} (hα : 1 < α) : 0 < sharpRenyiConst α := by
  unfold sharpRenyiConst
  have h0 : 0 < α := by linarith
  positivity

/-- `c_*(α)` is exactly the two-summand Ram–Sason constant
    `α^{1/(α-1)} ((α+1)/(2α))^{(α+1)/(α-1)}`. -/
theorem sharpRenyiConst_eq_ramSason {α : ℝ} (hα : 1 < α) :
    sharpRenyiConst α =
      α ^ (1 / (α - 1)) * ((α + 1) / (2 * α)) ^ ((α + 1) / (α - 1)) := by
  have h0 : 0 < α := by linarith
  have h1 : 0 < α - 1 := by linarith
  have hlhs : 0 < sharpRenyiConst α := sharpRenyiConst_pos hα
  have hrhs : 0 < α ^ (1 / (α - 1)) * ((α + 1) / (2 * α)) ^ ((α + 1) / (α - 1)) := by
    positivity
  refine Real.log_injOn_pos (Set.mem_Ioi.2 hlhs) (Set.mem_Ioi.2 hrhs) ?_
  unfold sharpRenyiConst
  have ha1 : (0 : ℝ) < α + 1 := by linarith
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow ha1, Real.log_rpow (by norm_num), Real.log_rpow h0, Real.log_rpow h0,
    Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  field_simp
  ring

/-- The equivalent Ram–Sason form `α^{1/(α-1)} (1 - 1/(2α'))^{2α'-1}`, `α' = α/(α-1)`. -/
theorem sharpRenyiConst_eq_ramSason' {α : ℝ} (hα : 1 < α) :
    sharpRenyiConst α =
      α ^ (1 / (α - 1)) * (1 - 1 / (2 * (α / (α - 1)))) ^ (2 * (α / (α - 1)) - 1) := by
  have h0 : α ≠ 0 := by linarith
  have h1 : α - 1 ≠ 0 := by linarith
  rw [sharpRenyiConst_eq_ramSason hα]
  congr 2
  · field_simp; ring
  · field_simp; ring

/-- **Regression:** `c_*(2) = 27/32`. -/
theorem sharpRenyiConst_two : sharpRenyiConst 2 = 27 / 32 := by
  unfold sharpRenyiConst
  norm_num

end InfoTheory.Known.Certificates.RenyiEntropyPowerSharp
