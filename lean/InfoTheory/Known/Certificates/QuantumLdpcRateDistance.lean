import InfoTheory.Problems.QuantumLdpcRateDistance
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certificate for `InfoTheory.Problems.QuantumLdpcRateDistance`

The frozen statement asks whether `w`-LDPC CSS codes (`ExistsQLDPCCSSCode n k d w`:
`Hx Hzᵀ = 0`, row/column weights `≤ w`, `k ≤ n − rank Hx − rank Hz`, and both CSS distances
`≥ d`) reach the CSS Gilbert–Varshamov tradeoff `k/n ≥ 1 − 2h(δ) − ε`, `d ≥ δ n`, with `w`
depending only on `(δ, ε)`.

## Certified
* **Regression, trivial code:** `trivial_code : ExistsQLDPCCSSCode n n 1 0` (no checks:
  the `[[n, n, 1]]` code, check weight `0`).
* **Non-junk distance:** `trivial_rate_forces_distance_le_one`: if `0 < n` and
  `ExistsQLDPCCSSCode n n d w` then `d ≤ 1`. Rate-1 CSS codes have distance at most `1`, so
  the distance clause is a genuine constraint (codes cannot cheat with full rate and large
  `d`), and `rate_le_one : ExistsQLDPCCSSCode n k d w → k ≤ n`.
* **Non-vacuous hypotheses:** `binaryEntropy_hundredth_lt : binaryEntropy (1/100) < 1/2`, so
  `δ = 1/100` satisfies the premises `0 < δ < 1/2`, `0 < 1 − 2h(δ)` (the Statement does not hold
  vacuously).

## Not certified
* Good qLDPC codes (Panteleev–Kalachev 2022; quantum Tanner codes); the CSS GV bound for dense
  random CSS codes (Calderbank–Shor 1996).

## Adversarial check (2026-11-27)
The formalization is faithful: logical `Z` operators are `ker Hx / row Hz`, logical `X`
operators `ker Hz / row Hx`, `k = n − rank Hx − rank Hz` (as an upper bound on the claimed
`k`), and LDPC is bounded row *and* column weight. Panteleev–Kalachev only give *some*
linear rate/distance, far below `1 − 2h(δ)`, so they do not settle the Statement. However,
2026 preprints claim the CSS GV bound at bounded check weight (Kasai arXiv:2603.24588,
"Finite-Degree Quantum LDPC Codes Reaching the Gilbert–Varshamov Bound"; Mittal–Srivastava–
Tulsiani–Wootters arXiv:2610.02648); the `.md` already records `formal_status:
claimed-resolved`. Kept as is (claims unrefereed); Lean not modified.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.QuantumLdpcRateDistance

open InfoTheory InfoTheory.Problems.QuantumLdpcRateDistance

theorem rowSpace_empty {n : ℕ} (H : Matrix (Fin 0) (Fin n) (ZMod 2)) : rowSpace H = ⊥ := by
  unfold rowSpace
  rw [Submodule.span_eq_bot]
  rintro r ⟨i, -⟩
  exact i.elim0

/-- The trivial `[[n, n, 1]]` code with no checks. -/
theorem trivial_code (n : ℕ) : ExistsQLDPCCSSCode n n 1 0 := by
  refine ⟨0, 0, 0, 0, fun i => i.elim0, fun i => i.elim0, fun t => ?_, fun j => j.elim0,
    fun t => ?_, ?_, ?_, ?_⟩
  · unfold binWeight; simp
  · unfold binWeight; simp
  · rw [rowSpace_empty]; simp
  · intro v _ hv
    rw [rowSpace_empty, Submodule.mem_bot] at hv
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv
    unfold binWeight
    exact Finset.one_le_card.mpr ⟨t, by simpa using ht⟩
  · intro v _ hv
    rw [rowSpace_empty, Submodule.mem_bot] at hv
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv
    unfold binWeight
    exact Finset.one_le_card.mpr ⟨t, by simpa using ht⟩

/-- The logical dimension never exceeds the blocklength. -/
theorem rate_le_one {n k d w : ℕ} (h : ExistsQLDPCCSSCode n k d w) : k ≤ n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hk, _⟩ := h
  omega

/-- A rate-one CSS code (`k = n`) has distance at most `1`. -/
theorem trivial_rate_forces_distance_le_one {n d w : ℕ} (hn : 0 < n)
    (h : ExistsQLDPCCSSCode n n d w) : d ≤ 1 := by
  obtain ⟨mX, mZ, Hx, Hz, -, -, -, -, -, hk, hZ, -⟩ := h
  have hx0 : Module.finrank (ZMod 2) (rowSpace Hx) = 0 := by omega
  have hz0 : Module.finrank (ZMod 2) (rowSpace Hz) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hx0 hz0
  let e : Fin n → ZMod 2 := Pi.single ⟨0, hn⟩ 1
  have hrow : ∀ i : Fin mX, (fun t => Hx i t) = 0 := by
    intro i
    have : (fun t => Hx i t) ∈ rowSpace Hx := Submodule.subset_span ⟨i, rfl⟩
    rw [hx0, Submodule.mem_bot] at this
    exact this
  have hker : ∀ i : Fin mX, ∑ t : Fin n, Hx i t * e t = 0 := by
    intro i
    have := congrFun (hrow i)
    simp only [Pi.zero_apply] at this
    simp [this]
  have hnot : e ∉ rowSpace Hz := by
    rw [hz0, Submodule.mem_bot]
    intro he
    have := congrFun he ⟨0, hn⟩
    simp [e] at this
  have := hZ e hker hnot
  have hw : binWeight e = 1 := by
    unfold binWeight
    rw [Finset.card_eq_one]
    refine ⟨⟨0, hn⟩, ?_⟩
    ext t
    by_cases ht : t = ⟨0, hn⟩
    · subst ht; simp [e]
    · simp [e, ht, Pi.single_apply]
  omega

/-- `h(1/100) < 1/2`, so `δ = 1/100` meets the Statement's premises. -/
theorem binaryEntropy_hundredth_lt : binaryEntropy (1 / 100) < 1 / 2 := by
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  -- `−p log₂ p = p log₂ 100 ≤ p · 7` since `100 < 2⁷`.
  have h1 : negPLogP (1 / 100) ≤ 7 / 100 := by
    unfold negPLogP log2
    split_ifs with hc
    · norm_num at hc
    have : Real.log (1 / 100) = - Real.log 100 := by
      rw [one_div, Real.log_inv]
    rw [this]
    have h100 : Real.log 100 < 7 * Real.log 2 := by
      have e : Real.log ((2 : ℝ) ^ 7) = 7 * Real.log 2 := by
        rw [Real.log_pow]; norm_num
      rw [← e]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    rw [show -(1 / 100 : ℝ) * (-Real.log 100 / Real.log 2) = Real.log 100 / Real.log 2 / 100 by
      ring, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- `−q log₂ q ≤ (1 − q)/ln 2` for `q ∈ (0,1]` (from `log q ≥ 1 − 1/q`).
  have h2 : negPLogP (1 - 1 / 100) ≤ 3 / 200 := by
    unfold negPLogP log2
    split_ifs with hc
    · norm_num at hc
    have hlog : -(1 / 99 : ℝ) ≤ Real.log (1 - 1 / 100) := by
      have := Real.add_one_le_exp (-(1 / 99 : ℝ))
      have h := Real.log_le_log (Real.exp_pos _) (show Real.exp (-(1/99 : ℝ)) ≤ 1 - 1 / 100 from by
        have := Real.exp_neg (1 / 99 : ℝ)
        have hexp : (1 + 1 / 99 : ℝ) ≤ Real.exp (1 / 99) := by
          have := Real.add_one_le_exp (1 / 99 : ℝ); linarith
        rw [this]
        rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        calc (1 - 1 / 100 : ℝ)⁻¹ = 1 + 1 / 99 := by norm_num
          _ ≤ _ := hexp)
      rwa [Real.log_exp] at h
    rw [show -(1 - 1 / 100 : ℝ) * (Real.log (1 - 1 / 100) / Real.log 2) =
      (-(99 / 100) * Real.log (1 - 1 / 100)) / Real.log 2 by ring, div_le_iff₀ hl2']
    nlinarith
  unfold binaryEntropy
  linarith

end InfoTheory.Known.Certificates.QuantumLdpcRateDistance
