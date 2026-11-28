import InfoTheory.Problems.GilbertVarshamovBinary
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.GilbertVarshamovBinary`

**Outcome: the `Statement` is faithful.** It is neither forced true nor forced false by the
definitions.

The `Statement` compares exactly `asymptoticCodeRate 2 δ` with `gilbertVarshamov δ = 1 - h(δ)`.
`asymptoticCodeRate` is the `limsup` form: the `sInf` of eventual upper bounds of
`(1/n) log₂ A_2(n, ⌈δn⌉)`. That is the rate quantity in the problem, so no bridging lemma is
needed (`statement_iff` is `Iff.rfl`). The `sInf` is over a set that is nonempty and bounded
below (`rate_set_bddBelow`; nonemptiness is in `Known.asymptoticCodeRate_two_mem_Icc`), so it
is not junk.

Certified, for `0 < δ < 1/2`:
* `gilbertVarshamov_le_asymptoticCodeRate` (reused from `InfoTheory.Known.Coding`): the known
  half `1 - h(δ) ≤ R_2(δ)` (Gilbert 1952, Varshamov 1957; MacWilliams–Sloane, *The Theory of
  Error-Correcting Codes*, Ch. 17 Thm 30).
* `asymptoticCodeRate_two_le_one_sub`: the asymptotic Singleton bound `R_2(δ) ≤ 1 - δ` (for
  `0 < δ ≤ 1`). It is derived from `Known.singleton_bound` (Singleton 1964; MacWilliams–Sloane
  Ch. 1 Thm 11).
* `lt_binaryEntropy` / `gilbertVarshamov_lt_one_sub`: `δ < h(δ)`, so `1 - h(δ) < 1 - δ`.
* `gilbertVarshamov_sandwich`: `1 - h(δ) ≤ R_2(δ) ≤ 1 - δ` with `1 - h(δ) < 1 - δ`. So the
  equality in the `Statement` is genuinely open with respect to these bounds.

* **Regression** (solved endpoints): `regression_rate_zero` — `R_2(0) = 1`, and
  `regression_statement_eq_at_zero` — the `Statement`'s equation `R_2(δ) = 1 - h(δ)` holds at
  the excluded boundary `δ = 0` (both sides are `1`); `regression_rate_one` — `R_2(1) = 0`
  (only two codewords at distance `n`).

Not certified:
* The asymptotic Hamming bound `R_2(δ) ≤ 1 - h(δ/2)` (MacWilliams–Sloane Ch. 17 §7). The finite
  bound is `Known.hamming_bound`. The asymptotic form also needs the lower estimate
  `C(n, t) ≥ 2^{n h(t/n)}/(n+1)` and continuity of `h`; we did not formalize these.
* The Elias–Bassalygo and McEliece–Rodemich–Rumsey–Welch (1977) upper bounds. MRRW needs
  Delsarte's linear-programming bound, which is far out of reach.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.GilbertVarshamovBinary

open InfoTheory InfoTheory.Known

/-- The frozen statement compares exactly `asymptoticCodeRate 2 δ` with `1 - h(δ)`. -/
theorem statement_iff : InfoTheory.Problems.GilbertVarshamovBinary.Statement ↔
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → asymptoticCodeRate 2 δ = 1 - binaryEntropy δ := Iff.rfl

/-- The set whose `sInf` defines `R_2(δ)` is bounded below by `0`. -/
theorem rate_set_bddBelow (δ : ℝ) : BddBelow {r : ℝ | ∃ N : ℕ, ∀ n ≥ N,
    (Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log ((2 : ℕ) : ℝ)) / (n : ℝ)
      ≤ r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨N, hN⟩
  have := hN N le_rfl
  have h0 := (binary_rate_term_mem_Icc N (Nat.ceil (δ * (N : ℝ)))).1
  push_cast at this
  linarith

/-- Per-blocklength Singleton estimate: `(1/n) log₂ A_2(n, ⌈δn⌉) ≤ 1 - δ + 1/n`. -/
theorem singleton_term_le {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log 2) / (n : ℝ)
      ≤ 1 - δ + 1 / n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set d := Nat.ceil (δ * (n : ℝ)) with hd
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hdn : d ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hS := singleton_bound (q := 2) hd1 hdn
  have hA1 := one_le_maxCodeSize (q := 2) (by norm_num) n d
  have hlog : Real.log (maxCodeSize 2 n d : ℝ) ≤ ((n - d + 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast hA1) (by exact_mod_cast hS)
  have hcast : ((n - d + 1 : ℕ) : ℝ) = n - d + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hdn, Nat.cast_one]
  have hdge : δ * n ≤ d := Nat.le_ceil _
  rw [hcast] at hlog
  rw [div_le_iff₀ hnpos, div_le_iff₀ hl2]
  have : (1 - δ + 1 / n) * n = n - δ * n + 1 := by
    rw [add_mul, one_div, inv_mul_cancel₀ hnpos.ne']; ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_right hdge hl2.le]

/-- **Asymptotic Singleton bound** (MacWilliams–Sloane, Ch. 1 Thm 11 and Ch. 17 §7):
`R_2(δ) ≤ 1 - δ` for `0 < δ ≤ 1`. -/
theorem asymptoticCodeRate_two_le_one_sub {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    asymptoticCodeRate 2 δ ≤ 1 - δ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  unfold asymptoticCodeRate
  refine csInf_le (rate_set_bddBelow δ) ⟨N + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have := singleton_term_le h0 h1 hn1
  have h2 : (1 : ℝ) / n ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hn
  push_cast
  linarith

/-- `δ < h(δ)` on `(0, 1/2)`: indeed `h(δ) ≥ δ log₂ (1/δ) > δ`. -/
theorem lt_binaryEntropy {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) : δ < binaryEntropy δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog : Real.log δ < -Real.log 2 := by
    rw [← Real.log_inv]; exact Real.log_lt_log h0 (by norm_num; linarith)
  have hA : negPLogP δ = -δ * log2 δ := by simp [negPLogP, not_le.mpr h0]
  have hB : 0 ≤ negPLogP (1 - δ) := InfoTheory.Bridge.negPLogP_nonneg (by linarith)
  have hC : log2 δ < -1 := by unfold log2; rw [div_lt_iff₀ hl2]; linarith
  unfold binaryEntropy; rw [hA]; nlinarith

/-- The GV value lies strictly below the Singleton value: `1 - h(δ) < 1 - δ` on `(0, 1/2)`. -/
theorem gilbertVarshamov_lt_one_sub {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    gilbertVarshamov δ < 1 - δ := by
  unfold gilbertVarshamov; linarith [lt_binaryEntropy h0 h1]

/-- **Sandwich.** For `δ ∈ (0, 1/2)`: `1 - h(δ) ≤ R_2(δ) ≤ 1 - δ`, and `1 - h(δ) < 1 - δ`.
So the definitions neither force the equality of the `Statement` nor refute it. -/
theorem gilbertVarshamov_sandwich {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    gilbertVarshamov δ ≤ asymptoticCodeRate 2 δ ∧ asymptoticCodeRate 2 δ ≤ 1 - δ ∧
      gilbertVarshamov δ < 1 - δ :=
  ⟨gilbertVarshamov_le_asymptoticCodeRate h0 h1,
    asymptoticCodeRate_two_le_one_sub h0 (by linarith), gilbertVarshamov_lt_one_sub h0 h1⟩

/-! ### Regression: solved endpoint values -/

/-- **Regression**: `R_2(0) = 1` (with no distance constraint every word is a codeword). -/
theorem regression_rate_zero : asymptoticCodeRate 2 0 = 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hterm : ∀ n : ℕ, 1 ≤ n →
      (Real.log (maxCodeSize 2 n (Nat.ceil ((0 : ℝ) * (n : ℝ))) : ℝ) /
        Real.log ((2 : ℕ) : ℝ)) / (n : ℝ) = 1 := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [zero_mul, Nat.ceil_zero, maxCodeSize_zero]
    push_cast
    rw [Real.log_pow, mul_div_assoc, div_self hl2.ne', mul_one, div_self hnpos.ne']
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ N : ℕ, ∀ n ≥ N,
      (Real.log (maxCodeSize 2 n (Nat.ceil ((0 : ℝ) * (n : ℝ))) : ℝ) /
        Real.log ((2 : ℕ) : ℝ)) / (n : ℝ) ≤ r} := by
    refine ⟨0, fun n _ => ?_⟩
    have := (binary_rate_term_mem_Icc n (Nat.ceil ((0 : ℝ) * (n : ℝ)))).2
    push_cast at this ⊢
    exact this
  unfold asymptoticCodeRate
  refine le_antisymm (csInf_le (rate_set_bddBelow 0) hmem) (le_csInf ⟨1, hmem⟩ ?_)
  rintro r ⟨N, hN⟩
  have := hN (max N 1) (le_max_left _ _)
  rwa [hterm _ (le_max_right _ _)] at this

/-- **Regression**: the `Statement`'s equation holds at the excluded boundary `δ = 0`. -/
theorem regression_statement_eq_at_zero : asymptoticCodeRate 2 0 = gilbertVarshamov 0 := by
  rw [regression_rate_zero]
  simp [gilbertVarshamov, binaryEntropy, negPLogP, log2]

/-- **Regression**: `R_2(1) = 0`. -/
theorem regression_rate_one : asymptoticCodeRate 2 1 = 0 :=
  le_antisymm (by simpa using asymptoticCodeRate_two_le_one_sub (δ := 1) one_pos le_rfl)
    (asymptoticCodeRate_two_mem_Icc 1).1

end InfoTheory.Known.Certificates.GilbertVarshamovBinary
