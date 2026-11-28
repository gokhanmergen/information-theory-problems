import InfoTheory.Problems.LogSobolevHypercubeSharp
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.LogSobolevHypercubeSharp`

The frozen statement is the Fourier Entropy–Influence (FEI) conjecture of Friedgut–Kalai
(1996): `∃ C > 0, ∀ n f, H(f̂²) ≤ C · I(f)` for Boolean `f : {0,1}^n → {±1}`.

## Certified (about exactly these objects)
* `abs_fourierCoeff_le_one`, `fourierEntropy_nonneg`, `totalInfluence_nonneg` — every
  Walsh coefficient lies in `[-1, 1]`, so `H(f̂²) ≥ 0`; and `I(f) ≥ 0`. Both sides of the
  conjectured inequality are genuine nonnegative reals.
* `fourierCoeff_and2`, `fourierEntropy_and2 : H(f̂²) = 2`, `totalInfluence_and2 : I(f) = 1` —
  **regression** for the 2-bit AND (`f = -1` iff both bits are `1`): all four squared
  coefficients equal `1/4` (O'Donnell 2014, Ex. 1.1), so `H/I = 2`.
* `two_le_of_FEI` — consequently any constant `C` that works in `Statement` satisfies
  `C ≥ 2`; the statement is not vacuous for small `C`.
* `fourierEntropy_dict`, `totalInfluence_dict` — **regression** for the 1-bit dictator:
  `H = 0`, `I = 1` (FEI holds trivially for dictators).

## Not certified
* Parseval `∑_S f̂(S)² = 1`, the trivial bound `H ≤ I · log n + O(I)`, Hod's (2018) lower bound
  `C ≥ 6.278…`, and FEI for special classes (symmetric functions, read-once formulas, …).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.LogSobolevHypercubeSharp

open InfoTheory InfoTheory.Problems.LogSobolevHypercubeSharp

theorem abs_parityChar_eq_one {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    |parityChar S x| = 1 := by
  unfold parityChar
  rw [Finset.abs_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs <;> simp

/-- Every Walsh–Fourier coefficient of a `±1`-valued function lies in `[-1, 1]`. -/
theorem abs_fourierCoeff_le_one (n : ℕ) (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) :
    |fourierCoeff n f S| ≤ 1 := by
  unfold fourierCoeff
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ n)]
  have hsum : |∑ x : Fin n → Bool, (if f x then (1 : ℝ) else -1) * parityChar S x| ≤ 2 ^ n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ x : Fin n → Bool, |(if f x then (1 : ℝ) else -1) * parityChar S x| = 1 := by
      intro x
      rw [abs_mul, abs_parityChar_eq_one]
      split_ifs <;> simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  calc 1 / 2 ^ n * |∑ x : Fin n → Bool, (if f x then (1 : ℝ) else -1) * parityChar S x|
      ≤ 1 / 2 ^ n * 2 ^ n := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

theorem negPLogP_nonneg_of_le_one {p : ℝ} (hp : p ≤ 1) : 0 ≤ negPLogP p := by
  unfold negPLogP
  split_ifs with h
  · exact le_rfl
  · rw [not_le] at h
    unfold log2
    have : Real.log p ≤ 0 := Real.log_nonpos h.le hp
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have : Real.log p / Real.log 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg this h2.le
    nlinarith

/-- `H(f̂²) ≥ 0`. -/
theorem fourierEntropy_nonneg (n : ℕ) (f : (Fin n → Bool) → Bool) : 0 ≤ fourierEntropy n f := by
  refine Finset.sum_nonneg fun S _ => negPLogP_nonneg_of_le_one ?_
  have := abs_fourierCoeff_le_one n f S
  rw [← sq_abs]
  nlinarith [abs_nonneg (fourierCoeff n f S)]

/-- `I(f) ≥ 0`. -/
theorem totalInfluence_nonneg (n : ℕ) (f : (Fin n → Bool) → Bool) : 0 ≤ totalInfluence n f :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-! ### Regression: the 2-bit AND function -/

/-- The 2-bit AND in `±1` form: `f(x) = -1` (encoded `false`) iff `x₀ = x₁ = 1`. -/
def and2 : (Fin 2 → Bool) → Bool := fun x => !(x 0 && x 1)

theorem univ_cube2 : (Finset.univ : Finset (Fin 2 → Bool)) =
    {![false, false], ![false, true], ![true, false], ![true, true]} := by decide

theorem univ_subsets2 : (Finset.univ : Finset (Finset (Fin 2))) =
    {∅, {0}, {1}, {0, 1}} := by decide

theorem fourierCoeff_and2 (S : Finset (Fin 2)) : (fourierCoeff 2 and2 S) ^ 2 = 1 / 4 := by
  have hS : S ∈ ({∅, {0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) := by
    rw [← univ_subsets2]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl <;>
    simp [fourierCoeff, univ_cube2, parityChar, and2, Finset.sum_insert] <;> norm_num

theorem negPLogP_quarter : negPLogP (1 / 4) = 1 / 2 := by
  unfold negPLogP log2
  have hq : ¬ ((1 : ℝ) / 4 ≤ 0) := by norm_num
  simp only [hq, ↓reduceIte]
  have h4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4]
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp
  ring

/-- **Regression:** `H(\widehat{AND}²) = 2` bits. -/
theorem fourierEntropy_and2 : fourierEntropy 2 and2 = 2 := by
  unfold fourierEntropy
  simp only [fourierCoeff_and2, negPLogP_quarter, Finset.sum_const, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **Regression:** `I(AND) = 1`. -/
theorem totalInfluence_and2 : totalInfluence 2 and2 = 1 := by
  unfold totalInfluence
  simp only [fourierCoeff_and2]
  rw [univ_subsets2, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  norm_num

/-- Any constant `C` valid in `Statement` must satisfy `C ≥ 2` (2-bit AND). -/
theorem two_le_of_FEI {C : ℝ}
    (hC : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), fourierEntropy n f ≤ C * totalInfluence n f) :
    2 ≤ C := by
  have := hC 2 and2
  rw [fourierEntropy_and2, totalInfluence_and2, mul_one] at this
  exact this

/-! ### Regression: the 1-bit dictator -/

/-- The dictator `f(x) = (-1)^{x₀}` (encoded `true ↦ +1` when `x₀ = 0`). -/
def dict1 : (Fin 1 → Bool) → Bool := fun x => !(x 0)

theorem univ_cube1 : (Finset.univ : Finset (Fin 1 → Bool)) = {![false], ![true]} := by decide

theorem univ_subsets1 : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide

theorem fourierCoeff_dict1_empty : fourierCoeff 1 dict1 ∅ = 0 := by
  simp [fourierCoeff, univ_cube1, parityChar, dict1]

theorem fourierCoeff_dict1_single : fourierCoeff 1 dict1 {0} = 1 := by
  simp [fourierCoeff, univ_cube1, parityChar, dict1]; norm_num

theorem fourierEntropy_dict : fourierEntropy 1 dict1 = 0 := by
  unfold fourierEntropy
  rw [univ_subsets1, Finset.sum_insert (by decide), Finset.sum_singleton,
    fourierCoeff_dict1_empty, fourierCoeff_dict1_single]
  simp [negPLogP, log2]

theorem totalInfluence_dict : totalInfluence 1 dict1 = 1 := by
  unfold totalInfluence
  rw [univ_subsets1, Finset.sum_insert (by decide), Finset.sum_singleton,
    fourierCoeff_dict1_empty, fourierCoeff_dict1_single]
  simp

end InfoTheory.Known.Certificates.LogSobolevHypercubeSharp
