import InfoTheory.Problems.BscReliabilityFunction
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.BscReliabilityFunction`

The frozen statement asks whether, for `BSC(p)` with `0 < p < 1/2` and
`0 < R < 1 - h(p)`, the reliability function equals `max(E_r(R), E_ex(R))`.

## Certified (about exactly these objects)
* `bsc_isPositive` — `BSC(p)` is strictly positive for `0 < p < 1`.
* `randomCodingExponent_le_reliabilityFunction_bsc` — the random-coding lower bound
  `E_r(R) ≤ E(R)` (Gallager 1965, Thm. 1; Bridge `randomCodingExponent_le_reliabilityFunction`).
* `reliabilitySet_bddAbove_bsc` — `E(R)` is a genuine finite supremum.
* `statement_objects_wellDefined` — the defining sets of `E_r(R)` and `E_ex(R)` are bounded
  above (generic `randomCodingSet_bddAbove`, `expurgatedSet_bddAbove`: every
  `E₀(ρ,P) - ρR` and `E_x(ρ,P) - ρR` is `≤ -log₂ min W(y|x)`), so the `max` in `Statement` is
  not a junk value; and `0 ≤ E_r(R) ≤ E(R)` (`randomCodingExponent_nonneg`).
* `reliabilityFunction_nonneg_bsc` — `E(R) ≥ 0`.

## Not certified
* The expurgated lower bound `E_ex(R) ≤ E(R)` (Gallager 1965, Thm. 2): needs the
  expurgation argument, not in `Bridge`.
* The sphere-packing upper bound and tightness above `R_crit` (Shannon–Gallager–Berlekamp
  1967), and the straight-line / MRRW-type bounds below `R_crit`: not in `Bridge`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BscReliabilityFunction

open InfoTheory InfoTheory.Bridge InfoTheory.Problems.BscReliabilityFunction

/-! ### Generic finiteness facts for strictly positive DMCs -/

section Exponents

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A strictly positive DMC has a uniform positive lower bound on its transition probabilities. -/
theorem exists_pos_lower (W : DMC α β) (hW : W.IsPositive) [Nonempty α] [Nonempty β] :
    ∃ c > 0, ∀ x y, c ≤ W.trans x y := by
  obtain ⟨xy, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (α × β))
    (fun xy => W.trans xy.1 xy.2) Finset.univ_nonempty
  exact ⟨_, hW xy.1 xy.2, fun x y => hmin (x, y) (Finset.mem_univ _)⟩

theorem log2_le_log2 {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx h) (Real.log_pos one_lt_two).le

/-- **The random-coding exponent is a genuine (finite) supremum** for strictly positive DMCs
    and `R ≥ 0`: every `E₀(ρ, P) - ρR ≤ -log₂ c`, where `c = min W(y|x) > 0`. -/
theorem randomCodingSet_bddAbove (W : DMC α β) (hW : W.IsPositive) [Nonempty α] [Nonempty β]
    {R : ℝ} (hR : 0 ≤ R) :
    BddAbove { v : ℝ | ∃ (ρ : ℝ) (P : ProbDist α), 0 ≤ ρ ∧ ρ ≤ 1 ∧
      let E0 := -log2 (∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ))
      v = E0 - ρ * R } := by
  obtain ⟨c, hc, hcle⟩ := exists_pos_lower W hW
  refine ⟨-log2 c, ?_⟩
  rintro v ⟨ρ, P, hρ0, hρ1, rfl⟩
  have hs : 0 < 1 / (1 + ρ) := by positivity
  have hin : ∀ y, c ^ (1 / (1 + ρ)) ≤ ∑ x : α, P.pmf x * W.trans x y ^ (1 / (1 + ρ)) := by
    intro y
    calc c ^ (1 / (1 + ρ)) = ∑ x : α, P.pmf x * c ^ (1 / (1 + ρ)) := by
          rw [← Finset.sum_mul, P.sum_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le (hcle x y) hs.le) (P.nonneg x)
  have hout : ∀ y, c ≤ (∑ x : α, P.pmf x * W.trans x y ^ (1 / (1 + ρ))) ^ (1 + ρ) := by
    intro y
    calc c = (c ^ (1 / (1 + ρ))) ^ (1 + ρ) := by
          rw [← Real.rpow_mul hc.le, show 1 / (1 + ρ) * (1 + ρ) = 1 by field_simp, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hc.le _) (hin y) (by linarith)
  obtain ⟨y0⟩ := ‹Nonempty β›
  have hsum : c ≤ ∑ y : β, (∑ x : α, P.pmf x * W.trans x y ^ (1 / (1 + ρ))) ^ (1 + ρ) :=
    le_trans (hout y0) (Finset.single_le_sum (f := fun y =>
      (∑ x : α, P.pmf x * W.trans x y ^ (1 / (1 + ρ))) ^ (1 + ρ))
      (fun y _ => Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
        mul_nonneg (P.nonneg x) (Real.rpow_nonneg (W.nonneg x y) _)) _) (Finset.mem_univ y0))
  have := log2_le_log2 hc hsum
  nlinarith [mul_nonneg hρ0 hR]

/-- **The expurgated exponent is a genuine (finite) supremum** for strictly positive DMCs and
    `R ≥ 0`: every `E_x(ρ, P) - ρR ≤ -log₂ c`, since all Bhattacharyya sums are `≥ c`. -/
theorem expurgatedSet_bddAbove (W : DMC α β) (hW : W.IsPositive) [Nonempty α] [Nonempty β]
    {R : ℝ} (hR : 0 ≤ R) :
    BddAbove { v : ℝ | ∃ (ρ : ℝ) (P : ProbDist α), 1 ≤ ρ ∧
      let Ex := -ρ * log2 (∑ x₁ : α, ∑ x₂ : α, P.pmf x₁ * P.pmf x₂ *
        (∑ y : β, Real.sqrt (W.trans x₁ y * W.trans x₂ y)) ^ (1 / ρ))
      v = Ex - ρ * R } := by
  obtain ⟨c, hc, hcle⟩ := exists_pos_lower W hW
  refine ⟨-log2 c, ?_⟩
  rintro v ⟨ρ, P, hρ1, rfl⟩
  have hρ : 0 < ρ := by linarith
  obtain ⟨y0⟩ := ‹Nonempty β›
  have hB : ∀ x₁ x₂, c ≤ ∑ y : β, Real.sqrt (W.trans x₁ y * W.trans x₂ y) := by
    intro x₁ x₂
    calc c = Real.sqrt (c * c) := (Real.sqrt_mul_self hc.le).symm
      _ ≤ Real.sqrt (W.trans x₁ y0 * W.trans x₂ y0) :=
          Real.sqrt_le_sqrt (mul_le_mul (hcle _ _) (hcle _ _) hc.le (W.nonneg _ _))
      _ ≤ _ := Finset.single_le_sum (f := fun y => Real.sqrt (W.trans x₁ y * W.trans x₂ y))
          (fun y _ => Real.sqrt_nonneg _) (Finset.mem_univ y0)
  have hPP : ∑ x₁ : α, ∑ x₂ : α, P.pmf x₁ * P.pmf x₂ = 1 := by
    simp_rw [← Finset.mul_sum, P.sum_one, mul_one]; exact P.sum_one
  have hsum : c ^ (1 / ρ) ≤ ∑ x₁ : α, ∑ x₂ : α, P.pmf x₁ * P.pmf x₂ *
      (∑ y : β, Real.sqrt (W.trans x₁ y * W.trans x₂ y)) ^ (1 / ρ) := by
    calc c ^ (1 / ρ) = ∑ x₁ : α, ∑ x₂ : α, P.pmf x₁ * P.pmf x₂ * c ^ (1 / ρ) := by
          simp_rw [← Finset.sum_mul]; rw [hPP, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun x₁ _ => Finset.sum_le_sum fun x₂ _ =>
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le (hB x₁ x₂) (by positivity))
            (mul_nonneg (P.nonneg _) (P.nonneg _))
  have hlog := log2_le_log2 (Real.rpow_pos_of_pos hc _) hsum
  have hrp : log2 (c ^ (1 / ρ)) = (1 / ρ) * log2 c := by
    unfold log2; rw [Real.log_rpow hc]; ring
  rw [hrp] at hlog
  have : -ρ * log2 (∑ x₁ : α, ∑ x₂ : α, P.pmf x₁ * P.pmf x₂ *
      (∑ y : β, Real.sqrt (W.trans x₁ y * W.trans x₂ y)) ^ (1 / ρ)) ≤ -log2 c := by
    have h2 := mul_le_mul_of_nonneg_left hlog hρ.le
    rw [← mul_assoc, mul_one_div_cancel hρ.ne', one_mul] at h2
    linarith
  nlinarith [mul_nonneg hρ.le hR]

/-- `E_r(R) ≥ 0` (take `ρ = 0`), for strictly positive DMCs and `R ≥ 0`. -/
theorem randomCodingExponent_nonneg (W : DMC α β) (hW : W.IsPositive) [Nonempty α]
    [Nonempty β] {R : ℝ} (hR : 0 ≤ R) : 0 ≤ randomCodingExponent W R := by
  refine le_csSup (randomCodingSet_bddAbove W hW hR) ⟨0, ProbDist.uniform, le_rfl, zero_le_one, ?_⟩
  dsimp only
  have := gallagerE0_zero (ProbDist.uniform : ProbDist α) W
  unfold gallagerE0 at this
  rw [this]; ring

end Exponents


/-! ### The exact objects of `Statement` -/

section BSC

/-- `BSC(p)` with `0 < p < 1` is strictly positive. -/
theorem bsc_isPositive {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (bsc p h0 h1).IsPositive := by
  intro x y; simp only [bsc]; split_ifs <;> linarith

/-- **Random-coding lower bound** `E_r(R) ≤ E(R)` (Gallager 1965, Thm. 1; Bridge
    `randomCodingExponent_le_reliabilityFunction`) for exactly the channels and rates of
    `Statement`. -/
theorem randomCodingExponent_le_reliabilityFunction_bsc {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1 / 2) {R : ℝ} (hR : 0 < R) :
    randomCodingExponent (bsc p h0 h1) R ≤ reliabilityFunction (bsc p h0 h1) R :=
  randomCodingExponent_le_reliabilityFunction _ (bsc_isPositive h0 h1 hp0 (by linarith)) hR

/-- **`E(R)` is a genuine (finite) supremum**: the set of achievable exponents is bounded
    above (Bridge `reliabilitySet_bddAbove_of_isPositive`). -/
theorem reliabilitySet_bddAbove_bsc {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) {R : ℝ} (hR : 0 < R) :
    BddAbove { E : ℝ | ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      dmcMinError (bsc p h0 h1) n (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))) ≤
        (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) } :=
  reliabilitySet_bddAbove_of_isPositive _ (bsc_isPositive h0 h1 hp0 (by linarith)) hR

/-- **Both exponents on the right-hand side of `Statement` are genuine (finite) suprema**,
    and `0 ≤ E_r(R) ≤ E(R)`: the `max` in `Statement` is not a junk value. -/
theorem statement_objects_wellDefined {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) {R : ℝ} (hR : 0 < R) :
    BddAbove { v : ℝ | ∃ (ρ : ℝ) (P : ProbDist Bool), 0 ≤ ρ ∧ ρ ≤ 1 ∧
      let E0 := -log2 (∑ y : Bool, (∑ x : Bool, P.pmf x *
        ((bsc p h0 h1).trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ))
      v = E0 - ρ * R } ∧
    BddAbove { v : ℝ | ∃ (ρ : ℝ) (P : ProbDist Bool), 1 ≤ ρ ∧
      let Ex := -ρ * log2 (∑ x₁ : Bool, ∑ x₂ : Bool, P.pmf x₁ * P.pmf x₂ *
        (∑ y : Bool, Real.sqrt ((bsc p h0 h1).trans x₁ y * (bsc p h0 h1).trans x₂ y)) ^ (1 / ρ))
      v = Ex - ρ * R } ∧
    0 ≤ randomCodingExponent (bsc p h0 h1) R ∧
    randomCodingExponent (bsc p h0 h1) R ≤ reliabilityFunction (bsc p h0 h1) R := by
  have hpos := bsc_isPositive h0 h1 hp0 (by linarith)
  exact ⟨randomCodingSet_bddAbove _ hpos hR.le, expurgatedSet_bddAbove _ hpos hR.le,
    randomCodingExponent_nonneg _ hpos hR.le,
    randomCodingExponent_le_reliabilityFunction_bsc h0 h1 hp0 hp1 hR⟩

/-- Hence `E(R) ≥ 0` on the whole range of `Statement`. -/
theorem reliabilityFunction_nonneg_bsc {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1 / 2) {R : ℝ} (hR : 0 < R) : 0 ≤ reliabilityFunction (bsc p h0 h1) R :=
  le_trans (statement_objects_wellDefined h0 h1 hp0 hp1 hR).2.2.1
    (statement_objects_wellDefined h0 h1 hp0 hp1 hR).2.2.2

end BSC

end InfoTheory.Known.Certificates.BscReliabilityFunction
