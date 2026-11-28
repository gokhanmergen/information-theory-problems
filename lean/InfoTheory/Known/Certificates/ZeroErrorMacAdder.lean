import InfoTheory.Problems.ZeroErrorMacAdder
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ZeroErrorMacAdder`

The frozen statement asks whether the zero-error sum capacity of the binary adder MAC,
`zeroErrorAdderMACSumCapacity` (an `sSup` of rates of nonempty uniquely decodable code pairs),
is *attained* by some finite code pair. The docstring brackets the capacity in
`[≈ 1.3186, ≈ 1.480]`.

Certified here, about the exact object `zeroErrorAdderMACSumCapacity` used in `Statement`
(reusing `InfoTheory.Known`):
* `rateSet_nonempty`, `rateSet_bddAbove` — the `sSup` is over a nonempty set bounded above, so it
  is a genuine supremum (not a junk value);
* `rate_le_capacity` — every code pair's rate is `≤` the capacity;
* `statement_iff` — `Statement ↔` the supremum belongs to the set of achievable rates (i.e. it
  is a maximum), confirming the formalization matches the question asked;
* `known_bounds` — `(1 + log₂ 3)/2 ≤ C ≤ log₂ 3`: lower bound from the length-2 pair
  `A = {00, 11}`, `B = {00, 01, 10}` (Kasami–Lin, *Coding for a multiple-access channel*,
  IEEE Trans. Inform. Theory 22 (1976)), upper bound from `|A|·|B| ≤ 3^n` (the output alphabet
  has three letters);
* `one_lt_capacity`, `capacity_lt_two` — hence `1 < C < 2`.

Not certified: the docstring's numerical bracket `[≈ 1.3186, ≈ 1.480]`. These are literature
claims (lower bound from computer-found codes, e.g. Mattas–Östergård 2005; upper bound from
entropy/combinatorial arguments, Urbanke–Li 1998 and later work) which are *not* checked here;
they are consistent with the certified bracket `[(1+log₂3)/2 ≈ 1.2925, log₂3 ≈ 1.585]`.
An exhaustive search (outside Lean) over all code pairs of length `n ≤ 4` found no pair beating
rate `(1+log₂3)/2`, so improving the certified lower bound needs longer codes. The upper bound
`3/2` (Shannon sum capacity) would require an entropy argument that is not formalised here.
The `Statement` itself is not settled by these facts.

* **Regression** (exact small-blocklength optima, Kasami–Lin 1976): `regression_n1` — at
  `n = 1` every uniquely decodable pair has `|A|·|B| ≤ 2` (sum rate `1`), attained by
  `({0,1}, {0})`; `regression_n2` — at `n = 2` every pair has `|A|·|B| ≤ 6`, attained by the
  Kasami–Lin pair `({00,11}, {00,01,10})` (sum rate `(1 + log₂ 3)/2`). Both upper bounds are
  exhaustive checks by `decide` over all code pairs, using the exact predicate `IsAdderMACCode`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ZeroErrorMacAdder

open InfoTheory InfoTheory.Known

/-- The set of achievable sum rates whose `sSup` is `zeroErrorAdderMACSumCapacity`. -/
abbrev rateSet : Set ℝ :=
  { r : ℝ | ∃ (n : ℕ) (A B : Finset (Fin n → Fin 2)),
    0 < n ∧ A.Nonempty ∧ B.Nonempty ∧ IsAdderMACCode n A B ∧
    r = (log2 (A.card : ℝ) + log2 (B.card : ℝ)) / (n : ℝ) }

theorem rateSet_bddAbove : BddAbove rateSet := zeroErrorAdderMAC_set_bddAbove

theorem rateSet_nonempty : rateSet.Nonempty :=
  ⟨_, 1, Finset.univ, {fun _ => 0}, one_pos, Finset.univ_nonempty, by simp,
    isAdderMACCode_silent 1, rfl⟩

/-- Every uniquely decodable code pair has rate at most the capacity. -/
theorem rate_le_capacity {n : ℕ} {A B : Finset (Fin n → Fin 2)} (hn : 0 < n)
    (hA : A.Nonempty) (hB : B.Nonempty) (h : IsAdderMACCode n A B) :
    (log2 (A.card : ℝ) + log2 (B.card : ℝ)) / (n : ℝ) ≤ zeroErrorAdderMACSumCapacity :=
  le_csSup rateSet_bddAbove ⟨n, A, B, hn, hA, hB, h, rfl⟩

/-- The statement says exactly that the supremum is attained (is a maximum). -/
theorem statement_iff :
    InfoTheory.Problems.ZeroErrorMacAdder.Statement ↔
      zeroErrorAdderMACSumCapacity ∈ rateSet := by
  constructor
  · rintro ⟨n, A, B, hn, hA, hB, h, he⟩
    exact ⟨n, A, B, hn, hA, hB, h, he.symm⟩
  · rintro ⟨n, A, B, hn, hA, hB, h, he⟩
    exact ⟨n, A, B, hn, hA, hB, h, he.symm⟩

/-- Certified bracket `(1 + log₂ 3)/2 ≤ C ≤ log₂ 3`. -/
theorem known_bounds :
    (1 + log2 3) / 2 ≤ zeroErrorAdderMACSumCapacity ∧
      zeroErrorAdderMACSumCapacity ≤ log2 3 :=
  ⟨one_add_log2_three_div_two_le_zeroErrorAdderMACSumCapacity,
    zeroErrorAdderMACSumCapacity_le_log2_three⟩

private lemma one_lt_log2_three : 1 < log2 3 := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [log2, lt_div_iff₀ hL, one_mul]
  exact Real.log_lt_log two_pos (by norm_num)

private lemma log2_three_lt_two : log2 3 < 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [log2, div_lt_iff₀ hL, ← Real.log_rpow two_pos]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `1 < C`: the capacity strictly beats time sharing with a silent user. -/
theorem one_lt_capacity : 1 < zeroErrorAdderMACSumCapacity := by
  have := one_lt_log2_three
  linarith [known_bounds.1]

/-- `C < 2`. -/
theorem capacity_lt_two : zeroErrorAdderMACSumCapacity < 2 :=
  known_bounds.2.trans_lt log2_three_lt_two

/-! ### Regression: exact optima at blocklengths `1` and `2` -/

/-- Decidability of `IsAdderMACCode`. -/
@[instance_reducible] def decIsAdderMACCode (n : ℕ) (A B : Finset (Fin n → Fin 2)) :
    Decidable (IsAdderMACCode n A B) := by
  unfold IsAdderMACCode; exact Finset.decidableDforallFinset

attribute [local instance] decIsAdderMACCode

/-- **Regression** (`n = 1`): the best uniquely decodable pair has `|A|·|B| = 2`. -/
theorem regression_n1 :
    (∃ A B : Finset (Fin 1 → Fin 2), IsAdderMACCode 1 A B ∧ A.card * B.card = 2) ∧
      ∀ A B : Finset (Fin 1 → Fin 2), IsAdderMACCode 1 A B → A.card * B.card ≤ 2 :=
  ⟨⟨Finset.univ, {fun _ => 0}, by decide, by decide⟩, by decide⟩

/-- **Regression** (`n = 2`, Kasami–Lin 1976): the best uniquely decodable pair has
`|A|·|B| = 6`, e.g. `A = {00, 11}`, `B = {00, 01, 10}`. -/
theorem regression_n2 :
    (∃ A B : Finset (Fin 2 → Fin 2), IsAdderMACCode 2 A B ∧ A.card * B.card = 6) ∧
      ∀ A B : Finset (Fin 2 → Fin 2), IsAdderMACCode 2 A B → A.card * B.card ≤ 6 :=
  ⟨⟨{![0, 0], ![1, 1]}, {![0, 0], ![0, 1], ![1, 0]}, by decide, by decide⟩, by decide⟩

end InfoTheory.Known.Certificates.ZeroErrorMacAdder
