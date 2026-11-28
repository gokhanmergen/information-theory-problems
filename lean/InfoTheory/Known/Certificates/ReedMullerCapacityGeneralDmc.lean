import InfoTheory.Problems.ReedMullerCapacityGeneralDmc

/-!
# Certificate for `InfoTheory.Problems.ReedMullerCapacityGeneralDmc`

The frozen statement asks whether plain binary Reed–Muller codes `RM(m, r)` (no coset /
scrambling), under an optimal (block-MAP) decoder, achieve the uniform-input mutual information
`I(U; Y)` of **every** binary-input DMC `W : DMC Bool (Fin k)`.

Certified here, about these exact objects:
* `rmBlockError_nonneg`, `rmBlockError_le_one` — the error functional is a genuine probability
  in `[0, 1]` for every code and decoder (the `C.card = 0` junk branch never fires on RM codes,
  see `zero_mem_code_finset`);
* `reedMullerCode_mono` — `RM(m, r) ≤ RM(m, r')` for `r ≤ r'` (the nested chain);
* `finrank_le` — `dim RM(m, r) ≤ 2^m`, so the rate in `Statement` is at most `1`;
* **regression**: `finrank_rm_zero` — `RM(m, 0)` is the repetition code: dimension `1`, rate
  `2^{-m}`; `one_mem_rm_zero` — it contains the all-ones word.

Not certified: `dim RM(m, r) = ∑_{i ≤ r} C(m, i)` in general, the Kudekar et al. (BEC),
Reeves–Pfister and Abbe–Sandon (BMS) capacity theorems, or anything about asymmetric channels.
The `Statement` is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ReedMullerCapacityGeneralDmc

open InfoTheory InfoTheory.Problems.ReedMullerCapacityGeneralDmc

theorem rmBlockError_nonneg {k : ℕ} (W : DMC Bool (Fin k)) (m : ℕ)
    (C : Finset ((Fin m → ZMod 2) → ZMod 2))
    (dec : ((Fin m → ZMod 2) → Fin k) → ((Fin m → ZMod 2) → ZMod 2)) :
    0 ≤ rmBlockError W m C dec := by
  unfold rmBlockError
  split_ifs
  · exact le_rfl
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun y _ => ?_)
    split_ifs
    · exact Finset.prod_nonneg fun x _ => W.nonneg _ _
    · exact le_rfl

/-- The output law of a fixed codeword sums to one. -/
theorem sum_prod_trans {k : ℕ} (W : DMC Bool (Fin k)) (m : ℕ) (c : (Fin m → ZMod 2) → ZMod 2) :
    ∑ y : (Fin m → ZMod 2) → Fin k, ∏ x : Fin m → ZMod 2, W.trans (decide (c x = 1)) (y x) = 1 := by
  rw [← Fintype.prod_sum (fun x b => W.trans (decide (c x = 1)) b)]
  simp [W.sum_one]

theorem rmBlockError_le_one {k : ℕ} (W : DMC Bool (Fin k)) (m : ℕ)
    (C : Finset ((Fin m → ZMod 2) → ZMod 2))
    (dec : ((Fin m → ZMod 2) → Fin k) → ((Fin m → ZMod 2) → ZMod 2)) :
    rmBlockError W m C dec ≤ 1 := by
  unfold rmBlockError
  split_ifs with h
  · exact zero_le_one
  · have hpos : (0 : ℝ) < C.card := by exact_mod_cast Nat.pos_of_ne_zero h
    have hsum : ∑ c ∈ C, ∑ y : (Fin m → ZMod 2) → Fin k,
        (if dec y ≠ c then ∏ x : Fin m → ZMod 2, W.trans (decide (c x = 1)) (y x) else 0)
          ≤ ∑ c ∈ C, (1 : ℝ) := by
      refine Finset.sum_le_sum fun c _ => ?_
      rw [← sum_prod_trans W m c]
      refine Finset.sum_le_sum fun y _ => ?_
      split_ifs
      · exact le_rfl
      · exact Finset.prod_nonneg fun x _ => W.nonneg _ _
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    rw [one_div, inv_mul_le_iff₀ hpos, mul_one]
    exact hsum

theorem zero_mem_code_finset (m r : ℕ) : (0 : (Fin m → ZMod 2) → ZMod 2) ∈ reedMullerCode m r :=
  Submodule.zero_mem _

theorem reedMullerCode_mono (m : ℕ) {r r' : ℕ} (h : r ≤ r') :
    reedMullerCode m r ≤ reedMullerCode m r' := by
  refine Submodule.span_mono ?_
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, le_trans hS h, rfl⟩

theorem finrank_le (m r : ℕ) :
    Module.finrank (ZMod 2) (reedMullerCode m r) ≤ 2 ^ m := by
  refine le_trans (Submodule.finrank_le _) ?_
  simp [Module.finrank_fintype_fun_eq_card]

theorem rm_zero_eq_span (m : ℕ) :
    reedMullerCode m 0 = Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
  unfold reedMullerCode
  congr 1
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Nat.le_zero, Finset.card_eq_zero]
  constructor
  · rintro ⟨S, rfl, rfl⟩; funext x; simp [rmMonomial]
  · rintro rfl; exact ⟨∅, rfl, by funext x; simp [rmMonomial]⟩

theorem one_mem_rm_zero (m : ℕ) : (fun _ => (1 : ZMod 2)) ∈ reedMullerCode m 0 := by
  rw [rm_zero_eq_span]; exact Submodule.subset_span rfl

/-- `RM(m, 0)` is the repetition code: dimension `1`. -/
theorem finrank_rm_zero (m : ℕ) : Module.finrank (ZMod 2) (reedMullerCode m 0) = 1 := by
  rw [rm_zero_eq_span]
  refine finrank_span_singleton ?_
  intro h
  have := congrFun h (fun _ => 0)
  simp at this

end InfoTheory.Known.Certificates.ReedMullerCapacityGeneralDmc
