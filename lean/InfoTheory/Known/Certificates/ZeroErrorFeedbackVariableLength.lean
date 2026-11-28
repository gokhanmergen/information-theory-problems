import InfoTheory.Problems.ZeroErrorFeedbackVariableLength
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ZeroErrorFeedbackVariableLength`

The frozen statement asks whether every DMC with `C > 0` and a zero transition admits zero-error
variable-length feedback codes with `E[τ] ≤ log₂ M / C + C₀` for all `M ≥ 2`.

## Certified (about exactly these objects)
* `pathProb_nonneg` — path probabilities are nonnegative.
* `isStopPath_fixed_iff` — for the fixed-length stopping rule `stop t _ = (t = n)`, the
  first-stopping trajectories are exactly those of length `n` (the stopping-time encoding
  behaves as intended).
* `noiseless_isZeroErrorVLFCode`, `noiseless_expectedStopTime` — **regression** on the binary
  noiseless channel (`C = 1`): sending the message bit once is a zero-error VLF code (it
  terminates a.s., has finite `E[τ]`, decodes with zero error) with `E[τ] = 1 = log₂ 2 / C`.
  So `IsZeroErrorVLFCode` is satisfiable and the converse `E[τ] ≥ log₂ M / C` is met with
  equality for `M = 2`.
* `noiseless_hyp` — the binary noiseless channel satisfies both hypotheses of `Statement`
  (`C > 0` and a zero transition), and `noiseless_bound_M2` — the bound of `Statement` holds
  for it at `M = 2` with `C₀ = 0`.

## Not certified
* The Wald/Fano converse `E[τ] ≥ log₂ M / C` for general zero-error VLF codes.
* The first-order result (Burnashev 1976) that the zero-error VLF capacity equals `C` when a
  zero transition exists, and any `O(log log M)` overhead achievability.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ZeroErrorFeedbackVariableLength

open InfoTheory InfoTheory.Known InfoTheory.Problems.ZeroErrorFeedbackVariableLength

theorem pathProb_nonneg {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) {M : ℕ}
    (enc : ∀ t : ℕ, Fin M → (Fin t → β) → α) (m : Fin M) (t : ℕ) (y : Fin t → β) :
    0 ≤ pathProb W enc m t y :=
  Finset.prod_nonneg fun _ _ => W.nonneg _ _

/-- The fixed-length stopping rule `stop t _ = (t = n)`. -/
def fixedStop {β : Type*} (n : ℕ) : ∀ t : ℕ, (Fin t → β) → Bool := fun t _ => decide (t = n)

theorem isStopPath_fixed_iff {β : Type*} (n t : ℕ) (y : Fin t → β) :
    IsStopPath (fixedStop n) t y ↔ t = n := by
  unfold IsStopPath fixedStop
  constructor
  · rintro ⟨h, -⟩; simpa using h
  · rintro rfl
    refine ⟨by simp, fun s => ?_⟩
    simpa using s.2.ne

/-! ### Regression: the binary noiseless channel -/

/-- Binary noiseless channel. -/
noncomputable abbrev W2 : DMC (Fin 2) (Fin 2) := noiselessChannel (Fin 2)

/-- Encoder: send the message bit (ignoring feedback). -/
def enc2 : ∀ t : ℕ, Fin 2 → (Fin t → Fin 2) → Fin 2 := fun _ m _ => m

/-- Decoder: read the first output symbol. -/
def dec2 : ∀ t : ℕ, (Fin t → Fin 2) → Fin 2 := fun t y => if h : 0 < t then y ⟨0, h⟩ else 0

open Classical in
theorem term_eq (m : Fin 2) (t : ℕ) :
    (∑ y : Fin t → Fin 2,
      if IsStopPath (fixedStop 1) t y then pathProb W2 enc2 m t y else 0) =
      if t = 1 then 1 else 0 := by
  by_cases ht : t = 1
  · subst ht
    simp only [↓reduceIte]
    have : ∀ y : Fin 1 → Fin 2,
        (if IsStopPath (fixedStop 1) 1 y then pathProb W2 enc2 m 1 y else 0) =
          W2.trans m (y 0) := by
      intro y
      simp only [(isStopPath_fixed_iff 1 1 y).2 rfl, ↓reduceIte]
      simp [pathProb, enc2]
    simp only [this]
    rw [← W2.sum_one m]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ (fun y => rfl)
  · simp only [ht, ↓reduceIte]
    refine Finset.sum_eq_zero fun y _ => ?_
    have hn : ¬ IsStopPath (fixedStop 1) t y := fun h => ht ((isStopPath_fixed_iff 1 t y).1 h)
    simp only [hn, ↓reduceIte]

open Classical in
theorem tterm_eq (m : Fin 2) (t : ℕ) :
    (t : ℝ) * (∑ y : Fin t → Fin 2,
      if IsStopPath (fixedStop 1) t y then pathProb W2 enc2 m t y else 0) =
      if t = 1 then 1 else 0 := by
  rw [term_eq]
  split_ifs with h
  · subst h; simp
  · simp

/-- **Regression:** one-shot transmission is a zero-error VLF code on the noiseless channel. -/
theorem noiseless_isZeroErrorVLFCode : IsZeroErrorVLFCode W2 2 enc2 (fixedStop 1) dec2 := by
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m t y hstop hpos => ?_⟩
  · simp_rw [term_eq]; exact (hasSum_ite_eq 1 (1 : ℝ)).summable
  · simp_rw [term_eq]; exact (hasSum_ite_eq 1 (1 : ℝ)).tsum_eq
  · simp_rw [tterm_eq]; exact (hasSum_ite_eq 1 (1 : ℝ)).summable
  · have ht := (isStopPath_fixed_iff 1 t y).1 hstop
    subst ht
    simp only [pathProb, enc2, Finset.univ_unique, Finset.prod_singleton] at hpos
    have : m = y default := by
      simp only [W2, noiselessChannel] at hpos
      split_ifs at hpos with h
      exacts [h, absurd hpos (lt_irrefl 0)]
    simp [dec2, this]

/-- **Regression:** `E[τ] = 1` for the one-shot code. -/
theorem noiseless_expectedStopTime : expectedStopTime W2 2 enc2 (fixedStop 1) = 1 := by
  unfold expectedStopTime
  simp_rw [tterm_eq, (hasSum_ite_eq 1 (1 : ℝ)).tsum_eq]
  simp

theorem log2_two_nat : log2 ((2 : ℕ) : ℝ) = 1 := by
  unfold log2; push_cast; exact div_self (Real.log_pos one_lt_two).ne'

theorem W2_capacity : W2.capacity = 1 := by
  rw [W2, noiselessChannel_fin_capacity, log2_two_nat]

/-- The binary noiseless channel satisfies the hypotheses of `Statement`. -/
theorem noiseless_hyp : 0 < W2.capacity ∧
    ∃ (x₁ x₂ : Fin 2) (y : Fin 2), 0 < W2.trans x₁ y ∧ W2.trans x₂ y = 0 := by
  refine ⟨by rw [W2_capacity]; norm_num, 0, 1, 0, ?_, ?_⟩ <;> simp [W2, noiselessChannel]

/-- The bound of `Statement` holds for the binary noiseless channel at `M = 2` with `C₀ = 0`. -/
theorem noiseless_bound_M2 :
    ∃ (enc : ∀ t : ℕ, Fin 2 → (Fin t → Fin 2) → Fin 2)
      (stop : ∀ t : ℕ, (Fin t → Fin 2) → Bool) (dec : ∀ t : ℕ, (Fin t → Fin 2) → Fin 2),
      IsZeroErrorVLFCode W2 2 enc stop dec ∧
      expectedStopTime W2 2 enc stop ≤ log2 ((2 : ℕ) : ℝ) / W2.capacity + 0 := by
  refine ⟨enc2, fixedStop 1, dec2, noiseless_isZeroErrorVLFCode, ?_⟩
  rw [noiseless_expectedStopTime, W2_capacity, log2_two_nat]
  norm_num

end InfoTheory.Known.Certificates.ZeroErrorFeedbackVariableLength
