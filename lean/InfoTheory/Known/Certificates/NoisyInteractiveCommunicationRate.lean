import InfoTheory.Problems.NoisyInteractiveCommunicationRate
import InfoTheory.Known.Entropy
import InfoTheory.Bridge.MrsGerber

/-!
# Certificate for `InfoTheory.Problems.NoisyInteractiveCommunicationRate`

The frozen statement: `1 - C_int(ε) = O(h(ε))` as `ε → 0⁺` for adaptive randomized interactive
coding over `BSC(ε)`. Haeupler (FOCS 2014) conjectured instead `1 - Θ(√ε)`; the Statement is
the opposite direction of that conjecture and is open either way. Facts about the *exact*
objects `runNoiseless`, `runAdaptiveNoisyViews`, `interactiveCapacityBSC`:

## Certified
* `runNoiseless_prefix`, `runNoiseless_last`: transcripts are consistent and alternate
  (Alice on even rounds, Bob on odd rounds).
* `bob_receives_xor`, `speaker_hears_nothing`, `views_prefix`: the noisy model is a half-duplex
  BSC — a listener receives the other party's bit XOR the error, a speaker hears nothing.
* `interactiveCapacityBSC_nonneg`: `C_int(ε) ≥ 0`.
* `binaryEntropy_small`, `statement_implies_capacity_to_one`: the right-hand side vanishes, so
  the Statement genuinely asserts `C_int(ε) → 1` with overhead `O(h(ε))`.

## Not certified
* Boundedness `C_int(ε) ≤ 1` (cut-set/Fano over adaptive protocols; needed so the `sSup` is not
  the junk `0`), Haeupler's `1 - O(√ε)` achievability, the Kol–Raz non-adaptive bound.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.NoisyInteractiveCommunicationRate

open InfoTheory InfoTheory.Problems.NoisyInteractiveCommunicationRate

/-! ### The noiseless reference protocol -/

variable {kX kY : ℕ} (alice : (t : ℕ) → Fin kX → (Fin t → Bool) → Bool)
  (bob : (t : ℕ) → Fin kY → (Fin t → Bool) → Bool) (x : Fin kX) (y : Fin kY)

/-- Transcripts are consistent: round `t + 1` extends the round-`t` transcript. -/
theorem runNoiseless_prefix (t : ℕ) (i : ℕ) (hi : i < t) :
    runNoiseless alice bob x y (t + 1) ⟨i, by omega⟩ = runNoiseless alice bob x y t ⟨i, hi⟩ := by
  simp [runNoiseless, hi]

/-- Round `t` is spoken by Alice when `t` is even and by Bob when `t` is odd (alternation). -/
theorem runNoiseless_last (t : ℕ) :
    runNoiseless alice bob x y (t + 1) ⟨t, by omega⟩ =
      if t % 2 = 0 then alice t x (runNoiseless alice bob x y t)
      else bob t y (runNoiseless alice bob x y t) := by
  simp [runNoiseless]

/-! ### The noisy adaptive channel model -/

section Noisy
variable {kX kY kR N : ℕ}
  (alice1 : (t : ℕ) → Fin kX → Fin kR → (Fin t → Option Bool) → Option Bool)
  (bob1 : (t : ℕ) → Fin kY → Fin kR → (Fin t → Option Bool) → Option Bool)
  (x : Fin kX) (y : Fin kY) (r : Fin kR) (e : Fin N → Bool)

/-- One-way round, Alice → Bob: Bob receives Alice's bit XOR the channel error (BSC use). -/
theorem bob_receives_xor (t : ℕ) (ht : t < N) (a : Bool)
    (hA : alice1 t x r (runAdaptiveNoisyViews alice1 bob1 x y r e t).1 = some a)
    (hB : bob1 t y r (runAdaptiveNoisyViews alice1 bob1 x y r e t).2 = none) :
    (runAdaptiveNoisyViews alice1 bob1 x y r e (t + 1)).2 ⟨t, by omega⟩ =
      some (xor a (e ⟨t, ht⟩)) := by
  simp [runAdaptiveNoisyViews, hA, hB, ht]

/-- A transmitting party hears nothing in that round (half-duplex). -/
theorem speaker_hears_nothing (t : ℕ) (a : Bool)
    (hA : alice1 t x r (runAdaptiveNoisyViews alice1 bob1 x y r e t).1 = some a) :
    (runAdaptiveNoisyViews alice1 bob1 x y r e (t + 1)).1 ⟨t, by omega⟩ = none := by
  simp [runAdaptiveNoisyViews, hA]

/-- Views are consistent: round `t + 1` extends the round-`t` views. -/
theorem views_prefix (t i : ℕ) (hi : i < t) :
    (runAdaptiveNoisyViews alice1 bob1 x y r e (t + 1)).1 ⟨i, by omega⟩ =
        (runAdaptiveNoisyViews alice1 bob1 x y r e t).1 ⟨i, hi⟩ ∧
      (runAdaptiveNoisyViews alice1 bob1 x y r e (t + 1)).2 ⟨i, by omega⟩ =
        (runAdaptiveNoisyViews alice1 bob1 x y r e t).2 ⟨i, hi⟩ := by
  simp [runAdaptiveNoisyViews, hi]

end Noisy

/-! ### The capacity functional -/

/-- Every rate in the defining set is `≥ 0`, so `C_int(ε) ≥ 0` (no negative junk). -/
theorem interactiveCapacityBSC_nonneg (ε : ℝ) : 0 ≤ interactiveCapacityBSC ε :=
  Real.sSup_nonneg (fun _ hR => hR.1)

/-- `h(ε) → 0` as `ε → 0⁺`: the Statement's right-hand side vanishes, so the Statement is a
    genuine claim about `C_int(ε) → 1` at rate `O(h(ε))`. -/
theorem binaryEntropy_small {η : ℝ} (hη : 0 < η) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε, 0 ≤ ε → ε < ε₁ → binaryEntropy ε < η := by
  have hc := Bridge.binaryEntropy_continuousOn 0 ⟨le_rfl, zero_le_one⟩
  have h0 : binaryEntropy 0 = 0 := by simp [binaryEntropy, negPLogP, log2]
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hball⟩ := hc η hη
  refine ⟨min δ 1, lt_min hδ one_pos, fun ε he0 he1 => ?_⟩
  have hd : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg he0]; exact lt_of_lt_of_le he1 (min_le_left _ _)
  have := hball ⟨he0, le_of_lt (lt_of_lt_of_le he1 (min_le_right _ _))⟩ hd
  rw [h0, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

/-- **Consequence of the Statement (sanity).** If the Statement holds then
    `C_int(ε) → 1` as `ε → 0⁺`, the known behaviour (Haeupler 2014 proves
    `C_int(ε) ≥ 1 - O(√ε)`; this direction is not formalized here). -/
theorem statement_implies_capacity_to_one (hS : Statement) {η : ℝ} (hη : 0 < η) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε, 0 < ε → ε < ε₁ → 1 - η ≤ interactiveCapacityBSC ε := by
  obtain ⟨C, ε₀, hC, hε₀, -, hbound⟩ := hS
  obtain ⟨ε₁, hε₁, hsmall⟩ := binaryEntropy_small (div_pos hη hC)
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun ε he0 he1 => ?_⟩
  have h1 := hbound ε he0 (lt_of_lt_of_le he1 (min_le_left _ _))
  have h2 := hsmall ε he0.le (lt_of_lt_of_le he1 (min_le_right _ _))
  have h3 : C * binaryEntropy ε < η := by
    have := mul_lt_mul_of_pos_left h2 hC
    rwa [mul_div_cancel₀ _ hC.ne'] at this
  linarith

end InfoTheory.Known.Certificates.NoisyInteractiveCommunicationRate
