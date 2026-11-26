import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.ZeroErrorFeedbackVariableLength

/-- Predicate that `y : Fin t → β` is a first-stopping output trajectory under causal
    stopping rule `stop`: it stops at time `t` and at no earlier time `s < t`. -/
def IsStopPath {β : Type*} (stop : ∀ t : ℕ, (Fin t → β) → Bool)
    (t : ℕ) (y : Fin t → β) : Prop :=
  stop t y = true ∧
  ∀ s : Fin t, stop s.1 (fun j => y ⟨j.1, Nat.lt_trans j.2 s.2⟩) = false

/-- Transition probability of output prefix `y : Fin t → β` given message `m : Fin M`
    under causal feedback encoder `enc` over DMC `W`. -/
noncomputable def pathProb {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) {M : ℕ} (enc : ∀ t : ℕ, Fin M → (Fin t → β) → α)
    (m : Fin M) (t : ℕ) (y : Fin t → β) : ℝ :=
  ∏ i : Fin t, W.trans (enc i.1 m (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i)

open Classical in
/-- A zero-error variable-length feedback (VLF) code for `M` messages over `W`:
    terminates almost surely with **finite expected stopping time** (`Summable`) for every
    message `m` (preventing infinite-`E[τ]` codes from getting `tsum = 0`), and decodes
    with zero error on every reachable stopping trajectory. -/
def IsZeroErrorVLFCode {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (M : ℕ)
    (enc : ∀ t : ℕ, Fin M → (Fin t → β) → α)
    (stop : ∀ t : ℕ, (Fin t → β) → Bool)
    (dec : ∀ t : ℕ, (Fin t → β) → Fin M) : Prop :=
  (∀ m : Fin M,
    Summable (fun t : ℕ => ∑ y : Fin t → β,
      if IsStopPath stop t y then pathProb W enc m t y else 0)) ∧
  (∀ m : Fin M,
    ∑' t : ℕ, ∑ y : Fin t → β,
      (if IsStopPath stop t y then pathProb W enc m t y else 0) = 1) ∧
  (∀ m : Fin M,
    Summable (fun t : ℕ => (t : ℝ) * ∑ y : Fin t → β,
      if IsStopPath stop t y then pathProb W enc m t y else 0)) ∧
  (∀ (m : Fin M) (t : ℕ) (y : Fin t → β),
    IsStopPath stop t y → 0 < pathProb W enc m t y → dec t y = m)

open Classical in
/-- Expected stopping time `E[τ]` of a VLF code under equiprobable messages in `Fin M`. -/
noncomputable def expectedStopTime {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (M : ℕ)
    (enc : ∀ t : ℕ, Fin M → (Fin t → β) → α)
    (stop : ∀ t : ℕ, (Fin t → β) → Bool) : ℝ :=
  ((1 : ℝ) / (M : ℝ)) * ∑ m : Fin M,
    ∑' t : ℕ, (t : ℝ) * ∑ y : Fin t → β,
      (if IsStopPath stop t y then pathProb W enc m t y else 0)

/-- Constant Additive Overhead for Zero-Error Variable-Length Feedback Coding
    (Burnashev 1976; Polyanskiy–Poor–Verdú 2011):
    for every finite-alphabet DMC `W` with positive capacity `C(W) > 0` admitting zero-error
    confirmation (`∃ x₁ x₂ y, W(y | x₁) > 0 ∧ W(y | x₂) = 0`), does there exist a constant
    `C₀` depending only on `W` such that for all `M ≥ 2`, there is a zero-error VLF code
    with expected stopping time at most `log₂ M / C(W) + C₀`? -/
def Statement : Prop :=
  ∀ (kX kY : ℕ), 0 < kX → 0 < kY →
    ∀ (W : DMC (Fin kX) (Fin kY)),
      0 < W.capacity →
      (∃ (x₁ x₂ : Fin kX) (y : Fin kY), 0 < W.trans x₁ y ∧ W.trans x₂ y = 0) →
      ∃ C₀ : ℝ, ∀ M : ℕ, 2 ≤ M →
        ∃ (enc : ∀ t : ℕ, Fin M → (Fin t → Fin kY) → Fin kX)
          (stop : ∀ t : ℕ, (Fin t → Fin kY) → Bool)
          (dec : ∀ t : ℕ, (Fin t → Fin kY) → Fin M),
          IsZeroErrorVLFCode W M enc stop dec ∧
          expectedStopTime W M enc stop ≤ log2 (M : ℝ) / W.capacity + C₀

def problem : OpenProblem where
  id := "zero-error-feedback-variable-length"
  title := "Constant Additive Overhead for Zero-Error Variable-Length Feedback Coding"
  category := .zeroError
  status := .open
  posedBy := "Mikhail V. Burnashev; Yury Polyanskiy, H. Vincent Poor, Sergio Verdú"
  posedYear := 2011
  statement := Statement

end InfoTheory.Problems.ZeroErrorFeedbackVariableLength
