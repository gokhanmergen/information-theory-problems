import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.DeletionChannel

/-- Capacity of the Binary Deletion Channel (Dobrushin 1967; Mitzenmacher 2009):
    A central open structural conjecture on `C(d)` is that the binary deletion channel
    capacity `d ↦ C(d)` is convex on `(0, 1)` (Mitzenmacher 2009, Open Problem 1;
    which would in particular imply tight linear interpolation bounds across all `d ∈ (0, 1)`). -/
def Statement : Prop :=
  ∀ (d₁ d₂ t : ℝ),
    0 < d₁ → d₁ < 1 → 0 < d₂ → d₂ < 1 → 0 ≤ t → t ≤ 1 →
    binaryDeletionCapacity (t * d₁ + (1 - t) * d₂) ≤
      t * binaryDeletionCapacity d₁ + (1 - t) * binaryDeletionCapacity d₂

def problem : OpenProblem where
  id := "deletion-channel"
  title := "Capacity of the Binary Deletion Channel"
  category := .channelCapacity
  status := .open
  posedBy := "folklore since Dobrushin"
  posedYear := 1967
  statement := Statement

end InfoTheory.Problems.DeletionChannel
