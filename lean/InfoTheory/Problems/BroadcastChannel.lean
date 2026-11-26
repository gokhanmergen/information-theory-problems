import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.BroadcastChannel

/-- Capacity Region of the General Two-Receiver Broadcast Channel (Cover 1972; Marton 1979):
    Does Marton's single-letter inner bound characterize the full capacity region `C(W)`
    for every finite-alphabet two-receiver discrete memoryless broadcast channel `W`? -/
def Statement : Prop :=
  ∀ (kX kY₁ kY₂ : ℕ) (W : BroadcastChannel (Fin kX) (Fin kY₁) (Fin kY₂)),
    bcCapacityRegion W = martonInnerBound W

def problem : OpenProblem where
  id := "broadcast-channel"
  title := "Capacity Region of the General Two-Receiver Broadcast Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas Cover"
  posedYear := 1972
  statement := Statement

end InfoTheory.Problems.BroadcastChannel
