import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.TwoWayChannelCapacity

/-- A `k`-step causal adaptive encoding strategy mapping past outputs to the next input. -/
abbrev CausalStrat (k : ℕ) (X Y : Type*) :=
  ∀ i : Fin k, (Fin i.1 → Y) → X

open Classical in
/-- Shannon's `k`-block strategy inner bound `G_k(W)` for a discrete memoryless two-way
    channel `W` (Shannon 1961, Theorem 1). For `k = 1` this reduces to Shannon's
    single-letter inner bound; as `k → ∞` its closure equals `twcCapacityRegion W`. -/
def twcKLetterInnerBound {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (k : ℕ) (W : TwoWayChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kQ : ℕ) (Pq : ProbDist (Fin kQ))
      (Ps₁ : Fin kQ → ProbDist (CausalStrat k X₁ Y₁))
      (Ps₂ : Fin kQ → ProbDist (CausalStrat k X₂ Y₂))
      (J : ProbDist (Fin kQ × CausalStrat k X₁ Y₁ × CausalStrat k X₂ Y₂ ×
        (Fin k → Y₁ × Y₂))),
      (∀ q s₁ s₂ y,
        J.pmf (q, s₁, s₂, y) =
          Pq.pmf q * (Ps₁ q).pmf s₁ * (Ps₂ q).pmf s₂ *
          ∏ i : Fin k,
            W.trans
              (s₁ i (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).1),
               s₂ i (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).2))
              (y i)) ∧
      r.1 ≤ (1 / (k : ℝ)) *
        condMutualInfo (J.map (fun t => (t.2.1, (fun i => (t.2.2.2 i).2), (t.2.2.1, t.1)))) ∧
      r.2 ≤ (1 / (k : ℝ)) *
        condMutualInfo (J.map (fun t => (t.2.2.1, (fun i => (t.2.2.2 i).1), (t.2.1, t.1)))) }

/-- Capacity Region of Shannon's Discrete Memoryless Two-Way Channel (Shannon 1961):
    Does every finite-alphabet discrete memoryless two-way channel achieve its exact
    capacity region at some finite strategy horizon `k ≥ 1`? -/
def Statement : Prop :=
  ∀ (kX₁ kX₂ kY₁ kY₂ : ℕ) (W : TwoWayChannel (Fin kX₁) (Fin kX₂) (Fin kY₁) (Fin kY₂)),
    ∃ k : ℕ, 0 < k ∧ twcCapacityRegion W = twcKLetterInnerBound k W

def problem : OpenProblem where
  id := "two-way-channel-capacity"
  title := "Capacity Region of Shannon's Discrete Memoryless Two-Way Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Claude E. Shannon"
  posedYear := 1961
  statement := Statement

end InfoTheory.Problems.TwoWayChannelCapacity
