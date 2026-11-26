import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.MacWithFeedback

/-- A `k`-step causal feedback encoding strategy for one user of a DM-MAC. -/
abbrev MACFeedbackStrat (k : ℕ) (X Y : Type*) :=
  ∀ i : Fin k, (Fin i.1 → Y) → X

open Classical in
/-- The `k`-letter Cover–Leung achievable region `R_CL^(k)(W)` for a DM-MAC with noiseless
    feedback. For `k = 1` this coincides with `coverLeungRegion W`; its closure over `k ≥ 1`
    equals `macFeedbackCapacityRegion W` (Kramer 1998). -/
def coverLeungKLetterRegion {X₁ X₂ Y : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y]
    (k : ℕ) (W : MACChannel X₁ X₂ Y) : Set (ℝ × ℝ) :=
  closure { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU : ℕ) (Pu : ProbDist (Fin kU))
      (Ps₁ : Fin kU → ProbDist (MACFeedbackStrat k X₁ Y))
      (Ps₂ : Fin kU → ProbDist (MACFeedbackStrat k X₂ Y))
      (J : ProbDist (Fin kU × MACFeedbackStrat k X₁ Y × MACFeedbackStrat k X₂ Y ×
        (Fin k → Y))),
      (∀ u s₁ s₂ y,
        J.pmf (u, s₁, s₂, y) =
          Pu.pmf u * (Ps₁ u).pmf s₁ * (Ps₂ u).pmf s₂ *
          ∏ i : Fin k,
            W.trans
              (s₁ i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
               s₂ i (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩))
              (y i)) ∧
      r.1 ≤ (1 / (k : ℝ)) *
        condMutualInfo (J.map (fun t => (t.2.1, t.2.2.2, (t.2.2.1, t.1)))) ∧
      r.2 ≤ (1 / (k : ℝ)) *
        condMutualInfo (J.map (fun t => (t.2.2.1, t.2.2.2, (t.2.1, t.1)))) ∧
      r.1 + r.2 ≤ (1 / (k : ℝ)) *
        mutualInfo (J.map (fun t => ((t.2.1, t.2.2.1), t.2.2.2))) }

/-- Capacity Region of the Multiple-Access Channel with Noiseless Feedback
    (Gaarder–Wolf 1975; Cover–Leung 1981; Bross–Lapidoth 2005):
    Does every finite-alphabet two-user DM-MAC with noiseless feedback achieve its exact
    capacity region at some finite strategy horizon `k ≥ 1`? -/
def Statement : Prop :=
  ∀ (kX₁ kX₂ kY : ℕ) (W : MACChannel (Fin kX₁) (Fin kX₂) (Fin kY)),
    ∃ k : ℕ, 0 < k ∧ macFeedbackCapacityRegion W = coverLeungKLetterRegion k W

def problem : OpenProblem where
  id := "mac-with-feedback"
  title := "Capacity Region of the Multiple-Access Channel with Noiseless Feedback"
  category := .networkInfoTheory
  status := .open
  posedBy := "N. Thomas Gaarder and Jack Keil Wolf"
  posedYear := 1975
  statement := Statement

end InfoTheory.Problems.MacWithFeedback
