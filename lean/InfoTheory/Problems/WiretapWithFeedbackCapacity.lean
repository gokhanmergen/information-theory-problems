import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.WiretapWithFeedbackCapacity

/-- Operational achievability of secrecy rate `R` over a discrete memoryless wiretap channel
    `W(y, z | x)` with noiseless causal secure output feedback `Y^{i-1}` to the encoder. -/
def IsWiretapFeedbackAchievable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WiretapChannel X Y Z) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (kR : ℕ) (Prand : ProbDist (Fin kR))
      (enc : ∀ (i : Fin n), Fin M → Fin kR → (Fin i.1 → Y) → X)
      (dec : (Fin n → Y) → Fin M)
      (Q : ProbDist (Fin M × (Fin n → Y) × (Fin n → Z))),
      (∀ (m : Fin M) (y : Fin n → Y) (z : Fin n → Z),
        Q.pmf (m, y, z) = ((1 : ℝ) / (M : ℝ)) *
          ∑ r : Fin kR, Prand.pmf r *
            ∏ i : Fin n, W.trans (enc i m r (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, z i)) ∧
      (∑ t : Fin M × (Fin n → Y) × (Fin n → Z),
        if dec t.2.1 ≠ t.1 then Q.pmf t else 0) ≤ ε ∧
      mutualInfo (Q.map (fun t => (t.1, t.2.2))) ≤ (n : ℝ) * ε

/-- Operational secrecy capacity `C_s^{fb}(W)` with noiseless secure output feedback. -/
noncomputable def wiretapFeedbackCapacity {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WiretapChannel X Y Z) : ℝ :=
  sSup { R : ℝ | IsWiretapFeedbackAchievable W R }

/-- Ahlswede–Cai (2006) single-letter upper bound `max_{P_X} min(I(X; Y), H(Y | Z))`,
    known to be tight for degraded and reversely degraded wiretap channels. -/
noncomputable def ahlswedeCaiBound {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WiretapChannel X Y Z) : ℝ :=
  sSup { r : ℝ | ∃ (P : ProbDist X),
    let J := W.joint P
    r = min (mutualInfo (J.map (fun t => (t.1, t.2.1))))
            (condEntropy (J.map (fun t => (t.2.1, t.2.2)))) }

/-- Tightness of the Ahlswede–Cai single-letter formula for all general (non-degraded)
    discrete memoryless wiretap channels with noiseless secure output feedback. -/
def Statement : Prop :=
  ∀ (kX kY kZ : ℕ) (W : WiretapChannel (Fin kX) (Fin kY) (Fin kZ)),
    0 < kX → 0 < kY → 0 < kZ →
    wiretapFeedbackCapacity W = ahlswedeCaiBound W

def problem : OpenProblem where
  id := "wiretap-with-feedback-capacity"
  title := "Secrecy Capacity of the General Wiretap Channel with Noiseless Output Feedback"
  category := .securityPrivacy
  status := .open
  posedBy := "Rudolf Ahlswede and Ning Cai"
  posedYear := 2006
  statement := Statement

end InfoTheory.Problems.WiretapWithFeedbackCapacity
