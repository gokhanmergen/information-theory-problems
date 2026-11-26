import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.InteractiveInfoComplexityCompression

/-- Recursive transcript prefix evaluator for a 2-party alternating randomized protocol
    with **both public randomness `rPub` and independent private randomness `(rA, rB)`**:
    Alice sends on even rounds using `(x, rPub, rA, prev)`, Bob sends on odd rounds using
    `(y, rPub, rB, prev)`. Private coins are essential: without them, `I(X, Y; Π | R_pub) = H(Π | R_pub)`
    and compression reduces to standard Huffman/Dietzfelbinger–Wunderlich coding. -/
def runPrefix {kX kY kRA kRB : ℕ}
    (alice : (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
    (x : Fin kX) (y : Fin kY) (rA : Fin kRA) (rB : Fin kRB) : (t : ℕ) → (Fin t → Bool)
  | 0 => fun i => Fin.elim0 i
  | t + 1 =>
    let prev := runPrefix alice bob x y rA rB t
    let nextBit := if t % 2 = 0 then alice t x rA prev else bob t y rB prev
    fun i => if h : i.1 < t then prev ⟨i.1, h⟩ else nextBit

/-- Average error probability of a randomized interactive protocol `(alice, bob, out)` of
    length `L` with public randomness `Ppub` and independent private randomness `(PA, PB)`. -/
noncomputable def protocolErr {kX kY L kPub kRA kRB : ℕ}
    (f : Fin kX × Fin kY → Bool) (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
    (out : Fin kPub → (Fin L → Bool) → Bool) : ℝ :=
  ∑ xy : Fin kX × Fin kY, ∑ r : Fin kPub, ∑ rA : Fin kRA, ∑ rB : Fin kRB,
    μ.pmf xy * Ppub.pmf r * PA.pmf rA * PB.pmf rB *
      if out r (runPrefix (alice r) (bob r) xy.1 xy.2 rA rB L) ≠ f xy then 1 else 0

/-- External information cost `I(X, Y; Π | R_pub)` of a randomized interactive protocol
    with public coins `R_pub` and independent private coins `(R_A, R_B)`. -/
noncomputable def extInfoCost {kX kY L kPub kRA kRB : ℕ}
    (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool) : ℝ :=
  let full := μ.prod (Ppub.prod (PA.prod PB))
  condMutualInfo (full.map (fun t =>
    (t.1, runPrefix (alice t.2.1) (bob t.2.1) t.1.1 t.1.2 t.2.2.1 t.2.2.2 L, t.2.1)))

/-- Linear External Information Compression Conjecture (Barak–Braverman–Chen–Rao 2010;
    Braverman 2012): does there exist a universal constant `C > 0` such that every
    two-party randomized interactive protocol (with both public and private coins) having
    external information cost `I` and error `≤ 1/10` can be compressed to communication
    `≤ C · (I + 1)` with error `≤ 1/3`? -/
def Statement : Prop :=
  ∃ (C : ℝ), 0 < C ∧
    ∀ (kX kY L kPub kRA kRB : ℕ) (f : Fin kX × Fin kY → Bool)
      (μ : ProbDist (Fin kX × Fin kY))
      (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
      (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
      (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
      (out : Fin kPub → (Fin L → Bool) → Bool),
      0 < kX → 0 < kY → 0 < kPub → 0 < kRA → 0 < kRB →
      protocolErr f μ Ppub PA PB alice bob out ≤ (1 : ℝ) / 10 →
      ∃ (L' kPub' kRA' kRB' : ℕ)
        (Ppub' : ProbDist (Fin kPub')) (PA' : ProbDist (Fin kRA')) (PB' : ProbDist (Fin kRB'))
        (alice' : Fin kPub' → (t : ℕ) → Fin kX → Fin kRA' → (Fin t → Bool) → Bool)
        (bob' : Fin kPub' → (t : ℕ) → Fin kY → Fin kRB' → (Fin t → Bool) → Bool)
        (out' : Fin kPub' → (Fin L' → Bool) → Bool),
        0 < kPub' ∧ 0 < kRA' ∧ 0 < kRB' ∧
        (L' : ℝ) ≤ C * (extInfoCost (L := L) μ Ppub PA PB alice bob + 1) ∧
        protocolErr f μ Ppub' PA' PB' alice' bob' out' ≤ (1 : ℝ) / 3

def problem : OpenProblem where
  id := "interactive-info-complexity-compression"
  title := "Optimal Compression of Interactive Protocols by External Information Cost"
  category := .securityPrivacy
  status := .open
  posedBy := "Boaz Barak, Mark Braverman, Xi Chen, and Anup Rao"
  posedYear := 2010
  statement := Statement

end InfoTheory.Problems.InteractiveInfoComplexityCompression
