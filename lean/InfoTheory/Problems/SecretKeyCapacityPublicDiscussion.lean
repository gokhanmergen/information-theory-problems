import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SecretKeyCapacityPublicDiscussion

/-- The Gohari–Anantharam (2010) sharpening of Renner–Wolf's reduced intrinsic information:
    `inf_{P_{U | XYZ}} [ I(X; Y ↓ Z, U) + I(U; X, Y | Z) ]`. -/
noncomputable def gohariAnantharamBound {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (P : ProbDist (X × Y × Z)) : ℝ :=
  sInf { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist ((X × Y × Z) × Fin kU)),
    Q.fst = P ∧
    r = intrinsicInfo (Q.map (fun t => (t.1.1, t.1.2.1, (t.1.2.2, t.2)))) +
        condMutualInfo (Q.map (fun t => (t.2, (t.1.1, t.1.2.1), t.1.2.2))) }

/-- Single-letter characterization conjecture for secret key capacity with unlimited two-way
    public discussion: does `S(X; Y ‖ Z)` equal the Gohari–Anantharam reduced intrinsic
    information upper bound for every finite discrete memoryless source `P_{XYZ}`? -/
def Statement : Prop :=
  ∀ (kX kY kZ : ℕ) (P : ProbDist (Fin kX × Fin kY × Fin kZ)),
    0 < kX → 0 < kY → 0 < kZ →
    secretKeyCapacity P = gohariAnantharamBound P

def problem : OpenProblem where
  id := "secret-key-capacity-public-discussion"
  title := "Single-Letter Characterization of Secret Key Capacity with Unlimited Public Discussion"
  category := .securityPrivacy
  status := .open
  posedBy := "Ueli M. Maurer; Rudolf Ahlswede and Imre Csiszár"
  posedYear := 1993
  statement := Statement

end InfoTheory.Problems.SecretKeyCapacityPublicDiscussion
