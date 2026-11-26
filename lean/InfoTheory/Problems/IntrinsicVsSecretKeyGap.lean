import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.IntrinsicVsSecretKeyGap

/-- Existence of bipartite classical bound information (Gisin–Wolf 2000; Renner–Wolf 2003):
    does there exist a finite discrete distribution `P_{XYZ}` with strictly positive
    intrinsic information `I(X; Y ↓ Z) > 0` yet zero secret key capacity `S(X; Y ‖ Z) = 0`? -/
def Statement : Prop :=
  ∃ (kX kY kZ : ℕ) (P : ProbDist (Fin kX × Fin kY × Fin kZ)),
    0 < kX ∧ 0 < kY ∧ 0 < kZ ∧
    0 < intrinsicInfo P ∧
    secretKeyCapacity P = 0

def problem : OpenProblem where
  id := "intrinsic-vs-secret-key-gap"
  title := "Classical Bound Information and the Gap Between Intrinsic Information and Secret Key Capacity"
  category := .securityPrivacy
  status := .open
  posedBy := "Ueli M. Maurer and Stefan Wolf; Nicolas Gisin and Stefan Wolf"
  posedYear := 1999
  statement := Statement

end InfoTheory.Problems.IntrinsicVsSecretKeyGap
