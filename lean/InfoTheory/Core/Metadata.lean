/-!
# Problem Metadata and Status Types

Core metadata types linking each Lean 4 formal problem statement in
`InfoTheory.Problems.*` to its catalog entry in `problems/<id>.md`.
-/

namespace InfoTheory

/-- Resolution status of a cataloged problem, matching `problems/<id>.md`. -/
inductive ProblemStatus where
  | open
  | partiallySolved
  | solved
  deriving DecidableEq, Repr

/-- Thematic subfield of information theory. -/
inductive ProblemCategory where
  | entropyInequalities
  | channelCapacity
  | networkInfoTheory
  | sourceCoding
  | zeroError
  | codingTheory
  | networkCoding
  | quantumInfo
  | securityPrivacy
  | statisticalInfoTheory
  deriving DecidableEq, Repr

/-- A cataloged open problem together with its frozen Lean 4 proposition `statement`.
    Resolving the problem requires supplying a Lean proof of `statement` or `¬ statement`
    using only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). -/
structure OpenProblem where
  id : String
  title : String
  category : ProblemCategory
  status : ProblemStatus
  posedBy : String
  posedYear : Nat
  statement : Prop

end InfoTheory
