import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.InsertionDeletionChannel

/-- Transition probability `Pr[IDS(p_d, p_i)(x) = y]` of Gallager's binary insertion–deletion
    channel: each bit is deleted with probability `pd`, kept unchanged with probability
    `1 - pd - pi`, or replaced by two independent uniform random bits with probability `pi`. -/
noncomputable def idsProb (pd pi : ℝ) : List Bool → List Bool → ℝ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: xs, [] => pd * idsProb pd pi xs []
  | a :: xs, [b] =>
      pd * idsProb pd pi xs [b] +
      (if a = b then (1 - pd - pi) * idsProb pd pi xs [] else 0)
  | a :: xs, b₁ :: b₂ :: ys =>
      pd * idsProb pd pi xs (b₁ :: b₂ :: ys) +
      (if a = b₁ then (1 - pd - pi) * idsProb pd pi xs (b₂ :: ys) else 0) +
      (pi / 4) * idsProb pd pi xs ys

/-- Blocklength-`n` mutual information `I(X^n; Y)` over Gallager's binary insertion–deletion
    channel for an input distribution `P` on `{0,1}^n`. -/
noncomputable def idsMI (pd pi : ℝ) (n : ℕ) (P : ProbDist (Fin n → Bool)) : ℝ :=
  let outType := Σ k : Fin (2 * n + 1), Fin k.1 → Bool
  let py : outType → ℝ := fun y =>
    ∑ x : Fin n → Bool, P.pmf x * idsProb pd pi (List.ofFn x) (List.ofFn y.2)
  let hY : ℝ := ∑ y : outType, negPLogP (py y)
  let hYgivenX : ℝ := ∑ x : Fin n → Bool, P.pmf x *
    ∑ y : outType, negPLogP (idsProb pd pi (List.ofFn x) (List.ofFn y.2))
  hY - hYgivenX

/-- Maximum blocklength-`n` mutual information `C_n(pd, pi) = sup_P I(X^n; Y)`. -/
noncomputable def idsMaxMI (pd pi : ℝ) (n : ℕ) : ℝ :=
  sSup { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = idsMI pd pi n P }

/-- Shannon capacity `C_IDS(pd, pi) = lim_{n → ∞} C_n/n = inf_{n ≥ 1} (1/n) max_P I(X^n; Y)`
    of Gallager's binary insertion–deletion channel (Dobrushin 1967; Fekete subadditivity). -/
noncomputable def idsCapacity (pd pi : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = idsMaxMI pd pi n / (n : ℝ) }

/-- Joint Convexity Conjecture for the Binary Insertion–Deletion Channel (Gallager 1961;
    Mitzenmacher 2009; Dalai 2011): the capacity `(pd, pi) ↦ C_IDS(pd, pi)` is jointly
    convex on the parameter simplex `{(pd, pi) : pd ≥ 0, pi ≥ 0, pd + pi ≤ 1}`.
    Specializing to `pi = qi = 0` yields the open convexity conjecture for the binary
    deletion channel capacity `C(d)`. -/
def Statement : Prop :=
  ∀ (pd pi qd qi lam : ℝ),
    0 ≤ pd → 0 ≤ pi → pd + pi ≤ 1 →
    0 ≤ qd → 0 ≤ qi → qd + qi ≤ 1 →
    0 ≤ lam → lam ≤ 1 →
    idsCapacity (lam * pd + (1 - lam) * qd) (lam * pi + (1 - lam) * qi) ≤
      lam * idsCapacity pd pi + (1 - lam) * idsCapacity qd qi

def problem : OpenProblem where
  id := "insertion-deletion-channel"
  title := "Capacity and Convexity of the Binary Insertion–Deletion Channel"
  category := .channelCapacity
  status := .open
  posedBy := "Robert G. Gallager; Michael Mitzenmacher"
  posedYear := 1961
  statement := Statement

end InfoTheory.Problems.InsertionDeletionChannel
