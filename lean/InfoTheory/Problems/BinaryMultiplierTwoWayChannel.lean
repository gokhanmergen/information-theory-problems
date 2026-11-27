import InfoTheory.Core

/-!
# Symmetric capacity of Blackwell's binary multiplying channel

`Statement`: the equal-rate capacity `bmcSymmetricCapacity` of the BMC `Y = X₁ · X₂` equals
`bmcHWParallelChannelBound`, the Hekstra–Willems (1989) dependence-balance bound with an
adaptive parallel channel (≈ 0.64628 bits), the sharpest known converse.

**Statement-fix (2026-11-27).** The original right-hand side was the *plain*
dependence-balance functional `sup min(I(X₁;Y|X₂Z), I(X₂;Y|X₁Z))` subject to
`I(X₁;X₂|Z) ≤ I(X₁;X₂|Y,Z)`. For a deterministic channel that constraint reads
`H(Y|Z) ≤ I(X₁;Y|X₂Z) + I(X₂;Y|X₁Z)`, which is automatic at symmetric rates `≥ 1/2`, so the
functional equals Shannon's outer bound `log₂ φ ≈ 0.69424` (Bloemen 1996, §6.4.2). The old
statement therefore asserted `C_sym = log₂ φ`, which contradicts the Zhang–Berger–Schalkwijk
bound `C_sym ≤ 0.64891`
(`attempts/binary-multiplier-two-way-channel/2026-11-26-claude-opus-5-5-db-catalog-error-survey.md`).
The new right-hand side is the bound the literature's `0.64628` refers to, written in the
closed form derived in that attempt (the parallel channel makes the DB constraint force
`X₁ ⊥ X₂ | U`); a numerical optimisation reproduces `0.6462832`.

Known facts: `0.63072 ≤ C_sym ≤ 0.64628` (Schalkwijk–Meeuwissen–Bloemen 1995;
Hekstra–Willems 1989). Hekstra–Willems' parallel channel is optimal among binary adaptive
parallel channels (Tandon–Ulukus 2007). The question is whether this best known converse is
tight. The `sSup` is over a nonempty set bounded above by `1` (certificate).
-/

open scoped BigOperators

namespace InfoTheory.Problems.BinaryMultiplierTwoWayChannel

/-- Symmetric (equal-rate) operational capacity of Blackwell's Binary Multiplying Channel
    `Y₁ = Y₂ = X₁ · X₂`. -/
noncomputable def bmcSymmetricCapacity : ℝ :=
  sSup { R : ℝ | (R, R) ∈ twcCapacityRegion binaryMultiplyingChannel }

/-- Crossover probability of the Hekstra–Willems adaptive parallel channel for the BMC
    (Bloemen 1996, Table 6.2 / eq. (6.58)), as a function of `α = P(X₁ = 1 | U = u)` and
    `β = P(X₂ = 1 | U = u)`: on input `(0, 0)` the auxiliary output is `B = 0` with this
    probability. (Lean's `x / 0 = 0` fires only at `α = β ∈ {0, 1}`, where the rate terms below
    do not depend on the crossover.) -/
noncomputable def hwCrossover (α β : ℝ) : ℝ :=
  α * (1 - β) / ((1 - α) * β + α * (1 - β))

/-- Hekstra–Willems (1989) dependence-balance upper bound **with an adaptive parallel channel**
    on the equal-rate point of the BMC, in closed form (≈ 0.64628 bits).

    The bound is `sup min{I(X₁; Y B | X₂ U), I(X₁; Y | X₂), I(X₂; Y B | X₁ U), I(X₂; Y | X₁)}`
    over `p(u, x₁, x₂)` with `I(X₁; X₂ | U) ≤ I(X₁; X₂ | Y, B, U)`, where `B` is the output of
    the parallel channel `(0,0,0) ↦ B ~ (p, 1 - p)`, `(0,1,0) ↦ 1`, `(1,0,0) ↦ 0`, `(1,1,1) ↦ ∗`
    with `p = hwCrossover α β`. Since `(Y, B)` determines one of the inputs,
    `I(X₁; X₂ | Y, B, U) = 0`, so the constraint forces `X₁ ⊥ X₂ | U`; with `U = u` of weight
    `w u` and `(α u, β u)` the conditional input marginals, the four terms are `r₁`, the
    `U`-free term `P₂ h(P₁₁ / P₂)`, `r₂`, and `P₁ h(P₁₁ / P₁)` below. (`P₁₁ / P₂` is junk only
    when `P₂ = 0`, where the term is `0` anyway.) -/
noncomputable def bmcHWParallelChannelBound : ℝ :=
  sSup { r : ℝ | ∃ (k : ℕ) (w α β : Fin k → ℝ),
    (∀ u, 0 ≤ w u) ∧ (∑ u, w u) = 1 ∧
    (∀ u, 0 ≤ α u ∧ α u ≤ 1) ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧
    let p : Fin k → ℝ := fun u => hwCrossover (α u) (β u)
    -- `I(X₁; Y B | X₂, U)`
    let r₁ := ∑ u, w u * (β u * binaryEntropy (α u) + (1 - β u) *
      (binaryEntropy ((1 - α u) * (1 - p u)) - (1 - α u) * binaryEntropy (p u)))
    -- `I(X₂; Y B | X₁, U)`
    let r₂ := ∑ u, w u * (α u * binaryEntropy (β u) + (1 - α u) *
      (binaryEntropy ((1 - β u) * p u) - (1 - β u) * binaryEntropy (p u)))
    let P₁ := ∑ u, w u * α u
    let P₂ := ∑ u, w u * β u
    let P₁₁ := ∑ u, w u * (α u * β u)
    r = min (min r₁ (P₂ * binaryEntropy (P₁₁ / P₂)))
            (min r₂ (P₁ * binaryEntropy (P₁₁ / P₁))) }

/-- Symmetric Capacity of Blackwell's Binary Multiplying Channel (Blackwell / Shannon 1961;
    Hekstra–Willems 1989):
    Does the symmetric capacity of `binaryMultiplyingChannel` equal the Hekstra–Willems
    dependence-balance bound with adaptive parallel channel (≈ 0.64628 bits)? -/
def Statement : Prop :=
  bmcSymmetricCapacity = bmcHWParallelChannelBound

def problem : OpenProblem where
  id := "binary-multiplier-two-way-channel"
  title := "Symmetric Capacity of Blackwell's Binary Multiplying Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "David Blackwell (via Claude E. Shannon)"
  posedYear := 1961
  statement := Statement

end InfoTheory.Problems.BinaryMultiplierTwoWayChannel
