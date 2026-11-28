import InfoTheory.Core

/-!
# Zero-error broadcasting over the pentagon: does `C₅` have a free lunch?

**Statement-fix (2026-11-27).** The previous statement asked whether a register-machine
program computes the zero-error *feedback sum capacity* of a general two-receiver broadcast
channel to within `1/m`. No source poses that question: neither Körner–Orlitsky (1998) nor
Shayevitz–Wigger (2013) (the cited references) mention zero-error feedback broadcast
computability, and two independent provenance checks plus a literature search found nothing.
It was a catalog invention. The statement is retargeted to a genuinely posed open zero-error
broadcast problem, a concrete instance of Hu–Shayevitz (2017), Problems 1(ii) and 2.

**Setting** (Hu–Shayevitz, *The ρ-capacity of a graph*, IEEE Trans. Inf. Theory 63(4), 2017,
arXiv:1607.07263). A zero-error broadcast channel with two receivers is modeled by a pair of
confusability graphs `(G₁, G₂)` with private messages. Taking receiver 1 noiseless
(`G₁` = the empty graph `K̄ₘ`) and receiver 2 with confusability graph `G` gives the
*ρ-capacity* `C_ρ(G) = sup {R : (ρ, R) ∈ C(K̄ₘ, G)}` (their Proposition 2), equivalently
`lim (1/n) log α_{2^{ρn}}(G^{⊠n})`. It is non-increasing and concave in `ρ`, and
`C₀(G) = log Θ(G)`. The *free-lunch point* `ρ*(G)` is the largest `ρ` with
`C_ρ(G) = C₀(G)`: up to that point the noiseless receiver gets rate `ρ` at no cost to the
noisy one.

Hu–Shayevitz list as open problems: "Find the ρ-capacity of the Pentagon `C₅`" (Problem 1(ii))
and "Characterize the free-lunch point `ρ*(G)`. Specifically, give a necessary and sufficient
condition for `ρ*(G) > 0`" (Problem 2). Their bounds for `C₅` (Example 6: the time-sharing
lower bound, clique and independent-family bounds, and the Lovász-type bound of Theorem 4,
which applies only for `ρ` in roughly `(0.58, 1.55)` bits) leave open whether
`ρ*(C₅) > 0`.

`Statement`: **the pentagon has a free lunch**, `ρ*(C₅) > 0`. That is, there is `ρ > 0`
such that the rate pair `(ρ, ½ log₂ 5)` lies in the (closed) zero-error capacity region of
the broadcast channel with a noiseless receiver and a `C₅` receiver (`½ log₂ 5 = log₂ Θ(C₅)`
by Lovász 1979). Written without limits or `sSup`: for every `δ > 0` there is a zero-error
code of some blocklength `n` with `log₂ M₁ ≥ (ρ - δ) n` and `log₂ M₂ ≥ (½ log₂ 5 - δ) n`.
Message sets are required to be nonempty, so the code conditions are never vacuous.

Known facts (certificate `InfoTheory.Known.Certificates.ZeroErrorBroadcastChannel`): with
`ρ = 0` the condition holds, via Shannon's code `{(i, 2i)}` (so the question is exactly about
`ρ > 0`); every code has `M₂ ≤ α(C₅^{⊠n}) ≤ 5^{n/2}` and `M₁ M₂ ≤ 5ⁿ`, so the receiver-2
target `½ log₂ 5` is the largest possible, and any witness has `ρ ≤ ½ log₂ 5`.
-/

open scoped BigOperators

namespace InfoTheory.Problems.ZeroErrorBroadcastChannel

/-- Two input words are *distinguishable* at the `C₅` receiver iff they cannot produce a
    common output. In the strong power, a common output is possible iff the words are equal
    or adjacent. -/
def Distinguishable (n : ℕ) (x y : Fin n → ZMod 5) : Prop :=
  x ≠ y ∧ ¬ (strongPower (cycleGraph 5) n).Adj x y

/-- A zero-error code of blocklength `n` for the two-receiver broadcast channel whose
    receiver 1 sees the input noiselessly (confusability graph `K̄₅`) and whose receiver 2
    has confusability graph `C₅`, with private messages `w₁ ∈ [M₁]`, `w₂ ∈ [M₂]`.
    Receiver 1 decodes `w₁` from the codeword; receiver 2 decodes `w₂` iff codewords carrying
    different `w₂` are distinguishable in `C₅^{⊠n}`. -/
def IsPentagonBroadcastCode (n M₁ M₂ : ℕ) (enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)) :
    Prop :=
  (∀ w₁ w₁' : Fin M₁, ∀ w₂ w₂' : Fin M₂, enc w₁ w₂ = enc w₁' w₂' → w₁ = w₁') ∧
  (∀ w₁ w₁' : Fin M₁, ∀ w₂ w₂' : Fin M₂, w₂ ≠ w₂' →
    Distinguishable n (enc w₁ w₂) (enc w₁' w₂'))

/-- The rate pair `(R₁, R₂)` lies in the closed zero-error capacity region `C(K̄₅, C₅)`:
    for every `δ > 0` some zero-error code has rates at least `(R₁ - δ, R₂ - δ)`. -/
def InPentagonRegion (R₁ R₂ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (n M₁ M₂ : ℕ) (enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)),
    0 < n ∧ 0 < M₁ ∧ 0 < M₂ ∧ IsPentagonBroadcastCode n M₁ M₂ enc ∧
    (R₁ - δ) * (n : ℝ) ≤ log2 (M₁ : ℝ) ∧ (R₂ - δ) * (n : ℝ) ≤ log2 (M₂ : ℝ)

/-- **Free lunch for the pentagon** (Hu–Shayevitz 2017, Problems 1(ii) and 2, for
    `G = C₅`): is the free-lunch point `ρ*(C₅)` positive, i.e. is there `ρ > 0` with
    `(ρ, ½ log₂ 5) ∈ C(K̄₅, C₅)`, so that `C_ρ(C₅) = log₂ Θ(C₅)`? -/
def Statement : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ InPentagonRegion ρ (log2 5 / 2)

def problem : OpenProblem where
  id := "zero-error-broadcast-channel"
  title := "Zero-Error Broadcasting over the Pentagon: Is the Free-Lunch Point of C₅ Positive?"
  category := .zeroError
  status := .open
  posedBy := "Sihuang Hu, Ofer Shayevitz"
  posedYear := 2017
  statement := Statement

end InfoTheory.Problems.ZeroErrorBroadcastChannel
