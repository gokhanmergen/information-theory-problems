import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.PolarCodeScalingExponent

/-- Base-`ℓ` lexicographic bijection `Fin (ℓ^m) → (Fin m → Fin ℓ)` for `ℓ > 0`. -/
def polarIdx (ℓ m : ℕ) (hℓ : 0 < ℓ) (t : Fin (ℓ ^ m)) : Fin m → Fin ℓ :=
  fun s => ⟨(t.1 / ℓ ^ (m - 1 - s.1)) % ℓ, Nat.mod_lt _ hℓ⟩

/-- Encoding `x = u · G^{⊗ m}` of a message vector `u : (Fin m → Fin ℓ) → ZMod 2` under
    the `m`-fold Kronecker power of an `ℓ × ℓ` binary kernel `G`. -/
def polarEncode (ℓ m : ℕ) (G : Fin ℓ → Fin ℓ → ZMod 2)
    (u : (Fin m → Fin ℓ) → ZMod 2) : (Fin m → Fin ℓ) → ZMod 2 :=
  fun j => ∑ i : Fin m → Fin ℓ, u i * ∏ s : Fin m, G (i s) (j s)

/-- Invertibility of an `ℓ × ℓ` binary matrix `G` over `𝔽₂`. -/
def IsInvertibleKernel (ℓ : ℕ) (G : Fin ℓ → Fin ℓ → ZMod 2) : Prop :=
  ∃ Ginv : Fin ℓ → Fin ℓ → ZMod 2,
    ∀ i j : Fin ℓ, (∑ k : Fin ℓ, G i k * Ginv k j) = if i = j then 1 else 0

/-- Exact successive cancellation (SC) block error probability of a binary polar code
    with kernel `G`, depth `m`, information set `A`, and causal SC decision functions `dec`,
    communicating over `BSC(p)` (via the exact genie-aided coupling identity). -/
noncomputable def polarSCBlockError (ℓ m : ℕ) (hℓ : 0 < ℓ)
    (G : Fin ℓ → Fin ℓ → ZMod 2)
    (A : Finset (Fin m → Fin ℓ))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (dec : ∀ t : Fin (ℓ ^ m), ((Fin m → Fin ℓ) → Bool) → (Fin t.1 → ZMod 2) → ZMod 2) : ℝ :=
  let validU : Finset ((Fin m → Fin ℓ) → ZMod 2) :=
    Finset.univ.filter (fun u => ∀ i : Fin m → Fin ℓ, i ∉ A → u i = 0)
  ((1 : ℝ) / ((2 ^ A.card : ℕ) : ℝ)) *
    ∑ u ∈ validU,
      ∑ y : (Fin m → Fin ℓ) → Bool,
        if ∃ t : Fin (ℓ ^ m),
            polarIdx ℓ m hℓ t ∈ A ∧
            dec t y (fun s : Fin t.1 => u (polarIdx ℓ m hℓ ⟨s.1, Nat.lt_trans s.2 t.2⟩)) ≠
              u (polarIdx ℓ m hℓ t)
        then
          ∏ j : Fin m → Fin ℓ,
            (bsc p hp0 hp1).trans (decide (polarEncode ℓ m G u j = 1)) (y j)
        else 0

open Classical in
/-- Bit-channel likelihood used by the standard successive-cancellation decoder: up to the
    constant factor `2^{-(N-1)}`, this is Arıkan's `W_N^{(t)}(y, u_{<t} | b)`, the sum of
    `W^N(y | u G^{⊗ m})` over **all** `u` agreeing with the prefix `pre` at the SC positions
    `< t` and with `u_t = b`; all later bits (frozen or not) are summed over, as in Arıkan's SC
    decoder. -/
noncomputable def bitChannelLik (ℓ m : ℕ) (hℓ : 0 < ℓ) (G : Fin ℓ → Fin ℓ → ZMod 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : Fin (ℓ ^ m))
    (y : (Fin m → Fin ℓ) → Bool) (pre : Fin t.1 → ZMod 2) (b : ZMod 2) : ℝ :=
  ∑ u : (Fin m → Fin ℓ) → ZMod 2,
    if (∀ s : Fin t.1, u (polarIdx ℓ m hℓ ⟨s.1, Nat.lt_trans s.2 t.2⟩) = pre s) ∧
        u (polarIdx ℓ m hℓ t) = b
    then ∏ j : Fin m → Fin ℓ, (bsc p hp0 hp1).trans (decide (polarEncode ℓ m G u j = 1)) (y j)
    else 0

/-- The standard SC decision rule (Arıkan 2009): decide `u_t = 1` iff its bit-channel
    likelihood is strictly larger than that of `u_t = 0` (ties broken towards `0`).  Plugged
    into the genie-aided error functional `polarSCBlockError`, this gives exactly the block
    error probability of the actual SC decoder. -/
noncomputable def scDecoder (ℓ m : ℕ) (hℓ : 0 < ℓ) (G : Fin ℓ → Fin ℓ → ZMod 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ t : Fin (ℓ ^ m), ((Fin m → Fin ℓ) → Bool) → (Fin t.1 → ZMod 2) → ZMod 2 :=
  fun t y pre =>
    if bitChannelLik ℓ m hℓ G p hp0 hp1 t y pre 0 < bitChannelLik ℓ m hℓ G p hp0 hp1 t y pre 1
    then 1 else 0

/-- Open problem: On `BSC(p)` for any `p ∈ (0, 1/2)`, can binary polar codes with a single
    fixed finite invertible binary kernel `G ∈ GL_ℓ(𝔽₂)`, under **successive-cancellation**
    decoding, achieve scaling exponent arbitrarily close to the optimal value `μ = 2`?

    Statement-fix (2026-11-27): the previous version quantified existentially over arbitrary
    decision functions `dec t y u_{<t}`.  Such a `dec` may ignore the prefix and output the
    `t`-th coordinate of the **block-MAP** estimate (it may also use that future frozen bits are
    `0`), so the "SC" error functional equalled the block-MAP error of the polar code and the
    statement asked about MAP decoding of polar subcodes (a family containing Reed–Muller codes),
    not about SC decoding.  The decoder is now pinned to Arıkan's SC rule `scDecoder`. -/
def Statement : Prop :=
  ∀ (p ε η : ℝ), (hp0 : 0 < p) → (hp1 : p < 1 / 2) → 0 < ε → 0 < η → η < 1 →
    ∃ (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (G : Fin ℓ → Fin ℓ → ZMod 2) (c : ℝ) (m₀ : ℕ),
      IsInvertibleKernel ℓ G ∧ 0 < c ∧
      ∀ m : ℕ, m₀ ≤ m →
        ∃ A : Finset (Fin m → Fin ℓ),
          (1 - binaryEntropy p) - c * ((ℓ ^ m : ℕ) : ℝ) ^ (-(1 : ℝ) / (2 + ε)) ≤
            (A.card : ℝ) / ((ℓ ^ m : ℕ) : ℝ) ∧
          polarSCBlockError ℓ m (by omega : 0 < ℓ) G A p (le_of_lt hp0) (by linarith)
            (scDecoder ℓ m (by omega : 0 < ℓ) G p (le_of_lt hp0) (by linarith)) ≤ η

def problem : OpenProblem where
  id := "polar-code-scaling-exponent"
  title := "Optimal Scaling Exponent of Binary Polar Codes with Finite Kernels on the BSC"
  category := .codingTheory
  status := .partiallySolved
  posedBy := "Erdal Arıkan; S. Hamed Hassani, Kasra Alishahi, and Rüdiger L. Urbanke"
  posedYear := 2014
  statement := Statement

end InfoTheory.Problems.PolarCodeScalingExponent
