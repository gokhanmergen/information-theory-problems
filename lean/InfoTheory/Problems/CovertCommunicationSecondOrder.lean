import InfoTheory.Core

/-!
# Second-order asymptotics of covert communication (missed-detection metric)

`Statement`: for every binary-input wiretap DMC with innocent symbol `false`, `P₁ ≪ P₀`,
`Q₁ ≪ Q₀`, `Q₁ ≠ Q₀`, and every `ε ∈ (0, 1)`, false-alarm level `α ∈ (0, 1)` and
`δ ∈ (0, 1 - α)`, the maximal number `M*_β(n, ε, δ, α)` of messages that can be sent with
maximal error `≤ ε` while the warden's optimal missed-detection probability at false-alarm
level `α` stays `≥ 1 - α - δ` satisfies
`log₂ M*_β ≥ a √n - b n^{1/4} - o(n^{1/4})`, where
`a = (Λ + Υ) D(P₁‖P₀) / √χ²(Q₁‖Q₀)`, `b = √((Λ + Υ) V_P / √χ²(Q₁‖Q₀)) · Q⁻¹(ε)`,
`Λ = Q⁻¹(1 - α - δ)`, `Υ = Q⁻¹(α)`, `V_P = Var_{P₁}[log₂ (P₁/P₀)]`. This is the
Tahmasbi–Bloch (2019, after Theorem 3) conjecture that their converse (29) is achievable;
the converse `log₂ M*_β ≤ a √n - b n^{1/4} + O(log n)` is their theorem.

**Statement-fix (2026-11-27).** The previous statement asked whether keyless codes match
key-assisted codes to `o(n^{1/4})` in the regime `D(P₁‖P₀) > D(Q₁‖Q₀)`, under KL covertness
and *average* error. Under the *maximal* error criterion of Tahmasbi–Bloch this is settled by
their Theorem 1 itself: its achievability proof (IEEE T-IT 65(4), 2019, eq. (196)) takes
`log M + log K = max(log M, (1 + ρ) ℓ_n D_Q)`, so for `(1 + ρ) D_Q < D_P` the key is empty and
keyless codes attain `log M*_D` up to `O(log n)`. Under average error the question is one
nobody posed: Tahmasbi–Bloch (Appendix A) show that even the first-order term then depends on
`ε`. The open questions they do state are the exact second order under the variational
distance and missed-detection metrics. The variational-distance case is claimed by
Zhang–Zhou–Li (arXiv:2609.24675, Sept 2026); the missed-detection case, formalized here,
remains open.

All quantities are junk-free under the hypotheses: covertness is a `sInf` over deterministic
tests (nonempty, bounded below by `0`), the message count is a `sSup` over codes containing
the one-message all-innocent code and bounded by `kYⁿ/(1 - ε)`, `χ²(Q₁‖Q₀) > 0` because
`Q₁ ≪ Q₀` and `Q₁ ≠ Q₀`, and the quantile `Q⁻¹` is only evaluated in `(0, 1)`.
-/

open scoped BigOperators

namespace InfoTheory.Problems.CovertCommunicationSecondOrder

/-- KL divergence (in bits) between two nonnegative pmf functions on a finite type. -/
noncomputable def klDivFn {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, if p a ≤ 0 then 0 else p a * log2 (p a / q a)

/-- `χ²(p ‖ q) = ∑ (p - q)² / q` between two nonnegative pmf functions. -/
noncomputable def chiSqFn {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, if q a ≤ 0 then 0 else (p a - q a) ^ 2 / q a

/-- Variance under `p` of the log-likelihood ratio `log₂ (p / q)` (in bits²). -/
noncomputable def llrVarFn {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ a : α, if p a ≤ 0 then 0 else p a * (log2 (p a / q a)) ^ 2) - (klDivFn p q) ^ 2

open MeasureTheory in
/-- Standard normal cumulative distribution function `Φ(t)`. -/
noncomputable def stdNormalCDF (t : ℝ) : ℝ :=
  ∫ x : ℝ, if x ≤ t then gaussianPdf1D 1 x else 0

/-- Inverse Gaussian tail `Q⁻¹(t) = Φ⁻¹(1 - t)` (for `t ∈ (0, 1)`). -/
noncomputable def gaussQinv (t : ℝ) : ℝ :=
  sInf { s : ℝ | 1 - t ≤ stdNormalCDF s }

/-- Optimal missed-detection probability `β_α(P, Q) = min_{T : P(Tᶜ) ≤ α} Q(T)` over
    deterministic tests `T` (accept `H₀ : P` on `T`). -/
noncomputable def betaAlpha {Ω : Type*} [Fintype Ω] (α : ℝ) (P Q : Ω → ℝ) : ℝ :=
  sInf { b : ℝ | ∃ T : Ω → Bool,
    (∑ ω : Ω, if T ω then 0 else P ω) ≤ α ∧ b = ∑ ω : Ω, if T ω then Q ω else 0 }

/-- Maximal number of messages `M*_β(n, ε, δ, α)` over a binary-input wiretap DMC `W`
    (innocent symbol `false`) in `n` uses, with a shared key of any size `K`, maximal error
    `≤ ε` over every key and message, and warden missed-detection
    `β_α(Q₀^{⊗n}, P̂_Zⁿ) ≥ 1 - α - δ` (Tahmasbi–Bloch 2019, Definition 1). -/
noncomputable def covertMaxMessagesBeta {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : WiretapChannel Bool Y Z) (n : ℕ) (ε δ α : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ (m K : ℕ) (enc : Fin K → Fin m → Fin n → Bool)
    (dec : Fin K → (Fin n → Y) → Fin m),
    0 < m ∧ 0 < K ∧ r = (m : ℝ) ∧
    (∀ (s : Fin K) (w : Fin m),
      (∑ y : Fin n → Y, if dec s y ≠ w then
        ∏ i : Fin n, ∑ z : Z, W.trans (enc s w i) (y i, z) else 0) ≤ ε) ∧
    let qZ (z : Fin n → Z) : ℝ := ((1 : ℝ) / ((m * K : ℕ) : ℝ)) *
      ∑ s : Fin K, ∑ w : Fin m, ∏ i : Fin n, ∑ y : Y, W.trans (enc s w i) (y, z i)
    let q0Pow (z : Fin n → Z) : ℝ := ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i)
    1 - α - δ ≤ betaAlpha α q0Pow qZ }

/-- Tahmasbi–Bloch (2019) missed-detection second-order conjecture: the converse
    `log₂ M*_β ≤ a √n - b n^{1/4} + O(log n)` is achievable up to `o(n^{1/4})`. -/
def Statement : Prop :=
  ∀ (kY kZ : ℕ) (W : WiretapChannel Bool (Fin kY) (Fin kZ)),
    0 < kY → 0 < kZ →
    let P0 (y : Fin kY) : ℝ := ∑ z : Fin kZ, W.trans false (y, z)
    let P1 (y : Fin kY) : ℝ := ∑ z : Fin kZ, W.trans true (y, z)
    let Q0 (z : Fin kZ) : ℝ := ∑ y : Fin kY, W.trans false (y, z)
    let Q1 (z : Fin kZ) : ℝ := ∑ y : Fin kY, W.trans true (y, z)
    (∀ (y : Fin kY), P0 y = 0 → P1 y = 0) →
    (∀ (z : Fin kZ), Q0 z = 0 → Q1 z = 0) →
    (∃ (z : Fin kZ), Q1 z ≠ Q0 z) →
    ∀ (ε α δ η : ℝ), 0 < ε → ε < 1 → 0 < α → α < 1 → 0 < δ → δ < 1 - α → 0 < η →
      let Λ := gaussQinv (1 - α - δ)
      let Υ := gaussQinv α
      let sχ := Real.sqrt (chiSqFn Q1 Q0)
      let a := (Λ + Υ) * klDivFn P1 P0 / sχ
      let b := Real.sqrt ((Λ + Υ) * llrVarFn P1 P0 / sχ) * gaussQinv ε
      ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
        a * Real.sqrt (n : ℝ) - b * ((n : ℝ) ^ ((1 : ℝ) / 4)) - η * ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤
          log2 (covertMaxMessagesBeta W n ε δ α)

def problem : OpenProblem where
  id := "covert-communication-second-order"
  title := "Second-Order Asymptotics and Keyless Dispersion of Square-Root-Law Covert Communication"
  category := .securityPrivacy
  status := .open
  posedBy := "Boulat A. Bash, Dennis Goeckel, and Don Towsley; Ligong Wang, Gregory W. Wornell, and Lizhong Zheng; Matthieu R. Bloch"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.CovertCommunicationSecondOrder
