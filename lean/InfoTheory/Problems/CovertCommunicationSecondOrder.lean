import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CovertCommunicationSecondOrder

/-- KL divergence (in bits) between two nonnegative pmf functions on a finite type. -/
noncomputable def klDivFn {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a : α, if p a ≤ 0 then 0 else p a * log2 (p a / q a)

/-- Maximum message count achievable over a binary-input wiretap DMC `W` (innocent symbol
    `false`) in `n` uses with average error `≤ ε`, KL covertness `≤ δ`, and NO shared key. -/
noncomputable def covertMaxMessagesKeyless {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : WiretapChannel Bool Y Z) (n : ℕ) (ε δ : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ (m kR : ℕ) (enc : Fin m → Fin kR → Fin n → Bool)
    (dec : (Fin n → Y) → Fin m),
    0 < m ∧ 0 < kR ∧ r = (m : ℝ) ∧
    let err := ((1 : ℝ) / ((m * kR : ℕ) : ℝ)) *
      ∑ msg : Fin m, ∑ rnd : Fin kR, ∑ y : Fin n → Y,
        if dec y ≠ msg then
          ∏ i : Fin n, ∑ z : Z, W.trans (enc msg rnd i) (y i, z)
        else 0
    let qZ (z : Fin n → Z) : ℝ := ((1 : ℝ) / ((m * kR : ℕ) : ℝ)) *
      ∑ msg : Fin m, ∑ rnd : Fin kR,
        ∏ i : Fin n, ∑ y : Y, W.trans (enc msg rnd i) (y, z i)
    let q0Pow (z : Fin n → Z) : ℝ :=
      ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i)
    err ≤ ε ∧ klDivFn qZ q0Pow ≤ δ }

/-- Maximum message count achievable over a binary-input wiretap DMC `W` (innocent symbol
    `false`) in `n` uses with average error `≤ ε`, KL covertness `≤ δ`, WITH a shared
    secret key known to encoder and decoder. -/
noncomputable def covertMaxMessagesKeyed {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : WiretapChannel Bool Y Z) (n : ℕ) (ε δ : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ (m kK : ℕ) (enc : Fin m → Fin kK → Fin n → Bool)
    (dec : Fin kK → (Fin n → Y) → Fin m),
    0 < m ∧ 0 < kK ∧ r = (m : ℝ) ∧
    let err := ((1 : ℝ) / ((m * kK : ℕ) : ℝ)) *
      ∑ msg : Fin m, ∑ key : Fin kK, ∑ y : Fin n → Y,
        if dec key y ≠ msg then
          ∏ i : Fin n, ∑ z : Z, W.trans (enc msg key i) (y i, z)
        else 0
    let qZ (z : Fin n → Z) : ℝ := ((1 : ℝ) / ((m * kK : ℕ) : ℝ)) *
      ∑ msg : Fin m, ∑ key : Fin kK,
        ∏ i : Fin n, ∑ y : Y, W.trans (enc msg key i) (y, z i)
    let q0Pow (z : Fin n → Z) : ℝ :=
      ∏ i : Fin n, ∑ y : Y, W.trans false (y, z i)
    err ≤ ε ∧ klDivFn qZ q0Pow ≤ δ }

/-- Keyless second-order (`n^{1/4}`) dispersion conjecture (Tahmasbi–Bloch 2019):
    for every binary-input wiretap DMC in the keyless covert regime
    `D(P₁ ‖ P₀) > D(Q₁ ‖ Q₀) > 0` with `P₁ ≪ P₀` and `Q₁ ≪ Q₀`, does keyless covert
    communication match the key-assisted `n^{1/4}` second-order dispersion? -/
def Statement : Prop :=
  ∀ (kY kZ : ℕ) (W : WiretapChannel Bool (Fin kY) (Fin kZ)),
    0 < kY → 0 < kZ →
    let P0 (y : Fin kY) : ℝ := ∑ z : Fin kZ, W.trans false (y, z)
    let P1 (y : Fin kY) : ℝ := ∑ z : Fin kZ, W.trans true (y, z)
    let Q0 (z : Fin kZ) : ℝ := ∑ y : Fin kY, W.trans false (y, z)
    let Q1 (z : Fin kZ) : ℝ := ∑ y : Fin kY, W.trans true (y, z)
    (∀ (y : Fin kY), P0 y = 0 → P1 y = 0) →
    (∀ (z : Fin kZ), Q0 z = 0 → Q1 z = 0) →
    0 < klDivFn Q1 Q0 →
    klDivFn Q1 Q0 < klDivFn P1 P0 →
    ∀ (ε δ η : ℝ), 0 < ε → ε < (1 : ℝ) / 2 → 0 < δ → 0 < η →
      ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
        log2 (covertMaxMessagesKeyed W n ε δ) - log2 (covertMaxMessagesKeyless W n ε δ) ≤
          η * ((n : ℝ) ^ ((1 : ℝ) / 4))

def problem : OpenProblem where
  id := "covert-communication-second-order"
  title := "Second-Order Asymptotics and Keyless Dispersion of Square-Root-Law Covert Communication"
  category := .securityPrivacy
  status := .open
  posedBy := "Boulat A. Bash, Dennis Goeckel, and Don Towsley; Ligong Wang, Gregory W. Wornell, and Lizhong Zheng; Matthieu R. Bloch"
  posedYear := 2013
  statement := Statement

end InfoTheory.Problems.CovertCommunicationSecondOrder
