import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.CeoProblemGeneral

/-- Operational achievability of `(R₁, R₂, D)` for the two-agent discrete memoryless
    CEO problem with hidden source `Px`, conditionally independent observation channels
    `W₁, W₂`, and distortion measure `d`. -/
def IsCEOAchievable {X Y₁ Y₂ Xh : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Xh]
    (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂) (d : Distortion X Xh)
    (R₁ R₂ D : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))))
    ∃ (enc₁ : (Fin n → Y₁) → Fin M₁)
      (enc₂ : (Fin n → Y₂) → Fin M₂)
      (dec : Fin M₁ × Fin M₂ → Fin n → Xh),
      let Pn (z : Fin n → X × Y₁ × Y₂) : ℝ :=
        ∏ i : Fin n, Px.pmf (z i).1 * W₁.trans (z i).1 (z i).2.1 * W₂.trans (z i).1 (z i).2.2
      let avgD := ∑ z : Fin n → X × Y₁ × Y₂, Pn z *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          d.dist (z i).1 (dec (enc₁ (fun j => (z j).2.1), enc₂ (fun j => (z j).2.2)) i))
      avgD ≤ D + ε

/-- Single-letter Berger–Tung inner bound (with time-sharing) for the two-agent discrete
    memoryless CEO problem. -/
def InCEOBergerTungInner {X Y₁ Y₂ Xh : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Xh]
    (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂) (d : Distortion X Xh)
    (R₁ R₂ D : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ (kQ kU₁ kU₂ : ℕ) (Pq : ProbDist (Fin kQ))
    (Q₁ : Fin kQ × Y₁ → ProbDist (Fin kU₁))
    (Q₂ : Fin kQ × Y₂ → ProbDist (Fin kU₂))
    (g : Fin kU₁ × Fin kU₂ × Fin kQ → Xh)
    (J : ProbDist (Fin kQ × X × Y₁ × Y₂ × Fin kU₁ × Fin kU₂)),
    (∀ q x y₁ y₂ u₁ u₂,
      J.pmf (q, x, y₁, y₂, u₁, u₂) =
        Pq.pmf q * Px.pmf x * W₁.trans x y₁ * W₂.trans x y₂ *
        (Q₁ (q, y₁)).pmf u₁ * (Q₂ (q, y₂)).pmf u₂) ∧
    (∑ t, J.pmf t * d.dist t.2.1 (g (t.2.2.2.2.1, t.2.2.2.2.2, t.1))) ≤ D ∧
    R₁ ≥ condMutualInfo (J.map (fun t => (t.2.2.1, t.2.2.2.2.1, (t.2.2.2.2.2, t.1)))) ∧
    R₂ ≥ condMutualInfo (J.map (fun t => (t.2.2.2.1, t.2.2.2.2.2, (t.2.2.2.2.1, t.1)))) ∧
    R₁ + R₂ ≥ condMutualInfo (J.map (fun t =>
      ((t.2.2.1, t.2.2.2.1), (t.2.2.2.2.1, t.2.2.2.2.2), t.1)))

/-- Closure of the Berger–Tung inner bound for the two-agent discrete memoryless CEO problem. -/
def InCEOBergerTungClosure {X Y₁ Y₂ Xh : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Xh]
    (Px : ProbDist X) (W₁ : DMC X Y₁) (W₂ : DMC X Y₂) (d : Distortion X Xh)
    (R₁ R₂ D : ℝ) : Prop :=
  ∀ ε > 0, InCEOBergerTungInner Px W₁ W₂ d (R₁ + ε) (R₂ + ε) (D + ε)

/-- Binary Hamming distortion on `Bool`. -/
def ceoBinHamming : Distortion Bool Bool where
  dist := fun x y => if x = y then 0 else 1
  nonneg := fun x y => by split_ifs <;> norm_num

/-- Rate-Distortion Region of the Two-Agent Binary Symmetric CEO Problem
    (Berger–Zhang–Viswanathan 1996; Courtade–Weissman 2014):
    For general discrete CEO channels, structured Körner–Marton XOR instances can beat
    Berger–Tung. For the canonical **binary symmetric CEO problem** (`X ~ Bern(1/2)`
    observed through independent `BSC(p₁)` and `BSC(p₂)` under Hamming distortion),
    does the closure of the Berger–Tung inner bound characterize the exact rate-distortion region? -/
def Statement : Prop :=
  ∀ (p₁ p₂ : ℝ) (h10 : 0 < p₁) (h11 : p₁ < 1 / 2) (h20 : 0 < p₂) (h21 : p₂ < 1 / 2)
    (R₁ R₂ D : ℝ),
    0 ≤ D → D ≤ 1 / 2 →
    let W₁ := bsc p₁ (le_of_lt h10) (by linarith)
    let W₂ := bsc p₂ (le_of_lt h20) (by linarith)
    (IsCEOAchievable ProbDist.uniform W₁ W₂ ceoBinHamming R₁ R₂ D ↔
     InCEOBergerTungClosure ProbDist.uniform W₁ W₂ ceoBinHamming R₁ R₂ D)

def problem : OpenProblem where
  id := "ceo-problem-general"
  title := "Rate-Distortion Region of the General Discrete Memoryless CEO Problem"
  category := .sourceCoding
  status := .open
  posedBy := "Toby Berger, Zhen Zhang, and Harish Viswanathan"
  posedYear := 1996
  statement := Statement

end InfoTheory.Problems.CeoProblemGeneral
