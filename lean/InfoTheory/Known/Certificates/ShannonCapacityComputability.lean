import InfoTheory.Problems.ShannonCapacityComputability
import InfoTheory.Known.ZeroError

/-!
# Certificate for `InfoTheory.Problems.ShannonCapacityComputability`

The frozen statement asks for a register machine that, on input `(n, code, m)`, halts with a
rational `num / den` within `1 / m` of `shannonCapacity (graphOfCode n code)`. The certificate
checks that the instance encoding and the target quantity are the intended ones, i.e. that the
machine would really have to approximate `Θ(G)` on genuine graphs (no junk value).

## Certified
* `graphOfCode_cycle5`, `shannonCapacity_graphOfCode_cycle5`: the bitmask `1581186`
  (bits `1, 7, 13, 19, 20` = edges `01, 12, 23, 34, 40`) decodes to the pentagon `C₅`, and the
  quantity the machine must approximate on it is `Θ(C₅) = √5` (Lovász 1979, Thm. 2; reuses
  `Known.shannonCapacity_cycle5`). So a correct machine must output an approximation of the
  irrational `√5`: the target is not a junk rational constant.
* `graphOfCode_zero`, `shannonCapacity_graphOfCode_zero`: code `0` is the edgeless graph on
  `n` vertices and its target value is `Θ = n` (perfect graph; Shannon 1956).
* `graphOfCode_complete3`, `shannonCapacity_graphOfCode_complete3`: code `511` is `K₃` and the
  target value is `Θ(K₃) = 1` (every strong power of a complete graph is complete).
* `shannonCapacity_graphOfCode_mem_Icc`: for every encodable input, `1 ≤ Θ ≤ n`, so the
  target is a finite real in a known bounded range and `num / den` with `num, den ∈ ℕ` can
  approximate it (no sign or overflow obstruction).
* `initRegs_input`: the input registers `0, 1, 2` hold `n`, `code`, `m`.

## Adversarial check (2026-11-27)
The Statement is faithful: Borel–Turing computability of `Θ(G)` from a finite description of
`G` is the open problem recorded by Boche and Deppe ("Computability of the zero-error capacity
of noisy channels", arXiv:2010.06873; journal version *Information* 16(7), 2025), who note
that it remains completely open. Their non-computability results concern the zero-error
capacity as a function of channels with computable *real* transition probabilities (where
the confusability graph itself is not computable from the input); they do not bear on the
finite-graph input used here.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ShannonCapacityComputability

open InfoTheory InfoTheory.Known InfoTheory.Problems.ShannonCapacityComputability

/-- The input registers hold exactly `(n, code, m)`. -/
theorem initRegs_input (numRegs n code m : ℕ) (h : 3 ≤ numRegs) :
    initRegs numRegs n code m ⟨0, by omega⟩ = n ∧
    initRegs numRegs n code m ⟨1, by omega⟩ = code ∧
    initRegs numRegs n code m ⟨2, by omega⟩ = m := by
  simp [initRegs]

/-- The bitmask of the pentagon: bits `1, 7, 13, 19, 20` (edges `01, 12, 23, 34, 40`). -/
def codeC5 : ℕ := 2 ^ 1 + 2 ^ 7 + 2 ^ 13 + 2 ^ 19 + 2 ^ 20

/-- `codeC5` decodes to the pentagon `C₅ = cycleGraph 5` (on `ZMod 5 = Fin 5`). -/
theorem graphOfCode_cycle5 : graphOfCode 5 codeC5 = cycleGraph 5 := by
  ext i j
  show (i ≠ j ∧ ((codeC5 / 2 ^ (i.1 * 5 + j.1)) % 2 = 1 ∨ (codeC5 / 2 ^ (j.1 * 5 + i.1)) % 2 = 1))
    ↔ (i ≠ j ∧ ((i : ZMod 5) - j = 1 ∨ (j : ZMod 5) - i = 1))
  revert i j
  decide

/-- **Regression:** on the pentagon the machine must approximate `Θ(C₅) = √5`
(Lovász 1979). -/
theorem shannonCapacity_graphOfCode_cycle5 :
    shannonCapacity (graphOfCode 5 codeC5) = Real.sqrt 5 := by
  rw [graphOfCode_cycle5]
  have h : ∀ i₁ i₂ : Fintype (ZMod 5),
      @shannonCapacity _ i₁ (cycleGraph 5) = @shannonCapacity _ i₂ (cycleGraph 5) :=
    fun i₁ i₂ => by rw [Subsingleton.elim i₁ i₂]
  exact (h _ _).trans shannonCapacity_cycle5

/-- Code `0` decodes to the edgeless graph. -/
theorem graphOfCode_zero (n : ℕ) : graphOfCode n 0 = ⊥ := by
  ext i j
  simp [graphOfCode]

/-- **Regression:** the edgeless graph on `n` vertices has `Θ = n`. -/
theorem shannonCapacity_graphOfCode_zero (n : ℕ) :
    shannonCapacity (graphOfCode n 0) = n := by
  apply le_antisymm
  · simpa using shannonCapacity_le_card (graphOfCode n 0)
  · have hind : IsIndepSet (graphOfCode n 0) Finset.univ := by
      intro u _ v _ h
      rw [graphOfCode_zero] at h
      exact h
    have h1 := card_le_indepNumber hind
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact (Nat.cast_le.2 h1).trans (le_shannonCapacity _)

/-- Code `511` (all nine bits) decodes to the complete graph `K₃`. -/
theorem graphOfCode_complete3 : graphOfCode 3 511 = ⊤ := by
  ext i j
  show (i ≠ j ∧ ((511 / 2 ^ (i.1 * 3 + j.1)) % 2 = 1 ∨ (511 / 2 ^ (j.1 * 3 + i.1)) % 2 = 1))
    ↔ i ≠ j
  revert i j
  decide

/-- Strong powers of a complete graph have independence number at most `1`. -/
theorem indepNumber_strongPower_top_le {V : Type*} [Fintype V] (k : ℕ) :
    indepNumber (strongPower (⊤ : SimpleGraph V) k) ≤ 1 := by
  rw [indepNumber_le_iff]
  intro S hS
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  refine hS a ha b hb ⟨hab, fun i => ?_⟩
  by_cases h : a i = b i
  · exact Or.inl h
  · exact Or.inr h

/-- **Regression:** `Θ(K₃) = 1`. -/
theorem shannonCapacity_graphOfCode_complete3 :
    shannonCapacity (graphOfCode 3 511) = 1 := by
  rw [graphOfCode_complete3]
  apply le_antisymm
  · rw [shannonCapacity_le_iff]
    intro k _
    have h1 : (indepNumber (strongPower (⊤ : SimpleGraph (Fin 3)) k) : ℝ) ≤ 1 := by
      exact_mod_cast indepNumber_strongPower_top_le k
    calc ((indepNumber (strongPower (⊤ : SimpleGraph (Fin 3)) k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ))
        ≤ (1 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by positivity)
      _ = 1 := Real.one_rpow _
  · exact one_le_shannonCapacity _

/-- For every encodable input (`n ≥ 1`), the target value lies in `[1, n]`. -/
theorem shannonCapacity_graphOfCode_mem_Icc (n code : ℕ) (hn : 0 < n) :
    1 ≤ shannonCapacity (graphOfCode n code) ∧ shannonCapacity (graphOfCode n code) ≤ n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨one_le_shannonCapacity _, by simpa using shannonCapacity_le_card (graphOfCode n code)⟩

end InfoTheory.Known.Certificates.ShannonCapacityComputability
