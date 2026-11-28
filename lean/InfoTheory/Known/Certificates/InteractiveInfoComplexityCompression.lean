import InfoTheory.Problems.InteractiveInfoComplexityCompression
import InfoTheory.Bridge.CoverThomas

/-!
# Certificate for `InfoTheory.Problems.InteractiveInfoComplexityCompression`

The frozen statement asks for a universal `C` such that every protocol (public and private
coins) computing a Boolean `f` with error `≤ 1/10` under `μ` can be replaced by one with error
`≤ 1/3` and communication `≤ C (IC^ext + 1)`, where `IC^ext = extInfoCost = I(XY; Π | R_pub)`.

## Certified (about exactly `extInfoCost` / `protocolErr`)
* `condMutualInfo_le_log2_card'`: `I(A; B | C) ≤ log₂ |B|`.
* `extInfoCost_nonneg`, `extInfoCost_le_length` (regression, the textbook sandwich
  `0 ≤ IC^ext(π) ≤ C(π)`): the external information cost of a length-`L` protocol lies in
  `[0, L]`. So `extInfoCost` is a genuine information quantity (not a junk value), and the
  Statement interpolates between the trivial bound `C(π') = C(π)` and the conjectured
  `O(IC^ext)`.
* `protocolErr_nonneg`, `protocolErr_le_one`: the error functional is a probability.
* `conclusion_of_short`: the Statement's conclusion is satisfiable by the protocol itself
  whenever `L ≤ C (IC^ext + 1)` (the positivity side-conditions are not an obstruction), so
  `extInfoCost_le_length` gives `Statement`-instances with `C = 1` for every protocol of length
  `L ≤ IC^ext + 1`.

## Not certified
* Barak–Braverman–Chen–Rao compression `O(IC^ext · polylog C(π))`, Braverman–Kol (2018)
  `poly(IC^ext) · log log C(π)`, or the Ganor–Kol–Raz (2016) exponential separation, which is
  for a *search problem* and does not settle this Boolean-function statement.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.InteractiveInfoComplexityCompression

open InfoTheory InfoTheory.Bridge InfoTheory.Problems.InteractiveInfoComplexityCompression

lemma map_snd_eq_snd' {α β : Type*} [Fintype α] [Fintype β] (R : ProbDist (α × β)) :
    R.map Prod.snd = R.snd := by
  classical
  have h : ∀ b, (R.map Prod.snd).pmf b = R.snd.pmf b := by
    intro b
    simp only [ProbDist.map, ProbDist.snd]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single b]
    · simp
    · intro b' _ h; simp [h]
    · simp
  cases hR : R.map Prod.snd
  cases hS : R.snd
  rw [hR, hS] at h
  congr
  funext b
  exact h b

/-- `I(A; B | C) ≤ log₂ |B|`. -/
theorem condMutualInfo_le_log2_card' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Nonempty β] (P : ProbDist (α × β × γ)) : condMutualInfo P ≤ log2 (Fintype.card β) := by
  unfold condMutualInfo
  dsimp only
  have h1 : shannonEntropy (P.map (fun t => (t.1, t.2.2))) ≤ shannonEntropy P :=
    shannonEntropy_map_le _ P
  have h2 := shannonEntropy_subadd (P.map (fun t => (t.2.1, t.2.2)))
  rw [← map_snd_eq_snd', map_comp_eq] at h2
  have h3 := shannonEntropy_le_log2_card (P.map (fun t => (t.2.1, t.2.2))).fst
  have h4 : ((fun x : β × γ => x.2) ∘ fun t : α × β × γ => (t.2.1, t.2.2)) =
      fun t => t.2.2 := rfl
  rw [h4] at h2
  linarith

section

variable {kX kY L kPub kRA kRB : ℕ}

theorem extInfoCost_nonneg (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool) :
    0 ≤ extInfoCost (L := L) μ Ppub PA PB alice bob := by
  unfold extInfoCost
  exact condMutualInfo_nonneg _

/-- **Regression (`IC^ext ≤ C(π)`).** The external information cost of a length-`L` protocol is
    at most `L` bits. -/
theorem extInfoCost_le_length (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool) :
    extInfoCost (L := L) μ Ppub PA PB alice bob ≤ L := by
  unfold extInfoCost
  dsimp only
  refine le_trans (condMutualInfo_le_log2_card' _) (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  unfold log2
  push_cast
  rw [Real.log_pow, mul_div_assoc, div_self (Real.log_pos one_lt_two).ne', mul_one]

theorem protocolErr_nonneg (f : Fin kX × Fin kY → Bool) (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
    (out : Fin kPub → (Fin L → Bool) → Bool) :
    0 ≤ protocolErr f μ Ppub PA PB alice bob out := by
  unfold protocolErr
  refine Finset.sum_nonneg fun xy _ => Finset.sum_nonneg fun r _ =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  have := μ.nonneg xy; have := Ppub.nonneg r; have := PA.nonneg a; have := PB.nonneg b
  split_ifs <;> positivity

theorem protocolErr_le_one (f : Fin kX × Fin kY → Bool) (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
    (out : Fin kPub → (Fin L → Bool) → Bool) :
    protocolErr f μ Ppub PA PB alice bob out ≤ 1 := by
  unfold protocolErr
  have hle : ∀ xy r a b, μ.pmf xy * Ppub.pmf r * PA.pmf a * PB.pmf b *
      (if out r (runPrefix (alice r) (bob r) xy.1 xy.2 a b L) ≠ f xy then (1 : ℝ) else 0) ≤
      μ.pmf xy * Ppub.pmf r * PA.pmf a * PB.pmf b := by
    intro xy r a b
    have := μ.nonneg xy; have := Ppub.nonneg r; have := PA.nonneg a; have := PB.nonneg b
    have h0 : 0 ≤ μ.pmf xy * Ppub.pmf r * PA.pmf a * PB.pmf b := by positivity
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact h0
  calc _ ≤ ∑ xy : Fin kX × Fin kY, ∑ r : Fin kPub, ∑ a : Fin kRA, ∑ b : Fin kRB,
        μ.pmf xy * Ppub.pmf r * PA.pmf a * PB.pmf b :=
        Finset.sum_le_sum fun xy _ => Finset.sum_le_sum fun r _ =>
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hle xy r a b
    _ = 1 := by
        simp only [← Finset.mul_sum, PB.sum_one, mul_one, PA.sum_one, Ppub.sum_one, μ.sum_one]

/-- The conclusion of the Statement is met by the protocol itself whenever it is already short:
    `L ≤ C (IC^ext + 1)`. (Error `≤ 1/10 ≤ 1/3`; all positivity side-conditions hold.) -/
theorem conclusion_of_short (C : ℝ) (f : Fin kX × Fin kY → Bool)
    (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
    (out : Fin kPub → (Fin L → Bool) → Bool)
    (hPub : 0 < kPub) (hRA : 0 < kRA) (hRB : 0 < kRB)
    (herr : protocolErr f μ Ppub PA PB alice bob out ≤ (1 : ℝ) / 10)
    (hshort : (L : ℝ) ≤ C * (extInfoCost (L := L) μ Ppub PA PB alice bob + 1)) :
    ∃ (L' kPub' kRA' kRB' : ℕ)
      (Ppub' : ProbDist (Fin kPub')) (PA' : ProbDist (Fin kRA')) (PB' : ProbDist (Fin kRB'))
      (alice' : Fin kPub' → (t : ℕ) → Fin kX → Fin kRA' → (Fin t → Bool) → Bool)
      (bob' : Fin kPub' → (t : ℕ) → Fin kY → Fin kRB' → (Fin t → Bool) → Bool)
      (out' : Fin kPub' → (Fin L' → Bool) → Bool),
      0 < kPub' ∧ 0 < kRA' ∧ 0 < kRB' ∧
      (L' : ℝ) ≤ C * (extInfoCost (L := L) μ Ppub PA PB alice bob + 1) ∧
      protocolErr f μ Ppub' PA' PB' alice' bob' out' ≤ (1 : ℝ) / 3 :=
  ⟨L, kPub, kRA, kRB, Ppub, PA, PB, alice, bob, out, hPub, hRA, hRB, hshort,
    le_trans herr (by norm_num)⟩

/-- Consequence of the two facts above: with `C = 1`, the Statement's conclusion holds for
    every protocol whose length is at most `IC^ext + 1` (e.g. every protocol with `L ≤ 1`). -/
theorem conclusion_of_length_le_one (f : Fin kX × Fin kY → Bool)
    (μ : ProbDist (Fin kX × Fin kY))
    (Ppub : ProbDist (Fin kPub)) (PA : ProbDist (Fin kRA)) (PB : ProbDist (Fin kRB))
    (alice : Fin kPub → (t : ℕ) → Fin kX → Fin kRA → (Fin t → Bool) → Bool)
    (bob : Fin kPub → (t : ℕ) → Fin kY → Fin kRB → (Fin t → Bool) → Bool)
    (out : Fin kPub → (Fin L → Bool) → Bool)
    (hPub : 0 < kPub) (hRA : 0 < kRA) (hRB : 0 < kRB) (hL : L ≤ 1)
    (herr : protocolErr f μ Ppub PA PB alice bob out ≤ (1 : ℝ) / 10) :
    ∃ (L' kPub' kRA' kRB' : ℕ)
      (Ppub' : ProbDist (Fin kPub')) (PA' : ProbDist (Fin kRA')) (PB' : ProbDist (Fin kRB'))
      (alice' : Fin kPub' → (t : ℕ) → Fin kX → Fin kRA' → (Fin t → Bool) → Bool)
      (bob' : Fin kPub' → (t : ℕ) → Fin kY → Fin kRB' → (Fin t → Bool) → Bool)
      (out' : Fin kPub' → (Fin L' → Bool) → Bool),
      0 < kPub' ∧ 0 < kRA' ∧ 0 < kRB' ∧
      (L' : ℝ) ≤ 1 * (extInfoCost (L := L) μ Ppub PA PB alice bob + 1) ∧
      protocolErr f μ Ppub' PA' PB' alice' bob' out' ≤ (1 : ℝ) / 3 := by
  refine conclusion_of_short 1 f μ Ppub PA PB alice bob out hPub hRA hRB herr ?_
  have := extInfoCost_nonneg (L := L) μ Ppub PA PB alice bob
  have hL' : (L : ℝ) ≤ 1 := by exact_mod_cast hL
  linarith

end

end InfoTheory.Known.Certificates.InteractiveInfoComplexityCompression
