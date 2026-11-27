import InfoTheory.Problems.ZeroErrorSourceCodingSideInfo
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ZeroErrorSourceCodingSideInfo`

The frozen statement asks whether a register machine can approximate Witsenhausen's
zero-error side-information rate `witsenhausenRate (graphOfCode n code)` to within `1/m`.

## Certified (about exactly these objects)
* `witsenhausenRate_nonneg` — `R₀(G) ≥ 0`.
* `witsenhausenRate_le_log2_of_coloring` — `R₀(G) ≤ log₂ m` for every proper `m`-coloring
  (so `R₀(G) ≤ log₂ χ(G)`), and `witsenhausenRate_le_log2_card` — `R₀(G) ≤ log₂ |V|`
  (Witsenhausen 1976).
* `log2_clique_le_witsenhausenRate` — the clique lower bound `log₂ ω(G) ≤ R₀(G)`
  (Witsenhausen 1976).
* `witsenhausenRate_top`, `witsenhausenRate_bot` — exact values `log₂ |V|` for complete
  graphs and `0` for edgeless graphs (perfect-graph cases `R₀ = log₂ ω`).
* `graphOfCode_zero`, `witsenhausenRate_graphOfCode_zero`, `witsenhausenRate_graphOfCode_mem`
  — for the exact graphs of `Statement`: every target lies in `[0, log₂ n]`, and the
  bitmask `0` gives target `0`; the targets are genuine reals, not junk.

## Not certified
* The Lovász-theta / Shannon-capacity bounds `log₂(n/Θ(G)) ≤ R₀(G)` and `R₀(C₅) = log₂ √5`
  (need the strong-product/complement duality; not attempted).
* Upper semicomputability of `R₀` (it is an infimum of computable quantities): requires
  formalizing register-machine programs for chromatic numbers of strong powers.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ZeroErrorSourceCodingSideInfo

open InfoTheory InfoTheory.Problems.ZeroErrorSourceCodingSideInfo

section Witsenhausen

variable {V : Type*} [Fintype V]

/-- `R₀(G) ≥ 0`: every element `log₂ m / k` of the defining set is nonnegative. -/
theorem witsenhausenRate_nonneg (G : SimpleGraph V) : 0 ≤ witsenhausenRate G := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨k, m, c, hk, hm, -, rfl⟩
  refine div_nonneg ?_ (Nat.cast_nonneg k)
  unfold log2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (Real.log_pos one_lt_two).le

/-- **Coloring upper bound** `R₀(G) ≤ log₂ m` for any proper `m`-coloring of `G`
    (Witsenhausen 1976; in particular `R₀(G) ≤ log₂ χ(G)`). -/
theorem witsenhausenRate_le_log2_of_coloring (G : SimpleGraph V) {m : ℕ} (hm : 0 < m)
    (c : V → Fin m) (hc : ∀ x y, G.Adj x y → c x ≠ c y) : witsenhausenRate G ≤ log2 m := by
  have hmem : log2 (m : ℝ) / ((1 : ℕ) : ℝ) ∈ { r : ℝ | ∃ (k : ℕ) (m : ℕ) (c : (Fin k → V) → Fin m),
      0 < k ∧ 0 < m ∧ (∀ x y, (strongPower G k).Adj x y → c x ≠ c y) ∧
      r = log2 (m : ℝ) / (k : ℝ) } := by
    refine ⟨1, m, fun x => c (x 0), one_pos, hm, ?_, rfl⟩
    rintro x y ⟨hne, h⟩
    have h0 : x 0 ≠ y 0 := fun h0 => hne (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h0)
    rcases h 0 with h' | h'
    · exact absurd h' h0
    · exact hc _ _ h'
  have := csInf_le ⟨0, by
    rintro r ⟨k, m, c, hk, hm, -, rfl⟩
    refine div_nonneg ?_ (Nat.cast_nonneg k)
    unfold log2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (Real.log_pos one_lt_two).le⟩ hmem
  rw [Nat.cast_one, div_one] at this
  exact this

/-- `R₀(G) ≤ log₂ |V|` (color every vertex differently). -/
theorem witsenhausenRate_le_log2_card [Nonempty V] (G : SimpleGraph V) :
    witsenhausenRate G ≤ log2 (Fintype.card V) :=
  witsenhausenRate_le_log2_of_coloring G Fintype.card_pos (Fintype.equivFin V)
    fun x y h => (Fintype.equivFin V).injective.ne (G.ne_of_adj h)

/-- **Clique lower bound** `log₂ ω(G) ≤ R₀(G)` (Witsenhausen 1976): for any clique `S`, every
    zero-error code for `G^{⊠k}` must separate all `|S|^k` tuples from `S^k`. -/
theorem log2_clique_le_witsenhausenRate [Nonempty V] (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) : log2 (S.card : ℝ) ≤ witsenhausenRate G := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, log2, Real.log_zero, zero_div]
    exact witsenhausenRate_nonneg G
  refine le_csInf ⟨_, 1, Fintype.card V, fun x => Fintype.equivFin V (x 0), one_pos,
    Fintype.card_pos, fun x y ⟨hne, _⟩ => ?_, rfl⟩ ?_
  · intro h
    exact hne (funext fun i => by
      rw [Fin.fin_one_eq_zero i]; exact (Fintype.equivFin V).injective h)
  rintro r ⟨k, m, c, hk, hm, hc, rfl⟩
  -- the code is injective on `S^k`
  let f : (Fin k → S) → Fin m := fun s => c (fun i => (s i).1)
  have hf : Function.Injective f := by
    intro s t hst
    by_contra hne
    have hne' : (fun i => (s i).1) ≠ (fun i => (t i).1) := fun h =>
      hne (funext fun i => Subtype.ext (congrFun h i))
    refine hc _ _ ⟨hne', fun i => ?_⟩ hst
    by_cases hi : (s i).1 = (t i).1
    · exact Or.inl hi
    · exact Or.inr (hS _ (s i).2 _ (t i).2 hi)
  have hcard : S.card ^ k ≤ m := by
    have := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_fun, Fintype.card_coe] using this
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hk']
  have h1 : log2 ((S.card : ℝ) ^ k) ≤ log2 (m : ℝ) := by
    unfold log2
    refine div_le_div_of_nonneg_right (Real.log_le_log (by positivity) ?_)
      (Real.log_pos one_lt_two).le
    exact_mod_cast hcard
  have h2 : log2 ((S.card : ℝ) ^ k) = k * log2 (S.card : ℝ) := by
    unfold log2; rw [Real.log_pow]; ring
  linarith

/-- For the complete graph, `R₀(K_V) = log₂ |V|`. -/
theorem witsenhausenRate_top [Nonempty V] [DecidableEq V] :
    witsenhausenRate (⊤ : SimpleGraph V) = log2 (Fintype.card V) := by
  refine le_antisymm (witsenhausenRate_le_log2_card _) ?_
  have := log2_clique_le_witsenhausenRate (⊤ : SimpleGraph V) Finset.univ
    (fun x _ y _ h => h)
  simpa using this

/-- For the edgeless graph, `R₀ = 0`. -/
theorem witsenhausenRate_bot : witsenhausenRate (⊥ : SimpleGraph V) = 0 := by
  refine le_antisymm ?_ (witsenhausenRate_nonneg _)
  have := witsenhausenRate_le_log2_of_coloring (⊥ : SimpleGraph V) one_pos (fun _ => 0)
    (fun x y h => h.elim)
  simpa [log2] using this

end Witsenhausen

/-! ### The graphs of `Statement` -/

/-- The bitmask `0` encodes the edgeless graph, whose rate is `0`; so the target values of
    `Statement` include genuine (non-junk) reals. -/
theorem graphOfCode_zero (n : ℕ) : graphOfCode n 0 = ⊥ := by
  ext i j
  simp [graphOfCode]

theorem witsenhausenRate_graphOfCode_zero (n : ℕ) : witsenhausenRate (graphOfCode n 0) = 0 := by
  rw [graphOfCode_zero]; exact witsenhausenRate_bot

/-- Every target value of `Statement` lies in `[0, log₂ n]`. -/
theorem witsenhausenRate_graphOfCode_mem (n code : ℕ) (hn : 0 < n) :
    0 ≤ witsenhausenRate (graphOfCode n code) ∧
      witsenhausenRate (graphOfCode n code) ≤ log2 n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨witsenhausenRate_nonneg _, ?_⟩
  simpa using witsenhausenRate_le_log2_card (graphOfCode n code)

end InfoTheory.Known.Certificates.ZeroErrorSourceCodingSideInfo
