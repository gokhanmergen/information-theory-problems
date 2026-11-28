import InfoTheory.Problems.SpernerCapacityDirectedGraphs
import InfoTheory.Known
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Certificate for `InfoTheory.Problems.SpernerCapacityDirectedGraphs`

The frozen `Statement` is **Alon's random-tournament conjecture** (Alon 1998, *On the
capacity of digraphs*): a uniformly random tournament `T_n` satisfies
`2^{Σ(T_n)} ≤ c · log₂ n` with probability `→ 1`.

Certified about the exact objects in `Statement`:
* `known_bounds_tournament` — for every tournament `T` on `n ≥ 2` vertices,
  `2 ≤ 2^{Σ(T)} ≤ n`. So the quantity compared with `c · log₂ n` is a genuine (bounded,
  non-junk) supremum, and the conjecture asks for a real improvement over the trivial `≤ n`.
* General lemmas: `one_le_spernerCapacity` (`1 ≤ Σ(D)` for every digraph with an edge, via
  balanced binary codes and `C(2m, m) ≥ 4^m/(2m+1)`; classical, cf. Gargano–Körner–Vaccaro,
  *Sperner capacities*, Graphs Combin. 9 (1993); Körner–Simonyi, JCTA 59 (1992)).

History: the entry previously stated `Σ(\vec{C}_5) < 1`; `one_le_spernerCapacity_directedCycle`
shows that was false (with Alon's out-degree bound `Σ(\vec{C}_m) = 1`), which is why the
entry was replaced (statement-fix commit 0c19d64).

* **Regression** (solved cases): `regression_tournament_two` — every tournament on `2`
  vertices (the exact object `tournamentOfBits 2 ori`) has `Σ = 1`, Sperner's theorem
  (Gargano–Körner–Vaccaro 1993); `regression_complete_symmetric` — the complete symmetric
  digraph on `n` vertices has `Σ = log₂ n = log₂ Θ(K̄_n)` (symmetric-digraph reduction to
  Shannon capacity of the edgeless confusability graph); `regression_empty` — the edgeless
  digraph has `Σ = 0 = log₂ Θ(K_n)`.

Not certified: Alon's construction of tournaments with `2^{Σ} ≥ n/2` and transitive
subtournaments of size `O(log n)`, and the out-degree upper bound.
-/

open scoped BigOperators
open Filter Topology

namespace InfoTheory.Known.Certificates.SpernerCapacityDirectedGraphs

open InfoTheory InfoTheory.Known

variable {V : Type*}

/-- The balanced code: words of length `2m` over `{u, v}` with exactly `m` letters `v`,
indexed by the `m`-subsets `S` of positions carrying `v`. -/
def balancedCode [DecidableEq V] (u v : V) (m : ℕ) : Finset (Fin (2 * m) → V) :=
  (Finset.powersetCard m (Finset.univ : Finset (Fin (2 * m)))).image
    (fun S i => if i ∈ S then v else u)

lemma balancedWord_injective {u v : V} (huv : u ≠ v) (m : ℕ) :
    Function.Injective (fun (S : Finset (Fin (2 * m))) (i : Fin (2 * m)) =>
      if i ∈ S then v else u) := by
  intro S T h
  ext i
  have := congrFun h i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [eq_comm]

/-- The balanced code has `C(2m, m)` codewords. -/
theorem card_balancedCode [DecidableEq V] {u v : V} (huv : u ≠ v) (m : ℕ) :
    (balancedCode u v m).card = (2 * m).choose m := by
  rw [balancedCode, Finset.card_image_of_injective _ (balancedWord_injective huv m),
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The balanced code is a Sperner code for any digraph with an edge `u → v`. -/
theorem isSpernerCode_balancedCode [DecidableEq V] (D : DiGraph V) {u v : V}
    (huv : D.edge u v) (m : ℕ) : IsSpernerCode D (2 * m) (balancedCode u v m) := by
  intro x hx y hy hxy
  simp only [balancedCode, Finset.mem_image, Finset.mem_powersetCard] at hx hy
  obtain ⟨S, ⟨-, hS⟩, rfl⟩ := hx
  obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hy
  have hST : S ≠ T := by rintro rfl; exact hxy rfl
  have hnot : ¬ T ⊆ S := fun hsub =>
    hST (Finset.eq_of_subset_of_card_le hsub (by rw [hS, hT])).symm
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.1 hnot
  exact ⟨i, by simpa [hiT, hiS] using huv⟩

/-- `1 - log₂(2m+1)/(2m) ≤ Σ(D)` for every digraph with an edge and every `m ≥ 1`. -/
theorem one_sub_log2_le_spernerCapacity [Fintype V] (D : DiGraph V) {u v : V}
    (huv : D.edge u v) {m : ℕ} (hm : 0 < m) :
    1 - log2 (2 * m + 1) / (2 * m) ≤ spernerCapacity D := by
  classical
  have hne : u ≠ v := fun h => D.irrefl u (h ▸ huv)
  have hk : 0 < 2 * m := by omega
  have hmem : log2 ((balancedCode u v m).card : ℝ) / ((2 * m : ℕ) : ℝ) ∈
      { r : ℝ | ∃ (k : ℕ) (C : Finset (Fin k → V)),
        0 < k ∧ C.Nonempty ∧ IsSpernerCode D k C ∧ r = log2 (C.card : ℝ) / (k : ℝ) } := by
    refine ⟨2 * m, balancedCode u v m, hk, ?_, isSpernerCode_balancedCode D huv m, rfl⟩
    rw [← Finset.card_pos, card_balancedCode hne]
    exact Nat.choose_pos (by omega)
  refine le_trans ?_ (le_csSup (spernerCapacity_set_bddAbove D) hmem)
  rw [card_balancedCode hne]
  -- `4^m ≤ (2m+1) C(2m,m)`
  have hc := Nat.four_pow_le_two_mul_add_one_mul_centralBinom m
  rw [Nat.centralBinom_eq_two_mul_choose] at hc
  set c := (2 * m).choose m with hcdef
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.choose_pos (by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcR : (4 : ℝ) ^ m ≤ (2 * m + 1) * c := by exact_mod_cast hc
  have hlog : Real.log ((4 : ℝ) ^ m) ≤ Real.log (2 * m + 1) + Real.log c := by
    rw [← Real.log_mul (by positivity) hcpos.ne']
    exact Real.log_le_log (by positivity) hcR
  rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
  push_cast
  simp only [log2]
  rw [sub_le_iff_le_add, div_div, div_div, ← add_div, le_div_iff₀ (by positivity)]
  push_cast at hlog
  nlinarith

/-- `log₂(2m+1)/(2m) → 0`. -/
theorem tendsto_log2_div : Tendsto (fun m : ℕ => log2 (2 * m + 1) / (2 * m)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + (-1))) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h2 : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      (Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop)
  have h3 := (h1.comp h2).const_mul (1 / Real.log 2)
  rw [mul_zero] at h3
  refine h3.congr fun m => ?_
  simp only [Function.comp, log2, pow_one]
  ring_nf

/-- **`Σ(D) ≥ 1` for every digraph with an edge** (balanced binary words; Sperner 1928 /
Körner–Simonyi 1992). -/
theorem one_le_spernerCapacity [Fintype V] (D : DiGraph V) {u v : V} (huv : D.edge u v) :
    1 ≤ spernerCapacity D := by
  have h := (tendsto_log2_div.const_sub 1)
  rw [sub_zero] at h
  refine le_of_tendsto h ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact one_sub_log2_le_spernerCapacity D huv hm

/-- `\vec{C}_5` has the edge `0 → 1`. -/
theorem directedCycle5_edge : (directedCycle 5).edge 0 1 := by
  refine ⟨by decide, by decide⟩

/-- `1 ≤ Σ(\vec{C}_5)`. -/
theorem one_le_spernerCapacity_directedCycle : 1 ≤ spernerCapacity (directedCycle 5) :=
  one_le_spernerCapacity _ directedCycle5_edge

/-- Trivial upper bound `Σ(\vec{C}_5) ≤ log₂ 5` (the `sSup` is not junk). -/
theorem spernerCapacity_directedCycle_le_log2_five :
    spernerCapacity (directedCycle 5) ≤ log2 5 := by
  have := spernerCapacity_le_log2_card (directedCycle 5)
  simpa [ZMod.card] using this

/-- Every tournament on `n ≥ 2` vertices has an edge between vertices `0` and `1`. -/
theorem tournament_has_edge {n : ℕ} (hn : 2 ≤ n)
    (ori : { p : Fin n × Fin n // p.1 < p.2 } → Bool) :
    ∃ u v : Fin n, (InfoTheory.Problems.SpernerCapacityDirectedGraphs.tournamentOfBits n ori).edge u v := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a < b := by simp [a, b, Fin.lt_def]
  cases h : ori ⟨(a, b), hab⟩
  · refine ⟨b, a, ?_⟩
    simp only [InfoTheory.Problems.SpernerCapacityDirectedGraphs.tournamentOfBits,
      not_lt.2 hab.le, dif_neg, not_false_eq_true, hab, dif_pos, h]
  · refine ⟨a, b, ?_⟩
    simp only [InfoTheory.Problems.SpernerCapacityDirectedGraphs.tournamentOfBits, hab, dif_pos, h]

/-- **Certificate for Alon's conjecture:** for every tournament `T` on `n ≥ 2` vertices,
`2 ≤ 2^{Σ(T)} ≤ n`. The lower bound is `one_le_spernerCapacity`; the upper bound is the
trivial `Σ(D) ≤ log₂ |V|`. -/
theorem known_bounds_tournament {n : ℕ} (hn : 2 ≤ n)
    (ori : { p : Fin n × Fin n // p.1 < p.2 } → Bool) :
    let T := InfoTheory.Problems.SpernerCapacityDirectedGraphs.tournamentOfBits n ori
    2 ≤ (2 : ℝ) ^ spernerCapacity T ∧ (2 : ℝ) ^ spernerCapacity T ≤ n := by
  intro T
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨u, v, huv⟩ := tournament_has_edge hn ori
  have h1 : 1 ≤ spernerCapacity T := one_le_spernerCapacity T huv
  have h2 : spernerCapacity T ≤ log2 (Fintype.card (Fin n)) := spernerCapacity_le_log2_card T
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨?_, ?_⟩
  · calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ spernerCapacity T := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  · calc (2 : ℝ) ^ spernerCapacity T ≤ 2 ^ log2 (Fintype.card (Fin n)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      _ = n := by
          rw [Fintype.card_fin]
          have : log2 (n : ℝ) = Real.logb 2 n := rfl
          rw [this, Real.rpow_logb (by norm_num) (by norm_num) hn0]

/-! ### Regression: solved cases -/

/-- **Regression** (Sperner's theorem): every tournament on two vertices has `Σ = 1`. -/
theorem regression_tournament_two (ori : { p : Fin 2 × Fin 2 // p.1 < p.2 } → Bool) :
    spernerCapacity (InfoTheory.Problems.SpernerCapacityDirectedGraphs.tournamentOfBits 2 ori)
      = 1 := by
  obtain ⟨u, v, huv⟩ := tournament_has_edge le_rfl ori
  refine le_antisymm ?_ (one_le_spernerCapacity _ huv)
  have := spernerCapacity_le_log2_card
    (InfoTheory.Problems.SpernerCapacityDirectedGraphs.tournamentOfBits 2 ori)
  simpa [log2, div_self (Real.log_pos one_lt_two).ne'] using this

/-- The complete symmetric digraph (`u → v` for all `u ≠ v`). -/
def completeDi (n : ℕ) : DiGraph (Fin n) where
  edge u v := u ≠ v
  irrefl _ h := h rfl

/-- The edgeless digraph. -/
def emptyDi (n : ℕ) : DiGraph (Fin n) where
  edge _ _ := False
  irrefl _ h := h

/-- **Regression** (symmetric digraphs reduce to Shannon capacity): the complete symmetric
digraph on `n ≥ 1` vertices has `Σ = log₂ n`. -/
theorem regression_complete_symmetric (n : ℕ) [NeZero n] :
    spernerCapacity (completeDi n) = log2 n := by
  classical
  refine le_antisymm (by simpa using spernerCapacity_le_log2_card (completeDi n)) ?_
  refine le_csSup (spernerCapacity_set_bddAbove _) ⟨1, Finset.univ, one_pos,
    Finset.univ_nonempty, fun x _ y _ hxy => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    exact ⟨i, hi⟩
  · simp

/-- **Regression**: the edgeless digraph on `n ≥ 1` vertices has `Σ = 0` (codes have one word). -/
theorem regression_empty (n : ℕ) [NeZero n] : spernerCapacity (emptyDi n) = 0 := by
  refine le_antisymm (csSup_le ⟨0, 1, {fun _ => 0}, one_pos, by simp,
    fun x hx y hy hxy => absurd ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm)
      hxy, by simp [log2]⟩ ?_) (spernerCapacity_nonneg _)
  rintro r ⟨k, C, -, hC, hcode, rfl⟩
  have hcard : C.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => by
    by_contra hxy
    obtain ⟨i, hi⟩ := hcode x hx y hy hxy
    exact hi
  have h1 : C.card = 1 := le_antisymm hcard (Finset.card_pos.2 hC)
  simp [h1, log2]

end InfoTheory.Known.Certificates.SpernerCapacityDirectedGraphs
