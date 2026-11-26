import InfoTheory.Problems.SpernerCapacityDirectedGraphs
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.SpernerCapacityDirectedGraphs`

**Outcome: the frozen `Statement` is FALSE** (catalog error), see `statement_false`.

The docstring asserts (via Alon's out-degree bound `Σ(D) ≤ log₂(Δ⁺(D)+1)`) that
`Σ(\vec{C}_5) ≤ 1` and asks whether `Σ(\vec{C}_5) < 1`. With the project's definition of
`IsSpernerCode` (for every ordered pair `x ≠ y` there is a coordinate `i` with an edge
`x i → y i`), *every* digraph with at least one edge `u → v` has `Σ(D) ≥ 1`: the
balanced binary words over `{u, v}` of length `2m` with exactly `m` letters `v` form a Sperner
code (for distinct words of equal weight, some coordinate carries `u` in the first word and
`v` in the second), of size `C(2m, m) ≥ 4^m / (2m+1)`, whose rate tends to `1`. This is the
classical observation (via Sperner's theorem) that a single oriented edge already has Sperner
capacity `1`, cf. Gargano–Körner–Vaccaro, *Sperner capacities*, Graphs Combin. 9 (1993) 31–46,
and Körner–Simonyi, *A Sperner-type theorem and qualitative independence*,
J. Combin. Theory Ser. A 59 (1992) 90–103; the non-trivial content of Blokhuis (1993),
Calderbank–Frankl–Graham–Li–Shepp (1993) for `\vec{C}_3` and of Alon (1998) in general is
the *upper* bound `≤ 1`.

Hence `Σ(\vec{C}_5) ≥ 1`, so `Σ(\vec{C}_5) < 1` is false; together with Alon's bound quoted in
the problem docstring, `Σ(\vec{C}_5) = 1`. The catalog entry is therefore not an open problem
as stated and needs to be replaced (e.g. by a genuinely open Sperner-capacity question).

Certified:
* `isSpernerCode_balancedCode` — the balanced code is a Sperner code;
* `card_balancedCode` — it has `C(2m, m)` words;
* `one_sub_log2_le_spernerCapacity` — `1 - log₂(2m+1)/(2m) ≤ Σ(D)` for `m ≥ 1`;
* `one_le_spernerCapacity` — `1 ≤ Σ(D)` whenever `D` has an edge;
* `one_le_spernerCapacity_directedCycle` — `1 ≤ Σ(\vec{C}_5)`;
* `spernerCapacity_directedCycle_le_log2_five` — the trivial upper bound `Σ(\vec{C}_5) ≤ log₂ 5`
  (reused from `InfoTheory.Known`), so the `sSup` is not junk;
* `statement_false : ¬ Statement`.

Not certified: Alon's bound `Σ(\vec{C}_5) ≤ 1` (Alon, *The Shannon capacity of a union*,
Combinatorica 18 (1998); needs the polynomial method), and hence not `Σ(\vec{C}_5) = 1`.
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

/-- **The frozen statement `Σ(\vec{C}_5) < 1` is false.** -/
theorem statement_false :
    ¬ InfoTheory.Problems.SpernerCapacityDirectedGraphs.Statement := fun h =>
  absurd one_le_spernerCapacity_directedCycle (not_le.2 h)

end InfoTheory.Known.Certificates.SpernerCapacityDirectedGraphs
