import InfoTheory.Problems.MrsGerberGeneral
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.Mathlib
import InfoTheory.Known.Entropy
import InfoTheory.Known.Operational

/-!
# Certificate for `InfoTheory.Problems.MrsGerberGeneral`

The frozen statement asks that `u ↦ f_q(u, v)` be convex on `[0, log₂ q]` for every cyclic
group `ℤ/qℤ` (`q ≥ 2`), where `f_q = minCyclicSumEntropy` is an `sInf` of `H(X + Y mod q)`
over independent `X, Y` with `H(X) ≥ u`, `H(Y) ≥ v`.

Certified here, about the *exact* `minCyclicSumEntropy` of `Statement` (no junk values):
* `sumSet_nonempty`, `sumSet_bddBelow` — for `u, v ≤ log₂ q` the `sInf` is over a nonempty set
  bounded below (uniform `X, Y` are feasible), so `f_q(u, v)` is a genuine infimum on the whole
  square `[0, log₂ q]²` quantified in `Statement`;
* `entropy_add_ge_left`, `entropy_add_ge_right` — `H(X + Y) ≥ max(H(X), H(Y))` for independent
  `X, Y` on `ℤ/qℤ` (the trivial lower bound behind Mrs. Gerber-type inequalities);
* `max_le_minCyclicSumEntropy` — `max(u, v) ≤ f_q(u, v)` on the square;
* `minCyclicSumEntropy_le_log2` — `f_q(u, v) ≤ log₂ q` on the square;
* `minCyclicSumEntropy_mono_left` — `f_q` is nondecreasing in `u`;
* **boundary values (regressions):** `minCyclicSumEntropy_zero_zero` — `f_q(0, 0) = 0`
  (point masses), and `minCyclicSumEntropy_log2_left` — `f_q(log₂ q, v) = log₂ q`.

Not certified: Wyner–Ziv's `q = 2` formula `f_2(u, v) = h(h⁻¹(u) ⋆ h⁻¹(v))` (would need the
`Fin 2`/`Bool` transfer of `Bridge.MrsGerber`), the Jog–Anantharam `2^m` theorem, or any
convexity statement. The `Statement` itself is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MrsGerberGeneral

open InfoTheory InfoTheory.Problems.MrsGerberGeneral

/-- The cyclic sum map `(x, y) ↦ x + y mod q`. -/
def cycAdd (q : ℕ) (hq : 0 < q) (xy : Fin q × Fin q) : Fin q :=
  ⟨(xy.1.1 + xy.2.1) % q, Nat.mod_lt _ hq⟩

/-- `(x, y) ↦ (x + y mod q, y)` is injective. -/
theorem cycShear_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (fun xy : Fin q × Fin q => (cycAdd q hq xy, xy.2)) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  simp only [Prod.mk.injEq, cycAdd, Fin.ext_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext ?_ (Fin.ext h2)
  apply Fin.ext
  have hx1 := x₁.2; have hx2 := x₂.2
  rw [h2] at h1
  have := Nat.ModEq.add_right_cancel' y₂.1 h1
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hx2] at this

/-- `H(X + Y) ≥ H(X)` for independent `X, Y` on `ℤ/qℤ`. -/
theorem entropy_add_ge_left (q : ℕ) (hq : 0 < q) (P Q : ProbDist (Fin q)) :
    shannonEntropy P ≤ shannonEntropy ((P.prod Q).map (cycAdd q hq)) := by
  set S := (P.prod Q).map (fun xy : Fin q × Fin q => (cycAdd q hq xy, xy.2))
  have hS : shannonEntropy S = shannonEntropy P + shannonEntropy Q := by
    rw [Known.Operational.shannonEntropy_map_of_injective _ (cycShear_injective q hq),
      Bridge.shannonEntropy_prod]
  have hfst : S.fst = (P.prod Q).map (cycAdd q hq) := by
    rw [← Known.Operational.map_fst_eq_fst, Bridge.map_comp_eq]; rfl
  have hsnd : shannonEntropy S.snd = shannonEntropy Q := by
    rw [← Known.Operational.map_snd_eq_snd, Bridge.map_comp_eq]
    show shannonEntropy ((P.prod Q).map Prod.snd) = _
    rw [Known.Operational.map_snd_eq_snd, Known.shannonEntropy_prod_snd]
  have := Known.shannonEntropy_le_add S
  rw [hS, hfst, hsnd] at this
  linarith

/-- `H(X + Y) ≥ H(Y)` for independent `X, Y` on `ℤ/qℤ`. -/
theorem entropy_add_ge_right (q : ℕ) (hq : 0 < q) (P Q : ProbDist (Fin q)) :
    shannonEntropy Q ≤ shannonEntropy ((P.prod Q).map (cycAdd q hq)) := by
  have hswap : (P.prod Q).map (cycAdd q hq) = (Q.prod P).map (cycAdd q hq) := by
    have h1 : (P.prod Q) = (Q.prod P).map Prod.swap := by
      refine Known.Operational.probDist_eq_of_pmf fun ab => ?_
      classical
      simp only [ProbDist.map, ProbDist.prod]
      rw [Finset.sum_eq_single (ab.2, ab.1)]
      · simp [mul_comm]
      · intro b _ hb
        have : Prod.swap b ≠ ab := fun h => hb (by rw [← h]; rfl)
        simp [this]
      · simp
    rw [h1, Bridge.map_comp_eq]
    congr 1
    funext xy
    simp only [Function.comp_apply, cycAdd, Prod.fst_swap, Prod.snd_swap, Nat.add_comm]
  rw [hswap]; exact entropy_add_ge_left q hq Q P

/-! ### The infimum is well defined on the square -/

/-- The set whose `sInf` is `minCyclicSumEntropy q hq u v`. -/
def sumSet (q : ℕ) (hq : 0 < q) (u v : ℝ) : Set ℝ :=
  { r : ℝ | ∃ (P Q : ProbDist (Fin q)),
    u ≤ shannonEntropy P ∧ v ≤ shannonEntropy Q ∧
    r = shannonEntropy ((P.prod Q).map
      (fun xy => (⟨(xy.1.1 + xy.2.1) % q, Nat.mod_lt _ hq⟩ : Fin q))) }

theorem minCyclicSumEntropy_eq (q : ℕ) (hq : 0 < q) (u v : ℝ) :
    minCyclicSumEntropy q hq u v = sInf (sumSet q hq u v) := rfl

theorem sumSet_bddBelow (q : ℕ) (hq : 0 < q) (u v : ℝ) : BddBelow (sumSet q hq u v) :=
  ⟨0, by rintro r ⟨P, Q, -, -, rfl⟩; exact Bridge.shannonEntropy_nonneg _⟩

theorem sumSet_nonempty (q : ℕ) (hq : 0 < q) {u v : ℝ} (hu : u ≤ log2 (q : ℝ))
    (hv : v ≤ log2 (q : ℝ)) : (sumSet q hq u v).Nonempty := by
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  refine ⟨_, ProbDist.uniform, ProbDist.uniform, ?_, ?_, rfl⟩ <;>
    rwa [Known.shannonEntropy_uniform, Fintype.card_fin]

theorem max_le_minCyclicSumEntropy (q : ℕ) (hq : 0 < q) {u v : ℝ} (hu : u ≤ log2 (q : ℝ))
    (hv : v ≤ log2 (q : ℝ)) : max u v ≤ minCyclicSumEntropy q hq u v := by
  refine le_csInf (sumSet_nonempty q hq hu hv) ?_
  rintro r ⟨P, Q, hP, hQ, rfl⟩
  exact max_le (hP.trans (entropy_add_ge_left q hq P Q)) (hQ.trans (entropy_add_ge_right q hq P Q))

theorem minCyclicSumEntropy_le_log2 (q : ℕ) (hq : 0 < q) {u v : ℝ} (hu : u ≤ log2 (q : ℝ))
    (hv : v ≤ log2 (q : ℝ)) : minCyclicSumEntropy q hq u v ≤ log2 (q : ℝ) := by
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨r, hr⟩ := sumSet_nonempty q hq hu hv
  refine (csInf_le (sumSet_bddBelow q hq u v) hr).trans ?_
  obtain ⟨P, Q, -, -, rfl⟩ := hr
  simpa using Bridge.shannonEntropy_le_log2_card ((P.prod Q).map
    (fun xy => (⟨(xy.1.1 + xy.2.1) % q, Nat.mod_lt _ hq⟩ : Fin q)))

/-- `f_q` is nondecreasing in its first argument. -/
theorem minCyclicSumEntropy_mono_left (q : ℕ) (hq : 0 < q) {u u' v : ℝ} (huu : u ≤ u')
    (hu' : u' ≤ log2 (q : ℝ)) (hv : v ≤ log2 (q : ℝ)) :
    minCyclicSumEntropy q hq u v ≤ minCyclicSumEntropy q hq u' v := by
  refine csInf_le_csInf (sumSet_bddBelow q hq u v) (sumSet_nonempty q hq hu' hv) ?_
  rintro r ⟨P, Q, hP, hQ, rfl⟩
  exact ⟨P, Q, huu.trans hP, hQ, rfl⟩

/-- Point mass on `0 : ℤ/qℤ`. -/
def dirac0 (q : ℕ) (hq : 0 < q) : ProbDist (Fin q) where
  pmf a := if a = ⟨0, hq⟩ then 1 else 0
  nonneg a := by split_ifs <;> norm_num
  sum_one := by simp

theorem entropy_of_zero_one {α : Type*} [Fintype α] (P : ProbDist α)
    (h : ∀ a, P.pmf a = 0 ∨ P.pmf a = 1) : shannonEntropy P = 0 := by
  unfold shannonEntropy
  refine Finset.sum_eq_zero fun a _ => ?_
  rcases h a with h | h <;> rw [h] <;> simp [negPLogP, log2]

/-- **Boundary value**: `f_q(0, 0) = 0` (two point masses). -/
theorem minCyclicSumEntropy_zero_zero (q : ℕ) (hq : 0 < q) (hq2 : 2 ≤ q) :
    minCyclicSumEntropy q hq 0 0 = 0 := by
  have hlog : (0 : ℝ) ≤ log2 (q : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))
      (Real.log_pos one_lt_two).le
  refine le_antisymm ?_ (le_csInf (sumSet_nonempty q hq hlog hlog) ?_)
  · refine csInf_le (sumSet_bddBelow q hq 0 0) ⟨dirac0 q hq, dirac0 q hq,
      Bridge.shannonEntropy_nonneg _, Bridge.shannonEntropy_nonneg _, ?_⟩
    symm
    apply entropy_of_zero_one
    intro b
    classical
    simp only [ProbDist.map, ProbDist.prod, dirac0, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (⟨0, hq⟩, ⟨0, hq⟩)]
    · simp only [if_true]; split_ifs <;> simp
    · rintro ⟨x, y⟩ _ hne
      by_cases hy : y = ⟨0, hq⟩ <;> by_cases hx : x = ⟨0, hq⟩ <;> simp_all
    · simp
  · rintro r ⟨P, Q, -, -, rfl⟩; exact Bridge.shannonEntropy_nonneg _

/-- **Boundary value**: `f_q(log₂ q, v) = log₂ q` for every `v ≤ log₂ q`. -/
theorem minCyclicSumEntropy_log2_left (q : ℕ) (hq : 0 < q) {v : ℝ} (hv : v ≤ log2 (q : ℝ)) :
    minCyclicSumEntropy q hq (log2 (q : ℝ)) v = log2 (q : ℝ) :=
  le_antisymm (minCyclicSumEntropy_le_log2 q hq le_rfl hv)
    ((le_max_left _ _).trans (max_le_minCyclicSumEntropy q hq le_rfl hv))

end InfoTheory.Known.Certificates.MrsGerberGeneral
