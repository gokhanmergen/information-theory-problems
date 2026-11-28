import InfoTheory.Problems.ShannonCapacityC7
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ShannonCapacityC7`

The frozen statement is `shannonCapacity (cycleGraph 7) < lovaszTheta (cycleGraph 7)`. Its
docstring claims `367^{1/5} ≤ Θ(C₇) ≤ ϑ(C₇) = 7 cos(π/7) / (1 + cos(π/7)) ≈ 3.3177`.

Certified here, about the exact objects in `Statement`:
* `three_le_shannonCapacity_cycle7` — `3 ≤ Θ(C₇)` (`α(C₇) = 3`, Shannon 1956);
* `indepNumber_strongPower_cycle7_two_ge` — `α(C₇ ⊠ C₇) ≥ 10` (explicit independent set,
  checked by `decide`; the value `α(C₇²) = 10` is classical, see e.g. Hales, *Numerical
  invariants and the strong product of graphs*, J. Combin. Theory B 15 (1973));
* `sqrt10_le_shannonCapacity_cycle7` — `√10 ≤ Θ(C₇)`;
* `shannonCapacity_cycle7_le_lovaszTheta` — `Θ(C₇) ≤ ϑ(C₇)` (Lovász 1979, Theorem 1, reused);
* `lovaszTheta_cycle7_le` — `ϑ(C₇) ≤ 7 cos(π/7)/(1 + cos(π/7))`, via an explicit
  orthonormal representation in `ℝ⁵` (the circulant "Fourier" representation, Lovász 1979,
  Corollary 5): `u_a = (√C, √B cos θ_a, √B sin θ_a, √A cos 2θ_a, √A sin 2θ_a)`,
  `θ_a = 2πa/7`, with handle `c = e₀`;
* `lovaszTheta_cycle7_lt` — `ϑ(C₇) < 7/2`;
* `sqrt10_le_lovaszTheta_cycle7` — so `√10 ≤ Θ(C₇) ≤ ϑ(C₇) < 7/2`, i.e. neither side of the
  strict inequality is a junk value and the `Statement` is not trivially settled.

* **Regression** (solved cases of the same objects `shannonCapacity`, `lovaszTheta`,
  `cycleGraph`): `regression_cycle4` — `Θ(C₄) = 2 = α(C₄)` (even cycle, perfect graph;
  upper bound by the clique cover `{0,1}, {2,3}`); `regression_cycle5_not_strict` — for `C₅`
  the analogue of the `Statement` is **false**: `Θ(C₅) = ϑ(C₅) = √5` (Lovász 1979), so the
  strict separation asked for `C₇` genuinely fails for the pentagon;
  `regression_complete` — `Θ(K_n) = 1`.

Not certified:
* `367^{1/5} ≤ Θ(C₇)` (Polak–Schrijver 2019, needs a 367-word independent set in `C₇^{⊠5}`);
* the matching lower bound `ϑ(C₇) ≥ 7 cos(π/7)/(1+cos(π/7))` (needs the dual/eigenvalue
  characterisation of `ϑ`, not available for the project's primal definition).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ShannonCapacityC7

open InfoTheory InfoTheory.Known

/-- `3 ≤ Θ(C₇)`. -/
theorem three_le_shannonCapacity_cycle7 : (3 : ℝ) ≤ shannonCapacity (cycleGraph 7) := by
  have h := le_shannonCapacity (cycleGraph 7)
  rw [indepNumber_cycle7] at h
  exact_mod_cast h

set_option maxRecDepth 100000 in
/-- An explicit 10-element independent set in `C₇ ⊠ C₇`, so `α(C₇^{⊠2}) ≥ 10`. -/
theorem indepNumber_strongPower_cycle7_two_ge :
    10 ≤ indepNumber (strongPower (cycleGraph 7) 2) :=
  le_indepNumber_iff.2 ⟨{![0, 0], ![0, 2], ![1, 4], ![2, 0], ![2, 2], ![3, 4], ![4, 1],
    ![4, 6], ![5, 3], ![6, 5]}, by decide, by decide⟩

/-- `√10 ≤ Θ(C₇)`. -/
theorem sqrt10_le_shannonCapacity_cycle7 :
    Real.sqrt 10 ≤ shannonCapacity (cycleGraph 7) := by
  have h := indepNumber_strongPower_rpow_le_shannonCapacity (cycleGraph 7) (k := 2) two_pos
  have h10 : (10 : ℝ) ≤ indepNumber (strongPower (cycleGraph 7) 2) := by
    exact_mod_cast indepNumber_strongPower_cycle7_two_ge
  refine le_trans ?_ h
  rw [Real.sqrt_eq_rpow]
  push_cast
  exact Real.rpow_le_rpow (by norm_num) h10 (by norm_num)

/-- `Θ(C₇) ≤ ϑ(C₇)` (Lovász 1979). -/
theorem shannonCapacity_cycle7_le_lovaszTheta :
    shannonCapacity (cycleGraph 7) ≤ lovaszTheta (cycleGraph 7) :=
  shannonCapacity_le_lovaszTheta _

/-! ## The upper bound `ϑ(C₇) ≤ 7 cos(π/7)/(1+cos(π/7))` -/

/-- `cos(π/7)` is a root of `8x³ - 4x² - 4x + 1`. -/
theorem cos_pi_div_seven_minpoly :
    8 * Real.cos (Real.pi / 7) ^ 3 - 4 * Real.cos (Real.pi / 7) ^ 2
      - 4 * Real.cos (Real.pi / 7) + 1 = 0 := by
  set γ := Real.cos (Real.pi / 7) with hγ
  have hγpos : 0 < γ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- `cos(4π/7) = -cos(3π/7)`
  have h4 : Real.cos (4 * (Real.pi / 7)) = -Real.cos (3 * (Real.pi / 7)) := by
    rw [← Real.cos_pi_sub]; congr 1; ring
  have h2 : Real.cos (4 * (Real.pi / 7)) = 2 * (2 * γ ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * (Real.pi / 7) = 2 * (2 * (Real.pi / 7)) by ring, Real.cos_two_mul,
      Real.cos_two_mul]
  rw [h2, Real.cos_three_mul] at h4
  have : (γ + 1) * (8 * γ ^ 3 - 4 * γ ^ 2 - 4 * γ + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact h

/-- **Lovász's bound for `C₇`**: `ϑ(C₇) ≤ 7 cos(π/7) / (1 + cos(π/7))` (Lovász 1979,
Corollary 5), via the explicit circulant orthonormal representation in `ℝ⁵`. -/
theorem lovaszTheta_cycle7_le :
    lovaszTheta (cycleGraph 7) ≤
      7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)) := by
  set c2 := Real.cos (4 * Real.pi / 7) with hc2def
  set c3 := Real.cos (6 * Real.pi / 7) with hc3def
  have hpi := Real.pi_pos
  have hc2neg : c2 < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have hc3neg : c3 < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have h1c2 : 0 < 1 - c2 := by linarith
  have h1c3 : 0 < 1 - c3 := by linarith
  set A := 1 / (2 * (1 - c2) * (1 - c3)) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; apply div_pos one_pos
    apply mul_pos (mul_pos two_pos (by linarith)) (by linarith)
  set B := -2 * A * (c2 + c3) with hBdef
  set C := A * (1 + 2 * c2 * c3) with hCdef
  have hBnn : 0 ≤ B := by rw [hBdef]; nlinarith
  have hCpos : 0 < C := by rw [hCdef]; apply mul_pos hApos; nlinarith
  have hsum : C + B + A = 1 := by
    rw [hCdef, hBdef, hAdef]; field_simp; ring
  set p := Real.sqrt C
  set q := Real.sqrt B
  set r := Real.sqrt A
  have hp : p ^ 2 = C := Real.sq_sqrt hCpos.le
  have hq : q ^ 2 = B := Real.sq_sqrt hBnn
  have hr : r ^ 2 = A := Real.sq_sqrt hApos.le
  have hppos : 0 < p := Real.sqrt_pos.2 hCpos
  let θ : ZMod 7 → ℝ := fun a => 2 * Real.pi * (a.val : ℝ) / 7
  let u : ZMod 7 → Fin 5 → ℝ := fun a =>
    ![p, q * Real.cos (θ a), q * Real.sin (θ a), r * Real.cos (2 * θ a),
      r * Real.sin (2 * θ a)]
  let c : Fin 5 → ℝ := ![1, 0, 0, 0, 0]
  have hkey : ∀ a b : ZMod 7, a ≠ b → ¬ (cycleGraph 7).Adj a b →
      ((a.val : ℤ) - b.val) ∈ ({2, 3, 4, 5, -2, -3, -4, -5} : Finset ℤ) := by decide
  have hval : 1 / C = 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)) := by
    set γ := Real.cos (Real.pi / 7) with hγ
    have hγpos : 0 < γ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hm := cos_pi_div_seven_minpoly
    rw [← hγ] at hm
    have e3 : c3 = -γ := by
      rw [hc3def, hγ, ← Real.cos_pi_sub]; congr 1; ring
    have e2 : c2 = 3 * γ - 4 * γ ^ 3 := by
      rw [hc2def, show 4 * Real.pi / 7 = Real.pi - 3 * (Real.pi / 7) by ring, Real.cos_pi_sub,
        Real.cos_three_mul, ← hγ]; ring
    have hd : 0 < 1 + 2 * c2 * c3 := by nlinarith
    have hC' : C = (1 + 2 * c2 * c3) / (2 * (1 - c2) * (1 - c3)) := by
      rw [hCdef, hAdef]; field_simp
    rw [hC', one_div_div, div_eq_div_iff hd.ne' (by linarith), e2, e3]
    linear_combination (2 - γ - 6 * γ ^ 2) * hm
  refine (csInf_le (lovaszTheta_set_bddBelow _) ⟨5, u, c, ⟨?_, ?_⟩, ?_, ?_⟩).trans hval.le
  · intro a
    simp only [u, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hp, hq, hr]
    nlinarith [Real.sin_sq_add_cos_sq (θ a), Real.sin_sq_add_cos_sq (2 * θ a)]
  · intro a b hab hnadj
    have key := hkey a b hab hnadj
    set δ := θ a - θ b with hδ
    have hcosδ : Real.cos δ = c2 ∨ Real.cos δ = c3 := by
      have e : δ = 2 * Real.pi * (((a.val : ℤ) - b.val : ℤ) : ℝ) / 7 := by
        simp only [hδ, θ]; push_cast; ring
      rw [e]
      simp only [Finset.mem_insert, Finset.mem_singleton] at key
      rcases key with k | k | k | k | k | k | k | k <;> rw [k] <;> push_cast
      · left; rw [hc2def]; congr 1; ring
      · right; rw [hc3def]; congr 1; ring
      · right; rw [hc3def, ← Real.cos_two_pi_sub]; congr 1; ring
      · left; rw [hc2def, ← Real.cos_two_pi_sub]; congr 1; ring
      · left; rw [hc2def, ← Real.cos_neg]; congr 1; ring
      · right; rw [hc3def, ← Real.cos_neg]; congr 1; ring
      · right; rw [hc3def, ← Real.cos_neg, ← Real.cos_two_pi_sub]; congr 1; ring
      · left; rw [hc2def, ← Real.cos_neg, ← Real.cos_two_pi_sub]; congr 1; ring
    have hpoly : C + B * Real.cos δ + A * (2 * Real.cos δ ^ 2 - 1) =
        2 * A * (Real.cos δ - c2) * (Real.cos δ - c3) := by
      rw [hCdef, hBdef]; ring
    simp only [u, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
    calc p * p + q * Real.cos (θ a) * (q * Real.cos (θ b))
          + q * Real.sin (θ a) * (q * Real.sin (θ b))
          + r * Real.cos (2 * θ a) * (r * Real.cos (2 * θ b))
          + r * Real.sin (2 * θ a) * (r * Real.sin (2 * θ b))
        = p ^ 2 + q ^ 2 * Real.cos (θ a - θ b) + r ^ 2 * Real.cos (2 * θ a - 2 * θ b) := by
          rw [Real.cos_sub, Real.cos_sub]; ring
      _ = C + B * Real.cos δ + A * (2 * Real.cos δ ^ 2 - 1) := by
          rw [hp, hq, hr, ← hδ, show 2 * θ a - 2 * θ b = 2 * δ by rw [hδ]; ring,
            Real.cos_two_mul]
      _ = 0 := by
          rw [hpoly]
          rcases hcosδ with h | h <;> rw [h] <;> ring
  · simp [c, Fin.sum_univ_five]
  · intro a
    have hcu : ∑ i : Fin 5, c i * u a i = p := by
      simp [c, u, Fin.sum_univ_five]
    rw [hcu, hp]
    exact ⟨hppos.ne', le_rfl⟩

/-- `ϑ(C₇) < 7/2`. -/
theorem lovaszTheta_cycle7_lt : lovaszTheta (cycleGraph 7) < 7 / 2 := by
  refine lovaszTheta_cycle7_le.trans_lt ?_
  have hpi := Real.pi_pos
  have hγpos : 0 < Real.cos (Real.pi / 7) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hγlt : Real.cos (Real.pi / 7) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by positivity)
  rw [div_lt_div_iff₀ (by linarith) two_pos]
  linarith

/-- `√10 ≤ ϑ(C₇)`. -/
theorem sqrt10_le_lovaszTheta_cycle7 : Real.sqrt 10 ≤ lovaszTheta (cycleGraph 7) :=
  sqrt10_le_shannonCapacity_cycle7.trans shannonCapacity_cycle7_le_lovaszTheta

/-- Summary: `√10 ≤ Θ(C₇) ≤ ϑ(C₇) ≤ 7cos(π/7)/(1+cos(π/7)) < 7/2`. -/
theorem known_bounds :
    Real.sqrt 10 ≤ shannonCapacity (cycleGraph 7) ∧
    shannonCapacity (cycleGraph 7) ≤ lovaszTheta (cycleGraph 7) ∧
    lovaszTheta (cycleGraph 7) ≤ 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)) ∧
    lovaszTheta (cycleGraph 7) < 7 / 2 :=
  ⟨sqrt10_le_shannonCapacity_cycle7, shannonCapacity_cycle7_le_lovaszTheta,
    lovaszTheta_cycle7_le, lovaszTheta_cycle7_lt⟩

/-! ### Regression: solved cases of the same objects -/

/-- Clique-cover bound (fibres of `f` are cliques): `α(G^{⊠k}) ≤ |W|^k`. -/
private theorem indepNumber_strongPower_le_of_cover {V₀ W₀ : Type*} [Fintype V₀] [Fintype W₀]
    {G : SimpleGraph V₀} (f : V₀ → W₀) (hf : ∀ x y, f x = f y → x = y ∨ G.Adj x y) (k : ℕ) :
    indepNumber (strongPower G k) ≤ Fintype.card W₀ ^ k := by
  classical
  obtain ⟨S, hS, hc⟩ := exists_indepSet_card_eq_indepNumber (strongPower G k)
  rw [← hc]
  have hinj : Set.InjOn (fun x : Fin k → V₀ => f ∘ x) (S : Set (Fin k → V₀)) := by
    intro x hx y hy hxy
    by_contra hne
    exact hS x hx y hy ⟨hne, fun i => hf _ _ (congrFun hxy i)⟩
  have := Finset.card_le_card_of_injOn _ (t := (Finset.univ : Finset (Fin k → W₀)))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  simpa [Fintype.card_fun] using this

/-- Clique-cover bound for the Shannon capacity: `Θ(G) ≤ |W|` (a cover by `|W|` cliques). -/
private theorem shannonCapacity_le_of_cover {V₀ W₀ : Type*} [Fintype V₀] [Fintype W₀]
    {G : SimpleGraph V₀} (f : V₀ → W₀) (hf : ∀ x y, f x = f y → x = y ∨ G.Adj x y) :
    shannonCapacity G ≤ Fintype.card W₀ := by
  refine (shannonCapacity_le_iff G).2 fun k hk => ?_
  have h1 : (indepNumber (strongPower G k) : ℝ) ≤ (Fintype.card W₀ : ℝ) ^ k := by
    exact_mod_cast indepNumber_strongPower_le_of_cover f hf k
  calc _ ≤ ((Fintype.card W₀ : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ)) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = _ := by rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) hk.ne'

/-- `Θ(K_n) = 1` for the complete graph on a nonempty vertex set (perfect graph: `Θ = α`). -/
private theorem shannonCapacity_top {V₀ : Type*} [Fintype V₀] [Nonempty V₀] :
    shannonCapacity (⊤ : SimpleGraph V₀) = 1 := by
  refine le_antisymm ?_ (one_le_shannonCapacity _)
  have := shannonCapacity_le_of_cover (G := (⊤ : SimpleGraph V₀)) (fun _ => ()) (fun x y _ => by
    by_cases h : x = y
    · exact Or.inl h
    · exact Or.inr ((SimpleGraph.top_adj x y).2 h))
  simpa using this

/-- **Regression**: `Θ(C₄) = 2` (perfect graph, `Θ = α`). -/
theorem regression_cycle4 : shannonCapacity (cycleGraph 4) = 2 := by
  refine le_antisymm ?_ ?_
  · have := shannonCapacity_le_of_cover (G := cycleGraph 4)
      (fun x : ZMod 4 => decide (x = 0 ∨ x = 1)) (by decide)
    simpa using this
  · have h2 : 2 ≤ indepNumber (cycleGraph 4) :=
      le_indepNumber_iff.2 ⟨{0, 2}, by decide, by decide⟩
    exact le_trans (by exact_mod_cast h2) (le_shannonCapacity _)

/-- **Regression** (Lovász 1979): for the pentagon `Θ(C₅) = ϑ(C₅)`, so the analogue of the
`Statement` for `C₅` is false. -/
theorem regression_cycle5_not_strict :
    ¬ shannonCapacity (cycleGraph 5) < lovaszTheta (cycleGraph 5) := by
  rw [shannonCapacity_cycle5, lovaszTheta_cycle5]
  exact lt_irrefl _

/-- **Regression**: `Θ(K_n) = 1`. -/
theorem regression_complete (n : ℕ) [NeZero n] : shannonCapacity (⊤ : SimpleGraph (Fin n)) = 1 :=
  shannonCapacity_top

end InfoTheory.Known.Certificates.ShannonCapacityC7
