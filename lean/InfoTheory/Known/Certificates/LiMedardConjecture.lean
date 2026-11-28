import InfoTheory.Problems.LiMedardConjecture

/-!
# Certificate for `InfoTheory.Problems.LiMedardConjecture`

The frozen statement asks that for all `n ≥ 1`, `α ∈ (0, 1/2)`, `q ∈ (1, 2]` and every
balanced `f : {0,1}^n → {0,1}`, `2^{-n} Σ_y (T_ρ f(y))^q ≤ (α^q + (1-α)^q)/2`, where
`T_ρ f = noiseOp n α f`.

Certified here, about the *exact* objects in `Statement` (`noiseOp`, the balance condition,
the `2^{-n}`-normalized `rpow` moment):
* `sum_comp_coord` — `Σ_{x ∈ {0,1}^n} g(x_i) = (g 1 + g 0) · 2^{n-1}` (counting lemma);
* `noiseOp_coord` — for a function of one coordinate, `T_ρ f(y)` only sees `y_i`: the
  operator is the genuine BSC posterior mean;
* `dictator_balanced`, `antiDictator_balanced` — dictators `x ↦ x_i` and anti-dictators
  `x ↦ ¬x_i` satisfy the balance hypothesis;
* `dictator_moment`, `antiDictator_moment` — **sharpness**: they attain the right-hand side
  with equality, for every `n ≥ 1`, every `α` and every real `q` (so the bound is the exact
  conjectured maximum, not a vacuous or junk value);
* `statement_n_one` — **regression (solved special case `n = 1`)**: for one bit every
  balanced function is a dictator or anti-dictator, so the inequality holds (with equality).

Not certified: the Parseval case `q = 2` for `n ≥ 2`, the high-noise regime
(Samorodnitsky), Yu's local optimality, or the equivalence with Courtade–Kumar. The
`Statement` itself (all `n`) is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.LiMedardConjecture

open InfoTheory InfoTheory.Problems.LiMedardConjecture

/-- Summing a function of one coordinate over the cube. -/
theorem sum_comp_coord {n : ℕ} (i₀ : Fin n) (g : Bool → ℝ) :
    ∑ x : Fin n → Bool, g (x i₀) = (g true + g false) * 2 ^ (n - 1) := by
  classical
  have h1 : ∀ x : Fin n → Bool,
      g (x i₀) = ∏ i : Fin n, (if i = i₀ then g (x i) else 1) := by
    intro x
    rw [Finset.prod_ite_eq' Finset.univ i₀ (fun i => g (x i))]
    simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if i = i₀ then g b else 1)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  simp only [if_true, Fintype.sum_bool]
  congr 1
  rw [Finset.prod_congr rfl (g := fun _ => (2 : ℝ))]
  · rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  · intro i hi
    have hne := Finset.ne_of_mem_erase hi
    simp [hne]; norm_num

/-- BSC transition weight `P(Y = c | X = b)`. -/
noncomputable def w (α : ℝ) (b c : Bool) : ℝ := if b = c then 1 - α else α

/-- The noise operator applied to a function of a single coordinate. -/
theorem noiseOp_coord {n : ℕ} (α : ℝ) (i₀ : Fin n) (φ : Bool → Bool) (y : Fin n → Bool) :
    noiseOp n α (fun x => φ (x i₀)) y =
      w α true (y i₀) * (if φ true then 1 else 0) +
        w α false (y i₀) * (if φ false then 1 else 0) := by
  classical
  unfold noiseOp
  have h1 : ∀ x : Fin n → Bool,
      (∏ i : Fin n, if x i = y i then 1 - α else α) * (if φ (x i₀) then (1 : ℝ) else 0) =
        ∏ i : Fin n, (w α (x i) (y i) *
          (if i = i₀ then (if φ (x i) then (1 : ℝ) else 0) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i₀]
    simp [w]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    w α b (y i) * (if i = i₀ then (if φ b then (1 : ℝ) else 0) else 1))]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  rw [Finset.prod_eq_one]
  · simp [Fintype.sum_bool]
  · intro i hi
    have hne := Finset.ne_of_mem_erase hi
    simp only [Fintype.sum_bool, hne, if_false, mul_one]
    unfold w
    cases y i <;> simp

/-- The `2^{-n}`-normalized `q`-moment of a function of one coordinate. -/
theorem moment_coord {n : ℕ} (hn : 1 ≤ n) (α q : ℝ) (i₀ : Fin n) (φ : Bool → Bool) :
    ((1 : ℝ) / ((2 : ℝ) ^ n)) * ∑ y : Fin n → Bool, (noiseOp n α (fun x => φ (x i₀)) y) ^ q =
      ((w α true true * (if φ true then 1 else 0) +
          w α false true * (if φ false then 1 else 0)) ^ q +
        (w α true false * (if φ true then 1 else 0) +
          w α false false * (if φ false then 1 else 0)) ^ q) / 2 := by
  simp_rw [noiseOp_coord]
  rw [sum_comp_coord i₀ (fun c => (w α true c * (if φ true then 1 else 0) +
      w α false c * (if φ false then 1 else 0)) ^ q)]
  have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2]
  have : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  field_simp

/-- Dictators are balanced. -/
theorem dictator_balanced {n : ℕ} (hn : 1 ≤ n) (i₀ : Fin n) :
    2 * (Finset.univ.filter (fun x : Fin n → Bool => x i₀ = true)).card = 2 ^ n := by
  have h := sum_comp_coord i₀ (fun b => if b = true then 1 else 0)
  simp only [Finset.sum_boole, if_true, Bool.false_eq_true, if_false, add_zero, one_mul] at h
  have h' : ((Finset.univ.filter (fun x : Fin n → Bool => x i₀ = true)).card : ℝ) =
      2 ^ (n - 1) := by simpa using h
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h2]; congr 1; exact_mod_cast h'

/-- Anti-dictators are balanced. -/
theorem antiDictator_balanced {n : ℕ} (hn : 1 ≤ n) (i₀ : Fin n) :
    2 * (Finset.univ.filter (fun x : Fin n → Bool => (!x i₀) = true)).card = 2 ^ n := by
  have h := sum_comp_coord i₀ (fun b => if (!b) = true then 1 else 0)
  simp only [Finset.sum_boole, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false,
    if_true, zero_add, one_mul] at h
  have h' : ((Finset.univ.filter (fun x : Fin n → Bool => (!x i₀) = true)).card : ℝ) =
      2 ^ (n - 1) := by simpa using h
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h2]; congr 1; exact_mod_cast h'

/-- **Sharpness**: dictators attain the conjectured maximum. -/
theorem dictator_moment {n : ℕ} (hn : 1 ≤ n) (α q : ℝ) (i₀ : Fin n) :
    ((1 : ℝ) / ((2 : ℝ) ^ n)) * ∑ y : Fin n → Bool, (noiseOp n α (fun x => x i₀) y) ^ q =
      (α ^ q + (1 - α) ^ q) / 2 := by
  have := moment_coord hn α q i₀ id
  simp only [id] at this
  rw [this]; simp [w]; ring

/-- **Sharpness**: anti-dictators attain the conjectured maximum. -/
theorem antiDictator_moment {n : ℕ} (hn : 1 ≤ n) (α q : ℝ) (i₀ : Fin n) :
    ((1 : ℝ) / ((2 : ℝ) ^ n)) * ∑ y : Fin n → Bool, (noiseOp n α (fun x => !x i₀) y) ^ q =
      (α ^ q + (1 - α) ^ q) / 2 := by
  rw [moment_coord hn α q i₀ (fun b => !b)]; simp [w]

/-- **Regression (`n = 1`)**: every balanced function of one bit is a dictator or an
anti-dictator, so the Li–Médard inequality holds for `n = 1` (with equality). -/
theorem statement_n_one (α q : ℝ) (f : (Fin 1 → Bool) → Bool)
    (hbal : 2 * (Finset.univ.filter (fun x : Fin 1 → Bool => f x = true)).card = 2 ^ 1) :
    ((1 : ℝ) / ((2 : ℝ) ^ 1)) * ∑ y : Fin 1 → Bool, (noiseOp 1 α f y) ^ q ≤
      (α ^ q + (1 - α) ^ q) / 2 := by
  set F : Bool → Bool := fun b => f (fun _ => b) with hF
  have hf : f = fun x => F (x 0) := by
    funext x
    simp only [hF]
    congr 1; funext i; rw [Subsingleton.elim i 0]
  have hcard := sum_comp_coord (0 : Fin 1) (fun b => if F b = true then 1 else 0)
  have hc' : ((Finset.univ.filter (fun x : Fin 1 → Bool => f x = true)).card : ℝ) =
      ∑ x : Fin 1 → Bool, (if F (x 0) = true then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]; simp [hf]
  have hbal' : ((Finset.univ.filter (fun x : Fin 1 → Bool => f x = true)).card : ℝ) = 1 := by
    have : (Finset.univ.filter (fun x : Fin 1 → Bool => f x = true)).card = 1 := by omega
    exact_mod_cast this
  rw [hc', hcard] at hbal'
  norm_num at hbal'
  rw [hf]
  cases ht : F true <;> cases hfl : F false <;> simp [ht, hfl] at hbal'
  · -- `F = not`
    have : (fun x : Fin 1 → Bool => F (x 0)) = fun x => !x 0 := by
      funext x; cases hx : x 0 <;> simp [ht, hfl]
    rw [this, antiDictator_moment le_rfl]
  · -- `F = id`
    have : (fun x : Fin 1 → Bool => F (x 0)) = fun x => x 0 := by
      funext x; cases hx : x 0 <;> simp [ht, hfl]
    rw [this, dictator_moment le_rfl]

end InfoTheory.Known.Certificates.LiMedardConjecture
