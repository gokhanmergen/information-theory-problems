import InfoTheory.Problems.EntropicDoublingConstant
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.EntropicDoublingConstant`

The frozen statement asks for the sharp constant `2` in the entropic PFR inequality
`min_H d[P; U_H] ≤ 2 d[P; P]` on `𝔽₂ⁿ` (Gowers–Green–Manners–Tao, "On a conjecture of Marton",
arXiv:2311.05762, 2023; Tao, "Sumset and inverse sumset theory for Shannon entropy",
Combin. Probab. Comput. 19, 2010). This file proves known facts about the exact objects
`ruzsaDist` and `IsUniformOnSubspace`.

## Certified
* `entropy_sum_ge`: `H(X + Y) ≥ max(H(X), H(Y))` for independent `X, Y` (Tao 2010, §3).
* `ruzsaDist_nonneg`: `d[X; Y] ≥ 0` (GGMT 2023, Lemma 3.11), so the right-hand side
  `2 d[P; P]` of the Statement is nonnegative.
* `sum_uniformOnSubspace_pmf`, `ruzsaDist_uniformOnSubspace_self`: for `U_H` uniform on a
  subspace, `U_H + U_H' ~ U_H` and `d[U_H; U_H] = 0` (GGMT 2023, Lemma 3.11).
* `statement_at_uniformOnSubspace`: for subspace-uniform `P` the Statement's inequality holds
  with equality (`0 = 0`), so the constant is tested exactly at the extremal objects.

## Not certified
* The GGMT bound with an absolute constant (and Liao's improvement), and Ruzsa's triangle
  inequality for `d`, are out of scope.
* Numerical sanity check (not a proof; Python, 3000 random `P` for each `n ≤ 3`, all
  subspaces): the worst ratio `min_H d[P; U_H] / d[P; P]` found was `≈ 1.17 < 2`, so the
  Statement is not refuted by small cases.
-/

open scoped BigOperators Classical

namespace InfoTheory.Known.Certificates.EntropicDoublingConstant

open InfoTheory InfoTheory.Problems.EntropicDoublingConstant InfoTheory.Known.MapEntropy

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Subadditivity in map form: `H(a(X), b(X)) ≤ H(a(X)) + H(b(X))`. -/
lemma entropy_map_pair_le {A B : Type*} [Fintype A] [Fintype B] (R : ProbDist α)
    (a : α → A) (b : α → B) :
    shannonEntropy (R.map fun x => (a x, b x)) ≤
      shannonEntropy (R.map a) + shannonEntropy (R.map b) := by
  have key := entropy_submod_triple R a b (fun _ => ())
  have e1 : shannonEntropy (R.map fun x => (a x, b x, ())) =
      shannonEntropy (R.map fun x => (a x, b x)) :=
    entropy_map_eq_of_ker R fun x y => by simp
  have e2 : shannonEntropy (R.map fun x => (a x, ())) = shannonEntropy (R.map a) :=
    entropy_map_eq_of_ker R fun x y => by simp
  have e3 : shannonEntropy (R.map fun x => (b x, ())) = shannonEntropy (R.map b) :=
    entropy_map_eq_of_ker R fun x y => by simp
  have e4 : shannonEntropy (R.map fun _ => ()) = 0 :=
    entropy_map_eq_zero_of_const R fun _ _ => rfl
  linarith

lemma shannonEntropy_map_id (R : ProbDist α) : shannonEntropy (R.map id) = shannonEntropy R := by
  unfold shannonEntropy
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [ProbDist.map]

lemma shannonEntropy_map_snd (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy ((P.prod Q).map Prod.snd) = shannonEntropy Q := by
  unfold shannonEntropy
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  simp [ProbDist.map, ProbDist.prod, Fintype.sum_prod_type, ← Finset.sum_mul, P.sum_one]

lemma shannonEntropy_map_fst (P : ProbDist α) (Q : ProbDist β) :
    shannonEntropy ((P.prod Q).map Prod.fst) = shannonEntropy P := by
  unfold shannonEntropy
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [ProbDist.map, ProbDist.prod, Fintype.sum_prod_type, ← Finset.mul_sum, Q.sum_one]

/-- `H(X + Y) ≥ H(X)` and `H(X + Y) ≥ H(Y)` for independent `X ~ P`, `Y ~ Q` on `𝔽₂ⁿ`
(Tao, "Sumset and inverse sumset theory for Shannon entropy", CPC 19, 2010, Lemma 3.1 /
Ruzsa 2009). Proof: `H(X+Y, Y) = H(X, Y) = H(X) + H(Y)` and subadditivity. -/
theorem entropy_sum_ge (n : ℕ) (P Q : ProbDist (Fin n → ZMod 2)) :
    shannonEntropy P ≤ shannonEntropy ((P.prod Q).map (fun xy i => xy.1 i + xy.2 i)) ∧
    shannonEntropy Q ≤ shannonEntropy ((P.prod Q).map (fun xy i => xy.1 i + xy.2 i)) := by
  set R := P.prod Q
  set s : (Fin n → ZMod 2) × (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun xy i => xy.1 i + xy.2 i
  have hHR : shannonEntropy R = shannonEntropy P + shannonEntropy Q :=
    InfoTheory.Bridge.shannonEntropy_prod P Q
  have hb : shannonEntropy (R.map fun x => (s x, x.2)) = shannonEntropy R := by
    rw [← shannonEntropy_map_id R]
    refine entropy_map_eq_of_ker R fun x y => ?_
    simp only [id, Prod.mk.injEq, s]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      refine Prod.ext ?_ h2
      funext i
      have := congrFun h1 i
      rw [h2] at this
      simpa using this
  have ha : shannonEntropy (R.map fun x => (s x, x.1)) = shannonEntropy R := by
    rw [← shannonEntropy_map_id R]
    refine entropy_map_eq_of_ker R fun x y => ?_
    simp only [id, Prod.mk.injEq, s]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      refine Prod.ext h2 ?_
      funext i
      have := congrFun h1 i
      rw [h2] at this
      simpa using this
  have s1 := entropy_map_pair_le R s Prod.snd
  have s2 := entropy_map_pair_le R s Prod.fst
  have hq := shannonEntropy_map_snd P Q
  have hp := shannonEntropy_map_fst P Q
  constructor <;> linarith

/-- **Nonnegativity of the entropic Ruzsa distance**, `d[X; Y] ≥ 0` (Tao 2010, §3;
Gowers–Green–Manners–Tao, "On a conjecture of Marton", 2023, Lemma 3.11 (ii)). In particular
`d[P; P] ≥ 0`, so the right-hand side `2 d[P; P]` of the Statement is nonnegative. -/
theorem ruzsaDist_nonneg (n : ℕ) (P Q : ProbDist (Fin n → ZMod 2)) : 0 ≤ ruzsaDist n P Q := by
  obtain ⟨h1, h2⟩ := entropy_sum_ge n P Q
  unfold ruzsaDist
  linarith

/-! ### Uniform distributions on subspaces: `d[U_H; U_H] = 0` -/

/-- The sum of two independent copies of the uniform distribution on a subspace `H` is again
uniform on `H`. -/
lemma sum_uniformOnSubspace_pmf (n : ℕ) (U : ProbDist (Fin n → ZMod 2))
    (H : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hU : ∀ x, U.pmf x = if x ∈ H then (1 : ℝ) / ((2 : ℝ) ^ (Module.finrank (ZMod 2) H)) else 0)
    (z : Fin n → ZMod 2) :
    ((U.prod U).map (fun xy i => xy.1 i + xy.2 i)).pmf z = U.pmf z := by
  set c : ℝ := (1 : ℝ) / ((2 : ℝ) ^ (Module.finrank (ZMod 2) H)) with hc
  have step1 : ((U.prod U).map (fun xy i => xy.1 i + xy.2 i)).pmf z =
      ∑ x, U.pmf x * U.pmf (z - x) := by
    simp only [ProbDist.map, ProbDist.prod, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ∀ y : Fin n → ZMod 2, ((fun i => x i + y i) = z) ↔ y = z - x := by
      intro y
      rw [eq_sub_iff_add_eq']
      rfl
    simp_rw [this]
    simp
  rw [step1]
  have hcard : (Fintype.card H : ℝ) = (2 : ℝ) ^ (Module.finrank (ZMod 2) H) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := H), ZMod.card]
    push_cast; rfl
  by_cases hz : z ∈ H
  · have hterm : ∀ x, U.pmf x * U.pmf (z - x) = if x ∈ H then c * c else 0 := by
      intro x
      rw [hU, hU]
      by_cases hx : x ∈ H
      · simp [hx, H.sub_mem hz hx]
      · simp [hx]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hU]
    simp only [hz, ↓reduceIte]
    have hfc : ((Finset.univ.filter fun x => x ∈ H).card : ℝ) = Fintype.card H := by
      rw [← Fintype.card_subtype]
    rw [hfc, hcard, hc]
    field_simp
  · have hterm : ∀ x, U.pmf x * U.pmf (z - x) = 0 := by
      intro x
      rw [hU, hU]
      by_cases hx : x ∈ H
      · have : z - x ∉ H := fun h => hz (by simpa using H.add_mem h hx)
        simp [this]
      · simp [hx]
    simp_rw [hterm]
    rw [Finset.sum_const_zero, hU]
    simp only [hz, ↓reduceIte]

/-- **Equality case** `d[U_H; U_H] = 0` for `U_H` uniform on a subspace (Tao 2010, §3;
Gowers–Green–Manners–Tao 2023, Lemma 3.11). -/
theorem ruzsaDist_uniformOnSubspace_self (n : ℕ) (U : ProbDist (Fin n → ZMod 2))
    (hU : IsUniformOnSubspace n U) : ruzsaDist n U U = 0 := by
  obtain ⟨H, hH⟩ := hU
  have heq : shannonEntropy ((U.prod U).map (fun xy i => xy.1 i + xy.2 i)) = shannonEntropy U := by
    unfold shannonEntropy
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [sum_uniformOnSubspace_pmf n U H hH z]
  unfold ruzsaDist
  rw [heq]; ring

/-- **The Statement is tight / consistent at `P = U_H`**: taking `U = P` gives
`d[P; U] = 0 = 2 d[P; P]`, so for subspace-uniform `P` the inequality holds with equality. -/
theorem statement_at_uniformOnSubspace (n : ℕ) (P : ProbDist (Fin n → ZMod 2))
    (hP : IsUniformOnSubspace n P) :
    ∃ U : ProbDist (Fin n → ZMod 2),
      IsUniformOnSubspace n U ∧ ruzsaDist n P U = 2 * ruzsaDist n P P :=
  ⟨P, hP, by rw [ruzsaDist_uniformOnSubspace_self n P hP]; ring⟩

end InfoTheory.Known.Certificates.EntropicDoublingConstant
