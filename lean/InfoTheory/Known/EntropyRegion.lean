import InfoTheory.Core

/-!
# Known facts about the entropy region (`Γ*_n`, `cl(Γ*_n)`, `Γ_n`, `L_n`)

Fully proved textbook facts about the definitions in `InfoTheory/Core/Entropy.lean`
(section "Entropy Vectors"), serving both as a validation of those definitions and as a
lemma base:

* `linearRank_isPolymatroid`: `L_n ⊆ Γ_n`.
* `ingleton_subspaces`, `ingleton_of_linearRank`: Ingleton's inequality for subspaces / `L_4`.
* `entropic_isPolymatroid`: the Shannon inequalities, `Γ*_n ⊆ Γ_n`.
* `almostEntropic_isPolymatroid`: `cl(Γ*_n) ⊆ Γ_n`.
* `exists_polymatroid_not_ingleton`, `exists_polymatroid_not_linearRank`: Ingleton is not a
  Shannon inequality; `L_4 ⊊ Γ_4`.

General entropy-of-a-function lemmas (`MapEntropy.*`) are proved from scratch here (no
dependency on other `Known` files): data processing for entropy and nonnegativity of
conditional mutual information, via the expectation form `H(f(X)) = E[-log₂ P(f(X) = f(x))]`
and `log t ≤ t - 1`.
-/

namespace InfoTheory.Known

open scoped BigOperators

section Linear

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Rank of the span of a subfamily of subspaces. -/
private noncomputable def rk {n : ℕ} (V : Fin n → Submodule K W) (S : Finset (Fin n)) : ℕ :=
  Module.finrank K (⨆ i ∈ S, V i : Submodule K W)

private lemma rk_mono {n : ℕ} (V : Fin n → Submodule K W) {S T : Finset (Fin n)} (h : S ⊆ T) :
    rk V S ≤ rk V T :=
  Submodule.finrank_mono (biSup_mono fun _ hi => h hi)

private lemma rk_submod {n : ℕ} (V : Fin n → Submodule K W) (S T : Finset (Fin n)) :
    rk V (S ∪ T) + rk V (S ∩ T) ≤ rk V S + rk V T := by
  unfold rk
  rw [Finset.iSup_union, ← Submodule.finrank_sup_add_finrank_inf_eq (⨆ i ∈ S, V i) (⨆ i ∈ T, V i)]
  apply Nat.add_le_add_left
  apply Submodule.finrank_mono
  exact le_inf (biSup_mono fun i hi => (Finset.mem_inter.1 hi).1)
    (biSup_mono fun i hi => (Finset.mem_inter.1 hi).2)

/-- **Ingleton's inequality for subspaces** (Ingleton 1971; Hammer–Romashchenko–Shen–Vereshchagin
2000, Thm. 1): for subspaces `A, B, C, D` of a finite-dimensional vector space,
`dim A + dim B + dim (C+D) + dim (A+B+C) + dim (A+B+D)
  ≤ dim (A+B) + dim (A+C) + dim (A+D) + dim (B+C) + dim (B+D)`.
Proof: put `Z = A ∩ B` and apply the modular law `dim (X+Y) + dim (X ∩ Y) = dim X + dim Y`
four times. -/
theorem ingleton_subspaces (A B C D : Submodule K W) :
    Module.finrank K A + Module.finrank K B + Module.finrank K (C ⊔ D : Submodule K W) +
        Module.finrank K (A ⊔ (B ⊔ C) : Submodule K W) +
        Module.finrank K (A ⊔ (B ⊔ D) : Submodule K W) ≤
      Module.finrank K (A ⊔ B : Submodule K W) + Module.finrank K (A ⊔ C : Submodule K W) +
        Module.finrank K (A ⊔ D : Submodule K W) + Module.finrank K (B ⊔ C : Submodule K W) +
        Module.finrank K (B ⊔ D : Submodule K W) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ C) (B ⊔ C)
  have e3 := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ D) (B ⊔ D)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq ((A ⊓ B) ⊔ C) ((A ⊓ B) ⊔ D)
  have m2 : Module.finrank K (A ⊔ (B ⊔ C) : Submodule K W) ≤
      Module.finrank K ((A ⊔ C) ⊔ (B ⊔ C) : Submodule K W) :=
    Submodule.finrank_mono (sup_le (le_sup_left.trans le_sup_left)
      (sup_le (le_sup_left.trans le_sup_right) (le_sup_right.trans le_sup_right)))
  have m3 : Module.finrank K (A ⊔ (B ⊔ D) : Submodule K W) ≤
      Module.finrank K ((A ⊔ D) ⊔ (B ⊔ D) : Submodule K W) :=
    Submodule.finrank_mono (sup_le (le_sup_left.trans le_sup_left)
      (sup_le (le_sup_left.trans le_sup_right) (le_sup_right.trans le_sup_right)))
  have m2' : Module.finrank K ((A ⊓ B) ⊔ C : Submodule K W) ≤
      Module.finrank K ((A ⊔ C) ⊓ (B ⊔ C) : Submodule K W) :=
    Submodule.finrank_mono (le_inf (sup_le_sup_right inf_le_left C)
      (sup_le_sup_right inf_le_right C))
  have m3' : Module.finrank K ((A ⊓ B) ⊔ D : Submodule K W) ≤
      Module.finrank K ((A ⊔ D) ⊓ (B ⊔ D) : Submodule K W) :=
    Submodule.finrank_mono (le_inf (sup_le_sup_right inf_le_left D)
      (sup_le_sup_right inf_le_right D))
  have m4 : Module.finrank K (C ⊔ D : Submodule K W) ≤
      Module.finrank K (((A ⊓ B) ⊔ C) ⊔ ((A ⊓ B) ⊔ D) : Submodule K W) :=
    Submodule.finrank_mono (sup_le_sup le_sup_right le_sup_right)
  have m4' : Module.finrank K (A ⊓ B : Submodule K W) ≤ Module.finrank K (((A ⊓ B) ⊔ C) ⊓ ((A ⊓ B) ⊔ D) : Submodule K W) :=
    Submodule.finrank_mono (le_inf le_sup_left le_sup_left)
  omega

/-- Dimension of a subspace, as a plain function of the subspace (avoids dependent rewriting). -/
private noncomputable def fr (U : Submodule K W) : ℕ := Module.finrank K U

end Linear

/-- **Linear rank vectors are polymatroids** (Hammer–Romashchenko–Shen–Vereshchagin 2000;
Yeung, *Information Theory and Network Coding*, 2008): if `h S = c · dim (∑_{i∈S} V i)` with `c > 0`, then `h` satisfies
`h ∅ = 0`, monotonicity, and submodularity (the latter from the modular law for subspaces). -/
theorem linearRank_isPolymatroid {n : ℕ} {h : Finset (Fin n) → ℝ}
    (hlin : IsLinearRankVector n h) : IsPolymatroid n h := by
  obtain ⟨p, r, d, hp, hr, c, V, hc, hV⟩ := hlin
  have hV' : ∀ S, h S = c * (rk V S : ℝ) := hV
  refine ⟨?_, ?_, ?_⟩
  · rw [hV']; simp [rk]
  · intro S T hST
    rw [hV', hV']
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast rk_mono V hST) hc.le
  · intro S T
    rw [hV', hV', hV', hV', ← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast rk_submod V S T) hc.le

/-- **Ingleton's inequality holds for linear rank vectors** (Ingleton 1971; Hammer–Romashchenko–
Shen–Vereshchagin 2000): for `h ∈ L_4`,
`h(12) + h(13) + h(14) + h(23) + h(24) ≥ h(1) + h(2) + h(34) + h(123) + h(124)`
(indices `1,2,3,4` are `0,1,2,3 : Fin 4`). -/
theorem ingleton_of_linearRank {h : Finset (Fin 4) → ℝ} (hlin : IsLinearRankVector 4 h) :
    h {0} + h {1} + h {2, 3} + h {0, 1, 2} + h {0, 1, 3} ≤
      h {0, 1} + h {0, 2} + h {0, 3} + h {1, 2} + h {1, 3} := by
  obtain ⟨p, r, d, hp, hr, c, V, hc, hV⟩ := hlin
  have hV' : ∀ S, h S = c * (fr (⨆ i ∈ S, V i) : ℝ) := hV
  simp only [hV', Finset.iSup_insert, Finset.iSup_singleton]
  have key := ingleton_subspaces (V 0) (V 1) (V 2) (V 3)
  have key' : (fr (V 0) : ℝ) + fr (V 1) + fr (V 2 ⊔ V 3) + fr (V 0 ⊔ (V 1 ⊔ V 2)) +
      fr (V 0 ⊔ (V 1 ⊔ V 3)) ≤ (fr (V 0 ⊔ V 1) : ℝ) + fr (V 0 ⊔ V 2) + fr (V 0 ⊔ V 3) +
      fr (V 1 ⊔ V 2) + fr (V 1 ⊔ V 3) := by
    simp only [fr]; exact_mod_cast key
  nlinarith [key', hc]

/-! ### Shannon inequalities for entropic vectors -/

namespace MapEntropy

section Entropic

open Classical

variable {α : Type*} [Fintype α]

/-- Probability of the `f`-class of `x`, i.e. `P(f(X) = f(x))`. -/
private noncomputable def cls {A : Type*} [Fintype A] (P : ProbDist α) (f : α → A) (x : α) : ℝ :=
  (P.map f).pmf (f x)

private lemma map_pmf {A : Type*} [Fintype A] (P : ProbDist α) (f : α → A) (b : A) :
    (P.map f).pmf b = ∑ a, if f a = b then P.pmf a else 0 := rfl

private lemma negPLogP_eq {q : ℝ} (hq : 0 ≤ q) : negPLogP q = q * (-log2 q) := by
  unfold negPLogP
  split_ifs with h
  · have : q = 0 := le_antisymm h hq
    simp [this]
  · ring

/-- Entropy of `f(X)` as the expectation of `-log₂ P(f(X) = f(x))` over `x ∼ P`. -/
private lemma entropy_map_eq {A : Type*} [Fintype A] (P : ProbDist α) (f : α → A) :
    shannonEntropy (P.map f) = ∑ x, P.pmf x * (-log2 (cls P f x)) := by
  unfold shannonEntropy
  have step : ∀ b : A, negPLogP ((P.map f).pmf b) =
      ∑ x, if f x = b then P.pmf x * (-log2 (cls P f x)) else 0 := by
    intro b
    rw [negPLogP_eq ((P.map f).nonneg b)]
    conv_lhs => arg 1; rw [map_pmf]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · simp [cls, h]
    · simp
  rw [Finset.sum_congr rfl fun b _ => step b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

private lemma le_cls {A : Type*} [Fintype A] (P : ProbDist α) (f : α → A) (x : α) :
    P.pmf x ≤ cls P f x := by
  unfold cls
  rw [map_pmf]
  have := Finset.single_le_sum (f := fun y => if f y = f x then P.pmf y else 0)
    (fun y _ => by split_ifs <;> simp [P.nonneg]) (Finset.mem_univ x)
  simpa using this

private lemma cls_mono {A B : Type*} [Fintype A] [Fintype B] (P : ProbDist α) {f : α → A}
    {g : α → B} (hfg : ∀ x y, f x = f y → g x = g y) (x : α) : cls P f x ≤ cls P g x := by
  unfold cls
  rw [map_pmf, map_pmf]
  refine Finset.sum_le_sum fun y _ => ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (hfg y x h1) h2
  · exact P.nonneg y
  · exact le_rfl

/-- **Entropy of a function is at most the entropy of its argument** (Yeung 2008, Ch. 2;
Cover–Thomas 2006, Exercise 2.4): if `g(X)` is a function of `f(X)`, then `H(g(X)) ≤ H(f(X))`. -/
theorem entropy_map_le_of_factor {A B : Type*} [Fintype A] [Fintype B] (P : ProbDist α)
    {f : α → A} {g : α → B} (hfg : ∀ x y, f x = f y → g x = g y) :
    shannonEntropy (P.map g) ≤ shannonEntropy (P.map f) := by
  rw [entropy_map_eq, entropy_map_eq]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases (P.nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · refine mul_le_mul_of_nonneg_left ?_ (P.nonneg x)
    unfold log2
    refine neg_le_neg (div_le_div_of_nonneg_right ?_ (Real.log_pos one_lt_two).le)
    exact Real.log_le_log (hpos.trans_le (le_cls P f x)) (cls_mono P hfg x)

/-- Two maps with the same kernel generate the same entropy (Yeung 2008, Ch. 2: entropy
depends only on the partition induced by a random variable). -/
theorem entropy_map_eq_of_ker {A B : Type*} [Fintype A] [Fintype B] (P : ProbDist α)
    {f : α → A} {g : α → B} (hfg : ∀ x y, f x = f y ↔ g x = g y) :
    shannonEntropy (P.map g) = shannonEntropy (P.map f) :=
  le_antisymm (entropy_map_le_of_factor P fun x y => (hfg x y).1)
    (entropy_map_le_of_factor P fun x y => (hfg x y).2)

/-- The entropy of a constant (deterministic) random variable is `0` (Yeung 2008, Ch. 2). -/
theorem entropy_map_eq_zero_of_const {A : Type*} [Fintype A] (P : ProbDist α) {f : α → A}
    (hf : ∀ x y, f x = f y) : shannonEntropy (P.map f) = 0 := by
  rw [entropy_map_eq]
  refine Finset.sum_eq_zero fun x _ => ?_
  have : cls P f x = 1 := by
    unfold cls; rw [map_pmf]; simp [hf _ x, P.sum_one]
  simp [this, log2]

private lemma sum_marg {A C : Type*} [Fintype A] [Fintype C] (P : ProbDist α) (f : α → A)
    (g : α → C) (c' : C) :
    ∑ a', (P.map (fun x => (f x, g x))).pmf (a', c') = (P.map g).pmf c' := by
  simp only [map_pmf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Prod.mk.injEq, ite_and]
  rw [Finset.sum_ite_eq]
  simp

/-- **Nonnegativity of conditional mutual information** (Yeung 2008, Ch. 2; Cover–Thomas
2006, §2.6, information inequality, proved here via `log t ≤ t - 1`): for maps `a, b, c` of `X ∼ P`,
`H(A,B,C) + H(C) ≤ H(A,C) + H(B,C)`, i.e. `I(A;B|C) ≥ 0`. -/
theorem entropy_submod_triple {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (P : ProbDist α) (a : α → A) (b : α → B) (c : α → C) :
    shannonEntropy (P.map fun x => (a x, b x, c x)) + shannonEntropy (P.map c) ≤
      shannonEntropy (P.map fun x => (a x, c x)) + shannonEntropy (P.map fun x => (b x, c x)) := by
  set fabc : α → A × B × C := fun x => (a x, b x, c x) with hfabc
  set fac : α → A × C := fun x => (a x, c x) with hfac
  set fbc : α → B × C := fun x => (b x, c x) with hfbc
  set Pabc := P.map fabc
  set Pac := P.map fac
  set Pbc := P.map fbc
  set Pc := P.map c
  -- the ratio `t(x) = P(a,c) P(b,c) / (P(a,b,c) P(c))`
  set G : A × B × C → ℝ := fun z => Pac.pmf (z.1, z.2.2) * Pbc.pmf (z.2.1, z.2.2) / Pc.pmf z.2.2
    with hG
  set t : α → ℝ := fun x => cls P fac x * cls P fbc x / (cls P fabc x * cls P c x) with ht
  have tG : ∀ x, t x = G (fabc x) / Pabc.pmf (fabc x) := by
    intro x
    simp only [ht, hG, cls]
    ring
  have Gnn : ∀ z, 0 ≤ G z := fun z =>
    div_nonneg (mul_nonneg (Pac.nonneg _) (Pbc.nonneg _)) (Pc.nonneg _)
  -- `∑ G = 1`
  have sumG : ∑ z, G z = 1 := by
    have hc' : ∀ c' : C, ∑ b' : B, ∑ a' : A, G (a', b', c') = Pc.pmf c' := by
      intro c'
      have e : ∑ b' : B, ∑ a' : A, G (a', b', c') =
          (∑ a', Pac.pmf (a', c')) * (∑ b', Pbc.pmf (b', c')) / Pc.pmf c' := by
        rw [Finset.sum_mul_sum, Finset.sum_div, Finset.sum_comm]
        simp only [hG, Finset.sum_div]
      rw [e, sum_marg P a c c', sum_marg P b c c']
      exact mul_self_div_self _
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have e2 : ∑ a' : A, ∑ b' : B, ∑ c' : C, G (a', b', c') =
        ∑ c' : C, ∑ b' : B, ∑ a' : A, G (a', b', c') := by
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl fun (b' : B) _ => Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [e2, Finset.sum_congr rfl fun c' _ => hc' c']
    exact Pc.sum_one
  -- `∑ w t ≤ 1`
  have sumt : ∑ x, P.pmf x * t x ≤ 1 := by
    have e1 : ∑ x, P.pmf x * t x =
        ∑ z, ∑ x, if fabc x = z then P.pmf x * (G z / Pabc.pmf z) else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_ite_eq, tG]
      simp
    rw [e1, ← sumG]
    refine Finset.sum_le_sum fun z _ => ?_
    have : (∑ x, if fabc x = z then P.pmf x * (G z / Pabc.pmf z) else 0) =
        Pabc.pmf z * (G z / Pabc.pmf z) := by
      rw [show Pabc = P.map fabc from rfl, map_pmf, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [this]
    rcases (Pabc.nonneg z).eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using Gnn z
    · rw [mul_div_cancel₀ _ hpos.ne']
  -- `∑ w log t ≤ 0`
  have sumlog : ∑ x, P.pmf x * Real.log (t x) ≤ 0 := by
    have : ∑ x, P.pmf x * Real.log (t x) ≤ ∑ x, P.pmf x * (t x - 1) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rcases (P.nonneg x).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · refine mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ?_) hpos.le
        simp only [ht]
        have := le_cls P fac x; have := le_cls P fbc x
        have := le_cls P fabc x; have := le_cls P c x
        apply div_pos <;> [apply mul_pos; apply mul_pos] <;> linarith
    refine this.trans ?_
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, P.sum_one]
    linarith
  -- pointwise identity relating the entropies to `log t`
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have pt : ∀ x, P.pmf x * (-log2 (cls P fac x)) + P.pmf x * (-log2 (cls P fbc x)) -
      P.pmf x * (-log2 (cls P fabc x)) - P.pmf x * (-log2 (cls P c x)) =
      -(P.pmf x * Real.log (t x)) / Real.log 2 := by
    intro x
    rcases (P.nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have h1 := hpos.trans_le (le_cls P fac x); have h2 := hpos.trans_le (le_cls P fbc x)
      have h3 := hpos.trans_le (le_cls P fabc x); have h4 := hpos.trans_le (le_cls P c x)
      simp only [ht, log2]
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h2.ne',
        Real.log_mul h3.ne' h4.ne']
      field_simp
      ring
  have key : shannonEntropy Pac + shannonEntropy Pbc - shannonEntropy Pabc - shannonEntropy Pc =
      -(∑ x, P.pmf x * Real.log (t x)) / Real.log 2 := by
    simp only [Pac, Pbc, Pabc, Pc, entropy_map_eq]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun x _ => pt x, ← Finset.sum_div, Finset.sum_neg_distrib]
  have : 0 ≤ -(∑ x, P.pmf x * Real.log (t x)) / Real.log 2 :=
    div_nonneg (by linarith) hl2.le
  linarith

end Entropic

end MapEntropy

open MapEntropy

section EntropicVector

/-- Restriction of a joint outcome `x : Fin n → Fin k` to the coordinates in `S`. -/
private def restr {n k : ℕ} (S : Finset (Fin n)) (x : Fin n → Fin k) : S → Fin k :=
  fun i => x i.1

private lemma restr_eq_iff {n k : ℕ} (S : Finset (Fin n)) (x y : Fin n → Fin k) :
    restr S x = restr S y ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

private lemma subsetEntropyVec_eq {n k : ℕ} (P : ProbDist (Fin n → Fin k)) (S : Finset (Fin n)) :
    subsetEntropyVec P S = shannonEntropy (P.map (restr S)) := rfl

/-- `h(∅) = 0` for every subset-entropy vector (the empty marginal is deterministic). -/
theorem subsetEntropyVec_empty {n k : ℕ} (P : ProbDist (Fin n → Fin k)) :
    subsetEntropyVec P ∅ = 0 := by
  rw [subsetEntropyVec_eq]
  exact entropy_map_eq_zero_of_const P fun x y => (restr_eq_iff _ x y).2 (by simp)

/-- **Monotonicity of joint entropy** (Yeung 2008, Ch. 2 and Ch. 14: `H(X_S) ≤ H(X_T)` for
`S ⊆ T`). -/
theorem subsetEntropyVec_mono {n k : ℕ} (P : ProbDist (Fin n → Fin k)) {S T : Finset (Fin n)}
    (hST : S ⊆ T) : subsetEntropyVec P S ≤ subsetEntropyVec P T := by
  rw [subsetEntropyVec_eq, subsetEntropyVec_eq]
  refine entropy_map_le_of_factor P fun x y hxy => ?_
  rw [restr_eq_iff] at hxy ⊢
  exact fun i hi => hxy i (hST hi)

/-- **Submodularity of joint entropy** (Fujishige 1978; Yeung 2008, Ch. 14:
`H(X_{S∪T}) + H(X_{S∩T}) ≤ H(X_S) + H(X_T)`, equivalently `I(X_S; X_T | X_{S∩T}) ≥ 0`). -/
theorem subsetEntropyVec_submod {n k : ℕ} (P : ProbDist (Fin n → Fin k)) (S T : Finset (Fin n)) :
    subsetEntropyVec P (S ∪ T) + subsetEntropyVec P (S ∩ T) ≤
      subsetEntropyVec P S + subsetEntropyVec P T := by
  simp only [subsetEntropyVec_eq]
  have core := entropy_submod_triple P (restr S) (restr T) (restr (S ∩ T))
  have e1 : shannonEntropy (P.map (restr (S ∪ T))) =
      shannonEntropy (P.map fun x => (restr S x, restr T x, restr (S ∩ T) x)) := by
    refine entropy_map_eq_of_ker P fun x y => ?_
    simp only [Prod.mk.injEq, restr_eq_iff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2, -⟩ i (hi | hi)
      exacts [h1 i hi, h2 i hi]
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi),
        fun i hi => h i (Or.inl hi.1)⟩
  have e2 : ∀ U : Finset (Fin n), U ∩ T ⊆ U → shannonEntropy (P.map (restr U)) =
      shannonEntropy (P.map fun x => (restr U x, restr (U ∩ T) x)) := by
    intro U hU
    refine entropy_map_eq_of_ker P fun x y => ?_
    simp only [Prod.mk.injEq, restr_eq_iff]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun i hi => h i (hU hi)⟩
  have e3 : shannonEntropy (P.map (restr T)) =
      shannonEntropy (P.map fun x => (restr T x, restr (S ∩ T) x)) := by
    refine entropy_map_eq_of_ker P fun x y => ?_
    simp only [Prod.mk.injEq, restr_eq_iff]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun i hi => h i (Finset.mem_inter.1 hi).2⟩
  rw [e1, e2 S Finset.inter_subset_left, e3]
  exact core

/-- **Entropic vectors are polymatroids** — the Shannon inequalities, `Γ*_n ⊆ Γ_n`
(Fujishige 1978; Yeung 1997; Yeung 2008, Ch. 13–14). This validates `subsetEntropyVec`. -/
theorem entropic_isPolymatroid {n : ℕ} {h : Finset (Fin n) → ℝ} (hent : IsEntropicVector n h) :
    IsPolymatroid n h := by
  obtain ⟨k, P, hP⟩ := hent
  refine ⟨?_, ?_, ?_⟩
  · rw [hP]; exact subsetEntropyVec_empty P
  · intro S T hST
    rw [hP, hP]; exact subsetEntropyVec_mono P hST
  · intro S T
    rw [hP, hP, hP, hP]; exact subsetEntropyVec_submod P S T

/-- **The almost-entropic cone lies in the polymatroid cone**, `cl(Γ*_n) ⊆ Γ_n`
(Yeung 2008, Ch. 13–15; Zhang–Yeung 1998: `Γ_n` is closed and contains `Γ*_n`). -/
theorem almostEntropic_isPolymatroid {n : ℕ} {h : Finset (Fin n) → ℝ}
    (hae : InAlmostEntropicCone n h) : IsPolymatroid n h := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    obtain ⟨h', hh', hclose⟩ := hae |h ∅| (abs_pos.2 hne)
    have h0 := (entropic_isPolymatroid hh').1
    have := hclose ∅
    rw [h0, sub_zero] at this
    exact lt_irrefl _ this
  · intro S T hST
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨h', hh', hclose⟩ := hae ((h S - h T) / 2) (by linarith)
    have hm := (entropic_isPolymatroid hh').2.1 S T hST
    have h1 := abs_lt.1 (hclose S)
    have h2 := abs_lt.1 (hclose T)
    linarith [h1.1, h1.2, h2.1, h2.2]
  · intro S T
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨h', hh', hclose⟩ :=
      hae ((h (S ∪ T) + h (S ∩ T) - h S - h T) / 4) (by linarith)
    have hm := (entropic_isPolymatroid hh').2.2 S T
    have h1 := abs_lt.1 (hclose (S ∪ T))
    have h2 := abs_lt.1 (hclose (S ∩ T))
    have h3 := abs_lt.1 (hclose S)
    have h4 := abs_lt.1 (hclose T)
    linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

end EntropicVector

/-! ### Sanity checks on the polymatroid cone -/

section PolymatroidSanity

/-- Polymatroids are nonnegative (`h S ≥ h ∅ = 0` by monotonicity), so the definition of
`IsPolymatroid` indeed encodes the "nonnegative" clause of `Γ_n` (Yeung 2008, Ch. 14). -/
theorem polymatroid_nonneg {n : ℕ} {h : Finset (Fin n) → ℝ} (hp : IsPolymatroid n h)
    (S : Finset (Fin n)) : 0 ≤ h S := by
  have := hp.2.1 ∅ S (Finset.empty_subset S)
  rw [hp.1] at this
  exact this

/-- An integer polymatroid on 4 elements: `h(i) = 2`, `h(ij) = 3` except `h(34) = 4`,
and `h = 4` on all sets of size `≥ 3`. -/
def ingletonViolator (S : Finset (Fin 4)) : ℕ :=
  if S.card = 0 then 0 else if S.card = 1 then 2 else if S.card = 2 ∧ S ≠ {2, 3} then 3 else 4

/-- **Ingleton is not a Shannon inequality** (Ingleton 1971; Hammer–Romashchenko–Shen–
Vereshchagin 2000; the explicit witness below was found by a small computer search):
there is a polymatroid on 4 elements violating Ingleton's inequality
(`h(12)+h(13)+h(14)+h(23)+h(24) = 15 < 16 = h(1)+h(2)+h(34)+h(123)+h(124)`). Hence
`ingleton_of_linearRank` is a genuine (non-Shannon-derivable) constraint on `L_4`. -/
theorem exists_polymatroid_not_ingleton :
    ∃ h : Finset (Fin 4) → ℝ, IsPolymatroid 4 h ∧
      ¬ (h {0} + h {1} + h {2, 3} + h {0, 1, 2} + h {0, 1, 3} ≤
        h {0, 1} + h {0, 2} + h {0, 3} + h {1, 2} + h {1, 3}) := by
  refine ⟨fun S => (ingletonViolator S : ℝ), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [ingletonViolator]
  · have key : ∀ S T : Finset (Fin 4), S ⊆ T → ingletonViolator S ≤ ingletonViolator T := by
      decide
    intro S T hST
    beta_reduce
    exact_mod_cast key S T hST
  · have key : ∀ S T : Finset (Fin 4), ingletonViolator (S ∪ T) + ingletonViolator (S ∩ T) ≤
        ingletonViolator S + ingletonViolator T := by
      decide
    intro S T
    beta_reduce
    exact_mod_cast key S T
  · have key : ingletonViolator {0, 1} + ingletonViolator {0, 2} + ingletonViolator {0, 3} +
        ingletonViolator {1, 2} + ingletonViolator {1, 3} <
        ingletonViolator {0} + ingletonViolator {1} + ingletonViolator {2, 3} +
        ingletonViolator {0, 1, 2} + ingletonViolator {0, 1, 3} := by
      decide
    rw [not_le]
    beta_reduce
    exact_mod_cast key

/-- Consequently the polymatroid cone strictly contains the linear rank vectors on 4 elements:
`ingletonViolator` is a polymatroid that is not a linear rank vector. -/
theorem exists_polymatroid_not_linearRank :
    ∃ h : Finset (Fin 4) → ℝ, IsPolymatroid 4 h ∧ ¬ IsLinearRankVector 4 h := by
  obtain ⟨h, hp, hI⟩ := exists_polymatroid_not_ingleton
  exact ⟨h, hp, fun hl => hI (ingleton_of_linearRank hl)⟩

end PolymatroidSanity

end InfoTheory.Known
