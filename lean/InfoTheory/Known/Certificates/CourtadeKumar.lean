import InfoTheory.Problems.CourtadeKumar
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.CourtadeKumar`

The frozen statement asserts `mutualInfoBSC n α _ _ f ≤ 1 - binaryEntropy α` for all `n`,
`α ∈ (0, 1/2)` and Boolean `f : {0,1}^n → {0,1}` (Courtade–Kumar, "Which Boolean functions
maximize mutual information on noisy inputs?", IEEE Trans. Inf. Theory 60(8), 2014,
Conjecture 1). This file proves known facts about the *exact* object `mutualInfoBSC` from
`InfoTheory/Core/Channels.lean`, showing the formalization is faithful.

## Certified
* `mutualInfoBSC_dictator_equiv`, `mutualInfoBSC_dictator`, `mutualInfoBSC_antidictator`:
  for `n ≥ 1` the dictator `f(x) = x₀` (and anti-dictator `¬x₀`) attains
  `I(f(X); Y) = 1 - h(α)` exactly (Courtade–Kumar 2014). Hence `statement_tight`: the
  conjectured bound cannot be lowered, and `statement_rhs_eq_bsc_capacity`: it equals
  `C(BSC(α))` (reusing `Known.bsc_capacity`, Cover–Thomas §7.1.4).
* `mutualInfoBSC_const`: constant functions give `I = 0`.
* `mutualInfoBSC_nonneg`, `mutualInfoBSC_le_one`: `0 ≤ I(f(X); Y) ≤ H(f(X)) ≤ 1`
  (Cover–Thomas Thms 2.6.3, 2.6.4).
* `mutualInfoBSC_one_cases`, `mutualInfoBSC_one_le`, `mutualInfoBSC_zero_le`,
  `statement_of_le_one`: the Statement holds for `n ≤ 1` (for `n = 1` every Boolean
  function is constant, a dictator or an anti-dictator), even for every `α ∈ [0, 1]`.

## Not certified
* The known partial results for `n ≥ 2` — e.g. the strong-data-processing bound
  `I(f(X); Y) ≤ (1-2α)²` (Ahlswede–Gács 1976), Ordentlich–Shayevitz–Weinstein 2016,
  Samorodnitsky 2016 (the conjecture for `α` below an absolute constant), and
  Pichler–Piantanida–Matz 2018 (the two-function version) — are deep and out of scope.
* No junk value was found: `mutualInfoBSC` is a finite sum, and the dictator calculation
  reproduces the textbook value.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CourtadeKumar

open InfoTheory

private lemma log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

private lemma negPLogP_of_nonneg {p : ℝ} (hp : 0 ≤ p) : negPLogP p = -p * log2 p := by
  unfold negPLogP
  split_ifs with h
  · have : p = 0 := le_antisymm h hp
    simp [this]
  · rfl

private lemma negPLogP_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negPLogP (a * b) = a * negPLogP b + b * negPLogP a := by
  rw [negPLogP_of_nonneg (mul_nonneg ha hb), negPLogP_of_nonneg ha, negPLogP_of_nonneg hb]
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp
  unfold log2; rw [Real.log_mul ha'.ne' hb'.ne']; ring

/-- pmf of the pushforward `(f(X), Y)`. -/
lemma map_fst_pmf {A B : Type*} [Fintype A] [Fintype B] (P : ProbDist (A × B)) (f : A → Bool)
    (b : Bool) (y : B) :
    (P.map (fun xy => (f xy.1, xy.2))).pmf (b, y) = ∑ x, if f x = b then P.pmf (x, y) else 0 := by
  classical
  simp only [ProbDist.map, Fintype.sum_prod_type, Prod.mk.injEq]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : f x = b <;> simp [hx]

section Fixed

variable {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1)

/-- The BSC is doubly stochastic: column sums are `1`. -/
lemma bsc_col_sum (y : Bool) : ∑ a, (bsc α h0 h1).trans a y = 1 := by
  cases y <;> simp [bsc]

/-- Column sums of `BSC(α)^n` are `1`. -/
lemma bscPower_col_sum {n : ℕ} (y : Fin n → Bool) :
    ∑ x : Fin n → Bool, ((bsc α h0 h1).power n).trans x y = 1 := by
  simp only [DMC.power]
  rw [← Fintype.prod_sum (fun i a => (bsc α h0 h1).trans a (y i))]
  exact Finset.prod_eq_one (fun i _ => bsc_col_sum h0 h1 (y i))

lemma bscNoisyPair_pmf {n : ℕ} (x y : Fin n → Bool) :
    (bscNoisyPair n α h0 h1).pmf (x, y) =
      (1 / (2 : ℝ) ^ n) * ((bsc α h0 h1).power n).trans x y := by
  simp [bscNoisyPair, DMC.joint, ProbDist.uniform]

/-- Sum of a function of the first coordinate. -/
lemma sum_apply_zero {m : ℕ} (F : Bool → ℝ) :
    ∑ y : Fin (m + 1) → Bool, F (y 0) = 2 ^ m * ∑ a, F a := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp]
  simp [Fin.consEquiv, Fintype.sum_prod_type]
  ring

/-- Joint pmf of `(g(X₀), Y)` for `X ~ Unif({0,1}^(m+1))`, `Y = BSC(α)^(m+1)(X)`:
`P(b, y) = 2^{-(m+1)} ∑_{a : g a = b} W(a, y₀)`. -/
lemma coord_pmf {m : ℕ} (g : Bool → Bool) (b : Bool) (y : Fin (m + 1) → Bool) :
    ((bscNoisyPair (m + 1) α h0 h1).map (fun xy => (g (xy.1 0), xy.2))).pmf (b, y) =
      (1 / (2 : ℝ) ^ (m + 1)) * ∑ a, if g a = b then (bsc α h0 h1).trans a (y 0) else 0 := by
  rw [map_fst_pmf (bscNoisyPair (m + 1) α h0 h1) (fun x => g (x 0)) b y]
  have key : ∀ x : Fin (m + 1) → Bool,
      (if g (x 0) = b then (bscNoisyPair (m + 1) α h0 h1).pmf (x, y) else 0) =
        (1 / (2 : ℝ) ^ (m + 1)) * ∏ i, ((if i = 0 then (if g (x i) = b then 1 else 0) else 1) *
          (bsc α h0 h1).trans (x i) (y i)) := by
    intro x
    rw [bscNoisyPair_pmf, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    simp only [DMC.power]
    split_ifs <;> simp
  simp_rw [key, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun i a => (if i = 0 then (if g a = b then 1 else 0) else 1) *
    (bsc α h0 h1).trans a (y i))]
  rw [Fin.prod_univ_succ]
  simp only [ite_true, Fin.succ_ne_zero, ite_false, one_mul, bsc_col_sum, Finset.prod_const_one,
    mul_one]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs <;> simp

private lemma sum_ite_equiv (e : Bool ≃ Bool) (b : Bool) (F : Bool → ℝ) :
    (∑ a, if e a = b then F a else 0) = F (e.symm b) := by
  simp_rw [← Equiv.eq_symm_apply]
  simp

lemma dictator_pmf {m : ℕ} (e : Bool ≃ Bool) (b : Bool) (y : Fin (m + 1) → Bool) :
    ((bscNoisyPair (m + 1) α h0 h1).map (fun xy => (e (xy.1 0), xy.2))).pmf (b, y) =
      (1 / (2 : ℝ) ^ (m + 1)) * (bsc α h0 h1).trans (e.symm b) (y 0) := by
  rw [coord_pmf h0 h1 e b y, sum_ite_equiv e b (fun a => (bsc α h0 h1).trans a (y 0))]

private lemma negPLogP_half : negPLogP (1 / 2) = 1 / 2 := by
  have h2 : log2 (1 / 2) = -1 := by
    unfold log2
    rw [one_div, Real.log_inv, neg_div, div_self log_two_pos.ne']
  rw [negPLogP_of_nonneg (by norm_num), h2]; norm_num

private lemma sum_negPLogP_bsc (e : Bool ≃ Bool) (t : Bool) :
    ∑ b, negPLogP ((bsc α h0 h1).trans (e.symm b) t) = binaryEntropy α := by
  rw [e.symm.sum_comp (fun a => negPLogP ((bsc α h0 h1).trans a t))]
  cases t <;> simp [bsc, binaryEntropy, add_comm]

/-- **Tightness of the Courtade–Kumar bound** (Courtade–Kumar 2014, IEEE Trans. IT 60(8),
discussion after Conjecture 1): a dictator function `f(x) = x₀` (or its negation; any
`f(x) = e(x₀)` with `e` a bijection of `Bool`) achieves `I(f(X); Y) = 1 - h(α)`, i.e. the
capacity of `BSC(α)`. -/
theorem mutualInfoBSC_dictator_equiv (m : ℕ) (e : Bool ≃ Bool) :
    mutualInfoBSC (m + 1) α h0 h1 (fun x => e (x 0)) = 1 - binaryEntropy α := by
  set c : ℝ := 1 / (2 : ℝ) ^ (m + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set Q := (bscNoisyPair (m + 1) α h0 h1).map (fun xy => (e (xy.1 0), xy.2)) with hQ
  have hpmf : ∀ b y, Q.pmf (b, y) = c * (bsc α h0 h1).trans (e.symm b) (y 0) :=
    fun b y => dictator_pmf h0 h1 e b y
  have hfst : ∀ b, Q.fst.pmf b = 1 / 2 := by
    intro b
    simp only [ProbDist.fst, hpmf]
    rw [sum_apply_zero (fun t => c * (bsc α h0 h1).trans (e.symm b) t), ← Finset.mul_sum,
      (bsc α h0 h1).sum_one, hc]
    field_simp; ring
  have hsnd : ∀ y, Q.snd.pmf y = c := by
    intro y
    simp only [ProbDist.snd, hpmf, ← Finset.mul_sum]
    rw [e.symm.sum_comp (fun a => (bsc α h0 h1).trans a (y 0)), bsc_col_sum, mul_one]
  have hcard : (2 : ℝ) ^ (m + 1) * c = 1 := by rw [hc]; field_simp
  unfold mutualInfoBSC mutualInfo
  change shannonEntropy Q.fst + shannonEntropy Q.snd - shannonEntropy Q = _
  have H1 : shannonEntropy Q.fst = 1 := by
    unfold shannonEntropy; simp_rw [hfst, negPLogP_half]; simp
  have H2 : shannonEntropy Q.snd = ∑ _y : Fin (m + 1) → Bool, negPLogP c := by
    unfold shannonEntropy; simp_rw [hsnd]
  have H3 : shannonEntropy Q = binaryEntropy α + ∑ _y : Fin (m + 1) → Bool, negPLogP c := by
    unfold shannonEntropy
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [hpmf]
    have inner : ∀ t : Bool, ∑ b, negPLogP (c * (bsc α h0 h1).trans (e.symm b) t) =
        c * binaryEntropy α + negPLogP c := by
      intro t
      simp_rw [negPLogP_mul hc0 ((bsc α h0 h1).nonneg _ _)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_negPLogP_bsc h0 h1 e,
        e.symm.sum_comp (fun a => (bsc α h0 h1).trans a t), bsc_col_sum, one_mul]
    simp_rw [inner]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← mul_assoc, hcard, one_mul]
  rw [H1, H2, H3]; ring

/-- **Tightness, dictator form**: for `n ≥ 1` the dictator `f(x) = x₀` achieves
`I(f(X); Y) = 1 - h(α)` (Courtade–Kumar 2014), so the conjectured bound cannot be improved. -/
theorem mutualInfoBSC_dictator {n : ℕ} (hn : 0 < n) :
    mutualInfoBSC n α h0 h1 (fun x => x ⟨0, hn⟩) = 1 - binaryEntropy α := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact mutualInfoBSC_dictator_equiv h0 h1 m (Equiv.refl Bool)

/-- The anti-dictator `f(x) = ¬x₀` also achieves `1 - h(α)`. -/
theorem mutualInfoBSC_antidictator (m : ℕ) :
    mutualInfoBSC (m + 1) α h0 h1 (fun x => !(x 0)) = 1 - binaryEntropy α :=
  mutualInfoBSC_dictator_equiv h0 h1 m (Function.Involutive.toPerm _ Bool.not_not)

/-- A constant function carries no information: `I(c; Y) = 0`. -/
theorem mutualInfoBSC_const (n : ℕ) (b₀ : Bool) :
    mutualInfoBSC n α h0 h1 (fun _ => b₀) = 0 := by
  set Q := (bscNoisyPair n α h0 h1).map (fun xy => (b₀, xy.2)) with hQ
  have hpmf : ∀ b y, Q.pmf (b, y) = if b₀ = b then 1 / (2 : ℝ) ^ n else 0 := by
    intro b y
    rw [hQ, map_fst_pmf (bscNoisyPair n α h0 h1) (fun _ => b₀) b y]
    by_cases hb : b₀ = b
    · simp only [hb, ite_true]
      simp_rw [bscNoisyPair_pmf h0 h1, ← Finset.mul_sum, bscPower_col_sum h0 h1, mul_one]
    · simp [hb]
  have hfst : ∀ b, Q.fst.pmf b = if b₀ = b then 1 else 0 := by
    intro b
    simp only [ProbDist.fst, hpmf]
    by_cases hb : b₀ = b
    · simp only [hb, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast; field_simp
    · simp [hb]
  have H1 : shannonEntropy Q.fst = 0 := by
    unfold shannonEntropy
    simp_rw [hfst]
    cases b₀ <;> simp [negPLogP, log2]
  have hle := mutualInfo_le_entropy_fst Q
  have hge := InfoTheory.Bridge.mutualInfo_nonneg Q
  unfold mutualInfoBSC
  change mutualInfo Q = 0
  linarith

/-- `I(f(X); Y) ≥ 0` (Cover–Thomas Thm 2.6.3). -/
theorem mutualInfoBSC_nonneg (n : ℕ) (f : (Fin n → Bool) → Bool) :
    0 ≤ mutualInfoBSC n α h0 h1 f :=
  InfoTheory.Bridge.mutualInfo_nonneg _

/-- **Trivial bound** `I(f(X); Y) ≤ H(f(X)) ≤ log₂ 2 = 1` (Cover–Thomas Thms 2.6.4, 2.4.1),
valid for every `n`, every `α ∈ [0, 1]` and every Boolean `f`. -/
theorem mutualInfoBSC_le_one (n : ℕ) (f : (Fin n → Bool) → Bool) :
    mutualInfoBSC n α h0 h1 f ≤ 1 := by
  unfold mutualInfoBSC
  refine (mutualInfo_le_entropy_fst _).trans ?_
  refine (InfoTheory.Bridge.shannonEntropy_le_log2_card _).trans (le_of_eq ?_)
  simp [log2, div_self log_two_pos.ne']

include h0 h1 in
/-- The conjectured right-hand side `1 - h(α)` (= `C(BSC(α))`) is nonnegative. -/
theorem one_sub_binaryEntropy_nonneg : 0 ≤ 1 - binaryEntropy α := by
  linarith [binaryEntropy_le_one h0 h1]

/-- For `n = 1` every Boolean function is constant, a dictator or an anti-dictator, so
`I(f(X); Y) ∈ {0, 1 - h(α)}`. -/
theorem mutualInfoBSC_one_cases (f : (Fin 1 → Bool) → Bool) :
    mutualInfoBSC 1 α h0 h1 f = 0 ∨ mutualInfoBSC 1 α h0 h1 f = 1 - binaryEntropy α := by
  have hf : ∀ x : Fin 1 → Bool, f x = f (fun _ => x 0) := fun x =>
    congrArg f (funext fun i => by rw [Fin.fin_one_eq_zero i])
  cases h₁ : f (fun _ => false) <;> cases h₂ : f (fun _ => true)
  · left
    have : f = fun _ => false := funext fun x => by
      rw [hf x]; cases x 0 <;> assumption
    rw [this]; exact mutualInfoBSC_const h0 h1 1 false
  · right
    have : f = fun x => (Equiv.refl Bool) (x 0) := funext fun x => by
      rw [hf x]; cases hx : x 0 <;> simpa
    rw [this]; exact mutualInfoBSC_dictator_equiv h0 h1 0 _
  · right
    have : f = fun x => (Function.Involutive.toPerm _ Bool.not_not) (x 0) := funext fun x => by
      rw [hf x]; cases hx : x 0 <;> simpa
    rw [this]; exact mutualInfoBSC_dictator_equiv h0 h1 0 _
  · left
    have : f = fun _ => true := funext fun x => by
      rw [hf x]; cases x 0 <;> assumption
    rw [this]; exact mutualInfoBSC_const h0 h1 1 true

/-- **The case `n = 1` of the Courtade–Kumar conjecture** (folklore; Courtade–Kumar 2014),
in fact for every `α ∈ [0, 1]`. -/
theorem mutualInfoBSC_one_le (f : (Fin 1 → Bool) → Bool) :
    mutualInfoBSC 1 α h0 h1 f ≤ 1 - binaryEntropy α := by
  rcases mutualInfoBSC_one_cases h0 h1 f with h | h <;> rw [h]
  exact one_sub_binaryEntropy_nonneg h0 h1

/-- The degenerate case `n = 0` (every `f` is constant). -/
theorem mutualInfoBSC_zero_le (f : (Fin 0 → Bool) → Bool) :
    mutualInfoBSC 0 α h0 h1 f ≤ 1 - binaryEntropy α := by
  have : f = fun _ => f default := funext fun x => congrArg f (Subsingleton.elim _ _)
  rw [this, mutualInfoBSC_const h0 h1 0]
  exact one_sub_binaryEntropy_nonneg h0 h1

end Fixed

/-- **The Statement restricted to `n ≤ 1`** holds (the open content is `n ≥ 2`). -/
theorem statement_of_le_one :
    ∀ (n : ℕ), n ≤ 1 → ∀ (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (f : (Fin n → Bool) → Bool),
      mutualInfoBSC n α (le_of_lt h0) (by linarith) f ≤ 1 - binaryEntropy α := by
  intro n hn α h0 h1 f
  interval_cases n
  · exact mutualInfoBSC_zero_le _ _ f
  · exact mutualInfoBSC_one_le _ _ f

/-- **Tightness of the Statement**: for every admissible `α` and `n ≥ 1` the bound is attained,
so `1 - h(α)` cannot be replaced by anything smaller. -/
theorem statement_tight (n : ℕ) (hn : 0 < n) (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∃ f : (Fin n → Bool) → Bool,
      mutualInfoBSC n α (le_of_lt h0) (by linarith) f = 1 - binaryEntropy α :=
  ⟨_, mutualInfoBSC_dictator _ _ hn⟩

/-- The right-hand side `1 - h(α)` of the Statement is the BSC capacity
(reuses `Known.bsc_capacity`; Cover–Thomas §7.1.4). -/
theorem statement_rhs_eq_bsc_capacity (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    1 - binaryEntropy α = (bsc α h0 h1).capacity :=
  (InfoTheory.Known.bsc_capacity h0 h1).symm

end InfoTheory.Known.Certificates.CourtadeKumar
