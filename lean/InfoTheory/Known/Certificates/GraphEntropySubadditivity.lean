import InfoTheory.Problems.GraphEntropySubadditivity
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.GraphEntropySubadditivity`

Statement-fix (2026-11-27): the frozen statement now asks Körner's question (recorded by
Simonyi 2001, §7.4) whether the complementary graph entropy
`H̄(G, P) = lim_{ε→0} limsup_t min_{P^t(U)>1-ε} (1/t) log₂ χ(G^{⊠t}[U])`
(`complementaryGraphEntropy`) is subadditive under edge union.

## Certified for `H̄(G, P)` (the objects of the current `Statement`)
* `iidProb_univ`: `P^t(Fin t → V) = 1`, so the block minimisation is over a non-empty set.
* `block_le`, `block_nonneg`, `block_le_log2_of_coloring`, `block_le_log2_card`; the
  `limsup` layer `limsup_le`, `limsup_nonneg`; and the `ε → 0` layer `coEntropy_le`,
  `coEntropy_nonneg`. Together these give **no junk values**: `0 ≤ H̄(G, P) ≤ log₂ |V|`.
* `coEntropy_le_log2_of_coloring`: `H̄(G, P) ≤ log₂ χ(G)` (product colouring of `G^{⊠t}`).
* Regressions: `coEntropy_bot` gives `H̄(\bar K_n, P) = 0`, and `coEntropy_top_uniform` gives
  `H̄(K_n, Unif) = log₂ n = H(Unif)`. The latter is the textbook value `H̄(K_n, P) = H(P)` at
  the uniform `P`, and it needs the full `lim inf/sup` structure: each block satisfies
  `≥ log₂ n + log₂(1-ε)/t`.
* Instances of the inequality in `Statement`: `coEntropy_subadditive_bot_left`, and
  `coEntropy_union_compl_uniform`, where for `F ∪ Fᶜ = K_n` the left side is exactly `log₂ n`.

## Also certified (previous target, kept as related facts about Witsenhausen's rate)
* Witsenhausen's bounds `log₂ ω ≤ R₀ ≤ log₂ χ`, `R₀(K_n) = log₂ n`, `R₀(\bar K_n) = 0`;
  `graphUnion` sanity (`graphUnion_compl : F ∪ Fᶜ = K_n`); and the product-colouring
  bound `rate_union_le_log2_mul`.

## Not certified
* `H̄(G, P) = H(P)` for general `P` on `K_n` (needs the AEP); Marton's cases (`F, G` perfect,
  or `F ∪ G` perfect) of the open inequality.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.GraphEntropySubadditivity

open InfoTheory InfoTheory.Problems.GraphEntropySubadditivity

section Witsenhausen

variable {V : Type*} [Fintype V]

theorem rate_nonneg (G : SimpleGraph V) : 0 ≤ witsenhausenRate G := by
  refine Real.sInf_nonneg ?_
  rintro r ⟨k, m, c, hk, hm, -, rfl⟩
  refine div_nonneg ?_ (Nat.cast_nonneg k)
  unfold log2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (Real.log_pos one_lt_two).le

/-- **Colouring upper bound** `R₀(G) ≤ log₂ m` (Witsenhausen 1976). -/
theorem rate_le_log2_of_coloring (G : SimpleGraph V) {m : ℕ} (hm : 0 < m)
    (c : V → Fin m) (hc : ∀ x y, G.Adj x y → c x ≠ c y) : witsenhausenRate G ≤ log2 m := by
  have hmem : log2 (m : ℝ) / ((1 : ℕ) : ℝ) ∈ { r : ℝ | ∃ (k : ℕ) (m : ℕ)
      (c : (Fin k → V) → Fin m),
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

theorem rate_le_log2_card [Nonempty V] (G : SimpleGraph V) :
    witsenhausenRate G ≤ log2 (Fintype.card V) :=
  rate_le_log2_of_coloring G Fintype.card_pos (Fintype.equivFin V)
    fun _ _ h => (Fintype.equivFin V).injective.ne (G.ne_of_adj h)

/-- **Clique lower bound** `log₂ ω(G) ≤ R₀(G)` (Witsenhausen 1976). -/
theorem log2_clique_le_rate [Nonempty V] (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) : log2 (S.card : ℝ) ≤ witsenhausenRate G := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, log2, Real.log_zero, zero_div]
    exact rate_nonneg G
  refine le_csInf ⟨_, 1, Fintype.card V, fun x => Fintype.equivFin V (x 0), one_pos,
    Fintype.card_pos, fun x y ⟨hne, _⟩ => ?_, rfl⟩ ?_
  · intro h
    exact hne (funext fun i => by
      rw [Fin.fin_one_eq_zero i]; exact (Fintype.equivFin V).injective h)
  rintro r ⟨k, m, c, hk, hm, hc, rfl⟩
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

theorem rate_top [Nonempty V] [DecidableEq V] :
    witsenhausenRate (⊤ : SimpleGraph V) = log2 (Fintype.card V) := by
  refine le_antisymm (rate_le_log2_card _) ?_
  have := log2_clique_le_rate (⊤ : SimpleGraph V) Finset.univ (fun x _ y _ h => h)
  simpa using this

theorem rate_bot : witsenhausenRate (⊥ : SimpleGraph V) = 0 := by
  refine le_antisymm ?_ (rate_nonneg _)
  have := rate_le_log2_of_coloring (⊥ : SimpleGraph V) one_pos (fun _ => 0)
    (fun _ _ h => h.elim)
  simpa [log2] using this

end Witsenhausen

/-! ### `graphUnion` is the edge union -/

section Union

variable {V : Type*}

theorem graphUnion_adj (F G : SimpleGraph V) (u v : V) :
    (graphUnion F G).Adj u v ↔ F.Adj u v ∨ G.Adj u v := Iff.rfl

theorem graphUnion_comm (F G : SimpleGraph V) : graphUnion F G = graphUnion G F := by
  ext u v; exact or_comm

theorem graphUnion_bot (F : SimpleGraph V) : graphUnion F ⊥ = F := by
  ext u v; simp [graphUnion_adj]

theorem graphUnion_self (F : SimpleGraph V) : graphUnion F F = F := by
  ext u v; simp [graphUnion_adj]

/-- `F ∪ Fᶜ = K_V`: the complementary case of the problem. -/
theorem graphUnion_compl (F : SimpleGraph V) : graphUnion F Fᶜ = ⊤ := by
  ext u v
  simp only [graphUnion_adj, SimpleGraph.compl_adj, SimpleGraph.top_adj]
  constructor
  · rintro (h | h)
    · exact F.ne_of_adj h
    · exact h.1
  · intro h
    by_cases hF : F.Adj u v
    · exact Or.inl hF
    · exact Or.inr ⟨h, hF⟩

end Union

/-! ### Product-colouring bound and the perfect-type regression -/

/-- **Product colouring:** `R₀(F ∪ G) ≤ log₂ a + log₂ b` for proper colourings of `F`, `G`
    with `a`, `b` colours. -/
theorem rate_union_le_log2_mul {V : Type*} [Fintype V] (F G : SimpleGraph V) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (cF : V → Fin a) (hF : ∀ x y, F.Adj x y → cF x ≠ cF y)
    (cG : V → Fin b) (hG : ∀ x y, G.Adj x y → cG x ≠ cG y) :
    witsenhausenRate (graphUnion F G) ≤ log2 a + log2 b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have h := rate_le_log2_of_coloring (graphUnion F G) hab
    (fun v => finProdFinEquiv (cF v, cG v)) (by
      intro x y hxy hc
      have hc' := finProdFinEquiv.injective hc
      simp only [Prod.mk.injEq] at hc'
      rcases hxy with h1 | h1
      · exact hF _ _ h1 hc'.1
      · exact hG _ _ h1 hc'.2)
  have hlog : log2 ((a * b : ℕ) : ℝ) = log2 a + log2 b := by
    unfold log2
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
    ring
  rw [hlog] at h
  exact h

/-- **Regression (perfect-type graphs):** if `R₀(F) = log₂ a` and `R₀(G) = log₂ b` are
    attained by one-shot colourings (as for perfect graphs, `R₀ = log₂ χ`), then the
    inequality of `Statement` holds for `(F, G)`. -/
theorem subadditive_of_rate_eq_log2_coloring {V : Type*} [Fintype V] (F G : SimpleGraph V)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (cF : V → Fin a) (hF : ∀ x y, F.Adj x y → cF x ≠ cF y)
    (cG : V → Fin b) (hG : ∀ x y, G.Adj x y → cG x ≠ cG y)
    (hRF : witsenhausenRate F = log2 a) (hRG : witsenhausenRate G = log2 b) :
    witsenhausenRate (graphUnion F G) ≤ witsenhausenRate F + witsenhausenRate G := by
  rw [hRF, hRG]; exact rate_union_le_log2_mul F G ha hb cF hF cG hG

/-- Concrete instance: `R₀(K_n ∪ K_n) = log₂ n ≤ 2 log₂ n`. -/
theorem subadditive_top_top (n : ℕ) :
    witsenhausenRate (graphUnion (⊤ : SimpleGraph (Fin n)) ⊤) ≤
      witsenhausenRate (⊤ : SimpleGraph (Fin n)) + witsenhausenRate (⊤ : SimpleGraph (Fin n)) := by
  rw [graphUnion_self]
  have := rate_nonneg (⊤ : SimpleGraph (Fin n))
  linarith

/-- Concrete instance: `R₀(\bar K_n ∪ G) = R₀(G)`. -/
theorem subadditive_bot_left {n : ℕ} (G : SimpleGraph (Fin n)) :
    witsenhausenRate (graphUnion (⊥ : SimpleGraph (Fin n)) G) ≤
      witsenhausenRate (⊥ : SimpleGraph (Fin n)) + witsenhausenRate G := by
  rw [graphUnion_comm, graphUnion_bot, rate_bot, zero_add]

/-- The complementary case has left-hand side exactly `log₂ n`. -/
theorem rate_union_compl (n : ℕ) (hn : 0 < n) (F : SimpleGraph (Fin n)) :
    witsenhausenRate (graphUnion F Fᶜ) = log2 n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [graphUnion_compl, rate_top, Fintype.card_fin]

/-! ### Complementary graph entropy `H̄(G, P)` (objects of the current `Statement`) -/

section CoEntropy

variable {V : Type*} [Fintype V]

theorem log2_nat_nonneg' {m : ℕ} (hm : 0 < m) : 0 ≤ log2 (m : ℝ) := by
  unfold log2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (Real.log_pos one_lt_two).le

theorem iidProb_univ (P : ProbDist V) (t : ℕ) : iidProb P t Finset.univ = 1 := by
  unfold iidProb
  have h := Fintype.prod_sum (fun (_ : Fin t) (v : V) => P.pmf v)
  simp only [P.sum_one, Finset.prod_const_one] at h
  exact h.symm

theorem block_le (G : SimpleGraph V) (P : ProbDist V) {ε : ℝ} {t : ℕ}
    (U : Finset (Fin t → V)) {m : ℕ} (c : (Fin t → V) → Fin m)
    (hU : 1 - ε < iidProb P t U) (hm : 0 < m)
    (hc : ∀ x ∈ U, ∀ y ∈ U, (strongPower G t).Adj x y → c x ≠ c y) :
    coEntropyBlock G P ε t ≤ log2 (m : ℝ) / (t : ℝ) := by
  unfold coEntropyBlock
  refine csInf_le ⟨0, ?_⟩ ⟨U, m, c, hU, hm, hc, rfl⟩
  rintro r ⟨U, m, c, -, hm, -, rfl⟩
  exact div_nonneg (log2_nat_nonneg' hm) (Nat.cast_nonneg _)

theorem block_nonneg (G : SimpleGraph V) (P : ProbDist V) (ε : ℝ) (t : ℕ) :
    0 ≤ coEntropyBlock G P ε t := by
  unfold coEntropyBlock
  apply Real.sInf_nonneg
  rintro r ⟨U, m, c, -, hm, -, rfl⟩
  exact div_nonneg (log2_nat_nonneg' hm) (Nat.cast_nonneg _)

/-- Product colouring: a proper `m`-colouring of `G` colours every strong power, so each block
    quantity is at most `log₂ m`. -/
theorem block_le_log2_of_coloring (G : SimpleGraph V) (P : ProbDist V) {ε : ℝ} (hε : 0 < ε)
    {t : ℕ} (ht : 0 < t) {m : ℕ} (hm : 0 < m) (c0 : V → Fin m)
    (hc0 : ∀ x y, G.Adj x y → c0 x ≠ c0 y) :
    coEntropyBlock G P ε t ≤ log2 (m : ℝ) := by
  have hne : Nonempty (Fin t → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
  have hcard : 0 < Fintype.card (Fin t → Fin m) := Fintype.card_pos
  refine (block_le G P Finset.univ
    (fun x => Fintype.equivFin (Fin t → Fin m) (fun i => c0 (x i))) ?_ hcard ?_).trans_eq ?_
  · rw [iidProb_univ]; linarith
  · rintro x - y - ⟨hxy, h⟩ heq
    have h2 := (Fintype.equivFin _).injective heq
    apply hxy
    funext i
    rcases h i with h' | h'
    · exact h'
    · exact absurd (congrFun h2 i) (hc0 _ _ h')
  · have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    unfold log2
    rw [Real.log_pow]
    field_simp

theorem block_le_log2_card [Nonempty V] (G : SimpleGraph V) (P : ProbDist V) {ε : ℝ}
    (hε : 0 < ε) : ∀ t : ℕ, 0 < t → coEntropyBlock G P ε t ≤ log2 (Fintype.card V) :=
  fun _ ht => block_le_log2_of_coloring G P hε ht Fintype.card_pos (Fintype.equivFin V)
    fun _ _ h => (Fintype.equivFin V).injective.ne (G.ne_of_adj h)

theorem limsup_le {G : SimpleGraph V} {P : ProbDist V} {ε B : ℝ}
    (hB : ∀ t : ℕ, 0 < t → coEntropyBlock G P ε t ≤ B) :
    coEntropyLimsup G P ε ≤ B := by
  unfold coEntropyLimsup
  refine csInf_le_of_le (b := sSup {r : ℝ | ∃ t : ℕ, 0 ≤ t ∧ 0 < t ∧
      r = coEntropyBlock G P ε t}) ⟨0, ?_⟩ ⟨0, rfl⟩ ?_
  · rintro s ⟨N, rfl⟩
    refine le_trans (block_nonneg G P ε (N + 1))
      (le_csSup ⟨B, ?_⟩ ⟨N + 1, Nat.le_succ N, Nat.succ_pos N, rfl⟩)
    rintro r ⟨t, -, ht, rfl⟩
    exact hB t ht
  · refine csSup_le ⟨_, 1, Nat.zero_le 1, one_pos, rfl⟩ ?_
    rintro r ⟨t, -, ht, rfl⟩
    exact hB t ht

theorem limsup_nonneg {G : SimpleGraph V} {P : ProbDist V} {ε B : ℝ}
    (hB : ∀ t : ℕ, 0 < t → coEntropyBlock G P ε t ≤ B) :
    0 ≤ coEntropyLimsup G P ε := by
  unfold coEntropyLimsup
  apply Real.sInf_nonneg
  rintro s ⟨N, rfl⟩
  refine le_trans (block_nonneg G P ε (N + 1))
    (le_csSup ⟨B, ?_⟩ ⟨N + 1, Nat.le_succ N, Nat.succ_pos N, rfl⟩)
  rintro r ⟨t, -, ht, rfl⟩
  exact hB t ht

theorem coEntropy_le {G : SimpleGraph V} {P : ProbDist V} {B : ℝ}
    (hB : ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 0 < t → coEntropyBlock G P ε t ≤ B) :
    complementaryGraphEntropy G P ≤ B := by
  unfold complementaryGraphEntropy
  refine csSup_le ⟨_, 1 / 2, by norm_num, by norm_num, rfl⟩ ?_
  rintro h ⟨ε, hε0, -, rfl⟩
  exact limsup_le (hB ε hε0)

theorem coEntropy_nonneg [Nonempty V] (G : SimpleGraph V) (P : ProbDist V) :
    0 ≤ complementaryGraphEntropy G P := by
  unfold complementaryGraphEntropy
  apply Real.sSup_nonneg
  rintro h ⟨ε, hε0, -, rfl⟩
  exact limsup_nonneg (block_le_log2_card G P hε0)

/-- **No junk:** `H̄(G, P) ≤ log₂ |V|`. -/
theorem coEntropy_le_log2_card [Nonempty V] (G : SimpleGraph V) (P : ProbDist V) :
    complementaryGraphEntropy G P ≤ log2 (Fintype.card V) :=
  coEntropy_le fun _ hε => block_le_log2_card G P hε

/-- `H̄(G, P) ≤ log₂ χ(G)`: for any proper `m`-colouring of `G`. -/
theorem coEntropy_le_log2_of_coloring (G : SimpleGraph V) (P : ProbDist V) {m : ℕ}
    (hm : 0 < m) (c0 : V → Fin m) (hc0 : ∀ x y, G.Adj x y → c0 x ≠ c0 y) :
    complementaryGraphEntropy G P ≤ log2 (m : ℝ) :=
  coEntropy_le fun _ hε _ ht => block_le_log2_of_coloring G P hε ht hm c0 hc0

/-- Regression: the edgeless graph has `H̄(\bar K_n, P) = 0`. -/
theorem coEntropy_bot [Nonempty V] (P : ProbDist V) :
    complementaryGraphEntropy (⊥ : SimpleGraph V) P = 0 := by
  refine le_antisymm ?_ (coEntropy_nonneg _ P)
  have := coEntropy_le_log2_of_coloring (⊥ : SimpleGraph V) P one_pos (fun _ => 0)
    (fun _ _ h => h.elim)
  simpa [log2] using this

/-- Each block of the complete graph under the uniform law is at least
    `log₂ |V| + log₂(1 - ε)/t`: a proper colouring of `K^{⊠t}[U]` is injective on `U`, and
    `P^t(U) = |U| / |V|^t > 1 - ε`. -/
theorem block_top_uniform_ge [Nonempty V] {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {t : ℕ}
    (ht : 0 < t) :
    log2 (Fintype.card V : ℝ) + log2 (1 - ε) / t ≤
      coEntropyBlock (⊤ : SimpleGraph V) ProbDist.uniform ε t := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  unfold coEntropyBlock
  apply le_csInf
  · refine ⟨_, Finset.univ, Fintype.card (Fin t → V), Fintype.equivFin (Fin t → V), ?_,
      Fintype.card_pos, ?_, rfl⟩
    · rw [iidProb_univ]; linarith
    · rintro x - y - ⟨hxy, -⟩ h
      exact hxy ((Fintype.equivFin _).injective h)
  rintro r ⟨U, m, c, hU, hm, hc, rfl⟩
  have hinj : Set.InjOn c U := by
    intro x hx y hy hxy
    by_contra hne
    refine hc x hx y hy ⟨hne, fun i => ?_⟩ hxy
    by_cases h : x i = y i
    · exact Or.inl h
    · exact Or.inr ((SimpleGraph.top_adj _ _).mpr h)
  have hcardU : (U.card : ℝ) ≤ m := by
    have := Finset.card_le_card_of_injOn c (fun x _ => Finset.mem_univ (c x)) hinj
    simpa using (show (U.card : ℝ) ≤ ((Finset.univ : Finset (Fin m)).card : ℝ) by
      exact_mod_cast this)
  have hprob : iidProb (ProbDist.uniform : ProbDist V) t U =
      U.card * ((Fintype.card V : ℝ) ^ t)⁻¹ := by
    unfold iidProb
    simp [ProbDist.uniform, Finset.sum_const, Finset.prod_const]
  rw [hprob, lt_mul_inv_iff₀ (by positivity)] at hU
  have h2 : (1 - ε) * (Fintype.card V : ℝ) ^ t < m := lt_of_lt_of_le hU hcardU
  have h3 : log2 ((1 - ε) * (Fintype.card V : ℝ) ^ t) ≤ log2 (m : ℝ) := by
    unfold log2
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (mul_pos (by linarith) (by positivity)) h2.le)
      (Real.log_pos one_lt_two).le
  have h4 : log2 ((1 - ε) * (Fintype.card V : ℝ) ^ t) =
      log2 (1 - ε) + t * log2 (Fintype.card V : ℝ) := by
    unfold log2
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    ring
  rw [le_div_iff₀ htR, add_mul, div_mul_cancel₀ _ htR.ne']
  linarith

theorem le_of_forall_add_div_le {L a S : ℝ} {N : ℕ}
    (h : ∀ t : ℕ, N ≤ t → 0 < t → L + a / t ≤ S) (ha : a ≤ 0) : L ≤ S := by
  by_contra hlt0
  have hlt : S < L := lt_of_not_ge hlt0
  have hSL : S - L < 0 := by linarith
  obtain ⟨t, ht⟩ := exists_nat_gt (max (N : ℝ) (a / (S - L)))
  have htN : (N : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
  have hta : a / (S - L) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have ht0 : 0 < t := by
    have : (0 : ℝ) < t := lt_of_le_of_lt (Nat.cast_nonneg N) htN
    exact_mod_cast this
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have h1 := h t (by exact_mod_cast htN.le) ht0
  rw [div_lt_iff_of_neg hSL] at hta
  have h2 : a / t ≤ S - L := by linarith
  rw [div_le_iff₀ htR] at h2
  linarith

/-- Regression: `H̄(K_n, Unif) = log₂ n` (= `H(Unif)`, the textbook value `H̄(K_n, P) = H(P)`). -/
theorem coEntropy_top_uniform [Nonempty V] :
    complementaryGraphEntropy (⊤ : SimpleGraph V) ProbDist.uniform =
      log2 (Fintype.card V : ℝ) := by
  refine le_antisymm (coEntropy_le_log2_card _ _) ?_
  have hε0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hε1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hlim : log2 (Fintype.card V : ℝ) ≤
      coEntropyLimsup (⊤ : SimpleGraph V) ProbDist.uniform (1 / 2) := by
    unfold coEntropyLimsup
    refine le_csInf ⟨_, 0, rfl⟩ ?_
    rintro s ⟨N, rfl⟩
    refine le_of_forall_add_div_le (a := log2 (1 - 1 / 2)) (N := N) (fun t hNt ht => ?_) ?_
    · refine le_trans (block_top_uniform_ge hε0 hε1 ht) (le_csSup ⟨log2 (Fintype.card V : ℝ), ?_⟩ ⟨t, hNt, ht, rfl⟩)
      rintro r ⟨t', -, ht', rfl⟩
      exact block_le_log2_card _ _ hε0 t' ht'
    · unfold log2
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (by norm_num) (by norm_num))
        (Real.log_pos one_lt_two).le
  refine le_trans hlim (le_csSup ⟨log2 (Fintype.card V : ℝ), ?_⟩ ⟨1 / 2, hε0, hε1, rfl⟩)
  rintro h ⟨ε, hε, -, rfl⟩
  exact limsup_le (block_le_log2_card _ _ hε)

end CoEntropy

/-- Instance of the `Statement` inequality: `H̄(\bar K_n ∪ G, P) ≤ H̄(\bar K_n, P) + H̄(G, P)`. -/
theorem coEntropy_subadditive_bot_left {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (P : ProbDist (Fin n)) :
    complementaryGraphEntropy (graphUnion (⊥ : SimpleGraph (Fin n)) G) P ≤
      complementaryGraphEntropy (⊥ : SimpleGraph (Fin n)) P + complementaryGraphEntropy G P := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [graphUnion_comm, graphUnion_bot, coEntropy_bot, zero_add]

/-- In the complementary case `F ∪ Fᶜ = K_n` with uniform `P`, the left side of `Statement` is
    exactly `log₂ n`. -/
theorem coEntropy_union_compl_uniform (n : ℕ) (hn : 0 < n) (F : SimpleGraph (Fin n)) :
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    complementaryGraphEntropy (graphUnion F Fᶜ) ProbDist.uniform = log2 n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [graphUnion_compl, coEntropy_top_uniform, Fintype.card_fin]

end InfoTheory.Known.Certificates.GraphEntropySubadditivity
