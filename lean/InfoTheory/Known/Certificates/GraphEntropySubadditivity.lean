import InfoTheory.Problems.GraphEntropySubadditivity
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.GraphEntropySubadditivity`

The frozen statement asks whether Witsenhausen's zero-error rate
`R₀(G) = inf_k (1/k) log₂ χ(G^{⊠k})` (`witsenhausenRate`) is subadditive under edge union:
`R₀(F ∪ G) ≤ R₀(F) + R₀(G)`.

## Certified (about exactly these objects)
* `rate_nonneg`, `rate_le_log2_of_coloring`, `rate_le_log2_card`, `log2_clique_le_rate`,
  `rate_top`, `rate_bot` — Witsenhausen's (1976) basic bounds `log₂ ω(G) ≤ R₀(G) ≤ log₂ χ(G)`
  and the exact values `R₀(K_n) = log₂ n`, `R₀(\bar K_n) = 0` (same proofs as in the
  `ZeroErrorSourceCodingSideInfo` certificate, restated here for these objects).
* `graphUnion_comm`, `graphUnion_bot`, `graphUnion_self`, `graphUnion_compl` — `graphUnion`
  is the genuine edge union (`F ∪ Fᶜ = K_n`).
* `rate_union_le_log2_mul` — **one-shot product-colouring bound**
  `R₀(F ∪ G) ≤ log₂ a + log₂ b` for any proper `a`-colouring of `F` and `b`-colouring of `G`
  (hence `R₀(F ∪ G) ≤ log₂ χ(F) + log₂ χ(G)`).
* `subadditive_of_rate_eq_log2_coloring` — **regression**: whenever `R₀(F) = log₂ χ(F)` and
  `R₀(G) = log₂ χ(G)` (e.g. perfect graphs, where `R₀ = log₂ ω = log₂ χ`), the inequality of
  `Statement` holds for `(F, G)`; `subadditive_top_top`, `subadditive_bot_left` are concrete
  instances.

## Not certified
* The complementary case `R₀(F) + R₀(\bar F) ≥ log₂ n` (needs the Lovász-theta sandwich for
  co-normal powers); the value `R₀(C₅) = log₂ √5`.
* Provenance: we could not locate the exact sentence posing union-subadditivity of the
  Witsenhausen rate in Körner–Marton (1988) or Simonyi (1995); see the problem file.
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

end InfoTheory.Known.Certificates.GraphEntropySubadditivity
