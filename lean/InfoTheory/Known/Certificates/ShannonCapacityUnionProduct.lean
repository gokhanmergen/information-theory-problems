import InfoTheory.Problems.ShannonCapacityUnionProduct
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ShannonCapacityUnionProduct`

The frozen statement asks whether `Θ(G + H)` is uniformly bounded over all pairs of graphs
with `Θ(G), Θ(H) ≤ C`, where `G + H = disjointUnionGraph G H`. The docstring recalls Shannon's
`Θ(G + H) ≥ Θ(G) + Θ(H)` and Alon's counterexample to equality (Alon, *The Shannon capacity of
a union*, Combinatorica 18 (1998) 301–310).

Certified here, about the exact objects in `Statement`:
* `indepNumber_add_le` — `α(G) + α(H) ≤ α(G + H)` (union of independent sets);
* `add_indepNumber_le_shannonCapacity` — `α(G) + α(H) ≤ Θ(G + H)`;
* `shannonCapacity_le_union_left/right` — `Θ(G) ≤ Θ(G + H)` and `Θ(H) ≤ Θ(G + H)`
  (`G^{⊠k}` embeds in `(G + H)^{⊠k}`), hence `max(Θ(G), Θ(H)) ≤ Θ(G + H)`;
* `shannonCapacity_union_le_card` — `Θ(G + H) ≤ |V(G)| + |V(H)|` (the `sSup` is not junk).

* **Regression** (solved perfect-graph case of the problem's `disjointUnionGraph`):
  `regression_union_complete` — `Θ(K_m + K_n) = 2 = Θ(K_m) + Θ(K_n)` (additivity holds for
  perfect graphs; upper bound by the clique cover with the two parts).

Not certified: Shannon's superadditivity `Θ(G + H) ≥ Θ(G) + Θ(H)` (Shannon 1956, Theorem 4),
whose proof needs the binomial expansion `α((G+H)^{⊠k}) ≥ ∑ C(k,j) α(G^{⊠j}) α(H^{⊠(k-j)})`
plus a limiting argument; and Alon's lower-bound constructions. The `Statement` is not
settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ShannonCapacityUnionProduct

open InfoTheory InfoTheory.Known

variable {V W : Type*} [Fintype V] [Fintype W]

/-- `α(G) + α(H) ≤ α(G + H)`. -/
theorem indepNumber_add_le (G : SimpleGraph V) (H : SimpleGraph W) :
    indepNumber G + indepNumber H ≤ indepNumber (disjointUnionGraph G H) := by
  obtain ⟨S, hS, hSc⟩ := exists_indepSet_card_eq_indepNumber G
  obtain ⟨T, hT, hTc⟩ := exists_indepSet_card_eq_indepNumber H
  refine le_indepNumber_iff.2 ⟨S.disjSum T, ?_, by rw [Finset.card_disjSum, hSc, hTc]⟩
  rintro (u | u) hu (v | v) hv
  · simp only [Finset.inl_mem_disjSum] at hu hv
    exact hS u hu v hv
  · exact id
  · exact id
  · simp only [Finset.inr_mem_disjSum] at hu hv
    exact hT u hu v hv

/-- `α(G) + α(H) ≤ Θ(G + H)`. -/
theorem add_indepNumber_le_shannonCapacity (G : SimpleGraph V) (H : SimpleGraph W) :
    (indepNumber G : ℝ) + indepNumber H ≤ shannonCapacity (disjointUnionGraph G H) := by
  refine le_trans ?_ (le_shannonCapacity _)
  exact_mod_cast indepNumber_add_le G H

/-- Transfer along a coordinatewise embedding that reflects adjacency. -/
private theorem shannonCapacity_le_of_embedding {G : SimpleGraph V} {K : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f) (hadj : ∀ a b, K.Adj (f a) (f b) → a = b ∨ G.Adj a b) :
    shannonCapacity G ≤ shannonCapacity K := by
  refine (shannonCapacity_le_iff G).2 fun k hk => ?_
  refine le_trans ?_ (indepNumber_strongPower_rpow_le_shannonCapacity K hk)
  refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by positivity)
  refine Nat.cast_le.2 (indepNumber_le_of_injective (fun x i => f (x i)) ?_ ?_)
  · intro x y hxy
    funext i
    exact hf (congrFun hxy i)
  · rintro x y ⟨hne, h⟩
    refine ⟨fun hxy => hne (by rw [hxy]), fun i => ?_⟩
    rcases h i with h | h
    · exact Or.inl (hf h)
    · exact hadj _ _ h

/-- `Θ(G) ≤ Θ(G + H)`. -/
theorem shannonCapacity_le_union_left (G : SimpleGraph V) (H : SimpleGraph W) :
    shannonCapacity G ≤ shannonCapacity (disjointUnionGraph G H) :=
  shannonCapacity_le_of_embedding Sum.inl Sum.inl_injective fun _ _ h => Or.inr h

/-- `Θ(H) ≤ Θ(G + H)`. -/
theorem shannonCapacity_le_union_right (G : SimpleGraph V) (H : SimpleGraph W) :
    shannonCapacity H ≤ shannonCapacity (disjointUnionGraph G H) :=
  shannonCapacity_le_of_embedding Sum.inr Sum.inr_injective fun _ _ h => Or.inr h

/-- `max(Θ(G), Θ(H)) ≤ Θ(G + H)`. -/
theorem max_le_shannonCapacity_union (G : SimpleGraph V) (H : SimpleGraph W) :
    max (shannonCapacity G) (shannonCapacity H) ≤ shannonCapacity (disjointUnionGraph G H) :=
  max_le (shannonCapacity_le_union_left G H) (shannonCapacity_le_union_right G H)

/-- `Θ(G + H) ≤ |V(G)| + |V(H)|`. -/
theorem shannonCapacity_union_le_card (G : SimpleGraph V) (H : SimpleGraph W) :
    shannonCapacity (disjointUnionGraph G H) ≤ Fintype.card V + Fintype.card W := by
  have := shannonCapacity_le_card (disjointUnionGraph G H)
  simpa [Fintype.card_sum] using this

/-! ### Regression: union of two complete graphs -/

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

/-- **Regression**: `Θ(K_m + K_n) = 2 = Θ(K_m) + Θ(K_n)` for `m, n ≥ 1`. -/
theorem regression_union_complete (m n : ℕ) [NeZero m] [NeZero n] :
    shannonCapacity (disjointUnionGraph (⊤ : SimpleGraph (Fin m)) (⊤ : SimpleGraph (Fin n))) = 2 ∧
      shannonCapacity (⊤ : SimpleGraph (Fin m)) + shannonCapacity (⊤ : SimpleGraph (Fin n)) = 2 := by
  refine ⟨le_antisymm ?_ ?_, by rw [shannonCapacity_top, shannonCapacity_top]; norm_num⟩
  · have := shannonCapacity_le_of_cover
      (G := disjointUnionGraph (⊤ : SimpleGraph (Fin m)) (⊤ : SimpleGraph (Fin n)))
      (fun p : Fin m ⊕ Fin n => p.isLeft) (by
        rintro (u | u) (v | v) h
        · by_cases huv : u = v
          · exact Or.inl (by rw [huv])
          · exact Or.inr ((SimpleGraph.top_adj u v).2 huv)
        · simp at h
        · simp at h
        · by_cases huv : u = v
          · exact Or.inl (by rw [huv])
          · exact Or.inr ((SimpleGraph.top_adj u v).2 huv))
    simpa using this
  · have h := add_indepNumber_le_shannonCapacity (⊤ : SimpleGraph (Fin m)) (⊤ : SimpleGraph (Fin n))
    have h1 : (1 : ℝ) ≤ indepNumber (⊤ : SimpleGraph (Fin m)) := by
      exact_mod_cast one_le_indepNumber _
    have h2 : (1 : ℝ) ≤ indepNumber (⊤ : SimpleGraph (Fin n)) := by
      exact_mod_cast one_le_indepNumber _
    linarith

end InfoTheory.Known.Certificates.ShannonCapacityUnionProduct
