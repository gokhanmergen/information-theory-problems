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

end InfoTheory.Known.Certificates.ShannonCapacityUnionProduct
