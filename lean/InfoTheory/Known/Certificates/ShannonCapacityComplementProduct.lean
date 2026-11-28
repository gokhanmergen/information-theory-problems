import InfoTheory.Problems.ShannonCapacityComplementProduct
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ShannonCapacityComplementProduct`

The frozen statement asks for a constant `c > 0` such that for all large `n` some graph `G` on
`Fin n` has `Θ(G) · Θ(Ḡ) ≤ (log₂ n)^c`, where `Ḡ = graphCompl G`. The docstring recalls
`Θ(G ⊠ Ḡ) ≥ n` and `ϑ(G) ϑ(Ḡ) ≥ n` (Lovász 1979) and Alon's construction with
`Θ(G) Θ(Ḡ) ≤ 2^{O(√(log n log log n))}` (Alon, *The Shannon capacity of a union*,
Combinatorica 18 (1998)).

Note: `Θ(G) · Θ(Ḡ) ≥ n` is *false* in general (that is exactly Alon's theorem); the valid
diagonal bound is for the capacity of the strong product `G ⊠ Ḡ`, certified below.

Certified here (for the `graphCompl` and `shannonCapacity` of the problem file):
* `isIndepSet_diag` / `card_le_indepNumber_strongProd_compl` — the diagonal `{(v, v)}` is
  independent in `G ⊠ Ḡ`, so `α(G ⊠ Ḡ) ≥ n`;
* `card_le_shannonCapacity_strongProd_compl` — `n ≤ Θ(G ⊠ Ḡ)` (docstring claim);
* `one_le_shannonCapacity_mul_compl` — `1 ≤ Θ(G) Θ(Ḡ)` on a nonempty vertex set;
* `max_indepNumber_le_shannonCapacity_mul_compl` — `max(α(G), α(Ḡ)) ≤ Θ(G) Θ(Ḡ)`;
* `shannonCapacity_mul_compl_le` — `Θ(G) Θ(Ḡ) ≤ n²` (the product is not a junk value).

* **Regression** (solved perfect-graph case): `regression_compl_top` — `Θ(K̄_n) = n`
  (edgeless graph) for the problem's own `graphCompl`; `regression_complete_mul_compl` —
  `Θ(K_n) · Θ(K̄_n) = n`, the exact known value (both graphs perfect, `Θ = α`), which meets
  the lower bound `Θ(G ⊠ Ḡ) ≥ n` with equality.

Not certified: `ϑ(G) ϑ(Ḡ) ≥ n` (needs the dual characterisation of `ϑ`), Alon's upper
construction, and the Ramsey consequence `Θ(G) Θ(Ḡ) ≥ max(α(G), α(Ḡ)) ≥ ½ log₂ n` (Erdős–Szekeres;
would show `c ≥ 1` is necessary). The `Statement` is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ShannonCapacityComplementProduct

open InfoTheory InfoTheory.Known InfoTheory.Problems.ShannonCapacityComplementProduct

variable {V : Type*} [Fintype V]

/-- The diagonal is independent in `G ⊠ Ḡ`. -/
theorem isIndepSet_diag [DecidableEq V] (G : SimpleGraph V) :
    IsIndepSet (strongProd G (graphCompl G)) (Finset.univ.image fun v => (v, v)) := by
  intro p hp q hq hpq
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨v, rfl⟩ := hq
  obtain ⟨hne, h1, h2⟩ := hpq
  have huv : u ≠ v := fun h => hne (by rw [h])
  rcases h1 with h1 | h1
  · exact huv h1
  rcases h2 with h2 | h2
  · exact huv h2
  · exact h2.2 h1

/-- `n ≤ α(G ⊠ Ḡ)`. -/
theorem card_le_indepNumber_strongProd_compl (G : SimpleGraph V) :
    Fintype.card V ≤ indepNumber (strongProd G (graphCompl G)) := by
  classical
  refine le_indepNumber_iff.2 ⟨_, isIndepSet_diag G, ?_⟩
  rw [Finset.card_image_of_injective _ (fun u v h => congrArg Prod.fst h), Finset.card_univ]

/-- `n ≤ Θ(G ⊠ Ḡ)` (Lovász 1979). -/
theorem card_le_shannonCapacity_strongProd_compl (G : SimpleGraph V) :
    (Fintype.card V : ℝ) ≤ shannonCapacity (strongProd G (graphCompl G)) :=
  le_trans (by exact_mod_cast card_le_indepNumber_strongProd_compl G) (le_shannonCapacity _)

/-- `1 ≤ Θ(G) Θ(Ḡ)` on a nonempty vertex set. -/
theorem one_le_shannonCapacity_mul_compl [Nonempty V] (G : SimpleGraph V) :
    1 ≤ shannonCapacity G * shannonCapacity (graphCompl G) := by
  have h1 := one_le_shannonCapacity G
  have h2 := one_le_shannonCapacity (graphCompl G)
  nlinarith

/-- `max(α(G), α(Ḡ)) ≤ Θ(G) Θ(Ḡ)` on a nonempty vertex set. -/
theorem max_indepNumber_le_shannonCapacity_mul_compl [Nonempty V] (G : SimpleGraph V) :
    max (indepNumber G : ℝ) (indepNumber (graphCompl G)) ≤
      shannonCapacity G * shannonCapacity (graphCompl G) := by
  have a1 := le_shannonCapacity G
  have a2 := le_shannonCapacity (graphCompl G)
  have h1 := one_le_shannonCapacity G
  have h2 := one_le_shannonCapacity (graphCompl G)
  refine max_le ?_ ?_ <;> nlinarith [Nat.cast_nonneg (α := ℝ) (indepNumber G),
    Nat.cast_nonneg (α := ℝ) (indepNumber (graphCompl G))]

/-- `Θ(G) Θ(Ḡ) ≤ n²`. -/
theorem shannonCapacity_mul_compl_le (G : SimpleGraph V) :
    shannonCapacity G * shannonCapacity (graphCompl G) ≤ (Fintype.card V : ℝ) ^ 2 := by
  rw [sq]
  exact mul_le_mul (shannonCapacity_le_card G) (shannonCapacity_le_card _)
    (shannonCapacity_nonneg _) (Nat.cast_nonneg _)

/-! ### Regression: complete graph and its complement -/

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

/-- **Regression**: the complement of `K_n` (edgeless) has `Θ = n`. -/
theorem regression_compl_top (n : ℕ) :
    shannonCapacity (graphCompl (⊤ : SimpleGraph (Fin n))) = n := by
  classical
  refine le_antisymm (by simpa using shannonCapacity_le_card (graphCompl (⊤ : SimpleGraph (Fin n))))
    ?_
  have hind : IsIndepSet (graphCompl (⊤ : SimpleGraph (Fin n))) Finset.univ := by
    intro u _ v _ h
    exact h.2 ((SimpleGraph.top_adj u v).2 h.1)
  have := card_le_indepNumber hind
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact le_trans (by exact_mod_cast this) (le_shannonCapacity _)

/-- **Regression**: `Θ(K_n) · Θ(K̄_n) = n` (perfect graphs). -/
theorem regression_complete_mul_compl (n : ℕ) [NeZero n] :
    shannonCapacity (⊤ : SimpleGraph (Fin n)) *
      shannonCapacity (graphCompl (⊤ : SimpleGraph (Fin n))) = n := by
  rw [shannonCapacity_top, regression_compl_top, one_mul]

end InfoTheory.Known.Certificates.ShannonCapacityComplementProduct
