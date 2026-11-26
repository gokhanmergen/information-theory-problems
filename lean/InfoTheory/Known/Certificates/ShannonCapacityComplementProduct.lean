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

end InfoTheory.Known.Certificates.ShannonCapacityComplementProduct
