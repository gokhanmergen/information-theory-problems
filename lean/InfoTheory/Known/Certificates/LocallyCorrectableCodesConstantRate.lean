import InfoTheory.Problems.LocallyCorrectableCodesConstantRate

/-!
# Certificate for `InfoTheory.Problems.LocallyCorrectableCodesConstantRate`

The frozen statement asks for binary linear LCCs (`IsBinaryLCC n k q δ ε`) with constant rate
`k ≥ R n`, constant `δ, ε > 0` and `q ≤ C (log n)^c` queries, for infinitely many `n`.

## Certified (about exactly `IsBinaryLCC`)
* `card_good_ge`: the union-bound counting behind every 2-query self-corrector: if a bijection
  `σ` is used to pair query `r` with `σ r`, at least `N - 2|E|` seeds avoid an error set `E`.
* `hadamard_isBinaryLCC` (regression, the classical solved case): the Hadamard code
  `x ↦ (⟨x, a⟩)_{a ∈ 𝔽₂^k}` of length `2^k` and dimension `k` is a `2`-query
  `(1/8, 1/4)`-LCC for every `k` (corrector `y(b) + y(b + a)` with `b` uniform). So the predicate
  is satisfiable with constant `δ, ε` and constant query complexity at exponentially small
  rate — the Statement's difficulty lies entirely in combining constant rate with few queries.
* `isBinaryLCC_mono_queries`: more queries never hurt (`q ≤ q'`), so the `q`-bound in the
  Statement is an upper bound, as intended.

## Not certified
* Constant-rate LCCs with `q = n^{o(1)}` (Kopparty–Meir–Ron-Zewi–Saraf 2017), or any
  constant-rate construction; lower bounds for constant `q` (Katz–Trevisan; Kothari–Manohar
  2024 for `q = 3`).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.LocallyCorrectableCodesConstantRate

open InfoTheory InfoTheory.Problems.LocallyCorrectableCodesConstantRate

/-- Union bound: at least `N - 2|E|` seeds `r` have both `r ∉ E` and `σ r ∉ E`. -/
theorem card_good_ge {N : ℕ} (σ : Fin N ≃ Fin N) (E : Finset (Fin N)) (P : Fin N → Prop)
    [DecidablePred P] (hP : ∀ r, r ∉ E → σ r ∉ E → P r) :
    (N : ℝ) - 2 * E.card ≤ ((Finset.univ.filter P).card : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) P
  have hsub : Finset.univ.filter (fun r => ¬ P r) ⊆
      E ∪ Finset.univ.filter (fun r => σ r ∈ E) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_union, Finset.mem_filter]
    by_contra h
    rw [not_or, not_and] at h
    exact hr.2 (hP r h.1 (h.2 (Finset.mem_univ _)))
  have hσ : (Finset.univ.filter (fun r => σ r ∈ E)).card ≤ E.card := by
    refine Finset.card_le_card_of_injOn σ ?_ σ.injective.injOn
    intro r hr
    exact (Finset.mem_filter.1 hr).2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le E (Finset.univ.filter (fun r => σ r ∈ E))
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have : N ≤ (Finset.univ.filter P).card + 2 * E.card := by omega
  have : (N : ℝ) ≤ ((Finset.univ.filter P).card : ℝ) + 2 * (E.card : ℝ) := by exact_mod_cast this
  linarith

/-! ### The Hadamard code -/

/-- `𝔽₂`-inner product. -/
def ip {k : ℕ} (x a : Fin k → ZMod 2) : ZMod 2 := ∑ t, x t * a t

lemma ip_single {k : ℕ} (x : Fin k → ZMod 2) (t : Fin k) : ip x (Pi.single t 1) = x t := by
  simp [ip, Pi.single_apply]

lemma ip_shift {k : ℕ} (x u a : Fin k → ZMod 2) : ip x u + ip x (u + a) = ip x a := by
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  simp only [ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [← add_assoc, h2, zero_add]

/-- Indexing of the `2^k` coordinates by `𝔽₂^k`. -/
noncomputable def idx (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → ZMod 2) :=
  (Fintype.equivFinOfCardEq (by simp [ZMod.card])).symm

/-- The Hadamard encoder `x ↦ (⟨x, idx j⟩)_j`. -/
noncomputable def had (k : ℕ) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (2 ^ k) → ZMod 2) where
  toFun x j := ip x (idx k j)
  map_add' x y := by
    funext j
    simp [ip, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp [ip, Finset.mul_sum, mul_assoc]

lemma had_injective (k : ℕ) : Function.Injective (had k) := by
  intro x x' h
  funext t
  have := congrFun h ((idx k).symm (Pi.single t 1))
  simpa [had, ip_single] using this

/-- Pairing of seeds: `σ_a(r) = idx⁻¹(idx r + a)`. -/
noncomputable def shift (k : ℕ) (a : Fin k → ZMod 2) : Fin (2 ^ k) ≃ Fin (2 ^ k) :=
  (idx k).trans ((Equiv.addRight a).trans (idx k).symm)

lemma had_add_shift (k : ℕ) (x a : Fin k → ZMod 2) (r : Fin (2 ^ k)) :
    had k x r + had k x (shift k a r) = ip x a := by
  simp [had, shift, ip_shift]

/-- **Regression.** The Hadamard code is a `2`-query `(1/8, 1/4)`-LCC of length `2^k`,
    dimension `k`. -/
theorem hadamard_isBinaryLCC (k : ℕ) :
    IsBinaryLCC (2 ^ k) k 2 (1 / 8) (1 / 4) := by
  classical
  refine ⟨LinearMap.range (had k), ?_, 2 ^ k, by positivity,
    fun i r => ![r, shift k (idx k i) r], fun _ _ v => v 0 + v 1, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (had_injective k), Module.finrank_fin_fun]
  · rintro c ⟨x, rfl⟩ y hy i
    let E : Finset (Fin (2 ^ k)) := Finset.univ.filter (fun j => had k x j ≠ y j)
    have hE : (E.card : ℝ) ≤ 1 / 8 * ((2 ^ k : ℕ) : ℝ) := hy
    have hgood := card_good_ge (shift k (idx k i)) E
      (fun r => (fun v : Fin 2 → ZMod 2 => v 0 + v 1)
        (fun j => y (![r, shift k (idx k i) r] j)) = had k x i) (by
        intro r hr hσr
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr hσr
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hr, ← hσr, had_add_shift]
        rfl)
    have hN : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    rw [ge_iff_le, le_div_iff₀ hN]
    linarith

/-- More queries never hurt. -/
theorem isBinaryLCC_mono_queries {n k q q' : ℕ} {δ ε : ℝ} (hq : q ≤ q') (hq0 : 0 < q)
    (h : IsBinaryLCC n k q δ ε) : IsBinaryLCC n k q' δ ε := by
  obtain ⟨C, hC, R, hR, queries, eval, hcorr⟩ := h
  -- Pad with repeated copies of query `0`, and ignore the padding.
  let cut : Fin q' → Fin q := fun j => if h : j.1 < q then ⟨j.1, h⟩ else ⟨0, hq0⟩
  let ext : Fin q → Fin q' := fun j => ⟨j.1, lt_of_lt_of_le j.2 hq⟩
  refine ⟨C, hC, R, hR, fun i r j => queries i r (cut j),
    fun i r v => eval i r (fun j => v (ext j)), ?_⟩
  intro c hc y hy i
  have hce : ∀ j : Fin q, cut (ext j) = j := fun j => by
    simp [cut, ext, j.2]
  simpa only [hce] using hcorr c hc y hy i

end InfoTheory.Known.Certificates.LocallyCorrectableCodesConstantRate
