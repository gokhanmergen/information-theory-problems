import InfoTheory.Problems.ListDecodingCapacityBinaryLinear
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ListDecodingCapacityBinaryLinear`

**Outcome: the `Statement` is faithful.** The predicate `ExistsBinaryLinearListDecodable` is
satisfiable, so the `Statement` is not vacuously true. It is not trivially false either: the
list size it uses is bounded.

Certified:
* `exists_listDecodable_two_pow`: for all `k ≤ n` and every `p`, some binary linear `[n, k]`
  code is `(p, 2^k)`-list-decodable. Without a bound on `L` the predicate is trivial. The
  `Statement` avoids this because it pins `L = ⌊c/ε⌋`, independent of `n`, while
  `k ≥ (1 - h(p) - ε) n → ∞`, so `L ≪ 2^k`.
* `exists_listDecodable_zero`: the zero code is `(p, 1)`-list-decodable for every `p`.
* `not_exists_of_lt`: the predicate is false for `k > n`, as it should be.

* **Regression** (trivial radii): `regression_radius_zero` — at radius `p = 0` the full space
  `F₂ⁿ` (rate `1`) is `(0, 1)`-list-decodable, the known value of list-decoding capacity
  `1 - h(0) = 1`; `regression_radius_one` — at radius `p = 1` (every ball is the whole space)
  no linear `[n, k]` code is `(1, L)`-list-decodable with `L < 2^k`, consistent with the
  list-decoding capacity being `0` for `p ≥ 1/2` (bounded list size forces `k = O(1)`).

Not certified:
* The random-linear-code list size `h(p)/ε + o(1/ε)` (Guruswami–Håstad–Kopparty, *On the
  list-decodability of random linear codes*, IEEE Trans. IT 57 (2011); Li–Wootters, *Improved
  list-decodability of random linear binary codes*, IEEE Trans. IT 67 (2021)). This needs a
  probabilistic argument.
* The list-decoding capacity converse (Elias 1957; Guruswami's thesis, Thm 5.3), which needs
  the binomial–entropy lower bound. Not formalized.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ListDecodingCapacityBinaryLinear

open InfoTheory InfoTheory.Known InfoTheory.Problems.ListDecodingCapacityBinaryLinear

/-- The `Bool → ZMod 2` identification used in `ExistsBinaryLinearListDecodable`. -/
def toZ {n : ℕ} (c : Fin n → Bool) : Fin n → ZMod 2 := fun i => if c i then 1 else 0

theorem toZ_injective {n : ℕ} : Function.Injective (toZ (n := n)) := by
  intro c c' h
  funext i
  have := congrFun h i
  simp only [toZ] at this
  cases hc : c i <;> cases hc' : c' i <;> simp_all

/-- Extension by zero `F_2^k → F_2^n` (`k ≤ n`): its range is the `k`-dimensional code of words
supported on the first `k` coordinates. -/
noncomputable def extendZero (k n : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x i := if h : i.val < k then x ⟨i.val, h⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by ext i; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem extendZero_castLE {k n : ℕ} (hk : k ≤ n) (x : Fin k → ZMod 2) (j : Fin k) :
    extendZero k n x (Fin.castLE hk j) = x j := by
  simp [extendZero]

theorem extendZero_injective {k n : ℕ} (hk : k ≤ n) : Function.Injective (extendZero k n) := by
  intro x y h
  funext j
  rw [← extendZero_castLE hk x j, ← extendZero_castLE hk y j, h]

/-- **Sanity check (the list size must be bounded).** For every `k ≤ n` and every radius `p`,
there is a binary linear `[n, k]` code that is `(p, 2^k)`-list-decodable: the list size
`L = 2^k = |C|` is trivially achievable. Hence the predicate is satisfiable and the `Statement`
is non-trivial only because it pins `L = ⌊c/ε⌋`, a constant independent of `n`, while
`k ≥ (1 - h(p) - ε) n` grows. -/
theorem exists_listDecodable_two_pow (n k : ℕ) (hk : k ≤ n) (p : ℝ) :
    ExistsBinaryLinearListDecodable n k p (2 ^ k) := by
  classical
  set V := LinearMap.range (extendZero k n)
  set C : Finset (Fin n → Bool) := Finset.univ.filter (fun c => toZ c ∈ V)
  refine ⟨V, C, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (extendZero_injective hk), Module.finrank_fin_fun]
  · intro c
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · intro y
    refine (Finset.card_filter_le _ _).trans ?_
    have hinj : Set.InjOn (fun (c : Fin n → Bool) (j : Fin k) => c (Fin.castLE hk j))
        (C : Set (Fin n → Bool)) := by
      intro c hc c' hc' h
      simp only [C, Finset.coe_filter, Finset.mem_univ, true_and] at hc hc'
      obtain ⟨x, hx⟩ := hc
      obtain ⟨x', hx'⟩ := hc'
      apply toZ_injective
      rw [← hx, ← hx']
      congr 1
      funext j
      rw [← extendZero_castLE hk x j, ← extendZero_castLE hk x' j, hx, hx']
      have hj : c (Fin.castLE hk j) = c' (Fin.castLE hk j) := congrFun h j
      simp only [toZ, hj]
    have := Finset.card_le_card_of_injOn _ (t := (Finset.univ : Finset (Fin k → Bool)))
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    simpa using this

/-- The zero code is `(p, 1)`-list-decodable for every `p`: `k = 0` is always admissible. -/
theorem exists_listDecodable_zero (n : ℕ) (p : ℝ) : ExistsBinaryLinearListDecodable n 0 p 1 := by
  simpa using exists_listDecodable_two_pow n 0 (Nat.zero_le n) p

/-- No linear code has dimension above the blocklength: the predicate fails for `k > n`. -/
theorem not_exists_of_lt {n k : ℕ} (h : n < k) (p : ℝ) (L : ℕ) :
    ¬ ExistsBinaryLinearListDecodable n k p L := by
  rintro ⟨V, -, hV, -, -⟩
  have := Submodule.finrank_le V
  simp only [Module.finrank_fin_fun] at this
  omega

/-! ### Regression: trivial radii -/

/-- **Regression** (radius `0`, rate `1`): the whole space is a linear `[n, n]` code that is
`(0, 1)`-list-decodable (every radius-0 ball is a single word). -/
theorem regression_radius_zero (n : ℕ) : ExistsBinaryLinearListDecodable n n 0 1 := by
  refine ⟨⊤, Finset.univ, ?_, ?_, ?_⟩
  · rw [finrank_top, Module.finrank_fin_fun]
  · intro c; simp
  · intro y
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_mul] at ha hb
    have ha' : a = y := by
      by_contra h
      have := hammingDistVec_pos.mpr h
      have : (0 : ℝ) < hammingDistVec a y := by exact_mod_cast this
      linarith
    have hb' : b = y := by
      by_contra h
      have := hammingDistVec_pos.mpr h
      have : (0 : ℝ) < hammingDistVec b y := by exact_mod_cast this
      linarith
    rw [ha', hb']

/-- Inverse of `toZ`. -/
def fromZ {n : ℕ} (v : Fin n → ZMod 2) : Fin n → Bool := fun i => decide (v i = 1)

theorem toZ_fromZ {n : ℕ} (v : Fin n → ZMod 2) : toZ (fromZ v) = v := by
  funext i
  have key : ∀ x : ZMod 2, (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by decide
  exact key (v i)

/-- **Regression** (radius `1`): every Hamming ball of radius `n` is the whole space, so a
linear `[n, k]` code is `(1, L)`-list-decodable only if `2^k ≤ L`. -/
theorem regression_radius_one {n k L : ℕ} (hL : L < 2 ^ k) :
    ¬ ExistsBinaryLinearListDecodable n k 1 L := by
  classical
  rintro ⟨V, C, hV, hC, hdec⟩
  have hball := hdec (fun _ => false)
  have hfilt : C.filter (fun c => (hammingDistVec c (fun _ => false) : ℝ) ≤ 1 * (n : ℝ)) = C := by
    refine Finset.filter_true_of_mem fun c _ => ?_
    rw [one_mul]; exact_mod_cast hammingDistVec_le_length _ _
  rw [hfilt] at hball
  have hcardV : (Finset.univ.filter (fun v : Fin n → ZMod 2 => v ∈ V)).card = 2 ^ k := by
    rw [← Fintype.card_subtype]
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [ZMod.card, hV] at this
    rw [← this]
  have hle : (Finset.univ.filter (fun v : Fin n → ZMod 2 => v ∈ V)).card ≤ C.card := by
    refine Finset.card_le_card_of_injOn fromZ (fun v hv => ?_) (fun v _ w _ h => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
      exact (hC _).mpr (by rw [show (fun i => if fromZ v i then (1 : ZMod 2) else 0) = toZ (fromZ v)
        from rfl, toZ_fromZ]; exact hv)
    · rw [← toZ_fromZ v, ← toZ_fromZ w, h]
  omega

end InfoTheory.Known.Certificates.ListDecodingCapacityBinaryLinear
