import InfoTheory.Problems.MdsConjecture
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.MdsConjecture`

**Outcome: the `Statement` is faithful and non-vacuous.** Its hypotheses are satisfiable
exactly when `q ≥ 3`. The bound `n ≤ q + 1` it asserts is attained, and its two smallest cases
(`k = 2`, and `k = 3` with `q` even) are theorems.

Degenerate cases checked. `IsLinearMDSCode F n k` asks for a `k`-dimensional subspace of `F^n`
in which every nonzero word has weight `≥ n - k + 1`. Since `finrank ≤ n`, this forces `k ≤ n`,
so the truncated subtraction `n - k` is harmless. In the `Statement`, `q - 1` is truncated
subtraction. For `q = 2`, the hypothesis `2 ≤ k ≤ q - 1 = 1` is unsatisfiable
(`no_k_of_card_two`); this matches the literature, where the conjecture is stated for
`2 ≤ k ≤ q - 1`. For `q ≥ 3`, `q - 1` is the true value. The trivial MDS families (`k = 1`
repetition codes and `k = n - 1` parity codes, which exist for every `n`) are excluded or
satisfy the bound. So no degenerate case settles the `Statement`.

Certified:
* `eq_zero_of_vanish`, `restrict_surjective`: every `k` coordinates of an MDS code form an
  information set (MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 11 Thm 2).
* `bush_bound`: the Bush bound `n ≤ q + k - 1` for MDS codes with `k ≥ 2` (Bush 1952;
  MacWilliams–Sloane Ch. 11 §5). This is the classical unconditional upper bound.
* `dersEval`, `ders_isLinearMDSCode`: doubly extended Reed–Solomon codes `[q+1, k, q-k+2]_q`
  for `1 ≤ k ≤ q + 1` (MacWilliams–Sloane Ch. 11 §5; Roth, *Introduction to Coding Theory*,
  §5.2). (`Known.reedSolomon_isLinearMDSCode` gives only length `n ≤ q`.)
* `statement_hyp_attained`: for every `k` with `2 ≤ k ≤ q - 1` there is an MDS code of length
  `q + 1`. So the `Statement`'s non-exceptional bound is sharp, and its hypotheses are
  satisfiable.
* `statement_of_k_two_or_three_even`: the `Statement`'s conclusion holds for `k = 2`, and for
  `k = 3` with `q` even. Both follow from the Bush bound.

Not certified:
* Segre's theorem (`k = 3`, `q` odd: ovals are conics) and Ball's theorem (the conjecture for
  `q = p` prime, J. Eur. Math. Soc. 14 (2012)). Both need finite-geometry or polynomial-method
  machinery.
* Attainment of the exceptional bound `q + 2` for `q` even and `k ∈ {3, q-1}` (hyperovals,
  e.g. the regular hyperoval). Not attempted.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.MdsConjecture

open InfoTheory InfoTheory.Known

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- In an `[n, k, n-k+1]` code, a codeword vanishing on the image of an injective
`e : Fin k → Fin n` (i.e. on `k` coordinates) is zero. -/
theorem eq_zero_of_vanish {n k : ℕ} {V : Submodule F (Fin n → F)}
    (hV : ∀ v ∈ V, v ≠ 0 → n - k + 1 ≤ (Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card)
    {v : Fin n → F} (hv : v ∈ V) (e : Fin k → Fin n) (he : Function.Injective e)
    (hz : ∀ i, v (e i) = 0) : v = 0 := by
  by_contra hne
  have h1 := hV v hv hne
  set Z := Finset.univ.map ⟨e, he⟩
  have hZ : Z.card = k := by simp [Z]
  have h2 : (Finset.univ.filter (fun i : Fin n => v i ≠ 0)) ⊆ Zᶜ := by
    intro i hi
    rw [Finset.mem_compl]
    intro hiZ
    simp only [Z, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hiZ
    obtain ⟨j, rfl⟩ := hiZ
    exact (Finset.mem_filter.mp hi).2 (hz j)
  have h3 := Finset.card_le_card h2
  rw [Finset.card_compl, Fintype.card_fin] at h3
  have : Z.card ≤ n := by simpa using Z.card_le_univ
  omega

omit [Fintype F] in
/-- In an `[n, k, n-k+1]` code, every `k` coordinates form an information set: restriction to
them is onto `F^k` (MacWilliams–Sloane, Ch. 11 Thm 2). -/
theorem restrict_surjective {n k : ℕ} {V : Submodule F (Fin n → F)}
    (hk : Module.finrank F V = k)
    (hV : ∀ v ∈ V, v ≠ 0 → n - k + 1 ≤ (Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card)
    (e : Fin k → Fin n) (he : Function.Injective e) (t : Fin k → F) :
    ∃ v ∈ V, ∀ i, v (e i) = t i := by
  let L : V →ₗ[F] (Fin k → F) := (LinearMap.funLeft F F e).comp V.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (eq_zero_of_vanish hV w.2 e he fun j => congrFun hw j)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hk])).mp hinj
  obtain ⟨w, hw⟩ := hsurj t
  exact ⟨w, w.2, fun i => congrFun hw i⟩

/-- **Bush bound** (Bush 1952; MacWilliams–Sloane Ch. 11 §5, Cor. to Thm 6): a linear
`[n, k, n-k+1]_q` MDS code with `k ≥ 2` has `n ≤ q + k - 1`. -/
theorem bush_bound {n k : ℕ} (hk : 2 ≤ k) (h : IsLinearMDSCode F n k) :
    n ≤ Fintype.card F + k - 1 := by
  obtain ⟨V, hdim, hV⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hkn : m + 2 ≤ n := by
    have := Submodule.finrank_le V
    simp only [Module.finrank_fin_fun] at this
    omega
  let J : Finset (Fin n) := Finset.univ.filter (fun j => m + 1 ≤ j.val)
  have hJ : J.card = n - (m + 1) := card_filter_le_val n (m + 1)
  let e : Fin n → Fin (m + 2) → Fin n := fun j i =>
    if h : i.val < m + 1 then ⟨i.val, by omega⟩ else j
  have he : ∀ j ∈ J, Function.Injective (e j) := by
    intro j hj x y hxy
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [e] at hxy
    apply Fin.ext
    split_ifs at hxy with h1 h2 h2
    · simpa using congrArg Fin.val hxy
    · have := congrArg Fin.val hxy; simp at this; omega
    · have := congrArg Fin.val hxy; simp at this; omega
    · omega
  have heq : ∀ j j' : Fin n, ∀ i : Fin (m + 2), i.val < m + 1 → e j i = e j' i := by
    intro j j' i hi; simp only [e, hi, ↓reduceDIte]
  let t : Fin (m + 2) → F := fun i => if i.val = m then 1 else 0
  have hf : ∀ j ∈ J, ∃ v ∈ V, ∀ i, v (e j i) = t i :=
    fun j hj => restrict_surjective hdim hV (e j) (he j hj) t
  choose! f hfV hft using hf
  have hfj : ∀ j ∈ J, f j j = 0 := by
    intro j hj
    have := hft j hj (Fin.last (m + 1))
    simpa [e, t] using this
  have hfT : ∀ j ∈ J, ∀ i : Fin n, i.val < m → f j i = 0 := by
    intro j hj i hi
    have := hft j hj ⟨i.val, by omega⟩
    have h1 : e j ⟨i.val, by omega⟩ = i := by
      simp only [e]; split_ifs with h
      · rfl
      · simp at h; omega
    rw [h1] at this
    rw [this]; simp [t]; omega
  have hfa : ∀ j ∈ J, f j ⟨m, by omega⟩ = 1 := by
    intro j hj
    have := hft j hj ⟨m, by omega⟩
    simpa [e, t] using this
  let j0 : Fin n := ⟨m + 1, by omega⟩
  have hg : Set.InjOn (fun j => f j j0) (J : Set (Fin n)) := by
    intro j hj j' hj' hjj
    simp only at hjj
    have hw : f j - f j' = 0 := by
      refine eq_zero_of_vanish hV (V.sub_mem (hfV j hj) (hfV j' hj')) (e j0) (he j0 (by
        simp [J, j0])) fun i => ?_
      simp only [Pi.sub_apply, sub_eq_zero]
      by_cases hi : i.val < m + 1
      · have h1 := hft j hj i
        have h2 := hft j' hj' i
        rw [heq j j0 i hi] at h1
        rw [heq j' j0 i hi] at h2
        rw [h1, h2]
      · have : e j0 i = j0 := by simp only [e, hi, ↓reduceDIte]
        rw [this]; exact hjj
    have hff : f j = f j' := sub_eq_zero.mp hw
    by_contra hne
    have hjJ : m + 1 ≤ j.val := by simpa [J] using hj
    have hj'J : m + 1 ≤ j'.val := by simpa [J] using hj'
    let e' : Fin (m + 2) → Fin n := fun i =>
      if h : i.val < m then ⟨i.val, by omega⟩ else if i.val = m then j else j'
    have he' : Function.Injective e' := by
      intro x y hxy
      simp only [e'] at hxy
      apply Fin.ext
      have hne' : j.val ≠ j'.val := fun h => hne (Fin.ext h)
      split_ifs at hxy <;> simp only [Fin.ext_iff] at hxy <;> omega
    have h0 : f j = 0 := by
      refine eq_zero_of_vanish hV (hfV j hj) e' he' fun i => ?_
      simp only [e']
      split_ifs with h1 h2
      · exact hfT j hj _ h1
      · exact hfj j hj
      · rw [hff]; exact hfj j' hj'
    have := hfa j hj
    rw [h0] at this
    exact zero_ne_one this
  have := Finset.card_le_card_of_injOn (fun j => f j j0) (s := J) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hg
  rw [Finset.card_univ] at this
  omega


/-! ### Doubly extended Reed–Solomon codes -/

omit [Fintype F] in
/-- A nonzero polynomial vanishes at no more than `natDegree` of the distinct points `σ i`. -/
theorem card_eval_zero_le {p : Polynomial F} (hp : p ≠ 0) {q : ℕ} (σ : Fin q ↪ F) :
    (Finset.univ.filter (fun i : Fin q => p.eval (σ i) = 0)).card ≤ p.natDegree := by
  rw [← Finset.card_map σ]
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  simp only [Finset.map_val, Multiset.mem_map, Finset.mem_val, Finset.mem_filter,
    Finset.mem_univ, true_and] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact (Polynomial.mem_roots hp).mpr hi

/-- Doubly extended Reed–Solomon encoder: a polynomial of degree `< k` is evaluated at all `q`
field elements, plus the "point at infinity" `p ↦ coeff p (k-1)`. -/
noncomputable def dersEval (F : Type) [Field F] [Fintype F] (k : ℕ) :
    Polynomial.degreeLT F k →ₗ[F] (Fin (Fintype.card F + 1) → F) where
  toFun p i := if h : i.val < Fintype.card F then
      p.1.eval ((Fintype.equivFin F).symm ⟨i.val, h⟩) else p.1.coeff (k - 1)
  map_add' p p' := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c p := by ext i; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

omit [DecidableEq F] in
theorem dersEval_castSucc (k : ℕ) (p : Polynomial.degreeLT F k) (i : Fin (Fintype.card F)) :
    dersEval F k p (Fin.castSucc i) = p.1.eval ((Fintype.equivFin F).symm i) := by
  simp [dersEval]

omit [DecidableEq F] in
theorem dersEval_last (k : ℕ) (p : Polynomial.degreeLT F k) :
    dersEval F k p (Fin.last _) = p.1.coeff (k - 1) := by
  simp [dersEval]

/-- A nonzero codeword of the doubly extended RS code has at most `k - 1` zero coordinates. -/
theorem dersEval_zeros_le {k : ℕ} (hk : 1 ≤ k) (p : Polynomial.degreeLT F k) (hp : p.1 ≠ 0) :
    (Finset.univ.filter (fun i => dersEval F k p i = 0)).card ≤ k - 1 := by
  have hroot := card_eval_zero_le hp (Fintype.equivFin F).symm.toEmbedding
  have hdeg : p.1.natDegree < k := by
    have := p.2
    rw [Polynomial.mem_degreeLT] at this
    exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr this
  rw [Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [dersEval_castSucc, dersEval_last]
  rw [← Finset.card_filter]
  simp only [Equiv.coe_toEmbedding] at hroot
  split_ifs with hc
  · have hne : p.1.natDegree ≠ k - 1 := by
      intro h
      apply hp
      rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, h, hc]
    omega
  · omega

/-- **Doubly extended Reed–Solomon codes are MDS** (MacWilliams–Sloane, Ch. 11 §5, Thm 9;
Roth, *Introduction to Coding Theory*, §5.2): for `1 ≤ k ≤ q + 1` there is a linear
`[q+1, k, q-k+2]_q` code. -/
theorem ders_isLinearMDSCode {k : ℕ} (hk1 : 1 ≤ k) (hkq : k ≤ Fintype.card F + 1) :
    IsLinearMDSCode F (Fintype.card F + 1) k := by
  set L := dersEval F k
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    by_contra hne
    have hp0 : p.1 ≠ 0 := fun h => hne (Subtype.ext h)
    have h1 := dersEval_zeros_le hk1 p hp0
    have hall : Finset.univ.filter (fun i => dersEval F k p i = 0) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact congrFun hp i
    rw [hall, Finset.card_univ, Fintype.card_fin] at h1
    omega
  refine ⟨LinearMap.range L, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj,
      LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F k), Module.finrank_fin_fun]
  · rintro v ⟨p, rfl⟩ hv
    have hp0 : p.1 ≠ 0 := by
      intro h; apply hv
      have : p = 0 := Subtype.ext h
      rw [this, map_zero]
    have h1 := dersEval_zeros_le hk1 p hp0
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (Fintype.card F + 1)))) (fun i => dersEval F k p i = 0)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (Finset.univ.filter (fun i => L p i ≠ 0)) =
        Finset.univ.filter (fun i => ¬ dersEval F k p i = 0) := rfl
    rw [h3]
    omega

/-! ### Consequences for the frozen `Statement` -/

/-- **Non-vacuity / sharpness.** Whenever the `Statement`'s hypotheses `2 ≤ k ≤ q - 1` hold
(which needs `q ≥ 3`), an MDS code of length `n = q + 1` exists. So the non-exceptional bound
`n ≤ q + 1` cannot be improved, and the `Statement` is not vacuous. -/
theorem statement_hyp_attained (F : Type) [Field F] [Fintype F] [DecidableEq F] (k : ℕ)
    (hk : 2 ≤ k) (hkq : k ≤ Fintype.card F - 1) :
    IsLinearMDSCode F (Fintype.card F + 1) k :=
  ders_isLinearMDSCode (by omega) (by omega)

/-- For `q = 2` the `Statement`'s hypotheses `2 ≤ k ≤ q - 1` are unsatisfiable (so that case
is vacuous, as in the literature). -/
theorem no_k_of_card_two (F : Type) [Field F] [Fintype F] (hq : Fintype.card F = 2) (k : ℕ) :
    ¬ (2 ≤ k ∧ k ≤ Fintype.card F - 1) := by omega

/-- **The `Statement` holds for `k = 2`**, and for `k = 3` when `q` is even. Both follow from the
Bush bound (MacWilliams–Sloane Ch. 11 §5; Segre's conjecture is classical for these `k`). -/
theorem statement_of_k_two_or_three_even (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (hk : k = 2 ∨ (k = 3 ∧ Fintype.card F % 2 = 0))
    (h : IsLinearMDSCode F n k) :
    if Fintype.card F % 2 = 0 ∧ (k = 3 ∨ k = Fintype.card F - 1) then
      n ≤ Fintype.card F + 2 else n ≤ Fintype.card F + 1 := by
  have hb := bush_bound (by omega) h
  split_ifs <;> omega

end InfoTheory.Known.Certificates.MdsConjecture
