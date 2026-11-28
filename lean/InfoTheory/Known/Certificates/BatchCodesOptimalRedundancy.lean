import InfoTheory.Problems.BatchCodesOptimalRedundancy

/-!
# Certificate for `InfoTheory.Problems.BatchCodesOptimalRedundancy`

The frozen statement asks whether, for every fixed `k ≥ 3`, the minimum redundancy
`minBatchRedundancy n k = r_B(n, k)` of binary linear primitive multiset `k`-batch codes is
`O_k(√n)`. Facts about the *exact* objects `IsLinearBinaryBatchCode` / `minBatchRedundancy`:

## Certified
* `repetition_isBatchCode`: the `k`-fold repetition code is a linear `k`-batch code of length
  `n + (k-1) n`; hence `minBatchRedundancy_le_repetition : r_B(n, k) ≤ (k - 1) n`. The defining
  set is non-empty, so `minBatchRedundancy` is a genuine minimum, never the junk `sInf ∅ = 0`.
* `minBatchRedundancy_one` (regression): `r_B(n, 1) = 0`.
* `not_isBatchCode_zero_redundancy`: for `k ≥ 2` and `n ≥ 1` there is no zero-redundancy code
  (the request `(i, i, …)` needs two disjoint recovery sets for `x_i`, impossible for a bijective
  linear encoder); hence `one_le_minBatchRedundancy : 1 ≤ r_B(n, k)`.
* `parity_isBatchCode` + `minBatchRedundancy_two` (regression, the solved case `k = 2`):
  the single-parity code is a `2`-batch code, and `r_B(n, 2) = 1` exactly for every `n ≥ 1`.

## Not certified
* The `Ω(√n)` lower bound for `k ≥ 3` (Rao–Vardy 2016, Wootters 2016), the `Θ(√n)` results for
  small `k` and the `O(√n log n)` upper bound for constant `k` (Vardy–Yaakobi 2016).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.BatchCodesOptimalRedundancy

open InfoTheory InfoTheory.Problems.BatchCodesOptimalRedundancy

/-! ### Repetition code -/

/-- Position of copy `t` of message symbol `i` in the `k`-fold repetition code. -/
def repPos {n k : ℕ} (t : Fin k) (i : Fin n) : Fin (n + (k - 1) * n) :=
  ⟨t.1 * n + i.1, by
    have ht := t.2
    have hi := i.2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have : t.1 * n ≤ k' * n := Nat.mul_le_mul_right n (by omega)
    simp only [Nat.add_sub_cancel]
    omega⟩

lemma repPos_mod {n k : ℕ} (t : Fin k) (i : Fin n) : (repPos t i).1 % n = i.1 := by
  simp [repPos, Nat.mul_comm t.1 n, Nat.mod_eq_of_lt i.2]

lemma repPos_div {n k : ℕ} (t : Fin k) (i : Fin n) : (repPos t i).1 / n = t.1 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [repPos]
  rw [Nat.mul_comm t.1 n, Nat.mul_add_div hn, Nat.div_eq_of_lt i.2, Nat.add_zero]

/-- The `k`-fold repetition code is a binary linear primitive multiset `k`-batch code. -/
theorem repetition_isBatchCode {n : ℕ} (hn : 0 < n) (k : ℕ) :
    IsLinearBinaryBatchCode n (n + (k - 1) * n) k := by
  refine ⟨LinearMap.funLeft (ZMod 2) (ZMod 2)
    (fun j : Fin (n + (k - 1) * n) => (⟨j.1 % n, Nat.mod_lt _ hn⟩ : Fin n)), ?_⟩
  intro req
  refine ⟨fun t => {repPos t (req t)}, fun t c => c (repPos t (req t)), ?_, ?_, ?_⟩
  · intro t₁ t₂ hne j ⟨h₁, h₂⟩
    rw [Finset.mem_singleton] at h₁ h₂
    apply hne
    apply Fin.ext
    rw [← repPos_div t₁ (req t₁), ← repPos_div t₂ (req t₂), ← h₁, ← h₂]
  · intro t c₁ c₂ h
    exact h _ (Finset.mem_singleton_self _)
  · intro x t
    simp only [LinearMap.funLeft_apply]
    congr 1
    exact Fin.ext (repPos_mod t (req t))

/-- Non-junk: `r_B(n, k) ≤ (k - 1) n`, and the defining set is non-empty. -/
theorem minBatchRedundancy_le_repetition {n : ℕ} (hn : 0 < n) (k : ℕ) :
    minBatchRedundancy n k ≤ (k - 1) * n :=
  Nat.sInf_le (repetition_isBatchCode hn k)

/-- Regression: `r_B(n, 1) = 0`. -/
theorem minBatchRedundancy_one {n : ℕ} (hn : 0 < n) : minBatchRedundancy n 1 = 0 := by
  have := minBatchRedundancy_le_repetition hn 1
  simpa using this

/-! ### No zero-redundancy code for `k ≥ 2` -/

theorem not_isBatchCode_zero_redundancy {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) :
    ¬ IsLinearBinaryBatchCode n (n + 0) k := by
  rintro ⟨enc, henc⟩
  let t₀ : Fin k := ⟨0, by omega⟩
  let t₁ : Fin k := ⟨1, by omega⟩
  have ht : t₀ ≠ t₁ := by simp [t₀, t₁, Fin.ext_iff]
  -- `enc` is injective (every symbol is recoverable), hence surjective.
  have hinj : Function.Injective enc := by
    intro x x' hxx'
    funext i
    obtain ⟨R, dec, -, -, hdec⟩ := henc (fun _ => i)
    rw [← hdec x t₀, ← hdec x' t₀, hxx']
  have hsurj : Function.Surjective enc := by
    let f : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) := enc
    exact (LinearMap.injective_iff_surjective (f := f)).1 hinj
  -- Request `(i, i, …)` with `i = 0`.
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨R, dec, hdisj, hloc, hdec⟩ := henc (fun _ => i)
  have hsame : ∀ c, dec t₀ c = dec t₁ c := by
    intro c
    obtain ⟨x, rfl⟩ := hsurj c
    rw [hdec x t₀, hdec x t₁]
  -- `dec t₀` is identically `0`.
  have hzero : ∀ c, dec t₀ c = 0 := by
    intro c
    classical
    let c' : Fin (n + 0) → ZMod 2 := fun j => if j ∈ R t₀ then c j else 0
    have h1 : dec t₀ c = dec t₀ c' := hloc t₀ c c' (fun j hj => by simp [c', hj])
    have h2 : dec t₁ c' = dec t₁ 0 := hloc t₁ c' 0 (fun j hj => by
      have : j ∉ R t₀ := fun h0 => hdisj t₀ t₁ ht j ⟨h0, hj⟩
      simp [c', this])
    have h3 : dec t₁ 0 = 0 := by
      have := hdec 0 t₁
      rwa [map_zero] at this
    rw [h1, hsame, h2, h3]
  have := hdec (Pi.single i 1) t₀
  rw [hzero, Pi.single_eq_same] at this
  exact zero_ne_one this

/-- For `k ≥ 2`, every batch code has redundancy at least `1`. -/
theorem one_le_minBatchRedundancy {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) :
    1 ≤ minBatchRedundancy n k := by
  have hne : { r : ℕ | IsLinearBinaryBatchCode n (n + r) k }.Nonempty :=
    ⟨_, repetition_isBatchCode hn k⟩
  have hmem := Nat.sInf_mem hne
  rcases Nat.eq_zero_or_pos (minBatchRedundancy n k) with h | h
  · exfalso
    unfold minBatchRedundancy at h
    rw [h] at hmem
    exact not_isBatchCode_zero_redundancy hn hk hmem
  · exact h

/-! ### Single-parity code (`k = 2`) -/

lemma fin2_cases (t : Fin 2) : t = 0 ∨ t = 1 := by
  fin_cases t <;> simp


/-- Systematic single-parity encoder `x ↦ (x, ∑ x_i)`. -/
def parityEnc (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (n + 1) → ZMod 2) where
  toFun x j := if h : j.1 < n then x ⟨j.1, h⟩ else ∑ i, x i
  map_add' x y := by
    funext j
    by_cases h : j.1 < n <;> simp [h, Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    by_cases h : j.1 < n <;> simp [h, Finset.mul_sum]

lemma parityEnc_castSucc {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) :
    parityEnc n x (Fin.castSucc i) = x i := by
  simp [parityEnc]

lemma parityEnc_last {n : ℕ} (x : Fin n → ZMod 2) :
    parityEnc n x (Fin.last n) = ∑ i, x i := by
  simp [parityEnc]

/-- The single-parity code is a binary linear primitive multiset `2`-batch code. -/
theorem parity_isBatchCode (n : ℕ) : IsLinearBinaryBatchCode n (n + 1) 2 := by
  classical
  refine ⟨parityEnc n, fun req => ?_⟩
  by_cases hreq : req 0 = req 1
  · -- Same symbol twice: read it directly, and recover it from the parity and the rest.
    let i := req 0
    let R : Fin 2 → Finset (Fin (n + 1)) := fun t =>
      if t = 0 then {Fin.castSucc i} else Finset.univ.erase (Fin.castSucc i)
    let dec : Fin 2 → (Fin (n + 1) → ZMod 2) → ZMod 2 := fun t c =>
      if t = 0 then c (Fin.castSucc i)
      else c (Fin.last n) - ∑ j ∈ Finset.univ.erase i, c (Fin.castSucc j)
    refine ⟨R, dec, ?_, ?_, ?_⟩
    · intro t₁ t₂ hne j ⟨h₁, h₂⟩
      fin_cases t₁ <;> fin_cases t₂ <;> simp_all [R]
    · intro t c₁ c₂ h
      rcases fin2_cases t with rfl | rfl
      · have := h (Fin.castSucc i) (by simp [R])
        simpa [dec] using this
      · have hl : c₁ (Fin.last n) = c₂ (Fin.last n) := h _ (by
          simp only [R, Fin.isValue, one_ne_zero, ↓reduceIte, Finset.mem_erase,
            Finset.mem_univ, and_true]
          exact (Fin.castSucc_lt_last i).ne')
        simp only [dec, Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [hl]
        congr 1
        refine Finset.sum_congr rfl fun j hj => h _ ?_
        rw [Finset.mem_erase] at hj
        simp only [R, Fin.isValue, one_ne_zero, ↓reduceIte, Finset.mem_erase]
        exact ⟨fun h' => hj.1 (Fin.castSucc_injective _ h'), Finset.mem_univ _⟩
    · intro x t
      rcases fin2_cases t with rfl | rfl
      · simp [dec, parityEnc_castSucc, i]
      · have hi : req 1 = i := hreq.symm
        rw [hi]
        simp only [dec, Fin.isValue, one_ne_zero, ↓reduceIte, parityEnc_last,
          parityEnc_castSucc]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        ring
  · -- Two different symbols: read each directly.
    refine ⟨fun t => {Fin.castSucc (req t)}, fun t c => c (Fin.castSucc (req t)), ?_, ?_, ?_⟩
    · intro t₁ t₂ hne j ⟨h₁, h₂⟩
      rw [Finset.mem_singleton] at h₁ h₂
      have : req t₁ = req t₂ := Fin.castSucc_injective _ (h₁.symm.trans h₂)
      fin_cases t₁ <;> fin_cases t₂ <;> simp_all
    · intro t c₁ c₂ h
      exact h _ (Finset.mem_singleton_self _)
    · intro x t
      exact parityEnc_castSucc x (req t)

/-- **Regression (solved case `k = 2`):** `r_B(n, 2) = 1` for every `n ≥ 1`. -/
theorem minBatchRedundancy_two {n : ℕ} (hn : 0 < n) : minBatchRedundancy n 2 = 1 :=
  le_antisymm (Nat.sInf_le (parity_isBatchCode n)) (one_le_minBatchRedundancy hn le_rfl)

end InfoTheory.Known.Certificates.BatchCodesOptimalRedundancy
