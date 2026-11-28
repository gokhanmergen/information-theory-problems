import InfoTheory.Problems.LocallyDecodableCodes3Query

/-!
# Certificate for `InfoTheory.Problems.LocallyDecodableCodes3Query`

The frozen statement asks whether every `3`-query binary LDC (`IsBinaryLDC k n 3 δ ε`) with
constant `δ, ε > 0` has super-polynomial length `n > C k^d` for all large `k`. Because the
Statement is universally quantified over LDCs, its main vacuity risk is that the hypothesis is
never satisfiable; the certificate rules this out.

## Certified (about exactly `IsBinaryLDC`)
* `card_good_ge`: union bound for paired queries (at least `N - 2|E|` seeds avoid `E`).
* `hadamard_isBinaryLDC` (non-vacuity + regression): the Hadamard code of length `2^k` is a
  `3`-query (in fact `2`-query, the third query is ignored) `(1/8, 1/4)`-LDC for **every** `k`.
  Hence for `δ ≤ 1/8`, `ε ≤ 1/4` the hypothesis of the Statement is satisfiable for every
  message length (via `isBinaryLDC_mono`), so the Statement is not vacuous; and it is consistent
  with the conjectured answer (`2^k` is super-polynomial).
* `isBinaryLDC_mono`: the predicate is antitone in `δ` and `ε`.
* `isBinaryLDC_eps_le`: any LDC with `k ≥ 1` has `ε ≤ 1/2` (success probability `≤ 1`); so the
  Statement is vacuous only for `ε > 1/2`, where it is trivially true, as intended.

## Not certified
* The lower bounds `n ≥ Ω̃(k^3)` (Alrabiah–Guruswami–Kothari–Manohar 2023) or `Ω̃(k^2)`
  (Kerenidis–de Wolf 2004), and the matching-vector upper bound `exp(exp(Õ(√log k)))`
  (Yekhanin 2008, Efremenko 2009).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.LocallyDecodableCodes3Query

open InfoTheory InfoTheory.Problems.LocallyDecodableCodes3Query

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

/-! ### The Hadamard code over `Bool` -/

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

/-- `Bool → 𝔽₂`. -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

/-- `𝔽₂ → Bool`. -/
def ofZ (z : ZMod 2) : Bool := decide (z = 1)

lemma ofZ_add (a b : ZMod 2) : ofZ (a + b) = xor (ofZ a) (ofZ b) := by
  revert a b; decide

lemma ofZ_toZ (b : Bool) : ofZ (toZ b) = b := by
  cases b <;> decide

/-- Hadamard encoder `x ↦ (⟨x, a⟩)_{a ∈ 𝔽₂^k}` on `Bool` strings. -/
noncomputable def hadEnc (k : ℕ) (x : Fin k → Bool) : Fin (2 ^ k) → Bool :=
  fun j => ofZ (ip (fun t => toZ (x t)) (idx k j))

/-- Pairing of seeds: `σ_a(r) = idx⁻¹(idx r + a)`. -/
noncomputable def shift (k : ℕ) (a : Fin k → ZMod 2) : Fin (2 ^ k) ≃ Fin (2 ^ k) :=
  (idx k).trans ((Equiv.addRight a).trans (idx k).symm)

lemma hadEnc_xor_shift (k : ℕ) (x : Fin k → Bool) (i : Fin k) (r : Fin (2 ^ k)) :
    xor (hadEnc k x r) (hadEnc k x (shift k (Pi.single i 1) r)) = x i := by
  simp only [hadEnc, shift, Equiv.trans_apply, Equiv.coe_addRight, Equiv.apply_symm_apply]
  rw [← ofZ_add, ip_shift, ip_single, ofZ_toZ]

/-- **Non-vacuity / regression.** The Hadamard code is a `3`-query `(1/8, 1/4)`-LDC of length
    `2^k` for every message length `k` (decoder `y(b) ⊕ y(b + eᵢ)`, third query unused). -/
theorem hadamard_isBinaryLDC (k : ℕ) : IsBinaryLDC k (2 ^ k) 3 (1 / 8) (1 / 4) := by
  classical
  refine ⟨hadEnc k, 2 ^ k, by positivity,
    fun i r => ![r, shift k (Pi.single i 1) r, r], fun _ _ v => xor (v 0) (v 1), ?_⟩
  intro x y hy i
  let E : Finset (Fin (2 ^ k)) := Finset.univ.filter (fun j => hadEnc k x j ≠ y j)
  have hE : (E.card : ℝ) ≤ 1 / 8 * ((2 ^ k : ℕ) : ℝ) := hy
  have hgood := card_good_ge (shift k (Pi.single i 1)) E
    (fun r => (fun v : Fin 3 → Bool => xor (v 0) (v 1))
      (fun j => y (![r, shift k (Pi.single i 1) r, r] j)) = x i) (by
      intro r hr hσr
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr hσr
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hr, ← hσr, hadEnc_xor_shift])
  have hN : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  rw [ge_iff_le, le_div_iff₀ hN]
  linarith

/-- The LDC predicate is antitone in the noise rate and the advantage. -/
theorem isBinaryLDC_mono {k n q : ℕ} {δ δ' ε ε' : ℝ} (hδ : δ' ≤ δ) (hε : ε' ≤ ε)
    (h : IsBinaryLDC k n q δ ε) : IsBinaryLDC k n q δ' ε' := by
  obtain ⟨enc, R, hR, queries, eval, hdec⟩ := h
  refine ⟨enc, R, hR, queries, eval, fun x y hy i => ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := hdec x y (le_trans hy (mul_le_mul_of_nonneg_right hδ hn)) i
  linarith

/-- Hence for all `δ ≤ 1/8`, `ε ≤ 1/4`, the Statement's hypothesis holds at every `k`. -/
theorem hadamard_isBinaryLDC_of_le (k : ℕ) {δ ε : ℝ} (hδ : δ ≤ 1 / 8) (hε : ε ≤ 1 / 4) :
    IsBinaryLDC k (2 ^ k) 3 δ ε :=
  isBinaryLDC_mono hδ hε (hadamard_isBinaryLDC k)

/-- Success probability is at most `1`, so any LDC with `k ≥ 1` has advantage `ε ≤ 1/2`. -/
theorem isBinaryLDC_eps_le {k n q : ℕ} {δ ε : ℝ} (hk : 0 < k) (hδ : 0 ≤ δ)
    (h : IsBinaryLDC k n q δ ε) : ε ≤ 1 / 2 := by
  classical
  obtain ⟨enc, R, hR, queries, eval, hdec⟩ := h
  have := hdec (fun _ => false) (enc fun _ => false)
    (by simp [hammingDistVec]; positivity) ⟨0, hk⟩
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hle : ((Finset.univ.filter (fun r : Fin R =>
      eval ⟨0, hk⟩ r (fun j => enc (fun _ => false) (queries ⟨0, hk⟩ r j)) = false)).card : ℝ)
        ≤ R := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin R))
      (fun r : Fin R => eval ⟨0, hk⟩ r (fun j => enc (fun _ => false) (queries ⟨0, hk⟩ r j))
        = false)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : ((Finset.univ.filter (fun r : Fin R =>
      eval ⟨0, hk⟩ r (fun j => enc (fun _ => false) (queries ⟨0, hk⟩ r j)) = false)).card : ℝ)
        / R ≤ 1 := by
    rw [div_le_one hR']; exact hle
  linarith

end InfoTheory.Known.Certificates.LocallyDecodableCodes3Query
