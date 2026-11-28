import InfoTheory.Problems.ExplicitListDecodableBinary

/-!
# Certificate for `InfoTheory.Problems.ExplicitListDecodableBinary`

The (fixed, 2026-11-27) statement asks for uniform polynomial-time Turing machines `E, D`
encoding `k = a m` bits into `n = b m` bits at a rational rate `a / b ≥ 1 - h(p) - ε` with
`D` list-decoding radius `p n` to a list of `L` messages.

## Certified (about exactly the objects in `Statement`)
* `statement_iff`: `Statement` unfolds to `∀ p ε, … → ∃ a b L c d N₀ E D, … ∧ ∀ m ≥ N₀,
  Body p a b L c d E D m`, where `Body` is the per-length predicate (halting, injectivity,
  list-decoding). The checks below are about this exact `Body`.
* `idTM_run`: semantics sanity of the Turing-machine model: the one-step identity machine
  `idTM` halts after one step and leaves its input on the tape, so
  `readTapeBits idTM (tmRunOnBits idTM x T)` returns `x` (padded with `false`) for all `T ≥ 1`.
* `body_identity_zero_radius` (regression, the solved degenerate case `p = 0`): the trivial
  code `E = D = idTM`, rate `a / b = 1 = 1 - h(0)`, list size `L = 1`, time `T = 1`, satisfies
  `Body 0 1 1 1 1 0 idTM idTM m` for every `m`. So `Body` is satisfiable by honest machines
  (halting, readout and list layout are not junk), and at `p = 0` capacity is achieved
  explicitly, as it should be.
* `body_injective_rate_le`: any `Body` witness with `m ≥ 1` has `a ≤ b` (an injective map
  `{0,1}^{am} → {0,1}^{bm}`), i.e. rate `≤ 1`.

## Not certified
* The list-decoding converse (rate `≤ 1 - h(p) + o(1)` for constant `L`), the random-coding
  achievability, and the best explicit results (Blokh–Zyablov radius, Guruswami–Rudra 2008).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ExplicitListDecodableBinary

open InfoTheory InfoTheory.Problems.ExplicitListDecodableBinary

/-- The per-length predicate inside `Statement`. -/
def Body (p : ℝ) (a b L c d : ℕ) (E D : UniformTM) (m : ℕ) : Prop :=
  let n : ℕ := b * m
  let k : ℕ := a * m
  let T : ℕ := c * n ^ d
  let enc (msg : Fin k → Bool) : Fin n → Bool := readTapeBits E (tmRunOnBits E msg T) n
  let dec (y : Fin n → Bool) : Fin (L * k) → Bool :=
    readTapeBits D (tmRunOnBits D y T) (L * k)
  (∀ msg : Fin k → Bool, (tmRunOnBits E msg T).state.1 = 0) ∧
  (∀ y : Fin n → Bool, (tmRunOnBits D y T).state.1 = 0) ∧
  Function.Injective enc ∧
  ∀ (msg : Fin k → Bool) (y : Fin n → Bool),
    (hammingDistVec (enc msg) y : ℝ) ≤ p * (n : ℝ) →
    ∃ ℓ : Fin L, extractListItem (dec y) ℓ = msg

theorem statement_iff : Statement ↔
    ∀ (p ε : ℝ), 0 < p → p < 1 / 2 → 0 < ε → ε < 1 - binaryEntropy p →
      ∃ (a b L c d N₀ : ℕ) (E D : UniformTM), 0 < b ∧ 0 < L ∧ 0 < c ∧
        1 - binaryEntropy p - ε ≤ (a : ℝ) / (b : ℝ) ∧
        ∀ m : ℕ, N₀ ≤ m → Body p a b L c d E D m :=
  Iff.rfl

/-- The identity machine: in state `1` rewrite the scanned symbol, move right, halt. -/
def idTM : UniformTM where
  numStates := 2
  hpos := by norm_num
  trans := fun _ s => (⟨0, by norm_num⟩, s, true)

lemma idTM_trans (st : Fin idTM.numStates) (a : Option Bool) :
    idTM.trans st a = (⟨0, by norm_num [idTM]⟩, a, true) := rfl

/-- Initial tape holding `inp` on `[0, inLen)`. -/
def initTape {inLen : ℕ} (inp : Fin inLen → Bool) : ℤ → Option Bool := fun p =>
  if _h0 : 0 ≤ p then
    if hlt : p.toNat < inLen then some (inp ⟨p.toNat, hlt⟩) else none
  else none

lemma idTM_run_aux {inLen : ℕ} (inp : Fin inLen → Bool) (T : ℕ) :
    (tmRunOnBits idTM inp T).tape = initTape inp ∧
      (1 ≤ T → (tmRunOnBits idTM inp T).state.1 = 0) := by
  induction T with
  | zero => exact ⟨rfl, fun h => absurd h (by norm_num)⟩
  | succ T ih =>
    have hstep : tmRunOnBits idTM inp (T + 1) = tmStep idTM (tmRunOnBits idTM inp T) := rfl
    rw [hstep]
    unfold tmStep
    split_ifs with h0
    · exact ⟨ih.1, fun _ => h0⟩
    · refine ⟨?_, fun _ => rfl⟩
      funext q
      simp only [idTM_trans]
      split_ifs with hq
      · rw [hq, ih.1]
      · rw [ih.1]

/-- Semantics sanity: after `T ≥ 1` steps `idTM` has halted with its input on the tape. -/
theorem idTM_run {inLen : ℕ} (inp : Fin inLen → Bool) {T : ℕ} (hT : 1 ≤ T) (outLen : ℕ)
    (i : Fin outLen) (hi : i.1 < inLen) :
    (tmRunOnBits idTM inp T).state.1 = 0 ∧
      readTapeBits idTM (tmRunOnBits idTM inp T) outLen i = inp ⟨i.1, hi⟩ := by
  obtain ⟨htape, hstate⟩ := idTM_run_aux inp T
  refine ⟨hstate hT, ?_⟩
  unfold readTapeBits
  rw [htape]
  simp [initTape, hi]

/-- **Regression (`p = 0`).** The identity code achieves rate `1 = 1 - h(0)` with list size
    `1` in time `1`: `Body 0 1 1 1 1 0 idTM idTM m` holds for every `m`. -/
theorem body_identity_zero_radius (m : ℕ) : Body 0 1 1 1 1 0 idTM idTM m := by
  have hrd : ∀ (len : ℕ) (inp : Fin len → Bool) (outLen : ℕ) (i : Fin outLen)
      (hi : i.1 < len), readTapeBits idTM (tmRunOnBits idTM inp (1 * (1 * m) ^ 0)) outLen i =
        inp ⟨i.1, hi⟩ := fun len inp outLen i hi =>
    (idTM_run inp (by simp) outLen i hi).2
  refine ⟨fun msg => (idTM_run_aux msg _).2 (by simp),
    fun y => (idTM_run_aux y _).2 (by simp), ?_, ?_⟩
  · intro x x' h
    funext j
    have hj : j.1 < 1 * m := j.2
    have := congrFun h ⟨j.1, by simpa using hj⟩
    simp only at this
    rw [hrd _ x _ _ hj, hrd _ x' _ _ hj] at this
    exact this
  · intro msg y hdist
    refine ⟨0, ?_⟩
    have h0 : hammingDistVec (readTapeBits idTM (tmRunOnBits idTM msg (1 * (1 * m) ^ 0)) (1 * m))
        y = 0 := by
      have : (hammingDistVec (readTapeBits idTM (tmRunOnBits idTM msg (1 * (1 * m) ^ 0))
          (1 * m)) y : ℝ) ≤ 0 := by simpa using hdist
      exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
    have heq : ∀ j : Fin (1 * m),
        readTapeBits idTM (tmRunOnBits idTM msg (1 * (1 * m) ^ 0)) (1 * m) j = y j := by
      intro j
      by_contra hne
      have : j ∈ Finset.univ.filter (fun i : Fin (1 * m) =>
          readTapeBits idTM (tmRunOnBits idTM msg (1 * (1 * m) ^ 0)) (1 * m) i ≠ y i) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
      have hpos := Finset.card_pos.2 ⟨j, this⟩
      unfold hammingDistVec at h0
      omega
    funext j
    have hj : j.1 < 1 * m := j.2
    unfold extractListItem
    simp only [Fin.val_zero, zero_mul, zero_add]
    rw [hrd _ y _ _ (by simpa using hj)]
    have := heq ⟨j.1, hj⟩
    rw [hrd _ msg _ _ hj] at this
    exact this.symm

/-- Rate at most `1`: an injective `{0,1}^{am} → {0,1}^{bm}` needs `a ≤ b` (for `m ≥ 1`). -/
theorem body_injective_rate_le {p : ℝ} {a b L c d m : ℕ} {E D : UniformTM} (hm : 1 ≤ m)
    (h : Body p a b L c d E D m) : a ≤ b := by
  obtain ⟨-, -, hinj, -⟩ := h
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

end InfoTheory.Known.Certificates.ExplicitListDecodableBinary
