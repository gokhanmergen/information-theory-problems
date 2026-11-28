import InfoTheory.Problems.IndexCodingSingleLetter

/-!
# Certificate for `InfoTheory.Problems.IndexCodingSingleLetter`

The frozen statement asks for a halting Turing machine that, on (an encoding of) a digraph `G`
and a rational threshold `p/q` with precision `1/prec`, decides which side of the threshold the
broadcast rate `β(G) = indexCodingBroadcastRate` (Core; an `sInf` of `log₂ M / t` over zero-error
vector index codes) lies on, up to the `±1/prec` margin.

Certified here, about `indexCodingBroadcastRate` applied to the exact instance `Statement`
builds from an adjacency matrix (`queryInst`), and about general instances (no junk values):
* `betaSet_nonempty`, `betaSet_bddBelow` — the `sInf` is over a nonempty set bounded below;
* `one_le_beta`, `beta_le_n` — `1 ≤ β(G) ≤ n` for `n ≥ 1` (so `β` is a genuine real in
  `[1, n]` and the threshold questions in `Statement` are non-trivial);
* **regressions** (perfect graphs, `β = α(G)`):
  - `beta_complete` / `queryInst_complete` — complete side information: `β = 1`;
  - `beta_edgeless` / `queryInst_edgeless` — no side information: `β = n`;
  - `queryInst_ignores_diagonal` — the instance ignores diagonal entries of `adj`, so self-loops
    in the input encoding are harmless.

Not certified: any computability or uncomputability fact (the open question), the MAIS/LP lower
bounds, the fractional-clique-cover upper bound, or the `n ≤ 5` values of Arbabjolfaei et al.
The `Statement` itself is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.IndexCodingSingleLetter

open InfoTheory InfoTheory.Problems.IndexCodingSingleLetter

theorem log2_two_pow (k : ℕ) : log2 ((2 : ℝ) ^ k) = k := by
  unfold log2
  rw [Real.log_pow]
  have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

theorem log2_le_log2 {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx h) (Real.log_pos one_lt_two).le

theorem log2_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  div_nonneg (Real.log_nonneg hx) (Real.log_pos one_lt_two).le

/-! ### The nonlinear broadcast rate `β` -/

theorem betaSet_bddBelow {n : ℕ} (inst : IndexCodingInstance n) :
    BddBelow { r : ℝ | ∃ (t M : ℕ), 0 < t ∧ 0 < M ∧
      ∃ (enc : (Fin n → Fin t → Bool) → Fin M)
        (dec : ∀ i : Fin n, Fin M → (Fin n → Fin t → Bool) → (Fin t → Bool)),
        (∀ i m x y, (∀ j, inst.sideInfo i j → x j = y j) → dec i m x = dec i m y) ∧
        (∀ x i, dec i (enc x) x = x i) ∧
        r = log2 (M : ℝ) / (t : ℝ) } := by
  refine ⟨0, ?_⟩
  rintro r ⟨t, M, ht, hM, -, -, -, -, rfl⟩
  exact div_nonneg (log2_nonneg_of_one_le (by exact_mod_cast hM)) (Nat.cast_nonneg t)

/-- Any zero-error code with a finite broadcast alphabet type upper-bounds `β`. -/
theorem beta_le_of_code {n : ℕ} (inst : IndexCodingInstance n) (t : ℕ) (ht : 0 < t)
    (C : Type) [Fintype C] [Nonempty C] (enc : (Fin n → Fin t → Bool) → C)
    (dec : ∀ i : Fin n, C → (Fin n → Fin t → Bool) → (Fin t → Bool))
    (hside : ∀ i c x y, (∀ j, inst.sideInfo i j → x j = y j) → dec i c x = dec i c y)
    (hdec : ∀ x i, dec i (enc x) x = x i) :
    indexCodingBroadcastRate inst ≤ log2 (Fintype.card C : ℝ) / t := by
  let e := Fintype.equivFin C
  refine csInf_le (betaSet_bddBelow inst) ⟨t, Fintype.card C, ht, Fintype.card_pos,
    fun x => e (enc x), fun i m x => dec i (e.symm m) x, ?_, ?_, rfl⟩
  · intro i m x y h; exact hside i _ x y h
  · intro x i; simp [hdec]

theorem beta_le_n {n : ℕ} (inst : IndexCodingInstance n) :
    indexCodingBroadcastRate inst ≤ n := by
  have := beta_le_of_code inst 1 one_pos (Fin n → Fin 1 → Bool) id (fun i c _ => c i)
    (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, pow_one] at this
  push_cast at this
  rw [log2_two_pow] at this; simpa using this

theorem betaSet_nonempty {n : ℕ} (inst : IndexCodingInstance n) :
    { r : ℝ | ∃ (t M : ℕ), 0 < t ∧ 0 < M ∧
      ∃ (enc : (Fin n → Fin t → Bool) → Fin M)
        (dec : ∀ i : Fin n, Fin M → (Fin n → Fin t → Bool) → (Fin t → Bool)),
        (∀ i m x y, (∀ j, inst.sideInfo i j → x j = y j) → dec i m x = dec i m y) ∧
        (∀ x i, dec i (enc x) x = x i) ∧
        r = log2 (M : ℝ) / (t : ℝ) }.Nonempty := by
  let C := Fin n → Fin 1 → Bool
  let e := Fintype.equivFin C
  exact ⟨_, 1, Fintype.card C, one_pos, Fintype.card_pos, fun x => e x,
    fun i m _ => (e.symm m) i, fun _ _ _ _ _ => rfl, fun x i => by simp, rfl⟩

/-- `β(G) ≥ 1` whenever there is at least one receiver. -/
theorem one_le_beta {n : ℕ} (inst : IndexCodingInstance n) (hn : 0 < n) :
    1 ≤ indexCodingBroadcastRate inst := by
  refine le_csInf (betaSet_nonempty inst) ?_
  rintro r ⟨t, M, ht, hM, enc, dec, hside, hdec, rfl⟩
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Fin n → Fin t → Bool := fun _ _ => false
  let φ : (Fin t → Bool) → Fin M := fun y => enc (Function.update x0 i0 y)
  have hagree : ∀ y y' : Fin t → Bool, ∀ c, dec i0 c (Function.update x0 i0 y) =
      dec i0 c (Function.update x0 i0 y') := by
    intro y y' c
    refine hside i0 c _ _ fun j hj => ?_
    have hne : j ≠ i0 := fun h => inst.irrefl i0 (h ▸ hj)
    simp [Function.update_of_ne hne]
  have hφ : Function.Injective φ := by
    intro y y' h
    have e1 := hdec (Function.update x0 i0 y) i0
    have e2 := hdec (Function.update x0 i0 y') i0
    simp only [Function.update_self] at e1 e2
    rw [← e1, ← e2]
    change dec i0 (φ y) _ = dec i0 (φ y') _
    rw [h, hagree y y']
  have hcard := Fintype.card_le_of_injective φ hφ
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  have hcardR : (2 : ℝ) ^ t ≤ (M : ℝ) := by exact_mod_cast hcard
  have hlog := log2_le_log2 (by positivity) hcardR
  rw [log2_two_pow] at hlog
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [le_div_iff₀ htpos]; linarith

/-- No side information: `β(G) ≥ n` (the encoder must be injective). -/
theorem n_le_beta_of_edgeless {n : ℕ} (inst : IndexCodingInstance n)
    (h : ∀ i j, ¬ inst.sideInfo i j) : (n : ℝ) ≤ indexCodingBroadcastRate inst := by
  refine le_csInf (betaSet_nonempty inst) ?_
  rintro r ⟨t, M, ht, hM, enc, dec, hside, hdec, rfl⟩
  have hinj : Function.Injective enc := by
    intro x y hxy
    funext i
    rw [← hdec x i, ← hdec y i, hxy]
    exact hside i _ x y fun j hj => (h i j hj).elim
  have hcard := Fintype.card_le_of_injective enc hinj
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hcard
  have hcardR : (2 : ℝ) ^ (t * n) ≤ (M : ℝ) := by rw [pow_mul]; exact_mod_cast hcard
  have hlog := log2_le_log2 (by positivity) hcardR
  rw [log2_two_pow] at hlog
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [le_div_iff₀ htpos]; push_cast at hlog; linarith

theorem beta_edgeless {n : ℕ} (inst : IndexCodingInstance n) (h : ∀ i j, ¬ inst.sideInfo i j) :
    indexCodingBroadcastRate inst = n :=
  le_antisymm (beta_le_n inst) (n_le_beta_of_edgeless inst h)

/-- `𝔽₂`-indicator of a bit. -/
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_decide (b : Bool) : decide (b2z b = 1) = b := by cases b <;> decide

/-- Complete side information: one parity bit suffices, `β(G) ≤ 1`. -/
theorem beta_le_one_of_complete {n : ℕ} (inst : IndexCodingInstance n)
    (h : ∀ i j, i ≠ j → inst.sideInfo i j) : indexCodingBroadcastRate inst ≤ 1 := by
  have := beta_le_of_code inst 1 one_pos (ZMod 2) (fun x => ∑ j, b2z (x j 0))
    (fun i c x _ => decide (c - ∑ j ∈ Finset.univ.erase i, b2z (x j 0) = 1)) ?_ ?_
  · rw [ZMod.card] at this
    have h2 : log2 ((2 : ℕ) : ℝ) = 1 := by simpa using log2_two_pow 1
    rwa [h2, Nat.cast_one, div_one] at this
  · intro i c x y hxy
    funext _
    rw [Finset.sum_congr rfl fun j hj => by rw [hxy j (h i j (Finset.ne_of_mem_erase hj).symm)]]
  · intro x i
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_right, b2z_decide]

theorem beta_complete {n : ℕ} (inst : IndexCodingInstance n) (hn : 0 < n)
    (h : ∀ i j, i ≠ j → inst.sideInfo i j) : indexCodingBroadcastRate inst = 1 :=
  le_antisymm (beta_le_one_of_complete inst h) (one_le_beta inst hn)

/-! ### The instance built inside `Statement` -/

/-- The side-information instance that `Statement` builds from an adjacency matrix. -/
def queryInst (n : ℕ) (adj : Fin n → Fin n → Bool) : IndexCodingInstance n :=
  ⟨fun i j => i ≠ j ∧ adj i j = true, fun _ h => h.1 rfl⟩

theorem queryInst_ignores_diagonal (n : ℕ) (adj adj' : Fin n → Fin n → Bool)
    (h : ∀ i j, i ≠ j → adj i j = adj' i j) :
    indexCodingBroadcastRate (queryInst n adj) = indexCodingBroadcastRate (queryInst n adj') := by
  have : queryInst n adj = queryInst n adj' := by
    unfold queryInst
    congr 1
    funext i j
    apply propext
    constructor
    · rintro ⟨hij, ha⟩; exact ⟨hij, (h i j hij) ▸ ha⟩
    · rintro ⟨hij, ha⟩; exact ⟨hij, (h i j hij).symm ▸ ha⟩
  rw [this]

theorem queryInst_bounds (n : ℕ) (adj : Fin n → Fin n → Bool) (hn : 0 < n) :
    1 ≤ indexCodingBroadcastRate (queryInst n adj) ∧
      indexCodingBroadcastRate (queryInst n adj) ≤ n :=
  ⟨one_le_beta _ hn, beta_le_n _⟩

theorem queryInst_complete (n : ℕ) (hn : 0 < n) :
    indexCodingBroadcastRate (queryInst n fun _ _ => true) = 1 :=
  beta_complete _ hn fun _ _ hij => ⟨hij, rfl⟩

theorem queryInst_edgeless (n : ℕ) :
    indexCodingBroadcastRate (queryInst n fun _ _ => false) = n :=
  beta_edgeless _ fun _ _ h => Bool.false_ne_true h.2

end InfoTheory.Known.Certificates.IndexCodingSingleLetter
