import InfoTheory.Problems.IndexCodingLinearNonlinearGap

/-!
# Certificate for `InfoTheory.Problems.IndexCodingLinearNonlinearGap`

The frozen statement asks whether, for every `ε > 0`, there are arbitrarily large `n`-vertex
side-information digraphs with `n^(1-ε) · β(G) ≤ β_lin(G)`, where `β = indexCodingBroadcastRate`
(Core; an `sInf` of `log₂ M / t`) and `β_lin = fieldLinearIndexCodingRate` (an `sInf` of `m / t`
over all finite fields and vector lengths).

Certified here, about these exact objects (no junk values):
* `beta_le_n`, `one_le_beta` — `1 ≤ β(G) ≤ n` for every instance with `n ≥ 1` (so the `sInf`
  is over a nonempty set and `β(G) > 0`; the inequality in `Statement` cannot hold through a
  junk `β = 0`);
* `betaLin_le_n`, `one_le_betaLin` — `1 ≤ β_lin(G) ≤ n` (the trivial code over `𝔽₂`, and the
  counting bound `|F|^t ≤ |F|^m` for any field);
* **regressions** (perfect graphs, where `β = β_lin = α(G) = χ(Ḡ)`):
  - `beta_complete`, `betaLin_complete` — complete side information: `β = β_lin = 1`
    (one parity symbol over `𝔽₂`);
  - `beta_edgeless`, `betaLin_edgeless` — no side information: `β = β_lin = n`;
  so the ratio `β_lin / β` is exactly `1` on both extremes, and `statement_fails_on_complete`
  records that complete graphs with `n ≥ 2` never witness the `Statement` inequality for
  `ε < 1`.

Not certified: `β ≤ β_lin` in general (simulating an `F`-linear code by a binary code needs
block-length bookkeeping when `|F|` is not a power of two), the Lubetzky–Stav and
Blasiak–Kleinberg–Lubetzky separations, and any polynomial separation for digraph (unicast)
instances. The `Statement` itself is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.IndexCodingLinearNonlinearGap

open InfoTheory InfoTheory.Problems.IndexCodingLinearNonlinearGap

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

/-! ### The field-independent vector-linear rate `β_lin` -/

theorem betaLinSet_bddBelow {n : ℕ} (inst : IndexCodingInstance n) :
    BddBelow { r : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F),
      @HasFieldLinearIndexRate F hF hFin n inst r } := by
  refine ⟨0, ?_⟩
  rintro r ⟨F, hF, hFin, t, m, ht, enc, dec, -, -, rfl⟩
  positivity

theorem betaLin_le_of_code {n : ℕ} (inst : IndexCodingInstance n) (F : Type) [Field F]
    [Fintype F] (t m : ℕ) (ht : 0 < t) (enc : (Fin n → Fin t → F) →ₗ[F] (Fin m → F))
    (dec : ∀ i : Fin n, (Fin m → F) → (Fin n → Fin t → F) → (Fin t → F))
    (hside : ∀ i c x y, (∀ j : Fin n, inst.sideInfo i j → x j = y j) → dec i c x = dec i c y)
    (hdec : ∀ x i, dec i (enc x) x = x i) :
    fieldLinearIndexCodingRate inst ≤ (m : ℝ) / t :=
  csInf_le (betaLinSet_bddBelow inst)
    ⟨F, inferInstance, inferInstance, t, m, ht, enc, dec, hside, hdec, rfl⟩

/-- Uncoded transmission over `𝔽₂` as a linear map. -/
def uncodedEnc (n : ℕ) : (Fin n → Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x j := x j 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem betaLin_le_n {n : ℕ} (inst : IndexCodingInstance n) :
    fieldLinearIndexCodingRate inst ≤ n := by
  have := betaLin_le_of_code inst (ZMod 2) 1 n one_pos (uncodedEnc n) (fun i c _ _ => c i)
    (fun _ _ _ _ _ => rfl)
    (fun x i => by funext k; rw [Subsingleton.elim k 0]; rfl)
  simpa using this

theorem betaLinSet_nonempty {n : ℕ} (inst : IndexCodingInstance n) :
    { r : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F),
      @HasFieldLinearIndexRate F hF hFin n inst r }.Nonempty :=
  ⟨_, ZMod 2, inferInstance, inferInstance, 1, n, one_pos, uncodedEnc n, fun i c _ _ => c i,
    fun _ _ _ _ _ => rfl, fun x i => by funext k; rw [Subsingleton.elim k 0]; rfl, rfl⟩

/-- `β_lin(G) ≥ 1` whenever there is at least one receiver (any field). -/
theorem one_le_betaLin {n : ℕ} (inst : IndexCodingInstance n) (hn : 0 < n) :
    1 ≤ fieldLinearIndexCodingRate inst := by
  refine le_csInf (betaLinSet_nonempty inst) ?_
  rintro r ⟨F, hF, hFin, t, m, ht, enc, dec, hside, hdec, rfl⟩
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let φ : (Fin t → F) → (Fin m → F) := fun y => enc (Pi.single i0 y)
  have hagree : ∀ y y' : Fin t → F, ∀ c, dec i0 c (Pi.single i0 y) =
      dec i0 c (Pi.single i0 y') := by
    intro y y' c
    refine hside i0 c _ _ fun j hj => ?_
    have hne : j ≠ i0 := fun h => inst.irrefl i0 (h ▸ hj)
    simp [Pi.single_eq_of_ne hne]
  have hφ : Function.Injective φ := by
    intro y y' h
    have e1 := hdec (Pi.single i0 y) i0
    have e2 := hdec (Pi.single i0 y') i0
    simp only [Pi.single_eq_same] at e1 e2
    rw [← e1, ← e2]
    change dec i0 (φ y) _ = dec i0 (φ y') _
    rw [h, hagree y y']
  have hcard := Fintype.card_le_of_injective φ hφ
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  have h2 : 1 < Fintype.card F := Fintype.one_lt_card
  have htm : t ≤ m := (Nat.pow_le_pow_iff_right h2).mp hcard
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [le_div_iff₀ htpos, one_mul]; exact_mod_cast htm

/-- No side information: `β_lin(G) = n`. -/
theorem betaLin_edgeless {n : ℕ} (inst : IndexCodingInstance n)
    (h : ∀ i j, ¬ inst.sideInfo i j) : fieldLinearIndexCodingRate inst = n := by
  refine le_antisymm (betaLin_le_n inst) (le_csInf (betaLinSet_nonempty inst) ?_)
  rintro r ⟨F, hF, hFin, t, m, ht, enc, dec, hside, hdec, rfl⟩
  have hinj : Function.Injective enc := by
    intro x y hxy
    funext i
    rw [← hdec x i, ← hdec y i, hxy]
    exact hside i _ x y fun j hj => (h i j hj).elim
  have hcard := Fintype.card_le_of_injective enc hinj
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul] at hcard
  have h2 : 1 < Fintype.card F := Fintype.one_lt_card
  have htm : t * n ≤ m := (Nat.pow_le_pow_iff_right h2).mp hcard
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [le_div_iff₀ htpos]
  have : ((t * n : ℕ) : ℝ) ≤ m := by exact_mod_cast htm
  push_cast at this; linarith

/-- The `𝔽₂` parity code as a linear map. -/
def parityEnc (n : ℕ) : (Fin n → Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 1 → ZMod 2) where
  toFun x _ := ∑ j, x j 0
  map_add' x y := by funext; simp [Finset.sum_add_distrib]
  map_smul' c x := by funext; simp [Finset.mul_sum]

theorem betaLin_le_one_of_complete {n : ℕ} (inst : IndexCodingInstance n)
    (h : ∀ i j, i ≠ j → inst.sideInfo i j) : fieldLinearIndexCodingRate inst ≤ 1 := by
  have := betaLin_le_of_code inst (ZMod 2) 1 1 one_pos (parityEnc n)
    (fun i c x _ => c 0 - ∑ j ∈ Finset.univ.erase i, x j 0) ?_ ?_
  · simpa using this
  · intro i c x y hxy
    funext _
    rw [Finset.sum_congr rfl fun j hj => by rw [hxy j (h i j (Finset.ne_of_mem_erase hj).symm)]]
  · intro x i
    funext k
    rw [Subsingleton.elim k 0]
    change (∑ j, x j 0) - _ = _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_right]

theorem betaLin_complete {n : ℕ} (inst : IndexCodingInstance n) (hn : 0 < n)
    (h : ∀ i j, i ≠ j → inst.sideInfo i j) : fieldLinearIndexCodingRate inst = 1 :=
  le_antisymm (betaLin_le_one_of_complete inst h) (one_le_betaLin inst hn)

/-- Complete side-information graphs never witness the `Statement` inequality
    (`n ≥ 2`, `ε < 1`): there `β = β_lin = 1 < n^(1-ε)`. -/
theorem statement_fails_on_complete {n : ℕ} (inst : IndexCodingInstance n) (hn : 2 ≤ n)
    (h : ∀ i j, i ≠ j → inst.sideInfo i j) {ε : ℝ} (hε : ε < 1) :
    fieldLinearIndexCodingRate inst < (n : ℝ) ^ (1 - ε) * indexCodingBroadcastRate inst := by
  rw [betaLin_complete inst (by omega) h, beta_complete inst (by omega) h, mul_one]
  exact Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < n)) (by linarith)

end InfoTheory.Known.Certificates.IndexCodingLinearNonlinearGap
