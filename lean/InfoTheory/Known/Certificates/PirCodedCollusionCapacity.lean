import InfoTheory.Problems.PirCodedCollusionCapacity

/-!
# Certificate for `InfoTheory.Problems.PirCodedCollusionCapacity`

The frozen statement is the asymptotic MDS-TPIR capacity conjecture
`C_∞(N, K, T) = 1 - (K + T - 1)/N` for `1 ≤ K, T`, `K + T - 1 < N`, where
`mdsTPirCapacity N K T M` is an `sSup` of zero-error download rates over all finite fields and
`mdsTPirAsympCapacity N K T` is the `sInf` over `M ≥ 1` of these capacities.

Certified here, about these exact objects:
* `vandermonde_isMDS`, `exists_mds_generator` — `[N, K]` MDS generator matrices (in the exact
  `IsMDSGenerator` sense) exist for every `K ≤ N` (Vandermonde/Reed–Solomon over a prime field
  `ZMod p`, `p ≥ N`); so the rate sets are not vacuously empty;
* `hasRate_inv_M` — the scheme "download every file from `K` servers" (constant queries, hence
  `T`-private for every `T`) achieves rate `1/M` whenever `1 ≤ K ≤ N`, `1 ≤ M`;
* `rate_le_one`, `rateSet_bddAbove` — every scheme has rate `≤ 1` (the answers determine the
  `LK` desired symbols; counting `|F|^{LK} ≤ ∏ D_j`), so the `sSup` is over a set bounded above;
* `inv_M_le_capacity`, `capacity_le_one` — `1/M ≤ C(N, K, T, M) ≤ 1`;
* **regression** `capacity_one_file` — `C(N, K, T, 1) = 1` (one file: no privacy cost; this is the
  `M = 1` value of the Sun–Jafar, Banawan–Ulukus and Freij-Hollanti et al. formulas);
* `asympSet_nonempty`, `asympSet_bddBelow`, `asympCapacity_mem_Icc` — the `sInf` defining
  `C_∞` is over a nonempty set bounded below, and `0 ≤ C_∞(N, K, T) ≤ 1`; `asymp_le_capacity`.

Not certified: the Sun–Jafar / Banawan–Ulukus capacity formulas (`K = 1` or `T = 1`), the
star-product achievability `C_∞ ≥ 1 - (K+T-1)/N`, and the Sun–Jafar `(4,2,2,2)` rate `3/5`.
The `Statement` itself is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.PirCodedCollusionCapacity

open InfoTheory InfoTheory.Problems.PirCodedCollusionCapacity

theorem log2_le_log2 {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx h) (Real.log_pos one_lt_two).le

theorem log2_pow' {x : ℝ} (n : ℕ) : log2 (x ^ n) = n * log2 x := by
  unfold log2; rw [Real.log_pow, mul_div_assoc]

theorem log2_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < log2 x :=
  div_pos (Real.log_pos hx) (Real.log_pos one_lt_two)

theorem log2_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x :=
  div_nonneg (Real.log_nonneg hx) (Real.log_pos one_lt_two).le

theorem log2_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
    log2 (∏ i ∈ s, f i) = ∑ i ∈ s, log2 (f i) := by
  unfold log2; rw [Real.log_prod hf, Finset.sum_div]

/-! ### Vandermonde (Reed–Solomon) generator matrices are MDS -/

/-- The `K × N` Vandermonde matrix `G r j = α_j ^ r`. -/
def vdm (F : Type) [Field F] {N K : ℕ} (α : Fin N → F) : Matrix (Fin K) (Fin N) F :=
  Matrix.of fun r j => α j ^ (r : ℕ)

theorem vandermonde_isMDS (F : Type) [Field F] [Fintype F] {N K : ℕ} (α : Fin N → F)
    (hα : Function.Injective α) : IsMDSGenerator F N K (vdm F α) := by
  classical
  intro S hS x₁ x₂ h
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; funext r; exact r.elim0
  let p : Polynomial F := ∑ r : Fin K, Polynomial.C (x₁ r - x₂ r) * Polynomial.X ^ (r : ℕ)
  have hdeg : p.natDegree < Fintype.card S := by
    rw [Fintype.card_coe, hS]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := K - 1)
      fun r _ => ?_) (by omega)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have heval : ∀ j : S, p.eval (α j) = 0 := by
    intro j
    have hj := h j.1 j.2
    simp only [vdm, Matrix.of_apply] at hj
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hj
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hj]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hp0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun j : S => α j) (hα.comp Subtype.val_injective) heval hdeg
  funext r
  have hc := congrArg (fun q : Polynomial F => q.coeff (r : ℕ)) hp0
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single r (fun b _ hb => if_neg fun h => hb (Fin.ext h).symm)
    (by simp)] at hc
  simpa [sub_eq_zero] using hc

/-- `[N, K]` MDS generators exist over a prime field `ZMod p` with `p ≥ N`. -/
theorem exists_mds_generator (N K : ℕ) :
    ∃ (F : Type) (hF : Field F) (hFin : Fintype F) (hDec : DecidableEq F)
      (G : Matrix (Fin K) (Fin N) F), @IsMDSGenerator F hF hFin N K G := by
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (ZMod p) := by
    rw [Fintype.card_fin, ZMod.card]; exact hNp
  obtain ⟨α⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨ZMod p, inferInstance, inferInstance, inferInstance, vdm (ZMod p) α,
    vandermonde_isMDS (ZMod p) α α.injective⟩

/-! ### Upper bound: every scheme has rate at most `1` -/

theorem rate_le_one {F : Type} [Field F] [Fintype F] [DecidableEq F] {N K T M : ℕ} {R : ℝ}
    (hM : 1 ≤ M) (h : HasMDSTPIRRate F N K T M R) : R ≤ 1 := by
  obtain ⟨L, numRand, Q, D, G, query, ans, dec, hL, hn, hQ, hD, -, hcorr, -, hpos, hR⟩ := h
  let θ0 : Fin M := ⟨0, hM⟩
  let u0 : Fin numRand := ⟨0, hn⟩
  let W0 : Fin M → Fin L → Fin K → F := fun _ _ _ => 0
  let φ : (Fin L → Fin K → F) → (∀ j : Fin N, Fin (D j)) := fun w j =>
    ans j (fun m ℓ => ∑ r : Fin K, Function.update W0 θ0 w m ℓ r * G r j) (query θ0 u0 j)
  have hdec : ∀ w, dec θ0 u0 (φ w) = w := by
    intro w
    have := hcorr (Function.update W0 θ0 w) θ0 u0
    simp only [Function.update_self] at this
    exact this
  have hφ : Function.Injective φ := by
    intro w w' hw
    rw [← hdec w, ← hdec w', hw]
  have hcard := Fintype.card_le_of_injective φ hφ
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_pi] at hcard
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hcardR : (((Fintype.card F : ℝ)) ^ K) ^ L ≤ ∏ j : Fin N, (D j : ℝ) := by
    exact_mod_cast hcard
  have hlog := log2_le_log2 (by positivity) hcardR
  rw [log2_pow', log2_pow',
    log2_prod _ _ fun j _ => (Nat.cast_pos.mpr (hD j)).ne'] at hlog
  have hnum : ((L * K : ℕ) : ℝ) * log2 (Fintype.card F : ℝ) ≤ ∑ j : Fin N, log2 (D j : ℝ) := by
    push_cast; linarith
  exact hR.trans ((div_le_one hpos).mpr hnum)

/-! ### Achievability: download every file from `K` servers -/

/-- Server `j` returns all of its stored symbols iff `j ∈ S₀` (answer type indexed by `c_j`). -/
abbrev AnsTy (F : Type) {N : ℕ} (S0 : Finset (Fin N)) (M : ℕ) (j : Fin N) : Type :=
  Fin (if j ∈ S0 then 1 else 0) → Fin M → F

theorem hasRate_inv_M {F : Type} [Field F] [Fintype F] [DecidableEq F] {N K T M : ℕ}
    (hK : 1 ≤ K) (hKN : K ≤ N) (hM : 1 ≤ M) (G : Matrix (Fin K) (Fin N) F)
    (hG : IsMDSGenerator F N K G) : HasMDSTPIRRate F N K T M (1 / (M : ℝ)) := by
  classical
  obtain ⟨S0, -, hS0⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N)))
    (n := K) (by simpa using hKN)
  let A := AnsTy F S0 M
  let e : ∀ j, A j ≃ Fin (Fintype.card (A j)) := fun j => Fintype.equivFin (A j)
  let encS : (Fin 1 → Fin K → F) → (S0 → F) := fun w j => ∑ r : Fin K, w 0 r * G r j
  have hinj : Function.Injective encS := by
    intro w w' hw
    funext ℓ
    rw [Subsingleton.elim ℓ 0]
    exact hG S0 hS0 _ _ fun j hj => congrFun hw ⟨j, hj⟩
  have hidx : ∀ j : S0, 0 < (if (j : Fin N) ∈ S0 then 1 else 0) := fun j => by simp [j.2]
  refine ⟨1, 1, 1, fun j => Fintype.card (A j), G, fun _ _ _ => 0,
    fun j s _ => e j (fun _ m => s m 0),
    fun θ _ a => Function.invFun encS (fun j : S0 => (e j).symm (a j) ⟨0, hidx j⟩ θ),
    one_pos, one_pos, one_pos, fun j => Fintype.card_pos, hG, ?_, ?_, ?_, ?_⟩
  · intro W θ u
    simp only [Equiv.symm_apply_apply]
    have : (fun j : S0 => ∑ r : Fin K, W θ 0 r * G r j) = encS (W θ) := rfl
    rw [this, Function.leftInverse_invFun hinj]
  · intro S _ θ₁ θ₂ qObs; rfl
  · -- positivity of the total download
    obtain ⟨j0, hj0⟩ : S0.Nonempty := Finset.card_pos.mp (by omega)
    have hterm : ∀ j : Fin N, 0 ≤ log2 (Fintype.card (A j) : ℝ) := fun j =>
      log2_nonneg_of_one_le (by exact_mod_cast Fintype.card_pos)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j0))
    apply log2_pos_of_one_lt
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card (A j0) := by
      simp only [A, AnsTy, Fintype.card_fun, Fintype.card_fin, hj0, if_true, pow_one]
      exact Nat.one_lt_pow (by omega) hq
    exact_mod_cast this
  · -- the rate equals `1/M`
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have hlq : 0 < log2 (Fintype.card F : ℝ) := log2_pos_of_one_lt (by exact_mod_cast hq)
    have hsum : ∑ j : Fin N, log2 (Fintype.card (A j) : ℝ) =
        (K : ℝ) * ((M : ℝ) * log2 (Fintype.card F : ℝ)) := by
      have hj : ∀ j : Fin N, log2 (Fintype.card (A j) : ℝ) =
          ((if j ∈ S0 then 1 else 0 : ℕ) : ℝ) * ((M : ℝ) * log2 (Fintype.card F : ℝ)) := by
        intro j
        simp only [A, AnsTy, Fintype.card_fun, Fintype.card_fin]
        push_cast
        rw [log2_pow', log2_pow']
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul]
      congr 1
      simp [Nat.cast_ite, Finset.sum_ite_mem, hS0]
    rw [hsum]
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    apply le_of_eq
    field_simp
    push_cast; ring

/-! ### The capacity `C(N, K, T, M)` -/

abbrev rateSet (N K T M : ℕ) : Set ℝ :=
  { R : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F) (hDec : DecidableEq F),
    @HasMDSTPIRRate F hF hFin hDec N K T M R }

theorem rateSet_bddAbove (N K T M : ℕ) (hM : 1 ≤ M) : BddAbove (rateSet N K T M) := by
  refine ⟨1, ?_⟩
  rintro R ⟨F, hF, hFin, hDec, h⟩
  exact rate_le_one hM h

theorem inv_M_mem_rateSet {N K T M : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (hM : 1 ≤ M) :
    1 / (M : ℝ) ∈ rateSet N K T M := by
  obtain ⟨F, hF, hFin, hDec, G, hG⟩ := exists_mds_generator N K
  exact ⟨F, hF, hFin, hDec, hasRate_inv_M hK hKN hM G hG⟩

theorem rateSet_nonempty {N K T M : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (hM : 1 ≤ M) :
    (rateSet N K T M).Nonempty := ⟨_, inv_M_mem_rateSet hK hKN hM⟩

theorem capacity_le_one {N K T M : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (hM : 1 ≤ M) :
    mdsTPirCapacity N K T M ≤ 1 :=
  csSup_le (rateSet_nonempty hK hKN hM) fun _ ⟨_, _, _, _, h⟩ => rate_le_one hM h

theorem inv_M_le_capacity {N K T M : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (hM : 1 ≤ M) :
    1 / (M : ℝ) ≤ mdsTPirCapacity N K T M :=
  le_csSup (rateSet_bddAbove N K T M hM) (inv_M_mem_rateSet hK hKN hM)

/-- **Regression:** with a single file there is nothing to hide, `C(N, K, T, 1) = 1`. -/
theorem capacity_one_file {N K T : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    mdsTPirCapacity N K T 1 = 1 :=
  le_antisymm (capacity_le_one hK hKN le_rfl)
    (by simpa using inv_M_le_capacity (T := T) hK hKN le_rfl)

/-! ### The asymptotic capacity `C_∞(N, K, T)` -/

abbrev asympSet (N K T : ℕ) : Set ℝ :=
  { c : ℝ | ∃ M : ℕ, 1 ≤ M ∧ c = mdsTPirCapacity N K T M }

theorem asympSet_nonempty (N K T : ℕ) : (asympSet N K T).Nonempty :=
  ⟨_, 1, le_rfl, rfl⟩

theorem asympSet_bddBelow {N K T : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    BddBelow (asympSet N K T) := by
  refine ⟨0, ?_⟩
  rintro c ⟨M, hM, rfl⟩
  exact le_trans (by positivity) (inv_M_le_capacity hK hKN hM)

theorem asymp_le_capacity {N K T M : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) (hM : 1 ≤ M) :
    mdsTPirAsympCapacity N K T ≤ mdsTPirCapacity N K T M :=
  csInf_le (asympSet_bddBelow hK hKN) ⟨M, hM, rfl⟩

theorem asympCapacity_mem_Icc {N K T : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    0 ≤ mdsTPirAsympCapacity N K T ∧ mdsTPirAsympCapacity N K T ≤ 1 := by
  refine ⟨le_csInf (asympSet_nonempty N K T) ?_, ?_⟩
  · rintro c ⟨M, hM, rfl⟩
    exact le_trans (by positivity) (inv_M_le_capacity hK hKN hM)
  · exact (asymp_le_capacity hK hKN le_rfl).trans (capacity_le_one hK hKN le_rfl)

/-- Under the hypotheses of `Statement`, `K ≤ N`, so all the above applies. -/
theorem statement_hyps_K_le_N {N K T : ℕ} (hT : 1 ≤ T) (h : K + T - 1 < N) : K ≤ N := by
  omega

end InfoTheory.Known.Certificates.PirCodedCollusionCapacity
