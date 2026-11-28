import InfoTheory.Problems.CodedCachingExactTradeoff

/-!
# Certificate for `InfoTheory.Problems.CodedCachingExactTradeoff`

The frozen statement asks whether, for `N ≥ K ≥ 2` and `M = tN/K` (`1 ≤ t ≤ K`), the exact
coded-placement optimal rate `codedCachingOptimalRate N K M` (an `sInf` of zero-error achievable
rates) equals the Maddah-Ali–Niesen value `(K - t)/(t + 1)`.

Certified here, about the exact objects `IsCodedCachingAchievable` / `codedCachingOptimalRate`
used in `Statement`:
* `achievable_N` — rate `N` (send every file) is achievable at every `M ≥ 0`, so the `sInf` is
  over a nonempty set (`rateSet_nonempty`) bounded below by `0` (`rateSet_bddBelow`): not junk;
* `optimalRate_nonneg`, `optimalRate_le_N` — `0 ≤ R*(N, K, M) ≤ N`;
* `cutset_lower_bound` — the single-user cut-set bound `1 - M/N ≤ R*(N, K, M)` (for `N, K ≥ 1`),
  proved by the zero-error counting argument (cache of user 1 plus the `N` broadcasts for the
  demand vectors `(s, …, s)` determine all `N` files). At `t = K - 1` this gives
  `R* ≥ 1/K = R_MAN`, the matching converse quoted in the problem file;
* `optimalRate_full_memory` — `R*(N, K, N) = 0`, i.e. the `t = K` instance of `Statement` holds;
* `optimalRate_K2_half` — **regression**: `R*(N, 2, N/2) = 1/2` for every `N ≥ 2`
  (Maddah-Ali–Niesen 2014: the explicit XOR scheme with `F = 2` plus the cut-set bound);
* `statement_K_eq_two` — hence the `K = 2` slice of `Statement` holds for all `N ≥ 2`
  (consistent with the solved case `N = K = 2`); this does not touch any `K ≥ 3` instance.

Not certified: the general MAN achievability `R* ≤ (K - t)/(t + 1)` for `K ≥ 3`, the uncoded
placement converse of Yu–Maddah-Ali–Avestimehr, Tian's computer-aided results for `(3, 3)`, and
the factor-2 bound. The `Statement` itself (all `K ≥ 3`) is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.CodedCachingExactTradeoff

open InfoTheory InfoTheory.Problems.CodedCachingExactTradeoff

theorem log2_two_pow (k : ℕ) : log2 ((2 : ℝ) ^ k) = k := by
  unfold log2
  rw [Real.log_pow]
  have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp

theorem log2_le_log2 {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx h) (Real.log_pos one_lt_two).le

theorem log2_mul' {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log2 (x * y) = log2 x + log2 y := by
  unfold log2; rw [Real.log_mul hx.ne' hy.ne', add_div]

theorem log2_pow' {x : ℝ} (n : ℕ) : log2 (x ^ n) = n * log2 x := by
  unfold log2; rw [Real.log_pow, mul_div_assoc]

theorem log2_one' : log2 1 = 0 := by simp [log2]

/-- A fixed scheme over finite cache/broadcast alphabets (types) at one file size `F`
    witnesses achievability. -/
theorem achievable_of_scheme {N K : ℕ} {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (F : ℕ) (hF : 0 < F)
    (Cty Bty : Type) [Fintype Cty] [Fintype Bty] [Nonempty Cty] [Nonempty Bty]
    (hC : log2 (Fintype.card Cty : ℝ) ≤ M * F) (hB : log2 (Fintype.card Bty : ℝ) ≤ R * F)
    (place : Fin K → (Fin N → Fin F → Bool) → Cty)
    (deliver : (Fin K → Fin N) → (Fin N → Fin F → Bool) → Bty)
    (dec : Fin K → (Fin K → Fin N) → Cty → Bty → (Fin F → Bool))
    (hdec : ∀ d W k, dec k d (place k W) (deliver d W) = W (d k)) :
    IsCodedCachingAchievable N K M R := by
  refine ⟨hM, hR, fun ε hε => ?_⟩
  let eC := Fintype.equivFin Cty
  let eB := Fintype.equivFin Bty
  have hFε : 0 ≤ ε * (F : ℝ) := by positivity
  refine ⟨F, Fintype.card Cty, Fintype.card Bty, hF, Fintype.card_pos, Fintype.card_pos,
    by nlinarith, by nlinarith, fun k W => eC (place k W), fun d W => eB (deliver d W),
    fun k d c b => dec k d (eC.symm c) (eB.symm b), ?_⟩
  intro d W k
  simp [hdec]

/-- Rate `N` (broadcast all files uncoded, empty caches) is achievable at every `M ≥ 0`. -/
theorem achievable_N (N K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    IsCodedCachingAchievable N K M N := by
  refine achievable_of_scheme hM (Nat.cast_nonneg N) 1 one_pos Unit (Fin N → Fin 1 → Bool)
    ?_ ?_ (fun _ _ => ()) (fun _ W => W) (fun k d _ W => W (d k)) (fun _ _ _ => rfl)
  · simp [log2_one', hM]
  · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    rw [log2_two_pow]; simp

/-- The set whose `sInf` is `codedCachingOptimalRate N K M`. -/
abbrev rateSet (N K : ℕ) (M : ℝ) : Set ℝ := { R : ℝ | IsCodedCachingAchievable N K M R }

theorem rateSet_nonempty (N K : ℕ) {M : ℝ} (hM : 0 ≤ M) : (rateSet N K M).Nonempty :=
  ⟨_, achievable_N N K hM⟩

theorem rateSet_bddBelow (N K : ℕ) (M : ℝ) : BddBelow (rateSet N K M) :=
  ⟨0, fun _ h => h.2.1⟩

theorem optimalRate_nonneg (N K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ codedCachingOptimalRate N K M :=
  le_csInf (rateSet_nonempty N K hM) (fun _ h => h.2.1)

theorem optimalRate_le_N (N K : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    codedCachingOptimalRate N K M ≤ N :=
  csInf_le (rateSet_bddBelow N K M) (achievable_N N K hM)

/-- Single-user cut-set bound, for one achievable rate: `N - M ≤ N R`. -/
theorem cutset_of_achievable {N K : ℕ} {M R : ℝ} (hK : 1 ≤ K)
    (h : IsCodedCachingAchievable N K M R) : (N : ℝ) - M ≤ N * R := by
  obtain ⟨hM, hR, hach⟩ := h
  have key : ∀ ε : ℝ, 0 < ε → (N : ℝ) - M ≤ N * R + ((N : ℝ) + 1) * ε := by
    intro ε hε
    obtain ⟨F, C, B, hF, hC, hB, hlogC, hlogB, place, deliver, dec, hdec⟩ := hach ε hε
    let k0 : Fin K := ⟨0, hK⟩
    let Φ : (Fin N → Fin F → Bool) → Fin C × (Fin N → Fin B) :=
      fun W => (place k0 W, fun s => deliver (fun _ => s) W)
    have hΦ : Function.Injective Φ := by
      intro W W' hWW
      simp only [Φ, Prod.mk.injEq] at hWW
      obtain ⟨h1, h2⟩ := hWW
      funext s
      have e1 := hdec (fun _ => s) W k0
      have e2 := hdec (fun _ => s) W' k0
      rw [h1, congrFun h2 s] at e1
      exact e1.symm.trans e2
    have hcard := Fintype.card_le_of_injective Φ hΦ
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Fintype.card_prod]
      at hcard
    have hcardR : ((2 : ℝ) ^ F) ^ N ≤ (C : ℝ) * (B : ℝ) ^ N := by exact_mod_cast hcard
    have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
    have hlog := log2_le_log2 (by positivity) hcardR
    rw [← pow_mul, log2_two_pow, log2_mul' hCpos (by positivity), log2_pow'] at hlog
    have hFpos : (0 : ℝ) < F := by exact_mod_cast hF
    push_cast at hlog
    -- `F N ≤ (M + ε) F + N (R + ε) F`
    have h3 : (F : ℝ) * N ≤ (M + ε) * F + N * ((R + ε) * F) := by
      have := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      linarith
    have h4 : ((N : ℝ) - M - N * R - ((N : ℝ) + 1) * ε) * F ≤ 0 := by nlinarith
    have := nonpos_of_mul_nonpos_left h4 hFpos
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have := key (δ / ((N : ℝ) + 1)) (div_pos hδ hN1)
  rwa [mul_div_cancel₀ _ hN1.ne'] at this

/-- **Single-user cut-set bound** `R*(N, K, M) ≥ 1 - M/N` (zero-error counting form). -/
theorem cutset_lower_bound {N K : ℕ} {M : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) (hM : 0 ≤ M) :
    1 - M / N ≤ codedCachingOptimalRate N K M := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine le_csInf (rateSet_nonempty N K hM) fun R hR => ?_
  have := cutset_of_achievable hK hR
  have h2 : (N : ℝ) * (1 - M / N) ≤ N * R := by
    rw [mul_sub, mul_div_cancel₀ _ hNpos.ne']; linarith
  exact le_of_mul_le_mul_left h2 hNpos

/-- `t = K`: with `M = N` every user caches everything, `R* = 0`. -/
theorem optimalRate_full_memory (N K : ℕ) : codedCachingOptimalRate N K N = 0 := by
  refine le_antisymm (csInf_le (rateSet_bddBelow N K N) ?_)
    (optimalRate_nonneg N K (Nat.cast_nonneg N))
  refine achievable_of_scheme (Nat.cast_nonneg N) le_rfl 1 one_pos (Fin N → Fin 1 → Bool) Unit
    ?_ ?_ (fun _ W => W) (fun _ _ => ()) (fun k d W _ => W (d k)) (fun _ _ _ => rfl)
  · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    rw [log2_two_pow]; simp
  · simp [log2_one']

/-- The Maddah-Ali–Niesen `K = 2`, `t = 1` scheme: `F = 2`, user `k` caches bit `k` of every
    file, the server broadcasts `W_{d₀}[1] ⊕ W_{d₁}[0]`. -/
theorem achievable_K2_half (N : ℕ) :
    IsCodedCachingAchievable N 2 ((N : ℝ) / 2) (1 / 2) := by
  refine achievable_of_scheme (by positivity) (by norm_num) 2 two_pos (Fin N → Bool) Bool
    ?_ ?_ (fun k W j => W j k) (fun d W => xor (W (d 0) 1) (W (d 1) 0))
    (fun k d c b i => if i = k then c (d k) else xor b (c (d i))) ?_
  · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    push_cast
    rw [log2_two_pow]; push_cast; linarith
  · simp only [Fintype.card_bool]
    push_cast
    have : log2 (2 : ℝ) = 1 := by simpa using log2_two_pow 1
    rw [this]; norm_num
  · intro d W k
    funext i
    fin_cases k <;> fin_cases i <;> simp <;> cases W (d 0) 1 <;> cases W (d 1) 0 <;> simp

/-- **Regression (Maddah-Ali–Niesen 2014):** `R*(N, 2, N/2) = 1/2` for every `N ≥ 2`. -/
theorem optimalRate_K2_half {N : ℕ} (hN : 2 ≤ N) :
    codedCachingOptimalRate N 2 ((N : ℝ) / 2) = 1 / 2 := by
  refine le_antisymm (csInf_le (rateSet_bddBelow _ _ _) (achievable_K2_half N)) ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have := cutset_lower_bound (N := N) (K := 2) (M := (N : ℝ) / 2) (by omega) (by norm_num)
    (by positivity)
  have e : (N : ℝ) / 2 / N = 1 / 2 := by field_simp
  rw [e] at this
  linarith

/-- The `K = 2` slice of `Statement` holds (both `t = 1` and `t = 2`). -/
theorem statement_K_eq_two : ∀ N t : ℕ, 2 ≤ N → 1 ≤ t → t ≤ 2 →
    codedCachingOptimalRate N 2 ((t : ℝ) * (N : ℝ) / (2 : ℕ)) =
      ((2 - t : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) := by
  intro N t hN ht1 ht2
  interval_cases t
  · have e : ((1 : ℕ) : ℝ) * (N : ℝ) / ((2 : ℕ) : ℝ) = (N : ℝ) / 2 := by push_cast; ring
    rw [e, optimalRate_K2_half hN]; norm_num
  · have e : ((2 : ℕ) : ℝ) * (N : ℝ) / ((2 : ℕ) : ℝ) = (N : ℝ) := by push_cast; field_simp
    rw [e, optimalRate_full_memory]; norm_num

/-- The `t = K` instances of `Statement` hold. -/
theorem statement_t_eq_K (N K : ℕ) (hK : 1 ≤ K) :
    codedCachingOptimalRate N K ((K : ℝ) * (N : ℝ) / (K : ℝ)) =
      ((K - K : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
  have hKpos : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  rw [mul_div_cancel_left₀ _ hKpos, optimalRate_full_memory]; simp

end InfoTheory.Known.Certificates.CodedCachingExactTradeoff
