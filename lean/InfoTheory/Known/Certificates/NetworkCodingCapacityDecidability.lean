import InfoTheory.Problems.NetworkCodingCapacityDecidability

/-!
# Certificate for `InfoTheory.Problems.NetworkCodingCapacityDecidability`

The frozen statement asks for one Turing machine that, on the binary encoding of a
multi-source DAG network `net` (with a non-local demand) and a rational query
`(p / q, 1 / prec)`, halts and answers `true` if `p/q + 1/prec ≤ C_asymp(net)` and `false` if
`C_asymp(net) ≤ p/q − 1/prec` (the standard weak comparison oracle, equivalent to
computability of the real `C_asymp(net)` uniformly in `net`).

## Certified
* `tmOutputs_unique`: a machine halts with at most one output bit, so the two answer clauses
  of the Statement cannot both be met by "outputting both" (the halting state is absorbing,
  `tmRun_halted`).
* `constMachine_outputs`: the machine model is non-vacuous (a two-state machine halts on
  every input and outputs `false`).
* `encNat_append_inj`, `encodeQuery_inj_VK`, `encodeQuery_inj_query`: the instance encoding
  is decodable: the vertex count `V`, the source count `K` and the query `(p, q, prec)` are
  recovered from the bit string (the adjacency/source/demand blocks have lengths fixed by
  `V`, `K`).
* **Regression (point-to-point edge):** for the network `edgeNet` (two vertices, one unit edge
  `0 → 1`, one source at `0` demanded at `1`), `edgeNet_rate_one_achievable` (uncoded
  forwarding: rate `1`, zero error, every blocklength), `edgeNet_converse`
  (every achievable rate is `≤ 1`: a sink seeing `t` bits decodes at most `2^t` messages
  correctly, so the error fraction tends to `1` when `R > 1`), hence
  **`dagAsympCapacity_edgeNet : C_asymp(edgeNet) = 1`**. The capacity object is not junk
  (not `sSup ∅ = 0`, not an unbounded `sSup`), and it gives the max-flow value on the
  simplest instance (Ahlswede–Cai–Li–Yeung 2000).

## Adversarial check (2026-11-27)
The Statement is faithful and open. C. T. Li (IEEE Trans. Inf. Theory 69(6), 2023,
arXiv:2205.11461) proved undecidability of *solvability* of network coding (exact,
zero-error codes of a given rate over some finite alphabet), of conditional information
inequalities and of conditional independence implication; this does not decide whether the
*vanishing-error* capacity `C_asymp` (equivalently, by Yan–Yeung–Zhang 2012, an optimization
over `cl(Γ*_n)`) is a computable function of the network. Kühne–Yashfe's undecidability
concerns vector-linear codes. No 2023–2026 result settling computability of `C_asymp` was
found. The encoding is a finite description (unary/binary blocks), the query is rational,
the capacity is finite under the non-local-demand hypothesis (cut bound), and the weak
comparison formulation is the literature's notion of computability of a real.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.NetworkCodingCapacityDecidability

open InfoTheory InfoTheory.Problems.NetworkCodingCapacityDecidability

/-! ### The machine model -/

theorem tmRun_succ (M : TuringMachine) (n : ℕ) (cfg : TMConfig M) :
    tmRun M (n + 1) cfg = tmStep M (tmRun M n cfg) := rfl

/-- Once halted, a machine stays in the same configuration. -/
theorem tmRun_halted (M : TuringMachine) (cfg : TMConfig M) (s : ℕ)
    (hs : (tmRun M s cfg).state.1 = 0) (k : ℕ) : tmRun M (s + k) cfg = tmRun M s cfg := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, tmRun_succ, ih]
    unfold tmStep
    rw [if_pos hs]

/-- A machine halts with at most one output bit. -/
theorem tmOutputs_unique (M : TuringMachine) (inp : List Bool) :
    tmOutputs M inp true → tmOutputs M inp false → False := by
  rintro ⟨s₁, h₁, t₁⟩ ⟨s₂, h₂, t₂⟩
  rcases le_total s₁ s₂ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [tmRun_halted M _ s₁ h₁ k, t₁] at t₂
    exact Bool.noConfusion t₂
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [tmRun_halted M _ s₂ h₂ k, t₂] at t₁
    exact Bool.noConfusion t₁

/-- A two-state machine that writes `false` and halts. -/
def constMachine : TuringMachine where
  numStates := 2
  hpos := by norm_num
  trans := fun _ _ => (⟨0, by norm_num⟩, false, true)

theorem constMachine_outputs (inp : List Bool) : tmOutputs constMachine inp false :=
  ⟨1, rfl, rfl⟩

/-! ### The encoding is decodable -/

theorem encNat_append_inj {a b : ℕ} {L L' : List Bool}
    (h : encNat a ++ L = encNat b ++ L') : a = b ∧ L = L' := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [encNat] using h
    | succ b => simp [encNat, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [encNat, List.replicate_succ] at h
    | succ b =>
      simp only [encNat, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      have := ih (b := b) (by simpa [encNat] using h)
      exact ⟨by omega, this.2⟩

/-- The encoding determines the number of vertices and of sources. -/
theorem encodeQuery_inj_VK {V K V' K' : ℕ} (net : MultiSourceDAG V K)
    (net' : MultiSourceDAG V' K') (p q r p' q' r' : ℕ)
    (h : encodeQuery net p q r = encodeQuery net' p' q' r') : V = V' ∧ K = K' := by
  unfold encodeQuery at h
  simp only [List.append_assoc] at h
  obtain ⟨hV, h⟩ := encNat_append_inj h
  exact ⟨hV, (encNat_append_inj h).1⟩

/-- For a fixed network, the encoding determines the query `(p, q, prec)`. -/
theorem encodeQuery_inj_query {V K : ℕ} (net : MultiSourceDAG V K) (p q r p' q' r' : ℕ)
    (h : encodeQuery net p q r = encodeQuery net p' q' r') : p = p' ∧ q = q' ∧ r = r' := by
  unfold encodeQuery at h
  simp only [List.append_assoc, List.append_cancel_left_eq] at h
  obtain ⟨hp, h⟩ := encNat_append_inj h
  obtain ⟨hq, h⟩ := encNat_append_inj h
  exact ⟨hp, hq, (encNat_append_inj (L := []) (L' := []) (by simpa using h)).1⟩

/-! ### Regression: a single unit edge has capacity `1` -/

/-- Two vertices, one edge `0 → 1`, one source at `0` demanded at `1`. -/
def edgeNet : MultiSourceDAG 2 1 where
  adj := fun u v => decide (u.1 = 0 ∧ v.1 = 1)
  src := fun _ => 0
  dem := fun v _ => decide (v.1 = 1)

theorem edgeNet_nonlocal : ∃ (v : Fin 2) (i : Fin 1), edgeNet.dem v i = true ∧ edgeNet.src i ≠ v :=
  ⟨1, 0, rfl, by decide⟩

private lemma msgSize_one (t : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((t : ℝ) * 1))) = 2 ^ t := by
  rw [mul_one, Real.rpow_natCast, show ((2 : ℝ) ^ t) = ((2 ^ t : ℕ) : ℝ) by push_cast; rfl,
    Nat.floor_natCast]
  exact Nat.max_eq_right Nat.one_le_two_pow

/-- **Uncoded forwarding achieves rate `1`** (zero error, every blocklength). -/
theorem edgeNet_rate_one_achievable : IsAsympAchievable edgeNet 1 := by
  refine ⟨zero_le_one, fun ε hε => ⟨1, one_pos, fun t _ => ?_⟩⟩
  have hM := msgSize_one t
  dsimp only
  refine ⟨fun msg u v => if u.1 = 0 ∧ v.1 = 1 then ⟨(msg 0).1, by rw [← hM]; exact (msg 0).2⟩
      else ⟨0, Nat.two_pow_pos t⟩,
    fun v i inc msg => ⟨(inc 0).1, by rw [hM]; exact (inc 0).2⟩, ?_, ?_, ?_, ?_⟩
  · intro msg u v huv
    dsimp only
    rw [if_neg]
    rintro ⟨h0, h1⟩
    exact huv ⟨by omega, decide_eq_true ⟨h0, h1⟩⟩
  · intro msg₁ msg₂ u _ hsrc v
    dsimp only
    by_cases h : u.1 = 0 ∧ v.1 = 1
    · rw [if_pos h, if_pos h]
      have : msg₁ 0 = msg₂ 0 := hsrc 0 (Fin.ext (by simp [edgeNet, h.1]))
      rw [this]
    · rw [if_neg h, if_neg h]
  · intro v i inc msg₁ msg₂ _
    rfl
  · rw [Finset.filter_false_of_mem]
    · simp only [Finset.card_empty, Nat.cast_zero, zero_div]
      exact hε.le
    · rintro msg - ⟨v, i, hdem, hne⟩
      apply hne
      have hv : v.1 = 1 := by simpa [edgeNet] using hdem
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      apply Fin.ext
      simp [hv]

/-- **Converse:** every achievable rate on `edgeNet` is at most `1`. -/
theorem edgeNet_converse {R : ℝ} (hR : IsAsympAchievable edgeNet R) : R ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨-, hach⟩ := hR
  obtain ⟨N, -, hN⟩ := hach (1 / 2) (by norm_num)
  set T : ℕ := Nat.ceil (2 / (R - 1)) with hT
  set t : ℕ := max N T with ht
  have hRt : 2 ≤ (t : ℝ) * (R - 1) := by
    have h1 : 2 / (R - 1) ≤ (t : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right N T)
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < R - 1)).1 h1
    linarith
  set M : ℕ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((t : ℝ) * R))) with hMdef
  have code := hN t (le_max_left N T)
  dsimp only at code
  obtain ⟨edgeVal, dec, h1, -, h3, herr⟩ := code
  -- `M ≥ 2^(t+1) + 1`
  have hMbig : 2 ^ (t + 1) + 1 ≤ M := by
    have hpow : (2 : ℝ) ^ ((t : ℝ) * R) = 2 ^ t * (2 : ℝ) ^ ((t : ℝ) * (R - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1; ring
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ ((t : ℝ) * (R - 1)) := by
      calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hRt
    have h2t : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have hfl : 2 ^ (t + 1) + 1 ≤ Nat.floor ((2 : ℝ) ^ ((t : ℝ) * R)) := by
      apply Nat.le_floor
      rw [hpow]
      push_cast
      rw [pow_succ]
      nlinarith
    exact hfl.trans (Nat.le_max_right _ _)
  -- correct messages inject into the `2^t` edge values
  let ok : Finset (Fin 1 → Fin M) := Finset.univ.filter fun msg =>
    dec 1 0 (fun w => edgeVal msg w 1) msg = msg 0
  have hok : ok.card ≤ 2 ^ t := by
    have := Finset.card_le_card_of_injOn (fun msg => edgeVal msg 0 1) (s := ok) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) ?_
    · simpa using this
    intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, ok] at hm₁ hm₂
    have hinc : (fun w => edgeVal m₁ w 1) = (fun w => edgeVal m₂ w 1) := by
      funext w
      by_cases hw : w = 0
      · subst hw; exact heq
      · have hw1 : w = 1 := by omega
        subst hw1
        apply Fin.ext
        rw [h1 m₁ 1 1 (by simp), h1 m₂ 1 1 (by simp)]
    have hdec := h3 1 0 (fun w => edgeVal m₂ w 1) m₁ m₂ (fun j hj => by
      exact absurd hj (by simp [edgeNet]))
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [← hm₁, ← hm₂, hinc, hdec]
  -- every non-erroneous message is correct
  have hsub : (Finset.univ.filter fun msg : Fin 1 → Fin M => ¬ ∃ (v : Fin 2) (i : Fin 1),
      edgeNet.dem v i = true ∧ dec v i (fun w => edgeVal msg w v) msg ≠ msg i) ⊆ ok := by
    intro msg hmsg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and, not_not] at hmsg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ok]
    exact hmsg 1 0 rfl
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun msg : Fin 1 → Fin M => ∃ (v : Fin 2) (i : Fin 1),
      edgeNet.dem v i = true ∧ dec v i (fun w => edgeVal msg w v) msg ≠ msg i)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one] at hcard
  have hneg := (Finset.card_le_card hsub).trans hok
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [pow_one, div_le_iff₀ hMpos] at herr
  have : (M : ℝ) ≤ 2 * 2 ^ t := by
    have : ((Finset.univ.filter fun msg : Fin 1 → Fin M => ∃ (v : Fin 2) (i : Fin 1),
      edgeNet.dem v i = true ∧ dec v i (fun w => edgeVal msg w v) msg ≠ msg i).card : ℝ)
        ≥ M - 2 ^ t := by
      have : ((Finset.univ.filter fun msg : Fin 1 → Fin M => ¬ ∃ (v : Fin 2) (i : Fin 1),
        edgeNet.dem v i = true ∧ dec v i (fun w => edgeVal msg w v) msg ≠ msg i).card : ℝ)
          ≤ 2 ^ t := by exact_mod_cast hneg
      have hc : ((Finset.univ.filter fun msg : Fin 1 → Fin M => ∃ (v : Fin 2) (i : Fin 1),
        edgeNet.dem v i = true ∧ dec v i (fun w => edgeVal msg w v) msg ≠ msg i).card : ℝ) +
          ((Finset.univ.filter fun msg : Fin 1 → Fin M => ¬ ∃ (v : Fin 2) (i : Fin 1),
        edgeNet.dem v i = true ∧ dec v i (fun w => edgeVal msg w v) msg ≠ msg i).card : ℝ)
          = M := by exact_mod_cast hcard
      linarith
    linarith
  have : ((2 ^ (t + 1) + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hMbig
  push_cast at this
  rw [pow_succ] at this
  linarith

/-- **`C_asymp(edgeNet) = 1`**: the capacity of a single unit edge is one bit per use. -/
theorem dagAsympCapacity_edgeNet : dagAsympCapacity edgeNet = 1 := by
  unfold dagAsympCapacity
  apply le_antisymm
  · exact csSup_le ⟨1, edgeNet_rate_one_achievable⟩ fun R hR => edgeNet_converse hR
  · exact le_csSup ⟨1, fun R hR => edgeNet_converse hR⟩ edgeNet_rate_one_achievable

end InfoTheory.Known.Certificates.NetworkCodingCapacityDecidability
