import InfoTheory.Problems.RelayChannel
import InfoTheory.Known
import InfoTheory.Bridge

/-!
# Certificate for `InfoTheory.Problems.RelayChannel`

The frozen statement asks whether, for every finite DM relay channel `W`, the operational
capacity `relayCapacity W` (Core: causal relay functions `X_{r,i} = f_i(Y_r^{i-1})`) equals the
Cover–El Gamal Theorem 7 rate `coverElGamalTheorem7Rate W`.

## Certified (about exactly these objects)
* `relay_err_ge` — a counting converse: for **every** relay code (any causal relay strategy),
  average error `≥ 1 - |Y|ⁿ / M`. It uses the normalisation of causal chains
  (`Known.Operational.sum_causal_prod_eq_one`).
* `le_log2_card_of_isRelayAchievable`, `relayCapacity_le_log2_card` — every achievable rate,
  hence `relayCapacity W`, is `≤ log₂ |Y|`. So the `sSup` defining `relayCapacity` is over a
  set that is bounded above; with `isRelayAchievable_zero` it is also nonempty, and
  `relayCapacity_nonneg` holds.
* `isRelayAchievable_of_direct`, `directChannel_capacity_le_relayCapacity` — the
  point-to-point lower bound (El Gamal–Kim §16.1): if the relay sends a fixed symbol `x_r`,
  every rate below the capacity of the induced DMC `x ↦ p(y | x, x_r)` is achievable, so
  `C(p(y | x, x_r)) ≤ relayCapacity W` for every `x_r` (Shannon's theorem,
  `Bridge.shannon_channel_coding_achievability`).
* `relayCutsetBound_nonneg`, `relayCutsetBound_le_log2_card` — the cutset bound of Core lies in
  `[0, log₂ |Y|]`.
* `coverElGamalTheorem7Rate_nonneg`, `coverElGamalTheorem7Rate_le_log2_card` — the right-hand
  side of the statement lies in `[0, log₂ |Y|]` (for the lower bound take `U` and `Ŷ` constant;
  then the compression penalty `I(Y_r; Ŷ | U, X, X_r, Y)` vanishes,
  `condMutualInfo_eq_zero_of_subsingleton`).

So both sides of the equation are finite reals in `[0, log₂ |Y|]`, and the operational side is
`≥` every fixed-relay direct-link capacity. Neither side is a junk value.

## Not certified
* (Now in `Bridge`, db659ea: the cutset converse `relayCapacity W ≤ relayCutsetBound W`,
  `Bridge.relayCapacity_le_cutsetBound`. It does not bear on the statement below, since on
  the catalog-error channel the cutset bound equals the Lean functional `log₂ 3`.)
* Achievability of `coverElGamalTheorem7Rate` (decode-and-forward / compress-and-forward):
  this needs block-Markov coding, which is not in the library.
* **Frozen `Statement` is false (on paper; catalog error, statement-fix pending).**
  `coverElGamalTheorem7Rate` keeps two of Theorem 7's three constraints and allows an
  arbitrary joint law `P(u, x, x_r)`; on a 4×2→6×2 channel capacity is exactly `3/2` while the
  Lean functional equals `log₂ 3` (`problems/relay-channel.md`, formalization note;
  `attempts/relay-channel/2026-11-26-claude-opus-5-5-thm7-transcription-catalog-error.md`).
  Proving it here as `statement_false` is medium effort (explicit entropies plus a
  multi-letter converse adapting `Bridge.relay_mac_cut_le_sum`). The mathematical problem
  (is the faithful Theorem 7 rate the capacity?) remains open; Zhang 1988 and
  El Gamal–Gohari–Nair 2022 show only that the *cutset bound* is loose.

Sources: Cover–El Gamal, "Capacity theorems for the relay channel", IEEE Trans. IT 1979;
El Gamal–Kim, *Network Information Theory*, Ch. 16.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.RelayChannel

open InfoTheory InfoTheory.Bridge InfoTheory.Known InfoTheory.Known.Operational
open InfoTheory.Problems.RelayChannel

/-! ### Generic counting converse -/

section Counting

/-- **Counting bound on correct decoding**: if each message `m` induces a probability law
    `T m` on `Ω` and the decoder only sees `π ω ∈ Z`, then the total probability of correct
    decoding, summed over messages, is at most `|Z|`. -/
theorem sum_success_le_card {M Ω Z : Type*} [Fintype M] [Fintype Ω] [Fintype Z] [DecidableEq M]
    (T : M → Ω → ℝ) (hT0 : ∀ m ω, 0 ≤ T m ω) (hT1 : ∀ m, ∑ ω, T m ω = 1)
    (π : Ω → Z) (dec : Z → M) :
    ∑ m, ∑ ω, (if dec (π ω) = m then T m ω else 0) ≤ (Fintype.card Z : ℝ) := by
  classical
  rw [Finset.sum_comm]
  have h1 : ∀ ω, ∑ m, (if dec (π ω) = m then T m ω else 0) = T (dec (π ω)) ω := by
    intro ω; rw [Finset.sum_ite_eq]; simp
  simp_rw [h1]
  have h2 : ∀ ω, T (dec (π ω)) ω = ∑ z, if π ω = z then T (dec z) ω else 0 := by
    intro ω; rw [Finset.sum_ite_eq]; simp
  simp_rw [h2]
  rw [Finset.sum_comm]
  calc ∑ z, ∑ ω, (if π ω = z then T (dec z) ω else 0) ≤ ∑ z : Z, ∑ ω, T (dec z) ω := by
        refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun ω _ => ?_
        split_ifs
        · exact le_rfl
        · exact hT0 _ _
    _ = Fintype.card Z := by simp [hT1]

/-- **Counting converse for the average error**: `P_e ≥ 1 - |Z| / M`. -/
theorem err_ge_one_sub_card {Ω Z : Type*} [Fintype Ω] [Fintype Z] {M : ℕ} (hM : 0 < M)
    (T : Fin M → Ω → ℝ) (hT0 : ∀ m ω, 0 ≤ T m ω) (hT1 : ∀ m, ∑ ω, T m ω = 1)
    (π : Ω → Z) (dec : Z → Fin M) :
    1 - (Fintype.card Z : ℝ) / M ≤
      ((1 : ℝ) / (M : ℝ)) * ∑ m, ∑ ω, (if dec (π ω) ≠ m then T m ω else 0) := by
  have hS := sum_success_le_card T hT0 hT1 π dec
  have hsplit : ∀ m, ∑ ω, (if dec (π ω) ≠ m then T m ω else 0) =
      1 - ∑ ω, (if dec (π ω) = m then T m ω else 0) := by
    intro m
    rw [← hT1 m, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : dec (π ω) = m <;> simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [mul_sub, one_div, inv_mul_cancel₀ hMr.ne', ← div_eq_inv_mul]
  have : (∑ m, ∑ ω, (if dec (π ω) = m then T m ω else 0)) / M ≤ (Fintype.card Z : ℝ) / M :=
    div_le_div_of_nonneg_right hS hMr.le
  linarith

lemma natMax_one_floor_ge (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
  set x : ℝ := (2 : ℝ) ^ ((n : ℝ) * R) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : x / 2 ≤ (Nat.floor x : ℝ) := by
    have h1 : x - 1 < (Nat.floor x : ℝ) := Nat.sub_one_lt_floor x
    by_cases hx2 : x < 2
    · have : (1 : ℝ) ≤ (Nat.floor x : ℝ) := by
        exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx1
      linarith
    · push Not at hx2
      linarith
  have : (Nat.floor x : ℝ) ≤ ((Nat.max 1 (Nat.floor x) : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 1 (Nat.floor x)
  linarith

lemma natMax_one_pos (k : ℕ) : 0 < Nat.max 1 k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- **Rate bound from the counting converse**: if codes of size `max 1 ⌊2^{nR}⌋` have error
    at least `1 - Kⁿ / M` and this error can be made `≤ ε` for every `ε > 0` and all large `n`,
    then `R ≤ log₂ K`. -/
theorem rate_le_log2_of_err_ge {R : ℝ} {K : ℕ} (hK : 0 < K) (hR : 0 ≤ R)
    (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      1 - ((K : ℝ) ^ n) / ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ ε) :
    R ≤ log2 K := by
  by_contra hlt
  push Not at hlt
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK2 : (K : ℝ) < (2 : ℝ) ^ R := by
    have e : (2 : ℝ) ^ (log2 (K : ℝ)) = K := by
      unfold log2
      rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne',
        Real.exp_log hKr]
    rw [← e]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  have h2R : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
  set a : ℝ := (K : ℝ) / (2 : ℝ) ^ R with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one h2R]; exact hK2
  have hev : ∀ᶠ n : ℕ in Filter.atTop, a ^ n < 1 / 4 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  obtain ⟨n, hnN, hn⟩ := ((Filter.eventually_ge_atTop N).and hev).exists
  have hc := hN n hnN
  have hM := natMax_one_floor_ge n hR
  set M : ℝ := ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) with hMdef
  have hpow : (2 : ℝ) ^ ((n : ℝ) * R) = ((2 : ℝ) ^ R) ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by positivity
  have hMpos : 0 < M := lt_of_lt_of_le hpos hM
  have hbound : (K : ℝ) ^ n / M ≤ 2 * a ^ n := by
    have hp : (0 : ℝ) < ((2 : ℝ) ^ R) ^ n := by positivity
    calc (K : ℝ) ^ n / M ≤ (K : ℝ) ^ n / ((2 : ℝ) ^ ((n : ℝ) * R) / 2) :=
          div_le_div_of_nonneg_left (by positivity) hpos hM
      _ = 2 * a ^ n := by rw [hpow, ha, div_pow]; field_simp
  linarith

end Counting

variable {X Xr Y Yr : Type*} [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]

/-! ### Upper bound: `relayCapacity ≤ log₂ |Y|` -/

/-- **Counting converse for the relay channel**: for every relay code (any causal relay
    strategy) with `M ≥ 1` messages, the average error of `IsRelayAchievable` is at least
    `1 - |Y|ⁿ / M`. -/
theorem relay_err_ge (W : RelayChannel X Xr Y Yr) {n M : ℕ} (hM : 0 < M)
    (enc : Fin M → Fin n → X) (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
    (dec : (Fin n → Y) → Fin M) :
    1 - ((Fintype.card Y : ℝ) ^ n) / M ≤ ((1 : ℝ) / (M : ℝ)) *
      ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
        (if dec y ≠ m then ∏ i : Fin n,
          W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
        else 0) := by
  classical
  let T : Fin M → (Fin n → Yr) × (Fin n → Y) → ℝ := fun m ω => ∏ i : Fin n,
    W.trans (enc m i, relay i (fun j => ω.1 ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (ω.2 i, ω.1 i)
  have hT0 : ∀ m ω, 0 ≤ T m ω := fun m ω => Finset.prod_nonneg fun i _ => W.nonneg _ _
  have hT1 : ∀ m, ∑ ω, T m ω = 1 := by
    intro m
    let e : ((Fin n → Yr) × (Fin n → Y)) ≃ (Fin n → Y × Yr) :=
      { toFun := fun p i => (p.2 i, p.1 i)
        invFun := fun f => (fun i => (f i).2, fun i => (f i).1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.sum_equiv e (T m)
      (fun w => ∏ i : Fin n, W.trans (enc m i,
        relay i (fun j => (w ⟨j.1, Nat.lt_trans j.2 i.2⟩).2)) (w i)) (fun _ => rfl)]
    exact sum_causal_prod_eq_one n
      (fun i h b => W.trans (enc m i, relay i (fun j => (h j).2)) b) (fun i h => W.sum_one _)
  have h := err_ge_one_sub_card hM T hT0 hT1 Prod.snd dec
  rw [Fintype.card_fun, Fintype.card_fin] at h
  push_cast at h
  refine le_of_le_of_eq h ?_
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.sum_prod_type]

/-- Every operationally achievable relay rate satisfies `R ≤ log₂ |Y|`. -/
theorem le_log2_card_of_isRelayAchievable [Nonempty Y] (W : RelayChannel X Xr Y Yr) {R : ℝ}
    (h : IsRelayAchievable W R) : R ≤ log2 (Fintype.card Y) := by
  obtain ⟨hR, h⟩ := h
  refine rate_le_log2_of_err_ge Fintype.card_pos hR fun ε hε => ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, relay, dec, herr⟩ := hN n hn
  exact le_trans (relay_err_ge W (natMax_one_pos _) enc relay dec) herr

theorem isRelayAchievable_bddAbove [Nonempty Y] (W : RelayChannel X Xr Y Yr) :
    BddAbove { R : ℝ | IsRelayAchievable W R } :=
  ⟨_, fun _ hR => le_log2_card_of_isRelayAchievable W hR⟩

/-! ### Lower bound: the direct link with a fixed relay symbol -/

/-- The point-to-point channel `x ↦ p(y | x, x_r)` seen by the destination when the relay
    always sends `x_r`. -/
def directChannel (W : RelayChannel X Xr Y Yr) (xr : Xr) : DMC X Y :=
  marginalFst (dmcPrecomp W (fun x => (x, xr)))

/-- **Fixed-relay achievability** (El Gamal–Kim §16.1): a point-to-point code for the direct
    channel `p(y | x, x_r)` is a relay code whose relay always sends `x_r`. -/
theorem isRelayAchievable_of_direct (W : RelayChannel X Xr Y Yr) (xr : Xr) {R : ℝ}
    (h : IsDmcAchievableRate (directChannel W xr) R) : IsRelayAchievable W R := by
  classical
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, herr⟩ := hN n hn
  refine ⟨enc, fun _ _ => xr, dec, ?_⟩
  exact le_of_eq_of_le (relayIgnoringInput_err (Xr := Xr) (dmcPrecomp W (fun x => (x, xr)))
    enc (fun _ _ => xr) dec) herr

/-- Rate `0` is achievable (nonempty input and relay alphabets). -/
theorem isRelayAchievable_zero [Nonempty X] [Nonempty Xr] (W : RelayChannel X Xr Y Yr) :
    IsRelayAchievable W 0 :=
  isRelayAchievable_of_direct W (Classical.arbitrary Xr) (isDmcAchievableRate_zero _)

theorem relayCapacity_nonneg [Nonempty X] [Nonempty Xr] [Nonempty Y]
    (W : RelayChannel X Xr Y Yr) : 0 ≤ relayCapacity W :=
  le_csSup (isRelayAchievable_bddAbove W) (isRelayAchievable_zero W)

/-- **Counting upper bound**: `relayCapacity W ≤ log₂ |Y|`. -/
theorem relayCapacity_le_log2_card [Nonempty X] [Nonempty Xr] [Nonempty Y]
    (W : RelayChannel X Xr Y Yr) : relayCapacity W ≤ log2 (Fintype.card Y) :=
  csSup_le ⟨0, isRelayAchievable_zero W⟩ fun _ hR => le_log2_card_of_isRelayAchievable W hR

/-- **Point-to-point lower bound** (El Gamal–Kim §16.1): for every relay symbol `x_r`,
    `C(p(y | x, x_r)) ≤ relayCapacity W`. -/
theorem directChannel_capacity_le_relayCapacity [Nonempty X] [Nonempty Y]
    (W : RelayChannel X Xr Y Yr) (xr : Xr) :
    (directChannel W xr).capacity ≤ relayCapacity W := by
  have : Nonempty Xr := ⟨xr⟩
  by_contra hlt
  push Not at hlt
  have h0 := relayCapacity_nonneg W
  set r := (relayCapacity W + (directChannel W xr).capacity) / 2 with hr
  have hach : IsRelayAchievable W r :=
    isRelayAchievable_of_direct W xr
      (shannon_channel_coding_achievability _ r (by rw [hr]; linarith) (by rw [hr]; linarith))
  have := le_csSup (isRelayAchievable_bddAbove W) hach
  change r ≤ relayCapacity W at this
  rw [hr] at this
  linarith

/-! ### The cutset bound and the Theorem 7 rate are finite and nonnegative -/

theorem log2_card_nonneg (α : Type*) [Fintype α] [Nonempty α] :
    0 ≤ log2 (Fintype.card α : ℝ) := by
  unfold log2
  apply div_nonneg _ (Real.log_pos one_lt_two).le
  apply Real.log_nonneg
  exact_mod_cast Fintype.card_pos

theorem relayCutsetBound_nonneg (W : RelayChannel X Xr Y Yr) : 0 ≤ relayCutsetBound W := by
  unfold relayCutsetBound
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨P, rfl⟩ := hr
  exact le_min (condMutualInfo_nonneg _) (mutualInfo_nonneg _)

theorem relayCutsetBound_le_log2_card [Nonempty Y] (W : RelayChannel X Xr Y Yr) :
    relayCutsetBound W ≤ log2 (Fintype.card Y) := by
  unfold relayCutsetBound
  refine Real.sSup_le (fun r hr => ?_) (log2_card_nonneg Y)
  obtain ⟨P, rfl⟩ := hr
  exact min_le_of_right_le ((mutualInfo_le_entropy_snd _).trans (shannonEntropy_le_log2_card _))

/-- Conditional mutual information vanishes when the middle variable is constant. -/
theorem condMutualInfo_eq_zero_of_subsingleton {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Subsingleton β] (P : ProbDist (α × β × γ)) : condMutualInfo P = 0 := by
  classical
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
  · exfalso
    have : ∑ t : α × β × γ, P.pmf t = 0 :=
      Finset.sum_eq_zero fun t _ => (IsEmpty.false t.2.1).elim
    linarith [P.sum_one]
  have hc1 : Function.Injective (fun c : γ => (b₀, c)) := fun x y h => (Prod.mk.inj h).2
  have hc2 : Function.Injective (fun ac : α × γ => (ac.1, b₀, ac.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2
  have h1 : P.map (fun t => (t.2.1, t.2.2)) = (P.map (fun t => t.2.2)).map (fun c => (b₀, c)) := by
    rw [map_comp_eq]
    congr 1
    funext t
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have h2 : shannonEntropy P =
      shannonEntropy ((P.map (fun t => (t.1, t.2.2))).map (fun ac => (ac.1, b₀, ac.2))) := by
    rw [map_comp_eq, ← shannonEntropy_map_equiv (Equiv.refl _) P]
    congr 2
    funext t
    exact Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) rfl)
  unfold condMutualInfo
  dsimp only
  rw [h1, h2, shannonEntropy_map_of_injective _ hc1, shannonEntropy_map_of_injective _ hc2]
  ring

theorem coverElGamalTheorem7Rate_le_log2_card [Nonempty Y] (W : RelayChannel X Xr Y Yr) :
    coverElGamalTheorem7Rate W ≤ log2 (Fintype.card Y) := by
  unfold coverElGamalTheorem7Rate
  refine Real.sSup_le (fun r hr => ?_) (log2_card_nonneg Y)
  obtain ⟨kU, kYh, P, Q, rfl⟩ := hr
  refine min_le_of_right_le ?_
  exact le_trans (sub_le_self _ (condMutualInfo_nonneg _))
    ((mutualInfo_le_entropy_snd _).trans (shannonEntropy_le_log2_card _))

/-- The trivial test channel into `Fin 1`. -/
def trivialTest (α : Type*) [Fintype α] : DMC α (Fin 1) where
  trans _ _ := 1
  nonneg _ _ := zero_le_one
  sum_one _ := by simp

theorem coverElGamalTheorem7Rate_nonneg [Nonempty X] [Nonempty Xr] [Nonempty Y]
    (W : RelayChannel X Xr Y Yr) : 0 ≤ coverElGamalTheorem7Rate W := by
  unfold coverElGamalTheorem7Rate
  refine le_csSup_of_le ⟨log2 (Fintype.card Y), fun r hr => ?_⟩
    ⟨1, 1, ProbDist.uniform, trivialTest _, rfl⟩ ?_
  · obtain ⟨kU, kYh, P, Q, rfl⟩ := hr
    refine min_le_of_right_le ?_
    exact le_trans (sub_le_self _ (condMutualInfo_nonneg _))
      ((mutualInfo_le_entropy_snd _).trans (shannonEntropy_le_log2_card _))
  · refine le_min (add_nonneg (condMutualInfo_nonneg _) (condMutualInfo_nonneg _)) ?_
    rw [condMutualInfo_eq_zero_of_subsingleton, sub_zero]
    exact mutualInfo_nonneg _

end InfoTheory.Known.Certificates.RelayChannel
