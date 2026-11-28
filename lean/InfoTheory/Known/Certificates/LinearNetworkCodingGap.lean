import InfoTheory.Problems.LinearNetworkCodingGap

/-!
# Certificate for `InfoTheory.Problems.LinearNetworkCodingGap`

The frozen statement asks whether, for every `ε > 0`, there are arbitrarily large DAG
multiple-unicast networks on `V` vertices with `0 < C_nl` and `V^(1-ε) · C_lin ≤ C_nl`, where
`C_nl = dagNonlinearCapacity` and `C_lin = dagLinearCapacity` are `sSup`s. A junk value
`C_lin = 0` (from an empty or unbounded set) would make the inequality trivial. Certified here,
about these exact objects:

* **no junk** — both defining sets always contain `0`, and whenever some session has
  `src ≠ dst` both are bounded by the in-degree cut at that sink:
  - `nonlinear_le_indeg`: `C_nl ≤ indeg(dst i)` (the sink must recover `2^{tλ}` messages from
    `indeg · t` received bits; uses that inactive edges carry `0`);
  - `linear_le_indeg`: `C_lin ≤ indeg(dst i)` over **every** finite field (the counting bound
    `|F|^k ≤ |F|^{t · indeg}`, `|F| ≥ 2`);
  - `nonlinear_nonneg`, `linear_nonneg`.
* **regression** (single unicast on one edge, where linear coding — indeed routing — is
  optimal and both capacities equal the min-cut `1`): on `singleEdge` (vertices `0 → 1`, one
  session `0 → 1`), `nonlinear_singleEdge : C_nl = 1` and `linear_singleEdge : C_lin = 1`
  (a scalar `𝔽₂` code); `singleEdge_not_witness` records that it never witnesses the
  `Statement` inequality for `ε < 1`.

Not certified: `C_lin ≤ C_nl` in general (simulating an `F`-linear code by binary alphabets
when `|F|` is not a power of two), the Dougherty–Freiling–Zeger `10/11` gap, and the
Blasiak–Kleinberg–Lubetzky polynomial separation. The `Statement` is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.LinearNetworkCodingGap

open InfoTheory InfoTheory.Problems.LinearNetworkCodingGap

/-- Number of active edges into `d`. -/
def indeg {V : ℕ} (net : DAGNetwork V) (d : Fin V) : ℕ :=
  (Finset.univ.filter (fun w : Fin V => w.1 < d.1 ∧ net.adj w d = true)).card

/-- The set whose `sSup` is `C_nl`. -/
def nlSet {V : ℕ} (net : DAGNetwork V) : Set ℝ :=
  { lam : ℝ | 0 ≤ lam ∧
    ∃ (t M : ℕ), 0 < t ∧ 0 < M ∧ (2 : ℝ) ^ ((t : ℝ) * lam) ≤ (M : ℝ) ∧
      ∃ edgeVal : (Fin net.numSessions → Fin M) → Fin V → Fin V → Fin (2 ^ t),
        (∀ msg u v, ¬ (u.1 < v.1 ∧ net.adj u v = true) → (edgeVal msg u v).1 = 0) ∧
        (∀ msg₁ msg₂ u,
          (∀ w : Fin V, edgeVal msg₁ w u = edgeVal msg₂ w u) →
          (∀ i : Fin net.numSessions, net.src i = u → msg₁ i = msg₂ i) →
          ∀ v : Fin V, edgeVal msg₁ u v = edgeVal msg₂ u v) ∧
        (∀ i : Fin net.numSessions, ∀ msg₁ msg₂,
          (∀ w : Fin V, edgeVal msg₁ w (net.dst i) = edgeVal msg₂ w (net.dst i)) →
          (∀ j : Fin net.numSessions, net.src j = net.dst i → msg₁ j = msg₂ j) →
          msg₁ i = msg₂ i) }

theorem nonlinear_eq {V : ℕ} (net : DAGNetwork V) : dagNonlinearCapacity net = sSup (nlSet net) :=
  rfl

theorem nlSet_zero_mem {V : ℕ} (net : DAGNetwork V) : (0 : ℝ) ∈ nlSet net :=
  ⟨le_rfl, 1, 1, one_pos, one_pos, by simp, fun _ _ _ => ⟨0, by positivity⟩,
    fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem nlSet_bdd {V : ℕ} (net : DAGNetwork V) (i : Fin net.numSessions)
    (hne : net.src i ≠ net.dst i) : ∀ lam ∈ nlSet net, lam ≤ indeg net (net.dst i) := by
  rintro lam ⟨-, t, M, ht, hM0, hpow, edgeVal, hinact, -, hdec⟩
  set d := net.dst i
  let S := {w : Fin V // w.1 < d.1 ∧ net.adj w d = true}
  let emb : Fin M → (Fin net.numSessions → Fin M) := fun a j => if j = i then a else ⟨0, hM0⟩
  let f : Fin M → (S → Fin (2 ^ t)) := fun a w => edgeVal (emb a) w.1 d
  have hinj : Function.Injective f := by
    intro a b hab
    have hedge : ∀ w, edgeVal (emb a) w d = edgeVal (emb b) w d := by
      intro w
      by_cases hw : w.1 < d.1 ∧ net.adj w d = true
      · exact congrFun hab ⟨w, hw⟩
      · exact Fin.ext (by rw [hinact _ _ _ hw, hinact _ _ _ hw])
    have hsrc : ∀ j, net.src j = d → emb a j = emb b j := by
      intro j hj
      by_cases hji : j = i
      · subst hji; exact absurd hj hne
      · simp [emb, hji]
    simpa [emb] using hdec i (emb a) (emb b) hedge hsrc
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_fun] at hcard
  have hS : Fintype.card S = indeg net d := by
    simp [S, indeg, Fintype.card_subtype]
  rw [hS, ← pow_mul] at hcard
  have hR : (2 : ℝ) ^ ((t : ℝ) * lam) ≤ (2 : ℝ) ^ ((t : ℝ) * (indeg net d : ℝ)) := by
    refine le_trans hpow ?_
    have : (M : ℝ) ≤ ((2 ^ (t * indeg net d) : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_pow, ← Real.rpow_natCast] at this
    convert this using 2; push_cast; ring
  rw [Real.rpow_le_rpow_left_iff one_lt_two] at hR
  exact le_of_mul_le_mul_left hR (by exact_mod_cast ht)

/-- In-degree cut bound: `C_nl ≤ indeg(dst i)` for any session with `src i ≠ dst i`. -/
theorem nonlinear_le_indeg {V : ℕ} (net : DAGNetwork V) (i : Fin net.numSessions)
    (hne : net.src i ≠ net.dst i) : dagNonlinearCapacity net ≤ indeg net (net.dst i) :=
  csSup_le ⟨0, nlSet_zero_mem net⟩ (nlSet_bdd net i hne)

theorem nonlinear_nonneg {V : ℕ} (net : DAGNetwork V) (i : Fin net.numSessions)
    (hne : net.src i ≠ net.dst i) : 0 ≤ dagNonlinearCapacity net :=
  le_csSup ⟨_, nlSet_bdd net i hne⟩ (nlSet_zero_mem net)

/-! ### Linear side -/

/-- The set whose `sSup` is `C_lin`. -/
def linSet {V : ℕ} (net : DAGNetwork V) : Set ℝ :=
  { lam : ℝ | ∃ (F : Type) (hF : Field F) (hFin : Fintype F), @HasLinearDAGRate F hF hFin V net lam }

theorem linear_eq {V : ℕ} (net : DAGNetwork V) : dagLinearCapacity net = sSup (linSet net) :=
  rfl

theorem linSet_zero_mem {V : ℕ} (net : DAGNetwork V) : (0 : ℝ) ∈ linSet net := by
  refine ⟨ZMod 2, inferInstance, inferInstance, le_rfl, 1, 0, one_pos, by simp, 0, ?_, ?_, ?_⟩
  · intro _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _; exact Subsingleton.elim _ _

theorem linSet_bdd {V : ℕ} (net : DAGNetwork V) (i : Fin net.numSessions)
    (hne : net.src i ≠ net.dst i) : ∀ lam ∈ linSet net, lam ≤ indeg net (net.dst i) := by
  rintro lam ⟨F, hF, hFin, -, t, k, ht, hk, edgeVal, hinact, -, hdec⟩
  let _ := hF; let _ := hFin
  set d := net.dst i
  let S := {w : Fin V // w.1 < d.1 ∧ net.adj w d = true}
  let emb : (Fin k → F) → (Fin net.numSessions → Fin k → F) := fun a j => if j = i then a else 0
  let f : (Fin k → F) → (S → Fin t → F) := fun a w => edgeVal (emb a) w.1 d
  have hinj : Function.Injective f := by
    intro a b hab
    have hedge : ∀ w, edgeVal (emb a) w d = edgeVal (emb b) w d := by
      intro w
      by_cases hw : w.1 < d.1 ∧ net.adj w d = true
      · exact congrFun hab ⟨w, hw⟩
      · rw [hinact _ _ _ hw, hinact _ _ _ hw]
    have hsrc : ∀ j, net.src j = d → emb a j = emb b j := by
      intro j hj
      by_cases hji : j = i
      · subst hji; exact absurd hj hne
      · simp [emb, hji]
    simpa [emb] using hdec i (emb a) (emb b) hedge hsrc
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_fun] at hcard
  have hS : Fintype.card S = indeg net d := by
    simp [S, indeg, Fintype.card_subtype]
  rw [hS, ← pow_mul] at hcard
  have hk' : k ≤ t * indeg net d :=
    (Nat.pow_le_pow_iff_right (Fintype.one_lt_card (α := F))).1 hcard
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  refine le_trans hk ?_
  rw [div_le_iff₀ htR]
  have : (k : ℝ) ≤ (t : ℝ) * (indeg net d : ℝ) := by exact_mod_cast hk'
  linarith

/-- In-degree cut bound over every finite field: `C_lin ≤ indeg(dst i)`. -/
theorem linear_le_indeg {V : ℕ} (net : DAGNetwork V) (i : Fin net.numSessions)
    (hne : net.src i ≠ net.dst i) : dagLinearCapacity net ≤ indeg net (net.dst i) :=
  csSup_le ⟨0, linSet_zero_mem net⟩ (linSet_bdd net i hne)

theorem linear_nonneg {V : ℕ} (net : DAGNetwork V) (i : Fin net.numSessions)
    (hne : net.src i ≠ net.dst i) : 0 ≤ dagLinearCapacity net :=
  le_csSup ⟨_, linSet_bdd net i hne⟩ (linSet_zero_mem net)

/-! ### Regression: one edge, one session -/

/-- The DAG `0 → 1` with the single session `0 → 1`. -/
def singleEdge : DAGNetwork 2 where
  adj u v := decide (u = 0 ∧ v = 1)
  numSessions := 1
  src _ := 0
  dst _ := 1

/-- The unique session of `singleEdge`. -/
def s0 : Fin singleEdge.numSessions := ⟨0, Nat.one_pos⟩

theorem singleEdge_ne : singleEdge.src s0 ≠ singleEdge.dst s0 := by decide

theorem indeg_singleEdge : indeg singleEdge (singleEdge.dst s0) = 1 := by decide

theorem nonlinear_singleEdge : dagNonlinearCapacity singleEdge = 1 := by
  have hub := nonlinear_le_indeg singleEdge s0 singleEdge_ne
  rw [indeg_singleEdge] at hub
  refine le_antisymm (by exact_mod_cast hub)
    (le_csSup ⟨_, nlSet_bdd singleEdge s0 singleEdge_ne⟩ ?_)
  refine ⟨zero_le_one, 1, 2, one_pos, two_pos, by norm_num,
    fun msg u v => if u = 0 ∧ v = 1 then ⟨(msg s0).1, by simpa using (msg s0).2⟩ else 0,
    ?_, ?_, ?_⟩
  · intro msg u v h
    by_cases huv : u = 0 ∧ v = 1
    · exact absurd ⟨by rw [huv.1, huv.2]; decide, by simp [singleEdge, huv]⟩ h
    · simp [huv]
  · intro m₁ m₂ u _ hsrc v
    by_cases hu : u = 0
    · subst hu
      have : m₁ s0 = m₂ s0 := hsrc s0 rfl
      simp [this]
    · simp [hu]
  · intro i m₁ m₂ hedge _
    have hi : i = s0 := Fin.ext (by have := i.isLt; change i.1 < 1 at this; change i.1 = 0; omega)
    subst hi
    have h := congrArg Fin.val (hedge 0)
    simp [singleEdge] at h
    exact Fin.ext h

theorem linear_singleEdge : dagLinearCapacity singleEdge = 1 := by
  have hub := linear_le_indeg singleEdge s0 singleEdge_ne
  rw [indeg_singleEdge] at hub
  refine le_antisymm (by exact_mod_cast hub)
    (le_csSup ⟨_, linSet_bdd singleEdge s0 singleEdge_ne⟩ ?_)
  let L : (Fin singleEdge.numSessions → Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → Fin 2 → Fin 1 → ZMod 2) :=
    { toFun := fun msg u v s => if u = 0 ∧ v = 1 then msg s0 s else 0
      map_add' := by
        intro a b; funext u v s; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := by
        intro c a; funext u v s; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  refine ⟨ZMod 2, inferInstance, inferInstance, zero_le_one, 1, 1, one_pos, by norm_num, L,
    ?_, ?_, ?_⟩
  · intro msg u v h
    by_cases huv : u = 0 ∧ v = 1
    · exact absurd ⟨by rw [huv.1, huv.2]; decide, by simp [singleEdge, huv]⟩ h
    · funext s; simp [L, huv]
  · intro m₁ m₂ u _ hsrc v
    by_cases hu : u = 0
    · subst hu
      have : m₁ s0 = m₂ s0 := hsrc s0 rfl
      funext s; simp [L, this]
    · funext s; simp [L, hu]
  · intro i m₁ m₂ hedge _
    have hi : i = s0 := Fin.ext (by have := i.isLt; change i.1 < 1 at this; change i.1 = 0; omega)
    subst hi
    funext s
    have h : (if ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) then m₁ s0 s else 0) =
        (if ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) then m₂ s0 s else 0) := congrFun (hedge 0) s
    simpa using h

/-- On `singleEdge` the gap is `1`, so it never witnesses the `Statement` inequality for
    `ε < 1` (`2^(1-ε) > 1`). -/
theorem singleEdge_not_witness (ε : ℝ) (hε : ε < 1) :
    ¬ ((2 : ℕ) : ℝ) ^ (1 - ε) * dagLinearCapacity singleEdge ≤ dagNonlinearCapacity singleEdge := by
  rw [linear_singleEdge, nonlinear_singleEdge, mul_one, not_le]
  exact Real.one_lt_rpow (by norm_num) (by linarith)

end InfoTheory.Known.Certificates.LinearNetworkCodingGap
