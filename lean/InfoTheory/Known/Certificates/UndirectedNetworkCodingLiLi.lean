import InfoTheory.Problems.UndirectedNetworkCodingLiLi

/-!
# Certificate for `InfoTheory.Problems.UndirectedNetworkCodingLiLi`

The frozen statement (the Li–Li conjecture) asks that `undirectedCodingThroughput net =
undirectedRoutingThroughput net` for every undirected multiple-unicast network with at least
one pair. Both sides are `sSup`s in Core, so the equation could hold through junk values
(`sSup ∅ = sSup (unbounded) = 0`). Certified here, about these exact objects:

* **no junk** — for every network with `numPairs > 0` both defining sets contain `0` and are
  bounded above by an elementary cut bound:
  - `routing_le_srcCut`: `λ_route ≤ ∑ᵤ cap(s₁, u)` (all flow of commodity 1 leaves `s₁`);
  - `coding_le_dstCut`: `λ_code ≤ ∑_w cap(w, t₁)` (the sink `t₁` must recover `2^{Nλ}`
    messages from at most `N · ∑_w cap(w, t₁)` received bits — a counting/injectivity
    argument on the exact Core code model);
  - `routing_nonneg`, `coding_nonneg`.
  So both throughputs are genuine suprema, and the conjecture is not settled by junk.
* **regression** (single unicast, `k = 1`, where max-flow/min-cut settles the conjecture):
  on the single unit edge `singleEdge` (`0 — 1`, one pair `0 → 1`),
  `routing_singleEdge : λ_route = 1`, `coding_singleEdge : λ_code = 1`, and hence
  `liLi_singleEdge`: the conjectured equality holds there with the right value `1`.

Not certified: `λ_route ≤ λ_code` in general (simulating fractional flows by codes needs
rational approximation and rounding), Hu's two-commodity theorem, the `O(log k)` flow–cut gap,
or any instance with a flow–cut gap. The `Statement` itself is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.UndirectedNetworkCodingLiLi

open InfoTheory

/-! ### Routing side -/

theorem routing_set_zero_mem {V : Type*} [Fintype V] (net : UndirectedMultipleUnicast V) :
    (0 : ℝ) ∈ { lam : ℝ | 0 ≤ lam ∧
      ∃ flow : Fin net.numPairs → V → V → ℝ,
        (∀ i u v, 0 ≤ flow i u v) ∧
        (∀ u v, ∑ i : Fin net.numPairs, (flow i u v + flow i v u) ≤ (net.cap u v : ℝ)) ∧
        (∀ i v, v ≠ net.src i → v ≠ net.dst i →
          ∑ u : V, flow i u v = ∑ u : V, flow i v u) ∧
        (∀ i, ∑ u : V, flow i (net.src i) u - ∑ u : V, flow i u (net.src i) = lam) } := by
  refine ⟨le_rfl, fun _ _ _ => 0, fun _ _ _ => le_rfl, fun u v => ?_, fun _ _ _ _ => rfl,
    fun _ => by simp⟩
  simp

theorem routing_set_bdd {V : Type*} [Fintype V] (net : UndirectedMultipleUnicast V)
    (i : Fin net.numPairs) :
    ∀ lam ∈ { lam : ℝ | 0 ≤ lam ∧
      ∃ flow : Fin net.numPairs → V → V → ℝ,
        (∀ i u v, 0 ≤ flow i u v) ∧
        (∀ u v, ∑ i : Fin net.numPairs, (flow i u v + flow i v u) ≤ (net.cap u v : ℝ)) ∧
        (∀ i v, v ≠ net.src i → v ≠ net.dst i →
          ∑ u : V, flow i u v = ∑ u : V, flow i v u) ∧
        (∀ i, ∑ u : V, flow i (net.src i) u - ∑ u : V, flow i u (net.src i) = lam) },
      lam ≤ ∑ u : V, (net.cap (net.src i) u : ℝ) := by
  rintro lam ⟨-, flow, hnn, hcap, -, hnet⟩
  rw [← hnet i]
  have h1 : ∑ u : V, flow i (net.src i) u ≤ ∑ u : V, (net.cap (net.src i) u : ℝ) := by
    refine Finset.sum_le_sum fun u _ => ?_
    refine le_trans ?_ (hcap (net.src i) u)
    have hle : flow i (net.src i) u ≤ flow i (net.src i) u + flow i u (net.src i) :=
      le_add_of_nonneg_right (hnn _ _ _)
    refine le_trans hle ?_
    exact Finset.single_le_sum (f := fun j => flow j (net.src i) u + flow j u (net.src i))
      (fun j _ => add_nonneg (hnn _ _ _) (hnn _ _ _)) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ u : V, flow i u (net.src i) := Finset.sum_nonneg fun u _ => hnn _ _ _
  linarith

/-- Cut bound at the first source: `λ_route ≤ ∑ᵤ cap(s₁, u)`. -/
theorem routing_le_srcCut {V : Type*} [Fintype V] (net : UndirectedMultipleUnicast V)
    (i : Fin net.numPairs) :
    undirectedRoutingThroughput net ≤ ∑ u : V, (net.cap (net.src i) u : ℝ) :=
  csSup_le ⟨0, routing_set_zero_mem net⟩ (routing_set_bdd net i)

theorem routing_nonneg {V : Type*} [Fintype V] (net : UndirectedMultipleUnicast V)
    (hk : 0 < net.numPairs) : 0 ≤ undirectedRoutingThroughput net :=
  le_csSup ⟨_, routing_set_bdd net ⟨0, hk⟩⟩ (routing_set_zero_mem net)

/-! ### Coding side -/

theorem coding_set_zero_mem {V : Type*} [Fintype V] [DecidableEq V]
    (net : UndirectedMultipleUnicast V) :
    (0 : ℝ) ∈ { lam : ℝ | 0 ≤ lam ∧
    ∃ (N T M : ℕ), 0 < N ∧ 0 < T ∧ (M : ℝ) ≥ (2 : ℝ) ^ ((N : ℝ) * lam) ∧
      ∃ (bits : Fin T → V → V → ℕ)
        (edgeVal : (Fin net.numPairs → Fin M) → Fin T → V → V → ℕ),
        (∀ u v, u ≠ v → ∑ t : Fin T, (bits t u v + bits t v u) ≤ N * net.cap u v) ∧
        (∀ t u, bits t u u = 0) ∧
        (∀ msg t u v, edgeVal msg t u v < 2 ^ (bits t u v)) ∧
        (∀ msg₁ msg₂ t u,
          (∀ i : Fin net.numPairs, net.src i = u → msg₁ i = msg₂ i) →
          (∀ (t' : Fin T) (w : V), t'.1 < t.1 → edgeVal msg₁ t' w u = edgeVal msg₂ t' w u) →
          ∀ v : V, edgeVal msg₁ t u v = edgeVal msg₂ t u v) ∧
        (∀ i msg₁ msg₂,
          (∀ j : Fin net.numPairs, net.src j = net.dst i → msg₁ j = msg₂ j) →
          (∀ t w, edgeVal msg₁ t w (net.dst i) = edgeVal msg₂ t w (net.dst i)) →
          msg₁ i = msg₂ i) } := by
  refine ⟨le_rfl, 1, 1, 1, one_pos, one_pos, by simp, fun _ _ _ => 0, fun _ _ _ _ => 0,
    fun _ _ _ => by simp, fun _ _ => rfl, fun _ _ _ _ => by simp, fun _ _ _ _ _ _ _ => rfl,
    fun i m₁ m₂ _ _ => Subsingleton.elim _ _⟩

theorem coding_set_bdd {V : Type*} [Fintype V] [DecidableEq V]
    (net : UndirectedMultipleUnicast V) (i : Fin net.numPairs) :
    ∀ lam ∈ { lam : ℝ | 0 ≤ lam ∧
    ∃ (N T M : ℕ), 0 < N ∧ 0 < T ∧ (M : ℝ) ≥ (2 : ℝ) ^ ((N : ℝ) * lam) ∧
      ∃ (bits : Fin T → V → V → ℕ)
        (edgeVal : (Fin net.numPairs → Fin M) → Fin T → V → V → ℕ),
        (∀ u v, u ≠ v → ∑ t : Fin T, (bits t u v + bits t v u) ≤ N * net.cap u v) ∧
        (∀ t u, bits t u u = 0) ∧
        (∀ msg t u v, edgeVal msg t u v < 2 ^ (bits t u v)) ∧
        (∀ msg₁ msg₂ t u,
          (∀ i : Fin net.numPairs, net.src i = u → msg₁ i = msg₂ i) →
          (∀ (t' : Fin T) (w : V), t'.1 < t.1 → edgeVal msg₁ t' w u = edgeVal msg₂ t' w u) →
          ∀ v : V, edgeVal msg₁ t u v = edgeVal msg₂ t u v) ∧
        (∀ i msg₁ msg₂,
          (∀ j : Fin net.numPairs, net.src j = net.dst i → msg₁ j = msg₂ j) →
          (∀ t w, edgeVal msg₁ t w (net.dst i) = edgeVal msg₂ t w (net.dst i)) →
          msg₁ i = msg₂ i) },
      lam ≤ ∑ w : V, (net.cap w (net.dst i) : ℝ) := by
  rintro lam ⟨hlam, N, T, M, hN, -, hM, bits, edgeVal, hcap, hdiag, hlt, -, hdec⟩
  set d := net.dst i with hd
  have hM1 : (1 : ℝ) ≤ M := le_trans (Real.one_le_rpow one_le_two
    (mul_nonneg (Nat.cast_nonneg _) hlam)) hM
  have hM0 : 0 < M := by exact_mod_cast lt_of_lt_of_le one_pos hM1
  let emb : Fin M → (Fin net.numPairs → Fin M) := fun a j => if j = i then a else ⟨0, hM0⟩
  let f : Fin M → (∀ p : Fin T × V, Fin (2 ^ bits p.1 p.2 d)) :=
    fun a p => ⟨edgeVal (emb a) p.1 p.2 d, hlt _ _ _ _⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hedge : ∀ t w, edgeVal (emb a) t w d = edgeVal (emb b) t w d := by
      intro t w
      have := congrArg Fin.val (congrFun hab (t, w))
      simpa [f] using this
    have hsrc : ∀ j : Fin net.numPairs, net.src j = d → emb a j = emb b j := by
      intro j hj
      by_cases hji : j = i
      · subst hji; exact absurd hj (net.src_ne_dst j)
      · simp [emb, hji]
    have := hdec i (emb a) (emb b) hsrc hedge
    simpa [emb] using this
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_fin, Fintype.card_pi] at hcard
  simp only [Fintype.card_fin] at hcard
  rw [Finset.prod_pow_eq_pow_sum] at hcard
  have hsum : ∑ p : Fin T × V, bits p.1 p.2 d ≤ N * ∑ w : V, net.cap w d := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases hw : w = d
    · subst hw; simp [hdiag]
    · refine le_trans ?_ (hcap w d hw)
      exact Finset.sum_le_sum fun t _ => Nat.le_add_right _ _
  have hMle : M ≤ 2 ^ (N * ∑ w : V, net.cap w d) :=
    le_trans hcard (Nat.pow_le_pow_right two_pos hsum)
  have hMleR : (M : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * ∑ w : V, (net.cap w d : ℝ)) := by
    have : (M : ℝ) ≤ ((2 ^ (N * ∑ w : V, net.cap w d) : ℕ) : ℝ) := by exact_mod_cast hMle
    rw [Nat.cast_pow, ← Real.rpow_natCast] at this
    convert this using 2
    push_cast; ring
  have hexp := le_trans hM hMleR
  rw [Real.rpow_le_rpow_left_iff one_lt_two] at hexp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact le_of_mul_le_mul_left hexp hNpos

/-- Cut bound at the first sink: `λ_code ≤ ∑_w cap(w, t₁)`. -/
theorem coding_le_dstCut {V : Type*} [Fintype V] [DecidableEq V]
    (net : UndirectedMultipleUnicast V) (i : Fin net.numPairs) :
    undirectedCodingThroughput net ≤ ∑ w : V, (net.cap w (net.dst i) : ℝ) :=
  csSup_le ⟨0, coding_set_zero_mem net⟩ (coding_set_bdd net i)

theorem coding_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (net : UndirectedMultipleUnicast V) (hk : 0 < net.numPairs) :
    0 ≤ undirectedCodingThroughput net :=
  le_csSup ⟨_, coding_set_bdd net ⟨0, hk⟩⟩ (coding_set_zero_mem net)

/-! ### Regression: a single unit edge with one unicast pair -/

/-- The single undirected unit edge `0 — 1` with one pair `0 → 1`. -/
def singleEdge : UndirectedMultipleUnicast (Fin 2) where
  cap u v := if u = v then 0 else 1
  symm u v := by fin_cases u <;> fin_cases v <;> rfl
  numPairs := 1
  src _ := 0
  dst _ := 1
  src_ne_dst _ := by decide

/-- The unique pair of `singleEdge`. -/
def pair0 : Fin singleEdge.numPairs := ⟨0, Nat.one_pos⟩

@[simp] theorem singleEdge_numPairs : singleEdge.numPairs = 1 := rfl

theorem pair_eq (i : Fin singleEdge.numPairs) : i = pair0 :=
  Fin.ext (by have := i.isLt; change i.1 < 1 at this; change i.1 = 0; omega)

theorem routing_singleEdge : undirectedRoutingThroughput singleEdge = 1 := by
  have hub := routing_le_srcCut singleEdge pair0
  simp [singleEdge, Fin.sum_univ_two] at hub
  refine le_antisymm hub (le_csSup ⟨_, routing_set_bdd singleEdge pair0⟩ ?_)
  refine ⟨zero_le_one, fun _ u v => if u = 0 ∧ v = 1 then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro _ u v; beta_reduce; split_ifs <;> norm_num
  · intro u v
    fin_cases u <;> fin_cases v <;> simp [singleEdge] <;>
      exact Finset.card_le_one.2 fun a _ b _ => (pair_eq a).trans (pair_eq b).symm
  · intro _ v h0 h1
    fin_cases v
    · exact absurd rfl h0
    · exact absurd rfl h1
  · intro _; simp [singleEdge]

theorem coding_singleEdge : undirectedCodingThroughput singleEdge = 1 := by
  have hub := coding_le_dstCut singleEdge pair0
  simp [singleEdge, Fin.sum_univ_two] at hub
  refine le_antisymm hub (le_csSup ⟨_, coding_set_bdd singleEdge pair0⟩ ?_)
  refine ⟨zero_le_one, 1, 1, 2, one_pos, one_pos, by norm_num,
    fun _ u v => if u = 0 ∧ v = 1 then 1 else 0,
    fun msg _ u v => if u = 0 ∧ v = 1 then (msg pair0).val else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v _
    fin_cases u <;> fin_cases v <;> simp [singleEdge]
  · intro _ u; beta_reduce; split_ifs with h
    · exact absurd (h.1.symm.trans h.2) (by decide)
    · rfl
  · intro msg _ u v
    by_cases h : u = 0 ∧ v = 1
    · simp only [h, and_self, ite_true, pow_one]; exact (msg pair0).isLt
    · simp [h]
  · intro m₁ m₂ t u hsrc _ v
    by_cases hu : u = 0
    · subst hu
      have : m₁ pair0 = m₂ pair0 := hsrc pair0 rfl
      simp [this]
    · simp [hu]
  · intro i m₁ m₂ _ hedge
    have h := hedge 0 0
    rw [pair_eq i]
    simp [singleEdge] at h
    exact Fin.ext h

/-- The Li–Li equality holds on the single-edge network, with the max-flow value `1`. -/
theorem liLi_singleEdge :
    undirectedCodingThroughput singleEdge = undirectedRoutingThroughput singleEdge := by
  rw [coding_singleEdge, routing_singleEdge]

end InfoTheory.Known.Certificates.UndirectedNetworkCodingLiLi
