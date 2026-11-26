import InfoTheory.Core

/-!
# Known results about zero-error capacity (validation of `InfoTheory.Core.ZeroError`)

Fully proved textbook facts about the project's definitions `indepNumber`, `strongPower`,
`shannonCapacity`, `cycleGraph`, `lovaszTheta`, `spernerCapacity` and
`zeroErrorAdderMACSumCapacity`.
-/

open scoped BigOperators

namespace InfoTheory.Known

open InfoTheory

/-! ## Decidability instances (for kernel `decide` on small graphs) -/

scoped instance cycleGraph_decAdj (m : ℕ) : DecidableRel (cycleGraph m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (x - y = 1 ∨ y - x = 1)))

scoped instance strongPower_decAdj {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) : DecidableRel (strongPower G k).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ∀ i : Fin k, x i = y i ∨ G.Adj (x i) (y i)))

scoped instance isIndepSet_dec {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Decidable (IsIndepSet G S) :=
  inferInstanceAs (Decidable (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v))

/-! ## Boundedness API for `indepNumber` -/

section Bounded

variable {V : Type*} [Fintype V]

/-- The set whose `sSup` defines `indepNumber` is bounded above by `|V|`. -/
lemma indepNumber_set_bddAbove (G : SimpleGraph V) :
    BddAbove { m : ℕ | ∃ S : Finset V, IsIndepSet G S ∧ S.card = m } :=
  ⟨Fintype.card V, by
    rintro m ⟨S, -, rfl⟩
    exact Finset.card_le_univ S⟩

omit [Fintype V] in
/-- The set whose `sSup` defines `indepNumber` is nonempty (it contains `0`, via `∅`). -/
lemma indepNumber_set_nonempty (G : SimpleGraph V) :
    { m : ℕ | ∃ S : Finset V, IsIndepSet G S ∧ S.card = m }.Nonempty :=
  ⟨0, ∅, fun u hu => by simp at hu, rfl⟩

/-- The independence number is attained: some independent set has exactly `α(G)` elements. -/
theorem exists_indepSet_card_eq_indepNumber (G : SimpleGraph V) :
    ∃ S : Finset V, IsIndepSet G S ∧ S.card = indepNumber G :=
  Nat.sSup_mem (indepNumber_set_nonempty G) (indepNumber_set_bddAbove G)

/-- Every independent set has at most `α(G)` elements. -/
theorem card_le_indepNumber {G : SimpleGraph V} {S : Finset V}
    (h : IsIndepSet G S) : S.card ≤ indepNumber G :=
  le_csSup (indepNumber_set_bddAbove G) ⟨S, h, rfl⟩

/-- `α(G) ≤ |V|`. -/
theorem indepNumber_le_card (G : SimpleGraph V) : indepNumber G ≤ Fintype.card V := by
  obtain ⟨S, -, hS⟩ := exists_indepSet_card_eq_indepNumber G
  rw [← hS]; exact Finset.card_le_univ S

/-- Characterisation: `α(G) ≤ m` iff every independent set has at most `m` elements. -/
theorem indepNumber_le_iff {G : SimpleGraph V} {m : ℕ} :
    indepNumber G ≤ m ↔ ∀ S : Finset V, IsIndepSet G S → S.card ≤ m := by
  constructor
  · intro h S hS; exact (card_le_indepNumber hS).trans h
  · intro h
    obtain ⟨S, hS, hc⟩ := exists_indepSet_card_eq_indepNumber G
    rw [← hc]; exact h S hS

/-- Characterisation: `m ≤ α(G)` iff some independent set has at least `m` elements. -/
theorem le_indepNumber_iff {G : SimpleGraph V} {m : ℕ} :
    m ≤ indepNumber G ↔ ∃ S : Finset V, IsIndepSet G S ∧ m ≤ S.card := by
  constructor
  · intro h
    obtain ⟨S, hS, hc⟩ := exists_indepSet_card_eq_indepNumber G
    exact ⟨S, hS, hc ▸ h⟩
  · rintro ⟨S, hS, hm⟩; exact hm.trans (card_le_indepNumber hS)

/-- A single vertex is independent, so `α(G) ≥ 1` on a nonempty vertex set. -/
theorem one_le_indepNumber [Nonempty V] (G : SimpleGraph V) : 1 ≤ indepNumber G := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  refine le_indepNumber_iff.2 ⟨{v}, ?_, by simp⟩
  intro a ha b hb
  simp only [Finset.mem_singleton] at ha hb
  subst ha hb
  exact G.irrefl

/-- Monotonicity of `α` under maps that reflect adjacency: if `f : V → W` is injective and
`H.Adj (f u) (f v) → G.Adj u v`, then `α(G) ≤ α(H)`. -/
theorem indepNumber_le_of_injective {W : Type*} [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ u v, H.Adj (f u) (f v) → G.Adj u v) : indepNumber G ≤ indepNumber H := by
  classical
  obtain ⟨S, hS, hc⟩ := exists_indepSet_card_eq_indepNumber G
  rw [← hc, ← Finset.card_image_of_injective S hf]
  apply card_le_indepNumber
  intro x hx y hy hxy
  simp only [Finset.mem_image] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact hS u hu v hv (hadj u v hxy)

end Bounded

/-! ## Strong powers -/

section StrongPower

variable {V : Type*} [Fintype V]

/-- `α(G^{⊠k}) ≤ |V|^k`. -/
theorem indepNumber_strongPower_le (G : SimpleGraph V) (k : ℕ) :
    indepNumber (strongPower G k) ≤ Fintype.card V ^ k := by
  simpa [Fintype.card_fun] using indepNumber_le_card (strongPower G k)

/-- `α(G) ≤ α(G^{⊠1})` (the first strong power contains a copy of `G`). -/
theorem indepNumber_le_indepNumber_strongPower_one (G : SimpleGraph V) :
    indepNumber G ≤ indepNumber (strongPower G 1) := by
  refine indepNumber_le_of_injective (fun v => fun _ => v) ?_ ?_
  · intro u v h; exact congrFun h 0
  · intro u v ⟨hne, h⟩
    rcases h 0 with h | h
    · exact absurd (funext fun _ => h) hne
    · exact h

/-- `α(G^{⊠0}) = 1`: the zeroth power is the one-vertex graph. -/
theorem indepNumber_strongPower_zero (G : SimpleGraph V) :
    indepNumber (strongPower G 0) = 1 := by
  refine le_antisymm ?_ (one_le_indepNumber _)
  simpa using indepNumber_le_card (strongPower G 0)

/-- Supermultiplicativity of the independence numbers of strong powers (concatenation of
codes; Shannon 1956): `α(G^{⊠j}) · α(G^{⊠k}) ≤ α(G^{⊠(j+k)})`. -/
theorem indepNumber_strongPower_add_ge (G : SimpleGraph V) (j k : ℕ) :
    indepNumber (strongPower G j) * indepNumber (strongPower G k) ≤
      indepNumber (strongPower G (j + k)) := by
  classical
  obtain ⟨S, hS, hSc⟩ := exists_indepSet_card_eq_indepNumber (strongPower G j)
  obtain ⟨T, hT, hTc⟩ := exists_indepSet_card_eq_indepNumber (strongPower G k)
  let f : (Fin j → V) × (Fin k → V) → (Fin (j + k) → V) := fun p => Fin.append p.1 p.2
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : a = a' := funext fun i => by simpa [f] using congrFun h (Fin.castAdd k i)
    have h2 : b = b' := funext fun i => by simpa [f] using congrFun h (Fin.natAdd j i)
    rw [h1, h2]
  rw [← hSc, ← hTc, ← Finset.card_product, ← Finset.card_image_of_injective _ hf]
  apply card_le_indepNumber
  intro x hx y hy hadj
  simp only [Finset.mem_image, Finset.mem_product] at hx hy
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
  obtain ⟨⟨a', b'⟩, ⟨ha', hb'⟩, rfl⟩ := hy
  obtain ⟨hne, hco⟩ := hadj
  by_cases hab : a = a'
  · subst hab
    have hbb : b ≠ b' := by rintro rfl; exact hne rfl
    exact hT b hb b' hb' ⟨hbb, fun i => by simpa [f] using hco (Fin.natAdd j i)⟩
  · exact hS a ha a' ha' ⟨hab, fun i => by simpa [f] using hco (Fin.castAdd k i)⟩

/-- `α(G)^k ≤ α(G^{⊠k})` (product codes). -/
theorem pow_indepNumber_le_indepNumber_strongPower (G : SimpleGraph V) (k : ℕ) :
    indepNumber G ^ k ≤ indepNumber (strongPower G k) := by
  induction k with
  | zero => simp [indepNumber_strongPower_zero]
  | succ k ih =>
    rw [pow_succ]
    exact (Nat.mul_le_mul ih (indepNumber_le_indepNumber_strongPower_one G)).trans
      (indepNumber_strongPower_add_ge G k 1)

end StrongPower

/-! ## Shannon capacity: boundedness API and basic bounds -/

section Shannon

variable {V : Type*} [Fintype V]

/-- Each term of the Shannon-capacity supremum is at most `|V|`. -/
theorem indepNumber_strongPower_rpow_le_card (G : SimpleGraph V) {k : ℕ} (hk : 0 < k) :
    ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ)) ≤ Fintype.card V := by
  have h1 : (indepNumber (strongPower G k) : ℝ) ≤ (Fintype.card V : ℝ) ^ k := by
    exact_mod_cast indepNumber_strongPower_le G k
  calc _ ≤ ((Fintype.card V : ℝ) ^ k) ^ ((1 : ℝ) / (k : ℝ)) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = _ := by rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) hk.ne'

/-- The set defining `shannonCapacity` is bounded above (by `|V|`). -/
theorem shannonCapacity_set_bddAbove (G : SimpleGraph V) :
    BddAbove { r : ℝ | ∃ k : ℕ, 0 < k ∧
      r = ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ)) } :=
  ⟨Fintype.card V, by
    rintro r ⟨k, hk, rfl⟩
    exact indepNumber_strongPower_rpow_le_card G hk⟩

/-- The set defining `shannonCapacity` is nonempty (the `k = 1` term). -/
theorem shannonCapacity_set_nonempty (G : SimpleGraph V) :
    { r : ℝ | ∃ k : ℕ, 0 < k ∧
      r = ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ)) }.Nonempty :=
  ⟨_, 1, one_pos, rfl⟩

/-- Every term `α(G^{⊠k})^{1/k}` (`k ≥ 1`) is a lower bound for `Θ(G)`. -/
theorem indepNumber_strongPower_rpow_le_shannonCapacity (G : SimpleGraph V) {k : ℕ}
    (hk : 0 < k) :
    ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ)) ≤ shannonCapacity G :=
  le_csSup (shannonCapacity_set_bddAbove G) ⟨k, hk, rfl⟩

/-- `Θ(G) ≤ t` iff every term `α(G^{⊠k})^{1/k}` (`k ≥ 1`) is at most `t`. -/
theorem shannonCapacity_le_iff (G : SimpleGraph V) {t : ℝ} :
    shannonCapacity G ≤ t ↔
      ∀ k : ℕ, 0 < k → ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ)) ≤ t := by
  constructor
  · intro h k hk; exact (indepNumber_strongPower_rpow_le_shannonCapacity G hk).trans h
  · intro h
    refine csSup_le (shannonCapacity_set_nonempty G) ?_
    rintro r ⟨k, hk, rfl⟩
    exact h k hk

/-- `Θ(G) ≤ |V|` (trivial upper bound). -/
theorem shannonCapacity_le_card (G : SimpleGraph V) : shannonCapacity G ≤ Fintype.card V :=
  (shannonCapacity_le_iff G).2 fun _ hk => indepNumber_strongPower_rpow_le_card G hk

/-- `α(G) ≤ Θ(G)` (Shannon 1956; the `k = 1` term). -/
theorem le_shannonCapacity (G : SimpleGraph V) : (indepNumber G : ℝ) ≤ shannonCapacity G := by
  have h := indepNumber_strongPower_rpow_le_shannonCapacity G (k := 1) one_pos
  simp only [Nat.cast_one, div_one, Real.rpow_one] at h
  exact (Nat.cast_le.2 (indepNumber_le_indepNumber_strongPower_one G)).trans h

/-- `0 ≤ Θ(G)`. -/
theorem shannonCapacity_nonneg (G : SimpleGraph V) : 0 ≤ shannonCapacity G :=
  (Nat.cast_nonneg _).trans (le_shannonCapacity G)

/-- `1 ≤ Θ(G)` on a nonempty vertex set. -/
theorem one_le_shannonCapacity [Nonempty V] (G : SimpleGraph V) : 1 ≤ shannonCapacity G :=
  le_trans (by exact_mod_cast one_le_indepNumber G) (le_shannonCapacity G)

end Shannon

/-! ## The pentagon `C₅` (Shannon 1956) -/

/-- `α(C₅) = 2`. -/
theorem indepNumber_cycle5 : indepNumber (cycleGraph 5) = 2 := by
  refine le_antisymm (indepNumber_le_iff.2 (by decide)) (le_indepNumber_iff.2 ⟨{0, 2}, ?_, ?_⟩)
  · decide
  · decide

/-- The code `{(i, 2i mod 5)}` is independent in `C₅ ⊠ C₅`, so `α(C₅^{⊠2}) ≥ 5`
(Shannon 1956). -/
theorem indepNumber_strongPower_cycle5_two_ge :
    5 ≤ indepNumber (strongPower (cycleGraph 5) 2) :=
  le_indepNumber_iff.2 ⟨{![0, 0], ![1, 2], ![2, 4], ![3, 1], ![4, 3]}, by decide, by decide⟩

/-- `√5 ≤ Θ(C₅)` (Shannon 1956). -/
theorem sqrt5_le_shannonCapacity_cycle5 : Real.sqrt 5 ≤ shannonCapacity (cycleGraph 5) := by
  have h := indepNumber_strongPower_rpow_le_shannonCapacity (cycleGraph 5) (k := 2) two_pos
  have h5 : (5 : ℝ) ≤ indepNumber (strongPower (cycleGraph 5) 2) := by
    exact_mod_cast indepNumber_strongPower_cycle5_two_ge
  refine le_trans ?_ h
  rw [Real.sqrt_eq_rpow]
  push_cast
  exact Real.rpow_le_rpow (by norm_num) h5 (by norm_num)

set_option maxRecDepth 100000 in
/-- `α(C₇) = 3`. -/
theorem indepNumber_cycle7 : indepNumber (cycleGraph 7) = 3 := by
  refine le_antisymm (indepNumber_le_iff.2 (by decide)) (le_indepNumber_iff.2 ⟨{0, 2, 4}, ?_, ?_⟩)
  · decide
  · decide

/-! ## The Lovász theta function (Lovász 1979) -/

section Lovasz

variable {V : Type*} [Fintype V]

/-- Bessel's inequality in coordinates: for pairwise-orthogonal unit vectors `u v` (`v ∈ S`),
`∑_{v ∈ S} ⟨c, u v⟩² ≤ ‖c‖²`. -/
theorem bessel_sum_sq_le {ι : Type*} {d : ℕ} (S : Finset ι) (u : ι → Fin d → ℝ)
    (c : Fin d → ℝ) (hu : ∀ v ∈ S, ∑ i, u v i ^ 2 = 1)
    (horth : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ∑ i, u v i * u w i = 0) :
    ∑ v ∈ S, (∑ i, c i * u v i) ^ 2 ≤ ∑ i, c i ^ 2 := by
  classical
  set a : ι → ℝ := fun v => ∑ i, c i * u v i with ha
  set p : Fin d → ℝ := fun i => ∑ v ∈ S, a v * u v i with hp
  have h1 : ∑ i, c i * p i = ∑ v ∈ S, a v ^ 2 := by
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [sq]
    conv_rhs => rw [ha]
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, p i ^ 2 = ∑ v ∈ S, a v ^ 2 := by
    have : ∀ i, p i ^ 2 = ∑ v ∈ S, ∑ w ∈ S, a v * a w * (u v i * u w i) := by
      intro i
      simp only [hp, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by ring
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single v]
    · rw [← Finset.mul_sum]
      have := hu v hv
      simp only [← sq] at this ⊢
      rw [this, mul_one]
    · intro w hw hwv
      rw [← Finset.mul_sum, horth v hv w hw (Ne.symm hwv), mul_zero]
    · intro h; exact absurd hv h
  have h3 : ∀ i, (c i - p i) ^ 2 = c i ^ 2 - 2 * (c i * p i) + p i ^ 2 := fun i => by ring
  have h4 : 0 ≤ ∑ i, (c i - p i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [h3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2] at h4
  linarith

omit [Fintype V] in
/-- If `(u, c)` is an orthonormal representation of `G` with handle `c` and value `t`
(i.e. `1/⟨c,u_v⟩² ≤ t` for all `v`), then every independent set has at most `t` elements
(Lovász 1979, Lemma 3). -/
theorem card_le_of_orthonormalRep [Nonempty V] {G : SimpleGraph V} {d : ℕ}
    {u : V → Fin d → ℝ} {c : Fin d → ℝ} {t : ℝ} (hu : IsOrthonormalRep G d u)
    (hc : ∑ i, c i ^ 2 = 1)
    (ht : ∀ v : V, (∑ i, c i * u v i) ≠ 0 ∧ 1 / (∑ i, c i * u v i) ^ 2 ≤ t)
    {S : Finset V} (hS : IsIndepSet G S) : (S.card : ℝ) ≤ t := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have ht0 : 0 ≤ t := le_trans (by positivity) (ht v₀).2
  have hb := bessel_sum_sq_le S u c (fun v _ => hu.1 v)
    (fun v hv w hw hvw => hu.2 v w hvw (hS v hv w hw))
  rw [hc] at hb
  have hv : ∀ v ∈ S, (1 : ℝ) ≤ t * (∑ i, c i * u v i) ^ 2 := by
    intro v _
    have hpos : 0 < (∑ i, c i * u v i) ^ 2 := by
      have := (ht v).1; positivity
    have := (ht v).2
    rw [div_le_iff₀ hpos] at this
    exact this
  calc (S.card : ℝ) = ∑ v ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ S, t * (∑ i, c i * u v i) ^ 2 := Finset.sum_le_sum hv
    _ = t * ∑ v ∈ S, (∑ i, c i * u v i) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left hb ht0
    _ = t := mul_one t

/-- The set defining `lovaszTheta` is nonempty on a nonempty vertex set: the standard-basis
representation with handle `(1/√n, …, 1/√n)` has value `n = |V|`. -/
theorem lovaszTheta_set_nonempty [Nonempty V] (G : SimpleGraph V) :
    { t : ℝ | ∃ (d : ℕ) (u : V → Fin d → ℝ) (c : Fin d → ℝ),
      IsOrthonormalRep G d u ∧ (∑ i : Fin d, (c i) ^ 2 = 1) ∧
      (∀ v : V, (∑ i : Fin d, c i * u v i) ≠ 0 ∧
        1 / (∑ i : Fin d, c i * u v i) ^ 2 ≤ t) }.Nonempty := by
  classical
  set n := Fintype.card V with hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  let e : V ≃ Fin n := Fintype.equivFin V
  refine ⟨n, n, fun v i => if e v = i then 1 else 0, fun _ => 1 / Real.sqrt n, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro v; simp
  · intro v w hvw _
    have : e v ≠ e w := e.injective.ne hvw
    simp [this]
  · simp only [div_pow, one_pow, Real.sq_sqrt hnpos.le, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro v
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    refine ⟨by simpa using hs, ?_⟩
    rw [div_pow, Real.sq_sqrt hnpos.le]
    simp

omit [Fintype V] in
/-- The set defining `lovaszTheta` is bounded below by `0` on a nonempty vertex set. -/
theorem lovaszTheta_set_bddBelow [Nonempty V] (G : SimpleGraph V) :
    BddBelow { t : ℝ | ∃ (d : ℕ) (u : V → Fin d → ℝ) (c : Fin d → ℝ),
      IsOrthonormalRep G d u ∧ (∑ i : Fin d, (c i) ^ 2 = 1) ∧
      (∀ v : V, (∑ i : Fin d, c i * u v i) ≠ 0 ∧
        1 / (∑ i : Fin d, c i * u v i) ^ 2 ≤ t) } := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  refine ⟨0, ?_⟩
  rintro t ⟨d, u, c, -, -, ht⟩
  exact le_trans (by positivity) (ht v₀).2

/-- `α(G) ≤ ϑ(G)` (Lovász 1979, Lemma 3). -/
theorem indepNumber_le_lovaszTheta [Nonempty V] (G : SimpleGraph V) :
    (indepNumber G : ℝ) ≤ lovaszTheta G := by
  obtain ⟨S, hS, hc⟩ := exists_indepSet_card_eq_indepNumber G
  refine le_csInf (lovaszTheta_set_nonempty G) ?_
  rintro t ⟨d, u, c, hu, hcn, ht⟩
  rw [← hc]
  exact card_le_of_orthonormalRep hu hcn ht hS

/-- Sum over `Fin (d^k)` of a product of coordinates, through `finFunctionFinEquiv`. -/
lemma sum_finFunctionFinEquiv_prod {d k : ℕ} (F : Fin k → Fin d → ℝ) :
    ∑ j : Fin (d ^ k), ∏ i, F i (finFunctionFinEquiv.symm j i) = ∏ i, ∑ l, F i l := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Equiv.sum_comp finFunctionFinEquiv.symm (fun φ => ∏ i, F i (φ i))

omit [Fintype V] in
/-- Tensor powers of orthonormal representations: if `t` is a feasible value for `ϑ(G)` then
`t^k` is a feasible value for `ϑ(G^{⊠k})` (Lovász 1979, Lemma 2). -/
theorem lovaszTheta_feasible_strongPower {G : SimpleGraph V} {t : ℝ} {d : ℕ}
    {u : V → Fin d → ℝ} {c : Fin d → ℝ} (hu : IsOrthonormalRep G d u)
    (hc : ∑ i, c i ^ 2 = 1)
    (ht : ∀ v : V, (∑ i, c i * u v i) ≠ 0 ∧ 1 / (∑ i, c i * u v i) ^ 2 ≤ t) (k : ℕ) :
    ∃ (U : (Fin k → V) → Fin (d ^ k) → ℝ) (C : Fin (d ^ k) → ℝ),
      IsOrthonormalRep (strongPower G k) (d ^ k) U ∧ (∑ j, C j ^ 2 = 1) ∧
      (∀ x, (∑ j, C j * U x j) ≠ 0 ∧ 1 / (∑ j, C j * U x j) ^ 2 ≤ t ^ k) := by
  classical
  let U : (Fin k → V) → Fin (d ^ k) → ℝ :=
    fun x j => ∏ i, u (x i) (finFunctionFinEquiv.symm j i)
  let C : Fin (d ^ k) → ℝ := fun j => ∏ i, c (finFunctionFinEquiv.symm j i)
  have hinner : ∀ x, ∑ j, C j * U x j = ∏ i, ∑ l, c l * u (x i) l := by
    intro x
    simp only [C, U, ← Finset.prod_mul_distrib]
    exact sum_finFunctionFinEquiv_prod (fun i l => c l * u (x i) l)
  refine ⟨U, C, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x
    simp only [U, ← Finset.prod_pow]
    rw [sum_finFunctionFinEquiv_prod (fun i l => u (x i) l ^ 2)]
    simp [hu.1]
  · intro x y hxy hnadj
    simp only [U, ← Finset.prod_mul_distrib]
    rw [sum_finFunctionFinEquiv_prod (fun i l => u (x i) l * u (y i) l)]
    have : ∃ i, x i ≠ y i ∧ ¬ G.Adj (x i) (y i) := by
      by_contra hcon
      push Not at hcon
      exact hnadj ⟨hxy, fun i => by
        by_cases h : x i = y i
        · exact Or.inl h
        · exact Or.inr (hcon i h)⟩
    obtain ⟨i, hi, hni⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hu.2 _ _ hi hni)
  · simp only [C, ← Finset.prod_pow]
    rw [sum_finFunctionFinEquiv_prod (fun i l => c l ^ 2)]
    simp [hc]
  · intro x
    rw [hinner]
    refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => (ht (x i)).1, ?_⟩
    rw [← Finset.prod_pow, one_div, ← Finset.prod_inv_distrib]
    calc ∏ i, ((∑ l, c l * u (x i) l) ^ 2)⁻¹ ≤ ∏ _i : Fin k, t :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => by simpa [one_div] using (ht (x i)).2)
      _ = t ^ k := by simp

/-- `α(G^{⊠k}) ≤ ϑ(G)^k`-type bound: every feasible value `t` of `ϑ(G)` satisfies
`α(G^{⊠k}) ≤ t^k` (Lovász 1979). -/
theorem indepNumber_strongPower_le_of_feasible [Nonempty V] {G : SimpleGraph V} {t : ℝ}
    {d : ℕ} {u : V → Fin d → ℝ} {c : Fin d → ℝ} (hu : IsOrthonormalRep G d u)
    (hc : ∑ i, c i ^ 2 = 1)
    (ht : ∀ v : V, (∑ i, c i * u v i) ≠ 0 ∧ 1 / (∑ i, c i * u v i) ^ 2 ≤ t) (k : ℕ) :
    (indepNumber (strongPower G k) : ℝ) ≤ t ^ k := by
  obtain ⟨U, C, hU, hC, hUC⟩ := lovaszTheta_feasible_strongPower hu hc ht k
  obtain ⟨S, hS, hcard⟩ := exists_indepSet_card_eq_indepNumber (strongPower G k)
  rw [← hcard]
  exact card_le_of_orthonormalRep hU hC hUC hS

/-- Lovász's theorem on a nonempty vertex set; see `shannonCapacity_le_lovaszTheta`. -/
theorem shannonCapacity_le_lovaszTheta_of_nonempty [Nonempty V] (G : SimpleGraph V) :
    shannonCapacity G ≤ lovaszTheta G := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  refine (shannonCapacity_le_iff G).2 fun k hk => ?_
  refine le_csInf (lovaszTheta_set_nonempty G) ?_
  rintro t ⟨d, u, c, hu, hc, ht⟩
  have ht0 : 0 ≤ t := le_trans (by positivity) (ht v₀).2
  have h := indepNumber_strongPower_le_of_feasible hu hc ht k
  calc ((indepNumber (strongPower G k) : ℝ)) ^ ((1 : ℝ) / (k : ℝ))
      ≤ (t ^ k) ^ ((1 : ℝ) / (k : ℝ)) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = t := by rw [one_div]; exact Real.pow_rpow_inv_natCast ht0 hk.ne'

/-- On an empty vertex set, `ϑ(G) = 0` (the defining set is all of `ℝ`, and the project's
`sInf` of an unbounded-below set is `0`). -/
theorem lovaszTheta_of_isEmpty [IsEmpty V] (G : SimpleGraph V) : lovaszTheta G = 0 := by
  have : { t : ℝ | ∃ (d : ℕ) (u : V → Fin d → ℝ) (c : Fin d → ℝ),
      IsOrthonormalRep G d u ∧ (∑ i : Fin d, (c i) ^ 2 = 1) ∧
      (∀ v : V, (∑ i : Fin d, c i * u v i) ≠ 0 ∧
        1 / (∑ i : Fin d, c i * u v i) ^ 2 ≤ t) } = Set.univ := by
    refine Set.eq_univ_of_forall fun t => ⟨1, fun v => isEmptyElim v, fun _ => 1,
      ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩, by simp, fun v => isEmptyElim v⟩
  rw [lovaszTheta, this, Real.sInf_univ]

/-- On an empty vertex set, `Θ(G) = 0`. -/
theorem shannonCapacity_of_isEmpty [IsEmpty V] (G : SimpleGraph V) : shannonCapacity G = 0 := by
  refine le_antisymm ((shannonCapacity_le_iff G).2 fun k hk => ?_) (shannonCapacity_nonneg G)
  have h0 : indepNumber (strongPower G k) = 0 := by
    have := indepNumber_strongPower_le G k
    rw [Fintype.card_eq_zero, zero_pow hk.ne'] at this
    omega
  rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity)]

/-- **Lovász's theorem** (Lovász 1979, Theorem 1): `Θ(G) ≤ ϑ(G)`. -/
theorem shannonCapacity_le_lovaszTheta (G : SimpleGraph V) :
    shannonCapacity G ≤ lovaszTheta G := by
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [shannonCapacity_of_isEmpty, lovaszTheta_of_isEmpty]
  · exact shannonCapacity_le_lovaszTheta_of_nonempty G

end Lovasz

/-! ## `Θ(C₅) = √5` (Lovász 1979) -/

/-- Lovász's umbrella: `ϑ(C₅) ≤ √5`. The representation is
`u_a = (s cos(2πa/5), s sin(2πa/5), h)` with `h² = 1/√5`, `s² = 1 - 1/√5`, and handle
`c = (0, 0, 1)` (Lovász 1979, proof of Theorem 2). -/
theorem lovaszTheta_cycle5_le : lovaszTheta (cycleGraph 5) ≤ Real.sqrt 5 := by
  set r5 := Real.sqrt 5 with hr5def
  have hr5 : 0 < r5 := by positivity
  have hr5sq : r5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr5gt1 : 1 < r5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp, hr5def]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set h := Real.sqrt (1 / r5) with hhdef
  set s := Real.sqrt (1 - 1 / r5) with hsdef
  have hhpos : 0 < h := Real.sqrt_pos.2 (by positivity)
  have hh : h ^ 2 = 1 / r5 := Real.sq_sqrt (by positivity)
  have hs : s ^ 2 = 1 - 1 / r5 :=
    Real.sq_sqrt (by rw [sub_nonneg, div_le_one hr5]; exact hr5gt1.le)
  let θ : ZMod 5 → ℝ := fun a => 2 * Real.pi * (a.val : ℝ) / 5
  let u : ZMod 5 → Fin 3 → ℝ := fun a => ![s * Real.cos (θ a), s * Real.sin (θ a), h]
  let c : Fin 3 → ℝ := ![0, 0, 1]
  have hkey : ∀ a b : ZMod 5, a ≠ b → ¬ (cycleGraph 5).Adj a b →
      ((a.val : ℤ) - b.val) ∈ ({2, 3, -2, -3} : Finset ℤ) := by decide
  refine csInf_le (lovaszTheta_set_bddBelow _) ⟨3, u, c, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a
    simp only [u, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [mul_pow, mul_pow, hh, hs]
    nlinarith [Real.sin_sq_add_cos_sq (θ a)]
  · intro a b hab hnadj
    have key := hkey a b hab hnadj
    have hcos : Real.cos (θ a - θ b) = -((1 + r5) / 4) := by
      have e : θ a - θ b = 2 * Real.pi * (((a.val : ℤ) - b.val : ℤ) : ℝ) / 5 := by
        simp only [θ]; push_cast; ring
      rw [e]
      simp only [Finset.mem_insert, Finset.mem_singleton] at key
      rcases key with k | k | k | k <;> rw [k] <;> push_cast
      · rw [show 2 * Real.pi * 2 / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub,
          Real.cos_pi_div_five]
      · rw [show 2 * Real.pi * 3 / 5 = Real.pi / 5 + Real.pi by ring, Real.cos_add_pi,
          Real.cos_pi_div_five]
      · rw [show 2 * Real.pi * (-2) / 5 = -(Real.pi - Real.pi / 5) by ring, Real.cos_neg,
          Real.cos_pi_sub, Real.cos_pi_div_five]
      · rw [show 2 * Real.pi * (-3) / 5 = -(Real.pi / 5 + Real.pi) by ring, Real.cos_neg,
          Real.cos_add_pi, Real.cos_pi_div_five]
    simp only [u, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    calc s * Real.cos (θ a) * (s * Real.cos (θ b)) + s * Real.sin (θ a) * (s * Real.sin (θ b))
          + h * h = s ^ 2 * Real.cos (θ a - θ b) + h ^ 2 := by rw [Real.cos_sub]; ring
      _ = 0 := by
        rw [hcos, hs, hh]
        field_simp
        nlinarith [hr5sq]
  · simp [c, Fin.sum_univ_three]
  · intro a
    have hcu : ∑ i : Fin 3, c i * u a i = h := by
      simp [c, u, Fin.sum_univ_three]
    rw [hcu, hh]
    refine ⟨hhpos.ne', ?_⟩
    rw [one_div_one_div]

/-- `Θ(C₅) = √5` (Lovász 1979, Theorem 2; lower bound Shannon 1956). -/
theorem shannonCapacity_cycle5 : shannonCapacity (cycleGraph 5) = Real.sqrt 5 :=
  le_antisymm ((shannonCapacity_le_lovaszTheta _).trans lovaszTheta_cycle5_le)
    sqrt5_le_shannonCapacity_cycle5

/-- `ϑ(C₅) = √5` (Lovász 1979). -/
theorem lovaszTheta_cycle5 : lovaszTheta (cycleGraph 5) = Real.sqrt 5 :=
  le_antisymm lovaszTheta_cycle5_le
    (sqrt5_le_shannonCapacity_cycle5.trans (shannonCapacity_le_lovaszTheta _))

/-! ## Sperner capacity and the zero-error adder MAC -/

section Log2

private lemma log2_le_log2' {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos one_lt_two).le

private lemma log2_pow' (x : ℝ) (n : ℕ) : log2 (x ^ n) = n * log2 x := by
  simp [log2, Real.log_pow, mul_div_assoc]

private lemma log2_one' : log2 1 = 0 := by simp [log2]

private lemma log2_two' : log2 2 = 1 := div_self (Real.log_pos one_lt_two).ne'

end Log2

section Sperner

variable {V : Type*} [Fintype V]

/-- Every nonempty code of length `k ≥ 1` has rate `log₂|C|/k ≤ log₂|V|`. -/
theorem log2_card_div_le_log2_card {k : ℕ} (hk : 0 < k) {C : Finset (Fin k → V)}
    (hC : C.Nonempty) : log2 (C.card : ℝ) / (k : ℝ) ≤ log2 (Fintype.card V) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcard : (C.card : ℝ) ≤ (Fintype.card V : ℝ) ^ k := by
    have := Finset.card_le_univ C
    simp only [Fintype.card_fun, Fintype.card_fin] at this
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  rw [div_le_iff₀ hkpos, mul_comm, ← log2_pow']
  exact log2_le_log2' hCpos hcard

/-- The set defining `spernerCapacity` is bounded above, by `log₂ |V|`. -/
theorem spernerCapacity_set_bddAbove (D : DiGraph V) :
    BddAbove { r : ℝ | ∃ (k : ℕ) (C : Finset (Fin k → V)),
      0 < k ∧ C.Nonempty ∧ IsSpernerCode D k C ∧ r = log2 (C.card : ℝ) / (k : ℝ) } := by
  refine ⟨log2 (Fintype.card V), ?_⟩
  rintro r ⟨k, C, hk, hC, -, rfl⟩
  exact log2_card_div_le_log2_card hk hC

/-- `Σ(D) ≥ 0` on a nonempty vertex set (a one-word code has rate `0`). -/
theorem spernerCapacity_nonneg [Nonempty V] (D : DiGraph V) : 0 ≤ spernerCapacity D := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  refine le_csSup (spernerCapacity_set_bddAbove D) ⟨1, {fun _ => v}, one_pos, by simp, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · simp [log2_one']

/-- `Σ(D) ≤ log₂ |V|`. -/
theorem spernerCapacity_le_log2_card [Nonempty V] (D : DiGraph V) :
    spernerCapacity D ≤ log2 (Fintype.card V) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  refine csSup_le ⟨_, 1, {fun _ => v}, one_pos, by simp, ?_, rfl⟩ ?_
  · intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · rintro r ⟨k, C, hk, hC, -, rfl⟩
    exact log2_card_div_le_log2_card hk hC

end Sperner

section AdderMAC

/-- The set defining `zeroErrorAdderMACSumCapacity` is bounded above (by `2`). -/
theorem zeroErrorAdderMAC_set_bddAbove :
    BddAbove { r : ℝ | ∃ (n : ℕ) (A B : Finset (Fin n → Fin 2)),
      0 < n ∧ A.Nonempty ∧ B.Nonempty ∧ IsAdderMACCode n A B ∧
      r = (log2 (A.card : ℝ) + log2 (B.card : ℝ)) / (n : ℝ) } := by
  refine ⟨2, ?_⟩
  rintro r ⟨n, A, B, hn, hA, hB, -, rfl⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ X : Finset (Fin n → Fin 2), X.Nonempty → log2 (X.card : ℝ) ≤ n := by
    intro X hX
    have hcard : (X.card : ℝ) ≤ (2 : ℝ) ^ n := by
      have := Finset.card_le_univ X
      simp only [Fintype.card_fun, Fintype.card_fin] at this
      exact_mod_cast this
    have := log2_le_log2' (by exact_mod_cast hX.card_pos) hcard
    rwa [log2_pow', log2_two', mul_one] at this
  rw [div_le_iff₀ hnpos]
  linarith [key A hA, key B hB]

/-- The "silent second user" code pair `A = {0,1}^n`, `B = {0}` is uniquely decodable. -/
theorem isAdderMACCode_silent (n : ℕ) :
    IsAdderMACCode n Finset.univ {fun _ => 0} := by
  intro a₁ _ a₂ _ b₁ hb₁ b₂ hb₂ h
  simp only [Finset.mem_singleton] at hb₁ hb₂
  subst hb₁ hb₂
  exact ⟨funext fun i => Fin.ext (by simpa using h i), rfl⟩

/-- Time sharing with a silent second user: `1 ≤` the zero-error sum capacity of the binary
adder MAC (`A = {0,1}^n`, `B = {0}`). -/
theorem one_le_zeroErrorAdderMACSumCapacity : 1 ≤ zeroErrorAdderMACSumCapacity := by
  refine le_csSup zeroErrorAdderMAC_set_bddAbove
    ⟨1, Finset.univ, {fun _ => 0}, one_pos, Finset.univ_nonempty, by simp,
      isAdderMACCode_silent 1, ?_⟩
  simp [log2_two', log2_one']

/-- The length-2 code pair `A = {00, 11}`, `B = {00, 01, 10}` is uniquely decodable for the
binary adder MAC, so the zero-error sum capacity is at least `(1 + log₂ 3)/2 ≈ 1.29`
(classical construction; cf. Kasami–Lin 1976, van Tilborg). -/
theorem one_add_log2_three_div_two_le_zeroErrorAdderMACSumCapacity :
    (1 + log2 3) / 2 ≤ zeroErrorAdderMACSumCapacity := by
  refine le_csSup zeroErrorAdderMAC_set_bddAbove
    ⟨2, {![0, 0], ![1, 1]}, {![0, 0], ![0, 1], ![1, 0]}, two_pos, by simp, by simp,
      by unfold IsAdderMACCode; decide, ?_⟩
  have hA : ({![0, 0], ![1, 1]} : Finset (Fin 2 → Fin 2)).card = 2 := by decide
  have hB : ({![0, 0], ![0, 1], ![1, 0]} : Finset (Fin 2 → Fin 2)).card = 3 := by decide
  rw [hA, hB]
  norm_num [log2_two']

/-- Counting bound: a uniquely decodable adder-MAC code pair satisfies `|A|·|B| ≤ 3^n`
(the map `(a, b) ↦ a + b ∈ {0,1,2}^n` is injective on `A × B`). -/
theorem card_mul_card_le_of_isAdderMACCode {n : ℕ} {A B : Finset (Fin n → Fin 2)}
    (h : IsAdderMACCode n A B) : A.card * B.card ≤ 3 ^ n := by
  classical
  let f : (Fin n → Fin 2) × (Fin n → Fin 2) → (Fin n → Fin 3) :=
    fun p i => ⟨(p.1 i).1 + (p.2 i).1, by omega⟩
  have hinj : Set.InjOn f (A ×ˢ B : Finset _) := by
    rintro ⟨a₁, b₁⟩ hp ⟨a₂, b₂⟩ hq hfe
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
    obtain ⟨ha, hb⟩ := h a₁ hp.1 a₂ hq.1 b₁ hp.2 b₂ hq.2 fun i => by
      simpa [f] using congrArg Fin.val (congrFun hfe i)
    rw [ha, hb]
  have := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  simpa [Finset.card_product, Fintype.card_fun] using this

/-- Upper bound: the zero-error sum capacity of the binary adder MAC is at most `log₂ 3`
(the output alphabet has three letters). -/
theorem zeroErrorAdderMACSumCapacity_le_log2_three :
    zeroErrorAdderMACSumCapacity ≤ log2 3 := by
  refine csSup_le ⟨_, 1, Finset.univ, {fun _ => 0}, one_pos, Finset.univ_nonempty,
    by simp, isAdderMACCode_silent 1, rfl⟩ ?_
  · rintro r ⟨n, A, B, hn, hA, hB, hcode, rfl⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hprod : (A.card : ℝ) * B.card ≤ (3 : ℝ) ^ n := by
      exact_mod_cast card_mul_card_le_of_isAdderMACCode hcode
    have hl : log2 (A.card : ℝ) + log2 (B.card : ℝ) = log2 ((A.card : ℝ) * B.card) := by
      simp only [log2, Real.log_mul hApos.ne' hBpos.ne', add_div]
    rw [div_le_iff₀ hnpos, hl, show log2 3 * (n : ℝ) = n * log2 3 from mul_comm _ _,
      ← log2_pow']
    exact log2_le_log2' (mul_pos hApos hBpos) hprod

end AdderMAC

end InfoTheory.Known
