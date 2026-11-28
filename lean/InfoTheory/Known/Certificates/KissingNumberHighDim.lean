import InfoTheory.Problems.KissingNumberHighDim
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.KissingNumberHighDim`

**Outcome: the definition of `kissingNumber` is sound.** The `sSup` is over a nonempty set
that is bounded above, so it is attained, and the elementary values come out right. No junk was
found.

`kissingNumber d` is the `sSup` of the sizes `m` of families of unit vectors in `ℝ^d` with
pairwise inner product `≤ 1/2`. Repeated points are excluded automatically, because a unit
vector has inner product `1` with itself.

Certified:
* `config_card_le`, `bddAbove_kissingSet`, `kissingNumber_le`: every such family has at most
  `(2d+3)^d` points. Proof: pigeonhole on a grid of mesh `1/(d+1)`. Two of the points are at
  distance `≥ 1`, so they never share a cell. This finiteness is what makes the `sSup`
  meaningful (cf. Conway–Sloane, *Sphere Packings, Lattices and Groups*, Ch. 1 §2.5).
* `kissingSet_nonempty`, `exists_config_kissingNumber`, `le_kissingNumber`: `τ(d)` is attained
  and dominates every configuration.
* `kissingNumber_zero`: `τ(0) = 0`.
* `two_mul_le_kissingNumber`: `2d ≤ τ(d)`, from the cross-polytope `±eᵣ` (Conway–Sloane Ch. 1,
  Table 1.5).
* `card_le_kissingNumber_of_isCode`: a binary code of length `d` with minimum distance `≥ d/4`
  embeds as a kissing configuration via `c ↦ ((-1)^{c_r}/√d)_r`.
* `gilbertVarshamov_quarter_le_log2_kissingNumber` and `gilbertVarshamov_quarter_pos`: for every
  `d ≥ 1`, `0 < 1 - h(1/4) ≤ (1/d) log₂ τ(d)`. Exponential growth, with exponent `≈ 0.1887`,
  via the Gilbert–Varshamov bound. This exponent is weaker than Chabauty–Shannon–Wyner's
  `0.2075`, so it does not settle the `Statement`. It does show that the `Statement`'s quantity
  `log₂ τ(d) / d` is bounded below by a positive constant and is not junk.

* **Regression** (known small values): `regression_kissing_one` — `τ(1) = 2`;
  `regression_kissing_two_ge` — `6 ≤ τ(2)` (regular hexagon; the known value is `τ(2) = 6`,
  the matching upper bound is not formalized); `kissingNumber_zero` — `τ(0) = 0`.

Not certified:
* The Chabauty–Shannon–Wyner lower bound `τ(d) ≥ (2/√3)^{d(1+o(1))}` (Shannon 1959; Wyner 1965),
  which needs spherical-cap volume estimates. Only the weaker exponent `1 - h(1/4)` is
  certified.
* The Kabatiansky–Levenshtein upper bound `τ(d) ≤ 2^{0.401 d (1+o(1))}` (1978), which needs
  Delsarte's LP bound.
* The volume bound `τ(d) ≤ 3^d`. Not attempted; our `(2d+3)^d` bound suffices for
  finiteness, but it does not bound the exponent.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.KissingNumberHighDim

open InfoTheory InfoTheory.Known

/-- The set whose `sSup` is `kissingNumber d`. -/
def kissingSet (d : ℕ) : Set ℕ :=
  { m : ℕ | ∃ pts : Fin m → Fin d → ℝ,
    (∀ i, ∑ r : Fin d, (pts i r) ^ 2 = 1) ∧
    (∀ i j, i ≠ j → ∑ r : Fin d, pts i r * pts j r ≤ 1 / 2) }

theorem kissingNumber_eq_sSup (d : ℕ) : kissingNumber d = sSup (kissingSet d) := rfl

/-- **Finiteness of kissing configurations** (pigeonhole on a grid of mesh `1/(d+1)`): unit vectors
in `ℝ^d` with pairwise inner product `≤ 1/2` are at mutual distance `≥ 1`, so two of them never
share a grid cell; hence there are at most `(2d+3)^d` of them. (Cf. Conway–Sloane, *Sphere
Packings, Lattices and Groups*, Ch. 1 §2.5, where the sharper volume bound `3^d` is used.) -/
theorem config_card_le {d m : ℕ} (pts : Fin m → Fin d → ℝ)
    (h1 : ∀ i, ∑ r : Fin d, (pts i r) ^ 2 = 1)
    (h2 : ∀ i j, i ≠ j → ∑ r : Fin d, pts i r * pts j r ≤ 1 / 2) :
    m ≤ (2 * d + 3) ^ d := by
  set N : ℕ := d + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  let c : Fin m → Fin d → ℤ := fun i r => ⌊(N : ℝ) * pts i r⌋
  have hcoord : ∀ i r, |pts i r| ≤ 1 := by
    intro i r
    have : (pts i r) ^ 2 ≤ 1 := by
      rw [← h1 i]
      exact Finset.single_le_sum (f := fun r => (pts i r) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ r)
    rw [← sq_le_one_iff_abs_le_one] at *
    exact this
  have hmaps : Set.MapsTo c (Finset.univ : Finset (Fin m))
      (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)) := by
    intro i _
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro r
    have hab := abs_le.mp (hcoord i r)
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr
      push_cast
      nlinarith
    · have : (⌊(N : ℝ) * pts i r⌋ : ℝ) ≤ N := (Int.floor_le _).trans (by nlinarith)
      exact_mod_cast this
  have hinj : Set.InjOn c (Finset.univ : Finset (Fin m)) := by
    intro i _ j _ hij
    by_contra hne
    have hclose : ∀ r, |pts i r - pts j r| < 1 / N := by
      intro r
      have h := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hij r)
      rw [← mul_sub, abs_mul, abs_of_pos hNpos] at h
      rw [lt_div_iff₀ hNpos]
      linarith
    have hsum : ∑ r, (pts i r - pts j r) ^ 2 = 2 - 2 * ∑ r, pts i r * pts j r := by
      have : ∀ r, (pts i r - pts j r) ^ 2 =
          (pts i r) ^ 2 + (pts j r) ^ 2 - 2 * (pts i r * pts j r) := fun r => by ring
      simp_rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1]
      ring
    have hge : 1 ≤ ∑ r, (pts i r - pts j r) ^ 2 := by
      rw [hsum]; linarith [h2 i j hne]
    have hle : ∑ r, (pts i r - pts j r) ^ 2 ≤ d * (1 / (N : ℝ)) ^ 2 := by
      calc ∑ r, (pts i r - pts j r) ^ 2 ≤ ∑ _r : Fin d, (1 / (N : ℝ)) ^ 2 :=
            Finset.sum_le_sum fun r _ => by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hclose r).le 2
        _ = d * (1 / (N : ℝ)) ^ 2 := by simp
    have hlt : (d : ℝ) * (1 / (N : ℝ)) ^ 2 < 1 := by
      rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity), hN]
      push_cast
      nlinarith
    linarith
  have := Finset.card_le_card_of_injOn c hmaps hinj
  rw [Finset.card_univ, Fintype.card_fin, Fintype.card_piFinset, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Int.card_Icc] at this
  have h' : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * d + 3 := by omega
  rwa [h'] at this

/-- The `sSup` defining `kissingNumber d` is over a bounded set (so it is not the junk `0`). -/
theorem bddAbove_kissingSet (d : ℕ) : BddAbove (kissingSet d) :=
  ⟨(2 * d + 3) ^ d, fun _ ⟨pts, h1, h2⟩ => config_card_le pts h1 h2⟩

theorem kissingSet_nonempty (d : ℕ) : (kissingSet d).Nonempty :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- Every kissing configuration has at most `τ(d)` points. -/
theorem le_kissingNumber {d m : ℕ} (pts : Fin m → Fin d → ℝ)
    (h1 : ∀ i, ∑ r : Fin d, (pts i r) ^ 2 = 1)
    (h2 : ∀ i j, i ≠ j → ∑ r : Fin d, pts i r * pts j r ≤ 1 / 2) :
    m ≤ kissingNumber d :=
  le_csSup (bddAbove_kissingSet d) ⟨pts, h1, h2⟩

/-- `τ(d)` is attained by a configuration. -/
theorem exists_config_kissingNumber (d : ℕ) : kissingNumber d ∈ kissingSet d :=
  Nat.sSup_mem (kissingSet_nonempty d) (bddAbove_kissingSet d)

/-- Crude upper bound `τ(d) ≤ (2d+3)^d`. -/
theorem kissingNumber_le (d : ℕ) : kissingNumber d ≤ (2 * d + 3) ^ d := by
  obtain ⟨pts, h1, h2⟩ := exists_config_kissingNumber d
  exact config_card_le pts h1 h2

/-- `τ(0) = 0`: `ℝ^0` has no unit vectors. -/
theorem kissingNumber_zero : kissingNumber 0 = 0 := by
  obtain ⟨pts, h1, -⟩ := exists_config_kissingNumber 0
  by_contra h
  have := h1 ⟨0, Nat.pos_of_ne_zero h⟩
  simp at this

/-- **Cross-polytope lower bound** `2d ≤ τ(d)`: the `2d` vectors `±eᵣ` (Conway–Sloane Ch. 1,
Table 1.5). -/
theorem two_mul_le_kissingNumber (d : ℕ) : 2 * d ≤ kissingNumber d := by
  let pts : Fin (d + d) → Fin d → ℝ :=
    Fin.append (fun r => Pi.single r 1) (fun r => -Pi.single r 1)
  have h := le_kissingNumber pts ?_ ?_
  · omega
  · intro i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
      simp only [pts, Fin.append_left, Fin.append_right] <;> simp [Pi.single_apply]
  · intro i j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
      refine Fin.addCases (fun r' => ?_) (fun r' => ?_) j <;> intro hij <;>
      simp only [pts, Fin.append_left, Fin.append_right] at hij ⊢ <;> simp [Pi.single_apply] <;>
      split_ifs with h <;> first
        | (subst h; exact absurd rfl hij)
        | norm_num


/-! ### Exponential lower bound from binary codes -/

/-- Spherical embedding of a binary code: `c ↦ ((-1)^{c_r}/√d)_r`. The inner product of two images
is `(d - 2·dist)/d`, which is `≤ 1/2` once `dist ≥ d/4`. -/
theorem card_le_kissingNumber_of_isCode {d dmin : ℕ} (hd : 1 ≤ d) (h4 : d ≤ 4 * dmin)
    {C : Finset (Fin d → Fin 2)} (hC : IsCode 2 d dmin C) : C.card ≤ kissingNumber d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
  have hsqpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
  let s : Fin 2 → ℝ := fun a => if a = 0 then 1 else -1
  let pts : Fin C.card → Fin d → ℝ := fun i r => s ((C.equivFin.symm i).1 r) / Real.sqrt d
  refine le_kissingNumber pts ?_ ?_
  · intro i
    have : ∀ r, (pts i r) ^ 2 = 1 / d := by
      intro r
      simp only [pts, div_pow, hsq, s]
      split_ifs <;> norm_num
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self hdpos.ne']
  · intro i j hij
    set c := (C.equivFin.symm i).1
    set c' := (C.equivFin.symm j).1
    have hcc' : c ≠ c' := by
      intro h
      apply hij
      exact C.equivFin.symm.injective (Subtype.ext h)
    have hdist := hC c (C.equivFin.symm i).2 c' (C.equivFin.symm j).2 hcc'
    have hterm : ∀ r, pts i r * pts j r =
        (1 - 2 * (if c r ≠ c' r then (1 : ℝ) else 0)) / d := by
      intro r
      simp only [pts]
      rw [div_mul_div_comm, ← sq, hsq]
      congr 1
      simp only [s, c, c']
      have h2 : ∀ a b : Fin 2, (if a = 0 then (1 : ℝ) else -1) * (if b = 0 then 1 else -1) =
          1 - 2 * (if a ≠ b then 1 else 0) := by
        intro a b; fin_cases a <;> fin_cases b <;> norm_num
      exact h2 _ _
    simp_rw [hterm]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hD : ((Finset.univ.filter (fun r => c r ≠ c' r)).card : ℝ) = hammingDistVec c c' := rfl
    rw [hD, div_le_iff₀ hdpos]
    have : (d : ℝ) ≤ 4 * hammingDistVec c c' := by exact_mod_cast h4.trans (by omega)
    linarith

/-- Per-blocklength Gilbert–Varshamov estimate `1 - h(δ) ≤ (1/n) log₂ A_2(n, ⌈δn⌉)` for
`δ ∈ (0, 1/2)` and `n ≥ 1` (the same argument as `Known.gilbertVarshamov_le_asymptoticCodeRate`,
MacWilliams–Sloane Ch. 17 Thm 30). -/
theorem gilbertVarshamov_le_term {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) (n : ℕ) (hn1 : 1 ≤ n) :
    gilbertVarshamov δ ≤ log2 (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set d := Nat.ceil (δ * (n : ℝ)) with hd
  set A := maxCodeSize 2 n d
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hgv := gilbert_varshamov_bound (q := 2) (n := n) hd1
  simp only [Nat.add_one_sub_one, one_pow, mul_one] at hgv
  set m := d - 1
  have hdm : d = m + 1 := by omega
  have hr : Finset.range d = Finset.range (m + 1) := by rw [hdm]
  rw [hr] at hgv
  have hm : (m : ℝ) ≤ δ * n := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ δ * n)
    rw [← hd] at this
    have : (m : ℝ) = (d : ℝ) - 1 := by rw [hdm]; push_cast; ring
    linarith
  have hvol := sum_choose_mul_exp_le_one h0 h1.le n m hm
  set L := δ * Real.log δ + (1 - δ) * Real.log (1 - δ)
  set V := ∑ i ∈ Finset.range (m + 1), (n.choose i : ℝ)
  have hgvR : (2 : ℝ) ^ n ≤ (A : ℝ) * V := by
    have := (Nat.cast_le (α := ℝ)).mpr hgv
    push_cast at this
    exact this
  have hA : 0 < (A : ℝ) := by
    have := one_le_maxCodeSize (q := 2) (by norm_num) n d
    exact_mod_cast this
  have hE : 0 < Real.exp (n * L) := Real.exp_pos _
  have hkey : (2 : ℝ) ^ n * Real.exp (n * L) ≤ A := by
    calc (2 : ℝ) ^ n * Real.exp (n * L) ≤ (A : ℝ) * V * Real.exp (n * L) :=
          mul_le_mul_of_nonneg_right hgvR hE.le
      _ = A * (V * Real.exp (n * L)) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hvol hA.le
      _ = A := mul_one _
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) hE.ne', Real.log_pow, Real.log_exp] at hlog
  have hH := binaryEntropy_mul_log_two h0 (by linarith)
  rw [log2, le_div_iff₀ hnpos, le_div_iff₀ hl2]
  unfold gilbertVarshamov
  have : (1 - binaryEntropy δ) * n * Real.log 2 = n * Real.log 2 + n * L := by
    have : (1 - binaryEntropy δ) * n * Real.log 2 =
        n * Real.log 2 - n * (binaryEntropy δ * Real.log 2) := by ring
    rw [this, hH]; ring
  rw [this]
  exact hlog

/-- **Exponential growth of `τ(d)`** (Conway–Sloane Ch. 1 §2.5, via binary codes and the
Gilbert–Varshamov bound): for every `d ≥ 1`, `1 - h(1/4) ≤ (1/d) log₂ τ(d)`. This is a positive
constant (`≈ 0.1887`), below the Chabauty–Shannon–Wyner exponent `log₂(2/√3) ≈ 0.2075`. So the
quantity in the `Statement` has a certified positive lower bound and is not junk. -/
theorem gilbertVarshamov_quarter_le_log2_kissingNumber (d : ℕ) (hd : 1 ≤ d) :
    gilbertVarshamov (1 / 4) ≤ log2 (kissingNumber d : ℝ) / (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine (gilbertVarshamov_le_term (by norm_num) (by norm_num) d hd).trans ?_
  apply div_le_div_of_nonneg_right _ hdpos.le
  obtain ⟨C, hC, hc⟩ := exists_code_card_eq_maxCodeSize 2 d (Nat.ceil ((1 / 4 : ℝ) * d))
  have h4 : d ≤ 4 * Nat.ceil ((1 / 4 : ℝ) * d) := by
    have := Nat.le_ceil ((1 / 4 : ℝ) * d)
    have : (d : ℝ) ≤ 4 * (Nat.ceil ((1 / 4 : ℝ) * d) : ℝ) := by linarith
    exact_mod_cast this
  have hle := card_le_kissingNumber_of_isCode hd h4 hC
  rw [hc] at hle
  have hA1 := one_le_maxCodeSize (q := 2) (by norm_num) d (Nat.ceil ((1 / 4 : ℝ) * d))
  unfold log2
  apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
  exact Real.log_le_log (by exact_mod_cast hA1) (by exact_mod_cast hle)

/-- `1 - h(1/4) > 0`, so `τ(d) ≥ 2^{c d}` with `c > 0`. -/
theorem gilbertVarshamov_quarter_pos : 0 < gilbertVarshamov (1 / 4) := by
  unfold gilbertVarshamov
  rw [binaryEntropy_eq_binEntropy (by norm_num) (by norm_num)]
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have : Real.binEntropy (1 / 4) < Real.log 2 := Real.binEntropy_lt_log_two.mpr (by norm_num)
  rw [sub_pos, div_lt_one hl2]
  exact this

/-! ### Regression: known small values -/

/-- **Regression**: `τ(1) = 2` (the only unit vectors in `ℝ¹` are `±1`). -/
theorem regression_kissing_one : kissingNumber 1 = 2 := by
  refine le_antisymm ?_ (by simpa using two_mul_le_kissingNumber 1)
  obtain ⟨pts, h1, h2⟩ := exists_config_kissingNumber 1
  by_contra hlt
  rw [not_le] at hlt
  have hsq : ∀ i, pts i 0 ^ 2 = 1 := fun i => by simpa using h1 i
  have key : ∀ x y : ℝ, x ^ 2 = 1 → y ^ 2 = 1 → x * y ≤ 1 / 2 → x * y = -1 := by
    intro x y hx hy hxy
    have h : (x * y - 1) * (x * y + 1) = 0 := by linear_combination y ^ 2 * hx + hy
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  let i0 : Fin (kissingNumber 1) := ⟨0, by omega⟩
  let i1 : Fin (kissingNumber 1) := ⟨1, by omega⟩
  let i2 : Fin (kissingNumber 1) := ⟨2, by omega⟩
  have h01 := h2 i0 i1 (by simp [i0, i1, Fin.ext_iff])
  have h02 := h2 i0 i2 (by simp [i0, i2, Fin.ext_iff])
  have h12 := h2 i1 i2 (by simp [i1, i2, Fin.ext_iff])
  simp only [Fin.sum_univ_one] at h01 h02 h12
  have e01 := key _ _ (hsq i0) (hsq i1) h01
  have e02 := key _ _ (hsq i0) (hsq i2) h02
  have e12 := key _ _ (hsq i1) (hsq i2) h12
  have hprod : (pts i0 0 * pts i1 0 * pts i2 0) ^ 2 =
      (pts i0 0 * pts i1 0) * (pts i1 0 * pts i2 0) * (pts i0 0 * pts i2 0) := by ring
  rw [e01, e02, e12] at hprod
  nlinarith [sq_nonneg (pts i0 0 * pts i1 0 * pts i2 0)]

/-- **Regression**: `6 ≤ τ(2)` (the regular hexagon; `τ(2) = 6` is classical). -/
theorem regression_kissing_two_ge : 6 ≤ kissingNumber 2 := by
  set t : ℝ := Real.sqrt 3 / 2 with ht
  have hs : t * t = 3 / 4 := by
    rw [ht, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  let pts : Fin 6 → Fin 2 → ℝ :=
    ![![1, 0], ![1 / 2, t], ![-1 / 2, t], ![-1, 0], ![-1 / 2, -t], ![1 / 2, -t]]
  refine le_kissingNumber pts ?_ ?_
  · intro i
    fin_cases i <;> simp [pts, Fin.sum_univ_two] <;> nlinarith [hs]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [pts, Fin.sum_univ_two] at hij ⊢ <;> nlinarith [hs]

end InfoTheory.Known.Certificates.KissingNumberHighDim
