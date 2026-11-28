import InfoTheory.Problems.GaussianInterferenceChannel

/-!
# Certificate for `InfoTheory.Problems.GaussianInterferenceChannel`

The statement asks whether, for every `a, b ≥ 0` and `P₁, P₂ > 0`, the closure of the operational
capacity region of the Gaussian interference channel equals the closure of
`InGaussianHKRegion a b P₁ P₂`, the Gaussian Han–Kobayashi region with a coded time-sharing
variable and power control.

## Certified (about exactly these objects)
* `basic_mem_region`, `zero_mem_region` : the single-phase Gaussian HK polytope is the `m = 1`
  case, and `(0, 0)` lies in the region; so the region is nonempty.
* `convexHull_subset_region` : the region contains `InGaussianHKConvexHull` (the *old*
  frozen region: convex hull of single-phase polytopes with power control).  Hence the new
  statement is about a set sandwiched between the refuted one and the capacity region.
* `region_R₁_le`, `region_R₂_le` : every point satisfies `Rⱼ ≤ ½ log₂(1 + Pⱼ)` (Jensen for
  `log`); so the region is bounded and the right-hand side is a genuine bounded set.
* `decoupled_region_eq` : for `a = b = 0` (two separate AWGN links) the region is exactly the
  rectangle `[0, ½ log₂(1 + P₁)] × [0, ½ log₂(1 + P₂)]`, i.e. the textbook capacity region.
* `zero_achievable` : `(0, 0)` is operationally achievable, so the left-hand side is nonempty.
* **Regression** `strong_region_eq` : under strong interference `a² ≥ 1, b² ≥ 1` the region is
  *exactly* the Sato / Han–Kobayashi capacity region
  `{0 ≤ Rⱼ ≤ C(Pⱼ), R₁ + R₂ ≤ min(C(P₁ + a²P₂), C(P₂ + b²P₁))}` (`StrongInterferenceRegion`);
  `⊆` is `strong_region_sum_le` (per phase `C((P₁ + a²P₂c)/N₁) + C(P₂p/N₂) ≤ C(P₁ + a²P₂)`, then
  Jensen), `⊇` is `strong_subset_region` (single phase, all power common).  With
  `decoupled_region_eq` the frozen formula reproduces the textbook answer in both solved cases.

## Not certified
* Achievability of the region (Han–Kobayashi 1981 with `Q`; Gaussian inputs) and any converse
  (Sato 1981 strong interference; Etkin–Tse–Wang 2008 one-bit gap).
* The catalog-error separation (coded time-sharing beats the convex hull at
  `a = b = 1/2, P = 100`); the convex-hull upper bound there (≤ 3.828526) is an outward-rounded
  interval branch-and-bound outside Lean
  (`attempts/gaussian-interference-channel/code/reviewer_bnb_rigorous.py`).
-/

open scoped BigOperators
open MeasureTheory

namespace InfoTheory.Known.Certificates.GaussianInterferenceChannel

open InfoTheory InfoTheory.Problems.GaussianInterferenceChannel

/-- The *old* frozen region (before the 2026-11-27 statement fix): convex hull of single-phase
    Gaussian HK polytopes with power control across phases (plain time-sharing). -/
def InGaussianHKConvexHull (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  ∃ (m : ℕ) (w : Fin m → ℝ) (p₁ p₂ r₁ r₂ : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
    (∀ i, 0 ≤ p₁ i ∧ 0 ≤ p₂ i) ∧
    (∑ i : Fin m, w i * p₁ i ≤ P₁) ∧
    (∑ i : Fin m, w i * p₂ i ≤ P₂) ∧
    (∀ i, InGaussianHKBasic a b (p₁ i) (p₂ i) (r₁ i) (r₂ i)) ∧
    R₁ = ∑ i : Fin m, w i * r₁ i ∧
    R₂ = ∑ i : Fin m, w i * r₂ i

/-- The Gaussian capacity function `C(s) = ½ log₂(1 + s)`. -/
noncomputable def cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)

theorem cap_zero : cap 0 = 0 := by simp [cap, log2]

theorem cap_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : cap s ≤ cap t := by
  unfold cap log2
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have := Real.log_le_log (by linarith) (by linarith : 1 + s ≤ 1 + t)
  have := div_le_div_of_nonneg_right this h2.le
  linarith

theorem cap_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ cap s := cap_zero ▸ cap_mono le_rfl hs

/-! ### Averaging helpers -/

private lemma avg_le {m : ℕ} {w f g : Fin m → ℝ} (hw : ∀ i, 0 ≤ w i) (h : ∀ i, f i ≤ g i) :
    ∑ i, w i * f i ≤ ∑ i, w i * g i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

private lemma lin_avg {m : ℕ} (w x y : Fin m → ℝ) (c₁ c₂ : ℝ) :
    c₁ * ∑ i, w i * x i + c₂ * ∑ i, w i * y i = ∑ i, w i * (c₁ * x i + c₂ * y i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Jensen + monotonicity: `𝔼[C(Xᵢ / Nᵢ)] ≤ C(P)` when `Nᵢ ≥ 1`, `Xᵢ ≥ 0`, `𝔼 X ≤ P`. -/
theorem avg_cap_le {m : ℕ} {w x N : Fin m → ℝ} {P : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) (hN : ∀ i, 1 ≤ N i)
    (hP : ∑ i, w i * x i ≤ P) :
    ∑ i, w i * cap (x i / N i) ≤ cap P := by
  have h1 : ∑ i, w i * cap (x i / N i) ≤ ∑ i, w i * cap (x i) :=
    avg_le hw fun i => cap_mono (div_nonneg (hx i) (by linarith [hN i]))
      (div_le_self (hx i) (hN i))
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.univ)
    (w := w) (p := fun i => 1 + x i) (fun i _ => hw i) hw1
    (fun i _ => Set.mem_Ioi.mpr (by linarith [hx i]))
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ i, w i * (1 + x i) = 1 + ∑ i, w i * x i := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1]
  rw [hsum] at hJ
  have hxs : 0 ≤ ∑ i, w i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hx i)
  have h2 : ∑ i, w i * cap (x i) ≤ cap (∑ i, w i * x i) := by
    unfold cap log2
    have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
    have : ∑ i, w i * ((1 / 2 : ℝ) * (Real.log (1 + x i) / Real.log 2)) =
        (1 / 2 : ℝ) * ((∑ i, w i * Real.log (1 + x i)) / Real.log 2) := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have := div_le_div_of_nonneg_right hJ hl.le
    linarith
  exact h1.trans (h2.trans (cap_mono hxs hP))

/-! ### The region is nonempty and contains the old convex hull -/

/-- The single-phase polytope is the `m = 1` case of the coded-time-sharing region. -/
theorem basic_mem_region {a b P₁ P₂ R₁ R₂ : ℝ} (h : InGaussianHKBasic a b P₁ P₂ R₁ R₂) :
    InGaussianHKRegion a b P₁ P₂ R₁ R₂ := by
  obtain ⟨hR₁, hR₂, P₁c, P₁p, P₂c, P₂p, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hR₁, hR₂, 1, fun _ => 1, fun _ => P₁c, fun _ => P₁p, fun _ => P₂c, fun _ => P₂p,
    fun _ => zero_le_one, by simp, fun _ => ⟨h1, h2, h4, h5⟩, by simpa using h3,
    by simpa using h6, ?_⟩
  simpa using h7

theorem zero_mem_region (a b : ℝ) {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) :
    InGaussianHKRegion a b P₁ P₂ 0 0 := by
  apply basic_mem_region
  refine ⟨le_rfl, le_rfl, 0, 0, 0, 0, le_rfl, le_rfl, by simpa using hP₁, le_rfl, le_rfl,
    by simpa using hP₂, ?_⟩
  simp [log2]

/-- **The new region contains the old (refuted) convex-hull region.** -/
theorem convexHull_subset_region {a b P₁ P₂ R₁ R₂ : ℝ}
    (h : InGaussianHKConvexHull a b P₁ P₂ R₁ R₂) : InGaussianHKRegion a b P₁ P₂ R₁ R₂ := by
  obtain ⟨m, w, p₁, p₂, r₁, r₂, hw, hw1, hp, hP₁, hP₂, hB, rfl, rfl⟩ := h
  have hB' := fun i => (hB i).2.2
  choose P₁c P₁p P₂c P₂p hP using hB'
  have hr₁ : ∀ i, 0 ≤ r₁ i := fun i => (hB i).1
  have hr₂ : ∀ i, 0 ≤ r₂ i := fun i => (hB i).2.1
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hr₁ i),
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hr₂ i),
    m, w, P₁c, P₁p, P₂c, P₂p, hw, hw1,
    fun i => ⟨(hP i).1, (hP i).2.1, (hP i).2.2.2.1, (hP i).2.2.2.2.1⟩,
    (avg_le hw fun i => (hP i).2.2.1).trans hP₁,
    (avg_le hw fun i => (hP i).2.2.2.2.2.1).trans hP₂, ?_⟩
  dsimp only at hP ⊢
  have e1 : ∑ i, w i * r₁ i + ∑ i, w i * r₂ i = ∑ i, w i * (r₁ i + r₂ i) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : 2 * ∑ i, w i * r₁ i + ∑ i, w i * r₂ i = ∑ i, w i * (2 * r₁ i + r₂ i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, w i * r₁ i + 2 * ∑ i, w i * r₂ i = ∑ i, w i * (r₁ i + 2 * r₂ i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  exact ⟨avg_le hw fun i => (hP i).2.2.2.2.2.2.1,
    avg_le hw fun i => (hP i).2.2.2.2.2.2.2.1,
    avg_le hw fun i => (hP i).2.2.2.2.2.2.2.2.1,
    avg_le hw fun i => (hP i).2.2.2.2.2.2.2.2.2.1,
    avg_le hw fun i => (hP i).2.2.2.2.2.2.2.2.2.2.1,
    avg_le hw fun i => (hP i).2.2.2.2.2.2.2.2.2.2.2.1,
    avg_le hw fun i => (hP i).2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ### Single-user bounds: the region is bounded -/

theorem region_R₁_le {a b P₁ P₂ R₁ R₂ : ℝ} (h : InGaussianHKRegion a b P₁ P₂ R₁ R₂) :
    R₁ ≤ cap P₁ := by
  obtain ⟨-, -, m, w, P₁c, P₁p, P₂c, P₂p, hw, hw1, hnn, hP₁, -, h⟩ := h
  dsimp only at h
  exact h.1.trans (avg_cap_le hw hw1 (fun i => add_nonneg (hnn i).1 (hnn i).2.1)
    (fun i => le_add_of_nonneg_right (mul_nonneg (sq_nonneg a) (hnn i).2.2.2)) hP₁)

theorem region_R₂_le {a b P₁ P₂ R₁ R₂ : ℝ} (h : InGaussianHKRegion a b P₁ P₂ R₁ R₂) :
    R₂ ≤ cap P₂ := by
  obtain ⟨-, -, m, w, P₁c, P₁p, P₂c, P₂p, hw, hw1, hnn, -, hP₂, h⟩ := h
  dsimp only at h
  exact h.2.1.trans (avg_cap_le hw hw1 (fun i => add_nonneg (hnn i).2.2.1 (hnn i).2.2.2)
    (fun i => le_add_of_nonneg_right (mul_nonneg (sq_nonneg b) (hnn i).2.1)) hP₂)

/-- The region is bounded (it lies in the rectangle of single-user capacities). -/
theorem region_bounded (a b P₁ P₂ : ℝ) :
    Bornology.IsBounded {p : ℝ × ℝ | InGaussianHKRegion a b P₁ P₂ p.1 p.2} :=
  (Metric.isBounded_Icc ((0 : ℝ), (0 : ℝ)) (cap P₁, cap P₂)).subset fun _ hp =>
    ⟨⟨hp.1, hp.2.1⟩, ⟨region_R₁_le hp, region_R₂_le hp⟩⟩

/-! ### Decoupled channel `a = b = 0`: the region is the capacity rectangle -/

/-- For `a = b = 0` (two separate AWGN links) the coded-time-sharing Gaussian HK region is
    exactly `[0, ½ log₂(1 + P₁)] × [0, ½ log₂(1 + P₂)]`. -/
theorem decoupled_region_eq {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) :
    {p : ℝ × ℝ | InGaussianHKRegion 0 0 P₁ P₂ p.1 p.2} =
      Set.Icc 0 (cap P₁) ×ˢ Set.Icc 0 (cap P₂) := by
  ext ⟨R₁, R₂⟩
  simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
  constructor
  · intro h
    exact ⟨⟨h.1, region_R₁_le h⟩, ⟨h.2.1, region_R₂_le h⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    apply basic_mem_region
    refine ⟨h1, h3, 0, P₁, 0, P₂, le_rfl, hP₁, by simp, le_rfl, hP₂, by simp, ?_⟩
    unfold cap at h2 h4
    dsimp only
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero,
      div_one, zero_add, mul_zero]
    refine ⟨h2, h4, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Regression: strong interference `a² ≥ 1, b² ≥ 1` (Sato 1981; Han–Kobayashi 1981)

Under strong interference the capacity region is
`{R₁ ≤ C(P₁), R₂ ≤ C(P₂), R₁ + R₂ ≤ min(C(P₁ + a²P₂), C(P₂ + b²P₁))}`.  We prove that the
frozen region `InGaussianHKRegion` is *exactly* this set, so the formula reduces to the known
answer in this solved case. -/

/-- The known strong-interference capacity region (Sato 1981; Han–Kobayashi 1981). -/
def StrongInterferenceRegion (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ R₁ ≤ cap P₁ ∧ R₂ ≤ cap P₂ ∧
  R₁ + R₂ ≤ cap (P₁ + a ^ 2 * P₂) ∧ R₁ + R₂ ≤ cap (P₂ + b ^ 2 * P₁)

/-- Per-phase sum-rate bound: `C(A / N) + C(B / M) ≤ C(A + N - 1)` when `1 + B ≤ N`, `M ≥ 1`. -/
theorem cap_div_add_cap_div_le {A N B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hBN : 1 + B ≤ N) : cap (A / N) + cap (B / M) ≤ cap ((A + N - 1) / 1) := by
  have hN : 0 < N := by linarith
  have h1 : cap (B / M) ≤ cap B := cap_mono (div_nonneg hB (by linarith)) (div_le_self hB hM)
  have h2 : cap (A / N) + cap B ≤ cap ((A + N - 1) / 1) := by
    unfold cap log2
    have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
    have e : 1 + A / N = (A + N) / N := by field_simp; ring
    rw [e, div_one, show 1 + (A + N - 1) = A + N by ring,
      Real.log_div (by positivity) hN.ne']
    have := Real.log_le_log (by linarith) hBN
    have h3 : Real.log (1 + B) / Real.log 2 ≤ Real.log N / Real.log 2 :=
      div_le_div_of_nonneg_right this hl.le
    have h4 : (Real.log (A + N) - Real.log N) / Real.log 2 =
        Real.log (A + N) / Real.log 2 - Real.log N / Real.log 2 := sub_div _ _ _
    rw [h4]
    linarith
  linarith

/-- **Strong interference, `⊆`**: every point of the frozen region satisfies the two sum-rate
    bounds `R₁ + R₂ ≤ C(P₁ + a²P₂)` and `R₁ + R₂ ≤ C(P₂ + b²P₁)` when `a² ≥ 1`, `b² ≥ 1`. -/
theorem strong_region_sum_le {a b P₁ P₂ R₁ R₂ : ℝ} (ha : 1 ≤ a ^ 2) (hb : 1 ≤ b ^ 2)
    (h : InGaussianHKRegion a b P₁ P₂ R₁ R₂) :
    R₁ + R₂ ≤ cap (P₁ + a ^ 2 * P₂) ∧ R₁ + R₂ ≤ cap (P₂ + b ^ 2 * P₁) := by
  obtain ⟨-, -, m, w, P₁c, P₁p, P₂c, P₂p, hw, hw1, hnn, hP₁, hP₂, h⟩ := h
  dsimp only at h
  obtain ⟨-, -, h3, h4, -⟩ := h
  constructor
  · have key : ∀ i, cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / (1 + a ^ 2 * P₂p i)) +
        cap (P₂p i / (1 + b ^ 2 * P₁p i)) ≤
        cap ((P₁c i + P₁p i + a ^ 2 * P₂c i + (1 + a ^ 2 * P₂p i) - 1) / 1) := fun i => by
      obtain ⟨h1, h2, h3, h4⟩ := hnn i
      exact cap_div_add_cap_div_le (by positivity) h4
        (le_add_of_nonneg_right (by positivity)) (by nlinarith)
    have hav := avg_cap_le (w := w) (N := fun _ => 1) (P := P₁ + a ^ 2 * P₂)
      (x := fun i => P₁c i + P₁p i + a ^ 2 * P₂c i + (1 + a ^ 2 * P₂p i) - 1) hw hw1
      (fun i => by obtain ⟨h1, h2, h3, h4⟩ := hnn i; nlinarith [sq_nonneg a])
      (fun _ => le_rfl) (by
        have e := lin_avg w (fun i => P₁c i + P₁p i) (fun i => P₂c i + P₂p i) 1 (a ^ 2)
        have e2 : ∑ i, w i * (P₁c i + P₁p i + a ^ 2 * P₂c i + (1 + a ^ 2 * P₂p i) - 1) =
            ∑ i, w i * (1 * (P₁c i + P₁p i) + a ^ 2 * (P₂c i + P₂p i)) :=
          Finset.sum_congr rfl fun i _ => by ring
        rw [e2, ← e]
        nlinarith [sq_nonneg a])
    exact h3.trans ((avg_le hw key).trans hav)
  · have key : ∀ i, cap (P₁p i / (1 + a ^ 2 * P₂p i)) +
        cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / (1 + b ^ 2 * P₁p i)) ≤
        cap ((P₂c i + P₂p i + b ^ 2 * P₁c i + (1 + b ^ 2 * P₁p i) - 1) / 1) := fun i => by
      obtain ⟨h1, h2, h3, h4⟩ := hnn i
      rw [add_comm]
      exact cap_div_add_cap_div_le (by positivity) h2
        (le_add_of_nonneg_right (by positivity)) (by nlinarith)
    have hav := avg_cap_le (w := w) (N := fun _ => 1) (P := P₂ + b ^ 2 * P₁)
      (x := fun i => P₂c i + P₂p i + b ^ 2 * P₁c i + (1 + b ^ 2 * P₁p i) - 1) hw hw1
      (fun i => by obtain ⟨h1, h2, h3, h4⟩ := hnn i; nlinarith [sq_nonneg b])
      (fun _ => le_rfl) (by
        have e := lin_avg w (fun i => P₂c i + P₂p i) (fun i => P₁c i + P₁p i) 1 (b ^ 2)
        have e2 : ∑ i, w i * (P₂c i + P₂p i + b ^ 2 * P₁c i + (1 + b ^ 2 * P₁p i) - 1) =
            ∑ i, w i * (1 * (P₂c i + P₂p i) + b ^ 2 * (P₁c i + P₁p i)) :=
          Finset.sum_congr rfl fun i _ => by ring
        rw [e2, ← e]
        nlinarith [sq_nonneg b])
    exact h4.trans ((avg_le hw key).trans hav)

/-- **Strong interference, `⊇`**: the known capacity region is contained in the frozen region
    (single phase, everything common: `Pⱼc = Pⱼ`, `Pⱼp = 0`). -/
theorem strong_subset_region {a b P₁ P₂ R₁ R₂ : ℝ} (ha : 1 ≤ a ^ 2) (hb : 1 ≤ b ^ 2)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (h : StrongInterferenceRegion a b P₁ P₂ R₁ R₂) :
    InGaussianHKRegion a b P₁ P₂ R₁ R₂ := by
  obtain ⟨h1, h2, hR₁, hR₂, hs₁, hs₂⟩ := h
  apply basic_mem_region
  refine ⟨h1, h2, P₁, 0, P₂, 0, hP₁, le_rfl, by simp, hP₂, le_rfl, by simp, ?_⟩
  have ca : cap P₂ ≤ cap (a ^ 2 * P₂) := cap_mono hP₂ (by nlinarith)
  have cb : cap P₁ ≤ cap (b ^ 2 * P₁) := cap_mono hP₁ (by nlinarith)
  simp only [mul_zero, add_zero, div_one, zero_add]
  have l1 : log2 1 = 0 := by simp [log2]
  rw [l1]
  unfold cap at ca cb hR₁ hR₂ hs₁ hs₂
  refine ⟨hR₁, hR₂, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **Regression (strong interference)**: for `a² ≥ 1`, `b² ≥ 1` the frozen region
    `InGaussianHKRegion` is exactly the Sato / Han–Kobayashi capacity region
    `{R₁ ≤ C(P₁), R₂ ≤ C(P₂), R₁ + R₂ ≤ min(C(P₁ + a²P₂), C(P₂ + b²P₁))}`. -/
theorem strong_region_eq {a b P₁ P₂ : ℝ} (ha : 1 ≤ a ^ 2) (hb : 1 ≤ b ^ 2)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) :
    {p : ℝ × ℝ | InGaussianHKRegion a b P₁ P₂ p.1 p.2} =
      {p : ℝ × ℝ | StrongInterferenceRegion a b P₁ P₂ p.1 p.2} := by
  ext ⟨R₁, R₂⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨hs₁, hs₂⟩ := strong_region_sum_le ha hb h
    exact ⟨h.1, h.2.1, region_R₁_le h, region_R₂_le h, hs₁, hs₂⟩
  · exact strong_subset_region ha hb hP₁ hP₂

/-! ### Operational side: `(0, 0)` is achievable -/

theorem zero_achievable (a b : ℝ) {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) :
    InGaussianICAchievable a b P₁ P₂ 0 0 := by
  refine ⟨le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  have hM : Nat.max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * 0)⌋₊ = 1 := by simp
  dsimp only
  rw [hM]
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0, measurable_const,
    measurable_const, fun _ => ?_, fun _ => ?_, ?_⟩
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hP₁
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hP₂
  · simp only [Fin.isValue, Subsingleton.elim _ (0 : Fin 1), ne_eq, not_true_eq_false, or_self,
      ite_false, MeasureTheory.lintegral_zero, ENNReal.toReal_zero, Finset.sum_const_zero,
      mul_zero]
    exact hε.le

end InfoTheory.Known.Certificates.GaussianInterferenceChannel
