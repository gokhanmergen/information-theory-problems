import InfoTheory.Bridge.CoverThomas
import InfoTheory.Known.Entropy
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv

/-!
# Mrs. Gerber's Lemma & Binary Symmetric Degraded Broadcast Channel

Purely additive, kernel-verified formalization of **Mrs. Gerber's Lemma**
(Wyner & Ziv, *IEEE Trans. Info. Theory*, 1973; Cover & Thomas §15.6.2;
El Gamal–Kim Ch. 5) in both scalar and `n`-letter vector forms, together with
its flagship application to the **Binary Symmetric Degraded Broadcast Channel**
(Bergmans 1973; Wyner & Ziv 1973):

1. **Binary Entropy & Inverse Binary Entropy on `[0, 1/2]`**:
   - Algebraic properties of `binaryConv` (`p ★ q = p(1 - q) + (1 - p)q`)
   - `binaryEntropy_continuousOn`, `binaryEntropy_strictMonoOn`
   - `invBinaryEntropy_mem_Icc`, `binaryEntropy_invBinaryEntropy`
   - `invBinaryEntropy_binaryEntropy`, `invBinaryEntropy_binaryEntropy_ge_half`
   - `invBinaryEntropy_strictMonoOn`, `invBinaryEntropy_mono`, `invBinaryEntropy_continuousOn`
2. **Convexity of the Mrs. Gerber Function `mglFun p u := h(h⁻¹(u) ★ p)`**:
   - `mglFun`, `mglFun_zero`, `mglFun_half`, `mglFun_binaryEntropy`, `mglFun_mono`
   - `convexOn_mglFun`: for every `p ∈ [0, 1/2]`, `u ↦ h(h⁻¹(u) ★ p)` is convex on `[0, 1]`,
     proved elementarily via `MonotoneOn.convexOn_of_deriv` and `HasDerivAt.of_local_left_inverse`.
3. **Scalar Mrs. Gerber's Lemma (Wyner–Ziv 1973)**:
   - `passFirstThrough`: passing `X` in `(X, U)` through a DMC `W` (`U — X — Y`)
   - `mrs_gerber_scalar`: `h(h⁻¹(H(X | U)) ★ p) ≤ H(Y | U)` for `Y = BSC(p)(X)`.
4. **Vector (`n`-Letter) Mrs. Gerber's Lemma (Wyner–Ziv 1973, Theorem 1)**:
   - `mrs_gerber_vector_cond`: `n · h(h⁻¹(H(X^n | U) / n) ★ p) ≤ H(Y^n | U)`
   - `mrs_gerber_vector`: `n · h(h⁻¹(H(X^n) / n) ★ p) ≤ H(Y^n)`.
5. **Flagship Application — Binary Symmetric Degraded Broadcast Channel (Bergmans 1973)**:
   - `degradedBSC`: physically degraded `BSC(p₁, p₂)` for `0 ≤ p₁ ≤ p₂ ≤ 1/2`
   - `degradedBSC_mutualInfo_U_Y2_le`: `I(U; Y₂) ≤ 1 - h(h⁻¹(H(X | U)) ★ p₂)`
   - `degradedBSC_bergmans_outer_bound`: every auxiliary `U — X — Y₁ — Y₂` satisfies
     `∃ α ∈ [0, 1/2], I(U; Y₂) ≤ 1 - h(α ★ p₂) ∧ I(X; Y₁ | U) ≤ h(α ★ p₁) - h(p₁)`
   - `degradedBSC_bergmans_achievable`: matching single-letter achievability for every `α ∈ [0, 1/2]`.

All definitions and theorems leave `Core/`, `Problems/`, `Known/`, and all other
`Bridge/` files untouched.
-/

open scoped BigOperators Topology
open InfoTheory InfoTheory.Bridge Set Filter

namespace InfoTheory.Bridge

/-! ### 1. Algebraic Properties of `binaryConv` & Analysis of `binaryEntropy` / `invBinaryEntropy` -/

section BinaryEntropyInverse

/-- Binary convolution is commutative: `p ★ q = q ★ p`. -/
theorem binaryConv_comm (p q : ℝ) : binaryConv p q = binaryConv q p := by
  unfold binaryConv; ring

/-- Binary convolution is associative: `(a ★ b) ★ c = a ★ (b ★ c)`. -/
theorem binaryConv_assoc (a b c : ℝ) :
    binaryConv (binaryConv a b) c = binaryConv a (binaryConv b c) := by
  unfold binaryConv; ring

/-- `p ★ 0 = p`. -/
theorem binaryConv_zero_right (p : ℝ) : binaryConv p 0 = p := by
  unfold binaryConv; ring

/-- `p ★ (1/2) = 1/2`. -/
theorem binaryConv_half_right (p : ℝ) : binaryConv p (1 / 2) = 1 / 2 := by
  unfold binaryConv; ring

/-- Complement symmetry of binary convolution: `(1 - a) ★ b = 1 - (a ★ b)`. -/
theorem binaryConv_one_sub_left (a b : ℝ) :
    binaryConv (1 - a) b = 1 - binaryConv a b := by
  unfold binaryConv; ring

/-- Binary convolution preserves `[0, 1/2]`: if `a, b ∈ [0, 1/2]`, then `a ★ b ∈ [0, 1/2]`. -/
theorem binaryConv_mem_Icc_half {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    0 ≤ binaryConv a b ∧ binaryConv a b ≤ 1 / 2 := by
  unfold binaryConv
  constructor
  · nlinarith
  · have : 1 - 2 * (a * (1 - b) + (1 - a) * b) = (1 - 2 * a) * (1 - 2 * b) := by ring
    have hnn : 0 ≤ (1 - 2 * a) * (1 - 2 * b) := mul_nonneg (by linarith) (by linarith)
    linarith

private lemma binaryConv_mem_Icc_unit {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ binaryConv a b ∧ binaryConv a b ≤ 1 := by
  unfold binaryConv
  constructor <;> nlinarith

private lemma log_two_pos_mgl : 0 < Real.log 2 := Real.log_pos one_lt_two

private lemma binaryEntropy_zero_val : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, negPLogP, log2]

private lemma binaryEntropy_one_val : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, negPLogP, log2]

/-- `binaryEntropy` is continuous on `[0, 1]`. -/
theorem binaryEntropy_continuousOn : ContinuousOn binaryEntropy (Icc 0 1) := by
  have hcont : ContinuousOn (fun p => Real.binEntropy p / Real.log 2) (Icc 0 1) :=
    (Real.binEntropy_continuous.div_const (Real.log 2)).continuousOn
  refine hcont.congr fun p hp => ?_
  exact InfoTheory.Known.binaryEntropy_eq_binEntropy hp.1 hp.2

/-- `binaryEntropy` is strictly increasing on `[0, 1/2]`. -/
theorem binaryEntropy_strictMonoOn : StrictMonoOn binaryEntropy (Icc 0 (1 / 2)) := by
  intro x hx y hy hxy
  rw [InfoTheory.Known.binaryEntropy_eq_binEntropy hx.1 (by linarith [hx.2]),
      InfoTheory.Known.binaryEntropy_eq_binEntropy hy.1 (by linarith [hy.2])]
  have hx' : x ∈ Icc (0 : ℝ) 2⁻¹ := ⟨hx.1, by linarith [hx.2]⟩
  have hy' : y ∈ Icc (0 : ℝ) 2⁻¹ := ⟨hy.1, by linarith [hy.2]⟩
  exact div_lt_div_of_pos_right (Real.binEntropy_strictMonoOn hx' hy' hxy) log_two_pos_mgl

private lemma exists_unique_preimage_binaryEntropy {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ x ∈ Icc (0 : ℝ) (1 / 2), binaryEntropy x = u := by
  have hcont : ContinuousOn binaryEntropy (Icc 0 (1 / 2)) :=
    binaryEntropy_continuousOn.mono (Icc_subset_Icc_right (by norm_num))
  have himg := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hcont
  rw [binaryEntropy_zero_val, InfoTheory.Known.binaryEntropy_half] at himg
  exact himg ⟨hu0, hu1⟩

private lemma invBinaryEntropy_eq_of_eq {x u : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hux : binaryEntropy x = u) : invBinaryEntropy u = x := by
  unfold invBinaryEntropy
  refine IsGreatest.csSup_eq ⟨⟨hx0, hx1, hux.le⟩, ?_⟩
  rintro p ⟨hp0, hp1, hpu⟩
  by_contra hlt
  push Not at hlt
  have hstrict := binaryEntropy_strictMonoOn ⟨hx0, hx1⟩ ⟨hp0, hp1⟩ hlt
  linarith

/-- For `u ∈ [0, 1]`, `invBinaryEntropy u ∈ [0, 1/2]`. -/
theorem invBinaryEntropy_mem_Icc {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ invBinaryEntropy u ∧ invBinaryEntropy u ≤ 1 / 2 := by
  obtain ⟨x, hx, hux⟩ := exists_unique_preimage_binaryEntropy hu0 hu1
  rw [invBinaryEntropy_eq_of_eq hx.1 hx.2 hux]
  exact hx

/-- Right inverse: for `u ∈ [0, 1]`, `h(h⁻¹(u)) = u`. -/
theorem binaryEntropy_invBinaryEntropy {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    binaryEntropy (invBinaryEntropy u) = u := by
  obtain ⟨x, hx, hux⟩ := exists_unique_preimage_binaryEntropy hu0 hu1
  rw [invBinaryEntropy_eq_of_eq hx.1 hx.2 hux, hux]

/-- Left inverse on `[0, 1/2]`: for `x ∈ [0, 1/2]`, `h⁻¹(h(x)) = x`. -/
theorem invBinaryEntropy_binaryEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    invBinaryEntropy (binaryEntropy x) = x :=
  invBinaryEntropy_eq_of_eq hx0 hx1 rfl

/-- Full `[0, 1]` left-inverse identity: `h⁻¹(h(x)) = min x (1 - x)`. -/
theorem invBinaryEntropy_binaryEntropy_ge_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    invBinaryEntropy (binaryEntropy x) = min x (1 - x) := by
  by_cases h : x ≤ 1 / 2
  · rw [invBinaryEntropy_binaryEntropy hx0 h, min_eq_left (by linarith)]
  · push Not at h
    rw [InfoTheory.Known.binaryEntropy_symm x,
        invBinaryEntropy_binaryEntropy (by linarith) (by linarith),
        min_eq_right (by linarith)]

/-- `invBinaryEntropy` is strictly increasing on `[0, 1]`. -/
theorem invBinaryEntropy_strictMonoOn : StrictMonoOn invBinaryEntropy (Icc 0 1) := by
  intro u hu v hv huv
  have hxu := invBinaryEntropy_mem_Icc hu.1 hu.2
  have hxv := invBinaryEntropy_mem_Icc hv.1 hv.2
  by_contra hle
  push Not at hle
  rcases hle.eq_or_lt with heq | hlt
  · have := binaryEntropy_invBinaryEntropy hu.1 hu.2
    have := binaryEntropy_invBinaryEntropy hv.1 hv.2
    linarith [congrArg binaryEntropy heq]
  · have hstrict := binaryEntropy_strictMonoOn hxv hxu hlt
    rw [binaryEntropy_invBinaryEntropy hv.1 hv.2,
        binaryEntropy_invBinaryEntropy hu.1 hu.2] at hstrict
    linarith

/-- `invBinaryEntropy` is monotone on `[0, 1]`. -/
theorem invBinaryEntropy_mono : MonotoneOn invBinaryEntropy (Icc 0 1) :=
  invBinaryEntropy_strictMonoOn.monotoneOn

private lemma invBinaryEntropy_mem_Ioo {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    invBinaryEntropy u ∈ Ioo (0 : ℝ) (1 / 2) := by
  have hmem := invBinaryEntropy_mem_Icc hu0.le hu1.le
  refine ⟨?_, ?_⟩
  · refine lt_of_le_of_ne hmem.1 ?_
    intro h0
    have := binaryEntropy_invBinaryEntropy hu0.le hu1.le
    rw [← h0, binaryEntropy_zero_val] at this
    linarith
  · refine lt_of_le_of_ne hmem.2 ?_
    intro hhalf
    have := binaryEntropy_invBinaryEntropy hu0.le hu1.le
    rw [hhalf, InfoTheory.Known.binaryEntropy_half] at this
    linarith

/-- `invBinaryEntropy` is continuous on `[0, 1]`. -/
theorem invBinaryEntropy_continuousOn : ContinuousOn invBinaryEntropy (Icc 0 1) := by
  rw [Metric.continuousOn_iff]
  intro u hu ε hε
  set x := invBinaryEntropy u
  have hx : x ∈ Icc (0 : ℝ) (1 / 2) := invBinaryEntropy_mem_Icc hu.1 hu.2
  have hux : binaryEntropy x = u := binaryEntropy_invBinaryEntropy hu.1 hu.2
  -- Choose a positive radius δ from the left and right preimage windows.
  have hleft : ∃ δ₁ > 0, ∀ v ∈ Icc (0 : ℝ) 1, u - δ₁ < v → x - ε < invBinaryEntropy v := by
    by_cases hx0 : x = 0
    · refine ⟨1, zero_lt_one, fun v hv _ => ?_⟩
      have := (invBinaryEntropy_mem_Icc hv.1 hv.2).1
      linarith
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      set xl := max 0 (x - ε / 2)
      have hxl_mem : xl ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hx.2])⟩
      have hxl_lt : xl < x := max_lt hxpos (by linarith)
      have hul_lt : binaryEntropy xl < u := by
        rw [← hux]; exact binaryEntropy_strictMonoOn hxl_mem hx hxl_lt
      refine ⟨u - binaryEntropy xl, sub_pos.mpr hul_lt, fun v hv hvu => ?_⟩
      have hv_gt : binaryEntropy xl < v := by linarith
      have hul_mem : binaryEntropy xl ∈ Icc (0 : ℝ) 1 :=
        ⟨InfoTheory.Known.binaryEntropy_nonneg hxl_mem.1 (by linarith [hxl_mem.2]),
         InfoTheory.Known.binaryEntropy_le_one hxl_mem.1 (by linarith [hxl_mem.2])⟩
      have hinv := invBinaryEntropy_strictMonoOn hul_mem hv hv_gt
      rw [invBinaryEntropy_binaryEntropy hxl_mem.1 hxl_mem.2] at hinv
      have : x - ε / 2 ≤ xl := le_max_right _ _
      linarith
  have hright : ∃ δ₂ > 0, ∀ v ∈ Icc (0 : ℝ) 1, v < u + δ₂ → invBinaryEntropy v < x + ε := by
    by_cases hx1 : x = 1 / 2
    · refine ⟨1, zero_lt_one, fun v hv _ => ?_⟩
      have := (invBinaryEntropy_mem_Icc hv.1 hv.2).2
      linarith
    · have hxlt : x < 1 / 2 := lt_of_le_of_ne hx.2 hx1
      set xr := min (1 / 2) (x + ε / 2)
      have hxr_mem : xr ∈ Icc (0 : ℝ) (1 / 2) := ⟨le_min (by norm_num) (by linarith [hx.1]), min_le_left _ _⟩
      have hx_lt_r : x < xr := lt_min hxlt (by linarith)
      have hu_lt_r : u < binaryEntropy xr := by
        rw [← hux]; exact binaryEntropy_strictMonoOn hx hxr_mem hx_lt_r
      refine ⟨binaryEntropy xr - u, sub_pos.mpr hu_lt_r, fun v hv hvu => ?_⟩
      have hv_lt : v < binaryEntropy xr := by linarith
      have hur_mem : binaryEntropy xr ∈ Icc (0 : ℝ) 1 :=
        ⟨InfoTheory.Known.binaryEntropy_nonneg hxr_mem.1 (by linarith [hxr_mem.2]),
         InfoTheory.Known.binaryEntropy_le_one hxr_mem.1 (by linarith [hxr_mem.2])⟩
      have hinv := invBinaryEntropy_strictMonoOn hv hur_mem hv_lt
      rw [invBinaryEntropy_binaryEntropy hxr_mem.1 hxr_mem.2] at hinv
      have : xr ≤ x + ε / 2 := min_le_right _ _
      linarith
  obtain ⟨δ₁, hδ₁, hL⟩ := hleft
  obtain ⟨δ₂, hδ₂, hR⟩ := hright
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun v hv hdist => ?_⟩
  rw [Real.dist_eq, abs_lt] at hdist ⊢
  have h1 := hL v hv (by linarith [min_le_left δ₁ δ₂])
  have h2 := hR v hv (by linarith [min_le_right δ₁ δ₂])
  constructor <;> linarith

end BinaryEntropyInverse

/-! ### 2. Convexity of the Mrs. Gerber Function `mglFun` -/

section MGLConvexity

/-- The Mrs. Gerber function `u ↦ h(h⁻¹(u) ★ p)` for crossover probability `p ∈ [0, 1/2]`. -/
noncomputable def mglFun (p u : ℝ) : ℝ :=
  binaryEntropy (binaryConv (invBinaryEntropy u) p)

/-- At `p = 0`, `mglFun 0 u = u` on `[0, 1]`. -/
theorem mglFun_zero {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : mglFun 0 u = u := by
  rw [mglFun, binaryConv_zero_right, binaryEntropy_invBinaryEntropy hu0 hu1]

/-- At `p = 1/2`, `mglFun (1/2) u = 1`. -/
theorem mglFun_half (u : ℝ) : mglFun (1 / 2) u = 1 := by
  rw [mglFun, binaryConv_half_right, InfoTheory.Known.binaryEntropy_half]

/-- Composition identity on the full unit interval `[0, 1]`: `mglFun p (h(t)) = h(t ★ p)`. -/
theorem mglFun_binaryEntropy (p : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mglFun p (binaryEntropy t) = binaryEntropy (binaryConv t p) := by
  unfold mglFun
  rw [invBinaryEntropy_binaryEntropy_ge_half ht0 ht1]
  by_cases h : t ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith), binaryConv_one_sub_left, ← InfoTheory.Known.binaryEntropy_symm]

/-- `mglFun p` is monotone nondecreasing on `[0, 1]` for every `p ∈ [0, 1/2]`. -/
theorem mglFun_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    MonotoneOn (mglFun p) (Icc 0 1) := by
  intro u hu v hv huv
  unfold mglFun
  have hxu := invBinaryEntropy_mem_Icc hu.1 hu.2
  have hxv := invBinaryEntropy_mem_Icc hv.1 hv.2
  have hconv_u := binaryConv_mem_Icc_half hxu.1 hxu.2 hp0 hp1
  have hconv_v := binaryConv_mem_Icc_half hxv.1 hxv.2 hp0 hp1
  have hle : binaryConv (invBinaryEntropy u) p ≤ binaryConv (invBinaryEntropy v) p := by
    have hinv_le := invBinaryEntropy_mono hu hv huv
    unfold binaryConv
    nlinarith
  exact binaryEntropy_strictMonoOn.monotoneOn hconv_u hconv_v hle

/-! #### Elementary Calculus Helpers for `convexOn_mglFun` -/

/-- Auxiliary log-odds function `A(w) = log(1 + w) - log(1 - w) = log((1 + w) / (1 - w))` on `(-1, 1)`. -/
private noncomputable def mglLogOdds (w : ℝ) : ℝ :=
  Real.log (1 + w) - Real.log (1 - w)

private lemma mglLogOdds_zero : mglLogOdds 0 = 0 := by
  simp [mglLogOdds]

private lemma mglLogOdds_pos {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) : 0 < mglLogOdds w := by
  unfold mglLogOdds
  have hlt : 1 - w < 1 + w := by linarith
  exact sub_pos.mpr (Real.log_lt_log (by linarith) hlt)

private lemma hasDerivAt_mglLogOdds {w : ℝ} (hw1 : -1 < w) (hw2 : w < 1) :
    HasDerivAt mglLogOdds (2 / (1 - w ^ 2)) w := by
  have h1 : 1 + w ≠ 0 := by linarith
  have h2 : 1 - w ≠ 0 := by linarith
  have hd1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + w)) w := by
    simpa using ((hasDerivAt_id w).const_add (1 : ℝ)).log h1
  have hd2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) ((-1) / (1 - w)) w := by
    simpa using ((hasDerivAt_id w).const_sub (1 : ℝ)).log h2
  have heq : 1 / (1 + w) - (-1) / (1 - w) = 2 / (1 - w ^ 2) := by
    have hfac : 1 - w ^ 2 = (1 + w) * (1 - w) := by ring
    rw [hfac]; field_simp [h1, h2]; ring
  rw [← heq]
  exact hd1.sub hd2

private lemma mglLogOdds_eq_sub_log {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (1 - x) - Real.log x = mglLogOdds (1 - 2 * x) := by
  unfold mglLogOdds
  have h1 : 1 + (1 - 2 * x) = 2 * (1 - x) := by ring
  have h2 : 1 - (1 - 2 * x) = 2 * x := by ring
  rw [h1, h2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by linarith)]
  ring

/-- `χ(w) = 2w - (1 + w²) A(w) < 0` on `(0, 1)`. -/
private noncomputable def mglChi (w : ℝ) : ℝ :=
  2 * w - (1 + w ^ 2) * mglLogOdds w

private lemma hasDerivAt_mglChi {w : ℝ} (hw1 : -1 < w) (hw2 : w < 1) :
    HasDerivAt mglChi (-2 * w * mglLogOdds w - 4 * w ^ 2 / (1 - w ^ 2)) w := by
  have hA := hasDerivAt_mglLogOdds hw1 hw2
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 w := by
    simpa using (hasDerivAt_id w).const_mul (2 : ℝ)
  have hquad : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * w) w := by
    have hp := (hasDerivAt_pow 2 w).const_add (1 : ℝ)
    simpa using hp
  have hsub := hlin.sub (hquad.mul hA)
  have heq : 2 - (2 * w * mglLogOdds w + (1 + w ^ 2) * (2 / (1 - w ^ 2))) =
      -2 * w * mglLogOdds w - 4 * w ^ 2 / (1 - w ^ 2) := by
    have hne : 1 - w ^ 2 ≠ 0 := by nlinarith
    field_simp [hne]; ring
  rw [← heq]
  exact hsub

private lemma mglChi_neg {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) : mglChi w < 0 := by
  have hcont : ContinuousOn mglChi (Ico 0 1) := fun t ht =>
    (hasDerivAt_mglChi (by linarith [ht.1]) ht.2).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn mglChi (Ico 0 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Ico 0 1) hcont fun t ht => ?_
    rw [interior_Ico] at ht
    rw [(hasDerivAt_mglChi (by linarith [ht.1]) ht.2).deriv]
    have ht0 : 0 < t := ht.1
    have hA : 0 < mglLogOdds t := mglLogOdds_pos ht.1 ht.2
    have hden : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hterm1 : 0 < 2 * t * mglLogOdds t := by positivity
    have hterm2 : 0 < 4 * t ^ 2 / (1 - t ^ 2) := by positivity
    linarith
  have hlt := hanti ⟨le_rfl, zero_lt_one⟩ ⟨hw0.le, hw1⟩ hw0
  simpa [mglChi, mglLogOdds_zero] using hlt

/-- `ψ(w) = (1 - w²) A(w) / w` is strictly decreasing on `(0, 1)`. -/
private noncomputable def mglPsi (w : ℝ) : ℝ :=
  (1 - w ^ 2) * mglLogOdds w / w

private lemma hasDerivAt_mglPsi {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    HasDerivAt mglPsi (mglChi w / w ^ 2) w := by
  have hA := hasDerivAt_mglLogOdds (by linarith) hw1
  have hquad : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * w)) w := by
    have hp := (hasDerivAt_pow 2 w).const_sub (1 : ℝ)
    simpa using hp
  have hdiv := (hquad.mul hA).div (hasDerivAt_id w) hw0.ne'
  have heq : ((-(2 * w) * mglLogOdds w + (1 - w ^ 2) * (2 / (1 - w ^ 2))) * w -
      (1 - w ^ 2) * mglLogOdds w * 1) / w ^ 2 = mglChi w / w ^ 2 := by
    unfold mglChi
    have hne : 1 - w ^ 2 ≠ 0 := by nlinarith
    field_simp [hw0.ne', hne]
    ring
  rw [← heq]
  exact hdiv

private lemma mglPsi_strictAntiOn : StrictAntiOn mglPsi (Ioo 0 1) := by
  have hcont : ContinuousOn mglPsi (Ioo 0 1) := fun t ht =>
    (hasDerivAt_mglPsi ht.1 ht.2).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1) hcont fun t ht => ?_
  rw [interior_Ioo] at ht
  rw [(hasDerivAt_mglPsi ht.1 ht.2).deriv]
  exact div_neg_of_neg_of_pos (mglChi_neg ht.1 ht.2) (sq_pos_of_pos ht.1)

/-- For `λ ∈ (0, 1)`, the ratio `w ↦ A(λw) / A(w)` is strictly decreasing on `(0, 1)`. -/
private lemma mglRatio_strictAntiOn {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictAntiOn (fun w => mglLogOdds (lam * w) / mglLogOdds w) (Ioo 0 1) := by
  have hderiv : ∀ w ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => mglLogOdds (lam * t) / mglLogOdds t)
        ((lam * (2 / (1 - (lam * w) ^ 2)) * mglLogOdds w -
          mglLogOdds (lam * w) * (2 / (1 - w ^ 2))) / (mglLogOdds w) ^ 2) w := by
    intro w hw
    have hlw0 : 0 < lam * w := mul_pos hlam0 hw.1
    have hlw1 : lam * w < 1 := by nlinarith [hw.2]
    have hcomp : HasDerivAt (fun t => mglLogOdds (lam * t))
        (2 / (1 - (lam * w) ^ 2) * lam) w :=
      (hasDerivAt_mglLogOdds (by linarith) hlw1).comp w (by simpa using (hasDerivAt_id w).const_mul lam)
    have hA := hasDerivAt_mglLogOdds (by linarith [hw.1]) hw.2
    have hAw_ne : mglLogOdds w ≠ 0 := (mglLogOdds_pos hw.1 hw.2).ne'
    convert hcomp.div hA hAw_ne using 1
    ring
  have hcont : ContinuousOn (fun w => mglLogOdds (lam * w) / mglLogOdds w) (Ioo 0 1) :=
    fun w hw => (hderiv w hw).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1) hcont fun w hw => ?_
  rw [interior_Ioo] at hw
  rw [(hderiv w hw).deriv]
  have hlw0 : 0 < lam * w := mul_pos hlam0 hw.1
  have hlw_lt : lam * w < w := by nlinarith [hw.1]
  have hlw1 : lam * w < 1 := lt_trans hlw_lt hw.2
  have hpsi := mglPsi_strictAntiOn ⟨hlw0, hlw1⟩ hw hlw_lt
  unfold mglPsi at hpsi
  have hden1 : 0 < 1 - w ^ 2 := by nlinarith [hw.1, hw.2]
  have hden2 : 0 < 1 - (lam * w) ^ 2 := by nlinarith [hlw0, hlw1]
  have hAw : 0 < mglLogOdds w := mglLogOdds_pos hw.1 hw.2
  have hnum_neg : lam * (2 / (1 - (lam * w) ^ 2)) * mglLogOdds w -
      mglLogOdds (lam * w) * (2 / (1 - w ^ 2)) < 0 := by
    -- From `(1 - w²) A(w) / w < (1 - (λw)²) A(λw) / (λw)`, clear positive denominators.
    have hmul : (1 - w ^ 2) * mglLogOdds w * (lam * w) <
        (1 - (lam * w) ^ 2) * mglLogOdds (lam * w) * w := by
      have h1 := (div_lt_div_iff₀ hw.1 hlw0).mp hpsi
      exact h1
    have hmul' : lam * (1 - w ^ 2) * mglLogOdds w <
        (1 - (lam * w) ^ 2) * mglLogOdds (lam * w) := by
      nlinarith [hw.1]
    have hdiv : lam * mglLogOdds w / (1 - (lam * w) ^ 2) <
        mglLogOdds (lam * w) / (1 - w ^ 2) := by
      rw [div_lt_div_iff₀ hden2 hden1]
      linarith
    have h2 : lam * (2 / (1 - (lam * w) ^ 2)) * mglLogOdds w =
        2 * (lam * mglLogOdds w / (1 - (lam * w) ^ 2)) := by ring
    have h3 : mglLogOdds (lam * w) * (2 / (1 - w ^ 2)) =
        2 * (mglLogOdds (lam * w) / (1 - w ^ 2)) := by ring
    linarith
  exact div_neg_of_neg_of_pos hnum_neg (sq_pos_of_pos hAw)

private lemma hasDerivAt_binaryEntropy {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt binaryEntropy (mglLogOdds (1 - 2 * x) / Real.log 2) x := by
  have hbin : HasDerivAt Real.binEntropy (Real.log (1 - x) - Real.log x) x := by
    have hd := (Real.differentiableAt_binEntropy hx0.ne' hx1.ne).hasDerivAt
    rwa [Real.deriv_binEntropy] at hd
  have hdiv := hbin.div_const (Real.log 2)
  rw [mglLogOdds_eq_sub_log hx0 hx1] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝 x := Ioo_mem_nhds hx0 hx1
  filter_upwards [hmem] with t ht
  exact InfoTheory.Known.binaryEntropy_eq_binEntropy ht.1.le ht.2.le

private lemma hasDerivAt_invBinaryEntropy {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt invBinaryEntropy (Real.log 2 / mglLogOdds (1 - 2 * invBinaryEntropy u)) u := by
  set x := invBinaryEntropy u
  have hx : x ∈ Ioo (0 : ℝ) (1 / 2) := invBinaryEntropy_mem_Ioo hu0 hu1
  have hcont : ContinuousAt invBinaryEntropy u :=
    invBinaryEntropy_continuousOn.continuousAt (Icc_mem_nhds hu0 hu1)
  have hf := hasDerivAt_binaryEntropy hx.1 (by linarith [hx.2])
  have hz0 : 0 < 1 - 2 * x := by linarith [hx.2]
  have hz1 : 1 - 2 * x < 1 := by linarith [hx.1]
  have hf'_ne : mglLogOdds (1 - 2 * x) / Real.log 2 ≠ 0 :=
    div_ne_zero (mglLogOdds_pos hz0 hz1).ne' log_two_pos_mgl.ne'
  have hfg : ∀ᶠ v in 𝓝 u, binaryEntropy (invBinaryEntropy v) = v := by
    filter_upwards [Icc_mem_nhds hu0 hu1] with v hv
    exact binaryEntropy_invBinaryEntropy hv.1 hv.2
  have hinv := hf.of_local_left_inverse hcont hf'_ne hfg
  simpa [inv_div] using hinv

private lemma hasDerivAt_mglFun {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1 / 2)
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (mglFun p)
      ((1 - 2 * p) * mglLogOdds ((1 - 2 * p) * (1 - 2 * invBinaryEntropy u)) /
        mglLogOdds (1 - 2 * invBinaryEntropy u)) u := by
  set x := invBinaryEntropy u
  set lam := 1 - 2 * p
  have hx : x ∈ Ioo (0 : ℝ) (1 / 2) := invBinaryEntropy_mem_Ioo hu0 hu1
  have hlam0 : 0 < lam := by linarith
  have hlam1 : lam < 1 := by linarith
  have hinv := hasDerivAt_invBinaryEntropy hu0 hu1
  have hconv_eq : (fun t => binaryConv t p) = (fun t => p + lam * t) := by
    funext t; unfold binaryConv; dsimp only [lam]; ring
  have hconv_deriv : HasDerivAt (fun t => binaryConv t p) lam x := by
    rw [hconv_eq]
    simpa using ((hasDerivAt_id x).const_mul lam).const_add p
  have hy0 : 0 < binaryConv x p := by unfold binaryConv; nlinarith [hx.1, hx.2]
  have hy1 : binaryConv x p < 1 / 2 := by
    have : 1 - 2 * binaryConv x p = lam * (1 - 2 * x) := by unfold binaryConv; dsimp only [lam]; ring
    have : 0 < lam * (1 - 2 * x) := mul_pos hlam0 (by linarith [hx.2])
    linarith
  have hbe := hasDerivAt_binaryEntropy hy0 (by linarith)
  have h1 : HasDerivAt (fun v => binaryConv (invBinaryEntropy v) p)
      (lam * (Real.log 2 / mglLogOdds (1 - 2 * x))) u := by
    have h := hconv_deriv.comp u hinv
    have hfun : ((fun t => binaryConv t p) ∘ invBinaryEntropy) =
        (fun v => binaryConv (invBinaryEntropy v) p) := rfl
    rwa [hfun] at h
  have hcomp : HasDerivAt (mglFun p)
      ((mglLogOdds (1 - 2 * binaryConv x p) / Real.log 2) *
        (lam * (Real.log 2 / mglLogOdds (1 - 2 * x)))) u := by
    have h := hbe.comp u h1
    have hfun : (binaryEntropy ∘ fun v => binaryConv (invBinaryEntropy v) p) = mglFun p := rfl
    rwa [hfun] at h
  have hval : (mglLogOdds (1 - 2 * binaryConv x p) / Real.log 2) *
      (lam * (Real.log 2 / mglLogOdds (1 - 2 * x))) =
      lam * mglLogOdds (lam * (1 - 2 * x)) / mglLogOdds (1 - 2 * x) := by
    have hz_eq : 1 - 2 * binaryConv x p = lam * (1 - 2 * x) := by
      unfold binaryConv; dsimp only [lam]; ring
    rw [hz_eq]
    have hlog2 : Real.log 2 ≠ 0 := log_two_pos_mgl.ne'
    have hA_ne : mglLogOdds (1 - 2 * x) ≠ 0 :=
      (mglLogOdds_pos (by linarith [hx.2]) (by linarith [hx.1])).ne'
    generalize mglLogOdds (lam * (1 - 2 * x)) = A1
    generalize mglLogOdds (1 - 2 * x) = A2 at hA_ne
    generalize Real.log 2 = L at hlog2
    field_simp [hlog2, hA_ne]
  rw [hval] at hcomp
  exact hcomp

/-- **Core Convexity of the Mrs. Gerber Function** (Wyner & Ziv 1973, Lemma 1):
    for every `p ∈ [0, 1/2]`, `u ↦ h(h⁻¹(u) ★ p)` is convex on `[0, 1]`. -/
theorem convexOn_mglFun {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    ConvexOn ℝ (Icc 0 1) (mglFun p) := by
  rcases hp0.eq_or_lt with rfl | hp0'
  · -- `p = 0`: `mglFun 0 u = u` on `[0, 1]`
    refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
    have hxy : a * x + b * y ∈ Icc (0 : ℝ) 1 := (convex_Icc 0 1) hx hy ha hb hab
    simp only [smul_eq_mul]
    rw [mglFun_zero hxy.1 hxy.2, mglFun_zero hx.1 hx.2, mglFun_zero hy.1 hy.2]
  rcases hp1.eq_or_lt with rfl | hp1'
  · -- `p = 1/2`: `mglFun (1/2) u = 1`
    refine ⟨convex_Icc 0 1, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul, mglFun_half, mul_one]
    linarith
  -- Interior case `0 < p < 1/2`: apply `MonotoneOn.convexOn_of_deriv`.
  set lam := 1 - 2 * p
  have hlam0 : 0 < lam := by linarith
  have hlam1 : lam < 1 := by linarith
  have hcont_conv : Continuous (fun t => binaryConv t p) := by
    unfold binaryConv; fun_prop
  have hmaps : MapsTo (fun u => binaryConv (invBinaryEntropy u) p) (Icc 0 1) (Icc 0 1) := by
    intro u hu
    have hxu := invBinaryEntropy_mem_Icc hu.1 hu.2
    have hc := binaryConv_mem_Icc_half hxu.1 hxu.2 hp0 hp1
    exact ⟨hc.1, by linarith [hc.2]⟩
  have hcont : ContinuousOn (mglFun p) (Icc 0 1) :=
    binaryEntropy_continuousOn.comp
      (hcont_conv.continuousOn.comp invBinaryEntropy_continuousOn (fun _ _ => mem_univ _))
      hmaps
  have hdiff : DifferentiableOn ℝ (mglFun p) (interior (Icc 0 1)) := by
    rw [interior_Icc]
    intro u hu
    exact (hasDerivAt_mglFun hp0' hp1' hu.1 hu.2).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (deriv (mglFun p)) (interior (Icc 0 1)) := by
    rw [interior_Icc]
    intro u hu v hv huv
    rw [(hasDerivAt_mglFun hp0' hp1' hu.1 hu.2).deriv,
        (hasDerivAt_mglFun hp0' hp1' hv.1 hv.2).deriv]
    have hxu := invBinaryEntropy_mem_Ioo hu.1 hu.2
    have hxv := invBinaryEntropy_mem_Ioo hv.1 hv.2
    have hzu : 1 - 2 * invBinaryEntropy u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hxu.2], by linarith [hxu.1]⟩
    have hzv : 1 - 2 * invBinaryEntropy v ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hxv.2], by linarith [hxv.1]⟩
    have hzle : 1 - 2 * invBinaryEntropy v ≤ 1 - 2 * invBinaryEntropy u := by
      have := invBinaryEntropy_mono (Ioo_subset_Icc_self hu) (Ioo_subset_Icc_self hv) huv
      linarith
    have hratio := (mglRatio_strictAntiOn hlam0 hlam1).antitoneOn hzv hzu hzle
    have h1 : lam * mglLogOdds (lam * (1 - 2 * invBinaryEntropy u)) /
        mglLogOdds (1 - 2 * invBinaryEntropy u) =
        lam * (mglLogOdds (lam * (1 - 2 * invBinaryEntropy u)) /
          mglLogOdds (1 - 2 * invBinaryEntropy u)) := by ring
    have h2 : lam * mglLogOdds (lam * (1 - 2 * invBinaryEntropy v)) /
        mglLogOdds (1 - 2 * invBinaryEntropy v) =
        lam * (mglLogOdds (lam * (1 - 2 * invBinaryEntropy v)) /
          mglLogOdds (1 - 2 * invBinaryEntropy v)) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hratio hlam0.le
  exact hmono.convexOn_of_deriv (convex_Icc 0 1) hcont hdiff

end MGLConvexity

/-! ### 3. Scalar Mrs. Gerber's Lemma (Wyner–Ziv 1973) -/

section ScalarMGL

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

private lemma probDist_ext {α : Type*} [Fintype α] {P Q : ProbDist α}
    (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; exact funext h

/-- Joint distribution of `(Y, U)` when `(X, U) ~ P` and `X` passes through a DMC `W`
    (forming the Markov chain `U — X — Y`). -/
def passFirstThrough (W : DMC α β) (P : ProbDist (α × γ)) : ProbDist (β × γ) where
  pmf := fun yu => ∑ x : α, P.pmf (x, yu.2) * W.trans x yu.1
  nonneg := fun yu => Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg (x, yu.2)) (W.nonneg x yu.1)
  sum_one := by
    rw [Fintype.sum_prod_type_right]
    trans (∑ u : γ, ∑ x : α, P.pmf (x, u))
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp only
      rw [← Finset.mul_sum, W.sum_one, mul_one]
    · rw [← Fintype.sum_prod_type_right]
      exact P.sum_one

private lemma passFirstThrough_snd (W : DMC α β) (P : ProbDist (α × γ)) :
    (passFirstThrough W P).snd = P.snd := by
  apply probDist_ext; intro u
  unfold passFirstThrough ProbDist.snd
  dsimp only
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, W.sum_one, mul_one]

private lemma passFirstThrough_fst (W : DMC α β) (P : ProbDist (α × γ)) :
    (passFirstThrough W P).fst = (W.joint P.fst).snd := by
  apply probDist_ext; intro y
  unfold passFirstThrough ProbDist.fst ProbDist.snd DMC.joint
  dsimp only
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]

private lemma negPLogP_mul_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    negPLogP (s * t) = s * negPLogP t + t * negPLogP s := by
  rcases hs.eq_or_lt with rfl | hs'
  · simp [negPLogP]
  rcases ht.eq_or_lt with rfl | ht'
  · simp [negPLogP]
  have hst : 0 < s * t := mul_pos hs' ht'
  simp only [negPLogP, not_le.mpr hs', not_le.mpr ht', not_le.mpr hst, ↓reduceIte]
  rw [log2_mul_pos hs' ht']
  ring

private lemma condEntropy_bool_eq_sum {U : Type*} [Fintype U] (P : ProbDist (Bool × U)) :
    condEntropy P =
      ∑ u : U, P.snd.pmf u *
        binaryEntropy (if P.snd.pmf u = 0 then 0 else P.pmf (true, u) / P.snd.pmf u) := by
  unfold condEntropy shannonEntropy
  rw [Fintype.sum_prod_type_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsum_u : P.pmf (true, u) + P.pmf (false, u) = P.snd.pmf u := by
    simp [ProbDist.snd]
  have hbool : (∑ b : Bool, negPLogP (P.pmf (b, u))) =
      negPLogP (P.pmf (true, u)) + negPLogP (P.pmf (false, u)) := by
    simp [add_comm]
  rw [hbool]
  by_cases hs : P.snd.pmf u = 0
  · have ht0 : P.pmf (true, u) = 0 := by linarith [P.nonneg (true, u), P.nonneg (false, u)]
    have hf0 : P.pmf (false, u) = 0 := by linarith [P.nonneg (true, u), P.nonneg (false, u)]
    simp [hs, ht0, hf0, negPLogP]
  · simp only [hs, ↓reduceIte]
    have hspos : 0 < P.snd.pmf u := lt_of_le_of_ne (P.snd.nonneg u) (Ne.symm hs)
    set q := P.pmf (true, u) / P.snd.pmf u
    have hq0 : 0 ≤ q := div_nonneg (P.nonneg (true, u)) hspos.le
    have hq1 : q ≤ 1 := (div_le_one hspos).mpr (by linarith [P.nonneg (false, u)])
    have htrue : P.pmf (true, u) = P.snd.pmf u * q := by
      dsimp only [q]; field_simp [hs]
    have hfalse : P.pmf (false, u) = P.snd.pmf u * (1 - q) := by
      dsimp only [q]; field_simp [hs]; linarith
    rw [htrue, hfalse, negPLogP_mul_nonneg hspos.le hq0,
        negPLogP_mul_nonneg hspos.le (by linarith)]
    unfold binaryEntropy
    ring

/-- **Scalar Mrs. Gerber's Lemma** (Wyner & Ziv 1973; Cover & Thomas §15.6.2):
    for any finite auxiliary variable `U`, joint distribution `P_XU` on `Bool × U`, and
    crossover probability `p ∈ [0, 1/2]`, letting `P_YU` be the joint distribution of `(Y, U)`
    when `X` passes through `BSC(p)`,
    `h(h⁻¹(H(X | U)) ★ p) ≤ H(Y | U)`. -/
theorem mrs_gerber_scalar {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    binaryEntropy (binaryConv (invBinaryEntropy (condEntropy P_XU)) p) ≤
      condEntropy (passFirstThrough (bsc p hp0 (by linarith)) P_XU) := by
  set W := bsc p hp0 (by linarith)
  set P_YU := passFirstThrough W P_XU
  set q : U → ℝ := fun u => if P_XU.snd.pmf u = 0 then 0 else P_XU.pmf (true, u) / P_XU.snd.pmf u
  have hq_mem : ∀ u : U, 0 ≤ q u ∧ q u ≤ 1 := by
    intro u
    dsimp only [q]
    split_ifs with hs
    · exact ⟨le_rfl, zero_le_one⟩
    · have hspos : 0 < P_XU.snd.pmf u := lt_of_le_of_ne (P_XU.snd.nonneg u) (Ne.symm hs)
      have hsum : P_XU.pmf (true, u) + P_XU.pmf (false, u) = P_XU.snd.pmf u := by
        simp [ProbDist.snd]
      exact ⟨div_nonneg (P_XU.nonneg _) hspos.le,
             (div_le_one hspos).mpr (by linarith [P_XU.nonneg (false, u)])⟩
  have hH_XU : condEntropy P_XU = ∑ u : U, P_XU.snd.pmf u * binaryEntropy (q u) :=
    condEntropy_bool_eq_sum P_XU
  have hH_YU : condEntropy P_YU = ∑ u : U, P_XU.snd.pmf u * mglFun p (binaryEntropy (q u)) := by
    rw [condEntropy_bool_eq_sum P_YU]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hsnd : P_YU.snd.pmf u = P_XU.snd.pmf u := by
      have h := passFirstThrough_snd W P_XU
      exact congrArg (fun Q => Q.pmf u) h
    rw [hsnd]
    by_cases hs : P_XU.snd.pmf u = 0
    · simp [hs]
    · simp only [hs, ↓reduceIte]
      rw [mglFun_binaryEntropy p (hq_mem u).1 (hq_mem u).2]
      congr 2
      have hpyu : P_YU.pmf (true, u) = P_XU.pmf (true, u) * (1 - p) + P_XU.pmf (false, u) * p := by
        simp [P_YU, passFirstThrough, W, bsc, add_comm]
      have hsum : P_XU.pmf (true, u) + P_XU.pmf (false, u) = P_XU.snd.pmf u := by
        simp [ProbDist.snd]
      have hfalse : P_XU.pmf (false, u) = P_XU.snd.pmf u - P_XU.pmf (true, u) := by linarith
      rw [hpyu, hfalse]
      dsimp only [q]
      simp only [hs, ↓reduceIte]
      unfold binaryConv
      field_simp [hs]
  have hjensen := (convexOn_mglFun hp0 hp1).map_sum_le
    (t := Finset.univ)
    (w := fun u => P_XU.snd.pmf u)
    (p := fun u => binaryEntropy (q u))
    (fun u _ => P_XU.snd.nonneg u)
    P_XU.snd.sum_one
    (fun u _ => ⟨InfoTheory.Known.binaryEntropy_nonneg (hq_mem u).1 (hq_mem u).2,
                 InfoTheory.Known.binaryEntropy_le_one (hq_mem u).1 (hq_mem u).2⟩)
  simp only [smul_eq_mul] at hjensen
  change mglFun p (condEntropy P_XU) ≤ condEntropy P_YU
  rw [hH_XU, hH_YU]
  exact hjensen

end ScalarMGL

/-! ### 4. Vector (`n`-Letter) Mrs. Gerber's Lemma (Wyner–Ziv 1973, Theorem 1) -/

section VectorMGL

private def finSplitEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by funext i; refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by ext <;> simp

private def finOneEquiv : (Fin 1 → Bool) ≃ Bool where
  toFun x := x 0
  invFun b _ := b
  left_inv x := by funext i; fin_cases i; rfl
  right_inv _ := rfl

private lemma log2_two_val : log2 2 = 1 := by
  unfold log2; exact div_self log_two_pos_mgl.ne'

private lemma condEntropy_bool_le_one {U : Type*} [Fintype U] (P : ProbDist (Bool × U)) :
    condEntropy P ≤ 1 := by
  have h := condEntropy_le_log2_card P
  simpa [Fintype.card_bool, log2_two_val] using h

private lemma condEntropy_fin_bool_le {n : ℕ} {U : Type*} [Fintype U]
    (P : ProbDist ((Fin n → Bool) × U)) :
    condEntropy P ≤ (n : ℝ) := by
  have h := condEntropy_le_log2_card P
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    simp [Fintype.card_bool, Fintype.card_fin]
  rw [hcard, log2, Real.log_pow] at h
  have hmul : (n : ℝ) * Real.log 2 / Real.log 2 = (n : ℝ) := by
    field_simp [log_two_pos_mgl.ne']
  linarith

private lemma condEntropy_map_fst_equiv {α β U : Type*} [Fintype α] [Fintype β] [Fintype U]
    (e : α ≃ β) (P : ProbDist (α × U)) :
    condEntropy (P.map (fun t => (e t.1, t.2))) = condEntropy P := by
  classical
  let eProd : (α × U) ≃ (β × U) := e.prodCongr (Equiv.refl U)
  have hmap : P.map (fun t => (e t.1, t.2)) = P.map eProd := rfl
  have hsnd : (P.map (fun t => (e t.1, t.2))).snd = P.snd := by
    unfold ProbDist.snd ProbDist.map
    congr
    funext u
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single (e a)]
      · simp
      · intro b _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro u' _ hne
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold condEntropy
  rw [hsnd, hmap, shannonEntropy_map_equiv eProd P]

private lemma condEntropy_chain_triple {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (Q : ProbDist ((α × β) × γ)) :
    condEntropy Q =
      condEntropy (Q.map (fun t => (t.1.1, (t.1.2, t.2)))) +
        condEntropy (Q.map (fun t => (t.1.2, t.2))) := by
  classical
  let eAssoc : ((α × β) × γ) ≃ (α × (β × γ)) := Equiv.prodAssoc α β γ
  have h1 : Q.map (fun t => (t.1.1, (t.1.2, t.2))) = Q.map eAssoc := rfl
  have hsnd1 : (Q.map (fun t => (t.1.1, (t.1.2, t.2)))).snd = Q.map (fun t => (t.1.2, t.2)) := by
    unfold ProbDist.snd ProbDist.map
    congr
    funext ⟨b, c⟩
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t.1.2 = b ∧ t.2 = c
    · rw [Finset.sum_eq_single t.1.1]
      · simp [h]
      · intro a _ hne; simp [hne.symm]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · have hfalse : ¬ (t.1.2, t.2) = (b, c) := fun heq => h ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩
      simp only [hfalse, ↓reduceIte]
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ¬ (t.1.1, (t.1.2, t.2)) = (a, (b, c)) := fun heq =>
        h ⟨(Prod.mk.inj (Prod.mk.inj heq).2).1, (Prod.mk.inj (Prod.mk.inj heq).2).2⟩
      simp [this]
  have hsnd2 : (Q.map (fun t => (t.1.2, t.2))).snd = Q.snd := by
    unfold ProbDist.snd ProbDist.map
    congr
    funext c
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single ab.2]
      · simp
      · intro b _ hne; simp [hne.symm]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · intro c' _ hne
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  unfold condEntropy
  rw [hsnd1, hsnd2, h1, shannonEntropy_map_equiv eAssoc Q]
  ring

private lemma condEntropy_dpi_channel {α β γ U : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype U]
    (Q : ProbDist ((α × β) × U)) (W : DMC β γ) :
    condEntropy (Q.map (fun t => (t.1.1, (t.1.2, t.2)))) ≤
      condEntropy
        { pmf := fun z : α × (γ × U) => ∑ b : β, Q.pmf ((z.1, b), z.2.2) * W.trans b z.2.1
          nonneg := fun z => Finset.sum_nonneg fun b _ =>
            mul_nonneg (Q.nonneg ((z.1, b), z.2.2)) (W.nonneg b z.2.1)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [Fintype.sum_prod_type_right]
            trans (∑ a : α, ∑ u : U, ∑ b : β, Q.pmf ((a, b), u))
            · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [← Finset.mul_sum, W.sum_one, mul_one]
            · trans (∑ ab : α × β, ∑ u : U, Q.pmf (ab, u))
              · rw [Fintype.sum_prod_type]
                refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
              · rw [← Fintype.sum_prod_type]
                exact Q.sum_one } := by
  classical
  -- Construct the full joint distribution `R` of `(X₀, Y', (X', U))`.
  let R : ProbDist (α × γ × (β × U)) :=
    { pmf := fun t => Q.pmf ((t.1, t.2.2.1), t.2.2.2) * W.trans t.2.2.1 t.2.1
      nonneg := fun t => mul_nonneg (Q.nonneg _) (W.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        trans (∑ a : α, ∑ bu : β × U, Q.pmf ((a, bu.1), bu.2))
        · refine Finset.sum_congr rfl fun a _ => ?_
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl fun bu _ => ?_
          dsimp only
          rw [← Finset.mul_sum, W.sum_one, mul_one]
        · trans (∑ ab : α × β, ∑ u : U, Q.pmf (ab, u))
          · calc ∑ a : α, ∑ bu : β × U, Q.pmf ((a, bu.1), bu.2)
              _ = ∑ a : α, ∑ b : β, ∑ u : U, Q.pmf ((a, b), u) :=
                  Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type (fun bu : β × U => Q.pmf ((a, bu.1), bu.2))
              _ = ∑ ab : α × β, ∑ u : U, Q.pmf (ab, u) :=
                  (Fintype.sum_prod_type (fun ab : α × β => ∑ u : U, Q.pmf (ab, u))).symm
          · rw [← Fintype.sum_prod_type]
            exact Q.sum_one }
  -- Helper pmf identities for `R`'s three marginals used in `condMutualInfo R`.
  have hR_xz : ∀ a bu, (R.map (fun t => (t.1, t.2.2))).pmf (a, bu) =
      Q.pmf ((a, bu.1), bu.2) := by
    intro a bu
    unfold R ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single bu]
      · simp [← Finset.mul_sum, W.sum_one]
      · intro bu' _ hne; exact Finset.sum_eq_zero fun c _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a' _ hne
      exact Finset.sum_eq_zero fun t _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR_z : ∀ bu, (R.map (fun t => t.2.2)).pmf bu = ∑ a : α, Q.pmf ((a, bu.1), bu.2) := by
    intro bu
    unfold R ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single bu]
    · simp [← Finset.mul_sum, W.sum_one]
    · intro bu' _ hne; exact Finset.sum_eq_zero fun c _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR_yz : ∀ c bu, (R.map (fun t => (t.2.1, t.2.2))).pmf (c, bu) =
      (∑ a : α, Q.pmf ((a, bu.1), bu.2)) * W.trans bu.1 c := by
    intro c bu
    unfold R ProbDist.map; dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single bu]
      · simp
      · intro bu' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c' _ hne; exact Finset.sum_eq_zero fun bu' _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Markov property `I(X₀; Y' | X', U) = 0`: `R = condIndepDist R`.
  have hMarkov : condMutualInfo R = 0 := by
    rw [condMutualInfo_eq_zero_iff]
    apply probDist_ext
    rintro ⟨a, c, bu⟩
    change R.pmf (a, c, bu) =
      if (R.map (fun t => t.2.2)).pmf bu = 0 then 0
      else (R.map (fun t => (t.1, t.2.2))).pmf (a, bu) *
           (R.map (fun t => (t.2.1, t.2.2))).pmf (c, bu) /
           (R.map (fun t => t.2.2)).pmf bu
    rw [hR_xz a bu, hR_yz c bu, hR_z bu]
    by_cases hsum0 : (∑ a' : α, Q.pmf ((a', bu.1), bu.2)) = 0
    · simp only [hsum0, ↓reduceIte]
      have ha0 : Q.pmf ((a, bu.1), bu.2) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => Q.nonneg _)).mp hsum0 a (Finset.mem_univ a)
      change Q.pmf ((a, bu.1), bu.2) * W.trans bu.1 c = 0
      rw [ha0, zero_mul]
    · simp only [hsum0, ↓reduceIte]
      change Q.pmf ((a, bu.1), bu.2) * W.trans bu.1 c = _
      field_simp [hsum0]
  -- Nonnegativity of `I(X₀; X' | Y', U)`.
  let eSwap : (α × γ × (β × U)) ≃ (α × β × (γ × U)) :=
    { toFun := fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2))
      invFun := fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2))
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  let R' : ProbDist (α × β × (γ × U)) := R.map eSwap
  have hcmi_nonneg : 0 ≤ condMutualInfo R' := condMutualInfo_nonneg R'
  -- Identify the marginals appearing in `condMutualInfo R` and `condMutualInfo R'`.
  let P_a_cu : ProbDist (α × (γ × U)) :=
    { pmf := fun z => ∑ b : β, Q.pmf ((z.1, b), z.2.2) * W.trans b z.2.1
      nonneg := fun z => Finset.sum_nonneg fun b _ => mul_nonneg (Q.nonneg _) (W.nonneg _ _)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type_right]
        trans (∑ a : α, ∑ u : U, ∑ b : β, Q.pmf ((a, b), u))
        · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.mul_sum, W.sum_one, mul_one]
        · trans (∑ ab : α × β, ∑ u : U, Q.pmf (ab, u))
          · rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          · rw [← Fintype.sum_prod_type]; exact Q.sum_one }
  have hQ_eq : R.map (fun t => (t.1, t.2.2)) = Q.map (fun t => (t.1.1, (t.1.2, t.2))) := by
    apply probDist_ext
    rintro ⟨a, bu⟩
    rw [hR_xz a bu]
    unfold ProbDist.map; dsimp only
    rw [Finset.sum_eq_single ((a, bu.1), bu.2)]
    · simp
    · intro t _ hne
      have : ¬ (t.1.1, (t.1.2, t.2)) = (a, bu) := fun heq => by
        apply hne
        rcases t with ⟨⟨ta, tb⟩, tu⟩
        rcases bu with ⟨b, u⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        rfl
      simp [this]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hQsnd_eq : R.map (fun t => t.2.2) = (Q.map (fun t => (t.1.1, (t.1.2, t.2)))).snd := by
    rw [← hQ_eq]
    apply probDist_ext; intro bu
    unfold ProbDist.snd ProbDist.map; dsimp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t.2.2 = bu
    · rw [Finset.sum_eq_single t.1]
      · simp [ht]
      · intro a _ hne; simp [hne.symm]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · simp only [ht, ↓reduceIte]
      exact (Finset.sum_eq_zero fun a _ => by simp [ht]).symm
  have hR'_xz : R'.map (fun t => (t.1, t.2.2)) = P_a_cu := by
    rw [map_comp_eq]
    apply probDist_ext
    rintro ⟨a, c, u⟩
    unfold P_a_cu ProbDist.map R; dsimp only [Function.comp_apply, eSwap]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single u]
        · simp
        · intro u' _ hne; simp [hne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · intro c' _ hne; exact Finset.sum_eq_zero fun bu _ => by simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · intro a' _ hne; exact Finset.sum_eq_zero fun t _ => by simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hR'_z : R'.map (fun t => t.2.2) = P_a_cu.snd := by
    rw [← hR'_xz]
    unfold ProbDist.snd ProbDist.map
    congr
    funext cu
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t.2.2 = cu
    · rw [Finset.sum_eq_single t.1]
      · simp [ht]
      · intro a _ hne; simp [hne.symm]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · simp only [ht, ↓reduceIte]
      exact (Finset.sum_eq_zero fun a _ => by simp [ht]).symm
  have hR'_yz : shannonEntropy (R'.map (fun t => (t.2.1, t.2.2))) =
      shannonEntropy (R.map (fun t => (t.2.1, t.2.2))) := by
    let eMid : (γ × (β × U)) ≃ (β × (γ × U)) :=
      { toFun := fun t => (t.2.1, (t.1, t.2.2))
        invFun := fun t => (t.2.1, (t.1, t.2.2))
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    rw [← shannonEntropy_map_equiv eMid (R.map (fun t => (t.2.1, t.2.2))),
        map_comp_eq, map_comp_eq]
    rfl
  have hR'_ent : shannonEntropy R' = shannonEntropy R :=
    shannonEntropy_map_equiv eSwap R
  unfold condMutualInfo at hMarkov hcmi_nonneg
  dsimp only at hMarkov hcmi_nonneg
  rw [hQ_eq, hQsnd_eq] at hMarkov
  rw [hR'_xz, hR'_z, hR'_yz, hR'_ent] at hcmi_nonneg
  unfold condEntropy
  linarith

/-- **Vector (`n`-Letter) Conditional Mrs. Gerber's Lemma** (Wyner & Ziv 1973, Theorem 1):
    for every `n ≥ 1`, auxiliary finite type `U`, joint distribution `P_XU` on
    `(Fin n → Bool) × U`, and `p ∈ [0, 1/2]`, letting `P_YU` be the joint distribution of
    `(Y^n, U)` when `X^n` passes through `BSC(p)^n`,
    `n · h(h⁻¹(H(X^n | U) / n) ★ p) ≤ H(Y^n | U)`. -/
theorem mrs_gerber_vector_cond : ∀ (n : ℕ) (_ : 0 < n) {U : Type*} [Fintype U]
    (P_XU : ProbDist ((Fin n → Bool) × U)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2),
    (n : ℝ) * binaryEntropy (binaryConv (invBinaryEntropy (condEntropy P_XU / (n : ℝ))) p) ≤
      condEntropy (passFirstThrough ((bsc p hp0 (by linarith)).power n) P_XU)
  | 0, hn, _, _, _, _, _, _ => absurd hn (Nat.lt_irrefl 0)
  | 1, _, U, _, P_XU, p, hp0, hp1 => by
    -- Base case `n = 1`: reduce to `mrs_gerber_scalar` via `finOneEquiv : (Fin 1 → Bool) ≃ Bool`.
    let W1 := bsc p hp0 (by linarith)
    let Q_XU : ProbDist (Bool × U) := P_XU.map (fun t => (finOneEquiv t.1, t.2))
    have hX : condEntropy Q_XU = condEntropy P_XU :=
      condEntropy_map_fst_equiv finOneEquiv P_XU
    have hY_eq : (passFirstThrough (W1.power 1) P_XU).map (fun t => (finOneEquiv t.1, t.2)) =
        passFirstThrough W1 Q_XU := by
      classical
      apply probDist_ext
      rintro ⟨b, u⟩
      have hL : ((passFirstThrough (W1.power 1) P_XU).map (fun t => (finOneEquiv t.1, t.2))).pmf (b, u) =
          ∑ x : Fin 1 → Bool, P_XU.pmf (x, u) * W1.trans (x 0) b := by
        unfold ProbDist.map passFirstThrough DMC.power; dsimp only
        rw [Fintype.sum_prod_type, Finset.sum_eq_single (finOneEquiv.symm b)]
        · rw [Finset.sum_eq_single u]
          · simp [finOneEquiv]
          · intro u' _ hne; simp [hne]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        · intro y _ hne
          exact Finset.sum_eq_zero fun u' _ => by
            have hy : finOneEquiv y ≠ b := fun h => hne ((Equiv.eq_symm_apply finOneEquiv).mpr h)
            simp [hy]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      have hR : (passFirstThrough W1 Q_XU).pmf (b, u) =
          ∑ x : Fin 1 → Bool, P_XU.pmf (x, u) * W1.trans (x 0) b := by
        unfold passFirstThrough; dsimp only
        refine (Fintype.sum_equiv finOneEquiv _ _ fun x => ?_).symm
        have hQx : Q_XU.pmf (finOneEquiv x, u) = P_XU.pmf (x, u) := by
          unfold Q_XU ProbDist.map; dsimp only
          rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single u]
            · simp
            · intro u' _ hne; simp [hne]
            · intro hmem; exact absurd (Finset.mem_univ _) hmem
          · intro x' _ hne
            exact Finset.sum_eq_zero fun u' _ => by
              have hx : finOneEquiv x' ≠ finOneEquiv x := fun h => hne (finOneEquiv.injective h)
              simp [hx]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [hQx]; rfl
      rw [hL, hR]
    have hY : condEntropy (passFirstThrough W1 Q_XU) =
        condEntropy (passFirstThrough (W1.power 1) P_XU) := by
      rw [← hY_eq]
      exact condEntropy_map_fst_equiv finOneEquiv _
    have hsc := mrs_gerber_scalar Q_XU hp0 hp1
    rw [hX, hY] at hsc
    simpa using hsc
  | n + 2, _, U, _, P_XU, p, hp0, hp1 => by
    -- Inductive step from `m = n + 1 ≥ 1` to `m + 1 = n + 2`.
    set m := n + 1
    have hm_pos : 0 < m := Nat.succ_pos n
    have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have hm1_real : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    let W := bsc p hp0 (by linarith)
    let Wn := W.power m
    let Q_XU : ProbDist ((Bool × (Fin m → Bool)) × U) :=
      P_XU.map (fun t => (finSplitEquiv m t.1, t.2))
    let P_YU := passFirstThrough (W.power (m + 1)) P_XU
    let Q_YU : ProbDist ((Bool × (Fin m → Bool)) × U) :=
      P_YU.map (fun t => (finSplitEquiv m t.1, t.2))
    have hH_X_eq : condEntropy Q_XU = condEntropy P_XU :=
      condEntropy_map_fst_equiv (finSplitEquiv m) P_XU
    have hH_Y_eq : condEntropy Q_YU = condEntropy P_YU :=
      condEntropy_map_fst_equiv (finSplitEquiv m) P_YU
    -- Chain rule on both `Q_XU` and `Q_YU`.
    have hchain_X := condEntropy_chain_triple Q_XU
    have hchain_Y := condEntropy_chain_triple Q_YU
    -- Explicit pmf of `Q_XU` and `Q_YU`.
    have hQ_XU_pmf : ∀ x0 (x' : Fin m → Bool) u,
        Q_XU.pmf ((x0, x'), u) = P_XU.pmf (Fin.cons x0 x', u) := by
      classical
      intro x0 x' u
      unfold Q_XU ProbDist.map; dsimp only
      rw [Finset.sum_eq_single (Fin.cons x0 x', u)]
      · simp [finSplitEquiv]
      · intro t _ hne
        have : ¬ (finSplitEquiv m t.1, t.2) = ((x0, x'), u) := fun heq => by
          apply hne
          rcases t with ⟨tx, tu⟩
          simp only [Prod.mk.injEq] at heq
          obtain ⟨h1, rfl⟩ := heq
          have htx := (Equiv.eq_symm_apply (finSplitEquiv m)).mpr h1
          exact Prod.ext htx rfl
        simp [this]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have hQ_YU_pmf : ∀ y0 (y' : Fin m → Bool) u,
        Q_YU.pmf ((y0, y'), u) =
          ∑ x0 : Bool, ∑ x' : Fin m → Bool,
            Q_XU.pmf ((x0, x'), u) * W.trans x0 y0 * Wn.trans x' y' := by
      classical
      intro y0 y' u
      have h1 : Q_YU.pmf ((y0, y'), u) = P_YU.pmf (Fin.cons y0 y', u) := by
        unfold Q_YU ProbDist.map; dsimp only
        rw [Finset.sum_eq_single (Fin.cons y0 y', u)]
        · simp [finSplitEquiv]
        · intro t _ hne
          have : ¬ (finSplitEquiv m t.1, t.2) = ((y0, y'), u) := fun heq => by
            apply hne
            rcases t with ⟨ty, tu⟩
            simp only [Prod.mk.injEq] at heq
            obtain ⟨h1, rfl⟩ := heq
            have hty := (Equiv.eq_symm_apply (finSplitEquiv m)).mpr h1
            exact Prod.ext hty rfl
          simp [this]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      rw [h1]
      unfold P_YU passFirstThrough DMC.power
      dsimp only
      have hprod_sum : (∑ x0 : Bool, ∑ x' : Fin m → Bool,
            Q_XU.pmf ((x0, x'), u) * W.trans x0 y0 * Wn.trans x' y') =
          ∑ p : Bool × (Fin m → Bool), Q_XU.pmf (p, u) * W.trans p.1 y0 * Wn.trans p.2 y' :=
        (Fintype.sum_prod_type
          (fun p : Bool × (Fin m → Bool) => Q_XU.pmf (p, u) * W.trans p.1 y0 * Wn.trans p.2 y')).symm
      rw [hprod_sum]
      refine Fintype.sum_equiv (finSplitEquiv m) _ _ fun x => ?_
      have hcons : Fin.cons (finSplitEquiv m x).1 (finSplitEquiv m x).2 = x :=
        (finSplitEquiv m).left_inv x
      dsimp only [Wn, DMC.power]
      rw [hQ_XU_pmf, hcons, Fin.prod_univ_succ]
      simp [finSplitEquiv, mul_assoc]
    -- 1. Identify the `(Y', U)` marginal of `Q_YU` as `passFirstThrough Wn` applied to `(X', U)`.
    let P_X'U : ProbDist ((Fin m → Bool) × U) := Q_XU.map (fun t => (t.1.2, t.2))
    have hP_X'U_pmf : ∀ x' u, P_X'U.pmf (x', u) = ∑ x0 : Bool, Q_XU.pmf ((x0, x'), u) := by
      classical
      intro x' u
      unfold P_X'U ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x0 _ => ?_
      rw [Finset.sum_eq_single x']
      · rw [Finset.sum_eq_single u]
        · simp
        · intro u' _ hne; simp [hne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · intro x'' _ hne; exact Finset.sum_eq_zero fun u' _ => by simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have hY'U_eq : Q_YU.map (fun t => (t.1.2, t.2)) = passFirstThrough Wn P_X'U := by
      classical
      unfold ProbDist.map passFirstThrough
      congr
      funext ⟨y', u⟩
      dsimp only
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      trans (∑ y0 : Bool, Q_YU.pmf ((y0, y'), u))
      · refine Finset.sum_congr rfl fun y0 _ => ?_
        rw [Finset.sum_eq_single y']
        · rw [Finset.sum_eq_single u]
          · simp
          · intro u' _ hne; simp [hne]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        · intro y'' _ hne; exact Finset.sum_eq_zero fun u' _ => by simp [hne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · simp_rw [hQ_YU_pmf]
        rw [Finset.sum_comm]
        trans (∑ x' : Fin m → Bool, (∑ x0 : Bool, Q_XU.pmf ((x0, x'), u)) * Wn.trans x' y')
        · trans (∑ x0 : Bool, ∑ x' : Fin m → Bool, Q_XU.pmf ((x0, x'), u) * Wn.trans x' y')
          · refine Finset.sum_congr rfl fun x0 _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ => ?_
            calc ∑ y0 : Bool, Q_XU.pmf ((x0, x'), u) * W.trans x0 y0 * Wn.trans x' y'
              _ = Q_XU.pmf ((x0, x'), u) * (∑ y0 : Bool, W.trans x0 y0) * Wn.trans x' y' := by
                  rw [Finset.mul_sum, Finset.sum_mul]
              _ = Q_XU.pmf ((x0, x'), u) * Wn.trans x' y' := by rw [W.sum_one, mul_one]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ => by rw [Finset.sum_mul]
        · refine Finset.sum_congr rfl fun x' _ => by rw [← hP_X'U_pmf]
    -- Apply induction hypothesis to `P_X'U` (length `m = n + 1`).
    have hIH : (m : ℝ) * mglFun p (condEntropy P_X'U / (m : ℝ)) ≤
        condEntropy (Q_YU.map (fun t => (t.1.2, t.2))) := by
      rw [hY'U_eq]
      exact mrs_gerber_vector_cond m hm_pos P_X'U hp0 hp1
    -- 2. Identify `(Y₀, (Y', U))` as `passFirstThrough W` applied to `P_X0_Y'U`.
    let P_X0_Y'U : ProbDist (Bool × ((Fin m → Bool) × U)) :=
      { pmf := fun z => ∑ x' : Fin m → Bool, Q_XU.pmf ((z.1, x'), z.2.2) * Wn.trans x' z.2.1
        nonneg := fun z => Finset.sum_nonneg fun x' _ => mul_nonneg (Q_XU.nonneg _) (Wn.nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_prod_type_right]
          trans (∑ x0 : Bool, ∑ u : U, ∑ x' : Fin m → Bool, Q_XU.pmf ((x0, x'), u))
          · refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x' _ => ?_
            rw [← Finset.mul_sum, Wn.sum_one, mul_one]
          · trans (∑ p : Bool × (Fin m → Bool), ∑ u : U, Q_XU.pmf (p, u))
            · rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            · rw [← Fintype.sum_prod_type]; exact Q_XU.sum_one }
    have hY0_eq : Q_YU.map (fun t => (t.1.1, (t.1.2, t.2))) = passFirstThrough W P_X0_Y'U := by
      classical
      unfold ProbDist.map passFirstThrough P_X0_Y'U
      congr
      funext ⟨y0, y', u⟩
      dsimp only
      rw [Finset.sum_eq_single ((y0, y'), u)]
      · simp only [↓reduceIte, hQ_YU_pmf]
        refine Finset.sum_congr rfl fun x0 _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x' _ => by ring
      · intro t _ hne
        have : ¬ (t.1.1, (t.1.2, t.2)) = (y0, (y', u)) := fun heq => by
          apply hne
          rcases t with ⟨⟨ty0, ty'⟩, tu⟩
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          rfl
        simp [this]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    -- Scalar MGL on `(X₀, (Y', U))` + DPI `H(X₀ | X', U) ≤ H(X₀ | Y', U)`.
    have hscalar : mglFun p (condEntropy P_X0_Y'U) ≤
        condEntropy (Q_YU.map (fun t => (t.1.1, (t.1.2, t.2)))) := by
      rw [hY0_eq]
      exact mrs_gerber_scalar P_X0_Y'U hp0 hp1
    have hdpi : condEntropy (Q_XU.map (fun t => (t.1.1, (t.1.2, t.2)))) ≤ condEntropy P_X0_Y'U :=
      condEntropy_dpi_channel Q_XU Wn
    have hmono_step : mglFun p (condEntropy (Q_XU.map (fun t => (t.1.1, (t.1.2, t.2))))) ≤
        mglFun p (condEntropy P_X0_Y'U) :=
      mglFun_mono hp0 hp1
        ⟨condEntropy_nonneg _, condEntropy_bool_le_one _⟩
        ⟨condEntropy_nonneg _, condEntropy_bool_le_one _⟩
        hdpi
    -- 3. Combine the two bounds by convexity of `mglFun p`.
    set a := condEntropy P_X'U / (m : ℝ)
    set b := condEntropy (Q_XU.map (fun t => (t.1.1, (t.1.2, t.2))))
    have ha_mem : a ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (condEntropy_nonneg _) hm_real.le,
       (div_le_one hm_real).mpr (condEntropy_fin_bool_le P_X'U)⟩
    have hb_mem : b ∈ Icc (0 : ℝ) 1 :=
      ⟨condEntropy_nonneg _, condEntropy_bool_le_one _⟩
    have hw1 : 0 ≤ (m : ℝ) / ((m : ℝ) + 1) := by positivity
    have hw2 : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    have hwsum : (m : ℝ) / ((m : ℝ) + 1) + (1 : ℝ) / ((m : ℝ) + 1) = 1 := by
      field_simp [hm1_real.ne']
    have hconv := (convexOn_mglFun hp0 hp1).2 ha_mem hb_mem hw1 hw2 hwsum
    simp only [smul_eq_mul] at hconv
    have havg : (m : ℝ) / ((m : ℝ) + 1) * a + (1 : ℝ) / ((m : ℝ) + 1) * b =
        condEntropy P_XU / ((m + 1 : ℕ) : ℝ) := by
      rw [← hH_X_eq, hchain_X]
      dsimp only [a, b, P_X'U]
      push_cast
      field_simp [hm_real.ne', hm1_real.ne']
      ring
    rw [havg] at hconv
    have hmul_conv := mul_le_mul_of_nonneg_left hconv hm1_real.le
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have hrhs_eq : ((m : ℝ) + 1) * ((m : ℝ) / ((m : ℝ) + 1) * mglFun p a +
        (1 : ℝ) / ((m : ℝ) + 1) * mglFun p b) =
        (m : ℝ) * mglFun p a + mglFun p b := by
      field_simp [hm1_real.ne']
    rw [hrhs_eq] at hmul_conv
    change ((m + 1 : ℕ) : ℝ) * mglFun p (condEntropy P_XU / ((m + 1 : ℕ) : ℝ)) ≤ condEntropy P_YU
    rw [← hH_Y_eq, hchain_Y]
    rw [hcast] at hmul_conv ⊢
    linarith

/-- **Vector (`n`-Letter) Mrs. Gerber's Lemma** (Wyner & Ziv 1973, Theorem 1):
    for every `n ≥ 1`, input distribution `P_X` on `Fin n → Bool`, and `p ∈ [0, 1/2]`,
    letting `P_Y` be the output distribution of `X^n` passed through `BSC(p)^n`,
    `n · h(h⁻¹(H(X^n) / n) ★ p) ≤ H(Y^n)`. -/
theorem mrs_gerber_vector {n : ℕ} (hn : 0 < n) (P_X : ProbDist (Fin n → Bool))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :
    (n : ℝ) * binaryEntropy (binaryConv (invBinaryEntropy (shannonEntropy P_X / (n : ℝ))) p) ≤
      shannonEntropy (((bsc p hp0 (by linarith)).power n).joint P_X).snd := by
  let U : ProbDist Unit := ProbDist.uniform
  let P_XU : ProbDist ((Fin n → Bool) × Unit) := P_X.prod U
  have hU_ent : shannonEntropy U = 0 := by
    have h := InfoTheory.Known.shannonEntropy_uniform (α := Unit)
    simpa [U, log2] using h
  have hcond_X : condEntropy P_XU = shannonEntropy P_X := by
    unfold condEntropy
    have hsnd : P_XU.snd = U := by
      apply probDist_ext; intro u
      simp [P_XU, ProbDist.snd, ProbDist.prod, ← Finset.sum_mul, P_X.sum_one]
    rw [hsnd, shannonEntropy_prod, hU_ent, add_zero, sub_zero]
  let W := (bsc p hp0 (by linarith)).power n
  have hYU_eq : passFirstThrough W P_XU = (W.joint P_X).snd.prod U := by
    apply probDist_ext; rintro ⟨y, u⟩
    simp [passFirstThrough, P_XU, ProbDist.prod, ProbDist.snd, DMC.joint, Finset.sum_mul, mul_right_comm]
  have hcond_Y : condEntropy (passFirstThrough W P_XU) = shannonEntropy (W.joint P_X).snd := by
    rw [hYU_eq]
    unfold condEntropy
    have hsnd : ((W.joint P_X).snd.prod U).snd = U := by
      apply probDist_ext; intro u
      change (∑ y : Fin n → Bool, (W.joint P_X).snd.pmf y * U.pmf u) = U.pmf u
      rw [← Finset.sum_mul, (W.joint P_X).snd.sum_one, one_mul]
    rw [hsnd, shannonEntropy_prod, hU_ent, add_zero, sub_zero]
  have hvec := mrs_gerber_vector_cond n hn P_XU hp0 hp1
  rwa [hcond_X, hcond_Y] at hvec

end VectorMGL

/-! ### 5. Flagship Application: Binary Symmetric Degraded Broadcast Channel (Bergmans 1973) -/

section DegradedBroadcastChannel

private noncomputable def degradedNoise (p₁ p₂ : ℝ) : ℝ :=
  if p₁ = 1 / 2 then 0 else (p₂ - p₁) / (1 - 2 * p₁)

private lemma degradedNoise_mem_Icc {p₁ p₂ : ℝ} (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    0 ≤ degradedNoise p₁ p₂ ∧ degradedNoise p₁ p₂ ≤ 1 / 2 := by
  unfold degradedNoise
  split_ifs with h
  · norm_num
  · have hlt : p₁ < 1 / 2 := lt_of_le_of_ne (le_trans h12 hp₂) h
    have hden : 0 < 1 - 2 * p₁ := by linarith
    constructor
    · exact div_nonneg (by linarith) hden.le
    · rw [div_le_iff₀ hden]
      linarith

private lemma binaryConv_degradedNoise {p₁ p₂ : ℝ} (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    binaryConv p₁ (degradedNoise p₁ p₂) = p₂ := by
  unfold degradedNoise
  split_ifs with h
  · have hp2_eq : p₂ = 1 / 2 := le_antisymm hp₂ (by linarith)
    rw [h, hp2_eq, binaryConv_zero_right]
  · have hden : 1 - 2 * p₁ ≠ 0 := by intro hd; apply h; linarith
    have hlin : binaryConv p₁ ((p₂ - p₁) / (1 - 2 * p₁)) =
        p₁ + (1 - 2 * p₁) * ((p₂ - p₁) / (1 - 2 * p₁)) := by unfold binaryConv; ring
    rw [hlin, mul_div_cancel₀ _ hden]; ring

/-- **Binary Symmetric Degraded Broadcast Channel** `BSC(p₁, p₂)` for `0 ≤ p₁ ≤ p₂ ≤ 1/2`,
    realized as the physically degraded Markov cascade `X —BSC(p₁)→ Y₁ —BSC(q)→ Y₂`
    where `p₁ ★ q = p₂`. -/
noncomputable def degradedBSC (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    BroadcastChannel Bool Bool Bool :=
  let q := degradedNoise p₁ p₂
  have hq := degradedNoise_mem_Icc h12 hp₂
  let W₁ := bsc p₁ hp₁ (by linarith)
  let Wq := bsc q hq.1 (by linarith [hq.2])
  { trans := fun x y => W₁.trans x y.1 * Wq.trans y.1 y.2
    nonneg := fun x y => mul_nonneg (W₁.nonneg x y.1) (Wq.nonneg y.1 y.2)
    sum_one := fun x => by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, Wq.sum_one, mul_one, W₁.sum_one] }

private lemma bsc_cascade_sum {p₁ q : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x y₂ : Bool) :
    ∑ y₁ : Bool, (bsc p₁ hp₁0 hp₁1).trans x y₁ * (bsc q hq0 hq1).trans y₁ y₂ =
      (bsc (binaryConv p₁ q) (binaryConv_mem_Icc_unit hp₁0 hp₁1 hq0 hq1).1
        (binaryConv_mem_Icc_unit hp₁0 hp₁1 hq0 hq1).2).trans x y₂ := by
  cases x <;> cases y₂ <;> simp [bsc, binaryConv] <;> ring

private lemma degradedBSC_pass_Y1 {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    J.map (fun z => (z.2.1, z.1.2)) = passFirstThrough (bsc p₁ hp₁ (by linarith)) P_XU := by
  classical
  intro J
  unfold J ProbDist.map passFirstThrough degradedBSC
  congr
  funext ⟨y₁, u⟩
  dsimp only
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single u]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
    · simp only [↓reduceIte]
      rw [← Finset.mul_sum, ← Finset.mul_sum, (bsc _ _ _).sum_one, mul_one]
    · intro y₁' _ hne; exact Finset.sum_eq_zero fun y₂ _ => by simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro u' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

private lemma degradedBSC_pass_Y2_from_Y1 {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    J.map (fun z => (z.2.2, z.1.2)) =
      passFirstThrough (bsc (degradedNoise p₁ p₂) (degradedNoise_mem_Icc h12 hp₂).1
        (by linarith [(degradedNoise_mem_Icc h12 hp₂).2]))
        (passFirstThrough (bsc p₁ hp₁ (by linarith)) P_XU) := by
  classical
  intro J
  unfold J ProbDist.map passFirstThrough degradedBSC
  congr
  funext ⟨y₂, u⟩
  dsimp only
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  trans (∑ x : Bool, ∑ y₁ : Bool,
      P_XU.pmf (x, u) * ((bsc p₁ hp₁ (by linarith)).trans x y₁ *
        (bsc (degradedNoise p₁ p₂) (degradedNoise_mem_Icc h12 hp₂).1
          (by linarith [(degradedNoise_mem_Icc h12 hp₂).2])).trans y₁ y₂))
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single u]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y₁ _ => ?_
      rw [Finset.sum_eq_single y₂]
      · simp
      · intro y₂' _ hne; simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · intro u' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => by ring

private lemma degradedBSC_pass_Y2 {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    J.map (fun z => (z.2.2, z.1.2)) = passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU := by
  intro J
  rw [degradedBSC_pass_Y2_from_Y1 P_XU hp₁ h12 hp₂]
  unfold passFirstThrough
  congr
  funext ⟨y₂, u⟩
  dsimp only
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hq := degradedNoise_mem_Icc h12 hp₂
  have hc := bsc_cascade_sum hp₁ (by linarith) hq.1 (by linarith [hq.2]) x y₂
  have hconv : binaryConv p₁ (degradedNoise p₁ p₂) = p₂ := binaryConv_degradedNoise h12 hp₂
  rw [hc]
  simp [bsc, hconv]

private lemma degradedBSC_condMutualInfo_X_Y1_given_U {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    condMutualInfo (J.map (fun z => (z.1.1, z.2.1, z.1.2))) =
      condEntropy (passFirstThrough (bsc p₁ hp₁ (by linarith)) P_XU) - binaryEntropy p₁ := by
  classical
  intro J
  set W₁ := bsc p₁ hp₁ (by linarith)
  set P_XY1U : ProbDist (Bool × Bool × U) := J.map (fun z => (z.1.1, z.2.1, z.1.2))
  have hP_XY1U_pmf : ∀ x y₁ u, P_XY1U.pmf (x, y₁, u) = P_XU.pmf (x, u) * W₁.trans x y₁ := by
    intro x y₁ u
    unfold P_XY1U J ProbDist.map degradedBSC; dsimp only
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single u]
      · rw [Fintype.sum_prod_type, Finset.sum_eq_single y₁]
        · simp only [↓reduceIte]
          rw [← Finset.mul_sum, ← Finset.mul_sum, (bsc _ _ _).sum_one, mul_one]
        · intro y₁' _ hne; exact Finset.sum_eq_zero fun y₂ _ => by simp [hne]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · intro u' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · intro x' _ hne; exact Finset.sum_eq_zero fun u' _ => Finset.sum_eq_zero fun y _ => by simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hXZ : P_XY1U.map (fun t => (t.1, t.2.2)) = P_XU := by
    rw [map_comp_eq]
    unfold J ProbDist.map
    congr
    funext ⟨x, u⟩
    dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (x, u)]
    · simp [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one]
    · intro xu' _ hne; exact Finset.sum_eq_zero fun y _ => by simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hYZ : P_XY1U.map (fun t => (t.2.1, t.2.2)) = passFirstThrough W₁ P_XU := by
    rw [map_comp_eq]
    exact degradedBSC_pass_Y1 P_XU hp₁ h12 hp₂
  have hZ : P_XY1U.map (fun t => t.2.2) = (passFirstThrough W₁ P_XU).snd := by
    rw [passFirstThrough_snd, ← hXZ]
    unfold ProbDist.snd ProbDist.map
    congr
    funext u
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t.2.2 = u
    · rw [Finset.sum_eq_single t.1]
      · simp [ht]
      · intro x _ hne; simp [hne.symm]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · simp only [ht, ↓reduceIte]
      exact (Finset.sum_eq_zero fun x _ => by simp [ht]).symm
  -- Compute `H(X, Y₁, U) = H(X, U) + h(p₁)` directly.
  have hH_XY1U : shannonEntropy P_XY1U = shannonEntropy P_XU + binaryEntropy p₁ := by
    unfold shannonEntropy
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, hP_XY1U_pmf]
    trans (∑ x : Bool, ∑ u : U, (P_XU.pmf (x, u) * binaryEntropy p₁ + negPLogP (P_XU.pmf (x, u))))
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hterm : ∑ y₁ : Bool, negPLogP (P_XU.pmf (x, u) * W₁.trans x y₁) =
          P_XU.pmf (x, u) * (∑ y₁ : Bool, negPLogP (W₁.trans x y₁)) +
          (∑ y₁ : Bool, W₁.trans x y₁) * negPLogP (P_XU.pmf (x, u)) := by
        simp_rw [negPLogP_mul_nonneg (P_XU.nonneg _) (W₁.nonneg _ _),
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      have hbin : ∑ y₁ : Bool, negPLogP (W₁.trans x y₁) = binaryEntropy p₁ := by
        cases x <;> simp [W₁, bsc, binaryEntropy, add_comm]
      rw [hterm, hbin, W₁.sum_one, one_mul]
    · simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [← Fintype.sum_prod_type, P_XU.sum_one, one_mul, add_comm]
  unfold condMutualInfo condEntropy
  dsimp only
  rw [hXZ, hYZ, hZ, hH_XY1U]
  ring

private lemma degradedBSC_mutualInfo_U_Y2_eq {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    mutualInfo (J.map (fun z => (z.1.2, z.2.2))) =
      shannonEntropy (passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU).fst -
        condEntropy (passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU) := by
  intro J
  have hswap : J.map (fun z => (z.1.2, z.2.2)) =
      (J.map (fun z => (z.2.2, z.1.2))).map Prod.swap := by
    rw [map_comp_eq]; rfl
  rw [hswap, mutualInfo_swap, degradedBSC_pass_Y2 P_XU hp₁ h12 hp₂]
  unfold mutualInfo condEntropy
  ring

/-- **Direct Mrs. Gerber Bound on the Degraded Receiver**:
    for any auxiliary `U — X — Y₁ — Y₂` over `degradedBSC p₁ p₂` (`0 ≤ p₁ ≤ p₂ ≤ 1/2`),
    `I(U; Y₂) ≤ 1 - h(h⁻¹(H(X | U)) ★ p₂)`. -/
theorem degradedBSC_mutualInfo_U_Y2_le {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    mutualInfo (J.map (fun z => (z.1.2, z.2.2))) ≤
      1 - binaryEntropy (binaryConv (invBinaryEntropy (condEntropy P_XU)) p₂) := by
  intro J
  rw [degradedBSC_mutualInfo_U_Y2_eq P_XU hp₁ h12 hp₂]
  have hY2_le : shannonEntropy (passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU).fst ≤ 1 := by
    have h := shannonEntropy_le_log2_card
      (passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU).fst
    simpa [Fintype.card_bool, log2_two_val] using h
  have hmgl := mrs_gerber_scalar P_XU (by linarith : 0 ≤ p₂) hp₂
  linarith

/-- **Bergmans–Wyner–Ziv Outer Bound for the Binary Symmetric Degraded Broadcast Channel**
    (Bergmans 1973; Wyner & Ziv 1973; Cover & Thomas §15.6.2; El Gamal–Kim §5.3):
    for any `0 ≤ p₁ ≤ p₂ ≤ 1/2`, finite auxiliary `U`, and input distribution `P_XU` forming
    `U — X — Y₁ — Y₂` across `degradedBSC p₁ p₂`, there exists `α ∈ [0, 1/2]` such that
    `I(U; Y₂) ≤ 1 - h(α ★ p₂)` and `I(X; Y₁ | U) ≤ h(α ★ p₁) - h(p₁)`
    (with equality in the second bound). -/
theorem degradedBSC_bergmans_outer_bound {U : Type*} [Fintype U]
    (P_XU : ProbDist (Bool × U)) {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) :
    let J : ProbDist ((Bool × U) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    ∃ α ∈ Icc (0 : ℝ) (1 / 2),
      mutualInfo (J.map (fun z => (z.1.2, z.2.2))) ≤ 1 - binaryEntropy (binaryConv α p₂) ∧
      condMutualInfo (J.map (fun z => (z.1.1, z.2.1, z.1.2))) ≤
        binaryEntropy (binaryConv α p₁) - binaryEntropy p₁ := by
  intro J
  set P_Y1U := passFirstThrough (bsc p₁ hp₁ (by linarith)) P_XU
  set P_Y2U := passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU
  have hI1_eq := degradedBSC_condMutualInfo_X_Y1_given_U P_XU hp₁ h12 hp₂
  have hI2_eq := degradedBSC_mutualInfo_U_Y2_eq P_XU hp₁ h12 hp₂
  have hH1_ge : binaryEntropy p₁ ≤ condEntropy P_Y1U := by
    have hnn := condMutualInfo_nonneg (J.map (fun z => (z.1.1, z.2.1, z.1.2)))
    linarith
  have hH1_le : condEntropy P_Y1U ≤ 1 := condEntropy_bool_le_one P_Y1U
  have hY2_le : shannonEntropy P_Y2U.fst ≤ 1 := by
    have h := shannonEntropy_le_log2_card P_Y2U.fst
    simpa [Fintype.card_bool, log2_two_val] using h
  -- Handle `p₁ = 1/2` separately (`p₂ = 1/2`, both bounds vanish with `α = 0`).
  by_cases hp1_half : p₁ = 1 / 2
  · have hp2_half : p₂ = 1 / 2 := le_antisymm hp₂ (by linarith)
    refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
    · rw [hp2_half, binaryConv_half_right, InfoTheory.Known.binaryEntropy_half,
          sub_self, hI2_eq]
      have hmgl := mrs_gerber_scalar P_XU (by linarith : 0 ≤ p₂) hp₂
      have hbin2 : binaryEntropy (binaryConv (invBinaryEntropy (condEntropy P_XU)) p₂) = 1 := by
        rw [hp2_half, binaryConv_half_right, InfoTheory.Known.binaryEntropy_half]
      rw [hbin2] at hmgl
      have hP_Y2U_ge : 1 ≤ condEntropy P_Y2U := hmgl
      linarith
    · have hbin1 : binaryEntropy p₁ = 1 := by
        rw [hp1_half, InfoTheory.Known.binaryEntropy_half]
      rw [hp1_half, binaryConv_half_right, InfoTheory.Known.binaryEntropy_half, sub_self, hI1_eq]
      linarith [hH1_le, hbin1]
  · -- Main case `p₁ < 1/2`: set `β := h⁻¹(H(Y₁ | U)) ∈ [p₁, 1/2]` and `α := (β - p₁) / (1 - 2 p₁)`.
    have hp1_lt : p₁ < 1 / 2 := lt_of_le_of_ne (le_trans h12 hp₂) hp1_half
    have hden : 0 < 1 - 2 * p₁ := by linarith
    set β := invBinaryEntropy (condEntropy P_Y1U)
    have hβ_mem : β ∈ Icc (0 : ℝ) (1 / 2) :=
      invBinaryEntropy_mem_Icc (condEntropy_nonneg P_Y1U) hH1_le
    have hβ_ge : p₁ ≤ β := by
      have hp1_ent_mem : binaryEntropy p₁ ∈ Icc (0 : ℝ) 1 :=
        ⟨InfoTheory.Known.binaryEntropy_nonneg hp₁ (by linarith),
         InfoTheory.Known.binaryEntropy_le_one hp₁ (by linarith)⟩
      have hmono := invBinaryEntropy_mono hp1_ent_mem
        ⟨condEntropy_nonneg P_Y1U, hH1_le⟩ hH1_ge
      rwa [invBinaryEntropy_binaryEntropy hp₁ hp1_lt.le] at hmono
    set α := (β - p₁) / (1 - 2 * p₁)
    have hα0 : 0 ≤ α := div_nonneg (by linarith) hden.le
    have hα1 : α ≤ 1 / 2 := by
      dsimp only [α]
      rw [div_le_iff₀ hden]
      linarith [hβ_mem.2]
    have hα_conv : binaryConv α p₁ = β := by
      dsimp only [α]
      have hlin : binaryConv ((β - p₁) / (1 - 2 * p₁)) p₁ =
          p₁ + (1 - 2 * p₁) * ((β - p₁) / (1 - 2 * p₁)) := by unfold binaryConv; ring
      rw [hlin, mul_div_cancel₀ _ hden.ne']; ring
    -- Apply scalar Mrs. Gerber's Lemma to the degraded channel `U — Y₁ — Y₂` with noise `q`.
    set q := degradedNoise p₁ p₂
    have hq := degradedNoise_mem_Icc h12 hp₂
    have hmgl_q := mrs_gerber_scalar P_Y1U hq.1 hq.2
    have hY2_cascade : passFirstThrough (bsc q hq.1 (by linarith [hq.2])) P_Y1U = P_Y2U := by
      rw [← degradedBSC_pass_Y2_from_Y1 P_XU hp₁ h12 hp₂,
          degradedBSC_pass_Y2 P_XU hp₁ h12 hp₂]
    rw [hY2_cascade] at hmgl_q
    have hconv_q : binaryConv β q = binaryConv α p₂ := by
      rw [← hα_conv, binaryConv_assoc, binaryConv_degradedNoise h12 hp₂]
    rw [hconv_q] at hmgl_q
    refine ⟨α, ⟨hα0, hα1⟩, ?_, ?_⟩
    · rw [hI2_eq]; linarith
    · rw [hI1_eq, hα_conv, binaryEntropy_invBinaryEntropy (condEntropy_nonneg P_Y1U) hH1_le]

/-- **Tightness / Single-Letter Achievability of the Bergmans–Wyner–Ziv Boundary**:
    for every `0 ≤ p₁ ≤ p₂ ≤ 1/2` and every `α ∈ [0, 1/2]`, choosing `U ~ Bern(1/2)` and
    `X = BSC(α)(U)` achieves both bounds with exact equality:
    `I(U; Y₂) = 1 - h(α ★ p₂)` and `I(X; Y₁ | U) = h(α ★ p₁) - h(p₁)`. -/
theorem degradedBSC_bergmans_achievable {p₁ p₂ α : ℝ}
    (hp₁ : 0 ≤ p₁) (h12 : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1 / 2) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    let P_XU : ProbDist (Bool × Bool) :=
      ((bsc α hα0 (by linarith)).joint (ProbDist.uniform : ProbDist Bool)).map Prod.swap
    let J : ProbDist ((Bool × Bool) × (Bool × Bool)) :=
      { pmf := fun z => P_XU.pmf z.1 * (degradedBSC p₁ p₂ hp₁ h12 hp₂).trans z.1.1 z.2
        nonneg := fun z => mul_nonneg (P_XU.nonneg z.1) ((degradedBSC p₁ p₂ hp₁ h12 hp₂).nonneg _ _)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (degradedBSC p₁ p₂ hp₁ h12 hp₂).sum_one, mul_one, P_XU.sum_one] }
    mutualInfo (J.map (fun z => (z.1.2, z.2.2))) = 1 - binaryEntropy (binaryConv α p₂) ∧
    condMutualInfo (J.map (fun z => (z.1.1, z.2.1, z.1.2))) =
      binaryEntropy (binaryConv α p₁) - binaryEntropy p₁ := by
  classical
  intro P_XU J
  have hP_XU_pmf : ∀ x u : Bool,
      P_XU.pmf (x, u) = (1 / 2 : ℝ) * (bsc α hα0 (by linarith)).trans u x := by
    intro x u
    unfold P_XU ProbDist.map DMC.joint ProbDist.uniform
    dsimp only
    rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
    · rw [Finset.sum_eq_single x]
      · simp
      · intro x' _ hne; simp [Prod.swap, hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · intro u' _ hne; exact Finset.sum_eq_zero fun x' _ => by simp [Prod.swap, hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hpass_cond : ∀ (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
      condEntropy (passFirstThrough (bsc r hr0 hr1) P_XU) = binaryEntropy (binaryConv α r) := by
    intro r hr0 hr1
    rw [condEntropy_bool_eq_sum]
    have hsnd : ∀ u : Bool, (passFirstThrough (bsc r hr0 hr1) P_XU).snd.pmf u = 1 / 2 := by
      intro u
      rw [passFirstThrough_snd]
      unfold ProbDist.snd
      dsimp only
      simp_rw [hP_XU_pmf]
      rw [← Finset.mul_sum, (bsc α hα0 (by linarith)).sum_one, mul_one]
    have htrue : ∀ u : Bool, (passFirstThrough (bsc r hr0 hr1) P_XU).pmf (true, u) =
        (1 / 2 : ℝ) * (if u then 1 - binaryConv α r else binaryConv α r) := by
      intro u
      unfold passFirstThrough
      dsimp only
      simp_rw [hP_XU_pmf, mul_assoc, ← Finset.mul_sum]
      congr 1
      cases u
      · simp [bsc, binaryConv]
      · simp [bsc, binaryConv]; ring
    simp_rw [hsnd, htrue]
    have hne : (1 / 2 : ℝ) ≠ 0 := by norm_num
    simp only [hne, ↓reduceIte]
    have hdiv : ∀ c : ℝ, (1 / 2 : ℝ) * c / (1 / 2 : ℝ) = c := fun c => by ring
    simp_rw [hdiv]
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [← InfoTheory.Known.binaryEntropy_symm (binaryConv α r)]
    ring
  have hY2_unif : (passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU).fst =
      (ProbDist.uniform : ProbDist Bool) := by
    unfold passFirstThrough ProbDist.fst ProbDist.uniform
    congr
    funext y
    dsimp only
    simp_rw [hP_XU_pmf]
    cases y <;> simp [bsc] <;> ring
  have hY2_ent : shannonEntropy
      (passFirstThrough (bsc p₂ (by linarith) (by linarith)) P_XU).fst = 1 := by
    rw [hY2_unif, InfoTheory.Known.shannonEntropy_uniform]
    simp [Fintype.card_bool, log2_two_val]
  constructor
  · rw [degradedBSC_mutualInfo_U_Y2_eq P_XU hp₁ h12 hp₂, hY2_ent,
        hpass_cond p₂ (by linarith) (by linarith)]
  · rw [degradedBSC_condMutualInfo_X_Y1_given_U P_XU hp₁ h12 hp₂,
        hpass_cond p₁ hp₁ (by linarith)]

end DegradedBroadcastChannel

end InfoTheory.Bridge
