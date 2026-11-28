import InfoTheory.Problems.QuantumBroadcastCapacity
import InfoTheory.Known.Certificates.QuantumCapacitySingleLetter
import InfoTheory.Known.Certificates.QuantumReverseShannonNonCatalytic
import InfoTheory.Bridge.CoverThomas

/-!
# Certificate for `InfoTheory.Problems.QuantumBroadcastCapacity`

The frozen statement asks whether, for every finite-alphabet two-receiver classical-quantum
broadcast channel `W : Fin kX → DensityMatrix (d₁ * d₂)`, the operational capacity region
`cqBroadcastCapacityRegion W` equals the single-letter quantum Marton region with common
auxiliary `cqMartonInnerBound W` (Savov–Wilde 2015). This file certifies that both sides are
non-degenerate objects of the expected shape, about the *exact* sets in the `Statement`.

## Certified
* **Toolkit:** `partialTraceA_eq_sum`, `partialTraceA_posSemidef`, `partialTraceA_trace`
  (`Tr_A` is a CPTP partial trace; the `Tr_B` analogues are imported from
  `QuantumReverseShannonNonCatalytic`), `marg1_state`/`marg2_state`,
  `trace_kronPowerMat_of_trace_one`, `kronPowerMat_posSemidef` (tensor products of states are
  states), `trace_mul_state_re_le` (`Re Tr(Λρ) ≤ Re Tr Λ` for `Λ ⪰ 0` and a state `ρ`).
* **Both sides contain the origin:** `zero_mem_cqBroadcastCapacityRegion`,
  `zero_mem_cqMartonInnerBound` (for `0 < kX`).
* **Both sides are bounded, inside `[0, log₂ d₁] × [0, log₂ d₂]`:**
  `cqMartonInnerBound_subset_box` (`I(WU;B₁) ≤ S(B₁) ≤ log₂ d₁`, using that every guarded
  conditional-entropy term is `≥ 0`), and the operational converse
  `cqBroadcastCapacityRegion_subset_box`, via `achievable_rate₁_le` / `achievable_rate₂_le`:
  a POVM on `ℂ^{dⁿ}` distinguishes `M` messages with average success `≤ dⁿ / M`
  (`avg_success_le`), so success `≥ 1/2` forces `R ≤ log₂ d` (`rate_le_log2`).
* **Regression (single-user Holevo corners):** `holevo1_corner_mem`, `holevo2_corner_mem`:
  for every input law `p`, `(r, 0)` with `0 ≤ r ≤ χ(p; B₁)` and `(0, r)` with
  `0 ≤ r ≤ χ(p; B₂)` lie in `cqMartonInnerBound W`, where
  `χ(p; Bⱼ) = S(∑ₓ p(x) ρₓ^{Bⱼ}) − ∑ₓ p(x) S(ρₓ^{Bⱼ})` (`holevo1`, `holevo2`). This is
  the expected HSW corner of the Marton region (`W, V` constant, `U = X`, resp. symmetric);
  the guarded conditional states and `I(U;V|W)` evaluate correctly
  (`condMutualInfo_le_zero_of_unique_mid`/`_fst`).

## Not certified
* That `χ(p; B₁)` is an *operational* rate (`(χ, 0) ∈ cqBroadcastCapacityRegion`): this is the
  HSW coding theorem, not available in the library. Likewise the Marton inner bound
  `cqMartonInnerBound ⊆ cqBroadcastCapacityRegion` (Savov–Wilde / Radhakrishnan–Sen–Warsi).
* Nonnegativity of `χ` (concavity of von Neumann entropy) is not needed and not proved.

Nothing here proves or disproves `Statement` (classical Marton tightness embeds as the
diagonal case and is open).
-/

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace InfoTheory.Known.Certificates.QuantumBroadcastCapacity

open InfoTheory InfoTheory.Problems.QuantumBroadcastCapacity Matrix
open InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold
  (matEntropy_nonneg_of_state)
open InfoTheory.Known.Certificates.QuantumCapacitySingleLetter
  (matEntropy_le_log2_of_state kronMat_eq_reindex kronPowerMat_succ)
open InfoTheory.Known.Certificates.QuantumReverseShannonNonCatalytic
  (partialTraceB_posSemidef partialTraceB_trace)

/-! ### `partialTraceA` is a genuine partial trace -/

/-- The isometry-component `V_a : ℂ^{dA·dB} → ℂ^{dB}`, `|a', b⟩ ↦ δ_{a a'} |b⟩`. -/
def sliceA {dA dB : ℕ} (a : Fin dA) : Matrix (Fin dB) (Fin (dA * dB)) ℂ :=
  Matrix.of fun b i => if i.1 = a.1 * dB + b.1 then 1 else 0

theorem partialTraceA_eq_sum {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    @partialTraceA dA dB M = ∑ a : Fin dA, sliceA a * M * (sliceA a)ᴴ := by
  ext b₁ b₂
  simp only [partialTraceA, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, sliceA]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hlt : ∀ b : Fin dB, a.1 * dB + b.1 < dA * dB := fun b => by
    calc a.1 * dB + b.1 < a.1 * dB + dB := Nat.add_lt_add_left b.2 _
      _ = (a.1 + 1) * dB := by ring
      _ ≤ dA * dB := Nat.mul_le_mul_right dB a.2
  have key : ∀ (b : Fin dB) (f : Fin (dA * dB) → ℂ),
      ∑ i : Fin (dA * dB), (if i.1 = a.1 * dB + b.1 then (1 : ℂ) else 0) * f i =
        f ⟨a.1 * dB + b.1, hlt b⟩ := by
    intro b f
    rw [Finset.sum_eq_single ⟨a.1 * dB + b.1, hlt b⟩]
    · simp
    · intro i _ hi
      split_ifs with h
      · exact absurd (Fin.ext h) hi
      · rw [zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have key2 : ∀ (b : Fin dB) (f : Fin (dA * dB) → ℂ),
      ∑ j : Fin (dA * dB), f j * star (if j.1 = a.1 * dB + b.1 then (1 : ℂ) else 0) =
        f ⟨a.1 * dB + b.1, hlt b⟩ := by
    intro b f
    rw [Finset.sum_eq_single ⟨a.1 * dB + b.1, hlt b⟩]
    · simp
    · intro j _ hj
      split_ifs with h
      · exact absurd (Fin.ext h) hj
      · rw [star_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key2]
  exact (key b₁ (fun i => M i ⟨a.1 * dB + b₂.1, hlt b₂⟩)).symm

theorem partialTraceA_posSemidef {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.PosSemidef) : (@partialTraceA dA dB M).PosSemidef := by
  rw [partialTraceA_eq_sum]
  exact posSemidef_sum _ fun a _ => hM.mul_mul_conjTranspose_same (sliceA a)

theorem partialTraceA_trace {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    (@partialTraceA dA dB M).trace = M.trace := by
  unfold Matrix.trace
  simp only [partialTraceA, Matrix.of_apply, Matrix.diag]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv finProdFinEquiv _ _ fun x => ?_
  have he : finProdFinEquiv x = ⟨x.1.1 * dB + x.2.1, by
      calc x.1.1 * dB + x.2.1 < x.1.1 * dB + dB := Nat.add_lt_add_left x.2.2 _
        _ = (x.1.1 + 1) * dB := by ring
        _ ≤ dA * dB := Nat.mul_le_mul_right dB x.1.2⟩ :=
    Fin.ext (by rw [finProdFinEquiv_apply_val]; ring)
  rw [he]

/-- Both marginals of a c-q broadcast output are states. -/
theorem marg1_state {d₁ d₂ : ℕ} (ρ : DensityMatrix (d₁ * d₂)) :
    (@partialTraceB d₁ d₂ ρ.mat).PosSemidef ∧ (@partialTraceB d₁ d₂ ρ.mat).trace = 1 :=
  ⟨partialTraceB_posSemidef ρ.posSemidef, (partialTraceB_trace _).trans ρ.trace_one⟩

theorem marg2_state {d₁ d₂ : ℕ} (ρ : DensityMatrix (d₁ * d₂)) :
    (@partialTraceA d₁ d₂ ρ.mat).PosSemidef ∧ (@partialTraceA d₁ d₂ ρ.mat).trace = 1 :=
  ⟨partialTraceA_posSemidef ρ.posSemidef, (partialTraceA_trace _).trans ρ.trace_one⟩

/-! ### Mixtures of states -/

theorem wsum_posSemidef {ι : Type*} [Fintype ι] {d : ℕ} (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ) (hρ : ∀ i, (ρ i).PosSemidef) :
    (∑ i, (q i : ℂ) • ρ i).PosSemidef :=
  posSemidef_sum _ fun i _ => (hρ i).smul (Complex.zero_le_real.mpr (hq i))

theorem wsum_trace {ι : Type*} [Fintype ι] {d : ℕ} (q : ι → ℝ)
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ) (hρ : ∀ i, (ρ i).trace = 1) :
    (∑ i, (q i : ℂ) • ρ i).trace = ((∑ i, q i : ℝ) : ℂ) := by
  rw [Matrix.trace_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, hρ i, smul_eq_mul, mul_one]

/-- Normalizing a PSD matrix of positive trace `s` gives a state. -/
theorem normalize_state {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) {s : ℝ}
    (hs : 0 < s) (htr : A.trace = s) :
    (((1 / s : ℝ) : ℂ) • A).PosSemidef ∧ (((1 / s : ℝ) : ℂ) • A).trace = 1 := by
  refine ⟨hA.smul (Complex.zero_le_real.mpr (by positivity)), ?_⟩
  rw [Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, one_div,
    inv_mul_cancel₀ hs.ne', Complex.ofReal_one]

/-- A guarded conditional-entropy term `p · S(ρ/p)` is nonnegative. -/
theorem ite_entropy_nonneg {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) {s : ℝ}
    (htr : A.trace = s) :
    0 ≤ (if s ≤ 0 then 0 else s * matEntropy (((1 / s : ℝ) : ℂ) • A)) := by
  split_ifs with h
  · exact le_rfl
  · push Not at h
    obtain ⟨h1, h2⟩ := normalize_state hA h htr
    exact mul_nonneg h.le (matEntropy_nonneg_of_state h1 h2)

/-! ### The Marton inner bound is a bounded subset of the nonnegative quadrant -/

/-- Every rate pair of the single-letter quantum Marton region lies in
`[0, log₂ d₁] × [0, log₂ d₂]`. -/
theorem cqMartonInnerBound_subset_box {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂)) :
    cqMartonInnerBound W ⊆ Set.Icc 0 (log2 d₁) ×ˢ Set.Icc 0 (log2 d₂) := by
  refine closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
  rintro p ⟨h1, h2, kW, kU, kV, P, hP⟩
  dsimp only at hP
  obtain ⟨hA, hB, -, -⟩ := hP
  have hav1 := wsum_posSemidef (fun t => P.pmf t) P.nonneg
    (fun t : Fin kW × Fin kU × Fin kV × Fin kX => @partialTraceB d₁ d₂ (W t.2.2.2).mat)
    (fun t => (marg1_state _).1)
  have htr1 := wsum_trace (fun t => P.pmf t)
    (fun t : Fin kW × Fin kU × Fin kV × Fin kX => @partialTraceB d₁ d₂ (W t.2.2.2).mat)
    (fun t => (marg1_state _).2)
  rw [P.sum_one, Complex.ofReal_one] at htr1
  have hav2 := wsum_posSemidef (fun t => P.pmf t) P.nonneg
    (fun t : Fin kW × Fin kU × Fin kV × Fin kX => @partialTraceA d₁ d₂ (W t.2.2.2).mat)
    (fun t => (marg2_state _).1)
  have htr2 := wsum_trace (fun t => P.pmf t)
    (fun t : Fin kW × Fin kU × Fin kV × Fin kX => @partialTraceA d₁ d₂ (W t.2.2.2).mat)
    (fun t => (marg2_state _).2)
  rw [P.sum_one, Complex.ofReal_one] at htr2
  have hS1 := matEntropy_le_log2_of_state hav1 htr1
  have hS2 := matEntropy_le_log2_of_state hav2 htr2
  have hc1 : 0 ≤ ∑ w : Fin kW, ∑ u : Fin kU,
      if (∑ v : Fin kV, ∑ x : Fin kX, P.pmf (w, u, v, x)) ≤ 0 then 0 else
        (∑ v : Fin kV, ∑ x : Fin kX, P.pmf (w, u, v, x)) *
          matEntropy (((1 / ∑ v : Fin kV, ∑ x : Fin kX, P.pmf (w, u, v, x) : ℝ) : ℂ) •
            ∑ v : Fin kV, ∑ x : Fin kX,
              (P.pmf (w, u, v, x) : ℂ) • @partialTraceB d₁ d₂ (W x).mat) := by
    refine Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun u _ => ite_entropy_nonneg ?_ ?_
    · exact posSemidef_sum _ fun v _ => wsum_posSemidef _ (fun x => P.nonneg _) _
        (fun x => (marg1_state _).1)
    · rw [Matrix.trace_sum]; push_cast
      exact Finset.sum_congr rfl fun v _ => by
        rw [wsum_trace _ _ (fun x => (marg1_state _).2)]; push_cast; rfl
  have hc2 : 0 ≤ ∑ w : Fin kW, ∑ v : Fin kV,
      if (∑ u : Fin kU, ∑ x : Fin kX, P.pmf (w, u, v, x)) ≤ 0 then 0 else
        (∑ u : Fin kU, ∑ x : Fin kX, P.pmf (w, u, v, x)) *
          matEntropy (((1 / ∑ u : Fin kU, ∑ x : Fin kX, P.pmf (w, u, v, x) : ℝ) : ℂ) •
            ∑ u : Fin kU, ∑ x : Fin kX,
              (P.pmf (w, u, v, x) : ℂ) • @partialTraceA d₁ d₂ (W x).mat) := by
    refine Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun v _ => ite_entropy_nonneg ?_ ?_
    · exact posSemidef_sum _ fun u _ => wsum_posSemidef _ (fun x => P.nonneg _) _
        (fun x => (marg2_state _).1)
    · rw [Matrix.trace_sum]; push_cast
      exact Finset.sum_congr rfl fun u _ => by
        rw [wsum_trace _ _ (fun x => (marg2_state _).2)]; push_cast; rfl
  exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩

/-- The operational region lies in the closed nonnegative quadrant. -/
theorem cqBroadcastCapacityRegion_subset_nonneg {kX d₁ d₂ : ℕ}
    (W : Fin kX → DensityMatrix (d₁ * d₂)) :
    cqBroadcastCapacityRegion W ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := by
  refine closure_minimal ?_ (isClosed_Ici.prod isClosed_Ici)
  rintro p ⟨h1, h2, -⟩
  exact ⟨h1, h2⟩

/-! ### Degenerate conditional mutual information -/

theorem condMutualInfo_le_zero_of_unique_mid {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Unique β] (P : ProbDist (α × β × γ)) : condMutualInfo P ≤ 0 := by
  unfold condMutualInfo
  dsimp only
  have h1 : shannonEntropy (P.map fun t => (t.1, t.2.2)) ≤ shannonEntropy P :=
    Bridge.shannonEntropy_map_le _ _
  have h2 : shannonEntropy (P.map fun t => (t.2.1, t.2.2)) ≤
      shannonEntropy (P.map fun t => t.2.2) := by
    have : (P.map fun t => (t.2.1, t.2.2)) =
        (P.map fun t => t.2.2).map (fun z => ((default : β), z)) := by
      rw [Bridge.map_comp_eq]
      exact congrArg (fun f => P.map f) (funext fun t => by simp [Unique.eq_default t.2.1])
    rw [this]
    exact Bridge.shannonEntropy_map_le _ _
  linarith

theorem condMutualInfo_le_zero_of_unique_fst {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Unique α] (P : ProbDist (α × β × γ)) : condMutualInfo P ≤ 0 := by
  unfold condMutualInfo
  dsimp only
  have h1 : shannonEntropy (P.map fun t => (t.2.1, t.2.2)) ≤ shannonEntropy P :=
    Bridge.shannonEntropy_map_le _ _
  have h2 : shannonEntropy (P.map fun t => (t.1, t.2.2)) ≤
      shannonEntropy (P.map fun t => t.2.2) := by
    have : (P.map fun t => (t.1, t.2.2)) =
        (P.map fun t => t.2.2).map (fun z => ((default : α), z)) := by
      rw [Bridge.map_comp_eq]
      exact congrArg (fun f => P.map f) (funext fun t => by simp [Unique.eq_default t.1])
    rw [this]
    exact Bridge.shannonEntropy_map_le _ _
  linarith

/-! ### Regression: single-user Holevo corner points lie in the Marton region -/

/-- Holevo information `χ(p; B₁) = S(∑ₓ p(x) ρₓ^{B₁}) - ∑ₓ p(x) S(ρₓ^{B₁})` of the first
marginal ensemble. -/
noncomputable def holevo1 {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂))
    (p : ProbDist (Fin kX)) : ℝ :=
  matEntropy (∑ x, (p.pmf x : ℂ) • @partialTraceB d₁ d₂ (W x).mat) -
    ∑ x, p.pmf x * matEntropy (@partialTraceB d₁ d₂ (W x).mat)

/-- Holevo information `χ(p; B₂)` of the second marginal ensemble. -/
noncomputable def holevo2 {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂))
    (p : ProbDist (Fin kX)) : ℝ :=
  matEntropy (∑ x, (p.pmf x : ℂ) • @partialTraceA d₁ d₂ (W x).mat) -
    ∑ x, p.pmf x * matEntropy (@partialTraceA d₁ d₂ (W x).mat)

/-- Joint law of `(W, U, V, X)` with `W, V` constant and `U = X ~ p`. -/
noncomputable def cornerLaw1 {kX : ℕ} (p : ProbDist (Fin kX)) :
    ProbDist (Fin 1 × Fin kX × Fin 1 × Fin kX) where
  pmf t := if t.2.1 = t.2.2.2 then p.pmf t.2.2.2 else 0
  nonneg t := by split_ifs; exacts [p.nonneg _, le_rfl]
  sum_one := by simp [Fintype.sum_prod_type, p.sum_one]

theorem cornerLaw1_pmf {kX : ℕ} (p : ProbDist (Fin kX)) (t : Fin 1 × Fin kX × Fin 1 × Fin kX) :
    (cornerLaw1 p).pmf t = if t.2.1 = t.2.2.2 then p.pmf t.2.2.2 else 0 := rfl

/-- Joint law of `(W, U, V, X)` with `W, U` constant and `V = X ~ p`. -/
noncomputable def cornerLaw2 {kX : ℕ} (p : ProbDist (Fin kX)) :
    ProbDist (Fin 1 × Fin 1 × Fin kX × Fin kX) where
  pmf t := if t.2.2.1 = t.2.2.2 then p.pmf t.2.2.2 else 0
  nonneg t := by split_ifs; exacts [p.nonneg _, le_rfl]
  sum_one := by simp [Fintype.sum_prod_type, p.sum_one]

theorem cornerLaw2_pmf {kX : ℕ} (p : ProbDist (Fin kX)) (t : Fin 1 × Fin 1 × Fin kX × Fin kX) :
    (cornerLaw2 p).pmf t = if t.2.2.1 = t.2.2.2 then p.pmf t.2.2.2 else 0 := rfl

theorem inv_smul_smul_real {d : ℕ} {s : ℝ} (hs : s ≠ 0) (A : Matrix (Fin d) (Fin d) ℂ) :
    ((s : ℂ))⁻¹ • (s • A) = A := by
  rw [← Complex.coe_smul, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hs)]

theorem ite_term_eq {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (A : Matrix (Fin d) (Fin d) ℂ) :
    (if s ≤ 0 then 0 else s * matEntropy (((s : ℂ))⁻¹ • (s • A))) = s * matEntropy A := by
  split_ifs with h
  · rw [le_antisymm h hs, zero_mul]
  · rw [inv_smul_smul_real (ne_of_gt (lt_of_not_ge h))]

theorem sum_ofReal_pmf {α : Type*} [Fintype α] (p : ProbDist α) :
    ∑ i, ((p.pmf i : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_sum, p.sum_one, Complex.ofReal_one]

/-- **Receiver-1 corner.** Every rate `0 ≤ r ≤ χ(p; B₁)` (Holevo information of the first
marginal for any input law `p`) gives a point `(r, 0)` of the quantum Marton region
(`W, V` constant, `U = X`). -/
theorem holevo1_corner_mem {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂))
    (p : ProbDist (Fin kX)) {r : ℝ} (hr : 0 ≤ r) (hrχ : r ≤ holevo1 W p) :
    (r, 0) ∈ cqMartonInnerBound W := by
  refine subset_closure ⟨hr, le_rfl, 1, kX, 1, cornerLaw1 p, ?_⟩
  have hc := condMutualInfo_le_zero_of_unique_mid
    ((cornerLaw1 p).map fun t => (t.2.1, t.2.2.1, t.1))
  have ht : ∀ x, (if p.pmf x ≤ 0 then 0 else
      p.pmf x * matEntropy (((p.pmf x : ℂ))⁻¹ • (p.pmf x • @partialTraceB d₁ d₂ (W x).mat))) =
      p.pmf x * matEntropy (@partialTraceB d₁ d₂ (W x).mat) :=
    fun x => ite_term_eq (p.nonneg x) _
  unfold holevo1 at hrχ
  simp only [Complex.coe_smul] at hrχ
  dsimp only
  have h10 : ¬ ((1 : ℝ) ≤ 0) := by norm_num
  simp [cornerLaw1_pmf, Fintype.sum_prod_type, p.sum_one, ht]
  simp only [h10, ↓reduceIte]
  exact ⟨hrχ, le_rfl, by linarith, by linarith⟩

/-- **Receiver-2 corner.** Every rate `0 ≤ r ≤ χ(p; B₂)` gives a point `(0, r)` of the quantum
Marton region (`W, U` constant, `V = X`). -/
theorem holevo2_corner_mem {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂))
    (p : ProbDist (Fin kX)) {r : ℝ} (hr : 0 ≤ r) (hrχ : r ≤ holevo2 W p) :
    (0, r) ∈ cqMartonInnerBound W := by
  refine subset_closure ⟨le_rfl, hr, 1, 1, kX, cornerLaw2 p, ?_⟩
  have hc := condMutualInfo_le_zero_of_unique_fst
    ((cornerLaw2 p).map fun t => (t.2.1, t.2.2.1, t.1))
  have ht : ∀ x, (if p.pmf x ≤ 0 then 0 else
      p.pmf x * matEntropy (((p.pmf x : ℂ))⁻¹ • (p.pmf x • @partialTraceA d₁ d₂ (W x).mat))) =
      p.pmf x * matEntropy (@partialTraceA d₁ d₂ (W x).mat) :=
    fun x => ite_term_eq (p.nonneg x) _
  unfold holevo2 at hrχ
  simp only [Complex.coe_smul] at hrχ
  dsimp only
  have h10 : ¬ ((1 : ℝ) ≤ 0) := by norm_num
  simp [cornerLaw2_pmf, Fintype.sum_prod_type, p.sum_one, ht]
  simp only [h10, ↓reduceIte]
  exact ⟨le_rfl, hrχ, by linarith, by linarith⟩

/-! ### Both sides contain the origin -/

/-- Point mass at `x₀`. -/
noncomputable def pointMass {kX : ℕ} (x₀ : Fin kX) : ProbDist (Fin kX) where
  pmf x := if x = x₀ then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by simp

theorem holevo1_pointMass {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂)) (x₀ : Fin kX) :
    holevo1 W (pointMass x₀) = 0 := by
  simp [holevo1, pointMass]

theorem zero_mem_cqMartonInnerBound {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂))
    (hkX : 0 < kX) : ((0 : ℝ), (0 : ℝ)) ∈ cqMartonInnerBound W :=
  holevo1_corner_mem W (pointMass ⟨0, hkX⟩) le_rfl (holevo1_pointMass W _).ge

theorem trace_kronMat {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    (kronMat A B).trace = A.trace * B.trace := by
  rw [kronMat_eq_reindex, ← Matrix.trace_kronecker]
  unfold Matrix.trace
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl

theorem trace_kronPowerMat_of_trace_one {a : ℕ} :
    ∀ (n : ℕ) (f : Fin n → Matrix (Fin a) (Fin a) ℂ), (∀ i, (f i).trace = 1) →
      (kronPowerMat n f).trace = 1
  | 0, f, _ => by
    show ∑ _i : Fin (a ^ 0), (1 : ℂ) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, pow_zero, one_smul]
  | n + 1, f, hf =>
    (trace_kronMat _ _).trans (by
      rw [trace_kronPowerMat_of_trace_one n _ (fun i => hf _), hf, one_mul])

private lemma natMax_zero (n : ℕ) : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0))) = 1 := by
  simp

theorem isPOVM_one (D : ℕ) : IsPOVM D 1 (fun _ => (1 : Matrix (Fin D) (Fin D) ℂ)) :=
  ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

theorem zero_mem_cqBroadcastCapacityRegion {kX d₁ d₂ : ℕ}
    (W : Fin kX → DensityMatrix (d₁ * d₂)) (hkX : 0 < kX) :
    ((0 : ℝ), (0 : ℝ)) ∈ cqBroadcastCapacityRegion W := by
  refine subset_closure ⟨le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  rw [natMax_zero]
  refine ⟨fun _ _ _ => ⟨0, hkX⟩, fun _ => 1, fun _ => 1, isPOVM_one _, isPOVM_one _, ?_⟩
  dsimp only
  have h1 := trace_kronPowerMat_of_trace_one n (fun _ => @partialTraceB d₁ d₂ (W ⟨0, hkX⟩).mat)
    (fun _ => (marg1_state _).2)
  have h2 := trace_kronPowerMat_of_trace_one n (fun _ => @partialTraceA d₁ d₂ (W ⟨0, hkX⟩).mat)
    (fun _ => (marg2_state _).2)
  simp only [one_mul, h1, h2]
  norm_num
  exact Or.inl hε

/-! ### The operational region is bounded: `R₁ ≤ log₂ d₁`, `R₂ ≤ log₂ d₂` -/

/-- `Re Tr(Λ ρ) ≤ Re Tr Λ` for a PSD `Λ` and a state `ρ` (since `ρ ≤ 1`). -/
theorem trace_mul_state_re_le {D : ℕ} {Λ ρ : Matrix (Fin D) (Fin D) ℂ} (hΛ : Λ.PosSemidef)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) : (Λ * ρ).trace.re ≤ Λ.trace.re := by
  classical
  set U : Matrix (Fin D) (Fin D) ℂ := (hρ.1.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)
    with hU
  set lam : Fin D → ℝ := hρ.1.eigenvalues with hlam
  have hspec : ρ = U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * star U := by
    have := hρ.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hρ.1.eigenvectorUnitary.2
  have hsum : ∑ i, lam i = 1 := by
    have := hρ.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 : ((∑ i, lam i : ℝ) : ℂ) = 1 := by
      rw [this]; push_cast; rfl
    exact_mod_cast h2
  have hlam0 : ∀ i, 0 ≤ lam i := hρ.eigenvalues_nonneg
  have hlam1 : ∀ i, lam i ≤ 1 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (f := lam) (fun j _ => hlam0 j) (Finset.mem_univ i)
  set N := star U * Λ * U with hN
  have hNpsd : N.PosSemidef := by
    have := hΛ.conjTranspose_mul_mul_same U
    rw [hN, Matrix.star_eq_conjTranspose]
    exact this
  have htrΛ : Λ.trace = N.trace := by
    rw [hN, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htrΛρ : (Λ * ρ).trace = (N * diagonal (fun i => ((lam i : ℝ) : ℂ))).trace := by
    rw [hspec, hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [htrΛρ, htrΛ]
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.mul_diagonal, Complex.re_sum, Complex.re_mul_ofReal]
  refine Finset.sum_le_sum fun i _ => ?_
  have hd : 0 ≤ (N i i).re := (Complex.nonneg_iff.mp (hNpsd.diag_nonneg (i := i))).1
  nlinarith [hlam1 i, hlam0 i]

theorem kronMat_posSemidef {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℂ}
    {B : Matrix (Fin b) (Fin b) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (kronMat A B).PosSemidef := by
  rw [kronMat_eq_reindex]
  exact (hA.kronecker hB).submatrix _

theorem kronPowerMat_posSemidef {a : ℕ} :
    ∀ (n : ℕ) (f : Fin n → Matrix (Fin a) (Fin a) ℂ), (∀ i, (f i).PosSemidef) →
      (kronPowerMat n f).PosSemidef
  | 0, f, _ => by
    have hfun : (kronPowerMat 0 f : Matrix (Fin (a ^ 0)) (Fin (a ^ 0)) ℂ) =
        (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (a ^ 0)) (Fin (a ^ 0)) ℂ) := rfl
    have hsub : Subsingleton (Fin (a ^ 0)) := by rw [pow_zero]; infer_instance
    have h1 : (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (a ^ 0)) (Fin (a ^ 0)) ℂ) = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      rfl
    rw [hfun, h1]
    exact Matrix.PosSemidef.one
  | n + 1, f, hf =>
    kronMat_posSemidef (kronPowerMat_posSemidef n _ (fun i => hf _)) (hf _)

/-- Average success probability of `M₁` messages decoded by a POVM on `ℂ^D` is at most
`D / M₁`. -/
theorem avg_success_le {D M₁ M₂ : ℕ} (hM₂ : 0 < M₂) (Λ : Fin M₁ → Matrix (Fin D) (Fin D) ℂ)
    (hΛ : IsPOVM D M₁ Λ) (σ : Fin M₁ → Fin M₂ → Matrix (Fin D) (Fin D) ℂ)
    (hσ : ∀ m₁ m₂, (σ m₁ m₂).PosSemidef ∧ (σ m₁ m₂).trace = 1) :
    ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
      (Λ m₁ * σ m₁ m₂).trace.re ≤ (D : ℝ) / (M₁ : ℝ) := by
  have hle : ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (Λ m₁ * σ m₁ m₂).trace.re ≤
      ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, (Λ m₁).trace.re :=
    Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
      trace_mul_state_re_le (hΛ.1 m₁) (hσ m₁ m₂).1 (hσ m₁ m₂).2
  have htot : ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂, (Λ m₁).trace.re = (M₂ : ℝ) * D := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Matrix.trace_sum, hΛ.2, Matrix.trace_one,
      Fintype.card_fin, Complex.natCast_re]
  rcases Nat.eq_zero_or_pos M₁ with h0 | hM₁
  · subst h0; simp
  have hpos : (0 : ℝ) < ((M₁ * M₂ : ℕ) : ℝ) := by positivity
  calc ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
        (Λ m₁ * σ m₁ m₂).trace.re
      ≤ ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ((M₂ : ℝ) * D) := by
        rw [← htot]; exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (D : ℝ) / (M₁ : ℝ) := by
        push_cast
        field_simp

private lemma natMax_one_floor_ge' (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
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

/-- If eventually `1/2 ≤ Dⁿ / ⌊2^{nR}⌋`, then `R ≤ log₂ D`. -/
theorem rate_le_log2 {D : ℕ} {R : ℝ} (hR : 0 ≤ R) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → (1 : ℝ) / 2 ≤
      ((D ^ n : ℕ) : ℝ) / ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ)) :
    R ≤ log2 D := by
  -- `2^{nR} ≤ 4 Dⁿ` for all large `n`
  have key : ∀ n : ℕ, N ≤ n → (2 : ℝ) ^ ((n : ℝ) * R) ≤ 4 * (D : ℝ) ^ n := by
    intro n hn
    have hM := natMax_one_floor_ge' n hR
    have hMpos : (0 : ℝ) < ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
      have : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) :=
        lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      exact_mod_cast this
    have h1 := h n hn
    rw [le_div_iff₀ hMpos, Nat.cast_pow] at h1
    linarith
  rcases Nat.eq_zero_or_pos D with hD | hD
  · exfalso
    have := key (N + 1) (Nat.le_succ N)
    rw [hD] at this
    simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero N), mul_zero] at this
    exact absurd this (not_le.mpr (Real.rpow_pos_of_pos two_pos _))
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogk : ∀ n : ℕ, N ≤ n → (n : ℝ) * R * Real.log 2 ≤ Real.log 4 + n * Real.log D := by
    intro n hn
    have := Real.log_le_log (Real.rpow_pos_of_pos two_pos _) (key n hn)
    rw [Real.log_rpow two_pos, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    exact this
  by_contra hcon
  push Not at hcon
  have hδ : 0 < R * Real.log 2 - Real.log D := by
    unfold log2 at hcon
    rw [div_lt_iff₀ hlog2] at hcon
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log 4 / (R * Real.log 2 - Real.log D) + N)
  have hnN : N ≤ n := by
    have : (N : ℝ) < n := by
      have : 0 ≤ Real.log 4 / (R * Real.log 2 - Real.log D) :=
        div_nonneg (Real.log_nonneg (by norm_num)) hδ.le
      linarith
    exact_mod_cast this.le
  have h1 := hlogk n hnN
  have h2 : Real.log 4 < n * (R * Real.log 2 - Real.log D) := by
    have : Real.log 4 / (R * Real.log 2 - Real.log D) < n := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    rwa [div_lt_iff₀ hδ] at this
  nlinarith

/-- **Converse (dimension bound) for receiver 1.** -/
theorem achievable_rate₁_le {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂)) {R₁ R₂ : ℝ}
    (h : IsCQBroadcastAchievable W R₁ R₂) : R₁ ≤ log2 d₁ := by
  obtain ⟨hR₁, hR₂, h⟩ := h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  refine rate_le_log2 hR₁ N fun n hn => ?_
  obtain ⟨enc, Λ₁, Λ₂, hΛ₁, hΛ₂, hs₁, -⟩ := hN n hn
  have hM₂ : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂))) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have := avg_success_le hM₂ Λ₁ hΛ₁
    (fun m₁ m₂ => kronPowerMat n (fun i => @partialTraceB d₁ d₂ (W (enc m₁ m₂ i)).mat))
    (fun m₁ m₂ => ⟨kronPowerMat_posSemidef n _ (fun i => (marg1_state _).1),
      trace_kronPowerMat_of_trace_one n _ (fun i => (marg1_state _).2)⟩)
  linarith

/-- **Converse (dimension bound) for receiver 2.** -/
theorem achievable_rate₂_le {kX d₁ d₂ : ℕ} (W : Fin kX → DensityMatrix (d₁ * d₂)) {R₁ R₂ : ℝ}
    (h : IsCQBroadcastAchievable W R₁ R₂) : R₂ ≤ log2 d₂ := by
  obtain ⟨hR₁, hR₂, h⟩ := h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  refine rate_le_log2 hR₂ N fun n hn => ?_
  obtain ⟨enc, Λ₁, Λ₂, hΛ₁, hΛ₂, -, hs₂⟩ := hN n hn
  have hM₁ : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁))) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have := avg_success_le hM₁ Λ₂ hΛ₂
    (fun m₂ m₁ => kronPowerMat n (fun i => @partialTraceA d₁ d₂ (W (enc m₁ m₂ i)).mat))
    (fun m₂ m₁ => ⟨kronPowerMat_posSemidef n _ (fun i => (marg2_state _).1),
      trace_kronPowerMat_of_trace_one n _ (fun i => (marg2_state _).2)⟩)
  rw [Finset.sum_comm, Nat.mul_comm] at this
  linarith

/-- The operational capacity region lies in `[0, log₂ d₁] × [0, log₂ d₂]`. -/
theorem cqBroadcastCapacityRegion_subset_box {kX d₁ d₂ : ℕ}
    (W : Fin kX → DensityMatrix (d₁ * d₂)) :
    cqBroadcastCapacityRegion W ⊆ Set.Icc 0 (log2 d₁) ×ˢ Set.Icc 0 (log2 d₂) := by
  refine closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  exact ⟨⟨hp.1, achievable_rate₁_le W hp⟩, ⟨hp.2.1, achievable_rate₂_le W hp⟩⟩

end InfoTheory.Known.Certificates.QuantumBroadcastCapacity
