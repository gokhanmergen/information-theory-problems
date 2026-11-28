import InfoTheory.Problems.QuantumReverseShannonNonCatalytic
import InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold

/-!
# Certificate for `InfoTheory.Problems.QuantumReverseShannonNonCatalytic`

The frozen statement asks whether, for every qubit channel `N : M₂ → M₂`, the regularized
channel entanglement cost `E_C(N) = inf_{n ≥ 1} (1/n) sup_ρ E_F((id ⊗ N^{⊗n})(ρ))`
(reference dimension `2ⁿ`) equals the single-letter `E_F(N) = sup_ρ E_F((id ⊗ N)(ρ))`
(Berta–Brandão–Christandl–Wehner 2013).

## Certified
* `partialTraceB_eq_sum` (`Tr_B M = ∑_b V_b M V_b†` with `V_b = ⟨b|_B`),
  `partialTraceB_posSemidef`, `partialTraceB_trace`: `partialTraceB` is a genuine CPTP
  partial trace.
* `pureMat_posSemidef`, `pureMat_trace`: `|ψ⟩⟨ψ|` for a unit vector is a state.
* **Non-junk values:** `entanglementOfFormation_nonneg` (every term of the `sInf` is an
  average of reduced-state entropies, hence `≥ 0`), `channelEF_nonneg`,
  `channelEntanglementCost_nonneg`, and `channelEntanglementCost_le_one_letter`
  (`E_C(N) ≤` its `n = 1` term; the infimum is over a nonempty set bounded below).

## Not certified
* Explicit values (e.g. `E_F(id₂) = 1`, `E_F = 0` for entanglement-breaking channels), which
  need concavity/lower bounds of `E_F` over all decompositions; the BBCW coding theorem.

## Adversarial check (2026-11-27)
The `.md` defines `E_C` as the limit `lim (1/n) E_F(N^{⊗n})`; the Lean uses `inf_n`. These
agree given `E_C(N) ≤ E_F(N)` for all channels (apply it to `N^{⊗n}` and use
`E_C(N^{⊗n}) = n E_C(N)`), which is part of the BBCW characterization; minor doubt recorded,
not a modeling error. The reference dimension `d₁` (resp. `d₁ⁿ`) suffices (purifications).
Hastings-type non-additivity is only known in high dimension; for qubit channels the
question is open (as is additivity of `E_F` for two-qubit states). No resolution found
through 2026. Statement FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.QuantumReverseShannonNonCatalytic

open InfoTheory InfoTheory.Problems.QuantumReverseShannonNonCatalytic Matrix

/-- The isometry-component `V_b : ℂ^{dA·dB} → ℂ^{dA}`, `|a, b⟩ ↦ |a⟩`. -/
def slice {dA dB : ℕ} (b : Fin dB) : Matrix (Fin dA) (Fin (dA * dB)) ℂ :=
  Matrix.of fun a i => if i.1 = a.1 * dB + b.1 then 1 else 0

theorem partialTraceB_eq_sum {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    @partialTraceB dA dB M = ∑ b : Fin dB, slice b * M * (slice b)ᴴ := by
  ext a₁ a₂
  simp only [partialTraceB, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, slice]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hlt : ∀ a : Fin dA, a.1 * dB + b.1 < dA * dB := fun a => by
    calc a.1 * dB + b.1 < a.1 * dB + dB := Nat.add_lt_add_left b.2 _
      _ = (a.1 + 1) * dB := by ring
      _ ≤ dA * dB := Nat.mul_le_mul_right dB a.2
  have key : ∀ (a : Fin dA) (f : Fin (dA * dB) → ℂ),
      ∑ i : Fin (dA * dB), (if i.1 = a.1 * dB + b.1 then (1 : ℂ) else 0) * f i =
        f ⟨a.1 * dB + b.1, hlt a⟩ := by
    intro a f
    rw [Finset.sum_eq_single ⟨a.1 * dB + b.1, hlt a⟩]
    · simp
    · intro i _ hi
      rw [if_neg (fun h => hi (Fin.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have key2 : ∀ (a : Fin dA) (f : Fin (dA * dB) → ℂ),
      ∑ j : Fin (dA * dB), f j * star (if j.1 = a.1 * dB + b.1 then (1 : ℂ) else 0) =
        f ⟨a.1 * dB + b.1, hlt a⟩ := by
    intro a f
    rw [Finset.sum_eq_single ⟨a.1 * dB + b.1, hlt a⟩]
    · simp
    · intro j _ hj
      rw [if_neg (fun h => hj (Fin.ext h)), star_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key2]
  exact (key a₁ (fun i => M i ⟨a₂.1 * dB + b.1, hlt a₂⟩)).symm

theorem partialTraceB_posSemidef {dA dB : ℕ} {M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ}
    (hM : M.PosSemidef) : (@partialTraceB dA dB M).PosSemidef := by
  rw [partialTraceB_eq_sum]
  exact posSemidef_sum _ fun b _ => hM.mul_mul_conjTranspose_same (slice b)

theorem partialTraceB_trace {dA dB : ℕ} (M : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    (@partialTraceB dA dB M).trace = M.trace := by
  unfold Matrix.trace
  simp only [partialTraceB, Matrix.of_apply, Matrix.diag]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv finProdFinEquiv _ _ fun x => ?_
  have he : finProdFinEquiv x = ⟨x.1.1 * dB + x.2.1, by
      calc x.1.1 * dB + x.2.1 < x.1.1 * dB + dB := Nat.add_lt_add_left x.2.2 _
        _ = (x.1.1 + 1) * dB := by ring
        _ ≤ dA * dB := Nat.mul_le_mul_right dB x.1.2⟩ :=
    Fin.ext (by rw [finProdFinEquiv_apply_val]; ring)
  rw [he]

/-! ### Pure states -/

/-- Row vector `⟨ψ|` (conjugated amplitudes). -/
def braRow {d : ℕ} (ψ : Fin d → ℂ) : Matrix (Fin 1) (Fin d) ℂ := Matrix.of fun _ j => star (ψ j)

theorem pureMat_eq {d : ℕ} (ψ : Fin d → ℂ) :
    (Matrix.of fun i j => ψ i * star (ψ j)) = (braRow ψ)ᴴ * braRow ψ := by
  ext i j
  simp [braRow, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem pureMat_posSemidef {d : ℕ} (ψ : Fin d → ℂ) :
    (Matrix.of fun i j => ψ i * star (ψ j)).PosSemidef := by
  rw [pureMat_eq]; exact posSemidef_conjTranspose_mul_self _

theorem pureMat_trace {d : ℕ} (ψ : Fin d → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    (Matrix.of fun i j => ψ i * star (ψ j)).trace = 1 := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.of_apply, Complex.star_def, Complex.mul_conj']
  exact_mod_cast hψ

/-! ### Nonnegativity: the `sInf`/`sSup` are not junk-negative -/

/-- `E_F(σ) ≥ 0` (each pure-state term is the entropy of a reduced state). -/
theorem entanglementOfFormation_nonneg {dA dB : ℕ}
    (σ : Matrix (Fin (dA * dB)) (Fin (dA * dB)) ℂ) :
    0 ≤ @entanglementOfFormation dA dB σ := by
  apply Real.sInf_nonneg
  rintro r ⟨m, P, ψ, hn, -, rfl⟩
  refine Finset.sum_nonneg fun k _ => mul_nonneg (P.nonneg k) ?_
  exact ClassicalCapacityAdditivityThreshold.matEntropy_nonneg_of_state
    (partialTraceB_posSemidef (pureMat_posSemidef (ψ k)))
    (by rw [partialTraceB_trace, pureMat_trace _ (hn k)])

theorem channelEF_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) : 0 ≤ channelEF N := by
  apply Real.sSup_nonneg
  rintro r ⟨ρ, rfl⟩
  exact entanglementOfFormation_nonneg _

theorem channelEntanglementCost_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    0 ≤ channelEntanglementCost N := by
  apply Real.sInf_nonneg
  rintro r ⟨n, -, rfl⟩
  refine div_nonneg (Real.sSup_nonneg ?_) (Nat.cast_nonneg _)
  rintro e ⟨ρ, rfl⟩
  exact entanglementOfFormation_nonneg _

/-- The `n = 1` term of `E_C` is `E_F(N)` up to the reference dimension `d₁¹`; in
    particular `E_C(N) ≤` that term (the `inf` is over a set bounded below by `0`). -/
theorem channelEntanglementCost_le_one_letter {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    channelEntanglementCost N ≤
      (sSup { e : ℝ | ∃ (ρ : DensityMatrix (d₁ ^ 1 * d₁ ^ 1)),
        e = entanglementOfFormation (idTensorPowerApply (d₁ ^ 1) N 1 ρ.mat) }) / (1 : ℕ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨n, -, rfl⟩
    refine div_nonneg (Real.sSup_nonneg ?_) (Nat.cast_nonneg _)
    rintro e ⟨ρ, rfl⟩
    exact entanglementOfFormation_nonneg _
  · exact ⟨1, one_pos, rfl⟩

end InfoTheory.Known.Certificates.QuantumReverseShannonNonCatalytic
