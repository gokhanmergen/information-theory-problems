import InfoTheory.Problems.SicPovmZauner

/-!
# Certificate for `InfoTheory.Problems.SicPovmZauner`

The frozen statement is Zauner's conjecture: `∀ d ≥ 2, ∃ ψ, IsSICPOVM d ψ`, where
`IsSICPOVM d ψ` asks for `d²` unit vectors in `ℂ^d` with `|⟨ψ_j|ψ_k⟩|² = 1/(d+1)`, `j ≠ k`.

## Certified
* **Regression `d = 2` (tetrahedral / Bloch-sphere SIC):** `sic_dim_two : ∃ ψ, IsSICPOVM 2 ψ`,
  witnessed by `tetraSIC = (1,0), (1/√3, √(2/3)·ωᵏ)` (`k = 0,1,2`, `ω = e^{2πi/3}`),
  whose Bloch vectors form a regular tetrahedron. So `IsSICPOVM` is satisfiable in the
  first dimension covered by the statement (the predicate is not junk-false).
* `sic_dim_one : ∃ ψ, IsSICPOVM 1 ψ` (the trivial one-vector SIC in `d = 1`, excluded by the
  statement's `2 ≤ d`).
* **Non-triviality:** `not_sic_two_real : ¬ IsSICPOVM 2 ψ` for any family with real
  entries (`ψ j r = (x j r : ℂ)`, `x` real); the defining overlap condition genuinely forces
  complex amplitudes (there are at most 3 equiangular lines in `ℝ²`), so `IsSICPOVM` is not
  junk-true either.

## Not certified
* Any `d ≥ 3` (e.g. the Hesse SIC in `d = 3`); the Gerzon bound `≤ d²` equiangular lines.

## Adversarial check (2026-11-27)
The statement asks exactly for `d²` equiangular unit vectors with overlap `1/(d+1)` in
every `d ≥ 2`, which is the standard Zauner existence question (not the stronger
Weyl–Heisenberg-covariant version). Exact SICs are known only in finitely many dimensions;
infinite families are known only conditionally on the Stark conjectures
(Appleby–Flammia–McConnell–Yard; Kopp; Appleby–Bengtsson–Grassl–Harrison–McConnell 2022).
No unconditional resolution found through 2026. Statement FINE; Lean not modified.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.SicPovmZauner

open InfoTheory

/-- The trivial SIC in dimension one. -/
theorem sic_dim_one : ∃ ψ : Fin (1 * 1) → Fin 1 → ℂ, IsSICPOVM 1 ψ := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro j; simp
  · intro j k hjk
    exact absurd (Subsingleton.elim (α := Fin 1) j k) hjk

/-- `√3`. -/
noncomputable abbrev s3 : ℝ := Real.sqrt 3
/-- `√2`. -/
noncomputable abbrev s2 : ℝ := Real.sqrt 2

/-- The tetrahedral qubit SIC: `(1,0)` and `(1/√3, √(2/3) ωᵏ)`, `ω = (-1 + i√3)/2`. -/
noncomputable def tetraSIC : Fin (2 * 2) → Fin 2 → ℂ :=
  ![![1, 0],
    ![⟨1 / s3, 0⟩, ⟨s2 / s3, 0⟩],
    ![⟨1 / s3, 0⟩, ⟨-(s2 / (2 * s3)), s2 / 2⟩],
    ![⟨1 / s3, 0⟩, ⟨-(s2 / (2 * s3)), -(s2 / 2)⟩]]

private lemma s3_sq : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma s2_sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma s3_pos : 0 < s3 := Real.sqrt_pos.2 (by norm_num)

/-- The tetrahedral vectors form a SIC-POVM in `ℂ²`. -/
theorem tetraSIC_isSIC : IsSICPOVM 2 tetraSIC := by
  have h3 := s3_sq
  have h2 := s2_sq
  have hp := s3_pos
  have hne : s3 ≠ 0 := hp.ne'
  refine ⟨?_, ?_⟩
  · intro j
    fin_cases j <;>
      simp [tetraSIC, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply] <;>
      field_simp <;> nlinarith
  · intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | exact absurd rfl hjk
      | (simp [tetraSIC, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
         field_simp
         ring_nf
         have h4 : s2 ^ 4 = 4 := by nlinarith
         have h34 : s3 ^ 4 = 9 := by nlinarith
         have h23 : s2 ^ 2 * s3 ^ 2 = 6 := by rw [h2, h3]; norm_num
         have h43 : s2 ^ 4 * s3 ^ 2 = 12 := by rw [h4, h3]; norm_num
         have h44 : s2 ^ 4 * s3 ^ 4 = 36 := by rw [h4, h34]; norm_num
         linarith)

theorem sic_dim_two : ∃ ψ : Fin (2 * 2) → Fin 2 → ℂ, IsSICPOVM 2 ψ :=
  ⟨tetraSIC, tetraSIC_isSIC⟩

/-- No SIC in `ℂ²` has all amplitudes real. -/
theorem not_sic_two_real (x : Fin (2 * 2) → Fin 2 → ℝ) :
    ¬ IsSICPOVM 2 (fun j r => (x j r : ℂ)) := by
  rintro ⟨hn, ho⟩
  have n : ∀ j, x j 0 ^ 2 + x j 1 ^ 2 = 1 := by
    intro j
    have := hn j
    simp only [Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    exact this
  have o : ∀ j k : Fin (2 * 2), j ≠ k → (x j 0 * x k 0 + x j 1 * x k 1) ^ 2 = 1 / 3 := by
    intro j k hjk
    have := ho j k hjk
    have e : ∑ r : Fin 2, star ((x j r : ℂ)) * (x k r : ℂ) =
        ((x j 0 * x k 0 + x j 1 * x k 1 : ℝ) : ℂ) := by
      simp [Fin.sum_univ_two, Complex.conj_ofReal]
    rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    rw [this]; norm_num
  -- Coordinates relative to `u = x 0` and `u⊥ = (-u₁, u₀)`.
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * 2) → ℝ, ∀ k, a k = x 0 0 * x k 0 + x 0 1 * x k 1 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (2 * 2) → ℝ, ∀ k, b k = -x 0 1 * x k 0 + x 0 0 * x k 1 :=
    ⟨_, fun _ => rfl⟩
  have hu := n 0
  have inner : ∀ j k : Fin (2 * 2),
      x j 0 * x k 0 + x j 1 * x k 1 = a j * a k + b j * b k := by
    intro j k
    rw [ha, ha, hb, hb]
    linear_combination (-(x j 0 * x k 0 + x j 1 * x k 1)) * hu
  have hab : ∀ k, a k ^ 2 + b k ^ 2 = 1 := by
    intro k
    have := inner k k
    nlinarith [n k, this]
  have ha2 : ∀ k : Fin (2 * 2), 0 ≠ k → a k ^ 2 = 1 / 3 := by
    intro k hk
    rw [ha]; exact o 0 k hk
  have hb2 : ∀ k : Fin (2 * 2), 0 ≠ k → b k ^ 2 = 2 / 3 := by
    intro k hk
    have := hab k; have := ha2 k hk; linarith
  -- For distinct `j, k ≠ 0`: `(a_j a_k + b_j b_k)² = 1/3` with `a² = 1/3`, `b² = 2/3`
  -- forces `a_j a_k b_j b_k = -1/9`; the product over the three pairs is then a negative
  -- square.
  have prod : ∀ j k : Fin (2 * 2), j ≠ k → 0 ≠ j → 0 ≠ k →
      a j * a k * b j * b k = -1 / 9 := by
    intro j k hjk hj hk
    have e := o j k hjk
    rw [inner] at e
    have h1 : (a j * a k) ^ 2 = 1 / 9 := by rw [mul_pow, ha2 j hj, ha2 k hk]; norm_num
    have h2 : (b j * b k) ^ 2 = 4 / 9 := by rw [mul_pow, hb2 j hj, hb2 k hk]; norm_num
    nlinarith [e, h1, h2]
  have p12 := prod 1 2 (by decide) (by decide) (by decide)
  have p13 := prod 1 3 (by decide) (by decide) (by decide)
  have p23 := prod 2 3 (by decide) (by decide) (by decide)
  have : (a 1 * a 2 * a 3 * b 1 * b 2 * b 3) ^ 2 = -1 / 729 := by
    have : (a 1 * a 2 * a 3 * b 1 * b 2 * b 3) ^ 2 =
        (a 1 * a 2 * b 1 * b 2) * (a 1 * a 3 * b 1 * b 3) * (a 2 * a 3 * b 2 * b 3) := by ring
    rw [this, p12, p13, p23]; norm_num
  nlinarith [sq_nonneg (a 1 * a 2 * a 3 * b 1 * b 2 * b 3)]

end InfoTheory.Known.Certificates.SicPovmZauner
