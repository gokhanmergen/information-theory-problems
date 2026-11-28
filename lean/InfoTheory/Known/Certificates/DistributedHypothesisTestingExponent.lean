import InfoTheory.Problems.DistributedHypothesisTestingExponent
import InfoTheory.Bridge.Mathlib

/-!
# Certificate for `InfoTheory.Problems.DistributedHypothesisTestingExponent`

The frozen statement asks whether the operational type-II error exponent
`dhtOptimalExponent P Q R` of two-terminal distributed hypothesis testing equals the
time-shared Shimokawa–Han–Amari exponent `shaInnerBound P Q R` for all full-support binary
pairs `(P, Q)` and rates `R > 0`.

Certified here, about the exact objects of `Statement`:
* `iid_sum_one`, `type1_add_type2_self` — the `n`-letter laws are probability distributions,
  and when `P = Q` the two error probabilities of any test sum to `1`;
* `zero_mem_dhtSet`, `dhtOptimalExponent_nonneg` — exponent `0` is always achievable (accept
  everything), so `E* ≥ 0` and the `sSup` set is nonempty;
* **regression (`P = Q`, no test can tell the hypotheses apart)**:
  `dhtSet_le_zero_self`, `dhtOptimalExponent_self` — `E*(R, P, P) = 0` for every `P`, `R`
  (the known value: Stein exponent `D(P‖P) = 0`). This also shows the `sSup` is not the junk
  value of an unbounded set;
* `shaInnerBoundRaw_nonneg`, `shaInnerBound_nonneg` — the SHA quantities are `≥ 0` (each
  `sInf` is over KL values against `Q̃ = P_{U|X} Q` with the absolute-continuity guard, and the
  binning term carries `R - I(U;X|Y) ≥ 0`).

Not certified: the SHA achievability `E_SHA ≤ E*`, the Ahlswede–Csiszár formula for testing
against independence, the upper bound `E* ≤ D(P‖Q)` for general `(P, Q)`, and the value
`E_SHA(R, P, P) = 0` (needs the Markov factorization from `I(U;Y|X) = 0`). These facts do not
settle `Statement`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.DistributedHypothesisTestingExponent

open InfoTheory InfoTheory.Problems.DistributedHypothesisTestingExponent

theorem iid_sum_one {α : Type*} [Fintype α] (P : ProbDist α) (n : ℕ) :
    ∑ x : Fin n → α, ∏ i : Fin n, P.pmf (x i) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) a => P.pmf a)]
  simp [P.sum_one]

/-- Under `P = Q`, type-I plus type-II error of any test equals `1`. -/
theorem type1_add_type2_self {X Y : Type*} [Fintype X] [Fintype Y] (P : ProbDist (X × Y))
    (n : ℕ) (t : (Fin n → X × Y) → Bool) :
    (∑ xy : Fin n → X × Y, (∏ i : Fin n, P.pmf (xy i)) * if t xy = false then 1 else 0) +
    (∑ xy : Fin n → X × Y, (∏ i : Fin n, P.pmf (xy i)) * if t xy = true then 1 else 0) = 1 := by
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl (fun xy _ => ?_)).trans (iid_sum_one P n)
  cases t xy <;> simp

theorem zero_mem_dhtSet {X Y : Type*} [Fintype X] [Fintype Y] (P Q : ProbDist (X × Y))
    (R : ℝ) :
    (0 : ℝ) ∈ { E : ℝ | ∀ (ε : ℝ), 0 < ε →
      ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
        let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
        ∃ (enc : (Fin n → X) → Fin M) (acc : Fin M → (Fin n → Y) → Bool),
          let type1 := ∑ xy : Fin n → X × Y,
            (∏ i : Fin n, P.pmf (xy i)) *
              if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = false then 1 else 0
          let type2 := ∑ xy : Fin n → X × Y,
            (∏ i : Fin n, Q.pmf (xy i)) *
              if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = true then 1 else 0
          type1 ≤ ε ∧ type2 ≤ (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) } := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hM : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨fun _ => ⟨0, hM⟩, fun _ _ => true, ?_, ?_⟩
  · simp [hε.le]
  · simp only [if_true, mul_one, iid_sum_one]
    apply Real.one_le_rpow (by norm_num)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

theorem dhtOptimalExponent_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (P Q : ProbDist (X × Y)) (R : ℝ) : 0 ≤ dhtOptimalExponent P Q R := by
  unfold dhtOptimalExponent
  by_cases hb : BddAbove { E : ℝ | ∀ (ε : ℝ), 0 < ε →
      ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
        let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
        ∃ (enc : (Fin n → X) → Fin M) (acc : Fin M → (Fin n → Y) → Bool),
          let type1 := ∑ xy : Fin n → X × Y,
            (∏ i : Fin n, P.pmf (xy i)) *
              if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = false then 1 else 0
          let type2 := ∑ xy : Fin n → X × Y,
            (∏ i : Fin n, Q.pmf (xy i)) *
              if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = true then 1 else 0
          type1 ≤ ε ∧ type2 ≤ (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) }
  · exact le_csSup hb (zero_mem_dhtSet P Q R)
  · rw [Real.sSup_of_not_bddAbove hb]

/-- Regression: with identical hypotheses no positive exponent is achievable. -/
theorem dhtSet_le_zero_self {X Y : Type*} [Fintype X] [Fintype Y] (P : ProbDist (X × Y))
    (R E : ℝ)
    (hE : ∀ (ε : ℝ), 0 < ε →
      ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
        let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
        ∃ (enc : (Fin n → X) → Fin M) (acc : Fin M → (Fin n → Y) → Bool),
          let type1 := ∑ xy : Fin n → X × Y,
            (∏ i : Fin n, P.pmf (xy i)) *
              if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = false then 1 else 0
          let type2 := ∑ xy : Fin n → X × Y,
            (∏ i : Fin n, P.pmf (xy i)) *
              if acc (enc (fun i => (xy i).1)) (fun i => (xy i).2) = true then 1 else 0
          type1 ≤ ε ∧ type2 ≤ (2 : ℝ) ^ (-(n : ℝ) * (E - ε))) : E ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  set ε : ℝ := min (E / 2) (1 / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεE : ε ≤ E / 2 := min_le_left _ _
  have hε4 : ε ≤ 1 / 4 := min_le_right _ _
  obtain ⟨N, hN⟩ := hE ε hε0
  set n : ℕ := max N (Nat.ceil (2 / E)) with hndef
  obtain ⟨enc, acc, h1, h2⟩ := hN n (le_max_left _ _)
  have hsum := type1_add_type2_self P n
    (fun xy => acc (enc (fun i => (xy i).1)) (fun i => (xy i).2))
  have hn : 2 / E ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right N (Nat.ceil (2 / E)))
  have hexp : -(n : ℝ) * (E - ε) ≤ -1 := by
    have h2E : 2 ≤ (n : ℝ) * E := by
      rw [div_le_iff₀ hpos] at hn; linarith
    nlinarith
  have hpow : (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  rw [Real.rpow_neg_one] at hpow
  linarith

theorem dhtOptimalExponent_self {X Y : Type*} [Fintype X] [Fintype Y] (P : ProbDist (X × Y))
    (R : ℝ) : dhtOptimalExponent P P R = 0 := by
  apply le_antisymm _ (dhtOptimalExponent_nonneg P P R)
  unfold dhtOptimalExponent
  apply Real.sSup_nonpos
  intro E hE
  exact dhtSet_le_zero_self P R E hE

/-! ### The SHA quantities are nonnegative -/

theorem shaInnerBoundRaw_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (P Q : ProbDist (X × Y)) (R : ℝ) : 0 ≤ shaInnerBoundRaw P Q R := by
  apply Real.sSup_nonneg
  intro r hr
  obtain ⟨kU, Puxy, Quxy, -, -, -, hrest⟩ := hr
  dsimp only at hrest
  obtain ⟨hrate, rfl⟩ := hrest
  have t1 : 0 ≤ sInf { d : ℝ | ∃ (Pt : ProbDist (Fin kU × X × Y)),
      Pt.map (fun t => (t.1, t.2.1)) = Puxy.map (fun t => (t.1, t.2.1)) ∧
      Pt.map (fun t => (t.1, t.2.2)) = Puxy.map (fun t => (t.1, t.2.2)) ∧
      AbsCont Pt Quxy ∧ d = klDivergence Pt Quxy } := by
    apply Real.sInf_nonneg
    rintro d ⟨Pt, -, -, hac, rfl⟩
    exact InfoTheory.Bridge.klDivergence_nonneg _ _ hac
  have t2 : 0 ≤ sInf { d : ℝ | ∃ (Pt : ProbDist (Fin kU × X × Y)),
      Pt.map (fun t => (t.1, t.2.1)) = Puxy.map (fun t => (t.1, t.2.1)) ∧
      Pt.map (fun t => t.2.2) = P.snd ∧
      condEntropy (Puxy.map (fun t => (t.1, t.2.2))) ≤
        condEntropy (Pt.map (fun t => (t.1, t.2.2))) ∧
      AbsCont Pt Quxy ∧
      d = klDivergence Pt Quxy + R - condMutualInfo (Puxy.map (fun t => (t.1, t.2.1, t.2.2))) } := by
    apply Real.sInf_nonneg
    rintro d ⟨Pt, -, -, -, hac, rfl⟩
    have := InfoTheory.Bridge.klDivergence_nonneg _ _ hac
    linarith
  split_ifs
  · exact t1
  · exact le_min t1 t2

theorem shaInnerBound_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (P Q : ProbDist (X × Y)) (R : ℝ) : 0 ≤ shaInnerBound P Q R := by
  apply Real.sSup_nonneg
  rintro E ⟨m, w, Rs, hw, -, -, -, rfl⟩
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (shaInnerBoundRaw_nonneg P Q (Rs i)))

end InfoTheory.Known.Certificates.DistributedHypothesisTestingExponent
