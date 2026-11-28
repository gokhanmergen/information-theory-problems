import InfoTheory.Problems.PrivateVsQuantumCapacityGap
import InfoTheory.Known.Certificates.QuantumCapacityDepolarizing

/-!
# Certificate for `InfoTheory.Problems.PrivateVsQuantumCapacityGap`

The frozen statement asks for a qubit channel with `quantumCapacity N = 0` and
`0 < privateCapacity N`.

## Certified (non-junk)
* `privateCapacity_bddAbove`, `privateCapacity_le : P(N) ≤ log₂ d₂ + log₂ (#Kraus)`: every
  candidate rate `(χ_B - χ_E)/n` is bounded (each ensemble average is a state,
  `avg_posSemidef`, `avg_trace`), so the `sSup` in `privateCapacity` is a genuine supremum,
  never the `sSup` of an unbounded set.
* `privateCapacity_nonneg : 0 ≤ P(N)` for every channel with `d₁ > 0` (trivial one-point
  ensemble).
* **Regression, identity channel:** `privateCapacity_idCh : P(id_d) = log₂ d` (achieved by the
  uniform computational-basis ensemble; environment is one-dimensional), in particular
  `privateCapacity_idQubit : P(id₂) = 1`.
* **Regression (no trivial witness):** `idQubit_not_witness` (`Q(id₂) = 1 ≠ 0`) and
  `quantumCapacity_resetQubit : Q(reset₂) = 0` with `0 ≤ P(reset₂)`.
* `quantumCapacity_le_one` (qubit `Q ≤ 1`) from the depolarizing certificate.

## Not certified
* `Q(N) ≤ P(N)` in general, `P = 0` for anti-degradable / entanglement-breaking channels
  (e.g. `P(reset₂) = 0`; needs nonnegativity of the Holevo quantity, i.e. concavity of
  `matEntropy`), and Smith's `P = Q` for degradable channels.

## Adversarial check (2026-11-27)
`Q = 0 < P` is known only in dimension `≥ 4` (Horodecki–Horodecki–Horodecki–Oppenheim 2005;
Leung–Li–Smith–Smolin 2014). For qubits, PPT ⇒ entanglement-breaking, and the only known
zero-capacity qubit channels are anti-degradable or entanglement-breaking, both of which have
`P = 0`; no qubit example and no impossibility proof found (searched 2015–2026 literature on
private vs quantum capacity of qubit channels). `privateCapacity` matches the regularised
Devetak–Cai–Winter–Yeung formula. OPEN and FINE; Lean not modified.
-/

open scoped BigOperators Matrix ComplexOrder

namespace InfoTheory.Known.Certificates.PrivateVsQuantumCapacityGap

open InfoTheory Matrix InfoTheory.Problems.PrivateVsQuantumCapacityGap
open InfoTheory.Known.Certificates.QuantumCapacitySingleLetter
open InfoTheory.Known.Certificates.QuantumCapacityDepolarizing (quantumCapacity_le_one log2_two)
open InfoTheory.Known.Certificates.ClassicalCapacityAdditivityThreshold
  (matEntropy_nonneg_of_state matEntropy_eq_zero_of_idem pure0)

/-! ### Ensemble averages are states -/

theorem avg_posSemidef {m D : ℕ} (P : ProbDist (Fin m)) (M : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hM : ∀ x, (M x).PosSemidef) : (∑ x, (P.pmf x : ℂ) • M x).PosSemidef :=
  posSemidef_sum _ fun x _ => (hM x).smul (by exact_mod_cast P.nonneg x)

theorem avg_trace {m D : ℕ} (P : ProbDist (Fin m)) (M : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hM : ∀ x, (M x).trace = 1) : (∑ x, (P.pmf x : ℂ) • M x).trace = 1 := by
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, hM, smul_eq_mul, mul_one]
  exact_mod_cast P.sum_one

theorem weighted_sum_nonneg {m : ℕ} (P : ProbDist (Fin m)) (f : Fin m → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∑ x, P.pmf x * f x :=
  Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg x) (hf x)

theorem weighted_sum_le {m : ℕ} (P : ProbDist (Fin m)) (f : Fin m → ℝ) (c : ℝ)
    (hf : ∀ x, f x ≤ c) : ∑ x, P.pmf x * f x ≤ c := by
  calc ∑ x, P.pmf x * f x ≤ ∑ x, P.pmf x * c :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (P.nonneg x)
    _ = c := by rw [← Finset.sum_mul, P.sum_one, one_mul]

/-! ### `privateCapacity` is a bounded supremum -/

theorem private_rate_le {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (n m : ℕ) (hn : 0 < n)
    (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)) :
    let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
    let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
    let chiB := matEntropy avgB - ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
    let chiE := matEntropy avgE -
      ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
    (chiB - chiE) / (n : ℝ) ≤ log2 d₂ + log2 N.numKraus := by
  intro avgB avgE chiB chiE
  have hBs : ∀ x, (channelPowerApply N n (σ x).mat).PosSemidef := fun x =>
    channelPowerApply_posSemidef N n (σ x).posSemidef
  have hBt : ∀ x, (channelPowerApply N n (σ x).mat).trace = 1 := fun x => by
    rw [channelPowerApply_trace, (σ x).trace_one]
  have hEs : ∀ x, (channelPowerCompApply N n (σ x).mat).PosSemidef := fun x =>
    channelPowerCompApply_posSemidef N n (σ x).posSemidef
  have hEt : ∀ x, (channelPowerCompApply N n (σ x).mat).trace = 1 := fun x => by
    rw [channelPowerCompApply_trace, (σ x).trace_one]
  have h1 : matEntropy avgB ≤ n * log2 d₂ := by
    have := matEntropy_le_log2_of_state (avg_posSemidef P _ hBs) (avg_trace P _ hBt)
    rwa [log2_pow] at this
  have h2 : 0 ≤ ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat) :=
    weighted_sum_nonneg P _ fun x => matEntropy_nonneg_of_state (hBs x) (hBt x)
  have h3 : 0 ≤ matEntropy avgE :=
    matEntropy_nonneg_of_state (avg_posSemidef P _ hEs) (avg_trace P _ hEt)
  have h4 : ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat) ≤
      n * log2 N.numKraus :=
    weighted_sum_le P _ _ fun x => by
      have := matEntropy_le_log2_of_state (hEs x) (hEt x)
      rwa [log2_pow] at this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  show matEntropy avgB - _ - (matEntropy avgE - _) ≤ _
  nlinarith

theorem privateCapacity_bddAbove {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    BddAbove { r : ℝ | ∃ (n m : ℕ) (P : ProbDist (Fin m)) (σ : Fin m → DensityMatrix (d₁ ^ n)),
      0 < n ∧
      let avgB := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerApply N n (σ x).mat
      let avgE := ∑ x : Fin m, (P.pmf x : ℂ) • channelPowerCompApply N n (σ x).mat
      let chiB := matEntropy avgB -
        ∑ x : Fin m, P.pmf x * matEntropy (channelPowerApply N n (σ x).mat)
      let chiE := matEntropy avgE -
        ∑ x : Fin m, P.pmf x * matEntropy (channelPowerCompApply N n (σ x).mat)
      r = (chiB - chiE) / (n : ℝ) } := by
  refine ⟨log2 d₂ + log2 N.numKraus, ?_⟩
  rintro r ⟨n, m, P, σ, hn, rfl⟩
  exact private_rate_le N n m hn P σ

/-- `P(N) ≤ log₂ d₂ + log₂ (#Kraus)`: the `sSup` defining `privateCapacity` is bounded. -/
theorem privateCapacity_le {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) :
    privateCapacity N ≤ log2 d₂ + log2 N.numKraus := by
  unfold privateCapacity
  refine Real.sSup_le ?_ (add_nonneg (log2_natCast_nonneg _) (log2_natCast_nonneg _))
  rintro r ⟨n, m, P, σ, hn, rfl⟩
  exact private_rate_le N n m hn P σ

/-- The point-mass distribution on `Fin 1`. -/
def pointDist : ProbDist (Fin 1) := ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩

/-- `P(N) ≥ 0` for every channel with nonzero input dimension. -/
theorem privateCapacity_nonneg {d₁ d₂ : ℕ} (N : QuantumChannel d₁ d₂) (hd : 0 < d₁) :
    0 ≤ privateCapacity N := by
  unfold privateCapacity
  refine le_csSup (privateCapacity_bddAbove N)
    ⟨1, 1, pointDist, fun _ => pure0 (d₁ ^ 1) (pow_pos hd 1), one_pos, ?_⟩
  simp [pointDist]

/-! ### Regression: `P(id_d) = log₂ d` -/

theorem braE_mul_conj {D : ℕ} (x : Fin D) : braE x * (braE x)ᴴ = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [braE, Matrix.mul_apply, conjTranspose_apply]

/-- The computational basis state `|x⟩⟨x|`. -/
def basisState (D : ℕ) (x : Fin D) : DensityMatrix D where
  mat := (braE x)ᴴ * braE x
  posSemidef := posSemidef_conjTranspose_mul_self _
  trace_one := by rw [Matrix.trace_mul_comm, braE_mul_conj]; simp

theorem matEntropy_basisState (D : ℕ) (x : Fin D) : matEntropy (basisState D x).mat = 0 := by
  apply matEntropy_eq_zero_of_idem (basisState D x).posSemidef.1
  show (braE x)ᴴ * braE x * ((braE x)ᴴ * braE x) = (braE x)ᴴ * braE x
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (braE x), braE_mul_conj, Matrix.one_mul]

/-- The uniform distribution on `Fin D`. -/
noncomputable def unifDist (D : ℕ) (hD : 0 < D) : ProbDist (Fin D) :=
  ⟨fun _ => 1 / (D : ℝ), fun _ => by positivity, by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp⟩

theorem privateCapacity_idCh (d : ℕ) (hd : 0 < d) : privateCapacity (idCh d) = log2 d := by
  refine le_antisymm ?_ ?_
  · have h := privateCapacity_le (idCh d)
    have h1 : log2 (((idCh d).numKraus : ℕ) : ℝ) = 0 := by
      show log2 ((1 : ℕ) : ℝ) = 0
      simp [log2]
    linarith
  · have hD : 0 < d ^ 1 := pow_pos hd 1
    have hB : (∑ x : Fin (d ^ 1), ((unifDist (d ^ 1) hD).pmf x : ℂ) •
        channelPowerApply (idCh d) 1 (basisState (d ^ 1) x).mat) = (maxMixed (d ^ 1) hD).mat := by
      simp_rw [channelPowerApply_idCh]
      show ∑ x : Fin (d ^ 1), (((1 / ((d ^ 1 : ℕ) : ℝ) : ℝ)) : ℂ) • ((braE x)ᴴ * braE x) =
        (((1 / ((d ^ 1 : ℕ) : ℝ) : ℝ)) : ℂ) • 1
      rw [← Finset.smul_sum, sum_braE]
    have hE : (∑ x : Fin (d ^ 1), ((unifDist (d ^ 1) hD).pmf x : ℂ) •
        channelPowerCompApply (idCh d) 1 (basisState (d ^ 1) x).mat) =
        Matrix.of fun _ _ => 1 := by
      simp_rw [channelPowerCompApply_idCh]
      rw [← Finset.sum_smul]
      have : (∑ x : Fin (d ^ 1), ((unifDist (d ^ 1) hD).pmf x : ℂ)) = 1 := by
        exact_mod_cast (unifDist (d ^ 1) hD).sum_one
      rw [this, one_smul]
    unfold privateCapacity
    refine le_csSup_of_le (privateCapacity_bddAbove (idCh d))
      ⟨1, d ^ 1, unifDist (d ^ 1) hD, basisState (d ^ 1), one_pos, rfl⟩ ?_
    show _ ≤ (_ - _) / _
    rw [hB, hE, matEntropy_maxMixed]
    simp_rw [channelPowerApply_idCh, channelPowerCompApply_idCh, matEntropy_basisState]
    have h0 := matEntropy_ones_one 1
    rw [log2_pow]
    simp only [mul_zero, Finset.sum_const_zero, sub_zero, Nat.cast_one, div_one, one_mul]
    rw [show matEntropy (Matrix.of fun (_ : Fin ((idCh d).numKraus ^ 1))
      (_ : Fin ((idCh d).numKraus ^ 1)) => (1 : ℂ)) = 0 from h0]
    simp

theorem privateCapacity_idQubit : privateCapacity (idCh 2) = 1 := by
  rw [privateCapacity_idCh 2 two_pos, log2_two]

/-- **Regression:** the noiseless qubit is not a witness (`Q = 1`, `P = 1`). -/
theorem idQubit_not_witness :
    ¬ (quantumCapacity (idCh 2) = 0 ∧ 0 < privateCapacity (idCh 2)) := by
  rw [quantumCapacity_idQubit]
  exact fun h => one_ne_zero h.1

/-- **Regression:** the reset channel has `Q = 0` and `P ≥ 0`. -/
theorem resetQubit_capacities :
    quantumCapacity (resetCh 2 two_pos) = 0 ∧ 0 ≤ privateCapacity (resetCh 2 two_pos) :=
  ⟨quantumCapacity_resetQubit, privateCapacity_nonneg _ two_pos⟩

end InfoTheory.Known.Certificates.PrivateVsQuantumCapacityGap
