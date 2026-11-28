import InfoTheory.Core.GaussianOperational
import InfoTheory.Known.GaussianChannel
import InfoTheory.Known.GaussianAchievability
import InfoTheory.Known.CostConstrainedCoding
import Mathlib.Analysis.Convex.Basic

/-!
# Operational Capacity Region of the Two-User Gaussian MAC & Gaussian Broadcast Achievability

Formalizes two foundational multi-user Gaussian network information theory theorems with
zero modeling loopholes (measurable decoders, deterministic per-codeword power constraints,
`ℝ≥0∞`-valued error probabilities under i.i.d. Gaussian noise):

1. **Two-User Scalar Gaussian Multiple-Access Channel (MAC)** `Y = X₁ + X₂ + Z`, `Z ~ N(0, N)`
   (Cover & Thomas Theorem 15.1.1 / §15.3.6; El Gamal & Kim Theorem 4.6):
   - Operational definitions: `GaussianMACCode`, `GaussianMACCode.SatisfiesPower`,
     `gaussianMACErrorProb`, `gaussianMACAvgError`, `IsGaussianMACAchievable`,
     `gaussianMACCapacityRegion`, and the textbook pentagon `gaussianMACPentagon`.
   - **Exact Converse** (`gaussianMACCapacityRegion_subset_pentagon`):
     - Individual rate bounds `R₁ ≤ ½ log₂(1 + P₁/N)` and `R₂ ≤ ½ log₂(1 + P₂/N)` by conditioning
       on the best message of the other user and reducing to single-user `AwgnCode`.
     - Sum-rate bound `R₁ + R₂ ≤ ½ log₂(1 + (P₁ + P₂)/N)` via empirical mean-centering of both
       encoders (which preserves error probability identically, eliminates cross-user correlation
       `⟨∑ x₁', ∑ x₂'⟩ = 0`, and bounds average composite power by `n(P₁ + P₂)`), combined with
       the average-power Gaussian likelihood-ratio converse (`awgn_code_converse_avgPower`).
   - **Exact Achievability** (`pentagon_subset_gaussianMACCapacityRegion`):
     - Corner-point achievability (`gaussianMAC_corner_achievable`) via quantized Successive
       Interference Cancellation (SIC): random independent discretized-Gaussian codebooks,
       Donsker–Varadhan variational lower bound on the quantized interference channel
       `I(X₁; Y) → ½ log₂(1 + v₁ / (v₂ + N))` (using weighted Cauchy–Schwarz domination),
       exact subtraction `Y - X₁(m̂₁) = X₂ + Z` in Stage 2, and product-codebook expurgation
       enforcing per-codeword power constraints for both users simultaneously.
     - Time-sharing convexity of `gaussianMACCapacityRegion` via code concatenation + cyclic-shift
       zero-loss subcode extraction (`gaussianMACCapacityRegion_convex`).
     - Combining the five vertices of the pentagon via convexity yields
       `gaussianMACCapacityRegion_eq : gaussianMACCapacityRegion P₁ P₂ N = gaussianMACPentagon P₁ P₂ N`.

2. **Scalar Gaussian Broadcast Channel (BC) Superposition Coding Achievability**
   `Y₁ = X + Z₁`, `Y₂ = X + Z₂`, `0 < N₁ ≤ N₂` (Cover & Thomas §15.1.3 / Theorem 15.6.2;
   El Gamal & Kim Theorem 5.3):
   - Operational definitions: `GaussianBCCode`, `GaussianBCCode.SatisfiesPower`,
     `gaussianBCErrorProb₁`, `gaussianBCErrorProb₂`, `gaussianBCAvgError₁`, `gaussianBCAvgError₂`,
     `IsGaussianBCAchievable`.
   - **Superposition Coding Achievability** (`gaussianBC_superposition_achievable`): for every
     power split `α ∈ [0, 1]` and every `(R₁, R₂)` with `0 ≤ R₁ < ½ log₂(1 + α P / N₁)` and
     `0 ≤ R₂ < ½ log₂(1 + (1 - α) P / (α P + N₂))`, `(R₁, R₂)` is operationally achievable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace InfoTheory.Known

open InfoTheory InfoTheory.Bridge
open InfoTheory.Known.GaussianChannel
open InfoTheory.Known.GaussianAchievability
open InfoTheory.Known.CostConstrainedCoding

/-! ### 1. Operational Definitions for the Two-User Scalar Gaussian MAC -/

section GaussianMACDefs

/-- An `(n, M₁, M₂)` block code for the two-user scalar Gaussian MAC `Y = X₁ + X₂ + Z`:
    two deterministic encoders `Fin M₁ → Fin n → ℝ`, `Fin M₂ → Fin n → ℝ`, and a
    **measurable** joint decoder `(Fin n → ℝ) → Fin M₁ × Fin M₂`. -/
structure GaussianMACCode (n M₁ M₂ : ℕ) where
  encoder₁ : Fin M₁ → Fin n → ℝ
  encoder₂ : Fin M₂ → Fin n → ℝ
  decoder : (Fin n → ℝ) → Fin M₁ × Fin M₂
  measurable_decoder : Measurable decoder

/-- Deterministic per-codeword power constraints `∑ᵢ x₁(m₁)ᵢ² ≤ n P₁` and `∑ᵢ x₂(m₂)ᵢ² ≤ n P₂`
    for every message `m₁` and `m₂`. -/
def GaussianMACCode.SatisfiesPower {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂)
    (P₁ P₂ : ℝ) : Prop :=
  (∀ m₁ : Fin M₁, ∑ i : Fin n, (C.encoder₁ m₁ i) ^ 2 ≤ (n : ℝ) * P₁) ∧
  (∀ m₂ : Fin M₂, ∑ i : Fin n, (C.encoder₂ m₂ i) ^ 2 ≤ (n : ℝ) * P₂)

/-- Conditional error probability `λ_{m₁, m₂} = P_Z {z | ĝ(x₁(m₁) + x₂(m₂) + z) ≠ (m₁, m₂)}`
    under i.i.d. `N(0, N)` noise, valued in `ℝ≥0∞`. -/
noncomputable def gaussianMACErrorProb {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂)
    (N : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ≥0∞ :=
  awgnNoise n N {z | C.decoder (C.encoder₁ m₁ + C.encoder₂ m₂ + z) ≠ (m₁, m₂)}

/-- Average error probability `P_e^{(n)} = (M₁ M₂)⁻¹ ∑_{m₁, m₂} λ_{m₁, m₂}`. -/
noncomputable def gaussianMACAvgError {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂)
    (N : ℝ) : ℝ≥0∞ :=
  ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ *
    ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, gaussianMACErrorProb C N m₁ m₂

/-- Operational achievability of rate pair `(R₁, R₂)` (bits per channel use) over the
    two-user Gaussian MAC with powers `(P₁, P₂)` and noise variance `N`. -/
def IsGaussianMACAchievable (P₁ P₂ N R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : GaussianMACCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊)
                            (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊),
      C.SatisfiesPower P₁ P₂ ∧ gaussianMACAvgError C N ≤ ENNReal.ofReal δ

/-- Operational capacity region (closure of achievable rate pairs) of the two-user Gaussian MAC. -/
def gaussianMACCapacityRegion (P₁ P₂ N : ℝ) : Set (ℝ × ℝ) :=
  closure { r : ℝ × ℝ | IsGaussianMACAchievable P₁ P₂ N r.1 r.2 }

/-- Textbook capacity pentagon of the two-user Gaussian MAC (Cover & Thomas Thm. 15.1.1):
    `0 ≤ R₁ ≤ ½ log₂(1 + P₁/N)`, `0 ≤ R₂ ≤ ½ log₂(1 + P₂/N)`,
    `R₁ + R₂ ≤ ½ log₂(1 + (P₁ + P₂)/N)`. -/
def gaussianMACPentagon (P₁ P₂ N : ℝ) : Set (ℝ × ℝ) :=
  { r : ℝ × ℝ |
    0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    r.1 ≤ awgnCapacityFormula P₁ N ∧
    r.2 ≤ awgnCapacityFormula P₂ N ∧
    r.1 + r.2 ≤ awgnCapacityFormula (P₁ + P₂) N }

private lemma gaussianMACErrorProb_le_one {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂)
    (N : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) :
    gaussianMACErrorProb C N m₁ m₂ ≤ 1 :=
  prob_le_one

private lemma gaussianMACAvgError_ne_top {n M₁ M₂ : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (C : GaussianMACCode n M₁ M₂) (N : ℝ) :
    gaussianMACAvgError C N ≠ ⊤ := by
  unfold gaussianMACAvgError
  have hM : M₁ * M₂ ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hM)) ?_
  refine ENNReal.sum_ne_top.2 fun m₁ _ => ENNReal.sum_ne_top.2 fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C N m₁ m₂)

private lemma gaussianMACAvgError_toReal {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂) (N : ℝ) :
    (gaussianMACAvgError C N).toReal =
      (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C N m₁ m₂).toReal := by
  unfold gaussianMACAvgError
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  congr 1
  rw [ENNReal.toReal_sum (fun m₁ _ => ENNReal.sum_ne_top.2 fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C N m₁ m₂))]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  exact ENNReal.toReal_sum (fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C N m₁ m₂))

/-- Swapping the two users preserves a `GaussianMACCode`, its power constraint, and its error. -/
private def GaussianMACCode.swap {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂) :
    GaussianMACCode n M₂ M₁ where
  encoder₁ := C.encoder₂
  encoder₂ := C.encoder₁
  decoder y := (C.decoder y).swap
  measurable_decoder := measurable_swap.comp C.measurable_decoder

private lemma GaussianMACCode.swap_satisfiesPower {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂)
    {P₁ P₂ : ℝ} (h : C.SatisfiesPower P₁ P₂) : C.swap.SatisfiesPower P₂ P₁ :=
  ⟨h.2, h.1⟩

private lemma gaussianMACErrorProb_swap {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂)
    (N : ℝ) (m₂ : Fin M₂) (m₁ : Fin M₁) :
    gaussianMACErrorProb C.swap N m₂ m₁ = gaussianMACErrorProb C N m₁ m₂ := by
  unfold gaussianMACErrorProb GaussianMACCode.swap
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, add_comm (C.encoder₂ m₂) (C.encoder₁ m₁), ne_eq]
  constructor <;> intro h heq <;> apply h
  · rw [heq]; rfl
  · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)

private lemma gaussianMACAvgError_swap {n M₁ M₂ : ℕ} (C : GaussianMACCode n M₁ M₂) (N : ℝ) :
    gaussianMACAvgError C.swap N = gaussianMACAvgError C N := by
  unfold gaussianMACAvgError
  rw [Nat.mul_comm M₂ M₁]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
    gaussianMACErrorProb_swap C N m₂ m₁

private lemma isGaussianMACAchievable_swap {P₁ P₂ N R₁ R₂ : ℝ}
    (h : IsGaussianMACAchievable P₁ P₂ N R₁ R₂) :
    IsGaussianMACAchievable P₂ P₁ N R₂ R₁ := by
  refine ⟨h.2.1, h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨C, hpow, herr⟩ := hn₀ n hn
  exact ⟨C.swap, C.swap_satisfiesPower hpow, by rwa [gaussianMACAvgError_swap]⟩

end GaussianMACDefs

/-! ### 2. Exact Operational Converse for the Two-User Gaussian MAC -/

section GaussianMACConverse

/-- **Average-power finite-blocklength AWGN converse**: every `(n, M)` code (`M ≥ 1`) whose
    average codeword energy satisfies `∑_m ∑_i x(m)_i² ≤ M n P` obeys
    `(1 - P_e) ln M ≤ n · ½ ln(1 + P/N) + 1`. -/
theorem awgn_code_converse_avgPower {n M : ℕ} {N P : ℝ} (hN : 0 < N) (hP : 0 ≤ P) (hM : 1 ≤ M)
    (C : AwgnCode n M)
    (havgPow : ∑ m : Fin M, ∑ i : Fin n, (C.encoder m i) ^ 2 ≤ (M : ℝ) * (n : ℝ) * P) :
    (1 - (awgnAvgErrorProb C N).toReal) * Real.log M ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P / N)) + 1 := by
  have hS : 0 < P + N := by linarith
  set Q := awgnRefLaw n (P + N) with hQ
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmsg : ∀ m : Fin M, (1 - (awgnErrorProb C N m).toReal) * Real.log M -
      ((M : ℝ) - 1) * Q.real (C.decoder ⁻¹' {m}) ≤
      ∫ y, awgnBlockLLR N (P + N) (C.encoder m) y ∂awgnBlockLaw n N (C.encoder m) := by
    intro m
    have hA := measurableSet_decoder_preimage C m
    have h1 := awgn_message_bound hN hS (C.encoder m) hA hMr
    have h3 : (awgnBlockLaw n N (C.encoder m)).real (C.decoder ⁻¹' {m}) =
        1 - (awgnErrorProb C N m).toReal := by
      have h := awgnErrorProb_add_success C N m
      have hne : awgnErrorProb C N m ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (awgnErrorProb_le_one C N m)
      rw [measureReal_def]
      have h' := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add hne (measure_ne_top _ _), ENNReal.toReal_one] at h'
      linarith
    rwa [h3] at h1
  have hsumQ : ∑ m : Fin M, Q.real (C.decoder ⁻¹' {m}) = 1 := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), sum_measure_decoder_preimage C Q,
      ENNReal.toReal_one]
  have hsumRHS : ∑ m : Fin M,
      ∫ y, awgnBlockLLR N (P + N) (C.encoder m) y ∂awgnBlockLaw n N (C.encoder m) ≤
      (M : ℝ) * ((n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P / N))) := by
    have hterm : ∀ m : Fin M,
        ∫ y, awgnBlockLLR N (P + N) (C.encoder m) y ∂awgnBlockLaw n N (C.encoder m) =
          (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + P / N) - 1 / 2) +
            ((∑ i : Fin n, (C.encoder m i) ^ 2) + (n : ℝ) * N) / (2 * (P + N)) := by
      intro m
      rw [integral_awgnBlockLLR hN hS, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hlog : Real.log ((P + N) / N) = Real.log (1 + P / N) := by
        congr 1; field_simp; ring
      rw [hlog]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hdiv : ((∑ m : Fin M, ∑ i : Fin n, (C.encoder m i) ^ 2) + (M : ℝ) * ((n : ℝ) * N)) /
        (2 * (P + N)) ≤ (M : ℝ) * (n : ℝ) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hsum := le_trans (Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) => hmsg m)) hsumRHS
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumQ, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  rw [awgnAvgErrorProb_toReal]
  set E := ∑ m : Fin M, (awgnErrorProb C N m).toReal
  have hMpos : (0 : ℝ) < M := by linarith
  have hrw : (1 - 1 / (M : ℝ) * E) * Real.log M = ((M - E) * Real.log M) / M := by
    field_simp
  rw [hrw, div_le_iff₀ hMpos]
  nlinarith

/-- Finite-blocklength sum-rate converse for any two-user Gaussian MAC code via empirical
    mean-centering. -/
theorem gaussianMAC_sum_converse_code {n M₁ M₂ : ℕ} {N P₁ P₂ : ℝ}
    (hN : 0 < N) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (C : GaussianMACCode n M₁ M₂) (hpow : C.SatisfiesPower P₁ P₂) :
    (1 - (gaussianMACAvgError C N).toReal) * (Real.log M₁ + Real.log M₂) ≤
      (n : ℝ) * ((1 / 2 : ℝ) * Real.log (1 + (P₁ + P₂) / N)) + 1 := by
  have hM₁pos : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂pos : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  -- Empirical means of the two codebooks
  let μ₁ : Fin n → ℝ := fun i => (1 / (M₁ : ℝ)) * ∑ m₁ : Fin M₁, C.encoder₁ m₁ i
  let μ₂ : Fin n → ℝ := fun i => (1 / (M₂ : ℝ)) * ∑ m₂ : Fin M₂, C.encoder₂ m₂ i
  let x₁' : Fin M₁ → Fin n → ℝ := fun m₁ i => C.encoder₁ m₁ i - μ₁ i
  let x₂' : Fin M₂ → Fin n → ℝ := fun m₂ i => C.encoder₂ m₂ i - μ₂ i
  let e : Fin (M₁ * M₂) ≃ Fin M₁ × Fin M₂ := finProdFinEquiv.symm
  -- Centered composite single-user AWGN code of size `M₁ * M₂`
  let Csum : AwgnCode n (M₁ * M₂) :=
    { encoder := fun k i => x₁' (e k).1 i + x₂' (e k).2 i
      decoder := fun y => e.symm (C.decoder (y + μ₁ + μ₂))
      measurable_decoder := (measurable_of_finite e.symm).comp
        (C.measurable_decoder.comp ((measurable_id.add measurable_const).add measurable_const)) }
  -- Step 1: exact preservation of error probability under mean-centering
  have herr_eq : awgnAvgErrorProb Csum N = gaussianMACAvgError C N := by
    unfold awgnAvgErrorProb gaussianMACAvgError
    congr 1
    rw [Fintype.sum_equiv e _ (fun p => gaussianMACErrorProb C N p.1 p.2), Fintype.sum_prod_type]
    intro k
    unfold awgnErrorProb gaussianMACErrorProb
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, Csum, ne_eq]
    have hshift : (fun i => x₁' (e k).1 i + x₂' (e k).2 i) + z + μ₁ + μ₂ =
        C.encoder₁ (e k).1 + C.encoder₂ (e k).2 + z := by
      ext i
      simp only [Pi.add_apply, x₁', x₂']
      ring
    rw [hshift]
    constructor <;> intro h heq <;> apply h
    · rw [heq]; exact e.symm_apply_apply k
    · exact (e.symm_apply_eq.mp heq)
  -- Step 2: zero means and variance reduction
  have hmean₁ : ∀ i : Fin n, ∑ m₁ : Fin M₁, x₁' m₁ i = 0 := by
    intro i
    simp only [x₁', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, μ₁]
    field_simp [hM₁pos.ne']
    ring
  have hmean₂ : ∀ i : Fin n, ∑ m₂ : Fin M₂, x₂' m₂ i = 0 := by
    intro i
    simp only [x₂', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, μ₂]
    field_simp [hM₂pos.ne']
    ring
  have hvar₁ : ∀ i : Fin n, ∑ m₁ : Fin M₁, (x₁' m₁ i) ^ 2 ≤ ∑ m₁ : Fin M₁, (C.encoder₁ m₁ i) ^ 2 := by
    intro i
    have hexp : ∑ m₁ : Fin M₁, (x₁' m₁ i) ^ 2 =
        (∑ m₁ : Fin M₁, (C.encoder₁ m₁ i) ^ 2) - (M₁ : ℝ) * (μ₁ i) ^ 2 := by
      have hsq : ∀ m₁ : Fin M₁, (x₁' m₁ i) ^ 2 =
          (C.encoder₁ m₁ i) ^ 2 - 2 * μ₁ i * C.encoder₁ m₁ i + (μ₁ i) ^ 2 := fun m₁ => by
        dsimp only [x₁']; ring
      simp_rw [hsq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsum₁ : ∑ m₁ : Fin M₁, C.encoder₁ m₁ i = (M₁ : ℝ) * μ₁ i := by
        dsimp only [μ₁]; field_simp [hM₁pos.ne']
      rw [hsum₁]
      ring
    rw [hexp]
    have hnn : 0 ≤ (M₁ : ℝ) * (μ₁ i) ^ 2 := by positivity
    linarith
  have hvar₂ : ∀ i : Fin n, ∑ m₂ : Fin M₂, (x₂' m₂ i) ^ 2 ≤ ∑ m₂ : Fin M₂, (C.encoder₂ m₂ i) ^ 2 := by
    intro i
    have hexp : ∑ m₂ : Fin M₂, (x₂' m₂ i) ^ 2 =
        (∑ m₂ : Fin M₂, (C.encoder₂ m₂ i) ^ 2) - (M₂ : ℝ) * (μ₂ i) ^ 2 := by
      have hsq : ∀ m₂ : Fin M₂, (x₂' m₂ i) ^ 2 =
          (C.encoder₂ m₂ i) ^ 2 - 2 * μ₂ i * C.encoder₂ m₂ i + (μ₂ i) ^ 2 := fun m₂ => by
        dsimp only [x₂']; ring
      simp_rw [hsq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsum₂ : ∑ m₂ : Fin M₂, C.encoder₂ m₂ i = (M₂ : ℝ) * μ₂ i := by
        dsimp only [μ₂]; field_simp [hM₂pos.ne']
      rw [hsum₂]
      ring
    rw [hexp]
    have hnn : 0 ≤ (M₂ : ℝ) * (μ₂ i) ^ 2 := by positivity
    linarith
  -- Step 3: composite average power `≤ (M₁ * M₂) * n * (P₁ + P₂)`
  have havgPow : ∑ k : Fin (M₁ * M₂), ∑ i : Fin n, (Csum.encoder k i) ^ 2 ≤
      ((M₁ * M₂ : ℕ) : ℝ) * (n : ℝ) * (P₁ + P₂) := by
    have hrew : ∑ k : Fin (M₁ * M₂), ∑ i : Fin n, (Csum.encoder k i) ^ 2 =
        ∑ i : Fin n, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (x₁' m₁ i + x₂' m₂ i) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_equiv e _ (fun p => (x₁' p.1 i + x₂' p.2 i) ^ 2) (fun _ => rfl),
        Fintype.sum_prod_type]
    rw [hrew]
    have hcoord : ∀ i : Fin n,
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (x₁' m₁ i + x₂' m₂ i) ^ 2 ≤
          (M₂ : ℝ) * (∑ m₁ : Fin M₁, (C.encoder₁ m₁ i) ^ 2) +
          (M₁ : ℝ) * (∑ m₂ : Fin M₂, (C.encoder₂ m₂ i) ^ 2) := by
      intro i
      have hexp : ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (x₁' m₁ i + x₂' m₂ i) ^ 2 =
          (M₂ : ℝ) * (∑ m₁ : Fin M₁, (x₁' m₁ i) ^ 2) +
          (M₁ : ℝ) * (∑ m₂ : Fin M₂, (x₂' m₂ i) ^ 2) := by
        have hsq : ∀ m₁ m₂, (x₁' m₁ i + x₂' m₂ i) ^ 2 =
            (x₁' m₁ i) ^ 2 + (x₂' m₂ i) ^ 2 + 2 * x₁' m₁ i * x₂' m₂ i := fun _ _ => by ring
        simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum, hmean₂ i, mul_zero, Finset.sum_const_zero, add_zero]
      rw [hexp]
      nlinarith [hvar₁ i, hvar₂ i]
    have hsum_coord := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcoord i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_coord
    have hp1 : ∑ i : Fin n, ∑ m₁ : Fin M₁, (C.encoder₁ m₁ i) ^ 2 ≤ (M₁ : ℝ) * ((n : ℝ) * P₁) := by
      rw [Finset.sum_comm]
      calc ∑ m₁ : Fin M₁, ∑ i : Fin n, (C.encoder₁ m₁ i) ^ 2
          ≤ ∑ _m₁ : Fin M₁, (n : ℝ) * P₁ := Finset.sum_le_sum fun m₁ _ => hpow.1 m₁
        _ = (M₁ : ℝ) * ((n : ℝ) * P₁) := by simp
    have hp2 : ∑ i : Fin n, ∑ m₂ : Fin M₂, (C.encoder₂ m₂ i) ^ 2 ≤ (M₂ : ℝ) * ((n : ℝ) * P₂) := by
      rw [Finset.sum_comm]
      calc ∑ m₂ : Fin M₂, ∑ i : Fin n, (C.encoder₂ m₂ i) ^ 2
          ≤ ∑ _m₂ : Fin M₂, (n : ℝ) * P₂ := Finset.sum_le_sum fun m₂ _ => hpow.2 m₂
        _ = (M₂ : ℝ) * ((n : ℝ) * P₂) := by simp
    push_cast
    nlinarith
  -- Step 4: apply the average-power single-user AWGN converse
  have hM12 : 1 ≤ M₁ * M₂ := Nat.mul_pos hM₁ hM₂
  have hconv := awgn_code_converse_avgPower hN (by linarith) hM12 Csum havgPow
  rw [herr_eq, Nat.cast_mul, Real.log_mul hM₁pos.ne' hM₂pos.ne'] at hconv
  exact hconv

/-- Every operationally achievable Gaussian MAC rate pair satisfies `R₁` is single-user AWGN
    achievable with power `P₁`. -/
private lemma isAwgnAchievable_fst_of_mac {P₁ P₂ N R₁ R₂ : ℝ}
    (h : IsGaussianMACAchievable P₁ P₂ N R₁ R₂) :
    IsAwgnAchievable P₁ N R₁ := by
  refine ⟨h.1, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  set M₁ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊
  set M₂ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊
  obtain ⟨C, hpow, herr⟩ := hn₀ n hn
  have hM₁ : 1 ≤ M₁ := le_max_left _ _
  have hM₂ : 1 ≤ M₂ := le_max_left _ _
  -- For each fixed `m₂`, shift the decoder by `C.encoder₂ m₂` to obtain a single-user AWGN code
  let C₁ : Fin M₂ → AwgnCode n M₁ := fun m₂ =>
    { encoder := C.encoder₁
      decoder := fun y => (C.decoder (y + C.encoder₂ m₂)).1
      measurable_decoder := measurable_fst.comp
        (C.measurable_decoder.comp (measurable_id.add measurable_const)) }
  have herr_le : ∀ m₁ m₂, awgnErrorProb (C₁ m₂) N m₁ ≤ gaussianMACErrorProb C N m₁ m₂ := by
    intro m₁ m₂
    refine measure_mono fun z hz => ?_
    simp only [Set.mem_ofPred_eq, C₁, ne_eq] at hz ⊢
    intro heq
    apply hz
    have hadd : C.encoder₁ m₁ + z + C.encoder₂ m₂ = C.encoder₁ m₁ + C.encoder₂ m₂ + z := by
      ext i; simp [add_assoc, add_comm]
    rw [hadd, heq]
  have havg_le : (1 / (M₂ : ℝ)) * ∑ m₂ : Fin M₂, (awgnAvgErrorProb (C₁ m₂) N).toReal ≤ δ := by
    have hδ_real : (gaussianMACAvgError C N).toReal ≤ δ :=
      ENNReal.toReal_le_of_le_ofReal hδ.le herr
    refine le_trans ?_ hδ_real
    rw [gaussianMACAvgError_toReal]
    simp_rw [awgnAvgErrorProb_toReal]
    rw [← Finset.mul_sum, ← mul_assoc, Finset.sum_comm]
    have hcoef : (1 / (M₂ : ℝ)) * (1 / (M₁ : ℝ)) = 1 / ((M₁ * M₂ : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [hcoef]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
      ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C N m₁ m₂))
        (herr_le m₁ m₂)) (by positivity)
  have hM₂pos : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hex : ∃ m₂ : Fin M₂, (awgnAvgErrorProb (C₁ m₂) N).toReal ≤ δ := by
    by_contra hall
    push Not at hall
    have hsum : (M₂ : ℝ) * δ < ∑ m₂ : Fin M₂, (awgnAvgErrorProb (C₁ m₂) N).toReal := by
      have : (M₂ : ℝ) * δ = ∑ _m₂ : Fin M₂, δ := by simp
      rw [this]
      exact Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM₂⟩⟩)
        fun m₂ _ => hall m₂
    rw [one_div, inv_mul_le_iff₀ hM₂pos] at havg_le
    linarith
  obtain ⟨m₂, hm₂⟩ := hex
  refine ⟨C₁ m₂, hpow.1, ?_⟩
  rw [ENNReal.le_ofReal_iff_toReal_le (awgnAvgErrorProb_ne_top hM₁ _ N) hδ.le]
  exact hm₂

/-- Every operationally achievable rate pair lies in `gaussianMACPentagon P₁ P₂ N`. -/
theorem isGaussianMACAchievable_mem_pentagon {P₁ P₂ N R₁ R₂ : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N)
    (h : IsGaussianMACAchievable P₁ P₂ N R₁ R₂) :
    (R₁, R₂) ∈ gaussianMACPentagon P₁ P₂ N := by
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · exact isAwgnAchievable_le hN hP₁ (isAwgnAchievable_fst_of_mac h)
  · exact isAwgnAchievable_le hN hP₂ (isAwgnAchievable_fst_of_mac (isGaussianMACAchievable_swap h))
  · -- Sum-rate asymptotic converse from `gaussianMAC_sum_converse_code`
    set K := (1 / 2 : ℝ) * Real.log (1 + (P₁ + P₂) / N) with hK
    have hK0 : 0 ≤ K := by
      have : 1 ≤ 1 + (P₁ + P₂) / N := by have := div_nonneg (by linarith : 0 ≤ P₁ + P₂) hN.le; linarith
      have := Real.log_nonneg this
      positivity
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have step1 : ∀ δ : ℝ, 0 < δ → δ < 1 → (1 - δ) * (R₁ + R₂) * Real.log 2 ≤ K := by
      intro δ hδ hδ1
      obtain ⟨n₀, hn₀⟩ := h.2.2 δ hδ
      have hev : ∀ᶠ n : ℕ in atTop,
          (1 - δ) * (R₁ + R₂) * Real.log 2 ≤
            K + (1 + 2 * (1 - δ) * Real.log 2) * (1 / (n : ℝ)) := by
        refine eventually_atTop.2 ⟨max n₀ 1, fun n hn => ?_⟩
        obtain ⟨C, hpow, herr⟩ := hn₀ n (le_trans (le_max_left _ _) hn)
        have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
        have hM₁ : 1 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊ := le_max_left _ _
        have hM₂ : 1 ≤ max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊ := le_max_left _ _
        have hconv := gaussianMAC_sum_converse_code hN hP₁ hP₂ hM₁ hM₂ C hpow
        have he : (gaussianMACAvgError C N).toReal ≤ δ :=
          ENNReal.toReal_le_of_le_ofReal hδ.le herr
        have hl1 := log_codeSize_ge n R₁
        have hl2 := log_codeSize_ge n R₂
        have hl0 : 0 ≤ Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊ : ℕ) : ℝ) +
            Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊ : ℕ) : ℝ) :=
          add_nonneg (Real.log_nonneg (by exact_mod_cast hM₁))
            (Real.log_nonneg (by exact_mod_cast hM₂))
        have h1 : (1 - δ) * (((n : ℝ) * (R₁ + R₂) - 2) * Real.log 2) ≤ (n : ℝ) * K + 1 := by
          have hsum_l : ((n : ℝ) * (R₁ + R₂) - 2) * Real.log 2 ≤
              Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊ : ℕ) : ℝ) +
              Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊ : ℕ) : ℝ) := by linarith
          calc (1 - δ) * (((n : ℝ) * (R₁ + R₂) - 2) * Real.log 2)
              ≤ (1 - δ) * (Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊ : ℕ) : ℝ) +
                  Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊ : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left hsum_l (by linarith)
            _ ≤ (1 - (gaussianMACAvgError C N).toReal) *
                  (Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊ : ℕ) : ℝ) +
                  Real.log ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊ : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) hl0
            _ ≤ (n : ℝ) * K + 1 := hconv
        have hdiv : (1 - δ) * (R₁ + R₂) * Real.log 2 =
            ((1 - δ) * (((n : ℝ) * (R₁ + R₂) - 2) * Real.log 2) +
              2 * (1 - δ) * Real.log 2) / n := by
          field_simp; ring
        rw [hdiv, div_le_iff₀ hnr]
        have hexp : (K + (1 + 2 * (1 - δ) * Real.log 2) * (1 / (n : ℝ))) * n =
            (n : ℝ) * K + 1 + 2 * (1 - δ) * Real.log 2 := by
          field_simp; ring
        rw [hexp]
        linarith
      have hlim : Tendsto
          (fun n : ℕ => K + (1 + 2 * (1 - δ) * Real.log 2) * (1 / (n : ℝ))) atTop (𝓝 K) := by
        simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_mul
          (1 + 2 * (1 - δ) * Real.log 2)).const_add K
      exact ge_of_tendsto hlim hev
    have hRK : (R₁ + R₂) * Real.log 2 ≤ K := by
      by_contra hlt
      push Not at hlt
      have hRpos : 0 < (R₁ + R₂) * Real.log 2 := lt_of_le_of_lt hK0 hlt
      set δ := ((R₁ + R₂) * Real.log 2 - K) / (2 * ((R₁ + R₂) * Real.log 2)) with hδ
      have hδpos : 0 < δ := div_pos (by linarith) (by linarith)
      have hδ1 : δ < 1 := by rw [hδ, div_lt_one (by linarith)]; linarith
      have h1 := step1 δ hδpos hδ1
      have hR12_ne : R₁ + R₂ ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hRpos; exact lt_irrefl _ hRpos
      have hcalc : (1 - δ) * (R₁ + R₂) * Real.log 2 = ((R₁ + R₂) * Real.log 2 + K) / 2 := by
        rw [hδ]; field_simp [hR12_ne, hlog2.ne']; ring
      rw [hcalc] at h1
      linarith
    have hcap : awgnCapacityFormula (P₁ + P₂) N = K / Real.log 2 := by
      unfold awgnCapacityFormula log2; rw [hK]; ring
    rw [hcap, le_div_iff₀ hlog2]
    exact hRK

/-- The textbook Gaussian MAC pentagon is a closed subset of `ℝ × ℝ`. -/
theorem isClosed_gaussianMACPentagon (P₁ P₂ N : ℝ) :
    IsClosed (gaussianMACPentagon P₁ P₂ N) := by
  have hc1 : IsClosed { r : ℝ × ℝ | 0 ≤ r.1 } := isClosed_le continuous_const continuous_fst
  have hc2 : IsClosed { r : ℝ × ℝ | 0 ≤ r.2 } := isClosed_le continuous_const continuous_snd
  have hc3 : IsClosed { r : ℝ × ℝ | r.1 ≤ awgnCapacityFormula P₁ N } :=
    isClosed_le continuous_fst continuous_const
  have hc4 : IsClosed { r : ℝ × ℝ | r.2 ≤ awgnCapacityFormula P₂ N } :=
    isClosed_le continuous_snd continuous_const
  have hc5 : IsClosed { r : ℝ × ℝ | r.1 + r.2 ≤ awgnCapacityFormula (P₁ + P₂) N } :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have heq : gaussianMACPentagon P₁ P₂ N =
      { r : ℝ × ℝ | 0 ≤ r.1 } ∩ ({ r : ℝ × ℝ | 0 ≤ r.2 } ∩
      ({ r : ℝ × ℝ | r.1 ≤ awgnCapacityFormula P₁ N } ∩
      ({ r : ℝ × ℝ | r.2 ≤ awgnCapacityFormula P₂ N } ∩
       { r : ℝ × ℝ | r.1 + r.2 ≤ awgnCapacityFormula (P₁ + P₂) N }))) := by
    ext r; simp [gaussianMACPentagon]
  rw [heq]
  exact hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5)))

/-- **Exact Operational Converse for the Two-User Gaussian MAC**
    (Cover & Thomas Thm. 15.1.1 converse; El Gamal & Kim Thm. 4.6):
    `gaussianMACCapacityRegion P₁ P₂ N ⊆ gaussianMACPentagon P₁ P₂ N`. -/
theorem gaussianMACCapacityRegion_subset_pentagon {P₁ P₂ N : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    gaussianMACCapacityRegion P₁ P₂ N ⊆ gaussianMACPentagon P₁ P₂ N :=
  closure_minimal (fun _ hr => isGaussianMACAchievable_mem_pentagon hP₁ hP₂ hN hr)
    (isClosed_gaussianMACPentagon P₁ P₂ N)

end GaussianMACConverse

/-! ### 3. Quantized Gaussian Interference Channel & Donsker–Varadhan Limit

For independent discretized Gaussian inputs `X₁ ~ gIn v₁ k` and `X₂ ~ gIn v₂ k` transmitted over
`Y = X₁ + X₂ + Z` (`Z ~ N(0, N)`), treating `X₂` as noise yields the single-user DMC
`gInterfChan v₂ N k`.  We show `I(gIn v₁ k, gInterfChan v₂ N k) → ½ log₂(1 + v₁ / (v₂ + N))`
from below via Donsker–Varadhan with the Gaussian LLR test function `gLLR (v₂ + N) (v₁ + v₂ + N)`. -/

section InterferenceDV

/-- Quantized 2-user Gaussian MAC `W_mac(j | i₁, i₂) = P_Z[qIdx k (qVal k i₁ + qVal k i₂ + Z) = j]`. -/
private noncomputable def gMacChan (N : ℝ) (k : ℕ) :
    DMC (Fin (qCard k) × Fin (qCard k)) (Fin (qCard k)) where
  trans p j := (gaussianReal (qVal k p.1 + qVal k p.2) N.toNNReal).real (qIdx k ⁻¹' {j})
  nonneg _ _ := measureReal_nonneg
  sum_one _ := sum_measureReal_preimage_eq_one _ (measurable_qIdx k)

/-- Marginal interference DMC seen by User 1 when User 2 transmits i.i.d. `gIn v₂ k`:
    `W₁(j | i₁) = ∑_{i₂} P₂(i₂) · P_Z[qIdx k (qVal k i₁ + qVal k i₂ + Z) = j]`. -/
private noncomputable def gInterfChan (v₂ N : ℝ) (k : ℕ) :
    DMC (Fin (qCard k)) (Fin (qCard k)) where
  trans i₁ j := ∑ i₂ : Fin (qCard k), (gIn v₂ k).pmf i₂ * (gMacChan N k).trans (i₁, i₂) j
  nonneg _ _ := Finset.sum_nonneg fun _ _ => mul_nonneg (ProbDist.nonneg _ _) (DMC.nonneg _ _ _)
  sum_one i₁ := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (gMacChan N k).sum_one, mul_one]
    exact (gIn v₂ k).sum_one

private lemma sum_gInterfChan_mul (v₂ N : ℝ) (k : ℕ) (i₁ : Fin (qCard k)) (g : ℝ → ℝ) :
    ∑ j, (gInterfChan v₂ N k).trans i₁ j * g (qVal k j) =
      ∫ u₂, ∫ z, g (qRound k (qVal k i₁ + qRound k u₂ + z))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal := by
  simp only [gInterfChan, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ i₂ : Fin (qCard k),
      ∑ j, (gIn v₂ k).pmf i₂ * (gMacChan N k).trans (i₁, i₂) j * g (qVal k j) =
        (gIn v₂ k).pmf i₂ *
          ∫ z, g (qRound k (qVal k i₁ + qVal k i₂ + z)) ∂gaussianReal 0 N.toNNReal := by
    intro i₂
    have h1 := sum_measureReal_preimage_mul (gaussianReal (qVal k i₁ + qVal k i₂) N.toNNReal)
      (measurable_qIdx k) (fun j => g (qVal k j))
    have h2 := integral_gaussianReal_eq_translate (qVal k i₁ + qVal k i₂) N.toNNReal
      (fun y => g (qVal k (qIdx k y)))
    have h3 : ∑ j, (gMacChan N k).trans (i₁, i₂) j * g (qVal k j) =
        ∫ z, g (qRound k (qVal k i₁ + qVal k i₂ + z)) ∂gaussianReal 0 N.toNNReal :=
      h1.trans h2
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i₂ _ => hinner i₂]
  exact sum_gIn_mul v₂ k (fun a₂ =>
    ∫ z, g (qRound k (qVal k i₁ + a₂ + z)) ∂gaussianReal 0 N.toNNReal)

private lemma interfDvA_eq (v₁ v₂ N : ℝ) (k : ℕ) (T : ℝ → ℝ → ℝ) :
    ∑ x, ∑ y, (gIn v₁ k).pmf x * (gInterfChan v₂ N k).trans x y * T (qVal k x) (qVal k y) =
      ∫ u₁, ∫ u₂, ∫ z, T (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal ∂gaussianReal 0 v₁.toNNReal := by
  have h1 : ∀ x, ∑ y, (gIn v₁ k).pmf x * (gInterfChan v₂ N k).trans x y * T (qVal k x) (qVal k y) =
      (gIn v₁ k).pmf x *
        ∫ u₂, ∫ z, T (qVal k x) (qRound k (qVal k x + qRound k u₂ + z))
          ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal := by
    intro x
    rw [← sum_gInterfChan_mul v₂ N k x (T (qVal k x)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  exact sum_gIn_mul v₁ k (fun a₁ =>
    ∫ u₂, ∫ z, T a₁ (qRound k (a₁ + qRound k u₂ + z))
      ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal)

private lemma interfDvB_eq (v₁ v₂ N : ℝ) (k : ℕ) (T : ℝ → ℝ → ℝ) :
    ∑ x, ∑ y, (gIn v₁ k).pmf x * (∑ x', (gIn v₁ k).pmf x' * (gInterfChan v₂ N k).trans x' y) *
        Real.exp (T (qVal k x) (qVal k y)) =
      ∫ u₁', ∫ u₁, ∫ u₂, ∫ z,
        Real.exp (T (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal
        ∂gaussianReal 0 v₁.toNNReal ∂gaussianReal 0 v₁.toNNReal := by
  have h1 : ∀ x, ∑ y, (gIn v₁ k).pmf x *
        (∑ x', (gIn v₁ k).pmf x' * (gInterfChan v₂ N k).trans x' y) *
        Real.exp (T (qVal k x) (qVal k y)) =
      (gIn v₁ k).pmf x * ∑ x', (gIn v₁ k).pmf x' *
        ∑ y, (gInterfChan v₂ N k).trans x' y * Real.exp (T (qVal k x) (qVal k y)) := by
    intro x
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y _ => by ring
  have h2 : ∀ x x', ∑ y, (gInterfChan v₂ N k).trans x' y * Real.exp (T (qVal k x) (qVal k y)) =
      ∫ u₂, ∫ z, Real.exp (T (qVal k x) (qRound k (qVal k x' + qRound k u₂ + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal :=
    fun x x' => sum_gInterfChan_mul v₂ N k x' (fun b => Real.exp (T (qVal k x) b))
  have h3 : ∀ x, ∑ x', (gIn v₁ k).pmf x' *
        ∫ u₂, ∫ z, Real.exp (T (qVal k x) (qRound k (qVal k x' + qRound k u₂ + z)))
          ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal =
      ∫ u₁, ∫ u₂, ∫ z, Real.exp (T (qVal k x) (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal ∂gaussianReal 0 v₁.toNNReal :=
    fun x => sum_gIn_mul v₁ k (fun a₁ =>
      ∫ u₂, ∫ z, Real.exp (T (qVal k x) (qRound k (a₁ + qRound k u₂ + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal)
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  simp_rw [h2, h3]
  exact sum_gIn_mul v₁ k (fun a =>
    ∫ u₁, ∫ u₂, ∫ z, Real.exp (T a (qRound k (qRound k u₁ + qRound k u₂ + z)))
      ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal ∂gaussianReal 0 v₁.toNNReal)

/-- Weighted 3-term Cauchy–Schwarz: `(a + b + c)² ≤ (v₁ + v₂ + v₃) · (a²/v₁ + b²/v₂ + c²/v₃)`. -/
private lemma weighted_sq_add_three_le {v₁ v₂ v₃ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hv₃ : 0 < v₃)
    (a b c : ℝ) :
    (a + b + c) ^ 2 / (v₁ + v₂ + v₃) ≤ a ^ 2 / v₁ + b ^ 2 / v₂ + c ^ 2 / v₃ := by
  have hS : 0 < v₁ + v₂ + v₃ := by linarith
  rw [div_le_iff₀ hS]
  have hdiff : (a ^ 2 / v₁ + b ^ 2 / v₂ + c ^ 2 / v₃) * (v₁ + v₂ + v₃) - (a + b + c) ^ 2 =
      (v₂ * a - v₁ * b) ^ 2 / (v₁ * v₂) +
      (v₃ * a - v₁ * c) ^ 2 / (v₁ * v₃) +
      (v₃ * b - v₂ * c) ^ 2 / (v₂ * v₃) := by
    field_simp [hv₁.ne', hv₂.ne', hv₃.ne']
    ring
  have hnn : 0 ≤ (v₂ * a - v₁ * b) ^ 2 / (v₁ * v₂) +
      (v₃ * a - v₁ * c) ^ 2 / (v₁ * v₃) +
      (v₃ * b - v₂ * c) ^ 2 / (v₂ * v₃) := by positivity
  linarith

private lemma abs_qRound_sum3_le (k : ℕ) (u₁ u₂ z : ℝ) :
    |qRound k (qRound k u₁ + qRound k u₂ + z)| ≤ (|u₁| + 1) + (|u₂| + 1) + (|z| + 1) := by
  have h1 := abs_qRound_le k u₁
  have h2 := abs_qRound_le k u₂
  have h3 := abs_qRound_le k (qRound k u₁ + qRound k u₂ + z)
  have h4 := abs_add_le (qRound k u₁ + qRound k u₂) z
  have h5 := abs_add_le (qRound k u₁) (qRound k u₂)
  linarith

private lemma tendsto_gLLR_qRound3 (N' S u₁' u₁ u₂ z : ℝ) :
    Tendsto (fun k : ℕ =>
      gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z))) atTop
      (𝓝 (gLLR N' S u₁' (u₁ + u₂ + z))) := by
  have h1' : Tendsto (fun k : ℕ => qRound k u₁') atTop (𝓝 u₁') :=
    tendsto_qRound tendsto_const_nhds
  have h1 : Tendsto (fun k : ℕ => qRound k u₁) atTop (𝓝 u₁) :=
    tendsto_qRound tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ => qRound k u₂) atTop (𝓝 u₂) :=
    tendsto_qRound tendsto_const_nhds
  have h3 : Tendsto (fun k : ℕ => (qRound k u₁', qRound k (qRound k u₁ + qRound k u₂ + z))) atTop
      (𝓝 (u₁', u₁ + u₂ + z)) :=
    h1'.prodMk_nhds (tendsto_qRound ((h1.add h2).add_const z))
  have h4 := ((continuous_gLLR N' S).tendsto (u₁', u₁ + u₂ + z)).comp h3
  exact h4

private lemma measurable_gLLR_qRound3 (N' S : ℝ) (k : ℕ) (u₁' u₁ u₂ : ℝ) :
    Measurable (fun z => gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z))) := by
  have h : Measurable (fun z => (qRound k u₁', qRound k (qRound k u₁ + qRound k u₂ + z))) :=
    measurable_const.prodMk ((measurable_qRound k).comp (measurable_const_add _))
  have h2 := (continuous_gLLR N' S).measurable.comp h
  exact h2

/-- First DV term of the quantized interference channel converges to
    `½ ln((v₁ + v₂ + N) / (v₂ + N))`. -/
private theorem tendsto_interfDvA {v₁ v₂ N : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hN : 0 < N) :
    Tendsto (fun k : ℕ =>
      ∫ u₁, ∫ u₂, ∫ z,
        gLLR (v₂ + N) (v₁ + v₂ + N) (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal ∂gaussianReal 0 v₁.toNNReal)
      atTop (𝓝 (1 / 2 * Real.log ((v₁ + v₂ + N) / (v₂ + N)))) := by
  set N' := v₂ + N with hN'_def
  set S := v₁ + v₂ + N with hS_def
  have hN' : 0 < N' := by linarith
  have hS : 0 < S := by linarith
  set c₀ := |1 / 2 * Real.log (S / N')| with hc₀
  set K := 1 / N' + 1 / (2 * S) with hK_def
  have hK : 0 ≤ K := by positivity
  set γ₁ := gaussianReal 0 v₁.toNNReal
  set γ₂ := gaussianReal 0 v₂.toNNReal
  set γN := gaussianReal 0 N.toNNReal
  -- Pointwise quadratic domination
  have hbd : ∀ (k : ℕ) (u₁ u₂ z : ℝ),
      ‖gLLR N' S (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z))‖ ≤
        (c₀ + K * (8 * u₁ ^ 2 + 6 * u₂ ^ 2 + 20)) + 6 * K * z ^ 2 := by
    intro k u₁ u₂ z
    have hx := sq_le_two_sq_add_two (abs_qRound_le k u₁)
    have habs := abs_qRound_sum3_le k u₁ u₂ z
    have hy1 : qRound k (qRound k u₁ + qRound k u₂ + z) ^ 2 ≤
        ((|u₁| + 1) + (|u₂| + 1) + (|z| + 1)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hy2 : ((|u₁| + 1) + (|u₂| + 1) + (|z| + 1)) ^ 2 ≤
        3 * ((|u₁| + 1) ^ 2 + (|u₂| + 1) ^ 2 + (|z| + 1) ^ 2) := by
      nlinarith [sq_nonneg ((|u₁| + 1) - (|u₂| + 1)), sq_nonneg ((|u₁| + 1) - (|z| + 1)),
        sq_nonneg ((|u₂| + 1) - (|z| + 1))]
    have hy3 : (|u₁| + 1) ^ 2 ≤ 2 * u₁ ^ 2 + 2 := by nlinarith [sq_abs u₁, sq_nonneg (|u₁| - 1)]
    have hy4 : (|u₂| + 1) ^ 2 ≤ 2 * u₂ ^ 2 + 2 := by nlinarith [sq_abs u₂, sq_nonneg (|u₂| - 1)]
    have hy5 : (|z| + 1) ^ 2 ≤ 2 * z ^ 2 + 2 := by nlinarith [sq_abs z, sq_nonneg (|z| - 1)]
    rw [Real.norm_eq_abs]
    refine le_trans (abs_gLLR_le hN' hS _ _) ?_
    have hsum : (qRound k u₁ ^ 2 + qRound k (qRound k u₁ + qRound k u₂ + z) ^ 2) * K ≤
        (8 * u₁ ^ 2 + 6 * u₂ ^ 2 + 6 * z ^ 2 + 20) * K :=
      mul_le_mul_of_nonneg_right (by linarith) hK
    linarith
  -- Level 1 (z)
  have hlev1 : ∀ u₁ u₂ : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, gLLR N' S (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z)) ∂γN) atTop
      (𝓝 (∫ z, gLLR N' S u₁ (u₁ + u₂ + z) ∂γN)) := by
    intro u₁ u₂
    refine tendsto_integral_of_dominated_convergence
      (fun z => (c₀ + K * (8 * u₁ ^ 2 + 6 * u₂ ^ 2 + 20)) + 6 * K * z ^ 2)
      (fun k => (measurable_gLLR_qRound3 N' S k u₁ u₁ u₂).aestronglyMeasurable)
      (integrable_const_add_mul_sq _ _ _) (fun k => ae_of_all _ fun z => hbd k u₁ u₂ z)
      (ae_of_all _ fun z => tendsto_gLLR_qRound3 N' S u₁ u₁ u₂ z)
  -- Level 2 (u₂)
  have hbd2 : ∀ (k : ℕ) (u₁ u₂ : ℝ),
      ‖∫ z, gLLR N' S (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z)) ∂γN‖ ≤
        (c₀ + K * 20 + 6 * K * N + 8 * K * u₁ ^ 2) + 6 * K * u₂ ^ 2 := by
    intro k u₁ u₂
    refine le_trans (norm_integral_le_of_norm_le (integrable_const_add_mul_sq _ _ _)
      (ae_of_all _ fun z => hbd k u₁ u₂ z)) (le_of_eq ?_)
    rw [integral_const_add_mul_sq _ _ _ hN.le]
    ring
  have hlev2 : ∀ u₁ : ℝ, Tendsto (fun k : ℕ =>
      ∫ u₂, ∫ z, gLLR N' S (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z)) ∂γN ∂γ₂) atTop
      (𝓝 (∫ u₂, ∫ z, gLLR N' S u₁ (u₁ + u₂ + z) ∂γN ∂γ₂)) := by
    intro u₁
    refine tendsto_integral_of_dominated_convergence
      (fun u₂ => (c₀ + K * 20 + 6 * K * N + 8 * K * u₁ ^ 2) + 6 * K * u₂ ^ 2)
      (fun k => aesm_comp_qRound k
        (fun a₂ => ∫ z, gLLR N' S (qRound k u₁) (qRound k (qRound k u₁ + a₂ + z)) ∂γN) _)
      (integrable_const_add_mul_sq _ _ _) (fun k => ae_of_all _ fun u₂ => hbd2 k u₁ u₂)
      (ae_of_all _ fun u₂ => hlev1 u₁ u₂)
  -- Level 3 (u₁)
  have hbd3 : ∀ (k : ℕ) (u₁ : ℝ),
      ‖∫ u₂, ∫ z, gLLR N' S (qRound k u₁) (qRound k (qRound k u₁ + qRound k u₂ + z)) ∂γN ∂γ₂‖ ≤
        (c₀ + K * 20 + 6 * K * N + 6 * K * v₂) + 8 * K * u₁ ^ 2 := by
    intro k u₁
    refine le_trans (norm_integral_le_of_norm_le (integrable_const_add_mul_sq _ _ _)
      (ae_of_all _ fun u₂ => hbd2 k u₁ u₂)) (le_of_eq ?_)
    rw [integral_const_add_mul_sq _ _ _ hv₂.le]
    ring
  have hlev3 := tendsto_integral_of_dominated_convergence (μ := γ₁)
    (fun u₁ => (c₀ + K * 20 + 6 * K * N + 6 * K * v₂) + 8 * K * u₁ ^ 2)
    (fun k => aesm_comp_qRound k
      (fun a₁ => ∫ u₂, ∫ z, gLLR N' S a₁ (qRound k (a₁ + qRound k u₂ + z)) ∂γN ∂γ₂) _)
    (integrable_const_add_mul_sq _ _ _) (fun k => ae_of_all _ fun u₁ => hbd3 k u₁)
    (ae_of_all _ fun u₁ => hlev2 u₁)
  -- Evaluate the limit via `γ₂ ∗ γN = γ_{N'}`
  have hconv : γ₂ ∗ γN = gaussianReal 0 N'.toNNReal := by
    rw [gaussianReal_conv_gaussianReal, add_zero, hN'_def, Real.toNNReal_add hv₂.le hN.le]
  have hinner_val : ∀ u₁ : ℝ, ∫ u₂, ∫ z, gLLR N' S u₁ (u₁ + u₂ + z) ∂γN ∂γ₂ =
      (1 / 2 * Real.log (S / N') - 1 / 2 + N' / (2 * S)) + 1 / (2 * S) * u₁ ^ 2 := by
    intro u₁
    have hint : Integrable (fun w => gLLR N' S u₁ (u₁ + w)) (gaussianReal 0 N'.toNNReal) := by
      refine (integrable_const_add_mul_sq (c₀ + K * (3 * u₁ ^ 2)) (2 * K) N'.toNNReal).mono' ?_ ?_
      · exact ((continuous_gLLR N' S).comp
          (continuous_const.prodMk (continuous_const.add continuous_id))).aestronglyMeasurable
      · refine ae_of_all _ fun w => ?_
        rw [Real.norm_eq_abs]
        refine le_trans (abs_gLLR_le hN' hS u₁ (u₁ + w)) ?_
        have hsq : (u₁ + w) ^ 2 ≤ 2 * u₁ ^ 2 + 2 * w ^ 2 := by nlinarith [sq_nonneg (u₁ - w)]
        have : (u₁ ^ 2 + (u₁ + w) ^ 2) * K ≤ (3 * u₁ ^ 2 + 2 * w ^ 2) * K :=
          mul_le_mul_of_nonneg_right (by linarith) hK
        linarith
    have hint' : Integrable (fun w => gLLR N' S u₁ (u₁ + w)) (γ₂ ∗ γN) := by rw [hconv]; exact hint
    have h1 := integral_conv hint'
    have hrew : (fun u₂ => ∫ z, gLLR N' S u₁ (u₁ + (u₂ + z)) ∂γN) =
        fun u₂ => ∫ z, gLLR N' S u₁ (u₁ + u₂ + z) ∂γN := by
      funext u₂; congr 1; funext z; rw [add_assoc]
    rw [hrew] at h1
    rw [← h1, hconv]
    have htr := integral_gaussianReal_eq_translate u₁ N'.toNNReal (fun y => gLLR N' S u₁ y)
    rw [← htr]
    have h2 : (fun y => gLLR N' S u₁ y) = awgnLetterLLR N' S u₁ := by
      funext y; exact gLLR_eq_awgnLetterLLR hN' hS u₁ y
    rw [h2, integral_awgnLetterLLR hN' hS u₁]
    ring
  have hval : ∫ u₁, ∫ u₂, ∫ z, gLLR N' S u₁ (u₁ + u₂ + z) ∂γN ∂γ₂ ∂γ₁ =
      1 / 2 * Real.log (S / N') := by
    simp_rw [hinner_val]
    rw [integral_const_add_mul_sq _ _ _ hv₁.le, hS_def, hN'_def]
    field_simp
    ring
  rw [hval] at hlev3
  exact hlev3

/-- Second DV term of the quantized interference channel converges to `1`. -/
private theorem tendsto_interfDvB {v₁ v₂ N : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hN : 0 < N) :
    Tendsto (fun k : ℕ =>
      ∫ u₁', ∫ u₁, ∫ u₂, ∫ z,
        Real.exp (gLLR (v₂ + N) (v₁ + v₂ + N) (qRound k u₁')
          (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂gaussianReal 0 N.toNNReal ∂gaussianReal 0 v₂.toNNReal
        ∂gaussianReal 0 v₁.toNNReal ∂gaussianReal 0 v₁.toNNReal)
      atTop (𝓝 1) := by
  set N' := v₂ + N with hN'_def
  set S := v₁ + v₂ + N with hS_def
  have hN' : 0 < N' := by linarith
  have hS : 0 < S := by linarith
  have hNS : N' < S := by linarith
  have h2SN : 0 < 2 * S - N' := by linarith
  set γ₁ := gaussianReal 0 v₁.toNNReal
  set γ₂ := gaussianReal 0 v₂.toNNReal
  set γN := gaussianReal 0 N.toNNReal
  set a₀ := Real.exp (1 / 2 * Real.log (S / N'))
  set E0 : ℝ → ℝ := fun t => Real.exp (1 / (2 * (2 * S - N')) * (|t| + 1) ^ 2)
  set E1 : ℝ → ℝ := fun t => Real.exp (1 / (4 * v₁) * (|t| + 1) ^ 2)
  set E2 : ℝ → ℝ := fun t => Real.exp (1 / (4 * v₂) * (|t| + 1) ^ 2)
  set E3 : ℝ → ℝ := fun t => Real.exp (1 / (4 * N) * (|t| + 1) ^ 2)
  have hE0 : Integrable E0 γ₁ := integrable_exp_shift_sq_gaussianReal hv₁
    (by rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith)
  have hE1 : Integrable E1 γ₁ := integrable_exp_shift_sq_gaussianReal hv₁
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith)
  have hE2 : Integrable E2 γ₂ := integrable_exp_shift_sq_gaussianReal hv₂
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith)
  have hE3 : Integrable E3 γN := integrable_exp_shift_sq_gaussianReal hN
    (by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith)
  set IN := ∫ z, E3 z ∂γN
  set I2 := ∫ u₂, E2 u₂ ∂γ₂
  set I1 := ∫ u₁, E1 u₁ ∂γ₁
  -- Pointwise 4-factor exponential domination via weighted Cauchy–Schwarz
  have hbd : ∀ (k : ℕ) (u₁' u₁ u₂ z : ℝ),
      ‖Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z)))‖ ≤
        a₀ * E0 u₁' * E1 u₁ * E2 u₂ * E3 z := by
    intro k u₁' u₁ u₂ z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [a₀, E0, E1, E2, E3]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr (le_trans (gLLR_le hN' hNS _ _) ?_)
    have hx : qRound k u₁' ^ 2 ≤ (|u₁'| + 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_qRound_le k u₁') 2
    have e0 : qRound k u₁' ^ 2 / (2 * (2 * S - N')) ≤ 1 / (2 * (2 * S - N')) * (|u₁'| + 1) ^ 2 := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hx (one_div_pos.mpr (by linarith)).le
    have hy1 : qRound k (qRound k u₁ + qRound k u₂ + z) ^ 2 ≤
        ((|u₁| + 1) + (|u₂| + 1) + (|z| + 1)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_qRound_sum3_le k u₁ u₂ z) 2
    have hcs := weighted_sq_add_three_le hv₁ hv₂ hN (|u₁| + 1) (|u₂| + 1) (|z| + 1)
    have hy2 : qRound k (qRound k u₁ + qRound k u₂ + z) ^ 2 / (4 * S) ≤
        1 / (4 * v₁) * (|u₁| + 1) ^ 2 + 1 / (4 * v₂) * (|u₂| + 1) ^ 2 +
          1 / (4 * N) * (|z| + 1) ^ 2 := by
      have hstep1 : qRound k (qRound k u₁ + qRound k u₂ + z) ^ 2 / (4 * S) ≤
          ((|u₁| + 1) + (|u₂| + 1) + (|z| + 1)) ^ 2 / (4 * S) :=
        div_le_div_of_nonneg_right hy1 (by positivity)
      have hstep2 : ((|u₁| + 1) + (|u₂| + 1) + (|z| + 1)) ^ 2 / (4 * S) =
          (1 / 4) * (((|u₁| + 1) + (|u₂| + 1) + (|z| + 1)) ^ 2 / (v₁ + v₂ + N)) := by
        rw [hS_def]; field_simp [(by linarith : v₁ + v₂ + N ≠ 0)]
      have hstep3 : (1 / 4) * ((|u₁| + 1) ^ 2 / v₁ + (|u₂| + 1) ^ 2 / v₂ + (|z| + 1) ^ 2 / N) =
          1 / (4 * v₁) * (|u₁| + 1) ^ 2 + 1 / (4 * v₂) * (|u₂| + 1) ^ 2 +
            1 / (4 * N) * (|z| + 1) ^ 2 := by
        ring
      nlinarith
    linarith
  -- Level 1 (z)
  have hlev1 : ∀ u₁' u₁ u₂ : ℝ, Tendsto (fun k : ℕ =>
      ∫ z, Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z))) ∂γN)
      atTop (𝓝 (∫ z, Real.exp (gLLR N' S u₁' (u₁ + u₂ + z)) ∂γN)) := by
    intro u₁' u₁ u₂
    refine tendsto_integral_of_dominated_convergence
      (fun z => a₀ * E0 u₁' * E1 u₁ * E2 u₂ * E3 z)
      (fun k => (Real.continuous_exp.measurable.comp
        (measurable_gLLR_qRound3 N' S k u₁' u₁ u₂)).aestronglyMeasurable)
      (hE3.const_mul _) (fun k => ae_of_all _ fun z => hbd k u₁' u₁ u₂ z)
      (ae_of_all _ fun z => (Real.continuous_exp.tendsto _).comp
        (tendsto_gLLR_qRound3 N' S u₁' u₁ u₂ z))
  -- Level 2 (u₂)
  have hbd2 : ∀ (k : ℕ) (u₁' u₁ u₂ : ℝ),
      ‖∫ z, Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z))) ∂γN‖ ≤
        a₀ * E0 u₁' * E1 u₁ * E2 u₂ * IN := by
    intro k u₁' u₁ u₂
    refine le_trans (norm_integral_le_of_norm_le (hE3.const_mul (a₀ * E0 u₁' * E1 u₁ * E2 u₂))
      (ae_of_all _ fun z => hbd k u₁' u₁ u₂ z)) (le_of_eq ?_)
    rw [integral_const_mul]
  have hlev2 : ∀ u₁' u₁ : ℝ, Tendsto (fun k : ℕ =>
      ∫ u₂, ∫ z, Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂γN ∂γ₂) atTop (𝓝 (∫ u₂, ∫ z, Real.exp (gLLR N' S u₁' (u₁ + u₂ + z)) ∂γN ∂γ₂)) := by
    intro u₁' u₁
    refine tendsto_integral_of_dominated_convergence
      (fun u₂ => a₀ * E0 u₁' * E1 u₁ * E2 u₂ * IN)
      (fun k => aesm_comp_qRound k
        (fun a₂ => ∫ z, Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + a₂ + z))) ∂γN) _)
      ((hE2.const_mul _).mul_const _) (fun k => ae_of_all _ fun u₂ => hbd2 k u₁' u₁ u₂)
      (ae_of_all _ fun u₂ => hlev1 u₁' u₁ u₂)
  -- Level 3 (u₁)
  have hbd3 : ∀ (k : ℕ) (u₁' u₁ : ℝ),
      ‖∫ u₂, ∫ z, Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂γN ∂γ₂‖ ≤ a₀ * E0 u₁' * E1 u₁ * I2 * IN := by
    intro k u₁' u₁
    refine le_trans (norm_integral_le_of_norm_le
      ((hE2.const_mul (a₀ * E0 u₁' * E1 u₁)).mul_const IN)
      (ae_of_all _ fun u₂ => hbd2 k u₁' u₁ u₂)) (le_of_eq ?_)
    rw [integral_mul_const, integral_const_mul]
  have hlev3 : ∀ u₁' : ℝ, Tendsto (fun k : ℕ =>
      ∫ u₁, ∫ u₂, ∫ z,
        Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂γN ∂γ₂ ∂γ₁) atTop
      (𝓝 (∫ u₁, ∫ u₂, ∫ z, Real.exp (gLLR N' S u₁' (u₁ + u₂ + z)) ∂γN ∂γ₂ ∂γ₁)) := by
    intro u₁'
    refine tendsto_integral_of_dominated_convergence
      (fun u₁ => a₀ * E0 u₁' * E1 u₁ * I2 * IN)
      (fun k => aesm_comp_qRound k
        (fun a₁ => ∫ u₂, ∫ z,
          Real.exp (gLLR N' S (qRound k u₁') (qRound k (a₁ + qRound k u₂ + z))) ∂γN ∂γ₂) _)
      (((hE1.const_mul _).mul_const _).mul_const _)
      (fun k => ae_of_all _ fun u₁ => hbd3 k u₁' u₁)
      (ae_of_all _ fun u₁ => hlev2 u₁' u₁)
  -- Level 4 (u₁')
  have hbd4 : ∀ (k : ℕ) (u₁' : ℝ),
      ‖∫ u₁, ∫ u₂, ∫ z,
        Real.exp (gLLR N' S (qRound k u₁') (qRound k (qRound k u₁ + qRound k u₂ + z)))
        ∂γN ∂γ₂ ∂γ₁‖ ≤ a₀ * E0 u₁' * I1 * I2 * IN := by
    intro k u₁'
    refine le_trans (norm_integral_le_of_norm_le
      (((hE1.const_mul (a₀ * E0 u₁')).mul_const I2).mul_const IN)
      (ae_of_all _ fun u₁ => hbd3 k u₁' u₁)) (le_of_eq ?_)
    rw [integral_mul_const, integral_mul_const, integral_const_mul]
  have hlev4 := tendsto_integral_of_dominated_convergence (μ := γ₁)
    (fun u₁' => a₀ * E0 u₁' * I1 * I2 * IN)
    (fun k => aesm_comp_qRound k
      (fun a => ∫ u₁, ∫ u₂, ∫ z,
        Real.exp (gLLR N' S a (qRound k (qRound k u₁ + qRound k u₂ + z))) ∂γN ∂γ₂ ∂γ₁) _)
    ((((hE0.const_mul a₀).mul_const I1).mul_const I2).mul_const IN)
    (fun k => ae_of_all _ fun u₁' => hbd4 k u₁')
    (ae_of_all _ fun u₁' => hlev3 u₁')
  -- Evaluate the limit via `γ₂ ∗ γN = γ_{N'}` and `integral_integral_exp_gLLR`
  have hconv : γ₂ ∗ γN = gaussianReal 0 N'.toNNReal := by
    rw [gaussianReal_conv_gaussianReal, add_zero, hN'_def, Real.toNNReal_add hv₂.le hN.le]
  have hinner_eq : ∀ u₁' u₁ : ℝ,
      ∫ u₂, ∫ z, Real.exp (gLLR N' S u₁' (u₁ + u₂ + z)) ∂γN ∂γ₂ =
        ∫ w, Real.exp (gLLR N' S u₁' (u₁ + w)) ∂gaussianReal 0 N'.toNNReal := by
    intro u₁' u₁
    have hint : Integrable (fun w => Real.exp (gLLR N' S u₁' (u₁ + w)))
        (gaussianReal 0 N'.toNNReal) := by
      have hc : 1 / (2 * S) < 1 / (2 * N') := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
      refine ((integrable_exp_mul_sq_gaussianReal hN' hc).const_mul
        (Real.exp (1 / 2 * Real.log (S / N') + u₁' ^ 2 / (2 * (2 * S - N')) +
          u₁ ^ 2 / (2 * S)))).mono' ?_ ?_
      · exact (Real.continuous_exp.comp ((continuous_gLLR N' S).comp
          (continuous_const.prodMk (continuous_const.add continuous_id)))).aestronglyMeasurable
      · refine ae_of_all _ fun w => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        refine Real.exp_le_exp.mpr (le_trans (gLLR_le hN' hNS u₁' (u₁ + w)) ?_)
        have hsq : (u₁ + w) ^ 2 ≤ 2 * u₁ ^ 2 + 2 * w ^ 2 := by nlinarith [sq_nonneg (u₁ - w)]
        have hdiv : (u₁ + w) ^ 2 / (4 * S) ≤ u₁ ^ 2 / (2 * S) + 1 / (2 * S) * w ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          have : (u₁ ^ 2 / (2 * S) + 1 / (2 * S) * w ^ 2) * (4 * S) = 2 * u₁ ^ 2 + 2 * w ^ 2 := by
            field_simp; ring
          linarith
        linarith
    have hint' : Integrable (fun w => Real.exp (gLLR N' S u₁' (u₁ + w))) (γ₂ ∗ γN) := by
      rw [hconv]; exact hint
    have h1 := integral_conv hint'
    have hrew : (fun u₂ => ∫ z, Real.exp (gLLR N' S u₁' (u₁ + (u₂ + z))) ∂γN) =
        fun u₂ => ∫ z, Real.exp (gLLR N' S u₁' (u₁ + u₂ + z)) ∂γN := by
      funext u₂; congr 1; funext z; rw [add_assoc]
    rw [hrew] at h1
    rw [← h1, hconv]
  have hval : ∫ u₁', ∫ u₁, ∫ u₂, ∫ z, Real.exp (gLLR N' S u₁' (u₁ + u₂ + z)) ∂γN ∂γ₂ ∂γ₁ ∂γ₁ =
      1 := by
    simp_rw [hinner_eq]
    have hS' : S = v₁ + N' := by rw [hS_def, hN'_def]; ring
    simp_rw [γ₁, hS', integral_integral_exp_gLLR hv₁ hN']
    simp
  rw [hval] at hlev4
  exact hlev4

/-- Mutual information lower bound for `gInterfChan v₂ N k` holds eventually as `k → ∞`. -/
private lemma eventually_interf_mutualInfo_gt {v₁ v₂ N R₁ : ℝ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hN : 0 < N)
    (hR₁ : R₁ < awgnCapacityFormula v₁ (v₂ + N)) :
    ∀ᶠ k : ℕ in atTop, R₁ < (gInterfChan v₂ N k).mutualInfo (gIn v₁ k) := by
  have hA := tendsto_interfDvA hv₁ hv₂ hN
  have hB := tendsto_interfDvB hv₁ hv₂ hN
  have hlim := hA.sub (hB.log one_ne_zero)
  rw [Real.log_one, sub_zero] at hlim
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hN' : 0 < v₂ + N := by linarith
  have hRlt : R₁ * Real.log 2 < 1 / 2 * Real.log ((v₁ + v₂ + N) / (v₂ + N)) := by
    have h1 : 1 + v₁ / (v₂ + N) = (v₁ + v₂ + N) / (v₂ + N) := by field_simp [hN'.ne']; ring
    unfold awgnCapacityFormula log2 at hR₁
    rw [h1] at hR₁
    have h3 := mul_lt_mul_of_pos_right hR₁ hlog2
    have h2 : 1 / 2 * (Real.log ((v₁ + v₂ + N) / (v₂ + N)) / Real.log 2) * Real.log 2 =
        1 / 2 * Real.log ((v₁ + v₂ + N) / (v₂ + N)) := by field_simp
    linarith
  filter_upwards [(tendsto_order.1 hlim).1 _ hRlt] with k hk
  have hdv := mutualInfo_ge_dv (gInterfChan v₂ N k) (gIn v₁ k)
    (fun x y => gLLR (v₂ + N) (v₁ + v₂ + N) (qVal k x) (qVal k y))
  rw [interfDvA_eq v₁ v₂ N k (gLLR (v₂ + N) (v₁ + v₂ + N)),
    interfDvB_eq v₁ v₂ N k (gLLR (v₂ + N) (v₁ + v₂ + N))] at hdv
  have : R₁ * Real.log 2 < (gInterfChan v₂ N k).mutualInfo (gIn v₁ k) * Real.log 2 := by linarith
  exact lt_of_mul_lt_mul_right this hlog2.le

/-- Mutual information lower bound for `gChan N k` holds eventually as `k → ∞`. -/
private lemma eventually_single_mutualInfo_gt {v N R : ℝ}
    (hv : 0 < v) (hN : 0 < N) (hR : R < awgnCapacityFormula v N) :
    ∀ᶠ k : ℕ in atTop, R < (gChan N k).mutualInfo (gIn v k) := by
  have hA := tendsto_dvA hv hN
  have hB := tendsto_dvB hv hN
  have hlim := hA.sub (hB.log one_ne_zero)
  rw [Real.log_one, sub_zero] at hlim
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hRlt : R * Real.log 2 < 1 / 2 * Real.log ((v + N) / N) := by
    have h1 : 1 + v / N = (v + N) / N := by field_simp [hN.ne']; ring
    unfold awgnCapacityFormula log2 at hR
    rw [h1] at hR
    have h3 := mul_lt_mul_of_pos_right hR hlog2
    have h2 : 1 / 2 * (Real.log ((v + N) / N) / Real.log 2) * Real.log 2 =
        1 / 2 * Real.log ((v + N) / N) := by field_simp
    linarith
  filter_upwards [(tendsto_order.1 hlim).1 _ hRlt] with k hk
  have hdv := mutualInfo_ge_dv (gChan N k) (gIn v k)
    (fun x y => gLLR N (v + N) (qVal k x) (qVal k y))
  rw [dvA_eq v N k (gLLR N (v + N)), dvB_eq v N k (gLLR N (v + N))] at hdv
  have : R * Real.log 2 < (gChan N k).mutualInfo (gIn v k) * Real.log 2 := by linarith
  exact lt_of_mul_lt_mul_right this hlog2.le

end InterferenceDV

/-! ### 4. Corner-Point Achievability via Successive Interference Cancellation (SIC) -/

section CornerAchievability

/-- The quantized Stage-1 error probability `P_Z[dec₁(qIdx(x₁ + x₂ + Z)) ≠ m₁]` equals the
    discrete error probability over `(gMacChan N k).power n`. -/
private lemma stage1_error_toReal (N : ℝ) (k n M₁ : ℕ)
    (x₁ x₂ : Fin n → Fin (qCard k)) (dec₁ : (Fin n → Fin (qCard k)) → Fin M₁) (m₁ : Fin M₁) :
    (awgnNoise n N {z | dec₁ (fun i => qIdx k (qVal k (x₁ i) + qVal k (x₂ i) + z i)) ≠ m₁}).toReal =
      ∑ y : Fin n → Fin (qCard k),
        if dec₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (x₁ i, x₂ i)) y else 0 := by
  classical
  let s : Fin n → ℝ := fun i => qVal k (x₁ i) + qVal k (x₂ i)
  let thr : (Fin n → ℝ) → (Fin n → Fin (qCard k)) := fun y i => qIdx k (y i)
  have hthr : Measurable thr :=
    measurable_pi_iff.mpr fun i => (measurable_qIdx k).comp (measurable_pi_apply i)
  have hfin : MeasurableSet {b : Fin n → Fin (qCard k) | dec₁ b ≠ m₁} :=
    (Set.toFinite _).measurableSet
  have hpre : {z : Fin n → ℝ | dec₁ (fun i => qIdx k (qVal k (x₁ i) + qVal k (x₂ i) + z i)) ≠ m₁} =
      (fun z => s + z) ⁻¹' (thr ⁻¹' {b | dec₁ b ≠ m₁}) := by
    ext z; rfl
  rw [hpre, ← Measure.map_apply (measurable_const_add s) (hthr hfin), ← awgnBlockLaw_eq_map,
    ← Measure.map_apply hthr hfin]
  have hmap : (awgnBlockLaw n N s).map thr =
      Measure.pi (fun i => (gaussianReal (s i) N.toNNReal).map (qIdx k)) :=
    Measure.pi_map_pi (fun i => (measurable_qIdx k).aemeasurable)
  rw [hmap]
  have hS : {b : Fin n → Fin (qCard k) | dec₁ b ≠ m₁} =
      ↑(Finset.univ.filter (fun b => dec₁ b ≠ m₁)) := by ext; simp
  rw [hS, ← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Measure.pi_singleton, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.map_apply (measurable_qIdx k) (measurableSet_singleton _)]
    rfl
  · rfl

/-- Averaging the `n`-letter quantized MAC transition probability over `enc₂ ~ codebookProb P₂ n M₂`
    yields the `n`-letter interference DMC `(gInterfChan v₂ N k).power n`. -/
private lemma sum_codebookProb_gMacChan (v₂ N : ℝ) (k n M₂ : ℕ)
    (x₁ : Fin n → Fin (qCard k)) (y : Fin n → Fin (qCard k)) (m₂ : Fin M₂) :
    ∑ enc₂ : Fin M₂ → Fin n → Fin (qCard k),
      codebookProb (gIn v₂ k) n M₂ enc₂ *
        ((gMacChan N k).power n).trans (fun i => (x₁ i, enc₂ m₂ i)) y =
      ((gInterfChan v₂ N k).power n).trans x₁ y := by
  have h1 : ∀ enc₂ : Fin M₂ → Fin n → Fin (qCard k),
      codebookProb (gIn v₂ k) n M₂ enc₂ = (iidDist (iidDist (gIn v₂ k) n) M₂).pmf enc₂ :=
    fun _ => rfl
  simp_rw [h1]
  rw [iidDist_sum_coord (iidDist (gIn v₂ k) n)
    (fun x₂ => ((gMacChan N k).power n).trans (fun i => (x₁ i, x₂ i)) y) m₂]
  show ∑ x₂ : Fin n → Fin (qCard k),
      (∏ i : Fin n, (gIn v₂ k).pmf (x₂ i)) *
        (∏ i : Fin n, (gMacChan N k).trans (x₁ i, x₂ i) (y i)) =
    ∏ i : Fin n, ∑ a₂ : Fin (qCard k),
      (gIn v₂ k).pmf a₂ * (gMacChan N k).trans (x₁ i, a₂) (y i)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i a₂ => (gIn v₂ k).pmf a₂ * (gMacChan N k).trans (x₁ i, a₂) (y i)).symm

/-- Measurable SIC Gaussian MAC code built from discrete encoders `enc₁, enc₂` and discrete
    decoders `dec₁, dec₂`: decode `m̂₁` from `qIdx ∘ y`, subtract `qVal ∘ enc₁ m̂₁` in `ℝⁿ`,
    then decode `m̂₂` from `qIdx ∘ (y - qVal ∘ enc₁ m̂₁)`. -/
private noncomputable def sicGaussianMACCode (k : ℕ) {n M₁ M₂ : ℕ}
    (enc₁ : Fin M₁ → Fin n → Fin (qCard k)) (enc₂ : Fin M₂ → Fin n → Fin (qCard k))
    (dec₁ : (Fin n → Fin (qCard k)) → Fin M₁) (dec₂ : (Fin n → Fin (qCard k)) → Fin M₂) :
    GaussianMACCode n M₁ M₂ where
  encoder₁ m₁ i := qVal k (enc₁ m₁ i)
  encoder₂ m₂ i := qVal k (enc₂ m₂ i)
  decoder y :=
    let m1hat := dec₁ (fun i => qIdx k (y i))
    (m1hat, dec₂ (fun i => qIdx k (y i - qVal k (enc₁ m1hat i))))
  measurable_decoder := by
    have hm₁ : Measurable (fun y : Fin n → ℝ => dec₁ (fun i => qIdx k (y i))) :=
      (measurable_of_finite dec₁).comp
        (measurable_pi_iff.mpr fun i => (measurable_qIdx k).comp (measurable_pi_apply i))
    have hm₂ : Measurable (fun y : Fin n → ℝ =>
        dec₂ (fun i => qIdx k (y i - qVal k (enc₁ (dec₁ (fun j => qIdx k (y j))) i)))) := by
      refine (measurable_of_finite dec₂).comp (measurable_pi_iff.mpr fun i => ?_)
      have hsub : Measurable (fun y : Fin n → ℝ =>
          y i - qVal k (enc₁ (dec₁ (fun j => qIdx k (y j))) i)) :=
        (measurable_pi_apply i).sub ((measurable_of_finite (fun m => qVal k (enc₁ m i))).comp hm₁)
      exact (measurable_qIdx k).comp hsub
    exact hm₁.prodMk hm₂

/-- Union bound separating Stage-1 and Stage-2 error probabilities for `sicGaussianMACCode`. -/
private lemma sicGaussianMACCode_error_le (N : ℝ) (k : ℕ) {n M₁ M₂ : ℕ}
    (enc₁ : Fin M₁ → Fin n → Fin (qCard k)) (enc₂ : Fin M₂ → Fin n → Fin (qCard k))
    (dec₁ : (Fin n → Fin (qCard k)) → Fin M₁) (dec₂ : (Fin n → Fin (qCard k)) → Fin M₂)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    (gaussianMACErrorProb (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂) N m₁ m₂).toReal ≤
      (∑ y : Fin n → Fin (qCard k),
        if dec₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) +
      msgError (gChan N k) enc₂ dec₂ m₂ := by
  let E₁ : Set (Fin n → ℝ) :=
    {z | dec₁ (fun i => qIdx k (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i) + z i)) ≠ m₁}
  let E₂ : Set (Fin n → ℝ) :=
    {z | dec₂ (fun i => qIdx k (qVal k (enc₂ m₂ i) + z i)) ≠ m₂}
  have hsub : {z : Fin n → ℝ | (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).decoder
      ((sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).encoder₁ m₁ +
       (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).encoder₂ m₂ + z) ≠ (m₁, m₂)} ⊆ E₁ ∪ E₂ := by
    intro z hz
    simp only [Set.mem_ofPred_eq, sicGaussianMACCode, Pi.add_apply, ne_eq] at hz
    by_cases h1 : dec₁ (fun i => qIdx k (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i) + z i)) = m₁
    · right
      simp only [E₂, Set.mem_ofPred_eq, ne_eq]
      intro h2
      apply hz
      refine Prod.ext h1 ?_
      rw [h1]
      have hcancel : (fun i => qIdx k (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i) + z i -
          qVal k (enc₁ m₁ i))) = (fun i => qIdx k (qVal k (enc₂ m₂ i) + z i)) := by
        funext i; congr 1; ring
      rw [hcancel]
      exact h2
    · left; exact h1
  have hmeas : gaussianMACErrorProb (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂) N m₁ m₂ ≤
      awgnNoise n N E₁ + awgnNoise n N E₂ :=
    le_trans (measure_mono hsub) (measure_union_le E₁ E₂)
  have hreal : (gaussianMACErrorProb (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂) N m₁ m₂).toReal ≤
      (awgnNoise n N E₁).toReal + (awgnNoise n N E₂).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hmeas
  have hE1 : (awgnNoise n N E₁).toReal = ∑ y : Fin n → Fin (qCard k),
      if dec₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0 :=
    stage1_error_toReal N k n M₁ (enc₁ m₁) (enc₂ m₂) dec₁ m₁
  have hE2 : (awgnNoise n N E₂).toReal = msgError (gChan N k) enc₂ dec₂ m₂ := by
    have hq := quantCode_errorProb_toReal N (qVal k) (qIdx k) (measurable_qIdx k) enc₂ dec₂ m₂
    exact hq
  rw [hE1, hE2] at hreal
  exact hreal

/-- Expected-value existence of a quantized SIC Gaussian MAC codebook with small average error
    and few power-violating codewords in both encoders simultaneously. -/
private theorem exists_sic_codebook_err_add_viol_le {v₁ v₂ N P₁ P₂ : ℝ}
    (k n M₁' M₂' : ℕ) (hM₁' : 0 < M₁') (hM₂' : 0 < M₂') (ε₁ ε₂ : ℝ) :
    let W₁ := gInterfChan v₂ N k
    let W₂ := gChan N k
    let Q₁ := gIn v₁ k
    let Q₂ := gIn v₂ k
    let b : Fin (qCard k) → ℝ := fun i => qVal k i ^ 2
    ∃ (enc₁ : Fin M₁' → Fin n → Fin (qCard k)) (enc₂ : Fin M₂' → Fin n → Fin (qCard k))
      (dec₁ : (Fin n → Fin (qCard k)) → Fin M₁') (dec₂ : (Fin n → Fin (qCard k)) → Fin M₂'),
      (gaussianMACAvgError (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂) N).toReal +
        numViol b P₁ enc₁ / (M₁' : ℝ) + numViol b P₂ enc₂ / (M₂' : ℝ) ≤
      (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
      ((M₁' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) +
      (1 - ∑ xy ∈ jointTypicalSet (W₂.joint Q₂) n ε₂, (jointIidDist (W₂.joint Q₂) n).pmf xy) +
      ((M₂' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) +
      violProb Q₁ b P₁ n + violProb Q₂ b P₂ n := by
  classical
  dsimp only
  set W₁ := gInterfChan v₂ N k
  set W₂ := gChan N k
  set Q₁ := gIn v₁ k
  set Q₂ := gIn v₂ k
  set b : Fin (qCard k) → ℝ := fun i => qVal k i ^ 2
  set w₁ := codebookProb Q₁ n M₁'
  set w₂ := codebookProb Q₂ n M₂'
  let dec₁Of := fun enc₁ => jointTypicalDec (W₁.joint Q₁) n M₁' hM₁' ε₁ enc₁
  let dec₂Of := fun enc₂ => jointTypicalDec (W₂.joint Q₂) n M₂' hM₂' ε₂ enc₂
  have hM₁r : (0 : ℝ) < M₁' := Nat.cast_pos.mpr hM₁'
  have hM₂r : (0 : ℝ) < M₂' := Nat.cast_pos.mpr hM₂'
  have hM12r : (0 : ℝ) < ((M₁' * M₂' : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hM₁' hM₂')
  have hw₁_sum : ∑ enc₁, w₁ enc₁ = 1 := codebookProb_sum_one Q₁ n M₁'
  have hw₂_sum : ∑ enc₂, w₂ enc₂ = 1 := codebookProb_sum_one Q₂ n M₂'
  have hw₁_viol : ∑ enc₁, w₁ enc₁ * numViol b P₁ enc₁ = (M₁' : ℝ) * violProb Q₁ b P₁ n :=
    sum_codebookProb_numViol Q₁ b P₁ n M₁'
  have hw₂_viol : ∑ enc₂, w₂ enc₂ * numViol b P₂ enc₂ = (M₂' : ℝ) * violProb Q₂ b P₂ n :=
    sum_codebookProb_numViol Q₂ b P₂ n M₂'
  -- Bound Stage-1 expected error by `dmc_random_coding_expected_error_le W₁ Q₁`
  have hE1 : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
      ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ m₁ : Fin M₁', ∑ m₂ : Fin M₂',
        ∑ y : Fin n → Fin (qCard k),
          if dec₁Of enc₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) ≤
      (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
      ((M₁' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) := by
    have hinner : ∀ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
        ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ m₁ : Fin M₁', ∑ m₂ : Fin M₂',
          ∑ y : Fin n → Fin (qCard k),
            if dec₁Of enc₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
        w₁ enc₁ * dmcAvgError W₁ n M₁' enc₁ (dec₁Of enc₁) := by
      intro enc₁
      have hfactor : ∀ enc₂, (w₁ enc₁ * w₂ enc₂) *
          ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ m₁ : Fin M₁', ∑ m₂ : Fin M₂',
            ∑ y : Fin n → Fin (qCard k),
              if dec₁Of enc₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
          w₁ enc₁ * (1 / ((M₁' * M₂' : ℕ) : ℝ)) *
            ∑ m₁ : Fin M₁', ∑ m₂ : Fin M₂', ∑ y : Fin n → Fin (qCard k),
              if dec₁Of enc₁ y ≠ m₁ then
                w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0 := by
        intro enc₂
        have : ∀ m₁ m₂ y, w₂ enc₂ * (if dec₁Of enc₁ y ≠ m₁ then
              ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
            if dec₁Of enc₁ y ≠ m₁ then
              w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0 := by
          intro m₁ m₂ y; split_ifs <;> ring
        have hpush : (w₁ enc₁ * w₂ enc₂) * (1 / ((M₁' * M₂' : ℕ) : ℝ)) =
            (w₁ enc₁ * (1 / ((M₁' * M₂' : ℕ) : ℝ))) * w₂ enc₂ := by ring
        rw [← mul_assoc, hpush, mul_assoc, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m₂ _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => this m₁ m₂ y
      simp_rw [hfactor, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have hswap : ∀ m₁ : Fin M₁',
          ∑ enc₂, ∑ m₂ : Fin M₂', ∑ y : Fin n → Fin (qCard k),
            (if dec₁Of enc₁ y ≠ m₁ then
              w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
          (M₂' : ℝ) * ∑ y : Fin n → Fin (qCard k),
            if dec₁Of enc₁ y ≠ m₁ then (W₁.power n).trans (enc₁ m₁) y else 0 := by
        intro m₁
        rw [Finset.sum_comm]
        have hm₂ : ∀ m₂ : Fin M₂',
            ∑ enc₂, ∑ y : Fin n → Fin (qCard k),
              (if dec₁Of enc₁ y ≠ m₁ then
                w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
            ∑ y : Fin n → Fin (qCard k),
              if dec₁Of enc₁ y ≠ m₁ then (W₁.power n).trans (enc₁ m₁) y else 0 := by
          intro m₂
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases hy : dec₁Of enc₁ y ≠ m₁
          · have hte : ∀ enc₂, (if dec₁Of enc₁ y ≠ m₁ then
                w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) =
                w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y :=
              fun _ => ite_eq_left_iff.mpr fun h => absurd hy h
            rw [Finset.sum_congr rfl fun enc₂ _ => hte enc₂,
              ite_eq_left_iff.mpr fun h => absurd hy h]
            exact sum_codebookProb_gMacChan v₂ N k n M₂' (enc₁ m₁) y m₂
          · have hte : ∀ enc₂, (if dec₁Of enc₁ y ≠ m₁ then
                w₂ enc₂ * ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) = 0 :=
              fun _ => ite_eq_right_iff.mpr fun h => absurd h hy
            rw [Finset.sum_congr rfl fun enc₂ _ => hte enc₂, Finset.sum_const_zero,
              ite_eq_right_iff.mpr fun h => absurd h hy]
        simp_rw [hm₂, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [hswap, ← Finset.mul_sum]
      rw [dmcAvgError_eq_msgError W₁ hM₁' enc₁ (dec₁Of enc₁)]
      unfold msgError
      push_cast
      field_simp [hM₁r.ne', hM₂r.ne']
    simp_rw [hinner]
    have hexp : ∑ enc₁, w₁ enc₁ * dmcAvgError W₁ n M₁' enc₁ (dec₁Of enc₁) ≤
        (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
        ((M₁' - 1 : ℕ) : ℝ) *
          (∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁,
            ((iidDist (W₁.joint Q₁).fst n).prod (iidDist (W₁.joint Q₁).snd n)).pmf xy) :=
      dmc_random_coding_expected_error_le W₁ Q₁ n M₁' hM₁' ε₁
    have hindep : ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁,
          ((iidDist (W₁.joint Q₁).fst n).prod (iidDist (W₁.joint Q₁).snd n)).pmf xy ≤
        (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) :=
      jointTypicalSet_indep_prob_le (W₁.joint Q₁) n ε₁
    have hmul := mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg (M₁' - 1))
    linarith
  -- Bound Stage-2 expected error by `dmc_random_coding_expected_error_le W₂ Q₂`
  have hE2 : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
      ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁', ∑ m₂ : Fin M₂',
        msgError W₂ enc₂ (dec₂Of enc₂) m₂) ≤
      (1 - ∑ xy ∈ jointTypicalSet (W₂.joint Q₂) n ε₂, (jointIidDist (W₂.joint Q₂) n).pmf xy) +
      ((M₂' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) := by
    have hsimp : ∀ enc₁ enc₂, (w₁ enc₁ * w₂ enc₂) *
        ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁', ∑ m₂ : Fin M₂',
          msgError W₂ enc₂ (dec₂Of enc₂) m₂) =
        w₁ enc₁ * (w₂ enc₂ * dmcAvgError W₂ n M₂' enc₂ (dec₂Of enc₂)) := by
      intro enc₁ enc₂
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        dmcAvgError_eq_msgError W₂ hM₂' enc₂ (dec₂Of enc₂)]
      push_cast
      field_simp [hM₁r.ne', hM₂r.ne']
    simp_rw [hsimp, ← Finset.mul_sum, ← Finset.sum_mul, hw₁_sum, one_mul]
    have hexp : ∑ enc₂, w₂ enc₂ * dmcAvgError W₂ n M₂' enc₂ (dec₂Of enc₂) ≤
        (1 - ∑ xy ∈ jointTypicalSet (W₂.joint Q₂) n ε₂, (jointIidDist (W₂.joint Q₂) n).pmf xy) +
        ((M₂' - 1 : ℕ) : ℝ) *
          (∑ xy ∈ jointTypicalSet (W₂.joint Q₂) n ε₂,
            ((iidDist (W₂.joint Q₂).fst n).prod (iidDist (W₂.joint Q₂).snd n)).pmf xy) :=
      dmc_random_coding_expected_error_le W₂ Q₂ n M₂' hM₂' ε₂
    have hindep : ∑ xy ∈ jointTypicalSet (W₂.joint Q₂) n ε₂,
          ((iidDist (W₂.joint Q₂).fst n).prod (iidDist (W₂.joint Q₂).snd n)).pmf xy ≤
        (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) :=
      jointTypicalSet_indep_prob_le (W₂.joint Q₂) n ε₂
    have hmul := mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg (M₂' - 1))
    linarith
  -- Expected power violation fractions
  have hV1 : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) * (numViol b P₁ enc₁ / (M₁' : ℝ)) =
      violProb Q₁ b P₁ n := by
    have h1 : ∀ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) * (numViol b P₁ enc₁ / (M₁' : ℝ)) =
        w₁ enc₁ * (numViol b P₁ enc₁ / (M₁' : ℝ)) := fun enc₁ => by
      have : ∀ enc₂, (w₁ enc₁ * w₂ enc₂) * (numViol b P₁ enc₁ / (M₁' : ℝ)) =
          w₂ enc₂ * (w₁ enc₁ * (numViol b P₁ enc₁ / (M₁' : ℝ))) := fun _ => by ring
      simp_rw [this, ← Finset.sum_mul, hw₂_sum, one_mul]
    simp_rw [h1, mul_div_assoc', ← Finset.sum_div, hw₁_viol]
    field_simp [hM₁r.ne']
  have hV2 : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) * (numViol b P₂ enc₂ / (M₂' : ℝ)) =
      violProb Q₂ b P₂ n := by
    rw [Finset.sum_comm]
    have h1 : ∀ enc₂, ∑ enc₁, (w₁ enc₁ * w₂ enc₂) * (numViol b P₂ enc₂ / (M₂' : ℝ)) =
        w₂ enc₂ * (numViol b P₂ enc₂ / (M₂' : ℝ)) := fun enc₂ => by
      have : ∀ enc₁, (w₁ enc₁ * w₂ enc₂) * (numViol b P₂ enc₂ / (M₂' : ℝ)) =
          w₁ enc₁ * (w₂ enc₂ * (numViol b P₂ enc₂ / (M₂' : ℝ))) := fun _ => by ring
      simp_rw [this, ← Finset.sum_mul, hw₁_sum, one_mul]
    simp_rw [h1, mul_div_assoc', ← Finset.sum_div, hw₂_viol]
    field_simp [hM₂r.ne']
  -- Combine via `sicGaussianMACCode_error_le` and pick the best deterministic pair `(enc₁, enc₂)`
  set RHS :=
    (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
    ((M₁' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) +
    (1 - ∑ xy ∈ jointTypicalSet (W₂.joint Q₂) n ε₂, (jointIidDist (W₂.joint Q₂) n).pmf xy) +
    ((M₂' - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) +
    violProb Q₁ b P₁ n + violProb Q₂ b P₂ n
  have havg_bound : ∀ enc₁ enc₂,
      (gaussianMACAvgError (sicGaussianMACCode k enc₁ enc₂ (dec₁Of enc₁) (dec₂Of enc₂)) N).toReal ≤
        ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ m₁ : Fin M₁', ∑ m₂ : Fin M₂',
          ∑ y : Fin n → Fin (qCard k),
            if dec₁Of enc₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) +
        ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁', ∑ m₂ : Fin M₂',
          msgError W₂ enc₂ (dec₂Of enc₂) m₂) := by
    intro enc₁ enc₂
    rw [gaussianMACAvgError_toReal, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m₁ _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun m₂ _ =>
      sicGaussianMACCode_error_le N k enc₁ enc₂ (dec₁Of enc₁) (dec₂Of enc₂) m₁ m₂
  let w : ((Fin M₁' → Fin n → Fin (qCard k)) × (Fin M₂' → Fin n → Fin (qCard k))) → ℝ :=
    fun p => w₁ p.1 * w₂ p.2
  have hw0 : ∀ p, 0 ≤ w p := fun p =>
    mul_nonneg (codebookProb_nonneg Q₁ n M₁' p.1) (codebookProb_nonneg Q₂ n M₂' p.2)
  have hw1 : ∑ p, w p = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [w, ← Finset.mul_sum, hw₂_sum, mul_one, hw₁_sum]
  have htot : ∑ p : (Fin M₁' → Fin n → Fin (qCard k)) × (Fin M₂' → Fin n → Fin (qCard k)),
      w p * ((gaussianMACAvgError (sicGaussianMACCode k p.1 p.2 (dec₁Of p.1) (dec₂Of p.2)) N).toReal +
        numViol b P₁ p.1 / (M₁' : ℝ) + numViol b P₂ p.2 / (M₂' : ℝ)) ≤ RHS := by
    rw [Fintype.sum_prod_type]
    have hstep : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
        ((gaussianMACAvgError (sicGaussianMACCode k enc₁ enc₂ (dec₁Of enc₁) (dec₂Of enc₂)) N).toReal +
          numViol b P₁ enc₁ / (M₁' : ℝ) + numViol b P₂ enc₂ / (M₂' : ℝ)) ≤
        ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
          (((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ m₁ : Fin M₁', ∑ m₂ : Fin M₂',
            ∑ y : Fin n → Fin (qCard k),
              if dec₁Of enc₁ y ≠ m₁ then ((gMacChan N k).power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0) +
           ((1 / ((M₁' * M₂' : ℕ) : ℝ)) * ∑ _m₁ : Fin M₁', ∑ m₂ : Fin M₂',
            msgError W₂ enc₂ (dec₂Of enc₂) m₂) +
           numViol b P₁ enc₁ / (M₁' : ℝ) + numViol b P₂ enc₂ / (M₂' : ℝ)) :=
      Finset.sum_le_sum fun enc₁ _ => Finset.sum_le_sum fun enc₂ _ =>
        mul_le_mul_of_nonneg_left (by linarith [havg_bound enc₁ enc₂]) (hw0 (enc₁, enc₂))
    refine le_trans hstep ?_
    simp_rw [mul_add, Finset.sum_add_distrib]
    exact le_trans (add_le_add (add_le_add (add_le_add hE1 hE2) (le_of_eq hV1)) (le_of_eq hV2))
      (le_of_eq (by dsimp only [RHS]; ring))
  obtain ⟨⟨enc₁, enc₂⟩, hbest⟩ := exists_le_of_weighted_sum_le_cc w
    (fun p => (gaussianMACAvgError (sicGaussianMACCode k p.1 p.2 (dec₁Of p.1) (dec₂Of p.2)) N).toReal +
      numViol b P₁ p.1 / (M₁' : ℝ) + numViol b P₂ p.2 / (M₂' : ℝ))
    RHS hw0 hw1 htot
  exact ⟨enc₁, enc₂, dec₁Of enc₁, dec₂Of enc₂, hbest⟩

/-- **Product-codebook expurgation**: from a `(n, 2M₁, 2M₂)` Gaussian MAC code whose average error
    plus both violator fractions is at most `β ≤ min(δ/4, 1/2)`, extract a `(n, M₁, M₂)` subcode
    in which EVERY codeword of both users satisfies its power constraint and `avgErr ≤ δ`. -/
private theorem exists_mac_subcode_of_err_add_viol_le {n M₁ M₂ : ℕ} {N P₁ P₂ β δ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hδ : 0 < δ)
    (C : GaussianMACCode n (2 * M₁) (2 * M₂))
    (hviol : (gaussianMACAvgError C N).toReal +
      (∑ m₁ : Fin (2 * M₁), if (n : ℝ) * P₁ < ∑ i, (C.encoder₁ m₁ i) ^ 2 then (1 : ℝ) else 0) /
        ((2 * M₁ : ℕ) : ℝ) +
      (∑ m₂ : Fin (2 * M₂), if (n : ℝ) * P₂ < ∑ i, (C.encoder₂ m₂ i) ^ 2 then (1 : ℝ) else 0) /
        ((2 * M₂ : ℕ) : ℝ) ≤ β)
    (hβδ : 4 * β ≤ δ) (hβ1 : 2 * β ≤ 1) :
    ∃ C' : GaussianMACCode n M₁ M₂,
      C'.SatisfiesPower P₁ P₂ ∧ gaussianMACAvgError C' N ≤ ENNReal.ofReal δ := by
  classical
  have h2M₁ : (0 : ℝ) < ((2 * M₁ : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * M₁ by omega)
  have h2M₂ : (0 : ℝ) < ((2 * M₂ : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * M₂ by omega)
  let V₁ : ℝ := ∑ m₁ : Fin (2 * M₁), if (n : ℝ) * P₁ < ∑ i, (C.encoder₁ m₁ i) ^ 2 then 1 else 0
  let V₂ : ℝ := ∑ m₂ : Fin (2 * M₂), if (n : ℝ) * P₂ < ∑ i, (C.encoder₂ m₂ i) ^ 2 then 1 else 0
  have hV₁0 : 0 ≤ V₁ := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hV₂0 : 0 ≤ V₂ := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have herr0 : 0 ≤ (gaussianMACAvgError C N).toReal := ENNReal.toReal_nonneg
  have herr_le : (gaussianMACAvgError C N).toReal ≤ β := by
    have := div_nonneg hV₁0 h2M₁.le
    have := div_nonneg hV₂0 h2M₂.le
    linarith
  -- Power-valid subsets `G₁`, `G₂` have size `≥ M₁`, `≥ M₂`
  let B₁ : Finset (Fin (2 * M₁)) := Finset.univ.filter fun m₁ => (n : ℝ) * P₁ < ∑ i, (C.encoder₁ m₁ i) ^ 2
  let B₂ : Finset (Fin (2 * M₂)) := Finset.univ.filter fun m₂ => (n : ℝ) * P₂ < ∑ i, (C.encoder₂ m₂ i) ^ 2
  let G₁ : Finset (Fin (2 * M₁)) := Finset.univ.filter fun m₁ => ∑ i, (C.encoder₁ m₁ i) ^ 2 ≤ (n : ℝ) * P₁
  let G₂ : Finset (Fin (2 * M₂)) := Finset.univ.filter fun m₂ => ∑ i, (C.encoder₂ m₂ i) ^ 2 ≤ (n : ℝ) * P₂
  have hG₁ : M₁ ≤ G₁.card := by
    have hV1_eq : (B₁.card : ℝ) = V₁ := by
      dsimp only [B₁, V₁]
      rw [Finset.card_filter]; push_cast; rfl
    have hB1 : (B₁.card : ℝ) ≤ M₁ := by
      have hdiv : V₁ / ((2 * M₁ : ℕ) : ℝ) ≤ β := by
        have := div_nonneg hV₂0 h2M₂.le; linarith
      rw [div_le_iff₀ h2M₁] at hdiv
      rw [hV1_eq]
      push_cast at hdiv
      nlinarith [(Nat.cast_nonneg M₁ : (0 : ℝ) ≤ M₁)]
    have hcomp : G₁ᶜ = B₁ := by ext m₁; simp [G₁, B₁, not_le]
    have htot : G₁.card + B₁.card = 2 * M₁ := by
      rw [← hcomp, Finset.card_add_card_compl, Fintype.card_fin]
    have : (G₁.card : ℝ) + B₁.card = 2 * M₁ := by exact_mod_cast htot
    exact_mod_cast (by linarith : (M₁ : ℝ) ≤ G₁.card)
  have hG₂ : M₂ ≤ G₂.card := by
    have hV2_eq : (B₂.card : ℝ) = V₂ := by
      dsimp only [B₂, V₂]
      rw [Finset.card_filter]; push_cast; rfl
    have hB2 : (B₂.card : ℝ) ≤ M₂ := by
      have hdiv : V₂ / ((2 * M₂ : ℕ) : ℝ) ≤ β := by
        have := div_nonneg hV₁0 h2M₁.le; linarith
      rw [div_le_iff₀ h2M₂] at hdiv
      rw [hV2_eq]
      push_cast at hdiv
      nlinarith [(Nat.cast_nonneg M₂ : (0 : ℝ) ≤ M₂)]
    have hcomp : G₂ᶜ = B₂ := by ext m₂; simp [G₂, B₂, not_le]
    have htot : G₂.card + B₂.card = 2 * M₂ := by
      rw [← hcomp, Finset.card_add_card_compl, Fintype.card_fin]
    have : (G₂.card : ℝ) + B₂.card = 2 * M₂ := by exact_mod_cast htot
    exact_mod_cast (by linarith : (M₂ : ℝ) ≤ G₂.card)
  let ι₁ : Fin M₁ → Fin (2 * M₁) := fun m₁ => G₁.orderEmbOfFin rfl (Fin.castLE hG₁ m₁)
  let ι₂ : Fin M₂ → Fin (2 * M₂) := fun m₂ => G₂.orderEmbOfFin rfl (Fin.castLE hG₂ m₂)
  have hι₁_mem : ∀ m₁, ι₁ m₁ ∈ G₁ := fun m₁ => Finset.orderEmbOfFin_mem G₁ rfl _
  have hι₂_mem : ∀ m₂, ι₂ m₂ ∈ G₂ := fun m₂ => Finset.orderEmbOfFin_mem G₂ rfl _
  have hι₁_inj : Function.Injective ι₁ := fun a b h =>
    Fin.castLE_injective hG₁ ((G₁.orderEmbOfFin rfl).injective h)
  have hι₂_inj : Function.Injective ι₂ := fun a b h =>
    Fin.castLE_injective hG₂ ((G₂.orderEmbOfFin rfl).injective h)
  let inv₁ : Fin (2 * M₁) → Fin M₁ := fun k =>
    if h : ∃ m, ι₁ m = k then Classical.choose h else ⟨0, hM₁⟩
  let inv₂ : Fin (2 * M₂) → Fin M₂ := fun k =>
    if h : ∃ m, ι₂ m = k then Classical.choose h else ⟨0, hM₂⟩
  have hinv₁ : ∀ m₁, inv₁ (ι₁ m₁) = m₁ := fun m₁ => by
    have hex : ∃ m, ι₁ m = ι₁ m₁ := ⟨m₁, rfl⟩
    simp only [inv₁, hex, ↓reduceDIte]
    exact hι₁_inj (Classical.choose_spec hex)
  have hinv₂ : ∀ m₂, inv₂ (ι₂ m₂) = m₂ := fun m₂ => by
    have hex : ∃ m, ι₂ m = ι₂ m₂ := ⟨m₂, rfl⟩
    simp only [inv₂, hex, ↓reduceDIte]
    exact hι₂_inj (Classical.choose_spec hex)
  let C' : GaussianMACCode n M₁ M₂ :=
    { encoder₁ := fun m₁ => C.encoder₁ (ι₁ m₁)
      encoder₂ := fun m₂ => C.encoder₂ (ι₂ m₂)
      decoder := fun y => (inv₁ (C.decoder y).1, inv₂ (C.decoder y).2)
      measurable_decoder := (measurable_of_finite fun p : Fin (2 * M₁) × Fin (2 * M₂) =>
        (inv₁ p.1, inv₂ p.2)).comp C.measurable_decoder }
  refine ⟨C', ⟨fun m₁ => (Finset.mem_filter.mp (hι₁_mem m₁)).2,
              fun m₂ => (Finset.mem_filter.mp (hι₂_mem m₂)).2⟩, ?_⟩
  rw [ENNReal.le_ofReal_iff_toReal_le (gaussianMACAvgError_ne_top hM₁ hM₂ C' N) hδ.le]
  have herr_pt : ∀ m₁ m₂, gaussianMACErrorProb C' N m₁ m₂ ≤
      gaussianMACErrorProb C N (ι₁ m₁) (ι₂ m₂) := by
    intro m₁ m₂
    refine measure_mono fun z hz => ?_
    simp only [Set.mem_ofPred_eq, C', ne_eq] at hz ⊢
    intro heq
    apply hz
    rw [heq, hinv₁, hinv₂]
  have hsum_le : ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C' N m₁ m₂).toReal ≤
      ∑ k₁ : Fin (2 * M₁), ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N k₁ k₂).toReal := by
    calc ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C' N m₁ m₂).toReal
        ≤ ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C N (ι₁ m₁) (ι₂ m₂)).toReal :=
          Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
            ENNReal.toReal_mono
              (ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C N _ _))
              (herr_pt m₁ m₂)
      _ ≤ ∑ m₁ : Fin M₁, ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N (ι₁ m₁) k₂).toReal := by
          refine Finset.sum_le_sum fun m₁ _ => ?_
          calc ∑ m₂ : Fin M₂, (gaussianMACErrorProb C N (ι₁ m₁) (ι₂ m₂)).toReal
              = ∑ k₂ ∈ Finset.univ.image ι₂, (gaussianMACErrorProb C N (ι₁ m₁) k₂).toReal :=
                (Finset.sum_image (f := fun k₂ => (gaussianMACErrorProb C N (ι₁ m₁) k₂).toReal)
                  (fun a _ b _ h => hι₂_inj h)).symm
            _ ≤ ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N (ι₁ m₁) k₂).toReal :=
                Finset.sum_le_univ_sum_of_nonneg fun _ => ENNReal.toReal_nonneg
      _ ≤ ∑ k₁ : Fin (2 * M₁), ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N k₁ k₂).toReal := by
          calc ∑ m₁ : Fin M₁, ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N (ι₁ m₁) k₂).toReal
              = ∑ k₁ ∈ Finset.univ.image ι₁,
                  ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N k₁ k₂).toReal :=
                (Finset.sum_image (f := fun k₁ =>
                  ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N k₁ k₂).toReal)
                  (fun a _ b _ h => hι₁_inj h)).symm
            _ ≤ ∑ k₁ : Fin (2 * M₁), ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N k₁ k₂).toReal :=
                Finset.sum_le_univ_sum_of_nonneg fun _ =>
                  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  rw [gaussianMACAvgError_toReal]
  have h4 : (1 / ((M₁ * M₂ : ℕ) : ℝ)) = 4 * (1 / (((2 * M₁) * (2 * M₂) : ℕ) : ℝ)) := by
    have hM₁r : (0 : ℝ) < M₁ := Nat.cast_pos.mpr hM₁
    have hM₂r : (0 : ℝ) < M₂ := Nat.cast_pos.mpr hM₂
    push_cast; field_simp; ring
  rw [h4, mul_assoc]
  have hC := gaussianMACAvgError_toReal C N
  have hbound : (1 / (((2 * M₁) * (2 * M₂) : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C' N m₁ m₂).toReal ≤ β := by
    calc (1 / (((2 * M₁) * (2 * M₂) : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C' N m₁ m₂).toReal
        ≤ (1 / (((2 * M₁) * (2 * M₂) : ℕ) : ℝ)) *
            ∑ k₁ : Fin (2 * M₁), ∑ k₂ : Fin (2 * M₂), (gaussianMACErrorProb C N k₁ k₂).toReal :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (gaussianMACAvgError C N).toReal := hC.symm
      _ ≤ β := herr_le
  linarith

/-- **Corner-point achievability for the two-user Gaussian MAC (via SIC)**:
    whenever `P₁ > 0`, `P₂ > 0`, `N > 0`, `0 ≤ R₁ < ½ log₂(1 + P₁/(P₂ + N))`, and
    `0 ≤ R₂ < ½ log₂(1 + P₂/N)`, the pair `(R₁, R₂)` is operationally achievable. -/
theorem gaussianMAC_corner_achievable {P₁ P₂ N R₁ R₂ : ℝ}
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) (hN : 0 < N)
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (hR₁ : R₁ < awgnCapacityFormula P₁ (P₂ + N))
    (hR₂ : R₂ < awgnCapacityFormula P₂ N) :
    IsGaussianMACAchievable P₁ P₂ N R₁ R₂ := by
  -- Step 1: pick strictly smaller input powers `0 < v₁ < P₁`, `0 < v₂ < P₂` preserving strict bounds
  have hcont₂ : ContinuousAt (fun w => awgnCapacityFormula w N) P₂ := by
    unfold awgnCapacityFormula log2
    have h1 : (1 + P₂ / N) ≠ 0 := by positivity
    exact (((continuousAt_const.add (continuousAt_id.div_const N)).log h1).div_const _).const_mul _
  have hev₂ : ∀ᶠ v₂ in 𝓝[<] P₂, R₂ < awgnCapacityFormula v₂ N ∧ v₂ ∈ Set.Ioo 0 P₂ :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont₂.eventually (lt_mem_nhds hR₂))).and
      (Ioo_mem_nhdsLT hP₂)
  obtain ⟨v₂, hv₂R₂, hv₂0, hv₂P₂⟩ := hev₂.exists
  have hR₁_v₂ : R₁ < awgnCapacityFormula P₁ (v₂ + N) := by
    refine lt_of_lt_of_le hR₁ ?_
    unfold awgnCapacityFormula log2
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hdiv : P₁ / (P₂ + N) ≤ P₁ / (v₂ + N) :=
      div_le_div_of_nonneg_left hP₁.le (by linarith) (by linarith)
    gcongr
  have hcont₁ : ContinuousAt (fun w => awgnCapacityFormula w (v₂ + N)) P₁ := by
    unfold awgnCapacityFormula log2
    have h1 : (1 + P₁ / (v₂ + N)) ≠ 0 := by positivity
    exact (((continuousAt_const.add (continuousAt_id.div_const (v₂ + N))).log h1).div_const _).const_mul _
  have hev₁ : ∀ᶠ v₁ in 𝓝[<] P₁, R₁ < awgnCapacityFormula v₁ (v₂ + N) ∧ v₁ ∈ Set.Ioo 0 P₁ :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont₁.eventually (lt_mem_nhds hR₁_v₂))).and
      (Ioo_mem_nhdsLT hP₁)
  obtain ⟨v₁, hv₁R₁, hv₁0, hv₁P₁⟩ := hev₁.exists
  -- Step 2: pick a single quantization level `k` satisfying both MI bounds and both power bounds
  have hev_k := ((eventually_interf_mutualInfo_gt hv₁0 hv₂0 hN hv₁R₁).and
      (eventually_single_mutualInfo_gt hv₂0 hN hv₂R₂)).and
    (((tendsto_order.1 (tendsto_power hv₁0)).2 P₁ hv₁P₁).and
      ((tendsto_order.1 (tendsto_power hv₂0)).2 P₂ hv₂P₂))
  obtain ⟨k, ⟨hI₁, hI₂⟩, ⟨hpow₁, hpow₂⟩⟩ := hev_k.exists
  rw [← power_gIn_eq v₁ k] at hpow₁
  rw [← power_gIn_eq v₂ k] at hpow₂
  -- Step 3: asymptotics using `exists_sic_codebook_err_add_viol_le` + product expurgation
  refine ⟨hR₁0, hR₂0, fun δ hδ => ?_⟩
  set W₁ := gInterfChan v₂ N k
  set W₂ := gChan N k
  set Q₁ := gIn v₁ k
  set Q₂ := gIn v₂ k
  set b : Fin (qCard k) → ℝ := fun i => qVal k i ^ 2
  set ε₁ : ℝ := (W₁.mutualInfo Q₁ - R₁) / 4
  set ε₂ : ℝ := (W₂.mutualInfo Q₂ - R₂) / 4
  have hε₁ : 0 < ε₁ := by dsimp only [ε₁]; linarith
  have hε₂ : 0 < ε₂ := by dsimp only [ε₂]; linarith
  set t : ℝ := min (δ / 4) (1 / 2) / 6 with ht_def
  have ht : 0 < t := by rw [ht_def]; have := lt_min (by linarith : 0 < δ / 4) (by norm_num : (0 : ℝ) < 1 / 2); positivity
  obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one (W₁.joint Q₁) hε₁ ht
  obtain ⟨N₂, hN₂⟩ := joint_aep_prob_tendsto_one (W₂.joint Q₂) hε₂ ht
  have hev_n : ∀ᶠ n : ℕ in atTop,
      (N₁ ≤ n ∧ N₂ ≤ n) ∧
      ((2 : ℝ) ^ (-((n : ℝ) * ε₁)) ≤ t / 2 ∧ (2 : ℝ) ^ (-((n : ℝ) * ε₂)) ≤ t / 2) ∧
      (violProb Q₁ b P₁ n ≤ t ∧ violProb Q₂ b P₂ n ≤ t) :=
    ((eventually_ge_atTop N₁).and (eventually_ge_atTop N₂)).and
      (((eventually_two_rpow_neg_le hε₁ (by linarith)).and
        (eventually_two_rpow_neg_le hε₂ (by linarith))).and
      ((violProb_eventually_le Q₁ b hpow₁ ht).and (violProb_eventually_le Q₂ b hpow₂ ht)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev_n
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨⟨hn1, hn2⟩, ⟨hexp1, hexp2⟩, ⟨hv1, hv2⟩⟩ := hn₀ n hn
  set M₁ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊
  set M₂ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  obtain ⟨enc₁, enc₂, dec₁, dec₂, hbound⟩ :=
    exists_sic_codebook_err_add_viol_le (v₁ := v₁) (v₂ := v₂) (N := N) (P₁ := P₁) (P₂ := P₂)
      k n (2 * M₁) (2 * M₂) (by omega) (by omega) ε₁ ε₂
  have hM_le : ∀ (R : ℝ), 0 ≤ R →
      (((2 * max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ - 1 : ℕ)) : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R) := by
    intro R hR0
    have hpowR : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hle : ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
      rcases le_total 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ with h | h
      · rw [max_eq_right h]; exact Nat.floor_le (by positivity)
      · rw [max_eq_left h]; push_cast; exact hpowR
    have hsub : ((2 * max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ - 1 : ℕ) : ℝ) ≤
        ((2 * max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    rw [Nat.cast_mul, Nat.cast_ofNat] at hsub
    linarith
  have hterm2 : (((2 * M₁ - 1 : ℕ)) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) ≤ t := by
    have hprod : (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) =
        (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₁]; ring
    calc (((2 * M₁ - 1 : ℕ)) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁)))
        ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) :=
          mul_le_mul_of_nonneg_right (hM_le R₁ hR₁0) (by positivity)
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := by rw [mul_assoc, hprod]
      _ ≤ t := by linarith
  have hterm4 : (((2 * M₂ - 1 : ℕ)) : ℝ) *
      (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) ≤ t := by
    have hprod : (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) =
        (2 : ℝ) ^ (-((n : ℝ) * ε₂)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₂]; ring
    calc (((2 * M₂ - 1 : ℕ)) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂)))
        ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (W₂.mutualInfo Q₂ - 3 * ε₂))) :=
          mul_le_mul_of_nonneg_right (hM_le R₂ hR₂0) (by positivity)
      _ = 2 * (2 : ℝ) ^ (-((n : ℝ) * ε₂)) := by rw [mul_assoc, hprod]
      _ ≤ t := by linarith
  have haep1 := hN₁ n hn1
  have haep2 := hN₂ n hn2
  have h6t : (gaussianMACAvgError (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂) N).toReal +
      (∑ m₁ : Fin (2 * M₁), if (n : ℝ) * P₁ < ∑ i, ((sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).encoder₁ m₁ i) ^ 2 then (1 : ℝ) else 0) /
        ((2 * M₁ : ℕ) : ℝ) +
      (∑ m₂ : Fin (2 * M₂), if (n : ℝ) * P₂ < ∑ i, ((sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).encoder₂ m₂ i) ^ 2 then (1 : ℝ) else 0) /
        ((2 * M₂ : ℕ) : ℝ) ≤ 6 * t := by
    have hv1_eq : (∑ m₁ : Fin (2 * M₁),
        if (n : ℝ) * P₁ < ∑ i, ((sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).encoder₁ m₁ i) ^ 2 then (1 : ℝ) else 0) =
        numViol b P₁ enc₁ := by
      unfold numViol CostViol
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only [sicGaussianMACCode, b]
      by_cases hlt : (n : ℝ) * P₁ < ∑ i, qVal k (enc₁ m i) ^ 2 <;> simp [hlt]
    have hv2_eq : (∑ m₂ : Fin (2 * M₂),
        if (n : ℝ) * P₂ < ∑ i, ((sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂).encoder₂ m₂ i) ^ 2 then (1 : ℝ) else 0) =
        numViol b P₂ enc₂ := by
      unfold numViol CostViol
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp only [sicGaussianMACCode, b]
      by_cases hlt : (n : ℝ) * P₂ < ∑ i, qVal k (enc₂ m i) ^ 2 <;> simp [hlt]
    rw [hv1_eq, hv2_eq]
    linarith
  have hβδ : 4 * (6 * t) ≤ δ := by
    have : 6 * t ≤ δ / 4 := by rw [ht_def]; linarith [min_le_left (δ / 4) (1 / 2 : ℝ)]
    linarith
  have hβ1 : 2 * (6 * t) ≤ 1 := by
    have : 6 * t ≤ 1 / 2 := by rw [ht_def]; linarith [min_le_right (δ / 4) (1 / 2 : ℝ)]
    linarith
  exact exists_mac_subcode_of_err_add_viol_le hM₁ hM₂ hδ
    (sicGaussianMACCode k enc₁ enc₂ dec₁ dec₂) h6t hβδ hβ1

end CornerAchievability

/-! ### 5. Time-Sharing Convexity & Exact Capacity Region Theorem -/

section TimeSharingAndExactRegion

/-- Cyclic-shift zero-loss subcode extraction: from any `(n, K₁, K₂)` Gaussian MAC code with
    `1 ≤ M₁ ≤ K₁` and `1 ≤ M₂ ≤ K₂`, extract a `(n, M₁, M₂)` subcode preserving per-codeword
    power constraints with average error `≤` the original average error. -/
private theorem exists_mac_subcode_of_le {n K₁ K₂ M₁ M₂ : ℕ} {N P₁ P₂ : ℝ}
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hMK₁ : M₁ ≤ K₁) (hMK₂ : M₂ ≤ K₂)
    (C : GaussianMACCode n K₁ K₂) (hpow : C.SatisfiesPower P₁ P₂) :
    ∃ C' : GaussianMACCode n M₁ M₂,
      C'.SatisfiesPower P₁ P₂ ∧ gaussianMACAvgError C' N ≤ gaussianMACAvgError C N := by
  classical
  have hK₁ : 0 < K₁ := by omega
  have hK₂ : 0 < K₂ := by omega
  let emb₁ : Fin K₁ → Fin M₁ → Fin K₁ := fun s m => ⟨(s.val + m.val) % K₁, Nat.mod_lt _ hK₁⟩
  let emb₂ : Fin K₂ → Fin M₂ → Fin K₂ := fun s m => ⟨(s.val + m.val) % K₂, Nat.mod_lt _ hK₂⟩
  have hmod_cases : ∀ {K x y : ℕ}, x < K → y < K →
      (x + y) % K = if x + y < K then x + y else x + y - K := by
    intro K x y hx hy
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hemb₁_inj : ∀ s, Function.Injective (emb₁ s) := by
    intro s a b h
    simp only [emb₁, Fin.mk.injEq] at h
    have ha : a.val < K₁ := lt_of_lt_of_le a.isLt hMK₁
    have hb : b.val < K₁ := lt_of_lt_of_le b.isLt hMK₁
    rw [hmod_cases s.isLt ha, hmod_cases s.isLt hb] at h
    ext; split_ifs at h <;> omega
  have hemb₂_inj : ∀ s, Function.Injective (emb₂ s) := by
    intro s a b h
    simp only [emb₂, Fin.mk.injEq] at h
    have ha : a.val < K₂ := lt_of_lt_of_le a.isLt hMK₂
    have hb : b.val < K₂ := lt_of_lt_of_le b.isLt hMK₂
    rw [hmod_cases s.isLt ha, hmod_cases s.isLt hb] at h
    ext; split_ifs at h <;> omega
  have hshift_left : ∀ {K s m : ℕ}, s < K → m < K → ((s + m) % K + K - m) % K = s := by
    intro K s m hs hm
    rw [hmod_cases hs hm]
    split_ifs with hlt
    · have : s + m + K - m = s + K := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hs]
    · have : s + m - K + K - m = s := by omega
      rw [this, Nat.mod_eq_of_lt hs]
  have hshift_right : ∀ {K k m : ℕ}, k < K → m < K → ((k + K - m) % K + m) % K = k := by
    intro K k m hk hm
    by_cases hmk : m ≤ k
    · have h1 : (k + K - m) % K = k - m := by
        have : k + K - m = (k - m) + K := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1, show k - m + m = k by omega, Nat.mod_eq_of_lt hk]
    · have h1 : (k + K - m) % K = k + K - m := Nat.mod_eq_of_lt (by omega)
      rw [h1, show k + K - m + m = k + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  -- For fixed `m`, `s ↦ emb s m` is a bijection on `Fin K`
  let shiftEquiv₁ : Fin M₁ → (Fin K₁ ≃ Fin K₁) := fun m =>
    { toFun := fun s => emb₁ s m
      invFun := fun k => ⟨(k.val + K₁ - m.val) % K₁, Nat.mod_lt _ hK₁⟩
      left_inv := fun s => by ext; exact hshift_left s.isLt (lt_of_lt_of_le m.isLt hMK₁)
      right_inv := fun k => by ext; exact hshift_right k.isLt (lt_of_lt_of_le m.isLt hMK₁) }
  let shiftEquiv₂ : Fin M₂ → (Fin K₂ ≃ Fin K₂) := fun m =>
    { toFun := fun s => emb₂ s m
      invFun := fun k => ⟨(k.val + K₂ - m.val) % K₂, Nat.mod_lt _ hK₂⟩
      left_inv := fun s => by ext; exact hshift_left s.isLt (lt_of_lt_of_le m.isLt hMK₂)
      right_inv := fun k => by ext; exact hshift_right k.isLt (lt_of_lt_of_le m.isLt hMK₂) }
  -- Average of restricted error over all cyclic shifts `(s₁, s₂)` equals `avgErr(C)`
  let f : Fin K₁ × Fin K₂ → ℝ := fun s =>
    (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianMACErrorProb C N (emb₁ s.1 m₁) (emb₂ s.2 m₂)).toReal
  have havg : ∑ s : Fin K₁ × Fin K₂, (1 / ((K₁ * K₂ : ℕ) : ℝ)) * f s =
      (gaussianMACAvgError C N).toReal := by
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    simp_rw [f, ← Finset.mul_sum]
    have hsum : ∑ s₁ : Fin K₁, ∑ s₂ : Fin K₂, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
        (gaussianMACErrorProb C N (emb₁ s₁ m₁) (emb₂ s₂ m₂)).toReal =
        ((M₁ * M₂ : ℕ) : ℝ) *
          ∑ k₁ : Fin K₁, ∑ k₂ : Fin K₂, (gaussianMACErrorProb C N k₁ k₂).toReal := by
      trans (∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ s₁ : Fin K₁, ∑ s₂ : Fin K₂,
          (gaussianMACErrorProb C N (emb₁ s₁ m₁) (emb₂ s₂ m₂)).toReal)
      · trans (∑ s₁ : Fin K₁, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ s₂ : Fin K₂,
            (gaussianMACErrorProb C N (emb₁ s₁ m₁) (emb₂ s₂ m₂)).toReal)
        · refine Finset.sum_congr rfl fun s₁ _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
      · have hconst : ∀ m₁ m₂,
            ∑ s₁ : Fin K₁, ∑ s₂ : Fin K₂,
              (gaussianMACErrorProb C N (emb₁ s₁ m₁) (emb₂ s₂ m₂)).toReal =
            ∑ k₁ : Fin K₁, ∑ k₂ : Fin K₂, (gaussianMACErrorProb C N k₁ k₂).toReal := by
          intro m₁ m₂
          calc ∑ s₁ : Fin K₁, ∑ s₂ : Fin K₂,
                (gaussianMACErrorProb C N (emb₁ s₁ m₁) (emb₂ s₂ m₂)).toReal
              = ∑ k₁ : Fin K₁, ∑ s₂ : Fin K₂,
                  (gaussianMACErrorProb C N k₁ (emb₂ s₂ m₂)).toReal :=
                Fintype.sum_equiv (shiftEquiv₁ m₁) _ _ (fun _ => rfl)
            _ = ∑ k₁ : Fin K₁, ∑ k₂ : Fin K₂, (gaussianMACErrorProb C N k₁ k₂).toReal :=
                Finset.sum_congr rfl fun k₁ _ =>
                  Fintype.sum_equiv (shiftEquiv₂ m₂) _ _ (fun _ => rfl)
        simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_mul, mul_assoc]
    rw [hsum, gaussianMACAvgError_toReal]
    have hM12 : ((M₁ * M₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    field_simp [hM12]
  have hw1 : ∑ _s : Fin K₁ × Fin K₂, (1 / ((K₁ * K₂ : ℕ) : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, one_div]
    have hne : ((K₁ * K₂ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact mul_inv_cancel₀ hne
  obtain ⟨⟨s₁, s₂⟩, hs⟩ := exists_le_of_weighted_sum_le_cc
    (fun _ : Fin K₁ × Fin K₂ => 1 / ((K₁ * K₂ : ℕ) : ℝ)) f (gaussianMACAvgError C N).toReal
    (fun _ => by positivity) hw1 (le_of_eq havg)
  let inv₁ : Fin K₁ → Fin M₁ := fun k =>
    if h : ∃ m, emb₁ s₁ m = k then Classical.choose h else ⟨0, hM₁⟩
  let inv₂ : Fin K₂ → Fin M₂ := fun k =>
    if h : ∃ m, emb₂ s₂ m = k then Classical.choose h else ⟨0, hM₂⟩
  have hinv₁ : ∀ m₁, inv₁ (emb₁ s₁ m₁) = m₁ := fun m₁ => by
    have hex : ∃ m, emb₁ s₁ m = emb₁ s₁ m₁ := ⟨m₁, rfl⟩
    simp only [inv₁, hex, ↓reduceDIte]
    exact hemb₁_inj s₁ (Classical.choose_spec hex)
  have hinv₂ : ∀ m₂, inv₂ (emb₂ s₂ m₂) = m₂ := fun m₂ => by
    have hex : ∃ m, emb₂ s₂ m = emb₂ s₂ m₂ := ⟨m₂, rfl⟩
    simp only [inv₂, hex, ↓reduceDIte]
    exact hemb₂_inj s₂ (Classical.choose_spec hex)
  let C' : GaussianMACCode n M₁ M₂ :=
    { encoder₁ := fun m₁ => C.encoder₁ (emb₁ s₁ m₁)
      encoder₂ := fun m₂ => C.encoder₂ (emb₂ s₂ m₂)
      decoder := fun y => (inv₁ (C.decoder y).1, inv₂ (C.decoder y).2)
      measurable_decoder := (measurable_of_finite fun p : Fin K₁ × Fin K₂ =>
        (inv₁ p.1, inv₂ p.2)).comp C.measurable_decoder }
  refine ⟨C', ⟨fun m₁ => hpow.1 (emb₁ s₁ m₁), fun m₂ => hpow.2 (emb₂ s₂ m₂)⟩, ?_⟩
  rw [← ENNReal.toReal_le_toReal (gaussianMACAvgError_ne_top hM₁ hM₂ C' N)
    (gaussianMACAvgError_ne_top (by omega) (by omega) C N)]
  refine le_trans ?_ hs
  rw [gaussianMACAvgError_toReal]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
    ENNReal.toReal_mono
      (ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C N _ _))
      (measure_mono fun z hz => by
        simp only [Set.mem_ofPred_eq, C', ne_eq] at hz ⊢
        intro heq; apply hz; rw [heq, hinv₁, hinv₂])) (by positivity)

/-- Projection of `awgnNoise n N` onto the first `n₁` coordinates equals `awgnNoise n₁ N`. -/
private lemma awgnNoise_map_left {n₁ n₂ n : ℕ} (h : n₁ + n₂ = n) (N : ℝ) :
    (awgnNoise n N).map (fun (z : Fin n → ℝ) (i : Fin n₁) => z ⟨i.val, by omega⟩) =
      awgnNoise n₁ N := by
  let proj : (Fin n → ℝ) → (Fin n₁ → ℝ) := fun z i => z ⟨i.val, by omega⟩
  have hproj : Measurable proj := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hproj (MeasurableSet.univ_pi hs)]
  let s' : Fin n → Set ℝ := fun j => if hj : j.val < n₁ then s ⟨j.val, hj⟩ else Set.univ
  have hpre : proj ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, proj, s']
    constructor
    · intro hz j; split_ifs with hj
      · exact hz ⟨j.val, hj⟩
      · trivial
    · intro hz i
      have := hz ⟨i.val, by omega⟩
      simp [i.isLt] at this
      exact this
  rw [hpre, awgnNoise, Measure.pi_pi]
  let e : Fin n₁ ⊕ Fin n₂ ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  rw [← Fintype.prod_equiv e (fun x => gaussianReal 0 N.toNNReal (s' (e x)))
      (fun j => gaussianReal 0 N.toNNReal (s' j)) (fun _ => rfl), Fintype.prod_sum_type]
  have hleft : ∏ i : Fin n₁, gaussianReal 0 N.toNNReal (s' (e (Sum.inl i))) =
      ∏ i : Fin n₁, gaussianReal 0 N.toNNReal (s i) :=
    Finset.prod_congr rfl fun i _ => by simp [e, s', i.isLt]
  have hright : ∏ j : Fin n₂, gaussianReal 0 N.toNNReal (s' (e (Sum.inr j))) = 1 :=
    Finset.prod_eq_one fun j _ => by
      have hge : ¬ ((e (Sum.inr j)).val < n₁) := by simp [e]
      simp [s', hge]
  rw [hleft, hright, mul_one]

/-- Projection of `awgnNoise n N` onto the last `n₂` coordinates equals `awgnNoise n₂ N`. -/
private lemma awgnNoise_map_right {n₁ n₂ n : ℕ} (h : n₁ + n₂ = n) (N : ℝ) :
    (awgnNoise n N).map (fun (z : Fin n → ℝ) (j : Fin n₂) => z ⟨n₁ + j.val, by omega⟩) =
      awgnNoise n₂ N := by
  let proj : (Fin n → ℝ) → (Fin n₂ → ℝ) := fun z j => z ⟨n₁ + j.val, by omega⟩
  have hproj : Measurable proj := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hproj (MeasurableSet.univ_pi hs)]
  let s' : Fin n → Set ℝ := fun j => if hj : n₁ ≤ j.val then s ⟨j.val - n₁, by omega⟩ else Set.univ
  have hpre : proj ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, proj, s']
    constructor
    · intro hz j; split_ifs with hj
      · have h1 := hz ⟨j.val - n₁, by omega⟩
        have hidx : (⟨n₁ + (j.val - n₁), by omega⟩ : Fin n) = j := by ext; simp; omega
        rwa [hidx] at h1
      · trivial
    · intro hz i
      have := hz ⟨n₁ + i.val, by omega⟩
      simp only [Nat.le_add_right, ↓reduceDIte, Nat.add_sub_cancel_left] at this
      exact this
  rw [hpre, awgnNoise, Measure.pi_pi]
  let e : Fin n₁ ⊕ Fin n₂ ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  rw [← Fintype.prod_equiv e (fun x => gaussianReal 0 N.toNNReal (s' (e x)))
      (fun j => gaussianReal 0 N.toNNReal (s' j)) (fun _ => rfl), Fintype.prod_sum_type]
  have hleft : ∏ i : Fin n₁, gaussianReal 0 N.toNNReal (s' (e (Sum.inl i))) = 1 :=
    Finset.prod_eq_one fun i _ => by
      have hlt : ¬ (n₁ ≤ (e (Sum.inl i)).val) := by simp [e]
      simp [s', hlt]
  have hright : ∏ j : Fin n₂, gaussianReal 0 N.toNNReal (s' (e (Sum.inr j))) =
      ∏ j : Fin n₂, gaussianReal 0 N.toNNReal (s j) :=
    Finset.prod_congr rfl fun j _ => by simp [e, s']
  rw [hleft, hright, one_mul]

/-- Time-sharing concatenation of two Gaussian MAC codes of blocklengths `n₁` and `n₂`
    (`n₁ + n₂ = n`): preserves per-codeword power `(P₁, P₂)` and adds average errors. -/
private theorem exists_mac_concat_code {n₁ n₂ n K₁₁ K₂₁ K₁₂ K₂₂ : ℕ} {N P₁ P₂ : ℝ}
    (h : n₁ + n₂ = n) (hK₁₁ : 1 ≤ K₁₁) (hK₂₁ : 1 ≤ K₂₁) (hK₁₂ : 1 ≤ K₁₂) (hK₂₂ : 1 ≤ K₂₂)
    (C₁ : GaussianMACCode n₁ K₁₁ K₂₁) (C₂ : GaussianMACCode n₂ K₁₂ K₂₂)
    (hpow₁ : C₁.SatisfiesPower P₁ P₂) (hpow₂ : C₂.SatisfiesPower P₁ P₂) :
    ∃ C : GaussianMACCode n (K₁₁ * K₁₂) (K₂₁ * K₂₂),
      C.SatisfiesPower P₁ P₂ ∧
      gaussianMACAvgError C N ≤ gaussianMACAvgError C₁ N + gaussianMACAvgError C₂ N := by
  let e₁ : Fin (K₁₁ * K₁₂) ≃ Fin K₁₁ × Fin K₁₂ := finProdFinEquiv.symm
  let e₂ : Fin (K₂₁ * K₂₂) ≃ Fin K₂₁ × Fin K₂₂ := finProdFinEquiv.symm
  let join : (Fin n₁ → ℝ) → (Fin n₂ → ℝ) → (Fin n → ℝ) := fun x₁ x₂ i =>
    if hi : i.val < n₁ then x₁ ⟨i.val, hi⟩ else x₂ ⟨i.val - n₁, by omega⟩
  let projL : (Fin n → ℝ) → (Fin n₁ → ℝ) := fun y i => y ⟨i.val, by omega⟩
  let projR : (Fin n → ℝ) → (Fin n₂ → ℝ) := fun y j => y ⟨n₁ + j.val, by omega⟩
  have hprojL : Measurable projL := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have hprojR : Measurable projR := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  let C : GaussianMACCode n (K₁₁ * K₁₂) (K₂₁ * K₂₂) :=
    { encoder₁ := fun m₁ => join (C₁.encoder₁ (e₁ m₁).1) (C₂.encoder₁ (e₁ m₁).2)
      encoder₂ := fun m₂ => join (C₁.encoder₂ (e₂ m₂).1) (C₂.encoder₂ (e₂ m₂).2)
      decoder := fun y =>
        let d₁ := C₁.decoder (projL y)
        let d₂ := C₂.decoder (projR y)
        (e₁.symm (d₁.1, d₂.1), e₂.symm (d₁.2, d₂.2))
      measurable_decoder := by
        have hd₁ := C₁.measurable_decoder.comp hprojL
        have hd₂ := C₂.measurable_decoder.comp hprojR
        exact (measurable_of_finite fun p : (Fin K₁₁ × Fin K₂₁) × (Fin K₁₂ × Fin K₂₂) =>
          (e₁.symm (p.1.1, p.2.1), e₂.symm (p.1.2, p.2.2))).comp (hd₁.prodMk hd₂) }
  have hsum_join : ∀ (x₁ : Fin n₁ → ℝ) (x₂ : Fin n₂ → ℝ),
      ∑ i : Fin n, (join x₁ x₂ i) ^ 2 = (∑ i : Fin n₁, x₁ i ^ 2) + (∑ j : Fin n₂, x₂ j ^ 2) := by
    intro x₁ x₂
    let ef : Fin n₁ ⊕ Fin n₂ ≃ Fin n := finSumFinEquiv.trans (finCongr h)
    rw [← Fintype.sum_equiv ef (fun u => (join x₁ x₂ (ef u)) ^ 2)
      (fun i => (join x₁ x₂ i) ^ 2) (fun _ => rfl), Fintype.sum_sum_type]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by simp [ef, join, i.isLt]
    · exact Finset.sum_congr rfl fun j _ => by
        have hnot : ¬ (n₁ + j.val < n₁) := by omega
        simp [ef, join, hnot]
  have hpowC : C.SatisfiesPower P₁ P₂ := by
    have hn : (n : ℝ) = (n₁ : ℝ) + (n₂ : ℝ) := by exact_mod_cast h.symm
    refine ⟨fun m₁ => ?_, fun m₂ => ?_⟩
    · rw [show ∑ i, (C.encoder₁ m₁ i) ^ 2 = _ from hsum_join _ _, hn, add_mul]
      exact add_le_add (hpow₁.1 _) (hpow₂.1 _)
    · rw [show ∑ i, (C.encoder₂ m₂ i) ^ 2 = _ from hsum_join _ _, hn, add_mul]
      exact add_le_add (hpow₁.2 _) (hpow₂.2 _)
  refine ⟨C, hpowC, ?_⟩
  have herr_pt : ∀ m₁ m₂, gaussianMACErrorProb C N m₁ m₂ ≤
      gaussianMACErrorProb C₁ N (e₁ m₁).1 (e₂ m₂).1 +
      gaussianMACErrorProb C₂ N (e₁ m₁).2 (e₂ m₂).2 := by
    intro m₁ m₂
    let A₁ : Set (Fin n₁ → ℝ) :=
      {z₁ | C₁.decoder (C₁.encoder₁ (e₁ m₁).1 + C₁.encoder₂ (e₂ m₂).1 + z₁) ≠ ((e₁ m₁).1, (e₂ m₂).1)}
    let A₂ : Set (Fin n₂ → ℝ) :=
      {z₂ | C₂.decoder (C₂.encoder₁ (e₁ m₁).2 + C₂.encoder₂ (e₂ m₂).2 + z₂) ≠ ((e₁ m₁).2, (e₂ m₂).2)}
    have hA₁ : MeasurableSet A₁ :=
      (C₁.measurable_decoder.comp (measurable_const_add _)) (measurableSet_singleton _).compl
    have hA₂ : MeasurableSet A₂ :=
      (C₂.measurable_decoder.comp (measurable_const_add _)) (measurableSet_singleton _).compl
    have hsub : {z : Fin n → ℝ | C.decoder (C.encoder₁ m₁ + C.encoder₂ m₂ + z) ≠ (m₁, m₂)} ⊆
        projL ⁻¹' A₁ ∪ projR ⁻¹' A₂ := by
      intro z hz
      by_contra hnot
      simp only [Set.mem_union, Set.mem_preimage, not_or, A₁, A₂, Set.mem_ofPred_eq, not_not] at hnot
      apply hz
      have hL : projL (C.encoder₁ m₁ + C.encoder₂ m₂ + z) =
          C₁.encoder₁ (e₁ m₁).1 + C₁.encoder₂ (e₂ m₂).1 + projL z := by
        ext i; simp [C, projL, join, i.isLt]
      have hR : projR (C.encoder₁ m₁ + C.encoder₂ m₂ + z) =
          C₂.encoder₁ (e₁ m₁).2 + C₂.encoder₂ (e₂ m₂).2 + projR z := by
        ext j
        have hnot' : ¬ (n₁ + j.val < n₁) := by omega
        simp [C, projR, join, hnot']
      simp only [C, hL, hR, hnot.1, hnot.2, e₁.symm_apply_apply, e₂.symm_apply_apply]
    calc gaussianMACErrorProb C N m₁ m₂
        ≤ awgnNoise n N (projL ⁻¹' A₁) + awgnNoise n N (projR ⁻¹' A₂) :=
          le_trans (measure_mono hsub) (measure_union_le _ _)
      _ = (awgnNoise n N).map projL A₁ + (awgnNoise n N).map projR A₂ := by
          rw [Measure.map_apply hprojL hA₁, Measure.map_apply hprojR hA₂]
      _ = gaussianMACErrorProb C₁ N (e₁ m₁).1 (e₂ m₂).1 +
          gaussianMACErrorProb C₂ N (e₁ m₁).2 (e₂ m₂).2 := by
          rw [awgnNoise_map_left h N, awgnNoise_map_right h N]; rfl
  have hM₁ : 1 ≤ K₁₁ * K₁₂ := Nat.mul_pos hK₁₁ hK₁₂
  have hM₂ : 1 ≤ K₂₁ * K₂₂ := Nat.mul_pos hK₂₁ hK₂₂
  rw [← ENNReal.toReal_le_toReal (gaussianMACAvgError_ne_top hM₁ hM₂ C N)
      (ENNReal.add_ne_top.2 ⟨gaussianMACAvgError_ne_top hK₁₁ hK₂₁ C₁ N,
        gaussianMACAvgError_ne_top hK₁₂ hK₂₂ C₂ N⟩),
    ENNReal.toReal_add (gaussianMACAvgError_ne_top hK₁₁ hK₂₁ C₁ N)
      (gaussianMACAvgError_ne_top hK₁₂ hK₂₂ C₂ N),
    gaussianMACAvgError_toReal, gaussianMACAvgError_toReal, gaussianMACAvgError_toReal]
  have hptR : ∀ m₁ m₂, (gaussianMACErrorProb C N m₁ m₂).toReal ≤
      (gaussianMACErrorProb C₁ N (e₁ m₁).1 (e₂ m₂).1).toReal +
      (gaussianMACErrorProb C₂ N (e₁ m₁).2 (e₂ m₂).2).toReal := fun m₁ m₂ => by
    rw [← ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C₁ N _ _))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C₂ N _ _))]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2
      ⟨ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C₁ N _ _),
       ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianMACErrorProb_le_one C₂ N _ _)⟩)
      (herr_pt m₁ m₂)
  have hsum : ∑ m₁ : Fin (K₁₁ * K₁₂), ∑ m₂ : Fin (K₂₁ * K₂₂),
        (gaussianMACErrorProb C N m₁ m₂).toReal ≤
      ((K₁₂ * K₂₂ : ℕ) : ℝ) *
        (∑ a₁ : Fin K₁₁, ∑ b₁ : Fin K₂₁, (gaussianMACErrorProb C₁ N a₁ b₁).toReal) +
      ((K₁₁ * K₂₁ : ℕ) : ℝ) *
        (∑ a₂ : Fin K₁₂, ∑ b₂ : Fin K₂₂, (gaussianMACErrorProb C₂ N a₂ b₂).toReal) := by
    calc ∑ m₁, ∑ m₂, (gaussianMACErrorProb C N m₁ m₂).toReal
        ≤ ∑ m₁, ∑ m₂, ((gaussianMACErrorProb C₁ N (e₁ m₁).1 (e₂ m₂).1).toReal +
            (gaussianMACErrorProb C₂ N (e₁ m₁).2 (e₂ m₂).2).toReal) :=
          Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => hptR m₁ m₂
      _ = (∑ m₁, ∑ m₂, (gaussianMACErrorProb C₁ N (e₁ m₁).1 (e₂ m₂).1).toReal) +
          (∑ m₁, ∑ m₂, (gaussianMACErrorProb C₂ N (e₁ m₁).2 (e₂ m₂).2).toReal) := by
          simp_rw [Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          · rw [Fintype.sum_equiv e₁ _ (fun p₁ => ∑ m₂, (gaussianMACErrorProb C₁ N p₁.1 (e₂ m₂).1).toReal)
              (fun _ => rfl), Fintype.sum_prod_type]
            have h2 : ∀ a₁ : Fin K₁₁, ∑ m₂ : Fin (K₂₁ * K₂₂),
                (gaussianMACErrorProb C₁ N a₁ (e₂ m₂).1).toReal =
                (K₂₂ : ℝ) * ∑ b₁ : Fin K₂₁, (gaussianMACErrorProb C₁ N a₁ b₁).toReal := by
              intro a₁
              rw [Fintype.sum_equiv e₂ _ (fun p₂ => (gaussianMACErrorProb C₁ N a₁ p₂.1).toReal)
                (fun _ => rfl), Fintype.sum_prod_type]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← Finset.mul_sum]
            simp_rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← Finset.mul_sum, Nat.cast_mul, mul_assoc]
          · rw [Fintype.sum_equiv e₁ _ (fun p₁ => ∑ m₂, (gaussianMACErrorProb C₂ N p₁.2 (e₂ m₂).2).toReal)
              (fun _ => rfl), Fintype.sum_prod_type]
            have h2 : ∀ a₂ : Fin K₁₂, ∑ m₂ : Fin (K₂₁ * K₂₂),
                (gaussianMACErrorProb C₂ N a₂ (e₂ m₂).2).toReal =
                (K₂₁ : ℝ) * ∑ b₂ : Fin K₂₂, (gaussianMACErrorProb C₂ N a₂ b₂).toReal := by
              intro a₂
              rw [Fintype.sum_equiv e₂ _ (fun p₂ => (gaussianMACErrorProb C₂ N a₂ p₂.2).toReal)
                (fun _ => rfl), Fintype.sum_prod_type]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            simp_rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← Finset.mul_sum, Nat.cast_mul, mul_assoc]
  have hK11p : (0 : ℝ) < K₁₁ := by exact_mod_cast hK₁₁
  have hK21p : (0 : ℝ) < K₂₁ := by exact_mod_cast hK₂₁
  have hK12p : (0 : ℝ) < K₁₂ := by exact_mod_cast hK₁₂
  have hK22p : (0 : ℝ) < K₂₂ := by exact_mod_cast hK₂₂
  have hmul := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / (((K₁₁ * K₁₂) * (K₂₁ * K₂₂) : ℕ) : ℝ) by positivity)
  refine le_trans hmul (le_of_eq ?_)
  push_cast
  field_simp [hK11p.ne', hK21p.ne', hK12p.ne', hK22p.ne']

/-- Time-sharing between two achievable rate pairs: any strictly dominated rate pair (or `0` on
    a coordinate) below a convex combination is achievable. -/
private lemma isGaussianMACAchievable_timeShare {P₁ P₂ N : ℝ} {r s u : ℝ × ℝ} {t : ℝ}
    (hr : IsGaussianMACAchievable P₁ P₂ N r.1 r.2)
    (hs : IsGaussianMACAchievable P₁ P₂ N s.1 s.2)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hu10 : 0 ≤ u.1) (hu20 : 0 ≤ u.2)
    (hu1 : u.1 = 0 ∨ u.1 < (1 - t) * r.1 + t * s.1)
    (hu2 : u.2 = 0 ∨ u.2 < (1 - t) * r.2 + t * s.2) :
    IsGaussianMACAchievable P₁ P₂ N u.1 u.2 := by
  refine ⟨hu10, hu20, fun δ hδ => ?_⟩
  obtain ⟨n₁₀, hn₁₀⟩ := hr.2.2 (δ / 2) (by linarith)
  obtain ⟨n₂₀, hn₂₀⟩ := hs.2.2 (δ / 2) (by linarith)
  -- Blocklength split `n₁ = ⌊(1 - t) n⌋₊`, `n₂ = n - n₁`
  have h1t : 0 < 1 - t := by linarith
  have hev_n₁ : ∀ᶠ n : ℕ in atTop, n₁₀ ≤ ⌊(1 - t) * (n : ℝ)⌋₊ := by
    have htend : Tendsto (fun n : ℕ => (1 - t) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop h1t
    filter_upwards [htend.eventually_ge_atTop (n₁₀ : ℝ)] with n hn
    exact Nat.le_floor hn
  have hev_n₂ : ∀ᶠ n : ℕ in atTop, n₂₀ ≤ n - ⌊(1 - t) * (n : ℝ)⌋₊ := by
    have htend : Tendsto (fun n : ℕ => t * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop ht0
    filter_upwards [htend.eventually_ge_atTop (n₂₀ : ℝ)] with n hn
    have hfl : (⌊(1 - t) * (n : ℝ)⌋₊ : ℝ) ≤ (1 - t) * (n : ℝ) := Nat.floor_le (by positivity)
    have hle : (n₂₀ : ℝ) + (⌊(1 - t) * (n : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) := by linarith
    have hleN : n₂₀ + ⌊(1 - t) * (n : ℝ)⌋₊ ≤ n := by exact_mod_cast hle
    omega
  have hev_size : ∀ (a b c : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c →
      (c = 0 ∨ c < (1 - t) * a + t * b) →
      ∀ᶠ n : ℕ in atTop,
        max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * c)⌋₊ ≤
          max 1 ⌊(2 : ℝ) ^ ((⌊(1 - t) * (n : ℝ)⌋₊ : ℝ) * a)⌋₊ *
          max 1 ⌊(2 : ℝ) ^ (((n - ⌊(1 - t) * (n : ℝ)⌋₊ : ℕ) : ℝ) * b)⌋₊ := by
    intro a b c ha hb hc hcb
    rcases hcb with rfl | hlt
    · refine eventually_atTop.2 ⟨0, fun n _ => ?_⟩
      simp only [mul_zero, Real.rpow_zero, Nat.floor_one, max_self]
      exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
        (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    · set gap := (1 - t) * a + t * b - c
      have hgap : 0 < gap := by dsimp only [gap]; linarith
      have htend : Tendsto (fun n : ℕ => (n : ℝ) * gap) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hgap
      filter_upwards [htend.eventually_ge_atTop (a + 2)] with n hn
      set n₁ := ⌊(1 - t) * (n : ℝ)⌋₊
      set n₂ := n - n₁
      have hn₁_le : (n₁ : ℝ) ≤ (1 - t) * (n : ℝ) := Nat.floor_le (by positivity)
      have hn₁_gt : (1 - t) * (n : ℝ) - 1 < (n₁ : ℝ) := by
        have := Nat.lt_floor_add_one ((1 - t) * (n : ℝ)); linarith
      have hn₁_le_n : n₁ ≤ n := by
        have : (n₁ : ℝ) ≤ (n : ℝ) := by nlinarith
        exact_mod_cast this
      have hn₂_eq : (n₂ : ℝ) = (n : ℝ) - (n₁ : ℝ) := Nat.cast_sub hn₁_le_n
      have hexp : (n : ℝ) * c ≤ (n₁ : ℝ) * a + (n₂ : ℝ) * b - 2 := by
        rw [hn₂_eq]
        have h1 : (n₁ : ℝ) * a ≥ ((1 - t) * (n : ℝ) - 1) * a := by nlinarith
        have h2 : ((n : ℝ) - (n₁ : ℝ)) * b ≥ t * (n : ℝ) * b := by nlinarith
        dsimp only [gap] at hn
        nlinarith
      have hM_le : ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * c)⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * c) := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * c) := Real.one_le_rpow (by norm_num) (by positivity)
        rcases le_total 1 ⌊(2 : ℝ) ^ ((n : ℝ) * c)⌋₊ with h | h
        · rw [max_eq_right h]; exact Nat.floor_le (by positivity)
        · rw [max_eq_left h]; push_cast; exact h1
      have hhalf : ∀ x : ℝ, (2 : ℝ) ^ (x - 1) ≤ (max 1 ⌊(2 : ℝ) ^ x⌋₊ : ℕ) := by
        intro x
        have h1 : (2 : ℝ) ^ (x - 1) = (2 : ℝ) ^ x / 2 := by
          rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        have h1M : (1 : ℝ) ≤ (max 1 ⌊(2 : ℝ) ^ x⌋₊ : ℕ) := by exact_mod_cast le_max_left 1 _
        have hleM : (⌊(2 : ℝ) ^ x⌋₊ : ℝ) ≤ (max 1 ⌊(2 : ℝ) ^ x⌋₊ : ℕ) :=
          Nat.cast_le.mpr (le_max_right 1 _)
        have hfl := Nat.lt_floor_add_one ((2 : ℝ) ^ x)
        rw [h1]
        by_cases h2 : (2 : ℝ) ≤ (2 : ℝ) ^ x <;> linarith
      have hprod : (2 : ℝ) ^ ((n₁ : ℝ) * a + (n₂ : ℝ) * b - 2) ≤
          ((max 1 ⌊(2 : ℝ) ^ ((n₁ : ℝ) * a)⌋₊ * max 1 ⌊(2 : ℝ) ^ ((n₂ : ℝ) * b)⌋₊ : ℕ) : ℝ) := by
        have hmul := mul_le_mul (hhalf ((n₁ : ℝ) * a)) (hhalf ((n₂ : ℝ) * b))
          (Real.rpow_pos_of_pos (by norm_num) _).le (Nat.cast_nonneg _)
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hmul
        rw [Nat.cast_mul]
        convert hmul using 2
        ring
      have hpow_le : (2 : ℝ) ^ ((n : ℝ) * c) ≤ (2 : ℝ) ^ ((n₁ : ℝ) * a + (n₂ : ℝ) * b - 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      exact_mod_cast le_trans hM_le (le_trans hpow_le hprod)
  have hev := (hev_n₁.and hev_n₂).and
    ((hev_size r.1 s.1 u.1 hr.1 hs.1 hu10 hu1).and (hev_size r.2 s.2 u.2 hr.2.1 hs.2.1 hu20 hu2))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨⟨hn1, hn2⟩, ⟨hsz1, hsz2⟩⟩ := hn₀ n hn
  set n₁ := ⌊(1 - t) * (n : ℝ)⌋₊
  set n₂ := n - n₁
  have hn₁_le_n : n₁ ≤ n := by
    have hfl : (n₁ : ℝ) ≤ (1 - t) * (n : ℝ) := Nat.floor_le (by positivity)
    exact_mod_cast (by nlinarith : (n₁ : ℝ) ≤ (n : ℝ))
  have hsum_n : n₁ + n₂ = n := Nat.add_sub_of_le hn₁_le_n
  obtain ⟨C₁, hpow₁, herr₁⟩ := hn₁₀ n₁ hn1
  obtain ⟨C₂, hpow₂, herr₂⟩ := hn₂₀ n₂ hn2
  obtain ⟨Ccat, hpowCat, herrCat⟩ := exists_mac_concat_code hsum_n
    (le_max_left 1 _) (le_max_left 1 _) (le_max_left 1 _) (le_max_left 1 _) C₁ C₂ hpow₁ hpow₂
  obtain ⟨C', hpow', herr'⟩ := exists_mac_subcode_of_le
    (le_max_left 1 _) (le_max_left 1 _) hsz1 hsz2 Ccat hpowCat
  refine ⟨C', hpow', ?_⟩
  calc gaussianMACAvgError C' N
      ≤ gaussianMACAvgError Ccat N := herr'
    _ ≤ gaussianMACAvgError C₁ N + gaussianMACAvgError C₂ N := herrCat
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add herr₁ herr₂
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

/-- **Time-sharing convexity**: `gaussianMACCapacityRegion P₁ P₂ N` is convex. -/
theorem gaussianMACCapacityRegion_convex (P₁ P₂ N : ℝ) :
    Convex ℝ (gaussianMACCapacityRegion P₁ P₂ N) := by
  let A : Set (ℝ × ℝ) := { r : ℝ × ℝ | IsGaussianMACAchievable P₁ P₂ N r.1 r.2 }
  have hseg : ∀ r ∈ A, ∀ s ∈ A, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • r + b • s ∈ closure A := by
    intro r hr s hs a b ha hb hab
    by_cases ha0 : a = 0
    · subst ha0; have hb1 : b = 1 := by linarith
      subst hb1; simp only [zero_smul, one_smul, zero_add]; exact subset_closure hs
    · by_cases hb0 : b = 0
      · subst hb0; have ha1 : a = 1 := by linarith
        subst ha1; simp only [zero_smul, one_smul, add_zero]; exact subset_closure hr
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have ha_eq : a = 1 - b := by linarith
        rw [mem_closure_iff_seq_limit]
        let seq : ℕ → ℝ × ℝ := fun m =>
          let c : ℝ := 1 - 1 / ((m + 2 : ℕ) : ℝ)
          (c * (a * r.1 + b * s.1), c * (a * r.2 + b * s.2))
        refine ⟨seq, fun m => ?_, ?_⟩
        · have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
          have hc0 : 0 ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by
            rw [sub_nonneg, div_le_one hm]; exact_mod_cast (show 1 ≤ m + 2 by omega)
          have hc1 : 1 - 1 / ((m + 2 : ℕ) : ℝ) < 1 := by linarith [one_div_pos.mpr hm]
          have h10 : 0 ≤ (1 - 1 / ((m + 2 : ℕ) : ℝ)) * (a * r.1 + b * s.1) :=
            mul_nonneg hc0 (add_nonneg (mul_nonneg ha hr.1) (mul_nonneg hb hs.1))
          have h20 : 0 ≤ (1 - 1 / ((m + 2 : ℕ) : ℝ)) * (a * r.2 + b * s.2) :=
            mul_nonneg hc0 (add_nonneg (mul_nonneg ha hr.2.1) (mul_nonneg hb hs.2.1))
          refine isGaussianMACAchievable_timeShare hr hs hb_pos (by linarith) h10 h20 ?_ ?_
          · by_cases hsum : a * r.1 + b * s.1 = 0
            · left; simp [seq, hsum]
            · right
              have hpos : 0 < a * r.1 + b * s.1 :=
                lt_of_le_of_ne (add_nonneg (mul_nonneg ha hr.1) (mul_nonneg hb hs.1)) (Ne.symm hsum)
              rw [← ha_eq]; nlinarith
          · by_cases hsum : a * r.2 + b * s.2 = 0
            · left; simp [seq, hsum]
            · right
              have hpos : 0 < a * r.2 + b * s.2 :=
                lt_of_le_of_ne (add_nonneg (mul_nonneg ha hr.2.1) (mul_nonneg hb hs.2.1)) (Ne.symm hsum)
              rw [← ha_eq]; nlinarith
        · have hlimc : Tendsto (fun m : ℕ => 1 - 1 / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
            have h1 : Tendsto (fun m : ℕ => 1 / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
              tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
            simpa using tendsto_const_nhds.sub h1
          have hp1 : Tendsto (fun m => (seq m).1) atTop (𝓝 (a * r.1 + b * s.1)) := by
            simpa [seq] using hlimc.mul_const (a * r.1 + b * s.1)
          have hp2 : Tendsto (fun m => (seq m).2) atTop (𝓝 (a * r.2 + b * s.2)) := by
            simpa [seq] using hlimc.mul_const (a * r.2 + b * s.2)
          exact hp1.prodMk_nhds hp2
  intro x hx y hy a b ha hb hab
  rw [gaussianMACCapacityRegion] at hx hy ⊢
  obtain ⟨rx, hrx_mem, hrx_lim⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨ry, hry_mem, hry_lim⟩ := mem_closure_iff_seq_limit.mp hy
  refine isClosed_closure.mem_of_tendsto ((hrx_lim.const_smul a).add (hry_lim.const_smul b)) ?_
  exact Eventually.of_forall fun m => hseg (rx m) (hrx_mem m) (ry m) (hry_mem m) a b ha hb hab

/-- Any point of a polymatroid pentagon lies in any convex set containing its 5 vertices. -/
private lemma mem_convex_of_pentagon {S : Set (ℝ × ℝ)} (hS : Convex ℝ S)
    {A B C x y : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hAC : A ≤ C) (hBC : B ≤ C) (hCAB : C ≤ A + B)
    (hv0 : (0, 0) ∈ S) (hv1 : (A, 0) ∈ S) (hv2 : (A, C - A) ∈ S)
    (hv3 : (C - B, B) ∈ S) (hv4 : (0, B) ∈ S)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxA : x ≤ A) (hyB : y ≤ B) (hxyC : x + y ≤ C) :
    (x, y) ∈ S := by
  have hrect : ∀ (u v s t : ℝ), 0 ≤ u → 0 ≤ v →
      (0, 0) ∈ S → (u, 0) ∈ S → (0, v) ∈ S → (u, v) ∈ S →
      0 ≤ s → s ≤ u → 0 ≤ t → t ≤ v → (s, t) ∈ S := by
    intro u v s t hu hv h00 hu0 h0v huv hs0 hsu ht0 htv
    have h0t : (0, t) ∈ S := by
      by_cases hv0' : v = 0
      · have : t = 0 := by linarith
        subst this; exact h00
      · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0')
        have hcomb := hS h00 h0v (show 0 ≤ 1 - t / v by rw [sub_nonneg, div_le_one hvpos]; exact htv)
          (div_nonneg ht0 hvpos.le) (by ring)
        have heq : (1 - t / v) • ((0 : ℝ), (0 : ℝ)) + (t / v) • ((0 : ℝ), v) = (0, t) := by
          ext <;> simp [div_mul_cancel₀ t hvpos.ne']
        rwa [← heq]
    have hut : (u, t) ∈ S := by
      by_cases hv0' : v = 0
      · have : t = 0 := by linarith
        subst this; exact hu0
      · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0')
        have hcomb := hS hu0 huv (show 0 ≤ 1 - t / v by rw [sub_nonneg, div_le_one hvpos]; exact htv)
          (div_nonneg ht0 hvpos.le) (by ring)
        have heq : (1 - t / v) • (u, (0 : ℝ)) + (t / v) • (u, v) = (u, t) := by
          ext
          · simp; ring
          · simp [div_mul_cancel₀ t hvpos.ne']
        rwa [← heq]
    by_cases hu0' : u = 0
    · have : s = 0 := by linarith
      subst this; exact h0t
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0')
      have hcomb := hS h0t hut (show 0 ≤ 1 - s / u by rw [sub_nonneg, div_le_one hupos]; exact hsu)
        (div_nonneg hs0 hupos.le) (by ring)
      have heq : (1 - s / u) • ((0 : ℝ), t) + (s / u) • (u, t) = (s, t) := by
        ext
        · simp [div_mul_cancel₀ s hupos.ne']
        · simp; ring
      rwa [← heq]
  have hCB0 : (C - B, 0) ∈ S := by
    by_cases hA : A = 0
    · have : C - B = 0 := by linarith
      rwa [this]
    · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
      let t := (C - B) / A
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hApos.le
      have ht1 : t ≤ 1 := (div_le_one hApos).mpr (by linarith)
      have hcomb := hS hv0 hv1 (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      have heq : (1 - t) • ((0 : ℝ), (0 : ℝ)) + t • (A, (0 : ℝ)) = (C - B, 0) := by
        ext <;> simp [t, div_mul_cancel₀ _ hApos.ne']
      rwa [← heq]
  have h0CA : (0, C - A) ∈ S := by
    by_cases hB : B = 0
    · have : C - A = 0 := by linarith
      rwa [this]
    · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
      let t := (C - A) / B
      have ht0 : 0 ≤ t := div_nonneg (by linarith) hBpos.le
      have ht1 : t ≤ 1 := (div_le_one hBpos).mpr (by linarith)
      have hcomb := hS hv0 hv4 (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      have heq : (1 - t) • ((0 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), B) = (0, C - A) := by
        ext <;> simp [t, div_mul_cancel₀ _ hBpos.ne']
      rwa [← heq]
  by_cases hx_left : x ≤ C - B
  · exact hrect (C - B) B x y (by linarith) hB0 hv0 hCB0 hv4 hv3 hx0 hx_left hy0 hyB
  · by_cases hy_bot : y ≤ C - A
    · exact hrect A (C - A) x y hA0 (by linarith) hv0 hv1 h0CA hv2 hx0 hxA hy0 hy_bot
    · push Not at hx_left hy_bot
      have hp : (C - B, C - A) ∈ S :=
        hrect (C - B) B (C - B) (C - A) (by linarith) hB0 hv0 hCB0 hv4 hv3
          (by linarith) le_rfl (by linarith) (by linarith)
      let d : ℝ := A + B - C
      have hd : 0 < d := by dsimp only [d]; linarith
      let α : ℝ := (x - (C - B)) / d
      let β : ℝ := (y - (C - A)) / d
      let γ : ℝ := (C - x - y) / d
      have hα : 0 < α := div_pos (by linarith) hd
      have hβ : 0 < β := div_pos (by linarith) hd
      have hγ : 0 ≤ γ := div_nonneg (by linarith) hd.le
      have hsum : α + β + γ = 1 := by
        dsimp only [α, β, γ]
        rw [← add_div, ← add_div, div_eq_one_iff_eq hd.ne']
        dsimp only [d]; ring
      have hαβ : 0 < α + β := by linarith
      let q : ℝ × ℝ := (α / (α + β)) • (A, C - A) + (β / (α + β)) • (C - B, B)
      have hq : q ∈ S :=
        hS hv2 hv3 (div_nonneg hα.le hαβ.le) (div_nonneg hβ.le hαβ.le)
          (by rw [← add_div, div_self hαβ.ne'])
      have hcomb : (α + β) • q + γ • (C - B, C - A) ∈ S := hS hq hp hαβ.le hγ (by linarith)
      have heq : (α + β) • q + γ • (C - B, C - A) = (x, y) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, q]
          have h1 : (α + β) * (α / (α + β) * A + β / (α + β) * (C - B)) =
              α * A + β * (C - B) := by field_simp [hαβ.ne']
          rw [h1]; dsimp only [α, β, γ]
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
            ← add_div, ← add_div, div_eq_iff hd.ne']
          dsimp only [d]; ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, q]
          have h1 : (α + β) * (α / (α + β) * (C - A) + β / (α + β) * B) =
              α * (C - A) + β * B := by field_simp [hαβ.ne']
          rw [h1]; dsimp only [α, β, γ]
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
            ← add_div, ← add_div, div_eq_iff hd.ne']
          dsimp only [d]; ring
      rwa [← heq]

/-- Embedding a single-user AWGN achievable rate `R₁` into the MAC as `(R₁, 0)`. -/
private lemma isGaussianMACAchievable_of_awgn_left {P₁ P₂ N R₁ : ℝ}
    (hP₂ : 0 ≤ P₂) (h : IsAwgnAchievable P₁ N R₁) :
    IsGaussianMACAchievable P₁ P₂ N R₁ 0 := by
  refine ⟨h.1, le_rfl, fun δ hδ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := h.2 δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨C, hpow, herr⟩ := hn₀ n hn
  have hM₂ : max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * 0)⌋₊ = 1 := by simp
  rw [hM₂]
  let Cmac : GaussianMACCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊) 1 :=
    { encoder₁ := C.encoder
      encoder₂ := fun _ _ => 0
      decoder := fun y => (C.decoder y, 0)
      measurable_decoder := C.measurable_decoder.prodMk measurable_const }
  refine ⟨Cmac, ⟨hpow, fun _ => by show ∑ _i : Fin n, (0 : ℝ) ^ 2 ≤ _; simp; positivity⟩, ?_⟩
  have heq : gaussianMACAvgError Cmac N = awgnAvgErrorProb C N := by
    unfold gaussianMACAvgError awgnAvgErrorProb
    simp only [mul_one, Fin.sum_univ_one]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    unfold gaussianMACErrorProb awgnErrorProb
    congr 1; ext z
    have h0 : (fun _ : Fin n => (0 : ℝ)) = 0 := rfl
    simp [Cmac, h0]
  rwa [heq]

private lemma tendsto_one_sub_inv_add_two :
    Tendsto (fun m : ℕ => (1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

/-- **Exact Operational Achievability for the Two-User Gaussian MAC**
    (Cover & Thomas Thm. 15.1.1 achievability; El Gamal & Kim Thm. 4.6):
    `gaussianMACPentagon P₁ P₂ N ⊆ gaussianMACCapacityRegion P₁ P₂ N`. -/
theorem pentagon_subset_gaussianMACCapacityRegion {P₁ P₂ N : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    gaussianMACPentagon P₁ P₂ N ⊆ gaussianMACCapacityRegion P₁ P₂ N := by
  set A := awgnCapacityFormula P₁ N
  set B := awgnCapacityFormula P₂ N
  set C := awgnCapacityFormula (P₁ + P₂) N
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA0 : 0 ≤ A := by
    unfold A awgnCapacityFormula log2
    have : 1 ≤ 1 + P₁ / N := by have := div_nonneg hP₁ hN.le; linarith
    have := Real.log_nonneg this; positivity
  have hB0 : 0 ≤ B := by
    unfold B awgnCapacityFormula log2
    have : 1 ≤ 1 + P₂ / N := by have := div_nonneg hP₂ hN.le; linarith
    have := Real.log_nonneg this; positivity
  have hAC : A ≤ C := by
    unfold A C awgnCapacityFormula log2
    have h1 : 0 < 1 + P₁ / N := by positivity
    have h2 : 1 + P₁ / N ≤ 1 + (P₁ + P₂) / N := by rw [add_div]; linarith [div_nonneg hP₂ hN.le]
    gcongr
  have hBC : B ≤ C := by
    unfold B C awgnCapacityFormula log2
    have h1 : 0 < 1 + P₂ / N := by positivity
    have h2 : 1 + P₂ / N ≤ 1 + (P₁ + P₂) / N := by rw [add_div]; linarith [div_nonneg hP₁ hN.le]
    gcongr
  have hCAB : C ≤ A + B := by
    unfold A B C awgnCapacityFormula log2
    have h1 : 0 < 1 + P₁ / N := by positivity
    have h2 : 0 < 1 + P₂ / N := by positivity
    have h3 : 0 < 1 + (P₁ + P₂) / N := by positivity
    have hprod : 1 + (P₁ + P₂) / N ≤ (1 + P₁ / N) * (1 + P₂ / N) := by
      have : (1 + P₁ / N) * (1 + P₂ / N) - (1 + (P₁ + P₂) / N) = (P₁ * P₂) / N ^ 2 := by
        field_simp [hN.ne']; ring
      have hnn : 0 ≤ (P₁ * P₂) / N ^ 2 := by positivity
      linarith
    have hlog := Real.log_le_log h3 hprod
    rw [Real.log_mul h1.ne' h2.ne'] at hlog
    have hdiv1 := div_le_div_of_nonneg_right hlog hlog2.le
    have hdiv2 : (Real.log (1 + P₁ / N) + Real.log (1 + P₂ / N)) / Real.log 2 =
        Real.log (1 + P₁ / N) / Real.log 2 + Real.log (1 + P₂ / N) / Real.log 2 :=
      add_div _ _ _
    linarith
  have hCB_eq : C - B = awgnCapacityFormula P₁ (P₂ + N) := by
    unfold C B awgnCapacityFormula log2
    have h1 : 0 < 1 + (P₁ + P₂) / N := by positivity
    have h2 : 0 < 1 + P₂ / N := by positivity
    have hdiv : (1 + (P₁ + P₂) / N) / (1 + P₂ / N) = 1 + P₁ / (P₂ + N) := by
      field_simp [hN.ne', (show P₂ + N ≠ 0 by linarith)]; ring
    rw [← mul_sub, ← sub_div, ← Real.log_div h1.ne' h2.ne', hdiv]
  have hCA_eq : C - A = awgnCapacityFormula P₂ (P₁ + N) := by
    unfold C A awgnCapacityFormula log2
    have h1 : 0 < 1 + (P₁ + P₂) / N := by positivity
    have h2 : 0 < 1 + P₁ / N := by positivity
    have hdiv : (1 + (P₁ + P₂) / N) / (1 + P₁ / N) = 1 + P₂ / (P₁ + N) := by
      field_simp [hN.ne', (show P₁ + N ≠ 0 by linarith)]; ring
    rw [← mul_sub, ← sub_div, ← Real.log_div h1.ne' h2.ne', hdiv]
  -- All 5 vertices lie in `gaussianMACCapacityRegion P₁ P₂ N`
  have hv0 : (0, 0) ∈ gaussianMACCapacityRegion P₁ P₂ N :=
    subset_closure (isGaussianMACAchievable_of_awgn_left hP₂ (isAwgnAchievable_zero hP₁ N))
  have hv1 : (A, 0) ∈ gaussianMACCapacityRegion P₁ P₂ N := by
    rcases hA0.eq_or_lt with hA_eq | hA_pos
    · rw [← hA_eq]; exact hv0
    · rw [gaussianMACCapacityRegion, mem_closure_iff_seq_limit]
      refine ⟨fun m => ((1 - 1 / ((m + 2 : ℕ) : ℝ)) * A, 0), fun m => ?_, ?_⟩
      · have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
        have hc0 : 0 ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by
          rw [sub_nonneg, div_le_one hm]; exact_mod_cast (show 1 ≤ m + 2 by omega)
        have hc1 : 1 - 1 / ((m + 2 : ℕ) : ℝ) < 1 := by linarith [one_div_pos.mpr hm]
        exact isGaussianMACAchievable_of_awgn_left hP₂
          (isAwgnAchievable_of_lt_capacity hN hP₁ (mul_nonneg hc0 hA0) (by nlinarith))
      · have hlimA : Tendsto (fun m : ℕ => ((1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) * A) atTop (𝓝 A) := by
          simpa using tendsto_one_sub_inv_add_two.mul_const A
        exact hlimA.prodMk_nhds tendsto_const_nhds
  have hv4 : (0, B) ∈ gaussianMACCapacityRegion P₁ P₂ N := by
    rcases hB0.eq_or_lt with hB_eq | hB_pos
    · rw [← hB_eq]; exact hv0
    · rw [gaussianMACCapacityRegion, mem_closure_iff_seq_limit]
      refine ⟨fun m => (0, (1 - 1 / ((m + 2 : ℕ) : ℝ)) * B), fun m => ?_, ?_⟩
      · have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
        have hc0 : 0 ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by
          rw [sub_nonneg, div_le_one hm]; exact_mod_cast (show 1 ≤ m + 2 by omega)
        have hc1 : 1 - 1 / ((m + 2 : ℕ) : ℝ) < 1 := by linarith [one_div_pos.mpr hm]
        exact isGaussianMACAchievable_swap (isGaussianMACAchievable_of_awgn_left hP₁
          (isAwgnAchievable_of_lt_capacity hN hP₂ (mul_nonneg hc0 hB0) (by nlinarith)))
      · have hlimB : Tendsto (fun m : ℕ => ((1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) * B) atTop (𝓝 B) := by
          simpa using tendsto_one_sub_inv_add_two.mul_const B
        exact tendsto_const_nhds.prodMk_nhds hlimB
  have hv3 : (C - B, B) ∈ gaussianMACCapacityRegion P₁ P₂ N := by
    rcases hP₁.eq_or_lt with rfl | hP₁pos
    · have hCB0 : C - B = 0 := by rw [hCB_eq]; simp [awgnCapacityFormula, log2]
      rwa [hCB0]
    · rcases hP₂.eq_or_lt with rfl | hP₂pos
      · have hB0' : B = 0 := by simp [B, awgnCapacityFormula, log2]
        have hCA' : C = A := by simp [C, A]
        rwa [hB0', sub_zero, hCA']
      · rw [gaussianMACCapacityRegion, mem_closure_iff_seq_limit]
        refine ⟨fun m =>
          ((1 - 1 / ((m + 2 : ℕ) : ℝ)) * (C - B), (1 - 1 / ((m + 2 : ℕ) : ℝ)) * B),
          fun m => ?_, ?_⟩
        · have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
          have hc0 : 0 ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by
            rw [sub_nonneg, div_le_one hm]; exact_mod_cast (show 1 ≤ m + 2 by omega)
          have hc1 : 1 - 1 / ((m + 2 : ℕ) : ℝ) < 1 := by linarith [one_div_pos.mpr hm]
          have hCBpos : 0 < C - B := by
            rw [hCB_eq]; unfold awgnCapacityFormula log2
            have : 1 < 1 + P₁ / (P₂ + N) := by have := div_pos hP₁pos (by linarith : 0 < P₂ + N); linarith
            have := Real.log_pos this; positivity
          have hBpos : 0 < B := by
            unfold B awgnCapacityFormula log2
            have : 1 < 1 + P₂ / N := by have := div_pos hP₂pos hN; linarith
            have := Real.log_pos this; positivity
          exact gaussianMAC_corner_achievable hP₁pos hP₂pos hN
            (mul_nonneg hc0 hCBpos.le) (mul_nonneg hc0 hBpos.le)
            (by rw [← hCB_eq]; nlinarith) (by nlinarith)
        · have hlim1 : Tendsto (fun m : ℕ => ((1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) * (C - B)) atTop (𝓝 (C - B)) := by
            simpa using tendsto_one_sub_inv_add_two.mul_const (C - B)
          have hlim2 : Tendsto (fun m : ℕ => ((1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) * B) atTop (𝓝 B) := by
            simpa using tendsto_one_sub_inv_add_two.mul_const B
          exact hlim1.prodMk_nhds hlim2
  have hv2 : (A, C - A) ∈ gaussianMACCapacityRegion P₁ P₂ N := by
    rcases hP₂.eq_or_lt with rfl | hP₂pos
    · have hCA0 : C - A = 0 := by rw [hCA_eq]; simp [awgnCapacityFormula, log2]
      rwa [hCA0]
    · rcases hP₁.eq_or_lt with rfl | hP₁pos
      · have hA0' : A = 0 := by simp [A, awgnCapacityFormula, log2]
        have hCB' : C = B := by simp [C, B]
        rwa [hA0', sub_zero, hCB']
      · rw [gaussianMACCapacityRegion, mem_closure_iff_seq_limit]
        refine ⟨fun m =>
          ((1 - 1 / ((m + 2 : ℕ) : ℝ)) * A, (1 - 1 / ((m + 2 : ℕ) : ℝ)) * (C - A)),
          fun m => ?_, ?_⟩
        · have hm : (0 : ℝ) < (m + 2 : ℕ) := by positivity
          have hc0 : 0 ≤ 1 - 1 / ((m + 2 : ℕ) : ℝ) := by
            rw [sub_nonneg, div_le_one hm]; exact_mod_cast (show 1 ≤ m + 2 by omega)
          have hc1 : 1 - 1 / ((m + 2 : ℕ) : ℝ) < 1 := by linarith [one_div_pos.mpr hm]
          have hCApos : 0 < C - A := by
            rw [hCA_eq]; unfold awgnCapacityFormula log2
            have : 1 < 1 + P₂ / (P₁ + N) := by have := div_pos hP₂pos (by linarith : 0 < P₁ + N); linarith
            have := Real.log_pos this; positivity
          have hApos : 0 < A := by
            unfold A awgnCapacityFormula log2
            have : 1 < 1 + P₁ / N := by have := div_pos hP₁pos hN; linarith
            have := Real.log_pos this; positivity
          exact isGaussianMACAchievable_swap (gaussianMAC_corner_achievable hP₂pos hP₁pos hN
            (mul_nonneg hc0 hCApos.le) (mul_nonneg hc0 hApos.le)
            (by rw [← hCA_eq]; nlinarith) (by nlinarith))
        · have hlim1 : Tendsto (fun m : ℕ => ((1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) * A) atTop (𝓝 A) := by
            simpa using tendsto_one_sub_inv_add_two.mul_const A
          have hlim2 : Tendsto (fun m : ℕ => ((1 : ℝ) - 1 / ((m + 2 : ℕ) : ℝ)) * (C - A)) atTop (𝓝 (C - A)) := by
            simpa using tendsto_one_sub_inv_add_two.mul_const (C - A)
          exact hlim1.prodMk_nhds hlim2
  intro ⟨x, y⟩ ⟨hx0, hy0, hxA, hyB, hxyC⟩
  exact mem_convex_of_pentagon (gaussianMACCapacityRegion_convex P₁ P₂ N)
    hA0 hB0 hAC hBC hCAB hv0 hv1 hv2 hv3 hv4 hx0 hy0 hxA hyB hxyC

/-- **Exact Operational Capacity Region of the Two-User Scalar Gaussian MAC**
    (Cover & Thomas Theorem 15.1.1 / §15.3.6; El Gamal & Kim Theorem 4.6):
    for any powers `P₁, P₂ ≥ 0` and noise variance `N > 0`, the operational capacity region equals
    the pentagon `{(R₁, R₂) | 0 ≤ R₁ ≤ ½ log₂(1 + P₁/N), 0 ≤ R₂ ≤ ½ log₂(1 + P₂/N),
    R₁ + R₂ ≤ ½ log₂(1 + (P₁ + P₂)/N)}`. -/
theorem gaussianMACCapacityRegion_eq {P₁ P₂ N : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    gaussianMACCapacityRegion P₁ P₂ N = gaussianMACPentagon P₁ P₂ N :=
  Set.Subset.antisymm
    (gaussianMACCapacityRegion_subset_pentagon hP₁ hP₂ hN)
    (pentagon_subset_gaussianMACCapacityRegion hP₁ hP₂ hN)

end TimeSharingAndExactRegion

/-! ### 6. Scalar Gaussian Broadcast Channel: Superposition Coding Achievability

For the two-user degraded scalar Gaussian broadcast channel `Y₁ = X + Z₁`, `Y₂ = X + Z₂` with
`0 < N₁ ≤ N₂` and power budget `P ≥ 0`, every power split `α ∈ [0, 1]` achieves every strictly
interior rate pair `0 ≤ R₁ < ½ log₂(1 + α P / N₁)`, `0 ≤ R₂ < ½ log₂(1 + (1 - α) P / (α P + N₂))`
via superposition coding + successive decoding at the stronger receiver (Cover & Thomas Thm. 15.6.2;
El Gamal & Kim Thm. 5.3). -/

section GaussianBroadcast

/-- An `(n, M₁, M₂)` block code for the two-user scalar Gaussian broadcast channel:
    a single deterministic encoder `Fin M₁ → Fin M₂ → Fin n → ℝ` and two **measurable**
    decoders `decoder₁ : (Fin n → ℝ) → Fin M₁`, `decoder₂ : (Fin n → ℝ) → Fin M₂`. -/
structure GaussianBCCode (n M₁ M₂ : ℕ) where
  encoder : Fin M₁ → Fin M₂ → Fin n → ℝ
  decoder₁ : (Fin n → ℝ) → Fin M₁
  decoder₂ : (Fin n → ℝ) → Fin M₂
  measurable_decoder₁ : Measurable decoder₁
  measurable_decoder₂ : Measurable decoder₂

/-- Deterministic per-codeword power constraint `∑ᵢ x(m₁, m₂)ᵢ² ≤ n P` for all `(m₁, m₂)`. -/
def GaussianBCCode.SatisfiesPower {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂) (P : ℝ) : Prop :=
  ∀ (m₁ : Fin M₁) (m₂ : Fin M₂), ∑ i : Fin n, (C.encoder m₁ m₂ i) ^ 2 ≤ (n : ℝ) * P

/-- Conditional error probability at Receiver 1 (`Y₁ = X + Z₁`, `Z₁ ~ N(0, N₁)`). -/
noncomputable def gaussianBCErrorProb₁ {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂)
    (N₁ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ≥0∞ :=
  awgnNoise n N₁ {z | C.decoder₁ (C.encoder m₁ m₂ + z) ≠ m₁}

/-- Conditional error probability at Receiver 2 (`Y₂ = X + Z₂`, `Z₂ ~ N(0, N₂)`). -/
noncomputable def gaussianBCErrorProb₂ {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂)
    (N₂ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ≥0∞ :=
  awgnNoise n N₂ {z | C.decoder₂ (C.encoder m₁ m₂ + z) ≠ m₂}

/-- Average error probability at Receiver 1. -/
noncomputable def gaussianBCAvgError₁ {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂)
    (N₁ : ℝ) : ℝ≥0∞ :=
  ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ *
    ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, gaussianBCErrorProb₁ C N₁ m₁ m₂

/-- Average error probability at Receiver 2. -/
noncomputable def gaussianBCAvgError₂ {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂)
    (N₂ : ℝ) : ℝ≥0∞ :=
  ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ *
    ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, gaussianBCErrorProb₂ C N₂ m₁ m₂

/-- Operational achievability of rate pair `(R₁, R₂)` over the two-user scalar Gaussian BC
    with power `P` and noise variances `(N₁, N₂)`. -/
def IsGaussianBCAchievable (P N₁ N₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : GaussianBCCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊)
                           (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊),
      C.SatisfiesPower P ∧
      gaussianBCAvgError₁ C N₁ ≤ ENNReal.ofReal δ ∧
      gaussianBCAvgError₂ C N₂ ≤ ENNReal.ofReal δ

private lemma gaussianBCAvgError₁_ne_top {n M₁ M₂ : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (C : GaussianBCCode n M₁ M₂) (N₁ : ℝ) :
    gaussianBCAvgError₁ C N₁ ≠ ⊤ := by
  unfold gaussianBCAvgError₁
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))) ?_
  refine ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one

private lemma gaussianBCAvgError₂_ne_top {n M₁ M₂ : ℕ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (C : GaussianBCCode n M₁ M₂) (N₂ : ℝ) :
    gaussianBCAvgError₂ C N₂ ≠ ⊤ := by
  unfold gaussianBCAvgError₂
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))) ?_
  refine ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one

private lemma gaussianBCErrorProb₁_le_one {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂)
    (N₁ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : gaussianBCErrorProb₁ C N₁ m₁ m₂ ≤ 1 :=
  prob_le_one

private lemma gaussianBCErrorProb₂_le_one {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂)
    (N₂ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) : gaussianBCErrorProb₂ C N₂ m₁ m₂ ≤ 1 :=
  prob_le_one

private lemma gaussianBCAvgError₁_toReal {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂) (N₁ : ℝ) :
    (gaussianBCAvgError₁ C N₁).toReal =
      (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianBCErrorProb₁ C N₁ m₁ m₂).toReal := by
  unfold gaussianBCAvgError₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  congr 1
  rw [ENNReal.toReal_sum (fun m₁ _ => ENNReal.sum_ne_top.2 fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianBCErrorProb₁_le_one C N₁ m₁ m₂))]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  exact ENNReal.toReal_sum (fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianBCErrorProb₁_le_one C N₁ m₁ m₂))

private lemma gaussianBCAvgError₂_toReal {n M₁ M₂ : ℕ} (C : GaussianBCCode n M₁ M₂) (N₂ : ℝ) :
    (gaussianBCAvgError₂ C N₂).toReal =
      (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, (gaussianBCErrorProb₂ C N₂ m₁ m₂).toReal := by
  unfold gaussianBCAvgError₂
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  congr 1
  rw [ENNReal.toReal_sum (fun m₁ _ => ENNReal.sum_ne_top.2 fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianBCErrorProb₂_le_one C N₂ m₁ m₂))]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  exact ENNReal.toReal_sum (fun m₂ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (gaussianBCErrorProb₂_le_one C N₂ m₁ m₂))

/-- The discretized mean `E[qRound k U]` converges to `0` as `k → ∞`. -/
private lemma tendsto_mean_qRound (v : ℝ) :
    Tendsto (fun k : ℕ => ∫ u, qRound k u ∂gaussianReal 0 v.toNNReal) atTop (𝓝 0) := by
  have hdom : Integrable (fun u : ℝ => 2 + u ^ 2) (gaussianReal 0 v.toNNReal) := by
    simpa using integrable_const_add_mul_sq 2 1 v.toNNReal
  have hlim := tendsto_integral_of_dominated_convergence (μ := gaussianReal 0 v.toNNReal)
    (F := fun k u => qRound k u) (f := fun u => u) (fun u => 2 + u ^ 2)
    (fun k => (measurable_qRound k).aestronglyMeasurable) hdom
    (fun k => ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      have h1 := abs_qRound_le k u
      have h2 : |u| ≤ 1 + u ^ 2 := by nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
      linarith)
    (ae_of_all _ fun u => tendsto_qRound tendsto_const_nhds)
  simpa [integral_id_gaussianReal] using hlim

/-- The joint power `E[(X₁ + X₂)²]` under `gIn v₁ k × gIn v₂ k` converges to `v₁ + v₂`. -/
private lemma tendsto_sum_power {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) :
    Tendsto (fun k : ℕ =>
      meanCost ((gIn v₁ k).prod (gIn v₂ k)) (fun p => (qVal k p.1 + qVal k p.2) ^ 2))
      atTop (𝓝 (v₁ + v₂)) := by
  have hrew : ∀ k : ℕ,
      meanCost ((gIn v₁ k).prod (gIn v₂ k)) (fun p => (qVal k p.1 + qVal k p.2) ^ 2) =
        (∫ u, qRound k u ^ 2 ∂gaussianReal 0 v₁.toNNReal) +
        (∫ u, qRound k u ^ 2 ∂gaussianReal 0 v₂.toNNReal) +
        2 * (∫ u, qRound k u ∂gaussianReal 0 v₁.toNNReal) *
            (∫ u, qRound k u ∂gaussianReal 0 v₂.toNNReal) := by
    intro k
    unfold meanCost
    rw [Fintype.sum_prod_type]
    have hexp : ∀ i₁ i₂, ((gIn v₁ k).prod (gIn v₂ k)).pmf (i₁, i₂) * (qVal k i₁ + qVal k i₂) ^ 2 =
        (gIn v₁ k).pmf i₁ * (gIn v₂ k).pmf i₂ * qVal k i₁ ^ 2 +
        (gIn v₁ k).pmf i₁ * (gIn v₂ k).pmf i₂ * qVal k i₂ ^ 2 +
        2 * ((gIn v₁ k).pmf i₁ * qVal k i₁) * ((gIn v₂ k).pmf i₂ * qVal k i₂) := by
      intro i₁ i₂; simp only [ProbDist.prod]; ring
    simp_rw [hexp, Finset.sum_add_distrib]
    have h1 : ∑ i₁, ∑ i₂, (gIn v₁ k).pmf i₁ * (gIn v₂ k).pmf i₂ * qVal k i₁ ^ 2 =
        ∫ u, qRound k u ^ 2 ∂gaussianReal 0 v₁.toNNReal := by
      rw [← power_gIn_eq v₁ k]
      refine Finset.sum_congr rfl fun i₁ _ => ?_
      have : ∀ i₂, (gIn v₁ k).pmf i₁ * (gIn v₂ k).pmf i₂ * qVal k i₁ ^ 2 =
          ((gIn v₁ k).pmf i₁ * qVal k i₁ ^ 2) * (gIn v₂ k).pmf i₂ := fun _ => by ring
      simp_rw [this, ← Finset.mul_sum, (gIn v₂ k).sum_one, mul_one]
    have h2 : ∑ i₁, ∑ i₂, (gIn v₁ k).pmf i₁ * (gIn v₂ k).pmf i₂ * qVal k i₂ ^ 2 =
        ∫ u, qRound k u ^ 2 ∂gaussianReal 0 v₂.toNNReal := by
      rw [← power_gIn_eq v₂ k, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i₂ _ => ?_
      have : ∀ i₁, (gIn v₁ k).pmf i₁ * (gIn v₂ k).pmf i₂ * qVal k i₂ ^ 2 =
          ((gIn v₂ k).pmf i₂ * qVal k i₂ ^ 2) * (gIn v₁ k).pmf i₁ := fun _ => by ring
      simp_rw [this, ← Finset.mul_sum, (gIn v₁ k).sum_one, mul_one]
    have h3 : ∑ i₁, ∑ i₂, 2 * ((gIn v₁ k).pmf i₁ * qVal k i₁) * ((gIn v₂ k).pmf i₂ * qVal k i₂) =
        2 * (∫ u, qRound k u ∂gaussianReal 0 v₁.toNNReal) *
            (∫ u, qRound k u ∂gaussianReal 0 v₂.toNNReal) := by
      rw [← sum_gIn_mul v₁ k (fun a => a), ← sum_gIn_mul v₂ k (fun a => a)]
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.mul_sum]
    rw [h1, h2, h3]
  simp_rw [hrew]
  have hlim := ((tendsto_power hv₁).add (tendsto_power hv₂)).add
    (((tendsto_mean_qRound v₁).const_mul 2).mul (tendsto_mean_qRound v₂))
  simpa using hlim

/-- Expected joint power violation fraction under independent random codebooks equals
    `violProb ((gIn v₁ k).prod (gIn v₂ k)) (fun p => (qVal k p.1 + qVal k p.2)^2) P n`. -/
private lemma bc_expected_viol (v₁ v₂ P : ℝ) (k n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    let Q₁ := gIn v₁ k
    let Q₂ := gIn v₂ k
    let bsum : Fin (qCard k) × Fin (qCard k) → ℝ := fun p => (qVal k p.1 + qVal k p.2) ^ 2
    let violInd : (Fin M₁ → Fin n → Fin (qCard k)) → (Fin M₂ → Fin n → Fin (qCard k)) →
        Fin M₁ → Fin M₂ → ℝ := fun enc₁ enc₂ m₁ m₂ =>
      if (n : ℝ) * P < ∑ i : Fin n, (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)) ^ 2 then 1 else 0
    ∑ enc₁ : Fin M₁ → Fin n → Fin (qCard k), ∑ enc₂ : Fin M₂ → Fin n → Fin (qCard k),
      (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) *
      ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, violInd enc₁ enc₂ m₁ m₂) =
    violProb (Q₁.prod Q₂) bsum P n := by
  classical
  dsimp only
  set Q₁ := gIn v₁ k
  set Q₂ := gIn v₂ k
  set bsum : Fin (qCard k) × Fin (qCard k) → ℝ := fun p => (qVal k p.1 + qVal k p.2) ^ 2
  let violInd : (Fin M₁ → Fin n → Fin (qCard k)) → (Fin M₂ → Fin n → Fin (qCard k)) →
      Fin M₁ → Fin M₂ → ℝ := fun enc₁ enc₂ m₁ m₂ =>
    if (n : ℝ) * P < ∑ i : Fin n, (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)) ^ 2 then 1 else 0
  have hM₁r : (0 : ℝ) < M₁ := Nat.cast_pos.mpr hM₁
  have hM₂r : (0 : ℝ) < M₂ := Nat.cast_pos.mpr hM₂
  have hpair : ∀ (m₁ : Fin M₁) (m₂ : Fin M₂),
      ∑ enc₁ : Fin M₁ → Fin n → Fin (qCard k), ∑ enc₂ : Fin M₂ → Fin n → Fin (qCard k),
        (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) * violInd enc₁ enc₂ m₁ m₂ =
        violProb (Q₁.prod Q₂) bsum P n := by
    intro m₁ m₂
    have h1 : ∀ enc₁ : Fin M₁ → Fin n → Fin (qCard k),
        ∑ enc₂ : Fin M₂ → Fin n → Fin (qCard k),
          (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) * violInd enc₁ enc₂ m₁ m₂ =
        codebookProb Q₁ n M₁ enc₁ *
          ∑ x₂ : Fin n → Fin (qCard k), (iidDist Q₂ n).pmf x₂ *
            (if (n : ℝ) * P < ∑ i, (qVal k (enc₁ m₁ i) + qVal k (x₂ i)) ^ 2 then (1 : ℝ) else 0) := by
      intro enc₁
      simp_rw [mul_assoc, ← Finset.mul_sum]
      congr 1
      exact iidDist_sum_coord (iidDist Q₂ n)
        (fun x₂ => if (n : ℝ) * P < ∑ i, (qVal k (enc₁ m₁ i) + qVal k (x₂ i)) ^ 2 then (1 : ℝ) else 0) m₂
    simp_rw [h1]
    have h2 : ∑ enc₁ : Fin M₁ → Fin n → Fin (qCard k),
        codebookProb Q₁ n M₁ enc₁ *
          ∑ x₂ : Fin n → Fin (qCard k), (iidDist Q₂ n).pmf x₂ *
            (if (n : ℝ) * P < ∑ i, (qVal k (enc₁ m₁ i) + qVal k (x₂ i)) ^ 2 then (1 : ℝ) else 0) =
        ∑ x₁ : Fin n → Fin (qCard k), (iidDist Q₁ n).pmf x₁ *
          ∑ x₂ : Fin n → Fin (qCard k), (iidDist Q₂ n).pmf x₂ *
            (if (n : ℝ) * P < ∑ i, (qVal k (x₁ i) + qVal k (x₂ i)) ^ 2 then (1 : ℝ) else 0) :=
      iidDist_sum_coord (iidDist Q₁ n) (fun x₁ =>
        ∑ x₂ : Fin n → Fin (qCard k), (iidDist Q₂ n).pmf x₂ *
          (if (n : ℝ) * P < ∑ i, (qVal k (x₁ i) + qVal k (x₂ i)) ^ 2 then (1 : ℝ) else 0)) m₁
    rw [h2]
    let ez : (Fin n → Fin (qCard k) × Fin (qCard k)) ≃
        (Fin n → Fin (qCard k)) × (Fin n → Fin (qCard k)) :=
      { toFun := fun f => (fun i => (f i).1, fun i => (f i).2)
        invFun := fun p i => (p.1 i, p.2 i)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    unfold violProb CostViol
    rw [Fintype.sum_equiv ez _ (fun p =>
      if (n : ℝ) * P < ∑ i, (qVal k (p.1 i) + qVal k (p.2 i)) ^ 2
      then (iidDist Q₁ n).pmf p.1 * (iidDist Q₂ n).pmf p.2 else 0), Fintype.sum_prod_type]
    · refine Finset.sum_congr rfl fun x₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x₂ _ => ?_
      by_cases hlt : (n : ℝ) * P < ∑ i, (qVal k (x₁ i) + qVal k (x₂ i)) ^ 2 <;> simp [hlt]
    · intro f
      have hpmf : (iidDist (Q₁.prod Q₂) n).pmf f =
          (iidDist Q₁ n).pmf (fun i => (f i).1) * (iidDist Q₂ n).pmf (fun i => (f i).2) := by
        show (∏ i, (Q₁.pmf (f i).1 * Q₂.pmf (f i).2)) =
          (∏ i, Q₁.pmf (f i).1) * (∏ i, Q₂.pmf (f i).2)
        exact Finset.prod_mul_distrib
      simp only [ez, Equiv.coe_fn_mk, bsum, hpmf]
  have hpush : ∀ enc₁ enc₂,
      (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) *
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, violInd enc₁ enc₂ m₁ m₂) =
      (1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
        (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) * violInd enc₁ enc₂ m₁ m₂ := by
    intro enc₁ enc₂
    rw [← mul_assoc, mul_comm (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂),
      mul_assoc, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl fun m₁ _ => Finset.mul_sum _ _ _
  change ∑ enc₁, ∑ enc₂, (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) *
      ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, violInd enc₁ enc₂ m₁ m₂) = _
  simp_rw [hpush]
  rw [Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm, ← Finset.mul_sum]
  have hswap : ∑ enc₁, ∑ enc₂, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
      (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) * violInd enc₁ enc₂ m₁ m₂ =
      ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ enc₁, ∑ enc₂,
        (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) * violInd enc₁ enc₂ m₁ m₂ := by
    trans (∑ enc₁, ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ enc₂,
        (codebookProb Q₁ n M₁ enc₁ * codebookProb Q₂ n M₂ enc₂) * violInd enc₁ enc₂ m₁ m₂)
    · refine Finset.sum_congr rfl fun enc₁ _ => ?_
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
  rw [hswap]
  simp_rw [hpair, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [hM₁r.ne', hM₂r.ne']

/-- Finite-blocklength clipped superposition coding bound for the scalar Gaussian BC. -/
private theorem exists_bc_superposition_code {P N₁ N₂ v₁ v₂ : ℝ} (hP : 0 ≤ P)
    (k n M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε₁ ε₂₁ ε₂₂ : ℝ) :
    let Q₁ := gIn v₁ k
    let Q₂ := gIn v₂ k
    let W₁ := gChan N₁ k
    let W₂₁ := gInterfChan v₁ N₁ k
    let W₂₂ := gInterfChan v₁ N₂ k
    let bsum : Fin (qCard k) × Fin (qCard k) → ℝ := fun p => (qVal k p.1 + qVal k p.2) ^ 2
    ∃ C : GaussianBCCode n M₁ M₂,
      C.SatisfiesPower P ∧
      (gaussianBCAvgError₁ C N₁).toReal + (gaussianBCAvgError₂ C N₂).toReal ≤
        (1 - ∑ xy ∈ jointTypicalSet (W₂₁.joint Q₂) n ε₂₁, (jointIidDist (W₂₁.joint Q₂) n).pmf xy) +
        ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₁.mutualInfo Q₂ - 3 * ε₂₁))) +
        (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
        ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) +
        (1 - ∑ xy ∈ jointTypicalSet (W₂₂.joint Q₂) n ε₂₂, (jointIidDist (W₂₂.joint Q₂) n).pmf xy) +
        ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₂.mutualInfo Q₂ - 3 * ε₂₂))) +
        2 * violProb (Q₁.prod Q₂) bsum P n := by
  classical
  dsimp only
  set Q₁ := gIn v₁ k
  set Q₂ := gIn v₂ k
  set W₁ := gChan N₁ k
  set W₂₁ := gInterfChan v₁ N₁ k
  set W₂₂ := gInterfChan v₁ N₂ k
  set bsum : Fin (qCard k) × Fin (qCard k) → ℝ := fun p => (qVal k p.1 + qVal k p.2) ^ 2
  have hM₁r : (0 : ℝ) < M₁ := Nat.cast_pos.mpr hM₁
  have hM₂r : (0 : ℝ) < M₂ := Nat.cast_pos.mpr hM₂
  let dec₁Of := fun enc₁ => jointTypicalDec (W₁.joint Q₁) n M₁ hM₁ ε₁ enc₁
  let dec₂₁Of := fun enc₂ => jointTypicalDec (W₂₁.joint Q₂) n M₂ hM₂ ε₂₁ enc₂
  let dec₂₂Of := fun enc₂ => jointTypicalDec (W₂₂.joint Q₂) n M₂ hM₂ ε₂₂ enc₂
  let mkBC : (Fin M₁ → Fin n → Fin (qCard k)) → (Fin M₂ → Fin n → Fin (qCard k)) →
      GaussianBCCode n M₁ M₂ := fun enc₁ enc₂ =>
    { encoder := fun m₁ m₂ =>
        if ∑ i : Fin n, (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)) ^ 2 ≤ (n : ℝ) * P
        then fun i => qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)
        else fun _ => 0
      decoder₁ := fun y =>
        let m2hat := dec₂₁Of enc₂ (fun i => qIdx k (y i))
        dec₁Of enc₁ (fun i => qIdx k (y i - qVal k (enc₂ m2hat i)))
      decoder₂ := fun y => dec₂₂Of enc₂ (fun i => qIdx k (y i))
      measurable_decoder₁ := by
        have hm₂ : Measurable (fun y : Fin n → ℝ => dec₂₁Of enc₂ (fun i => qIdx k (y i))) :=
          (measurable_of_finite (dec₂₁Of enc₂)).comp
            (measurable_pi_iff.mpr fun i => (measurable_qIdx k).comp (measurable_pi_apply i))
        refine (measurable_of_finite (dec₁Of enc₁)).comp (measurable_pi_iff.mpr fun i => ?_)
        exact (measurable_qIdx k).comp ((measurable_pi_apply i).sub
          ((measurable_of_finite (fun m => qVal k (enc₂ m i))).comp hm₂))
      measurable_decoder₂ :=
        (measurable_of_finite (dec₂₂Of enc₂)).comp
          (measurable_pi_iff.mpr fun i => (measurable_qIdx k).comp (measurable_pi_apply i)) }
  have hbc_pow : ∀ enc₁ enc₂, (mkBC enc₁ enc₂).SatisfiesPower P := by
    intro enc₁ enc₂ m₁ m₂
    dsimp only [mkBC]
    split_ifs with h
    · exact h
    · simp; positivity
  let violInd : (Fin M₁ → Fin n → Fin (qCard k)) → (Fin M₂ → Fin n → Fin (qCard k)) →
      Fin M₁ → Fin M₂ → ℝ := fun enc₁ enc₂ m₁ m₂ =>
    if (n : ℝ) * P < ∑ i : Fin n, (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)) ^ 2 then 1 else 0
  have herr₁_pt : ∀ enc₁ enc₂ m₁ m₂,
      (gaussianBCErrorProb₁ (mkBC enc₁ enc₂) N₁ m₁ m₂).toReal ≤
        (∑ y : Fin n → Fin (qCard k),
          if dec₂₁Of enc₂ y ≠ m₂ then ((gMacChan N₁ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) +
        msgError W₁ enc₁ (dec₁Of enc₁) m₁ + violInd enc₁ enc₂ m₁ m₂ := by
    intro enc₁ enc₂ m₁ m₂
    by_cases hv : ∑ i : Fin n, (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)) ^ 2 ≤ (n : ℝ) * P
    · have hvi : violInd enc₁ enc₂ m₁ m₂ = 0 := by simp [violInd, not_lt.mpr hv]
      rw [hvi, add_zero]
      let E₁ : Set (Fin n → ℝ) :=
        {z | dec₂₁Of enc₂ (fun i => qIdx k (qVal k (enc₂ m₂ i) + qVal k (enc₁ m₁ i) + z i)) ≠ m₂}
      let E₂ : Set (Fin n → ℝ) :=
        {z | dec₁Of enc₁ (fun i => qIdx k (qVal k (enc₁ m₁ i) + z i)) ≠ m₁}
      have hsub : {z : Fin n → ℝ | (mkBC enc₁ enc₂).decoder₁ ((mkBC enc₁ enc₂).encoder m₁ m₂ + z) ≠ m₁} ⊆
          E₁ ∪ E₂ := by
        intro z hz
        simp only [Set.mem_ofPred_eq, mkBC, hv, ↓reduceIte, Pi.add_apply, ne_eq] at hz
        by_cases h2 : dec₂₁Of enc₂ (fun i => qIdx k (qVal k (enc₂ m₂ i) + qVal k (enc₁ m₁ i) + z i)) = m₂
        · right
          simp only [E₂, Set.mem_ofPred_eq, ne_eq]
          intro h1
          apply hz
          have hcomm : (fun i => qIdx k (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i) + z i)) =
              (fun i => qIdx k (qVal k (enc₂ m₂ i) + qVal k (enc₁ m₁ i) + z i)) := by
            funext i; congr 1; ring
          rw [hcomm, h2]
          have hcancel : (fun i => qIdx k (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i) + z i -
              qVal k (enc₂ m₂ i))) = (fun i => qIdx k (qVal k (enc₁ m₁ i) + z i)) := by
            funext i; congr 1; ring
          rw [hcancel]; exact h1
        · left; exact h2
      have hmeas : gaussianBCErrorProb₁ (mkBC enc₁ enc₂) N₁ m₁ m₂ ≤
          awgnNoise n N₁ E₁ + awgnNoise n N₁ E₂ :=
        le_trans (measure_mono hsub) (measure_union_le E₁ E₂)
      have hreal : (gaussianBCErrorProb₁ (mkBC enc₁ enc₂) N₁ m₁ m₂).toReal ≤
          (awgnNoise n N₁ E₁).toReal + (awgnNoise n N₁ E₂).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hmeas
      rw [stage1_error_toReal N₁ k n M₂ (enc₂ m₂) (enc₁ m₁) (dec₂₁Of enc₂) m₂] at hreal
      have hE2 : (awgnNoise n N₁ E₂).toReal = msgError W₁ enc₁ (dec₁Of enc₁) m₁ :=
        quantCode_errorProb_toReal N₁ (qVal k) (qIdx k) (measurable_qIdx k) enc₁ (dec₁Of enc₁) m₁
      rwa [hE2] at hreal
    · have hvi : violInd enc₁ enc₂ m₁ m₂ = 1 := by simp [violInd, lt_of_not_ge hv]
      rw [hvi]
      have hle1 : (gaussianBCErrorProb₁ (mkBC enc₁ enc₂) N₁ m₁ m₂).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top (gaussianBCErrorProb₁_le_one (mkBC enc₁ enc₂) N₁ m₁ m₂)
      have hn1' : 0 ≤ ∑ y : Fin n → Fin (qCard k),
          if dec₂₁Of enc₂ y ≠ m₂ then ((gMacChan N₁ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0 :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [(DMC.power _ _).nonneg]
      have hn2' : 0 ≤ msgError W₁ enc₁ (dec₁Of enc₁) m₁ := msgError_nonneg _ _ _ _
      linarith
  have herr₂_pt : ∀ enc₁ enc₂ m₁ m₂,
      (gaussianBCErrorProb₂ (mkBC enc₁ enc₂) N₂ m₁ m₂).toReal ≤
        (∑ y : Fin n → Fin (qCard k),
          if dec₂₂Of enc₂ y ≠ m₂ then ((gMacChan N₂ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) +
        violInd enc₁ enc₂ m₁ m₂ := by
    intro enc₁ enc₂ m₁ m₂
    by_cases hv : ∑ i : Fin n, (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i)) ^ 2 ≤ (n : ℝ) * P
    · have hvi : violInd enc₁ enc₂ m₁ m₂ = 0 := by simp [violInd, not_lt.mpr hv]
      rw [hvi, add_zero]
      have heq : (gaussianBCErrorProb₂ (mkBC enc₁ enc₂) N₂ m₁ m₂).toReal =
          (awgnNoise n N₂ {z | dec₂₂Of enc₂ (fun i => qIdx k (qVal k (enc₂ m₂ i) + qVal k (enc₁ m₁ i) + z i)) ≠ m₂}).toReal := by
        unfold gaussianBCErrorProb₂
        congr 2; ext z
        simp only [Set.mem_ofPred_eq, mkBC, hv, ↓reduceIte, Pi.add_apply, ne_eq]
        have hcomm : (fun i => qIdx k (qVal k (enc₁ m₁ i) + qVal k (enc₂ m₂ i) + z i)) =
            (fun i => qIdx k (qVal k (enc₂ m₂ i) + qVal k (enc₁ m₁ i) + z i)) := by
          funext i; congr 1; ring
        rw [hcomm]
      rw [heq, stage1_error_toReal N₂ k n M₂ (enc₂ m₂) (enc₁ m₁) (dec₂₂Of enc₂) m₂]
    · have hvi : violInd enc₁ enc₂ m₁ m₂ = 1 := by simp [violInd, lt_of_not_ge hv]
      rw [hvi]
      have hle1 : (gaussianBCErrorProb₂ (mkBC enc₁ enc₂) N₂ m₁ m₂).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top (gaussianBCErrorProb₂_le_one (mkBC enc₁ enc₂) N₂ m₁ m₂)
      have hn1' : 0 ≤ ∑ y : Fin n → Fin (qCard k),
          if dec₂₂Of enc₂ y ≠ m₂ then ((gMacChan N₂ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0 :=
        Finset.sum_nonneg fun _ _ => by split_ifs <;> simp [(DMC.power _ _).nonneg]
      linarith
  set w₁ := codebookProb Q₁ n M₁
  set w₂ := codebookProb Q₂ n M₂
  have hw₁_sum : ∑ enc₁, w₁ enc₁ = 1 := codebookProb_sum_one Q₁ n M₁
  have hw₂_sum : ∑ enc₂, w₂ enc₂ = 1 := codebookProb_sum_one Q₂ n M₂
  have hexp_interf : ∀ (N' ε' : ℝ) (decOf : (Fin M₂ → Fin n → Fin (qCard k)) → (Fin n → Fin (qCard k)) → Fin M₂),
      decOf = (fun enc₂ => jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂) →
      ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          ∑ y : Fin n → Fin (qCard k),
            if decOf enc₂ y ≠ m₂ then ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) ≤
        (1 - ∑ xy ∈ jointTypicalSet ((gInterfChan v₁ N' k).joint Q₂) n ε',
            (jointIidDist ((gInterfChan v₁ N' k).joint Q₂) n).pmf xy) +
        ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((gInterfChan v₁ N' k).mutualInfo Q₂ - 3 * ε'))) := by
    intro N' ε' decOf hdec
    subst hdec
    rw [Finset.sum_comm]
    have hinner : ∀ enc₂, ∑ enc₁, (w₁ enc₁ * w₂ enc₂) *
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
          ∑ y : Fin n → Fin (qCard k),
            if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
            then ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) =
        w₂ enc₂ * dmcAvgError (gInterfChan v₁ N' k) n M₂ enc₂
          (jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂) := by
      intro enc₂
      have hfac : ∀ enc₁, (w₁ enc₁ * w₂ enc₂) *
          ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂,
            ∑ y : Fin n → Fin (qCard k),
              if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
              then ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) =
          w₂ enc₂ * (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
            ∑ m₂ : Fin M₂, ∑ m₁ : Fin M₁, ∑ y : Fin n → Fin (qCard k),
              if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
              then w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0 := by
        intro enc₁
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        have : ∀ m₂ m₁ y, w₁ enc₁ * (if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
              then ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) =
            if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
            then w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0 := by
          intro m₂ m₁ y; split_ifs <;> ring
        have hpush : (w₁ enc₁ * w₂ enc₂) * (1 / ((M₁ * M₂ : ℕ) : ℝ)) =
            (w₂ enc₂ * (1 / ((M₁ * M₂ : ℕ) : ℝ))) * w₁ enc₁ := by ring
        rw [← mul_assoc, hpush, mul_assoc, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun m₂ _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => this m₂ m₁ y
      simp_rw [hfac, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have hm₂ : ∀ m₂ : Fin M₂,
          ∑ enc₁, ∑ m₁ : Fin M₁, ∑ y : Fin n → Fin (qCard k),
            (if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
             then w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) =
          (M₁ : ℝ) * ∑ y : Fin n → Fin (qCard k),
            if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
            then ((gInterfChan v₁ N' k).power n).trans (enc₂ m₂) y else 0 := by
        intro m₂
        rw [Finset.sum_comm]
        have hm₁ : ∀ m₁ : Fin M₁,
            ∑ enc₁, ∑ y : Fin n → Fin (qCard k),
              (if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
               then w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) =
            ∑ y : Fin n → Fin (qCard k),
              if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
              then ((gInterfChan v₁ N' k).power n).trans (enc₂ m₂) y else 0 := by
          intro m₁
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases hy : jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
          · have hte : ∀ enc₁, (if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
                then w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) =
                w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y :=
              fun _ => ite_eq_left_iff.mpr fun h => absurd hy h
            rw [Finset.sum_congr rfl fun enc₁ _ => hte enc₁,
              ite_eq_left_iff.mpr fun h => absurd hy h]
            exact sum_codebookProb_gMacChan v₁ N' k n M₁ (enc₂ m₂) y m₁
          · have hte : ∀ enc₁, (if jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂ y ≠ m₂
                then w₁ enc₁ * ((gMacChan N' k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) = 0 :=
              fun _ => ite_eq_right_iff.mpr fun h => absurd h hy
            rw [Finset.sum_congr rfl fun enc₁ _ => hte enc₁, Finset.sum_const_zero,
              ite_eq_right_iff.mpr fun h => absurd h hy]
        simp_rw [hm₁, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp_rw [hm₂, ← Finset.mul_sum]
      rw [dmcAvgError_eq_msgError (gInterfChan v₁ N' k) hM₂ enc₂ _]
      unfold msgError
      push_cast
      field_simp [hM₁r.ne', hM₂r.ne']
    simp_rw [hinner]
    have hexp : ∑ enc₂, w₂ enc₂ * dmcAvgError (gInterfChan v₁ N' k) n M₂ enc₂
          (jointTypicalDec ((gInterfChan v₁ N' k).joint Q₂) n M₂ hM₂ ε' enc₂) ≤
        (1 - ∑ xy ∈ jointTypicalSet ((gInterfChan v₁ N' k).joint Q₂) n ε',
            (jointIidDist ((gInterfChan v₁ N' k).joint Q₂) n).pmf xy) +
        ((M₂ - 1 : ℕ) : ℝ) *
          (∑ xy ∈ jointTypicalSet ((gInterfChan v₁ N' k).joint Q₂) n ε',
            ((iidDist ((gInterfChan v₁ N' k).joint Q₂).fst n).prod
              (iidDist ((gInterfChan v₁ N' k).joint Q₂).snd n)).pmf xy) :=
      dmc_random_coding_expected_error_le (gInterfChan v₁ N' k) Q₂ n M₂ hM₂ ε'
    have hindep : ∑ xy ∈ jointTypicalSet ((gInterfChan v₁ N' k).joint Q₂) n ε',
          ((iidDist ((gInterfChan v₁ N' k).joint Q₂).fst n).prod
            (iidDist ((gInterfChan v₁ N' k).joint Q₂).snd n)).pmf xy ≤
        (2 : ℝ) ^ (-((n : ℝ) * ((gInterfChan v₁ N' k).mutualInfo Q₂ - 3 * ε'))) :=
      jointTypicalSet_indep_prob_le ((gInterfChan v₁ N' k).joint Q₂) n ε'
    have hmul := mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg (M₂ - 1))
    linarith
  have hexp_s2 : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
      ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂,
        msgError W₁ enc₁ (dec₁Of enc₁) m₁) ≤
      (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
      ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) := by
    have hsimp : ∀ enc₁ enc₂, (w₁ enc₁ * w₂ enc₂) *
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ _m₂ : Fin M₂,
          msgError W₁ enc₁ (dec₁Of enc₁) m₁) =
        w₂ enc₂ * (w₁ enc₁ * dmcAvgError W₁ n M₁ enc₁ (dec₁Of enc₁)) := by
      intro enc₁ enc₂
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum, dmcAvgError_eq_msgError W₁ hM₁ enc₁ (dec₁Of enc₁)]
      push_cast
      field_simp [hM₁r.ne', hM₂r.ne']
    simp_rw [hsimp]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hw₂_sum, one_mul]
    have hexp : ∑ enc₁, w₁ enc₁ * dmcAvgError W₁ n M₁ enc₁ (dec₁Of enc₁) ≤
        (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
        ((M₁ - 1 : ℕ) : ℝ) *
          (∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁,
            ((iidDist (W₁.joint Q₁).fst n).prod (iidDist (W₁.joint Q₁).snd n)).pmf xy) :=
      dmc_random_coding_expected_error_le W₁ Q₁ n M₁ hM₁ ε₁
    have hindep : ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁,
          ((iidDist (W₁.joint Q₁).fst n).prod (iidDist (W₁.joint Q₁).snd n)).pmf xy ≤
        (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) :=
      jointTypicalSet_indep_prob_le (W₁.joint Q₁) n ε₁
    have hmul := mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg (M₁ - 1))
    linarith
  have hexp_viol : ∑ enc₁, ∑ enc₂, (w₁ enc₁ * w₂ enc₂) *
      ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, violInd enc₁ enc₂ m₁ m₂) =
      violProb (Q₁.prod Q₂) bsum P n :=
    bc_expected_viol v₁ v₂ P k n M₁ M₂ hM₁ hM₂
  have h1 := hexp_interf N₁ ε₂₁ dec₂₁Of rfl
  have h2 := hexp_interf N₂ ε₂₂ dec₂₂Of rfl
  let w : ((Fin M₁ → Fin n → Fin (qCard k)) × (Fin M₂ → Fin n → Fin (qCard k))) → ℝ :=
    fun p => w₁ p.1 * w₂ p.2
  have hw0 : ∀ p, 0 ≤ w p := fun p =>
    mul_nonneg (codebookProb_nonneg Q₁ n M₁ p.1) (codebookProb_nonneg Q₂ n M₂ p.2)
  have hw1 : ∑ p, w p = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [w, ← Finset.mul_sum, hw₂_sum, mul_one, hw₁_sum]
  set RHS :=
    (1 - ∑ xy ∈ jointTypicalSet (W₂₁.joint Q₂) n ε₂₁, (jointIidDist (W₂₁.joint Q₂) n).pmf xy) +
    ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₁.mutualInfo Q₂ - 3 * ε₂₁))) +
    (1 - ∑ xy ∈ jointTypicalSet (W₁.joint Q₁) n ε₁, (jointIidDist (W₁.joint Q₁) n).pmf xy) +
    ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) +
    (1 - ∑ xy ∈ jointTypicalSet (W₂₂.joint Q₂) n ε₂₂, (jointIidDist (W₂₂.joint Q₂) n).pmf xy) +
    ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₂.mutualInfo Q₂ - 3 * ε₂₂))) +
    2 * violProb (Q₁.prod Q₂) bsum P n
  have hsum_le : ∑ p : (Fin M₁ → Fin n → Fin (qCard k)) × (Fin M₂ → Fin n → Fin (qCard k)),
      w p * ((gaussianBCAvgError₁ (mkBC p.1 p.2) N₁).toReal +
             (gaussianBCAvgError₂ (mkBC p.1 p.2) N₂).toReal) ≤ RHS := by
    rw [Fintype.sum_prod_type]
    have hpt : ∀ enc₁ enc₂,
        (gaussianBCAvgError₁ (mkBC enc₁ enc₂) N₁).toReal +
        (gaussianBCAvgError₂ (mkBC enc₁ enc₂) N₂).toReal ≤
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ y,
          if dec₂₁Of enc₂ y ≠ m₂ then ((gMacChan N₁ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) +
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ _m₂ : Fin M₂, msgError W₁ enc₁ (dec₁Of enc₁) m₁) +
        ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ y,
          if dec₂₂Of enc₂ y ≠ m₂ then ((gMacChan N₂ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) +
        2 * ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, violInd enc₁ enc₂ m₁ m₂) := by
      intro enc₁ enc₂
      rw [gaussianBCAvgError₁_toReal, gaussianBCAvgError₂_toReal]
      have h1' : (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁, ∑ m₂, (gaussianBCErrorProb₁ (mkBC enc₁ enc₂) N₁ m₁ m₂).toReal ≤
          ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ y,
            if dec₂₁Of enc₂ y ≠ m₂ then ((gMacChan N₁ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) +
          ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ _m₂ : Fin M₂, msgError W₁ enc₁ (dec₁Of enc₁) m₁) +
          ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, violInd enc₁ enc₂ m₁ m₂) := by
        rw [← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp_rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => herr₁_pt enc₁ enc₂ m₁ m₂
      have h2' : (1 / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁, ∑ m₂, (gaussianBCErrorProb₂ (mkBC enc₁ enc₂) N₂ m₁ m₂).toReal ≤
          ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, ∑ y,
            if dec₂₂Of enc₂ y ≠ m₂ then ((gMacChan N₂ k).power n).trans (fun i => (enc₂ m₂ i, enc₁ m₁ i)) y else 0) +
          ((1 / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁, ∑ m₂, violInd enc₁ enc₂ m₁ m₂) := by
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp_rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => herr₂_pt enc₁ enc₂ m₁ m₂
      linarith
    have hstep := Finset.sum_le_sum fun enc₁ (_ : enc₁ ∈ Finset.univ) =>
      Finset.sum_le_sum fun enc₂ (_ : enc₂ ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (hpt enc₁ enc₂) (hw0 (enc₁, enc₂))
    refine le_trans hstep ?_
    dsimp only [w]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h2v : ∑ enc₁, ∑ enc₂, w₁ enc₁ * w₂ enc₂ *
        (2 * (1 / ((M₁ * M₂ : ℕ) : ℝ) * ∑ m₁, ∑ m₂, violInd enc₁ enc₂ m₁ m₂)) =
        2 * violProb (Q₁.prod Q₂) bsum P n := by
      have : ∀ enc₁ enc₂, w₁ enc₁ * w₂ enc₂ *
          (2 * (1 / ((M₁ * M₂ : ℕ) : ℝ) * ∑ m₁, ∑ m₂, violInd enc₁ enc₂ m₁ m₂)) =
          2 * ((w₁ enc₁ * w₂ enc₂) * (1 / ((M₁ * M₂ : ℕ) : ℝ) * ∑ m₁, ∑ m₂, violInd enc₁ enc₂ m₁ m₂)) :=
        fun _ _ => by ring
      simp_rw [this, ← Finset.mul_sum, hexp_viol]
    rw [h2v]
    exact le_trans
      (add_le_add (add_le_add (add_le_add h1 hexp_s2) h2) (le_refl (2 * violProb (Q₁.prod Q₂) bsum P n)))
      (le_of_eq (by dsimp only [RHS]; ring))
  obtain ⟨⟨enc₁, enc₂⟩, hbest⟩ := exists_le_of_weighted_sum_le_cc w
    (fun p => (gaussianBCAvgError₁ (mkBC p.1 p.2) N₁).toReal +
              (gaussianBCAvgError₂ (mkBC p.1 p.2) N₂).toReal)
    RHS hw0 hw1 hsum_le
  exact ⟨mkBC enc₁ enc₂, hbc_pow enc₁ enc₂, hbest⟩

/-- **Superposition Coding Achievability for the Scalar Gaussian Broadcast Channel**
    (Cover & Thomas Theorem 15.6.2; El Gamal & Kim Theorem 5.3):
    for noise variances `0 < N₁ ≤ N₂`, power `P ≥ 0`, power split `α ∈ [0, 1]`, and any
    strictly interior rate pair `0 ≤ R₁ < ½ log₂(1 + α P / N₁)`,
    `0 ≤ R₂ < ½ log₂(1 + (1 - α) P / (α P + N₂))`, the pair `(R₁, R₂)` is operationally
    achievable with deterministic per-codeword power constraint `∑ᵢ x(m₁, m₂)ᵢ² ≤ n P` and
    measurable decoders. -/
theorem gaussianBC_superposition_achievable {P N₁ N₂ α R₁ R₂ : ℝ}
    (hP : 0 ≤ P) (hN₁ : 0 < N₁) (hN₁₂ : N₁ ≤ N₂)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hR₁0 : 0 ≤ R₁) (hR₂0 : 0 ≤ R₂)
    (hR₁ : R₁ < awgnCapacityFormula (α * P) N₁)
    (hR₂ : R₂ < awgnCapacityFormula ((1 - α) * P) (α * P + N₂)) :
    IsGaussianBCAchievable P N₁ N₂ R₁ R₂ := by
  have hN₂ : 0 < N₂ := lt_of_lt_of_le hN₁ hN₁₂
  have hP₁ : 0 < α * P := by
    by_contra hle; push Not at hle
    have h0 : α * P = 0 := le_antisymm hle (mul_nonneg hα0 hP)
    rw [h0] at hR₁; simp [awgnCapacityFormula, log2] at hR₁; linarith
  have hP₂ : 0 < (1 - α) * P := by
    by_contra hle; push Not at hle
    have h0 : (1 - α) * P = 0 := le_antisymm hle (mul_nonneg (by linarith) hP)
    rw [h0] at hR₂; simp [awgnCapacityFormula, log2] at hR₂; linarith
  have hcont₁ : ContinuousAt (fun w => awgnCapacityFormula w N₁) (α * P) := by
    unfold awgnCapacityFormula log2
    have h1 : (1 + α * P / N₁) ≠ 0 := by positivity
    exact (((continuousAt_const.add (continuousAt_id.div_const N₁)).log h1).div_const _).const_mul _
  have hev₁ : ∀ᶠ v₁ in 𝓝[<] (α * P), R₁ < awgnCapacityFormula v₁ N₁ ∧ v₁ ∈ Set.Ioo 0 (α * P) :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont₁.eventually (lt_mem_nhds hR₁))).and
      (Ioo_mem_nhdsLT hP₁)
  obtain ⟨v₁, hv₁R₁, hv₁0, hv₁P₁⟩ := hev₁.exists
  have hR₂_v₁ : R₂ < awgnCapacityFormula ((1 - α) * P) (v₁ + N₂) := by
    refine lt_of_lt_of_le hR₂ ?_
    unfold awgnCapacityFormula log2
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hdiv : (1 - α) * P / (α * P + N₂) ≤ (1 - α) * P / (v₁ + N₂) :=
      div_le_div_of_nonneg_left hP₂.le (by linarith) (by linarith)
    gcongr
  have hcont₂ : ContinuousAt (fun w => awgnCapacityFormula w (v₁ + N₂)) ((1 - α) * P) := by
    unfold awgnCapacityFormula log2
    have h1 : (1 + (1 - α) * P / (v₁ + N₂)) ≠ 0 := by positivity
    exact (((continuousAt_const.add (continuousAt_id.div_const (v₁ + N₂))).log h1).div_const _).const_mul _
  have hev₂ : ∀ᶠ v₂ in 𝓝[<] ((1 - α) * P),
      R₂ < awgnCapacityFormula v₂ (v₁ + N₂) ∧ v₂ ∈ Set.Ioo 0 ((1 - α) * P) :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hcont₂.eventually (lt_mem_nhds hR₂_v₁))).and
      (Ioo_mem_nhdsLT hP₂)
  obtain ⟨v₂, hv₂R₂_2, hv₂0, hv₂P₂⟩ := hev₂.exists
  have hv₂R₂_1 : R₂ < awgnCapacityFormula v₂ (v₁ + N₁) := by
    refine lt_of_lt_of_le hv₂R₂_2 ?_
    unfold awgnCapacityFormula log2
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hdiv : v₂ / (v₁ + N₂) ≤ v₂ / (v₁ + N₁) :=
      div_le_div_of_nonneg_left hv₂0.le (by linarith) (by linarith)
    gcongr
  have hvsum : v₁ + v₂ < P := by linarith
  have hev_k := ((eventually_single_mutualInfo_gt hv₁0 hN₁ hv₁R₁).and
      (eventually_interf_mutualInfo_gt hv₂0 hv₁0 hN₁ hv₂R₂_1)).and
    ((eventually_interf_mutualInfo_gt hv₂0 hv₁0 hN₂ hv₂R₂_2).and
      ((tendsto_order.1 (tendsto_sum_power hv₁0 hv₂0)).2 P hvsum))
  obtain ⟨k, ⟨hI₁, hI₂₁⟩, ⟨hI₂₂, hpow⟩⟩ := hev_k.exists
  refine ⟨hR₁0, hR₂0, fun δ hδ => ?_⟩
  set Q₁ := gIn v₁ k
  set Q₂ := gIn v₂ k
  set W₁ := gChan N₁ k
  set W₂₁ := gInterfChan v₁ N₁ k
  set W₂₂ := gInterfChan v₁ N₂ k
  set bsum : Fin (qCard k) × Fin (qCard k) → ℝ := fun p => (qVal k p.1 + qVal k p.2) ^ 2
  set ε₁ : ℝ := (W₁.mutualInfo Q₁ - R₁) / 4
  set ε₂₁ : ℝ := (W₂₁.mutualInfo Q₂ - R₂) / 4
  set ε₂₂ : ℝ := (W₂₂.mutualInfo Q₂ - R₂) / 4
  have hε₁ : 0 < ε₁ := by dsimp only [ε₁]; linarith
  have hε₂₁ : 0 < ε₂₁ := by dsimp only [ε₂₁]; linarith
  have hε₂₂ : 0 < ε₂₂ := by dsimp only [ε₂₂]; linarith
  set t : ℝ := δ / 8 with ht_def
  have ht : 0 < t := by rw [ht_def]; positivity
  obtain ⟨K₁, hK₁⟩ := joint_aep_prob_tendsto_one (W₁.joint Q₁) hε₁ ht
  obtain ⟨K₂₁, hK₂₁⟩ := joint_aep_prob_tendsto_one (W₂₁.joint Q₂) hε₂₁ ht
  obtain ⟨K₂₂, hK₂₂⟩ := joint_aep_prob_tendsto_one (W₂₂.joint Q₂) hε₂₂ ht
  have hev_n : ∀ᶠ n : ℕ in atTop,
      (K₁ ≤ n ∧ K₂₁ ≤ n ∧ K₂₂ ≤ n) ∧
      ((2 : ℝ) ^ (-((n : ℝ) * ε₁)) ≤ t ∧
       (2 : ℝ) ^ (-((n : ℝ) * ε₂₁)) ≤ t ∧
       (2 : ℝ) ^ (-((n : ℝ) * ε₂₂)) ≤ t) ∧
      violProb (Q₁.prod Q₂) bsum P n ≤ t :=
    ((eventually_ge_atTop K₁).and ((eventually_ge_atTop K₂₁).and (eventually_ge_atTop K₂₂))).and
      (((eventually_two_rpow_neg_le hε₁ ht).and
        ((eventually_two_rpow_neg_le hε₂₁ ht).and (eventually_two_rpow_neg_le hε₂₂ ht))).and
        (violProb_eventually_le (Q₁.prod Q₂) bsum hpow ht))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev_n
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨⟨hn1, hn21, hn22⟩, ⟨hexp1, hexp21, hexp22⟩, hviol_n⟩ := hn₀ n hn
  set M₁ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₁)⌋₊
  set M₂ := max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R₂)⌋₊
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  obtain ⟨C, hCpow, hCerr⟩ :=
    exists_bc_superposition_code (P := P) (N₁ := N₁) (N₂ := N₂) (v₁ := v₁) (v₂ := v₂)
      hP k n M₁ M₂ hM₁ hM₂ ε₁ ε₂₁ ε₂₂
  have hM_le : ∀ (R : ℝ), 0 ≤ R →
      ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    intro R hR0
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := Real.one_le_rpow (by norm_num) (by positivity)
    have hle : ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
      rcases le_total 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ with h | h
      · rw [max_eq_right h]; exact Nat.floor_le (by positivity)
      · rw [max_eq_left h]; push_cast; exact h1
    have hsub : ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ - 1 : ℕ) : ℝ) ≤
        ((max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
    linarith
  have ht1 : ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) ≤ t := by
    have hprod : (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) =
        (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₁]; ring
    calc ((M₁ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁)))
        ≤ (2 : ℝ) ^ ((n : ℝ) * R₁) * (2 : ℝ) ^ (-((n : ℝ) * (W₁.mutualInfo Q₁ - 3 * ε₁))) :=
          mul_le_mul_of_nonneg_right (hM_le R₁ hR₁0) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * ε₁)) := hprod
      _ ≤ t := hexp1
  have ht21 : ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₁.mutualInfo Q₂ - 3 * ε₂₁))) ≤ t := by
    have hprod : (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₁.mutualInfo Q₂ - 3 * ε₂₁))) =
        (2 : ℝ) ^ (-((n : ℝ) * ε₂₁)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₂₁]; ring
    calc ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₁.mutualInfo Q₂ - 3 * ε₂₁)))
        ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₁.mutualInfo Q₂ - 3 * ε₂₁))) :=
          mul_le_mul_of_nonneg_right (hM_le R₂ hR₂0) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * ε₂₁)) := hprod
      _ ≤ t := hexp21
  have ht22 : ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₂.mutualInfo Q₂ - 3 * ε₂₂))) ≤ t := by
    have hprod : (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₂.mutualInfo Q₂ - 3 * ε₂₂))) =
        (2 : ℝ) ^ (-((n : ℝ) * ε₂₂)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; dsimp only [ε₂₂]; ring
    calc ((M₂ - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₂.mutualInfo Q₂ - 3 * ε₂₂)))
        ≤ (2 : ℝ) ^ ((n : ℝ) * R₂) * (2 : ℝ) ^ (-((n : ℝ) * (W₂₂.mutualInfo Q₂ - 3 * ε₂₂))) :=
          mul_le_mul_of_nonneg_right (hM_le R₂ hR₂0) (by positivity)
      _ = (2 : ℝ) ^ (-((n : ℝ) * ε₂₂)) := hprod
      _ ≤ t := hexp22
  have haep1 := hK₁ n hn1
  have haep21 := hK₂₁ n hn21
  have haep22 := hK₂₂ n hn22
  have h8t : 8 * t = δ := by rw [ht_def]; ring
  have hbest : (gaussianBCAvgError₁ C N₁).toReal + (gaussianBCAvgError₂ C N₂).toReal ≤ δ := by
    linarith
  refine ⟨C, hCpow, ?_, ?_⟩
  · rw [ENNReal.le_ofReal_iff_toReal_le (gaussianBCAvgError₁_ne_top hM₁ hM₂ C N₁) hδ.le]
    linarith [ENNReal.toReal_nonneg (a := gaussianBCAvgError₂ C N₂)]
  · rw [ENNReal.le_ofReal_iff_toReal_le (gaussianBCAvgError₂_ne_top hM₁ hM₂ C N₂) hδ.le]
    linarith [ENNReal.toReal_nonneg (a := gaussianBCAvgError₁ C N₁)]

end GaussianBroadcast

end InfoTheory.Known
