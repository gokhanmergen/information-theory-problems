import InfoTheory.Core
import InfoTheory.Core.GaussianOperational

open scoped BigOperators ENNReal
open MeasureTheory

namespace InfoTheory.Problems.AmplitudeConstrainedAwgnSupport

/-- Peak-amplitude constraint `|x(m)ᵢ| ≤ A` on every symbol of every codeword (Smith 1971). -/
def SatisfiesPeak {n M : ℕ} (C : AwgnCode n M) (A : ℝ) : Prop :=
  ∀ m i, |C.encoder m i| ≤ A

/-- The code uses at most `k` distinct amplitudes, all in `[-A, A]`: every symbol of every
    codeword lies in a fixed finite constellation `S ⊆ [-A, A]` with `|S| ≤ k`. -/
def UsesConstellation {n M : ℕ} (C : AwgnCode n M) (A : ℝ) (k : ℕ) : Prop :=
  ∃ S : Finset ℝ, S.card ≤ k ∧ (∀ s ∈ S, |s| ≤ A) ∧ ∀ m i, C.encoder m i ∈ S

/-- Operational achievability of rate `R` over the AWGN channel `Y = X + Z`, `Z ~ N(0, N)`,
    under the peak constraint `|X| ≤ A`: codes with measurable decoders
    (`MeasurableBlockCode`), `max 1 ⌊2^{nR}⌋` messages, and average error `≤ δ` (a value of a
    measure in `ℝ≥0∞`) for all large `n`. -/
def IsPeakAchievable (A N R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : AwgnCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊),
      SatisfiesPeak C A ∧ awgnAvgErrorProb C N ≤ ENNReal.ofReal δ

/-- As `IsPeakAchievable`, but each code must use a constellation of at most `k` points
    in `[-A, A]` (the constellation may depend on the blocklength). -/
def IsPeakAchievableWithin (A N : ℝ) (k : ℕ) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ C : AwgnCode n (max 1 ⌊(2 : ℝ) ^ ((n : ℝ) * R)⌋₊),
      UsesConstellation C A k ∧ awgnAvgErrorProb C N ≤ ENNReal.ofReal δ

/-- Operational capacity `C(A, N)` of the peak-amplitude-constrained AWGN channel.
    The set is nonempty and bounded above by `½ log₂(1 + A²/N)` for `A ≥ 0`, `N > 0`
    (certified in `Known.Certificates.AmplitudeConstrainedAwgnSupport`). -/
noncomputable def peakCapacity (A N : ℝ) : ℝ :=
  sSup { R : ℝ | IsPeakAchievable A N R }

/-- Operational capacity `C_k(A, N)` with at most `k` signal points.  Nonempty for `k ≥ 1`,
    `A ≥ 0` and bounded above by `peakCapacity A N` (certified). -/
noncomputable def peakCapacityWithin (A N : ℝ) (k : ℕ) : ℝ :=
  sSup { R : ℝ | IsPeakAchievableWithin A N k R }

/-- Monotonicity of the Number of Mass Points of the Amplitude-Constrained AWGN Capacity-Achieving
    Input (Sharma–Shamai 2010): if `k` signal points suffice to achieve capacity at amplitude
    `A'`, do they suffice at every smaller amplitude `A ≤ A'`?
    By Smith's theorem (unique, finitely supported optimal input), `C_k(A, N) = C(A, N)` holds
    iff the capacity-achieving input at amplitude `A/√N` has at most `k` mass points, so this
    says exactly that the support size `K(A)` is nondecreasing in `A`. -/
def Statement : Prop :=
  ∀ (N A A' : ℝ) (k : ℕ), 0 < N → 0 < A → A ≤ A' → 1 ≤ k →
    peakCapacityWithin A' N k = peakCapacity A' N →
      peakCapacityWithin A N k = peakCapacity A N

def problem : OpenProblem where
  id := "amplitude-constrained-awgn-support"
  title := "Monotonicity of the Support Size of the Amplitude-Constrained AWGN Optimal Input"
  category := .channelCapacity
  status := .open
  posedBy := "Nitin Sharma and Shlomo Shamai (Shitz)"
  posedYear := 2010
  statement := Statement

end InfoTheory.Problems.AmplitudeConstrainedAwgnSupport
