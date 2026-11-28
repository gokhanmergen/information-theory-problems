import InfoTheory.Problems.TraceReconstructionAverageCase
import InfoTheory.Known.Channels

/-!
# Certificate for `InfoTheory.Problems.TraceReconstructionAverageCase`

The frozen statement asks whether average-case trace reconstruction at deletion probability
`1/2` needs only `(log n)^{O(1)}` traces. Facts about the *exact* object
`traceReconAvgCaseSamples`:

## Certified
* `deletionProb_self`: `Pr[Del_d(x) = x] = (1-d)^{|x|}`; `deletionProb_nonneg`.
* `decOne_success`: the one-trace decoder "output the trace if it has full length" succeeds with
  probability `≥ (1-d)^n`.
* `traceReconAvgCaseSamples_eq_one` (regression): whenever `(1-d)^n ≥ 2/3` the sample
  complexity is exactly `1`; in particular `traceReconAvgCaseSamples_noiseless`
  (`d = 0`, every `n`), `traceReconAvgCaseSamples_zero_length`, and
  `traceReconAvgCaseSamples_one_small_d` (`n = 1`, `d ≤ 1/3`). The `sInf` is therefore a
  genuine minimum (positivity is built in: `0 < T`).

## Not certified
* Non-emptiness of the defining set at `d = 1/2` (so that `T_avg(n, 1/2)` is not the junk
  `sInf ∅ = 0`). It holds — output any full-length trace; success `1 - (1 - 2^{-n})^T → 1` —
  but the proof needs the normalisation `∑_y Pr[Del_d(x) = y] = 1`, not yet in `Known`.
  (At `d = 1` the set *is* empty for `n ≥ 2`; `d = 1` is outside the Statement.)
* The known bounds `exp(O(log^{1/3} n))` (Holden–Pemantle–Peres–Zhai 2020) and
  `Ω̃(log^{5/2} n)` (Chase 2021).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.TraceReconstructionAverageCase

open InfoTheory InfoTheory.Problems.TraceReconstructionAverageCase

/-- `Pr[Del_d(x) = x] = (1 - d)^{|x|}`: the full-length trace is the input itself. -/
theorem deletionProb_self (d : ℝ) (x : List Bool) :
    deletionProb d x x = (1 - d) ^ x.length := by
  unfold deletionProb
  simp [Known.subseqCount_of_length_eq]

theorem deletionProb_nonneg {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (x y : List Bool) :
    0 ≤ deletionProb d x y := by
  unfold deletionProb
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
      (pow_nonneg h0 _)
  · exact le_rfl

/-- Trace alphabet used by `traceReconAvgCaseSamples`. -/
abbrev Trace (n : ℕ) := Σ k : Fin (n + 1), Fin k.1 → Bool

/-- The full-length trace `x` (no deletion). -/
def fullTrace {n : ℕ} (x : Fin n → Bool) : Trace n := ⟨Fin.last n, x⟩

/-- One-trace decoder: output the trace if it has full length `n`, else all-`false`. -/
def decOne {n : ℕ} (tr : Fin 1 → Trace n) : Fin n → Bool :=
  if h : (tr 0).1.1 = n then fun i => (tr 0).2 (Fin.cast h.symm i) else fun _ => false

lemma decOne_full {n : ℕ} (x : Fin n → Bool) : decOne (fun _ => fullTrace x) = x := by
  unfold decOne fullTrace
  simp

/-- With one trace, the decoder `decOne` succeeds with probability at least `(1 - d)^n`. -/
theorem decOne_success {n : ℕ} {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    (1 - d) ^ n ≤ ((1 : ℝ) / ((2 ^ n : ℕ) : ℝ)) *
      ∑ x : Fin n → Bool, ∑ tr : Fin 1 → Trace n,
        if decOne tr = x then
          ∏ t : Fin 1, deletionProb d (List.ofFn x) (List.ofFn (tr t).2)
        else 0 := by
  have key : ∀ x : Fin n → Bool, (1 - d) ^ n ≤ ∑ tr : Fin 1 → Trace n,
      (if decOne tr = x then
        ∏ t : Fin 1, deletionProb d (List.ofFn x) (List.ofFn (tr t).2) else 0) := by
    intro x
    have hle := Finset.single_le_sum
      (f := fun tr : Fin 1 → Trace n => if decOne tr = x then
        ∏ t : Fin 1, deletionProb d (List.ofFn x) (List.ofFn (tr t).2) else 0)
      (fun tr _ => by
        split_ifs
        · exact Finset.prod_nonneg (fun t _ => deletionProb_nonneg h0 h1 _ _)
        · exact le_rfl)
      (Finset.mem_univ (fun _ : Fin 1 => fullTrace x))
    refine le_trans (le_of_eq ?_) hle
    simp only [decOne_full, ite_true, Finset.univ_unique, Finset.prod_singleton]
    unfold fullTrace
    rw [deletionProb_self, List.length_ofFn]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => key x)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
  calc (1 - d) ^ n = ((1 : ℝ) / ((2 ^ n : ℕ) : ℝ)) * (((2 ^ n : ℕ) : ℝ) * (1 - d) ^ n) := by
        field_simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hsum

/-- **Regression (solved special case).** Whenever one trace already succeeds with probability
    `(1 - d)^n ≥ 2/3` — in particular for the noiseless channel `d = 0` — the sample
    complexity is exactly one trace. -/
theorem traceReconAvgCaseSamples_eq_one {n : ℕ} {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1)
    (h : (2 : ℝ) / 3 ≤ (1 - d) ^ n) : traceReconAvgCaseSamples n d = 1 := by
  have hmem : 1 ∈ { T : ℕ | 0 < T ∧
      ∃ dec : (Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool) → (Fin n → Bool),
        let successProb : ℝ :=
          ((1 : ℝ) / ((2 ^ n : ℕ) : ℝ)) *
            ∑ x : Fin n → Bool,
              ∑ tr : Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool,
                if dec tr = x then
                  ∏ t : Fin T, deletionProb d (List.ofFn x) (List.ofFn (tr t).2)
                else 0
        2 / 3 ≤ successProb } :=
    ⟨one_pos, decOne, le_trans h (decOne_success h0 h1)⟩
  unfold traceReconAvgCaseSamples
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

/-- Noiseless channel: one trace suffices. -/
theorem traceReconAvgCaseSamples_noiseless (n : ℕ) : traceReconAvgCaseSamples n 0 = 1 :=
  traceReconAvgCaseSamples_eq_one le_rfl zero_le_one (by simp; norm_num)

/-- The empty string is reconstructed from one trace at every deletion probability. -/
theorem traceReconAvgCaseSamples_zero_length {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    traceReconAvgCaseSamples 0 d = 1 :=
  traceReconAvgCaseSamples_eq_one h0 h1 (by simp; norm_num)

/-- Small deletion rates: a single trace suffices while `(1 - d)^n ≥ 2/3`, e.g. `n = 1`,
    `d ≤ 1/3`. -/
theorem traceReconAvgCaseSamples_one_small_d {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1 / 3) :
    traceReconAvgCaseSamples 1 d = 1 :=
  traceReconAvgCaseSamples_eq_one h0 (by linarith) (by simp; linarith)

end InfoTheory.Known.Certificates.TraceReconstructionAverageCase
