import InfoTheory.Problems.TraceReconstructionWorstCase
import InfoTheory.Known.Channels

/-!
# Certificate for `InfoTheory.Problems.TraceReconstructionWorstCase`

The frozen statement asks whether `T_wc(n, 1/2) = O(n^c)`, where `traceReconWorstCaseSamples n d`
is the least `T > 0` such that every pair `x ≠ y ∈ {0,1}^n` can be told apart from `T`
independent `Del_d` traces with average success `≥ 2/3` (`prob x true + prob y false ≥ 4/3`).
Pairwise distinguishing and worst-case reconstruction differ by at most an `O(n)` factor
(amplify plus Scheffé tournament), so the polynomial-vs-superpolynomial question is the same.

## Certified (about exactly `traceReconWorstCaseSamples`)
* `deletionProb_self`, `deletionProb_nil`, `deletionProb_nonneg`: `Pr[Del_d(x) = x] = (1-d)^{|x|}`,
  `Pr[Del_d(x) = ε] = d^{|x|}`.
* `fullTest_success`: the one-trace test "say `x` iff the trace is the full word `x`" has
  `prob x true + prob y false ≥ 2(1-d)^n + d^n` for every pair `x ≠ y` (`n ≥ 1`); the `y`-side
  uses the two traces "full `y`" and "empty".
* `traceReconWorstCaseSamples_eq_one` (regression): if `2(1-d)^n + d^n ≥ 4/3` then
  `T_wc(n, d) = 1` exactly, so the `sInf` is a genuine minimum there. Instances:
  `traceReconWorstCaseSamples_noiseless` (`d = 0`, every `n`),
  `traceReconWorstCaseSamples_zero_length` (`n = 0`), and — at the Statement's own deletion
  probability — `traceReconWorstCaseSamples_one_half_one` : `T_wc(1, 1/2) = 1`.

## Not certified
* Non-emptiness of the defining set for general `n` at `d = 1/2` (so that `T_wc(n, 1/2)` is not
  the junk `sInf ∅ = 0`). It holds — "say `x` iff some trace is the full word `x`" has success
  `1 - (1 - 2^{-n})^T + 1` — but the `y`-side needs the normalisation `∑_z Pr[Del_d(y) = z] = 1`,
  not yet in `Known` (the same gap as the average-case certificate).
* The known bounds `exp(Õ(n^{1/5}))` (Chase 2021), the claimed quasipolynomial bound of
  Burudgunte–Valiant–Wang (arXiv:2607.04073, 2026, unverified here) and `Ω̃(n^{3/2})` (Chase 2021).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.TraceReconstructionWorstCase

open InfoTheory InfoTheory.Problems.TraceReconstructionWorstCase

/-- `Pr[Del_d(x) = x] = (1 - d)^{|x|}`. -/
theorem deletionProb_self (d : ℝ) (x : List Bool) :
    deletionProb d x x = (1 - d) ^ x.length := by
  unfold deletionProb
  simp [Known.subseqCount_of_length_eq]

/-- `Pr[Del_d(x) = ε] = d^{|x|}`: the empty trace means every bit was deleted. -/
theorem deletionProb_nil (d : ℝ) (x : List Bool) :
    deletionProb d x [] = d ^ x.length := by
  unfold deletionProb
  have : subseqCount x ([] : List Bool) = 1 := by cases x <;> rfl
  simp [this]

theorem deletionProb_nonneg {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (x y : List Bool) :
    0 ≤ deletionProb d x y := by
  unfold deletionProb
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
      (pow_nonneg h0 _)
  · exact le_rfl

/-- Trace alphabet used by `traceReconWorstCaseSamples`. -/
abbrev Trace (n : ℕ) := Σ k : Fin (n + 1), Fin k.1 → Bool

/-- The full-length trace `x` (no deletion). -/
def fullTrace {n : ℕ} (x : Fin n → Bool) : Trace n := ⟨Fin.last n, x⟩

/-- The empty trace (everything deleted). -/
def emptyTrace (n : ℕ) : Trace n := ⟨0, fun i => Fin.elim0 i⟩

/-- One-trace test: answer `true` ("it is `x`") iff the trace is the full word `x`. -/
def fullTest {n : ℕ} (x : Fin n → Bool) (tr : Fin 1 → Trace n) : Bool :=
  decide (tr 0 = fullTrace x)

lemma fullTrace_injective {n : ℕ} : Function.Injective (fullTrace (n := n)) := by
  intro x y h
  unfold fullTrace at h
  simpa using h

lemma emptyTrace_ne_fullTrace {n : ℕ} (hn : 1 ≤ n) (x : Fin n → Bool) :
    emptyTrace n ≠ fullTrace x := by
  intro h
  have := congrArg (fun t : Trace n => t.1.1) h
  simp [emptyTrace, fullTrace] at this
  omega

/-- Success of the one-trace full-word test on any pair `x ≠ y`. -/
theorem fullTest_success {n : ℕ} {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (hn : 1 ≤ n)
    (x y : Fin n → Bool) (hxy : x ≠ y) :
    2 * (1 - d) ^ n + d ^ n ≤
      (∑ tr : Fin 1 → Trace n,
          if fullTest x tr = true then
            ∏ t : Fin 1, deletionProb d (List.ofFn x) (List.ofFn (tr t).2) else 0) +
      (∑ tr : Fin 1 → Trace n,
          if fullTest x tr = false then
            ∏ t : Fin 1, deletionProb d (List.ofFn y) (List.ofFn (tr t).2) else 0) := by
  have hnn : ∀ (z : Fin n → Bool) (b : Bool) (tr : Fin 1 → Trace n),
      0 ≤ (if fullTest x tr = b then
        ∏ t : Fin 1, deletionProb d (List.ofFn z) (List.ofFn (tr t).2) else 0) := by
    intro z b tr
    split_ifs
    · exact Finset.prod_nonneg (fun t _ => deletionProb_nonneg h0 h1 _ _)
    · exact le_rfl
  -- `x`-side: the trace `fullTrace x`.
  have hx := Finset.single_le_sum (fun tr _ => hnn x true tr)
    (Finset.mem_univ (fun _ : Fin 1 => fullTrace x))
  have hxval : (if fullTest x (fun _ : Fin 1 => fullTrace x) = true then
      ∏ t : Fin 1, deletionProb d (List.ofFn x)
        (List.ofFn ((fun _ : Fin 1 => fullTrace x) t).2) else 0) = (1 - d) ^ n := by
    simp only [fullTest, decide_true, ite_true, Finset.univ_unique, Finset.prod_singleton]
    unfold fullTrace
    rw [deletionProb_self, List.length_ofFn]
  -- `y`-side: the traces `fullTrace y` and `emptyTrace`.
  have hne : (fun _ : Fin 1 => fullTrace y) ≠ (fun _ : Fin 1 => emptyTrace n) := by
    intro h
    exact emptyTrace_ne_fullTrace hn y (congrFun h 0).symm
  have hy := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun tr : Fin 1 → Trace n => if fullTest x tr = false then
      ∏ t : Fin 1, deletionProb d (List.ofFn y) (List.ofFn (tr t).2) else 0)
    (Finset.subset_univ {fun _ => fullTrace y, fun _ => emptyTrace n})
    (fun tr _ _ => hnn y false tr)
  rw [Finset.sum_pair hne] at hy
  have hy1 : (if fullTest x (fun _ : Fin 1 => fullTrace y) = false then
      ∏ t : Fin 1, deletionProb d (List.ofFn y)
        (List.ofFn ((fun _ : Fin 1 => fullTrace y) t).2) else 0) = (1 - d) ^ n := by
    have : fullTest x (fun _ : Fin 1 => fullTrace y) = false := by
      simp only [fullTest, decide_eq_false_iff_not]
      exact fun h => hxy (fullTrace_injective h).symm
    simp only [this, ite_true, Finset.univ_unique, Finset.prod_singleton]
    unfold fullTrace
    rw [deletionProb_self, List.length_ofFn]
  have hy2 : (if fullTest x (fun _ : Fin 1 => emptyTrace n) = false then
      ∏ t : Fin 1, deletionProb d (List.ofFn y)
        (List.ofFn ((fun _ : Fin 1 => emptyTrace n) t).2) else 0) = d ^ n := by
    have : fullTest x (fun _ : Fin 1 => emptyTrace n) = false := by
      simp only [fullTest, decide_eq_false_iff_not]
      exact emptyTrace_ne_fullTrace hn x
    simp only [this, ite_true, Finset.univ_unique, Finset.prod_singleton]
    have hl : List.ofFn (emptyTrace n).2 = [] := by simp [emptyTrace]
    rw [hl, deletionProb_nil, List.length_ofFn]
  rw [hxval] at hx
  rw [hy1, hy2] at hy
  linarith

/-- **Regression.** Whenever `2(1-d)^n + d^n ≥ 4/3` (and `n ≥ 1`), one trace suffices and the
    worst-case sample complexity is exactly `1`. -/
theorem traceReconWorstCaseSamples_eq_one {n : ℕ} {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1)
    (hn : 1 ≤ n) (h : (4 : ℝ) / 3 ≤ 2 * (1 - d) ^ n + d ^ n) :
    traceReconWorstCaseSamples n d = 1 := by
  have hmem : 1 ∈ { T : ℕ | 0 < T ∧
      ∀ x y : Fin n → Bool, x ≠ y →
        ∃ (dec : (Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool) → Bool),
          let prob (z : Fin n → Bool) (target : Bool) : ℝ :=
            ∑ tr : Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool,
              if dec tr = target then
                ∏ t : Fin T, deletionProb d (List.ofFn z) (List.ofFn (tr t).2)
              else 0
          prob x true + prob y false ≥ 4 / 3 } := by
    refine ⟨one_pos, fun x y hxy => ⟨fullTest x, ?_⟩⟩
    show _ ≤ _
    exact le_trans h (fullTest_success h0 h1 hn x y hxy)
  unfold traceReconWorstCaseSamples
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

/-- Noiseless channel: one trace distinguishes every pair. -/
theorem traceReconWorstCaseSamples_noiseless {n : ℕ} (hn : 1 ≤ n) :
    traceReconWorstCaseSamples n 0 = 1 :=
  traceReconWorstCaseSamples_eq_one le_rfl zero_le_one hn (by
    rw [zero_pow (by omega)]; norm_num)

/-- Length `0`: there are no pairs to distinguish, so `T_wc(0, d) = 1` (positivity is built in). -/
theorem traceReconWorstCaseSamples_zero_length (d : ℝ) :
    traceReconWorstCaseSamples 0 d = 1 := by
  have hmem : 1 ∈ { T : ℕ | 0 < T ∧
      ∀ x y : Fin 0 → Bool, x ≠ y →
        ∃ (dec : (Fin T → Σ k : Fin (0 + 1), Fin k.1 → Bool) → Bool),
          let prob (z : Fin 0 → Bool) (target : Bool) : ℝ :=
            ∑ tr : Fin T → Σ k : Fin (0 + 1), Fin k.1 → Bool,
              if dec tr = target then
                ∏ t : Fin T, deletionProb d (List.ofFn z) (List.ofFn (tr t).2)
              else 0
          prob x true + prob y false ≥ 4 / 3 } :=
    ⟨one_pos, fun x y hxy => absurd (funext fun i => Fin.elim0 i) hxy⟩
  unfold traceReconWorstCaseSamples
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

/-- **Regression at the Statement's deletion probability `d = 1/2`:** `T_wc(1, 1/2) = 1`
    (success `1/2 + (1/2 + 1/2) = 3/2 ≥ 4/3`). -/
theorem traceReconWorstCaseSamples_one_half_one :
    traceReconWorstCaseSamples 1 (1 / 2 : ℝ) = 1 :=
  traceReconWorstCaseSamples_eq_one (by norm_num) (by norm_num) le_rfl (by norm_num)

end InfoTheory.Known.Certificates.TraceReconstructionWorstCase
