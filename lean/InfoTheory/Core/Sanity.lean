import InfoTheory.Core.Entropy
import InfoTheory.Core.Channels
import InfoTheory.Core.Coding
import InfoTheory.Core.Quantum
import InfoTheory.Core.SecurityStats

/-!
# Core Definition Sanity & Regression Theorems

Proved sanity checks (zero `sorry`, standard axioms only) certifying that Core
information-theoretic definitions behave faithfully and guarding against regressions
of previously caught formalization bugs (C1, C4, C5, C8, C13):
- `binaryEntropy 0 = 0` and `binaryEntropy (1 / 2) = 1`
- Operational and single-letter capacity regions are topologically closed (C8)
- `IndexCodingInstance` forbids self-loops (C5)
- `klDivergenceEReal` returns `⊤` whenever `¬ AbsCont P Q` (C13)
- `extractAliceCopyIdx` / `extractBobCopyIdx` correctly de-interleave `(A₁ B₁)(A₂ B₂)`
  into `(A₁ A₂) | (B₁ B₂)` for `n = 2` (C4)
- `binaryDeletionCapacity d ≤ binaryDeletionMaxMI d n / n` for every `n ≥ 1` (Fekete infimum, C1)
-/

open scoped BigOperators

namespace InfoTheory.Sanity

/-- Binary entropy vanishes at `p = 0`. -/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, negPLogP, log2]

/-- Binary entropy equals `1` bit at `p = 1/2`. -/
theorem binaryEntropy_half : binaryEntropy (1 / 2) = 1 := by
  unfold binaryEntropy negPLogP log2
  have hpos : ¬ ((1 : ℝ) / 2 ≤ 0) := by norm_num
  have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hsub, if_neg hpos]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub]
  field_simp [hlog2]
  ring

/-- Broadcast capacity region is closed (C8 regression guard). -/
theorem bcCapacityRegion_isClosed {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : IsClosed (bcCapacityRegion W) :=
  isClosed_closure

/-- Marton inner bound is closed (C7/C8 regression guard). -/
theorem martonInnerBound_isClosed {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : IsClosed (martonInnerBound W) :=
  isClosed_closure

/-- Interference channel capacity region is closed (C8 regression guard). -/
theorem icCapacityRegion_isClosed {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : IsClosed (icCapacityRegion W) :=
  isClosed_closure

/-- Two-way channel capacity region is closed (C8 regression guard). -/
theorem twcCapacityRegion_isClosed {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) : IsClosed (twcCapacityRegion W) :=
  isClosed_closure

/-- MAC with feedback capacity region is closed (C8 regression guard). -/
theorem macFeedbackCapacityRegion_isClosed {X₁ X₂ Y : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y]
    (W : MACChannel X₁ X₂ Y) : IsClosed (macFeedbackCapacityRegion W) :=
  isClosed_closure

/-- Index coding instances forbid self-loops (C5 regression guard). -/
theorem indexCoding_no_self_loop {n : ℕ} (inst : IndexCodingInstance n) (i : Fin n) :
    ¬ inst.sideInfo i i :=
  inst.irrefl i

/-- Extended-real KL divergence equals `⊤` when `P` is not absolutely continuous w.r.t. `Q` (C13). -/
theorem klDivergenceEReal_eq_top_of_not_absCont {α : Type*} [Fintype α]
    (P Q : ProbDist α) (h : ¬ AbsCont P Q) : klDivergenceEReal P Q = ⊤ := by
  unfold klDivergenceEReal
  simp [h]

/-- Concrete 2-copy qubit interleaving check (C4 regression guard):
    basis index `idx = (a₁ * 2 + b₁) * 4 + (a₂ * 2 + b₂)` maps Alice's index to `a₁ * 2 + a₂`
    and Bob's index to `b₁ * 2 + b₂`, NOT copy-1 vs copy-2.
    For `(a₁, b₁) = (0, 1)` and `(a₂, b₂) = (1, 0)`, `idx = 1 * 4 + 2 = 6`:
    Alice gets `(0, 1) = 1`, Bob gets `(1, 0) = 2`. -/
theorem copyIdx_interleaving_n2 :
    extractAliceCopyIdx 2 2 2 6 = 1 ∧ extractBobCopyIdx 2 2 2 6 = 2 := by
  decide

/-- Exact 1-copy identity for `extractAliceCopyIdx` / `extractBobCopyIdx` (C4). -/
theorem copyIdx_n1 (dA dB idx : ℕ) (h : idx < dA * dB) :
    extractAliceCopyIdx dA dB 1 idx = idx / dB ∧
    extractBobCopyIdx dA dB 1 idx = idx % dB := by
  simp [extractAliceCopyIdx, extractBobCopyIdx, Nat.mod_eq_of_lt h]

/-- Single-bit deletion transition check: `Pr[Del_d([true]) = [true]] = 1 - d` and
    `Pr[Del_d([true]) = []] = d`. -/
theorem deletionProb_len1 (d : ℝ) :
    deletionProb d [true] [true] = 1 - d ∧ deletionProb d [true] [] = d := by
  simp [deletionProb, subseqCount]

/-- Fekete infimum upper bound (C1 regression guard): if the per-letter capacity sequence is
    bounded below (e.g. by `0`), then `binaryDeletionCapacity d ≤ binaryDeletionMaxMI d n / n`
    for every `n ≥ 1` (so any blocklength `n ≥ 2` strictly below `1 - d` strictly upper-bounds `C(d)`). -/
theorem binaryDeletionCapacity_le_block (d : ℝ) (n : ℕ) (hn : 0 < n)
    (hbdd : BddBelow { r : ℝ | ∃ m : ℕ, 0 < m ∧ r = binaryDeletionMaxMI d m / (m : ℝ) }) :
    binaryDeletionCapacity d ≤ binaryDeletionMaxMI d n / (n : ℝ) :=
  csInf_le hbdd ⟨n, hn, rfl⟩

end InfoTheory.Sanity
