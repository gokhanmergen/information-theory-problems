import InfoTheory.Known.Certificates.DeletionChannel

/-!
# Certificate: `DeletionChannelSmallDAsymptotics`

Proofs live in the shared file `InfoTheory.Known.Certificates.DeletionChannel`; this module
restates the certified facts for `InfoTheory.Problems.DeletionChannelSmallDAsymptotics`:
the series defining the Kanoria–Montanari constant converges (so its `tsum` is not a junk
value) and the constant is positive (≈ 0.2885, matching Kanoria–Montanari 2013).

* **Regression**: `regression_expansion_at_zero` — the expansion
  `C(d) = 1 - h(d) + ∑_{k≥1} c_k d^k` is exact at the solved point `d = 0` (`C(0) = 1`,
  `h(0) = 0`) for every coefficient sequence; `regression_noiseless_block` — the block
  objects give the noiseless value `C_n(0) = n`.
-/

namespace InfoTheory.Known.Certificates.DeletionChannelSmallDAsymptotics

open InfoTheory.Problems.DeletionChannelSmallDAsymptotics in
/-- The Kanoria–Montanari first-order constant is a genuine (convergent) positive sum. -/
theorem known_facts : Summable DeletionChannel.kmTerm ∧ 0 < kanoriaMontanariC1 :=
  ⟨DeletionChannel.kanoriaMontanari_summable, DeletionChannel.kanoriaMontanariC1_pos⟩

/-- **Regression**: the expansion form is exact at `d = 0`. -/
theorem regression_expansion_at_zero (c : ℕ → ℝ) :
    InfoTheory.binaryDeletionCapacity 0 =
      1 - InfoTheory.binaryEntropy 0 + ∑' k : ℕ, c (k + 1) * (0 : ℝ) ^ (k + 1) :=
  DeletionChannel.regression_expansion_at_zero c

/-- **Regression**: `C_n(0) = n` (noiseless channel). -/
theorem regression_noiseless_block (n : ℕ) : InfoTheory.binaryDeletionMaxMI 0 n = n :=
  DeletionChannel.regression_maxMI_zero n

end InfoTheory.Known.Certificates.DeletionChannelSmallDAsymptotics
