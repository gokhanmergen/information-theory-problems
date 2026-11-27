import InfoTheory.Known.Certificates.DeletionChannel

/-!
# Certificate: `DeletionChannelSmallDAsymptotics`

Proofs live in the shared file `InfoTheory.Known.Certificates.DeletionChannel`; this module
restates the certified facts for `InfoTheory.Problems.DeletionChannelSmallDAsymptotics`:
the series defining the Kanoria–Montanari constant converges (so its `tsum` is not a junk
value) and the constant is positive (≈ 0.2885, matching Kanoria–Montanari 2013).
-/

namespace InfoTheory.Known.Certificates.DeletionChannelSmallDAsymptotics

open InfoTheory.Problems.DeletionChannelSmallDAsymptotics in
/-- The Kanoria–Montanari first-order constant is a genuine (convergent) positive sum. -/
theorem known_facts : Summable DeletionChannel.kmTerm ∧ 0 < kanoriaMontanariC1 :=
  ⟨DeletionChannel.kanoriaMontanari_summable, DeletionChannel.kanoriaMontanariC1_pos⟩

end InfoTheory.Known.Certificates.DeletionChannelSmallDAsymptotics
