import InfoTheory.Problems.SdpiKlVsChisqEquality
import InfoTheory.Known.Certificates.SdpiKlVsChisqEquality

/-!
# Disproof of `InfoTheory.Problems.SdpiKlVsChisqEquality.Statement`

The statement asks whether two-sided equality of the input-dependent KL and `χ²` SDPI constants
of a reversible finite source forces its hypercontractivity ribbon (Nair's KL form) to be the
Bonami–Beckner region `(p - 1)/(q - 1) ≥ s_{χ²}`. It is false.

Counterexample (all proofs in `InfoTheory.Known.Certificates.SdpiKlVsChisqEquality`):
`exQ = (1/4, 1/4, 1/2)`,
`exW = [[9/20, 3/20, 2/5], [3/20, 9/20, 2/5], [1/5, 1/5, 3/5]]`.
The joint law `exQ × exW` is symmetric, so `Wrev = exW` and `QY = exQ`.

1. `sdpiChiSqAt_ex`: `s_{χ²}(exQ, exW) = 9/100`, the squared second singular value `3/10`.
2. `sdpiKLAt_ex`: `s_KL(exQ, exW) = 9/100`.
   - The lower bound comes from the tilted inputs `P_z → exQ`.
   - The upper bound is the global inequality `kl_ex_global`,
     `D(P exW ‖ exQ) ≤ (9/100) D(P ‖ exQ)` for every `P`. It is proved by the grouping
     identity, the even power series of the binary divergence, and an exact polynomial
     positivity certificate.
3. `ex_not_ribbon`: `(p, q) = (127/100, 4)` has `(p - 1)/(q - 1) = 9/100`, yet it is not in the
   ribbon. The witness is an explicit rational joint law, checked with certified `log₂` bounds.
-/

namespace InfoTheory.Solutions.SdpiKlVsChisqEquality

theorem disproof : ¬ InfoTheory.Problems.SdpiKlVsChisqEquality.Statement :=
  InfoTheory.Known.Certificates.SdpiKlVsChisqEquality.statement_false

end InfoTheory.Solutions.SdpiKlVsChisqEquality
